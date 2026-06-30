/// Runtime tables backed by BTreeSet plus per-column hash indexes.

use std::collections::{BTreeSet, BTreeMap};
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use serde::{Serialize, Deserialize};
use crate::ast::Value;

/// A row is a vector of values (positional, matching column order).
pub type Row = Vec<Value>;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Table {
    pub name: String,
    /// Column names + types (for debugging / display).
    pub columns: Vec<String>,
    /// The actual data: a sorted set of *currently valid* rows (log-time
    /// lookup).  For a windowed (metric) table this is the active set — rows
    /// whose validity window contains the current time; lookups read it
    /// unchanged.
    pub rows: BTreeSet<Row>,
    /// Per-column index: for each column i, map value -> set of rows with row[i] = value.
    ///
    /// Uses HashSet for O(1) amortized insert/remove instead of BTreeSet's O(log n).
    #[serde(skip, default)]
    pub column_indexes: Vec<HashMap<Value, HashSet<Row>>>,

    // ─── Metric windowing (Once / Since / Prev) ──────────────────────────────
    /// Window `(a, b)` in timestamp units.  A tuple observed at time `t` is
    /// valid for a query at time `c` iff `c - t ∈ [a, b]`.  `None` = non-metric
    /// (`[0, ∞)`): accumulate forever, no windowing machinery is used.
    #[serde(default)]
    pub window: Option<(u64, Option<u64>)>,
    /// Whether this is a lagged (Prev) table: cleared and repopulated each
    /// time-point so it reflects only the immediately-preceding one, with the
    /// window (if any) bounding the gap between consecutive time-points.
    #[serde(default)]
    pub lagged: bool,
    /// Reference count of currently-active observations per row.  A row is in
    /// `rows` iff its count is > 0.  (Non-lagged windowed tables only.)
    #[serde(default)]
    active_count: HashMap<Row, u32>,
    /// Pending observations not yet within the lower bound: activation-ts → rows.
    #[serde(default)]
    by_activation: BTreeMap<u64, Vec<Row>>,
    /// Scheduled expiries: expiry-ts → rows (the ts at which an observation
    /// leaves the window, i.e. `t + b + 1`).
    #[serde(default)]
    by_expiry: BTreeMap<u64, Vec<Row>>,
    /// Rows already observed at `cur_ts` (dedups repeated adds within one
    /// time-point); cleared by `advance`.
    #[serde(default)]
    latest_obs: HashSet<Row>,
    /// Timestamp of the most recent `advance` — the anchor for new observations.
    #[serde(default)]
    cur_ts: u64,
    /// Timestamp at which a lagged table was last populated (for the gap check).
    #[serde(default)]
    pub prev_ts: Option<u64>,
}

impl Table {
    pub fn new(name: String, columns: Vec<String>) -> Self {
        let ncols = columns.len();
        Table {
            name,
            columns,
            rows: BTreeSet::new(),
            column_indexes: vec![HashMap::default(); ncols],
            window: None,
            lagged: false,
            active_count: HashMap::default(),
            by_activation: BTreeMap::new(),
            by_expiry: BTreeMap::new(),
            latest_obs: HashSet::default(),
            cur_ts: 0,
            prev_ts: None,
        }
    }

    /// Whether this table uses the sliding-window machinery (metric, non-lagged).
    #[inline]
    fn is_windowed(&self) -> bool {
        self.window.is_some() && !self.lagged
    }

    /// Low-level insert into the active set + indexes.  Returns true if new.
    #[inline]
    fn raw_insert(&mut self, row: Row) -> bool {
        self.ensure_indexes();
        if row.len() != self.columns.len() {
            return false;
        }
        if !self.rows.insert(row.clone()) {
            return false;
        }
        for (i, val) in row.iter().enumerate() {
            self.column_indexes[i].entry(val.clone()).or_default().insert(row.clone());
        }
        true
    }

    /// Low-level removal from the active set + indexes.  Returns true if present.
    #[inline]
    fn raw_remove(&mut self, row: &Row) -> bool {
        self.ensure_indexes();
        if row.len() != self.columns.len() {
            return false;
        }
        if !self.rows.remove(row) {
            return false;
        }
        for (i, val) in row.iter().enumerate() {
            if let Some(bucket) = self.column_indexes[i].get_mut(val) {
                bucket.remove(row);
                if bucket.is_empty() {
                    self.column_indexes[i].remove(val);
                }
            }
        }
        true
    }

    /// Register one active observation of `row` (ref-count++), making it visible.
    #[inline]
    fn activate(&mut self, row: Row) {
        let c = self.active_count.entry(row.clone()).or_insert(0);
        *c += 1;
        if *c == 1 {
            self.raw_insert(row);
        }
    }

    /// Drop one active observation of `row` (ref-count--), hiding it at zero.
    #[inline]
    fn deactivate(&mut self, row: &Row) {
        if let Some(c) = self.active_count.get_mut(row) {
            *c -= 1;
            if *c == 0 {
                self.active_count.remove(row);
                self.raw_remove(row);
            }
        }
    }

    /// Drop every pending activation/expiry for `row` (used by `remove` so a
    /// row withdrawn by a Since `¬φ` clause cannot be resurrected by a stale
    /// scheduled event).
    fn purge_pending(&mut self, row: &Row) {
        for v in self.by_activation.values_mut() { v.retain(|r| r != row); }
        for v in self.by_expiry.values_mut()     { v.retain(|r| r != row); }
        self.by_activation.retain(|_, v| !v.is_empty());
        self.by_expiry.retain(|_, v| !v.is_empty());
    }

    /// Advance a windowed table's clock to `ts`: activate observations that
    /// have entered the lower bound and expire those that have left the upper
    /// bound.  Activations are processed before expiries so an observation
    /// whose whole window is skipped over nets out correctly.  No-op for
    /// non-windowed and lagged tables.
    pub fn advance(&mut self, ts: u64) {
        self.cur_ts = ts;
        self.latest_obs.clear();
        if !self.is_windowed() {
            return;
        }
        // Activations with key ≤ ts.
        let act_keys: Vec<u64> = self.by_activation.range(..=ts).map(|(k, _)| *k).collect();
        for k in act_keys {
            if let Some(rows) = self.by_activation.remove(&k) {
                for row in rows { self.activate(row); }
            }
        }
        // Expiries with key ≤ ts.
        let exp_keys: Vec<u64> = self.by_expiry.range(..=ts).map(|(k, _)| *k).collect();
        for k in exp_keys {
            if let Some(rows) = self.by_expiry.remove(&k) {
                for row in &rows { self.deactivate(row); }
            }
        }
    }

    /// Apply the gap window of a lagged (Prev) table at the current time.  If
    /// the gap to the time-point where it was last populated falls outside
    /// `[a, b]`, hide its rows (it is repopulated afresh each time-point, so
    /// the data is about to be replaced anyway).
    pub fn apply_lag_gap(&mut self, current_ts: u64) {
        let (Some((a, b)), Some(prev)) = (self.window, self.prev_ts) else { return; };
        let gap = current_ts.saturating_sub(prev);
        let in_window = gap >= a && b.map_or(true, |b| gap <= b);
        if !in_window {
            self.clear();
        }
    }

    /// Insert a row.  For windowed (metric, non-lagged) tables this registers
    /// an observation at the current anchor time; for ordinary and lagged
    /// tables it is a plain set insert.  Returns true if the active set changed.
    #[inline]
    pub fn add(&mut self, row: Row) -> bool {
        if !self.is_windowed() {
            return self.raw_insert(row);
        }
        if row.len() != self.columns.len() {
            return false;
        }
        // Dedup repeated adds of the same row within one time-point.
        if !self.latest_obs.insert(row.clone()) {
            return false;
        }
        let (a, b) = self.window.unwrap();
        let t = self.cur_ts;
        let became_active = if a == 0 {
            let newly = !self.active_count.contains_key(&row);
            self.activate(row.clone());
            newly
        } else {
            self.by_activation.entry(t + a).or_default().push(row.clone());
            false
        };
        if let Some(b) = b {
            self.by_expiry.entry(t + b + 1).or_default().push(row);
        }
        became_active
    }

    /// Remove a row.  For windowed tables this withdraws it entirely (drops all
    /// active observations and cancels pending ones).  Returns true if it was
    /// active.
    #[inline]
    pub fn remove(&mut self, row: &Row) -> bool {
        if !self.is_windowed() {
            return self.raw_remove(row);
        }
        self.purge_pending(row);
        self.latest_obs.remove(row);
        if self.active_count.remove(row).is_some() {
            self.raw_remove(row)
        } else {
            false
        }
    }

    /// Number of tuples.
    #[inline]
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    /// Iterate all rows.
    pub fn iter(&self) -> impl Iterator<Item = &Row> {
        self.rows.iter()
    }

    /// Remove all rows (and any pending windowing state).
    #[inline]
    pub fn clear(&mut self) {
        self.ensure_indexes();

        self.rows.clear();
        for idx in &mut self.column_indexes {
            idx.clear();
        }
        self.active_count.clear();
        self.by_activation.clear();
        self.by_expiry.clear();
        self.latest_obs.clear();
    }

    /// Ensure per-column indexes are present and consistent with current rows.
    ///
    /// This repairs tables loaded from older serialized states where
    /// `column_indexes` was absent.
    fn ensure_indexes(&mut self) {
        if self.column_indexes.len() == self.columns.len() {
            return;
        }

        self.column_indexes = vec![HashMap::default(); self.columns.len()];
        for row in &self.rows {
            if row.len() != self.columns.len() {
                continue;
            }
            for (i, val) in row.iter().enumerate() {
                self.column_indexes[i]
                    .entry(val.clone())
                    .or_default()
                    .insert(row.clone());
            }
        }
    }

    /// Retrieve all rows matching equality constraints on a subset of columns.
    ///
    /// Constraints are given as `(column_index, value)` pairs.
    /// Returns cloned rows to keep the API simple and independent from internal index storage.
    pub fn lookup_eq_by_pos(&self, constraints: &[(usize, Value)]) -> Vec<Row> {
        if constraints.is_empty() {
            return self.rows.iter().cloned().collect();
        }

        // Fallback for deserialized/legacy states where indexes may be absent.
        if self.column_indexes.len() != self.columns.len() {
            return self.rows
                .iter()
                .filter(|row| constraints.iter().all(|(col, value)| row.get(*col) == Some(value)))
                .cloned()
                .collect();
        }

        // Validate column indices.
        for (col, _) in constraints {
            if *col >= self.columns.len() {
                return vec![];
            }
        }

        // Pick the most selective bucket as the seed (smallest cardinality).
        let mut seed: Option<&HashSet<Row>> = None;
        for (col, value) in constraints {
            let Some(bucket) = self.column_indexes[*col].get(value) else {
                return vec![];
            };
            seed = match seed {
                None => Some(bucket),
                Some(best) if bucket.len() < best.len() => Some(bucket),
                Some(best) => Some(best),
            };
        }

        let Some(seed_rows) = seed else {
            return vec![];
        };

        seed_rows
            .iter()
            .filter(|row| {
                constraints.iter().all(|(col, value)| row.get(*col) == Some(value))
            })
            .cloned()
            .collect()
    }

    /// Check whether any row satisfies the given equality constraints without
    /// cloning any rows — use this when only existence matters.
    pub fn exists_eq_by_pos(&self, constraints: &[(usize, Value)]) -> bool {
        if constraints.is_empty() {
            return !self.rows.is_empty();
        }

        if self.column_indexes.len() != self.columns.len() {
            return self.rows
                .iter()
                .any(|row| constraints.iter().all(|(col, v)| row.get(*col) == Some(v)));
        }

        for (col, _) in constraints {
            if *col >= self.columns.len() {
                return false;
            }
        }

        let mut seed: Option<&HashSet<Row>> = None;
        for (col, value) in constraints {
            let Some(bucket) = self.column_indexes[*col].get(value) else {
                return false;
            };
            seed = match seed {
                None => Some(bucket),
                Some(best) if bucket.len() < best.len() => Some(bucket),
                Some(best) => Some(best),
            };
        }

        let Some(seed_rows) = seed else { return false; };

        seed_rows
            .iter()
            .any(|row| constraints.iter().all(|(col, v)| row.get(*col) == Some(v)))
    }

    /// Return raw pointers to matching rows without cloning row data.
    ///
    /// Callers hold `&self` immutably for at least as long as the returned
    /// pointers are used — the rows inside a `Table` are never freed while a
    /// shared reference to the table exists, so dereferencing is safe.
    pub fn iter_matching_ptrs(&self, constraints: &[(usize, Value)]) -> Vec<*const Row> {
        if constraints.is_empty() {
            return self.rows.iter().map(|r| r as *const Row).collect();
        }

        if self.column_indexes.len() != self.columns.len() {
            return self.rows
                .iter()
                .filter(|row| constraints.iter().all(|(col, v)| row.get(*col) == Some(v)))
                .map(|r| r as *const Row)
                .collect();
        }

        for (col, _) in constraints {
            if *col >= self.columns.len() {
                return vec![];
            }
        }

        let mut seed: Option<&HashSet<Row>> = None;
        for (col, value) in constraints {
            let Some(bucket) = self.column_indexes[*col].get(value) else {
                return vec![];
            };
            seed = match seed {
                None => Some(bucket),
                Some(best) if bucket.len() < best.len() => Some(bucket),
                Some(best) => Some(best),
            };
        }

        let Some(seed_rows) = seed else { return vec![]; };

        seed_rows
            .iter()
            .filter(|row| constraints.iter().all(|(col, v)| row.get(*col) == Some(v)))
            .map(|r| r as *const Row)
            .collect()
    }

    /// Name-based convenience wrapper around `lookup_eq_by_pos`.
    #[allow(dead_code)]
    pub fn lookup_eq_by_name(&self, constraints: &[(&str, Value)]) -> Vec<Row> {
        let mut by_pos = Vec::with_capacity(constraints.len());
        for (name, value) in constraints {
            let Some(pos) = self.columns.iter().position(|c| c == name) else {
                return vec![];
            };
            by_pos.push((pos, value.clone()));
        }
        self.lookup_eq_by_pos(&by_pos)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Value::Int;

    fn windowed(a: u64, b: Option<u64>) -> Table {
        let mut t = Table::new("T".into(), vec!["x".into()]);
        t.window = Some((a, b));
        t
    }

    // ONCE[0,b]: a tuple is valid from observation until b time units later.
    #[test]
    fn once_upper_bound() {
        let mut t = windowed(0, Some(20));
        t.advance(30);
        t.add(vec![Int(3)]);
        assert!(t.contains(&vec![Int(3)]));      // gap 0
        t.advance(40);
        assert!(t.contains(&vec![Int(3)]));      // gap 10
        t.advance(50);
        assert!(t.contains(&vec![Int(3)]));      // gap 20 (inclusive)
        t.advance(51);
        assert!(!t.contains(&vec![Int(3)]));     // gap 21 → evicted
    }

    // ONCE[a,b] with a>0: a tuple is pre-stored, not yet valid, until the lower
    // bound is reached.
    #[test]
    fn once_lower_bound_prestore() {
        let mut t = windowed(20, Some(40));
        t.advance(30);
        t.add(vec![Int(3)]);
        assert!(!t.contains(&vec![Int(3)]));     // gap 0 < 20: pending
        t.advance(49);
        assert!(!t.contains(&vec![Int(3)]));     // gap 19 < 20
        t.advance(50);
        assert!(t.contains(&vec![Int(3)]));      // gap 20: now valid
        t.advance(70);
        assert!(t.contains(&vec![Int(3)]));      // gap 40 (inclusive)
        t.advance(71);
        assert!(!t.contains(&vec![Int(3)]));     // gap 41 → evicted
    }

    // Unbounded upper (Some(a, None)): once active, valid forever.
    #[test]
    fn once_unbounded_upper() {
        let mut t = windowed(0, None);
        t.advance(10);
        t.add(vec![Int(1)]);
        for ts in [10u64, 1000, 1_000_000] {
            t.advance(ts);
            assert!(t.contains(&vec![Int(1)]));
        }
    }

    // Repeated observations form a union of windows: a later observation keeps
    // the tuple valid past the first observation's expiry.
    #[test]
    fn reobservation_union() {
        let mut t = windowed(0, Some(10));
        t.advance(0);
        t.add(vec![Int(1)]);                     // window [0,10]
        t.advance(5);
        t.add(vec![Int(1)]);                     // window [5,15]
        t.advance(11);
        assert!(t.contains(&vec![Int(1)]));      // first expired, second active
        t.advance(15);
        assert!(t.contains(&vec![Int(1)]));
        t.advance(16);
        assert!(!t.contains(&vec![Int(1)]));     // both expired
    }

    // remove() withdraws a tuple entirely and cancels pending (re)activations,
    // so a scheduled expiry cannot resurrect it (Since `¬φ` semantics).
    #[test]
    fn remove_purges_pending() {
        let mut t = windowed(0, Some(100));
        t.advance(10);
        t.add(vec![Int(1)]);
        assert!(t.contains(&vec![Int(1)]));
        assert!(t.remove(&vec![Int(1)]));
        assert!(!t.contains(&vec![Int(1)]));
        t.advance(50);
        assert!(!t.contains(&vec![Int(1)]));     // not resurrected
    }

    // Same tuple added several times within one time-point counts once.
    #[test]
    fn dedup_within_timepoint() {
        let mut t = windowed(0, Some(5));
        t.advance(0);
        t.add(vec![Int(7)]);
        t.add(vec![Int(7)]);
        t.add(vec![Int(7)]);
        assert!(t.contains(&vec![Int(7)]));
        t.advance(6);
        assert!(!t.contains(&vec![Int(7)]));     // single window, expired together
    }

    // A non-windowed table accumulates as before.
    #[test]
    fn non_windowed_accumulates() {
        let mut t = Table::new("T".into(), vec!["x".into()]);
        t.add(vec![Int(1)]);
        t.add(vec![Int(2)]);
        assert!(t.contains(&vec![Int(1)]));
        assert!(t.contains(&vec![Int(2)]));
        assert_eq!(t.len(), 2);
    }
}
