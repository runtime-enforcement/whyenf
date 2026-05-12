/// Runtime tables backed by BTreeSet plus per-column hash indexes.

use std::collections::{BTreeSet, HashMap};
use serde::{Serialize, Deserialize};
use crate::ast::Value;

/// A row is a vector of values (positional, matching column order).
pub type Row = Vec<Value>;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Table {
    pub name: String,
    /// Column names + types (for debugging / display).
    pub columns: Vec<String>,
    /// The actual data: a sorted set of rows (log-time lookup).
    pub rows: BTreeSet<Row>,
    /// Per-column index: for each column i, map value -> set of rows with row[i] = value.
    ///
    /// This supports efficient subset-equality lookups such as:
    ///   col1 = v1, col3 = v3
    #[serde(skip, default)]
    pub column_indexes: Vec<HashMap<Value, BTreeSet<Row>>>,
}

impl Table {
    pub fn new(name: String, columns: Vec<String>) -> Self {
        let ncols = columns.len();
        Table {
            name,
            columns,
            rows: BTreeSet::new(),
            column_indexes: vec![HashMap::new(); ncols],
        }
    }

    /// Insert a row. Returns true if it was actually new.
    #[inline]
    pub fn add(&mut self, row: Row) -> bool {
        self.ensure_indexes();

        if row.len() != self.columns.len() {
            return false;
        }

        let inserted = self.rows.insert(row.clone());
        if !inserted {
            return false;
        }

        for (i, val) in row.iter().enumerate() {
            self.column_indexes[i]
                .entry(val.clone())
                .or_default()
                .insert(row.clone());
        }

        true
    }

    /// Remove a row. Returns true if it existed.
    #[inline]
    pub fn remove(&mut self, row: &Row) -> bool {
        self.ensure_indexes();

        if row.len() != self.columns.len() {
            return false;
        }

        let removed = self.rows.remove(row);
        if !removed {
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

    /// Check membership (O(log n)).
    #[inline]
    pub fn contains(&self, row: &Row) -> bool {
        self.rows.contains(row)
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

    /// Remove all rows.
    #[inline]
    pub fn clear(&mut self) {
        self.ensure_indexes();

        self.rows.clear();
        for idx in &mut self.column_indexes {
            idx.clear();
        }
    }

    /// Ensure per-column indexes are present and consistent with current rows.
    ///
    /// This repairs tables loaded from older serialized states where
    /// `column_indexes` was absent.
    fn ensure_indexes(&mut self) {
        if self.column_indexes.len() == self.columns.len() {
            return;
        }

        self.column_indexes = vec![HashMap::new(); self.columns.len()];
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
        let mut seed: Option<&BTreeSet<Row>> = None;
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
