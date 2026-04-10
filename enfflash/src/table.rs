/// Runtime tables backed by BTreeSet for logarithmic access.

use std::collections::BTreeSet;
use crate::ast::Value;

/// A row is a vector of values (positional, matching column order).
pub type Row = Vec<Value>;

#[derive(Debug, Clone)]
pub struct Table {
    pub name: String,
    /// Column names + types (for debugging / display).
    pub columns: Vec<String>,
    /// The actual data: a sorted set of rows (log-time lookup).
    pub rows: BTreeSet<Row>,
}

impl Table {
    pub fn new(name: String, columns: Vec<String>) -> Self {
        Table {
            name,
            columns,
            rows: BTreeSet::new(),
        }
    }

    /// Insert a row. Returns true if it was actually new.
    #[inline]
    pub fn add(&mut self, row: Row) -> bool {
        self.rows.insert(row)
    }

    /// Remove a row. Returns true if it existed.
    #[inline]
    pub fn remove(&mut self, row: &Row) -> bool {
        self.rows.remove(row)
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
        self.rows.clear();
    }
}
