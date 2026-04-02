use std::collections::HashMap;
use crate::ast::*;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Monotonicity {
    Monotone,
    Antimonotone,
    Neither
}

impl Monotonicity {
    pub fn and(&self, other: &Monotonicity) -> Monotonicity {
        match (self, other) {
            (Monotonicity::Monotone, Monotonicity::Monotone) => Monotonicity::Monotone,
            (Monotonicity::Antimonotone, Monotonicity::Antimonotone) => Monotonicity::Antimonotone,
            _ => Monotonicity::Neither,
        }
    }
}

/// Computes the monotonicity of each event in an expression, updating a map: event name → monotonicity.
pub fn compute_filter_monotonicity(
    expr: &FilterExpr,
    monotonicity: &mut HashMap<String, Monotonicity>,
    monotonicities: &HashMap<String, HashMap<String, Monotonicity>>,
    polarity: bool,
) {
    match expr {
        FilterExpr::BoolLit(_) => {}

        FilterExpr::And(l, r) | FilterExpr::Or(l, r) => {
            compute_filter_monotonicity(l, monotonicity, monotonicities, polarity);
            compute_filter_monotonicity(r, monotonicity, monotonicities, polarity);
        }

        FilterExpr::Not(f) => {
            compute_filter_monotonicity(f, monotonicity, monotonicities, !polarity);
        }

        FilterExpr::Compare { .. } => {}

        FilterExpr::TableLookup { name, args: _ } => {
            if let Some(m) = monotonicities.get(name) {
                for (ev, mono) in m {
                    monotonicity
                        .entry(ev.clone())
                        .and_modify(|e| *e = e.and(mono))
                        .or_insert(mono.clone());
                }
            }
            else {
                let mono: &Monotonicity = if polarity { &Monotonicity::Monotone } else { &Monotonicity::Antimonotone };
                monotonicity
                    .entry(name.clone())
                    .and_modify(|e| *e = e.and(mono))
                    .or_insert(mono.clone());
            }
        }
    }
}

/// Computes the monotonicity of each event in a rule. Returns a map: event name → monotonicity.
pub fn compute_rule_monotonicity(
    rule: &RuleDef,
    monotonicities: &HashMap<String, HashMap<String, Monotonicity>>
) -> HashMap<String, Monotonicity> {
    let mut monotonicity = HashMap::new();
    for pat in &rule.trigger.patterns {
        monotonicity.entry(pat.name.clone()).or_insert(Monotonicity::Monotone);
    }
    compute_filter_monotonicity(&rule.trigger.filter, &mut monotonicity, monotonicities, true);
    monotonicity    
}

/// Computes the monotonicity of each event in a table definition. Returns a map: event name → monotonicity.
pub fn compute_table_monotonicity(
    table: &TableDef,
    monotonicities: &HashMap<String, HashMap<String, Monotonicity>>
) -> HashMap<String, Monotonicity> {
    let mut monotonicity = HashMap::new();
    compute_filter_monotonicity(&table.add_clause.filter, &mut monotonicity, monotonicities, true);
    if let Some(remove) = &table.remove_clause {
        compute_filter_monotonicity(&remove.filter, &mut monotonicity, monotonicities, false);
    }
    monotonicity
}

/// Computes the monotonicity of each event in a let definition. Returns a map: event name → monotonicity.
pub fn compute_let_monotonicity(
    let_def: &LetDef,
    monotonicities: &HashMap<String, HashMap<String, Monotonicity>>
) -> HashMap<String, Monotonicity> {    
    let mut monotonicity = HashMap::new();
    compute_filter_monotonicity(&let_def.body, &mut monotonicity, monotonicities, true);
    monotonicity
}