//! EDG-ordered clause sections for enforcement-time evaluation.
//!
//! The enforcement fixpoint used to re-evaluate *every* rule each iteration
//! until nothing new appeared (a single blanket loop).  Instead we precompute,
//! once at engine construction, a dependency order over the rules:
//!
//!   * Build the rule dependency graph: an edge `i -> j` whenever the event
//!     produced by rule `i` can appear in the trigger of rule `j` (directly, or
//!     transitively through a let-definition / table the trigger references).
//!   * Contract its strongly-connected components (Tarjan) and topologically
//!     order them.  Each SCC becomes a [`Section`].
//!   * A section with a single rule and no self-dependency runs **once**; a
//!     larger SCC, or a self-recursive rule, is a **fixpoint section** iterated
//!     locally until it stabilises.
//!
//! Processing sections in this order means an influencing rule is always
//! evaluated before the rules it feeds, so most rules need only a single pass.

use std::collections::{HashMap, HashSet};
use crate::ast::*;

#[derive(Debug, Clone)]
pub struct Section {
    /// Indices into `program.rules`, to be evaluated together.
    pub rules: Vec<usize>,
    /// Whether this section must be iterated to a local fixpoint.
    pub recursive: bool,
}

/// Predicate names referenced by a clause (event patterns + table lookups).
fn clause_pred_names(clause: &Clause, out: &mut HashSet<String>) {
    for conj in &clause.patterns {
        for g in conj {
            if let GuardPattern::Event(ep) = g {
                out.insert(ep.name.clone());
            }
        }
    }
    filter_pred_names(&clause.filter, out);
}

fn filter_pred_names(f: &FilterExpr, out: &mut HashSet<String>) {
    match f {
        FilterExpr::TableLookup { name, .. } => { out.insert(name.clone()); }
        FilterExpr::And(a, b) | FilterExpr::Or(a, b) => {
            filter_pred_names(a, out);
            filter_pred_names(b, out);
        }
        FilterExpr::Not(a) => filter_pred_names(a, out),
        _ => {}
    }
}

/// Transitively add the names reachable from `name` through `ref_map`.
fn expand(name: &str, ref_map: &HashMap<String, HashSet<String>>, acc: &mut HashSet<String>) {
    if let Some(refs) = ref_map.get(name) {
        for r in refs {
            if acc.insert(r.clone()) {
                expand(r, ref_map, acc);
            }
        }
    }
}

/// Tarjan's SCC. Returns `(scc_count, scc_of)`.
fn tarjan(n: usize, adj: &[Vec<usize>]) -> (usize, Vec<usize>) {
    let mut index = vec![usize::MAX; n];
    let mut lowlink = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut scc_of = vec![usize::MAX; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut counter = 0usize;
    let mut n_sccs = 0usize;

    // iterative DFS to avoid blowing the call stack on large policies
    // frame: (vertex, next successor index)
    for start in 0..n {
        if index[start] != usize::MAX { continue; }
        let mut work: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(&(v, ci)) = work.last() {
            if ci == 0 {
                index[v] = counter;
                lowlink[v] = counter;
                counter += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            if ci < adj[v].len() {
                let w = adj[v][ci];
                work.last_mut().unwrap().1 += 1;
                if index[w] == usize::MAX {
                    work.push((w, 0));
                } else if on_stack[w] {
                    lowlink[v] = lowlink[v].min(index[w]);
                }
            } else {
                if lowlink[v] == index[v] {
                    loop {
                        let w = stack.pop().unwrap();
                        on_stack[w] = false;
                        scc_of[w] = n_sccs;
                        if w == v { break; }
                    }
                    n_sccs += 1;
                }
                work.pop();
                if let Some(&(p, _)) = work.last() {
                    lowlink[p] = lowlink[p].min(lowlink[v]);
                }
            }
        }
    }
    (n_sccs, scc_of)
}

/// Compute the EDG-ordered sections for a program, grouped into waves.
/// The fallback (no .ef markers) wraps each section in its own single-element
/// wave (no wave-level parallelism, but the correct type for the engine).
pub fn compute_sections(program: &Program) -> Vec<Vec<Section>> {
    let rules = &program.rules;
    let n = rules.len();
    if n == 0 { return Vec::new(); }

    // Escape hatch: single recursive section, each in its own wave.
    if std::env::var("ENFFLASH_NO_SECTIONS").is_ok() {
        return vec![vec![Section { rules: (0..n).collect(), recursive: true }]];
    }

    // name -> names referenced by its definition (let-defs and tables)
    let mut ref_map: HashMap<String, HashSet<String>> = HashMap::new();
    for ld in &program.let_defs {
        let e = ref_map.entry(ld.name.clone()).or_default();
        clause_pred_names(&ld.clause, e);
    }
    for td in &program.tables {
        let mut s = HashSet::new();
        clause_pred_names(&td.add_clause, &mut s);
        if let Some(rc) = &td.remove_clause { clause_pred_names(rc, &mut s); }
        ref_map.entry(td.name.clone()).or_default().extend(s);
    }

    // expanded trigger-name set per rule
    let trig_names: Vec<HashSet<String>> = rules.iter().map(|r| {
        let mut direct = HashSet::new();
        clause_pred_names(&r.trigger, &mut direct);
        let mut full = direct.clone();
        for nm in &direct { expand(nm, &ref_map, &mut full); }
        full
    }).collect();

    // event name -> rules producing it
    let mut producers: HashMap<&str, Vec<usize>> = HashMap::new();
    for (i, r) in rules.iter().enumerate() {
        producers.entry(r.event.as_str()).or_default().push(i);
    }

    // edges i -> j when rules[i].event occurs in trigger of rule j
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut self_loop = vec![false; n];
    for j in 0..n {
        for nm in &trig_names[j] {
            if let Some(ps) = producers.get(nm.as_str()) {
                for &i in ps {
                    if i == j { self_loop[j] = true; }
                    else { adj[i].push(j); }
                }
            }
        }
    }
    for a in adj.iter_mut() { a.sort_unstable(); a.dedup(); }

    let (scc_count, scc_of) = tarjan(n, &adj);

    // group rules by SCC
    let mut scc_rules: Vec<Vec<usize>> = vec![Vec::new(); scc_count];
    for i in 0..n { scc_rules[scc_of[i]].push(i); }

    // condensation DAG + indegrees
    let mut cond_adj: Vec<HashSet<usize>> = vec![HashSet::new(); scc_count];
    let mut indeg = vec![0usize; scc_count];
    for i in 0..n {
        for &j in &adj[i] {
            let (a, b) = (scc_of[i], scc_of[j]);
            if a != b && cond_adj[a].insert(b) { indeg[b] += 1; }
        }
    }

    // Kahn topological order (influencers before influenced)
    let mut order: Vec<usize> = Vec::with_capacity(scc_count);
    let mut queue: Vec<usize> = (0..scc_count).filter(|&s| indeg[s] == 0).collect();
    let mut placed = vec![false; scc_count];
    while let Some(s) = queue.pop() {
        if placed[s] { continue; }
        placed[s] = true;
        order.push(s);
        for &t in &cond_adj[s] {
            indeg[t] -= 1;
            if indeg[t] == 0 { queue.push(t); }
        }
    }
    // defensive: append any SCC not reached (shouldn't happen for a DAG)
    for s in 0..scc_count { if !placed[s] { order.push(s); } }

    order.into_iter().map(|s| {
        let rs = std::mem::take(&mut scc_rules[s]);
        let recursive = rs.len() > 1 || rs.iter().any(|&i| self_loop[i]);
        vec![Section { rules: rs, recursive }]
    }).collect()
}
