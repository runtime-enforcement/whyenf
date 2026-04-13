/// AST types for enfflash programs and logs.

use std::fmt;
use std::collections::HashSet;
use serde::{Serialize, Deserialize};

// ─── Value types ─────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash, Serialize, Deserialize)]
pub enum Value {
    Int(i64),
    Float(OrderedFloat),
    Str(String),
    Bool(bool),
}

/// Wrapper for f64 that implements Eq + Ord (total order, NaN == NaN).
#[derive(Debug, Clone, Copy)]
pub struct OrderedFloat(pub f64);

impl PartialEq for OrderedFloat {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}
impl Eq for OrderedFloat {}

impl PartialOrd for OrderedFloat {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for OrderedFloat {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.total_cmp(&other.0)
    }
}
impl std::hash::Hash for OrderedFloat {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Serialize for OrderedFloat {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_f64(self.0)
    }
}
impl<'de> Deserialize<'de> for OrderedFloat {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let v = f64::deserialize(deserializer)?;
        Ok(OrderedFloat(v))
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{}", i),
            Value::Float(OrderedFloat(v)) => write!(f, "{}", v),
            Value::Str(s) => write!(f, "\"{}\"", s),
            Value::Bool(b) => write!(f, "{}", b),
        }
    }
}

// ─── Types ───────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Ty {
    Int,
    Float,
    Str,
    Bool,
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Int => write!(f, "int"),
            Ty::Float => write!(f, "float"),
            Ty::Str => write!(f, "str"),
            Ty::Bool => write!(f, "bool"),
        }
    }
}

// ─── Log ─────────────────────────────────────────────────────────────────────

/// A single event instance, e.g. `Login("alice", 42)`
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EventInstance {
    pub name: String,
    pub args: Vec<Value>,
}

impl fmt::Display for EventInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.name)?;
        for (i, a) in self.args.iter().enumerate() {
            if i > 0 { write!(f, ", ")?; }
            write!(f, "{}", a)?;
        }
        write!(f, ")")
    }
}

impl EventInstance {
    /// Produce a JSON representation matching the OCaml `Event.to_json` format:
    /// `{ "name": "...", "args": [ ... ] }`
    pub fn to_json(&self) -> String {
        let args: Vec<String> = self.args.iter().map(|a| format!("{}", a)).collect();
        format!("{{ \"name\": \"{}\", \"args\": [ {} ] }}", self.name, args.join(", "))
    }
}

/// One time‐point in the log: timestamp + events.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimePoint {
    pub timestamp: u64,
    pub events: Vec<EventInstance>,
}

// ─── Program AST ─────────────────────────────────────────────────────────────

/// Top‐level program.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Program {
    pub event_decls: Vec<EventDecl>,
    pub fun_decls: Vec<FunDecl>,
    pub let_defs: Vec<LetDef>,
    pub tables: Vec<TableDef>,
    pub rules: Vec<RuleDef>,
    /// Interleaved order of tables and let-defs for correct evaluation
    pub items: Vec<ProgramItem>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EventDecl {
    pub name: String,
    pub param_types: Vec<Ty>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunDecl {
    pub name: String,
    pub param_names: Vec<String>,
    pub param_types: Vec<Ty>,
    pub ret_type: Ty,
    /// Python source code body (between { })
    pub body: String,
}

// ─── Let definitions ─────────────────────────────────────────────────────────

/// Named boolean predicate: `let Name(x:type, ...) := { expr }`
/// If `is_filter` is true, this is a `filter let` — it has no event guards
/// and can only be used as a filter condition, not as a guard that binds variables.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LetDef {
    pub label: Option<String>,
    pub is_filter: bool,
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub clause: Clause,
}

/// Helper for parsing interleaved tables, rules and let definitions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProgramItem {
    Table(TableDef),
    Rule(RuleDef),
    Let(LetDef),
}

// ─── Patterns & Expressions ──────────────────────────────────────────────────

/// Pattern that matches against events, e.g. `Login(x, y) & Access(x, z)`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EventPattern {
    pub name: String,
    pub args: Vec<PatternArg>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PatternArg {
    Var(String),
    Literal(Value),
    Wildcard,
}

/// A guard element: either an event pattern or an equality constraint (var == const).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum GuardPattern {
    Event(EventPattern),
    EqConst(String, Value),
}

/// Boolean filter expression (used after `if`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FilterExpr {
    /// true / false literal
    BoolLit(bool),
    /// Reference to a table: `TableName(expr, expr, ...)`
    TableLookup { name: String, args: Vec<TermExpr> },
    /// Comparison: `x == 42`, `x != y`, `x < 3`, etc.
    Compare {
        lhs: TermExpr,
        op: CmpOp,
        rhs: TermExpr,
    },
    And(Box<FilterExpr>, Box<FilterExpr>),
    Or(Box<FilterExpr>, Box<FilterExpr>),
    Not(Box<FilterExpr>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub enum TermExpr {
    Var(String),
    Lit(Value),
    FunCall { name: String, args: Vec<TermExpr> },
}

impl TermExpr {
    pub fn fvs(self) -> HashSet<String> {
        return match self {
            TermExpr::Var(s) => HashSet::from([s]),
            TermExpr::Lit(_) => HashSet::new(),
            TermExpr::FunCall { name: _, args} => {
                let mut vars = HashSet::new();
                for arg in args {
                    for var in arg.fvs() {
                        vars.insert(var);
                    }
                }
                vars
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CmpOp {
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
}

// ─── Display implementations for expressions ─────────────────────────────────

impl fmt::Display for TermExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermExpr::Var(name) => write!(f, "{}", name),
            TermExpr::Lit(v) => write!(f, "{}", v),
            TermExpr::FunCall { name, args } => {
                write!(f, "{}(", name)?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", a)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for CmpOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CmpOp::Eq => write!(f, "=="),
            CmpOp::Neq => write!(f, "!="),
            CmpOp::Lt => write!(f, "<"),
            CmpOp::Le => write!(f, "<="),
            CmpOp::Gt => write!(f, ">"),
            CmpOp::Ge => write!(f, ">="),
        }
    }
}

impl fmt::Display for FilterExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FilterExpr::BoolLit(b) => write!(f, "{}", b),
            FilterExpr::TableLookup { name, args } => {
                write!(f, "{}(", name)?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", a)?;
                }
                write!(f, ")")
            }
            FilterExpr::Compare { lhs, op, rhs } => write!(f, "{} {} {}", lhs, op, rhs),
            FilterExpr::And(l, r) => write!(f, "({} ∧ {})", l, r),
            FilterExpr::Or(l, r) => write!(f, "({} ∨ {})", l, r),
            FilterExpr::Not(inner) => write!(f, "¬{}", inner),
        }
    }
}

impl fmt::Display for PatternArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternArg::Var(name) => write!(f, "{}", name),
            PatternArg::Literal(v) => write!(f, "{}", v),
            PatternArg::Wildcard => write!(f, "_"),
        }
    }
}

impl fmt::Display for EventPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.name)?;
        for (i, a) in self.args.iter().enumerate() {
            if i > 0 { write!(f, ", ")?; }
            write!(f, "{}", a)?;
        }
        write!(f, ")")
    }
}

impl fmt::Display for GuardPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GuardPattern::Event(ep) => write!(f, "{}", ep),
            GuardPattern::EqConst(var, val) => write!(f, "{}={}", var, val),
        }
    }
}

// ─── Table definitions ───────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TableDef {
    pub label: Option<String>,
    pub lagged: bool,
    pub name: String,
    pub columns: Vec<(String, Ty)>,
    pub add_clause: Clause,
    pub remove_clause: Option<Clause>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Clause {
    /// Disjunction of conjunctions: each inner Vec is an AND of guard patterns,
    /// the outer Vec is an OR of those conjunctions.
    pub patterns: Vec<Vec<GuardPattern>>,
    pub filter: FilterExpr,
}

// ─── Rule definitions ────────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuleDef {
    pub label: Option<String>,
    pub event: String,
    pub params: Vec<TermExpr>,
    pub action: RuleAction,
    pub delay: Option<u64>,
    pub tp_offset: Option<u64>,
    pub trigger: Clause,
    pub validate: Option<FilterExpr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RuleAction {
    Cause,    // +
    Suppress, // -
    Observe,  // none
}
