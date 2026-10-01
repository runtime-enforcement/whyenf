# Lean formalization of EnfFlash

A Lean 4 / Mathlib formalization of the core of EnfFlash (compilation of
MFOTL to EF enforcement programs and their execution) and its correctness,
following the paper *Practical Runtime Enforcement of First-Order Temporal
Requirements*.  No `sorry`s; the main theorems depend only on Lean's
standard axioms.  The remaining assumptions are listed in
[Assumptions](#assumptions).

Build: `lake build` (Lean `v4.31.0`, Mathlib `v4.31.0`).

**Checking against the paper:** [`PAPER.md`](PAPER.md) maps every
definition and claim of the paper (section by section) to its Lean
counterpart.
[`Enfflash/Paper.lean`](Enfflash/Paper.lean) restates all numbered lemmas and
theorems in paper order. `python3 scripts/check_paper_md.py` checks that
every Lean name in `PAPER.md` exists and that the claims use only standard
axioms.

## Contents

Definitions:

| File | Paper | Contents |
|---|---|---|
| `MFOTL.lean` | §2.2, §4.1 | MFOTL (`MF`: de Bruijn variables, function terms with support, nested past and future operators, let bindings, aggregations `agg` with operators `AggOp`) and its semantics; the let-normal form `Fm` enforced by the compiler (let-bound predicates, `◇`, `○`), its semantics, let bodies and their meaning (`LetSem`) |
| `EF.lean` | §3 | EF programs: guards, triggers, effects, rules (clauses), sections; semantics: rule firing, `update` and one `Saturate` pass (`step`: the rules in order, as in Algorithm 2), `Saturate` runs (`SatRun`), tables, the enforcement loop's specification (`LoopRun`) |

Let-normalization (§4.1):

| File | Main results |
|---|---|
| `LetNormal.lean` | `norm` translates `MF` to let-normal form: it binds every past subformula, every source let, and every future-free existential to a let over its free variables; **`let_normal_form`** (paper Thm. 4.1: `LNF` and `LetEquiv`), from `norm_correct` (equivalence under the let definitions), `norm_ordered` (lets only refer to earlier lets), **`norm_shape`** (let-normal form: quantifiers in the enforced formula only range over subformulas with future operators), **`norm_presentOps`** (let operands are future-free for `PastPure` policies), `Tr.sat_fv` |

Compilation and its correctness:

| File | Paper | Main results |
|---|---|---|
| `Guards.lean` | §4.2, Fig. 4 | guard extraction `↝`: `GX.sound` (`GEquiv`: equivalence of guarded formulas) |
| `GuardTypes.lean` | §4.2, App. A | declarative guardedness `Grd` (`GRD(x)^p`); **`gx_iff`** (extraction succeeds iff the guards bind `x` or `x` is guarded in the filter); joint guard extraction `GXJ` (the corrected `Guards`, Fig. 5), `GXJ.sound`, **`gxj_iff`** (joint extraction succeeds iff all variables are guarded) |
| `Rewrite.lean` | §4.3, Fig. 6 | rewrite judgement `Rw` (`↪^ℂ`/`↪^𝕊`), `TypeLet` targets; **local soundness** `Rw.sound` |
| `Realize.lean` | §4.4, Alg. 3 | gating by `Cau_p`/`Sup_p`, realizations; `obligations_sound`, `program_sound` |
| `Saturate.lean` | §3.2, Alg. 2 | `saturate_sound` (stratified runs), `once_fixed`, `clause_holds_point`, `fixpoint_exists` |
| `Tables.lean` | §3.2 | `since_table_correct`, `prev_table_correct`, `letSem_of_tables` |
| `Enforcer.lean` | Alg. 1–2, Thm. 4.5 | `LoopRun.clauses_hold`, `enforcer_sound` |
| `Loop.lean` | Alg. 1, `μ`/`ν` of Alg. 2 | **the enforcement loop as a program** (`LoopParams.run`: cursor over the calls `μ(k)`, `ν(τ_k)`, …, `ν(τ_{k+1}-1)`, obligations with timestamp/time-point deadlines, output time-points); `react_reached`, `pro_reached`, `laterFire`, `nextFire`, **`loopRun`** (the loop's output is a `LoopRun`), `outTr_mono`; finite traces: **`run_congr`**, **`pt_congr`**, `before_react` (the loop is causal: the output up to the last input of a finite trace is the same for all its extensions, e.g. with empty inputs, as the engine's final flush) |
| `TableImpl.lean` | Alg. 2 | concrete tables (since stores, lagged rows) and let evaluation in let order; **`tables_compute`**: in the loop's output, the tables compute the lets |
| `TableDeps.lean` | §4.5 | dependencies of the concrete tables: **`tables_letDeps`** (lets only depend on the events `ldOf` defining them, as in the EDG), **`flow`**, **`lv_flow`** (let values, including aggregation results through the non-stable sources `nsrcOf`, are known values or come from the positions `lsrcOf`, computed from the guards of the let operands, as in the DFG), **`tabInv_commit`** (tables stay finite), **`tableParams_wf`** (well-formed loop parameters from properties of the program only) |

Dependency analysis (§4.5) and compilation (§4.6):

| File | Main results |
|---|---|
| `Graph.lean` | finite graphs: the ancestor-count `rank` is monotone along paths and equal only within an SCC (`rank_mono_path`, `rank_eq_path`); the `level` w.r.t. strict edges not on cycles (`level_mono`, `level_strict`) |
| `EDG.lean` | Event Dependency Graph (lets decomposed into their events); **`SCCOrder`**: the sections of `Compile(Γ, R, ≺)`, one per SCC in a topological order `≺` (`TopoOrdered`); **`stratified_of_topo`**: such sections are stratified; **`sccOrder_spec`**: an SCC order exists; `once_ok` |
| `Conflict.lean` | the conflict check on the EDG (`ConflictCheck`: the conflict `query` of every cause/suppress pair of an event, sharing the upstream events `Up`, reported unsatisfiable by a sound SMT solver `SMT`); **`ConflictCheck.exclusive`**: the check establishes `Exclusive` (`ExclusiveNow` for immediate, `ExclusiveDeferred` for deferred causes), via `query_sat`; soundness of `Exclusive` despite accumulation of `C`/`S` over iterations: `conflictFree_of_exclusive`, `LoopRun.conflictFree` |
| `Dataflow.lean` | helpers for the termination argument: active domain, action arguments, finiteness of lists over a finite set (`finite_lists`) |
| `AggImg.lean` | values produced by aggregations: `aggImg_finite` (finitely many values give finitely many aggregation results), the aggregation closure `aggClo` |
| `DFG.lean` | Data-Flow Graph over argument positions, stable functions given by a finite stability closure (`StabOp`, `Term.stableIn`), non-stable edges through aggregations (`Clause.asrc`, `CloOp`); `dfg_terminates`: no non-stable edge on a cycle ⇒ fixpoint reached; `saturate_terminates`; the data-flow check with the compiler's stability labels (`DFGCheck`) and **`DFGCheck.acyclic`**: it establishes `DFGAcyclic` |
| `Clauses.lean` | generated clauses are well-formed (`GoodClause`, **`Rw.good`**, `gate_good`, `lnf_letsWF`), hence the data-flow side conditions hold (`dfClause_of_good`) |
| `EndToEnd.lean` | `enforcer_sound_topo` (compilation correctness for a run of the loop, with sections in SCC order and the conflict check); **`enforcement_correct`**: from an MFOTL policy `□φ` through let-normalization, compilation, and the loop program with concrete tables and a terminating `Saturate` (`satFn`, `tableParams_wf`), every output satisfies `□φ` |
| `TypeSystem.lean` | App. A | the type system of EF-MFOTL: `Typ` (`Γ ⊢ φ : α ▷ Δ`), `TypedLets`, `EFMFOTL`; **`typ_iff_rw`** (typing = rewriting), `exS_side_iff`, **`efmfotl_iff_compiles`** (typable iff there is a `Compilation`, with the same clause set) |
| `Examples.lean` | `φ_law`, `φ_del` (Ex. 2.3) as policies; `φ_agg` with `CNT` (Ex. 2.3); **Example A.4** (`φ_del ∈ EF-MFOTL`, hence compilable) |
| `Paper.lean` | all numbered claims of the paper, in paper order (see `PAPER.md`) |

## Main theorem

```lean
theorem enforcement_correct {Φ : Policy B D} (P : Compiled Φ) {S : SMT PEmpty (QSym B ℕ) D}
    (h : P.Checks S) :
    SoundEnforcer Φ.φ P.v₀ (enforce P h)
```

(`EndToEnd.lean`), where

* `Policy`: a policy `□φ`: well-formed (`MF.WF`), past operators and let
  bodies future-free (`MF.PastPure`); `Φ.χ`, `Φ.Γ` is its let-normal form;
* `Compiled Φ`: the compiler's output: a successful `Compilation` (the same
  notion characterized by the type system in `efmfotl_iff_compiles`: correct
  guards for the let operands (`LetGuards`), a valid realization of the lets,
  and a candidate clause set `C` for `χ` (`Rw`)), plus the rules containing
  `C` and the realization clauses, and their sections along a topological
  order `≺` of the SCCs of the EDG (`SCCOrder`; `P.prog` is the program),
  and the compiler's stability labels `P.stab` (variables, constants,
  applications of functions declared `sfun`);
* `Compiled.Checks S`: the two checks of the paper succeeded, both stated on
  graphs: the conflict check on the EDG (`ConflictCheck`: for every rule
  causing an event and every rule suppressing it, the SMT solver `S` reports
  their conflict query unsatisfiable) and the data-flow check on the DFG
  (`DFGCheck`: no edge labelled non-stable on a cycle, lets decomposed along
  `lsrcOf`/`nsrcOf`); the well-formedness of the generated rules is proved
  (`Compiled.good`);
* `InputTrace`: an infinite input trace with monotone, progressing timestamps
  and finite databases;
* `enforce P h ρ`: the output of the enforcement loop (concrete tables,
  terminating `Saturate`) on `ρ`;
* `SoundEnforcer φ v₀ E`: every output `E ρ` satisfies `φ` at every
  time-point.

## Modelling choices

* Function applications are semantic (`Term.fn f xs`, `f` reading only its
  support `xs`, `Term.WF`); variables and constants are syntactic.
* Aggregations `ȳ ← ω(t̄; ḡ) φ` (`MF.agg`) are formalized throughout: an
  aggregation operator (`AggOp`) maps the multiset of rows (multiplicities
  `List D → ℕ∞`) to finitely many result rows; an aggregation holds only for
  non-empty groups (as computed by EF's `agg let`); let-normalization binds
  aggregations to lets (`LBody.agg`), evaluated directly on the working set;
  their operands must be guarded (except the results), and their results
  are non-stable in the data-flow graph.  User-defined table operators
  (`tfun`) are aggregation operators.
* Let-normal form binds future-free existentials to lets; existentials over
  subformulas with future operators stay in the enforced formula (they cannot
  be evaluated by tables; the compiler handles them by rewriting).
* The conflict query (`query`) is the conjunction of the two triggers, each
  over its own copy of the variables and predicates, sharing only the events
  upstream of the section in the EDG (`Up`; nothing for a deferred cause),
  and of the equality of the two effects' arguments.
* The DFG's stability labels (`Compiled.stab`) are syntactic: they mark
  variables, constants and applications of `sfun`s.  That these terms are
  indeed stable is the trusted assumption (2) below.

## Assumptions

`enforcement_correct` is proved without `sorry` and without axioms beyond
Lean's standard ones (`propext`, `Classical.choice`, `Quot.sound`).  What it
relies on falls into four groups.

**Trusted (hypotheses of the theorem).**

1. *The SMT solver* (`SMT`, the parameter `S` of `Checks`): a formula it
   reports unsatisfiable has no model (`SMT.sound`).  It is only consulted for
   conflict queries, i.e. for events that are both caused (immediately or
   later) and suppressed.
2. *The user's `sfun` declarations* (`Compiled.stab_sound`): the terms the
   compiler labels stable (variables, constants, applications of functions
   declared `sfun`) are stable for some stability closure, i.e. applying them
   repeatedly to finitely many values yields finitely many values.

**Checked by the compiler (hypotheses `Checks`, stated on graphs).**

3. *The conflict check on the EDG* (`ConflictCheck`): for every rule causing
   an event and every rule suppressing it, the solver reports their conflict
   query unsatisfiable.  `ConflictCheck.exclusive` proves that this
   establishes the semantic property used by the soundness proof
   (`Exclusive`).
4. *The data-flow check on the DFG* (`DFGCheck`): no edge labelled
   non-stable lies on a cycle.  `DFGCheck.acyclic` proves that, with (2), this
   establishes the termination criterion (`DFGAcyclic`).

**Produced by the compiler (hypothesis `Compiled`, specified, not
implemented).**

5. *A compilation exists* (`Compilation`, characterized by the type system:
   `efmfotl_iff_compiles`), and the program's rules are exactly its clauses,
   grouped into one section per SCC of the EDG in topological order
   (`SCCOrder`).  The compiler's search (`Generate`, `Realizations`, Tarjan's
   algorithm) is specified by these outputs; an SCC order always exists
   (`sccOrder_spec`).  The well-formedness of the generated rules is proved
   (`Compiled.good`), not assumed.

**Not formalized (gap between the formalization and the implementation).**

* The OCaml compiler and the Rust engine are not verified: the formalization
  proves the algorithms (compilation, Algorithms 1 and 2 with concrete
  tables), not their code.  The concrete EF syntax, its parser, and the
  output format are not formalized.
* The translation of the conflict query into Z3's input
  (`src/smt_check.ml`).  It replaces quantifiers, temporal subformulas and
  aggregations by fresh Booleans and gives unknown functions uninterpreted
  symbols, which only adds models; hence an `unsat` answer for the translated
  query implies that the formalized `query` is unsatisfiable.  This argument
  is informal.
* Functions are semantic, total and pure (`Term.fn`, `Term.WF`): Python
  functions are assumed to terminate, not to fail, and to depend only on
  their arguments.
* Traces are infinite; finite traces are covered by causality
  (`LoopParams.pt_congr`: the output up to the last input does not depend on
  how the input continues).
* The complexity results (§3.3) and the evaluation (§5) are not formalized.

