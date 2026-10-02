# Lean formalization of EnfFlash

A Lean 4 / Mathlib formalization of the core of EnfFlash (compilation of
MFOTL to EF enforcement programs and their execution) and its correctness,
following the paper *Practical Runtime Enforcement of First-Order Temporal
Requirements*.  No `sorry`s; the main theorems depend only on Lean's
standard axioms.  The remaining assumptions are listed in
[Assumptions](#assumptions).

**Scope.** The pipeline is formalized end to end: let-normalization, the
compiler (Algorithms 3 and 4, `compile`), the two static checks, and the
enforcement loop running the EF program (Algorithms 1 and 2); the gaps to
the implementation are listed under [Assumptions](#assumptions).  Not proved:
*completeness*, i.e. that the compiler succeeds on every policy in EF-MFOTL.
The compiler is a mathematical definition, not executable code
(`noncomputable`); where the compilation rules leave a choice, it makes a
fixed one, which need not coincide with the OCaml compiler's.

Build: `lake build` (Lean `v4.31.0`, Mathlib `v4.31.0`).

**Checking against the paper:** [`PAPER.md`](PAPER.md) maps the
definitions and claims of the paper (section by section) to their Lean
counterparts, and marks what is only specified or not formalized.
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
| `Compile.lean` | the compiler as functions (Algorithms 3 and 4): guard extraction **`gx`**, **`gxj`**, rewriting **`rw`**, `TypeLet` (**`gdOf`**, **`realOf`**), **`compilations`**, **`compile`**; their soundness (`gx_sound`, `gxj_sound`, `rw_sound`, `letGuards_ok`, `realOf_valid`) **`compile_sound`**, the pipeline **`enfflash`** and the end-to-end theorem **`enforcement_correct`** |
| `CompileExample.lean` | **`compile_phiDel`**: on Example A.4, `compile` returns the paper's program |
| `Items.lean` | EF items (`Item`: `let`/`filter let`, `table` with window and `add`/`remove` clauses, `lagged table`, `agg let`), `rows` (`{v↾x̄ ∣ v ∈ ⟦c⟧_R}`), `eval` (`Eval`), `interp` (`Interp`), `updateTables` (table updates of `Saturate`); the items of the lets (`items`, `itemOf`); **`interp_eq`**, **`updateTables_eq`**, **`itemParams_eq`**: the loop running the items is the loop with concrete tables |
| `EndToEnd.lean` | `enforcer_sound_topo` (compilation correctness for a run of the loop, with sections in SCC order and the conflict check); **`compiled_sound`**: from an MFOTL policy `□φ` through let-normalization, compilation, and the loop running the EF program (`enforce`, `Compiled.efParams`) with a terminating `Saturate` (`satFn`, `tableParams_wf`), every output satisfies `□φ` |
| `TypeSystem.lean` | App. A | the type system of EF-MFOTL: `Typ` (`Γ ⊢ φ : α ▷ Δ`), `TypedLets`, `EFMFOTL`; **`typ_iff_rw`** (typing = rewriting), `exS_side_iff`, **`efmfotl_iff_compiles`** (typable iff there is a `Compilation`, with the same clause set) |
| `Examples.lean` | `φ_law`, `φ_del` (Ex. 2.3) as policies; `φ_agg` with `CNT` (Ex. 2.3); **Example A.4** (`φ_del ∈ EF-MFOTL`, hence compilable) |
| `Paper.lean` | all numbered claims of the paper, in paper order (see `PAPER.md`) |

## Main theorem

```lean
theorem enforcement_correct (Φ : Policy B D) (S₀ : Sig B ℕ D) (v₀ : ℕ → D)
    (stab : Term D → Prop)
    (hstab : ∃ Stab : Set D → Set D, StabOp Stab ∧ ∀ t, stab t → t.stableIn Stab)
    (S : SMT PEmpty (QSym B ℕ) D) {E : InputTrace B D → Tr B ℕ D}
    (hE : enfflash Φ S₀ v₀ stab hstab S = some E) :
    SoundEnforcer Φ.φ v₀ E
```

(`Compile.lean`; paper Theorem 4.5): if EnfFlash returns an enforcer `E` for
the policy `□φ`, then on every input trace (`InputTrace`: monotone,
progressing timestamps, finite databases) the output of `E` satisfies `□φ`
(`SoundEnforcer`).  `enfflash` compiles the policy (`compile`), keeps the
first program that passes the two checks of Section 4.5, and runs it.  The
inputs are the policy, the signature `S₀` (which events may be caused or
suppressed), a default valuation `v₀`, the user's stability labels `stab`
(`sfun`), and an SMT solver `S`.

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

The theorem uses no axioms beyond Lean's standard ones (`propext`,
`Classical.choice`, `Quot.sound`).  It trusts two components:

1. *The SMT solver* `S`, used by the conflict check: a formula it reports
   unsatisfiable has no model (`SMT.sound`).
2. *The user's `sfun` declarations*, used by the data-flow check: the terms
   labelled stable yield finitely many values when applied repeatedly to
   finitely many values (`hstab`).

**Not formalized (gap between the formalization and the implementation).**

* The OCaml compiler and the Rust engine are not verified: the formalization
  proves the algorithms, not their code.  The concrete EF text syntax and its
  parser are not formalized.
* The clauses of tables and lets are those of guard extraction (guards and
  residual filter), simplified as in the compiler (`Fm.simp`: `⊤`
  conjuncts and double negations dropped); e.g. the table `Since1` of
  Figure 2 gets exactly `add {consent(u,c)}` and `remove {revoke(u,c)}`
  (`since1_clauses`).  The compiler's other rewrites of filters (e.g. pushing
  the negation of a `remove` filter through `∧`/`∨`) are not reproduced, and
  the filters of rules are not simplified (e.g. `⊤ ∧ ⊤` in Example A.4).
* The translation of the conflict query into Z3's input
  (`src/smt_check.ml`), which only adds models (quantifiers and temporal
  subformulas become fresh Booleans); that an `unsat` answer carries over is
  argued informally.
* Functions are semantic, total and pure: Python functions are assumed to
  terminate, not to fail, and to depend only on their arguments.
* Traces are infinite; finite traces are covered by causality
  (`LoopParams.pt_congr`).
* The complexity results (§3.3) and the evaluation (§5) are not formalized.
