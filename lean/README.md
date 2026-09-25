# Lean formalization of Enfflash

A Lean 4 / Mathlib formalization of the core of Enfflash (compilation of
MFOTL to EF enforcement programs and their execution) and its correctness,
following the paper *Enfflash: Truly Real-Time Enforcement of First-Order
Temporal Requirements*.  No `sorry`s; the main theorems depend only on
Lean's standard axioms.

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
| `Guards.lean` | §4.2, Fig. 4 | guard extraction `↝`: `GX.sound` (`GEquiv`: equivalence of guarded formulas) (and the original sequential `Guards`, `GXs`) |
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
| `EDG.lean` | Event Dependency Graph (lets decomposed into their events); **`SCCOrder`**: the sections of `Compile(Γ, R, ≺)`, one per SCC in a topological order `≺` (`TopoOrdered`); **`stratified_of_topo`**: such sections are stratified; **`sccOrder_spec`**: an SCC order exists; `stratified_of_rank`, `sccSections` (coarser sections by rank); `once_ok` |
| `Conflict.lean` | what the SMT check must establish (`Exclusive`: `ExclusiveNow` for immediate, `ExclusiveDeferred` for deferred causes) and its soundness despite accumulation of `C`/`S` over iterations: `conflictFree_of_exclusive`, `LoopRun.conflictFree` |
| `Dataflow.lean` | termination when all effects are stable: `stable_terminates` |
| `AggImg.lean` | values produced by aggregations: `aggImg_finite` (finitely many values give finitely many aggregation results), the aggregation closure `aggClo` |
| `DFG.lean` | Data-Flow Graph over argument positions, stable functions given by a finite stability closure (`StabOp`, `Term.stableIn`), non-stable edges through aggregations (`Clause.asrc`, `CloOp`); `dfg_terminates`: no non-stable edge on a cycle ⇒ fixpoint reached; `saturate_terminates` |
| `Clauses.lean` | generated clauses are well-formed (`GoodClause`, **`Rw.good`**, `gate_good`, `lnf_letsWF`), hence the data-flow side conditions hold (`dfClause_of_good`) |
| `Main.lean` | **`enforcer_sound_topo`** (sections in SCC order), `enforcer_sound_analysed`, `enforcer_sound_scc`: compilation correctness with the EDG order and conflict checks as the only assumptions on the program |
| `EndToEnd.lean` | **`enforcement_correct`**: from an MFOTL policy `□φ` through let-normalization, compilation, and the loop program with concrete tables and a terminating `Saturate` (`satFn`, `tableParams_wf`), every output satisfies `□φ` |
| `TypeSystem.lean` | App. A | the type system of EF-MFOTL: `Typ` (`Γ ⊢ φ : α ▷ Δ`), `TypedLets`, `EFMFOTL`; **`typ_iff_rw`** (typing = rewriting), `exS_side_iff`, **`efmfotl_iff_compiles`** (typable iff there is a `Compilation`, with the same clause set) |
| `Examples.lean` | a concrete derivation; counterexample to the original `Since` suppression rule; `φ_law`, `φ_del` (Ex. 2.3) as policies; `φ_agg` with `CNT` (Ex. 2.3); **Example A.4** (`φ_del ∈ EF-MFOTL`, hence compilable) |
| `Paper.lean` | all numbered claims of the paper, in paper order (see `PAPER.md`) |

## Main theorem

```lean
theorem enforcement_correct {Φ : Policy B D} (P : Compiled Φ) (h : P.Checks) :
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
  order `≺` of the SCCs of the EDG (`SCCOrder`; `P.prog` is the program);
* `Compiled.Checks`: the two checks of the paper succeeded: the conflict
  check (`Exclusive`) and the data-flow check
  (`DFGAcyclic` with lets decomposed along `lsrcOf`/`nsrcOf`, for some finite
  stability closure `StabOp` of the stable functions); the well-formedness of
  the generated rules is proved (`Compiled.good`);
* `InputTrace`: an infinite input trace with monotone, progressing timestamps
  and finite databases;
* `enforce P h ρ`: the output of the enforcement loop (concrete tables,
  terminating `Saturate`) on `ρ`;
* `SoundEnforcer φ v₀ E`: every output `E ρ` satisfies `φ` at every
  time-point.

## Modelling choices and scope

* Function applications are semantic (`Term.fn f xs`, `f` reading only its
  support `xs`, `Term.WF`): this models Python functions as total, pure
  functions of their arguments; variables and constants are syntactic.
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
* The conflict check is formalized by the semantic property it must
  establish; Z3's encoding is not formalized.
* Finite traces are handled by causality: `pt_congr` shows the enforced output
  up to the last input does not depend on how the input is continued.

## Issues found (and fixed in the compiler, engine, and paper)

1. **`Since` with `a > 0` was suppressed via its right operand** (Alg. 3 and
   `src/enforceability.ml`).  The witness of `φl S_[a,b] φr` with `a > 0` lies
   strictly in the past, so only the left operand can be falsified now
   (`LBody.supTarget`, `Examples.lean`).  Regression test
   `66_since_lower_sup`.
2. **`NEXT[0,b]` obligations were discharged at the next *real* time-point**
   (`enfflash/src/engine.rs`), possibly much more than `b` time units later,
   and proactive time-points were not counted.  Regression test
   `67_next_bounded`.  Bounded chains of `NEXT` are now rejected by the
   compiler, since their intermediate time-points need not exist.
   Observable change: a due `NEXT` obligation now makes `ν` insert a
   proactive time-point (as in `Loop.lean`), so e.g. in the GDPR benchmark's
   `information` policy, `inform` is caused right after `collect` rather than
   at the next input event.
3. `EVENTUALLY[a,b]` with no effect and `a > 0` (e.g. `EVENTUALLY[5,5] TRUE`)
   was accepted; nothing guarantees a time-point in the interval.
4. `delay 0` obligations created during a proactive cascade were dropped.
5. **The SMT conflict check was unsound for deferred effects**
   (`src/smt_check.ml`): a `delay`/`next` cause and a suppression were
   compared as if evaluated at the same time-point, sharing upstream events.
   E.g. `□∀x. (A(x) → ◇[1,1] E(x)) ∧ (¬A(x) → ¬E(x))` was accepted, and the
   enforcer caused `E(1)` at a time-point where `A(1)` does not hold.  Now no
   symbol is shared for such pairs (`ExclusiveDeferred`).  Regression test
   `68_deferred_conflict`.
6. **`PREVIOUS` tables ignored the enforcer's own actions**
   (`enfflash/src/engine.rs`): lagged tables were filled from the *input*
   events of the previous time-point (ignoring caused/suppressed events) and
   were not advanced at proactive time-points.  E.g. with
   `□(C(x) → ¬●B(x))`, a `B(1)` caused at the previous (reactive or
   proactive) time-point did not prevent `C(1)`.  Regression tests
   `69_prev_proactive`, `70_prev_caused`.
7. **Suppressed events stayed in the working set and in tables**
   (`enfflash/src/engine.rs`): triggers and `SINCE`/`ONCE` tables still saw
   suppressed input events, whereas Algorithm 2 evaluates them on
   `(D∖S)∪C`.  E.g. with `□(¬A(x)) ∧ □(C(x) → ⧫A(x))`, after `A(1)` was
   suppressed, `C(1)` was allowed.  Suppressed events are now removed and
   affected tables are rebuilt from a snapshot.  Regression test
   `71_once_suppressed`; expected outputs of `26_since_sup_lr` and
   `63_since_metric` changed accordingly (fewer, still sufficient
   suppressions).
8. **The data-flow check ignored data flow through lets**
   (`src/dataflow.ml`): nodes were `(event or let name, position)`, with no
   edges from a let's defining atoms to its arguments, so a cycle through a
   let went unnoticed.  E.g. `□∀x. ⧫[0,0] A(x) → A(x+1)` was accepted (while
   `A(x) → A(x+1)` is rejected), and the engine stopped at its iteration cap
   with an output violating the policy.  Lets now contribute edges from the
   atoms producing their tuples to their arguments, non-stable for
   aggregation results (as `lsrcOf`/`nsrcOf` in `TableDeps.lean`).
   Regression test `72_let_cycle`.
9. Paper-only: rule `Vac` (must be `(π,⊥) ↝⁺ (∅,⊥)` and `(π,⊤) ↝⁻ (∅,⊤)`),
   `Guards` starts from `{⊤}` not `⊥`, a typo in the guard lemma, and `μ`/`ν`
   in Alg. 2 (seeding of `next` obligations, `D` vs `∅`, garbled condition);
   sections run in *topological* order of the SCCs (sources first), not
   reverse-topological; the conflict check's treatment of same-SCC atoms and
   deferred effects is now stated explicitly.
