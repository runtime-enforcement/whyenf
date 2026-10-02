# Paper ↔ Lean map

This file maps the definitions and claims of the paper *Practical Runtime
Enforcement of First-Order Temporal Requirements* to the Lean 4
formalization in this directory. It covers every section except the complexity results (§3.3)
and the evaluation (§5). The assumptions of the main theorem are summarized in
[Assumptions](#assumptions) at the end.

**Scope.** The pipeline is formalized end to end: let-normalization, the
compiler (Algorithms 3 and 4, `compile`), the two static checks, and the
enforcement loop running the EF program (Algorithms 1 and 2); the gaps to
the implementation are listed under [Assumptions](#assumptions).  Not proved:
*completeness*, i.e. that the compiler succeeds on every policy in EF-MFOTL.
The compiler is a mathematical definition, not executable code
(`noncomputable`); where the compilation rules leave a choice, it makes a
fixed one, which need not coincide with the OCaml compiler's.

## How to check

```sh
cd lean
lake build                          # builds everything; there is no `sorry`
python3 scripts/check_paper_md.py   # every Lean name below exists; claims use only standard axioms
```

* **[`Enfflash/Paper.lean`](Enfflash/Paper.lean)** restates every numbered
  lemma and theorem, in paper order and in the paper's vocabulary (`thm_4_1`,
  `lem_4_2`, …, `thm_A_3`). Each one is proved by a one-line reference to the
  development, so the statements can be compared with the paper in one place.
* The tables below give, for each paper concept, the Lean declaration and how
  it differs. The script checks that every name in the **Lean** column exists.
* All claims depend only on `propext`, `Classical.choice` and `Quot.sound`.

Legend for the notes column:

| Mark | Meaning |
|---|---|
| ✅ | formalized as in the paper |
| ≈ | formalized, with the modelling difference described |
| — | not formalized (out of scope) |

---

## §2 Runtime enforcement

### §2.1 Traces

| Paper | Lean | Notes |
|---|---|---|
| event names `𝔼`, arity `ι` | `Ev` | ≈ base event names are a type parameter `B`. `Ev B L` adds the obligation events `Cau_p`/`Sup_p` of the lets `p : L`. Base-event arities are not tracked: argument lists have any length. |
| event `(e, d̄)`, database `𝔻` | `DB` | ✅ `DB B L D = Set (Ev B L × List D)`. Finiteness is `Set.Finite`. |
| `𝔻_E` (databases over `E ⊆ 𝔼`) | `Sig` | ≈ not defined separately. Only events in `Sig.cau`/`Sig.sup` are caused or suppressed (rules `Rw.evC`/`Rw.evS`). |
| trace `σ = (τ_i, D_i)_i`: monotone, progressing | `Tr`, `InputTrace` | ≈ `Tr` is an infinite trace (`db`, `ts`) that also carries the interpretation `lv` of let-bound predicates. Monotonicity, progress and finite databases are the fields of `InputTrace`; outputs are monotone by `LoopParams.outTr_mono`. |
| finite traces | `LoopParams.pt_congr`, `LoopParams.before_react` | ≈ causality: the output produced while reading the first `N` inputs does not depend on later inputs. The output for a finite trace is therefore a prefix of the output for any infinite extension of it. |
| time-point | — | indices `i : ℕ` |
| Example 2.1 | `Examples.Ev0` | ✅ the event names |
| Example 2.2 | — | — |

### §2.2 MFOTL

| Paper | Lean | Notes |
|---|---|---|
| terms `x ∣ c ∣ f(t̄)`, `⟦t⟧_v` | `Term`, `Term.eval`, `Term.WF` | ≈ variables are de Bruijn indices. A function application `Term.fn f xs` is *semantic*: a total function of the valuation that reads only its support `xs` (`Term.WF`). This models `fun` as pure total functions. |
| syntax of `φ` | `MF` | ≈ constructors `tt`, `pred` (event), `upred` (let-bound predicate, de Bruijn), `neg`, `conj`, `ex`, `nx` (`○_I`), `prev` (`●_I`), `ev` (`◇_[a,b]`), `since` (`S_I`), `letin`, `agg` (`ȳ ← ω(t̄; ḡ) φ`: the first `k` variables of `φ` are aggregated over, its other free variables form the group `ḡ`, the results are bound to `ys`). There is an extra equality atom `eq`. `◇` is bounded only (`b : ℕ`), since only bounded `◇` is enforceable (`Fut_◇`). |
| aggregation operators `ω`, `ω̂` | `AggOp` | ≈ `ω̂` maps a multiset of rows (a multiplicity `List D → ℕ∞` per row) to a set of result rows, and finite multisets to finite sets (`AggOp.fin`). User-defined table operators (`tfun`) are aggregation operators too. |
| intervals `I` | `inI` | ≈ `I = [a, b]` with `a : ℕ` and `b : Option ℕ` (`none` = ∞) |
| abbreviations `⊥, ∨, ⧫_I, □` | `Fm.disj` | ✅ `⊥ = ¬⊤`, `⧫_I φ = ⊤ S_I φ`. The outer `□` is implicit: a `Policy` `φ` stands for `□φ`. |
| `φ[d/x]` | `Fm.subst`, `instS` | ✅ |
| `fv(φ)` | `MF.fv` | ✅ |
| Figure 1 (semantics) | `MF.sat`, `aggSem`, `aggMS` | ≈ `MF.sat σ ρ i v φ`: lets are interpreted through the environment `ρ` of enclosing let bindings instead of the extended trace `σ[e ↦ φ]`. An aggregation holds only for a non-empty group `𝒢`. The multiset `⟅⟦t̄⟧_{v'} ∣ v' ∈ 𝒢⟆` is `aggMS` (counting the valuations of the aggregated variables). All other clauses match Figure 1. |
| Example 2.3: `φ_law`, `φ_del` | `Examples.phiLaw`, `Examples.phiDel`, `Examples.lawPolicy`, `Examples.delPolicy` | ✅ both are `Policy`s: well-formed and past-pure. `φ_let` is not formalized. |
| Example 2.3: `φ_agg` | `Examples.CNT`, `Examples.phiAgg`, `Examples.aggPolicy`, `Examples.aggPolicy_lnf` | ✅ with `CNT` as an `AggOp`, inside the policy `□¬∃u,n. φ_agg ∧ n = 1000`. Its let-normal form binds the since and the aggregation to lets. |

### §2.3 Enforcers

| Paper | Lean | Notes |
|---|---|---|
| proactive enforcer `(𝒮, s₀, μ, ν)` | `LoopParams`, `LState` | ≈ states are `LState`: tables `TS`, obligations `Ω`, output length. `s₀` is `LoopParams.run` at `0` (`tab₀`, `Ω = ∅`). `μ` and `ν` are the two cases of `LoopParams.step`. The parameters are specialized to EF programs (`P`, `ctx`, `commit`, `Sat`). |
| Algorithm 1 (enforcement loop) | `LoopParams.step`, `LoopParams.run`, `LoopParams.outTr` | ✅ a cursor `Cur` enumerates the calls `μ(k)` (`react k`) and `ν(t)` for `t = τ_k, …, τ_{k+1}-1` (`pro k t`). `LoopParams.outTr` is the output trace `ℰ(ρ)`. |
| soundness of `ℰ` w.r.t. `□φ` | `SoundEnforcer`, `Paper.sound_enforcer_def` | ✅ `∀ ρ i, φ.sat (E ρ) [] i v₀`, i.e. `□φ` holds on every output. |

---

## §3 EF: an operational enforcement language

### §3.1 Syntax

| Paper | Lean | Notes |
|---|---|---|
| clause: guards `π = κ₁ or … or κₙ`, filter `if φ` | `Trigger`, `Guards`, `GAtom` | ✅ abstract syntax: `Guards` is a list of conjunctions (lists) of atoms `GAtom.pred` (`e(t̄)`) or `GAtom.eq` (`x == c`). The filter is a formula `Fm`. |
| "each free variable is an argument of an atom of each guard" | `Guards.bindsAll`, `GoodClause`, `Rw.good`, `gate_good` | ✅ for the variables read by the effect: every clause generated by the compiler binds them in every guard (`GoodClause.locals`). |
| `rule ± e(t̄) [delay n] [next n] := trigger {c}` | `Clause`, `Effect` | ✅ `Effect.cau` (`+`), `Effect.sup` (`-`), `Effect.later b` (`[delay b]`), `Effect.next n` (`[next n]`). `Clause.nloc` counts the clause's local variables. |
| `section once/fixpoint` | `Program` | ✅ a program is a list of sections. A `once` section is a fixpoint section that stabilizes after one pass (`once_ok`). |
| `[filter] let`, `table … [window n b] := add {…} remove {…}`, `lagged table`, `agg let … group_by … over {…}` | `Item`, `Item.ar` | ✅ abstract syntax of the items (`Item.let_`, `Item.table`, `Item.lagged`, `Item.agg`). A clause is a trigger over the bound variables (existentials, aggregated variables) followed by the item's columns. Aggregation results may be at any column (`ys`). |
| declarations `event`, `pyinit`, `fun`, `tfun`; Figure 3 (concrete grammar) | — | the concrete text syntax is not formalized; functions are semantic (`Term.fn`), aggregation operators are `AggOp` |
| Figure 2 (program for `φ_law`) | — | — |

### §3.2 Semantics (Algorithm 2)

| Paper | Lean | Notes |
|---|---|---|
| enforcer state `(T, T^○, Ω)` | `LState`, `Tab`, `Deadline` | ≈ `Tab.since` holds the timestamped rows of the tables. `Tab.lag` holds the rows of the lagged tables. Deadlines are `Deadline.ts`/`Deadline.tp`. |
| `⟦p(t̄)⟧_R`, `⟦x == c⟧_R`, `⟦π if φ⟧_R` | `GAtom.sat`, `Guards.sat`, `Trigger.sat`, `ptTr` | ✅ triggers are evaluated on the one-point trace `ptTr W lv` of the working set |
| working set `𝒮 = (T, τ, D, C, S)`, `R₀ = T ∪ (D∖S) ∪ C` | `Ctx`, `work` | ✅ `work D₀ X` is `(D ∖ S) ∪ C`, where `X` holds the actions (`C`, `S`, and the deferred ones). `Ctx.lv` gives the tables and lets as a function of the working set. |
| `{v↾x̄ ∣ v ∈ ⟦c⟧_R}` | `rows`, `mem_rows` | ✅ the satisfying valuations of a clause, restricted to the item's columns |
| `Interp` | `interp`, `interpUpTo` | ✅ the items in order, each evaluated on the interpretation `R_{i-1}` of the earlier ones |
| `Eval` | `eval` | ✅ `let`: the rows of its clause; `table`: the stored rows in the window, minus the rows matched by `remove`, plus (if the window starts at `0`) those matched by `add`; `lagged table`: the stored rows in the window; `agg let`: `ω` applied to each group of the `over` clause (`aggSem`). |
| `Update(r, Ω, 𝒮, σ)`, `𝒜_𝒮(r)` | `update`, `fires`, `Effect.act`, `Act` | ✅ `fires K W c a`: rule `c` produces action `a` on the working set `W`. `delay`/`next` actions become obligations (`LoopParams.newObl`). |
| `Saturate`: `repeat for all r ∈ s: Update … until unchanged` | `step`, `Fixed`, `SatRun`, `Paper.saturate_until_unchanged` | ✅ `step` is one pass: `Update` for each rule in order, each on the working set left by the previous ones. The loop stops exactly at a fixpoint (`step_eq_iff_fixed`). `SatRun` runs the sections in order. |
| `once` sections | `once_fixed`, `once_ok` | ✅ a section without internal EDG edges is fixed after one pass |
| table updates at the end of `Saturate` | `updateTables`, `LoopParams.produce` | ✅ a table drops the rows matched by `remove` and stores, with the current timestamp, the rows matched by `add`; a lagged table stores the rows matched by `add` |
| (proof device) the items compute the lets | `interp_eq`, `updateTables_eq`, `itemParams_eq`, `eval_itemOf`, `lvOf`, `bodyVal`, `commitTab` | ✅ on the items of the lets, `Interp` is the formula-level let interpretation `lvOf` and the table updates are `commitTab`, so the loop running the items is the loop the correctness proof is carried out on |
| `μ` | `LoopParams.step`, `LoopParams.dueTp` | ✅ `Saturate` with input `D`, seeded with the `next` obligations due now |
| `ν` | `LoopParams.step`, `LoopParams.dueTs` | ✅ returns `⊥` (`none`) if nothing is due. Otherwise it runs `Saturate` on `∅`, seeded with the due obligations. |
| tables compute the let semantics | `since_table_correct`, `prev_table_correct`, `tables_compute`, `TablesComputeLets` | ✅ used by Theorem 4.5 |
| Example 3.1 | — | illustrative only |

---

## §4 From enforceable MFOTL to EF

### §4.1 Let-normal form

| Paper | Lean | Notes |
|---|---|---|
| let-normal form | `Fm`, `LetDef`, `LNF`, `LBody.shape`, `Fm.exFuture` | ✅ `χ` may contain `∃` only over subformulas with future operators (`Fm.exFuture`); future-free `∃` is bound to lets. |
| `LetNormalForm` (Algorithm 3, line 2) | `norm`, `lnf` | ✅ binds every past subformula, every aggregation, every source `let`, and every future-free `∃` to a let over its free variables |
| **Theorem 4.1** | `Paper.thm_4_1`, `let_normal_form` | ✅ `LNF Γ χ ∧ LetEquiv φ Γ χ` for `φ.WF []` |
| — (used by Theorem 4.5) | `norm_correct`, `norm_shape`, `norm_ordered`, `LetsOrdered`, `norm_presentOps` | lets only refer to earlier lets. Let operands are future-free for `PastPure` policies. |

### §4.2 Guard extraction

| Paper | Lean | Notes |
|---|---|---|
| `m ⊢ (π, φ) ↝^p_x (π', φ')` (Figure 4) | `GX` | ✅ one constructor per rule: `GX.grd`, `GX.vacPos`, `GX.vacNeg`, `GX.pred`, `GX.eq`, `GX.neg`, `GX.andL`/`GX.andR` (`And⁺` on the left or right conjunct of a binary `∧`), `GX.andNeg` |
| `⋁π ∧ φ ≡ ⋁π' ∧ φ'` | `GEquiv`, `polSat` | ✅ for both polarities |
| `x ∈ fv(κ')` for all `κ' ∈ π'` | `Guards.bindsAll`, `GAtom.binds` | ≈ slightly stronger: `x` is a direct argument of an atom of every `κ'` |
| **Lemma 4.2** | `Paper.lem_4_2`, `GX.sound` | ✅ `GX.sound` proves it for both polarities |
| `m ⊢ Φ ↝^p_X (π, φ)`, `Guards^m_X` (Figure 5) | `GXJ` | ✅ `GXJ.none`, `GXJ.vac`, `GXJ.pred`, `GXJ.eq`, `GXJ.andPos`, `GXJ.andNeg`, `GXJ.neg` |
| **Lemma 4.3** | `Paper.lem_4_3`, `GXJ.sound` | ✅ |
| "iterating `↝⁺_x` variable by variable is not sufficient" | — | — the counterexample `A(x,y) ∨ (C(y) ∧ D(x))` is not formalized |

### §4.3 Enforcement rewriting

| Paper | Lean | Notes |
|---|---|---|
| clause `θ ⇒ ε` denoting `□∀x̄. θ → ε` | `Clause`, `Clause.holds`, `Effect.holds` | ✅ `Effect.holds` gives the meaning of immediate and deferred effects on a trace |
| `Γ ⊢ φ ↪^ℂ 𝒞` / `↪^𝕊` (Figure 6) | `Rw` | ✅ `Rw S true`/`Rw S false`, one constructor per rule: `Rw.tt` (`⊤^ℂ`), `Rw.evC`, `Rw.evS`, `Rw.letC`, `Rw.letS`, `Rw.neg`, `Rw.andC`, `Rw.andSL`/`Rw.andSR`, `Rw.exC`, `Rw.exS`, `Rw.futEv`, `Rw.futNx1` (`Fut_○`), `Rw.futNxU` (`Fut_○ⁿ`, with `1 ≤ n`). `Rw` is a relation: the paper's `𝒞` is always among its results, and `Rw.exS` and the `Fut` rules also allow any subset of their alternatives. |
| `Γ(e) = (g, c, s)` | `Sig` | ≈ `Sig.enum` (enumerable predicates, `g`), `Sig.okC`/`Sig.okS` (`c`, `s`) for lets, `Sig.cau`/`Sig.sup` for base events, `Sig.d₀` (the canonical constant `0` of `Ex^ℂ`) |
| `𝒞[f]`, `𝒞₁ ⊗ 𝒞₂` | `prodCS`, `Clause.addFilter`, `Clause.substCtx`, `Clause.mapCau` | ✅ |
| `Ex^𝕊` side condition | `ExGuard`, `exS_side_iff` | ✅ |
| `Eventually_[b,b] ε`, `○…○ ε` | `Effect.later`, `Effect.next`, `nxU` | ≈ `Effect.next 1 true` (from `Fut_○`) also records that the next time-point is at most one time unit later, so that it lies in `[0, b]` |
| local soundness (proof of Theorem 4.5) | `Rw.sound` | ✅ if the clauses of an alternative hold, the target holds (`ℂ`) or fails (`𝕊`) |

### §4.4 Generating the candidate clause sets (Algorithm 3)

| Paper | Lean | Notes |
|---|---|---|
| `gate^ℂ_p`, `gate^𝕊_p` | `gate` | ✅ |
| `TypeLet`: guards of the let bodies | `LetGuards`, `LetDef.gop`, `LetDef.gvars`, `LBody.valOp`, `Fm.stripEx`, `enumOf` | ✅ `LetGuards Γ gd` states the conditions on the guards `gd`; `TypeLet` computes them (`gdOf`, `letGuards_ok`). The value-producing operand `gop` is guarded jointly (`GXJ`) in the variables `gvars`: for an aggregation, all of them except the results. The left operand of a `since` must be enumerable in **negative** polarity (the `remove` clause). Temporal lets and aggregations must be guardable. The terms of an aggregation are well-formed and only read guarded variables (`LetGuards.aggTerms`). |
| `TypeLet`: `𝒞^ℂ(p)`, `𝒞^𝕊(p)` (which operand to cause or suppress) | `LBody.cauTarget`, `LBody.supTarget` | ✅ for `a > 0`, a `since` is suppressed through its left operand. Aggregations, like `●`, are neither causable nor suppressable. |
| `Realizations` | `Real`, `Real.clauses`, `Real.Valid`, `Real.scope` | ≈ one chosen realization per let, derived in the scope of earlier lets |
| `Generate` (Algorithm 3) | `compilations`, `Compilation`, `Compiles` | ✅ `compilations` let-normalizes the policy, types its lets (`gdOf`, `realOf`) and rewrites the enforced formula in the scope of all lets (`rw`), giving one `Compilation` per candidate clause set |
| guard extraction as an algorithm | `gx`, `gxj`, `gx_sound`, `gxj_sound` | ✅ structural searches; in a positive conjunction, the left conjunct is tried first (`gx`), resp. the variables guardable in the left conjunct are guarded there (`gxj`) |
| `Γ ⊢ φ ↪^α 𝒞` as an algorithm | `rw`, `rw_sound`, `exGuard`, `peelNx` | ✅ returns the candidate clause sets; a suppressed conjunction suppresses its left conjunct if the right one is present, else its right one |
| `TypeLet` as an algorithm | `letGuards`, `letGuards₂`, `gdOf`, `clsOf`, `realOne`, `realOf`, `letGuards_ok`, `clsOf_ok`, `realOf_valid`, `TemporalOK` | ✅ one pass over the lets in let order: guards and item clauses (`clsOf`) with the earlier lets enumerable, then causation/suppression clauses in the scope of the earlier lets (the first candidate); compilation fails if a temporal let has no guards |
| soundness of the obligation events | `obligations_sound`, `program_sound` | ✅ |

### §4.5 Dependency analysis

| Paper | Lean | Notes |
|---|---|---|
| EDG (let atoms decomposed into their events) | `EDG`, `ldOf`, `LetDeps`, `tables_letDeps`, `trigDeps_evs` | ✅ `tables_letDeps`: a let only depends on the events it is defined from |
| SCCs in topological order `≺` (sources first) | `SCCOrder`, `TopoOrdered`, `sccOrder`, `sccOrder_spec`, `Paper.scc_order_exists` | ✅ one section per SCC, in a topological order. Such an order always exists. |
| stratification (implicit in the paper) | `Stratified`, `stratified_of_topo`, `saturate_sound`, `Paper.topological_order_stratified` | ✅ a later section never acts on an event read by an earlier one, so every rule is still saturated at the end of `Saturate` |
| cause/suppress check (SMT, sharing only upstream events; nothing if an effect is deferred) | `ConflictCheck`, `query`, `Up`, `SMT`, `query_sat`, `ConflictCheck.exclusive`, `Exclusive`, `ExclusiveNow`, `ExclusiveDeferred`, `effNames`, `LoopRun.conflictFree`, `Paper.conflict_check_exclusive`, `Paper.conflict_check_sound` | ✅ the check is stated on the EDG: for every rule causing an event and every rule suppressing it, a sound SMT solver (trusted, `SMT`) reports the conflict query (the two triggers over disjoint copies of variables and predicates, sharing the events upstream of the section, or nothing for a deferred cause, and equal effect arguments) unsatisfiable. `ConflictCheck.exclusive` proves that this establishes `Exclusive`: an instance caused by one rule is never suppressed by the other. Events never both caused and suppressed need no query (`ConflictCheck.of_noConflict`). The translation of the query into Z3 is not formalized. |
| DFG over argument positions `e.i` | `Pos`, `DFE`, `lsrcOf`, `LetsFlow`, `flow` | ✅ lets are decomposed into the positions their arguments come from |
| values created by aggregations | `nsrcOf`, `Clause.asrc`, `aggImg`, `aggClo`, `CloOp`, `aggImg_finite` | ✅ an aggregation result is computed from all values of the aggregation's operand, so its edges are **non-stable** (from all sources of the operand's guarded variables, `nsrcOf`). Termination uses that finitely many values give finitely many aggregation results (`aggImg_finite`). |
| stable edges and stable function symbols | `DFSL`, `Compiled.stab`, `Compiled.stab_sound`, `DFS`, `Term.stableIn`, `StabOp` | ✅ the compiler labels edges by its classification of terms (`Compiled.stab`: variables, constants, applications of `sfun`s). Trusted: the terms labelled stable are stable for a stability closure `Stab` (`StabOp`): finitely many values arise from a finite set however often stable functions are applied. Examples: comparisons, `not`, unary minus. |
| "no non-stable edge lies on a cycle" | `DFGCheck`, `DFGCheck.acyclic`, `Paper.dataflow_check_acyclic`, `DFGAcyclic`, `DFClause` | ✅ checked per section on the labelled DFG (`DFGCheck`); `DFGCheck.acyclic` proves the termination criterion `DFGAcyclic`. `DFClause` holds the side conditions on rules (constants, context variables and guard values in a finite set; local variables read by effects are bound by every guard). |
| "enforcement terminates if no non-stable edge lies on a cycle" | `Paper.termination`, `dfg_terminates`, `saturate_terminates`, `satFn`, `satFn_spec` | ✅ |

### §4.6 Compilation (Algorithm 4)

| Paper | Lean | Notes |
|---|---|---|
| `Compile(Γ, R, ≺)` as an algorithm | `compile`, `realClauses`, `compile_v₀`, `compile_sound` | ✅ the program of every compilation: the candidate clause set and the gated realization clauses, sectioned by `sccOrder`; each one whose checks pass is sound |
| EnfFlash end to end | `enfflash`, `enforcement_correct` | ✅ compile, keep the first program whose checks pass, run it; every enforcer it returns is sound |
| the compiler on Example A.4 | `Paper.ex_compile_A_4`, `Examples.compile_phiDel`, `Examples.rw_phiDel` | ✅ `compile` returns, for `φ_del`, a program with exactly the paper's clause set `{delRule}` |
| `Compile(Γ, R, ≺)` | `Compiled`, `Compiled.prog`, `items`, `itemOf` | ≈ a `Compiled` program: a `Compilation`, the rules (exactly `C` and the realization clauses, all with present filters), and the sections along `≺` (`SCCOrder`). Each let of `Γ` becomes its item (`itemOf`): a `let` for a present body (a `filter let` if it has no guards), a `table` for a since (add: right operand, remove: negated left operand), a `lagged table` for a previous, an `agg let` for an aggregation; the clauses are those of guard extraction (`ClausesOK`, `LetCl`): guards and residual filter of the operand, and for a table the `remove` clause `π_r if ¬φ_r'` from the negated left operand; filters are simplified (`Fm.simp`, `Tr.sat_simp`: meaning preserved); `val_iff`, `rem_iff` give their meaning; Figure 2's `Since1`: `since1_clauses`. |
| the two checks of §4.5 | `Compiled.Checks` | ✅ both on graphs: the conflict check on the EDG (`conflicts`, with the SMT solver's answers) and the data-flow check on the labelled DFG (`acyclic`) |
| well-formedness of the generated rules | `Compiled.good`, `GoodClause`, `Rw.good`, `gate_good`, `lnf_letsWF`, `dfClause_of_good` | ✅ proved, not checked: the generated clauses have well-formed terms, bind the local variables their effects read, only use guardable lets in guards, and defer effects by at least one step; with finitely many rules, the data-flow side conditions (`DFClause`) follow |
| the enforcer running `P` | `enforce`, `Compiled.efParams`, `itemParams`, `Compiled.efParams_eq`, `tableParams_wf` | ✅ Algorithm 1 running the EF program (the items and the rules) with a terminating `Saturate` |
| closed formula `□φ` | `Policy`, `Policy.Γ`, `Policy.χ` | ≈ a well-formed formula (`MF.WF`) whose past operators and let bodies are future-free (`MF.PastPure`, `MF.ffree`). The compiler requires this. |
| **Theorem 4.5** (compilation correctness) | `Paper.thm_4_5`, `enforcement_correct`, `compile_sound`, `compiled_sound` | ✅ stated end to end: every enforcer returned by `enfflash` is sound; `compile_sound` for each program of `compile` whose checks pass; `compiled_sound` for any compiled program |
| proof sketch: local soundness; well-definedness and termination | `Rw.sound`, `program_sound`, `enforcer_sound`, `enforcer_sound_topo`, `LoopRun.clauses_hold`, `clause_holds_point`, `LoopParams.loopRun` | ✅ `enforcer_sound_topo` is the theorem for a given loop run. `enforcement_correct` instantiates it with the loop program and the tables. |
| Example 4.4 | `Examples.lawPolicy` | ≈ only that `φ_law` is a policy; the output of `compile` on `φ_law` is not computed in Lean (it is for Example A.4: `Paper.ex_compile_A_4`). |

---

## Appendix A: a type system for the enforceable fragment

| Paper | Lean | Notes |
|---|---|---|
| contexts `Γ(p) ⊆ {𝔾, ℂ, 𝕊}`, `m_Γ` | `Caps`, `enumCaps`, `sigOf` | ✅ |
| `Γ ⊢ φ : GRD(x)^p` (Figure 9) | `Grd` | ✅ `Grd.pred`, `Grd.eq`, `Grd.top` (`Vac`), `Grd.neg`, `Grd.andL`, `Grd.andR`, `Grd.andNeg` |
| `Γ ⊢ φ : 𝔾^p_X` | `Enum` | ✅ |
| "the trigger `(π, ψ)` guards `x`" | `gx_iff` | ✅ the right-hand side of `gx_iff` |
| **Lemma A.1** (1), (2) | `Paper.lem_A_1_1`, `Paper.lem_A_1_2`, `gx_iff`, `gxj_iff` | ✅ for any set `m` of enumerable predicates |
| `Γ ⊢ φ : α ▷ Δ` (Figure 10) | `Typ` | ✅ `Typ.tt`, `Typ.evC`, `Typ.evS`, `Typ.letC`, `Typ.letS`, `Typ.neg` (`Neg^ℂ`/`Neg^𝕊`), `Typ.andC`, `Typ.andSL`, `Typ.andSR`, `Typ.exC`, `Typ.exS`, `Typ.futEv`, `Typ.futNx1`, `Typ.futNxU` |
| `Δ^ψ`, `Δ[0/x]`, `Δ↓_x`, unconditional, `◇_[b,b]Δ`, `○ⁿΔ` | `Clause.addFilter`, `Clause.substCtx`, `ExGuard`, `Clause.simple`, `Clause.mapCau` | ✅ |
| typing equals rewriting (proof of Theorem A.3) | `typ_iff_rw`, `exS_side_iff` | ✅ |
| let bindings: `φ̂_i`, `cau(φ_i)`, `sup(φ_i)`, the three conditions | `TypedLets`, `LetDef.gop`, `LetDef.gvars`, `LBody.cauTarget`, `LBody.supTarget` | ✅ `TypedLets.enum`, `TypedLets.removal`, `TypedLets.temporal`, `TypedLets.cau`, `TypedLets.sup`. `TypedLets.undef` adds that undefined lets have no capabilities. For an aggregation, `φ̂_i` is its operand, enumerable in all variables except the results; aggregations are temporal-like (`𝔾` required) and their terms read only enumerated variables (`TypedLets.aggTerms`). |
| **Definition A.2** (EF-MFOTL) | `EFMFOTL`, `Paper.def_A_2` | ✅ |
| **Theorem A.3** | `Paper.thm_A_3`, `efmfotl_iff_compiles` | ✅ `EFMFOTL S₀ φ Δ ↔ Nonempty (Compilation S₀ φ Δ)`. The same `Compilation` is an input of Theorem 4.5. |
| **Example A.4** | `Paper.ex_A_4`, `Examples.lnf_phiDel`, `Examples.delRule`, `Examples.phiDel_efmfotl`, `Examples.phiDel_compiles` | ✅ the let-normal form and the typing derivation, with exactly the paper's clause `(deletion_request(d,u), ⊤) ⇒ ◇_[30,30] delete(d,u)` |

---

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
