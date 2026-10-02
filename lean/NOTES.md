# Lean formalization of EnfFlash

This directory contains a Lean 4 formalization of *Practical Runtime Enforcement
of First-Order Temporal Requirements* (extended version). It covers §2, §3.1–3.2
and §4 of the paper and Appendix A:

* MFOTL (syntax and semantics), traces, enforcers, and Algorithm 1;
* the EF language and its reference interpreter (Algorithm 2);
* let-normal forms, guard extraction, enforcement rewriting, the generation of
  candidate clause sets (Algorithm 3), the dependency analysis, and
  compilation (Algorithm 4);
* the type system of Appendix A.

Every theorem, lemma and claim of these sections is stated and proved. The
complexity results of §3.3 and the evaluation of §5 are not formalized.

## Building

* Lean `v4.31.0` (`lean-toolchain`) and Mathlib `v4.31.0` (`lakefile.toml`).
* `lake exe cache get` downloads the Mathlib build, then `lake build` builds
  the formalization (56 files, about 13,500 lines).
* No proof uses `sorry`. The following prints only `propext`,
  `Classical.choice` and `Quot.sound` for each result:

```lean
import Paper
open Paper
#print axioms theorem_4_3
#print axioms theorem_A_2
```

## Layout

* `Paper/*.lean` transcribes the definitions of the paper, in the paper's
  order and notation. Comments cite the lines of `main.tex` they transcribe.
* `Paper/Claims.lean` states all results of the paper as propositions, in
  the order of the paper.
* `Paper/Proof/` contains every lemma and every proof. A statement `Theorem_4_3`
  is proved by `theorem_4_3 : Theorem_4_3 Voc`, and a claim `Claim_x` by
  `claim_x`. Lemma 4.2 is proved by `lemma_4_2_holds`.

Below, **F** marks a formalization choice: something the paper leaves
implicit, made explicit in Lean. **N** marks one of the few places where the
formalization is deliberately more precise than the paper text.

## Results

| Paper | Statement (`Claims.lean`) | Proof |
|---|---|---|
| Theorem 4.1 (let-normal form) | `Theorem_4_1` | `theorem_4_1` (`Proof/LetNormal.lean`) |
| equations behind `And⁺`, `And⁻` (§4.2) | `Claim_andPos_equation`, `Claim_andNeg_equation` | `Proof/Claims.lean` |
| Lemma 4.2 (guard extraction) | `Lemma_4_2` | `lemma_4_2_holds` (`Proof/Guards.lean`) |
| the outcomes of TypeLet (§4.4) | `Claim_typeLet_since`, `_prev_agg`, `_fatal`, `_present_unguarded` | `Proof/Claims.lean` |
| stable functions are closure-finite (§4.5) | `Claim_closure_finite` | `Proof/Dependency.lean` |
| examples of §4.5 | `Claim_conflict_C1`, `Claim_conflict_C1'`, `Claim_dfg_succ_rejected`, `Claim_dfg_use_accepted` | `Proof/Claims.lean` |
| Theorem 4.3 (compilation correctness) | `Theorem_4_3` | `theorem_4_3` (`Proof/Main.lean`) |
| `And^𝕊_L`, `And^𝕊_R` of Figure 7 | `Figure7_AndS_binary` | `Proof/TypeSystem.lean` |
| Lemma A.1 | `Lemma_A_1` | `lemma_A_1` (`Proof/TypeSystem.lean`) |
| Theorem A.2 | `Theorem_A_2` | `theorem_A_2` (`Proof/TypeSystem.lean`) |

In addition, `theorem_4_3_lnf` (`Proof/LnfInst.lean`) combines Theorems 4.1
and 4.3; see the section "Theorem 4.3 with the let-normal form of Theorem 4.1".

## Correspondence

### §2.1 Traces — `Paper/Traces.lean`

| Paper | Lean |
|---|---|
| signature `Σ = (𝔻, ℰ, ι)`, events, `𝔻𝔹`, `𝔻𝔹_E` | `Signature`, `Event`, `DB`, `DBOf` |
| traces, `|σ|`, `ε` | `Seq` (finite or infinite), `Trace`, `Seq.length`, `Trace.empty` |
| `σ · (τ, D)` (Algorithm 1) | `Trace.snoc?` (N4) |

### §2.2 MFOTL — `Paper/MFOTL.lean`

| Paper | Lean |
|---|---|
| `𝕍`, `𝔽`, `ι`, `f̂`, `Ω`, `ι'`, `ω̂` | `Vocabulary` |
| intervals `𝕀` | `Interval` (F13) |
| terms, `⟦t⟧_v` | `Term`, `Term.eval` (partial: `none` if a variable is unassigned) |
| formulae (including `x = c`), abbreviations | `Formula`, `Formula.or` … `Formula.Always` |
| `fv(φ)`, `φ[d/x]` | `Formula.fv` (N3), `Formula.subst` (N2) |
| Figure 1, `σ[e ↦ φ]` | `Formula.sat`, `Str.extend` (F2) |

### §2.3 Enforcers — `Paper/Enforcer.lean`

| Paper | Lean |
|---|---|
| proactive enforcer `(𝒮, s₀, μ, ν)` | `Enforcer` |
| Algorithm 1 | `Enforcer.proLoop`, `proRange`, `iter`, `run`, `out` (N4) |
| soundness | `Enforcer.Sound` (N4) |

### §3 EF — `Paper/EFSyntax.lean`, `Paper/EFSemantics.lean`

| Paper | Lean |
|---|---|
| Figure 3 | `Program`, `Item`, `Clause`, `EGuards`, `Atom`, `Filter`, … (abstract syntax; Python code is opaque, F10) |
| `⟦p(t̄)⟧_R`, `⟦x == c⟧_R`, `⟦π if φ⟧_R`, `⟦if φ⟧_R` | `Atom.sem`, `join`, `EGuard.sem`, `Clause.sem` |
| interpretations `R`, tables `T`, `T^○` | `Interpretation`, `Tables` (F1) |
| enforcer state, working set | `EState`, `WorkingSet` |
| `\overline{s}^I` | `window` |
| Eval, Interp, Update | `Eval` (F4, N5), `Interp`, `Update` (F3) |
| Saturate, μ, ν | `runSection`, `runSections`, `updTable`, `updLagged`, `Saturate`, `mu`, `nu` |

### §4.1–4.4 — `Paper/Generate.lean`, `Paper/Guards.lean`, `Paper/Rewrite.lean`

| Paper | Lean |
|---|---|
| let-normal form | `LNF`, `LNF.Valid`, `Formula.IsChi`, `IsPsi`, `IsLetBody` (N6) |
| guards, "`κ` binds `x`" | `GAtom`, `GConj`, `GDisj`, `GConj.Binds` |
| Figure 4, `Guards^m_X` | `GX`, `Guards` (F11) |
| `m ⊢ (π, ψ) ⇝^p_x (π', ψ')` | `TGX` |
| clauses, effects, `𝒞[f]`, `⊗` | `EClause`, `Effect`, `CSet.map`, `CSet.tensor` |
| Figure 5, `m_Γ`, "present" | `Rw` (F7), `RwSetting.m`, `Formula.Present` |
| `gate`, Algorithm 3 | `gate`, `TypeLet`, `TypeLets`, `Realizations`, `Generate` (F6, F8) |

### §4.5 Dependency analysis — `Paper/Dependency.lean`

| Paper | Lean |
|---|---|
| EDG (let atoms decomposed), SCCs | `Decomp`, `EDGEdge`, `EDG`, `Reach`, `SameSCC`, `SCCBefore` (N8) |
| cause/suppress check | `PairSat`, `ConflictCheck` (N8) |
| DFG, including the edges through lets | `DFGEdge`, `LetEdge`, `DFG` |
| stability, stable edges, termination check | `StabOrder`, `Stable`, `AggResult`, `StableEdge`, `DFGCheck` |

### §4.6 Compilation — `Paper/Compile.lean`

| Paper | Lean |
|---|---|
| `≺` on the condensed SCCs | `TopoOrder` (a rank function) |
| Algorithm 4, the items of the lets | `Compile`, `letItem`, `ruleItem`, `withSections`, `toClause` (F9, F10) |
| the enforcer of an EF program | `Program.enforcer` (F5) |
| sound enforcer on traces without let-bound or obligation events | `Program.SoundEnforcer`, `Admissible`, `NewNames` |
| well-formedness assumed by Theorem 4.3 | `WF` (N1, N6, F12) |

### Appendix A — `Paper/TypeSystem.lean`

| Paper | Lean |
|---|---|
| contexts `Γ(p) ⊆ {𝔾, ℂ, 𝕊}`, `m_Γ` | `Cap`, `ACtx`, `ACtx.m` |
| Figure 6, `𝔾^p_X`, "the trigger guards `x`" | `Grd`, `ACtx.Grd`, `ACtx.GSet`, `ACtx.TrigGuards` |
| `Δ^ψ`, `Δ[0/x]`, `Δ↓ₓ`, `◇_[b,b]Δ`, `○ⁿΔ` | `ClauseSet.conj`, `.subst`, `.down`, `.defer` |
| Figure 7 | `Typ` |
| `φ̂ᵢ`, `x̄ᵢȳ`, `cau`, `sup`, the conditions on lets | `hatOf`, `gsOf`, `cauOf`, `supOf`, `CondOK`, `LetsTyped` |
| EF-MFOTL | `EFMFOTL` |

## Formalization choices

* **F1** Partial maps are total maps. An interpretation `R : ℰ ⇀ 𝒫(𝔻*)` maps
  undefined names to `∅`; it is only used through membership. A context `Γ`
  is a map to `Option (Bool × Bool × Bool)`.
* **F2** `Formula.sat` is defined on structures `Str`: a sequence of timestamps
  and arbitrary, possibly infinite, databases, as in Figure 1. Infinite
  traces embed into it (`Trace.toStr`), and `Formula.satTr` requires the
  trace to be infinite.
* **F3** `|σ| + N` in Update is computed on `Trace.len σ ∈ ℕ`. Algorithm 1
  only passes finite `σ`.
* **F4** `Eval` of an `agg let` applies `ĝ` only to finite groups. The groups
  of a guarded `over` clause are finite.
* **F5** `μ` and `ν` are partial: `Saturate` is undefined when a `fixpoint`
  section diverges, and a returned event may not be in `𝔻𝔹_ℂ`/`𝔻𝔹_𝕊`.
  `Program.enforcer` has an absorbing failure state for these cases.
  `Program.SoundEnforcer` requires that the failure state is never entered.
* **F6** The paper does not fix a let-normalization procedure. `Generate` and
  `Theorem_4_3` take it as a parameter `LetNormalForm` whose result is valid,
  well formed, and equivalent to `□φ` on traces without let events.
  `theorem_4_3_lnf` instantiates it with the construction of Theorem 4.1.
* **F7** The n-ary `⋀ᵢ φᵢ` of the rules `And` is matched against right-nested
  binary conjunctions with `n ≥ 2` (`bigAnd`). For example, `a ∧ (b ∧ c)`
  matches `[a, b ∧ c]` and `[a, b, c]`.
* **F8** TypeLet calls `Guards^m_{fv(φ)}(φ)` on the operand `φ` of `⧫`, `●` and
  aggregations, as written. If the operand is `∃ȳ. χ` with free variables,
  this fails (Figure 4 has no rule for `∃`). The let-normal form constructed
  for Theorem 4.1 never puts `∃` directly under these operators.
* **F9** `Compile(ℒ, Γ, R, ≺)` takes:
  * the setting `Ξ`, which contains the base events needed for `m_Γ`;
  * an enumeration `rs` of `R` (the order of clauses inside an SCC is free);
  * a rank function `rk` for `≺`.

  `Γ` does not record the guards computed by TypeLet, so `letItem`
  recomputes them with `Guards`. The result may be a different derivation,
  which is equally valid by Lemma 4.2.
* **F10** The EF types of events and columns are parameters of `Compile`.
  Declarations, `pyinit`, `fun` and `tfun` do not affect the semantics: `f̂`
  and `ω̂` come from the vocabulary.
* **F11** When several derivations of `m ⊢ Φ ⇝⁺_X (π, φ)` exist, `Guards`
  fixes one by choice.
* **F12** Theorem 4.3 is stated over a single vocabulary that also contains
  the let-bound and the obligation events. The obligation events are given by
  functions `cauN`, `supN` of a setting `RwSetting`. `WF` requires them to be
  fresh, of the arity of `p`, and injective and distinct on the let-bound
  events.
* **F13** An interval is a non-empty order-connected subset of `ℕ`.
  `Interval.eq_icc` proves that each is `[a, b]` with `b ∈ ℕ ∪ {∞}`, and
  `Interval.bounds` returns these bounds, used by windows.

## Differences with the paper text

These eight places are more precise in Lean than in the paper. They concern
details that the paper leaves implicit.

* **N1 — well-formed terms and formulae.** The grammar of §2.2 does not
  restrict arities. In Lean, an event carries the proof that it has the arity
  of its name, so an atom with the wrong number of arguments is false. A
  function application with the wrong number of arguments does not evaluate.
  Theorem 4.3 assumes well-formed formulae (`WF`):
  * atoms `e(t̄)` with `|t̄| = ι(e)` (`Formula.WellArity`);
  * function symbols applied to `ι(f)` arguments, i.e. atom arguments
    evaluate when their variables are assigned (`Formula.FunOK`);
  * `|ȳ| = m` in `ȳ ← ω(t̄; ḡ) φ` with `ι'(ω) = (n, m)`;
  * `|x̄| = ι(e)` for a let `e(x̄)`.

  Without them the theorem fails. For example, for `□(Q(x) → P(f(x, x)))`
  with `ι(f) = 1`, the effect `P(f(x, x))` can never be caused.
* **N2 — substitution.** `φ[d/x]` is undefined (`none`) when `x` is a
  group-by or result variable of an aggregation in `φ`: it occurs there only
  in variable positions. `Ex^ℂ` (Figure 5) and `Δ[0/x]` (Figure 7) apply only
  where the substitution is defined.
* **N3 — free variables of lets.** `fv(let e(x̄) = φ in ψ) = fv(ψ)`, since
  Figure 1 evaluates `φ` under valuations independent of `v`. The bodies of
  lets have `fv(φ) = x̄` with distinct `x̄` (`WF`, and `LnfOK` for the sources
  of `theorem_4_3_lnf`).
* **N4 — the output of Algorithm 1 and soundness.**
  * `ℰ(ρ)` is the returned trace `σ`.
  * For an infinite `ρ`, the loop does not terminate, and `ℰ(ρ)` is the
    infinite trace of which every `σ` built by the loop is a prefix.
    `Enforcer.limit` constructs it.
  * `σ · (τ, D)` is a trace only if `D` is finite (`Trace.snoc?`). `ℰ(ρ)` is
    undefined otherwise.
  * Soundness quantifies over the *infinite* system traces, the only ones
    Figure 1 gives a semantics for, and requires `ℰ(σ)` to be defined. On
    finite traces, soundness would fail for `φ_del`: a deletion request at
    the end of a finite trace cannot be honoured.
* **N5 — defaults of tables.** A table without `[window n b]` has the window
  `[0, ∞)`, and a table without `remove` clause removes nothing.
* **N6 — well-formed let-normal forms.** Theorem 4.3 (`WF`) and Theorem A.2
  (`LNF.WFA`) assume the following, which holds for the let-normal form
  constructed for Theorem 4.1:
  * the let-bound events `eᵢ` are distinct and fresh;
  * each `x̄ᵢ` consists of distinct variables with `fv(φᵢ) = x̄ᵢ`, and
    `x̄ᵢ = ḡ ȳ` for an aggregation (the column order of EF aggregations);
  * `φᵢ` mentions only base events and `e₁, …, e_{i−1}`, and the `χⱼ` are
    closed;
  * in `∃ȳ. χ`, every `yⱼ` is free in `χ`, and the terms of an aggregation only
    use variables free in its body (Theorem A.2);
  * formulae are *clean* (`Formula.Clean`): no bound variable is free in the
    context or in a sibling, or bound twice on a path. α-renaming always
    achieves this.

  Figure 5 is unsound for formulae that are not clean. Suppressing
  `B(x) ∧ ∃x. A(x)` gives the clause `(A(x), B(x)) ⇒ ¬A(x)`, which confuses
  the two `x`.
* **N7 — Theorem 4.1.** The let-bound events of the normal form are fresh.
  Lean states the theorem over `ℰ ⊎ L` for a finite set `L` of new names
  (`Vocabulary.ext`). The equivalence holds on the traces over `Σ`, embedded
  by `Str.embed`, for valuations defined on the free variables.
* **N8 — the cause/suppress check.** `PairSat` formalizes the SMT query as
  follows:
  * The two clauses are renamed apart (two valuations), and the arguments of
    the caused and of the suppressed event are equal.
  * "Only taking into account events from SCCs strictly before `e`": the two
    triggers are evaluated on two structures that agree exactly on the events
    of the SCCs from which `e`'s SCC is reachable (other than `e`'s own SCC).
    This order does not depend on the choice of a topological order. Let
    atoms are interpreted by their definitions (`withLets`).
  * If one effect is deferred, the triggers are evaluated on two unrelated
    structures and time-points ("no event is shared").

  The query `θ_ℂ ∧ θ_𝕊` under one valuation, without renaming and without
  equating the arguments, would be unsound. Example: `(⊤, A(x)) ⇒ B(x)` and
  `(⊤, ¬A(x)) ⇒ ¬B(f(x))`. Here `A(x) ∧ ¬A(x)` is unsatisfiable, yet `B(a)` is
  caused and suppressed when `A(a)`, `¬A(b)` and `f(b) = a`.

## Theorem 4.3 with the let-normal form of Theorem 4.1

`theorem_4_3_lnf` (`Proof/LnfInst.lean`) instantiates Theorem 4.3 with the
normal form `lnfN φ` built in the proof of Theorem 4.1. The extended
vocabulary is `ℰ ⊎ (Fin K × Fin A)`:
* `K = 3(|φ| + 1)` gives three bands of indices: let-bound events, `Cau_p` and
  `Sup_p` (`oblN`);
* `A` bounds the arities.

For a closed MFOTL formula `φ`, the corollary proves all hypotheses of
`Theorem_4_3` on the let-normal form and the obligation events:
* `Valid` and every field of `WF`;
* the equivalence with `□φ` on traces without let events (`lnfN_equiv`).

It assumes the following of `φ`:
* `φ.Clean ∅`, `φ.WellArity` and `φ.FunOK`;
* `φ.LnfOK`: every subformula that becomes a let body (`∃`, `●`, `S`) is
  clean w.r.t. its own free variables;
* a source `let e(x̄) = ψ` has a clean body, distinct `x̄ = fv(ψ)` and
  `|x̄| = ι(e)`;
* aggregations have the arity of their operator.

The remaining hypotheses are that the algorithm succeeds: TypeLet,
`Generate`, the two checks of §4.5, a topological order, and `Compile`.

## The proof of Theorem 4.3

* **MFOTL level:**
  * `rw_sound` (`RwSound.lean`): enforcing any alternative of Figure 5
    enforces the formula.
  * `obl_sound` and `lnf_sat` (`Final.lean`): if every clause of `R` holds at
    every time-point, and the obligation events come from clauses, then the
    let-normal form holds.
* **EF level:**
  * The compiled let items compute the let relations: `eval_corr`
    (`Corr.lean`), `interp_corr` (`Interp.lean`), `tables_final`
    (`Tables.lean`).
  * One rule application adds what its clause fires (`upd_rule`,
    `Point.lean`).
  * `saturate_sem` (`Sat.lean`): `Saturate` reaches a fixpoint of all
    clauses, and every new event has a provenance.
* **Conflicts:** `conflict_free` (`Conflict.lean`): the cause/suppress check
  makes the caused and the suppressed events disjoint.
* **Termination** (`Levels.lean`, `DFG.lean`, `Bound.lean`, `Prod.lean`,
  `Term.lean`):
  * The termination check bounds every value at a position by the level of
    the position in the DFG (`rule_bound`).
  * The states of `Saturate` therefore range over a finite set, and
    `saturate_some` shows that it terminates.
* **Algorithm 1** (`Run.lean`, `Alg.lean`):
  * `call_spec` describes one call of `Saturate`.
  * `RInv`, the invariant of the run, records for each time-point the call
    that produced it. It also states that the obligations of a time-point `j`
    are in `Dⱼ`, that the obligations of a timestamp `t` are discharged at the
    last time-point with timestamp `t`, and that the gap condition of `○`
    holds.
  * `run_inv`: the run never fails.
* **Conclusion:** `sat_rel` (`Main.lean`) shows that every clause holds on the
  output trace. `theorem_4_3` combines it with `lnf_sat` and the equivalence
  of the let-normal form.
