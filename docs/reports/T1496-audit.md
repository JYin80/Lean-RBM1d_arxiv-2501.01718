Auditor model: claude-opus-5-5[1m]

# T1496 audit: absorbing the `≺` loss into the reduced (5.35) shape (inventory target M3)

Branch `t/T1496` @ 6c5f132, audited in detached worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1496-audit`
(the branch itself is checked out in `RBM1D-wt/T1496`; that worktree is clean and identical to 6c5f132).
Diff vs `main`: one new file `RBM1D/Hierarchy/Rhs535Scale.lean` (+117). No other file touched; no frozen signature changed.

## Overall verdict: PASS
Ticket acceptance is met: (T1) is present under the required name and is correct and sharp. (T2) is not written, which is what Step 0 requires, because `h560` is a hypothesis of `eGpm_le_rhs535_of_jS`. The prove report gives the required account of `h560`.

## Target (T1) `RBM.rhs535_div_le`: PASS
1. Math preflight: the prove report §(a) has a PASS for T1, written before the Lean section. It includes the Step 0 checks against the source.
2. Statement vs target: the conclusion `rhs535 Wr Lr ℓu (ℓs / c) ηu D J ρ d ≤ c ^ 3 * rhs535 Wr Lr ℓu ℓs ηu D J ρ d` is the ticket's (T1) verbatim.
   - I checked this against the definition `Step2FarInputs.rhs535` (Step2FarInputs.lean:994). `ℓs` enters only through `r = ℓu/ℓs`. The terms have degrees in `r` of 3 (`cNear·r³·1_{d≤ℓ*}`), 3/2 (`cFar·r·√r·A^{-1/2}·J`), 1 (`169·r·A⁻¹·J^{3/2}`) and 1 (`r·(ℓuηu)⁻¹·Lr·ρ`). The true degree is 3, so the power `c^3` matches it.
   - The power is sharp. A compiled check (below) shows that the near-field term alone scales by exactly `c^3`. So no smaller power works when the indicator equals 1.
   - Hypotheses are `1 ≤ c`, `1 ≤ Wr`, `0 < ℓu`, `0 < ℓs`, `0 < ηu`, `0 ≤ J`, `0 ≤ ρ`, `0 ≤ Lr` and the unused `0 ≤ d`. They are the positivity and nonnegativity conditions that `cNear_nonneg`/`cFar_nonneg` (`1 ≤ W`, `0 < ℓu`) and the definition need. None of them is stronger than what the consumer `eGpm_le_rhs535_of_jS` already supplies: `hW`, `1 ≤ ℓu`, `hℓs`, `hηu`, `hρ`, and `J = jS ≥ 1`.
   - There is no `N` in the statement, so parameter order does not arise.
3. Vacuity:
   - All hypotheses are simple sign conditions and are satisfiable together.
   - Compiled nondegenerate witness: `Wr=5, Lr=3, ℓu=2, ℓs=1, ηu=1/2, D=4, J=7, ρ=6, d=0, c=3`. I chose `d=0` so that the near-band indicator is 1 and the degree-3 term is active.
   - No structure fields. No large-parameter loophole. The statement is a pointwise real inequality.
4. Dependencies: `Step2FarInputs.rhs535` (def), `Lemma57.cNear_nonneg`, `Lemma57.cFar_nonneg` and `tailT_nonneg`. All are on `main`, and none depends on this ticket, so there is no cycle.
5. Build and axioms:
   - `lake build RBM1D.Hierarchy.Rhs535Scale`: Build completed successfully (3770 jobs). No errors, and no warnings in the new file. The `ring` "Try this" info lines come from dependencies such as `Gauss/IBP.lean`.
   - `lake build RBM1D`: Build completed successfully (9642 jobs). The new module is not yet imported by the root; the ticket says the import is added at merge.
   - `#print axioms RBM.rhs535_div_le`: `[propext, Classical.choice, Quot.sound]`.
   - No `sorry`, `admit` or `axiom` in the file.

Compiled audit checks (`lake env lean`, rc 0):
```
example : RBM.Step2FarInputs.rhs535 5 3 2 ((1:ℝ) / 3) (1/2) 4 7 6 0
    ≤ 3 ^ 3 * RBM.Step2FarInputs.rhs535 5 3 2 1 (1/2) 4 7 6 0 :=
  RBM.rhs535_div_le (by norm_num) ... (by norm_num)
example (Wr ℓu ℓs c ind : ℝ) (hc : c ≠ 0) (hs : ℓs ≠ 0) :
    RBM.Lemma57.cNear Wr ℓu * (ℓu / (ℓs / c)) ^ 3 * ind
      = c ^ 3 * (RBM.Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 * ind) := by field_simp
```

## Target (T2) `RBM.eGpm_le_rhs535_of_jS_scaled`: not written. Correct under Step 0. BLOCKED upstream.
- I confirmed that `h560` is a hypothesis of `Step2FarInputs.eGpm_le_rhs535_of_jS` (Step2FarInputs.lean:2248-2250), with `Gm := gmOfJS = √jS · √tailT(d)` (:2184). So Step 0 requires the prover to prove only T1 and report on T2. T2 is correctly omitted.
- The prover's account is accurate:
  - `h560` does not involve `ℓs`, so the `ℓs → ℓs/c` rescaling cannot weaken it. The rescaling does relax `h273` by `c^2`, `h557C`/`h557R` by `√c`, and `hκ` by `c`.
  - The account restates T1488 "Open issues" #2 correctly, using `tailT(0) = A⁻² + W^{-D}` (StretchedExp.lean:281).
  - The account is explicit that satisfiability of `h560` with high probability remains undetermined and uncompiled.
- Missing input for any future T2: a decision on `h560`. One option is a proof that it holds on the relevant event. The other is to re-route M3/M4 through the APrime `gmBlk`/`jG` form, as T1488 already proposes. This is a dispatcher and route decision, not a defect of this ticket.

## Notes
- The prove report's first line is `Prover model: claude-sonnet-5[1m]`, as the ticket requires.
- No paper-delta is needed. T1 is a scaling identity about a Lean-internal constant.
