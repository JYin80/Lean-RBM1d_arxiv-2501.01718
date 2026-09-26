/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Q716

/-!
# Q716: Lemma 7.3, (7.14) and (7.16), packaged for the G1c route

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 7.3, pp. 78–80, (7.13)–(7.24).

This module packages the pointwise, deterministic kernel bounds of Lemma 7.3 under the names
the `G1c` plan's pilot P1 asks for (`docs/claude-team/g1c-plan/G1c-plan-paper.md` §3.3(a),
§5 P1), for the paper's edge parameter `ξ_i = m(σ_i) m(σ_{i+1})` (Definition 5.2, cyclic:
`i + 1 : Fin n` wraps).

**Nothing here is new mathematics.** Every bound is `RBM.norm_Uker_fastDecay_le`,
`RBM.norm_Uker_fastDecay_le_of_eq`, `RBM.norm_Uker_fastDecay_le_sumZero_sigma`
(`Hierarchy/KernelDecay.lean`), already committed since **T51+T55** and already recorded as
an accepted paper-delta (`docs/paper-deltas.md` #35: the paper's `W^{C_nτ}` becomes a free
parameter `K ≥ 1`, `W^{-D}` becomes an explicit `δ ≥ 0`, marked *stronger / alternative
proof*). This file only specialises `ξ` to `xiOf (mSigma E) σ` and renames the results; see
`docs/reports/T1522-prove.md` for the trace through `Gauss/Lemma514Q716.lean` and
`Hierarchy/SumZeroDyn.lean` that the §10b reuse check asks for.

## Main results

* `RBM.Gauss.Q716.uker_decay_le`         : **(7.14)**
* `RBM.Gauss.Q716.uker_decay_le_nonAlt`  : **(7.16), Case 1** (`σ_k = σ_{k+1}` for some `k`,
  cyclic)
* `RBM.Gauss.Q716.uker_decay_le_sumZero` : **(7.16), Case 2** (sum-zero, (7.15))
* `RBM.Gauss.Q716.uker_decay_le_nonAlt_satisfiable`,
  `RBM.Gauss.Q716.uker_decay_le_sumZero_satisfiable` : nondegenerate satisfiability witnesses
  for the two cases, built from `RBM.Gauss.witTensor` (`Gauss/Lemma514Q716.lean`).

## Deviation from the literal paper wording

The paper writes the error term of (7.14)/(7.16) as a bare `W^{-D+C_n}`, with no
`s,t`-dependence. Taken literally (for *arbitrary* `0 ≤ s ≤ t < 1`, with `D`, `W`, `E`, `n`
fixed) that is false: the constant tensor `A ≡ δ` is `(ℓ, δ)`-fast-decaying for every `ℓ`
and bounded by `M = δ`, and for a real edge charge (`|ξ_i| = 1`) the exact value of
`(U_{s,t,σ} ∘ A)_a` is `δ · ((1-s)/(1-t))^n`, unbounded as `t → 1⁻` for fixed `s, δ, n`. This
is the same failure pattern as `RBM.Gauss.no_const_hkerC_on_gridS`, applied to the *literal*
wording rather than to the quantity the route actually needs. The bounds below keep the
`η_s/η_t` ratio explicit in the error term (`((1-s)/(1-t))^n · δ`) instead, exactly as the
already-accepted `Hierarchy/KernelDecay.lean` lemmas do (`docs/paper-deltas.md` #35); this is
what `RBM.Gauss.momNorm_Uker_sumZero_scale_le` and its siblings actually consume.
-/

namespace RBM.Gauss.Q716

/-- **(T1) Lemma 7.3, (7.14)**, for the paper's edge parameter `ξ = xiOf (mSigma E) σ`
(Definition 5.2). For `0 ≤ s ≤ t < 1`, `|E| < 2`, and `A` `(ℓ_s K, δ)`-fast-decaying ((7.13),
`K` playing the role of `W^τ`, `δ` the role of `W^{-D}`),
`‖(U_{s,t,σ} ∘ A)_a‖ ≤ C_n K^n · (ℓ_t/ℓ_s) · (ℓ_sη_s/(ℓ_tη_t))^n · ‖A‖_max + (η_s/η_t)^n δ`.
Reused verbatim from `RBM.norm_Uker_fastDecay_le` (already committed, T51+T55; see the module
docstring for the `((1-s)/(1-t))^n · δ` vs. literal `W^{-D+C_n}` deviation). -/
theorem uker_decay_le (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] (hn : 2 ≤ n) (hL : 3 ≤ L)
    {E : ℝ} (hE : |E| < 2) (σ : Fin n → Bool) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
    (ht1 : t < 1) {K M δ : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    {A : LoopArg L n → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hA : FastDecay L (ellHat L (s : ℂ) * K) δ A) (a : LoopArg L n) :
    ‖Uker L (xiOf (mSigma E) σ) s t A a‖ ≤
      cKer n * K ^ n * (ellHat L (t : ℂ) / ellHat L (s : ℂ))
        * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) ^ n * M
        + ((1 - s) / (1 - t)) ^ n * δ :=
  norm_Uker_fastDecay_le L (show 1 ≤ n by omega) hL hs0 hst ht1
    (fun i => (norm_xiOf_mSigma hE.le σ i).le) hK hM hδ hAM hA a

/-- **(T2) Lemma 7.3, (7.16) Case 1**: a cyclic non-alternating charge (`σ k = σ (k+1)` for
some `k`, indices in `Fin n`, matching `xiOf`'s cyclic `i + 1`). The `ℓ_t/ℓ_s` factor of (T1)
disappears; the constant now also depends on the fixed bulk gap `κ := min (2 - |E|) 1 > 0`
(the row-sum bound `Σ|Ξ_k| = O(1)` needs `ξ_k = m² ≠` too close to `1`, uniform in
`t ∈ [0,1)`), which is a function of `E` alone, not of `N, W, L, s, t`
(`docs/paper-deltas.md` #35). -/
theorem uker_decay_le_nonAlt (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] (hL : 3 ≤ L)
    {E : ℝ} (hE : |E| < 2) {σ : Fin n → Bool} {k : Fin n} (hk : σ k = σ (k + 1))
    {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1)
    {K M δ : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    {A : LoopArg L n → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hA : FastDecay L (ellHat L (s : ℂ) * K) δ A) (a : LoopArg L n) :
    ‖Uker L (xiOf (mSigma E) σ) s t A a‖ ≤
      cKerShort n (Real.sqrt (min (2 - |E|) 1)) * K ^ n
        * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) ^ n * M
        + ((1 - s) / (1 - t)) ^ n * δ := by
  have hκ0 : (0 : ℝ) < min (2 - |E|) 1 := lt_min (by linarith) one_pos
  have hκ1 : min (2 - |E|) 1 ≤ 1 := min_le_right _ _
  have hEκ : |E| ≤ 2 - min (2 - |E|) 1 := by
    have := min_le_left (2 - |E|) (1 : ℝ); linarith
  exact norm_Uker_fastDecay_le_of_eq L hL hκ0 hκ1 hEκ hk hs0 hst ht1 hK hM hδ hAM hA a

/-- **(T3) Lemma 7.3, (7.16) Case 2**: the sum-zero property (7.15) (`SumZeroAt L 0 A`, i.e.
`Σ_{a_2,…,a_n} A_a = 0` for every `a_1`, `0 : Fin n` being the paper's `a_1`) gives the same
improved bound as (T2), with **no** non-alternation hypothesis on `σ`. -/
theorem uker_decay_le_sumZero (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] (hn : 2 ≤ n) (hL : 3 ≤ L)
    {E : ℝ} (hE : |E| < 2) (σ : Fin n → Bool) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {K M δ : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    {A : LoopArg L n → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hA : FastDecay L (ellHat L (s : ℂ) * K) δ A) (hz : SumZeroAt L 0 A) (a : LoopArg L n) :
    ‖Uker L (xiOf (mSigma E) σ) s t A a‖ ≤
      cKerSumZero n * K ^ (2 * n)
        * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) ^ n * M
        + cKerSumZeroErr n * (L : ℝ) ^ n * ((1 - s) / (1 - t)) ^ n * δ :=
  norm_Uker_fastDecay_le_sumZero_sigma L hn hL hE.le σ hs0 hst ht0 ht1 hK hM hδ hAM hA hz a

/-- **Nondegenerate witness for (T2).** `σ ≡ true` is genuinely non-alternating
(`σ 0 = σ (0+1)`, cyclically), and `Gauss.witTensor L 0 1` is a **nonzero** tensor that is
simultaneously bounded and fast-decaying — the hypotheses of `uker_decay_le_nonAlt` (besides
`|E| < 2`, met at `E = 0`) are satisfiable together, non-vacuously. -/
theorem uker_decay_le_nonAlt_satisfiable (L : ℕ) [NeZero L] (hL : 3 ≤ L) :
    witTensor L 0 (1 : ℂ) ≠ 0 ∧
      (fun _ : Fin 2 => true) (0 : Fin 2) = (fun _ : Fin 2 => true) ((0 : Fin 2) + 1) ∧
      (∀ b, ‖witTensor L 0 (1 : ℂ) b‖ ≤ 1) ∧
      FastDecay L (ellHat L ((0 : ℝ) : ℂ) * 2) 0 (witTensor L 0 (1 : ℂ)) :=
  ⟨witTensor_ne_zero L hL one_ne_zero, rfl,
    fun b => by simpa using norm_witTensor_le L (m := 0) (κ := (1 : ℂ)) b,
    by
      have h0 : ((0 : ℝ) : ℂ) = 0 := by norm_num
      rw [h0, ellHat_zero L hL]
      exact fastDecay_witTensor L hL 1 (by norm_num)⟩

/-- **Nondegenerate witness for (T3).** The same nonzero tensor `Gauss.witTensor L 0 1` is
also sum-zero at coordinate `0` (`SumZeroDyn.sumZeroAt_zero_of_sumZero` converts the
`Gauss.witTensor`-level "sum-zero at every coordinate" witness), so all four hypotheses of
`uker_decay_le_sumZero` (besides `2 ≤ n`, `|E| < 2`) hold simultaneously for a genuinely
nonzero tensor. -/
theorem uker_decay_le_sumZero_satisfiable (L : ℕ) [NeZero L] (hL : 3 ≤ L) :
    witTensor L 0 (1 : ℂ) ≠ 0 ∧
      (∀ b, ‖witTensor L 0 (1 : ℂ) b‖ ≤ 1) ∧
      FastDecay L (ellHat L ((0 : ℝ) : ℂ) * 2) 0 (witTensor L 0 (1 : ℂ)) ∧
      SumZeroAt L 0 (witTensor L 0 (1 : ℂ)) :=
  ⟨witTensor_ne_zero L hL one_ne_zero,
    fun b => by simpa using norm_witTensor_le L (m := 0) (κ := (1 : ℂ)) b,
    by
      have h0 : ((0 : ℝ) : ℂ) = 0 := by norm_num
      rw [h0, ellHat_zero L hL]
      exact fastDecay_witTensor L hL 1 (by norm_num),
    SumZeroDyn.sumZeroAt_zero_of_sumZero L (sumZero_witTensor L hL 1)⟩

end RBM.Gauss.Q716
