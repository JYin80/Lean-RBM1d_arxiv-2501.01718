/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Moment

/-!
# Lemma 7.3, (7.16), pointwise

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 7.3, (7.13)–(7.24).

This module packages the pointwise, deterministic kernel bounds of Lemma 7.3 for the paper's
edge parameter `ξ_i = m(σ_i) m(σ_{i+1})` (Definition 5.2, cyclic:
`i + 1 : Fin n` wraps).

**Nothing here is new mathematics.** Every bound is `RBM.norm_Uker_fastDecay_le`,
`RBM.norm_Uker_fastDecay_le_of_eq`, `RBM.norm_Uker_fastDecay_le_sumZero_sigma`
(`Hierarchy/KernelDecay.lean`), where the paper's `W^{C_nτ}` becomes a free parameter `K ≥ 1`
and `W^{-D}` becomes an explicit `δ ≥ 0`. This file only specialises `ξ` to
`xiOf (mSigma E) σ` and renames the results.

## Main results

* `RBM.Gauss.Q716.uker_decay_le_nonAlt`  : **(7.16), Case 1** (`σ_k = σ_{k+1}` for some `k`,
  cyclic)
* `RBM.Gauss.Q716.uker_decay_le_sumZero` : **(7.16), Case 2** (sum-zero, (7.15))

## Deviation from the literal paper wording

The paper writes the error term of (7.14)/(7.16) as a bare `W^{-D+C_n}`, with no
`s,t`-dependence. Taken literally (for *arbitrary* `0 ≤ s ≤ t < 1`, with `D`, `W`, `E`, `n`
fixed) that is false: the constant tensor `A ≡ δ` is `(ℓ, δ)`-fast-decaying for every `ℓ`
and bounded by `M = δ`, and for a real edge charge (`|ξ_i| = 1`) the exact value of
`(U_{s,t,σ} ∘ A)_a` is `δ · ((1-s)/(1-t))^n`, unbounded as `t → 1⁻` for fixed `s, δ, n`. This
is the failure pattern of an `N`-independent edge-kernel ratio on the grid, applied to the
*literal* wording rather than to the quantity the route actually needs. The bounds below keep the
`η_s/η_t` ratio explicit in the error term (`((1-s)/(1-t))^n · δ`) instead, exactly as the
`Hierarchy/KernelDecay.lean` lemmas do; this is the form the moment route consumes.
-/

namespace RBM.Gauss.Q716

/-- **(T2) Lemma 7.3, (7.16) Case 1**: a cyclic non-alternating charge (`σ k = σ (k+1)` for
some `k`, indices in `Fin n`, matching `xiOf`'s cyclic `i + 1`). The `ℓ_t/ℓ_s` factor of (7.14)
disappears; the constant also depends on the fixed bulk gap `κ := min (2 - |E|) 1 > 0`
(the row-sum bound `Σ|Ξ_k| = O(1)` needs `ξ_k = m² ≠` too close to `1`, uniform in
`t ∈ [0,1)`), which is a function of `E` alone, not of `N, W, L, s, t`. -/
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

end RBM.Gauss.Q716
