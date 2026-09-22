/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSmoothWeightActual

/-!
# Same-sample higher-moment cutoff plateau

Positive support of either literal first-pass prefix weight at a fixed order `p ≥ 1`
puts the canonical actual smooth cutoff on its plateau.  Consequently the actual weight
at every higher order is one on the same sample.  This is only a deterministic comparison
of cutoff weights; it contains no moment estimate.
-/

namespace RBM.APrimeFirstCellHigherMomentCutoff

open Real Step2Bootstrap CutHypTheta Cutoff

/-- On the active branch, positive support of the doubled old prefix cutoff forces the
canonical actual smooth cutoff onto its order-independent plateau. -/
theorem cutoff_eq_one_of_widenedW_pos (d : Gauss.Dims)
    {E D δ : ℝ} {s t mesh : ℕ → ℝ}
    (hE : |E| < 2) (hδ : 0 ≤ δ)
    {N p k : ℕ} (ω : Gauss.Ω d)
    (hst : s N ≤ t N) (ht : t N < 1) (hmesh : 0 < mesh N)
    (hp : 1 ≤ p)
    (hactive : k ≤ cutNetTop s t mesh N ∧ 2 ≤ N)
    (hpos : 0 < APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ p N k ω) :
    APrimeSmoothWeightActual.cutoff d E D δ s mesh N k
      (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω = 1 := by
  let J : ℕ → ℝ → Gauss.Ω d → ℝ := fun N u ω =>
    Step2Moment.jSnorm (Gauss.sample d) E D s N u ω
  have hN : 0 < N := by omega
  have hold : k ≤ cutNetTop s t mesh N ∧ 1 ≤ N := ⟨hactive.1, by omega⟩
  by_cases hk : k = 0
  · subst k
    unfold APrimeSmoothWeightActual.cutoff
    rw [APrimeSmoothWeightActual.prefixSample_zero d E D s mesh N
      (APrimeSmoothWeightActual.canonicalM d s t mesh N)
      (APrimeSmoothWeightActual.canonicalM_pos d s t mesh N) ω]
    exact cutChi_eq_one (by simp)
  let θ : ℝ := 2 * Real.exp 1 * APrimePrior.priorLevel δ (fun _ => 1) N
  have hθ : 0 < θ := by
    dsimp [θ]
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
      (APrimePrior.priorLevel_pos (by omega) (by norm_num))
  have hsw : APrimeWeight.prefixSoftW (APrimeWeight.canonicalR s t mesh N)
      J s mesh N k θ ω ≠ 0 := by
    intro hzero
    rw [APrimeWeight.widenedW, if_pos hold] at hpos
    change 0 < (APrimeWeight.prefixSoftW (APrimeWeight.canonicalR s t mesh N)
      J s mesh N k θ ω) ^ (2 * p) at hpos
    rw [hzero, zero_pow (by omega : 2 * p ≠ 0)] at hpos
    exact (lt_irrefl 0) hpos
  have hJbound : ∀ j < k,
      Step2Moment.jSnorm (Gauss.sample d) E D s N
        (cutNetPt s mesh N j) ω ≤
      4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) := by
    intro j hj
    have habs := abs_le_two_mul_of_softW_ne_zero
      (r := APrimeWeight.canonicalR s t mesh N)
      (S := Finset.range k) (ρ := fun j => J N (cutNetPt s mesh N j) ω)
      (Θ := θ) (by simp [APrimeWeight.canonicalR]) hθ hsw
      (Finset.mem_range.mpr hj)
    calc
      _ ≤ |J N (cutNetPt s mesh N j) ω| := le_abs_self _
      _ ≤ 2 * θ := habs
      _ = 4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) := by
        simp [θ, APrimePrior.priorLevel]
        ring
  have hNcast : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hpow0 : 0 ≤ (N : ℝ) ^ (2 * δ) := by positivity
  have hn10 : (N : ℝ) ^ (-(10 : ℝ)) ≤ (N : ℝ) ^ (2 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hNcast (by linarith)
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have he2 : Real.exp 1 ≤ (Real.exp 1) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he1) he0]
  have hB0 : 0 ≤ 4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) := by positivity
  have hprefix := APrimeSmoothWeightActual.prefixSample_le_of_jSnorm_bound d
    (E := E) (D := D) (B := 4 * Real.exp 1 * (N : ℝ) ^ (2 * δ))
    (s := s) (t := t) (mesh := mesh) (N := N) (k := k)
    (m := APrimeSmoothWeightActual.canonicalM d s t mesh N)
    hE hst ht hmesh hN
    (APrimeSmoothWeightActual.canonicalM_pos d s t mesh N)
    hactive.1 hB0 ω hJbound
  have hcap : APrimeSmoothWeightActual.prefixSample d E D s mesh N k
      (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω ≤
      APrimeSmoothWeightActual.threshold δ N := by
    calc
      _ ≤ (((k * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
          ((1 : ℝ) / (2 * (APrimeSmoothWeightActual.canonicalM d s t mesh N : ℝ)))) *
          (4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) +
            (N : ℝ) ^ (-(10 : ℝ))) := hprefix
      _ ≤ Real.exp 1 * (4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) +
            (N : ℝ) ^ (-(10 : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (APrimeSmoothWeightActual.canonicalM_calibration d s t mesh N k hactive.1)
          (by positivity)
      _ ≤ Real.exp 1 * (4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) +
            (N : ℝ) ^ (2 * δ)) :=
        mul_le_mul_of_nonneg_left (by simpa only [add_comm] using
          (add_le_add_left hn10 (4 * Real.exp 1 * (N : ℝ) ^ (2 * δ)))) he0
      _ = 4 * (Real.exp 1) ^ 2 * (N : ℝ) ^ (2 * δ) +
            Real.exp 1 * (N : ℝ) ^ (2 * δ) := by ring
      _ ≤ 5 * (Real.exp 1) ^ 2 * (N : ℝ) ^ (2 * δ) := by
        nlinarith [mul_le_mul_of_nonneg_right he2 hpow0]
      _ ≤ APrimeSmoothWeightActual.threshold δ N := by
        unfold APrimeSmoothWeightActual.threshold
        nlinarith [sq_nonneg (Real.exp 1)]
  unfold APrimeSmoothWeightActual.cutoff
  exact cutChi_eq_one
    ((div_le_one (APrimeSmoothWeightActual.threshold_pos hN)).2 hcap)

/-- Positive support of the doubled target weight makes every canonical actual moment
weight equal to one on the same sample.  The inactive, small-size, and empty-prefix
branches are handled by the definitions. -/
theorem weight_eq_one_of_widenedW_pos (d : Gauss.Dims)
    {E D δ : ℝ} {s t mesh : ℕ → ℝ}
    (hE : |E| < 2) (hδ : 0 ≤ δ)
    {N p k : ℕ} (ω : Gauss.Ω d)
    (hst : s N ≤ t N) (ht : t N < 1) (hmesh : 0 < mesh N)
    (hp : 1 ≤ p) (P : ℕ) :
    0 < APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ p N k ω →
    APrimeSmoothWeightActual.weight d E D δ s t mesh 2 P N k
      (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω = 1 := by
  intro hpos
  by_cases hactive : k ≤ cutNetTop s t mesh N ∧ 2 ≤ N
  · by_cases hk : k = 0
    · subst k
      exact APrimeSmoothWeightActual.weight_zero_prefix d E D δ s t mesh 2 P N
        (APrimeSmoothWeightActual.canonicalM d s t mesh N)
        (APrimeSmoothWeightActual.canonicalM_pos d s t mesh N) ω
    · have hcut := cutoff_eq_one_of_widenedW_pos d hE hδ ω hst ht hmesh hp
        hactive hpos
      rw [APrimeSmoothWeightActual.weight, if_pos hactive, hcut, one_pow]
  · rw [APrimeSmoothWeightActual.weight, if_neg hactive]

/-- The narrow literal target weight has the same plateau consequence. -/
theorem weight_eq_one_of_piecewiseW_pos (d : Gauss.Dims)
    {E D δ : ℝ} {s t mesh : ℕ → ℝ}
    (hE : |E| < 2) (hδ : 0 ≤ δ)
    {N p k : ℕ} (ω : Gauss.Ω d)
    (hst : s N ≤ t N) (ht : t N < 1) (hmesh : 0 < mesh N)
    (hp : 1 ≤ p) (P : ℕ) :
    0 < APrimeWeight.piecewiseW (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ N k ω →
    APrimeSmoothWeightActual.weight d E D δ s t mesh 2 P N k
      (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω = 1 := by
  intro hpos
  apply weight_eq_one_of_widenedW_pos d hE hδ ω hst ht hmesh hp P
  exact hpos.trans_le (APrimeWeight.piecewiseW_le_widenedW
    (r := APrimeWeight.canonicalR s t mesh) (N₀ := 1)
    (J := fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
    (s := s) (t := t) (mesh := mesh) (by norm_num) δ p N k ω)

/-- Pointwise same-sample domination for a doubled target cutoff and an arbitrary
nonnegative even-power integrand. -/
theorem widenedW_mul_abs_pow_le_weight_mul (d : Gauss.Dims)
    {E D δ : ℝ} {s t mesh : ℕ → ℝ}
    (hE : |E| < 2) (hδ : 0 ≤ δ)
    {N p k : ℕ} (ω : Gauss.Ω d)
    (hst : s N ≤ t N) (ht : t N < 1) (hmesh : 0 < mesh N)
    (hp : 1 ≤ p) (P : ℕ) (Y : ℝ) :
    APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
        s t mesh δ p N k ω * |Y| ^ (2 * P) ≤
      APrimeSmoothWeightActual.weight d E D δ s t mesh 2 P N k
        (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω * |Y| ^ (2 * P) := by
  let w := APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
    (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
    s t mesh δ p N k ω
  by_cases hw : w = 0
  · rw [show APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
        s t mesh δ p N k ω = 0 from hw]
    simpa only [zero_mul] using mul_nonneg
      (APrimeSmoothWeightActual.weight_nonneg d E D δ s t mesh 2 P N k
        (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω)
      (pow_nonneg (abs_nonneg Y) (2 * P))
  · have hw0 : 0 ≤ w := APrimeWeight.widenedW_nonneg
      (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ p N k ω
    have hwpos : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hw)
    have hone := weight_eq_one_of_widenedW_pos d hE hδ ω hst ht hmesh hp P hwpos
    rw [hone, one_mul]
    exact mul_le_of_le_one_left (by positivity) (APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ p N k ω)

/-- Pointwise same-sample domination for the narrow literal target cutoff. -/
theorem piecewiseW_mul_abs_pow_le_weight_mul (d : Gauss.Dims)
    {E D δ : ℝ} {s t mesh : ℕ → ℝ}
    (hE : |E| < 2) (hδ : 0 ≤ δ)
    {N p k : ℕ} (ω : Gauss.Ω d)
    (hst : s N ≤ t N) (ht : t N < 1) (hmesh : 0 < mesh N)
    (hp : 1 ≤ p) (P : ℕ) (Y : ℝ) :
    APrimeWeight.piecewiseW (APrimeWeight.canonicalR s t mesh) 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
        s t mesh δ N k ω * |Y| ^ (2 * P) ≤
      APrimeSmoothWeightActual.weight d E D δ s t mesh 2 P N k
        (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω * |Y| ^ (2 * P) := by
  let w := APrimeWeight.piecewiseW (APrimeWeight.canonicalR s t mesh) 1
    (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
    s t mesh δ N k ω
  by_cases hw : w = 0
  · rw [show APrimeWeight.piecewiseW (APrimeWeight.canonicalR s t mesh) 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
        s t mesh δ N k ω = 0 from hw]
    simpa only [zero_mul] using mul_nonneg
      (APrimeSmoothWeightActual.weight_nonneg d E D δ s t mesh 2 P N k
        (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω)
      (pow_nonneg (abs_nonneg Y) (2 * P))
  · have hw0 : 0 ≤ w := APrimeWeight.piecewiseW_nonneg
      (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ N k ω
    have hwpos : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hw)
    have hone := weight_eq_one_of_piecewiseW_pos d hE hδ ω hst ht hmesh hp P hwpos
    rw [hone, one_mul]
    exact mul_le_of_le_one_left (by positivity) (APrimeWeight.piecewiseW_le_one
      (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ N k ω)

#print axioms cutoff_eq_one_of_widenedW_pos
#print axioms weight_eq_one_of_widenedW_pos
#print axioms weight_eq_one_of_piecewiseW_pos
#print axioms widenedW_mul_abs_pow_le_weight_mul
#print axioms piecewiseW_mul_abs_pow_le_weight_mul

end RBM.APrimeFirstCellHigherMomentCutoff
