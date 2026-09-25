/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FirstCellStep1LocalLaw
import RBM1D.Gauss.Eq45FlowBudget
import RBM1D.Gauss.LDEDiag

/-!
# Random-`Lmax` fluctuation averaging: first-cell entry preflight

This module records the actual first-cell same-sample entry witness for the
random-control fluctuation-averaging implication.  It deliberately does not
claim that implication: the common-deleted-minor moment estimate for
row-normalized fluctuations is not yet formalized here.  In particular, the
deterministic-scale theorem in `DetFlucAvgComplete` is not used as a substitute.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-- The first-cell deterministic weak-law scale squared is `1/(4W)`. -/
theorem firstCellPsi_sq_eq_invW_div_four (N : ℕ) :
    firstCellPsi N ^ 2 = ((Dims.exampleGrow.W N : ℝ)⁻¹) / 4 := by
  have hW : 0 ≤ (Dims.exampleGrow.W N : ℝ) := Nat.cast_nonneg _
  have hp : ((Dims.exampleGrow.W N : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 =
      ((Dims.exampleGrow.W N : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW]
    norm_num only [mul_div_cancel_left₀, mul_one]
    rw [Real.rpow_neg hW, Real.rpow_one]
  unfold firstCellPsi
  rw [div_pow, hp]
  ring

/-- The first-cell event threshold has squared size `N^(1/8) Ψ²`. -/
theorem firstCellDelta_sq_eq (N : ℕ) :
    firstCellDelta N ^ 2 = (N : ℝ) ^ ((1 : ℝ) / 8) * firstCellPsi N ^ 2 := by
  have hp : ((N : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 =
      (N : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1 <;> norm_num
  rw [firstCellDelta, mul_pow, hp]

/-- The entry threshold is at most `N^(-1/8)` eventually, so the same event
provides a polynomial weak entry law. -/
theorem firstCellDelta_le_rpow_neg_one_eighth :
    ∀ᶠ N : ℕ in atTop,
      firstCellDelta N ≤ (N : ℝ) ^ (-(1 : ℝ) / 8) := by
  filter_upwards [firstCellPsi_le_rpow_neg_quarter, eventually_ge_atTop 1]
    with N hΨ hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hΨ0 : 0 ≤ firstCellPsi N := (firstCellPsi_pos N).le
  have hmono :
      (N : ℝ) ^ ((1 : ℝ) / 16) * firstCellPsi N ≤
        (N : ℝ) ^ ((1 : ℝ) / 16) * (N : ℝ) ^ (-(1 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left hΨ (Real.rpow_nonneg hN0.le _)
  have hprod :
      (N : ℝ) ^ ((1 : ℝ) / 16) * (N : ℝ) ^ (-(1 : ℝ) / 4) =
        (N : ℝ) ^ (-(3 : ℝ) / 16) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  calc
    firstCellDelta N = (N : ℝ) ^ ((1 : ℝ) / 16) * firstCellPsi N := rfl
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 16) * (N : ℝ) ^ (-(1 : ℝ) / 4) := hmono
    _ = (N : ℝ) ^ (-(3 : ℝ) / 16) := hprod
    _ ≤ (N : ℝ) ^ (-(1 : ℝ) / 8) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)

/-- On one actual weak-law sample, every entry square is controlled by the
same realized `Lmax`, with only the polynomial `N^(1/8)` loss. -/
theorem firstCell_entry_sq_le_randomLmax
    {τ' : ℝ} {N : ℕ}
    {ω : Ω Dims.exampleGrow}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ')
      (firstCellT τ') firstCellDelta N)
    (hδ : firstCellDelta N ≤ 1 / 2)
    {u : ℝ} (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (ij : Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N) :
    ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
      (if ij.1 = ij.2 then mE 0 else 0)‖ ^ 2 ≤
        (N : ℝ) ^ ((1 : ℝ) / 8) *
          Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by
  have hflow : ω ∈ goodSetFlow Dims.exampleGrow 0 (firstCellS τ')
      (firstCellT τ') firstCellDelta N := hω.1
  have hgood : GoodEvent (green (Hflow Dims.exampleGrow N u ω) (zt 0 u))
      (mE 0) (firstCellDelta N) := hflow u hu
  have hlow := inv_W_le_Lmax_flow (d := Dims.exampleGrow) (s := firstCellS τ')
    (t := firstCellT τ') (δ := firstCellDelta) (E := 0) (N := N)
    (by norm_num : |(0 : ℝ)| ≤ 2) hδ hflow hu
  have hnorm := hgood ij.1 ij.2
  have hδ0 : 0 ≤ firstCellDelta N := by
    unfold firstCellDelta firstCellPsi
    positivity
  have hentry :
      ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
        (if ij.1 = ij.2 then mE 0 else 0)‖ ^ 2 ≤ firstCellDelta N ^ 2 := by
    nlinarith [norm_nonneg
      (green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
        (if ij.1 = ij.2 then mE 0 else 0))]
  have hψ : firstCellPsi N ^ 2 ≤
      Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by
    rw [firstCellPsi_sq_eq_invW_div_four]
    nlinarith [hlow]
  calc
    ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
        (if ij.1 = ij.2 then mE 0 else 0)‖ ^ 2 ≤ firstCellDelta N ^ 2 := hentry
    _ = (N : ℝ) ^ ((1 : ℝ) / 8) * firstCellPsi N ^ 2 := firstCellDelta_sq_eq N
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 8) *
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) :=
      mul_le_mul_of_nonneg_left hψ
        (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le N)) _)

/-- A single first-cell good sample simultaneously satisfies the polynomial
weak entry bound and the entry-square `REL` bound against its own `Lmax`.
The event is the existing actual Gaussian flow event, not a pair of separately
selected samples. -/
theorem firstCell_randomLmax_sameEvent_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ᶠ N : ℕ in atTop,
        firstCellS τ' N < firstCellT τ' N ∧
        ∃ ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ')
          (firstCellT τ') firstCellDelta N,
          ∀ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
            ∀ ij : Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N,
              ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
                (if ij.1 = ij.2 then mE 0 else 0)‖ ≤ (N : ℝ) ^ (-(1 : ℝ) / 8) ∧
              ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
                (if ij.1 = ij.2 then mE 0 else 0)‖ ^ 2 ≤
                (N : ℝ) ^ ((1 : ℝ) / 8) *
                  Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by
  obtain ⟨τ', hτ', hll, hnonempty⟩ := firstCell_step1_localLaw_witness
  refine ⟨τ', hτ', ?_⟩
  have hδhalf : ∀ᶠ N : ℕ in atTop, firstCellDelta N ≤ 1 / 2 := by
    filter_upwards [firstCellDelta_le_rpow_neg_one_eighth,
      eventually_le_rpow 2 (by norm_num : 0 < (1 : ℝ) / 8),
      eventually_ge_atTop 1] with N hδ hpow hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hpowInv : (N : ℝ) ^ (-(1 : ℝ) / 8) =
        ((N : ℝ) ^ ((1 : ℝ) / 8))⁻¹ := by
      rw [show (-(1 : ℝ) / 8) = -((1 : ℝ) / 8) by ring,
        Real.rpow_neg hN0.le]
    have hinv : ((N : ℝ) ^ ((1 : ℝ) / 8))⁻¹ ≤ (2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) hpow
    rw [hpowInv] at hδ
    norm_num at hinv
    exact hδ.trans hinv
  filter_upwards [hnonempty, firstCellDelta_le_rpow_neg_one_eighth,
    hδhalf] with N hnon hpoly hhalf
  rcases hnon with ⟨hinterval, hset⟩
  obtain ⟨ω, hω⟩ := hset
  refine ⟨hinterval, ω, hω, ?_⟩
  intro u hu ij
  have hgood : GoodEvent (green (Hflow Dims.exampleGrow N u ω) (zt 0 u))
      (mE 0) (firstCellDelta N) := hω.1 u hu
  have hnorm := hgood ij.1 ij.2
  have hlinear :
      ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
        (if ij.1 = ij.2 then mE 0 else 0)‖ ≤ (N : ℝ) ^ (-(1 : ℝ) / 8) :=
    hnorm.trans hpoly
  refine ⟨hlinear, ?_⟩
  exact firstCell_entry_sq_le_randomLmax hω hhalf hu ij

/-- At every positive interior time, an actual diagonal coordinate of the
Gaussian flow has positive second moment. -/
theorem firstCell_positive_diag_flow_second_moment
    {N : ℕ} (i : Dims.exampleGrow.Idx N)
    {u : ℝ} (hu : 0 < u) :
    0 < ∫ ω, ‖Hflow Dims.exampleGrow N u ω i i‖ ^ 2 ∂(P Dims.exampleGrow) := by
  have hu0 : 0 ≤ u := hu.le
  rw [integral_norm_Hflow_diag_pow hu0 i 1]
  have hW : 0 < (Dims.exampleGrow.W N : ℝ) := by
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hdiag : Sblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) i i =
      (1 / 3 : ℝ) / (Dims.exampleGrow.W N : ℝ) := by
    unfold Sblk sbKre
    rw [sub_self]
    have hmem : (0 : ZMod (Dims.exampleGrow.L N)) ∈ sbSupport (Dims.exampleGrow.L N) := by
      rw [sbSupport]
      exact Finset.mem_insert_self _ _
    rw [if_pos hmem]
  simp [dfac] at *
  rw [hdiag]
  positivity

/-- The first cell has a positive interior deterministic time. -/
theorem firstCell_positive_interior_time {τ' : ℝ} {N : ℕ}
    (hinterval : firstCellS τ' N < firstCellT τ' N) :
    ∃ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
      0 < u ∧ u < firstCellT τ' N := by
  have hs : firstCellS τ' N = 0 := by
    unfold firstCellS
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have ht : 0 < firstCellT τ' N := by rw [← hs]; exact hinterval
  refine ⟨firstCellT τ' N / 2, ?_⟩
  constructor
  · simp only [Set.mem_Icc]
    rw [hs]
    constructor
    · exact (div_nonneg ht.le (by norm_num))
    · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [ht.le]
  · constructor
    · exact div_pos ht (by norm_num)
    · rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [ht]

/-- Package the entry WLL/REL bounds and a positive-time variance witness with
the same nonempty actual flow-event sample. -/
theorem firstCell_randomLmax_nondegenerate_sameEvent_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ')
          (firstCellT τ') firstCellDelta N,
          (∀ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
            ∀ ij : Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N,
              ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
                (if ij.1 = ij.2 then mE 0 else 0)‖ ≤ (N : ℝ) ^ (-(1 : ℝ) / 8) ∧
              ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
                (if ij.1 = ij.2 then mE 0 else 0)‖ ^ 2 ≤
                (N : ℝ) ^ ((1 : ℝ) / 8) *
                  Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ∧
          ∃ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
            0 < u ∧ u < firstCellT τ' N ∧
            ∀ i : Dims.exampleGrow.Idx N,
              0 < ∫ ω', ‖Hflow Dims.exampleGrow N u ω' i i‖ ^ 2
                ∂(P Dims.exampleGrow) := by
  obtain ⟨τ', hτ', hN⟩ := firstCell_randomLmax_sameEvent_witness
  refine ⟨τ', hτ', ?_⟩
  filter_upwards [hN] with N hN
  rcases hN with ⟨hinterval, ω, hω, hentries⟩
  obtain ⟨u, hu, hu0, hut⟩ := firstCell_positive_interior_time hinterval
  refine ⟨ω, hω, hentries, u, hu, hu0, hut, ?_⟩
  intro i
  exact firstCell_positive_diag_flow_second_moment i hu0

#print axioms firstCellPsi_sq_eq_invW_div_four
#print axioms firstCellDelta_sq_eq
#print axioms firstCellDelta_le_rpow_neg_one_eighth
#print axioms firstCell_entry_sq_le_randomLmax
#print axioms firstCell_randomLmax_sameEvent_witness
#print axioms firstCell_positive_diag_flow_second_moment
#print axioms firstCell_positive_interior_time
#print axioms firstCell_randomLmax_nondegenerate_sameEvent_witness

end RBM.Gauss
