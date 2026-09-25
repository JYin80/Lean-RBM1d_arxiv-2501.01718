/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.SemicircleQuantileCells
import RBM1D.Defs.SemicircleFlowResolvent
import RBM1D.Defs.SemicircleCDFReflection

/-! # Semicircle quantile quadrature on the closed flow line -/

namespace RBM

open MeasureTheory Set Complex

noncomputable section

private def qkern (u x : ℝ) : ℂ :=
  (((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ))⁻¹

private def qden (u x : ℝ) : ℂ :=
  ((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ)

private theorem qden_gap (u x : ℝ) (hu : u ≤ 1 / 2) : 1-u ≤ ‖qden u x‖ :=
  semicircleFlowResolvent_denominator_gap u x hu

private theorem qden_ne (u x : ℝ) (hu : u ≤ 1 / 2) : qden u x ≠ 0 := by
  have h := qden_gap u x hu
  intro hz
  rw [hz, norm_zero] at h
  linarith

private theorem qkern_sub (u s x : ℝ) (hu : u ≤ 1 / 2) :
    qkern u s - qkern u x =
      ((Real.sqrt u * (x-s) : ℝ) : ℂ) * (qden u s)⁻¹ * (qden u x)⁻¹ := by
  have hs := qden_ne u s hu
  have hx := qden_ne u x hu
  dsimp [qkern]
  change (qden u s)⁻¹ - (qden u x)⁻¹ = _
  field_simp
  simp only [qden]
  push_cast
  ring

private theorem qkern_lipschitz (u s x : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    ‖qkern u s - qkern u x‖ ≤ 2 * Real.sqrt 2 * |s-x| := by
  have hbs : (1/2 : ℝ) ≤ ‖qden u s‖ := by
    have h := qden_gap u s hu1
    linarith
  have hbx : (1/2 : ℝ) ≤ ‖qden u x‖ := by
    have h := qden_gap u x hu1
    linarith
  have his : ‖(qden u s)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc
      ‖qden u s‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
        (inv_le_inv₀ (by linarith : 0 < ‖qden u s‖) (by norm_num)).2 hbs
      _ = 2 := by norm_num
  have hix : ‖(qden u x)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc
      ‖qden u x‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
        (inv_le_inv₀ (by linarith : 0 < ‖qden u x‖) (by norm_num)).2 hbx
      _ = 2 := by norm_num
  have hsqrt : 2 * Real.sqrt u ≤ Real.sqrt 2 := by
    have hsq := Real.sq_sqrt hu0
    have hsq2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg u
    have hn2 := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  rw [qkern_sub u s x hu1, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg u), norm_inv]
  rw [abs_sub_comm]
  calc
    Real.sqrt u * |s-x| * ‖qden u s‖⁻¹ * ‖qden u x‖⁻¹
        ≤ Real.sqrt u * |s-x| * 2 * 2 := by
          gcongr
          · simpa only [norm_inv] using his
          · simpa only [norm_inv] using hix
    _ ≤ 2 * Real.sqrt 2 * |s-x| := by
      have habs : 0 ≤ |s-x| := abs_nonneg _
      nlinarith

private def qgamma (W : ℕ) (hW : 1 ≤ W) (j : ℕ) : ℝ :=
  semicircleGamma W hW (min j W) (Nat.min_le_right j W)

/-- The T883 midpoint at indices `j<W`, extended by the last midpoint elsewhere. -/
def semicircleQuadratureLambda (W : ℕ) (hW : 1 ≤ W) (j : ℕ) : ℝ :=
  semicircleLambda W hW (min j (W-1))
    (lt_of_le_of_lt (Nat.min_le_right j (W-1)) (by omega))

theorem semicircleQuadratureLambda_eq (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j < W) :
    semicircleQuadratureLambda W hW j = semicircleLambda W hW j hj := by
  have hle : j ≤ W-1 := by omega
  simp [semicircleQuadratureLambda, Nat.min_eq_left hle]

private theorem qgamma_eq (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j ≤ W) :
    qgamma W hW j = semicircleGamma W hW j hj := by
  simp [qgamma, Nat.min_eq_left hj]

private theorem qgamma_zero (W : ℕ) (hW : 1 ≤ W) : qgamma W hW 0 = -2 := by
  rw [qgamma_eq W hW 0 (Nat.zero_le W), semicircleGamma_zero]

private theorem qgamma_last (W : ℕ) (hW : 1 ≤ W) : qgamma W hW W = 2 := by
  rw [qgamma_eq W hW W le_rfl, semicircleGamma_last]

private theorem qgamma_mono (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j < W) :
    qgamma W hW j < qgamma W hW (j+1) := by
  rw [qgamma_eq W hW j (Nat.le_of_lt hj),
    qgamma_eq W hW (j+1) (Nat.succ_le_of_lt hj)]
  exact semicircleGamma_strictMono W hW hj

private theorem qgamma_monotone (W : ℕ) (hW : 1 ≤ W) : Monotone (qgamma W hW) :=
  monotone_nat_of_le_succ (fun n => by
    by_cases hn : n < W
    · exact (qgamma_mono W hW n hn).le
    · have hWn : W ≤ n := Nat.le_of_not_gt hn
      simp [qgamma, Nat.min_eq_right hWn,
        Nat.min_eq_right (hWn.trans (Nat.le_succ n))])

private theorem qcell_mass (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j < W) :
    semicircleMeasure (Ioc (qgamma W hW j) (qgamma W hW (j+1))) =
      ENNReal.ofReal (1 / (W : ℝ)) := by
  rw [qgamma_eq W hW j (Nat.le_of_lt hj),
    qgamma_eq W hW (j+1) (Nat.succ_le_of_lt hj)]
  exact semicircleQuantileCell_mass W hW j hj

private theorem qcell_real (W : ℕ) (hW : 1 ≤ W) (j : ℕ) (hj : j < W) :
    semicircleMeasure.real (Ioc (qgamma W hW j) (qgamma W hW (j+1))) =
      1 / (W : ℝ) := by
  rw [Measure.real, qcell_mass W hW j hj, ENNReal.toReal_ofReal]
  positivity

private theorem qcell_union (W : ℕ) (hW : 1 ≤ W) :
    (⋃ j ∈ Finset.range W, Ioc (qgamma W hW j) (qgamma W hW (j+1))) =
      Ioc (-2 : ℝ) 2 := by
  have hpart : ∀ n ≤ W,
      (⋃ j ∈ Finset.range n, Ioc (qgamma W hW j) (qgamma W hW (j+1))) =
        Ioc (qgamma W hW 0) (qgamma W hW n) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hn' : n < W := Nat.lt_of_succ_le hn
      rw [Finset.range_add_one, Finset.set_biUnion_insert,
        ih (Nat.le_of_lt hn'), Set.union_comm]
      exact Ioc_union_Ioc_eq_Ioc (qgamma_monotone W hW (Nat.zero_le n))
        (qgamma_mono W hW n hn').le
  rw [hpart W le_rfl, qgamma_zero, qgamma_last]

private theorem qcell_pairwise (W : ℕ) (hW : 1 ≤ W) :
    Set.Pairwise (↑(Finset.range W))
      (fun i j => Disjoint (Ioc (qgamma W hW i) (qgamma W hW (i+1)))
        (Ioc (qgamma W hW j) (qgamma W hW (j+1)))) := by
  have hmono : Monotone (qgamma W hW) := qgamma_monotone W hW
  intro i hi j hj hij
  have hi' : i < W := Finset.mem_range.mp hi
  have hj' : j < W := Finset.mem_range.mp hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : i+1 ≤ j := Nat.succ_le_of_lt h
    exact Ioc_disjoint_Ioc_of_le (hmono hle)
  · have hle : j+1 ≤ i := Nat.succ_le_of_lt h
    exact (Ioc_disjoint_Ioc_of_le (hmono hle)).symm

private theorem qcell_compl_null :
    semicircleMeasure (Ioc (-2 : ℝ) 2)ᶜ = 0 := by
  have hsub : (Ioc (-2 : ℝ) 2)ᶜ ⊆
      (Icc (-2 : ℝ) 2)ᶜ ∪ {(-2 : ℝ)} := by
    intro x hx
    by_cases h : x = -2
    · exact Or.inr h
    · left
      intro hx'
      exact hx ⟨lt_of_le_of_ne hx'.1 (Ne.symm h), hx'.2⟩
  refine le_antisymm ?_ bot_le
  calc
    semicircleMeasure (Ioc (-2 : ℝ) 2)ᶜ ≤
        semicircleMeasure ((Icc (-2 : ℝ) 2)ᶜ ∪ {(-2 : ℝ)}) :=
      measure_mono hsub
    _ ≤ semicircleMeasure (Icc (-2 : ℝ) 2)ᶜ +
        semicircleMeasure ({(-2 : ℝ)} : Set ℝ) := measure_union_le _ _
    _ = 0 := by rw [semicircleMeasure_compl_Icc, semicircleMeasure_singleton]; simp

private theorem qkern_integral_eq_cell_sum (W : ℕ) (hW : 1 ≤ W)
    (u : ℝ) (hu : u ≤ 1 / 2) :
    (∫ x : ℝ, qkern u x ∂semicircleMeasure) =
      ∑ j ∈ Finset.range W,
        ∫ x in Ioc (qgamma W hW j) (qgamma W hW (j+1)),
          qkern u x ∂semicircleMeasure := by
  have hi : Integrable (qkern u) semicircleMeasure :=
    semicircleFlowResolvent_integrable u hu
  have hset : (∫ x in Ioc (-2 : ℝ) 2, qkern u x ∂semicircleMeasure) =
      ∫ x : ℝ, qkern u x ∂semicircleMeasure := by
    have h := integral_add_compl (f := qkern u) (μ := semicircleMeasure)
      (s := Ioc (-2 : ℝ) 2)
      measurableSet_Ioc hi
    simpa [qcell_compl_null] using h
  rw [← hset, ← qcell_union W hW]
  exact integral_biUnion_finset (Finset.range W)
    (fun j hj => measurableSet_Ioc) (qcell_pairwise W hW)
    (fun j hj => hi.integrableOn)

private theorem qcell_rep_integral (W : ℕ) (hW : 1 ≤ W)
    (u : ℝ) (j : ℕ) (hj : j < W) :
    (∫ _x in Ioc (qgamma W hW j) (qgamma W hW (j+1)),
      qkern u (semicircleQuadratureLambda W hW j) ∂semicircleMeasure) =
      (1 / (W : ℝ)) • qkern u (semicircleQuadratureLambda W hW j) := by
  rw [setIntegral_const, qcell_real W hW j hj]

private theorem qcell_error_le (W : ℕ) (hW : 1 ≤ W)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (j : ℕ) (hj : j < W) :
    ‖∫ x in Ioc (qgamma W hW j) (qgamma W hW (j+1)),
      (qkern u (semicircleQuadratureLambda W hW j) - qkern u x)
        ∂semicircleMeasure‖ ≤
      (2 * Real.sqrt 2 / (W : ℝ)) *
        (qgamma W hW (j+1) - qgamma W hW j) := by
  have hrep := semicircleGamma_lt_Lambda_lt_Gamma_succ W hW hj
  rw [← qgamma_eq W hW j (Nat.le_of_lt hj),
    ← qgamma_eq W hW (j+1) (Nat.succ_le_of_lt hj),
    ← semicircleQuadratureLambda_eq W hW j hj] at hrep
  have hfinite : semicircleMeasure
      (Ioc (qgamma W hW j) (qgamma W hW (j+1))) < ⊤ :=
    measure_lt_top semicircleMeasure _
  have h := norm_setIntegral_le_of_norm_le_const (μ := semicircleMeasure)
    (f := fun x : ℝ => qkern u (semicircleQuadratureLambda W hW j) - qkern u x)
    (s := Ioc (qgamma W hW j) (qgamma W hW (j+1)))
    (C := 2 * Real.sqrt 2 * (qgamma W hW (j+1) - qgamma W hW j))
    hfinite (by
      intro x hx
      have hdist : |semicircleQuadratureLambda W hW j - x| ≤
          qgamma W hW (j+1) - qgamma W hW j := by
        rw [abs_le]
        constructor <;> linarith [hrep.1, hrep.2, hx.1, hx.2]
      exact (qkern_lipschitz u _ x hu0 hu1).trans
        (mul_le_mul_of_nonneg_left hdist (by positivity)))
  rw [qcell_real W hW j hj] at h
  convert h using 1; ring

private theorem qcell_integral_sub (W : ℕ) (hW : 1 ≤ W)
    (u : ℝ) (hu : u ≤ 1 / 2) (j : ℕ) (hj : j < W) :
    (∫ x in Ioc (qgamma W hW j) (qgamma W hW (j+1)),
      (qkern u (semicircleQuadratureLambda W hW j) - qkern u x)
        ∂semicircleMeasure) =
      (1 / (W : ℝ)) • qkern u (semicircleQuadratureLambda W hW j) -
        ∫ x in Ioc (qgamma W hW j) (qgamma W hW (j+1)),
          qkern u x ∂semicircleMeasure := by
  have hfinite : semicircleMeasure
      (Ioc (qgamma W hW j) (qgamma W hW (j+1))) < ⊤ :=
    measure_lt_top semicircleMeasure _
  have hc : Integrable (fun _ : ℝ => qkern u (semicircleQuadratureLambda W hW j))
      (semicircleMeasure.restrict
        (Ioc (qgamma W hW j) (qgamma W hW (j+1)))) :=
    integrableOn_const hfinite.ne
  have hk : Integrable (qkern u)
      (semicircleMeasure.restrict
        (Ioc (qgamma W hW j) (qgamma W hW (j+1)))) :=
    (semicircleFlowResolvent_integrable u hu).integrableOn
  rw [integral_sub hc hk,
    qcell_rep_integral W hW u j hj]

/-- The closed-flow quadrature error uses the sum of every cell width. -/
theorem semicircleQuadrature_closed_flow (W : ℕ) (hW : 1 ≤ W)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    ‖(1 / (W : ℝ)) •
        (∑ j ∈ Finset.range W, qkern u (semicircleQuadratureLambda W hW j)) -
        Complex.I‖ ≤ 8 * Real.sqrt 2 / (W : ℝ) := by
  have hsum :
      (1 / (W : ℝ)) •
          (∑ j ∈ Finset.range W, qkern u (semicircleQuadratureLambda W hW j)) -
          (∫ x : ℝ, qkern u x ∂semicircleMeasure) =
        ∑ j ∈ Finset.range W,
          ∫ x in Ioc (qgamma W hW j) (qgamma W hW (j+1)),
            (qkern u (semicircleQuadratureLambda W hW j) - qkern u x)
              ∂semicircleMeasure := by
    rw [qkern_integral_eq_cell_sum W hW u hu1,
      Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact (qcell_integral_sub W hW u hu1 j (Finset.mem_range.mp hj)).symm
  have hwidth :
      (∑ j ∈ Finset.range W,
        (qgamma W hW (j+1) - qgamma W hW j)) = 4 := by
    rw [Finset.sum_range_sub, qgamma_last, qgamma_zero]
    ring
  have hint : (∫ x : ℝ, qkern u x ∂semicircleMeasure) = Complex.I :=
    semicircleFlowResolvent_integral u hu0 hu1
  rw [← hint, hsum]
  calc
    ‖∑ j ∈ Finset.range W,
        ∫ x in Ioc (qgamma W hW j) (qgamma W hW (j+1)),
          (qkern u (semicircleQuadratureLambda W hW j) - qkern u x)
            ∂semicircleMeasure‖
      ≤ ∑ j ∈ Finset.range W,
          ‖∫ x in Ioc (qgamma W hW j) (qgamma W hW (j+1)),
            (qkern u (semicircleQuadratureLambda W hW j) - qkern u x)
              ∂semicircleMeasure‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range W,
        (2 * Real.sqrt 2 / (W : ℝ)) *
          (qgamma W hW (j+1) - qgamma W hW j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact qcell_error_le W hW u hu0 hu1 j (Finset.mem_range.mp hj)
    _ = 8 * Real.sqrt 2 / (W : ℝ) := by
      rw [← Finset.mul_sum, hwidth]
      ring

/-- Exact kernel form of the deterministic `8√2/W` quadrature bound. -/
theorem semicircleQuadrature_closed_flow_explicit (W : ℕ) (hW : 1 ≤ W)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    ‖((↑(1 / (W : ℝ)) : ℂ) *
        (∑ j ∈ Finset.range W,
          (((Real.sqrt u * semicircleQuadratureLambda W hW j : ℝ) : ℂ) -
            Complex.I * ((1-u : ℝ) : ℂ))⁻¹)) - Complex.I‖ ≤
      8 * Real.sqrt 2 / (W : ℝ) := by
  simpa only [qkern, Complex.real_smul] using
    semicircleQuadrature_closed_flow W hW u hu0 hu1

private theorem qkern_zero (x : ℝ) : qkern 0 x = Complex.I := by
  norm_num [qkern]

/-- The quadrature is exactly `i` at the closed-flow endpoint `u=0`. -/
theorem semicircleQuadrature_zero (W : ℕ) (hW : 1 ≤ W) :
    (1 / (W : ℝ)) •
      (∑ j ∈ Finset.range W,
        qkern 0 (semicircleQuadratureLambda W hW j)) = Complex.I := by
  have hWne : (W : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hW))
  simp [qkern_zero, Finset.sum_const]
  have hWneC : (W : ℂ) ≠ 0 := by exact_mod_cast hWne
  field_simp [hWneC]

/-- At width one, the T883 representative is the center quantile. -/
theorem semicircleQuadratureLambda_one_zero :
    semicircleQuadratureLambda 1 (by norm_num) 0 = 0 := by
  have hmem : semicircleLambda 1 (by norm_num) 0 (by norm_num) ∈
      Icc (-2 : ℝ) 2 :=
    (semicircleMidpointQuantile 1 (by norm_num) 0 (by norm_num)).property
  have hcdf : ProbabilityTheory.cdf semicircleMeasure
      (semicircleLambda 1 (by norm_num) 0 (by norm_num)) = 1 / 2 := by
    simpa using semicircleLambda_cdf 1 (by norm_num) 0 (by norm_num)
  have huniq := (existsUnique_semicircleCDF_eq (1 / 2 : ℝ)
    (by norm_num) (by norm_num)).unique
    (show ProbabilityTheory.cdf semicircleMeasure
      (⟨semicircleLambda 1 (by norm_num) 0 (by norm_num), hmem⟩ :
        Icc (-2 : ℝ) 2) = 1 / 2 by exact hcdf)
    (show ProbabilityTheory.cdf semicircleMeasure
      (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2) = 1 / 2 by
        exact semicircleMeasure_cdf_zero)
  have hzero : semicircleLambda 1 (by norm_num) 0 (by norm_num) = 0 :=
    congrArg Subtype.val huniq
  simpa [semicircleQuadratureLambda_eq] using hzero

/-- The one-cell error at `u=1/2` is exactly one. -/
theorem semicircleQuadrature_one_half_error :
    ‖(1 / (1 : ℝ)) •
      (∑ j ∈ Finset.range 1,
        qkern (1 / 2) (semicircleQuadratureLambda 1 (by norm_num) j)) -
        Complex.I‖ = 1 := by
  simp only [Finset.sum_range_one, one_div]
  rw [semicircleQuadratureLambda_one_zero]
  norm_num [qkern]
  have h : (2 : ℂ) * Complex.I - Complex.I = Complex.I := by ring
  rw [h]
  simp

#print axioms semicircleQuadratureLambda
#print axioms semicircleQuadratureLambda_eq
#print axioms semicircleQuadrature_closed_flow
#print axioms semicircleQuadrature_closed_flow_explicit
#print axioms semicircleQuadrature_zero
#print axioms semicircleQuadratureLambda_one_zero
#print axioms semicircleQuadrature_one_half_error

end
end RBM
