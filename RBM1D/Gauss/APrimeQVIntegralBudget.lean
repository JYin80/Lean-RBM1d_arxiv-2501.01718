/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeOneStep

/-!
# T344: deterministic integral of the full quadratic-variation profile

This is a numerical calculation for the conditional T334 profile.  Its use for
the actual `qvAt` still requires the common source event and a comparison with
the weighted rate supplied to `APrimeOneStep.qv_bound_of_envelope`.
-/

namespace RBM.APrimeQVIntegralBudget

open MeasureTheory Set

noncomputable def ratio (s u : ℝ) : ℝ := (1 - s) / (1 - u)

private theorem ratio_pos {s u : ℝ} (hs : s < 1) (hu : u < 1) :
    0 < ratio s u := div_pos (by linarith) (by linarith)

private theorem hasDerivAt_ratio {s u : ℝ} (hu : u < 1) :
    HasDerivAt (ratio s) ((1 - s) / (1 - u) ^ 2) u := by
  have h := ((hasDerivAt_const u (1 - s)).div
    ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)) (by linarith : 1 - u ≠ 0))
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, id_eq]
    ring

private theorem hasDerivAt_ratio_power {s u q m : ℝ}
    (hs : s < 1) (hu : u < 1) (hm : m ≠ 0) (hq : q ≠ 0) :
    HasDerivAt (fun y => ratio s y ^ q / (m * q))
      ((ratio s u ^ q) / (m * (1 - u))) u := by
  have hr := (hasDerivAt_ratio (s := s) hu).rpow_const (p := q)
    (Or.inl (ne_of_gt (ratio_pos hs hu)))
  have h := hr.div_const (m * q)
  have h1u : 1 - u ≠ 0 := by linarith
  have hfac : (1 - s) / (1 - u) ^ 2 = ratio s u / (1 - u) := by
    unfold ratio
    field_simp
  convert h using 1
  rw [Real.rpow_sub_one (ne_of_gt (ratio_pos hs hu))]
  rw [hfac]
  field_simp [hm, hq, ne_of_gt (ratio_pos hs hu), h1u]

/-- Exact change of variables `du/(m(1-u)) = dx/(mx)` at power `q`. -/
theorem integral_ratio_power {s v q m : ℝ} (hs : s < 1) (hsv : s ≤ v)
    (hv : v < 1) (hm : m ≠ 0) (hq : q ≠ 0) :
    (∫ u in s..v, ratio s u ^ q / (m * (1 - u))) =
      (ratio s v ^ q - 1) / (m * q) := by
  let F : ℝ → ℝ := fun u => ratio s u ^ q / (m * q)
  let g : ℝ → ℝ := fun u => ratio s u ^ q / (m * (1 - u))
  have hcontF : ContinuousOn F (Icc s v) := by
    intro u hu
    exact (hasDerivAt_ratio_power hs (hu.2.trans_lt hv) hm hq).continuousAt.continuousWithinAt
  have hcontg : ContinuousOn g (Icc s v) := by
    have hden : ContinuousOn (fun u : ℝ => 1 - u) (Icc s v) :=
      continuousOn_const.sub continuousOn_id
    have hden0 : ∀ u ∈ Icc s v, 1 - u ≠ 0 := by
      intro u hu
      linarith [hu.2]
    have hrat : ContinuousOn (ratio s) (Icc s v) :=
      continuousOn_const.div hden hden0
    have hp : ContinuousOn (fun u => ratio s u ^ q) (Icc s v) :=
      hrat.rpow_const (fun u hu => Or.inl (ne_of_gt (ratio_pos hs (hu.2.trans_lt hv))))
    exact hp.div (continuousOn_const.mul hden) (by
      intro u hu
      exact mul_ne_zero hm (hden0 u hu))
  have hint : IntervalIntegrable g volume s v := hcontg.intervalIntegrable_of_Icc hsv
  have hd : ∀ u ∈ Ioo s v, HasDerivAt F (g u) u := by
    intro u hu
    exact hasDerivAt_ratio_power hs (hu.2.trans_le hv.le) hm hq
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsv hcontF hd hint
  have hss : ratio s s = 1 := by
    unfold ratio
    exact div_self (by linarith : 1 - s ≠ 0)
  change (∫ u in s..v, ratio s u ^ q / (m * (1 - u))) =
    ratio s v ^ q / (m * q) - ratio s s ^ q / (m * q) at hFTC
  rw [hss, Real.one_rpow] at hFTC
  calc
    (∫ u in s..v, ratio s u ^ q / (m * (1 - u))) =
        ratio s v ^ q / (m * q) - 1 / (m * q) := hFTC
    _ = (ratio s v ^ q - 1) / (m * q) := by ring

noncomputable def powerRate (m s q u : ℝ) : ℝ :=
  ratio s u ^ q / (m * (1 - u))

theorem intervalIntegrable_powerRate {s v q m : ℝ} (hsv : s ≤ v)
    (hv : v < 1) (hm : m ≠ 0) :
    IntervalIntegrable (powerRate m s q) volume s v := by
  have hden : ContinuousOn (fun u : ℝ => 1 - u) (Icc s v) :=
    continuousOn_const.sub continuousOn_id
  have hden0 : ∀ u ∈ Icc s v, 1 - u ≠ 0 := by
    intro u hu
    linarith [hu.2]
  have hrat : ContinuousOn (ratio s) (Icc s v) :=
    continuousOn_const.div hden hden0
  have hp : ContinuousOn (fun u => ratio s u ^ q) (Icc s v) :=
    hrat.rpow_const (fun u hu => Or.inl (ne_of_gt (ratio_pos (hsv.trans_lt hv)
      (hu.2.trans_lt hv))))
  have hc : ContinuousOn (powerRate m s q) (Icc s v) :=
    hp.div (continuousOn_const.mul hden) (by
      intro u hu
      exact mul_ne_zero hm (hden0 u hu))
  exact hc.intervalIntegrable_of_Icc hsv

theorem integral_powerRate {s v q m : ℝ} (hs : s < 1) (hsv : s ≤ v)
    (hv : v < 1) (hm : m ≠ 0) (hq : q ≠ 0) :
    (∫ u in s..v, powerRate m s q u) =
      (ratio s v ^ q - 1) / (m * q) :=
  integral_ratio_power hs hsv hv hm hq

/-- The full three-term profile after the square-root QV reduction. -/
noncomputable def qvEnvelope (m s v N δ τ A u : ℝ) : ℝ :=
  ratio s v ^ (-(4 : ℝ)) *
    (powerRate m s (-(3 / 2 : ℝ)) u +
      N ^ (4 * δ + 2 * τ) * A ^ (-(1 / 2 : ℝ)) *
        powerRate m s (19 / 4) u +
      N ^ (6 * δ + 3 * τ) * A⁻¹ * powerRate m s 8 u)

theorem intervalIntegrable_qvEnvelope {s v m N δ τ A : ℝ}
    (hsv : s ≤ v) (hv : v < 1) (hm : m ≠ 0) :
    IntervalIntegrable (qvEnvelope m s v N δ τ A) volume s v := by
  unfold qvEnvelope
  apply IntervalIntegrable.const_mul
  apply IntervalIntegrable.add
  apply IntervalIntegrable.add
  · exact intervalIntegrable_powerRate hsv hv hm
  · exact (intervalIntegrable_powerRate (q := 19 / 4) hsv hv hm).const_mul _
  · exact (intervalIntegrable_powerRate (q := 8) hsv hv hm).const_mul _

/-- Exact integrated near, quadratic far, and cubic far terms. -/
theorem integral_qvEnvelope {s v m N δ τ A : ℝ}
    (hs : s < 1) (hsv : s ≤ v) (hv : v < 1) (hm : m ≠ 0) :
    (∫ u in s..v, qvEnvelope m s v N δ τ A u) =
      ratio s v ^ (-(4 : ℝ)) *
        ((ratio s v ^ (-(3 / 2 : ℝ)) - 1) / (m * (-(3 / 2 : ℝ))) +
         N ^ (4 * δ + 2 * τ) * A ^ (-(1 / 2 : ℝ)) *
           ((ratio s v ^ (19 / 4 : ℝ) - 1) / (m * (19 / 4)) ) +
         N ^ (6 * δ + 3 * τ) * A⁻¹ *
           ((ratio s v ^ (8 : ℝ) - 1) / (m * 8))) := by
  have h0 := intervalIntegrable_powerRate (q := -(3 / 2 : ℝ)) hsv hv hm
  have h1 := intervalIntegrable_powerRate (q := 19 / 4) hsv hv hm
  have h2 := intervalIntegrable_powerRate (q := 8) hsv hv hm
  unfold qvEnvelope
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add (h0.add (h1.const_mul _)) (h2.const_mul _)]
  rw [intervalIntegral.integral_add h0 (h1.const_mul _)]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_powerRate hs hsv hv hm (by norm_num : (-(3 / 2 : ℝ)) ≠ 0),
    integral_powerRate hs hsv hv hm (by norm_num : (19 / 4 : ℝ) ≠ 0),
    integral_powerRate hs hsv hv hm (by norm_num : (8 : ℝ) ≠ 0)]

/-- Explicit constants from integrating the near, `J²`, and `J³` powers. -/
theorem integral_qvEnvelope_le {s v m N δ τ A : ℝ}
    (hs : s < 1) (hsv : s ≤ v) (hv : v < 1)
    (hm : 0 < m) (hN : 0 < N) (hA : 0 < A) :
    (∫ u in s..v, qvEnvelope m s v N δ τ A u) ≤
      ratio s v ^ (-(4 : ℝ)) *
        (2 / (3 * m) +
         N ^ (4 * δ + 2 * τ) * A ^ (-(1 / 2 : ℝ)) *
           (4 * ratio s v ^ (19 / 4 : ℝ) / (19 * m)) +
         N ^ (6 * δ + 3 * τ) * A⁻¹ *
           (ratio s v ^ (8 : ℝ) / (8 * m))) := by
  rw [integral_qvEnvelope hs hsv hv hm.ne']
  have hR : 0 < ratio s v := ratio_pos hs hv
  have hR4 : 0 ≤ ratio s v ^ (-(4 : ℝ)) := Real.rpow_nonneg hR.le _
  have hRnear : 0 ≤ ratio s v ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hR.le _
  have hC2 : 0 ≤ N ^ (4 * δ + 2 * τ) * A ^ (-(1 / 2 : ℝ)) := by positivity
  have hC3 : 0 ≤ N ^ (6 * δ + 3 * τ) * A⁻¹ := by positivity
  apply mul_le_mul_of_nonneg_left _ hR4
  have hnear : (ratio s v ^ (-(3 / 2 : ℝ)) - 1) / (m * (-(3 / 2 : ℝ))) ≤
      2 / (3 * m) := by
    have hm' : 0 < 3 * m := by positivity
    apply (le_div_iff₀ hm').2
    have heq : (ratio s v ^ (-(3 / 2 : ℝ)) - 1) / (m * (-(3 / 2 : ℝ))) *
        (3 * m) = 2 * (1 - ratio s v ^ (-(3 / 2 : ℝ))) := by
      field_simp
      ring
    rw [heq]
    nlinarith
  have hfar2 : (ratio s v ^ (19 / 4 : ℝ) - 1) / (m * (19 / 4 : ℝ)) ≤
      4 * ratio s v ^ (19 / 4 : ℝ) / (19 * m) := by
    have hden : 0 < 19 * m := by positivity
    apply (le_div_iff₀ hden).2
    have heq : (ratio s v ^ (19 / 4 : ℝ) - 1) / (m * (19 / 4 : ℝ)) *
        (19 * m) = 4 * (ratio s v ^ (19 / 4 : ℝ) - 1) := by
      field_simp
    rw [heq]
    norm_num
  have hfar3 : (ratio s v ^ (8 : ℝ) - 1) / (m * 8) ≤
      ratio s v ^ (8 : ℝ) / (8 * m) := by
    have hden : 0 < 8 * m := by positivity
    apply (le_div_iff₀ hden).2
    have heq : (ratio s v ^ (8 : ℝ) - 1) / (m * 8) * (8 * m) =
        ratio s v ^ (8 : ℝ) - 1 := by
      field_simp
    rw [heq]
    norm_num
  exact add_le_add (add_le_add hnear (mul_le_mul_of_nonneg_left hfar2 hC2))
    (mul_le_mul_of_nonneg_left hfar3 hC3)

/-- The quadratic and cubic far rows have strict room for `N^ν` under the
separate `N^c ≤ A` and `R^30 ≤ A` constraints. -/
theorem far_exponent_margins {c δ τ ν : ℝ}
    (hc : 0 < c) (hδ : δ = c / 1000) (hτ : τ = δ / 16)
    (hν : 0 < ν) (hνsmall : ν ≤ δ / 100) :
    (4 * δ + 2 * τ + ν) / c + (19 / 4 : ℝ) / 30 < 1 / 2 ∧
    (6 * δ + 3 * τ + ν) / c + (8 : ℝ) / 30 < 1 := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  subst δ
  subst τ
  constructor
  · have hrewrite :
        (4 * (c / 1000) + 2 * (c / 1000 / 16) + ν) / c +
          (19 / 4 : ℝ) / 30 =
        (4 * (c / 1000) + 2 * (c / 1000 / 16) + ν + c * (19 / 120)) / c := by
        field_simp [hc0]
        ring
    rw [hrewrite]
    apply (div_lt_iff₀ hc).2
    nlinarith
  · have hrewrite :
        (6 * (c / 1000) + 3 * (c / 1000 / 16) + ν) / c +
          (8 : ℝ) / 30 =
        (6 * (c / 1000) + 3 * (c / 1000 / 16) + ν + c * (8 / 30)) / c := by
        field_simp [hc0]
    rw [hrewrite]
    apply (div_lt_iff₀ hc).2
    nlinarith

/-- Separate lower bounds on `A` interpolate one monomial; they are not
multiplied.  This is the scalar form of the `Cond272Reg.margin` calculation. -/
theorem monomial_le_of_separate_scales {N R A c e b a : ℝ}
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hc : 0 < c)
    (he : 0 ≤ e) (hb : 0 ≤ b)
    (hNc : N ^ c ≤ A) (hR30 : R ^ (30 : ℝ) ≤ A)
    (hbudget : e / c + b / 30 ≤ a) :
    N ^ e * R ^ b ≤ A ^ a := by
  have hN0 : 0 ≤ N := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hA1 : 1 ≤ A := (Real.one_le_rpow hN hc.le).trans hNc
  have hA0 : 0 ≤ A := by linarith
  have hec : 0 ≤ e / c := div_nonneg he hc.le
  have hb30 : 0 ≤ b / 30 := by positivity
  have hNe : N ^ e ≤ A ^ (e / c) := by
    have hrewrite : N ^ e = (N ^ c) ^ (e / c) := by
      rw [← Real.rpow_mul hN0]
      congr 1
      field_simp [ne_of_gt hc]
    rw [hrewrite]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hNc hec
  have hRb : R ^ b ≤ A ^ (b / 30) := by
    have hrewrite : R ^ b = (R ^ (30 : ℝ)) ^ (b / 30) := by
      rw [← Real.rpow_mul hR0]
      congr 1
      ring
    rw [hrewrite]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hR0 _) hR30 hb30
  calc
    N ^ e * R ^ b ≤ A ^ (e / c) * A ^ (b / 30) :=
      mul_le_mul hNe hRb (Real.rpow_nonneg hR0 _) (Real.rpow_nonneg hA0 _)
    _ = A ^ (e / c + b / 30) := (Real.rpow_add (by linarith : 0 < A) _ _).symm
    _ ≤ A ^ a := Real.rpow_le_rpow_of_exponent_le hA1 hbudget

/-- The two full-QV far monomials are paid by the same endpoint scale, with
an explicit additional `N^ν` margin. -/
theorem far_rows_of_separate_scales {N R A c δ τ ν : ℝ}
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hc : 0 < c)
    (hδ : δ = c / 1000) (hτ : τ = δ / 16)
    (hν : 0 < ν) (hνsmall : ν ≤ δ / 100)
    (hNc : N ^ c ≤ A) (hR30 : R ^ (30 : ℝ) ≤ A) :
    N ^ (4 * δ + 2 * τ + ν) * R ^ (19 / 4 : ℝ) ≤ A ^ (1 / 2 : ℝ) ∧
    N ^ (6 * δ + 3 * τ + ν) * R ^ (8 : ℝ) ≤ A := by
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hτpos : 0 < τ := by rw [hτ]; positivity
  obtain ⟨hquad, hcubic⟩ := far_exponent_margins hc hδ hτ hν hνsmall
  constructor
  · exact monomial_le_of_separate_scales hN hR hc (by positivity)
      (by norm_num) hNc hR30 hquad.le
  · simpa only [Real.rpow_one] using
      (monomial_le_of_separate_scales hN hR hc (by positivity)
        (by norm_num) hNc hR30 hcubic.le)

/-- A convenient closed expression for the integrated deterministic budget. -/
noncomputable def integratedBudget (m R N δ τ A : ℝ) : ℝ :=
  R ^ (-(4 : ℝ)) *
    (2 / (3 * m) +
      N ^ (4 * δ + 2 * τ) * A ^ (-(1 / 2 : ℝ)) *
        (4 * R ^ (19 / 4 : ℝ) / (19 * m)) +
      N ^ (6 * δ + 3 * τ) * A⁻¹ *
        (R ^ (8 : ℝ) / (8 * m)))

/-- The three integrated powers in the endpoint form of (5.42). -/
theorem integratedBudget_endpoint {m R N δ τ A : ℝ} (hR : 0 < R) :
    integratedBudget m R N δ τ A =
      2 / (3 * m) * R ^ (-(4 : ℝ)) +
      (4 / (19 * m)) * N ^ (4 * δ + 2 * τ) * A ^ (-(1 / 2 : ℝ)) *
        R ^ (3 / 4 : ℝ) +
      (1 / (8 * m)) * N ^ (6 * δ + 3 * τ) * A⁻¹ * R ^ (4 : ℝ) := by
  have h2 : R ^ (-(4 : ℝ)) * R ^ (19 / 4 : ℝ) = R ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hR]
    norm_num
  have h3 : R ^ (-(4 : ℝ)) * R ^ (8 : ℝ) = R ^ (4 : ℝ) := by
    rw [← Real.rpow_add hR]
    norm_num
  unfold integratedBudget
  calc
    R ^ (-(4 : ℝ)) *
        (2 / (3 * m) + N ^ (4 * δ + 2 * τ) * A ^ (-(1 / 2 : ℝ)) *
          (4 * R ^ (19 / 4 : ℝ) / (19 * m)) +
          N ^ (6 * δ + 3 * τ) * A⁻¹ * (R ^ (8 : ℝ) / (8 * m))) =
      2 / (3 * m) * R ^ (-(4 : ℝ)) +
        (4 / (19 * m)) * N ^ (4 * δ + 2 * τ) * A ^ (-(1 / 2 : ℝ)) *
          (R ^ (-(4 : ℝ)) * R ^ (19 / 4 : ℝ)) +
        (1 / (8 * m)) * N ^ (6 * δ + 3 * τ) * A⁻¹ *
          (R ^ (-(4 : ℝ)) * R ^ (8 : ℝ)) := by ring
    _ = _ := by rw [h2, h3]

theorem integral_qvEnvelope_endpoint_le {s v m N δ τ A : ℝ}
    (hs : s < 1) (hsv : s ≤ v) (hv : v < 1)
    (hm : 0 < m) (hN : 0 < N) (hA : 0 < A) :
    (∫ u in s..v, qvEnvelope m s v N δ τ A u) ≤
      2 / (3 * m) * ratio s v ^ (-(4 : ℝ)) +
      (4 / (19 * m)) * N ^ (4 * δ + 2 * τ) * A ^ (-(1 / 2 : ℝ)) *
        ratio s v ^ (3 / 4 : ℝ) +
      (1 / (8 * m)) * N ^ (6 * δ + 3 * τ) * A⁻¹ *
        ratio s v ^ (4 : ℝ) := by
  rw [← integratedBudget_endpoint (ratio_pos hs hv)]
  exact integral_qvEnvelope_le hs hsv hv hm hN hA

/-- The only needed deterministic time comparison: the integral is bounded
by the explicit number which is checked against the target squared level. -/
theorem qv_time_premise_of_budget {s v m N δ τ A : ℝ} {p : ℕ} {C : ℝ}
    (hs : s < 1) (hsv : s ≤ v) (hv : v < 1)
    (hm : 0 < m) (hN : 0 < N) (hA : 0 < A)
    (hp : 1 ≤ p)
    (hbudget : (2 * (p : ℝ) - 1) *
      integratedBudget m (ratio s v) N δ τ A ≤ C ^ 2) :
    (2 * (p : ℝ) - 1) *
      (∫ u in s..v, qvEnvelope m s v N δ τ A u) ≤ C ^ 2 := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : 0 ≤ 2 * (p : ℝ) - 1 := by linarith
  exact (mul_le_mul_of_nonneg_left
    (show (∫ u in s..v, qvEnvelope m s v N δ τ A u) ≤
      integratedBudget m (ratio s v) N δ τ A from
      integral_qvEnvelope_le hs hsv hv hm hN hA) hp0).trans hbudget

/-- Exact handoff to the one-step square-root QV theorem.  The premise
`hgbd` is the still separate weighted-rate comparison for the actual QV. -/
theorem qv_bound_of_integrated_budget {s v m N δ τ A : ℝ} {p : ℕ} {C : ℝ}
    {g : ℝ → ℝ} (hs : s < 1) (hsv : s ≤ v) (hv : v < 1)
    (hm : 0 < m) (hN : 0 < N) (hA : 0 < A)
    (hp : 1 ≤ p) (hC : 0 ≤ C)
    (hgint : IntervalIntegrable g volume s v)
    (hgbd : ∀ u ∈ Icc s v, g u ≤ qvEnvelope m s v N δ τ A u)
    (hbudget : (2 * (p : ℝ) - 1) *
      integratedBudget m (ratio s v) N δ τ A ≤ C ^ 2) :
    √((2 * (p : ℝ) - 1) * ∫ u in s..v, g u) ≤ C := by
  exact APrimeOneStep.qv_bound_of_envelope hsv hp hC hgint
    (intervalIntegrable_qvEnvelope hsv hv hm.ne') hgbd
    (qv_time_premise_of_budget hs hsv hv hm hN hA hp hbudget)

theorem qvEnvelope_pos {m s v N δ τ A u : ℝ}
    (hs : s < 1) (hu : u < 1) (hv : v < 1)
    (hm : 0 < m) (hN : 0 < N) (hA : 0 < A) :
    0 < qvEnvelope m s v N δ τ A u := by
  have hRu : 0 < ratio s u := ratio_pos hs hu
  have hRv : 0 < ratio s v := ratio_pos hs hv
  unfold qvEnvelope powerRate
  positivity

/-- A positive-length first cell with nonzero deterministic QV envelope,
and with both separate scale constraints satisfied. -/
theorem first_cell_nonvacuous :
    ∃ (m s v N δ τ A c ν : ℝ),
      0 < m ∧ 0 ≤ s ∧ s < v ∧ v < 1 ∧ 1 < N ∧
      1 ≤ A ∧ A ≤ N ∧ 0 < c ∧
      δ = c / 1000 ∧ τ = δ / 16 ∧ 0 < ν ∧ ν ≤ δ / 100 ∧
      N ^ c ≤ A ∧ ratio s v ^ (30 : ℝ) ≤ A ∧
      0 < qvEnvelope m s v N δ τ A s := by
  refine ⟨1, 0, 1 / 2, (2 : ℝ) ^ 40, 1 / 1000, 1 / 16000,
    (2 : ℝ) ^ 40, 1, 1 / 100000, ?_⟩
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor
  · norm_num [ratio]
  · exact qvEnvelope_pos (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

end RBM.APrimeQVIntegralBudget

#print axioms RBM.APrimeQVIntegralBudget.integral_qvEnvelope_endpoint_le
#print axioms RBM.APrimeQVIntegralBudget.far_exponent_margins
#print axioms RBM.APrimeQVIntegralBudget.far_rows_of_separate_scales
#print axioms RBM.APrimeQVIntegralBudget.qv_bound_of_integrated_budget
#print axioms RBM.APrimeQVIntegralBudget.first_cell_nonvacuous
