/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeOneStep
import RBM1D.Gauss.APrimeExponents
import RBM1D.Gauss.APrimeDriftTimeFamily
import RBM1D.Gauss.Eq45FlowGrid

/-!
# T340: deterministic integrated first-pass drift budget

This file integrates the deterministic four-term envelope from (5.40)–(5.50).
It does not establish a pointwise bound for the actual Gaussian drift or the
joint high-probability event needed to use that bound.
-/

namespace RBM.APrimeDriftIntegralBudget

open MeasureTheory Set Filter

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

/-- Exact substitution `du / (m(1-u)) = dx / (mx)` for any nonzero real power. -/
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

/-- One term in the deterministic drift envelope. -/
noncomputable def powerRate (m s q u : ℝ) : ℝ :=
  ratio s u ^ q / (m * (1 - u))

theorem powerRate_pos {m s q u : ℝ} (hm : 0 < m) (hs : s < 1)
    (hu : u < 1) : 0 < powerRate m s q u := by
  have hx := ratio_pos hs hu
  unfold powerRate
  positivity

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

noncomputable def driftEnvelope (m s v N δ τ A u : ℝ) : ℝ :=
  (ratio s v) ^ (-(2 : ℝ)) *
    (powerRate m s (-(1 / 2 : ℝ)) u +
      N ^ (4 * δ) * A⁻¹ * powerRate m s 6 u +
      N ^ (2 * δ + τ) * A ^ (-(1 / 2 : ℝ)) * powerRate m s (11 / 4) u +
      N ^ (3 * δ + 3 * τ / 2) * A⁻¹ * powerRate m s (9 / 2) u)

theorem driftEnvelope_pos {m s v N δ τ A u : ℝ}
    (hm : 0 < m) (hs : s < 1) (hv : v < 1) (hu : u < 1)
    (hN : 0 < N) (hA : 0 < A) :
    0 < driftEnvelope m s v N δ τ A u := by
  have hR := ratio_pos hs hv
  have hx := ratio_pos hs hu
  unfold driftEnvelope powerRate
  positivity

theorem intervalIntegrable_driftEnvelope {s v m N δ τ A : ℝ}
    (hsv : s ≤ v) (hv : v < 1) (hm : m ≠ 0) :
    IntervalIntegrable (driftEnvelope m s v N δ τ A) volume s v := by
  unfold driftEnvelope
  apply IntervalIntegrable.const_mul
  apply IntervalIntegrable.add
  apply IntervalIntegrable.add
  apply IntervalIntegrable.add
  · exact intervalIntegrable_powerRate hsv hv hm
  · exact (intervalIntegrable_powerRate (q := 6) hsv hv hm).const_mul _
  · exact (intervalIntegrable_powerRate (q := 11 / 4) hsv hv hm).const_mul _
  · exact (intervalIntegrable_powerRate (q := 9 / 2) hsv hv hm).const_mul _

/-- The four integrals before the separate-scale margin is applied. -/
theorem integral_driftEnvelope {s v m N δ τ A : ℝ}
    (hs : s < 1) (hsv : s ≤ v) (hv : v < 1) (hm : m ≠ 0) :
    (∫ u in s..v, driftEnvelope m s v N δ τ A u) =
      (ratio s v) ^ (-(2 : ℝ)) *
        ((ratio s v ^ (-(1 / 2 : ℝ)) - 1) / (m * (-(1 / 2 : ℝ))) +
         N ^ (4 * δ) * A⁻¹ * ((ratio s v ^ (6 : ℝ) - 1) / (m * 6)) +
         N ^ (2 * δ + τ) * A ^ (-(1 / 2 : ℝ)) *
           ((ratio s v ^ (11 / 4 : ℝ) - 1) / (m * (11 / 4))) +
         N ^ (3 * δ + 3 * τ / 2) * A⁻¹ *
           ((ratio s v ^ (9 / 2 : ℝ) - 1) / (m * (9 / 2)))) := by
  have h0 := intervalIntegrable_powerRate (q := -(1 / 2 : ℝ)) hsv hv hm
  have h1 := intervalIntegrable_powerRate (q := (6 : ℝ)) hsv hv hm
  have h2 := intervalIntegrable_powerRate (q := (11 / 4 : ℝ)) hsv hv hm
  have h3 := intervalIntegrable_powerRate (q := (9 / 2 : ℝ)) hsv hv hm
  unfold driftEnvelope
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add
    ((h0.add (h1.const_mul _)).add (h2.const_mul _)) (h3.const_mul _)]
  rw [intervalIntegral.integral_add (h0.add (h1.const_mul _)) (h2.const_mul _)]
  rw [intervalIntegral.integral_add h0 (h1.const_mul _)]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_powerRate hs hsv hv hm (by norm_num : (-(1 / 2 : ℝ)) ≠ 0),
    integral_powerRate hs hsv hv hm (by norm_num : (6 : ℝ) ≠ 0),
    integral_powerRate hs hsv hv hm (by norm_num : (11 / 4 : ℝ) ≠ 0),
    integral_powerRate hs hsv hv hm (by norm_num : (9 / 2 : ℝ) ≠ 0)]

/-- The direct integral is small under the three separate far-row inequalities.
These rows have no relation to the false bound on `QbActual`. -/
theorem integral_driftEnvelope_le_of_rows {s v m N δ τ A : ℝ}
    (hs : s < 1) (hsv : s ≤ v) (hv : v < 1) (hm : 0 < m)
    (hN : 0 < N) (hA : 0 < A)
    (h1 : N ^ (4 * δ) * A⁻¹ * ratio s v ^ (6 : ℝ) ≤ 1)
    (h2 : N ^ (2 * δ + τ) * A ^ (-(1 / 2 : ℝ)) *
      ratio s v ^ (11 / 4 : ℝ) ≤ 1)
    (h3 : N ^ (3 * δ + 3 * τ / 2) * A⁻¹ *
      ratio s v ^ (9 / 2 : ℝ) ≤ 1) :
    (∫ u in s..v, driftEnvelope m s v N δ τ A u) ≤
      3 / m * ratio s v ^ (-(2 : ℝ)) := by
  let R := ratio s v
  have hR : 0 < R := ratio_pos hs hv
  have hR2 : 0 ≤ R ^ (-(2 : ℝ)) := Real.rpow_nonneg hR.le _
  have hRn : 0 ≤ R ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hR.le _
  have hc1 : 0 ≤ N ^ (4 * δ) * A⁻¹ := by positivity
  have hc2 : 0 ≤ N ^ (2 * δ + τ) * A ^ (-(1 / 2 : ℝ)) := by positivity
  have hc3 : 0 ≤ N ^ (3 * δ + 3 * τ / 2) * A⁻¹ := by positivity
  have hn : (R ^ (-(1 / 2 : ℝ)) - 1) / (m * (-(1 / 2 : ℝ))) ≤ 2 / m := by
    have hiden : 0 < m⁻¹ := inv_pos.mpr hm
    have : (R ^ (-(1 / 2 : ℝ)) - 1) / (m * (-(1 / 2 : ℝ))) =
        2 / m - 2 * R ^ (-(1 / 2 : ℝ)) / m := by field_simp; ring
    rw [this]
    have : 0 ≤ 2 * R ^ (-(1 / 2 : ℝ)) / m := by positivity
    linarith
  have hf1 : N ^ (4 * δ) * A⁻¹ * ((R ^ (6 : ℝ) - 1) / (m * 6)) ≤
      1 / (6 * m) := by
    have h := mul_le_mul_of_nonneg_left (show R ^ (6 : ℝ) - 1 ≤ R ^ (6 : ℝ) by linarith) hc1
    have hm6 : 0 < 6 * m := by positivity
    rw [show m * (6 : ℝ) = 6 * m by ring, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (h.trans h1) hm6.le
  have hf2 : N ^ (2 * δ + τ) * A ^ (-(1 / 2 : ℝ)) *
      ((R ^ (11 / 4 : ℝ) - 1) / (m * (11 / 4))) ≤ 4 / (11 * m) := by
    have h := mul_le_mul_of_nonneg_left
      (show R ^ (11 / 4 : ℝ) - 1 ≤ R ^ (11 / 4 : ℝ) by linarith) hc2
    have hm11 : 0 < 11 * m := by positivity
    have heq : m * (11 / 4 : ℝ) = 11 * m / 4 := by ring
    have hright : 4 / (11 * m) = 1 / (m * (11 / 4 : ℝ)) := by
      rw [heq]
      field_simp
    rw [hright, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (h.trans h2) (by positivity)
  have hf3 : N ^ (3 * δ + 3 * τ / 2) * A⁻¹ *
      ((R ^ (9 / 2 : ℝ) - 1) / (m * (9 / 2))) ≤ 2 / (9 * m) := by
    have h := mul_le_mul_of_nonneg_left
      (show R ^ (9 / 2 : ℝ) - 1 ≤ R ^ (9 / 2 : ℝ) by linarith) hc3
    have hm9 : 0 < 9 * m := by positivity
    have heq : m * (9 / 2 : ℝ) = 9 * m / 2 := by ring
    have hright : 2 / (9 * m) = 1 / (m * (9 / 2 : ℝ)) := by
      rw [heq]
      field_simp
    rw [hright, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (h.trans h3) (by positivity)
  rw [integral_driftEnvelope hs hsv hv hm.ne']
  change R ^ (-(2 : ℝ)) *
      ((R ^ (-(1 / 2 : ℝ)) - 1) / (m * (-(1 / 2 : ℝ))) +
       N ^ (4 * δ) * A⁻¹ * ((R ^ (6 : ℝ) - 1) / (m * 6)) +
       N ^ (2 * δ + τ) * A ^ (-(1 / 2 : ℝ)) *
         ((R ^ (11 / 4 : ℝ) - 1) / (m * (11 / 4))) +
       N ^ (3 * δ + 3 * τ / 2) * A⁻¹ *
         ((R ^ (9 / 2 : ℝ) - 1) / (m * (9 / 2)))) ≤
      3 / m * R ^ (-(2 : ℝ))
  have hbound : 2 / m + 1 / (6 * m) + 4 / (11 * m) + 2 / (9 * m) ≤ 3 / m := by
    field_simp
    nlinarith [hm]
  have hinner : (R ^ (-(1 / 2 : ℝ)) - 1) / (m * (-(1 / 2 : ℝ))) +
       N ^ (4 * δ) * A⁻¹ * ((R ^ (6 : ℝ) - 1) / (m * 6)) +
       N ^ (2 * δ + τ) * A ^ (-(1 / 2 : ℝ)) *
         ((R ^ (11 / 4 : ℝ) - 1) / (m * (11 / 4))) +
       N ^ (3 * δ + 3 * τ / 2) * A⁻¹ *
         ((R ^ (9 / 2 : ℝ) - 1) / (m * (9 / 2))) ≤ 3 / m := by
    linarith
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hinner hR2

/-- The exact direct-integral connector consumed by the weighted one-step
inequality.  A pointwise `Adr` envelope is an explicit premise here; this
lemma does not construct it for the Gaussian model. -/
theorem direct_integral_drift_budget {s v m N δ τ A K : ℝ}
    {Adr Bcr Cbd : ℝ → ℝ}
    (hs : s < 1) (hsv : s ≤ v) (hv : v < 1) (hm : 0 < m)
    (hN : 0 < N) (hA : 0 < A)
    (h1 : N ^ (4 * δ) * A⁻¹ * ratio s v ^ (6 : ℝ) ≤ 1)
    (h2 : N ^ (2 * δ + τ) * A ^ (-(1 / 2 : ℝ)) *
      ratio s v ^ (11 / 4 : ℝ) ≤ 1)
    (h3 : N ^ (3 * δ + 3 * τ / 2) * A⁻¹ *
      ratio s v ^ (9 / 2 : ℝ) ≤ 1)
    (hABint : IntervalIntegrable (fun u => Adr u + Bcr u) volume s v)
    (hCint : IntervalIntegrable Cbd volume s v)
    (hAdr : ∀ u ∈ Icc s v, Adr u ≤ driftEnvelope m s v N δ τ A u)
    (hBcr : ∀ u ∈ Icc s v, Bcr u ≤ Cbd u)
    (hcross : 2 * (∫ u in s..v, Cbd u) ≤ K) :
    2 * (∫ u in s..v, Adr u + Bcr u) ≤
      6 / m * ratio s v ^ (-(2 : ℝ)) + K := by
  have hEnvInt := intervalIntegrable_driftEnvelope (N := N) (δ := δ)
    (τ := τ) (A := A) hsv hv hm.ne'
  have hEnvBd := integral_driftEnvelope_le_of_rows hs hsv hv hm hN hA h1 h2 h3
  have htime : 2 * (∫ u in s..v, driftEnvelope m s v N δ τ A u + Cbd u) ≤
      6 / m * ratio s v ^ (-(2 : ℝ)) + K := by
    rw [intervalIntegral.integral_add hEnvInt hCint]
    have heq : 2 * (3 / m * ratio s v ^ (-(2 : ℝ))) =
        6 / m * ratio s v ^ (-(2 : ℝ)) := by ring
    linarith
  exact APrimeOneStep.drift_bound_of_envelopes hsv hABint (hEnvInt.add hCint)
    hAdr hBcr htime

/-- Exact strict slack for the three drift rows.  The two regime conditions
`N^c ≤ A` and `R^30 ≤ A` are consumed by `Cond272Reg.margin` separately. -/
theorem drift_rows_strict {c δ τ ν : ℝ} (hc : 0 < c)
    (hδ : δ = c / 1000) (hτ : τ = δ / 16)
    (hν0 : 0 < ν) (hν : ν ≤ δ / 100) :
    (4 * δ + ν) / c + 6 / 30 < 1 ∧
    (2 * δ + τ + ν) / c + (11 / 4 : ℝ) / 30 < 1 / 2 ∧
    (3 * δ + 3 * τ / 2 + ν) / c + (9 / 2 : ℝ) / 30 < 1 := by
  constructor
  · have hnum : 4 * δ + ν < (4 / 5 : ℝ) * c := by
      rw [hδ] at hν ⊢
      linarith
    have hquot := (div_lt_iff₀ hc).2 hnum
    norm_num at hquot ⊢
    linarith
  constructor
  · have hnum : 2 * δ + τ + ν < (49 / 120 : ℝ) * c := by
      rw [hδ] at hν
      rw [hτ, hδ]
      linarith
    have hquot := (div_lt_iff₀ hc).2 hnum
    norm_num at hquot ⊢
    linarith
  · have hnum : 3 * δ + 3 * τ / 2 + ν < (17 / 20 : ℝ) * c := by
      rw [hδ] at hν
      rw [hτ, hδ]
      linarith
    have hquot := (div_lt_iff₀ hc).2 hnum
    norm_num at hquot ⊢
    linarith

private theorem row_le_one_of_margin {N R A e ν b a : ℝ}
    (hN : 1 ≤ N) (hR : 0 ≤ R) (hA : 0 < A) (hν : 0 ≤ ν)
    (hmargin : N ^ (e + ν) * R ^ b ≤ A ^ a) :
    N ^ e * A ^ (-a) * R ^ b ≤ 1 := by
  have hNpow : N ^ e ≤ N ^ (e + ν) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hRpow : 0 ≤ R ^ b := Real.rpow_nonneg hR _
  have hraw : N ^ e * R ^ b ≤ A ^ a :=
    (mul_le_mul_of_nonneg_right hNpow hRpow).trans hmargin
  have hApow : 0 < A ^ a := Real.rpow_pos_of_pos hA _
  rw [Real.rpow_neg hA.le]
  have hdiv : N ^ e * R ^ b / (A ^ a) ≤ 1 := by
    rw [div_le_iff₀ hApow]
    simpa using hraw
  convert hdiv using 1 <;> ring

/-- On every `Cond272Reg` window, the four-term deterministic envelope has an
integrated `R⁻²` bound.  The quantifier is eventual in `N`; no pointwise
Gaussian Good event is hidden in this statement. -/
theorem eventually_integral_driftEnvelope_le {Ω : Type*} [MeasurableSpace Ω]
    {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c δ τ ν : ℝ} (hc : 0 < c) (hδ : δ = c / 1000)
    (hτ : τ = δ / 16) (hν0 : 0 < ν) (hν : ν ≤ δ / 100)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop,
      (∫ u in s N..t N,
          driftEnvelope (mE E).im (s N) (t N) (N : ℝ) δ τ
            (B.scale E N (t N)) u) ≤
        3 / (mE E).im *
          (etaT E (s N) / etaT E (t N)) ^ (-(2 : ℝ)) := by
  have rows := drift_rows_strict hc hδ hτ hν0 hν
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hν : 0 ≤ ν := hν0.le
  have hrow1 := hreg.margin hE hst ht1 hc
    (e := 4 * δ + ν) (b := 6) (a := 1)
    (by positivity) (by norm_num) rows.1.le
  have hrow2 := hreg.margin hE hst ht1 hc
    (e := 2 * δ + τ + ν) (b := 11 / 4) (a := 1 / 2)
    (by positivity) (by norm_num) rows.2.1.le
  have hrow3 := hreg.margin hE hst ht1 hc
    (e := 3 * δ + 3 * τ / 2 + ν) (b := 9 / 2) (a := 1)
    (by positivity) (by norm_num) rows.2.2.le
  filter_upwards [hrow1, hrow2, hrow3, eventually_ge_atTop 1] with N h1 h2 h3 hN1
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hRpos : 0 < etaT E (s N) / etaT E (t N) :=
    div_pos (etaT_pos hE hs1) (etaT_pos hE (ht1 N))
  have hR : 0 < ratio (s N) (t N) := ratio_pos hs1 (ht1 N)
  have hReq : ratio (s N) (t N) = etaT E (s N) / etaT E (t N) := by
    rw [etaT_div_etaT hE]
    rfl
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  let A := B.scale E N (t N)
  have h1e := h1 ⟨t N, hst N, le_rfl⟩
  have h2e := h2 ⟨t N, hst N, le_rfl⟩
  have h3e := h3 ⟨t N, hst N, le_rfl⟩
  have hA : 0 < A := by
    have hp : 0 < (N : ℝ) ^ (4 * δ + ν) *
        (etaT E (s N) / etaT E (t N)) ^ (6 : ℝ) := by positivity
    have hpos := lt_of_lt_of_le hp h1e
    simpa [A] using hpos
  have hr1 : (N : ℝ) ^ (4 * δ) * A⁻¹ * ratio (s N) (t N) ^ (6 : ℝ) ≤ 1 := by
    have hr := row_le_one_of_margin hN hRpos.le hA hν h1e
    simpa [A, hReq, Real.rpow_one, Real.rpow_neg_one] using hr
  have hr2 : (N : ℝ) ^ (2 * δ + τ) * A ^ (-(1 / 2 : ℝ)) *
      ratio (s N) (t N) ^ (11 / 4 : ℝ) ≤ 1 := by
    have hr := row_le_one_of_margin hN hRpos.le hA hν h2e
    simpa [A, hReq] using hr
  have hr3 : (N : ℝ) ^ (3 * δ + 3 * τ / 2) * A⁻¹ *
      ratio (s N) (t N) ^ (9 / 2 : ℝ) ≤ 1 := by
    have hr := row_le_one_of_margin hN hRpos.le hA hν h3e
    simpa [A, hReq, Real.rpow_one, Real.rpow_neg_one] using hr
  have hm : 0 < (mE E).im := mE_im_pos hE
  have result := integral_driftEnvelope_le_of_rows hs1 (hst N) (ht1 N)
    hm hNp hA hr1 hr2 hr3
  simpa only [A, hReq] using result

/-- A growing Gaussian band's first grid cell has a strict time interval,
the genuine `Cond272Reg` scales, and a strictly positive deterministic drift
envelope.  This witnesses only deterministic assumptions, not a Good event. -/
theorem first_cell_deterministic_witness :
    ∃ τ' c : ℝ, 0 < τ' ∧ 0 < c ∧
      let B := Gauss.band Gauss.Dims.exampleGrow
      let s : ℕ → ℝ := fun N => gridT (B.W N) τ' (1 / 2 : ℝ) 0
      let t : ℕ → ℝ := fun N => gridT (B.W N) τ' (1 / 2 : ℝ) 1
      Cond272Reg B 0 s t c ∧
        ∀ᶠ N : ℕ in atTop, s N < t N ∧
          0 < driftEnvelope (mE 0).im (s N) (t N) (N : ℝ)
            (c / 1000) (c / 16000) (B.scale 0 N (t N)) (s N) := by
  let B := Gauss.band Gauss.Dims.exampleGrow
  have hcap : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-1 + (1 : ℝ) / 2) ≤ 1 - (1 / 2 : ℝ) := by
    filter_upwards [eventually_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_ge_atTop 1] with N hNpow hN
    have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hEq : (N : ℝ) ^ (-1 + (1 : ℝ) / 2) =
        ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [show -1 + (1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
        Real.rpow_neg hNr]
    rw [hEq]
    have hInv : ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ (2 : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hNpow)
    norm_num at hInv ⊢
    exact hInv
  obtain ⟨τ', hτ', c, hc, _n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain B (κ := 1) (τ := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)
  obtain ⟨_, hsteps⟩ := hgrid 0 (by norm_num) (fun _ => (1 / 2 : ℝ))
    (fun _ => by norm_num) hcap
  obtain ⟨hs0, hst, ht1, hreg⟩ := hsteps 0
  let s : ℕ → ℝ := fun N => gridT (B.W N) τ' (1 / 2 : ℝ) 0
  let t : ℕ → ℝ := fun N => gridT (B.W N) τ' (1 / 2 : ℝ) 1
  change Cond272Reg B 0 s t c at hreg
  change ∀ N, s N ≤ t N at hst
  change ∀ N, t N < 1 at ht1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hstrict, _⟩ :=
    Gauss.first_cell_joint_grid_scales hτ'
  have hpositive : ∀ᶠ N : ℕ in atTop, s N < t N ∧
      0 < driftEnvelope (mE 0).im (s N) (t N) (N : ℝ)
        (c / 1000) (c / 16000) (B.scale 0 N (t N)) (s N) := by
    filter_upwards [hstrict, eventually_ge_atTop 1] with N hstr hN1
    have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    have hA : 0 < B.scale 0 N (t N) := by
      rw [B.scale_eq_flowScale]
      exact flowScale_pos hW (B.one_le_L N) (by norm_num) (ht1 N)
    have hm : 0 < (mE 0).im := mE_im_pos (by norm_num)
    have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have hp := driftEnvelope_pos (δ := c / 1000) (τ := c / 16000)
      hm hs1 (ht1 N) hs1 hN hA
    exact ⟨by simpa only [B, s, t] using hstr, hp⟩
  exact ⟨τ', c, hτ', hc, by simpa only [B, s, t] using And.intro hreg hpositive⟩

#print axioms integral_ratio_power
#print axioms integral_driftEnvelope
#print axioms integral_driftEnvelope_le_of_rows
#print axioms direct_integral_drift_budget
#print axioms drift_rows_strict
#print axioms eventually_integral_driftEnvelope_le
#print axioms first_cell_deterministic_witness

end RBM.APrimeDriftIntegralBudget
