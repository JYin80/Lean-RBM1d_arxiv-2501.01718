/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetPoly

/-!
# T1113: deterministic integral of the crude positive-time cross envelope

This file integrates only the deterministic `r ↦ C / √r` envelope from
T1107. It does not assert integrability of the actual cross budget or its
random joint-rate factor.
-/

namespace RBM.APrimeGeneralMovingCrossEnvelopeIntegral

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.APrimeGeneralMovingCrossHcrossPositive

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The polynomial prefactor in the crude T1107 cross envelope. -/
noncomputable def envelopeConstant (p N : ℕ) (D : ℝ) : ℝ :=
  crossMomentCoeff p / (4 * (p : ℝ)) * (N : ℝ) ^ (2 * D + 17)

/-- The deterministic inverse-square-root envelope used by T1107. -/
noncomputable def crossEnvelope (p N : ℕ) (D r : ℝ) : ℝ :=
  envelopeConstant p N D / √r

private theorem invSqrt_eq_rpow {C r : ℝ} (hr : 0 ≤ r) :
    C / √r = C * r ^ (-1 / 2 : ℝ) := by
  calc
    C / √r = C * (√r)⁻¹ := by rw [div_eq_mul_inv]
    _ = C * (r ^ (1 / 2 : ℝ))⁻¹ := by rw [Real.sqrt_eq_rpow]
    _ = C * r ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg hr (1 / 2 : ℝ)]
    _ = C * r ^ (-1 / 2 : ℝ) := by
      rw [show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring]

/-- The singularity at zero is formally assigned value zero, matching
`Real.rpow` at zero for exponent `-1/2`. The power `r^(-1/2)` is interval
integrable on every real interval by `intervalIntegrable_rpow'`. -/
theorem intervalIntegrable_invSqrtEnvelope (C s v : ℝ)
    (hs : 0 ≤ s) (hsv : s ≤ v) :
    IntervalIntegrable (fun r : ℝ => C / √r) volume s v := by
  have hpow : IntervalIntegrable (fun r : ℝ => r ^ (-1 / 2 : ℝ)) volume s v := by
    exact intervalIntegral.intervalIntegrable_rpow' (a := s) (b := v) (by norm_num)
  have hEq : EqOn (fun r : ℝ => C / √r)
      (fun r => C * r ^ (-1 / 2 : ℝ)) (uIoo s v) := by
    intro r hr
    have hrpos : 0 < r := by
      rw [uIoo_of_le hsv] at hr
      exact lt_of_le_of_lt hs hr.1
    exact invSqrt_eq_rpow hrpos.le
  have hscaled : IntervalIntegrable
      (fun r : ℝ => C * r ^ (-1 / 2 : ℝ)) volume s v := hpow.const_mul C
  exact hscaled.congr_uIoo hEq.symm

/-- Exact interval integral of the formal inverse-square-root envelope,
including the endpoint `s = 0`. -/
theorem integral_invSqrtEnvelope (C s v : ℝ)
    (hs : 0 ≤ s) (hsv : s ≤ v) :
    (∫ r in s..v, C / √r) = 2 * C * (√v - √s) := by
  have hEq : EqOn (fun r : ℝ => C / √r)
      (fun r => C * r ^ (-1 / 2 : ℝ)) (Ioo s v) := by
    intro r hr
    have hrpos : 0 < r := lt_of_le_of_lt hs hr.1
    exact invSqrt_eq_rpow hrpos.le
  rw [intervalIntegral.integral_congr_Ioo_of_le hsv hEq,
    intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num : -1 < (-1 / 2 : ℝ)))]
  have hpow : (-1 / 2 : ℝ) + 1 = (1 / 2 : ℝ) := by ring
  rw [hpow]
  rw [← Real.sqrt_eq_rpow v, ← Real.sqrt_eq_rpow s]
  ring

theorem invSqrtEnvelope_formal_value_zero (C : ℝ) :
    C / √(0 : ℝ) = C * (0 : ℝ) ^ (-1 / 2 : ℝ) := by
  exact invSqrt_eq_rpow le_rfl

theorem integral_invSqrtEnvelope_from_zero (C v : ℝ) (hv : 0 ≤ v) :
    (∫ r in (0 : ℝ)..v, C / √r) = 2 * C * √v := by
  simpa using integral_invSqrtEnvelope C 0 v (by norm_num) hv

theorem integral_invSqrtEnvelope_degenerate (C s : ℝ) :
    (∫ r in s..s, C / √r) = 0 := by
  simp

theorem intervalIntegrable_crossEnvelope
    (p N : ℕ) (D s v : ℝ) (_hp : 1 ≤ p) (_hN : 1 ≤ N) (_hD : 60 ≤ D)
    (hs : 0 ≤ s) (hsv : s ≤ v) :
    IntervalIntegrable (fun r => crossEnvelope p N D r) volume s v := by
  simpa [crossEnvelope] using
    intervalIntegrable_invSqrtEnvelope (envelopeConstant p N D) s v hs hsv

theorem integral_crossEnvelope
    (p N : ℕ) (D s v : ℝ) (_hp : 1 ≤ p) (_hN : 1 ≤ N) (_hD : 60 ≤ D)
    (hs : 0 ≤ s) (hsv : s ≤ v) :
    (∫ r in s..v, crossEnvelope p N D r) =
      2 * envelopeConstant p N D * (√v - √s) := by
  simpa [crossEnvelope] using
    integral_invSqrtEnvelope (envelopeConstant p N D) s v hs hsv

theorem envelopeConstant_one (N : ℕ) (D : ℝ) :
    envelopeConstant 1 N D = (15 / 8 : ℝ) * (N : ℝ) ^ (2 * D + 17) := by
  rw [envelopeConstant, crossMomentCoeff_one]
  norm_num

/-- T1107's pointwise positive-time bound, combined with exact integrability
and evaluation of its deterministic envelope up to each active moving target
endpoint. No integral of the actual positive-time budget is claimed. -/
theorem eventually_active_target_cross_envelope_integral
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N,
      ∀ a : LoopArg (d.L N) 2,
        IntervalIntegrable
          (fun r => crossEnvelope p N D r) volume (s N)
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ∧
        (∫ r in (s N)..
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
          crossEnvelope p N D r) =
            2 * envelopeConstant p N D *
              (√(cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) - √(s N)) ∧
        (∀ r ∈ Icc (s N)
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
          0 < r →
            positiveTimeCrossBudget E D deltaWeight s t N k p a r ≤
              crossEnvelope p N D r) := by
  have hbudget :=
    APrimeGeneralMovingCrossBudgetPoly.eventually_positive_time_cross_budget_le_polynomial
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hbudget, eventually_ge_atTop 1] with N hbudgetN hN
  have hN' : 1 ≤ N := hN
  intro k hk a
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) := by
    dsimp [v]
    exact APrimeGeneralMovingJointMeasurable.target_endpoint_mem_window hst hk
  have hInt : IntervalIntegrable (fun r => crossEnvelope p N D r)
      volume (s N) v :=
    intervalIntegrable_crossEnvelope p N D (s N) v hp hN' hD (hs0 N) hv.1
  have hIntegral : (∫ r in (s N)..v, crossEnvelope p N D r) =
      2 * envelopeConstant p N D * (√v - √(s N)) :=
    integral_crossEnvelope p N D (s N) v hp hN' hD (hs0 N) hv.1
  refine ⟨?_, ?_, ?_⟩
  · simpa [v] using hInt
  · simpa [v] using hIntegral
  · intro r hr hrpos
    have hsource := hbudgetN k hk a r hr hrpos
    have hroot : 0 < √r := Real.sqrt_pos.2 hrpos
    have hpR : 0 < (p : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hp)
    have hrewrite :
        crossMomentCoeff p / (4 * (p : ℝ) * √r) *
            (N : ℝ) ^ (2 * D + 17) = crossEnvelope p N D r := by
      unfold crossEnvelope envelopeConstant
      field_simp [hpR.ne', hroot.ne']
    exact hsource.2.trans_eq hrewrite

/-- T995's accepted E=0, D=60 witness supplies a genuine positive-length
active target cell, including p=1, for the surrounding moving-window setup. -/
noncomputable abbrev t995_positive_cell_witness :=
  APrimeGeneralMovingCrossBudgetPoly.t995_positive_cell_witness

#print axioms intervalIntegrable_invSqrtEnvelope
#print axioms integral_invSqrtEnvelope
#print axioms invSqrtEnvelope_formal_value_zero
#print axioms integral_invSqrtEnvelope_from_zero
#print axioms integral_invSqrtEnvelope_degenerate
#print axioms intervalIntegrable_crossEnvelope
#print axioms integral_crossEnvelope
#print axioms envelopeConstant_one
#print axioms eventually_active_target_cross_envelope_integral
#print axioms t995_positive_cell_witness

end RBM.APrimeGeneralMovingCrossEnvelopeIntegral
