/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingAllOrdersMinkowskiActual
import RBM1D.Gauss.APrimeInit
import RBM1D.Gauss.APrimeOneStep

/-!
# T1317: conditional actual-QV fit into the free-loss small tail slot

For fixed `p` and target loss `lambda`, a uniform bound on the *literal actual*
QV norm integral with exponent `4h`, `h = lambda / 1000`, implies the precise
`APrimeInit.coordinate_integral_of_small_slots` QV input.  The time weight is
the same smooth actual weight at loss `lambda` as in
`APrimeGeneralMovingAllOrdersMinkowskiActual.actualClosedCellMinkowskiBoundAt`.

The integral estimate is an explicit conditional premise here.  This file does
not establish it; that remains the intended T1301 conclusion.
-/

namespace RBM.APrimeFreeLossQVSlotFit

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta Real
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The actual QV integrand used by the conditional input is nonnegative
and interval-integrable on every active closed cell, including the zero cell. -/
theorem actual_qv_integrand_well_formed
    {E D lambda : Real} {s t : Nat → Real} {p N k : Nat}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hp : 1 ≤ p) (hN : 0 < N)
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (a : LoopArg (d.L N) 2) :
    IntervalIntegrable
        (APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t lambda p N k a)
        volume (s N) (APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint s t D N k) ∧
      ∀ u, 0 ≤ APrimeGeneralMovingActualSmoothQVNormBudget.g
        E D s t lambda p N k a u := by
  let W := APrimeGeneralMovingActualSmoothQVNormBudget.weight E D s t lambda p N k
  have hWeight0 : ∀ ω, 0 ≤ W ω := by
    intro ω
    exact APrimeGeneralMovingActualSmoothQVNormBudget.weight_nonneg
      E D s t lambda p N k ω
  have hIntegrable := APrimeGeneralMovingActualSmoothQVNormBudget.intervalIntegrable_g
    (E := E) (D := D) (deltaWeight := lambda) (s := s) (t := t)
    hE hs0 hst ht1 hp hN hk a
  have hIntegrable' : IntervalIntegrable
      (APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t lambda p N k a)
        volume (s N) (APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint s t D N k) := by
    simpa [APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint,
      APrimeGeneralMovingActualSmoothQVNormBudget.endpoint,
      APrimeGeneralMovingQVNormBudget.endpoint] using hIntegrable
  refine ⟨hIntegrable', ?_⟩
  intro u
  change 0 ≤ APrimeModel.rateNormW (P d) W p
    (APrimeGeneralMovingActualSmoothQVNormBudget.qv E D s t N k a u)
  exact APrimeModel.rateNormW_nonneg hWeight0 p _

/-- Under the actual-smooth QV integral estimate at loss `lambda`, the literal
square-root term in the fixed-order actual closed-cell Minkowski inequality
fits the exact `tailTerm/R^4` input consumed by
`APrimeInit.coordinate_integral_of_small_slots`. The cutoff is chosen after
both `p` and `lambda`; all active cells, including `k = 0`, and all outputs
share it. -/
theorem eventually_actual_qv_integral_fits_small_slot
    {E D c lambda C : Real} {s t : Nat → Real} {p : Nat}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hlambda : 0 < lambda)
    (_hlambdaSmall : lambda ≤ min (1 / 10000) (c / 10000))
    (hp : 1 ≤ p) (_hC : 0 < C)
    (hQV : ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let v := APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint s t D N k
        let R := Step2Moment.ratR E s N v
        (∫ u in s N..v,
          APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t lambda p N k a u) ≤
          C * (N : Real) ^ (4 * (lambda / 1000)) * R ^ (-(4 : Real))) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let v := APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint s t D N k
        let R := Step2Moment.ratR E s N v
        let x := (N : Real) ^ (lambda / 8)
        Real.sqrt ((2 * (p : Real) - 1) *
          (∫ u in s N..v,
            APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t lambda p N k a u)) ≤
          APrimeOneStep.tailTerm x R (APrimeInit.slotKappa' x) / R ^ (4 : Nat) := by
  let h : Real := lambda / 1000
  let exponentGap : Real := 5 * lambda / 16 - 4 * h
  have hgap : 0 < exponentGap := by
    dsimp [exponentGap, h]
    nlinarith [hlambda]
  have hpReal : (1 : Real) ≤ p := by exact_mod_cast hp
  have hpFactor0 : 0 ≤ 2 * (p : Real) - 1 := by linarith
  have hfactor := eventually_le_rpow
    (2 * (2 * (p : Real) - 1) * C) hgap
  filter_upwards [hQV, hfactor, eventually_ge_atTop 1] with N hQVN hfactorN hN
  have hNpos : 0 < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hNge : (1 : Real) ≤ N := by exact_mod_cast hN
  have hx : 0 < (N : Real) ^ (lambda / 8) := by positivity
  intro k hk a
  let v := APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint s t D N k
  let R := Step2Moment.ratR E s N v
  let x := (N : Real) ^ (lambda / 8)
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hR : 0 < R := Step2Moment.ratR_pos hE
    (hv.1.trans_lt hv1) hv1
  have _hQVWellFormed := actual_qv_integrand_well_formed
    (lambda := lambda) hE hs0 hst ht1 hp (by omega) hk a
  have hQVN := hQVN k hk a
  change Real.sqrt ((2 * (p : Real) - 1) *
      (∫ u in s N..v,
        APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t lambda p N k a u)) ≤
    APrimeOneStep.tailTerm x R (APrimeInit.slotKappa' x) / R ^ (4 : Nat)
  have hbound :
      (2 * (p : Real) - 1) *
        (∫ u in s N..v,
          APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t lambda p N k a u) ≤
        (x ^ (5 / 4 : Real) * R ^ (-(2 : Real))) ^ 2 := by
    have hfactorN : 2 * (2 * (p : Real) - 1) * C ≤
        (N : Real) ^ exponentGap := hfactorN
    have hxpow : x ^ (5 / 4 : Real) = (N : Real) ^ (5 * lambda / 32) := by
      dsimp [x]
      rw [← Real.rpow_mul hNpos.le]
      congr 1
      ring
    have hpower :
        (x ^ (5 / 4 : Real) * R ^ (-(2 : Real))) ^ 2 =
          (N : Real) ^ (5 * lambda / 16) * R ^ (-(4 : Real)) := by
      rw [mul_pow, hxpow, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul hNpos.le, ← Real.rpow_mul hR.le]
      norm_num only [Nat.cast_ofNat]
      have he : (5 * lambda / 32) * (2 : Real) = 5 * lambda / 16 := by ring
      rw [he]
    rw [hpower]
    have hbase0 : 0 ≤ (N : Real) ^ (4 * h) * R ^ (-(4 : Real)) := by
      positivity
    have hmulQV := mul_le_mul_of_nonneg_left hQVN hpFactor0
    have hmulFactor := mul_le_mul_of_nonneg_right hfactorN hbase0
    have hsplit :
        (N : Real) ^ exponentGap *
            ((N : Real) ^ (4 * h) * R ^ (-(4 : Real))) =
          (N : Real) ^ (5 * lambda / 16) * R ^ (-(4 : Real)) := by
      calc
        _ = ((N : Real) ^ exponentGap * (N : Real) ^ (4 * h)) *
            R ^ (-(4 : Real)) := by ring
        _ = (N : Real) ^ (exponentGap + 4 * h) * R ^ (-(4 : Real)) := by
          rw [← Real.rpow_add hNpos]
        _ = _ := by
          congr 1
          dsimp [exponentGap, h]
          ring_nf
    rw [← hsplit]
    nlinarith [hmulQV, hmulFactor]
  have hsmall : 0 ≤ x ^ (5 / 4 : Real) * R ^ (-(2 : Real)) := by positivity
  have hslot :
      x ^ (5 / 4 : Real) * R ^ (-(2 : Real)) ≤
        APrimeOneStep.tailTerm x R (APrimeInit.slotKappa' x) / R ^ (4 : Nat) := by
    have hx0 : 0 < x := by positivity
    have hprod : x * APrimeInit.slotKappa' x = x ^ (5 / 4 : Real) := by
      unfold APrimeInit.slotKappa'
      calc
        x * x ^ (1 / 4 : Real) = x ^ (1 : Real) * x ^ (1 / 4 : Real) := by
          rw [Real.rpow_one]
        _ = x ^ ((1 : Real) + 1 / 4) :=
          (Real.rpow_add hx0 1 (1 / 4)).symm
        _ = x ^ (5 / 4 : Real) := by norm_num
    have htail := APrimeSlotArith.tailTerm_ge_kappa
      (x := x) (R := R) (κ := APrimeInit.slotKappa' x) hx0.le
    have hid : x ^ (5 / 4 : Real) * R ^ (-(2 : Real)) =
        (x * R ^ (2 : Nat) * APrimeInit.slotKappa' x) / R ^ (4 : Nat) := by
      rw [Real.rpow_neg hR.le, ← hprod]
      field_simp
      ring_nf
      norm_num [Real.rpow_natCast]
    rw [hid]
    exact div_le_div_of_nonneg_right htail (by positivity)
  calc
    Real.sqrt ((2 * (p : Real) - 1) *
        (∫ u in s N..v,
          APrimeGeneralMovingActualSmoothQVNormBudget.g E D s t lambda p N k a u))
      ≤ Real.sqrt ((x ^ (5 / 4 : Real) * R ^ (-(2 : Real))) ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = x ^ (5 / 4 : Real) * R ^ (-(2 : Real)) :=
      Real.sqrt_sq_eq_abs _ |>.trans (abs_of_nonneg hsmall)
    _ ≤ APrimeOneStep.tailTerm x R (APrimeInit.slotKappa' x) / R ^ (4 : Nat) := hslot

#print axioms actual_qv_integrand_well_formed
#print axioms eventually_actual_qv_integral_fits_small_slot

end
end RBM.APrimeFreeLossQVSlotFit
