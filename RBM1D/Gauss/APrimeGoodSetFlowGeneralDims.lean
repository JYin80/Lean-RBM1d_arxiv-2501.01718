/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingGoodSetFlowActual

/-!
# T1369: the actual Gaussian all-time good event for arbitrary dimensions

This generalizes the accepted `exampleGrow` producer to every `Dims`, keeping the
same terminal threshold `flowDelta` and the same all-time event `goodSetFlow`.
-/

namespace RBM.APrimeGoodSetFlowGeneralDims

open Filter MeasureTheory Set Gauss

noncomputable section

/-- The actual Gaussian flow event is measurable for every fixed `N` and dimension. -/
theorem measurableSet_goodSetFlow (d : Dims) {E : Real} (hE : |E| < 2)
    {s t : Nat -> Real} (ht1 : forall N, t N < 1) (N : Nat) :
    MeasurableSet (goodSetFlow d E s t (flowDelta d E t) N) := by
  have heq : goodSetFlow d E s t (flowDelta d E t) N =
      ⋂ u : TimeIcc s t N, ⋂ x : d.Idx N, ⋂ y : d.Idx N,
        {ω : Ω d |
          ‖green (Hflow d N (u : Real) ω) (zt E (u : Real)) x y -
            (if x = y then mE E else 0)‖ ≤ flowDelta d E t N} := by
    ext ω
    simp [goodSetFlow, GoodEvent]
  rw [heq]
  apply IsClosed.measurableSet
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  have hu1 : (u : Real) < 1 := u.2.2.trans_lt (ht1 N)
  have hmat : Continuous (fun ω : Ω d =>
      green (Hflow d N (u : Real) ω) (zt E (u : Real))) :=
    continuous_green_comp (continuous_Hflow d N (u : Real))
      (Hflow_isHermitian d N (u : Real))
      (zt_im_ne_zero_of_lt_one hE hu1)
  exact isClosed_le ((Continuous.matrix_elem hmat x y).sub continuous_const).norm
    continuous_const

/-- With `Step1.Hyp` exposed, the weak law gives one event simultaneously
controlling every running time in the interval. -/
theorem highProb_goodSetFlow_of_step1 (d : Dims) {E c : Real} {s t : Nat -> Real}
    (hE : |E| < 2)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    HighProb (P d) (goodSetFlow d E s t (flowDelta d E t)) := by
  let kappa : Real := (2 - |E|) / 2
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    linarith
  have hEkappa : |E| <= 2 - kappa := by
    dsimp [kappa]
    linarith
  have h58 := Step1.eq58 (sample d) hkappa hEkappa hB hs0 hst ht1 hreg.1
    hStep.scaling (by norm_num) (hStep.lift 2 (by norm_num))
  have hweak := Step1.weakLaw_highProb (sample d) hE hB hs0 hst ht1
    hreg.1 hc hreg.2 h58 hStep.lemma41 hStep.cont
  have hgood : HighProb (P d) (fun N =>
      {ω | forall u : TimeIcc s t N,
        ω ∈ Step1.goodEv (sample d) E N (u : Real)}) := by
    refine hweak.mono ?_
    filter_upwards [Step1.eventually_scale_facts (B := band d)
      hE hst ht1 hreg.1 hreg.2, eventually_ge_atTop 1]
      with N hf hN ω hω u
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hA : 0 < (band d).scale E N (u : Real) :=
      (band d).scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
    have hN1 : (1 : Real) <= N := by
      exact_mod_cast hN
    have hA1 : 1 <= (band d).scale E N (u : Real) :=
      (Real.one_le_rpow hN1 hc.le).trans (hf u).1
    have hpow : ((band d).scale E N (u : Real))⁻¹ ^ ((1 : Real) / 4) <=
        ((band d).scale E N (u : Real))⁻¹ ^ ((1 : Real) / 6) :=
      Real.rpow_le_rpow_of_exponent_ge (inv_pos.mpr hA)
        (inv_le_one_of_one_le₀ hA1) (by norm_num)
    exact (hω u).le.trans hpow
  refine hgood.mono ?_
  filter_upwards with N ω hω
  intro u hu
  let uu : TimeIcc s t N := ⟨u, hu⟩
  exact goodEv_subset_goodSet_flow hE hs0 ht1 N uu (hω uu)

/-- Closed actual Gaussian wrapper: `Step1.Hyp` is built from the same
`BoundsCore` and `Cond272Reg` assumptions. -/
theorem highProb_goodSetFlow (d : Dims) {E c : Real} {s t : Nat -> Real}
    (hE : |E| < 2)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s) :
    HighProb (P d) (goodSetFlow d E s t (flowDelta d E t)) := by
  let kappa : Real := (2 - |E|) / 2
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    linarith
  have hEkappa : |E| <= 2 - kappa := by
    dsimp [kappa]
    linarith
  have hStep : Step1.Hyp (sample d) E s t :=
    step1Hyp_gauss_of_scale'' d hkappa hEkappa hB hs0 hst ht1
      hreg.1 hc hreg.2
  exact highProb_goodSetFlow_of_step1 d hE hs0 hst ht1 hc hreg hB hStep

/-- High probability supplies eventual nonemptiness of the exact all-time event. -/
theorem eventually_goodSetFlow_nonempty (d : Dims) {E c : Real} {s t : Nat -> Real}
    (hE : |E| < 2)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ᶠ N : Nat in atTop,
      (goodSetFlow d E s t (flowDelta d E t) N).Nonempty := by
  exact (highProb_goodSetFlow d hE hs0 hst ht1 hc hreg hB).nonempty (by simp)

/-- The arbitrary-dimension theorem specializes directly to the accepted
`exampleGrow` event and its exact terminal threshold. -/
theorem exampleGrow_highProb_goodSetFlow {E c : Real} {s t : Nat -> Real}
    (hE : |E| < 2)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg (band Dims.exampleGrow) E s t c)
    (hB : BoundsCore (sample Dims.exampleGrow) E s) :
    HighProb (P Dims.exampleGrow)
      (goodSetFlow Dims.exampleGrow E s t (flowDelta Dims.exampleGrow E t)) := by
  exact highProb_goodSetFlow Dims.exampleGrow hE hs0 hst ht1 hc hreg hB

#print axioms measurableSet_goodSetFlow
#print axioms highProb_goodSetFlow_of_step1
#print axioms highProb_goodSetFlow
#print axioms eventually_goodSetFlow_nonempty
#print axioms exampleGrow_highProb_goodSetFlow

end
end RBM.APrimeGoodSetFlowGeneralDims
