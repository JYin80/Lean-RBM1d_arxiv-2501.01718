/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSingletonLocalLaw
import RBM1D.Gauss.GoodSetFlow

/-!
# T575: the actual general-moving `goodSetFlow` event

The simultaneous Step-1 weak-law event is strengthened to `Step1.goodEv` at
every running time and then embedded into the single terminal-threshold event
`goodSetFlow`.  The closed wrapper constructs `Step1.Hyp` from the same
current-window Gaussian inputs.
-/

namespace RBM.APrimeGeneralMovingGoodSetFlowActual

open Filter MeasureTheory Set Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The general-moving event is measurable for every fixed `N`. -/
theorem measurableSet_goodSetFlow {E : Real} (hE : |E| < 2)
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

/-- With `Step1.Hyp` exposed, the weak law produces one event simultaneously
controlling every `u : TimeIcc s t N`. -/
theorem highProb_goodSetFlow_of_step1 {E c : Real} {s t : Nat -> Real}
    (hE : |E| < 2)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
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
    filter_upwards [Step1.eventually_scale_facts (B := B)
      hE hst ht1 hreg.1 hreg.2, eventually_ge_atTop 1]
      with N hf hN ω hω u
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hA : 0 < B.scale E N (u : Real) :=
      B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
    have hN1 : (1 : Real) <= N := by
      exact_mod_cast hN
    have hA1 : 1 <= B.scale E N (u : Real) :=
      (Real.one_le_rpow hN1 hc.le).trans (hf u).1
    have hpow : (B.scale E N (u : Real))⁻¹ ^ ((1 : Real) / 4) <=
        (B.scale E N (u : Real))⁻¹ ^ ((1 : Real) / 6) :=
      Real.rpow_le_rpow_of_exponent_ge (inv_pos.mpr hA)
        (inv_le_one_of_one_le₀ hA1) (by norm_num)
    exact (hω u).le.trans hpow
  refine hgood.mono ?_
  filter_upwards with N ω hω
  intro u hu
  let uu : TimeIcc s t N := ⟨u, hu⟩
  exact goodEv_subset_goodSet_flow hE hs0 ht1 N uu (hω uu)

/-- Closed actual Gaussian wrapper: `Step1.Hyp` is obtained from the same
`BoundsCore` and `Cond272Reg` tuple, without a Step-2 input. -/
theorem highProb_goodSetFlow {E c : Real} {s t : Nat -> Real}
    (hE : |E| < 2)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
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
  exact highProb_goodSetFlow_of_step1 hE hs0 hst ht1 hc hreg hB hStep

/-- High probability itself supplies eventual nonemptiness of the exact
all-time event. -/
theorem eventually_goodSetFlow_nonempty {E c : Real} {s t : Nat -> Real}
    (hE : |E| < 2)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ᶠ N : Nat in atTop,
      (goodSetFlow d E s t (flowDelta d E t) N).Nonempty := by
  exact (highProb_goodSetFlow hE hs0 hst ht1 hc hreg hB).nonempty (by simp)

/-- One positive first-cell tuple simultaneously satisfies the window,
regularity, current-window bounds, Step-1, measurability, high probability,
and eventual nonemptiness requirements. -/
theorem positive_length_same_parameter_witness :
    ∃ τ' : Real, 0 < τ' ∧ ∃ c : Real, 0 < c ∧
      ∃ s t : Nat -> Real,
        (forall N, s N = 0) ∧
        (forall N, 0 <= s N) ∧
        (forall N, s N <= t N) ∧
        (forall N, t N < 1) ∧
        Cond272Reg B 0 s t c ∧
        BoundsCore (sample d) 0 s ∧
        Step1.Hyp (sample d) 0 s t ∧
        (forall N, MeasurableSet
          (goodSetFlow d 0 s t (flowDelta d 0 t) N)) ∧
        HighProb (P d) (goodSetFlow d 0 s t (flowDelta d 0 t)) ∧
        ∀ᶠ N : Nat in atTop,
          s N < t N ∧
            (goodSetFlow d 0 s t (flowDelta d 0 t) N).Nonempty := by
  obtain ⟨tauPrime, htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
      hStep, hpos, _⟩ :=
    APrimeGeneralMovingSingletonLocalLaw.positive_length_same_parameter_witness
  have hHP : HighProb (P d) (goodSetFlow d 0 s t (flowDelta d 0 t)) :=
    highProb_goodSetFlow_of_step1 (by norm_num) hs0 hst ht1 hc hreg hB hStep
  have hnonempty : ∀ᶠ N : Nat in atTop,
      (goodSetFlow d 0 s t (flowDelta d 0 t) N).Nonempty :=
    hHP.nonempty (by simp)
  refine ⟨tauPrime, htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1, hreg,
    hB, hStep, ?_, hHP, ?_⟩
  · intro N
    exact measurableSet_goodSetFlow (by norm_num) ht1 N
  · filter_upwards [hpos, hnonempty] with N hposN hnonemptyN
    exact ⟨hposN, hnonemptyN⟩

#print axioms measurableSet_goodSetFlow
#print axioms highProb_goodSetFlow_of_step1
#print axioms highProb_goodSetFlow
#print axioms eventually_goodSetFlow_nonempty
#print axioms positive_length_same_parameter_witness

end
end RBM.APrimeGeneralMovingGoodSetFlowActual
