/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingFixedOneLoop
import RBM1D.Gauss.APrimeGeneralMovingSelectorControl
import RBM1D.Gauss.APrimeGeneralMovingTwoChargeModulus
import RBM1D.Gauss.Lemma514Moment

/-!
# T517: fixed-time-uniform centered one-loop domination

The fixed-selector bound of T507 is converted, without a time union, to the
public `UnifDomIcc` interface on the original moving window.
-/

namespace RBM.APrimeGeneralMovingUnifDom

open Filter MeasureTheory Set Gauss

noncomputable section

noncomputable abbrev d : Dims := Dims.exampleGrow
noncomputable abbrev B : Band (Ω d) := band d

/-- The actual plus-charge centered block trace obeys the fixed-time-uniform
bound `2 qExt` throughout the original moving window. -/
theorem centeredTrace_unifDomIcc {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    UnifDomIcc (P d) s t
      (fun N u (b : ZMod (d.L N)) ω =>
        ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
          E N u ω true b‖)
      (fun N u (_b : ZMod (d.L N)) (_ω : Ω d) =>
        2 * APrimeGeneralMovingControlExtension.qExt E s t N u) := by
  refine Gauss.unifDomIcc_of_forall_stochDom hst ?_
  intro u hu
  have hfixed :=
    APrimeGeneralMovingFixedOneLoop.centered_block_trace_stochDom
      hE hs0 hst ht1 hu hc hreg hB hStep
  have hcontrol : ∀ N,
      2 * APrimeGeneralMovingSingletonLocalLaw.selectorQ E s u N =
        2 * APrimeGeneralMovingControlExtension.qExt E s t N (u N) :=
    APrimeGeneralMovingSelectorControl.two_mul_selectorQ_eq_two_mul_qExt hu
  simpa only [APrimeGeneralMovingTwoChargeModulus.centeredTrace,
    Gsig_true, mSigma_true, hcontrol] using hfixed

/-- T507's genuine positive first cell carries the fixed-time-uniform
centered one-loop law with the same parameter tuple. -/
theorem positive_length_same_parameter_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (sample d) 0 s ∧ Step1.Hyp (sample d) 0 s t ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      UnifDomIcc (P d) s t
        (fun N u (b : ZMod (d.L N)) ω =>
          ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
            0 N u ω true b‖)
        (fun N u (_b : ZMod (d.L N)) (_ω : Ω d) =>
          2 * APrimeGeneralMovingControlExtension.qExt 0 s t N u) := by
  obtain ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
      hStep, hpos, _hfixed⟩ :=
    APrimeGeneralMovingFixedOneLoop.positive_length_same_parameter_witness
  have hunif := centeredTrace_unifDomIcc (E := 0) (s := s) (t := t)
    (by norm_num) hs0 hst ht1 hc hreg hB hStep
  exact ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg,
    hB, hStep, hpos, hunif⟩

#print axioms centeredTrace_unifDomIcc
#print axioms positive_length_same_parameter_witness

end
end RBM.APrimeGeneralMovingUnifDom
