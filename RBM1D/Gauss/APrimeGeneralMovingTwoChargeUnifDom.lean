/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingUnifDom
import RBM1D.Gauss.APrimeGeneralMovingChargeTransfer

/-!
# T519: two-charge fixed-time-uniform centered one-loop domination

T517 supplies the actual plus-charge law.  T511's all-sample conjugation
identity transfers it to the minus charge with the identical control.
-/

namespace RBM.APrimeGeneralMovingTwoChargeUnifDom

open Filter MeasureTheory Set Gauss

noncomputable section

noncomputable abbrev d : Dims := Dims.exampleGrow
noncomputable abbrev B : Band (Ω d) := band d

/-- Both centered trace charges satisfy the same fixed-time-uniform moving
window law with control `2 qExt`. -/
theorem centeredTrace_twoCharge_unifDomIcc {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    ∀ σ : Bool,
      UnifDomIcc (P d) s t
        (fun N u (b : ZMod (d.L N)) ω =>
          ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
            E N u ω σ b‖)
        (fun N u (_b : ZMod (d.L N)) (_ω : Ω d) =>
          2 * APrimeGeneralMovingControlExtension.qExt E s t N u) := by
  have hplus := APrimeGeneralMovingUnifDom.centeredTrace_unifDomIcc
    hE hs0 hst ht1 hc hreg hB hStep
  intro σ
  cases σ with
  | false =>
      have hplus' : UnifDomIcc (P d) s t
          (fun N u (b : ZMod (d.L N)) ω =>
            APrimeGeneralMovingChargeTransfer.traceNorm E N u true b ω)
          (fun N u (_b : ZMod (d.L N)) (_ω : Ω d) =>
            2 * APrimeGeneralMovingControlExtension.qExt E s t N u) := by
        simpa only [APrimeGeneralMovingChargeTransfer.traceNorm] using hplus
      have hminus :=
        APrimeGeneralMovingChargeTransfer.unifDomIcc_false_of_true hplus'
      simpa only [APrimeGeneralMovingChargeTransfer.traceNorm] using hminus
  | true => exact hplus

/-- One genuine positive T517 tuple realizes the two-charge law together
with the original current-window assumptions. -/
theorem positive_length_same_parameter_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (sample d) 0 s ∧ Step1.Hyp (sample d) 0 s t ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      ∀ σ : Bool,
        UnifDomIcc (P d) s t
          (fun N u (b : ZMod (d.L N)) ω =>
            ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
              0 N u ω σ b‖)
          (fun N u (_b : ZMod (d.L N)) (_ω : Ω d) =>
            2 * APrimeGeneralMovingControlExtension.qExt 0 s t N u) := by
  obtain ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
      hStep, hpos, _hplus⟩ :=
    APrimeGeneralMovingUnifDom.positive_length_same_parameter_witness
  have htwo := centeredTrace_twoCharge_unifDomIcc
    (E := 0) (s := s) (t := t) (by norm_num)
      hs0 hst ht1 hc hreg hB hStep
  exact ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg,
    hB, hStep, hpos, htwo⟩

#print axioms centeredTrace_twoCharge_unifDomIcc
#print axioms positive_length_same_parameter_witness

end
end RBM.APrimeGeneralMovingTwoChargeUnifDom
