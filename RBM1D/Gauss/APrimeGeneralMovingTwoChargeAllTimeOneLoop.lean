/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingAllTimeOneLoop
import RBM1D.Gauss.APrimeGeneralMovingChargeTransfer

/-!
# T523: actual two-charge all-time moving one-loop domination

T518 supplies the plus-charge all-time law.  T511 transfers it pointwise to
the minus charge with the identical control and time-index family.
-/

namespace RBM.APrimeGeneralMovingTwoChargeAllTimeOneLoop

open Filter MeasureTheory Set Gauss

noncomputable section

noncomputable abbrev d : Dims := Dims.exampleGrow
noncomputable abbrev B : Band (Ω d) := band d

/-- Both charges of the actual centered block trace obey the same all-time
moving-window domination with control `2 qExt`. -/
theorem centeredTrace_twoCharge_stochDom_timeIcc {E c : ℝ}
    {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    ∀ σ : Bool,
      StochDom (P d) (U := fun N => TimeIcc s t N × ZMod (d.L N))
        (fun N p ω =>
          ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
            E N (p.1 : ℝ) ω σ p.2‖)
        (fun N p _ω =>
          2 * APrimeGeneralMovingControlExtension.qExt
            E s t N (p.1 : ℝ)) := by
  have hplus :=
    APrimeGeneralMovingAllTimeOneLoop.centeredTrace_stochDom_timeIcc
      hE hs0 hst ht1 hc hreg hB hStep
  intro σ
  cases σ with
  | false =>
      have hplus' : StochDom (P d)
          (U := fun N => TimeIcc s t N × ZMod (d.L N))
          (fun N p ω =>
            APrimeGeneralMovingChargeTransfer.traceNorm
              E N (p.1 : ℝ) true p.2 ω)
          (fun N p _ω =>
            2 * APrimeGeneralMovingControlExtension.qExt
              E s t N (p.1 : ℝ)) := by
        simpa only [APrimeGeneralMovingChargeTransfer.traceNorm] using hplus
      have hminus :=
        APrimeGeneralMovingChargeTransfer.stochDom_timeIcc_false_of_true hplus'
      simpa only [APrimeGeneralMovingChargeTransfer.traceNorm] using hminus
  | true => exact hplus

/-- T518's one genuine positive tuple realizes both charge laws together
with the original current-window inputs. -/
theorem positive_length_same_parameter_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (sample d) 0 s ∧ Step1.Hyp (sample d) 0 s t ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      ∀ σ : Bool,
        StochDom (P d) (U := fun N => TimeIcc s t N × ZMod (d.L N))
          (fun N p ω =>
            ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
              0 N (p.1 : ℝ) ω σ p.2‖)
          (fun N p _ω =>
            2 * APrimeGeneralMovingControlExtension.qExt
              0 s t N (p.1 : ℝ)) := by
  obtain ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
      hStep, hpos, _hplus⟩ :=
    APrimeGeneralMovingAllTimeOneLoop.positive_length_same_parameter_witness
  have htwo := centeredTrace_twoCharge_stochDom_timeIcc
    (E := 0) (s := s) (t := t) (by norm_num)
      hs0 hst ht1 hc hreg hB hStep
  exact ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg,
    hB, hStep, hpos, htwo⟩

#print axioms centeredTrace_twoCharge_stochDom_timeIcc
#print axioms positive_length_same_parameter_witness

end
end RBM.APrimeGeneralMovingTwoChargeAllTimeOneLoop
