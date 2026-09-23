/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingTraceModulus
import RBM1D.Gauss.APrimeTwoChargeOneLoop
import RBM1D.Gauss.APrimeGeneralMovingCarrierCore

/-!
# T501: two-charge centered block-trace modulus

Conjugation transfers T496's plus-charge pathwise modulus to the minus
charge on the identical norm event, without any scale loss.
-/

namespace RBM.APrimeGeneralMovingTwoChargeModulus

open Filter MeasureTheory Set Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d


/-- The plus-charge definition is exactly T496's centered trace. -/
theorem centeredTrace_true_eq (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω d)
    (b : ZMod (d.L N)) :
    centeredTrace E N u ω true b =
      APrimeGeneralMovingTraceModulus.centeredTrace E N u ω b := by
  rfl

/-- At every energy, time, block and sample, the minus centered trace is
the conjugate of the plus centered trace. -/
theorem centeredTrace_false_eq_conj_true (E : ℝ) (N : ℕ) (u : ℝ)
    (ω : Ω d) (b : ZMod (d.L N)) :
    centeredTrace E N u ω false b =
      (starRingEnd ℂ) (centeredTrace E N u ω true b) := by
  rw [centeredTrace, centeredTrace, mSigma_false, mSigma_true]
  exact APrimeTwoChargeOneLoop.centered_block_trace_false_eq_conj_true
    (d.L N) (d.W N) (Hflow d N u ω) (Hflow_isHermitian d N u ω)
      (zt E u) (mE E) b

/-- The two charge norms agree pointwise on the same sample. -/
theorem centeredTrace_false_norm_eq_true (E : ℝ) (N : ℕ) (u : ℝ)
    (ω : Ω d) (b : ZMod (d.L N)) :
    ‖centeredTrace E N u ω false b‖ =
      ‖centeredTrace E N u ω true b‖ := by
  rw [centeredTrace_false_eq_conj_true, Complex.norm_conj]

/-- T496's pathwise modulus holds for both charges on the identical fixed
norm event and the full moving window. -/
theorem eventually_centeredTrace_sub_le {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
      ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
        ∀ σ b, ‖centeredTrace E N u ω σ b -
          centeredTrace E N u' ω σ b‖ ≤
            2 * (N : ℝ) ^ 5 * Real.sqrt |u - u'| := by
  filter_upwards [
    APrimeGeneralMovingTraceModulus.eventually_centeredTrace_sub_le
      hE hs0 hst ht1 hc hreg] with N hN
  intro ω hω u hu u' hu' σ b
  have hplus := hN ω hω u hu u' hu' b
  cases σ with
  | false =>
      rw [centeredTrace_false_eq_conj_true,
        centeredTrace_false_eq_conj_true, ← map_sub, Complex.norm_conj]
      simpa only [centeredTrace_true_eq] using hplus
  | true =>
      simpa only [centeredTrace_true_eq] using hplus

/-- T496's positive-length witness carries the two-charge modulus together
with measurability, high probability and all-size nonemptiness of the same
fixed norm event. -/
theorem positive_length_same_good_twoCharge_modulus_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      (∀ N, MeasurableSet (APrimeGeneralMovingGoodMesh.good N)) ∧
      HighProb (P d) APrimeGeneralMovingGoodMesh.good ∧
      (∀ N, (APrimeGeneralMovingGoodMesh.good N).Nonempty) ∧
      (∀ᶠ N : ℕ in atTop, ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
        ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
          ∀ σ b, ‖centeredTrace 0 N u ω σ b -
            centeredTrace 0 N u' ω σ b‖ ≤
              2 * (N : ℝ) ^ 5 * Real.sqrt |u - u'|) := by
  obtain ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos,
      hmeas, hhigh, hnonempty, _hplus⟩ :=
    APrimeGeneralMovingTraceModulus.positive_length_same_good_trace_modulus_witness
  exact ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos,
    hmeas, hhigh, hnonempty,
    eventually_centeredTrace_sub_le (by norm_num) hs0 hst ht1 hc hreg⟩

#print axioms centeredTrace_true_eq
#print axioms centeredTrace_false_eq_conj_true
#print axioms centeredTrace_false_norm_eq_true
#print axioms eventually_centeredTrace_sub_le
#print axioms positive_length_same_good_twoCharge_modulus_witness

end
end RBM.APrimeGeneralMovingTwoChargeModulus
