/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingInitialHinit

/-!
# T496: centered block-trace modulus on a general moving window

On the fixed actual norm event, the resolvent Hölder modulus and the normalized
block trace cost no bandwidth factor.  This file proves only the deterministic
pathwise modulus.
-/

namespace RBM.APrimeGeneralMovingTraceModulus

open Filter MeasureTheory Set Gauss

open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The plus-charge centered block trace. -/
noncomputable def centeredTrace (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω d)
    (b : ZMod (d.L N)) : ℂ :=
  Matrix.trace ((green (Hflow d N u ω) (zt E u)
    - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
      Eblk (d.L N) (d.W N) b)

/-- On the actual norm event, every centered block trace is Hölder-`1/2)
with deterministic coefficient `2 N^5`, uniformly on the moving window. -/
theorem eventually_centeredTrace_sub_le {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
      ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
        ∀ b : ZMod (d.L N),
          ‖centeredTrace E N u ω b - centeredTrace E N u' ω b‖ ≤
            2 * (N : ℝ) ^ 5 * Real.sqrt |u - u'| := by
  filter_upwards [
    APrimeGeneralMovingInitialHinit.eventually_eta_window
      hE hs0 hst ht1 hc hreg,
    eventually_ge_atTop 1] with N hη hN
  intro ω hω u hu u' hu' b
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hηt0 : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
  have hηt := hη (t N) ⟨hst N, le_rfl⟩
  have hNneg : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hηinv : (etaT E (t N))⁻¹ ≤ (N : ℝ) ^ 2 := by
    have hi := inv_anti₀ (by positivity : 0 < (N : ℝ) ^ (-(2 : ℝ))) hηt
    have hrpow :
        (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hN0.le, Real.rpow_two]
    rw [hrpow, inv_inv] at hi
    exact hi
  have hX : ‖Xmat d N ω‖ ≤ (N : ℝ) := hω
  have htrace :
      ‖centeredTrace E N u ω b - centeredTrace E N u' ω b‖ ≤
        ‖green (Hflow d N u ω) (zt E u) -
          green (Hflow d N u' ω) (zt E u')‖ := by
    rw [centeredTrace, centeredTrace, ← Matrix.trace_sub]
    have heq :
        ((green (Hflow d N u ω) (zt E u)
            - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
              Eblk (d.L N) (d.W N) b -
          (green (Hflow d N u' ω) (zt E u')
            - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
              Eblk (d.L N) (d.W N) b) =
          (green (Hflow d N u ω) (zt E u) -
            green (Hflow d N u' ω) (zt E u')) *
              Eblk (d.L N) (d.W N) b := by
      noncomm_ring
    rw [heq]
    exact norm_trace_mul_Eblk_le _ b
  refine htrace.trans ((norm_green_flow_sub_le_sqrt d N hE
    (hs0 N) (ht1 N) ω hu hu').trans ?_)
  have hηsq :
      (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ ≤ (N : ℝ) ^ 4 := by
    have hs := mul_self_le_mul_self (inv_nonneg.mpr hηt0.le) hηinv
    calc
      _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
        simpa only [pow_two] using hs
      _ = (N : ℝ) ^ 4 := by ring
  have hX1 : ‖Xmat d N ω‖ + 1 ≤ 2 * (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hcoef :
      (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ *
          (‖Xmat d N ω‖ + 1) ≤ 2 * (N : ℝ) ^ 5 := by
    calc
      _ ≤ (N : ℝ) ^ 4 * (2 * (N : ℝ)) :=
        mul_le_mul hηsq hX1 (by positivity) (by positivity)
      _ = 2 * (N : ℝ) ^ 5 := by ring
  exact mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)

/-- T483's positive-length admissible window carries this modulus on the
same fixed norm event. -/
theorem positive_length_same_good_trace_modulus_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      (∀ N, MeasurableSet (APrimeGeneralMovingGoodMesh.good N)) ∧
      HighProb (P d) APrimeGeneralMovingGoodMesh.good ∧
      (∀ N, (APrimeGeneralMovingGoodMesh.good N).Nonempty) ∧
      (∀ᶠ N : ℕ in atTop, ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
        ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
          ∀ b : ZMod (d.L N),
            ‖centeredTrace 0 N u ω b - centeredTrace 0 N u' ω b‖ ≤
              2 * (N : ℝ) ^ 5 * Real.sqrt |u - u'|) := by
  obtain ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos, H⟩ :=
    APrimeGeneralMovingDetFields.positive_length_det_field_package_witness
  exact ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos,
    H.good_meas, H.good_highProb, H.good_nonempty,
    eventually_centeredTrace_sub_le (by norm_num) hs0 hst ht1 hc hreg⟩

#print axioms eventually_centeredTrace_sub_le
#print axioms positive_length_same_good_trace_modulus_witness

end
end RBM.APrimeGeneralMovingTraceModulus
