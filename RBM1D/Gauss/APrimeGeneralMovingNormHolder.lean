/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingTwoChargeModulus

/-!
# T508: real-norm Hölder leaf for the moving centered traces

The reverse triangle inequality transfers T501's complex two-charge
modulus to the real norm observable in the exact time-net shape
`K = 6`, `gamma = 1/2`.
-/

namespace RBM.APrimeGeneralMovingNormHolder

open Filter MeasureTheory Set Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The real-valued norm observable used by the time-net interface. -/
noncomputable def xi (E : ℝ) (N : ℕ) (u : ℝ) (σ : Bool)
    (b : ZMod (d.L N)) (ω : Ω d) : ℝ :=
  ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace E N u ω σ b‖

/-- Exact polynomial and Hölder exponents for the time-net slot. -/
theorem exact_parameters : (6 : ℝ) = 6 ∧ (1 / 2 : ℝ) = 1 / 2 :=
  ⟨rfl, rfl⟩

/-- On T501's identical norm event, the real norm observable has the
exact `hHol` bound with `K=6` and `gamma=1/2`. -/
theorem eventually_xi_holder {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
      ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
        ∀ σ b, |xi E N u σ b ω - xi E N u' σ b ω| ≤
          (N : ℝ) ^ (6 : ℝ) * |u - u'| ^ ((1 : ℝ) / 2) := by
  filter_upwards [
    APrimeGeneralMovingTwoChargeModulus.eventually_centeredTrace_sub_le
      hE hs0 hst ht1 hc hreg,
    eventually_ge_atTop 2] with N hmod hN
  intro ω hω u hu u' hu' σ b
  have hcomplex := hmod ω hω u hu u' hu' σ b
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hcoef : 2 * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 6 := by
    calc
      2 * (N : ℝ) ^ 5 ≤ (N : ℝ) * (N : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_right hNr (by positivity)
      _ = (N : ℝ) ^ 6 := by ring
  calc
    |xi E N u σ b ω - xi E N u' σ b ω| ≤
        ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace E N u ω σ b -
          APrimeGeneralMovingTwoChargeModulus.centeredTrace E N u' ω σ b‖ := by
      exact abs_norm_sub_norm_le _ _
    _ ≤ 2 * (N : ℝ) ^ 5 * Real.sqrt |u - u'| := hcomplex
    _ ≤ (N : ℝ) ^ 6 * Real.sqrt |u - u'| :=
      mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
    _ = (N : ℝ) ^ (6 : ℝ) * |u - u'| ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      exact (Real.rpow_natCast (N : ℝ) 6).symm

/-- T501's positive-length witness supplies this `hHol` leaf on the same
measurable, high-probability, all-size nonempty norm event. -/
theorem positive_length_same_good_xi_holder_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      (∀ N, MeasurableSet (APrimeGeneralMovingGoodMesh.good N)) ∧
      HighProb (P d) APrimeGeneralMovingGoodMesh.good ∧
      (∀ N, (APrimeGeneralMovingGoodMesh.good N).Nonempty) ∧
      (∀ᶠ N : ℕ in atTop, ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
        ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
          ∀ σ b, |xi 0 N u σ b ω - xi 0 N u' σ b ω| ≤
            (N : ℝ) ^ (6 : ℝ) * |u - u'| ^ ((1 : ℝ) / 2)) := by
  obtain ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos,
      hmeas, hhigh, hnonempty, _hmod⟩ :=
    APrimeGeneralMovingTwoChargeModulus.positive_length_same_good_twoCharge_modulus_witness
  exact ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos,
    hmeas, hhigh, hnonempty,
    eventually_xi_holder (by norm_num) hs0 hst ht1 hc hreg⟩

#print axioms exact_parameters
#print axioms eventually_xi_holder
#print axioms positive_length_same_good_xi_holder_witness

end
end RBM.APrimeGeneralMovingNormHolder
