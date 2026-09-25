/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Consequences
import RBM1D.Gauss.Model
import RBM1D.Gauss.DimsExample

/-!
# Conditional strict probability bridge

This changes only the tail exponent in the existing stochastic-domination consequence.
The spatial index type and the `W^ρ` scale are unchanged.  The complement statement
requires measurability of the actual bad event; it does not establish that property
for a Gaussian Green function.
-/

namespace RBM

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The bad event keeps the entire spatial-index union within one probability. -/
def Band.strictBadSet (B : Band Ω) {U : ℕ → Type*}
    (ξ ζ : ∀ N, U N → Ω → ℝ) (ρ : ℝ) (N : ℕ) : Set Ω :=
  {ω | ∃ u, (B.W N : ℝ) ^ ρ * ζ N u ω < ξ N u ω}

/-- Exponent `D+1` in the existing producer makes the `D` conclusion strict. -/
theorem Band.prob_lt_of_stochDom (B : Band Ω) {U : ℕ → Type*}
    {ξ ζ : ∀ N, U N → Ω → ℝ}
    (hζ : ∀ N u ω, 0 ≤ ζ N u ω) (h : StochDom B.P ξ ζ)
    {ρ D : ℝ} (hρ : 0 < ρ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      B.P (B.strictBadSet ξ ζ ρ N) < ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  filter_upwards [B.prob_le_of_stochDom hζ h hρ (by linarith : 0 < D + 1),
    eventually_ge_atTop 2] with N hP hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpow : (N : ℝ) ^ (-(D + 1)) < (N : ℝ) ^ (-D) :=
    Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith)
  exact lt_of_le_of_lt hP ((ENNReal.ofReal_lt_ofReal_iff
    (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _)).2 hpow)

/-- The complementary good event is strict only when the bad event is measurable. -/
theorem Band.prob_good_gt_of_stochDom (B : Band Ω) {U : ℕ → Type*}
    {ξ ζ : ∀ N, U N → Ω → ℝ}
    (hζ : ∀ N u ω, 0 ≤ ζ N u ω) (h : StochDom B.P ξ ζ)
    {ρ D : ℝ} (hρ : 0 < ρ) (hD : 0 < D)
    (hBadMeas : ∀ᶠ N : ℕ in atTop, MeasurableSet (B.strictBadSet ξ ζ ρ N)) :
    ∀ᶠ N : ℕ in atTop,
      ENNReal.ofReal (1 - (N : ℝ) ^ (-D)) <
        B.P {ω | ∀ u, ξ N u ω ≤ (B.W N : ℝ) ^ ρ * ζ N u ω} := by
  letI := B.isProbabilityMeasure
  filter_upwards [B.prob_lt_of_stochDom hζ h hρ hD, hBadMeas,
    eventually_ge_atTop 2] with N hP hMeas hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha0 : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hMeasure : B.P (B.strictBadSet ξ ζ ρ N) ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hP.le
  have hCompl :
      B.P {ω | ∀ u, ξ N u ω ≤ (B.W N : ℝ) ^ ρ * ζ N u ω} =
        1 - B.P (B.strictBadSet ξ ζ ρ N) := by
    have hSet : {ω | ∀ u, ξ N u ω ≤ (B.W N : ℝ) ^ ρ * ζ N u ω} =
        (B.strictBadSet ξ ζ ρ N)ᶜ := by
      ext ω
      simp [Band.strictBadSet, not_exists, not_lt]
    rw [hSet, measure_compl hMeas hMeasure]
    simp
  rw [hCompl]
  have ha1 : (N : ℝ) ^ (-D) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (show 1 < N by omega))
      (by linarith)
  have hbad1 : B.P (B.strictBadSet ξ ζ ρ N) ≤ 1 := by
    exact (measure_mono (Set.subset_univ _)).trans (by simp)
  have hgoodTop : (1 : ENNReal) - B.P (B.strictBadSet ξ ζ ρ N) ≠ ⊤ := by finiteness
  apply (ENNReal.ofReal_lt_iff_lt_toReal (by linarith : 0 ≤ 1 - (N : ℝ) ^ (-D))
    hgoodTop).2
  rw [ENNReal.toReal_sub_of_le hbad1 (by simp)]
  simp only [ENNReal.toReal_one]
  have hbadReal := ENNReal.toReal_lt_of_lt_ofReal hP
  linarith

end RBM

namespace RBM.StrictProbabilityBridge

open Filter MeasureTheory

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

/-- An admissible growing band and spectral sequence, with a nonzero control and a
probability-one good event, witness simultaneous satisfiability of the bridge inputs.
This is a generic logical witness, not a Gaussian Green-function estimate. -/
theorem exampleGrow_satisfies_bridge :
    SpecSeqN 1 (1 / 4) (fun N => lemE Complex.I) (fun _ : ℕ => Complex.I) ∧
    StochDom B.P (fun _ (_ : Unit) (_ : Gauss.Ω d) => (1 : ℝ))
      (fun _ (_ : Unit) (_ : Gauss.Ω d) => (1 : ℝ)) ∧
    (∀ N, MeasurableSet (B.strictBadSet
      (fun _ (_ : Unit) (_ : Gauss.Ω d) => (1 : ℝ))
      (fun _ (_ : Unit) (_ : Gauss.Ω d) => (1 : ℝ)) (1 / 4) N)) ∧
    (∀ N, B.P {ω : Gauss.Ω d | ∀ (_ : Unit),
      (1 : ℝ) ≤ (B.W N : ℝ) ^ (1 / 4) * 1} = 1) := by
  constructor
  · refine SpecSeqN.of_z (fun N => ?_) (fun N => ?_) (fun N => ?_) ?_
    · simp
    · simp
    · simp
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      simpa using Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num : (-1 + (1 / 4 : ℝ)) ≤ 0)
  constructor
  · exact StochDom.refl (P := B.P) (fun _ _ _ => by norm_num)
  constructor
  · intro N
    have hW : (1 : ℝ) ≤ (B.W N : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast B.W_pos N) (by norm_num)
    have hEmpty : B.strictBadSet
        (fun _ (_ : Unit) (_ : Gauss.Ω d) => (1 : ℝ))
        (fun _ (_ : Unit) (_ : Gauss.Ω d) => (1 : ℝ)) (1 / 4) N = ∅ := by
      ext ω
      simp only [Band.strictBadSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hbad⟩
      norm_num at hbad
      norm_num [div_eq_mul_inv] at hW ⊢
      linarith
    rw [hEmpty]
    exact MeasurableSet.empty
  · intro N
    letI := B.isProbabilityMeasure
    have hW : (1 : ℝ) ≤ (B.W N : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast B.W_pos N) (by norm_num)
    have hSet : {ω : Gauss.Ω d | ∀ (_ : Unit),
        (1 : ℝ) ≤ (B.W N : ℝ) ^ (1 / 4) * 1} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro _
      norm_num [div_eq_mul_inv] at hW ⊢
    rw [hSet]
    exact measure_univ

end RBM.StrictProbabilityBridge
