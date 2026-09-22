/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellHigherMomentCutoff
import RBM1D.Gauss.APrimeSmoothTransition

/-!
# An actual first-cell witness for the literal target cutoff

At the zero scalar Gaussian sample, the two entries in the first positive prefix satisfy
the literal target `prefNet` bound for all sufficiently large sizes.  Hence both old target
weights are one, and the same-sample bridge of T417 makes every canonical actual higher
moment weight one as well.
-/

namespace RBM.APrimeFirstCellTargetWeightWitness

open Real Filter Step2Bootstrap CutHypTheta Cutoff

/-- The normalized bootstrap quantity is nonnegative at every real time.  The fourth power
in its denominator makes this unconditional in the time parameter. -/
theorem jSnorm_nonneg_all_time (d : Gauss.Dims) (E D : ℝ) (s : ℕ → ℝ)
    (N : ℕ) (u : ℝ) (ω : Gauss.Ω d) :
    0 ≤ Step2Moment.jSnorm (Gauss.sample d) E D s N u ω := by
  unfold Step2Moment.jSnorm
  have hden : 0 ≤ Step2Moment.ratR E s N u ^ 4 := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul]
    exact sq_nonneg _
  exact div_nonneg
    ((show (0 : ℝ) ≤ 1 from by norm_num).trans
      (Step2Moment.one_le_jS (Gauss.sample d) N u ω))
    hden

/-- For `exampleGrow`, the literal target weights and every canonical actual higher-moment
weight simultaneously equal one at the same zero scalar sample and first positive prefix. -/
theorem eventually_exampleGrow_target_weights_one {τ δ : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hδ4 : δ < 1 / 4) :
    ∀ᶠ N : ℕ in atTop,
      APrimeWeight.piecewiseW
          (APrimeWeight.canonicalR (fun _ => 0) (Gauss.firstCellT τ)
            APrimeSmoothTransition.transitionMesh) 1
          (fun N u ω => Step2Moment.jSnorm (Gauss.sample Gauss.Dims.exampleGrow)
            0 60 (fun _ => 0) N u ω)
          (fun _ => 0) (Gauss.firstCellT τ) APrimeSmoothTransition.transitionMesh
          δ N 2 (APrimeSmoothTransition.scalarSample Gauss.Dims.exampleGrow 0) = 1 ∧
      (∀ p : ℕ, 1 ≤ p →
        APrimeWeight.widenedW
            (APrimeWeight.canonicalR (fun _ => 0) (Gauss.firstCellT τ)
              APrimeSmoothTransition.transitionMesh) 1
            (fun N u ω => Step2Moment.jSnorm (Gauss.sample Gauss.Dims.exampleGrow)
              0 60 (fun _ => 0) N u ω)
            (fun _ => 0) (Gauss.firstCellT τ) APrimeSmoothTransition.transitionMesh
            δ p N 2 (APrimeSmoothTransition.scalarSample Gauss.Dims.exampleGrow 0) = 1) ∧
      (∀ P : ℕ, 1 ≤ P →
        APrimeSmoothWeightActual.weight Gauss.Dims.exampleGrow 0 60 δ
          (fun _ => 0) (Gauss.firstCellT τ) APrimeSmoothTransition.transitionMesh
          2 P N 2
          (APrimeSmoothWeightActual.canonicalM Gauss.Dims.exampleGrow
            (fun _ => 0) (Gauss.firstCellT τ)
            APrimeSmoothTransition.transitionMesh N)
          (APrimeSmoothTransition.scalarSample Gauss.Dims.exampleGrow 0) = 1) := by
  have hpowEv : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ (2 * δ) :=
    eventually_le_rpow 2 (by positivity)
  filter_upwards [APrimeSmoothTransition.eventually_exampleGrow_transition hτ hδ hδ4,
    Gauss.Dims.dim_grow, eventually_ge_atTop 81, hpowEv] with N htransition hdim hN hpow
  let d := Gauss.Dims.exampleGrow
  let mesh := APrimeSmoothTransition.transitionMesh
  let t := Gauss.firstCellT τ
  let ω₀ := APrimeSmoothTransition.scalarSample d 0
  let J : ℕ → ℝ → Gauss.Ω d → ℝ := fun N u ω =>
    Step2Moment.jSnorm (Gauss.sample d) 0 60 (fun _ => 0) N u ω
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hmesh : mesh N = (N : ℝ) ^ (248 : ℕ) := by
    dsimp [mesh, APrimeSmoothTransition.transitionMesh]
    rw [max_eq_right hN1]
  have hmesh0 : 0 < mesh N := by rw [hmesh]; positivity
  have hu1nonneg : 0 ≤ (mesh N)⁻¹ := (inv_pos.mpr hmesh0).le
  have hu1half : (mesh N)⁻¹ ≤ 1 / 2 := by
    rw [hmesh]
    have hpow248 : (2 : ℝ) ≤ (N : ℝ) ^ (248 : ℕ) := by
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
      exact hN2.trans (by
        simpa only [pow_one] using
          (pow_le_pow_right₀ hN1 (by norm_num : 1 ≤ 248)))
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpow248)
  have hWn : Gauss.Dims.growW N ≤ N := by
    have hL1 : 1 ≤ Gauss.Dims.growL N :=
      le_trans (by norm_num) (Gauss.Dims.three_le_growL N)
    nlinarith [hdim.1]
  have hW : (d.W N : ℝ) ≤ N := by exact_mod_cast hWn
  have hWp : (d.W N : ℝ) ^ (59 : ℕ) ≤ (N : ℝ) ^ (59 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hW _
  have hN10 : (10 : ℝ) ≤ N := by exact_mod_cast (show 10 ≤ N by omega)
  have hnum : 10 * (d.W N : ℝ) ^ (59 : ℕ) ≤ (N : ℝ) ^ (248 : ℕ) := by
    calc
      _ ≤ 10 * (N : ℝ) ^ (59 : ℕ) :=
        mul_le_mul_of_nonneg_left hWp (by norm_num)
      _ ≤ (N : ℝ) * (N : ℝ) ^ (59 : ℕ) :=
        mul_le_mul_of_nonneg_right hN10 (by positivity)
      _ = (N : ℝ) ^ (60 : ℕ) := by ring
      _ ≤ (N : ℝ) ^ (248 : ℕ) := pow_le_pow_right₀ hN1 (by norm_num)
  have hsmall : 10 * (mesh N)⁻¹ * (d.W N : ℝ) ^ ((60 : ℝ) - 1) ≤ 1 := by
    rw [hmesh, show (60 : ℝ) - 1 = 59 by norm_num, Real.rpow_ofNat]
    calc
      _ = (10 * (d.W N : ℝ) ^ (59 : ℕ)) / (N : ℝ) ^ (248 : ℕ) := by ring
      _ ≤ 1 := (div_le_one (by positivity)).2 hnum
  have hpref : ω₀ ∈
      prefNet J (fun _ => 0) mesh (fun N _ => (N : ℝ) ^ (2 * δ) * 1) N 2 := by
    intro j hj
    interval_cases j
    · have hj0 := APrimeSmoothTransition.jSnorm_zero_le_two d N (D := 60)
        (u := 0) (by norm_num) (by norm_num) (by norm_num)
      simpa [J, cutNetPt] using hj0.trans hpow
    · have hj1 := APrimeSmoothTransition.jSnorm_zero_le_two d N (D := 60)
        (u := (mesh N)⁻¹) hu1nonneg hu1half hsmall
      simpa [J, cutNetPt] using hj1.trans hpow
  have hpieceLower : 1 ≤ APrimeWeight.piecewiseW
      (APrimeWeight.canonicalR (fun _ => 0) t mesh) 1 J
      (fun _ => 0) t mesh δ N 2 ω₀ :=
    APrimeWeight.piecewiseW_dom_canonical
      (fun N u ω => jSnorm_nonneg_all_time d 0 60 (fun _ => 0) N u ω)
      δ N 2 ω₀ hpref
  have hpieceUpper := APrimeWeight.piecewiseW_le_one
    (APrimeWeight.canonicalR (fun _ => 0) t mesh) 1 J
    (fun _ => 0) t mesh δ N 2 ω₀
  have hpiece : APrimeWeight.piecewiseW
      (APrimeWeight.canonicalR (fun _ => 0) t mesh) 1 J
      (fun _ => 0) t mesh δ N 2 ω₀ = 1 := le_antisymm hpieceUpper hpieceLower
  have ht0 : (fun _ : ℕ => (0 : ℝ)) N ≤ t N := by
    have hmono := gridT_mono
      (W := ((Gauss.band d).W N : ℝ))
      (by exact_mod_cast (Gauss.band d).one_le_W N)
      hτ.le (1 / 2 : ℝ) (Nat.zero_le 1)
    change (0 : ℝ) ≤ gridT ((Gauss.band d).W N : ℝ) τ (1 / 2 : ℝ) 1
    simpa only [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hmono
  have ht1 : t N < 1 := by
    exact (gridT_le (W := ((Gauss.band d).W N : ℝ))
      (τ' := τ) (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  refine ⟨hpiece, ?_, ?_⟩
  · intro p hp
    have hpw := APrimeWeight.piecewiseW_le_widenedW
      (r := APrimeWeight.canonicalR (fun _ => 0) t mesh) (N₀ := 1)
      (J := J) (s := fun _ => 0) (t := t) (mesh := mesh)
      (by norm_num) δ p N 2 ω₀
    have hwideUpper := APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR (fun _ => 0) t mesh) 1 J
      (fun _ => 0) t mesh δ p N 2 ω₀
    rw [hpiece] at hpw
    exact le_antisymm hwideUpper hpw
  · intro P _hP
    apply APrimeFirstCellHigherMomentCutoff.weight_eq_one_of_piecewiseW_pos
      d (by norm_num) hδ.le ω₀ ht0 ht1 hmesh0 (p := 1) (by norm_num) P
    rw [hpiece]
    norm_num

#print axioms jSnorm_nonneg_all_time
#print axioms eventually_exampleGrow_target_weights_one

end RBM.APrimeFirstCellTargetWeightWitness
