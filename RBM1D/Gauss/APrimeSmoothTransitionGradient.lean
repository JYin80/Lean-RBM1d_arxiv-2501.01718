/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # An actual nonzero derivative in the smooth-weight transition -/
namespace RBM.APrimeSmoothTransitionGradient
open Gauss Step2Bootstrap CutHypTheta Cutoff Filter
open APrimeSmoothTransition
open scoped Matrix.Norms.L2Operator

noncomputable def rayWeight (d : Gauss.Dims) (D δ : ℝ) (t mesh : ℕ → ℝ)
    (N0 p N m : ℕ) (x : ℝ) : ℝ :=
  APrimeSmoothWeightActual.weight d 0 D δ (fun _ => 0) t mesh N0 p N 2 m
    (scalarSample d x)

theorem contDiff_rayWeight (d : Gauss.Dims) {D δ : ℝ} {t mesh : ℕ → ℝ}
    {N0 p N m : ℕ} (hN : 0 < N) (hm : 1 ≤ m)
    (hh : (mesh N)⁻¹ < 1) :
    ContDiff ℝ 1 (rayWeight d D δ t mesh N0 p N m) := by
  have hc := APrimeSmoothWeightActual.contDiff_weightMatrix d
    (E := 0) (D := D) (δ := δ) (s := fun _ => 0) (t := t) (mesh := mesh)
    (N₀ := N0) (p := p) (N := N) (k := 2) (m := m)
    (by norm_num) (by norm_num) hN hm (by
      intro j hj
      interval_cases j
      · norm_num [cutNetPt]
      · simpa [cutNetPt] using hh)
  have hr : ContDiff ℝ 1 (fun x : ℝ =>
      (x : ℂ) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) :=
    Complex.ofRealCLM.contDiff.smul contDiff_const
  have heq : rayWeight d D δ t mesh N0 p N m = fun x : ℝ =>
      APrimeSmoothWeightActual.weightMatrix d 0 D δ (fun _ => 0) t mesh N0 p N 2 m
        ((x : ℂ) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) := by
    funext x
    rw [rayWeight, APrimeSmoothWeightActual.weight_eq_matrix, Xmat_scalarSample]
  rw [heq]
  exact hc.comp hr

private theorem exists_strict_transition {f : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hf : ContDiff ℝ 1 f) (h0 : f 0 = 1) (hb0 : f b = 0)
    (hr : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∃ x ∈ Set.Ioo 0 b, 0 < f x ∧ f x < 1 ∧ deriv f x = -1 / b := by
  obtain ⟨x, hx, hd⟩ := exists_deriv_eq_slope f hb hf.continuous.continuousOn
    (hf.differentiable (by norm_num)).differentiableOn
  rw [h0, hb0] at hd
  simp only [zero_sub, sub_zero] at hd
  have hn : deriv f x ≠ 0 := by rw [hd]; exact div_ne_zero (by norm_num) hb.ne'
  have hlo : 0 < f x := by
    apply lt_of_le_of_ne (hr x).1
    intro he
    have hm : IsLocalMin f x := Filter.Eventually.of_forall (fun y => by
      change f x ≤ f y
      rw [← he]
      exact (hr y).1)
    exact hn hm.deriv_eq_zero
  have hhi : f x < 1 := by
    apply lt_of_le_of_ne (hr x).2
    intro he
    have hm : IsLocalMax f x := Filter.Eventually.of_forall (fun y => by
      change f y ≤ f x
      rw [he]
      exact (hr y).2)
    exact hn hm.deriv_eq_zero
  exact ⟨x, hx, hlo, hhi, hd⟩

/-- Endpoint separation forces a genuine interior transition of the actual scalar ray. -/
theorem transition_of_endpoints (d : Gauss.Dims) {D δ : ℝ} {t mesh : ℕ → ℝ}
    {N0 p N m : ℕ} (hN : 0 < N) (hm : 1 ≤ m)
    (hmesh : 0 < mesh N) (hh : (mesh N)⁻¹ < 1)
    (hends : rayWeight d D δ t mesh N0 p N m 0 = 1 ∧
      rayWeight d D δ t mesh N0 p N m (2 / Real.sqrt ((mesh N)⁻¹)) = 0) :
    ∃ x ∈ Set.Ioo 0 (2 / Real.sqrt ((mesh N)⁻¹)),
      0 < rayWeight d D δ t mesh N0 p N m x ∧
      rayWeight d D δ t mesh N0 p N m x < 1 ∧
      deriv (rayWeight d D δ t mesh N0 p N m) x =
        -1 / (2 / Real.sqrt ((mesh N)⁻¹)) ∧
      deriv (rayWeight d D δ t mesh N0 p N m) x ≠ 0 := by
  have hb : 0 < 2 / Real.sqrt ((mesh N)⁻¹) := by
    exact div_pos (by norm_num) (Real.sqrt_pos.2 (inv_pos.2 hmesh))
  obtain ⟨x, hx, hlo, hhi, hd⟩ := exists_strict_transition hb
    (contDiff_rayWeight d hN hm hh) hends.1 hends.2 (fun x =>
      ⟨APrimeSmoothWeightActual.weight_nonneg d 0 D δ (fun _ => 0) t mesh N0 p N 2 m _,
       APrimeSmoothWeightActual.weight_le_one d 0 D δ (fun _ => 0) t mesh N0 p N 2 m _⟩)
  refine ⟨x, hx, hlo, hhi, hd, ?_⟩
  rw [hd]
  exact div_ne_zero (by norm_num) hb.ne'

/-- The complete finite numerical conditions of T356 yield a nonzero derivative,
without adding a regularity or event assumption. -/
theorem finite_transition_derivative (d : Gauss.Dims) {N N0 p m : ℕ}
    {D δ : ℝ} {t mesh : ℕ → ℝ} (hN : 2 ≤ N) (hN0 : N0 ≤ N) (hp : 1 ≤ p)
    (hm : 1 ≤ m) (hδ : 0 < δ) (hD : 2 ≤ D)
    (ht0 : 0 ≤ t N) (ht1 : t N < 1) (hmesh : 0 < mesh N)
    (hk : 2 ≤ cutNetTop (fun _ => 0) t mesh N)
    (hsmall : 10 * (mesh N)⁻¹ * (d.W N : ℝ)^(D-1) ≤ 1)
    (hcard : (((2 * Fintype.card (LoopArg (d.L N) 2) : ℕ) : ℝ) ^
      ((1 : ℝ) / (2 * (m : ℝ)))) ≤ Real.exp 1)
    (hlarge : 1024 * (Real.exp 1)^2 * (N : ℝ)^(2*δ) < (d.W N : ℝ)) :
    ∃ x ∈ Set.Ioo 0 (2 / Real.sqrt ((mesh N)⁻¹)),
      0 < rayWeight d D δ t mesh N0 p N m x ∧
      rayWeight d D δ t mesh N0 p N m x < 1 ∧
      deriv (rayWeight d D δ t mesh N0 p N m) x =
        -1 / (2 / Real.sqrt ((mesh N)⁻¹)) ∧
      deriv (rayWeight d D δ t mesh N0 p N m) x ≠ 0 := by
  have hW1 : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
  have hpow : 1 ≤ (d.W N : ℝ)^(D-1) := Real.one_le_rpow hW1 (by linarith)
  have hh : (mesh N)⁻¹ < 1 := by
    have hinv : 0 ≤ (mesh N)⁻¹ := (inv_pos.mpr hmesh).le
    nlinarith [mul_nonneg (by positivity : 0 ≤ 10 * (mesh N)⁻¹) (sub_nonneg.mpr hpow)]
  exact transition_of_endpoints d (by omega) hm hmesh hh
    (finite_transition d hN hN0 hp hm hδ hD ht0 ht1 hmesh hk hsmall hcard hlarge)

/-- One eventual size set works for every p; the transition point may depend on p. -/
theorem eventually_exampleGrow_transition_derivative {τ δ : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hδ4 : δ < 1/4) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, 1 ≤ p →
      ∃ x ∈ Set.Ioo 0 (2 / Real.sqrt ((transitionMesh N)⁻¹)),
        0 < rayWeight Gauss.Dims.exampleGrow 60 δ (Gauss.firstCellT τ)
          transitionMesh 2 p N (max 1 N) x ∧
        rayWeight Gauss.Dims.exampleGrow 60 δ (Gauss.firstCellT τ)
          transitionMesh 2 p N (max 1 N) x < 1 ∧
        deriv (rayWeight Gauss.Dims.exampleGrow 60 δ (Gauss.firstCellT τ)
          transitionMesh 2 p N (max 1 N)) x =
          -1 / (2 / Real.sqrt ((transitionMesh N)⁻¹)) ∧
        deriv (rayWeight Gauss.Dims.exampleGrow 60 δ (Gauss.firstCellT τ)
          transitionMesh 2 p N (max 1 N)) x ≠ 0 := by
  filter_upwards [eventually_exampleGrow_transition hτ hδ hδ4,
    eventually_ge_atTop 2] with N hends hN
  intro p hp
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hmesh : 1 < transitionMesh N := by
    unfold transitionMesh
    rw [max_eq_right (by linarith : (1 : ℝ) ≤ N)]
    have hn : (N : ℝ) ≤ (N : ℝ)^248 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ N)
        (by norm_num : 1 ≤ 248)
    linarith
  exact transition_of_endpoints Gauss.Dims.exampleGrow (by omega)
    (Nat.le_max_left _ _) (by linarith) (by
      apply (inv_lt_one₀ (by linarith : 0 < transitionMesh N)).2
      exact hmesh) (hends.2.2 p hp)

#print axioms contDiff_rayWeight
#print axioms transition_of_endpoints
#print axioms finite_transition_derivative
#print axioms eventually_exampleGrow_transition_derivative
end RBM.APrimeSmoothTransitionGradient
