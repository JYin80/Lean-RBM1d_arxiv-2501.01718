/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.SumZeroDyn
import RBM1D.Gauss.GridHierarchyN
import RBM1D.Gauss.LoopDecayFixed
import RBM1D.Gauss.DriftEnvelope
import Mathlib.Probability.Distributions.Geometric
import RBM1D.Hierarchy.ChargeReduce
import RBM1D.Flow.Initial
import Mathlib.Analysis.Calculus.Taylor

/-!
# The Q-algebra on the grid

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (5.88)-(5.101), at a fixed grid time / grid step, and Lemma 3.6 (3.12)-(3.13).
Paper loop length `n_p` corresponds to Lean tensors on `LoopArg L (n + 2)`, `n = n_p - 2`.

## Main results

* `Qstep_algebra`, `grid_step_Q`: the one-step identity
  `E[A_{k+1}|F_k] - U_{k,k+1} A_k = Δ (Q D + [Q, Θ](L-K) - ϑ̇ P(L-K)) + R^Q` with the explicit
  remainder `qStepErr`, from `discrete_hierarchy_step_n`.
* The input of (5.96): Ward's identity re-derived for a fixed Hermitian matrix (`psum_ward_of`,
  `wardMid_DlM`, `wardLast_DlM`), including the `(+,-)` pair, which Lemma 3.6 as stated does not
  cover: for `L` by `G(+)G(-) = G(-)G(+)` (`green_mul_green_comm`), for `K` by the conjugation
  symmetry `conj K_{t,σ,a} = K_{t,-σ,a}` of the tree representation (`conj_Kgen_flip`).
* `norm_comm_QTheta_le` ((5.99)), `max_varthetaDot_le`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open RBM Matrix Finset RBM.SumZeroDyn

section ContDiffTheta

open scoped Matrix.Norms.Operator

variable (L : ℕ) [NeZero L]

section ProdDiff

/-- A crude Lipschitz bound for finite products: if every factor of `f, g` is bounded by `M ≥ 1`
and every factor-difference by `D`, the product differs by at most `n M^n D`. -/
theorem norm_prod_sub_prod_le {n : ℕ} (f g : Fin n → ℂ) {M D : ℝ} (hM1 : 1 ≤ M) (hD0 : 0 ≤ D)
    (hf : ∀ i, ‖f i‖ ≤ M) (hg : ∀ i, ‖g i‖ ≤ M) (hfg : ∀ i, ‖f i - g i‖ ≤ D) :
    ‖(∏ i, f i) - ∏ i, g i‖ ≤ n * M ^ n * D := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    have key : f 0 * ∏ i : Fin k, f i.succ - g 0 * ∏ i : Fin k, g i.succ
        = f 0 * (∏ i : Fin k, f i.succ - ∏ i : Fin k, g i.succ)
          + (f 0 - g 0) * ∏ i : Fin k, g i.succ := by ring
    rw [key]
    have hgb : ‖∏ i : Fin k, g i.succ‖ ≤ M ^ k := by
      calc ‖∏ i : Fin k, g i.succ‖ ≤ ∏ i : Fin k, ‖g i.succ‖ := Finset.norm_prod_le _ _
        _ ≤ ∏ _i : Fin k, M :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hg i.succ)
        _ = M ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hind := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hf i.succ)
      (fun i => hg i.succ) (fun i => hfg i.succ)
    have hM0 : (0:ℝ) ≤ M := by linarith
    have step : ‖f 0 * (∏ i : Fin k, f i.succ - ∏ i : Fin k, g i.succ)
          + (f 0 - g 0) * ∏ i : Fin k, g i.succ‖
        ≤ M * ((k:ℝ) * M ^ k * D) + D * M ^ k := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      gcongr
      · exact hf 0
      · exact hfg 0
    refine step.trans ?_
    have : M * ((k:ℝ) * M ^ k * D) + D * M ^ k = ((k:ℝ) * M + 1) * (M ^ k * D) := by ring
    rw [this]
    have hfin : ((k:ℝ) * M + 1) ≤ ((k:ℕ) + 1 : ℝ) * M := by nlinarith
    push_cast
    calc ((k:ℝ) * M + 1) * (M ^ k * D)
        ≤ (((k:ℝ) + 1) * M) * (M ^ k * D) := by
          apply mul_le_mul_of_nonneg_right hfin
          positivity
      _ = ((k:ℝ) + 1) * M ^ (k + 1) * D := by rw [pow_succ]; ring

/-- The exact resolvent identity, real-parametrised, entrywise: `Θ_{u'} - Θ_u = (u'-u)(Θ_{u'} S
Θ_u)`, giving a crude but exact Lipschitz bound (no decay). -/
theorem norm_Theta_real_sub_le (hL : 3 ≤ L) {u u' : ℝ} (hu0 : 0 ≤ u) (huu' : u ≤ u')
    (hu'1 : u' < 1) (x y : ZMod L) :
    ‖Theta L (u' : ℂ) x y - Theta L (u : ℂ) x y‖ ≤ (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ := by
  have hu1 : u < 1 := lt_of_le_of_lt huu' hu'1
  have hξ : ‖(u : ℂ)‖ < 1 := norm_ofReal_lt_one hu0 hu1
  have hξ' : ‖(u' : ℂ)‖ < 1 := norm_ofReal_lt_one (hu0.trans huu') hu'1
  have hkey := congrFun (congrFun (Theta_sub_Theta L hL hξ hξ') x) y
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hkey
  have h1 : ‖((u' : ℂ) - (u : ℂ))‖ = u' - u := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hle : (0 : ℝ) ≤ u' - u := by linarith
  have hbound : ‖(Theta L (u' : ℂ) * SB L * Theta L (u : ℂ)) x y‖ ≤ (1 - u')⁻¹ * (1 - u)⁻¹ := by
    calc ‖(Theta L (u' : ℂ) * SB L * Theta L (u : ℂ)) x y‖
        ≤ ‖Theta L (u' : ℂ) * SB L * Theta L (u : ℂ)‖ := norm_entry_le_norm L _ x y
      _ ≤ ‖Theta L (u' : ℂ) * SB L‖ * ‖Theta L (u : ℂ)‖ := norm_mul_le _ _
      _ ≤ (‖Theta L (u' : ℂ)‖ * ‖SB L‖) * ‖Theta L (u : ℂ)‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (1 - u')⁻¹ * (1 - u)⁻¹ := by
          rw [norm_SB L hL, mul_one]
          have e1 : (1 - ‖(u' : ℂ)‖)⁻¹ = (1 - u')⁻¹ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hu0.trans huu')]
          have e2 : (1 - ‖(u : ℂ)‖)⁻¹ = (1 - u)⁻¹ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
          calc ‖Theta L (u' : ℂ)‖ * ‖Theta L (u : ℂ)‖
              ≤ (1 - ‖(u' : ℂ)‖)⁻¹ * (1 - ‖(u : ℂ)‖)⁻¹ :=
                mul_le_mul (norm_Theta_le L hL hξ') (norm_Theta_le L hL hξ) (norm_nonneg _)
                  (by positivity)
            _ = (1 - u')⁻¹ * (1 - u)⁻¹ := by rw [e1, e2]
  calc ‖Theta L (u' : ℂ) x y - Theta L (u : ℂ) x y‖
      = (u' - u) * ‖(Theta L (u' : ℂ) * SB L * Theta L (u : ℂ)) x y‖ := by
        rw [hkey, norm_mul, h1]
    _ ≤ (u' - u) * ((1 - u')⁻¹ * (1 - u)⁻¹) := mul_le_mul_of_nonneg_left hbound hle
    _ = (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ := by ring

/-- Operator-norm version of `norm_Theta_real_sub_le`, used to chain with `SB`/`Theta` in the
computation of `TST`'s Lipschitz bound. -/
theorem norm_Theta_real_sub_op_le (hL : 3 ≤ L) {u u' : ℝ} (hu0 : 0 ≤ u) (huu' : u ≤ u')
    (hu'1 : u' < 1) :
    ‖Theta L (u' : ℂ) - Theta L (u : ℂ)‖ ≤ (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ := by
  have hu1 : u < 1 := lt_of_le_of_lt huu' hu'1
  have hξ : ‖(u : ℂ)‖ < 1 := norm_ofReal_lt_one hu0 hu1
  have hξ' : ‖(u' : ℂ)‖ < 1 := norm_ofReal_lt_one (hu0.trans huu') hu'1
  rw [Theta_sub_Theta L hL hξ hξ', norm_smul]
  have h1 : ‖((u' : ℂ) - (u : ℂ))‖ = u' - u := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [h1]
  have hle : (0 : ℝ) ≤ u' - u := by linarith
  have hbound : ‖Theta L (u' : ℂ) * SB L * Theta L (u : ℂ)‖ ≤ (1 - u')⁻¹ * (1 - u)⁻¹ := by
    calc ‖Theta L (u' : ℂ) * SB L * Theta L (u : ℂ)‖
        ≤ ‖Theta L (u' : ℂ) * SB L‖ * ‖Theta L (u : ℂ)‖ := norm_mul_le _ _
      _ ≤ (‖Theta L (u' : ℂ)‖ * ‖SB L‖) * ‖Theta L (u : ℂ)‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (1 - u')⁻¹ * (1 - u)⁻¹ := by
          rw [norm_SB L hL, mul_one]
          have e1 : (1 - ‖(u' : ℂ)‖)⁻¹ = (1 - u')⁻¹ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hu0.trans huu')]
          have e2 : (1 - ‖(u : ℂ)‖)⁻¹ = (1 - u)⁻¹ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
          calc ‖Theta L (u' : ℂ)‖ * ‖Theta L (u : ℂ)‖
              ≤ (1 - ‖(u' : ℂ)‖)⁻¹ * (1 - ‖(u : ℂ)‖)⁻¹ :=
                mul_le_mul (norm_Theta_le L hL hξ') (norm_Theta_le L hL hξ) (norm_nonneg _)
                  (by positivity)
            _ = (1 - u')⁻¹ * (1 - u)⁻¹ := by rw [e1, e2]
  calc (u' - u) * ‖Theta L (u' : ℂ) * SB L * Theta L (u : ℂ)‖
      ≤ (u' - u) * ((1 - u')⁻¹ * (1 - u)⁻¹) := mul_le_mul_of_nonneg_left hbound hle
    _ = (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ := by ring

/-- `TST_u := Θ_u S^(B) Θ_u`'s crude Lipschitz bound, via one more exact resolvent split
`TST_{u'} - TST_u = (Θ_{u'}-Θ_u) S Θ_{u'} + Θ_u S (Θ_{u'}-Θ_u)`. -/
theorem norm_TST_real_sub_le (hL : 3 ≤ L) {u u' : ℝ} (hu0 : 0 ≤ u) (huu' : u ≤ u') (hu'1 : u' < 1)
    (x y : ZMod L) :
    ‖(Theta L (u' : ℂ) * SB L * Theta L (u' : ℂ)) x y
        - (Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y‖
      ≤ (u' - u) * (2 * ((1 - u')⁻¹ ^ 2 * (1 - u)⁻¹)) := by
  have hu1 : u < 1 := lt_of_le_of_lt huu' hu'1
  have hdiff : Theta L (u' : ℂ) * SB L * Theta L (u' : ℂ)
      - Theta L (u : ℂ) * SB L * Theta L (u : ℂ)
      = (Theta L (u' : ℂ) - Theta L (u : ℂ)) * SB L * Theta L (u' : ℂ)
        + Theta L (u : ℂ) * SB L * (Theta L (u' : ℂ) - Theta L (u : ℂ)) := by
    noncomm_ring
  have hkey := congrFun (congrFun hdiff x) y
  simp only [Matrix.sub_apply, Matrix.add_apply] at hkey
  rw [hkey]
  have hdop := norm_Theta_real_sub_op_le L hL hu0 huu' hu'1
  have huu0 : (0:ℝ) < 1 - u' := by linarith
  have huu1 : (0:ℝ) < 1 - u := by linarith
  have hΘ' : ‖Theta L (u' : ℂ)‖ ≤ (1 - u')⁻¹ := by
    have h := norm_Theta_le L hL (norm_ofReal_lt_one (hu0.trans huu') hu'1)
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hu0.trans huu')] at h
  have hΘ : ‖Theta L (u : ℂ)‖ ≤ (1 - u)⁻¹ := by
    have h := norm_Theta_le L hL (norm_ofReal_lt_one hu0 hu1)
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] at h
  have hP : (0:ℝ) ≤ (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ := by positivity
  have hmono : (1 - u)⁻¹ ≤ (1 - u')⁻¹ := by
    rw [inv_le_inv₀ huu1 huu0]; linarith
  have hb1 : ‖((Theta L (u' : ℂ) - Theta L (u : ℂ)) * SB L * Theta L (u' : ℂ)) x y‖
      ≤ (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u')⁻¹ := by
    calc ‖((Theta L (u' : ℂ) - Theta L (u : ℂ)) * SB L * Theta L (u' : ℂ)) x y‖
        ≤ ‖(Theta L (u' : ℂ) - Theta L (u : ℂ)) * SB L * Theta L (u' : ℂ)‖ :=
          norm_entry_le_norm L _ x y
      _ ≤ ‖(Theta L (u' : ℂ) - Theta L (u : ℂ)) * SB L‖ * ‖Theta L (u' : ℂ)‖ := norm_mul_le _ _
      _ ≤ (‖Theta L (u' : ℂ) - Theta L (u : ℂ)‖ * ‖SB L‖) * ‖Theta L (u' : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖Theta L (u' : ℂ) - Theta L (u : ℂ)‖ * ‖Theta L (u' : ℂ)‖ := by rw [norm_SB L hL, mul_one]
      _ ≤ ((u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹) * (1 - u')⁻¹ :=
          mul_le_mul hdop hΘ' (norm_nonneg _) hP
  have hb2 : ‖(Theta L (u : ℂ) * SB L * (Theta L (u' : ℂ) - Theta L (u : ℂ))) x y‖
      ≤ (1 - u)⁻¹ * ((u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹) := by
    calc ‖(Theta L (u : ℂ) * SB L * (Theta L (u' : ℂ) - Theta L (u : ℂ))) x y‖
        ≤ ‖Theta L (u : ℂ) * SB L * (Theta L (u' : ℂ) - Theta L (u : ℂ))‖ :=
          norm_entry_le_norm L _ x y
      _ ≤ ‖Theta L (u : ℂ) * SB L‖ * ‖Theta L (u' : ℂ) - Theta L (u : ℂ)‖ := norm_mul_le _ _
      _ ≤ (‖Theta L (u : ℂ)‖ * ‖SB L‖) * ‖Theta L (u' : ℂ) - Theta L (u : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖Theta L (u : ℂ)‖ * ‖Theta L (u' : ℂ) - Theta L (u : ℂ)‖ := by rw [norm_SB L hL, mul_one]
      _ ≤ (1 - u)⁻¹ * ((u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹) := mul_le_mul hΘ hdop (norm_nonneg _)
          (by positivity)
  refine (norm_add_le _ _).trans ?_
  have hb2' : (1 - u)⁻¹ * ((u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹)
      ≤ (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u')⁻¹ := by
    have heq : (1 - u)⁻¹ * ((u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹)
        = (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u)⁻¹ := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmono hP
  calc ‖((Theta L (u' : ℂ) - Theta L (u : ℂ)) * SB L * Theta L (u' : ℂ)) x y‖
        + ‖(Theta L (u : ℂ) * SB L * (Theta L (u' : ℂ) - Theta L (u : ℂ))) x y‖
      ≤ (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u')⁻¹
        + (1 - u)⁻¹ * ((u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹) := add_le_add hb1 hb2
    _ ≤ (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u')⁻¹
        + (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u')⁻¹ := add_le_add le_rfl hb2'
    _ = (u' - u) * (2 * ((1 - u')⁻¹ ^ 2 * (1 - u)⁻¹)) := by ring

/-- The "erase one index" variant of `norm_prod_sub_prod_le`, via a dummy value `1` at `i`. -/
theorem norm_prod_erase_sub_le {n : ℕ} (i : Fin n) (f g : Fin n → ℂ) {M D : ℝ} (hM1 : 1 ≤ M)
    (hD0 : 0 ≤ D) (hf : ∀ j, ‖f j‖ ≤ M) (hg : ∀ j, ‖g j‖ ≤ M) (hfg : ∀ j, ‖f j - g j‖ ≤ D) :
    ‖(∏ j ∈ Finset.univ.erase i, f j) - ∏ j ∈ Finset.univ.erase i, g j‖ ≤ n * M ^ n * D := by
  classical
  set f' : Fin n → ℂ := fun j => if j = i then 1 else f j with hf'def
  set g' : Fin n → ℂ := fun j => if j = i then 1 else g j with hg'def
  have hprodf : (∏ j, f' j) = ∏ j ∈ Finset.univ.erase i, f j := by
    rw [← Finset.mul_prod_erase Finset.univ f' (Finset.mem_univ i)]
    have hfi : f' i = 1 := by simp [hf'def]
    rw [hfi, one_mul]
    exact Finset.prod_congr rfl fun j hj => by simp [hf'def, (Finset.mem_erase.mp hj).1]
  have hprodg : (∏ j, g' j) = ∏ j ∈ Finset.univ.erase i, g j := by
    rw [← Finset.mul_prod_erase Finset.univ g' (Finset.mem_univ i)]
    have hgi : g' i = 1 := by simp [hg'def]
    rw [hgi, one_mul]
    exact Finset.prod_congr rfl fun j hj => by simp [hg'def, (Finset.mem_erase.mp hj).1]
  rw [← hprodf, ← hprodg]
  refine norm_prod_sub_prod_le f' g' hM1 hD0 (fun j => ?_) (fun j => ?_) (fun j => ?_)
  · by_cases hji : j = i
    · simp [hf'def, hji]; linarith
    · simpa [hf'def, hji] using hf j
  · by_cases hji : j = i
    · simp [hg'def, hji]; linarith
    · simpa [hg'def, hji] using hg j
  · by_cases hji : j = i
    · simp [hf'def, hg'def, hji]; linarith
    · simpa [hf'def, hg'def, hji] using hfg j

set_option maxHeartbeats 1000000 in
-- the final `nlinarith` combines four monomial bounds of degree `n + 6`; it needs extra time
/-- **Route A, final step: the Lipschitz bound for `ϑ̇` (`varthetaDot`), general `n`, purely
algebraic** (no calculus beyond the already-proved `hasDerivAt_vartheta`; this bounds the
*difference*, using the exact resolvent identity twice via `norm_Theta_real_sub_le` /
`norm_TST_real_sub_le` and the crude product-Lipschitz bound `norm_prod_sub_prod_le`). This is
the missing ingredient for the quadratic Taylor remainder of `Qop`. -/
theorem norm_varthetaDot_real_sub_le (hL : 3 ≤ L) {n : ℕ} {u u' : ℝ} (hu0 : 0 ≤ u)
    (huu' : u ≤ u') (hu'1 : u' < 1) (a : LoopArg L (n + 1)) :
    ‖varthetaDot L u' a - varthetaDot L u a‖
      ≤ (u' - u) * (10 * ((n : ℝ) + 1) ^ 2) * (1 - u')⁻¹ ^ (n + 6) := by
  have hu1 : u < 1 := lt_of_le_of_lt huu' hu'1
  set M : ℝ := (1 - u')⁻¹ with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]; rw [le_inv_comm₀ (by norm_num) (by linarith)]; linarith
  have hMu : (1 - u)⁻¹ ≤ M := by
    rw [hMdef, inv_le_inv₀ (by linarith) (by linarith)]; linarith
  set D : ℝ := (u' - u) * M ^ 2 with hDdef
  have hD0 : 0 ≤ D := by positivity
  have huD : u' - u ≤ D := by
    have : (1:ℝ) ≤ M ^ 2 := one_le_pow₀ hM1
    rw [hDdef]; nlinarith [sub_nonneg.mpr huu']
  -- entrywise magnitude bounds
  have hThP : ∀ x y : ZMod L, ‖Theta L (u' : ℂ) x y‖ ≤ M := fun x y => by
    have h := norm_Theta_apply_le L hL (norm_ofReal_lt_one (hu0.trans huu') hu'1) x y
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hu0.trans huu')] at h
  have hTh : ∀ x y : ZMod L, ‖Theta L (u : ℂ) x y‖ ≤ M := fun x y =>
    (by
      have h := norm_Theta_apply_le L hL (norm_ofReal_lt_one hu0 hu1) x y
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] at h :
        ‖Theta L (u:ℂ) x y‖ ≤ (1-u)⁻¹).trans hMu
  have hThD : ∀ x y : ZMod L, ‖Theta L (u' : ℂ) x y - Theta L (u : ℂ) x y‖ ≤ D := fun x y => by
    have h := norm_Theta_real_sub_le L hL hu0 huu' hu'1 x y
    calc ‖Theta L (u' : ℂ) x y - Theta L (u : ℂ) x y‖ ≤ (u' - u) * (1 - u')⁻¹ * (1 - u)⁻¹ := h
      _ ≤ (u' - u) * M * M := by
          have h0 : (0:ℝ) ≤ u' - u := by linarith
          gcongr
      _ = D := by rw [hDdef]; ring
  have hTSTP : ∀ x y : ZMod L, ‖(Theta L (u' : ℂ) * SB L * Theta L (u' : ℂ)) x y‖ ≤ M ^ 2 := by
    intro x y
    calc ‖(Theta L (u' : ℂ) * SB L * Theta L (u' : ℂ)) x y‖
        ≤ ‖Theta L (u' : ℂ) * SB L * Theta L (u' : ℂ)‖ := norm_entry_le_norm L _ x y
      _ ≤ ‖Theta L (u' : ℂ) * SB L‖ * ‖Theta L (u' : ℂ)‖ := norm_mul_le _ _
      _ ≤ (‖Theta L (u' : ℂ)‖ * ‖SB L‖) * ‖Theta L (u' : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖Theta L (u' : ℂ)‖ * ‖Theta L (u' : ℂ)‖ := by rw [norm_SB L hL, mul_one]
      _ ≤ M * M := by
          have h : ‖Theta L (u' : ℂ)‖ ≤ M := by
            have := norm_Theta_le L hL (norm_ofReal_lt_one (hu0.trans huu') hu'1)
            rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hu0.trans huu'), ← hMdef]
              at this
          exact mul_le_mul h h (norm_nonneg _) (by linarith)
      _ = M ^ 2 := by ring
  have hTSTD : ∀ x y : ZMod L,
      ‖(Theta L (u' : ℂ) * SB L * Theta L (u' : ℂ)) x y
          - (Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y‖ ≤ 2 * D * M := fun x y => by
    have h := norm_TST_real_sub_le L hL hu0 huu' hu'1 x y
    calc ‖(Theta L (u' : ℂ) * SB L * Theta L (u' : ℂ)) x y
          - (Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y‖
        ≤ (u' - u) * (2 * ((1 - u')⁻¹ ^ 2 * (1 - u)⁻¹)) := h
      _ ≤ (u' - u) * (2 * (M ^ 2 * M)) := by
          have h0 : (0:ℝ) ≤ u' - u := by linarith
          gcongr
      _ = 2 * D * M := by rw [hDdef]; ring
  have hTSTQ : ∀ x y : ZMod L, ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y‖ ≤ M ^ 2 := by
    intro x y
    calc ‖(Theta L (u : ℂ) * SB L * Theta L (u : ℂ)) x y‖
        ≤ ‖Theta L (u : ℂ) * SB L * Theta L (u : ℂ)‖ := norm_entry_le_norm L _ x y
      _ ≤ ‖Theta L (u : ℂ) * SB L‖ * ‖Theta L (u : ℂ)‖ := norm_mul_le _ _
      _ ≤ (‖Theta L (u : ℂ)‖ * ‖SB L‖) * ‖Theta L (u : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖Theta L (u : ℂ)‖ * ‖Theta L (u : ℂ)‖ := by rw [norm_SB L hL, mul_one]
      _ ≤ M * M := by
          have h : ‖Theta L (u : ℂ)‖ ≤ M := by
            have h2 := norm_Theta_le L hL (norm_ofReal_lt_one hu0 hu1)
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] at h2
            exact h2.trans hMu
          exact mul_le_mul h h (norm_nonneg _) (by linarith)
      _ = M ^ 2 := by ring
  -- abbreviations for the two pieces of `varthetaDot`'s formula
  set Bf : ℝ → ℂ := fun t => ∏ i : Fin n, Theta L (t : ℂ) (a 0) (a i.succ) with hBfdef
  set Pf : ℝ → Fin n → ℂ :=
    fun t i => ∏ j ∈ Finset.univ.erase i, Theta L (t : ℂ) (a 0) (a j.succ) with hPfdef
  set Tf : ℝ → Fin n → ℂ :=
    fun t i => (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a i.succ) with hTfdef
  set Sf : ℝ → ℂ := fun t => ∑ i : Fin n, Pf t i * Tf t i with hSfdef
  have hveq : ∀ t : ℝ, varthetaDot L t a
      = (-(n : ℂ) * (1 - (t : ℂ)) ^ (n - 1)) * Bf t + (1 - (t : ℂ)) ^ n * Sf t := fun t => rfl
  -- product magnitude bounds
  have hf : ∀ i : Fin n, ‖Theta L (u' : ℂ) (a 0) (a i.succ)‖ ≤ M := fun i => hThP _ _
  have hg : ∀ i : Fin n, ‖Theta L (u : ℂ) (a 0) (a i.succ)‖ ≤ M := fun i => hTh _ _
  have hfg : ∀ i : Fin n, ‖Theta L (u' : ℂ) (a 0) (a i.succ) - Theta L (u : ℂ) (a 0) (a i.succ)‖
      ≤ D := fun i => hThD _ _
  have hBfP_le : ‖Bf u'‖ ≤ M ^ n := by
    calc ‖Bf u'‖ ≤ ∏ i : Fin n, ‖Theta L (u' : ℂ) (a 0) (a i.succ)‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ _i : Fin n, M := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hf i)
      _ = M ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hBfQ_le : ‖Bf u‖ ≤ M ^ n := by
    calc ‖Bf u‖ ≤ ∏ i : Fin n, ‖Theta L (u : ℂ) (a 0) (a i.succ)‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ _i : Fin n, M := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hg i)
      _ = M ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hBf_sub : ‖Bf u' - Bf u‖ ≤ n * M ^ n * D :=
    norm_prod_sub_prod_le _ _ hM1 hD0 hf hg hfg
  have hPfP_le : ∀ i, ‖Pf u' i‖ ≤ M ^ n := by
    intro i
    calc ‖Pf u' i‖ ≤ ∏ j ∈ Finset.univ.erase i, ‖Theta L (u' : ℂ) (a 0) (a j.succ)‖ :=
          Finset.norm_prod_le _ _
      _ ≤ ∏ _j ∈ Finset.univ.erase i, M :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hf j)
      _ = M ^ (Finset.univ.erase i).card := by rw [Finset.prod_const]
      _ ≤ M ^ n := by
          apply pow_le_pow_right₀ hM1
          simpa using Finset.card_erase_le (a := i) (s := (Finset.univ : Finset (Fin n)))
  have hPf_sub : ∀ i, ‖Pf u' i - Pf u i‖ ≤ n * M ^ n * D :=
    fun i => norm_prod_erase_sub_le i _ _ hM1 hD0 hf hg hfg
  have hTfP_le : ∀ i, ‖Tf u' i‖ ≤ M ^ 2 := fun i => hTSTP _ _
  have hTfQ_le : ∀ i, ‖Tf u i‖ ≤ M ^ 2 := fun i => hTSTQ _ _
  have hTf_sub : ∀ i, ‖Tf u' i - Tf u i‖ ≤ 2 * D * M := fun i => hTSTD _ _
  have hMn2 : M ^ n ≤ M ^ (n + 2) := pow_le_pow_right₀ hM1 (by omega)
  have hMn1 : M ^ (n + 1) ≤ M ^ (n + 2) := pow_le_pow_right₀ hM1 (by omega)
  have hSf_sub : ‖Sf u' - Sf u‖ ≤ n * ((n : ℝ) + 2) * D * M ^ (n + 3) := by
    have hterm : ∀ i : Fin n, ‖Pf u' i * Tf u' i - Pf u i * Tf u i‖
        ≤ M ^ n * (2 * D * M) + n * M ^ n * D * M ^ 2 := by
      intro i
      have hsplit : Pf u' i * Tf u' i - Pf u i * Tf u i
          = Pf u' i * (Tf u' i - Tf u i) + (Pf u' i - Pf u i) * Tf u i := by ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h1 : ‖Pf u' i‖ * ‖Tf u' i - Tf u i‖ ≤ M ^ n * (2 * D * M) :=
        mul_le_mul (hPfP_le i) (hTf_sub i) (norm_nonneg _) (by positivity)
      have h2 : ‖Pf u' i - Pf u i‖ * ‖Tf u i‖ ≤ n * M ^ n * D * M ^ 2 :=
        mul_le_mul (hPf_sub i) (hTfQ_le i) (norm_nonneg _) (by positivity)
      exact add_le_add h1 h2
    have hSfeq : ‖Sf u' - Sf u‖ = ‖∑ i : Fin n, (Pf u' i * Tf u' i - Pf u i * Tf u i)‖ := by
      simp only [hSfdef, ← Finset.sum_sub_distrib]
    rw [hSfeq]
    calc ‖∑ i : Fin n, (Pf u' i * Tf u' i - Pf u i * Tf u i)‖
        ≤ ∑ i : Fin n, ‖Pf u' i * Tf u' i - Pf u i * Tf u i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, (M ^ n * (2 * D * M) + n * M ^ n * D * M ^ 2) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = n * (M ^ n * (2 * D * M) + n * M ^ n * D * M ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ n * ((n : ℝ) + 2) * D * M ^ (n + 3) := by
          have ea : M ^ n * (2 * D * M) = 2 * D * M ^ (n + 1) := by
            have h := (pow_succ M n).symm
            calc M ^ n * (2 * D * M) = 2 * D * (M ^ n * M) := by ring
              _ = 2 * D * M ^ (n + 1) := by rw [h]
          have eb : M ^ n * D * M ^ 2 = D * M ^ (n + 2) := by
            have h := (pow_add M n 2).symm
            calc M ^ n * D * M ^ 2 = D * (M ^ n * M ^ 2) := by ring
              _ = D * M ^ (n + 2) := by rw [h]
          have hM1' : M ^ (n+1) ≤ M ^ (n+3) := pow_le_pow_right₀ hM1 (by omega)
          have hM2' : M ^ (n+2) ≤ M ^ (n+3) := pow_le_pow_right₀ hM1 (by omega)
          nlinarith [ea, eb, hD0, sq_nonneg ((n:ℝ)),
            mul_le_mul_of_nonneg_left hM1' (by positivity : (0:ℝ) ≤ 2 * D),
            mul_le_mul_of_nonneg_left hM2' (by positivity : (0:ℝ) ≤ (n:ℝ) * D)]
  have hSf_le : ‖Sf u‖ ≤ (n : ℝ) * M ^ (n + 2) := by
    have hSueq : ‖Sf u‖ = ‖∑ i : Fin n, Pf u i * Tf u i‖ := by simp only [hSfdef]
    rw [hSueq]
    calc ‖∑ i : Fin n, Pf u i * Tf u i‖
        ≤ ∑ i : Fin n, ‖Pf u i * Tf u i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, M ^ (n+2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          calc ‖Pf u i‖ * ‖Tf u i‖ ≤ M ^ n * M ^ 2 := by
                have hPuQ_le : ‖Pf u i‖ ≤ M ^ n := by
                  calc ‖Pf u i‖ ≤ ∏ j ∈ Finset.univ.erase i, ‖Theta L (u : ℂ) (a 0) (a j.succ)‖ :=
                        Finset.norm_prod_le _ _
                    _ ≤ ∏ _j ∈ Finset.univ.erase i, M :=
                        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hg j)
                    _ = M ^ (Finset.univ.erase i).card := by rw [Finset.prod_const]
                    _ ≤ M ^ n := pow_le_pow_right₀ hM1
                        (by simpa using
                          Finset.card_erase_le (a := i) (s := (Finset.univ : Finset (Fin n))))
                exact mul_le_mul hPuQ_le (hTfQ_le i) (norm_nonneg _) (by positivity)
            _ = M ^ (n + 2) := by rw [← pow_add]
      _ = n * M ^ (n + 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the two power-difference facts for `(1-t)^k`
  have hpow1 : ‖(1 - (u' : ℂ)) ^ n - (1 - (u : ℂ)) ^ n‖ ≤ (n : ℝ) * (u' - u) := by
    have hreal : |( 1 - u') ^ n - (1 - u) ^ n|
        ≤ |(1 - u') - (1 - u)| * n * (max |1-u'| |1-u|) ^ (n-1) :=
      _root_.abs_pow_sub_pow_le (1 - u') (1 - u) n
    have hcast : (1 - (u' : ℂ)) ^ n - (1 - (u : ℂ)) ^ n
        = (((1 - u') ^ n - (1 - u) ^ n : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    have hmax : max |1 - u'| |1 - u| ≤ 1 := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - u'), abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - u)]
      exact max_le (by linarith) (by linarith)
    have hpow_le : (max |1 - u'| |1 - u|) ^ (n - 1) ≤ 1 := by
      calc (max |1 - u'| |1 - u|) ^ (n - 1) ≤ 1 ^ (n-1) := by
            apply pow_le_pow_left₀ (by positivity) hmax
        _ = 1 := one_pow _
    have habs : |(1 - u') - (1 - u)| = u' - u := by
      rw [show (1 - u') - (1 - u) = -(u' - u) by ring, abs_neg, abs_of_nonneg (by linarith)]
    calc |(1 - u') ^ n - (1 - u) ^ n| ≤ |(1-u')-(1-u)| * n * (max |1-u'| |1-u|)^(n-1) := hreal
      _ ≤ (u' - u) * n * 1 := by
          rw [habs]
          gcongr
      _ = (n:ℝ) * (u' - u) := by ring
  have hpow2 : ‖(1 - (u' : ℂ)) ^ (n-1) - (1 - (u : ℂ)) ^ (n-1)‖ ≤ (n : ℝ) * (u' - u) := by
    have hreal : |(1 - u') ^ (n-1) - (1 - u) ^ (n-1)|
        ≤ |(1 - u') - (1 - u)| * ((n-1 : ℕ):ℝ) * (max |1-u'| |1-u|) ^ ((n-1)-1) :=
      _root_.abs_pow_sub_pow_le (1 - u') (1 - u) (n-1)
    have hcast : (1 - (u' : ℂ)) ^ (n-1) - (1 - (u : ℂ)) ^ (n-1)
        = (((1 - u') ^ (n-1) - (1 - u) ^ (n-1) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    have hmax : max |1 - u'| |1 - u| ≤ 1 := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - u'), abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - u)]
      exact max_le (by linarith) (by linarith)
    have hpow_le : (max |1 - u'| |1 - u|) ^ ((n-1)-1) ≤ 1 := by
      calc (max |1 - u'| |1 - u|) ^ ((n-1)-1) ≤ 1 ^ ((n-1)-1) := by
            apply pow_le_pow_left₀ (by positivity) hmax
        _ = 1 := one_pow _
    have habs : |(1 - u') - (1 - u)| = u' - u := by
      rw [show (1 - u') - (1 - u) = -(u' - u) by ring, abs_neg, abs_of_nonneg (by linarith)]
    calc |(1 - u') ^ (n-1) - (1 - u) ^ (n-1)|
        ≤ |(1-u')-(1-u)| * ((n-1 : ℕ):ℝ) * (max |1-u'| |1-u|)^((n-1)-1) := hreal
      _ ≤ (u' - u) * ((n-1 : ℕ):ℝ) * 1 := by
          rw [habs]
          gcongr
      _ ≤ (n : ℝ) * (u' - u) := by
          have hcast : ((n - 1 : ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.sub_le n 1
          nlinarith [hD0, hcast]
  have hpowone1 : ‖(1 - (u' : ℂ)) ^ n‖ ≤ 1 := by
    rw [norm_pow]
    have : ‖(1 - (u':ℂ))‖ = 1 - u' := by
      rw [show (1 - (u':ℂ)) = ((1 - u' : ℝ):ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [this]
    exact pow_le_one₀ (by linarith) (by linarith)
  have hpowone2 : ‖(1 - (u' : ℂ)) ^ (n-1)‖ ≤ 1 := by
    rw [norm_pow]
    have : ‖(1 - (u':ℂ))‖ = 1 - u' := by
      rw [show (1 - (u':ℂ)) = ((1 - u' : ℝ):ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [this]
    exact pow_le_one₀ (by linarith) (by linarith)
  have hncomplex : ‖(-(n:ℂ))‖ = (n:ℝ) := by
    rw [norm_neg]
    simp
  rw [hveq u', hveq u]
  have hsplit : (-(n : ℂ) * (1 - (u' : ℂ)) ^ (n - 1)) * Bf u' + (1 - (u' : ℂ)) ^ n * Sf u'
      - ((-(n : ℂ) * (1 - (u : ℂ)) ^ (n - 1)) * Bf u + (1 - (u : ℂ)) ^ n * Sf u)
      = -(n : ℂ) * ((1 - (u' : ℂ)) ^ (n - 1) * (Bf u' - Bf u)
          + ((1 - (u' : ℂ)) ^ (n - 1) - (1 - (u : ℂ)) ^ (n - 1)) * Bf u)
        + ((1 - (u' : ℂ)) ^ n * (Sf u' - Sf u)
          + ((1 - (u' : ℂ)) ^ n - (1 - (u : ℂ)) ^ n) * Sf u) := by ring
  rw [hsplit]
  have hApart : ‖(-(n : ℂ)) * ((1 - (u' : ℂ)) ^ (n - 1) * (Bf u' - Bf u)
        + ((1 - (u' : ℂ)) ^ (n - 1) - (1 - (u : ℂ)) ^ (n - 1)) * Bf u)‖
      ≤ (n:ℝ) * ((n:ℝ) * M ^ n * D + (n:ℝ) * (u' - u) * M ^ n) := by
    rw [norm_mul, hncomplex]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖(1 - (u' : ℂ)) ^ (n - 1)‖ * ‖Bf u' - Bf u‖ ≤ 1 * ((n:ℝ) * M ^ n * D) :=
      mul_le_mul hpowone2 hBf_sub (norm_nonneg _) (by norm_num)
    have h2 : ‖(1 - (u' : ℂ)) ^ (n - 1) - (1 - (u : ℂ)) ^ (n - 1)‖ * ‖Bf u‖
        ≤ (n:ℝ) * (u' - u) * M ^ n :=
      mul_le_mul hpow2 hBfQ_le (norm_nonneg _) (by positivity)
    calc ‖(1 - (u' : ℂ)) ^ (n - 1)‖ * ‖Bf u' - Bf u‖
          + ‖(1 - (u' : ℂ)) ^ (n - 1) - (1 - (u : ℂ)) ^ (n - 1)‖ * ‖Bf u‖
        ≤ 1 * ((n:ℝ) * M ^ n * D) + (n:ℝ) * (u' - u) * M ^ n := add_le_add h1 h2
      _ = (n:ℝ) * M ^ n * D + (n:ℝ) * (u' - u) * M ^ n := by ring
  have hCpart : ‖(1 - (u' : ℂ)) ^ n * (Sf u' - Sf u)
        + ((1 - (u' : ℂ)) ^ n - (1 - (u : ℂ)) ^ n) * Sf u‖
      ≤ n * ((n:ℝ) + 2) * D * M ^ (n + 3) + (n:ℝ) * (u' - u) * ((n:ℝ) * M ^ (n + 2)) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖(1 - (u' : ℂ)) ^ n‖ * ‖Sf u' - Sf u‖ ≤ 1 * (n * ((n:ℝ) + 2) * D * M ^ (n + 3)) :=
      mul_le_mul hpowone1 hSf_sub (norm_nonneg _) (by norm_num)
    have h2 : ‖(1 - (u' : ℂ)) ^ n - (1 - (u : ℂ)) ^ n‖ * ‖Sf u‖
        ≤ (n:ℝ) * (u' - u) * ((n:ℝ) * M ^ (n + 2)) :=
      mul_le_mul hpow1 hSf_le (norm_nonneg _) (by positivity)
    calc ‖(1 - (u' : ℂ)) ^ n‖ * ‖Sf u' - Sf u‖
          + ‖(1 - (u' : ℂ)) ^ n - (1 - (u : ℂ)) ^ n‖ * ‖Sf u‖
        ≤ 1 * (n * ((n:ℝ) + 2) * D * M ^ (n + 3)) + (n:ℝ) * (u' - u) * ((n:ℝ) * M ^ (n + 2)) :=
          add_le_add h1 h2
      _ = n * ((n:ℝ) + 2) * D * M ^ (n + 3) + (n:ℝ) * (u' - u) * ((n:ℝ) * M ^ (n + 2)) := by ring
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add hApart hCpart).trans ?_
  have hx0 : (0:ℝ) ≤ u' - u := by linarith
  have hM0 : (0:ℝ) ≤ M := by linarith
  have hMn6 : M ^ n ≤ M ^ (n + 6) := pow_le_pow_right₀ hM1 (by omega)
  have hMn2_6 : M ^ (n + 2) ≤ M ^ (n + 6) := pow_le_pow_right₀ hM1 (by omega)
  have hMn5_6 : M ^ (n + 5) ≤ M ^ (n + 6) := pow_le_pow_right₀ hM1 (by omega)
  have hDeq : D = (u' - u) * M ^ 2 := hDdef
  have heq1 : (n:ℝ) * ((n:ℝ) * M ^ n * D + (n:ℝ) * (u' - u) * M ^ n)
      = (n:ℝ)^2 * (u' - u) * M ^ (n+2) + (n:ℝ)^2 * (u' - u) * M ^ n := by
    rw [hDeq]; ring
  have heq2 : n * ((n:ℝ) + 2) * D * M ^ (n + 3) + (n:ℝ) * (u' - u) * ((n:ℝ) * M ^ (n + 2))
      = (n:ℝ) * ((n:ℝ)+2) * (u' - u) * M ^ (n+5) + (n:ℝ)^2 * (u' - u) * M ^ (n+2) := by
    rw [hDeq]; ring
  rw [heq1, heq2]
  have hb1 : (n:ℝ)^2 * (u' - u) * M ^ (n+2) ≤ (n:ℝ)^2 * (u' - u) * M ^ (n+6) :=
    by gcongr
  have hb2 : (n:ℝ)^2 * (u' - u) * M ^ n ≤ (n:ℝ)^2 * (u' - u) * M ^ (n+6) :=
    by gcongr
  have hb3 : (n:ℝ) * ((n:ℝ)+2) * (u' - u) * M ^ (n+5)
      ≤ (n:ℝ) * ((n:ℝ)+2) * (u' - u) * M ^ (n+6) := by gcongr
  have hb4 : (n:ℝ)^2 * (u' - u) * M ^ (n+2) ≤ (n:ℝ)^2 * (u' - u) * M ^ (n+6) :=
    by gcongr
  have hsum : (n:ℝ)^2 * (u' - u) * M ^ (n+2) + (n:ℝ)^2 * (u' - u) * M ^ n
      + ((n:ℝ) * ((n:ℝ)+2) * (u' - u) * M ^ (n+5) + (n:ℝ)^2 * (u' - u) * M ^ (n+2))
      ≤ (4 * (n:ℝ)^2 + 2*(n:ℝ)) * (u' - u) * M ^ (n+6) := by
    have := add_le_add (add_le_add hb1 hb2) (add_le_add hb3 hb4)
    calc (n:ℝ)^2 * (u' - u) * M ^ (n+2) + (n:ℝ)^2 * (u' - u) * M ^ n
        + ((n:ℝ) * ((n:ℝ)+2) * (u' - u) * M ^ (n+5) + (n:ℝ)^2 * (u' - u) * M ^ (n+2))
        ≤ (n:ℝ)^2 * (u' - u) * M ^ (n+6) + (n:ℝ)^2 * (u' - u) * M ^ (n+6)
          + ((n:ℝ) * ((n:ℝ)+2) * (u' - u) * M ^ (n+6) + (n:ℝ)^2 * (u' - u) * M ^ (n+6)) := this
      _ = (4 * (n:ℝ)^2 + 2*(n:ℝ)) * (u' - u) * M ^ (n+6) := by ring
  refine hsum.trans ?_
  have hcoef : 4 * (n:ℝ)^2 + 2*(n:ℝ) ≤ 10 * ((n:ℝ)+1)^2 := by nlinarith [sq_nonneg ((n:ℝ))]
  have hMpow : (0:ℝ) ≤ M ^ (n+6) := pow_nonneg hM0 _
  nlinarith [mul_le_mul_of_nonneg_right hcoef (mul_nonneg hx0 hMpow)]

end ProdDiff

section QopStep

/-- The outer mean-value / Taylor step: given `hasDerivAt_vartheta` (the exact derivative) and
`norm_varthetaDot_real_sub_le` (the Lipschitz bound on that derivative), `ϑ_{u'} = ϑ_u +
(u'-u)ϑ̇_u + O((u'-u)^2 (1-u')^{-(n+6)})`. -/
theorem norm_vartheta_taylor_sub_le (hL : 3 ≤ L) {n : ℕ} {u u' : ℝ} (hu0 : 0 ≤ u)
    (huu' : u ≤ u') (hu'1 : u' < 1) (a : LoopArg L (n + 1)) :
    ‖vartheta L (u' : ℂ) a - vartheta L (u : ℂ) a - ((u' - u : ℝ) : ℂ) * varthetaDot L u a‖
      ≤ (5 * ((n : ℝ) + 1) ^ 2) * (1 - u')⁻¹ ^ (n + 6) * (u' - u) ^ 2 := by
  set K : ℝ := 10 * ((n:ℝ) + 1) ^ 2 * (1 - u')⁻¹ ^ (n + 6) with hKdef
  have hK0 : 0 ≤ K := by positivity
  set g : ℝ → ℂ := fun t => vartheta L (t : ℂ) a - vartheta L (u : ℂ) a
    - ((t - u : ℝ) : ℂ) * varthetaDot L u a with hgdef
  set B : ℝ → ℝ := fun t => (K / 2) * (t - u) ^ 2 with hBdef
  have hgderiv : ∀ t : ℝ, 0 ≤ t → t < 1 →
      HasDerivAt g (varthetaDot L t a - varthetaDot L u a) t := by
    intro t ht0 ht1
    have h1 : HasDerivAt (fun s : ℝ => vartheta L (s : ℂ) a) (varthetaDot L t a) t :=
      hasDerivAt_vartheta L hL ht0 ht1 a
    have h2 : HasDerivAt (fun s : ℝ => ((s - u : ℝ) : ℂ) * varthetaDot L u a)
        (varthetaDot L u a) t := by
      have h3 : HasDerivAt (fun s : ℝ => ((s - u : ℝ) : ℂ)) (1 : ℂ) t := by
        have h4 : HasDerivAt (fun s : ℝ => s - u) (1 : ℝ) t := (hasDerivAt_id t).sub_const u
        simpa using h4.ofReal_comp
      simpa using h3.mul_const (varthetaDot L u a)
    have hcomb := (h1.sub_const (vartheta L (u : ℂ) a)).sub h2
    have heq : (fun s : ℝ => vartheta L (s : ℂ) a - vartheta L (u : ℂ) a)
        - (fun s : ℝ => ((s - u : ℝ) : ℂ) * varthetaDot L u a) = g := by
      funext s
      show vartheta L (s : ℂ) a - vartheta L (u : ℂ) a - ((s - u : ℝ) : ℂ) * varthetaDot L u a
        = g s
      rw [hgdef]
    rw [heq] at hcomb
    exact hcomb
  have hBderiv : ∀ t : ℝ, HasDerivAt B (K * (t - u)) t := by
    intro t
    have hid : HasDerivAt (fun s : ℝ => s - u) 1 t := (hasDerivAt_id t).sub_const u
    have h1 : HasDerivAt (fun s : ℝ => (s - u) * (s - u)) ((1:ℝ) * (t - u) + (t - u) * 1) t :=
      hid.mul hid
    have h2 := h1.const_mul (K / 2)
    have heq : (fun s : ℝ => K / 2 * ((s - u) * (s - u))) = B := by
      funext s; rw [hBdef]; ring
    rw [heq] at h2
    exact h2.congr_deriv (by ring)
  have hga : ‖g u‖ ≤ B u := by simp [hgdef, hBdef]
  have hgcont : ContinuousOn g (Set.Icc u u') := by
    intro t ht
    exact (hgderiv t (hu0.trans ht.1) (lt_of_le_of_lt ht.2 hu'1)).continuousAt.continuousWithinAt
  have hgderivwithin : ∀ t ∈ Set.Ico u u',
      HasDerivWithinAt g (varthetaDot L t a - varthetaDot L u a) (Set.Ici t) t :=
    fun t ht => (hgderiv t (hu0.trans ht.1) (lt_trans ht.2 hu'1)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico u u', ‖varthetaDot L t a - varthetaDot L u a‖ ≤ K * (t - u) := by
    intro t ht
    have h1 := norm_varthetaDot_real_sub_le L hL hu0 ht.1 (lt_trans ht.2 hu'1) a
    have h2 : (1 - t)⁻¹ ^ (n + 6) ≤ (1 - u')⁻¹ ^ (n + 6) := by
      have h3 : (1 - t)⁻¹ ≤ (1 - u')⁻¹ := by
        rw [inv_le_inv₀ (by linarith [ht.2] : (0:ℝ) < 1 - t) (by linarith [ht.2] : (0:ℝ) < 1 - u')]
        linarith [ht.2]
      have h3' : (0:ℝ) ≤ (1 - t)⁻¹ := inv_nonneg.mpr (by linarith [ht.2])
      gcongr
    calc ‖varthetaDot L t a - varthetaDot L u a‖
        ≤ (t - u) * (10 * ((n:ℝ)+1)^2) * (1 - t)⁻¹ ^ (n+6) := h1
      _ ≤ (t - u) * (10 * ((n:ℝ)+1)^2) * (1 - u')⁻¹ ^ (n+6) := by
          have h4 : (0:ℝ) ≤ (t - u) * (10 * ((n:ℝ)+1)^2) :=
            mul_nonneg (by linarith [ht.1]) (by positivity)
          gcongr
      _ = K * (t - u) := by rw [hKdef]; ring
  have hfinal := image_norm_le_of_norm_deriv_right_le_deriv_boundary hgcont hgderivwithin hga
    hBderiv hbound (Set.right_mem_Icc.2 huu')
  calc ‖vartheta L (u' : ℂ) a - vartheta L (u : ℂ) a - ((u' - u : ℝ) : ℂ) * varthetaDot L u a‖
      = ‖g u'‖ := by rw [hgdef]
    _ ≤ B u' := hfinal
    _ = (5 * ((n:ℝ)+1)^2) * (1 - u')⁻¹ ^ (n+6) * (u' - u)^2 := by rw [hBdef, hKdef]; ring

end QopStep

end ContDiffTheta

section DirectReuse

variable (L : ℕ) [NeZero L]

/-- **`max_varthetaDot_le`, (5.87)-adjacent bound on `ϑ̇`, general `n`.** Direct instantiation
of `SumZeroDyn.norm_varthetaDot_le` (already deterministic, fixed real `u`, general `n`; `ℓ_u ↔
ellHat`, `η_u^{-1} ↔ (1-u)⁻¹`). -/
theorem max_varthetaDot_le (hL : 3 ≤ L) {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (a : LoopArg L (n + 1)) :
    ‖varthetaDot L u a‖ ≤ 2 * n * (cTwo52 / ellHat L (u : ℂ)) ^ n * (1 - u)⁻¹ :=
  norm_varthetaDot_le L hL hu0 hu1 a

/-- **`norm_comm_QTheta_le`, (5.99), general `n`.** Direct instantiation of
`SumZeroDyn.norm_commS_le` with `ξ := xiOf (mSigma E) σ` (`‖ξ_i‖ = 1` for `|E| ≤ 2`, general
charge `σ`, via `norm_xiOf_mSigma`), and a bound `P` on `P ∘ A` (matching (5.99)'s own hypothesis
structure: the paper bounds `[Q_t,Θ_{t,σ}] ∘ A` by `max_a |P ∘ A|_a`). -/
theorem norm_comm_QTheta_le (hL : 3 ≤ L) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (σ : Fin (n + 1) → Bool) {A : LoopArg L (n + 1) → ℂ} {P : ℝ} (hP0 : 0 ≤ P)
    (hPA : ∀ x, ‖Psum L A x‖ ≤ P) (a : LoopArg L (n + 1)) :
    ‖commS L (xiOf (mSigma E) σ) (u : ℂ) A a‖
      ≤ 2 * (n + 1) * (1 - u)⁻¹ * (cTwo52 / ellHat L (u : ℂ)) ^ n * P :=
  norm_commS_le L hL hu0 hu1 (fun i => le_of_eq (norm_xiOf_mSigma hE σ i)) hP0 hPA a

end DirectReuse



section WardTF

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
/-- Two resolvents of the same matrix commute. -/
theorem green_mul_green_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (z w : ℂ) : green H z * green H w = green H w * green H z := by
  unfold green
  rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev]
  congr 1
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_sub, smul_smul]
  rw [mul_comm z w]
  abel

omit [NeZero W] in
theorem Gt_mul_Gf {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    Gsig H z true * Gsig H z false
      = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gsig H z true - Gsig H z false) := by
  rw [← Gf_mul_Gt hH hz]
  simp only [Gsig_true]
  exact green_mul_green_comm H _ _

/-- **Ward's identity for `G`-loops at an interior label between `G(+)` and `G(-)`** (the
`(+,-)` companion of `sum_gloop_ward_mid`, from `G(+)G(-) = G(-)G(+)`). -/
theorem sum_gloop_ward_mid_tf {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ₁ σ₂ : List Bool) (a₁ a₂ : List (ZMod L))
    (h₁ : σ₁.length = a₁.length) (c : ZMod L) :
    ∑ b : ZMod L, gloop L W H z ⟨σ₁ ++ true :: false :: σ₂, a₁ ++ b :: c :: a₂⟩
      = (gloop L W H z ⟨σ₁ ++ true :: σ₂, a₁ ++ c :: a₂⟩
          - gloop L W H z ⟨σ₁ ++ false :: σ₂, a₁ ++ c :: a₂⟩) / (2 * W * Complex.I * z.im) := by
  set P₁ := gloopProd L W H z ⟨σ₁, a₁⟩
  set P₂ := gloopProd L W H z ⟨σ₂, a₂⟩
  have hterm : ∀ b : ZMod L, gloop L W H z ⟨σ₁ ++ true :: false :: σ₂, a₁ ++ b :: c :: a₂⟩
      = Matrix.trace (P₁ * Gsig H z true * Eblk L W b * (Gsig H z false * Eblk L W c * P₂)) := by
    intro b
    rw [gloop, gloopProd_append h₁, gloopProd_cons, gloopProd_cons]
    simp only [Matrix.mul_assoc]
    rfl
  simp_rw [hterm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, sum_Eblk L W]
  have e1 : gloop L W H z ⟨σ₁ ++ true :: σ₂, a₁ ++ c :: a₂⟩
      = Matrix.trace (P₁ * (Gsig H z true * Eblk L W c * P₂)) := by
    rw [gloop, gloopProd_append h₁, gloopProd_cons]
  have e2 : gloop L W H z ⟨σ₁ ++ false :: σ₂, a₁ ++ c :: a₂⟩
      = Matrix.trace (P₁ * (Gsig H z false * Eblk L W c * P₂)) := by
    rw [gloop, gloopProd_append h₁, gloopProd_cons]
  rw [e1, e2]
  have hG := Gt_mul_Gf hH hz
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by simp [Complex.I_ne_zero, hz]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  have key : P₁ * Gsig H z true * ((W : ℂ)⁻¹ • (1 : Matrix _ _ ℂ))
      * (Gsig H z false * Eblk L W c * P₂)
      = ((W : ℂ)⁻¹ * (2 * Complex.I * (z.im : ℂ))⁻¹)
        • (P₁ * (Gsig H z true * Eblk L W c * P₂) - P₁ * (Gsig H z false * Eblk L W c * P₂)) := by
    calc P₁ * Gsig H z true * ((W : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) * (Gsig H z false * Eblk L W c * P₂)
        = (W : ℂ)⁻¹ • (P₁ * (Gsig H z true * Gsig H z false) * Eblk L W c * P₂) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by
          rw [hG]
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.sub_mul, Matrix.mul_sub,
            Matrix.mul_assoc]
  rw [key, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  field_simp

/-- Ward's identity for `G`-loops at the last label, between `G(+)` at the end and `G(-)` at
the start. -/
theorem sum_gloop_ward_last_tf {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (μ : List Bool) (x : ZMod L)
    (a' : List (ZMod L)) (hμ : μ.length = a'.length) :
    ∑ b : ZMod L, gloop L W H z ⟨false :: μ ++ [true], x :: a' ++ [b]⟩
      = (gloop L W H z ⟨true :: μ, x :: a'⟩ - gloop L W H z ⟨false :: μ, x :: a'⟩)
        / (2 * W * Complex.I * z.im) := by
  set P := gloopProd L W H z ⟨μ, a'⟩
  have hl : (false :: μ).length = (x :: a').length := by simp [hμ]
  have hterm : ∀ b : ZMod L, gloop L W H z ⟨false :: μ ++ [true], x :: a' ++ [b]⟩
      = Matrix.trace (Gsig H z true * Eblk L W b * (Gsig H z false * Eblk L W x * P)) := by
    intro b
    rw [gloop, show false :: μ ++ [true] = (false :: μ) ++ [true] from rfl,
      show x :: a' ++ [b] = (x :: a') ++ [b] from rfl, gloopProd_append hl, gloopProd_cons,
      gloopProd_cons, gloopProd_nil, Matrix.mul_one, Matrix.trace_mul_comm]
  simp_rw [hterm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, sum_Eblk L W]
  have e1 : gloop L W H z ⟨true :: μ, x :: a'⟩ = Matrix.trace (Gsig H z true * Eblk L W x * P) := by
    rw [gloop, gloopProd_cons]
  have e2 : gloop L W H z ⟨false :: μ, x :: a'⟩
      = Matrix.trace (Gsig H z false * Eblk L W x * P) := by
    rw [gloop, gloopProd_cons]
  rw [e1, e2]
  have hG := Gt_mul_Gf hH hz
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by simp [Complex.I_ne_zero, hz]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  have key : Gsig H z true * ((W : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) * (Gsig H z false * Eblk L W x * P)
      = ((W : ℂ)⁻¹ * (2 * Complex.I * (z.im : ℂ))⁻¹)
        • (Gsig H z true * Eblk L W x * P - Gsig H z false * Eblk L W x * P) := by
    calc Gsig H z true * ((W : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) * (Gsig H z false * Eblk L W x * P)
        = (W : ℂ)⁻¹ • ((Gsig H z true * Gsig H z false) * Eblk L W x * P) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by
          rw [hG]
          simp only [Matrix.smul_mul, smul_smul, Matrix.sub_mul, Matrix.mul_assoc]
  rw [key, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  field_simp

end WardTF


section ConjK

variable {L : ℕ} [NeZero L]

theorem mSigma_not' (E : ℝ) (b : Bool) : mSigma E (!b) = (starRingEnd ℂ) (mSigma E b) := by
  cases b <;> simp [mSigma]

/-- `‖t m(s) m(s')‖ < 1` for `0 ≤ t < 1`, `|E| < 2`. -/
theorem norm_t_mm_lt_one {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s s' : Bool) : ‖(t : ℂ) * (mSigma E s * mSigma E s')‖ < 1 := by
  rw [norm_mul, norm_mul, norm_mSigma hE.le, norm_mSigma hE.le, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht0]
  linarith

theorem conj_t_mm (E t : ℝ) (s s' : Bool) :
    (starRingEnd ℂ) ((t : ℂ) * (mSigma E s * mSigma E s'))
      = (t : ℂ) * (mSigma E (!s) * mSigma E (!s')) := by
  rw [map_mul, map_mul, Complex.conj_ofReal, mSigma_not', mSigma_not']

theorem map_conj_thetaEdge (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (s s' : Bool) :
    (thetaEdge L (mSigma E) t s s').map (starRingEnd ℂ)
      = thetaEdge L (mSigma E) t (!s) (!s') := by
  ext x y
  rw [Matrix.map_apply, thetaEdge, thetaEdge,
    ChargeReduce.conj_Theta_apply L hL (norm_t_mm_lt_one hE ht0 ht1 s s') x y, conj_t_mm]

theorem conj_treeValW {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n)) (a : Fin n → ZMod L)
    (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) :
    (starRingEnd ℂ) (treeValW L F a M E)
      = treeValW L F a (fun v => (M v).map (starRingEnd ℂ))
          (fun d => (E d).map (starRingEnd ℂ)) := by
  simp only [treeValW, map_sum, map_mul, map_prod, Matrix.map_apply]

theorem conj_treeValG (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → ZMod L) (F : Finset (Fin n × Fin n)) :
    (starRingEnd ℂ) (treeValG L (mSigma E) t σ a F)
      = treeValG L (mSigma E) t (fun i => !σ i) a F := by
  rw [treeValG, conj_treeValW, treeValG]
  congr 1
  · funext v; exact map_conj_thetaEdge hL hE ht0 ht1 _ _
  · funext d
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _),
      map_conj_thetaEdge hL hE ht0 ht1]

theorem conj_Kn (hL : 3 ≤ L) (W : ℕ) {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → ZMod L) :
    (starRingEnd ℂ) (Kn L W (mSigma E) t n σ a) = Kn L W (mSigma E) t n (fun i => !σ i) a := by
  simp only [Kn, map_mul, map_prod, map_pow, map_inv₀, map_natCast, map_sum]
  congr 1
  · congr 1
    exact Finset.prod_congr rfl fun i _ => (mSigma_not' E (σ i)).symm
  · exact Finset.sum_congr rfl fun F _ => conj_treeValG hL hE ht0 ht1 σ a F

theorem getD_map_not (l : List Bool) {i : ℕ} (hi : i < l.length) :
    (l.map not).getD i false = !(l.getD i false) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
    List.getElem_map]

/-- **Conjugation flips every charge of the primitive loop**: `conj K_{t,σ,a} = K_{t,-σ,a}`
(labels and their order unchanged), for `0 ≤ t < 1`, `|E| < 2`, every length. From the tree
representation (Definition 3.3): `conj m(σ) = m(-σ)` and `conj Θ_ξ = Θ_{conj ξ}`. -/
theorem conj_Kgen_flip (hL : 3 ≤ L) (W : ℕ) {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (I : LoopIdx (ZMod L)) (hI : I.WF) :
    (starRingEnd ℂ) (Kgen L W (mSigma E) t I) = Kgen L W (mSigma E) t ⟨I.σ.map not, I.a⟩ := by
  have hlen : I.σ.length = I.a.length := hI
  have hlen1 : I.length = I.a.length := rfl
  have hJl : (⟨I.σ.map not, I.a⟩ : LoopIdx (ZMod L)).length = I.length := rfl
  rw [Kgen, Kgen]
  by_cases h1 : I.length = 1
  · have h1' : (⟨I.σ.map not, I.a⟩ : LoopIdx (ZMod L)).length = 1 := hJl.trans h1
    simp only [h1, h1', ↓reduceIte]
    rw [getD_map_not _ (by omega), mSigma_not']
  have h1' : ¬ (⟨I.σ.map not, I.a⟩ : LoopIdx (ZMod L)).length = 1 := by rw [hJl]; exact h1
  simp only [h1, h1', ↓reduceIte]
  by_cases h2 : I.length = 2
  · have h2' : (⟨I.σ.map not, I.a⟩ : LoopIdx (ZMod L)).length = 2 := hJl.trans h2
    simp only [h2, h2', ↓reduceIte]
    rw [getD_map_not _ (by omega), getD_map_not _ (by omega), kTwo, kTwo,
      map_mul, map_mul, map_inv₀, map_natCast,
      ChargeReduce.conj_Theta_apply L hL (norm_t_mm_lt_one hE ht0 ht1 _ _), conj_t_mm, map_mul,
      mSigma_not', mSigma_not']
  have h2' : ¬ (⟨I.σ.map not, I.a⟩ : LoopIdx (ZMod L)).length = 2 := by rw [hJl]; exact h2
  simp only [h2, h2', ↓reduceIte]
  by_cases h3 : 3 ≤ I.length
  · have h3' : 3 ≤ (⟨I.σ.map not, I.a⟩ : LoopIdx (ZMod L)).length := hJl ▸ h3
    have : NeZero I.length := ⟨by omega⟩
    simp only [h3, h3', ↓reduceDIte]
    rw [conj_Kn hL W hE ht0 ht1]
    congr 1
    funext i
    rw [getD_map_not _ (by omega)]
  · have h3' : ¬ 3 ≤ (⟨I.σ.map not, I.a⟩ : LoopIdx (ZMod L)).length := by rw [hJl]; exact h3
    simp only [h3, h3', ↓reduceDIte, map_zero]

/-- The inverse form: `K_{t,σ,a} = conj K_{t,-σ,a}`. -/
theorem Kgen_eq_conj_flip (hL : 3 ≤ L) (W : ℕ) {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ : List Bool) (a : List (ZMod L)) (h : σ.length = a.length) :
    Kgen L W (mSigma E) t ⟨σ, a⟩ = (starRingEnd ℂ) (Kgen L W (mSigma E) t ⟨σ.map not, a⟩) := by
  rw [conj_Kgen_flip hL W hE ht0 ht1 ⟨σ.map not, a⟩ (by simp [LoopIdx.WF, h])]
  simp [Function.comp_def]

end ConjK

section WardKTF

variable {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) [NeZero W] {E : ℝ} (hE : |E| < 2)
include hL hE

omit [NeZero L] hL [NeZero W] hE in
theorem conj_two_W_I_eta (t : ℝ) :
    (starRingEnd ℂ) (2 * (W : ℂ) * Complex.I * (etaT E t : ℂ))
      = -(2 * (W : ℂ) * Complex.I * (etaT E t : ℂ)) := by
  simp [map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast, map_ofNat]

/-- **Ward's identity for the primitive loop at an interior label between `G(+)` and `G(-)`**:
the `(+,-)` companion of `sum_Kgen_ward_mid`, obtained from it by conjugation
(`conj_Kgen_flip`). -/
theorem sum_Kgen_ward_mid_tf {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (σ₁ σ₂ : List Bool)
    (a₁ a₂ : List (ZMod L)) (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length)
    (hne : 1 ≤ a₁.length) (c : ZMod L) :
    ∑ b : ZMod L, Kgen L W (mSigma E) t ⟨σ₁ ++ true :: false :: σ₂, a₁ ++ b :: c :: a₂⟩
      = (Kgen L W (mSigma E) t ⟨σ₁ ++ true :: σ₂, a₁ ++ c :: a₂⟩
          - Kgen L W (mSigma E) t ⟨σ₁ ++ false :: σ₂, a₁ ++ c :: a₂⟩)
        / (2 * W * Complex.I * etaT E t) := by
  have hflip : ∀ b : ZMod L, Kgen L W (mSigma E) t ⟨σ₁ ++ true :: false :: σ₂, a₁ ++ b :: c :: a₂⟩
      = (starRingEnd ℂ) (Kgen L W (mSigma E) t
          ⟨σ₁.map not ++ false :: true :: σ₂.map not, a₁ ++ b :: c :: a₂⟩) := by
    intro b
    rw [Kgen_eq_conj_flip hL W hE ht0 ht1 _ _ (by simp [h₁, h₂])]
    simp
  simp_rw [hflip]
  rw [← map_sum, sum_Kgen_ward_mid hL W hE ht0 ht1 (σ₁.map not) (σ₂.map not) a₁ a₂
    (by simp [h₁]) (by simp [h₂]) hne c, map_div₀, map_sub, conj_two_W_I_eta W,
    Kgen_eq_conj_flip hL W hE ht0 ht1 (σ₁ ++ true :: σ₂) (a₁ ++ c :: a₂) (by simp [h₁, h₂]),
    Kgen_eq_conj_flip hL W hE ht0 ht1 (σ₁ ++ false :: σ₂) (a₁ ++ c :: a₂) (by simp [h₁, h₂])]
  simp only [List.map_append, List.map_cons, Bool.not_true, Bool.not_false]
  rw [div_neg, ← neg_div, neg_sub]

/-- Ward's identity for the primitive loop at the last label, between `G(+)` at the end and
`G(-)` at the start (conjugate of `ward_Kgen`). -/
theorem ward_Kgen_tf {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (μ : List Bool) (a' : List (ZMod L))
    (hμ : μ.length + 1 = a'.length) :
    ∑ x : ZMod L, Kgen L W (mSigma E) t ⟨false :: μ ++ [true], a' ++ [x]⟩
      = (Kgen L W (mSigma E) t ⟨true :: μ, a'⟩ - Kgen L W (mSigma E) t ⟨false :: μ, a'⟩)
        / (2 * W * Complex.I * etaT E t) := by
  have hflip : ∀ x : ZMod L, Kgen L W (mSigma E) t ⟨false :: μ ++ [true], a' ++ [x]⟩
      = (starRingEnd ℂ) (Kgen L W (mSigma E) t ⟨true :: μ.map not ++ [false], a' ++ [x]⟩) := by
    intro x
    rw [Kgen_eq_conj_flip hL W hE ht0 ht1 _ _ (by simp; omega)]
    simp
  simp_rw [hflip]
  rw [← map_sum, ward_Kgen hL W hE ht0 ht1 (μ.map not) a' (by simpa using hμ), map_div₀, map_sub,
    conj_two_W_I_eta W,
    Kgen_eq_conj_flip hL W hE ht0 ht1 (true :: μ) a' (by simp; omega),
    Kgen_eq_conj_flip hL W hE ht0 ht1 (false :: μ) a' (by simp; omega)]
  simp only [List.map_cons, Bool.not_true, Bool.not_false]
  rw [div_neg, ← neg_div, neg_sub]

end WardKTF

section WardM

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `L - K` of a fixed matrix `M` on loop indices, at the time `u`. -/
noncomputable def DlM (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (E u : ℝ)
    (I : LoopIdx (ZMod L)) : ℂ :=
  gloop L W M (zt E u) I - Kgen L W (mSigma E) u I

/-- The interior Ward step, for both orders `(p, !p)` of the opposite pair. -/
def WardMid (F : LoopIdx (ZMod L) → ℂ) (κ : ℂ) : Prop :=
  ∀ (p : Bool) (σ₁ σ₂ : List Bool) (a₁ a₂ : List (ZMod L)), σ₁.length = a₁.length →
    σ₂.length = a₂.length → 1 ≤ a₁.length → ∀ c : ZMod L,
      ∑ b : ZMod L, F ⟨σ₁ ++ p :: (!p) :: σ₂, a₁ ++ b :: c :: a₂⟩
        = κ * (F ⟨σ₁ ++ true :: σ₂, a₁ ++ c :: a₂⟩ - F ⟨σ₁ ++ false :: σ₂, a₁ ++ c :: a₂⟩)

/-- The last-label Ward step, for both orders. -/
def WardLast (F : LoopIdx (ZMod L) → ℂ) (κ : ℂ) : Prop :=
  ∀ (p : Bool) (μ : List Bool) (x : ZMod L) (a' : List (ZMod L)), μ.length = a'.length →
    ∑ b : ZMod L, F ⟨(!p) :: μ ++ [p], x :: a' ++ [b]⟩
      = κ * (F ⟨true :: μ, x :: a'⟩ - F ⟨false :: μ, x :: a'⟩)

theorem wardMid_DlM {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hM : M.IsHermitian)
    (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    WardMid (DlM M E u) (wardKappa W E u) := by
  intro p σ₁ σ₂ a₁ a₂ h₁ h₂ hne c
  have hη := etaT_pos hE hu1
  have hz : (zt E u).im ≠ 0 := by rw [zt_im_eq]; exact hη.ne'
  simp only [DlM]
  rw [Finset.sum_sub_distrib]
  cases p
  · rw [Bool.not_false, sum_gloop_ward_mid hM hz σ₁ σ₂ a₁ a₂ h₁ c,
      sum_Kgen_ward_mid hL W hE hu0 hu1 σ₁ σ₂ a₁ a₂ h₁ h₂ hne c, zt_im_eq, wardKappa]
    ring
  · rw [Bool.not_true, sum_gloop_ward_mid_tf hM hz σ₁ σ₂ a₁ a₂ h₁ c,
      sum_Kgen_ward_mid_tf hL W hE hu0 hu1 σ₁ σ₂ a₁ a₂ h₁ h₂ hne c, zt_im_eq, wardKappa]
    ring

theorem wardLast_DlM {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hM : M.IsHermitian)
    (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    WardLast (DlM M E u) (wardKappa W E u) := by
  intro p μ x a' hμ
  have hη := etaT_pos hE hu1
  have hz : (zt E u).im ≠ 0 := by rw [zt_im_eq]; exact hη.ne'
  simp only [DlM]
  rw [Finset.sum_sub_distrib]
  cases p
  · have hK := ward_Kgen hL W hE hu0 hu1 μ (x :: a') (by simp [hμ])
    simp only [List.cons_append] at hK
    rw [Bool.not_false, sum_gloop_ward_last hM hz μ x a' hμ]
    simp only [List.cons_append]
    rw [hK, zt_im_eq, wardKappa]
    ring
  · have hK := ward_Kgen_tf hL W hE hu0 hu1 μ (x :: a') (by simp [hμ])
    simp only [List.cons_append] at hK
    rw [Bool.not_true, sum_gloop_ward_last_tf hM hz μ x a' hμ]
    simp only [List.cons_append]
    rw [hK, zt_im_eq, wardKappa]
    ring

/-- The slot sum of `a ↦ F_{σ,a}` as a sum over label lists. -/
theorem Psum_loop_eq (F : LoopIdx (ZMod L) → ℂ) {n : ℕ} (σ : Fin (n + 1) → Bool) (x : ZMod L) :
    Psum L (fun b : LoopArg L (n + 1) => F ⟨List.ofFn σ, List.ofFn b⟩) x
      = allSum L n (fun rest => F ⟨List.ofFn σ, x :: rest⟩) := by
  rw [allSum_eq_sum_ofFn, Psum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [List.ofFn_succ]

/-- A non-constant charge vector has an opposite cyclic pair away from the fixed slot `0`. -/
theorem exists_ne_succ_of_nonconst {n : ℕ} {σ : Fin (n + 2) → Bool} (hσ : ∃ i j, σ i ≠ σ j) :
    ∃ j : Fin (n + 2), j ≠ 0 ∧ σ j ≠ σ (j + 1) := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ k : ℕ, (hk : k + 1 < n + 2) → σ ⟨k + 1, hk⟩ = σ ⟨1, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have h1 := hcon ⟨k + 1, by omega⟩ (by simp [Fin.ext_iff])
      have h2 : (⟨k + 1, by omega⟩ : Fin (n + 2)) + 1 = ⟨k + 1 + 1, hk⟩ := by
        rw [Fin.ext_iff, Fin.val_add_one_of_lt (by simp [Fin.lt_def]; omega)]
      rw [h2] at h1
      rw [← h1, ih (by omega)]
  have hall : ∀ i : Fin (n + 2), σ i = σ ⟨1, by omega⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    rcases i with _ | k
    · have h1 := hcon (Fin.last (n + 1)) (by simp [Fin.ext_iff])
      rw [Fin.last_add_one] at h1
      rw [show (⟨0, hi⟩ : Fin (n + 2)) = 0 from rfl, ← h1]
      exact hstep n (by omega)
    · exact hstep k hi
  obtain ⟨i, j, hij⟩ := hσ
  exact hij ((hall i).trans (hall j).symm)

/-- List form of the interior Ward step. -/
theorem ward_list_mid_of {F : LoopIdx (ZMod L) → ℂ} {κ : ℂ} (hmid : WardMid F κ)
    {p q m m' : ℕ} (hm : m = p + (q + 2)) (hm' : m' = p + (q + 1)) (s : Bool)
    (σ₁ σ₂ : List Bool) (h₁ : σ₁.length = p + 1) (h₂ : σ₂.length = q) (x : ZMod L) :
    allSum L m (fun rest => F ⟨σ₁ ++ s :: (!s) :: σ₂, x :: rest⟩)
      = κ * (allSum L m' (fun rest => F ⟨σ₁ ++ true :: σ₂, x :: rest⟩)
          - allSum L m' (fun rest => F ⟨σ₁ ++ false :: σ₂, x :: rest⟩)) := by
  subst hm hm'
  rw [allSum_add, allSum_add, allSum_add, ← allSum_linear]
  refine allSum_congr p fun l₁ hl₁ => ?_
  simp only [allSum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← allSum_sum, ← allSum_linear]
  refine allSum_congr q fun l₂ hl₂ => ?_
  have := hmid s σ₁ σ₂ (x :: l₁) l₂ (by simp [h₁, hl₁]) (by rw [h₂, hl₂]) (by simp) c
  simpa only [List.cons_append] using this

/-- **The Ward reduction of the slot sums (Lemma 3.6 applied to (5.96)), for every
non-constant charge vector**: given the two Ward steps for `F`, the slot sum of the loop of length
`n + 2` is `κ` times the difference of the slot sums of two loops of length `n + 1`. -/
theorem psum_ward_of {F : LoopIdx (ZMod L) → ℂ} {κ : ℂ} (hmid : WardMid F κ)
    (hlast : WardLast F κ) {n : ℕ} (σ : Fin (n + 2) → Bool) (hσ : ∃ i j, σ i ≠ σ j) :
    ∃ σ' σ'' : Fin (n + 1) → Bool, ∀ x : ZMod L,
      Psum L (fun b : LoopArg L (n + 2) => F ⟨List.ofFn σ, List.ofFn b⟩) x
        = κ * (Psum L (fun b : LoopArg L (n + 1) => F ⟨List.ofFn σ', List.ofFn b⟩) x
          - Psum L (fun b : LoopArg L (n + 1) => F ⟨List.ofFn σ'', List.ofFn b⟩) x) := by
  obtain ⟨j, hj0, hjne⟩ := exists_ne_succ_of_nonconst hσ
  set q := σ j with hq
  have hjt : σ (j + 1) = !q := by
    rcases hb : σ (j + 1) with _ | _ <;> rcases hq' : q with _ | _ <;> simp_all
  by_cases hjl : j = Fin.last (n + 1)
  · -- the last slot: `σ = (!q, μ, q)`
    subst hjl
    rw [Fin.last_add_one] at hjt
    set τ : Fin n → Bool := fun i => σ i.succ.castSucc with hτ
    refine ⟨Fin.cons true τ, Fin.cons false τ, fun x => ?_⟩
    have hσl : List.ofFn σ = (!q) :: List.ofFn τ ++ [q] := by
      rw [List.ofFn_succ', List.ofFn_succ, List.concat_eq_append]
      simp only [Fin.castSucc_zero, hjt, hτ, List.cons_append, ← hq]
    rw [Psum_loop_eq, Psum_loop_eq, Psum_loop_eq, hσl, List.ofFn_cons, List.ofFn_cons]
    rw [allSum_succ_last, ← allSum_linear]
    refine allSum_congr n fun l hl => ?_
    have := hlast q (List.ofFn τ) x l (by rw [List.length_ofFn, hl])
    simpa only [List.cons_append] using this
  · -- an interior slot `j = p + 1 ≤ n`
    obtain ⟨p, hp⟩ : ∃ p, j.val = p + 1 := ⟨j.val - 1, by
      have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      omega⟩
    have hjn : j.val ≤ n := by
      have := j.isLt
      have : j.val ≠ n + 1 := fun h => hjl (Fin.ext (by simp [h]))
      omega
    have hj1 : (j + 1).val = p + 2 := by
      rw [Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr hjl), hp]
    set l := List.ofFn σ with hl
    have hll : l.length = n + 2 := List.length_ofFn
    set σ₁ := l.take (p + 1) with hσ₁
    set σ₂ := l.drop (p + 3) with hσ₂
    have h₁ : σ₁.length = p + 1 := by simp [hσ₁, hll]; omega
    have h₂ : σ₂.length = n - 1 - p := by simp [hσ₂, hll]; omega
    have hsplit : l = σ₁ ++ q :: (!q) :: σ₂ := by
      conv_lhs => rw [← List.take_append_drop (p + 1) l]
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
      have e1 : l[p + 1]'(by omega) = q := by
        simp only [hl, List.getElem_ofFn]
        rw [hq]; congr 1; exact Fin.ext hp.symm
      have e2 : l[p + 1 + 1]'(by omega) = !q := by
        simp only [hl, List.getElem_ofFn]
        rw [← hjt]; congr 1; exact Fin.ext hj1.symm
      rw [e1, e2]
    have hlen' : (σ₁ ++ true :: σ₂).length = n + 1 := by simp [h₁, h₂]; omega
    have hlen'' : (σ₁ ++ false :: σ₂).length = n + 1 := by simp [h₁, h₂]; omega
    refine ⟨fun i => (σ₁ ++ true :: σ₂).getD i false, fun i => (σ₁ ++ false :: σ₂).getD i false,
      fun x => ?_⟩
    rw [Psum_loop_eq, Psum_loop_eq, Psum_loop_eq, ofFn_getD_eq _ hlen', ofFn_getD_eq _ hlen'',
      ← hl, hsplit]
    exact ward_list_mid_of hmid (p := p) (q := n - 1 - p) (by omega) (by omega) q σ₁ σ₂ h₁ h₂ x

end WardM

section LKTensor

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The tensor `(L - K)_{u,σ,·}(M)` of a fixed matrix `M` at the time `u`. -/
noncomputable def lkTM (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (B.Idx N) (B.Idx N) ℂ)
    {m : ℕ} (σ : Fin m → Bool) : LoopArg (B.L N) m → ℂ :=
  fun v => LvalN B E N u M σ v - KvN B E N u σ v

/-- `max_{σ,a} |L_{u,σ,a}(M) - K_{u,σ,a}|` over loops of length `m`, for a fixed matrix `M`. -/
noncomputable def lkMaxB (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) (m : ℕ) : ℝ :=
  ⨆ w : LoopData (B.L N) m, ‖gloop (B.L N) (B.W N) M (zt E u) w.idx - B.Kval E N u w.idx‖

/-- **(5.76) at a fixed matrix**:
`Ξ^{(L-K)}_{u,m}(M) = max_{σ,a} |(L - K)_{u,σ,a}(M)| (W ℓ_u η_u)^m`
(the matrix form of `RBM.Sample.xiLK`, for a general `Band`; at `B = band d` it is the same
formula as `RBM.Gauss.Grid.xiLKM d`). -/
noncomputable def xiLKB (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) (m : ℕ) : ℝ :=
  lkMaxB B E N u M m * B.scale E N u ^ m

theorem lkMaxB_nonneg (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (B.Idx N) (B.Idx N) ℂ)
    (m : ℕ) : 0 ≤ lkMaxB B E N u M m :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem norm_lkTM_le (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (B.Idx N) (B.Idx N) ℂ)
    {m : ℕ} (σ : Fin m → Bool) (b : LoopArg (B.L N) m) :
    ‖lkTM B E N u M σ b‖ ≤ lkMaxB B E N u M m :=
  le_ciSup (f := fun w : LoopData (B.L N) m =>
      ‖gloop (B.L N) (B.W N) M (zt E u) w.idx - B.Kval E N u w.idx‖)
    (Set.finite_range _).bddAbove (σ, b)

theorem lkMaxB_eq_xiLKB (B : Band Ω) {E : ℝ} (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (M : Matrix (B.Idx N) (B.Idx N) ℂ) (m : ℕ) :
    lkMaxB B E N u M m = xiLKB B E N u M m * (B.scale E N u)⁻¹ ^ m := by
  have h := (B.scale_pos' hE N hu0 hu1).ne'
  rw [xiLKB, mul_assoc, ← mul_pow, mul_inv_cancel₀ h, one_pow, mul_one]

end LKTensor

section T3

open Real

theorem one_le_W_rpow (d : Dims) (N : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : 1 ≤ (d.W N : ℝ) ^ τ :=
  Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ

end T3

section T6

open Real

end T6


section QStepAlg

variable {L : ℕ} [NeZero L]

/-- Crude counting bound for a slot sum: `|P ∘ A| ≤ L^n max|A|`. -/
theorem norm_Psum_le_card {n : ℕ} {A : LoopArg L (n + 1) → ℂ} {M : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ M) (x : ZMod L) : ‖Psum L A x‖ ≤ (L : ℝ) ^ n * M := by
  unfold Psum
  refine (norm_sum_le _ _).trans ?_
  calc ∑ r : LoopArg L n, ‖A (Fin.cons x r)‖ ≤ ∑ _r : LoopArg L n, M :=
        Finset.sum_le_sum fun r _ => hA _
    _ = (L : ℝ) ^ n * M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp [LoopArg, ZMod.card]

/-- `|ϑ_{t,a}| ≤ 1` for `0 ≤ t < 1` (each `|Θ_t(x,y)| ≤ (1-t)^{-1}`). -/
theorem norm_vartheta_le_one (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : LoopArg L (n + 1)) : ‖vartheta L (t : ℂ) a‖ ≤ 1 := by
  have hξ := norm_ofReal_lt_one ht0 ht1
  have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have h1t : 0 < 1 - t := by linarith
  rw [vartheta, norm_mul, norm_pow, norm_one_sub_ofReal ht1.le, norm_prod]
  calc (1 - t) ^ n * ∏ i : Fin n, ‖Theta L (t : ℂ) (a 0) (a i.succ)‖
      ≤ (1 - t) ^ n * ∏ _i : Fin n, (1 - t)⁻¹ := by
        gcongr with i
        have := norm_Theta_apply_le L hL hξ (a 0) (a i.succ)
        rwa [hnt] at this
    _ = 1 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow,
          mul_inv_cancel₀ h1t.ne', one_pow]

/-- `genS` is `ThetaOp` (both are `∑ᵢ ξᵢ Θ_{tξᵢ} S^{(B)}` acting slot-wise). -/
theorem genS_eq_ThetaOp {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ) (A : LoopArg L n → ℂ) :
    genS L ξ t A = ThetaOp L ξ t A := by
  funext a
  simp only [genS, genOp, genSM, ThetaOp, Matrix.smul_apply, smul_eq_mul]

theorem Uker_sub {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ) (A B : LoopArg L n → ℂ) (a : LoopArg L n) :
    Uker L ξ s t (fun b => A b - B b) a = Uker L ξ s t A a - Uker L ξ s t B a := by
  simp only [Uker_apply, mul_sub, Finset.sum_sub_distrib]

theorem Psum_lin {n : ℕ} (A B C : LoopArg L (n + 1) → ℂ) (κ : ℂ) (x : ZMod L) :
    Psum L (fun b => A b + κ * B b + C b) x = Psum L A x + κ * Psum L B x + Psum L C x := by
  simp only [Psum, Finset.sum_add_distrib, Finset.mul_sum]

/-- The explicit remainder of the one-step `Q`-identity (deterministic part). -/
noncomputable def qStepErr (L n : ℕ) (u Δ Mk Dm S : ℝ) : ℝ :=
  let Lp : ℝ := (L : ℝ) ^ (n + 1)
  let β : ℝ := (1 - (u + Δ))⁻¹
  let Ust : ℝ := ((n + 2 : ℕ) : ℝ) * Δ ^ 2 * β ^ 2
    + ((1 + Δ * β) ^ (n + 2) - 1 - ((n + 2 : ℕ) : ℝ) * Δ * β)
  let τB : ℝ := 5 * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * β ^ (n + 1 + 6) * Δ ^ 2
  let VdB : ℝ := 2 * ((n + 1 : ℕ) : ℝ) * (cTwo52 / ellHat L (u : ℂ)) ^ (n + 1) * (1 - u)⁻¹
  let Vdiff : ℝ := Δ * VdB + τB
  (1 + Lp) * S + Δ * (Lp * Dm) * Vdiff + 2 * (Lp * (Ust * Mk)) + Lp * Mk * τB
    + Δ * (Lp * (((n + 2 : ℕ) : ℝ) * (1 - u)⁻¹ * Mk)) * Vdiff

/-- **Deterministic core of the one-step `Q`-identity.** If `c = U_{u,u+Δ} X + Δ D + e` with
`|e| ≤ S` (the conclusion of `discrete_hierarchy_step_n`), then
`Q_{u+Δ} c - U_{u,u+Δ}(Q_u X) = Δ (Q_u D + [Q_u, Θ_{u,σ}] X - ϑ̇_u · P X) + R` with the explicit
`|R| ≤ qStepErr`. -/
theorem Qstep_algebra (hL : 3 ≤ L) {n : ℕ} (ξ : Fin (n + 2) → ℂ) (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ) (hut1 : u + Δ < 1)
    {X D c : LoopArg L (n + 2) → ℂ} {Mk Dm S : ℝ} (hMk0 : 0 ≤ Mk) (hDm0 : 0 ≤ Dm)
    (hX : ∀ b, ‖X b‖ ≤ Mk) (hD : ∀ b, ‖D b‖ ≤ Dm)
    (hc : ∀ b, ‖c b - Uker L ξ (u : ℂ) ((u + Δ : ℝ) : ℂ) X b - (Δ : ℂ) * D b‖ ≤ S)
    (a : LoopArg L (n + 2)) :
    ‖Qop L ((u + Δ : ℝ) : ℂ) c a - Uker L ξ (u : ℂ) ((u + Δ : ℝ) : ℂ) (Qop L (u : ℂ) X) a
        - (Δ : ℂ) * (Qop L (u : ℂ) D a + commS L ξ (u : ℂ) X a
          - varthetaDot L u a * Psum L X (a 0))‖
      ≤ qStepErr L n u Δ Mk Dm S := by
  have hu1 : u < 1 := by linarith
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hc a)
  set cu : ℂ := (u : ℂ) with hcu
  set cu' : ℂ := ((u + Δ : ℝ) : ℂ) with hcu'
  set Lp : ℝ := (L : ℝ) ^ (n + 1) with hLp
  have hLp0 : 0 ≤ Lp := by positivity
  set β : ℝ := (1 - (u + Δ))⁻¹ with hβ
  have hβ0 : 0 ≤ β := by rw [hβ]; exact inv_nonneg.2 (by linarith)
  set Ust : ℝ := ((n + 2 : ℕ) : ℝ) * Δ ^ 2 * β ^ 2
    + ((1 + Δ * β) ^ (n + 2) - 1 - ((n + 2 : ℕ) : ℝ) * Δ * β) with hUst
  set τB : ℝ := 5 * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * β ^ (n + 1 + 6) * Δ ^ 2 with hτB
  set VdB : ℝ := 2 * ((n + 1 : ℕ) : ℝ) * (cTwo52 / ellHat L (u : ℂ)) ^ (n + 1) * (1 - u)⁻¹
    with hVdB
  set Vdiff : ℝ := Δ * VdB + τB with hVdiff
  set Θb : ℝ := ((n + 2 : ℕ) : ℝ) * (1 - u)⁻¹ * Mk with hΘb
  -- the objects
  set Y : LoopArg L (n + 2) → ℂ := fun b => Psum L X (b 0) * vartheta L cu b with hY
  set e : LoopArg L (n + 2) → ℂ := fun b => c b - Uker L ξ cu cu' X b - (Δ : ℂ) * D b with he
  set ε : LoopArg L (n + 2) → ℂ :=
    fun b => Uker L ξ cu cu' X b - X b - (Δ : ℂ) * ThetaOp L ξ cu X b with hε
  set εY : LoopArg L (n + 2) → ℂ :=
    fun b => Uker L ξ cu cu' Y b - Y b - (Δ : ℂ) * ThetaOp L ξ cu Y b with hεY
  set τ : LoopArg L (n + 2) → ℂ :=
    fun b => vartheta L cu' b - vartheta L cu b - (Δ : ℂ) * varthetaDot L u b with hτ
  -- exact identities
  have h3 : Psum L c (a 0) = Psum L (Uker L ξ cu cu' X) (a 0) + (Δ : ℂ) * Psum L D (a 0)
      + Psum L e (a 0) := by
    rw [← Psum_lin]
    congr 1
    funext b
    simp only [he]; ring
  have h4 : Psum L (Uker L ξ cu cu' X) (a 0) = Psum L X (a 0)
      + (Δ : ℂ) * Psum L (ThetaOp L ξ cu X) (a 0) + Psum L ε (a 0) := by
    rw [← Psum_lin]
    congr 1
    funext b
    simp only [hε]; ring
  have h5 : Uker L ξ cu cu' (Qop L cu X) a = Uker L ξ cu cu' X a - Uker L ξ cu cu' Y a :=
    Uker_sub ξ cu cu' X Y a
  have h8 : commS L ξ cu X a
      = ThetaOp L ξ cu Y a - Psum L (ThetaOp L ξ cu X) (a 0) * vartheta L cu a := by
    have h := congrFun (commOp_eq L (genSM L ξ cu) cu X) a
    simp only [Pi.sub_apply] at h
    rw [commS, h]
    have e1 : genOp L (genSM L ξ cu) (fun b => Psum L X (b 0) * vartheta L cu b)
        = ThetaOp L ξ cu Y := genS_eq_ThetaOp ξ cu _
    have e2 : genOp L (genSM L ξ cu) X = ThetaOp L ξ cu X := genS_eq_ThetaOp ξ cu X
    rw [e1, e2]
  have hkey : Qop L cu' c a - Uker L ξ cu cu' (Qop L cu X) a
        - (Δ : ℂ) * (Qop L cu D a + commS L ξ cu X a - varthetaDot L u a * Psum L X (a 0))
      = (e a - Psum L e (a 0) * vartheta L cu' a)
        + (-((Δ : ℂ) * Psum L D (a 0) * (vartheta L cu' a - vartheta L cu a)))
        + (εY a - Psum L X (a 0) * τ a
          - (Δ : ℂ) * Psum L (ThetaOp L ξ cu X) (a 0) * (vartheta L cu' a - vartheta L cu a)
          - Psum L ε (a 0) * vartheta L cu' a) := by
    rw [h5, h8]
    simp only [Qop]
    rw [h3, h4]
    simp only [he, hε, hεY, hτ, hY]
    ring
  rw [hkey]
  -- bounds
  have hϑ : ∀ b, ‖vartheta L cu b‖ ≤ 1 := fun b => norm_vartheta_le_one hL (n := n + 1) hu0 hu1 b
  have hϑ' : ∀ b, ‖vartheta L cu' b‖ ≤ 1 := fun b =>
    norm_vartheta_le_one hL (n := n + 1) (by linarith) hut1 b
  have hPX : ∀ x, ‖Psum L X x‖ ≤ Lp * Mk := fun x => norm_Psum_le_card hX x
  have hYb : ∀ b, ‖Y b‖ ≤ Lp * Mk := by
    intro b
    simp only [hY]
    rw [norm_mul]
    calc ‖Psum L X (b 0)‖ * ‖vartheta L cu b‖ ≤ (Lp * Mk) * 1 :=
          mul_le_mul (hPX _) (hϑ b) (norm_nonneg _) (by positivity)
      _ = Lp * Mk := mul_one _
  have hPD : ‖Psum L D (a 0)‖ ≤ Lp * Dm := norm_Psum_le_card hD _
  have hPe : ‖Psum L e (a 0)‖ ≤ Lp * S := norm_Psum_le_card hc _
  have hεb : ∀ b, ‖ε b‖ ≤ Ust * Mk := fun b =>
    Uker_step_n hL ξ hξ hu0 hΔ0 hut1 hMk0 hX b
  have hPε : ‖Psum L ε (a 0)‖ ≤ Lp * (Ust * Mk) := norm_Psum_le_card hεb _
  have hεYb : ‖εY a‖ ≤ Ust * (Lp * Mk) :=
    Uker_step_n hL ξ hξ hu0 hΔ0 hut1 (by positivity) hYb a
  have hΘX : ∀ b, ‖ThetaOp L ξ cu X b‖ ≤ Θb := by
    intro b
    rw [← genS_eq_ThetaOp]
    have := norm_genOp_le L (genSM L ξ cu) hMk0 hX
      (fun i x => sum_norm_genSM_row_le_real L hL hu0 hu1 (hξ i) x) b
    have e : genS L ξ cu X b = genOp L (genSM L ξ cu) X b := rfl
    rw [e]
    simpa [hΘb, mul_assoc] using this
  have hPΘX : ‖Psum L (ThetaOp L ξ cu X) (a 0)‖ ≤ Lp * Θb := norm_Psum_le_card hΘX _
  have hτb : ‖τ a‖ ≤ τB := by
    have h := norm_vartheta_taylor_sub_le L hL (n := n + 1) hu0 (by linarith : u ≤ u + Δ) hut1 a
    have hsub : ((u + Δ - u : ℝ) : ℂ) = (Δ : ℂ) := by push_cast; ring
    rw [hsub, show u + Δ - u = Δ by ring] at h
    simp only [hτ, hτB, hβ]
    refine h.trans (le_of_eq ?_)
    push_cast
    ring
  have hVd : ‖varthetaDot L u a‖ ≤ VdB := norm_varthetaDot_le L hL hu0 hu1 a
  have hdiff : ‖vartheta L cu' a - vartheta L cu a‖ ≤ Vdiff := by
    have e1 : vartheta L cu' a - vartheta L cu a = (Δ : ℂ) * varthetaDot L u a + τ a := by
      simp only [hτ]; ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ0]
    exact add_le_add (mul_le_mul_of_nonneg_left hVd hΔ0) hτb
  have hVdiff0 : 0 ≤ Vdiff := (norm_nonneg _).trans hdiff
  have hnΔ : ‖(Δ : ℂ)‖ = Δ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ0]
  -- the three groups
  have hT3 : ‖e a - Psum L e (a 0) * vartheta L cu' a‖ ≤ (1 + Lp) * S := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul hPe (hϑ' a) (norm_nonneg _) (by positivity)
    have hea : ‖e a‖ ≤ S := hc a
    nlinarith
  have hT2 : ‖-((Δ : ℂ) * Psum L D (a 0) * (vartheta L cu' a - vartheta L cu a))‖
      ≤ Δ * (Lp * Dm) * Vdiff := by
    rw [norm_neg, norm_mul, norm_mul, hnΔ]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPD hΔ0) hdiff (norm_nonneg _) (by positivity)
  have hT1 : ‖εY a - Psum L X (a 0) * τ a
        - (Δ : ℂ) * Psum L (ThetaOp L ξ cu X) (a 0) * (vartheta L cu' a - vartheta L cu a)
        - Psum L ε (a 0) * vartheta L cu' a‖
      ≤ Ust * (Lp * Mk) + Lp * Mk * τB + Δ * (Lp * Θb) * Vdiff + Lp * (Ust * Mk) := by
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add hεYb ?_)) ?_)) ?_)
    · rw [norm_mul]
      exact mul_le_mul (hPX _) hτb (norm_nonneg _) (by positivity)
    · rw [norm_mul, norm_mul, hnΔ]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hPΘX hΔ0) hdiff (norm_nonneg _)
        (by positivity)
    · rw [norm_mul]
      calc ‖Psum L ε (a 0)‖ * ‖vartheta L cu' a‖ ≤ Lp * (Ust * Mk) * 1 :=
            mul_le_mul hPε (hϑ' a) (norm_nonneg _) ((norm_nonneg _).trans hPε)
        _ = Lp * (Ust * Mk) := mul_one _
  refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add hT3 hT2))
    hT1).trans (le_of_eq ?_))
  simp only [qStepErr]
  ring

end QStepAlg

section GridStepQ

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The deterministic sup bound on `(L - K)_{u_k}` used by `discrete_hierarchy_step_n`
(`|L| ≤ |Im z|^{-m} W^{-(m-1)}`
plus the `K` envelope `Bk`), at loop length `n + 2`. -/
noncomputable def lkEnv (B : Band Ω) (E : ℝ) (N n : ℕ) (u Bk : ℝ) : ℝ :=
  |(zt E u).im|⁻¹ ^ (n + 2) * (B.W N : ℝ)⁻¹ ^ (n + 1) + Bk

/-- The explicit deterministic envelope of the drift `D_u = driftF` at loop length `n + 2`
(`RBM.Gauss.norm_driftF_le_crude` with `M_G = η_u^{-(n+3)}`, `M_K = Bk`). -/
noncomputable def driftEnv (B : Band Ω) (E : ℝ) (N n : ℕ) (u Bk : ℝ) : ℝ :=
  let MG : ℝ := (etaT E u)⁻¹ ^ (n + 3)
  (B.W N : ℝ) * ((n : ℝ) + 2) * ((B.L N : ℝ) * ((MG + 1) * MG))
    + ((n : ℝ) + 2) * (2 * ((B.W N : ℝ) * ((n : ℝ) + 2) ^ 2
        * ((B.L N : ℝ) * (Bk * (MG + Bk)))))
    + (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * ((B.L N : ℝ) * ((MG + Bk) * (MG + Bk)))

/-- **`grid_step_Q`: the one-step identity for `A_k = Q_{u_k} ∘ (L - K)_{u_k,σ}(H_k)`.**
Almost surely, for every loop argument `a`,
`E[A_{k+1} | F_k] - U_{k,k+1} A_k = Δ (Q_{u_k} D_k + [Q_{u_k}, Θ_{u_k,σ}] (L-K)_k
  - ϑ̇_{u_k} · P (L-K)_k) + R^Q_k`
with the explicit `|R^Q_k| ≤ qStepErr(…, stepErrN)`: `(1 + L^{n+1})` times `stepErrN`
(`O(Δ² + Δ^{3/2})`) plus `O(Δ²)` terms with explicit polynomial coefficients. The hypotheses are
exactly those of `discrete_hierarchy_step_n` at loop length `n + 2`, any charge `σ`. -/
theorem grid_step_Q (B : Band Ω) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ)
    (hEb : |E| < 2) (hst : s N < t N) (hk : k < K N) (hu0 : 0 ≤ time s t K N k)
    (hu1 : time s t K N (k + 1) < 1) {n : ℕ} (σ : Fin (n + 2) → Bool)
    {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (time s t K N (k + 1)), ∀ J : LoopIdx (ZMod (B.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ n + 2 → ‖B.Kval E N w J‖ ≤ Bk)
    (hξ : ∀ a : LoopArg (B.L N) (n + 2), ‖(time s t K N k : ℂ) * xiLoop (mSigma E)
        (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) (n + 2 - 1)‖ < 1) :
    ∀ᵐ ω ∂ (Pg B.toDims), ∀ a : LoopArg (B.L N) (n + 2),
      ‖(Pg B.toDims)[fun ω' => Qop (B.L N) (time s t K N (k + 1) : ℂ)
              (lkTM B E N (time s t K N (k + 1)) (H B.toDims s t K N (k + 1) ω') σ) a
            | filt B.toDims k] ω
          - Uker (B.L N) (xiOf (mSigma E) σ) (time s t K N k : ℂ) (time s t K N (k + 1) : ℂ)
              (Qop (B.L N) (time s t K N k : ℂ)
                (lkTM B E N (time s t K N k) (H B.toDims s t K N k ω) σ)) a
          - (step s t K N : ℂ)
              * (Qop (B.L N) (time s t K N k : ℂ)
                    (DriftDef.driftF B E N (time s t K N k) (H B.toDims s t K N k ω) σ) a
                + commS (B.L N) (xiOf (mSigma E) σ) (time s t K N k : ℂ)
                    (lkTM B E N (time s t K N k) (H B.toDims s t K N k ω) σ) a
                - varthetaDot (B.L N) (time s t K N k) a
                    * Psum (B.L N) (lkTM B E N (time s t K N k) (H B.toDims s t K N k ω) σ)
                        (a 0))‖
        ≤ qStepErr (B.L N) n (time s t K N k) (step s t K N)
            (lkEnv B E N n (time s t K N k) Bk) (driftEnv B E N n (time s t K N k) Bk)
            (stepErrN B E N (n + 2) (time s t K N k) (time s t K N (k + 1)) (step s t K N) Bk) := by
  set d : Dims := B.toDims with hd
  set uk : ℝ := time s t K N k with hukdef
  set uk1 : ℝ := time s t K N (k + 1) with huk1def
  set Δ : ℝ := step s t K N with hΔdef
  have hKpos : 0 < K N := lt_of_le_of_lt (Nat.zero_le k) hk
  have hΔpos : 0 < Δ := by
    rw [hΔdef]; unfold step; exact div_pos (by linarith) (by exact_mod_cast hKpos)
  have huk1eq : uk1 = uk + Δ := by
    rw [huk1def, hukdef, hΔdef]; unfold time; push_cast; ring
  have hukuk1 : uk ≤ uk1 := by rw [huk1eq]; linarith
  have huk_lt : uk < 1 := by linarith
  have hzk : (zt E uk).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb huk_lt
  have hzk1 : (zt E uk1).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb hu1
  have hηk : 0 < |(zt E uk).im| := abs_pos.mpr hzk
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hukIcc : uk ∈ Set.Icc (0 : ℝ) uk1 := ⟨hu0, hukuk1⟩
  -- `discrete_hierarchy_step_n`
  have hT := discrete_hierarchy_step_n B s t K N k E hEb hst hk hu0 hu1 (n := n + 2) (by omega)
    σ hBk0 hBk hξ
  -- linearity of the conditional expectation through `Q_{u_{k+1}}`
  have hlin : ∀ a : LoopArg (B.L N) (n + 2), ∀ᵐ ω ∂ (Pg d),
      (Pg d)[fun ω' => Qop (B.L N) (uk1 : ℂ) (lkTM B E N uk1 (H d s t K N (k + 1) ω') σ) a
          | filt d k] ω
        = (Pg d)[fun ω' => lkTM B E N uk1 (H d s t K N (k + 1) ω') σ a | filt d k] ω
          - (∑ r : LoopArg (B.L N) (n + 1),
              (Pg d)[fun ω' => lkTM B E N uk1 (H d s t K N (k + 1) ω') σ (Fin.cons (a 0) r)
                | filt d k] ω) * vartheta (B.L N) (uk1 : ℂ) a := by
    intro a
    have hInt : ∀ b : LoopArg (B.L N) (n + 2),
        Integrable (fun ω' => lkTM B E N uk1 (H d s t K N (k + 1) ω') σ b) (Pg d) := by
      intro b
      set I : LoopIdx (ZMod (d.L N)) := ⟨List.ofFn σ, List.ofFn b⟩ with hIdef
      have hwf : I.WF := by show (List.ofFn σ).length = (List.ofFn b).length; simp
      have hn1 : 1 ≤ I.a.length := by
        show 1 ≤ (List.ofFn b).length; rw [List.length_ofFn]; omega
      have hTF : TestFun d N (loopObs d N (zt E uk1) I) :=
        testFun_loopObs_of_im_le hzk1 (abs_pos.mpr hzk1) le_rfl hwf hn1
      obtain ⟨C₀, hC₀⟩ := hTF.bdd₀
      have hHk1meas : Measurable (fun ω : Ωg d => H d s t K N (k + 1) ω) :=
        (H_measurable_filt d s t K N (k + 1)).mono ((filt d).le (k + 1)) le_rfl
      have hI1 : Integrable
          (fun ω : Ωg d => loopObs d N (zt E uk1) I (H d s t K N (k + 1) ω)) (Pg d) :=
        (memLp_top_of_bound
          (hTF.contDiff.continuous.measurable.comp hHk1meas).aestronglyMeasurable C₀
          (Eventually.of_forall fun ω => hC₀ _)).integrable le_top
      have hfun : (fun ω' => lkTM B E N uk1 (H d s t K N (k + 1) ω') σ b)
          = (fun ω' : Ωg d => loopObs d N (zt E uk1) I (H d s t K N (k + 1) ω'))
            - (fun _ => KvN B E N uk1 σ b) := by
        funext ω'
        rw [Pi.sub_apply, loopObs_of_isHermitian (H_isHermitian d s t K N (k + 1) ω')]
        rfl
      rw [hfun]
      exact hI1.sub (integrable_const _)
    have hfun : (fun ω' => Qop (B.L N) (uk1 : ℂ) (lkTM B E N uk1 (H d s t K N (k + 1) ω') σ) a)
        = (fun ω' => lkTM B E N uk1 (H d s t K N (k + 1) ω') σ a)
          - vartheta (B.L N) (uk1 : ℂ) a • ∑ r ∈ (Finset.univ : Finset (LoopArg (B.L N) (n + 1))),
              (fun ω' => lkTM B E N uk1 (H d s t K N (k + 1) ω') σ (Fin.cons (a 0) r)) := by
      funext ω'
      simp only [Qop, Psum, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      ring
    have hsumInt : Integrable (∑ r ∈ (Finset.univ : Finset (LoopArg (B.L N) (n + 1))),
        (fun ω' => lkTM B E N uk1 (H d s t K N (k + 1) ω') σ (Fin.cons (a 0) r))) (Pg d) :=
      integrable_finsetSum' _ fun r _ => hInt _
    rw [hfun]
    filter_upwards [condExp_sub (hInt a) (hsumInt.smul (vartheta (B.L N) (uk1 : ℂ) a)) (filt d k),
      condExp_smul (vartheta (B.L N) (uk1 : ℂ) a) (∑ r ∈ (Finset.univ : Finset _),
        (fun ω' => lkTM B E N uk1 (H d s t K N (k + 1) ω') σ (Fin.cons (a 0) r))) (filt d k),
      condExp_finsetSum (fun r _ => hInt (Fin.cons (a 0) r)) (filt d k)] with ω h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Finset.sum_apply, smul_eq_mul, mul_comm]
  have hlin' := ae_all_iff.mpr hlin
  filter_upwards [hT, hlin'] with ω hTω hlinω a
  set M : Matrix (d.Idx N) (d.Idx N) ℂ := H d s t K N k ω with hMdef
  have hM : M.IsHermitian := H_isHermitian d s t K N k ω
  set c : LoopArg (B.L N) (n + 2) → ℂ := fun b =>
    (Pg d)[fun ω' => lkTM B E N uk1 (H d s t K N (k + 1) ω') σ b | filt d k] ω with hcdef
  have hQc : (Pg d)[fun ω' => Qop (B.L N) (uk1 : ℂ) (lkTM B E N uk1 (H d s t K N (k + 1) ω') σ) a
      | filt d k] ω = Qop (B.L N) (uk1 : ℂ) c a := by
    rw [hlinω a]
    rfl
  rw [hQc]
  have hut1 : uk + Δ < 1 := by rw [← huk1eq]; exact hu1
  have hξ1 : ∀ i : Fin (n + 2), ‖xiOf (mSigma E) σ i‖ ≤ 1 := by
    intro i
    show ‖mSigma E (σ i) * mSigma E (σ (i + 1))‖ ≤ 1
    rw [norm_mul, norm_mSigma hEb.le, norm_mSigma hEb.le, one_mul]
  -- the bounds on `X = (L-K)_{u_k}` and `D = driftF`
  have hX : ∀ b, ‖lkTM B E N uk M σ b‖ ≤ lkEnv B E N n uk Bk := by
    intro b
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · have h := norm_gloop_le_of_le_abs_im (L := B.L N) (W := B.W N) hM hηk le_rfl
        (⟨List.ofFn σ, List.ofFn b⟩ : LoopIdx (ZMod (B.L N)))
        (by show (List.ofFn σ).length = (List.ofFn b).length; simp)
        (by show 1 ≤ (List.ofFn b).length; rw [List.length_ofFn]; omega)
      simpa [LvalN, List.length_ofFn] using h
    · exact hBk uk hukIcc _ (by show (List.ofFn σ).length = (List.ofFn b).length; simp)
        (by show 2 ≤ (List.ofFn b).length; rw [List.length_ofFn]; omega)
        (by show (List.ofFn b).length ≤ n + 2; rw [List.length_ofFn])
  have hMk0 : 0 ≤ lkEnv B E N n uk Bk := (norm_nonneg _).trans (hX a)
  have hD : ∀ b, ‖DriftDef.driftF B E N uk M σ b‖ ≤ driftEnv B E N n uk Bk := by
    intro b
    have hηu : 0 < etaT E uk := etaT_pos_of_lt_one hEb huk_lt
    refine norm_driftF_le_crude B E N hEb uk M σ b (by positivity) hBk0 ?_ ?_
    · intro J hJ hJ1 hJle
      exact norm_gloop_le_win hM hEb hu0 le_rfl huk_lt (n + 3) J hJ hJ1 hJle
    · intro J hJ hJ2 hJle
      exact hBk uk hukIcc J hJ hJ2 hJle
  have hDm0 : 0 ≤ driftEnv B E N n uk Bk := (norm_nonneg _).trans (hD a)
  have hc : ∀ b, ‖c b - Uker (B.L N) (xiOf (mSigma E) σ) (uk : ℂ) ((uk + Δ : ℝ) : ℂ)
      (lkTM B E N uk M σ) b - (Δ : ℂ) * DriftDef.driftF B E N uk M σ b‖
      ≤ stepErrN B E N (n + 2) uk uk1 Δ Bk := by
    intro b
    have h := hTω b
    rw [← huk1eq]
    exact h
  have hmain := Qstep_algebra hL3 (xiOf (mSigma E) σ) hξ1 hu0 hΔpos.le hut1 hMk0 hDm0 hX hD hc a
  rw [← huk1eq] at hmain
  exact hmain

end GridStepQ

section Witnesses

open Real

end Witnesses
end RBM.Gauss.Grid
