/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.EETensorBound
import RBM1D.Gauss.GridAssembly

/-!
# The `n = 2`, `σ = (+,+)` conditional-variance bound

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (5.22)–(5.25) and (5.81): the paired/Hermitian `vC` form of the conditional-variance
bound (**not** the real `v`/`|w|²` form), for the `n = 2` bootstrap at the charge pattern
`σ_pp := (+,+)` (Lean `sigmaPP`).

## Route

Every statement below is a direct `n = 2`, `σ = σ_pp` instantiation of the general-`n` results
of `RBM1D/Gauss/EETensorBound.lean`.

* `vC_gradMat_pp_le` — `eeHerm_le` at `n = 2` (`decaySet`), converted to the
  `A_v^{-4} η_v^{-1}` form of (5.81)/(5.77) via `W_mul_ell_div_scale_le`.
* `condVar_pp_le` — `vC_sum_le` (the **paired** form) followed by `vC_gradMat_pp_le`,
  uniformly in `b`. **Not** the real `v`/`|w|²` form.
* `condVar_pp_grid` — the grid form (`AbC`/`ukerMatC`/`gridΦG`) of the conditional-variance
  input of the grid assembly, with the row-sum bound `Σ_b‖w_b‖ ≤ C_U` taken as an explicit
  **hypothesis**. The sharper, hypothesis-free `qv_contraction_le_nonAlt` route is not used
  here.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory Filter Matrix RBM
open scoped ComplexConjugate

variable {d : Dims} {N : ℕ}

/-! ## 0. The charge pattern `σ_pp = (+,+)` -/

/-- **`sigmaPP`**: the charge pattern `σ = (+,+)` of PP-3 (both edges short, `ξ = m²`). -/
def sigmaPP : Fin 2 → Bool := ![true, true]

/-! ## (T2) `vC_gradMat_pp_le`: (5.81) at `n = 2` -/

/-- `Ξ^{(L)}_m(M) ≥ 0` whenever the scale `A ≥ 0` (`loopMax ≥ 0` times `A^{m-1} ≥ 0`). -/
private theorem loopXi_nonneg' {M : Matrix (d.Idx N) (d.Idx N) ℂ} {z : ℂ} {A : ℝ} (hA : 0 ≤ A)
    (m : ℕ) : 0 ≤ loopXi (d.L N) (d.W N) M z A m := by
  unfold loopXi
  exact mul_nonneg (loopMax_nonneg _) (pow_nonneg hA _)

/-- **`eeHermBdPP`**: the `(5.81)`-at-`n=2` bound, `C·W^τ·φ₆·A_v^{-4}·η_v^{-1} + tail`
(`C = 24e`, `tail = 4WL·W^{-D}`), `A_v := (band d).scale E N v = Wℓ_vη_v`, `η_v := etaT E v`. -/
noncomputable def eeHermBdPP (d : Dims) (N : ℕ) (E v τ D φ6 : ℝ) : ℝ :=
  24 * Real.exp 1 * φ6 * (d.W N : ℝ) ^ τ * ((band d).scale E N v)⁻¹ ^ 4 * (etaT E v)⁻¹
    + 4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D)

/-- `eeHermBdPP` is nonnegative under the standing hypotheses. -/
theorem eeHermBdPP_nonneg {E v τ D φ6 : ℝ} (hE : |E| < 2) (hv1 : v < 1)
    (hA1 : 1 ≤ (band d).scale E N v) (hφ6 : 0 ≤ φ6) :
    0 ≤ eeHermBdPP d N E v τ D φ6 := by
  have hη : 0 < etaT E v := etaT_pos_of_lt_one hE hv1
  have hAnn : (0 : ℝ) ≤ (band d).scale E N v := by linarith
  have hW : (0 : ℝ) ≤ (d.W N : ℝ) := Nat.cast_nonneg _
  have hWτ : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ := Real.rpow_nonneg hW τ
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW (-D)
  have hAinv4 : (0 : ℝ) ≤ ((band d).scale E N v)⁻¹ ^ 4 := by positivity
  have hη' : (0 : ℝ) ≤ (etaT E v)⁻¹ := inv_nonneg.2 hη.le
  have hL : (0 : ℝ) ≤ (d.L N : ℝ) := Nat.cast_nonneg _
  have h24e : (0 : ℝ) ≤ (24 : ℝ) * Real.exp 1 := by positivity
  have h4W : (0 : ℝ) ≤ (4 : ℝ) * (d.W N : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ 24 * Real.exp 1 * φ6 * (d.W N : ℝ) ^ τ * ((band d).scale E N v)⁻¹ ^ 4
      * (etaT E v)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h24e hφ6) hWτ) hAinv4) hη'
  have h2 : (0 : ℝ) ≤ 4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D) :=
    mul_nonneg (mul_nonneg h4W hL) hWD
  unfold eeHermBdPP
  linarith

/-- **`vC_gradMat_pp_le`** — (5.81) at `n = 2`: on the `(v,τ,D)`-decay of the length-`6`
`G`-loops (`decaySet`) and `Ξ^{(L)}_{v,6}(M) ≤ φ₆`, the conditional variance of a single
`σ_pp` direction is bounded, **uniformly in `b`**. -/
theorem vC_gradMat_pp_le {E v τ D φ6 : ℝ} (hE : |E| < 2) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hA1 : 1 ≤ (band d).scale E N v) (hWτ1 : 1 ≤ (d.W N : ℝ) ^ τ)
    (Kc : LoopArg (d.L N) 2 → ℂ) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hΞ6 : loopXi (d.L N) (d.W N) M (zt E v) ((band d).scale E N v) 6 ≤ φ6)
    (hdec : M ∈ decaySet d E N 6 v τ D) (b : LoopArg (d.L N) 2) :
    vC N (gradMat (fun M' => loopObs d N (zt E v) (toIdx sigmaPP b) M' - Kc b) M)
      ≤ eeHermBdPP d N E v τ D φ6 := by
  set A := (band d).scale E N v with hAdef
  have hAnn : (0 : ℝ) ≤ A := by linarith
  have hbound := eeHerm_le hE hv0 hv1 (n := 2) (by norm_num) sigmaPP Kc hM hA1 hΞ6 hdec b b
  rw [eeHerm_self, Complex.norm_real, Real.norm_of_nonneg (vC_nonneg N _)] at hbound
  push_cast at hbound
  have hpref := W_mul_ell_div_scale_le (d := d) (N := N) hE hv0 hv1 hWτ1
  have hΦnn : 0 ≤ φ6 := (loopXi_nonneg' hAnn 6).trans hΞ6
  have hA4nn : (0 : ℝ) ≤ A⁻¹ ^ 4 := by positivity
  have hcoefnn : (0 : ℝ) ≤ 8 * Real.exp 1 * φ6 := by positivity
  have hstep : 8 * Real.exp 1 * φ6
        * ((d.W N : ℝ) * (ellHat (d.L N) (v : ℂ) * (d.W N : ℝ) ^ τ + 1) / A) * A⁻¹ ^ 4
      ≤ 8 * Real.exp 1 * φ6 * (3 * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹) * A⁻¹ ^ 4 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpref hcoefnn) hA4nn
  calc vC N (gradMat (fun M' => loopObs d N (zt E v) (toIdx sigmaPP b) M' - Kc b) M)
      ≤ 2 * (2 * Real.exp 1 * 2 * φ6
          * ((d.W N : ℝ) * (ellHat (d.L N) (v : ℂ) * (d.W N : ℝ) ^ τ + 1) / A) * A⁻¹ ^ 4
        + 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D)) := hbound
    _ = 8 * Real.exp 1 * φ6
          * ((d.W N : ℝ) * (ellHat (d.L N) (v : ℂ) * (d.W N : ℝ) ^ τ + 1) / A) * A⁻¹ ^ 4
        + 4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D) := by ring
    _ ≤ 8 * Real.exp 1 * φ6 * (3 * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹) * A⁻¹ ^ 4
        + 4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D) := by linarith [hstep]
    _ = eeHermBdPP d N E v τ D φ6 := by unfold eeHermBdPP; ring

/-! ## (T3) `condVar_pp_le`: the paired form, arbitrary complex weights -/

/-- **`condVar_pp_le`** (the paired form) — for **arbitrary complex** weights
`w : LoopArg (d.L N) 2 → ℂ`, the conditional variance of a linear combination of `σ_pp` directions
is bounded by the Minkowski square of the row sum times the uniform-in-`b` bound of
`vC_gradMat_pp_le`. Route: `vC_sum_le` followed by `vC_gradMat_pp_le`, **not** the real
`v`/`|w|²` form. -/
theorem condVar_pp_le {E v τ D φ6 : ℝ} (hE : |E| < 2) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hA1 : 1 ≤ (band d).scale E N v) (hWτ1 : 1 ≤ (d.W N : ℝ) ^ τ)
    (Kc : LoopArg (d.L N) 2 → ℂ) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hΞ6 : loopXi (d.L N) (d.W N) M (zt E v) ((band d).scale E N v) 6 ≤ φ6)
    (hdec : M ∈ decaySet d E N 6 v τ D) (w : LoopArg (d.L N) 2 → ℂ) :
    vC N (∑ b : LoopArg (d.L N) 2, w b •
        gradMat (fun M' => loopObs d N (zt E v) (toIdx sigmaPP b) M' - Kc b) M)
      ≤ (∑ b : LoopArg (d.L N) 2, ‖w b‖) ^ 2 * eeHermBdPP d N E v τ D φ6 := by
  refine (vC_sum_le
      (fun b => gradMat (fun M' => loopObs d N (zt E v) (toIdx sigmaPP b) M' - Kc b) M) w).trans
    (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  exact ciSup_le fun b => vC_gradMat_pp_le hE hv0 hv1 hA1 hWτ1 Kc hM hΞ6 hdec b

/-! ## (T4) `condVar_pp_grid`: the grid form -/

/-- **`cPP`**: the grid form's bound, `c k a j := Δ·C_U²·eeHermBdPP`. -/
noncomputable def cPP (d : Dims) (N : ℕ) (E τ D φ6 CU Δ v : ℝ) : ℝ :=
  Δ * (CU ^ 2 * eeHermBdPP d N E v τ D φ6)

/-- **`condVar_pp_grid`** — the grid form of the conditional-variance input of the grid assembly,
`w_b = U_{j+1,k,σ_pp}(a,b)`. **The row-sum bound `Σ_b‖w_b‖ ≤ C_U` is taken as a
hypothesis** (`hCU`): `C_U` here is a free parameter, not derived.  (The sharper,
hypothesis-free `qv_contraction_le_nonAlt`/`step_mul_vC_AbC_le_nonAlt` is not used.) -/
theorem condVar_pp_grid (E : ℝ) (hE : |E| < 2) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (j k : ℕ)
    {τ D φ6 CU : ℝ} (hv0 : 0 ≤ time s t Kf N (j + 1)) (hv1 : time s t Kf N (j + 1) < 1)
    (hA1 : 1 ≤ (band d).scale E N (time s t Kf N (j + 1))) (hWτ1 : 1 ≤ (d.W N : ℝ) ^ τ)
    (hstep : 0 ≤ step s t Kf N) (ω : Ωg d)
    (hΞ6 : loopXi (d.L N) (d.W N) (H d s t Kf N j ω) (zt E (time s t Kf N (j + 1)))
        ((band d).scale E N (time s t Kf N (j + 1))) 6 ≤ φ6)
    (hdec : H d s t Kf N j ω ∈ decaySet d E N 6 (time s t Kf N (j + 1)) τ D)
    (a : LoopArg (d.L N) 2)
    (hCU : ∑ b : LoopArg (d.L N) 2,
        ‖ukerMatC (xiOf (mSigma E) sigmaPP) (time s t Kf N (j + 1)) (time s t Kf N k) a b‖
      ≤ CU) :
    step s t Kf N * vC N (AbC d s t Kf N j 2 (gridΦG d E s t Kf N sigmaPP (j + 1))
        (ukerMatC (xiOf (mSigma E) sigmaPP) (time s t Kf N (j + 1)) (time s t Kf N k)) a ω)
      ≤ cPP d N E τ D φ6 CU (step s t Kf N) (time s t Kf N (j + 1)) := by
  have hAnn' : (0 : ℝ) ≤ (band d).scale E N (time s t Kf N (j + 1)) := by linarith
  have hφ6 : (0 : ℝ) ≤ φ6 := (loopXi_nonneg' hAnn' 6).trans hΞ6
  have heq : AbC d s t Kf N j 2 (gridΦG d E s t Kf N sigmaPP (j + 1))
      (ukerMatC (xiOf (mSigma E) sigmaPP) (time s t Kf N (j + 1)) (time s t Kf N k)) a ω
      = ∑ a' : LoopArg (d.L N) 2,
          ukerMatC (xiOf (mSigma E) sigmaPP) (time s t Kf N (j + 1)) (time s t Kf N k) a a'
            • gradMat (fun M' => loopObs d N (zt E (time s t Kf N (j + 1)))
                (toIdx sigmaPP a') M'
                - (band d).Kval E N (time s t Kf N (j + 1)) (toIdx sigmaPP a'))
              (H d s t Kf N j ω) := rfl
  rw [heq]
  unfold cPP
  refine mul_le_mul_of_nonneg_left ?_ hstep
  refine (condVar_pp_le hE hv0 hv1 hA1 hWτ1
      (fun a' => (band d).Kval E N (time s t Kf N (j + 1)) (toIdx sigmaPP a'))
      (H_isHermitian d s t Kf N j ω) hΞ6 hdec
      (fun a' => ukerMatC (xiOf (mSigma E) sigmaPP) (time s t Kf N (j + 1))
        (time s t Kf N k) a a')).trans ?_
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hCU 2)
    (eeHermBdPP_nonneg hE hv1 hA1 hφ6)

/-! ## Satisfiability -/

end RBM.Gauss.Grid

end
