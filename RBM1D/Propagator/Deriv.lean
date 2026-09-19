/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.Matrix

/-!
# The derivative of the propagator, equation (2.51)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, equation (2.51):
`∂_ξ Θ_ξ = Θ_ξ S^(B) Θ_ξ`.

The proof goes through the resolvent identity
`Θ_ζ - Θ_ξ = (ζ - ξ) Θ_ζ S^(B) Θ_ξ`
together with continuity of `ξ ↦ Θ_ξ`, rather than differentiating the Neumann
series term by term.

The statement is given entrywise.  This is both what Section 3 actually uses
(everything there is an entrywise sum over block indices) and what avoids the
instance diamond between the Pi topology on `Matrix` and the topology of the
`ℓ^∞` operator norm.

This identity drives Section 3: it is what makes the primitive equation (2.48)
quadratic, and it is the computation behind Figure 7.
-/

namespace RBM

open Matrix Filter Topology
open scoped Matrix.Norms.Operator

variable (L : ℕ) [NeZero L]

theorem continuousAt_Theta (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    ContinuousAt (fun ζ : ℂ => Theta L ζ) ξ := by
  obtain ⟨u, hu⟩ := isUnit_one_sub_smul_SB L hL hξ
  have hinv : ContinuousAt (Ring.inverse : Matrix (ZMod L) (ZMod L) ℂ → _) (1 - ξ • SB L) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hlin : ContinuousAt (fun ζ : ℂ => 1 - ζ • SB L) ξ :=
    continuousAt_const.sub (continuousAt_id.smul continuousAt_const)
  simp only [Theta]
  exact ContinuousAt.comp (g := Ring.inverse) (f := fun ζ : ℂ => 1 - ζ • SB L) hinv hlin

/-- The resolvent identity for the propagator. -/
theorem Theta_sub_Theta (hL : 3 ≤ L) {ξ ζ : ℂ} (hξ : ‖ξ‖ < 1) (hζ : ‖ζ‖ < 1) :
    Theta L ζ - Theta L ξ = (ζ - ξ) • (Theta L ζ * SB L * Theta L ξ) := by
  have hd : (1 - ξ • SB L) - (1 - ζ • SB L) = (ζ - ξ) • SB L := by
    rw [sub_sub_sub_cancel_left, ← sub_smul]
  calc Theta L ζ - Theta L ξ
      = Theta L ζ * ((1 - ξ • SB L) * Theta L ξ)
        - Theta L ζ * (1 - ζ • SB L) * Theta L ξ := by
        rw [mul_Theta L hL hξ, Theta_mul L hL hζ, mul_one, one_mul]
    _ = Theta L ζ * ((1 - ξ • SB L) - (1 - ζ • SB L)) * Theta L ξ := by noncomm_ring
    _ = Theta L ζ * ((ζ - ξ) • SB L) * Theta L ξ := by rw [hd]
    _ = (ζ - ξ) • (Theta L ζ * SB L * Theta L ξ) := by simp

omit [NeZero L] in
theorem continuous_matrix_entry (a b : ZMod L) :
    Continuous fun M : Matrix (ZMod L) (ZMod L) ℂ => M a b :=
  (continuous_apply b).comp (continuous_apply a)

/-- Equation (2.51), entrywise: `∂_ξ (Θ_ξ)_{ab} = (Θ_ξ S^(B) Θ_ξ)_{ab}`. -/
theorem hasDerivAt_Theta_apply (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : ZMod L) :
    HasDerivAt (fun ζ : ℂ => Theta L ζ a b) ((Theta L ξ * SB L * Theta L ξ) a b) ξ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hball : ∀ᶠ ζ : ℂ in 𝓝[≠] ξ, ‖ζ‖ < 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((isOpen_lt continuous_norm continuous_const).mem_nhds hξ)
  have hslope : ∀ᶠ ζ : ℂ in 𝓝[≠] ξ,
      (Theta L ζ * SB L * Theta L ξ) a b = slope (fun ζ : ℂ => Theta L ζ a b) ξ ζ := by
    filter_upwards [hball, self_mem_nhdsWithin] with ζ hζ hmem
    have hne : ζ - ξ ≠ 0 := sub_ne_zero_of_ne hmem
    have hdiff : Theta L ζ a b - Theta L ξ a b
        = (ζ - ξ) * (Theta L ζ * SB L * Theta L ξ) a b := by
      have h := congrFun (congrFun (Theta_sub_Theta L hL hξ hζ) a) b
      simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
    rw [slope_def_field, hdiff, mul_comm, mul_div_assoc, div_self hne, mul_one]
  refine Tendsto.congr' hslope ?_
  have hM : Tendsto (fun ζ : ℂ => Theta L ζ) (𝓝[≠] ξ) (𝓝 (Theta L ξ)) :=
    (continuousAt_Theta L hL hξ).tendsto.mono_left nhdsWithin_le_nhds
  have hmul : Tendsto (fun ζ : ℂ => Theta L ζ * SB L * Theta L ξ) (𝓝[≠] ξ)
      (𝓝 (Theta L ξ * SB L * Theta L ξ)) :=
    (hM.mul tendsto_const_nhds).mul tendsto_const_nhds
  exact ((continuous_matrix_entry L a b).continuousAt.tendsto).comp hmul

end RBM
