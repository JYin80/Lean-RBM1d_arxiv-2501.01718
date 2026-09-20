/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Moments
import RBM1D.Gauss.LinearForm
import RBM1D.Gauss.Domination
import RBM1D.Green.EntryBound

/-!
# The diagonal large deviation bound `|H_{ii}|² ≺ S_{ii}`

`RBM.diag_bound_stochDom` (Lemma 4.1, (4.3)) takes `|H_{ii}|² ≺ S_{ii}` as its hypothesis
`hLdiag`.  For the Gaussian flow this is immediate: the diagonal entry
`H_{ii} = √u · ω⟨N,i,i,tt⟩` is a *real* centred Gaussian of variance `u S_{ii}` — the diagonal
of a Hermitian matrix carries no imaginary part, and `Xentry` reads a single coordinate there.
So every even moment is `u^p (2p-1)!! S_{ii}^p`, and `stochDom_of_momentDom` converts this into
`≺` after the union bound over the `LW ≤ N` sites.

The control `S_{ii} = 1/(3W)` is strictly positive, which is what `stochDom_of_momentDom`
needs.

## Main statements

* `RBM.Sblk_diag_pos`                     : `0 < S_{ii}`
* `RBM.Gauss.integral_norm_Hflow_diag_pow`: `E|H_{ii}|^{2p} = u^p (2p-1)!! S_{ii}^p`
* `RBM.Gauss.stochDom_normSq_Hflow_diag`  : the hypothesis `hLdiag` of
  `RBM.diag_bound_stochDom`
-/

namespace RBM

open MeasureTheory ProbabilityTheory Finset

/-- The diagonal of the variance profile is `1/(3W) > 0`. -/
theorem Sblk_diag_pos {L W : ℕ} [NeZero L] [NeZero W] (i : ZMod L × Fin W) :
    0 < Sblk L W i i := by
  have hW : (0 : ℝ) < W := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have h0 : sbKre L (i.1 - i.1) = 1 / 3 := by
    rw [sub_self, sbKre, ite_eq_left (by simp [sbSupport])]
  rw [Sblk, h0]
  positivity

namespace Gauss

variable {d : Dims} {N : ℕ} {u : ℝ}

/-! ### One coordinate -/

/-- Moments of a single coordinate, pushed through `P_map_eval`. -/
theorem integral_pow_coord (d : Dims) (c : Coord d) (k : ℕ) :
    ∫ ω, (ω c) ^ k ∂(P d) = ∫ x : ℝ, x ^ k ∂(gaussianReal 0 (gvar d c)) := by
  have hf : AEMeasurable (fun ω : Ω d => ω c) (P d) := (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ k) ((P d).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, P_map_eval]

theorem integrable_pow_coord (d : Dims) (c : Coord d) (k : ℕ) :
    Integrable (fun ω : Ω d => (ω c) ^ k) (P d) := by
  have hf : AEMeasurable (fun ω : Ω d => ω c) (P d) := (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ k) ((P d).map fun ω => ω c) := by
    fun_prop
  refine (integrable_map_measure hg hf).1 ?_
  rw [P_map_eval]
  exact integrable_pow_gaussianReal _ k

/-! ### The diagonal entry of the flow -/

/-- The diagonal entry is real: `|H_{ii}|² = u · ω⟨N,i,i,tt⟩²`. -/
theorem normSq_Hflow_diag (hu : 0 ≤ u) (ω : Ω d) (i : d.Idx N) :
    ‖Hflow d N u ω i i‖ ^ 2 = u * (ω ⟨N, i, i, true⟩) ^ 2 := by
  have hX : Xentry d N ω i i = ((ω ⟨N, i, i, true⟩ : ℝ) : ℂ) := by
    rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
  rw [Hflow_apply, hX, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg u), mul_pow, Real.sq_sqrt hu, sq_abs]

/-- **All even moments of the diagonal entry**: `E|H_{ii}|^{2p} = u^p (2p-1)!! S_{ii}^p`. -/
theorem integral_norm_Hflow_diag_pow (hu : 0 ≤ u) (i : d.Idx N) (p : ℕ) :
    ∫ ω, ‖Hflow d N u ω i i‖ ^ (2 * p) ∂(P d)
      = u ^ p * (dfac p * Sblk (d.L N) (d.W N) i i ^ p) := by
  have hpow : ∀ ω : Ω d, ‖Hflow d N u ω i i‖ ^ (2 * p)
      = u ^ p * (ω ⟨N, i, i, true⟩) ^ (2 * p) := by
    intro ω
    rw [pow_mul, normSq_Hflow_diag hu ω i, mul_pow, ← pow_mul, mul_comm 2 p]
  simp only [hpow]
  rw [integral_const_mul, integral_pow_coord, integral_pow_gaussianReal', gvar_diag]

theorem integrable_norm_Hflow_diag_pow (hu : 0 ≤ u) (i : d.Idx N) (k : ℕ) :
    Integrable (fun ω : Ω d => ‖Hflow d N u ω i i‖ ^ (2 * k)) (P d) := by
  have hpow : ∀ ω : Ω d, ‖Hflow d N u ω i i‖ ^ (2 * k)
      = u ^ k * (ω ⟨N, i, i, true⟩) ^ (2 * k) := by
    intro ω
    rw [pow_mul, normSq_Hflow_diag hu ω i, mul_pow, ← pow_mul, mul_comm 2 k]
  simp only [hpow]
  exact (integrable_pow_coord d _ (2 * k)).const_mul _

/-! ### The union bound -/

theorem eventually_card_Idx_le (d : Dims) :
    ∀ᶠ N : ℕ in Filter.atTop, (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
  filter_upwards [d.dim] with N hN
  have hcard : Fintype.card (d.Idx N) = d.L N * d.W N := by
    simp [Dims.Idx, ZMod.card]
  have hLW : d.L N * d.W N ≤ N := by
    have := hN.1
    rw [Nat.mul_comm] at this
    exact this
  rw [hcard, Real.rpow_one]
  exact_mod_cast hLW

/-- **The hypothesis `hLdiag` of `RBM.diag_bound_stochDom`**, for the Gaussian flow
`H_u = √u X`: `|H_{ii}|² ≺ S_{ii}`, uniformly in `i`.  No upper bound on `u` is needed — the
factor `u^{2p}` goes into the constant `C(ε,p)`, which may depend on the (fixed) time. -/
theorem stochDom_normSq_Hflow_diag (hu0 : 0 ≤ u) :
    StochDom (P d)
      (fun N (i : BIdx d.L d.W N) ω => ‖Hflow d N u ω i i‖ ^ 2)
      (fun N (i : BIdx d.L d.W N) _ => Sblk (d.L N) (d.W N) i i) := by
  refine stochDom_of_momentDom (eventually_card_Idx_le d)
    (fun N i => Sblk_diag_pos i) ?_ ?_
  · intro p N i
    have habs : ∀ ω : Ω d, ‖Hflow d N u ω i i‖ ^ (2 * (2 * p))
        = |‖Hflow d N u ω i i‖ ^ 2| ^ (2 * p) := fun ω => by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖Hflow d N u ω i i‖ ^ 2), ← pow_mul]
    have h := integrable_norm_Hflow_diag_pow (d := d) (N := N) (u := u) hu0 i (2 * p)
    simpa only [habs] using h
  · intro ε hε p
    have hd0 : (0 : ℝ) ≤ dfac (2 * p) := by unfold dfac; positivity
    have hud0 : (0 : ℝ) ≤ u ^ (2 * p) * dfac (2 * p) := by positivity
    refine ⟨u ^ (2 * p) * dfac (2 * p) + 1, by linarith, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN1 i
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hS : (0 : ℝ) < Sblk (d.L N) (d.W N) i i := Sblk_diag_pos i
    have hpt : ∀ ω : Ω d, |‖Hflow d N u ω i i‖ ^ 2| ^ (2 * p)
        = ‖Hflow d N u ω i i‖ ^ (2 * (2 * p)) := fun ω => by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖Hflow d N u ω i i‖ ^ 2), ← pow_mul]
    simp only [hpt]
    rw [integral_norm_Hflow_diag_pow hu0]
    have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) := Real.one_le_rpow hN1' (by positivity)
    set A : ℝ := Sblk (d.L N) (d.W N) i i ^ (2 * p) with hAdef
    have hA0 : 0 < A := by rw [hAdef]; positivity
    calc u ^ (2 * p) * (dfac (2 * p) * A)
        = (u ^ (2 * p) * dfac (2 * p)) * A := by ring
      _ ≤ (u ^ (2 * p) * dfac (2 * p) + 1) * A := by nlinarith
      _ ≤ (u ^ (2 * p) * dfac (2 * p) + 1) * ((N : ℝ) ^ (ε * p) * A) := by
          have h1 : A ≤ (N : ℝ) ^ (ε * p) * A := le_mul_of_one_le_left hA0.le hpow
          exact mul_le_mul_of_nonneg_left h1 (by linarith)

end Gauss

end RBM
