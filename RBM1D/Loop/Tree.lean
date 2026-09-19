/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Crossing
import RBM1D.Loop.Primitive

/-!
# Tree values: the star graph and the case `n = 4`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 3.3 and the
`n = 4` formula after Lemma 3.4, for the trees that are needed to pin down the conventions.

Indices are `0`-based: the polygon vertex `a i` (the paper's `a_{i+1}`) lies between the
regions `i` and `i + 1` (mod `n`), so the boundary edge at `a i` carries
`f_t = Θ_{t m(σ_i) m(σ_{i+1})}` (Definition 3.3, item 1).

## Two corrections, both checked against the primitive equation

* **Boundary indices in the `n = 4` display.** The display after Figure 6 writes the
  boundary factor at `a_i` as `Θ_{t m_{i-1} m_i}`, whereas Definition 3.3 (item 1) and the
  worked example after it give `Θ_{t m_i m_{i+1}}`.  Only the latter solves (2.48): a
  finite-difference check at `n = 3, 4` (`L = 5`, several `σ`, `a`) matches (2.48) to
  `10⁻¹¹` with `Θ_{t m_i m_{i+1}}` and misses by `10⁻²` with `Θ_{t m_{i-1} m_i}`.  The internal
  edges of the display are correct.  `RBM.gammaFour` uses the corrected boundary factors.
* **`n = 2`.** The star formula gives `(Θ²)_{a₁a₂}`, but the solution of (2.55) is
  `Θ_{a₁a₂}` (Example 2.15, `RBM.hasDerivAt_kTwo`).  `RBM.not_hasDerivAt_starK_two` proves that
  the star value does *not* solve (2.55).  For the `2`-gon the tree is the single edge
  `a₁ — a₂` with no internal vertex, and then Lemma 3.4 holds (`RBM.kTwo_eq_edge`).

See `docs/paper-deltas.md`.

## Main definitions

* `RBM.thetaEdge` : `Θ_{t m(s) m(s')}`
* `RBM.starGamma` : the star graph, `∑_b ∏_i (Θ_{t m_i m_{i+1}})_{a_i b}`
* `RBM.gammaFour`  : the `n = 4` display, with corrected boundary factors
* `RBM.splitGamma₀₂`, `RBM.splitGamma₁₃` : the two trees with one internal edge
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

/-- `Θ_{t m(s) m(s')}`, the value of an edge between regions with charges `s`, `s'`. -/
noncomputable def thetaEdge (m : Bool → ℂ) (t : ℝ) (s s' : Bool) : Matrix (ZMod L) (ZMod L) ℂ :=
  Theta L (t * (m s * m s'))

theorem thetaEdge_comm (m : Bool → ℂ) (t : ℝ) (s s' : Bool) :
    thetaEdge L m t s s' = thetaEdge L m t s' s := by
  rw [thetaEdge, thetaEdge, mul_comm (m s)]

/-- The star graph (`F = ∅`): `∑_b ∏_i (Θ_{t m_i m_{i+1}})_{a_i b}`, indices mod `n`. -/
noncomputable def starGamma {n : ℕ} [NeZero n] (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → ZMod L) : ℂ :=
  ∑ b : ZMod L, ∏ i : Fin n, thetaEdge L m t (σ i) (σ (i + 1)) (a i) b

section Two

/-- At `n = 2` the star formula gives `(Θ²)_{a₀a₁}`, not `Θ_{a₀a₁}`. -/
theorem starGamma_two (hL : 3 ≤ L) (m : Bool → ℂ) (t : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → ZMod L) (ht : ‖(t : ℂ) * (m (σ 0) * m (σ 1))‖ < 1) :
    starGamma L m t σ a
      = (thetaEdge L m t (σ 0) (σ 1) * thetaEdge L m t (σ 0) (σ 1)) (a 0) (a 1) := by
  rw [starGamma, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.prod_univ_two]
  have h11 : (1 : Fin 2) + 1 = 0 := rfl
  have h01 : (0 : Fin 2) + 1 = 1 := rfl
  rw [h11, h01, thetaEdge_comm L m t (σ 1) (σ 0)]
  congr 1
  exact (congrFun (congrFun (Theta_transpose L hL ht) (a 1)) b).symm

/-- (3.5) with the star value at `n = 2`: `W⁻¹ m₁ m₂ (Θ²)_{a₀a₁}`. -/
noncomputable def starKTwo (W : ℕ) (m : Bool → ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (x y : ZMod L) : ℂ :=
  (W : ℂ)⁻¹ * (m σ₁ * m σ₂) * (Theta L (t * (m σ₁ * m σ₂)) * Theta L (t * (m σ₁ * m σ₂))) x y

/-- **The star value does not solve the primitive equation at `n = 2`.**  At `t = 0` its
derivative is `2 W⁻¹ μ² S_{a₁a₂}` (`μ = m₁m₂`) while (2.55) demands `W⁻¹ μ² S_{a₁a₂}`. -/
theorem not_hasDerivAt_starK_two (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ)
    (σ₁ σ₂ : Bool) (a₁ a₂ : ZMod L) (hμ : m σ₁ * m σ₂ ≠ 0) (hS : SB L a₁ a₂ ≠ 0) :
    ¬ HasDerivAt (fun s => starKTwo L W m s σ₁ σ₂ a₁ a₂)
        ((W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
          starKTwo L W m 0 σ₁ σ₂ a₁ a * SB L a b * starKTwo L W m 0 σ₁ σ₂ b a₂) 0 := by
  intro h
  set μ := m σ₁ * m σ₂ with hμdef
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have h0 : ‖((0 : ℝ) : ℂ) * μ‖ < 1 := by simp
  -- derivative of each entry `s ↦ Θ(sμ)_{xy}` at `0` is `μ S_{xy}`
  have hent : ∀ x y : ZMod L, HasDerivAt (fun s : ℝ => Theta L ((s : ℂ) * μ) x y)
      (μ * SB L x y) 0 := by
    intro x y
    have h1 := hasDerivAt_Theta_apply L hL h0 x y
    have h2 : HasDerivAt (fun ζ : ℂ => ζ * μ) μ ((0 : ℝ) : ℂ) := by
      simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const μ
    have h3 := (h1.comp ((0 : ℝ) : ℂ) h2).comp_ofReal
    refine h3.congr_deriv ?_
    simp [Theta_zero, mul_comm]
  -- derivative of the star value at `0`
  have hstar : HasDerivAt (fun s => starKTwo L W m s σ₁ σ₂ a₁ a₂)
      ((W : ℂ)⁻¹ * μ * (2 * (μ * SB L a₁ a₂))) 0 := by
    have hsum : HasDerivAt
        (fun s : ℝ => ∑ b : ZMod L, Theta L ((s : ℂ) * μ) a₁ b * Theta L ((s : ℂ) * μ) b a₂)
        (∑ b : ZMod L, ((μ * SB L a₁ b) * (1 : Matrix (ZMod L) (ZMod L) ℂ) b a₂
          + (1 : Matrix (ZMod L) (ZMod L) ℂ) a₁ b * (μ * SB L b a₂))) 0 := by
      refine HasDerivAt.fun_sum fun b _ => ?_
      refine ((hent a₁ b).mul (hent b a₂)).congr_deriv ?_
      simp [Theta_zero]
    have hval : ∑ b : ZMod L, ((μ * SB L a₁ b) * (1 : Matrix (ZMod L) (ZMod L) ℂ) b a₂
          + (1 : Matrix (ZMod L) (ZMod L) ℂ) a₁ b * (μ * SB L b a₂)) = 2 * (μ * SB L a₁ a₂) := by
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
        Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
      ring
    rw [hval] at hsum
    have := hsum.const_mul ((W : ℂ)⁻¹ * μ)
    refine this.congr_deriv rfl |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => by
      simp only [starKTwo, Matrix.mul_apply, ← hμdef]
  have huniq := h.unique hstar
  -- the right-hand side of (2.55) at `t = 0`
  have hrhs : (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
      starKTwo L W m 0 σ₁ σ₂ a₁ a * SB L a b * starKTwo L W m 0 σ₁ σ₂ b a₂
      = (W : ℂ)⁻¹ * μ * (μ * SB L a₁ a₂) := by
    simp only [starKTwo, Complex.ofReal_zero, zero_mul, Theta_zero, mul_one, ← hμdef,
      Matrix.one_apply]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp
  rw [hrhs] at huniq
  have : (W : ℂ)⁻¹ * μ * (μ * SB L a₁ a₂) = 0 := by linear_combination -1 * huniq
  simp [hW, hμ, hS] at this

/-- The correct tree for the `2`-gon is the single edge `a₀ — a₁`; with it, (3.5) is
Example 2.15: `m_σ W⁻¹ Θ_{a₀a₁} = K_{t,σ,(a₀,a₁)}`. -/
theorem kTwo_eq_edge (W : ℕ) (m : Bool → ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a₁ a₂ : ZMod L) :
    kTwo L W m t σ₁ σ₂ a₁ a₂ = (m σ₁ * m σ₂) * (W : ℂ)⁻¹ * thetaEdge L m t σ₁ σ₂ a₁ a₂ := by
  rw [kTwo, thetaEdge]
  ring

end Two

section Four

variable (m : Bool → ℂ) (t : ℝ) (σ : Fin 4 → Bool) (a : Fin 4 → ZMod L)

/-- The boundary edge at `a i`: `Θ_{t m(σ_i) m(σ_{i+1})}`. -/
noncomputable abbrev bd (i : Fin 4) : Matrix (ZMod L) (ZMod L) ℂ :=
  thetaEdge L m t (σ i) (σ (i + 1))

/-- The `n = 4` formula after Figure 6, with the boundary factors corrected to
`Θ_{t m_i m_{i+1}}` (see the module docstring):
`∑_{b} ∏_i (Θ_{t m_i m_{i+1}})_{a_i b_i} (δ_{b₀b₁b₂b₃} + δ_{b₀b₁}δ_{b₂b₃}(Θ_{t m₀m₂} - 1)_{b₀b₂}
  + δ_{b₀b₃}δ_{b₁b₂}(Θ_{t m₁m₃} - 1)_{b₀b₁})`. -/
noncomputable def gammaFour : ℂ :=
  ∑ b₀ : ZMod L, ∑ b₁ : ZMod L, ∑ b₂ : ZMod L, ∑ b₃ : ZMod L,
    bd L m t σ 0 (a 0) b₀ * bd L m t σ 1 (a 1) b₁ * bd L m t σ 2 (a 2) b₂ *
      bd L m t σ 3 (a 3) b₃ *
    ((if b₁ = b₀ then if b₂ = b₀ then if b₃ = b₀ then 1 else 0 else 0 else 0)
      + (if b₁ = b₀ then if b₃ = b₂ then
          (thetaEdge L m t (σ 0) (σ 2) - 1) b₀ b₂ else 0 else 0)
      + (if b₃ = b₀ then if b₂ = b₁ then
          (thetaEdge L m t (σ 1) (σ 3) - 1) b₀ b₁ else 0 else 0))

/-- The tree `{(0, 2)}` of `TSP 4` (the paper's pairing `{1, 3}`): `a₀, a₁` hang on `x`,
`a₂, a₃` on `y`, and the internal edge `x — y` separates regions `0` and `2`. -/
noncomputable def splitGamma₀₂ : ℂ :=
  ∑ x : ZMod L, ∑ y : ZMod L,
    bd L m t σ 0 (a 0) x * bd L m t σ 1 (a 1) x * bd L m t σ 2 (a 2) y * bd L m t σ 3 (a 3) y *
      (thetaEdge L m t (σ 0) (σ 2) - 1) x y

/-- The tree `{(1, 3)}` of `TSP 4` (the paper's pairing `{2, 4}`): `a₀, a₃` hang on `x`,
`a₁, a₂` on `y`, and the internal edge separates regions `1` and `3`. -/
noncomputable def splitGamma₁₃ : ℂ :=
  ∑ x : ZMod L, ∑ y : ZMod L,
    bd L m t σ 0 (a 0) x * bd L m t σ 1 (a 1) y * bd L m t σ 2 (a 2) y * bd L m t σ 3 (a 3) x *
      (thetaEdge L m t (σ 1) (σ 3) - 1) x y

/-- **Acceptance criterion for the general tree value.**  The `n = 4` display is the sum of
the values of the three trees of `TSP 4 = {∅, {(0,2)}, {(1,3)}}` (`RBM.TSP_four`). -/
theorem gammaFour_eq :
    gammaFour L m t σ a = starGamma L m t σ a + splitGamma₀₂ L m t σ a + splitGamma₁₃ L m t σ a := by
  simp only [gammaFour, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, mul_one,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [starGamma, splitGamma₀₂, splitGamma₁₃]
  simp only [Fin.prod_univ_four]

end Four

end RBM
