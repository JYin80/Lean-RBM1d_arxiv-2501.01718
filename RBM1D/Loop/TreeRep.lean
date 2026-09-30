/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Example3
import RBM1D.Loop.Unique
import RBM1D.Propagator.Bounds

/-!
# Lemma 3.4: the tree representation, for `n ≤ 4`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 3.4, (3.5):

  `K_{t,σ,a} = m_σ W^{-n+1} ∑_{Γ ∈ T_SP(P_a)} Γ_a(t, σ)`.

`n = 2` is Example 2.15 and `n = 3` is Example 2.16
(`RBM1D.Loop.Example3`).  This file does `n = 4`, the first case with internal edges, and
exhibits the combinatorics of the general proof on it:

* **boundary edges ↔ terms with a `2`-chain.**  The boundary edge at `aᵢ` occurs, with the
  same factor `(Θ_{t mᵢmᵢ₊₁})_{aᵢ ·}`, in all three trees of `T_SP(4)`.  Differentiating it
  inserts `S^(B)` (2.51), and by linearity in that row the three contributions add up to
  `∑_x (mᵢmᵢ₊₁ Θ S)_{aᵢx} K_{(…),(…, x, …)}`, which is the `(k,l)` term with the `2`-chain
  `(σᵢ, σᵢ₊₁)`: `(1,2), (2,3), (3,4)` and the wrap-around `(1,4)`.
* **internal edges ↔ terms with two `3`-chains.**  The tree split along the diagonal
  `(0, 2)` has the internal edge `Θ_{t m₀m₂} - 1`; its derivative `m₀m₂ Θ S Θ` factors the tree
  into `K_{(σ₀σ₁σ₂)} S K_{(σ₀σ₂σ₃)}`, the `(k,l) = (1,3)` term.  Likewise `(1,3) ↔ (2,4)`.

That is the whole bijection "edges of trees ↔ `(k, l)` pairs" at `n = 4`: `4` boundary edges
and `2` diagonals against the `6` pairs `k < l`.

## Main results

* `RBM.kFour` : the tree representation at `n = 4`
* `RBM.kLoop4` : the same in the general form `primRhs`
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

section Shapes

variable {L}

/-- The star of the `4`-gon with boundary matrices `B₀, …, B₃`. -/
noncomputable def star4 (B₀ B₁ B₂ B₃ : Matrix (ZMod L) (ZMod L) ℂ) (a₀ a₁ a₂ a₃ : ZMod L) : ℂ :=
  ∑ b : ZMod L, B₀ a₀ b * B₁ a₁ b * B₂ a₂ b * B₃ a₃ b

/-- The tree split along the diagonal `(0, 2)`, with internal edge matrix `E`. -/
noncomputable def spl02 (B₀ B₁ B₂ B₃ E : Matrix (ZMod L) (ZMod L) ℂ) (a₀ a₁ a₂ a₃ : ZMod L) :
    ℂ :=
  ∑ x : ZMod L, ∑ y : ZMod L, B₀ a₀ x * B₁ a₁ x * B₂ a₂ y * B₃ a₃ y * E x y

/-- The tree split along the diagonal `(1, 3)`, with internal edge matrix `E`. -/
noncomputable def spl13 (B₀ B₁ B₂ B₃ E : Matrix (ZMod L) (ZMod L) ℂ) (a₀ a₁ a₂ a₃ : ZMod L) :
    ℂ :=
  ∑ x : ZMod L, ∑ y : ZMod L, B₀ a₀ x * B₁ a₁ y * B₂ a₂ y * B₃ a₃ x * E x y

variable (M N B₀ B₁ B₂ B₃ E : Matrix (ZMod L) (ZMod L) ℂ) (a₀ a₁ a₂ a₃ : ZMod L)

/-! ### Linearity in one boundary row: `f(M N) = ∑_z M_{a z} f(N)(z)` -/

/-! ### The internal edge: `∑_{x,y} f_x (P S P)_{xy} g_y = ∑_{u,v} (fP)_u S_{uv} (Pg)_v` -/

end Shapes

section Four

variable {L}

/-- The three trees of `T_SP(4)` with boundary matrices `B₀, …, B₃` and internal edges
`P - 1` (diagonal `(0,2)`) and `Q - 1` (diagonal `(1,3)`). -/
noncomputable def trees4 (B₀ B₁ B₂ B₃ P Q : Matrix (ZMod L) (ZMod L) ℂ) (a₀ a₁ a₂ a₃ : ZMod L) :
    ℂ :=
  star4 B₀ B₁ B₂ B₃ a₀ a₁ a₂ a₃ + spl02 B₀ B₁ B₂ B₃ (P - 1) a₀ a₁ a₂ a₃
    + spl13 B₀ B₁ B₂ B₃ (Q - 1) a₀ a₁ a₂ a₃

variable (M N B₀ B₁ B₂ B₃ P Q : Matrix (ZMod L) (ZMod L) ℂ) (a₀ a₁ a₂ a₃ : ZMod L)

/-! ### Derivatives of the tree shapes -/

variable {B₀ B₁ B₂ B₃ E : ℝ → Matrix (ZMod L) (ZMod L) ℂ}
  {D₀ D₁ D₂ D₃ DE : Matrix (ZMod L) (ZMod L) ℂ} {t : ℝ}

end Four

section KFour

variable {L}

/-- **(3.5) at `n = 4`**: `K = m₀m₁m₂m₃ W⁻³ ∑_{Γ ∈ T_SP(4)} Γ`, the boundary edge at `aᵢ`
being `Θ_{t mᵢ mᵢ₊₁}`. -/
noncomputable def kFour (W : ℕ) (m : Bool → ℂ) (t : ℝ) (s₀ s₁ s₂ s₃ : Bool)
    (a₀ a₁ a₂ a₃ : ZMod L) : ℂ :=
  (W : ℂ)⁻¹ ^ 3 * (m s₀ * m s₁ * m s₂ * m s₃) *
    trees4 (thetaEdge L m t s₀ s₁) (thetaEdge L m t s₁ s₂) (thetaEdge L m t s₂ s₃)
      (thetaEdge L m t s₃ s₀) (thetaEdge L m t s₀ s₂) (thetaEdge L m t s₁ s₃) a₀ a₁ a₂ a₃

theorem hasDerivAt_thetaEdge' (hL : 3 ≤ L) (m : Bool → ℂ) {t : ℝ} (s s' : Bool)
    (ht : ‖(t : ℂ) * (m s * m s')‖ < 1) (i j : ZMod L) :
    HasDerivAt (fun r : ℝ => thetaEdge L m r s s' i j)
      ((((m s * m s') • (thetaEdge L m t s s' * SB L)) * thetaEdge L m t s s') i j) t :=
  (hasDerivAt_thetaEdge hL m s s' ht i j).congr_deriv (by
    rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_comm])

end KFour

section Assembly

variable {L} (W : ℕ) [NeZero W] (m : Bool → ℂ) (t : ℝ) (s₀ s₁ s₂ s₃ : Bool)
  (a₀ a₁ a₂ a₃ : ZMod L)

/-- Examples 2.15, 2.16 and the `n = 4` tree representation as one function of the loop. -/
noncomputable def kLoop4 (W : ℕ) (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (ZMod L)) : ℂ :=
  match I.σ, I.a with
  | [σ₁, σ₂], [x₁, x₂] => kTwo L W m t σ₁ σ₂ x₁ x₂
  | [σ₁, σ₂, σ₃], [x₁, x₂, x₃] => kThree W m t σ₁ σ₂ σ₃ x₁ x₂ x₃
  | [σ₀, σ₁, σ₂, σ₃], [x₀, x₁, x₂, x₃] => kFour W m t σ₀ σ₁ σ₂ σ₃ x₀ x₁ x₂ x₃
  | _, _ => 0

end Assembly

section Uniqueness

variable {L}

omit [NeZero L] in
/-- A well-formed loop of length `2`, `3` or `4` is one of the three explicit shapes. -/
theorem loop_cases {I : LoopIdx (ZMod L)} (hI : I.WF) (h2 : 2 ≤ I.length) (h4 : I.length ≤ 4) :
    (∃ s₁ s₂ x₁ x₂, I = ⟨[s₁, s₂], [x₁, x₂]⟩) ∨
    (∃ s₁ s₂ s₃ x₁ x₂ x₃, I = ⟨[s₁, s₂, s₃], [x₁, x₂, x₃]⟩) ∨
    (∃ s₀ s₁ s₂ s₃ x₀ x₁ x₂ x₃, I = ⟨[s₀, s₁, s₂, s₃], [x₀, x₁, x₂, x₃]⟩) := by
  obtain ⟨σ, a⟩ := I
  simp only [LoopIdx.WF, LoopIdx.length] at hI h2 h4
  have hσ : σ.length = a.length := hI
  interval_cases h : a.length
  · obtain ⟨x₁, x₂, rfl⟩ := List.length_eq_two.1 h
    obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.1 hσ
    exact Or.inl ⟨s₁, s₂, x₁, x₂, rfl⟩
  · obtain ⟨x₁, x₂, x₃, rfl⟩ := List.length_eq_three.1 h
    obtain ⟨s₁, s₂, s₃, rfl⟩ := List.length_eq_three.1 hσ
    exact Or.inr (Or.inl ⟨s₁, s₂, s₃, x₁, x₂, x₃, rfl⟩)
  · obtain ⟨x₀, x₁, x₂, x₃, rfl⟩ := List.length_eq_four.1 h
    obtain ⟨s₀, s₁, s₂, s₃, rfl⟩ := List.length_eq_four.1 hσ
    exact Or.inr (Or.inr ⟨s₀, s₁, s₂, s₃, x₀, x₁, x₂, x₃, rfl⟩)

variable (W : ℕ) [NeZero W] (m : Bool → ℂ)

omit [NeZero W] in
theorem norm_mul_le_of_mem_Icc {t T₀ : ℝ} (hm1 : ∀ s, ‖m s‖ ≤ 1) (ht : t ∈ Set.Icc 0 T₀)
    (s s' : Bool) : ‖(t : ℂ) * (m s * m s')‖ ≤ T₀ := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
  have h1 := mul_le_mul (hm1 s) (hm1 s') (norm_nonneg _) zero_le_one
  rw [one_mul] at h1
  have := mul_le_mul_of_nonneg_left h1 ht.1
  linarith [ht.2]

omit [NeZero W] in
/-- The `2`-loops of the tree formula are bounded on `[0, T₀]`, `T₀ < 1`. -/
theorem norm_kLoop4_two_le (hL : 3 ≤ L) (hm1 : ∀ s, ‖m s‖ ≤ 1) {t T₀ : ℝ}
    (ht : t ∈ Set.Icc 0 T₀) (hT₀ : T₀ < 1) {I : LoopIdx (ZMod L)} (hI : I.WF)
    (h2 : I.length = 2) : ‖kLoop4 W m t I‖ ≤ (W : ℝ)⁻¹ * (1 - T₀)⁻¹ := by
  rcases loop_cases hI h2.ge (h2.le.trans (by norm_num)) with ⟨s₁, s₂, x₁, x₂, rfl⟩ |
    ⟨s₁, s₂, s₃, x₁, x₂, x₃, rfl⟩ | ⟨s₀, s₁, s₂, s₃, x₀, x₁, x₂, x₃, rfl⟩
  · have hq := norm_mul_le_of_mem_Icc m hm1 ht s₁ s₂
    have hq1 : ‖(t : ℂ) * (m s₁ * m s₂)‖ < 1 := hq.trans_lt hT₀
    have hΘ := norm_Theta_apply_le L hL hq1 x₁ x₂
    have hmm : ‖m s₁ * m s₂‖ ≤ 1 := by
      rw [norm_mul]; nlinarith [hm1 s₁, hm1 s₂, norm_nonneg (m s₁), norm_nonneg (m s₂)]
    have hinv : (1 - ‖(t : ℂ) * (m s₁ * m s₂)‖)⁻¹ ≤ (1 - T₀)⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    change ‖kTwo L W m t s₁ s₂ x₁ x₂‖ ≤ _
    rw [kTwo, norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
    calc (W : ℝ)⁻¹ * ‖m s₁ * m s₂‖ * ‖Theta L (t * (m s₁ * m s₂)) x₁ x₂‖
        ≤ (W : ℝ)⁻¹ * 1 * (1 - T₀)⁻¹ := by gcongr; exact hΘ.trans hinv
      _ = (W : ℝ)⁻¹ * (1 - T₀)⁻¹ := by ring
  · simp [LoopIdx.length] at h2
  · simp [LoopIdx.length] at h2

end Uniqueness

end RBM
