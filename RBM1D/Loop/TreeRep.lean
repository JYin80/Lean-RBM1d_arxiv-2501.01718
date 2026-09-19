/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Example3
import RBM1D.Loop.Unique

/-!
# Lemma 3.4: the tree representation, for `n ≤ 4`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 3.4, (3.5):

  `K_{t,σ,a} = m_σ W^{-n+1} ∑_{Γ ∈ T_SP(P_a)} Γ_a(t, σ)`.

`n = 2` is Example 2.15 (`RBM.kTwo_eq_treeSum`) and `n = 3` is Example 2.16
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

* `RBM.primRhs_four` : the six terms of (2.48) at `n = 4`
* `RBM.kFour`, `RBM.kFour_eq_treeSum` : the tree representation at `n = 4`
* `RBM.hasDerivAt_kFour`, `RBM.kFour_zero` : it solves (2.48) with the right initial value
* `RBM.kLoop4`, `RBM.hasDerivAt_kLoop4` : the same in the general form `primRhs`
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

section IndexCheck

/-- The six terms of (2.48) at `n = 4`, in the order `(k,l) = (1,2), (1,3), (1,4), (2,3),
(2,4), (3,4)`. -/
theorem primRhs_four (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (s₀ s₁ s₂ s₃ : Bool)
    (a₀ a₁ a₂ a₃ : ZMod L) :
    primRhs L W K ⟨[s₀, s₁, s₂, s₃], [a₀, a₁, a₂, a₃]⟩
      = (W : ℂ) * ((∑ x : ZMod L, ∑ y : ZMod L,
            K ⟨[s₀, s₁, s₂, s₃], [x, a₁, a₂, a₃]⟩ * SB L x y * K ⟨[s₀, s₁], [a₀, y]⟩)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            K ⟨[s₀, s₂, s₃], [x, a₂, a₃]⟩ * SB L x y * K ⟨[s₀, s₁, s₂], [a₀, a₁, y]⟩)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            K ⟨[s₀, s₃], [x, a₃]⟩ * SB L x y * K ⟨[s₀, s₁, s₂, s₃], [a₀, a₁, a₂, y]⟩)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            K ⟨[s₀, s₁, s₂, s₃], [a₀, x, a₂, a₃]⟩ * SB L x y * K ⟨[s₁, s₂], [a₁, y]⟩)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            K ⟨[s₀, s₁, s₃], [a₀, x, a₃]⟩ * SB L x y * K ⟨[s₁, s₂, s₃], [a₁, a₂, y]⟩)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            K ⟨[s₀, s₁, s₂, s₃], [a₀, a₁, x, a₃]⟩ * SB L x y * K ⟨[s₂, s₃], [a₂, y]⟩)) := by
  have h14 : Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  have h1 : Ioc 1 4 = ({2, 3, 4} : Finset ℕ) := by decide
  have h2 : Ioc 2 4 = ({3, 4} : Finset ℕ) := by decide
  have h3 : Ioc 3 4 = ({4} : Finset ℕ) := by decide
  have h4 : Ioc 4 4 = (∅ : Finset ℕ) := by decide
  have hlen : (LoopIdx.mk [s₀, s₁, s₂, s₃] [a₀, a₁, a₂, a₃]).length = 4 := rfl
  rw [primRhs, hlen, h14, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, h1, h2, h3, h4,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton, Finset.sum_singleton,
    Finset.sum_empty, add_zero]
  simp only [add_assoc]
  rfl

end IndexCheck

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

theorem sum_comm3 (f : ZMod L → ZMod L → ZMod L → ℂ) :
    ∑ x : ZMod L, ∑ y : ZMod L, ∑ z : ZMod L, f x y z
      = ∑ z : ZMod L, ∑ x : ZMod L, ∑ y : ZMod L, f x y z :=
  calc ∑ x : ZMod L, ∑ y : ZMod L, ∑ z : ZMod L, f x y z
      = ∑ x : ZMod L, ∑ z : ZMod L, ∑ y : ZMod L, f x y z :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z : ZMod L, ∑ x : ZMod L, ∑ y : ZMod L, f x y z := Finset.sum_comm

variable (M N B₀ B₁ B₂ B₃ E : Matrix (ZMod L) (ZMod L) ℂ) (a₀ a₁ a₂ a₃ : ZMod L)

/-! ### Linearity in one boundary row: `f(M N) = ∑_z M_{a z} f(N)(z)` -/

theorem star4_slot0 : star4 (M * N) B₁ B₂ B₃ a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₀ z * star4 N B₁ B₂ B₃ z a₁ a₂ a₃ := by
  simp only [star4, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem star4_slot1 : star4 B₀ (M * N) B₂ B₃ a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₁ z * star4 B₀ N B₂ B₃ a₀ z a₂ a₃ := by
  simp only [star4, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem star4_slot2 : star4 B₀ B₁ (M * N) B₃ a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₂ z * star4 B₀ B₁ N B₃ a₀ a₁ z a₃ := by
  simp only [star4, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem star4_slot3 : star4 B₀ B₁ B₂ (M * N) a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₃ z * star4 B₀ B₁ B₂ N a₀ a₁ a₂ z := by
  simp only [star4, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem spl02_slot0 : spl02 (M * N) B₁ B₂ B₃ E a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₀ z * spl02 N B₁ B₂ B₃ E z a₁ a₂ a₃ := by
  simp only [spl02, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm3]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem spl02_slot1 : spl02 B₀ (M * N) B₂ B₃ E a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₁ z * spl02 B₀ N B₂ B₃ E a₀ z a₂ a₃ := by
  simp only [spl02, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm3]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem spl02_slot2 : spl02 B₀ B₁ (M * N) B₃ E a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₂ z * spl02 B₀ B₁ N B₃ E a₀ a₁ z a₃ := by
  simp only [spl02, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm3]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem spl02_slot3 : spl02 B₀ B₁ B₂ (M * N) E a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₃ z * spl02 B₀ B₁ B₂ N E a₀ a₁ a₂ z := by
  simp only [spl02, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm3]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem spl13_slot0 : spl13 (M * N) B₁ B₂ B₃ E a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₀ z * spl13 N B₁ B₂ B₃ E z a₁ a₂ a₃ := by
  simp only [spl13, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm3]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem spl13_slot1 : spl13 B₀ (M * N) B₂ B₃ E a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₁ z * spl13 B₀ N B₂ B₃ E a₀ z a₂ a₃ := by
  simp only [spl13, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm3]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem spl13_slot2 : spl13 B₀ B₁ (M * N) B₃ E a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₂ z * spl13 B₀ B₁ N B₃ E a₀ a₁ z a₃ := by
  simp only [spl13, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm3]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem spl13_slot3 : spl13 B₀ B₁ B₂ (M * N) E a₀ a₁ a₂ a₃
    = ∑ z : ZMod L, M a₃ z * spl13 B₀ B₁ B₂ N E a₀ a₁ a₂ z := by
  simp only [spl13, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm3]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-! ### The internal edge: `∑_{x,y} f_x (P S P)_{xy} g_y = ∑_{u,v} (fP)_u S_{uv} (Pg)_v` -/

open Matrix in
theorem sum_bilin (P S : Matrix (ZMod L) (ZMod L) ℂ) (f g : ZMod L → ℂ) :
    ∑ x : ZMod L, ∑ y : ZMod L, f x * (P * S * P) x y * g y
      = ∑ u : ZMod L, ∑ v : ZMod L,
          (∑ x : ZMod L, f x * P x u) * S u v * (∑ y : ZMod L, P v y * g y) := by
  have lhs : ∑ x : ZMod L, ∑ y : ZMod L, f x * (P * S * P) x y * g y
      = f ⬝ᵥ ((P * S * P) *ᵥ g) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have rhs : ∑ u : ZMod L, ∑ v : ZMod L,
      (∑ x : ZMod L, f x * P x u) * S u v * (∑ y : ZMod L, P v y * g y)
      = (f ᵥ* P) ⬝ᵥ (S *ᵥ (P *ᵥ g)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.vecMul, Finset.mul_sum, mul_assoc]
  rw [lhs, rhs, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

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

theorem trees4_slot0 : ∑ z : ZMod L, M a₀ z * trees4 N B₁ B₂ B₃ P Q z a₁ a₂ a₃
    = trees4 (M * N) B₁ B₂ B₃ P Q a₀ a₁ a₂ a₃ := by
  simp only [trees4, mul_add, Finset.sum_add_distrib, star4_slot0, spl02_slot0, spl13_slot0]

theorem trees4_slot1 : ∑ z : ZMod L, M a₁ z * trees4 B₀ N B₂ B₃ P Q a₀ z a₂ a₃
    = trees4 B₀ (M * N) B₂ B₃ P Q a₀ a₁ a₂ a₃ := by
  simp only [trees4, mul_add, Finset.sum_add_distrib, star4_slot1, spl02_slot1, spl13_slot1]

theorem trees4_slot2 : ∑ z : ZMod L, M a₂ z * trees4 B₀ B₁ N B₃ P Q a₀ a₁ z a₃
    = trees4 B₀ B₁ (M * N) B₃ P Q a₀ a₁ a₂ a₃ := by
  simp only [trees4, mul_add, Finset.sum_add_distrib, star4_slot2, spl02_slot2, spl13_slot2]

theorem trees4_slot3 : ∑ z : ZMod L, M a₃ z * trees4 B₀ B₁ B₂ N P Q a₀ a₁ a₂ z
    = trees4 B₀ B₁ B₂ (M * N) P Q a₀ a₁ a₂ a₃ := by
  simp only [trees4, mul_add, Finset.sum_add_distrib, star4_slot3, spl02_slot3, spl13_slot3]

/-! ### Derivatives of the tree shapes -/

variable {B₀ B₁ B₂ B₃ E : ℝ → Matrix (ZMod L) (ZMod L) ℂ}
  {D₀ D₁ D₂ D₃ DE : Matrix (ZMod L) (ZMod L) ℂ} {t : ℝ}

theorem hasDerivAt_star4 (h₀ : ∀ i j, HasDerivAt (fun s => B₀ s i j) (D₀ i j) t)
    (h₁ : ∀ i j, HasDerivAt (fun s => B₁ s i j) (D₁ i j) t)
    (h₂ : ∀ i j, HasDerivAt (fun s => B₂ s i j) (D₂ i j) t)
    (h₃ : ∀ i j, HasDerivAt (fun s => B₃ s i j) (D₃ i j) t) :
    HasDerivAt (fun s => star4 (B₀ s) (B₁ s) (B₂ s) (B₃ s) a₀ a₁ a₂ a₃)
      (star4 D₀ (B₁ t) (B₂ t) (B₃ t) a₀ a₁ a₂ a₃ + star4 (B₀ t) D₁ (B₂ t) (B₃ t) a₀ a₁ a₂ a₃
        + star4 (B₀ t) (B₁ t) D₂ (B₃ t) a₀ a₁ a₂ a₃ + star4 (B₀ t) (B₁ t) (B₂ t) D₃ a₀ a₁ a₂ a₃)
      t := by
  simp only [star4]
  refine (HasDerivAt.fun_sum fun b _ =>
    (((h₀ a₀ b).mul (h₁ a₁ b)).mul (h₂ a₂ b)).mul (h₃ a₃ b)).congr_deriv ?_
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.mul_apply]; ring

theorem hasDerivAt_spl02 (h₀ : ∀ i j, HasDerivAt (fun s => B₀ s i j) (D₀ i j) t)
    (h₁ : ∀ i j, HasDerivAt (fun s => B₁ s i j) (D₁ i j) t)
    (h₂ : ∀ i j, HasDerivAt (fun s => B₂ s i j) (D₂ i j) t)
    (h₃ : ∀ i j, HasDerivAt (fun s => B₃ s i j) (D₃ i j) t)
    (hE : ∀ i j, HasDerivAt (fun s => E s i j) (DE i j) t) :
    HasDerivAt (fun s => spl02 (B₀ s) (B₁ s) (B₂ s) (B₃ s) (E s) a₀ a₁ a₂ a₃)
      (spl02 D₀ (B₁ t) (B₂ t) (B₃ t) (E t) a₀ a₁ a₂ a₃
        + spl02 (B₀ t) D₁ (B₂ t) (B₃ t) (E t) a₀ a₁ a₂ a₃
        + spl02 (B₀ t) (B₁ t) D₂ (B₃ t) (E t) a₀ a₁ a₂ a₃
        + spl02 (B₀ t) (B₁ t) (B₂ t) D₃ (E t) a₀ a₁ a₂ a₃
        + spl02 (B₀ t) (B₁ t) (B₂ t) (B₃ t) DE a₀ a₁ a₂ a₃) t := by
  simp only [spl02]
  refine (HasDerivAt.fun_sum fun x _ => HasDerivAt.fun_sum fun y _ =>
    ((((h₀ a₀ x).mul (h₁ a₁ x)).mul (h₂ a₂ y)).mul (h₃ a₃ y)).mul (hE x y)).congr_deriv ?_
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [Pi.mul_apply]; ring

theorem hasDerivAt_spl13 (h₀ : ∀ i j, HasDerivAt (fun s => B₀ s i j) (D₀ i j) t)
    (h₁ : ∀ i j, HasDerivAt (fun s => B₁ s i j) (D₁ i j) t)
    (h₂ : ∀ i j, HasDerivAt (fun s => B₂ s i j) (D₂ i j) t)
    (h₃ : ∀ i j, HasDerivAt (fun s => B₃ s i j) (D₃ i j) t)
    (hE : ∀ i j, HasDerivAt (fun s => E s i j) (DE i j) t) :
    HasDerivAt (fun s => spl13 (B₀ s) (B₁ s) (B₂ s) (B₃ s) (E s) a₀ a₁ a₂ a₃)
      (spl13 D₀ (B₁ t) (B₂ t) (B₃ t) (E t) a₀ a₁ a₂ a₃
        + spl13 (B₀ t) D₁ (B₂ t) (B₃ t) (E t) a₀ a₁ a₂ a₃
        + spl13 (B₀ t) (B₁ t) D₂ (B₃ t) (E t) a₀ a₁ a₂ a₃
        + spl13 (B₀ t) (B₁ t) (B₂ t) D₃ (E t) a₀ a₁ a₂ a₃
        + spl13 (B₀ t) (B₁ t) (B₂ t) (B₃ t) DE a₀ a₁ a₂ a₃) t := by
  simp only [spl13]
  refine (HasDerivAt.fun_sum fun x _ => HasDerivAt.fun_sum fun y _ =>
    ((((h₀ a₀ x).mul (h₁ a₁ y)).mul (h₂ a₂ y)).mul (h₃ a₃ x)).mul (hE x y)).congr_deriv ?_
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [Pi.mul_apply]; ring

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

/-- `kFour` is `m_σ W⁻³` times the general tree sum of `RBM1D.Loop.Tree`. -/
theorem kFour_eq_treeSum (hL : 3 ≤ L) (W : ℕ) (m : Bool → ℂ) (t : ℝ) (s₀ s₁ s₂ s₃ : Bool)
    (a₀ a₁ a₂ a₃ : ZMod L) (h13 : ‖(t : ℂ) * (m s₁ * m s₃)‖ < 1) :
    kFour W m t s₀ s₁ s₂ s₃ a₀ a₁ a₂ a₃
      = (W : ℂ)⁻¹ ^ 3 * (m s₀ * m s₁ * m s₂ * m s₃) *
          treeSum L m t [s₀, s₁, s₂, s₃] [a₀, a₁, a₂, a₃] := by
  have h : treeSum L m t [s₀, s₁, s₂, s₃] [a₀, a₁, a₂, a₃]
      = gammaFour L m t ![s₀, s₁, s₂, s₃] ![a₀, a₁, a₂, a₃] :=
    treeSum_four L m t ![s₀, s₁, s₂, s₃] ![a₀, a₁, a₂, a₃] hL h13
  rw [kFour, h, gammaFour_eq]
  simp only [trees4, star4, starGamma, spl02, spl13, splitGamma₀₂, splitGamma₁₃,
    Fin.prod_univ_four, bd]
  rfl

theorem hasDerivAt_thetaEdge' (hL : 3 ≤ L) (m : Bool → ℂ) {t : ℝ} (s s' : Bool)
    (ht : ‖(t : ℂ) * (m s * m s')‖ < 1) (i j : ZMod L) :
    HasDerivAt (fun r : ℝ => thetaEdge L m r s s' i j)
      ((((m s * m s') • (thetaEdge L m t s s' * SB L)) * thetaEdge L m t s s') i j) t :=
  (hasDerivAt_thetaEdge hL m s s' ht i j).congr_deriv (by
    rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_comm])

theorem thetaEdge_apply_comm (hL : 3 ≤ L) (m : Bool → ℂ) {t : ℝ} (s s' : Bool)
    (ht : ‖(t : ℂ) * (m s * m s')‖ < 1) (i j : ZMod L) :
    thetaEdge L m t s s' i j = thetaEdge L m t s' s j i := by
  rw [thetaEdge_comm L m t s' s]
  have := congrFun (congrFun (Theta_transpose L hL ht) j) i
  simp only [Matrix.transpose_apply] at this
  rw [thetaEdge, this]

end KFour

end RBM
