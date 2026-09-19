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
  simp only [star4, Matrix.mul_apply, Finset.mul_sum]
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

section Assembly

variable {L} (W : ℕ) [NeZero W] (m : Bool → ℂ) (t : ℝ) (s₀ s₁ s₂ s₃ : Bool)
  (a₀ a₁ a₂ a₃ : ZMod L)

/-- The prefactor `m₀m₁m₂m₃ W⁻³` of (3.5) at `n = 4`. -/
local notation "c₄" => (W : ℂ)⁻¹ ^ 3 * (m s₀ * m s₁ * m s₂ * m s₃)

/-- `Θ` edges at time `t`. -/
local notation "Θe" => thetaEdge L m t

omit [NeZero W] in
theorem sum_mul_kFour_slot0 (M : Matrix (ZMod L) (ZMod L) ℂ) :
    ∑ x : ZMod L, M a₀ x * kFour W m t s₀ s₁ s₂ s₃ x a₁ a₂ a₃
      = c₄ * trees4 (M * Θe s₀ s₁) (Θe s₁ s₂) (Θe s₂ s₃) (Θe s₃ s₀) (Θe s₀ s₂) (Θe s₁ s₃)
          a₀ a₁ a₂ a₃ := by
  rw [← trees4_slot0, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by rw [kFour]; ring

omit [NeZero W] in
theorem sum_mul_kFour_slot1 (M : Matrix (ZMod L) (ZMod L) ℂ) :
    ∑ x : ZMod L, M a₁ x * kFour W m t s₀ s₁ s₂ s₃ a₀ x a₂ a₃
      = c₄ * trees4 (Θe s₀ s₁) (M * Θe s₁ s₂) (Θe s₂ s₃) (Θe s₃ s₀) (Θe s₀ s₂) (Θe s₁ s₃)
          a₀ a₁ a₂ a₃ := by
  rw [← trees4_slot1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by rw [kFour]; ring

omit [NeZero W] in
theorem sum_mul_kFour_slot2 (M : Matrix (ZMod L) (ZMod L) ℂ) :
    ∑ x : ZMod L, M a₂ x * kFour W m t s₀ s₁ s₂ s₃ a₀ a₁ x a₃
      = c₄ * trees4 (Θe s₀ s₁) (Θe s₁ s₂) (M * Θe s₂ s₃) (Θe s₃ s₀) (Θe s₀ s₂) (Θe s₁ s₃)
          a₀ a₁ a₂ a₃ := by
  rw [← trees4_slot2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by rw [kFour]; ring

omit [NeZero W] in
theorem sum_mul_kFour_slot3 (M : Matrix (ZMod L) (ZMod L) ℂ) :
    ∑ x : ZMod L, M a₃ x * kFour W m t s₀ s₁ s₂ s₃ a₀ a₁ a₂ x
      = c₄ * trees4 (Θe s₀ s₁) (Θe s₁ s₂) (Θe s₂ s₃) (M * Θe s₃ s₀) (Θe s₀ s₂) (Θe s₁ s₃)
          a₀ a₁ a₂ a₃ := by
  rw [← trees4_slot3, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by rw [kFour]; ring

theorem thetaEdge_apply_symm (hL : 3 ≤ L) {s s' : Bool} (ht : ‖(t : ℂ) * (m s * m s')‖ < 1)
    (i j : ZMod L) : Θe s s' i j = Θe s s' j i := by
  rw [thetaEdge_apply_comm hL m s s' ht, thetaEdge_comm]

/-- **Internal edge `(0, 2)` ↔ the term `(k, l) = (1, 3)`.** -/
theorem term13_eq (hL : 3 ≤ L) (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1) :
    (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L,
        kThree W m t s₀ s₂ s₃ x a₂ a₃ * SB L x y * kThree W m t s₀ s₁ s₂ a₀ a₁ y
      = c₄ * spl02 (Θe s₀ s₁) (Θe s₁ s₂) (Θe s₂ s₃) (Θe s₃ s₀)
          (((m s₀ * m s₂) • (Θe s₀ s₂ * SB L)) * Θe s₀ s₂) a₀ a₁ a₂ a₃ := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  set F : ZMod L → ℂ := fun u => ∑ x : ZMod L, Θe s₀ s₁ a₀ x * Θe s₁ s₂ a₁ x * Θe s₀ s₂ x u
  set G : ZMod L → ℂ := fun v => ∑ y : ZMod L, Θe s₀ s₂ v y * (Θe s₂ s₃ a₂ y * Θe s₃ s₀ a₃ y)
  have k1 : ∀ u, kThree W m t s₀ s₁ s₂ a₀ a₁ u = (W : ℂ)⁻¹ ^ 2 * (m s₀ * m s₁ * m s₂) * F u := by
    intro u
    simp only [kThree, F]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [thetaEdge_apply_comm hL m s₂ s₀ (hm _ _) u b]
  have k2 : ∀ v, kThree W m t s₀ s₂ s₃ v a₂ a₃ = (W : ℂ)⁻¹ ^ 2 * (m s₀ * m s₂ * m s₃) * G v := by
    intro v
    simp only [kThree, G]
    congr 1
    exact Finset.sum_congr rfl fun b _ => by ring
  have key : spl02 (Θe s₀ s₁) (Θe s₁ s₂) (Θe s₂ s₃) (Θe s₃ s₀)
      (((m s₀ * m s₂) • (Θe s₀ s₂ * SB L)) * Θe s₀ s₂) a₀ a₁ a₂ a₃
      = (m s₀ * m s₂) * ∑ u : ZMod L, ∑ v : ZMod L, F u * SB L u v * G v := by
    simp only [F, G]
    rw [← sum_bilin (Θe s₀ s₂) (SB L) (fun x => Θe s₀ s₁ a₀ x * Θe s₁ s₂ a₁ x)
      (fun y => Θe s₂ s₃ a₂ y * Θe s₃ s₀ a₃ y), Finset.mul_sum]
    simp only [spl02, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [key]
  calc (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L,
        kThree W m t s₀ s₂ s₃ x a₂ a₃ * SB L x y * kThree W m t s₀ s₁ s₂ a₀ a₁ y
      = (W : ℂ) * ∑ u : ZMod L, ∑ v : ZMod L,
          ((W : ℂ)⁻¹ ^ 2 * (m s₀ * m s₁ * m s₂) * ((W : ℂ)⁻¹ ^ 2 * (m s₀ * m s₂ * m s₃)))
            * (F u * SB L u v * G v) := by
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
          rw [k1, k2, SB_apply_comm L v u]; ring
    _ = c₄ * ((m s₀ * m s₂) * ∑ u : ZMod L, ∑ v : ZMod L, F u * SB L u v * G v) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
          field_simp

/-- **Internal edge `(1, 3)` ↔ the term `(k, l) = (2, 4)`.** -/
theorem term24_eq (hL : 3 ≤ L) (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1) :
    (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L,
        kThree W m t s₀ s₁ s₃ a₀ x a₃ * SB L x y * kThree W m t s₁ s₂ s₃ a₁ a₂ y
      = c₄ * spl13 (Θe s₀ s₁) (Θe s₁ s₂) (Θe s₂ s₃) (Θe s₃ s₀)
          (((m s₁ * m s₃) • (Θe s₁ s₃ * SB L)) * Θe s₁ s₃) a₀ a₁ a₂ a₃ := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  set F : ZMod L → ℂ := fun u => ∑ x : ZMod L, Θe s₀ s₁ a₀ x * Θe s₃ s₀ a₃ x * Θe s₁ s₃ x u
  set G : ZMod L → ℂ := fun v => ∑ y : ZMod L, Θe s₁ s₃ v y * (Θe s₁ s₂ a₁ y * Θe s₂ s₃ a₂ y)
  have k1 : ∀ u, kThree W m t s₀ s₁ s₃ a₀ u a₃ = (W : ℂ)⁻¹ ^ 2 * (m s₀ * m s₁ * m s₃) * F u := by
    intro u
    simp only [kThree, F]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [thetaEdge_apply_symm m t hL (hm s₁ s₃) u b]; ring
  have k2 : ∀ v, kThree W m t s₁ s₂ s₃ a₁ a₂ v = (W : ℂ)⁻¹ ^ 2 * (m s₁ * m s₂ * m s₃) * G v := by
    intro v
    simp only [kThree, G]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [thetaEdge_comm L m t s₃ s₁]; ring
  have key : spl13 (Θe s₀ s₁) (Θe s₁ s₂) (Θe s₂ s₃) (Θe s₃ s₀)
      (((m s₁ * m s₃) • (Θe s₁ s₃ * SB L)) * Θe s₁ s₃) a₀ a₁ a₂ a₃
      = (m s₁ * m s₃) * ∑ u : ZMod L, ∑ v : ZMod L, F u * SB L u v * G v := by
    simp only [F, G]
    rw [← sum_bilin (Θe s₁ s₃) (SB L) (fun x => Θe s₀ s₁ a₀ x * Θe s₃ s₀ a₃ x)
      (fun y => Θe s₁ s₂ a₁ y * Θe s₂ s₃ a₂ y), Finset.mul_sum]
    simp only [spl13, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [key]
  calc (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L,
        kThree W m t s₀ s₁ s₃ a₀ x a₃ * SB L x y * kThree W m t s₁ s₂ s₃ a₁ a₂ y
      = (W : ℂ) * ∑ u : ZMod L, ∑ v : ZMod L,
          ((W : ℂ)⁻¹ ^ 2 * (m s₀ * m s₁ * m s₃) * ((W : ℂ)⁻¹ ^ 2 * (m s₁ * m s₂ * m s₃)))
            * (F u * SB L u v * G v) := by
        congr 1
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
          rw [k1, k2]; ring
    _ = c₄ * ((m s₁ * m s₃) * ∑ u : ZMod L, ∑ v : ZMod L, F u * SB L u v * G v) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
          field_simp

/-- **Lemma 3.4 at `n = 4`**: the tree representation solves (2.48).  The six terms are
the four boundary edges (`2`-chains) and the two internal edges (pairs of `3`-chains). -/
theorem hasDerivAt_kFour (hL : 3 ≤ L) (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1) :
    HasDerivAt (fun r => kFour W m r s₀ s₁ s₂ s₃ a₀ a₁ a₂ a₃)
      ((W : ℂ) * ((∑ x : ZMod L, ∑ y : ZMod L,
            kFour W m t s₀ s₁ s₂ s₃ x a₁ a₂ a₃ * SB L x y * kTwo L W m t s₀ s₁ a₀ y)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            kThree W m t s₀ s₂ s₃ x a₂ a₃ * SB L x y * kThree W m t s₀ s₁ s₂ a₀ a₁ y)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            kTwo L W m t s₀ s₃ x a₃ * SB L x y * kFour W m t s₀ s₁ s₂ s₃ a₀ a₁ a₂ y)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            kFour W m t s₀ s₁ s₂ s₃ a₀ x a₂ a₃ * SB L x y * kTwo L W m t s₁ s₂ a₁ y)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            kThree W m t s₀ s₁ s₃ a₀ x a₃ * SB L x y * kThree W m t s₁ s₂ s₃ a₁ a₂ y)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            kFour W m t s₀ s₁ s₂ s₃ a₀ a₁ x a₃ * SB L x y * kTwo L W m t s₂ s₃ a₂ y))) t := by
  have hB : ∀ (s s' : Bool) (i j : ZMod L), HasDerivAt (fun r : ℝ => thetaEdge L m r s s' i j)
      ((((m s * m s') • (Θe s s' * SB L)) * Θe s s') i j) t :=
    fun s s' => hasDerivAt_thetaEdge' hL m s s' (hm s s')
  have hE : ∀ (s s' : Bool) (i j : ZMod L),
      HasDerivAt (fun r : ℝ => (thetaEdge L m r s s' - 1) i j)
        ((((m s * m s') • (Θe s s' * SB L)) * Θe s s') i j) t :=
    fun s s' i j => by simpa using (hB s s' i j).sub_const ((1 : Matrix (ZMod L) (ZMod L) ℂ) i j)
  have hd := (((hasDerivAt_star4 a₀ a₁ a₂ a₃ (hB s₀ s₁) (hB s₁ s₂) (hB s₂ s₃) (hB s₃ s₀)).add
    (hasDerivAt_spl02 a₀ a₁ a₂ a₃ (hB s₀ s₁) (hB s₁ s₂) (hB s₂ s₃) (hB s₃ s₀) (hE s₀ s₂))).add
    (hasDerivAt_spl13 a₀ a₁ a₂ a₃ (hB s₀ s₁) (hB s₁ s₂) (hB s₂ s₃) (hB s₃ s₀)
      (hE s₁ s₃))).const_mul c₄
  refine hd.congr_deriv ?_
  -- rewrite the six terms of (2.48)
  have h14 : (m s₀ * m s₃) • (Θe s₃ s₀ * SB L) = (m s₃ * m s₀) • (Θe s₃ s₀ * SB L) := by
    rw [mul_comm]
  simp only [mul_add]
  rw [rhs_kTwo_left W m t s₀ s₁ a₀ (fun x => kFour W m t s₀ s₁ s₂ s₃ x a₁ a₂ a₃),
    rhs_kTwo_left W m t s₁ s₂ a₁ (fun x => kFour W m t s₀ s₁ s₂ s₃ a₀ x a₂ a₃),
    rhs_kTwo_left W m t s₂ s₃ a₂ (fun x => kFour W m t s₀ s₁ s₂ s₃ a₀ a₁ x a₃),
    rhs_kTwo_right W m t hL s₀ s₃ (hm _ _) a₃ (fun y => kFour W m t s₀ s₁ s₂ s₃ a₀ a₁ a₂ y),
    h14, sum_mul_kFour_slot0, sum_mul_kFour_slot1, sum_mul_kFour_slot2, sum_mul_kFour_slot3,
    term13_eq W m t s₀ s₁ s₂ s₃ a₀ a₁ a₂ a₃ hL hm, term24_eq W m t s₀ s₁ s₂ s₃ a₀ a₁ a₂ a₃ hL hm]
  simp only [trees4]
  ring

omit [NeZero W] in
/-- At `t = 0`, `kFour` is the initial value of Definition 2.12 for `n = 4`. -/
theorem kFour_zero :
    kFour W m 0 s₀ s₁ s₂ s₃ a₀ a₁ a₂ a₃ = primInit L W m ⟨[s₀, s₁, s₂, s₃], [a₀, a₁, a₂, a₃]⟩ := by
  have hΘ : ∀ s s' : Bool, thetaEdge L m 0 s s' = 1 := by
    intro s s'; simp [thetaEdge, Theta_zero]
  have hstar : star4 (1 : Matrix (ZMod L) (ZMod L) ℂ) 1 1 1 a₀ a₁ a₂ a₃
      = if a₁ = a₀ ∧ a₂ = a₀ ∧ a₃ = a₀ then 1 else 0 := by
    simp only [star4, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    by_cases h1 : a₁ = a₀ <;> by_cases h2 : a₂ = a₀ <;> by_cases h3 : a₃ = a₀ <;> simp [h1, h2, h3]
  have hall : (∀ x ∈ [a₀, a₁, a₂, a₃], ∀ y ∈ [a₀, a₁, a₂, a₃], x = y)
      ↔ (a₁ = a₀ ∧ a₂ = a₀ ∧ a₃ = a₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨-, h1, h2, h3⟩, -⟩
      exact ⟨h1.symm, h2.symm, h3.symm⟩
    · rintro ⟨rfl, rfl, rfl⟩
      simp
  rw [kFour, hΘ, hΘ, hΘ, hΘ, hΘ, hΘ, trees4, hstar, sub_self]
  simp only [spl02, spl13, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
    primInit, LoopIdx.length, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, hall]
  split_ifs <;> ring

/-- Examples 2.15, 2.16 and the `n = 4` tree representation as one function of the loop. -/
noncomputable def kLoop4 (W : ℕ) (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (ZMod L)) : ℂ :=
  match I.σ, I.a with
  | [σ₁, σ₂], [x₁, x₂] => kTwo L W m t σ₁ σ₂ x₁ x₂
  | [σ₁, σ₂, σ₃], [x₁, x₂, x₃] => kThree W m t σ₁ σ₂ σ₃ x₁ x₂ x₃
  | [σ₀, σ₁, σ₂, σ₃], [x₀, x₁, x₂, x₃] => kFour W m t σ₀ σ₁ σ₂ σ₃ x₀ x₁ x₂ x₃
  | _, _ => 0

/-- **Lemma 3.4 at `n = 4`, general form**: `kLoop4` satisfies (2.48) on loops of length `4`,
with the right-hand side built from the cut-and-glue operators. -/
theorem hasDerivAt_kLoop4 (hL : 3 ≤ L) (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1) :
    HasDerivAt (fun r => kLoop4 W m r ⟨[s₀, s₁, s₂, s₃], [a₀, a₁, a₂, a₃]⟩)
      (primRhs L W (kLoop4 W m t) ⟨[s₀, s₁, s₂, s₃], [a₀, a₁, a₂, a₃]⟩) t := by
  rw [primRhs_four]
  exact hasDerivAt_kFour W m t s₀ s₁ s₂ s₃ a₀ a₁ a₂ a₃ hL hm

end Assembly

section Uniqueness

variable {L}

/-- `kThree` is `m_σ W⁻²` times the general tree sum (`T_SP(3) = {∅}`, the star). -/
theorem kThree_eq_treeSum (W : ℕ) (m : Bool → ℂ) (t : ℝ) (s₁ s₂ s₃ : Bool) (a₁ a₂ a₃ : ZMod L) :
    kThree W m t s₁ s₂ s₃ a₁ a₂ a₃
      = (W : ℂ)⁻¹ ^ 2 * (m s₁ * m s₂ * m s₃) * treeSum L m t [s₁, s₂, s₃] [a₁, a₂, a₃] := by
  have hlen : [s₁, s₂, s₃].length = 3 := rfl
  have hbd : bdList L m t [s₁, s₂, s₃] [a₁, a₂, a₃]
      = [(a₁, thetaEdge L m t s₁ s₂), (a₂, thetaEdge L m t s₂ s₃),
          (a₃, thetaEdge L m t s₃ s₁)] := by
    simp only [bdList, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil]
    rfl
  rw [treeSum, hlen, TSP_three, Finset.sum_singleton, diagList_empty, treeVal,
    ite_eq_right (by simp), hbd, polyVal, kThree]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]

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

/-- `kLoop4` satisfies (2.48) on every loop of length `2`, `3` or `4`. -/
theorem hasDerivAt_kLoop4_of_le (hL : 3 ≤ L) {t : ℝ}
    (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1) {I : LoopIdx (ZMod L)} (hI : I.WF)
    (h2 : 2 ≤ I.length) (h4 : I.length ≤ 4) :
    HasDerivAt (fun r => kLoop4 W m r I) (primRhs L W (kLoop4 W m t) I) t := by
  rcases loop_cases hI h2 h4 with ⟨s₁, s₂, x₁, x₂, rfl⟩ | ⟨s₁, s₂, s₃, x₁, x₂, x₃, rfl⟩ |
    ⟨s₀, s₁, s₂, s₃, x₀, x₁, x₂, x₃, rfl⟩
  · rw [primRhs_two]
    exact hasDerivAt_kTwo L hL W m s₁ s₂ (hm _ _) x₁ x₂
  · rw [primRhs_three]
    exact hasDerivAt_kThree hL W m s₁ s₂ s₃ (hm _ _) (hm _ _) (hm _ _) x₁ x₂ x₃
  · exact hasDerivAt_kLoop4 W m t s₀ s₁ s₂ s₃ x₀ x₁ x₂ x₃ hL hm

omit [NeZero W] in
/-- `kLoop4` has the initial value of Definition 2.12 on loops of length `2`, `3`, `4`. -/
theorem kLoop4_zero_of_le {I : LoopIdx (ZMod L)} (hI : I.WF) (h2 : 2 ≤ I.length)
    (h4 : I.length ≤ 4) : kLoop4 W m 0 I = primInit L W m I := by
  rcases loop_cases hI h2 h4 with ⟨s₁, s₂, x₁, x₂, rfl⟩ | ⟨s₁, s₂, s₃, x₁, x₂, x₃, rfl⟩ |
    ⟨s₀, s₁, s₂, s₃, x₀, x₁, x₂, x₃, rfl⟩
  · exact kTwo_zero L W m s₁ s₂ x₁ x₂
  · exact kThree_zero W m s₁ s₂ s₃ x₁ x₂ x₃
  · exact kFour_zero W m s₀ s₁ s₂ s₃ x₀ x₁ x₂ x₃

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

/-- **Lemma 3.4 for `n ≤ 4`.**  Every solution `K` of Definition 2.12 on `[0, T₀]`, `T₀ < 1`,
with bounded `2`-loops and `|m| ≤ 1`, is given on loops of length `2, 3, 4` by the tree
formula `kLoop4`. -/
theorem eq_kLoop4_of_isPrimitive (hL : 3 ≤ L) (hm1 : ∀ s, ‖m s‖ ≤ 1) {T : Set ℝ}
    {K : ℝ → LoopIdx (ZMod L) → ℂ} (hK : IsPrimitive L W m T K) {T₀ R : ℝ} (hT₀ : T₀ < 1)
    (hT : Set.Icc 0 T₀ ⊆ T)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length → I.length ≤ 4 →
      K t I = kLoop4 W m t I := by
  set R' := max R ((W : ℝ)⁻¹ * (1 - T₀)⁻¹) with hR'
  have hR'0 : 0 ≤ R' := le_trans (by have : 0 < 1 - T₀ := by linarith
                                     positivity) (le_max_right _ _)
  have hbound : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 →
      ‖K t I‖ ≤ R' ∧ ‖kLoop4 W m t I‖ ≤ R' := fun t ht I hI h2 =>
    ⟨(hR t ht I hI h2).trans (le_max_left _ _),
      (norm_kLoop4_two_le W m hL hm1 ht hT₀ hI h2).trans (le_max_right _ _)⟩
  have hmt : ∀ t ∈ Set.Icc 0 T₀, ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1 :=
    fun t ht s s' => (norm_mul_le_of_mem_Icc m hm1 ht s s').trans_lt hT₀
  have main : ∀ n : ℕ, n ≤ 4 → ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF →
      2 ≤ I.length → I.length = n → K t I = kLoop4 W m t I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn4 t ht I hI h2 hIn
      have hn : 2 ≤ n := hIn ▸ h2
      refine eq_on_level L hL W K (kLoop4 W m) T₀ R' n hR'0
        (fun s hs J hJ hJn => hK.1 s (hT hs) J hJ (hJn ▸ hn))
        (fun s hs J hJ hJn => hasDerivAt_kLoop4_of_le W m hL (hmt s hs) hJ (hJn ▸ hn)
          (hJn ▸ hn4))
        hbound ?_ ?_ t ht I hI hIn
      · intro s hs J hJ hJ2 hJn
        exact ih _ hJn (by omega) s hs J hJ hJ2 rfl
      · intro J hJ hJn
        rw [hK.2.1 J hJ (hJn ▸ hn), kLoop4_zero_of_le W m hJ (hJn ▸ hn) (hJn ▸ hn4)]
  exact fun t ht I hI h2 h4 => main _ h4 t ht I hI h2 rfl

/-- **Lemma 3.4, (3.5), for `n ≤ 4`, in the paper's form**:
`K_{t,σ,a} = m_σ W^{-n+1} ∑_{Γ ∈ T_SP(P_a)} Γ_a(t, σ)`. -/
theorem treeRep_of_isPrimitive (hL : 3 ≤ L) (hm1 : ∀ s, ‖m s‖ ≤ 1) {T : Set ℝ}
    {K : ℝ → LoopIdx (ZMod L) → ℂ} (hK : IsPrimitive L W m T K) {T₀ R : ℝ} (hT₀ : T₀ < 1)
    (hT : Set.Icc 0 T₀ ⊆ T)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length → I.length ≤ 4 →
      K t I = (I.σ.map m).prod * (W : ℂ)⁻¹ ^ (I.length - 1) * treeSum L m t I.σ I.a := by
  intro t ht I hI h2 h4
  rw [eq_kLoop4_of_isPrimitive W m hL hm1 hK hT₀ hT hR t ht I hI h2 h4]
  have hmt : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1 :=
    fun s s' => (norm_mul_le_of_mem_Icc m hm1 ht s s').trans_lt hT₀
  rcases loop_cases hI h2 h4 with ⟨s₁, s₂, x₁, x₂, rfl⟩ | ⟨s₁, s₂, s₃, x₁, x₂, x₃, rfl⟩ |
    ⟨s₀, s₁, s₂, s₃, x₀, x₁, x₂, x₃, rfl⟩
  · change kTwo L W m t s₁ s₂ x₁ x₂ = _
    rw [kTwo_eq_treeSum]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, LoopIdx.length,
      List.length_cons, List.length_nil]
    ring
  · change kThree W m t s₁ s₂ s₃ x₁ x₂ x₃ = _
    rw [kThree_eq_treeSum]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, LoopIdx.length,
      List.length_cons, List.length_nil]
    ring
  · change kFour W m t s₀ s₁ s₂ s₃ x₀ x₁ x₂ x₃ = _
    rw [kFour_eq_treeSum hL W m t s₀ s₁ s₂ s₃ x₀ x₁ x₂ x₃ (hmt _ _)]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, LoopIdx.length,
      List.length_cons, List.length_nil]
    ring

end Uniqueness

end RBM
