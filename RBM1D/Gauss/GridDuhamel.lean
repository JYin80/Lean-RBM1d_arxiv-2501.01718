/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Kernel

/-!
# The discrete Duhamel telescoping identity

This is the discrete replacement for Lemma 5.3 / (5.20)-(5.21) used by the discrete Duhamel
argument on the grid (`docs/PAPER-VS-LEAN.md` §5.2).

## Main results

* `RBM.Gauss.Grid.duhamel_telescope`         : the generic telescoping identity for any
  family of `AddMonoidHom`s satisfying the evolution-kernel laws (self + composition).
* `RBM.Gauss.Grid.UkerHom`                   : `RBM.Uker` bundled as an `AddMonoidHom`
  (it is additive by `RBM.Uker_add`).
* `RBM.Gauss.Grid.Uker_grid_semigroup`       : the family `fun j k => Uker ξ (u j) (u k)`
  satisfies the hypotheses of `duhamel_telescope`, for an arbitrary sequence `u : ℕ → ℝ` of
  grid times (this covers the concrete grid `time s t K N`).
-/

namespace RBM.Gauss.Grid

open Finset

section Telescope

variable {V : Type*} [AddCommGroup V]

/-- **(T1)**: the discrete Duhamel telescoping identity.  For a family `U j k : V →+ V`
satisfying the evolution-kernel laws `U k k = id` and `(U j k).comp (U i j) = U i k` for
`i ≤ j ≤ k`, and any sequence `A : ℕ → V`,
`A k - U 0 k (A 0) = ∑_{j < k} U (j+1) k (A (j+1) - U j (j+1) (A j))`. -/
theorem duhamel_telescope (U : ℕ → ℕ → V →+ V)
    (hself : ∀ k, U k k = AddMonoidHom.id V)
    (hcomp : ∀ i j k, i ≤ j → j ≤ k → (U j k).comp (U i j) = U i k)
    (A : ℕ → V) (k : ℕ) :
    A k - U 0 k (A 0) =
      ∑ j ∈ Finset.range k, U (j + 1) k (A (j + 1) - U j (j + 1) (A j)) := by
  induction k with
  | zero =>
      have h0 : U 0 0 (A 0) = A 0 := by rw [hself 0]; rfl
      simp [h0]
  | succ k ih =>
      have hrw : ∀ j ∈ Finset.range k,
          U (j + 1) (k + 1) (A (j + 1) - U j (j + 1) (A j))
            = U k (k + 1) (U (j + 1) k (A (j + 1) - U j (j + 1) (A j))) := by
        intro j hj
        have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
        have hcomp' := hcomp (j + 1) k (k + 1) hjk (Nat.le_succ k)
        rw [← hcomp']
        rfl
      have hsum : ∑ j ∈ Finset.range k, U (j + 1) (k + 1) (A (j + 1) - U j (j + 1) (A j))
          = U k (k + 1) (A k - U 0 k (A 0)) := by
        rw [ih]
        rw [map_sum (U k (k+1))]
        exact Finset.sum_congr rfl (fun j hj => hrw j hj)
      have htail : U (k + 1) (k + 1) (A (k + 1) - U k (k + 1) (A k))
          = A (k + 1) - U k (k + 1) (A k) := by rw [hself (k+1)]; rfl
      have hfront : U k (k + 1) (A k - U 0 k (A 0))
          = U k (k + 1) (A k) - U 0 (k + 1) (A 0) := by
        rw [map_sub]
        have := hcomp 0 k (k + 1) (Nat.zero_le k) (Nat.le_succ k)
        rw [show U k (k+1) (U 0 k (A 0)) = (U k (k+1)).comp (U 0 k) (A 0) from rfl, this]
      rw [Finset.sum_range_succ, hsum, hfront, htail]
      abel

end Telescope

section Stopped

variable {V : Type*} [AddCommGroup V]

end Stopped

section UkerBundled

variable (L : ℕ) [NeZero L]

/-- The repo's `RBM.Uker` bundled as an `AddMonoidHom`, using its additivity `RBM.Uker_add`. -/
noncomputable def UkerHom {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ) :
    (LoopArg L n → ℂ) →+ (LoopArg L n → ℂ) :=
  AddMonoidHom.mk' (Uker L ξ s t) (Uker_add L ξ s t)

@[simp] theorem UkerHom_apply {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ) (A : LoopArg L n → ℂ) :
    UkerHom L ξ s t A = Uker L ξ s t A := rfl

/-- **`Uker_grid_semigroup`**: the family `fun j k => Uker ξ (u j) (u k)` (bundled) satisfies the
hypotheses of `duhamel_telescope`, for an arbitrary sequence of real "grid times"
`u : ℕ → ℝ`. -/
theorem Uker_grid_semigroup (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} (u : ℕ → ℝ)
    (hu : ∀ k i, ‖(u k : ℂ) * ξ i‖ < 1) :
    (∀ k, UkerHom L ξ (u k : ℂ) (u k : ℂ) = AddMonoidHom.id (LoopArg L n → ℂ)) ∧
      (∀ i j k, i ≤ j → j ≤ k →
        (UkerHom L ξ (u j : ℂ) (u k : ℂ)).comp (UkerHom L ξ (u i : ℂ) (u j : ℂ))
          = UkerHom L ξ (u i : ℂ) (u k : ℂ)) := by
  constructor
  · intro k
    apply AddMonoidHom.ext
    intro A
    rw [AddMonoidHom.id_apply, UkerHom_apply]
    exact Uker_self L hL (hu k) A
  · intro i j k _ hjk
    apply AddMonoidHom.ext
    intro A
    rw [AddMonoidHom.comp_apply, UkerHom_apply, UkerHom_apply, UkerHom_apply]
    exact Uker_comp L hL (hu j) (hu k) A

end UkerBundled

end RBM.Gauss.Grid
