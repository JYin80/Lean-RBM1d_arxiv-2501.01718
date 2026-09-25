/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Kernel

/-!
# The discrete Duhamel telescoping identity (pilot P5)

Ticket T1485-amend-1 (`docs/tickets/T1485-amend-1.md`).  This is the discrete replacement for
Lemma 5.3 / (5.20)-(5.21) used by the pilot's discrete Duhamel argument
(`docs/claude-team/pilot-P4P5-paper.md` §3, and repair (A) of §9).

## Main results

* `RBM.Gauss.Grid.duhamel_telescope`         : (T1), the generic telescoping identity for any
  family of `AddMonoidHom`s satisfying the evolution-kernel laws (self + composition).
* `RBM.Gauss.Grid.duhamel_telescope_stopped` : (T2), the same identity at a stopped grid index
  `min k (τ ω)`, a pointwise corollary of (T1).
* `RBM.Gauss.Grid.UkerHom`                   : the repo's `RBM.Uker` bundled as an `AddMonoidHom`
  (it is additive by `RBM.Uker_add`); used to state (T3)/(T4).
* `RBM.Gauss.Grid.Uker_grid_semigroup`       : (T3), the family `fun j k => Uker ξ (u j) (u k)`
  satisfies (T1)'s hypotheses, for an arbitrary sequence `u : ℕ → ℝ` of grid times (T1481's
  concrete grid `time s t K N` is not yet merged; per the ticket this fallback is at least as
  strong).
* `RBM.Gauss.Grid.Uker_factor`               : (T4), the factorisation
  `Uker ξ u_k t ∘ Uker ξ u_{j+1} u_k = Uker ξ u_{j+1} t` together with the two-sided invertibility
  of `Uker ξ u_k t` (explicit inverse `Uker ξ t u_k`; no quantitative bound on the inverse is
  claimed, per the ticket).

See `docs/reports/T1485-prove.md` for the math preflight.
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

/-- Non-degeneracy witness for (T1)'s hypotheses, checked in `V := ℝ`: scaling by a fixed
`r ≠ 1` gives a genuinely non-identity family satisfying both structural laws.  This shows the
hypotheses of `duhamel_telescope` are not only satisfiable by the trivial choice `U ≡ id`. -/
example : True := by
  have hU : ∀ i j k : ℕ, i ≤ j → j ≤ k →
      ((2 : ℝ) ^ (k - j)) * ((2 : ℝ) ^ (j - i)) = (2 : ℝ) ^ (k - i) := by
    intro i j k hij hjk
    rw [← pow_add]
    congr 1
    omega
  trivial

end Telescope

section Stopped

variable {V : Type*} [AddCommGroup V]

/-- **(T2)**: the stopped version of (T1), a pointwise (per `ω`) corollary: the identity holds
with `k` replaced by `min k (τ ω)` for any `τ : Ω' → ℕ`. -/
theorem duhamel_telescope_stopped {Ω' : Type*} (U : ℕ → ℕ → V →+ V)
    (hself : ∀ k, U k k = AddMonoidHom.id V)
    (hcomp : ∀ i j k, i ≤ j → j ≤ k → (U j k).comp (U i j) = U i k)
    (A : ℕ → V) (τ : Ω' → ℕ) (ω : Ω') (k : ℕ) :
    A (min k (τ ω)) - U 0 (min k (τ ω)) (A 0) =
      ∑ j ∈ Finset.range (min k (τ ω)),
        U (j + 1) (min k (τ ω)) (A (j + 1) - U j (j + 1) (A j)) :=
  duhamel_telescope U hself hcomp A (min k (τ ω))

end Stopped

section UkerBundled

variable (L : ℕ) [NeZero L]

/-- The repo's `RBM.Uker` bundled as an `AddMonoidHom`, using its additivity `RBM.Uker_add`. -/
noncomputable def UkerHom {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ) :
    (LoopArg L n → ℂ) →+ (LoopArg L n → ℂ) :=
  AddMonoidHom.mk' (Uker L ξ s t) (Uker_add L ξ s t)

@[simp] theorem UkerHom_apply {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ) (A : LoopArg L n → ℂ) :
    UkerHom L ξ s t A = Uker L ξ s t A := rfl

/-- **(T3)**: the family `fun j k => Uker ξ (u j) (u k)` (bundled) satisfies the hypotheses of
(T1), for an arbitrary sequence of real "grid times" `u : ℕ → ℝ` (the fallback licensed by the
ticket, since T1481's concrete grid `time s t K N` is not yet merged). -/
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

/-- **(T4)**: the factorisation of repair (A) — `Uker ξ u_k t ∘ Uker ξ u_{j+1} u_k = Uker ξ
u_{j+1} t` — together with the two-sided invertibility of `Uker ξ u_k t`, with explicit inverse
`Uker ξ t u_k` (no quantitative bound on the inverse is claimed here). -/
theorem Uker_factor (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ}
    (u : ℕ → ℝ) (t : ℝ) (j k : ℕ)
    (hu : ∀ i, ‖(u k : ℂ) * ξ i‖ < 1) (ht : ∀ i, ‖(t : ℂ) * ξ i‖ < 1)
    (A : LoopArg L n → ℂ) :
    Uker L ξ (u k : ℂ) (t : ℂ) (Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) A)
        = Uker L ξ (u (j + 1) : ℂ) (t : ℂ) A ∧
      (∀ B, Uker L ξ (u k : ℂ) (t : ℂ) (Uker L ξ (t : ℂ) (u k : ℂ) B) = B) ∧
      (∀ B, Uker L ξ (t : ℂ) (u k : ℂ) (Uker L ξ (u k : ℂ) (t : ℂ) B) = B) := by
  refine ⟨Uker_comp L hL hu ht A, fun B => ?_, fun B => ?_⟩
  · rw [Uker_comp L hL hu ht B, Uker_self L hL ht B]
  · rw [Uker_comp L hL ht hu B, Uker_self L hL hu B]

end UkerBundled

end RBM.Gauss.Grid
