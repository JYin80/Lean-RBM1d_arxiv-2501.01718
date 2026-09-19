/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Primitive
import RBM1D.Hierarchy.Kernel

/-!
# Section 5.2: the dynamics of `L - K`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, equations (5.12)-(5.15) (pp. 52-53).

The loop hierarchy (5.10) and the primitive equation (5.11) have the *same* quadratic
term, so subtracting them leaves only cross terms.  The quadratic term of (2.48) is
`RBM.primRhs`; what §5.2 needs is its polarization, the bilinear form `RBM.primBil`, for
which `primRhs K = primBil K K`.  Then, with `D = L - K`,

  `primRhs L - primRhs K = primBil K D + primBil D K + primBil D D`,

whose last summand is `E^{((L-K) x (L-K))}` of **(5.13)** and whose first two are the
`[K ~ (L-K)]` coupling of **(5.14)**.  Grading that coupling by the length of the `K`
factor and splitting off the `l_K = 2` piece is **(5.15)**; the `l_K = 2` piece is the one
that (5.19) identifies with the generator `Theta_{t,sigma}`.

Nothing here is stochastic: (5.10) itself is Ito's formula and stays a hypothesis, but
everything that happens *after* subtracting the two equations is algebra on `primRhs`.

## Main results

* `RBM.primBil`, `RBM.primBil_self`     : the polarization of `primRhs`
* `RBM.primRhs_sub`                     : **(5.12)**, **(5.13)**
* `RBM.primBilLen`, `RBM.sum_primBilLen`: **(5.14)**, the grading by `l_K`
* `RBM.primBil_eq_two_add`              : **(5.15)**, splitting off `l_K = 2`
-/

namespace RBM

open Matrix Finset

variable (L : ℕ) [NeZero L]

/-- The polarization of `primRhs`: the same sum with independent left and right factors. -/
noncomputable def primBil (W : ℕ) (K K' : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) : ℂ :=
  (W : ℂ) * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
    K (I.cutGlueL k l a) * SB L a b * K' (I.cutGlueR k l b)

@[simp] theorem primBil_self (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    primBil L W K K I = primRhs L W K I := rfl

theorem primBil_add_left (W : ℕ) (K₁ K₂ K' : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    primBil L W (K₁ + K₂) K' I = primBil L W K₁ K' I + primBil L W K₂ K' I := by
  simp only [primBil, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem primBil_add_right (W : ℕ) (K K₁ K₂ : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    primBil L W K (K₁ + K₂) I = primBil L W K K₁ I + primBil L W K K₂ I := by
  simp only [primBil, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem primBil_add_add (W : ℕ) (K D : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    primBil L W (K + D) (K + D) I
      = primBil L W K K I + primBil L W K D I + primBil L W D K I + primBil L W D D I := by
  rw [primBil_add_left, primBil_add_right, primBil_add_right]
  ring

/-- **(5.12) and (5.13)**: the loop hierarchy (5.10) and the primitive equation (5.11)
share their quadratic term, so their difference has exactly three summands.  The last one
is `E^{((L-K) x (L-K))}` of (5.13); the first two are the `[K ~ (L-K)]` coupling. -/
theorem primRhs_sub (W : ℕ) (Lf K : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    primRhs L W Lf I - primRhs L W K I
      = primBil L W K (Lf - K) I + primBil L W (Lf - K) K I
        + primBil L W (Lf - K) (Lf - K) I := by
  set D : LoopIdx (ZMod L) → ℂ := Lf - K with hD
  have hLf : Lf = K + D := by
    rw [hD]
    funext x
    simp
  have h1 : primRhs L W Lf I = primBil L W (K + D) (K + D) I := by
    rw [← primBil_self, hLf]
  rw [h1, primBil_add_add, ← primBil_self L W K I]
  ring

/-- **(5.14)**: the part of the coupling in which the *left* factor is a loop of length
`lK`.  In `primBil K D` the `K` factor is the left glue, so this grades the coupling by
the length of the `K`-loop, exactly as the paper's `[K ~ (L-K)]^{l_K}`. -/
noncomputable def primBilLen (W : ℕ) (lK : ℕ) (K K' : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) : ℂ :=
  (W : ℂ) * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
    (if (I.cutGlueL k l a).length = lK then
      K (I.cutGlueL k l a) * SB L a b * K' (I.cutGlueR k l b) else 0)

/-- Every `K`-loop occurring in the coupling has length at most `I.length`. -/
theorem length_cutGlueL_lt (I : LoopIdx (ZMod L)) {k l : ℕ} (hk : k ∈ Icc 1 I.length)
    (hl : l ∈ Ioc k I.length) (a : ZMod L) :
    (I.cutGlueL k l a).length < I.length + 2 := by
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  rw [LoopIdx.length_cutGlueL hk.1 hl.1 hl.2]
  omega

/-- Summing the graded pieces over every possible `l_K` recovers the whole coupling. -/
theorem sum_primBilLen (W : ℕ) (K K' : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, primBilLen L W lK K K' I = primBil L W K K' I := by
  simp only [primBilLen, primBil, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq (Finset.range N) ((I.cutGlueL k l a).length)
    (fun _ => K (I.cutGlueL k l a) * SB L a b * K' (I.cutGlueR k l b)),
    if_pos (Finset.mem_range.mpr (lt_of_lt_of_le (length_cutGlueL_lt L I hk hl a) hN))]

/-- **(5.15)**: splitting off the `l_K = 2` piece, which (5.19) identifies with the
generator `Theta_{t,sigma}`. -/
theorem primBil_eq_two_add (W : ℕ) (K K' : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    {N : ℕ} (hN : I.length + 2 ≤ N) (h2 : 2 ∈ Finset.range N) :
    primBil L W K K' I
      = primBilLen L W 2 K K' I
        + ∑ lK ∈ (Finset.range N).erase 2, primBilLen L W lK K K' I := by
  rw [← sum_primBilLen L W K K' I hN, ← Finset.add_sum_erase _ _ h2]

end RBM
