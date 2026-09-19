/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.WardInd
import RBM1D.Loop.Primitive

/-!
# The derivative identity behind Ward's identity at general `n`

Toward (3.18).  Fix `K : LoopIdx (ZMod L) → ℂ` (the primitive loop at a fixed time) and write
`N = |a'| = n - 1`.  This file rearranges `∑_x (2.48)(fullLoop μ a' x)` according to the cuts,
using the index identities of `RBM1D.Loop.WardInd`.
-/

namespace RBM

open Finset LoopIdx

variable (L : ℕ) [NeZero L]

/-- `∑_x K_{(+,μ,-),(a',x)}`: the left-hand side of (3.13). -/
noncomputable def wStar (K : LoopIdx (ZMod L) → ℂ) (μ : List Bool) (a' : List (ZMod L)) : ℂ :=
  ∑ x : ZMod L, K (fullLoop μ a' x)

/-- The difference of the two sides of (3.13), with `κ = (2 W i η_t)⁻¹`. -/
noncomputable def wD (K : LoopIdx (ZMod L) → ℂ) (κ : ℂ) (μ : List Bool) (a' : List (ZMod L)) :
    ℂ :=
  wStar L K μ a' - κ * (K (pmLoop true μ a') - K (pmLoop false μ a'))

/-- The `x`-summed right-hand side of (2.48) at `fullLoop μ a' x`, split into the cuts with
`l ≤ N` and the cuts `(k, N + 1)`; the right chains do not depend on `x`. -/
theorem sum_primRhs_fullLoop (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (μ : List Bool)
    (a' : List (ZMod L)) (hμ : μ.length + 1 = a'.length) :
    ∑ x : ZMod L, primRhs L W K (fullLoop μ a' x) = (W : ℂ) *
      (∑ k ∈ Icc 1 a'.length, ∑ l ∈ Ioc k a'.length, ∑ a : ZMod L, ∑ b : ZMod L,
          (∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
            K ((fullLoop μ a' 0).cutGlueR k l b)
        + ∑ k ∈ Icc 1 a'.length, ∑ a : ZMod L, ∑ b : ZMod L,
          (∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k (a'.length + 1) a)) * SB L a b *
            K ((fullLoop μ a' 0).cutGlueR k (a'.length + 1) b)) := by
  have hlen : ∀ x : ZMod L, (fullLoop μ a' x).length = a'.length + 1 := fun x => by
    simp [fullLoop, LoopIdx.length]
  -- the right chain does not depend on `x`
  have hR : ∀ x : ZMod L, ∀ k l, 1 ≤ k → k < l → l ≤ a'.length + 1 → ∀ b : ZMod L,
      (fullLoop μ a' x).cutGlueR k l b = (fullLoop μ a' 0).cutGlueR k l b :=
    fun x k l hk hkl hl b => cutGlueR_fullLoop_indep μ a' x b 0 hk hkl hl
  -- split each `primRhs`
  have hsplit : ∀ x : ZMod L, primRhs L W K (fullLoop μ a' x) = (W : ℂ) *
      (∑ k ∈ Icc 1 a'.length, ∑ l ∈ Ioc k a'.length, ∑ a : ZMod L, ∑ b : ZMod L,
          K ((fullLoop μ a' x).cutGlueL k l a) * SB L a b *
            K ((fullLoop μ a' 0).cutGlueR k l b)
        + ∑ k ∈ Icc 1 a'.length, ∑ a : ZMod L, ∑ b : ZMod L,
          K ((fullLoop μ a' x).cutGlueL k (a'.length + 1) a) * SB L a b *
            K ((fullLoop μ a' 0).cutGlueR k (a'.length + 1) b)) := by
    intro x
    rw [primRhs, hlen, sum_Icc_succ_top (by omega), Ioc_self, sum_empty, add_zero,
      ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Icc] at hk
    rw [sum_Ioc_succ_top hk.2]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      rw [mem_Ioc] at hl
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hR x k l hk.1 hl.1 (by omega) b]
    · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hR x k (a'.length + 1) hk.1 (by omega) le_rfl b]
  simp only [hsplit, ← Finset.mul_sum, sum_add_distrib]
  congr 2
  · rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
  · rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]

end RBM
