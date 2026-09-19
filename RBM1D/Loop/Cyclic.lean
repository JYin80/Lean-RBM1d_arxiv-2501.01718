/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Unique

/-!
# Cyclic invariance of the primitive loop

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*: the proof of Lemma 3.6 (Step 4)
uses that `K_{t,σ,a}` is invariant under cyclic rotation of the loop ("cyclicity").  This is
clear for the `G`-loops `L_{t,σ,a} = ⟨∏ G(σᵢ) E_{aᵢ}⟩` (cyclicity of the trace), but for `K`,
defined by Definition 2.12, it has to be proved.  The paper does not.

## The argument

`RBM.primRhs_rot` rewrites the right-hand side of (2.48) at `rot I` in terms of the cuts of
`I`: the cut `(k, l)` of `rot I` with `l < n` is the cut `(k + 1, l + 1)` of `I` (left chain
rotated), and the cut `(k, n)` is the cut `(1, k + 1)` of `I` with the chains swapped, which
the symmetry of `S^(B)` turns back into the usual order.
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

section Reindex

variable {M : Type*} [AddCommMonoid M]

theorem sum_Icc_shift (f : ℕ → M) (a b : ℕ) :
    ∑ k ∈ Icc a b, f (k + 1) = ∑ k ∈ Icc (a + 1) (b + 1), f k := by
  rw [← map_add_right_Icc, sum_map]
  rfl

theorem sum_Ioc_shift (f : ℕ → M) (a b : ℕ) :
    ∑ k ∈ Ioc a b, f (k + 1) = ∑ k ∈ Ioc (a + 1) (b + 1), f k := by
  rw [← map_add_right_Ioc, sum_map]
  rfl

theorem Icc_two_eq_Ioc_one (n : ℕ) : Icc 2 n = Ioc 1 n := by
  ext k
  simp only [mem_Icc, mem_Ioc]
  omega

end Reindex

/-- The right-hand side of (2.48) with the cuts `(1, l)` separated. -/
theorem primRhs_split (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    (hn : 1 ≤ I.length) :
    primRhs L W K I = (W : ℂ) *
      (∑ l ∈ Ioc 1 I.length, ∑ a : ZMod L, ∑ b : ZMod L,
          K (I.cutGlueL 1 l a) * SB L a b * K (I.cutGlueR 1 l b)
        + ∑ k ∈ Icc 2 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
          K (I.cutGlueL k l a) * SB L a b * K (I.cutGlueR k l b)) := by
  have h : Icc 1 I.length = insert 1 (Icc 2 I.length) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  rw [primRhs, h, sum_insert (by simp)]

/-- **(2.48) at the rotated loop**, in terms of the cuts of the original loop
`I = (s :: ss, c :: cs)` of length `n = |cs| + 1`. -/
theorem primRhs_rot (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (s : Bool) (ss : List Bool)
    (c : ZMod L) (cs : List (ZMod L)) (hss : ss.length = cs.length) :
    primRhs L W K (⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).rot = (W : ℂ) *
      (∑ l ∈ Ioc 1 (cs.length + 1), ∑ a : ZMod L, ∑ b : ZMod L,
          K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueL 1 l a).rot * SB L a b * K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueR 1 l b).rot
        + ∑ k ∈ Icc 2 (cs.length + 1), ∑ l ∈ Ioc k (cs.length + 1), ∑ a : ZMod L, ∑ b : ZMod L,
          K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueL k l a).rot * SB L a b * K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueR k l b)) := by
  have hrlen : (⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).rot.length = cs.length + 1 := by
    rw [LoopIdx.length_rot]
    simp [LoopIdx.length]
  rw [primRhs, hrlen, sum_Icc_succ_top (by omega), Ioc_self, sum_empty, add_zero]
  -- split off the cut at the last edge
  have hsplit : ∀ k ∈ Icc 1 cs.length, ∑ l ∈ Ioc k (cs.length + 1), ∑ a : ZMod L, ∑ b : ZMod L,
      K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).rot.cutGlueL k l a) * SB L a b * K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).rot.cutGlueR k l b)
      = ∑ l ∈ Ioc k cs.length, ∑ a : ZMod L, ∑ b : ZMod L,
          K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueL (k + 1) (l + 1) a).rot * SB L a b * K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueR (k + 1) (l + 1) b)
        + ∑ a : ZMod L, ∑ b : ZMod L,
          K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueL 1 (k + 1) a).rot * SB L a b * K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueR 1 (k + 1) b).rot := by
    intro k hk
    rw [mem_Icc] at hk
    rw [sum_Ioc_succ_top hk.2]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      rw [mem_Ioc] at hl
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [LoopIdx.cutGlueL_rot_of_lt s ss c cs a hss hk.1 hl.1 hl.2,
        LoopIdx.cutGlueR_rot_of_lt s ss c cs b hss hk.1 hl.1 hl.2]
    · rw [sum_comm]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [LoopIdx.cutGlueL_rot_last s ss c cs b hss hk.1 hk.2,
        LoopIdx.cutGlueR_rot_last s ss c cs a hss hk.1 hk.2,
        show SB L b a = SB L a b from congrFun (congrFun (SB_transpose L) a) b]
      ring
  rw [sum_congr rfl hsplit, sum_add_distrib, add_comm]
  refine congrArg _ (congrArg₂ (· + ·) ?_ ?_)
  · refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_Icc, mem_Ioc] at hx ⊢
      omega
    · intro x hx
      simp only [mem_Icc, mem_Ioc] at hx ⊢
      omega
    · intro x _
      simp
    · intro x hx
      simp only [mem_Ioc] at hx
      omega
    · intro x _
      rfl
  · refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_Icc] at hx ⊢
      omega
    · intro x hx
      simp only [mem_Icc] at hx ⊢
      omega
    · intro x _
      simp
    · intro x hx
      simp only [mem_Icc] at hx
      omega
    · intro x _
      refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
      · intro y hy
        simp only [mem_Ioc] at hy ⊢
        omega
      · intro y hy
        simp only [mem_Ioc] at hy ⊢
        omega
      · intro y _
        simp
      · intro y hy
        simp only [mem_Ioc] at hy
        omega
      · intro y _
        rfl

end RBM
