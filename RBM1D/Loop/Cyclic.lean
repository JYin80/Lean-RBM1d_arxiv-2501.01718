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

So `K∘rot - K` on loops of length `n` satisfies a linear equation whose coefficients are the
`2`-loops, once invariance is known on shorter loops; it vanishes at `t = 0` because the
initial value of Definition 2.12 is rotation invariant.  Grönwall (as in
`RBM1D.Loop.Unique`) and induction on the length finish.

## Main results

* `RBM.primRhs_rot`      : (2.48) at a rotated loop
* `RBM.primInit_rot`     : the initial value is rotation invariant
* `RBM.rot_eq_on_level`  : one level of the induction
* `RBM.isPrimitive_rot`  : **`K_{t, rot(σ,a)} = K_{t,σ,a}`** for a solution with bounded `2`-loops
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
          K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueL 1 l a).rot * SB L a b *
            K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueR 1 l b).rot
        + ∑ k ∈ Icc 2 (cs.length + 1), ∑ l ∈ Ioc k (cs.length + 1), ∑ a : ZMod L, ∑ b : ZMod L,
          K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueL k l a).rot * SB L a b *
            K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueR k l b)) := by
  have hrlen : (⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).rot.length = cs.length + 1 := by
    rw [LoopIdx.length_rot]
    simp [LoopIdx.length]
  rw [primRhs, hrlen, sum_Icc_succ_top (by omega), Ioc_self, sum_empty, add_zero]
  -- split off the cut at the last edge
  have hsplit : ∀ k ∈ Icc 1 cs.length, ∑ l ∈ Ioc k (cs.length + 1), ∑ a : ZMod L, ∑ b : ZMod L,
      K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).rot.cutGlueL k l a) * SB L a b *
        K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).rot.cutGlueR k l b)
      = ∑ l ∈ Ioc k cs.length, ∑ a : ZMod L, ∑ b : ZMod L,
          K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueL (k + 1) (l + 1) a).rot * SB L a b *
            K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueR (k + 1) (l + 1) b)
        + ∑ a : ZMod L, ∑ b : ZMod L,
          K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueL 1 (k + 1) a).rot * SB L a b *
            K ((⟨s :: ss, c :: cs⟩ : LoopIdx (ZMod L)).cutGlueR 1 (k + 1) b).rot := by
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

/-- The initial value of Definition 2.12 is invariant under rotation. -/
theorem primInit_rot (W : ℕ) (m : Bool → ℂ) (I : LoopIdx (ZMod L)) :
    primInit L W m I.rot = primInit L W m I := by
  simp only [primInit, LoopIdx.length_rot]
  congr 2
  · simp only [LoopIdx.rot, List.map_rotate]
    exact (List.rotate_perm _ 1).prod_eq
  · simp only [LoopIdx.rot, List.mem_rotate]

/-- **One level of the induction.**  If `K` solves (2.48) on `[0, T₀]` with `2`-loops
bounded by `R`, is invariant under `rot` on loops shorter than `n`, and at `t = 0` on loops
of length `n`, then it is invariant under `rot` on loops of length `n`. -/
theorem rot_eq_on_level (hL : 3 ≤ L) (W : ℕ) (K : ℝ → LoopIdx (ZMod L) → ℂ) (T₀ R : ℝ)
    (n : ℕ) (hn : 2 ≤ n) (hR0 : 0 ≤ R)
    (hK : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length →
      HasDerivAt (fun s => K s I) (primRhs L W (K t) I) t)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R)
    (hlow : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length →
      I.length < n → K t I.rot = K t I)
    (h0 : ∀ I : LoopIdx (ZMod L), I.WF → I.length = n → K 0 I.rot = K 0 I) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = n →
      K t I.rot = K t I := by
  let D : ℝ → LoopVec L n → ℂ := fun t p => K t (p.toLoop L).rot - K t (p.toLoop L)
  let D' : ℝ → LoopVec L n → ℂ := fun t p =>
    primRhs L W (K t) (p.toLoop L).rot - primRhs L W (K t) (p.toLoop L)
  have hD : ∀ t ∈ Set.Icc 0 T₀, HasDerivAt D (D' t) t := fun t ht =>
    hasDerivAt_pi.2 fun p =>
      (hK t ht _ (p.wf L).rot (by rw [LoopIdx.length_rot, p.length L]; exact hn)).sub
        (hK t ht _ (p.wf L) ((p.length L).symm ▸ hn))
  let C : ℝ := W * ((∑ _l ∈ Ioc 1 n, ∑ _a : ZMod L, ∑ _b : ZMod L, 2 * R)
    + ∑ k ∈ Icc 2 n, ∑ _l ∈ Ioc k n, ∑ _a : ZMod L, ∑ _b : ZMod L, 2 * R)
  have hC : 0 ≤ C := by
    refine mul_nonneg (Nat.cast_nonneg W) (add_nonneg ?_ ?_)
    · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => by positivity
    · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hbound : ∀ t ∈ Set.Ico 0 T₀, ‖D' t‖ ≤ C * ‖D t‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T₀ := Set.Ico_subset_Icc_self ht
    -- the rotation difference at a chain is `0` below length `n`, at most `‖D t‖` at `n`
    have hdiff : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ n →
        ‖K t J.rot - K t J‖ ≤ ‖D t‖ := by
      intro J hJ h2 hle
      rcases hle.lt_or_eq with hlt | heq
      · rw [hlow t ht' J hJ h2 hlt, sub_self, norm_zero]
        exact norm_nonneg _
      · obtain ⟨p, rfl⟩ := LoopVec.exists_toLoop L J hJ heq
        exact norm_le_pi_norm (D t) p
    have hRD : 0 ≤ R * ‖D t‖ := mul_nonneg hR0 (norm_nonneg _)
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).2 fun p => ?_
    -- write the loop as `(s :: ss, c :: cs)`
    have hI : (p.toLoop L).WF := p.wf L
    have hIn : (p.toLoop L).length = n := p.length L
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_length_pos
      (show 0 < (p.toLoop L).a.length from by rw [← LoopIdx.length, hIn]; omega)
    obtain ⟨s, ss, hss'⟩ := List.exists_cons_of_length_pos
      (show 0 < (p.toLoop L).σ.length from by rw [hI, ← LoopIdx.length, hIn]; omega)
    have hIeq : p.toLoop L = ⟨s :: ss, c :: cs⟩ := LoopIdx.ext hss' hcs
    have hss : ss.length = cs.length := by
      have := hI
      rw [hIeq] at this
      simpa [LoopIdx.WF] using this
    have hn' : cs.length + 1 = n := by
      rw [← hIn, hIeq]
      simp [LoopIdx.length]
    set I : LoopIdx (ZMod L) := ⟨s :: ss, c :: cs⟩ with hIdef
    have hIWF : I.WF := hIeq ▸ hI
    have hIlen : I.length = n := hIeq ▸ hIn
    -- per-term facts
    have hcut : ∀ k l, 1 ≤ k → k < l → l ≤ n → ∀ a b : ZMod L,
        (I.cutGlueL k l a).WF ∧ (I.cutGlueR k l b).WF ∧
        2 ≤ (I.cutGlueL k l a).length ∧ 2 ≤ (I.cutGlueR k l b).length ∧
        (I.cutGlueL k l a).length ≤ n ∧ (I.cutGlueR k l b).length ≤ n ∧
        ((I.cutGlueL k l a).length = n → (I.cutGlueR k l b).length = 2) ∧
        ((I.cutGlueR k l b).length = n → (I.cutGlueL k l a).length = 2) := by
      intro k l hk hkl hl a b
      have hlI : l ≤ I.length := hIlen ▸ hl
      refine ⟨LoopIdx.WF.cutGlueL a hIWF hk hkl hlI, LoopIdx.WF.cutGlueR b hIWF hk hkl hlI,
        LoopIdx.two_le_length_cutGlueL I a hk hkl hlI,
        LoopIdx.two_le_length_cutGlueR I b hk hkl hlI,
        hIlen ▸ LoopIdx.length_cutGlueL_le I a hk hkl hlI,
        hIlen ▸ LoopIdx.length_cutGlueR_le I b hk hkl hlI, fun h => ?_, fun h => ?_⟩
      · exact LoopIdx.length_cutGlueR_eq_two I a b hk hkl hlI (h.trans hIlen.symm)
      · exact LoopIdx.length_cutGlueL_eq_two I a b hk hkl hlI (h.trans hIlen.symm)
    -- bound on `‖K t X.rot - K t X‖ * ‖K t Y'‖` when `Y` is the partner of `X`
    have hA : ∀ l ∈ Ioc 1 n, ∀ a b : ZMod L,
        ‖K t (I.cutGlueL 1 l a).rot * SB L a b * K t (I.cutGlueR 1 l b).rot
          - K t (I.cutGlueL 1 l a) * SB L a b * K t (I.cutGlueR 1 l b)‖ ≤ 2 * (R * ‖D t‖) := by
      intro l hl a b
      rw [mem_Ioc] at hl
      obtain ⟨hWL, hWR, h2L, h2R, hLn, hRn, hLR, hRL⟩ := hcut 1 l le_rfl hl.1 hl.2 a b
      refine norm_mul_mul_sub_le (norm_SB_apply_le L hL a b) ?_ ?_
      · rcases hLn.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWL h2L hlt, sub_self, norm_zero, zero_mul]
          exact hRD
        · have hY := hR t ht' _ hWR.rot (by rw [LoopIdx.length_rot]; exact hLR heq)
          rw [mul_comm R]
          exact mul_le_mul (hdiff _ hWL h2L hLn) hY (norm_nonneg _) (norm_nonneg _)
      · rcases hRn.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWR h2R hlt, sub_self, norm_zero, mul_zero]
          exact hRD
        · have hX := hR t ht' _ hWL (hRL heq)
          exact mul_le_mul hX (hdiff _ hWR h2R hRn) (norm_nonneg _) hR0
    have hB : ∀ k ∈ Icc 2 n, ∀ l ∈ Ioc k n, ∀ a b : ZMod L,
        ‖K t (I.cutGlueL k l a).rot * SB L a b * K t (I.cutGlueR k l b)
          - K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b)‖ ≤ 2 * (R * ‖D t‖) := by
      intro k hk l hl a b
      rw [mem_Icc] at hk
      rw [mem_Ioc] at hl
      obtain ⟨hWL, hWR, h2L, h2R, hLn, hRn, hLR, hRL⟩ :=
        hcut k l (by omega) hl.1 hl.2 a b
      refine norm_mul_mul_sub_le (norm_SB_apply_le L hL a b) ?_ ?_
      · rcases hLn.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWL h2L hlt, sub_self, norm_zero, zero_mul]
          exact hRD
        · have hY := hR t ht' _ hWR (hLR heq)
          rw [mul_comm R]
          exact mul_le_mul (hdiff _ hWL h2L hLn) hY (norm_nonneg _) (norm_nonneg _)
      · rw [sub_self, norm_zero, mul_zero]
        exact hRD
    -- assemble
    have e : D' t p = (W : ℂ) *
        ((∑ l ∈ Ioc 1 n, ∑ a : ZMod L, ∑ b : ZMod L,
          (K t (I.cutGlueL 1 l a).rot * SB L a b * K t (I.cutGlueR 1 l b).rot
            - K t (I.cutGlueL 1 l a) * SB L a b * K t (I.cutGlueR 1 l b)))
        + ∑ k ∈ Icc 2 n, ∑ l ∈ Ioc k n, ∑ a : ZMod L, ∑ b : ZMod L,
          (K t (I.cutGlueL k l a).rot * SB L a b * K t (I.cutGlueR k l b)
            - K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b))) := by
      simp only [D']
      rw [hIeq, primRhs_rot L W (K t) s ss c cs hss,
        primRhs_split L W (K t) _ (by rw [hIlen]; omega)]
      simp only [← hIdef]
      rw [hIlen, hn']
      simp only [Finset.sum_sub_distrib]
      ring
    rw [e, norm_mul, Complex.norm_natCast]
    have hsum : ‖(∑ l ∈ Ioc 1 n, ∑ a : ZMod L, ∑ b : ZMod L,
          (K t (I.cutGlueL 1 l a).rot * SB L a b * K t (I.cutGlueR 1 l b).rot
            - K t (I.cutGlueL 1 l a) * SB L a b * K t (I.cutGlueR 1 l b)))
        + ∑ k ∈ Icc 2 n, ∑ l ∈ Ioc k n, ∑ a : ZMod L, ∑ b : ZMod L,
          (K t (I.cutGlueL k l a).rot * SB L a b * K t (I.cutGlueR k l b)
            - K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b))‖
        ≤ (∑ _l ∈ Ioc 1 n, ∑ _a : ZMod L, ∑ _b : ZMod L, 2 * (R * ‖D t‖))
          + ∑ k ∈ Icc 2 n, ∑ _l ∈ Ioc k n, ∑ _a : ZMod L, ∑ _b : ZMod L, 2 * (R * ‖D t‖) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        exact hA l hl a b
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        exact hB k hk l hl a b
    calc (W : ℝ) * ‖_‖ ≤ W * ((∑ _l ∈ Ioc 1 n, ∑ _a : ZMod L, ∑ _b : ZMod L, 2 * (R * ‖D t‖))
          + ∑ k ∈ Icc 2 n, ∑ _l ∈ Ioc k n, ∑ _a : ZMod L, ∑ _b : ZMod L, 2 * (R * ‖D t‖)) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg W)
      _ = C * ‖D t‖ := by simp only [C, Finset.sum_mul, add_mul, mul_assoc]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := D) (f' := D') (K := C) (a := 0) (b := T₀)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (funext fun p => sub_eq_zero.2 (h0 _ (p.wf L) (p.length L))) hbound
  intro t ht I hI hIn
  obtain ⟨p, rfl⟩ := LoopVec.exists_toLoop L I hI hIn
  exact sub_eq_zero.1 (congrFun (hzero t ht) p)

/-- **Cyclic invariance of `K`.**  A solution of Definition 2.12 on `[0, T₀]` whose
`2`-loops stay bounded is invariant under rotating the loop:
`K_{t, (σ₂,…,σₙ,σ₁), (a₂,…,aₙ,a₁)} = K_{t,σ,a}`. -/
theorem isPrimitive_rot (hL : 3 ≤ L) (W : ℕ) (m : Bool → ℂ) {T : Set ℝ}
    {K : ℝ → LoopIdx (ZMod L) → ℂ} (hK : IsPrimitive L W m T K) {T₀ R : ℝ}
    (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length → K t I.rot = K t I := by
  have main : ∀ n : ℕ, ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length →
      I.length = n → K t I.rot = K t I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht I hI h2 hIn
      have hn : 2 ≤ n := hIn ▸ h2
      refine rot_eq_on_level L hL W K T₀ R n hn hR0 (fun s hs => hK.1 s (hT hs)) hR ?_ ?_
        t ht I hI hIn
      · intro s hs J hJ hJ2 hJn
        exact ih _ hJn s hs J hJ hJ2 rfl
      · intro J hJ hJn
        rw [hK.2.1 _ hJ.rot (by rw [LoopIdx.length_rot, hJn]; exact hn),
          hK.2.1 _ hJ (hJn ▸ hn), primInit_rot]
  intro t ht I hI h2
  exact main _ t ht I hI h2 rfl

section Translation

/-!
### Translation invariance

Shifting every block label by `c` commutes with cut-and-glue (the glue labels shift too) and
`S^(B)` is translation invariant, so `K ∘ shift c` solves (2.48) exactly, with the same
initial value; uniqueness gives `K_{t,σ,a+c} = K_{t,σ,a}`.  The paper uses this ("by definition
of `K`, `K` is translation invariant") in the proof of Corollary 3.7.
-/

/-- Shift every block label by `c`. -/
def LoopIdx.shift (c : ZMod L) (I : LoopIdx (ZMod L)) : LoopIdx (ZMod L) :=
  ⟨I.σ, I.a.map (· + c)⟩

omit [NeZero L] in
theorem LoopIdx.shift_WF {c : ZMod L} {I : LoopIdx (ZMod L)} (hI : I.WF) : (I.shift L c).WF := by
  simpa [LoopIdx.WF, LoopIdx.shift] using hI

omit [NeZero L] in
theorem LoopIdx.length_shift (c : ZMod L) (I : LoopIdx (ZMod L)) :
    (I.shift L c).length = I.length := by
  simp [LoopIdx.length, LoopIdx.shift]

omit [NeZero L] in
theorem LoopIdx.cutGlueL_shift (c : ZMod L) (I : LoopIdx (ZMod L)) (k l : ℕ) (b : ZMod L) :
    (I.shift L c).cutGlueL k l b = (I.cutGlueL k l (b - c)).shift L c := by
  simp [LoopIdx.shift, LoopIdx.cutGlueL, List.map_take, List.map_drop]

omit [NeZero L] in
theorem LoopIdx.cutGlueR_shift (c : ZMod L) (I : LoopIdx (ZMod L)) (k l : ℕ) (b : ZMod L) :
    (I.shift L c).cutGlueR k l b = (I.cutGlueR k l (b - c)).shift L c := by
  simp [LoopIdx.shift, LoopIdx.cutGlueR, List.map_take, List.map_drop]

/-- (2.48) at a shifted loop. -/
theorem primRhs_shift (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (c : ZMod L) (I : LoopIdx (ZMod L)) :
    primRhs L W K (I.shift L c) = primRhs L W (fun J => K (J.shift L c)) I := by
  rw [primRhs, primRhs, LoopIdx.length_shift]
  congr 1
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  simp only [LoopIdx.cutGlueL_shift, LoopIdx.cutGlueR_shift]
  rw [← Equiv.sum_comp (Equiv.addRight c)]
  refine sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp (Equiv.addRight c)]
  refine sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, SB_apply_add_right]

/-- The initial value of Definition 2.12 is translation invariant. -/
theorem primInit_shift (W : ℕ) (m : Bool → ℂ) (c : ZMod L) (I : LoopIdx (ZMod L)) :
    primInit L W m (I.shift L c) = primInit L W m I := by
  simp only [primInit, LoopIdx.length_shift]
  congr 2
  simp only [LoopIdx.shift, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, add_left_inj]

/-- **Translation invariance of `K`**: a solution of Definition 2.12 on `[0, T₀]` with bounded
`2`-loops satisfies `K_{t,σ,a+c} = K_{t,σ,a}`. -/
theorem isPrimitive_shift (hL : 3 ≤ L) (W : ℕ) (m : Bool → ℂ) {T : Set ℝ}
    {K : ℝ → LoopIdx (ZMod L) → ℂ} (hK : IsPrimitive L W m T K) {T₀ R : ℝ}
    (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R)
    (c : ZMod L) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length →
      K t (I.shift L c) = K t I := by
  have hK' : IsPrimitive L W m T (fun t I => K t (I.shift L c)) := by
    refine ⟨fun t ht I hI h2 => ?_, fun I hI h2 => ?_, fun t ht s a => ?_⟩
    · have := hK.1 t ht (I.shift L c) (LoopIdx.shift_WF L hI)
        (by rw [LoopIdx.length_shift]; exact h2)
      rwa [primRhs_shift] at this
    · show K 0 (I.shift L c) = primInit L W m I
      rw [hK.2.1 _ (LoopIdx.shift_WF L hI) (by rw [LoopIdx.length_shift]; exact h2),
        primInit_shift]
    · exact hK.2.2 t ht s (a + c)
  intro t ht I hI h2
  exact (isPrimitive_unique L hL W m hK' hK hT hR0 (fun s hs J hJ hJ2 =>
    ⟨hR s hs _ (LoopIdx.shift_WF L hJ) (by rw [LoopIdx.length_shift]; exact hJ2),
      hR s hs J hJ hJ2⟩) t ht I hI h2)

end Translation

end RBM
