/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Primitive
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.Fintype.Vector

/-!
# Uniqueness for the primitive equation

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 2.12: `K` is *the*
solution of (2.48).  We prove uniqueness (not existence: existence comes from the tree
formula, Lemma 3.4).

## The structure of (2.48)

Every term of (2.48) at a loop of length `n` is a product of the values at two shorter
chains, of lengths `k + n - l + 1` and `l - k + 1`.  Both are in `[2, n]` and they add up
to `n + 2` (`RBM.LoopIdx.length_cutGlueL_add_length_cutGlueR`).  Hence
(`RBM.LoopIdx.length_cutGlueR_eq_two`, `RBM.LoopIdx.length_cutGlueL_eq_two`):

* if one chain has the full length `n`, the other has length `2`;
* so for `n ≥ 3`, once the lengths `< n` are fixed, the equation for length `n` is
  *linear* in the length-`n` unknowns, with coefficients given by the `2`-loops;
* for `n = 2` both chains have length `2` and the equation is quadratic (Riccati).

## The argument

One Grönwall argument covers both cases.  Fix `n` and assume two solutions agree on all
loops of length `< n`.  Let `D` be their difference on loops of length `n`.  Each term of
(2.48) differs by `(X - X') s Y + X' s (Y - Y')`; a difference `X - X'` vanishes unless its
chain has length `n`, and then the other factor is a `2`-loop.  So a bound `R` on the
`2`-loops gives `‖D'‖ ≤ C ‖D‖`, and `D(0) = 0` forces `D = 0`
(`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`).  Strong induction on `n`
finishes.  For `n = 2` the hypothesis on shorter loops is vacuous and the same estimate is
the Lipschitz bound of the Riccati right-hand side.

## Main results

* `RBM.LoopIdx.length_cutGlueR_eq_two`, `RBM.LoopIdx.length_cutGlueL_eq_two` : the
  structure lemma
* `RBM.eq_on_level` : one step of the induction
* `RBM.isPrimitive_unique` : **two solutions of Definition 2.12 on `[0, T₀]` whose
  `2`-loops are bounded agree on every loop**
-/

namespace RBM

namespace LoopIdx

variable {α : Type*} (x : LoopIdx α) (a b : α) {k l : ℕ}

/-- **Structure of (2.48).** If the left chain has the full length `n`, the right chain is
a `2`-loop. -/
theorem length_cutGlueR_eq_two (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length)
    (h : (x.cutGlueL k l a).length = x.length) : (x.cutGlueR k l b).length = 2 := by
  rw [length_cutGlueL x a hk hkl hl] at h
  rw [length_cutGlueR x b hk hkl hl]
  omega

/-- **Structure of (2.48).** If the right chain has the full length `n`, the left chain is
a `2`-loop. -/
theorem length_cutGlueL_eq_two (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length)
    (h : (x.cutGlueR k l b).length = x.length) : (x.cutGlueL k l a).length = 2 := by
  rw [length_cutGlueR x b hk hkl hl] at h
  rw [length_cutGlueL x a hk hkl hl]
  omega

end LoopIdx

open Finset

variable (L : ℕ) [NeZero L]

/-- Loops of length `n`, as a finite type. -/
abbrev LoopVec (n : ℕ) := List.Vector Bool n × List.Vector (ZMod L) n

/-- The loop with given charges and labels. -/
def LoopVec.toLoop {n : ℕ} (p : LoopVec L n) : LoopIdx (ZMod L) := ⟨p.1.1, p.2.1⟩

omit [NeZero L] in
theorem LoopVec.wf {n : ℕ} (p : LoopVec L n) : (p.toLoop L).WF := by
  show p.1.1.length = p.2.1.length
  rw [p.1.2, p.2.2]

omit [NeZero L] in
theorem LoopVec.length {n : ℕ} (p : LoopVec L n) : (p.toLoop L).length = n := p.2.2

omit [NeZero L] in
theorem LoopVec.exists_toLoop {n : ℕ} (J : LoopIdx (ZMod L)) (hJ : J.WF) (hJn : J.length = n) :
    ∃ p : LoopVec L n, p.toLoop L = J :=
  ⟨(⟨J.σ, hJ.trans hJn⟩, ⟨J.a, hJn⟩), rfl⟩

theorem norm_SB_apply_le (hL : 3 ≤ L) (a b : ZMod L) : ‖SB L a b‖ ≤ 1 := by
  have h := Finset.single_le_sum (f := fun b => ‖SB L a b‖₊) (fun _ _ => by positivity)
    (Finset.mem_univ b)
  rw [sum_nnnorm_SB_row L hL a] at h
  exact_mod_cast h

/-- The difference of one term of (2.48): `X s Y - X' s Y' = (X - X') s Y + X' s (Y - Y')`. -/
theorem norm_mul_mul_sub_le {X X' Y Y' s : ℂ} {R d : ℝ} (hs : ‖s‖ ≤ 1)
    (h1 : ‖X - X'‖ * ‖Y‖ ≤ R * d) (h2 : ‖X'‖ * ‖Y - Y'‖ ≤ R * d) :
    ‖X * s * Y - X' * s * Y'‖ ≤ 2 * (R * d) := by
  have e : X * s * Y - X' * s * Y' = (X - X') * s * Y + X' * s * (Y - Y') := by ring
  have e1 : ‖(X - X') * s * Y‖ ≤ R * d := by
    rw [norm_mul, norm_mul]
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg (norm_nonneg (X - X')) (norm_nonneg Y))
    nlinarith
  have e2 : ‖X' * s * (Y - Y')‖ ≤ R * d := by
    rw [norm_mul, norm_mul]
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg (norm_nonneg X') (norm_nonneg (Y - Y')))
    nlinarith
  rw [e]
  linarith [norm_add_le ((X - X') * s * Y) (X' * s * (Y - Y'))]

/-- **One step of the induction.**  Two functions satisfying (2.48) on loops of length `n`
on `[0, T₀]`, whose `2`-loops are bounded by `R`, which agree on all loops of length `< n` and
at `t = 0` on loops of length `n`, agree on loops of length `n`.  Only the equation at length
`n` is used, so this also compares a solution with a candidate known only up to length `n`. -/
theorem eq_on_level (hL : 3 ≤ L) (W : ℕ) (K K' : ℝ → LoopIdx (ZMod L) → ℂ) (T₀ R : ℝ)
    (n : ℕ) (hR0 : 0 ≤ R)
    (hK : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = n →
      HasDerivAt (fun s => K s I) (primRhs L W (K t) I) t)
    (hK' : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = n →
      HasDerivAt (fun s => K' s I) (primRhs L W (K' t) I) t)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 →
      ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R)
    (hlow : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length →
      I.length < n → K t I = K' t I)
    (h0 : ∀ I : LoopIdx (ZMod L), I.WF → I.length = n → K 0 I = K' 0 I) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = n → K t I = K' t I := by
  let D : ℝ → LoopVec L n → ℂ := fun t p => K t (p.toLoop L) - K' t (p.toLoop L)
  let D' : ℝ → LoopVec L n → ℂ := fun t p =>
    primRhs L W (K t) (p.toLoop L) - primRhs L W (K' t) (p.toLoop L)
  have hD : ∀ t ∈ Set.Icc 0 T₀, HasDerivAt D (D' t) t := fun t ht =>
    hasDerivAt_pi.2 fun p =>
      (hK t ht _ (p.wf L) (p.length L)).sub (hK' t ht _ (p.wf L) (p.length L))
  let C : ℝ := W * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ _a : ZMod L, ∑ _b : ZMod L, 2 * R
  have hC : 0 ≤ C := by
    refine mul_nonneg (Nat.cast_nonneg W) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg
      fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  have hbound : ∀ t ∈ Set.Ico 0 T₀, ‖D' t‖ ≤ C * ‖D t‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T₀ := Set.Ico_subset_Icc_self ht
    -- the difference at a chain is `0` below length `n` and at most `‖D t‖` at length `n`
    have hdiff : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ n →
        ‖K t J - K' t J‖ ≤ ‖D t‖ := by
      intro J hJ h2 hle
      rcases hle.lt_or_eq with hlt | heq
      · rw [hlow t ht' J hJ h2 hlt, sub_self, norm_zero]
        exact norm_nonneg _
      · obtain ⟨p, rfl⟩ := LoopVec.exists_toLoop L J hJ heq
        exact norm_le_pi_norm (D t) p
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).2 fun p => ?_
    set I := p.toLoop L with hIdef
    have hI : I.WF := p.wf L
    have hIn : I.length = n := p.length L
    have hterm : ∀ k ∈ Icc 1 n, ∀ l ∈ Ioc k n, ∀ a b : ZMod L,
        ‖K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b)
          - K' t (I.cutGlueL k l a) * SB L a b * K' t (I.cutGlueR k l b)‖
          ≤ 2 * (R * ‖D t‖) := by
      intro k hk l hl a b
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_Ioc] at hl
      have hk1 : 1 ≤ k := hk.1
      have hkl : k < l := hl.1
      have hlI : l ≤ I.length := hIn ▸ hl.2
      have hWL : (I.cutGlueL k l a).WF := LoopIdx.WF.cutGlueL a hI hk1 hkl hlI
      have hWR : (I.cutGlueR k l b).WF := LoopIdx.WF.cutGlueR b hI hk1 hkl hlI
      have h2L := LoopIdx.two_le_length_cutGlueL I a hk1 hkl hlI
      have h2R := LoopIdx.two_le_length_cutGlueR I b hk1 hkl hlI
      have hLle : (I.cutGlueL k l a).length ≤ n :=
        hIn ▸ LoopIdx.length_cutGlueL_le I a hk1 hkl hlI
      have hRle : (I.cutGlueR k l b).length ≤ n :=
        hIn ▸ LoopIdx.length_cutGlueR_le I b hk1 hkl hlI
      have hRD : 0 ≤ R * ‖D t‖ := mul_nonneg hR0 (norm_nonneg _)
      refine norm_mul_mul_sub_le (norm_SB_apply_le L hL a b) ?_ ?_
      · rcases hLle.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWL h2L hlt, sub_self, norm_zero, zero_mul]
          exact hRD
        · have h2 := LoopIdx.length_cutGlueR_eq_two I a b hk1 hkl hlI (heq.trans hIn.symm)
          have hY := (hR t ht' _ hWR h2).1
          have hX := hdiff _ hWL h2L hLle
          rw [mul_comm R]
          exact mul_le_mul hX hY (norm_nonneg _) (norm_nonneg _)
      · rcases hRle.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWR h2R hlt, sub_self, norm_zero, mul_zero]
          exact hRD
        · have h2 := LoopIdx.length_cutGlueL_eq_two I a b hk1 hkl hlI (heq.trans hIn.symm)
          have hX := (hR t ht' _ hWL h2).2
          have hY := hdiff _ hWR h2R hRle
          exact mul_le_mul hX hY (norm_nonneg _) hR0
    have e : D' t p = (W : ℂ) * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ a : ZMod L, ∑ b : ZMod L,
        (K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b)
          - K' t (I.cutGlueL k l a) * SB L a b * K' t (I.cutGlueR k l b)) := by
      simp only [D', primRhs, ← hIdef, hIn, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [e, norm_mul, Complex.norm_natCast]
    have hsum : ‖∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ a : ZMod L, ∑ b : ZMod L,
        (K t (I.cutGlueL k l a) * SB L a b * K t (I.cutGlueR k l b)
          - K' t (I.cutGlueL k l a) * SB L a b * K' t (I.cutGlueR k l b))‖
        ≤ ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ _a : ZMod L, ∑ _b : ZMod L, 2 * (R * ‖D t‖) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      exact hterm k hk l hl a b
    calc (W : ℝ) * ‖_‖ ≤ W * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ _a : ZMod L, ∑ _b : ZMod L,
          2 * (R * ‖D t‖) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg W)
      _ = C * ‖D t‖ := by
        simp only [C, Finset.sum_mul, mul_assoc]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := D) (f' := D') (K := C) (a := 0) (b := T₀)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (funext fun p => sub_eq_zero.2 (h0 _ (p.wf L) (p.length L))) hbound
  intro t ht I hI hIn
  obtain ⟨p, rfl⟩ := LoopVec.exists_toLoop L I hI hIn
  exact sub_eq_zero.1 (congrFun (hzero t ht) p)

/-- **Uniqueness for Definition 2.12.**  Two solutions of the primitive equation on
`[0, T₀]` (the same `W`, `m`) whose `2`-loops stay bounded agree on every loop of length
`≥ 2`.  The bound is only needed on `2`-loops: by the structure lemma they are the only
coefficients of the linear equations at higher length. -/
theorem isPrimitive_unique (hL : 3 ≤ L) (W : ℕ) (m : Bool → ℂ) {T : Set ℝ}
    {K K' : ℝ → LoopIdx (ZMod L) → ℂ} (hK : IsPrimitive L W m T K)
    (hK' : IsPrimitive L W m T K') {T₀ R : ℝ} (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 →
      ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length → K t I = K' t I := by
  have main : ∀ n : ℕ, ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length →
      I.length = n → K t I = K' t I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht I hI h2 hIn
      have hn : 2 ≤ n := hIn ▸ h2
      refine eq_on_level L hL W K K' T₀ R n hR0
        (fun s hs J hJ hJn => hK.1 s (hT hs) J hJ (hJn ▸ hn))
        (fun s hs J hJ hJn => hK'.1 s (hT hs) J hJ (hJn ▸ hn)) hR ?_ ?_ t ht I hI hIn
      · intro s hs J hJ hJ2 hJn
        exact ih _ hJn s hs J hJ hJ2 rfl
      · intro J hJ hJn
        rw [hK.2.1 J hJ (hJn ▸ hn), hK'.2.1 J hJ (hJn ▸ hn)]
  exact fun t ht I hI h2 => main _ t ht I hI h2 rfl

end RBM
