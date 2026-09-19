/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.GLoop

/-!
# `G`-chains (Appendix A)

Definition A.1 of the paper: for charges `tau = (s_1, ..., s_n)` and labels
`a = (a_1, ..., a_{n-1})`,

  `C_{tau,a} = G(s_1) E_{a_1} G(s_2) E_{a_2} ... E_{a_{n-1}} G(s_n)`.

The paper notes that these results are not used in the main theorem but may be useful
later.  Everything here is deterministic: a fixed Hermitian `H`, no expectation.

## Main results

* `gchain_snoc` : appending one `E G` block at the end.
* `gchain_conjTranspose` : `C† = C'` where `C'` is the chain with the charge list
  reversed and flipped.  **A chain conjugates to a chain**; for loops the same
  computation produces a cyclic shift instead, which is why the loop statement is the
  awkward one.
* `trace_gchain_mul_Eblk` : a chain becomes a loop, `⟨C_{tau,a} E_b⟩ = L_{tau, a ++ [b]}`.
-/

namespace RBM

open Matrix

section Chain

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- **Definition A.1**: the `G`-chain of charges `tau` and labels `a`.
The intended shape is `tau.length = a.length + 1`; other shapes are harmless. -/
noncomputable def gchain (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) :
    List Bool → List (ZMod L) → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ
  | [], _ => 1
  | s :: _, [] => Gsig H z s
  | s :: tau, b :: a => Gsig H z s * Eblk L W b * gchain H z tau a

variable {L W} {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

@[simp] theorem gchain_nil (a : List (ZMod L)) : gchain L W H z [] a = 1 := by
  cases a <;> rfl

@[simp] theorem gchain_single (s : Bool) : gchain L W H z [s] [] = Gsig H z s := rfl

@[simp] theorem gchain_cons (s : Bool) (b : ZMod L) (tau : List Bool) (a : List (ZMod L)) :
    gchain L W H z (s :: tau) (b :: a) = Gsig H z s * Eblk L W b * gchain L W H z tau a := rfl

/-- Appending one block at the end of a chain. -/
theorem gchain_append_one {tau : List Bool} {a : List (ZMod L)}
    (h : tau.length = a.length + 1) (s : Bool) (b : ZMod L) :
    gchain L W H z (tau ++ [s]) (a ++ [b])
      = gchain L W H z tau a * Eblk L W b * Gsig H z s := by
  induction tau generalizing a with
  | nil => simp at h
  | cons t tau ih =>
    cases a with
    | nil =>
      have htau : tau = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst htau
      simp [gchain, Matrix.mul_assoc]
    | cons c a =>
      have h' : tau.length = a.length + 1 := by simpa using h
      simp only [List.cons_append, gchain_cons, ih h', Matrix.mul_assoc]

/-- **A chain conjugates to a chain.**  `C† = C'`, where `C'` has the charge list
reversed and flipped and the labels reversed.  No cyclic shift appears -- that is the
difference between a chain and a loop. -/
theorem gchain_conjTranspose (hH : H.IsHermitian) {tau : List Bool} {a : List (ZMod L)}
    (h : tau.length = a.length + 1) :
    (gchain L W H z tau a)ᴴ = gchain L W H z (tau.map (!·)).reverse a.reverse := by
  induction tau generalizing a with
  | nil => simp at h
  | cons t tau ih =>
    cases a with
    | nil =>
      have htau : tau = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst htau
      simp [gchain, Gsig_conjTranspose hH]
    | cons c a =>
      have h' : tau.length = a.length + 1 := by simpa using h
      have hlen : (tau.map (!·)).reverse.length = a.reverse.length + 1 := by
        simpa using h'
      rw [gchain_cons, conjTranspose_mul, conjTranspose_mul, ih h',
        Eblk_conjTranspose, Gsig_conjTranspose hH]
      simp only [List.map_cons, List.reverse_cons, List.reverse_cons]
      rw [gchain_append_one hlen, Matrix.mul_assoc]

/-- **A chain closed by one `E` is a loop product** (matrix level). -/
theorem gchain_mul_Eblk {tau : List Bool} {a : List (ZMod L)}
    (h : tau.length = a.length + 1) (b : ZMod L) :
    gchain L W H z tau a * Eblk L W b = gloopProd L W H z ⟨tau, a ++ [b]⟩ := by
  induction tau generalizing a with
  | nil => simp at h
  | cons t tau ih =>
    cases a with
    | nil =>
      have htau : tau = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst htau
      simp [gchain, gloopProd_cons, gloopProd_nil]
    | cons c a =>
      have h' : tau.length = a.length + 1 := by simpa using h
      rw [gchain_cons, List.cons_append, gloopProd_cons, Matrix.mul_assoc, ih h']

/-- **A chain becomes a loop** (Appendix A): `⟨C_{tau,a} E_b⟩ = L_{tau, a ++ [b]}`. -/
theorem trace_gchain_mul_Eblk {tau : List Bool} {a : List (ZMod L)}
    (h : tau.length = a.length + 1) (b : ZMod L) :
    Matrix.trace (gchain L W H z tau a * Eblk L W b) = gloop L W H z ⟨tau, a ++ [b]⟩ := by
  rw [gloop, gchain_mul_Eblk h b]

end Chain

end RBM
