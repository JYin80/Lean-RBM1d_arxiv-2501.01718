/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Model
import RBM1D.Delocalization
import RBM1D.Loop.Index

/-!
# The `G`-loops of Definition 2.9

For a **fixed deterministic Hermitian** `H` we define

  `G(σ) = (H - z)⁻¹` for `σ = +` and `(H - z̄)⁻¹` for `σ = -`,   (Definition 2.9)
  `L_{σ,a} = ⟨∏_i G(σ_i) E_{a_i}⟩`,  `⟨A⟩ = Tr A`.               (2.41)

Nothing here is probabilistic: the expectation and the Itô calculus of the paper
act on top of this layer, but the definition of the loop and its algebra are
deterministic, and that is what this file provides.

## Main results

* `Gsig_conjTranspose` : `G(σ)† = G(-σ)`, the paper's `G_{t,+}† = G_{t,-}`.
* `green_sub_green` : the resolvent identity `G(z) - G(w) = (z-w) G(z) G(w)`,
  the source of every Ward identity downstream.
* `gloopProd_append`, `gloop_rotate` : the loop is invariant under rotating its
  index data, which is the algebraic content of "loop" in the paper.
-/

namespace RBM

open Matrix

section Gsig

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `G(σ)`: the resolvent at `z` for `σ = true` (the paper's `+`) and at `conj z`
for `σ = false`. -/
noncomputable def Gsig (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) : Matrix n n ℂ :=
  green H (if σ then z else (starRingEnd ℂ) z)

@[simp] theorem Gsig_true (H : Matrix n n ℂ) (z : ℂ) : Gsig H z true = green H z := rfl

@[simp] theorem Gsig_false (H : Matrix n n ℂ) (z : ℂ) :
    Gsig H z false = green H ((starRingEnd ℂ) z) := rfl

/-- `(H - z)ᴴ = H - z̄` for Hermitian `H`. -/
theorem conjTranspose_sub_smul {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ) :
    (H - z • (1 : Matrix n n ℂ))ᴴ = H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ) := by
  rw [conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one]
  rfl

/-- **`G(+)† = G(-)`** (Definition 2.9). -/
theorem Gsig_conjTranspose {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gsig H z σ)ᴴ = Gsig H z (!σ) := by
  cases σ
  · show (green H ((starRingEnd ℂ) z))ᴴ = green H z
    rw [green, green, conjTranspose_nonsing_inv, conjTranspose_sub_smul hH, Complex.conj_conj]
  · show (green H z)ᴴ = green H ((starRingEnd ℂ) z)
    rw [green, green, conjTranspose_nonsing_inv, conjTranspose_sub_smul hH]

/-- **The resolvent identity** `G(z) - G(w) = (z - w) • (G(z) * G(w))`.
Every Ward identity in the paper descends from this one line. -/
theorem green_sub_green {H : Matrix n n ℂ} {z w : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ))) (hw : IsUnit (H - w • (1 : Matrix n n ℂ))) :
    green H z - green H w = (z - w) • (green H z * green H w) := by
  have hz' : green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_isUnit_det _ |>.mp hz)
  have hw' : (H - w • (1 : Matrix n n ℂ)) * green H w = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.mp hw)
  calc green H z - green H w
      = green H z * ((H - w • (1 : Matrix n n ℂ)) * green H w)
        - (green H z * (H - z • (1 : Matrix n n ℂ))) * green H w := by
        rw [hz', hw', Matrix.one_mul, Matrix.mul_one]
    _ = green H z * ((H - w • (1 : Matrix n n ℂ)) - (H - z • (1 : Matrix n n ℂ)))
        * green H w := by
        noncomm_ring
    _ = green H z * ((z - w) • (1 : Matrix n n ℂ)) * green H w := by
        congr 2
        module
    _ = (z - w) • (green H z * green H w) := by
        simp [mul_smul_comm, smul_mul_assoc]

/-- **The Ward identity in resolvent form.**  With `z = E + iη`,
`G(z) - G(z̄) = 2iη · G(z)G(z̄)`, i.e. `Im G = η G G†`.  This is the special case
`w = z̄` of `green_sub_green`, and it is the form used throughout the paper. -/
theorem green_sub_green_conj {H : Matrix n n ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ))) :
    green H z - green H ((starRingEnd ℂ) z)
      = (2 * Complex.I * (z.im : ℂ)) • (green H z * green H ((starRingEnd ℂ) z)) := by
  rw [green_sub_green hz hz']
  congr 1
  rw [Complex.sub_conj]
  push_cast
  ring

end Gsig

section Loop

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The matrix product `∏_i G(σ_i) E_{a_i}` of (2.41). -/
noncomputable def gloopProd (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  (I.σ.zip I.a).foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M) 1

/-- **The `n`-`G` loop of (2.41)**, `L_{σ,a} = ⟨∏_i G(σ_i) E_{a_i}⟩`. -/
noncomputable def gloop (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) : ℂ :=
  Matrix.trace (gloopProd L W H z I)

variable {L W} {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

@[simp] theorem gloopProd_nil : gloopProd L W H z ⟨[], []⟩ = 1 := rfl

@[simp] theorem gloopProd_cons (s : Bool) (b : ZMod L) (σ : List Bool) (a : List (ZMod L)) :
    gloopProd L W H z ⟨s :: σ, b :: a⟩
      = Gsig H z s * Eblk L W b * gloopProd L W H z ⟨σ, a⟩ := rfl

/-- The loop product of a concatenation is the product of the loop products.
Requires the two blocks to be well formed, so that `zip` distributes. -/
theorem gloopProd_append {σ₁ : List Bool} {a₁ : List (ZMod L)} (h₁ : σ₁.length = a₁.length)
    (σ₂ : List Bool) (a₂ : List (ZMod L)) :
    gloopProd L W H z ⟨σ₁ ++ σ₂, a₁ ++ a₂⟩
      = gloopProd L W H z ⟨σ₁, a₁⟩ * gloopProd L W H z ⟨σ₂, a₂⟩ := by
  induction σ₁ generalizing a₁ with
  | nil =>
    obtain rfl : a₁ = [] := List.eq_nil_of_length_eq_zero h₁.symm
    simp
  | cons s σ ih =>
    obtain ⟨b, a, rfl⟩ : ∃ b a, a₁ = b :: a := by
      cases a₁ with
      | nil => simp at h₁
      | cons b a => exact ⟨b, a, rfl⟩
    have h : σ.length = a.length := by simpa using h₁
    simp only [List.cons_append, gloopProd_cons, ih h, Matrix.mul_assoc]

/-- **The loop is a loop**: rotating the index data by one place does not change it.
This is the trace cyclicity behind every "loop" statement in the paper. -/
theorem gloop_rotate (s : Bool) (b : ZMod L) {σ : List Bool} {a : List (ZMod L)}
    (h : σ.length = a.length) :
    gloop L W H z ⟨s :: σ, b :: a⟩ = gloop L W H z ⟨σ ++ [s], a ++ [b]⟩ := by
  rw [gloop, gloop, gloopProd_cons, gloopProd_append h [s] [b]]
  rw [Matrix.trace_mul_comm]
  simp only [gloopProd_cons, gloopProd_nil, Matrix.mul_one]

/-- **Summing one block index.**  Because `∑_a E_a = W⁻¹ I` (`sum_Eblk`), summing a
loop over one of its labels deletes that `E` and produces a factor `W⁻¹`.
This is the first step of the paper's Ward identity for loops. -/
theorem sum_gloop_head (s : Bool) (σ : List Bool) (a : List (ZMod L)) :
    ∑ b : ZMod L, gloop L W H z ⟨s :: σ, b :: a⟩
      = (W : ℂ)⁻¹ * Matrix.trace (Gsig H z s * gloopProd L W H z ⟨σ, a⟩) := by
  have hterm : ∀ b : ZMod L, gloop L W H z ⟨s :: σ, b :: a⟩
      = Matrix.trace (Gsig H z s * Eblk L W b * gloopProd L W H z ⟨σ, a⟩) := fun _ => rfl
  simp_rw [hterm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, sum_Eblk L W]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

end Loop

end RBM
