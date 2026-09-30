/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.EGDef
import RBM1D.Gauss.Model
import RBM1D.Gauss.DimsExample

/-!
# Centered block one-loops at both charges on one Gaussian sample

Conjugation of a Hermitian resolvent identifies the two centered block traces
at exactly the same spectral parameter, time, block, and sample.
-/

namespace RBM.TwoChargeOneLoop

open Matrix

theorem centered_block_trace_false_eq_conj_true (L W : ℕ) [NeZero L]
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (hM : M.IsHermitian)
    (z : ℂ) (m : ℂ) (b : ZMod L) :
    Matrix.trace ((Gsig M z false - (starRingEnd ℂ) m •
        (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W b)
      = (starRingEnd ℂ) (Matrix.trace ((Gsig M z true - m •
        (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W b)) := by
  let A : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
    Gsig M z true - m • 1
  have hA : Aᴴ = Gsig M z false - (starRingEnd ℂ) m • 1 := by
    simp only [A, Matrix.conjTranspose_sub, Gsig_conjTranspose hM,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    rfl
  rw [← hA, ← Complex.star_def, ← Matrix.trace_conjTranspose]
  rw [Matrix.conjTranspose_mul, Eblk_conjTranspose, Matrix.trace_mul_comm]

end RBM.TwoChargeOneLoop
