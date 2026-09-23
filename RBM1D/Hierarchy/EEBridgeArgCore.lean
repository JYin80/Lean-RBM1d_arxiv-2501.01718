/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DischargeBDG

/-!
# Doubled-argument adapter for Definition 5.4

The two `n`-label arguments feeding the glued `(2n+2)`-loop in (5.22)–(5.23)
use `Fin.append`.
This module contains the pure `E ⊗ E` argument adapter, below the `SumZeroDyn`
producer boundary.
-/

namespace RBM
namespace EEBridge

open Matrix RBM.Gauss

/-! ### (b) The type adaptation `LoopIdx` ↔ `LoopArg L (m + m)` -/

section Arg

variable {L : ℕ}

/-- The first half of a doubled loop argument (the convention of `RBM.SumZeroDyn.QQ` and of the
`bdg` field, i.e. the left inverse of `Fin.append`). -/
def leftArg {n : ℕ} (c : LoopArg L (n + n)) : LoopArg L n := fun i => c (Fin.castAdd n i)

/-- The second half of a doubled loop argument. -/
def rightArg {n : ℕ} (c : LoopArg L (n + n)) : LoopArg L n := fun i => c (Fin.natAdd n i)

@[simp] theorem leftArg_append {n : ℕ} (a a' : LoopArg L n) : leftArg (Fin.append a a') = a := by
  funext i; rw [leftArg, Fin.append_left]

@[simp] theorem rightArg_append {n : ℕ} (a a' : LoopArg L n) :
    rightArg (Fin.append a a') = a' := by
  funext i; rw [rightArg, Fin.append_right]

end Arg

section EeArg

/-- **`E ⊗ E` in the shape of `RBM.SumZeroDyn.Hierarchy.EE`**: a charge vector `σ : Fin n → Bool`
and a single doubled argument `LoopArg L (n + n)`, the two halves being the labels `a`, `a'` of
the two factors of Definition 5.4.  The charges of the second factor are again `σ`; it is read
as the complex conjugate (T74's convention, `docs/paper-deltas.md`), which
`RBM.EEBridge.glueLoop_prodList` shows is the `σ`-loop reversed with flipped charges. -/
noncomputable def eeArg (d : Gauss.Dims) (N : ℕ) (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    {n : ℕ} (σ : Fin n → Bool) (c : LoopArg (d.L N) (n + n)) : ℂ :=
  eeTens d N z M (toIdx σ (leftArg c)) (toIdx σ (rightArg c))

theorem eeArg_append (d : Gauss.Dims) (N : ℕ) (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    {n : ℕ} (σ : Fin n → Bool) (a a' : LoopArg (d.L N) n) :
    eeArg d N z M σ (Fin.append a a') = eeTens d N z M (toIdx σ a) (toIdx σ a') := by
  rw [eeArg, leftArg_append, rightArg_append]

end EeArg

end EEBridge
end RBM
