/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FlucAvg
import RBM1D.Gauss.SteinMatrix

/-!
# T83: the Gaussian integration-by-parts display of p. 50

The target is the hypothesis `hIBP` of `RBM.Gauss.trace_green_sub_mul_Eblk_stochDom`
(T88, `RBM1D/Gauss/FlucAvg.lean`), i.e. the display on p. 50 of the paper:

  `E_i(G_ii - m) = E_i[m(-H - tm)G]_ii = t m² ∑_k S_ik (G_kk - m) + O≺(Ψ²)`.

It splits into three steps.

1. **The algebraic identity** `G - m = m(-H - tm)G`, which rests on `m = -(tm + z_t)⁻¹`.
   That is this file's first section, and it is pure matrix algebra: no probability.
2. **Gaussian integration by parts** for each entry `H_ik`, i.e. the matrix Stein identity
   `RBM.Gauss.matrixStein` of T70 (`RBM1D/Gauss/SteinMatrix.lean`), which replaces `ω_α` by
   `gvar α · ∂_α`.  The derivative of a resolvent entry is again a product of resolvent
   entries, and `‖G‖ ≤ η⁻¹` is a *deterministic global* bound (T77's envelope), so the
   global boundedness hypotheses of `MatrixStein` are met without any cutoff.
3. **Removing the minor superscript** with (4.9), i.e. `E_i(G_kk - m) = G_kk - m + O≺(Ψ²)`,
   which is T85 (`RBM1D/Gauss/MinorReplace.lean`).

**Do not change** the statement `hIBP` is consumed at: `RBM1D/Green/EntryBound.lean` and
`RBM1D/Gauss/FlucAvg.lean` are both frozen interfaces.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ### Step 1: the algebraic identity `G - m = m(-H - tm)G`

Everything here is deterministic. -/

section Algebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `t·m + z_t = m + E`: the flow keeps the self-consistent equation in the form of
`RBM.mE_mul`. -/
theorem smul_add_zt (E t : ℝ) : (t : ℂ) * mE E + zt E t = mE E + E := by
  simp only [zt]
  ring

/-- **`m = -(t m + z_t)⁻¹`**, the self-consistent equation along the flow.  This is the one
fact the identity of this section rests on. -/
theorem mE_mul_smul_add_zt {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    mE E * ((t : ℂ) * mE E + zt E t) = -1 := by
  rw [smul_add_zt]
  exact mE_mul hE

/-- **The identity `G - m = m(-H - tm)G` of p. 50.**  Taking the `ii` entry of this and
applying `E_i` is the first step of the integration-by-parts display. -/
theorem green_sub_smul_one_eq {H : Matrix n n ℂ} (hH : H.IsHermitian) {E t : ℝ}
    (hE : |E| ≤ 2) (hz : (zt E t).im ≠ 0) :
    green H (zt E t) - mE E • (1 : Matrix n n ℂ)
      = mE E • ((-H - ((t : ℂ) * mE E) • (1 : Matrix n n ℂ)) * green H (zt E t)) := by
  have hGH : (H - (zt E t) • (1 : Matrix n n ℂ)) * green H (zt E t) = 1 :=
    sub_mul_green_of_im hH hz
  have hkey : mE E * ((t : ℂ) * mE E + zt E t) = -1 := mE_mul_smul_add_zt hE t
  have hsplit : (-H - ((t : ℂ) * mE E) • (1 : Matrix n n ℂ))
      = -(H - (zt E t) • (1 : Matrix n n ℂ))
        - (((t : ℂ) * mE E + zt E t) • (1 : Matrix n n ℂ)) := by
    rw [add_smul]
    abel
  rw [hsplit, sub_mul, neg_mul, hGH, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_neg,
    smul_smul, hkey, neg_smul, one_smul]
  abel

end Algebra

end RBM.Gauss
