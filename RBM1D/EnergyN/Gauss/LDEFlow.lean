/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDEFlow

/-!
# The row and column large-deviation bounds along the flow, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`: the large-deviation bounds
`ldeRowLHS ≤ ldeRowRHS` and `ldeColLHS ≤ ldeColRHS` for the Green function of the flow, uniformly
on `[s, t]` (`RBM.Gauss.unifDomIcc_ldeRowN`, `RBM.Gauss.unifDomIcc_ldeColN`).

No energy-dependent constant is fixed in them: every `zt E`/(mE E)-use is pointwise per fixed
`(N,u)` inside the tactic block; the generic (`E`-free) engine `unifDomIcc_sq_of_rowSum` is used
unchanged.
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset Matrix

variable {d : Dims} {s t : ℕ → ℝ} {E : ℕ → ℝ}

/-- **The row large-deviation bound `ldeRowLHS ≤ ldeRowRHS`** for the Green function of the flow,
uniformly on `[s, t]` and over off-diagonal pairs. -/
theorem unifDomIcc_ldeRowN (d : Dims) (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) :
    UnifDomIcc (P d) s t
      (fun N u (p : OffPair d.L d.W N) ω =>
        ldeRowLHS (Hflow d N u ω) (green (Hflow d N u ω) (zt (E N) u)) p.1.1 p.1.2)
      (fun N u (p : OffPair d.L d.W N) ω =>
        ldeRowRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt (E N) u)) p.1.1 p.1.2) := by
  refine unifDomIcc_sq_of_rowSum hs0 (fun N => (ht1 N).le)
    (U := fun N => LdeIdx d N) (fun N q => q.1)
    (fun N u q => minorCol d N u (zt (E N) u) q.1 q.2)
    (fun N u q => measurable_minorCol u (zt (E N) u) q.1 q.2)
    (fun N u q ω ω' h => minorCol_congr u (zt (E N) u) q.2 h)
    (V := fun N => OffPair d.L d.W N)
    (fun N p => (⟨p.1.1, ⟨p.1.2, Ne.symm p.2⟩⟩ : LdeIdx d N)) _ _ ?_ ?_ ?_
  · intro N u _ p ω
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Sblk_nonneg _ _) (by positivity)
  · intro N u hu p ω
    have hz : (zt (E N) u).im ≠ 0 := zt_im_ne_zero_of_lt_one (hE N) (lt_of_le_of_lt hu.2 (ht1 N))
    exact ldeRowLHS_eq u ⟨p.1.2, Ne.symm p.2⟩ (isUnit_det_Hflow_sub d N u ω hz)
      (green_Hflow_diag_ne_zero d N u ω hz p.1.1)
  · intro N u hu p ω
    have hz : (zt (E N) u).im ≠ 0 := zt_im_ne_zero_of_lt_one (hE N) (lt_of_le_of_lt hu.2 (ht1 N))
    exact rowVarSum_eq u ⟨p.1.2, Ne.symm p.2⟩ (isUnit_det_Hflow_sub d N u ω hz)
      (green_Hflow_diag_ne_zero d N u ω hz p.1.1)

/-- **The column large-deviation bound `ldeColLHS ≤ ldeColRHS`**, the companion of
`unifDomIcc_ldeRowN`, by Hermitian symmetry. -/
theorem unifDomIcc_ldeColN (d : Dims) (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) :
    UnifDomIcc (P d) s t
      (fun N u (p : OffPair d.L d.W N) ω =>
        ldeColLHS (Hflow d N u ω) (green (Hflow d N u ω) (zt (E N) u)) p.1.1 p.1.2)
      (fun N u (p : OffPair d.L d.W N) ω =>
        ldeColRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt (E N) u)) p.1.1 p.1.2) := by
  refine unifDomIcc_sq_of_rowSum hs0 (fun N => (ht1 N).le)
    (U := fun N => LdeIdx d N) (fun N q => q.1)
    (fun N u q => minorRowConj d N u (zt (E N) u) q.1 q.2)
    (fun N u q => measurable_minorRowConj u (zt (E N) u) q.1 q.2)
    (fun N u q ω ω' h => minorRowConj_congr u (zt (E N) u) q.2 h)
    (V := fun N => OffPair d.L d.W N)
    (fun N p => (⟨p.1.2, ⟨p.1.1, p.2⟩⟩ : LdeIdx d N)) _ _ ?_ ?_ ?_
  · intro N u _ p ω
    exact Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (Sblk_nonneg _ _)
  · intro N u hu p ω
    have hz : (zt (E N) u).im ≠ 0 := zt_im_ne_zero_of_lt_one (hE N) (lt_of_le_of_lt hu.2 (ht1 N))
    exact ldeColLHS_eq u ⟨p.1.1, p.2⟩ (isUnit_det_Hflow_sub d N u ω hz)
      (green_Hflow_diag_ne_zero d N u ω hz p.1.2)
  · intro N u hu p ω
    have hz : (zt (E N) u).im ≠ 0 := zt_im_ne_zero_of_lt_one (hE N) (lt_of_le_of_lt hu.2 (ht1 N))
    exact rowVarSum_minorRowConj_eq u ⟨p.1.1, p.2⟩ (isUnit_det_Hflow_sub d N u ω hz)
      (green_Hflow_diag_ne_zero d N u ω hz p.1.2)

end RBM.Gauss
