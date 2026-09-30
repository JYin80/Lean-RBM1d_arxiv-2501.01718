/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.RowIndep

/-!
# The identifications behind the large deviation hypotheses of `Green/EntryBound.lean`

Lemma 4.1 takes the paper's large deviation estimate for the row and column sums of (4.8) as a
hypothesis, in the form

* `StochDom P (ldeRowLHS (H N ω) (G N ω)) (ldeRowRHS S (G N ω))`,
* `StochDom P (ldeColLHS (H N ω) (G N ω)) (ldeColRHS S (G N ω))`.

For the Gaussian flow `H = H_u` these follow from the Gaussian row-sum bounds of
`Gauss/RowIndep.lean`, once three gaps are closed:

1. the identification of `ldeRowLHS`/`ldeColLHS` with the squared row sum and of the row
   variance with `u · ldeRowRHS` needs `H - z` invertible and `G_{ii} ≠ 0`.  Both hold **for
   every `ω`** when `Im z ≠ 0`: the first is `RBM.isUnit_det_sub_smul_one`, the second is
   `RBM.green_diag_ne_zero`, proved here from the Ward identity `Im G_{ii} = Im z · ‖G e_i‖²`;
2. the normalised bound `‖Z‖/√V ≺ 1` says nothing where `V = 0`, whereas the LDE inequality
   requires `Z = 0` there.  This is the a.s. argument
   `RBM.Gauss.rowSum_ae_eq_zero_of_varSum_eq_zero`;
3. the variance carries the factor `u`, which is harmless for `u ≤ 1`.

## Main statements

* `RBM.green_diag_ne_zero`         : `G_{ii} ≠ 0` for Hermitian `H` and `Im z ≠ 0`
* `RBM.Gauss.isUnit_det_Hflow_sub`, `RBM.Gauss.green_Hflow_diag_ne_zero` : the two side
  conditions for every `ω`
* `RBM.Gauss.ldeColLHS_eq`, `RBM.Gauss.rowVarSum_minorRowConj_eq` : the column identification,
  through the conjugated minor row
-/

namespace RBM

open MeasureTheory Matrix Finset

open scoped ComplexOrder

/-! ### The diagonal Green function never vanishes off the real axis -/

section GreenDiag

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Ward identity at one site.**  For Hermitian `H` and `Im z ≠ 0`, writing
`v = G e_i`, we have `Im G_{ii} = Im z · ‖v‖²`: indeed `G_{ii} = ⟪v, (H - z) v⟫`-bar and the
Hermitian part contributes nothing to the imaginary part. -/
theorem im_green_diag {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : n) :
    (green H z i i).im
      = z.im * (star (green H z *ᵥ Pi.single i 1) ⬝ᵥ (green H z *ᵥ Pi.single i 1)).re := by
  have hdet : IsUnit (H - z • (1 : Matrix n n ℂ)).det := isUnit_det_sub_smul_one hH hz
  set v : n → ℂ := green H z *ᵥ Pi.single i 1 with hv
  have hvi : v i = green H z i i := by
    rw [hv]; simp
  have hMv : (H - z • (1 : Matrix n n ℂ)) *ᵥ v = Pi.single i 1 := by
    rw [hv, Matrix.mulVec_mulVec, self_mul_green hdet, Matrix.one_mulVec]
  have hsplit : star v ⬝ᵥ ((H - z • (1 : Matrix n n ℂ)) *ᵥ v)
      = star v ⬝ᵥ (H *ᵥ v) - z * (star v ⬝ᵥ v) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
  rw [hMv, dotProduct_single_one] at hsplit
  have hHim : (star v ⬝ᵥ H *ᵥ v).im = 0 := by
    simpa [RCLike.im_to_complex] using hH.im_star_dotProduct_mulVec_self v
  have hself : (star v ⬝ᵥ v).im = 0 := by
    have := dotProduct_star_self_nonneg v
    rw [Complex.le_def] at this
    exact this.2.symm
  have := congrArg Complex.im hsplit
  rw [Complex.sub_im, hHim, Complex.mul_im, hself] at this
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_im, hvi] at this
  linarith [this]

/-- **`G_{ii} ≠ 0`.**  For Hermitian `H` and `Im z ≠ 0` the diagonal Green function is never
zero, because its imaginary part is `Im z` times the (positive) squared norm of a column of
`G`.  This is the side condition of `RBM.inv_minor_resolvent`, and it holds for *every*
matrix, with no exceptional set. -/
theorem green_diag_ne_zero {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (i : n) : green H z i i ≠ 0 := by
  have hdet : IsUnit (H - z • (1 : Matrix n n ℂ)).det := isUnit_det_sub_smul_one hH hz
  set v : n → ℂ := green H z *ᵥ Pi.single i 1 with hv
  have hMv : (H - z • (1 : Matrix n n ℂ)) *ᵥ v = Pi.single i 1 := by
    rw [hv, Matrix.mulVec_mulVec, self_mul_green hdet, Matrix.one_mulVec]
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hMv
    have h1 := congrFun hMv i
    simp at h1
  have hpos : (0 : ℂ) < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.2 hvne
  rw [Complex.lt_def] at hpos
  have hre : (0 : ℝ) < (star v ⬝ᵥ v).re := by simpa using hpos.1
  intro hzero
  have him := im_green_diag hH hz i
  rw [hzero] at him
  simp only [Complex.zero_im] at him
  have : z.im = 0 := by
    rcases mul_eq_zero.1 him.symm with h | h
    · exact h
    · exact absurd h (ne_of_gt hre)
  exact hz this

end GreenDiag

namespace Gauss

open ProbabilityTheory

variable {d : Dims} {N : ℕ} {u : ℝ} {z : ℂ}

/-! ### The side conditions hold for every `ω` -/

theorem isUnit_det_Hflow_sub (d : Dims) (N : ℕ) (u : ℝ) (ω : Ω d) (hz : z.im ≠ 0) :
    IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det :=
  isUnit_det_sub_smul_one (Hflow_isHermitian d N u ω) hz

theorem green_Hflow_diag_ne_zero (d : Dims) (N : ℕ) (u : ℝ) (ω : Ω d) (hz : z.im ≠ 0)
    (i : d.Idx N) : green (Hflow d N u ω) z i i ≠ 0 :=
  green_diag_ne_zero (Hflow_isHermitian d N u ω) hz i

/-! ### The column LDE: the conjugated minor row -/

/-- Where the resolvent exists, the coefficients `minorRowConj` are the conjugated entries of
`G^{(j)}`. -/
theorem minorRowConj_eq_greenMinor (u : ℝ) {j : d.Idx N} (k : {a : d.Idx N // a ≠ j}) {ω : Ω d}
    (hdet : IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hGjj : green (Hflow d N u ω) z j j ≠ 0) {l : d.Idx N} (hl : l ≠ j) :
    minorRowConj d N u z j k ω l
      = (starRingEnd ℂ) (greenMinor (green (Hflow d N u ω) z) j k.1 l) := by
  unfold minorRowConj
  rw [dite_eq_left_of_eq_true (by simpa using hl), inv_minor_resolvent hdet j hGjj]
  rfl

/-- **The left-hand side of the column LDE** is the row sum with the conjugated minor row: the
column sum `∑_{l ≠ j} G^{(j)}_{kl} H_{lj}` is the conjugate of `∑_{l ≠ j} H_{jl} conj G^{(j)}_{kl}`
by Hermitian symmetry of `H`. -/
theorem ldeColLHS_eq (u : ℝ) {j : d.Idx N} (k : {a : d.Idx N // a ≠ j}) {ω : Ω d}
    (hdet : IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hGjj : green (Hflow d N u ω) z j j ≠ 0) :
    ldeColLHS (Hflow d N u ω) (green (Hflow d N u ω) z) k.1 j
      = ‖rowSum d N u j (minorRowConj d N u z j k) ω‖ ^ 2 := by
  have key : rowSum d N u j (minorRowConj d N u z j k) ω
      = (starRingEnd ℂ) (∑ l ∈ Finset.univ.erase j,
          greenMinor (green (Hflow d N u ω) z) j k.1 l * Hflow d N u ω l j) := by
    unfold rowSum
    rw [map_sum, Finset.sum_subtype (p := fun l => l ≠ j) (Finset.univ.erase j)
      (fun l => by simp [Finset.mem_erase]) _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [minorRowConj_eq_greenMinor u k hdet hGjj l.2, map_mul,
      show (starRingEnd ℂ) (Hflow d N u ω l.1 j) = Hflow d N u ω j l.1 from
        (Hflow_isHermitian d N u ω).apply j l.1]
    ring
  rw [key, Complex.norm_conj, ldeColLHS]

/-- **The right-hand side of the column LDE** is the variance of that row sum, up to the factor
`u` (using `S_{jl} = S_{lj}`). -/
theorem rowVarSum_minorRowConj_eq (u : ℝ) {j : d.Idx N} (k : {a : d.Idx N // a ≠ j}) {ω : Ω d}
    (hdet : IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hGjj : green (Hflow d N u ω) z j j ≠ 0) :
    rowVarSum d N u j (minorRowConj d N u z j k) ω
      = u * ldeColRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) z) k.1 j := by
  unfold rowVarSum ldeColRHS
  congr 1
  rw [Finset.sum_subtype (p := fun l => l ≠ j) (Finset.univ.erase j)
    (fun l => by simp [Finset.mem_erase]) _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [minorRowConj_eq_greenMinor u k hdet hGjj l.2, Complex.norm_conj,
    Sblk_comm (d.L N) (d.W N) j l.1]
  ring

/-! ### The bridge from the normalised row sum to stochastic domination -/

end Gauss

end RBM
