/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Model
import RBM1D.Green.Minor
import RBM1D.Gauss.LinearForm

/-!
# The minor resolvent does not read row `i`

The large deviation estimates of T81/T82 rest on one structural fact: `G^(i)`, the resolvent of
`H` with row and column `i` removed, is a function of the coordinates **outside** row `i`, hence
independent of the Gaussian entries `H_{ik}`, `k ≠ i`, that multiply it.

Here that fact is proved in the form the model needs: if two sample points agree on every
coordinate whose index pair avoids `i`, then

* the entries `X_{kl}`, `k, l ≠ i`, agree (`Xentry_congr_of_ne`),
* hence the minor matrices agree (`Hflow_submatrix_congr`),
* hence, where the resolvents exist, the minor Green functions agree
  (`greenMinor_congr_of_offRow`).

The last statement is exactly "`G^(i)` is `FinDep` with a witness set avoiding row `i`", in the
concrete form used by the moment computations.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {d : Dims} {N : ℕ}

/-- Two sample points **agree off row `i`** when every coordinate at size `N` whose index pair
avoids `i` carries the same value. -/
def AgreeOffRow (d : Dims) (N : ℕ) (i : d.Idx N) (ω ω' : Ω d) : Prop :=
  ∀ (k l : d.Idx N) (b : Bool), k ≠ i → l ≠ i → ω ⟨N, k, l, b⟩ = ω' ⟨N, k, l, b⟩

/-- The entries of `X` away from row and column `i` only read coordinates that avoid `i`. -/
theorem Xentry_congr_of_ne {i : d.Idx N} {ω ω' : Ω d} (h : AgreeOffRow d N i ω ω')
    {k l : d.Idx N} (hk : k ≠ i) (hl : l ≠ i) :
    Xentry d N ω k l = Xentry d N ω' k l := by
  unfold Xentry
  split_ifs with h1 h2
  · rw [h k l true hk hl, h k l false hk hl]
  · rw [h l k true hl hk, h l k false hl hk]
  · rw [h k l true hk hl]

/-- The minor matrix of `H_u` at `i` only reads coordinates that avoid `i`. -/
theorem Hflow_submatrix_congr (u : ℝ) {i : d.Idx N} {ω ω' : Ω d} (h : AgreeOffRow d N i ω ω') :
    (Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
      = (Hflow d N u ω').submatrix (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N) := by
  ext k l
  simp only [Matrix.submatrix_apply, Hflow_apply]
  rw [Xentry_congr_of_ne h k.2 l.2]

/-- **`G^(i)` does not read row `i`.**  Where both resolvents exist and both diagonal entries
are nonzero, the minor Green function at `i` is unchanged by the coordinates of row `i`. -/
theorem greenMinor_congr_of_offRow (u : ℝ) (z : ℂ) {i : d.Idx N} {ω ω' : Ω d}
    (h : AgreeOffRow d N i ω ω')
    (hdet : IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hdet' : IsUnit (Hflow d N u ω' - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hGii : green (Hflow d N u ω) z i i ≠ 0)
    (hGii' : green (Hflow d N u ω') z i i ≠ 0) (k l : {a : d.Idx N // a ≠ i}) :
    greenMinor (green (Hflow d N u ω) z) i k.1 l.1
      = greenMinor (green (Hflow d N u ω') z) i k.1 l.1 := by
  have e := inv_minor_resolvent hdet i hGii
  have e' := inv_minor_resolvent hdet' i hGii'
  have hsub := Hflow_submatrix_congr (d := d) (N := N) u h
  have : minorGreen (green (Hflow d N u ω) z) i = minorGreen (green (Hflow d N u ω') z) i := by
    rw [← e, ← e', hsub]
  exact congrFun (congrFun this k) l

/-! ### The coordinates of row `i` -/

open Finset

/-- The coordinates of row `i` at size `N`: those whose index pair contains `i`. -/
def rowSet (d : Dims) (N : ℕ) (i : d.Idx N) : Finset (Coord d) :=
  (univ : Finset (d.Idx N × Bool)).image (fun p => (⟨N, i, p.1, p.2⟩ : Coord d)) ∪
    (univ : Finset (d.Idx N × Bool)).image (fun p => (⟨N, p.1, i, p.2⟩ : Coord d))

@[simp] theorem mem_rowSet {i k l : d.Idx N} {b : Bool} :
    (⟨N, k, l, b⟩ : Coord d) ∈ rowSet d N i ↔ (k = i ∨ l = i) := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
      injection hp with h1 h2
      simp only [Prod.mk.injEq] at h2
      exact Or.inl h2.1.symm
    · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
      injection hp with h1 h2
      simp only [Prod.mk.injEq] at h2
      exact Or.inr h2.2.1.symm
  · rintro (rfl | rfl)
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(l, b), Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(k, b), Finset.mem_univ _, rfl⟩)

/-- Agreeing outside the coordinates of row `i` is agreeing off row `i`. -/
theorem agreeOffRow_of_agree_compl {i : d.Idx N} {ω ω' : Ω d}
    (h : ∀ c ∉ rowSet d N i, ω c = ω' c) : AgreeOffRow d N i ω ω' := by
  intro k l b hk hl
  refine h _ ?_
  rw [mem_rowSet]
  rintro (rfl | rfl)
  · exact hk rfl
  · exact hl rfl

/-- **The row block is independent of any disjoint block of coordinates.** -/
theorem indepFun_rowSet (i : d.Idx N) (T : Finset (Coord d))
    (hT : Disjoint (rowSet d N i) T) :
    IndepFun (fun (ω : Ω d) (c : rowSet d N i) => ω c) (fun (ω : Ω d) (c : T) => ω c) (P d) :=
  (iIndepFun_coord d).indepFun_finset _ _ hT fun c => measurable_pi_apply c

/-! ### The row as a family indexed by `(column, real/imaginary)` -/

/-- The coordinate carrying the real (`b = true`) or imaginary (`b = false`) part of the entry
`X_{ik}`, for `k ≠ i`. -/
def rowCoord (d : Dims) (N : ℕ) (i k : d.Idx N) (b : Bool) : Coord d :=
  if idxKey d N i < idxKey d N k then ⟨N, i, k, b⟩ else ⟨N, k, i, b⟩

/-- The sign with which the imaginary coordinate enters `X_{ik}`. -/
def rowSign (d : Dims) (N : ℕ) (i k : d.Idx N) : ℝ :=
  if idxKey d N i < idxKey d N k then 1 else -1

theorem rowCoord_mem_rowSet (i k : d.Idx N) (b : Bool) :
    rowCoord d N i k b ∈ rowSet d N i := by
  unfold rowCoord
  split_ifs with h
  · exact mem_rowSet.2 (Or.inl rfl)
  · exact mem_rowSet.2 (Or.inr rfl)

/-- **The entry `X_{ik}` in terms of the two row coordinates.**  For `k ≠ i` it is
`ω(real) + ε i ω(imag)` with `ε = ±1`. -/
theorem Xentry_eq_rowCoord {i k : d.Idx N} (hik : i ≠ k) (ω : Ω d) :
    Xentry d N ω i k = (ω (rowCoord d N i k true) : ℂ)
      + (rowSign d N i k : ℂ) * Complex.I * (ω (rowCoord d N i k false) : ℂ) := by
  have hkey : idxKey d N i ≠ idxKey d N k := fun h => hik (idxKey_injective d N h)
  unfold Xentry rowCoord rowSign
  rcases lt_or_gt_of_ne hkey with h | h
  · simp only [h, ↓reduceIte]
    push_cast
    ring
  · have h' : ¬ idxKey d N i < idxKey d N k := by omega
    simp only [h', ↓reduceIte, h]
    push_cast
    ring

/-- The row coordinates are distinct: `(k, b) ↦ rowCoord i k b` is injective away from `i`. -/
theorem rowCoord_injOn {i : d.Idx N} {k l : d.Idx N} {b c : Bool} (hk : k ≠ i) (hl : l ≠ i)
    (h : rowCoord d N i k b = rowCoord d N i l c) : k = l ∧ b = c := by
  unfold rowCoord at h
  have hk' := hk
  have hl' := hl
  split_ifs at h with h1 h2 h2 <;> injection h with h3 h4 <;>
    simp only [Prod.mk.injEq] at h4 <;>
    first
      | exact ⟨h4.2.1, h4.2.2⟩
      | exact ⟨h4.1, h4.2.2⟩
      | (exfalso; simp_all)

/-! ### The row sum as a pair of real linear forms -/

/-- The index set of the row: a column `k ≠ i` together with a real/imaginary flag. -/
abbrev RowIdx (d : Dims) (N : ℕ) (i : d.Idx N) : Type := {k : d.Idx N // k ≠ i} × Bool

/-- The Gaussian coordinates of the row, indexed by `RowIdx`. -/
noncomputable def rowVar (d : Dims) (N : ℕ) (i : d.Idx N) (q : RowIdx d N i) (ω : Ω d) : ℝ :=
  ω (rowCoord d N i q.1.1 q.2)

/-- The coefficients of the real part of `∑_{k ≠ i} H_{ik} c_k`. -/
noncomputable def rowRe (d : Dims) (N : ℕ) (u : ℝ) (i : d.Idx N) (c : d.Idx N → ℂ)
    (q : RowIdx d N i) : ℝ :=
  if q.2 then Real.sqrt u * (c q.1.1).re
  else -(Real.sqrt u * rowSign d N i q.1.1 * (c q.1.1).im)

/-- The coefficients of the imaginary part of `∑_{k ≠ i} H_{ik} c_k`. -/
noncomputable def rowIm (d : Dims) (N : ℕ) (u : ℝ) (i : d.Idx N) (c : d.Idx N → ℂ)
    (q : RowIdx d N i) : ℝ :=
  if q.2 then Real.sqrt u * (c q.1.1).im
  else Real.sqrt u * rowSign d N i q.1.1 * (c q.1.1).re

/-- **The row sum, real part**: a real linear form in the row coordinates. -/
theorem re_row_sum (u : ℝ) (i : d.Idx N) (c : d.Idx N → ℂ) (ω : Ω d) :
    (∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 * c k.1).re
      = ∑ q : RowIdx d N i, rowRe d N u i c q * rowVar d N i q ω := by
  rw [Complex.re_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hflow_apply, Xentry_eq_rowCoord (Ne.symm k.2) ω]
  simp only [Fintype.sum_bool, rowRe, rowVar, rowSign, ↓reduceIte]
  by_cases h : idxKey d N i < idxKey d N k.1 <;>
    simp [h, Complex.add_re, Complex.mul_re] <;> ring

/-- **The row sum, imaginary part**. -/
theorem im_row_sum (u : ℝ) (i : d.Idx N) (c : d.Idx N → ℂ) (ω : Ω d) :
    (∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 * c k.1).im
      = ∑ q : RowIdx d N i, rowIm d N u i c q * rowVar d N i q ω := by
  rw [Complex.im_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hflow_apply, Xentry_eq_rowCoord (Ne.symm k.2) ω]
  simp only [Fintype.sum_bool, rowIm, rowVar, rowSign, ↓reduceIte]
  by_cases h : idxKey d N i < idxKey d N k.1 <;>
    simp [h, Complex.add_im, Complex.mul_im] <;> ring

/-! ### The moment bound for a row sum with frozen coefficients -/

theorem rowCoord_inj (i : d.Idx N) :
    Function.Injective fun q : RowIdx d N i => rowCoord d N i q.1.1 q.2 := by
  rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨l, hl⟩, c⟩ h
  obtain ⟨h1, h2⟩ := rowCoord_injOn hk hl h
  subst h1
  subst h2
  rfl

/-- The row coordinates form an independent family. -/
theorem iIndepFun_rowVar (i : d.Idx N) :
    ProbabilityTheory.iIndepFun (rowVar d N i) (P d) :=
  ProbabilityTheory.iIndepFun.precomp
    (g := fun q : RowIdx d N i => rowCoord d N i q.1.1 q.2) (rowCoord_inj i) (iIndepFun_coord d)

theorem measurable_rowVar (i : d.Idx N) (q : RowIdx d N i) :
    Measurable (rowVar d N i q) := measurable_pi_apply _

theorem map_rowVar (i : d.Idx N) (q : RowIdx d N i) :
    (P d).map (rowVar d N i q) = gaussianReal 0 (gvar d (rowCoord d N i q.1.1 q.2)) :=
  P_map_eval d _

/-- Off the diagonal the coordinate variance is `S_{ik}/2`, in either order of the index pair. -/
theorem gvar_rowCoord {i k : d.Idx N} (hk : k ≠ i) (b : Bool) :
    (gvar d (rowCoord d N i k b) : ℝ) = Sblk (d.L N) (d.W N) i k / 2 := by
  unfold rowCoord
  split_ifs with h
  · exact gvar_offDiag d N i k b (Ne.symm hk)
  · rw [gvar_offDiag d N k i b hk, Sblk_comm]

/-- The variance of the real part of the row sum: `(u/2) ∑_k S_{ik} |c_k|²`. -/
theorem linVar_rowRe {u : ℝ} (hu : 0 ≤ u) (i : d.Idx N) (c : d.Idx N → ℂ) :
    ((linVar (fun q : RowIdx d N i => gvar d (rowCoord d N i q.1.1 q.2))
        (rowRe d N u i c) Finset.univ : ℝ≥0) : ℝ)
      = u / 2 * ∑ k : {k : d.Idx N // k ≠ i}, Sblk (d.L N) (d.W N) i k.1 * ‖c k.1‖ ^ 2 := by
  unfold linVar
  push_cast
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool]
  simp only [rowRe, rowSign, ↓reduceIte, gvar_rowCoord k.2]
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  have hnorm : ‖c k.1‖ ^ 2 = (c k.1).re ^ 2 + (c k.1).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  by_cases h : idxKey d N i < idxKey d N k.1 <;> simp [h, hnorm, mul_pow, hsq] <;> ring

/-- The variance of the imaginary part is the same. -/
theorem linVar_rowIm {u : ℝ} (hu : 0 ≤ u) (i : d.Idx N) (c : d.Idx N → ℂ) :
    ((linVar (fun q : RowIdx d N i => gvar d (rowCoord d N i q.1.1 q.2))
        (rowIm d N u i c) Finset.univ : ℝ≥0) : ℝ)
      = u / 2 * ∑ k : {k : d.Idx N // k ≠ i}, Sblk (d.L N) (d.W N) i k.1 * ‖c k.1‖ ^ 2 := by
  unfold linVar
  push_cast
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool]
  simp only [rowIm, rowSign, ↓reduceIte, gvar_rowCoord k.2]
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  have hnorm : ‖c k.1‖ ^ 2 = (c k.1).re ^ 2 + (c k.1).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  by_cases h : idxKey d N i < idxKey d N k.1 <;> simp [h, hnorm, mul_pow, hsq] <;> ring

/-- **The moment bound for a row sum with frozen coefficients**:
`E‖∑_{k ≠ i} H_{ik} c_k‖^{2p} ≤ 2 (2p-1)!! (u ∑_k S_{ik} |c_k|²)^p`. -/
theorem integral_norm_row_sum_pow_le {u : ℝ} (hu : 0 ≤ u) (i : d.Idx N) (c : d.Idx N → ℂ)
    (p : ℕ) :
    ∫ ω, ‖∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 * c k.1‖ ^ (2 * p) ∂(P d)
      ≤ 2 * (dfac p *
        (u * ∑ k : {k : d.Idx N // k ≠ i}, Sblk (d.L N) (d.W N) i k.1 * ‖c k.1‖ ^ 2) ^ p) := by
  set V : ℝ := u / 2 * ∑ k : {k : d.Idx N // k ≠ i},
    Sblk (d.L N) (d.W N) i k.1 * ‖c k.1‖ ^ 2 with hV
  have hpt : ∀ ω : Ω d, ‖∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 * c k.1‖ ^ (2 * p)
      = ((∑ q : RowIdx d N i, rowRe d N u i c q * rowVar d N i q ω) ^ 2
        + (∑ q : RowIdx d N i, rowIm d N u i c q * rowVar d N i q ω) ^ 2) ^ p := by
    intro ω
    rw [pow_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← re_row_sum, ← im_row_sum]
    ring_nf
  simp_rw [hpt]
  have hbound := integral_sq_add_sq_pow_le (P := P d) (measurable_rowVar (d := d) (N := N) i)
    (map_rowVar (d := d) (N := N) i) (iIndepFun_rowVar (d := d) (N := N) i)
    (rowRe d N u i c) (rowIm d N u i c) Finset.univ p
  rw [linVar_rowRe hu, linVar_rowIm hu] at hbound
  refine hbound.trans (le_of_eq ?_)
  simp only [mul_pow, div_pow]
  field_simp
  ring

end RBM.Gauss
