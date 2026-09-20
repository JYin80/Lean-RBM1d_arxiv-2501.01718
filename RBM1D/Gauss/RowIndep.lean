/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Model
import RBM1D.Green.Minor
import RBM1D.Green.EntryBound
import RBM1D.Gauss.LinearForm
import RBM1D.Gauss.Generator
import RBM1D.Gauss.Domination
import RBM1D.Defs.MatrixMeasurable

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
open scoped NNReal ENNReal

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

/-! ### The two concrete finite blocks -/

/-- The coordinates that `H` at size `N` actually reads. -/
def relCoord (d : Dims) (N : ℕ) : Finset (Coord d) := (usedCoord d N).image (crd d N)

/-- The relevant coordinates outside row `i`. -/
def offRowCoord (d : Dims) (N : ℕ) (i : d.Idx N) : Finset (Coord d) :=
  relCoord d N \ rowSet d N i

theorem disjoint_rowSet_offRowCoord (i : d.Idx N) :
    Disjoint (rowSet d N i) (offRowCoord d N i) := by
  rw [Finset.disjoint_right]
  intro c hc
  exact (Finset.mem_sdiff.1 hc).2

theorem mem_relCoord_of_usedCoord {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) :
    (⟨N, p⟩ : Coord d) ∈ relCoord d N :=
  Finset.mem_image.2 ⟨p, hp, rfl⟩

/-- **The minor matrix reads only the off-row block.**  Two sample points agreeing on
`offRowCoord` have the same `H^{(i)}`. -/
theorem Hflow_submatrix_congr_offRowCoord (u : ℝ) {i : d.Idx N} {ω ω' : Ω d}
    (h : ∀ c ∈ offRowCoord d N i, ω c = ω' c) :
    (Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
      = (Hflow d N u ω').submatrix (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N) := by
  have key : ∀ (k l : d.Idx N) (b : Bool), k ≠ i → l ≠ i → (⟨N, k, l, b⟩ : Coord d) ∈ relCoord d N →
      ω ⟨N, k, l, b⟩ = ω' ⟨N, k, l, b⟩ := by
    intro k l b hk hl hmem
    refine h _ (Finset.mem_sdiff.2 ⟨hmem, ?_⟩)
    rw [mem_rowSet]
    rintro (rfl | rfl)
    · exact hk rfl
    · exact hl rfl
  ext k l
  simp only [Matrix.submatrix_apply, Hflow_apply]
  have hk := k.2
  have hl := l.2
  unfold Xentry
  split_ifs with h1 h2
  · rw [key k.1 l.1 true hk hl (mem_relCoord_of_usedCoord (mem_usedCoord.2 (Or.inl h1))),
      key k.1 l.1 false hk hl (mem_relCoord_of_usedCoord (mem_usedCoord.2 (Or.inl h1)))]
  · rw [key l.1 k.1 true hl hk (mem_relCoord_of_usedCoord (mem_usedCoord.2 (Or.inl h2))),
      key l.1 k.1 false hl hk (mem_relCoord_of_usedCoord (mem_usedCoord.2 (Or.inl h2)))]
  · have hkl : k.1 = l.1 := idxKey_injective d N (by omega)
    rw [key k.1 l.1 true hk hl (mem_relCoord_of_usedCoord (mem_usedCoord.2 (Or.inr ⟨hkl, rfl⟩)))]

/-- The row entries `H_{ik}`, `k ≠ i`, read only the row block. -/
theorem Hflow_row_congr (u : ℝ) {i : d.Idx N} {ω ω' : Ω d}
    (h : ∀ c ∈ rowSet d N i, ω c = ω' c) {k : d.Idx N} (hk : k ≠ i) :
    Hflow d N u ω i k = Hflow d N u ω' i k := by
  rw [Hflow_apply, Hflow_apply, Xentry_eq_rowCoord (Ne.symm hk) ω,
    Xentry_eq_rowCoord (Ne.symm hk) ω', h _ (rowCoord_mem_rowSet i k true),
    h _ (rowCoord_mem_rowSet i k false)]

/-- The row sum with coefficients reading only the off-row block, as a function of the two
blocks. -/
theorem row_sum_congr (u : ℝ) {i : d.Idx N} (C : Ω d → d.Idx N → ℂ)
    (hC : ∀ ω ω' : Ω d, (∀ c ∈ offRowCoord d N i, ω c = ω' c) → C ω = C ω')
    {ω ω' : Ω d} (h : ∀ c ∈ rowSet d N i ∪ offRowCoord d N i, ω c = ω' c) :
    (∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 * C ω k.1)
      = ∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω' i k.1 * C ω' k.1 := by
  have hrow : ∀ c ∈ rowSet d N i, ω c = ω' c := fun c hc =>
    h c (Finset.mem_union_left _ hc)
  have hoff : ∀ c ∈ offRowCoord d N i, ω c = ω' c := fun c hc =>
    h c (Finset.mem_union_right _ hc)
  rw [hC ω ω' hoff]
  exact Finset.sum_congr rfl fun k _ => by rw [Hflow_row_congr u hrow k.2]

/-! ### The conditional moment bound: random coefficients -/

variable {u : ℝ} {i : d.Idx N} {p : ℕ}

/-- Abbreviation for the row sum with coefficients `C`. -/
noncomputable def rowSum (d : Dims) (N : ℕ) (u : ℝ) (i : d.Idx N) (C : Ω d → d.Idx N → ℂ)
    (ω : Ω d) : ℂ :=
  ∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 * C ω k.1

/-- The (random) variance of the row sum. -/
noncomputable def rowVarSum (d : Dims) (N : ℕ) (u : ℝ) (i : d.Idx N) (C : Ω d → d.Idx N → ℂ)
    (ω : Ω d) : ℝ :=
  u * ∑ k : {k : d.Idx N // k ≠ i}, Sblk (d.L N) (d.W N) i k.1 * ‖C ω k.1‖ ^ 2

/-- **The row LDE moment bound.**  If the coefficients read only the off-row block, then
`E‖∑_{k ≠ i} H_{ik} C_k‖^{2p} ≤ 2 (2p-1)!! · E[(u ∑_k S_{ik} |C_k|²)^p]`: conditionally on the
off-row block the row sum is a centred complex Gaussian of variance `u ∑_k S_{ik}|C_k|²`, so the
frozen bound `integral_norm_row_sum_pow_le` applies fibrewise. -/
theorem integral_norm_rowSum_pow_le (hu : 0 ≤ u) (C : Ω d → d.Idx N → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Ω d, (∀ c ∈ offRowCoord d N i, ω c = ω' c) → C ω = C ω')
    (hint : Integrable (fun ω => ‖rowSum d N u i C ω‖ ^ (2 * p)) (P d))
    (hint' : Integrable (fun ω => rowVarSum d N u i C ω ^ p) (P d)) :
    ∫ ω, ‖rowSum d N u i C ω‖ ^ (2 * p) ∂(P d)
      ≤ 2 * (dfac p * ∫ ω, rowVarSum d N u i C ω ^ p ∂(P d)) := by
  classical
  set S := rowSet d N i with hS
  set T := offRowCoord d N i with hT
  set U : Ω d → ({c // c ∈ S} → ℝ) := fun ω c => ω c.1 with hU
  set V : Ω d → ({c // c ∈ T} → ℝ) := fun ω c => ω c.1 with hV
  have hUmeas : Measurable U := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hVmeas : Measurable V := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hindep : IndepFun U V (P d) := indepFun_rowSet i T (disjoint_rowSet_offRowCoord i)
  have hdisj := disjoint_rowSet_offRowCoord (d := d) (N := N) i
  -- the coefficients read only the second block, so they may be read off `V` alone
  have hCy : ∀ ω : Ω d, C ω = C (glue S T (0, V ω)) := by
    intro ω
    refine hC _ _ fun c hc => ?_
    have hcS : c ∉ S := Finset.disjoint_right.1 hdisj hc
    simp [glue, hcS, hc, hV]
  -- the row sum is a function of the two blocks
  have hrow : ∀ ω : Ω d, rowSum d N u i C ω = rowSum d N u i C (glue S T (U ω, V ω)) := by
    intro ω
    refine row_sum_congr u C hC fun c hc => ?_
    exact (glue_agree S T ω hc).symm
  set F : ({c // c ∈ S} → ℝ) × ({c // c ∈ T} → ℝ) → ℝ :=
    fun q => ‖rowSum d N u i C (glue S T q)‖ ^ (2 * p) with hF
  set G : ({c // c ∈ T} → ℝ) → ℝ :=
    fun y => 2 * (dfac p * rowVarSum d N u i C (glue S T (0, y)) ^ p) with hG
  -- measurability of the glued quantities
  have hglue := measurable_glue (ι := Coord d) S T
  have hFmeas : Measurable F := by
    refine (Measurable.pow_const ?_ _)
    refine Measurable.norm ?_
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((measurable_Hflow d N u i k.1).comp hglue).mul
      (((measurable_pi_apply k.1).comp hCmeas).comp hglue)
  have hGmeas : Measurable G := by
    refine (measurable_const.mul ((measurable_const.mul (Measurable.pow_const ?_ _))))
    refine (measurable_const.mul ?_)
    refine Finset.measurable_sum _ fun k _ => ?_
    exact measurable_const.mul
      ((((measurable_pi_apply k.1).comp hCmeas).comp (hglue.comp (measurable_const.prodMk
        measurable_id))).norm.pow_const _)
  -- transport the two integrability hypotheses
  have hpair : (P d).map (fun ω => (U ω, V ω)) = ((P d).map U).prod ((P d).map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hUmeas.aemeasurable hVmeas.aemeasurable).1 hindep
  have hFint : Integrable F (((P d).map U).prod ((P d).map V)) := by
    rw [← hpair]
    refine (integrable_map_measure hFmeas.aestronglyMeasurable
      (hUmeas.prodMk hVmeas).aemeasurable).2 ?_
    refine hint.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hF, Function.comp]
    rw [← hrow]
  have hGint : Integrable G ((P d).map V) := by
    refine (integrable_map_measure hGmeas.aestronglyMeasurable hVmeas.aemeasurable).2 ?_
    refine ((hint'.const_mul (dfac p)).const_mul 2).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hG, Function.comp, rowVarSum]
    rw [← hCy]
  -- the fibrewise (conditional) bound
  have hinner : ∀ y : {c // c ∈ T} → ℝ, (∫ x, F (x, y) ∂((P d).map U)) ≤ G y := by
    intro y
    have hmap := integral_map (μ := P d) (φ := U) (f := fun x => F (x, y))
      hUmeas.aemeasurable (hFmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    rw [hmap]
    have hval : ∀ ω : Ω d, F (U ω, y)
        = ‖∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 *
            C (glue S T (0, y)) k.1‖ ^ (2 * p) := by
      intro ω
      simp only [hF, rowSum]
      congr 2
      refine Finset.sum_congr rfl fun k _ => ?_
      have hHe : Hflow d N u (glue S T (U ω, y)) i k.1 = Hflow d N u ω i k.1 := by
        refine Hflow_row_congr u (fun c hc => ?_) k.2
        have hcS : c ∈ S := hc
        simp [glue, hcS, hU]
      have hCe : C (glue S T (U ω, y)) k.1 = C (glue S T (0, y)) k.1 := by
        have : C (glue S T (U ω, y)) = C (glue S T (0, y)) := by
          refine hC _ _ fun c hc => ?_
          have hcS : c ∉ S := Finset.disjoint_right.1 hdisj hc
          simp [glue, hcS, hc]
        rw [this]
      rw [hHe, hCe]
    simp only [hval]
    exact (integral_norm_row_sum_pow_le hu i (C (glue S T (0, y))) p).trans (le_of_eq (by
      simp only [hG, rowVarSum]))
  -- assemble
  have hmain := integral_indep_pair_le hUmeas hVmeas hindep hFint hGint
    (Filter.Eventually.of_forall hinner)
  have hL : ∫ ω, ‖rowSum d N u i C ω‖ ^ (2 * p) ∂(P d) = ∫ ω, F (U ω, V ω) ∂(P d) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hF]
    rw [← hrow]
  have hR : ∫ y, G y ∂((P d).map V) = 2 * (dfac p * ∫ ω, rowVarSum d N u i C ω ^ p ∂(P d)) := by
    rw [integral_map hVmeas.aemeasurable hGmeas.aestronglyMeasurable]
    simp only [hG, rowVarSum]
    rw [integral_const_mul, integral_const_mul]
    congr 2
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [← hCy]
  rw [hL, ← hR]
  exact hmain

/-- The coefficients normalised by the (random) standard deviation of the row sum. -/
noncomputable def rowCoeffNorm (d : Dims) (N : ℕ) (u : ℝ) (i : d.Idx N) (C : Ω d → d.Idx N → ℂ)
    (ω : Ω d) (k : d.Idx N) : ℂ :=
  if 0 < rowVarSum d N u i C ω then C ω k / (Real.sqrt (rowVarSum d N u i C ω) : ℂ) else 0

theorem rowVarSum_nonneg (hu : 0 ≤ u) (C : Ω d → d.Idx N → ℂ) (ω : Ω d) :
    0 ≤ rowVarSum d N u i C ω := by
  refine mul_nonneg hu (Finset.sum_nonneg fun k _ => ?_)
  exact mul_nonneg (Sblk_nonneg _ _) (by positivity)

/-- **The normalised row sum has variance `1`** wherever the variance is positive. -/
theorem rowVarSum_rowCoeffNorm (hu : 0 ≤ u) (C : Ω d → d.Idx N → ℂ) (ω : Ω d) :
    rowVarSum d N u i (rowCoeffNorm d N u i C) ω
      = if 0 < rowVarSum d N u i C ω then 1 else 0 := by
  have hV0 := rowVarSum_nonneg (i := i) hu C ω
  by_cases h : 0 < rowVarSum d N u i C ω
  · have hs : (0 : ℝ) < Real.sqrt (rowVarSum d N u i C ω) := Real.sqrt_pos.2 h
    have hsq : Real.sqrt (rowVarSum d N u i C ω) ^ 2 = rowVarSum d N u i C ω := Real.sq_sqrt hV0
    have hcoef : ∀ k : {k : d.Idx N // k ≠ i}, ‖rowCoeffNorm d N u i C ω k.1‖ ^ 2
        = ‖C ω k.1‖ ^ 2 / rowVarSum d N u i C ω := by
      intro k
      simp only [rowCoeffNorm, h, ↓reduceIte, norm_div, div_pow, Complex.norm_real,
        Real.norm_of_nonneg hs.le, hsq]
    rw [if_pos h]
    have hne : rowVarSum d N u i C ω ≠ 0 := ne_of_gt h
    have hcalc : rowVarSum d N u i (rowCoeffNorm d N u i C) ω
        = rowVarSum d N u i C ω / rowVarSum d N u i C ω := by
      conv_lhs => unfold rowVarSum
      simp only [hcoef]
      rw [Finset.sum_congr rfl fun k _ => (mul_div_assoc (Sblk (d.L N) (d.W N) i k.1)
        (‖C ω k.1‖ ^ 2) (rowVarSum d N u i C ω)).symm, ← Finset.sum_div, ← mul_div_assoc]
      rfl
    rw [hcalc, div_self hne]
  · rw [if_neg h]
    have hzero : ∀ k : {k : d.Idx N // k ≠ i}, rowCoeffNorm d N u i C ω k.1 = 0 := by
      intro k
      simp [rowCoeffNorm, h]
    unfold rowVarSum
    simp [hzero]

/-- The normalised coefficients still read only the off-row block. -/
theorem rowCoeffNorm_congr (C : Ω d → d.Idx N → ℂ)
    (hC : ∀ ω ω' : Ω d, (∀ c ∈ offRowCoord d N i, ω c = ω' c) → C ω = C ω')
    (ω ω' : Ω d) (h : ∀ c ∈ offRowCoord d N i, ω c = ω' c) :
    rowCoeffNorm d N u i C ω = rowCoeffNorm d N u i C ω' := by
  have hCe := hC ω ω' h
  funext k
  simp only [rowCoeffNorm, rowVarSum, hCe]
  rfl

theorem measurable_rowVarSum (C : Ω d → d.Idx N → ℂ) (hCmeas : Measurable C) :
    Measurable (rowVarSum d N u i C) := by
  unfold rowVarSum
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
  exact measurable_const.mul ((((measurable_pi_apply k.1).comp hCmeas).norm).pow_const 2)

theorem measurable_rowCoeffNorm (C : Ω d → d.Idx N → ℂ) (hCmeas : Measurable C) :
    Measurable (rowCoeffNorm d N u i C) := by
  refine Measurable.of_eval fun k => ?_
  refine Measurable.ite (measurableSet_lt measurable_const (measurable_rowVarSum C hCmeas)) ?_
    measurable_const
  refine ((measurable_pi_apply k).comp hCmeas).div ?_
  exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
    (measurable_rowVarSum C hCmeas))

/-- **The row LDE, ratio form.**  Normalising by the conditional standard deviation gives a
*constant* moment bound: `E[(‖∑_{k≠i} H_{ik} C_k‖² / (u ∑_k S_{ik}|C_k|²))^p] ≤ 2 (2p-1)!!`.
This is the `MomentDom` input (with `Φ = 1`) that `stochDom_of_momentDom` turns into `≺`. -/
theorem integral_norm_rowSum_norm_pow_le (hu : 0 ≤ u) (C : Ω d → d.Idx N → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Ω d, (∀ c ∈ offRowCoord d N i, ω c = ω' c) → C ω = C ω')
    (hint : Integrable
      (fun ω => ‖rowSum d N u i (rowCoeffNorm d N u i C) ω‖ ^ (2 * p)) (P d)) :
    ∫ ω, ‖rowSum d N u i (rowCoeffNorm d N u i C) ω‖ ^ (2 * p) ∂(P d) ≤ 2 * dfac p := by
  have hvar := rowVarSum_rowCoeffNorm (d := d) (N := N) (u := u) (i := i) hu C
  have hmeas' : Measurable (fun ω => rowVarSum d N u i (rowCoeffNorm d N u i C) ω ^ p) :=
    (measurable_rowVarSum _ (measurable_rowCoeffNorm C hCmeas)).pow_const p
  have hbdd : ∀ ω : Ω d, ‖rowVarSum d N u i (rowCoeffNorm d N u i C) ω ^ p‖ ≤ 1 := by
    intro ω
    rw [hvar ω]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · by_cases h : 0 < rowVarSum d N u i C ω <;> simp [h]
    · by_cases h : 0 < rowVarSum d N u i C ω <;> simp [h, zero_pow hp.ne']
  have hint' : Integrable (fun ω => rowVarSum d N u i (rowCoeffNorm d N u i C) ω ^ p) (P d) :=
    (integrable_const (1 : ℝ)).mono' hmeas'.aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  have hmain := integral_norm_rowSum_pow_le (d := d) (N := N) (u := u) (i := i) (p := p) hu
    (rowCoeffNorm d N u i C) (measurable_rowCoeffNorm C hCmeas)
    (fun ω ω' h => rowCoeffNorm_congr C hC ω ω' h) hint hint'
  refine hmain.trans ?_
  have hle : ∫ ω, rowVarSum d N u i (rowCoeffNorm d N u i C) ω ^ p ∂(P d) ≤ 1 := by
    calc ∫ ω, rowVarSum d N u i (rowCoeffNorm d N u i C) ω ^ p ∂(P d)
        ≤ ∫ _ω : Ω d, (1 : ℝ) ∂(P d) := by
          refine integral_mono hint' (integrable_const 1) fun ω => ?_
          have := hbdd ω
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = 1 := by simp
  have hd : 0 ≤ dfac p := by
    unfold dfac
    positivity
  nlinarith [hle, hd]

/-! ### Measurability of the minor resolvent -/

/-- The `j`-th column of the minor resolvent `(H^{(i)} - z)^{-1}`, as coefficients indexed by
all of `Idx N` (zero at `i`). -/
noncomputable def minorCol (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (i : d.Idx N)
    (j : {a : d.Idx N // a ≠ i}) (ω : Ω d) (k : d.Idx N) : ℂ :=
  if h : k ≠ i then
    (((Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
      - z • (1 : Matrix {a : d.Idx N // a ≠ i} {a : d.Idx N // a ≠ i} ℂ))⁻¹) ⟨k, h⟩ j
  else 0

/-- **The minor resolvent column reads only the off-row block.** -/
theorem minorCol_congr (u : ℝ) (z : ℂ) {i : d.Idx N} (j : {a : d.Idx N // a ≠ i})
    {ω ω' : Ω d} (h : ∀ c ∈ offRowCoord d N i, ω c = ω' c) :
    minorCol d N u z i j ω = minorCol d N u z i j ω' := by
  funext k
  unfold minorCol
  rw [Hflow_submatrix_congr_offRowCoord u h]

theorem measurable_minorCol (u : ℝ) (z : ℂ) (i : d.Idx N) (j : {a : d.Idx N // a ≠ i}) :
    Measurable (minorCol d N u z i j) := by
  refine Measurable.of_eval fun k => ?_
  unfold minorCol
  split
  · exact measurable_inv_entries
      (A := fun ω : Ω d => (Hflow d N u ω).submatrix
        (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
        - z • (1 : Matrix {a : d.Idx N // a ≠ i} {a : d.Idx N // a ≠ i} ℂ))
      (fun a b => (measurable_Hflow d N u a.1 b.1).sub measurable_const) _ _
  · exact measurable_const

/-! ### The row LDE for the Gaussian model -/

/-- **The linear LDE of T81, moment form.**  With the coefficients given by the `j`-th column of
the minor resolvent `(H^{(i)} - z)^{-1}` — which is independent of row `i` — the normalised row
sum has a *constant* moment bound:

`E[ (‖∑_{k ≠ i} H_{ik} G^{(i)}_{kj}‖² / (u ∑_k S_{ik} |G^{(i)}_{kj}|²))^p ] ≤ 2 (2p-1)!!`.

Through `stochDom_of_momentDom` (T73) this is `|∑_k H_{ik} G^{(i)}_{kj}|² ≺ ∑_k S_{ik}|G^{(i)}_{kj}|²`,
the paper's row LDE. -/
theorem integral_norm_rowSum_minorCol_pow_le (hu : 0 ≤ u) (z : ℂ)
    (j : {a : d.Idx N // a ≠ i})
    (hint : Integrable (fun ω => ‖rowSum d N u i
      (rowCoeffNorm d N u i (minorCol d N u z i j)) ω‖ ^ (2 * p)) (P d)) :
    ∫ ω, ‖rowSum d N u i (rowCoeffNorm d N u i (minorCol d N u z i j)) ω‖ ^ (2 * p) ∂(P d)
      ≤ 2 * dfac p :=
  integral_norm_rowSum_norm_pow_le hu (minorCol d N u z i j) (measurable_minorCol u z i j)
    (fun ω ω' h => minorCol_congr u z j h) hint

/-! ### Alignment with the LDE of `Green/EntryBound.lean` -/

variable {z : ℂ}

/-- Where the resolvent exists, the coefficients `minorCol` are the entries of `G^{(i)}`. -/
theorem minorCol_eq_greenMinor (u : ℝ) {i : d.Idx N} (j : {a : d.Idx N // a ≠ i}) {ω : Ω d}
    (hdet : IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hGii : green (Hflow d N u ω) z i i ≠ 0) {k : d.Idx N} (hk : k ≠ i) :
    minorCol d N u z i j ω k = greenMinor (green (Hflow d N u ω) z) i k j.1 := by
  unfold minorCol
  rw [dite_cond_eq_true (by simpa using hk), inv_minor_resolvent hdet i hGii]
  rfl

/-- **The left-hand side of the row LDE** is the row sum with the minor resolvent column. -/
theorem ldeRowLHS_eq (u : ℝ) {i : d.Idx N} (j : {a : d.Idx N // a ≠ i}) {ω : Ω d}
    (hdet : IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hGii : green (Hflow d N u ω) z i i ≠ 0) :
    ldeRowLHS (Hflow d N u ω) (green (Hflow d N u ω) z) i j.1
      = ‖rowSum d N u i (minorCol d N u z i j) ω‖ ^ 2 := by
  unfold ldeRowLHS rowSum
  congr 2
  rw [Finset.sum_subtype (p := fun k => k ≠ i) (Finset.univ.erase i)
    (fun k => by simp [Finset.mem_erase]) _]
  exact Finset.sum_congr rfl fun k _ =>
    by rw [minorCol_eq_greenMinor u j hdet hGii k.2]

/-- **The right-hand side of the row LDE** is the variance of that row sum, up to the factor
`u`. -/
theorem rowVarSum_eq (u : ℝ) {i : d.Idx N} (j : {a : d.Idx N // a ≠ i}) {ω : Ω d}
    (hdet : IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hGii : green (Hflow d N u ω) z i i ≠ 0) :
    rowVarSum d N u i (minorCol d N u z i j) ω
      = u * ldeRowRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) z) i j.1 := by
  unfold rowVarSum ldeRowRHS
  congr 1
  rw [Finset.sum_subtype (p := fun k => k ≠ i) (Finset.univ.erase i)
    (fun k => by simp [Finset.mem_erase]) _]
  exact Finset.sum_congr rfl fun k _ =>
    by rw [minorCol_eq_greenMinor u j hdet hGii k.2]

/-! ### The frozen bound in `ℝ≥0∞` form -/

theorem measurable_row_sum (u : ℝ) (i : d.Idx N) (c : d.Idx N → ℂ) :
    Measurable fun ω : Ω d => ∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 * c k.1 :=
  Finset.measurable_sum _ fun k _ => (measurable_Hflow d N u i k.1).mul measurable_const

/-- All even moments of a frozen row sum exist. -/
theorem integrable_norm_row_sum_pow (u : ℝ) (i : d.Idx N) (c : d.Idx N → ℂ) (p : ℕ) :
    Integrable (fun ω : Ω d =>
      ‖∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 * c k.1‖ ^ (2 * p)) (P d) := by
  have hre := integrable_pow_lin (P := P d) (measurable_rowVar (d := d) (N := N) i)
    (map_rowVar (d := d) (N := N) i) (iIndepFun_rowVar (d := d) (N := N) i)
    (rowRe d N u i c) Finset.univ p
  have him := integrable_pow_lin (P := P d) (measurable_rowVar (d := d) (N := N) i)
    (map_rowVar (d := d) (N := N) i) (iIndepFun_rowVar (d := d) (N := N) i)
    (rowIm d N u i c) Finset.univ p
  refine ((hre.add him).const_mul ((2 : ℝ) ^ p)).mono'
    (((measurable_row_sum u i c).norm).pow_const _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  set x := (∑ q : RowIdx d N i, rowRe d N u i c q * rowVar d N i q ω) with hx
  set y := (∑ q : RowIdx d N i, rowIm d N u i c q * rowVar d N i q ω) with hy
  have hz : ‖∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 * c k.1‖ ^ (2 * p)
      = (x ^ 2 + y ^ 2) ^ p := by
    rw [pow_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hx, hy, ← re_row_sum,
      ← im_row_sum]
    ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hz]
  have hxy : (x ^ 2 + y ^ 2) ^ p ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := by
    have hx0 : (0 : ℝ) ≤ x ^ 2 := by positivity
    have hy0 : (0 : ℝ) ≤ y ^ 2 := by positivity
    have h1 : (x ^ 2 + y ^ 2) ^ p ≤ (2 * max (x ^ 2) (y ^ 2)) ^ p := by
      refine pow_le_pow_left₀ (by positivity) ?_ p
      rcases le_total (x ^ 2) (y ^ 2) with h | h
      · simp [max_eq_right h]; linarith
      · simp [max_eq_left h]; linarith
    have h2 : max (x ^ 2) (y ^ 2) ^ p ≤ x ^ (2 * p) + y ^ (2 * p) := by
      rw [pow_mul, pow_mul]
      rcases le_total (x ^ 2) (y ^ 2) with h | h
      · rw [max_eq_right h]
        have : (0 : ℝ) ≤ (x ^ 2) ^ p := by positivity
        linarith
      · rw [max_eq_left h]
        have : (0 : ℝ) ≤ (y ^ 2) ^ p := by positivity
        linarith
    calc (x ^ 2 + y ^ 2) ^ p ≤ (2 * max (x ^ 2) (y ^ 2)) ^ p := h1
      _ = 2 ^ p * max (x ^ 2) (y ^ 2) ^ p := by rw [mul_pow]
      _ ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := by
          have : (0 : ℝ) ≤ 2 ^ p := by positivity
          exact mul_le_mul_of_nonneg_left h2 this
  calc (x ^ 2 + y ^ 2) ^ p ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := hxy
    _ = _ := by simp only [Pi.add_apply, hx, hy]

/-- The frozen bound, in `ℝ≥0∞` form. -/
theorem lintegral_norm_row_sum_pow_le {u : ℝ} (hu : 0 ≤ u) (i : d.Idx N) (c : d.Idx N → ℂ)
    (p : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖∑ k : {k : d.Idx N // k ≠ i},
        Hflow d N u ω i k.1 * c k.1‖ ^ (2 * p)) ∂(P d)
      ≤ ENNReal.ofReal (2 * (dfac p *
        (u * ∑ k : {k : d.Idx N // k ≠ i}, Sblk (d.L N) (d.W N) i k.1 * ‖c k.1‖ ^ 2) ^ p)) := by
  have hint := integrable_norm_row_sum_pow u i c p
  have hnn : 0 ≤ᵐ[P d] fun ω : Ω d =>
      ‖∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 * c k.1‖ ^ (2 * p) :=
    Filter.Eventually.of_forall fun ω => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact ENNReal.ofReal_le_ofReal (integral_norm_row_sum_pow_le hu i c p)

/-! ### The row LDE without integrability hypotheses -/

/-- **Tonelli assembly, constant-bound form.**  If the coefficients `D` read only the off-row
block and their (random) variance obeys a uniform bound after the frozen estimate, then
`∫⁻ ‖Z‖^{2p}` obeys that bound — with no integrability hypothesis. -/
theorem lintegral_norm_rowSum_pow_le_of_const (hu : 0 ≤ u) (D : Ω d → d.Idx N → ℂ)
    (hDmeas : Measurable D)
    (hDC : ∀ ω ω' : Ω d, (∀ c ∈ offRowCoord d N i, ω c = ω' c) → D ω = D ω') {c : ℝ≥0∞}
    (hb : ∀ ω : Ω d, ENNReal.ofReal (2 * (dfac p * rowVarSum d N u i D ω ^ p)) ≤ c) :
    ∫⁻ ω, ENNReal.ofReal (‖rowSum d N u i D ω‖ ^ (2 * p)) ∂(P d) ≤ c := by
  classical
  set S := rowSet d N i with hS
  set T := offRowCoord d N i with hT
  set U : Ω d → ({c // c ∈ S} → ℝ) := fun ω c => ω c.1 with hU
  set V : Ω d → ({c // c ∈ T} → ℝ) := fun ω c => ω c.1 with hV
  have hUmeas : Measurable U := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hVmeas : Measurable V := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hindep : IndepFun U V (P d) := indepFun_rowSet i T (disjoint_rowSet_offRowCoord i)
  have hdisj := disjoint_rowSet_offRowCoord (d := d) (N := N) i
  set F : ({c // c ∈ S} → ℝ) × ({c // c ∈ T} → ℝ) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (‖rowSum d N u i D (glue S T q)‖ ^ (2 * p)) with hF
  have hglue := measurable_glue (ι := Coord d) S T
  have hFmeas : Measurable F := by
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm ?_) _)
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((measurable_Hflow d N u i k.1).comp hglue).mul
      (((measurable_pi_apply k.1).comp hDmeas).comp hglue)
  have hrow : ∀ ω : Ω d, rowSum d N u i D ω = rowSum d N u i D (glue S T (U ω, V ω)) := by
    intro ω
    refine row_sum_congr u D hDC fun c hc => ?_
    exact (glue_agree S T ω hc).symm
  have hinner : ∀ y : {c // c ∈ T} → ℝ, (∫⁻ x, F (x, y) ∂((P d).map U)) ≤ c := by
    intro y
    have hFy : Measurable fun x : {c // c ∈ S} → ℝ => F (x, y) :=
      hFmeas.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_map hFy hUmeas]
    have hval : ∀ ω : Ω d, F (U ω, y)
        = ENNReal.ofReal (‖∑ k : {k : d.Idx N // k ≠ i},
            Hflow d N u ω i k.1 * D (glue S T (0, y)) k.1‖ ^ (2 * p)) := by
      intro ω
      simp only [hF, rowSum]
      congr 3
      refine Finset.sum_congr rfl fun k _ => ?_
      have hHe : Hflow d N u (glue S T (U ω, y)) i k.1 = Hflow d N u ω i k.1 := by
        refine Hflow_row_congr u (fun c hc => ?_) k.2
        have hcS : c ∈ S := hc
        simp [glue, hcS, hU]
      have hDe : D (glue S T (U ω, y)) k.1 = D (glue S T (0, y)) k.1 := by
        have : D (glue S T (U ω, y)) = D (glue S T (0, y)) := by
          refine hDC _ _ fun c hc => ?_
          have hcS : c ∉ S := Finset.disjoint_right.1 hdisj hc
          simp [glue, hcS, hc]
        rw [this]
      rw [hHe, hDe]
    simp only [hval]
    exact (lintegral_norm_row_sum_pow_le hu i (D (glue S T (0, y))) p).trans
      (hb (glue S T (0, y)))
  have hmain := lintegral_indep_pair_le hUmeas hVmeas hindep hFmeas hinner
  calc ∫⁻ ω, ENNReal.ofReal (‖rowSum d N u i D ω‖ ^ (2 * p)) ∂(P d)
      = ∫⁻ ω, F (U ω, V ω) ∂(P d) := by
        refine lintegral_congr fun ω => ?_
        simp only [hF]
        rw [← hrow]
    _ ≤ c := hmain

/-- **The row LDE, `ℝ≥0∞` form, no side conditions.**  Conditionally on the off-row block the
normalised row sum is a centred complex Gaussian of variance `≤ 1`. -/
theorem lintegral_norm_rowSum_norm_pow_le (hu : 0 ≤ u) (C : Ω d → d.Idx N → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Ω d, (∀ c ∈ offRowCoord d N i, ω c = ω' c) → C ω = C ω') :
    ∫⁻ ω, ENNReal.ofReal (‖rowSum d N u i (rowCoeffNorm d N u i C) ω‖ ^ (2 * p)) ∂(P d)
      ≤ ENNReal.ofReal (2 * dfac p) := by
  refine lintegral_norm_rowSum_pow_le_of_const hu (rowCoeffNorm d N u i C)
    (measurable_rowCoeffNorm C hCmeas) (fun ω ω' h => rowCoeffNorm_congr C hC ω ω' h)
    (fun ω => ENNReal.ofReal_le_ofReal ?_)
  have hvar := rowVarSum_rowCoeffNorm (d := d) (N := N) (u := u) (i := i) hu C ω
  have hd0 : (0 : ℝ) ≤ dfac p := by unfold dfac; positivity
  have hle : rowVarSum d N u i (rowCoeffNorm d N u i C) ω ^ p ≤ 1 := by
    rw [hvar]
    by_cases h : 0 < rowVarSum d N u i C ω
    · simp [h]
    · rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp [h]
      · simp [h, zero_pow hp.ne']
  nlinarith [hle, hd0]

/-- Integrability of the normalised row sum, from the finiteness of the `ℝ≥0∞` bound. -/
theorem integrable_norm_rowSum_norm_pow (hu : 0 ≤ u) (C : Ω d → d.Idx N → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Ω d, (∀ c ∈ offRowCoord d N i, ω c = ω' c) → C ω = C ω') :
    Integrable (fun ω => ‖rowSum d N u i (rowCoeffNorm d N u i C) ω‖ ^ (2 * p)) (P d) := by
  have hmeas : Measurable fun ω : Ω d =>
      ‖rowSum d N u i (rowCoeffNorm d N u i C) ω‖ ^ (2 * p) := by
    unfold rowSum
    refine (Measurable.norm ?_).pow_const _
    refine Finset.measurable_sum _ fun k _ => ?_
    exact (measurable_Hflow d N u i k.1).mul
      ((measurable_pi_apply k.1).comp (measurable_rowCoeffNorm C hCmeas))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hnn : ∀ ω : Ω d, ‖‖rowSum d N u i (rowCoeffNorm d N u i C) ω‖ ^ (2 * p)‖ₑ
      = ENNReal.ofReal (‖rowSum d N u i (rowCoeffNorm d N u i C) ω‖ ^ (2 * p)) :=
    fun ω => Real.enorm_eq_ofReal (by positivity)
  simp only [hnn]
  exact lt_of_le_of_lt (lintegral_norm_rowSum_norm_pow_le hu C hCmeas hC) ENNReal.ofReal_lt_top

/-- **The row LDE, Bochner form, no side conditions**: `E‖Z/√V‖^{2p} ≤ 2 (2p-1)!!`. -/
theorem integral_norm_rowSum_norm_pow_le' (hu : 0 ≤ u) (C : Ω d → d.Idx N → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Ω d, (∀ c ∈ offRowCoord d N i, ω c = ω' c) → C ω = C ω') :
    ∫ ω, ‖rowSum d N u i (rowCoeffNorm d N u i C) ω‖ ^ (2 * p) ∂(P d) ≤ 2 * dfac p :=
  integral_norm_rowSum_norm_pow_le hu C hCmeas hC
    (integrable_norm_rowSum_norm_pow hu C hCmeas hC)

/-- **The linear LDE of T81, final moment form.**  For the coefficients given by the `j`-th
column of the minor resolvent — independent of row `i` — the normalised row sum obeys the
constant moment bound, with no side conditions at all:

`E[ ‖∑_{k ≠ i} H_{ik} G^{(i)}_{kj}‖² / (u ∑_k S_{ik}|G^{(i)}_{kj}|²) ]^p ≤ 2 (2p-1)!!`. -/
theorem integral_norm_rowSum_minorCol_pow_le' (hu : 0 ≤ u) (z : ℂ)
    (j : {a : d.Idx N // a ≠ i}) :
    ∫ ω, ‖rowSum d N u i (rowCoeffNorm d N u i (minorCol d N u z i j)) ω‖ ^ (2 * p) ∂(P d)
      ≤ 2 * dfac p :=
  integral_norm_rowSum_norm_pow_le' hu (minorCol d N u z i j) (measurable_minorCol u z i j)
    (fun ω ω' h => minorCol_congr u z j h)

/-! ### The row LDE as stochastic domination -/

/-- The index set of the row LDE: a row `i` and a column `j ≠ i`. -/
abbrev LdeIdx (d : Dims) (N : ℕ) : Type := Σ i : d.Idx N, {a : d.Idx N // a ≠ i}

theorem card_LdeIdx_le (N : ℕ) :
    (Fintype.card (LdeIdx d N) : ℝ) ≤ (d.L N * d.W N : ℕ) * (d.L N * d.W N : ℕ) := by
  have hcard : Fintype.card (d.Idx N) = d.L N * d.W N := by
    simp [Dims.Idx, ZMod.card]
  have : Fintype.card (LdeIdx d N) ≤ Fintype.card (d.Idx N) * Fintype.card (d.Idx N) := by
    calc Fintype.card (LdeIdx d N) = ∑ i : d.Idx N, Fintype.card {a : d.Idx N // a ≠ i} :=
          Fintype.card_sigma
      _ ≤ ∑ _i : d.Idx N, Fintype.card (d.Idx N) :=
          Finset.sum_le_sum fun i _ => Fintype.card_subtype_le _
      _ = Fintype.card (d.Idx N) * Fintype.card (d.Idx N) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hcard] at this
  exact_mod_cast this

/-- The index set of the row LDE is polynomially large: `#LdeIdx ≤ N²` eventually. -/
theorem eventually_card_LdeIdx_le (d : Dims) :
    ∀ᶠ N : ℕ in Filter.atTop, (Fintype.card (LdeIdx d N) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
  filter_upwards [d.dim, Filter.eventually_ge_atTop 1] with N hN hN1
  refine (card_LdeIdx_le N).trans ?_
  have hLW : ((d.L N * d.W N : ℕ) : ℝ) ≤ (N : ℝ) := by
    have := hN.1
    have hcomm : d.W N * d.L N = d.L N * d.W N := Nat.mul_comm _ _
    rw [hcomm] at this
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have h0 : (0 : ℝ) ≤ ((d.L N * d.W N : ℕ) : ℝ) := by positivity
  calc ((d.L N * d.W N : ℕ) : ℝ) * ((d.L N * d.W N : ℕ) : ℝ) ≤ (N : ℝ) * (N : ℝ) :=
        mul_le_mul hLW hLW h0 (le_of_lt hNpos)
    _ = (N : ℝ) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring

/-- **Stochastic domination for any row sum with off-row coefficients.**  Given a family of
rows `row N q` and coefficients `C N q` that read only the corresponding off-row block, the
normalised row sums are `≺ 1`, uniformly over a polynomially large index set.  Both the row LDE
and (by Hermitian symmetry) the column LDE are instances. -/
theorem stochDom_rowSum_general (hu : 0 ≤ u) {U : ℕ → Type*} [∀ N, Fintype (U N)] {Ccard : ℝ}
    (hcard : ∀ᶠ N : ℕ in Filter.atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard)
    (row : ∀ N, U N → d.Idx N) (C : ∀ N, U N → Ω d → d.Idx N → ℂ)
    (hCmeas : ∀ N q, Measurable (C N q))
    (hC : ∀ N q (ω ω' : Ω d),
      (∀ c ∈ offRowCoord d N (row N q), ω c = ω' c) → C N q ω = C N q ω') :
    StochDom (P d)
      (fun N q ω =>
        ‖rowSum d N u (row N q) (rowCoeffNorm d N u (row N q) (C N q)) ω‖)
      (fun _ _ _ => 1) := by
  refine stochDom_of_momentDom hcard (fun N q => zero_lt_one) ?_ ?_
  · intro p N q
    have := integrable_norm_rowSum_norm_pow (d := d) (N := N) (u := u) (i := row N q) (p := p) hu
      (C N q) (hCmeas N q) (fun ω ω' h => hC N q ω ω' h)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [abs_norm]
  · intro ε hε p
    have hd0 : (0 : ℝ) ≤ dfac p := by unfold dfac; positivity
    refine ⟨2 * dfac p + 1, by linarith, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN1 q
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hbound := integral_norm_rowSum_norm_pow_le' (d := d) (N := N) (u := u)
      (i := row N q) (p := p) hu (C N q) (hCmeas N q) (fun ω ω' h => hC N q ω ω' h)
    have habs : ∫ ω, |‖rowSum d N u (row N q)
          (rowCoeffNorm d N u (row N q) (C N q)) ω‖| ^ (2 * p) ∂(P d)
        = ∫ ω, ‖rowSum d N u (row N q)
            (rowCoeffNorm d N u (row N q) (C N q)) ω‖ ^ (2 * p) ∂(P d) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [abs_norm]
    rw [habs]
    have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) := Real.one_le_rpow hN1' (by positivity)
    have : (2 * dfac p) ≤ (2 * dfac p + 1) * ((N : ℝ) ^ (ε * p) * 1 ^ (2 * p)) := by
      rw [one_pow, mul_one]
      nlinarith [hpow, hd0]
    linarith [hbound, this]

/-- **The linear LDE of T81 as stochastic domination**: for the Gaussian model,
`|∑_{k ≠ i} H_{ik} G^{(i)}_{kj}| ≺ (∑_k S_{ik} |G^{(i)}_{kj}|²)^{1/2}`, uniformly in `(i, j)`. -/
theorem stochDom_rowSum_minorCol (hu : 0 ≤ u) (z : ℂ) :
    StochDom (P d)
      (fun N (q : LdeIdx d N) ω =>
        ‖rowSum d N u q.1 (rowCoeffNorm d N u q.1 (minorCol d N u z q.1 q.2)) ω‖)
      (fun _ _ _ => 1) := by
  have hcard := eventually_card_LdeIdx_le d
  exact stochDom_rowSum_general (U := fun N => LdeIdx d N) (Ccard := 2) hu hcard
    (fun N q => q.1) (fun N q => minorCol d N u z q.1 q.2)
    (fun N q => measurable_minorCol u z q.1 q.2)
    (fun N q ω ω' h => minorCol_congr u z q.2 h)

/-! ### The column LDE, by Hermitian symmetry -/

/-- The conjugate of the `k`-th row of the minor resolvent `(H^{(j)} - z)^{-1}`, as coefficients
indexed by all of `Idx N` (zero at `j`).  By Hermitian symmetry the column sum of the paper is
the conjugate of the row sum with these coefficients. -/
noncomputable def minorRowConj (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (j : d.Idx N)
    (k : {a : d.Idx N // a ≠ j}) (ω : Ω d) (l : d.Idx N) : ℂ :=
  if h : l ≠ j then
    (starRingEnd ℂ) ((((Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ≠ j} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ j} → d.Idx N)
      - z • (1 : Matrix {a : d.Idx N // a ≠ j} {a : d.Idx N // a ≠ j} ℂ))⁻¹) k ⟨l, h⟩)
  else 0

theorem minorRowConj_congr (u : ℝ) (z : ℂ) {j : d.Idx N} (k : {a : d.Idx N // a ≠ j})
    {ω ω' : Ω d} (h : ∀ c ∈ offRowCoord d N j, ω c = ω' c) :
    minorRowConj d N u z j k ω = minorRowConj d N u z j k ω' := by
  funext l
  unfold minorRowConj
  rw [Hflow_submatrix_congr_offRowCoord u h]

theorem measurable_minorRowConj (u : ℝ) (z : ℂ) (j : d.Idx N)
    (k : {a : d.Idx N // a ≠ j}) : Measurable (minorRowConj d N u z j k) := by
  refine Measurable.of_eval fun l => ?_
  unfold minorRowConj
  split
  · refine Complex.continuous_conj.measurable.comp ?_
    exact measurable_inv_entries
      (A := fun ω : Ω d => (Hflow d N u ω).submatrix
        (Subtype.val : {a : d.Idx N // a ≠ j} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ j} → d.Idx N)
        - z • (1 : Matrix {a : d.Idx N // a ≠ j} {a : d.Idx N // a ≠ j} ℂ))
      (fun a b => (measurable_Hflow d N u a.1 b.1).sub measurable_const) _ _
  · exact measurable_const

/-- **The column LDE of T81 as stochastic domination**: the column sums
`∑_{l ≠ j} G^{(j)}_{kl} H_{lj}` obey the same bound, uniformly in `(j, k)`. -/
theorem stochDom_rowSum_minorRowConj (hu : 0 ≤ u) (z : ℂ) :
    StochDom (P d)
      (fun N (q : LdeIdx d N) ω =>
        ‖rowSum d N u q.1 (rowCoeffNorm d N u q.1 (minorRowConj d N u z q.1 q.2)) ω‖)
      (fun _ _ _ => 1) := by
  have hcard := eventually_card_LdeIdx_le d
  exact stochDom_rowSum_general (U := fun N => LdeIdx d N) (Ccard := 2) hu hcard
    (fun N q => q.1) (fun N q => minorRowConj d N u z q.1 q.2)
    (fun N q => measurable_minorRowConj u z q.1 q.2)
    (fun N q ω ω' h => minorRowConj_congr u z q.2 h)

/-- **The degenerate case.**  Where the conditional variance vanishes, so does the row sum,
almost surely: freezing the coefficients to `0` off that event gives a family whose variance is
identically `0`, hence whose second moment vanishes. -/
theorem rowSum_ae_eq_zero_of_varSum_eq_zero (hu : 0 ≤ u) (C : Ω d → d.Idx N → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Ω d, (∀ c ∈ offRowCoord d N i, ω c = ω' c) → C ω = C ω') :
    ∀ᵐ ω ∂(P d), rowVarSum d N u i C ω = 0 → rowSum d N u i C ω = 0 := by
  classical
  set D : Ω d → d.Idx N → ℂ :=
    fun ω k => if rowVarSum d N u i C ω = 0 then C ω k else 0 with hD
  have hVmeas : Measurable (rowVarSum d N u i C) := measurable_rowVarSum C hCmeas
  have hDmeas : Measurable D := by
    refine Measurable.of_eval fun k => ?_
    exact Measurable.ite (measurableSet_eq_fun hVmeas measurable_const)
      ((measurable_pi_apply k).comp hCmeas) measurable_const
  have hDC : ∀ ω ω' : Ω d, (∀ c ∈ offRowCoord d N i, ω c = ω' c) → D ω = D ω' := by
    intro ω ω' h
    have hCe := hC ω ω' h
    funext k
    simp only [hD, rowVarSum, hCe]
    rfl
  have hDvar : ∀ ω : Ω d, rowVarSum d N u i D ω = 0 := by
    intro ω
    by_cases h : rowVarSum d N u i C ω = 0
    · have : D ω = C ω := by funext k; simp [hD, h]
      simp only [rowVarSum] at h ⊢
      rw [this]
      exact h
    · have : D ω = fun _ => (0 : ℂ) := by funext k; simp [hD, h]
      simp [rowVarSum, this]
  -- the second moment of the frozen family vanishes
  have hzero : ∫⁻ ω, ENNReal.ofReal (‖rowSum d N u i D ω‖ ^ (2 * 1)) ∂(P d) = 0 := by
    refine le_antisymm ?_ (zero_le)
    refine lintegral_norm_rowSum_pow_le_of_const hu D hDmeas hDC fun ω => ?_
    simp [hDvar ω]
  have hae : ∀ᵐ ω ∂(P d), ENNReal.ofReal (‖rowSum d N u i D ω‖ ^ (2 * 1)) = 0 := by
    rw [lintegral_eq_zero_iff'] at hzero
    · exact hzero
    · refine (ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm ?_) _)).aemeasurable
      unfold rowSum
      exact Finset.measurable_sum _ fun k _ =>
        (measurable_Hflow d N u i k.1).mul ((measurable_pi_apply k.1).comp hDmeas)
  filter_upwards [hae] with ω hω hV
  have hDC' : D ω = C ω := by funext k; simp [hD, hV]
  have : ‖rowSum d N u i D ω‖ ^ (2 * 1) = 0 := by
    have := ENNReal.ofReal_eq_zero.1 hω
    have hnn : (0 : ℝ) ≤ ‖rowSum d N u i D ω‖ ^ (2 * 1) := by positivity
    linarith
  have hnorm : ‖rowSum d N u i D ω‖ = 0 := by
    have hp : ‖rowSum d N u i D ω‖ ^ (2 * 1) = ‖rowSum d N u i D ω‖ ^ 2 := by norm_num
    rw [hp, pow_eq_zero_iff (by norm_num)] at this
    exact this
  have : rowSum d N u i D ω = 0 := by simpa using hnorm
  rwa [show rowSum d N u i D ω = rowSum d N u i C ω by
    unfold rowSum; simp only [hDC']] at this

/-- Normalising the coefficients divides the row sum by the conditional standard deviation. -/
theorem rowSum_rowCoeffNorm (C : Ω d → d.Idx N → ℂ) {ω : Ω d}
    (hV : 0 < rowVarSum d N u i C ω) :
    rowSum d N u i (rowCoeffNorm d N u i C) ω
      = ((Real.sqrt (rowVarSum d N u i C ω) : ℂ))⁻¹ * rowSum d N u i C ω := by
  unfold rowSum rowCoeffNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hV, ↓reduceIte]
  field_simp

/-- **The row LDE as a high-probability inequality.**  For every `τ > 0`, with overwhelming
probability every pair `(i, j)` satisfies
`‖∑_{k ≠ i} H_{ik} C_{k}‖² ≤ N^{2τ} · u ∑_k S_{ik}|C_k|²`. -/
theorem highProb_norm_rowSum_sq_le (hu : 0 ≤ u) {U : ℕ → Type*} [∀ N, Fintype (U N)] {Ccard : ℝ}
    (hcard : ∀ᶠ N : ℕ in Filter.atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard)
    (row : ∀ N, U N → d.Idx N) (C : ∀ N, U N → Ω d → d.Idx N → ℂ)
    (hCmeas : ∀ N q, Measurable (C N q))
    (hC : ∀ N q (ω ω' : Ω d),
      (∀ c ∈ offRowCoord d N (row N q), ω c = ω' c) → C N q ω = C N q ω')
    {τ : ℝ} (hτ : 0 < τ) :
    HighProb (P d) (fun N => {ω | ∀ q : U N,
      ‖rowSum d N u (row N q) (C N q) ω‖ ^ 2
        ≤ (N : ℝ) ^ (2 * τ) * rowVarSum d N u (row N q) (C N q) ω}) := by
  classical
  -- the normalised sums are `≺ 1`
  have hgood := (stochDom_rowSum_general (d := d) (u := u) hu hcard row C hCmeas hC).highProb hτ
  -- the degenerate fibres are negligible
  have hdeg : HighProb (P d) (fun N => {ω | ∀ q : U N,
      rowVarSum d N u (row N q) (C N q) ω = 0 → rowSum d N u (row N q) (C N q) ω = 0}) := by
    intro D hD
    filter_upwards with N
    have hae : ∀ᵐ ω ∂(P d), ∀ q : U N,
        rowVarSum d N u (row N q) (C N q) ω = 0 → rowSum d N u (row N q) (C N q) ω = 0 := by
      rw [MeasureTheory.ae_all_iff]
      intro q
      exact rowSum_ae_eq_zero_of_varSum_eq_zero hu (C N q) (hCmeas N q) (hC N q)
    have : (P d) {ω | ¬ ∀ q : U N,
        rowVarSum d N u (row N q) (C N q) ω = 0 → rowSum d N u (row N q) (C N q) ω = 0} = 0 := by
      simpa [MeasureTheory.ae_iff] using hae
    rw [Set.compl_ofPred, this]
    simp
  refine (hgood.inter hdeg).mono ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN1 ω hω q
  obtain ⟨h1, h2⟩ := hω
  have hV0 : 0 ≤ rowVarSum d N u (row N q) (C N q) ω :=
    rowVarSum_nonneg hu (C N q) ω
  rcases eq_or_lt_of_le hV0 with hV | hV
  · rw [← hV, h2 q hV.symm]
    simp
  · have hs : (0 : ℝ) < Real.sqrt (rowVarSum d N u (row N q) (C N q) ω) := Real.sqrt_pos.2 hV
    have hnorm := h1 q
    rw [rowSum_rowCoeffNorm (C N q) hV, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hs.le, mul_one] at hnorm
    have hle : ‖rowSum d N u (row N q) (C N q) ω‖
        ≤ (N : ℝ) ^ τ * Real.sqrt (rowVarSum d N u (row N q) (C N q) ω) := by
      rw [inv_mul_le_iff₀ hs] at hnorm
      linarith [hnorm]
    have hnn : (0 : ℝ) ≤ ‖rowSum d N u (row N q) (C N q) ω‖ := norm_nonneg _
    have hrhs : (0 : ℝ) ≤ (N : ℝ) ^ τ * Real.sqrt (rowVarSum d N u (row N q) (C N q) ω) := by
      have : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (by positivity) τ
      positivity
    have hsq := mul_le_mul hle hle hnn hrhs
    have hsqrt : Real.sqrt (rowVarSum d N u (row N q) (C N q) ω) *
        Real.sqrt (rowVarSum d N u (row N q) (C N q) ω)
        = rowVarSum d N u (row N q) (C N q) ω := Real.mul_self_sqrt hV0
    have hNpow : (N : ℝ) ^ τ * (N : ℝ) ^ τ = (N : ℝ) ^ (2 * τ) := by
      rw [← Real.rpow_add (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1)]
      congr 1
      ring
    calc ‖rowSum d N u (row N q) (C N q) ω‖ ^ 2
        = ‖rowSum d N u (row N q) (C N q) ω‖ * ‖rowSum d N u (row N q) (C N q) ω‖ := by ring
      _ ≤ ((N : ℝ) ^ τ * Real.sqrt (rowVarSum d N u (row N q) (C N q) ω)) *
          ((N : ℝ) ^ τ * Real.sqrt (rowVarSum d N u (row N q) (C N q) ω)) := hsq
      _ = ((N : ℝ) ^ τ * (N : ℝ) ^ τ) *
          (Real.sqrt (rowVarSum d N u (row N q) (C N q) ω) *
            Real.sqrt (rowVarSum d N u (row N q) (C N q) ω)) := by ring
      _ = (N : ℝ) ^ (2 * τ) * rowVarSum d N u (row N q) (C N q) ω := by
          rw [hNpow, hsqrt]

end RBM.Gauss
