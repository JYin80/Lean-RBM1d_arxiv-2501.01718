/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.OUCommonFlow
import RBM1D.Flow.OUComparisonHessian
import RBM1D.Flow.GreenSpectralAlphaTail
import RBM1D.Flow.StieltjesEtaMonotone
import RBM1D.Defs.MatrixMeasurable
import RBM1D.Delocalization

/-!
# Step 3 of Theorem 2.6: the covering lemma and the weighted `L₁` kernel bound

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Theorem 2.6, Step 3.

* `RBM.sum_mass_window_le_im_green`, `RBM.sum_mass_window_le_of_im_green_le`: the deterministic
  covering lemma. A bound on `Im G_xx` at the single scale `η`, on the grid
  `E₀ - r + 2ηj`, `j ≤ ⌈r/η⌉₊`, controls the eigenvector mass at `x` of every spectral window
  `[E₀ - r, E₀ + r]`, `r ≥ 0`.
* `RBM.Gauss.InWindow222`: the spectral window (2.22).
* `RBM.Gauss.expect_L1_weighted_le`: the `L₁` half of the per-time bound behind (2.28)/(2.29), in
  the weighted form produced by (2.25), for the OU flow on the common carrier, from the
  single-scale local law `FlowLocalLaw` ((2.26) at `η̃ = N^{-1+2τ_U}`) and the flow QUE input
  `FlowEq747` ((2.27) via (7.47)).  The exponent is `1 - c/36 + (3|s|+16)τ_U`; the paper's `c/18`
  becomes `c/36` because of the QUE threshold of `measure_bad_flow_of_eq747`.

The local law is used only at its single scale `η̃`, at finitely many deterministic energies
(covering grids); larger scales are recovered by the covering lemma.
-/

open MeasureTheory Filter Matrix Topology
open scoped ENNReal

namespace RBM

/-- Real core of the covering: every `a` with `|a - E₀| ≤ r` is within `η` of one of the
`⌈r/η⌉₊ + 1` centres `E₀ - r + 2ηj`. -/
private theorem covering_exists_center {η r E₀ a : ℝ} (hη : 0 < η) (ha : |a - E₀| ≤ r) :
    ∃ j ∈ Finset.range (⌈r / η⌉₊ + 1), |a - (E₀ - r + 2 * η * j)| ≤ η := by
  have hr : 0 ≤ r := (abs_nonneg _).trans ha
  set x : ℝ := (a - E₀ + r) / (2 * η) with hx
  have hx0 : 0 ≤ x := by
    rw [hx]; apply div_nonneg _ (by positivity); linarith [(abs_le.1 ha).1]
  have hxr : x ≤ r / η := by
    rw [hx, div_le_div_iff₀ (by positivity) hη]
    nlinarith [(abs_le.1 ha).2]
  set j : ℕ := ⌊x + 1 / 2⌋₊ with hj
  have hj1 : (j : ℝ) ≤ x + 1 / 2 := Nat.floor_le (by linarith)
  have hj2 : x + 1 / 2 < j + 1 := Nat.lt_floor_add_one _
  refine ⟨j, ?_, ?_⟩
  · rw [Finset.mem_range]
    have h1 : (j : ℝ) < r / η + 1 := by linarith [div_nonneg hr hη.le]
    have h2 : r / η ≤ (⌈r / η⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast (show (j : ℝ) < (⌈r / η⌉₊ : ℝ) + 1 by linarith)
  · have hax : a = E₀ - r + 2 * η * x := by rw [hx]; field_simp; ring
    rw [hax, abs_le]
    constructor <;> nlinarith

/-- **Covering lemma (one scale ⇒ every larger scale).**  The eigenvector mass at `x` of the
eigenvalues in `[E₀ - r, E₀ + r]` is bounded by `2η` times the sum of `Im G_xx` at the
`⌈r/η⌉₊ + 1` points `E₀ - r + 2ηj + iη` (all at the single scale `η`). -/
theorem sum_mass_window_le_im_green {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {η r : ℝ} (hη : 0 < η) (hr : 0 ≤ r) (E₀ : ℝ)
    (x : n) :
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 ≤
      2 * η * ∑ j ∈ Finset.range (⌈r / η⌉₊ + 1),
        (green H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) x x).im := by
  set K := ⌈r / η⌉₊ + 1
  set w : n → ℝ := fun l => ‖hH.eigenvectorBasis l x‖ ^ 2
  set k : ℕ → n → ℝ := fun j l =>
    w l * (η / ((hH.eigenvalues l - (E₀ - r + 2 * η * j)) ^ 2 + η ^ 2))
  have hk0 : ∀ j l, 0 ≤ k j l := fun j l => by
    simp only [k, w]; positivity
  have hG : ∀ j : ℕ, (green H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) x x).im =
      ∑ l, k j l := by
    intro j
    rw [im_green_apply_self hH _ hη.ne']
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [k, w, Complex.normSq_eq_norm_sq]
    ring
  have hpt : ∀ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
      w l ≤ 2 * η * ∑ j ∈ Finset.range K, k j l := by
    intro l hl
    obtain ⟨j, hjK, hjc⟩ := covering_exists_center hη (Finset.mem_filter.1 hl).2
    have hw : 0 ≤ w l := by simp only [w]; positivity
    set D := (hH.eigenvalues l - (E₀ - r + 2 * η * j)) ^ 2 + η ^ 2
    have hD : 0 < D := by positivity
    have hDle : D ≤ 2 * η ^ 2 := by
      have : (hH.eigenvalues l - (E₀ - r + 2 * η * j)) ^ 2 ≤ η ^ 2 := by
        apply sq_le_sq' <;> linarith [(abs_le.1 hjc).1, (abs_le.1 hjc).2]
      simp only [D]; linarith
    have hone : w l ≤ 2 * η * k j l := by
      simp only [k]
      rw [show 2 * η * (w l * (η / D)) = w l * (2 * η ^ 2 / D) by field_simp]
      have : 1 ≤ 2 * η ^ 2 / D := by rw [le_div_iff₀ hD]; linarith
      nlinarith
    calc w l ≤ 2 * η * k j l := hone
      _ ≤ 2 * η * ∑ j ∈ Finset.range K, k j l := by
        gcongr
        exact Finset.single_le_sum (fun j _ => hk0 j l) hjK
  calc ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r), w l
      ≤ ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
          2 * η * ∑ j ∈ Finset.range K, k j l := Finset.sum_le_sum hpt
    _ ≤ ∑ l, 2 * η * ∑ j ∈ Finset.range K, k j l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro l _ _
        have := fun j => hk0 j l
        positivity
    _ = 2 * η * ∑ j ∈ Finset.range K,
          (green H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) x x).im := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [hG]

/-- Consumer form: a single-scale bound `Im G_xx ≤ Cb` at the grid points gives window mass
`≤ 2(r + 2η) Cb` at every scale `r ≥ 0`. -/
theorem sum_mass_window_le_of_im_green_le {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {η r Cb : ℝ} (hη : 0 < η) (hr : 0 ≤ r)
    (hCb : 0 ≤ Cb) (E₀ : ℝ) (x : n)
    (hG : ∀ j ∈ Finset.range (⌈r / η⌉₊ + 1),
      (green H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) x x).im ≤ Cb) :
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 ≤ 2 * (r + 2 * η) * Cb := by
  refine (sum_mass_window_le_im_green hH hη hr E₀ x).trans ?_
  have hsum := Finset.sum_le_sum hG
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hK : ((⌈r / η⌉₊ + 1 : ℕ) : ℝ) ≤ r / η + 2 := by
    push_cast; linarith [Nat.ceil_lt_add_one (div_nonneg hr hη.le)]
  calc 2 * η * _ ≤ 2 * η * (((⌈r / η⌉₊ + 1 : ℕ) : ℝ) * Cb) := by gcongr
    _ ≤ 2 * η * ((r / η + 2) * Cb) := by gcongr
    _ = 2 * (r + 2 * η) * Cb := by field_simp

/-! ### Deterministic consequences of single-scale grid bounds -/

section Grid

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The single-scale grid bound used throughout: `Im G_xx ≤ Cb` at every point of the covering
grid of centre `E₀` and radius `r` (scale `η`), for every site `x`. -/
def Step3KernelBounds.GridGood (H : Matrix n n ℂ) (η Cb E₀ r : ℝ) : Prop :=
  ∀ j ∈ Finset.range (⌈r / η⌉₊ + 1), ∀ x : n,
    (green H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) x x).im ≤ Cb

open Step3KernelBounds

variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

include hH in
private theorem gridGood_mass {η Cb E₀ r : ℝ} (hη : 0 < η) (hr : 0 ≤ r) (hCb : 0 ≤ Cb)
    (hG : GridGood H η Cb E₀ r) (x : n) :
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 ≤ 2 * (r + 2 * η) * Cb :=
  sum_mass_window_le_of_im_green_le hH hη hr hCb E₀ x fun j hj => hG j hj x

include hH in
/-- Eigenvalue counting from the site masses: `#{l : |λ_l - E₀| ≤ r} ≤ |n| · 2(r+2η)Cb`. -/
private theorem gridGood_count {η Cb E₀ r : ℝ} (hη : 0 < η) (hr : 0 ≤ r) (hCb : 0 ≤ Cb)
    (hG : GridGood H η Cb E₀ r) :
    ((Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r)).card : ℝ) ≤
      (Fintype.card n : ℝ) * (2 * (r + 2 * η) * Cb) := by
  have h1 : ((Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r)).card : ℝ) =
      ∑ x : n, ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [sum_sq_norm_eigenvector hH]
    simp
  rw [h1]
  calc _ ≤ ∑ _x : n, 2 * (r + 2 * η) * Cb :=
        Finset.sum_le_sum fun x _ => gridGood_mass hH hη hr hCb hG x
    _ = _ := by simp

include hH in
/-- Bulk delocalization from the grid: `|λ_α - E₀| ≤ R` gives `|u_α(x)|² ≤ 2η Cb`. -/
private theorem gridGood_deloc {η Cb E₀ R : ℝ} (hη : 0 < η)
    (hG : GridGood H η Cb E₀ R) {α : n} (hα : |hH.eigenvalues α - E₀| ≤ R) (x : n) :
    ‖hH.eigenvectorBasis α x‖ ^ 2 ≤ 2 * η * Cb := by
  obtain ⟨j, hj, hjc⟩ := covering_exists_center hη hα
  have hGj := hG j hj x
  rw [im_green_apply_self hH _ hη.ne'] at hGj
  set e : ℝ := E₀ - R + 2 * η * j
  have hterm : η * Complex.normSq (hH.eigenvectorBasis α x) /
      ((hH.eigenvalues α - e) ^ 2 + η ^ 2) ≤
      ∑ l, η * Complex.normSq (hH.eigenvectorBasis l x) /
        ((hH.eigenvalues l - e) ^ 2 + η ^ 2) :=
    Finset.single_le_sum (f := fun l => η * Complex.normSq (hH.eigenvectorBasis l x) /
        ((hH.eigenvalues l - e) ^ 2 + η ^ 2))
      (fun l _ => div_nonneg (mul_nonneg hη.le (Complex.normSq_nonneg _)) (by positivity))
      (Finset.mem_univ α)
  have hsq : (hH.eigenvalues α - e) ^ 2 ≤ η ^ 2 := by
    apply sq_le_sq' <;> linarith [(abs_le.1 hjc).1, (abs_le.1 hjc).2]
  have hD : 0 < (hH.eigenvalues α - e) ^ 2 + η ^ 2 := by positivity
  have hv : 0 ≤ ‖hH.eigenvectorBasis α x‖ ^ 2 := by positivity
  rw [Complex.normSq_eq_norm_sq] at hterm
  have hle : ‖hH.eigenvectorBasis α x‖ ^ 2 ≤
      2 * η * (η * ‖hH.eigenvectorBasis α x‖ ^ 2 / ((hH.eigenvalues α - e) ^ 2 + η ^ 2)) := by
    rw [mul_div_assoc', le_div_iff₀ hD]
    nlinarith
  calc _ ≤ 2 * η * (η * ‖hH.eigenvectorBasis α x‖ ^ 2 /
        ((hH.eigenvalues α - e) ^ 2 + η ^ 2)) := hle
    _ ≤ 2 * η * Cb := by gcongr; exact hterm.trans hGj

omit [DecidableEq n] in
/-- The zero-radius grid is the single energy `E₀`: a bound on every `Im G_xx(E₀ + iη)` bounds
`Im m(E₀ + iη)`. -/
private theorem gridGood_zero_stieltjes [DecidableEq n] [Nonempty n] {η Cb E₀ : ℝ}
    (hG : GridGood H η Cb E₀ 0) :
    (stieltjes H ((E₀ : ℂ) + η * Complex.I)).im ≤ Cb := by
  have hx : ∀ x : n, (green H ((E₀ : ℂ) + η * Complex.I) x x).im ≤ Cb := by
    intro x
    have := hG 0 (by simp) x
    simpa using this
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have htr : (stieltjes H ((E₀ : ℂ) + η * Complex.I)).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ x : n, (green H ((E₀ : ℂ) + η * Complex.I) x x).im := by
    rw [stieltjes, Matrix.trace, Complex.mul_im, Complex.im_sum, Complex.re_sum]
    have h1 : ((Fintype.card n : ℂ)⁻¹).im = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
    have h2 : ((Fintype.card n : ℂ)⁻¹).re = (Fintype.card n : ℝ)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [h1, h2]
    simp [Matrix.diag]
  rw [htr]
  calc _ ≤ (Fintype.card n : ℝ)⁻¹ * ∑ _x : n, Cb := by
        gcongr with x; exact hx x
    _ = Cb := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

end Grid

/-! ### Dyadic decomposition and pole bounds -/

/-- Dyadic majorant: for `f` antitone and nonnegative on `(0,∞)`, `ρ < d ≤ 2^K ρ` gives
`f d ≤ ∑_{k<K} 1_{d ≤ 2^{k+1}ρ} f(2^k ρ)`. -/
private theorem dyadic_le_sum {f : ℝ → ℝ} (hf : ∀ a b, 0 < a → a ≤ b → f b ≤ f a)
    (hf0 : ∀ a, 0 < a → 0 ≤ f a) {ρ d : ℝ} (hρ : 0 < ρ) :
    ∀ K : ℕ, ρ < d → d ≤ 2 ^ K * ρ →
      f d ≤ ∑ k ∈ Finset.range K, (if d ≤ 2 ^ (k + 1) * ρ then f (2 ^ k * ρ) else 0) := by
  intro K
  induction K with
  | zero => intro h1 h2; simp at h2; linarith
  | succ K ih =>
    intro h1 h2
    rw [Finset.sum_range_succ]
    have hnn : 0 ≤ ∑ k ∈ Finset.range K,
        (if d ≤ 2 ^ (k + 1) * ρ then f (2 ^ k * ρ) else 0) :=
      Finset.sum_nonneg fun k _ => by split_ifs <;> first | exact hf0 _ (by positivity) | exact le_rfl
    by_cases hd : d ≤ 2 ^ K * ρ
    · have := ih h1 hd
      have hlast : 0 ≤ (if d ≤ 2 ^ (K + 1) * ρ then f (2 ^ K * ρ) else 0) := by
        split_ifs; exact hf0 _ (by positivity)
      linarith
    · push Not at hd
      simp only [h2, ite_true]
      have := hf (2 ^ K * ρ) d (by positivity) hd.le
      linarith

private theorem geom_half_sum_le (K : ℕ) : ∑ k ∈ Finset.range K, ((2 : ℝ) ^ k)⁻¹ ≤ 2 := by
  have h := sum_geometric_two_le K
  simpa [one_div, inv_pow] using h

section Poles

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

private theorem pole_norm_eq (u : ℂ) (α : n) :
    ‖spectralPole hH u α‖ = ‖(hH.eigenvalues α : ℂ) - u‖⁻¹ := by
  rw [spectralPole, norm_inv]

private theorem pole_norm_le_inv_im {u : ℂ} (hη : 0 < u.im) (α : n) :
    ‖spectralPole hH u α‖ ≤ u.im⁻¹ := by
  rw [pole_norm_eq]
  have h : u.im ≤ ‖(hH.eigenvalues α : ℂ) - u‖ := by
    have := Complex.abs_im_le_norm ((hH.eigenvalues α : ℂ) - u)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at this
    rwa [abs_of_pos hη] at this
  exact inv_anti₀ hη h

private theorem pole_norm_le_inv_dist {u : ℂ} (α : n) (hd : 0 < |hH.eigenvalues α - u.re|) :
    ‖spectralPole hH u α‖ ≤ |hH.eigenvalues α - u.re|⁻¹ := by
  rw [pole_norm_eq]
  have h : |hH.eigenvalues α - u.re| ≤ ‖(hH.eigenvalues α : ℂ) - u‖ := by
    have := Complex.abs_re_le_norm ((hH.eigenvalues α : ℂ) - u)
    simpa only [Complex.sub_re, Complex.ofReal_re] using this
  exact inv_anti₀ hd h

theorem Step3KernelBounds.pole_norm_le_inv_im' {u : ℂ} (hη : 0 < u.im) (α : n) :
    ‖((hH.eigenvalues α : ℂ) - u)⁻¹‖ ≤ u.im⁻¹ :=
  pole_norm_le_inv_im hH hη α

private theorem pole_norm_sq_eq {u : ℂ} (α : n) :
    ‖spectralPole hH u α‖ ^ 2 = ((hH.eigenvalues α - u.re) ^ 2 + u.im ^ 2)⁻¹ := by
  rw [pole_norm_eq, inv_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
  ring

private theorem pole_norm_sq_le_inv_dist_sq {u : ℂ} (α : n)
    (hd : 0 < |hH.eigenvalues α - u.re|) :
    ‖spectralPole hH u α‖ ^ 2 ≤ (|hH.eigenvalues α - u.re| ^ 2)⁻¹ := by
  rw [← inv_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (pole_norm_le_inv_dist hH α hd) 2

include hH in
/-- Crude bound `Im m(w) ≤ 1/Im w`, and `Im m(w) ≥ 0`. -/
private theorem stieltjes_im_nonneg_le [Nonempty n] {w : ℂ} (hη : 0 < w.im) :
    0 ≤ (stieltjes H w).im ∧ (stieltjes H w).im ≤ w.im⁻¹ := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hf := stieltjes_im_eq_normalized_specWeight H hH w.re w.im hη
  rw [← hw] at hf
  rw [hf]
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ l : n, w.im / ((hH.eigenvalues l - w.re) ^ 2 + w.im ^ 2) ≤ w.im⁻¹ := by
    intro l
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg (hH.eigenvalues l - w.re)]
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => by positivity)
  · calc _ ≤ (Fintype.card n : ℝ)⁻¹ * ∑ _l : n, w.im⁻¹ := by
          gcongr with l; exact hterm l
      _ = w.im⁻¹ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

include hH in
open Step3KernelBounds in
/-- `Im m(w) ≤ (η̃/Im w) Cb` from the zero-radius grid at `Re w` (monotonicity in `η`). -/
private theorem stieltjes_im_le_of_grid [Nonempty n] {w : ℂ} (hη : 0 < w.im) {ηt Cb : ℝ}
    (hηη : w.im ≤ ηt) (hG : GridGood H ηt Cb w.re 0) :
    (stieltjes H w).im ≤ ηt / w.im * Cb := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hmono := stieltjes_eta_mul_im_mono H hH w.re w.im ηt hη hηη
  rw [← hw] at hmono
  have hT := gridGood_zero_stieltjes (H := H) hG
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  rw [div_mul_eq_mul_div, le_div_iff₀ hη, mul_comm]
  exact hmono.trans (mul_le_mul_of_nonneg_left hT hηt.le)

open Step3KernelBounds in
/-- `∑_α |p_α(u)|² ≤ (ηt/η²) |n| Cb` from the zero-radius grid at `Re u`. -/
private theorem sum_pole_sq_le_of_grid [Nonempty n] {u : ℂ} (hη : 0 < u.im) {ηt Cb : ℝ}
    (hηη : u.im ≤ ηt) (hG : GridGood H ηt Cb u.re 0) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 ≤ ηt / u.im ^ 2 * ((Fintype.card n : ℝ) * Cb) := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  have hT := gridGood_zero_stieltjes (H := H) hG
  have hf := stieltjes_im_eq_normalized_specWeight H hH u.re ηt hηt
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ l : n, ηt / ((hH.eigenvalues l - u.re) ^ 2 + ηt ^ 2) ≤
      (Fintype.card n : ℝ) * Cb := by
    rw [hf] at hT
    rw [inv_mul_le_iff₀ hcard] at hT
    exact hT
  have hterm : ∀ α : n, ‖spectralPole hH u α‖ ^ 2 ≤
      ηt / u.im ^ 2 * (ηt / ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) := by
    intro α
    rw [pole_norm_sq_eq]
    set x := (hH.eigenvalues α - u.re) ^ 2
    have hx : 0 ≤ x := sq_nonneg _
    rw [show ηt / u.im ^ 2 * (ηt / (x + ηt ^ 2)) = ηt ^ 2 / (u.im ^ 2 * (x + ηt ^ 2)) by
      field_simp]
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : u.im ^ 2 ≤ ηt ^ 2 := pow_le_pow_left₀ hη.le hηη 2
    nlinarith [mul_le_mul_of_nonneg_left h2 hx]
  calc _ ≤ ∑ α : n, ηt / u.im ^ 2 * (ηt / ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) :=
        Finset.sum_le_sum fun α _ => hterm α
    _ = ηt / u.im ^ 2 * ∑ α : n, ηt / ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

include hH in
open Step3KernelBounds in
/-- **The `Q_y` row.** `∑_γ |p_γ(u)| |u_γ(y)|² ≤ 6(η̃/η)Cb + 8K Cb + (2^K η̃)⁻¹` from the grids of
radii `2^k η̃`, `k ≤ K` (near part, `K` dyadic shells, completeness beyond `2^K η̃`). -/
private theorem sum_pole_mass_le {u : ℂ} (hη : 0 < u.im) {ηt Cb : ℝ} (hηη : u.im ≤ ηt)
    (hCb : 0 ≤ Cb) (K : ℕ) (hG : ∀ k ≤ K, GridGood H ηt Cb u.re (2 ^ k * ηt)) (y : n) :
    ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2 ≤
      6 * (ηt / u.im) * Cb + 8 * K * Cb + (2 ^ K * ηt)⁻¹ := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  set v : n → ℝ := fun γ => ‖hH.eigenvectorBasis γ y‖ ^ 2 with hv
  set dd : n → ℝ := fun γ => |hH.eigenvalues γ - u.re| with hdd
  have hv0 : ∀ γ, 0 ≤ v γ := fun γ => by positivity
  -- pointwise dyadic majorant
  have hpt : ∀ γ, ‖spectralPole hH u γ‖ * v γ ≤
      u.im⁻¹ * (if dd γ ≤ ηt then v γ else 0) +
        ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
          (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) + (2 ^ K * ηt)⁻¹ * v γ := by
    intro γ
    have hS0 : 0 ≤ ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
        (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (by split_ifs <;> simp [hv0])
    have hT0 : 0 ≤ (2 ^ K * ηt)⁻¹ * v γ := mul_nonneg (by positivity) (hv0 γ)
    by_cases h1 : dd γ ≤ ηt
    · simp only [h1, ite_true]
      have := mul_le_mul_of_nonneg_right (pole_norm_le_inv_im hH hη γ) (hv0 γ)
      linarith
    · push Not at h1
      have hdpos : 0 < dd γ := lt_trans hηt h1
      have hpd := mul_le_mul_of_nonneg_right (pole_norm_le_inv_dist hH γ hdpos) (hv0 γ)
      simp only [not_le.2 h1, ite_false, mul_zero, zero_add]
      by_cases h2 : dd γ ≤ 2 ^ K * ηt
      · have hdy := dyadic_le_sum (f := fun x => x⁻¹) (fun a b ha hab => inv_anti₀ ha hab)
          (fun a ha => inv_nonneg.2 ha.le) hηt K h1 h2
        have hdy' : (dd γ)⁻¹ * v γ ≤ ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
            (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) := by
          calc (dd γ)⁻¹ * v γ ≤ (∑ k ∈ Finset.range K,
                (if dd γ ≤ 2 ^ (k + 1) * ηt then (2 ^ k * ηt)⁻¹ else 0)) * v γ :=
                mul_le_mul_of_nonneg_right hdy (hv0 γ)
            _ = _ := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => ?_
                split_ifs <;> ring
        linarith
      · push Not at h2
        have : (dd γ)⁻¹ * v γ ≤ (2 ^ K * ηt)⁻¹ * v γ :=
          mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) h2.le) (hv0 γ)
        linarith
  -- mass bounds from the grids
  have hmass : ∀ r : ℝ, 0 ≤ r → GridGood H ηt Cb u.re r →
      ∑ γ, (if dd γ ≤ r then v γ else 0) ≤ 2 * (r + 2 * ηt) * Cb := by
    intro r hr hGr
    rw [← Finset.sum_filter]
    exact gridGood_mass hH hηt hr hCb hGr y
  have hm0 : ∑ γ, (if dd γ ≤ ηt then v γ else 0) ≤ 2 * (ηt + 2 * ηt) * Cb :=
    hmass ηt hηt.le (by simpa using hG 0 (Nat.zero_le _))
  have hmk : ∀ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
      ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) ≤ 8 * Cb := by
    intro k hk
    have hkK : k + 1 ≤ K := Finset.mem_range.1 hk
    have h := hmass (2 ^ (k + 1) * ηt) (by positivity) (hG (k + 1) hkK)
    have hp : (0 : ℝ) < 2 ^ k * ηt := by positivity
    have h1 : (2 ^ k * ηt)⁻¹ * ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) ≤
        (2 ^ k * ηt)⁻¹ * (2 * (2 ^ (k + 1) * ηt + 2 * ηt) * Cb) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : (2 ^ k * ηt)⁻¹ * (2 * (2 ^ (k + 1) * ηt + 2 * ηt) * Cb) =
        (4 + 4 * ((2 : ℝ) ^ k)⁻¹) * Cb := by
      field_simp; ring
    have h3 : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    nlinarith
  have hsumv : ∑ γ, v γ = 1 := sum_sq_norm_eigenvectorBasis hH y
  calc ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2
      = ∑ γ, ‖spectralPole hH u γ‖ * v γ := rfl
    _ ≤ ∑ γ, (u.im⁻¹ * (if dd γ ≤ ηt then v γ else 0) +
          ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
            (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) + (2 ^ K * ηt)⁻¹ * v γ) :=
        Finset.sum_le_sum fun γ _ => hpt γ
    _ = u.im⁻¹ * ∑ γ, (if dd γ ≤ ηt then v γ else 0) +
          ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
            ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) +
          (2 ^ K * ηt)⁻¹ * ∑ γ, v γ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_comm]
        congr 2
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ u.im⁻¹ * (2 * (ηt + 2 * ηt) * Cb) + ∑ _k ∈ Finset.range K, 8 * Cb +
          (2 ^ K * ηt)⁻¹ * 1 := by
        rw [hsumv]
        have hA : u.im⁻¹ * ∑ γ, (if dd γ ≤ ηt then v γ else 0) ≤
            u.im⁻¹ * (2 * (ηt + 2 * ηt) * Cb) :=
          mul_le_mul_of_nonneg_left hm0 (by positivity)
        have hB := Finset.sum_le_sum hmk
        linarith
    _ = 6 * (ηt / u.im) * Cb + 8 * K * Cb + (2 ^ K * ηt)⁻¹ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
        ring

end Poles

/-! ### Block profile: the `A_y` factor and the kernel -/

section Block

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {Hm : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : Hm.IsHermitian)

omit [NeZero L] [NeZero W] in
private theorem centered_profile_norm_le (x y : ZMod L × Fin W) :
    ‖Svar L W x y - ((L * W : ℕ) : ℂ)⁻¹‖ ≤ Sblk L W x y + (L * W : ℝ)⁻¹ := by
  calc ‖Svar L W x y - ((L * W : ℕ) : ℂ)⁻¹‖ ≤
        ‖Svar L W x y‖ + ‖((L * W : ℕ) : ℂ)⁻¹‖ := norm_sub_le _ _
    _ = Sblk L W x y + (L * W : ℝ)⁻¹ := by
      rw [Svar_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Sblk_nonneg x y), norm_inv, Complex.norm_natCast]
      simp only [Nat.cast_mul]

include hH in
/-- `|M_{y,α}| ≤ 2N · max_x |u_α(x)|²`. -/
private theorem norm_blockM_le_of_mass (hL : 3 ≤ L) (a0 : ZMod L) (α : ZMod L × Fin W)
    {D : ℝ} (hMass : ∀ x, ‖hH.eigenvectorBasis α x‖ ^ 2 ≤ D) :
    ‖blockM hH a0 α‖ ≤ 2 * (L * W : ℝ) * D := by
  have β : Fin W := ⟨0, NeZero.pos W⟩
  rw [blockM_eq hL hH a0 β α]
  have hN : (0 : ℝ) < (L * W : ℝ) := by
    exact_mod_cast Nat.mul_pos (NeZero.pos L) (NeZero.pos W)
  have hsumS : ∑ x : ZMod L × Fin W, (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) = 2 := by
    rw [Finset.sum_add_distrib, sum_Sblk_col hL (a0, β), Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
    norm_num
  calc ‖((L * W : ℕ) : ℂ) * ∑ x, ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) *
        (Svar L W x (a0, β) - ((L * W : ℕ) : ℂ)⁻¹)‖
      ≤ (L * W : ℝ) * ∑ x, ‖hH.eigenvectorBasis α x‖ ^ 2 *
          (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) := by
        rw [norm_mul, Complex.norm_natCast, Nat.cast_mul]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) hN.le
        refine Finset.sum_le_sum fun x _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (centered_profile_norm_le x (a0, β)) (by positivity)
    _ ≤ (L * W : ℝ) * ∑ x, D * (Sblk L W x (a0, β) + (L * W : ℝ)⁻¹) := by
        gcongr with x
        · exact add_nonneg (Sblk_nonneg _ _) (by positivity)
        · exact hMass x
    _ = 2 * (L * W : ℝ) * D := by
        rw [← Finset.mul_sum, hsumS]; ring

include hH in
open Step3KernelBounds in
/-- Bulk bound `|M_{y,α}| ≤ 4Nη̃Cb` for `|λ_α - Re u| ≤ R`, from the grid of radius `R`. -/
private theorem norm_blockM_le_of_grid (hL : 3 ≤ L) (a0 : ZMod L) {ηt Cb E₀ R : ℝ}
    (hηt : 0 < ηt) (hG : GridGood Hm ηt Cb E₀ R) {α : ZMod L × Fin W}
    (hα : |hH.eigenvalues α - E₀| ≤ R) :
    ‖blockM hH a0 α‖ ≤ 4 * (L * W : ℝ) * ηt * Cb := by
  have := norm_blockM_le_of_mass hH hL a0 α (D := 2 * ηt * Cb)
    (fun x => gridGood_deloc hH hηt hG hα x)
  linarith

include hH in
open Step3KernelBounds in
/-- **The `A_y` row.** Window part (`|λ_α - Re u| ≤ w'`, `|M| ≤ Mwin`), dyadic bulk part
(`w' < |λ_α - Re u| ≤ 2^{K'}w'`, delocalization and counting) and the part outside
`2^{K'}w'` (completeness `∑_α|M_{y,α}| ≤ 2N`). -/
private theorem sum_pole_sq_blockM_le (hL : 3 ≤ L) (a0 : ZMod L) {u : ℂ} (hη : 0 < u.im)
    {ηt Cb w' Rd Mwin : ℝ} (hηη : u.im ≤ ηt) (hCb : 0 ≤ Cb) (hw' : 0 < w')
    (hMwin : 0 ≤ Mwin) (K' : ℕ) (hRd : 2 ^ K' * w' ≤ Rd)
    (hGd : GridGood Hm ηt Cb u.re Rd) (hGc : ∀ k ≤ K', GridGood Hm ηt Cb u.re (2 ^ k * w'))
    (hG0 : GridGood Hm ηt Cb u.re 0)
    (hwin : ∀ α, |hH.eigenvalues α - u.re| ≤ w' → ‖blockM hH a0 α‖ ≤ Mwin) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM hH a0 α‖ ≤
      Mwin * (ηt / u.im ^ 2 * ((L * W : ℝ) * Cb)) +
        4 * (L * W : ℝ) * ηt * Cb * (2 * (L * W : ℝ) * Cb * (4 / w' + 4 * ηt / w' ^ 2)) +
        ((2 ^ K' * w') ^ 2)⁻¹ * (2 * (L * W : ℝ)) := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  have hN : (0 : ℝ) < (L * W : ℝ) := by
    exact_mod_cast Nat.mul_pos (NeZero.pos L) (NeZero.pos W)
  have hcard : (Fintype.card (ZMod L × Fin W) : ℝ) = (L * W : ℝ) := by
    simp [Fintype.card_prod, ZMod.card]
  set dd : ZMod L × Fin W → ℝ := fun α => |hH.eigenvalues α - u.re| with hdd
  set Mb : ℝ := 4 * (L * W : ℝ) * ηt * Cb with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  have hpt : ∀ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM hH a0 α‖ ≤
      (if dd α ≤ w' then Mwin * ‖spectralPole hH u α‖ ^ 2 else 0) +
        Mb * ∑ k ∈ Finset.range K',
          (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) +
        ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM hH a0 α‖ := by
    intro α
    have hS0 : 0 ≤ Mb * ∑ k ∈ Finset.range K',
        (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) :=
      mul_nonneg hMb0 (Finset.sum_nonneg fun k _ => by split_ifs <;> positivity)
    have hT0 : 0 ≤ ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM hH a0 α‖ := by positivity
    by_cases h1 : dd α ≤ w'
    · simp only [h1, ite_true]
      have := mul_le_mul_of_nonneg_left (hwin α h1) (sq_nonneg ‖spectralPole hH u α‖)
      nlinarith
    · push Not at h1
      simp only [not_le.2 h1, ite_false, zero_add]
      have hdpos : 0 < dd α := lt_trans hw' h1
      have hp2 := pole_norm_sq_le_inv_dist_sq hH α hdpos
      by_cases h2 : dd α ≤ 2 ^ K' * w'
      · have hM := norm_blockM_le_of_grid hH hL a0 hηt hGd (h2.trans hRd)
        have hdy := dyadic_le_sum (f := fun x => (x ^ 2)⁻¹)
          (fun a b ha hab => inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hab 2))
          (fun a ha => by positivity) hw' K' h1 h2
        have : ‖spectralPole hH u α‖ ^ 2 * ‖blockM hH a0 α‖ ≤ (dd α ^ 2)⁻¹ * Mb :=
          mul_le_mul hp2 hM (norm_nonneg _) (by positivity)
        have h3 : (dd α ^ 2)⁻¹ * Mb ≤ Mb * ∑ k ∈ Finset.range K',
            (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hdy hMb0
        linarith
      · push Not at h2
        have h4 : (dd α ^ 2)⁻¹ ≤ ((2 ^ K' * w') ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2.le 2)
        have : ‖spectralPole hH u α‖ ^ 2 * ‖blockM hH a0 α‖ ≤
            ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM hH a0 α‖ :=
          mul_le_mul_of_nonneg_right (hp2.trans h4) (norm_nonneg _)
        linarith
  -- window part
  have hW1 : ∑ α, (if dd α ≤ w' then Mwin * ‖spectralPole hH u α‖ ^ 2 else 0) ≤
      Mwin * (ηt / u.im ^ 2 * ((L * W : ℝ) * Cb)) := by
    calc _ ≤ ∑ α, Mwin * ‖spectralPole hH u α‖ ^ 2 :=
          Finset.sum_le_sum fun α _ => by split_ifs <;> [exact le_rfl; positivity]
      _ = Mwin * ∑ α, ‖spectralPole hH u α‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          have := sum_pole_sq_le_of_grid hH hη hηη hG0
          rwa [hcard] at this
  -- dyadic counting part
  have hcount : ∀ k ∈ Finset.range K',
      ∑ α, (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) ≤
        2 * (L * W : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ := by
    intro k hk
    have hkK : k + 1 ≤ K' := Finset.mem_range.1 hk
    have hc := gridGood_count hH hηt (by positivity) hCb (hGc (k + 1) hkK)
    rw [hcard] at hc
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hp : (0 : ℝ) < 2 ^ k * w' := by positivity
    calc _ ≤ (L * W : ℝ) * (2 * (2 ^ (k + 1) * w' + 2 * ηt) * Cb) * ((2 ^ k * w') ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 2 * (L * W : ℝ) * Cb * (2 / w' * ((2 : ℝ) ^ k)⁻¹ +
            2 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹) := by
          field_simp; ring
      _ ≤ 2 * (L * W : ℝ) * Cb * (2 / w' * ((2 : ℝ) ^ k)⁻¹ +
            2 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * 1) := by
          gcongr
          exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      _ = _ := by ring
  have hW2 : ∑ α, Mb * ∑ k ∈ Finset.range K',
      (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) ≤
      Mb * (2 * (L * W : ℝ) * Cb * (4 / w' + 4 * ηt / w' ^ 2)) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine mul_le_mul_of_nonneg_left ?_ hMb0
    calc _ ≤ ∑ k ∈ Finset.range K',
          2 * (L * W : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ :=
          Finset.sum_le_sum hcount
      _ = 2 * (L * W : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) *
            ∑ k ∈ Finset.range K', ((2 : ℝ) ^ k)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 2 * (L * W : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) * 2 := by
          gcongr; exact geom_half_sum_le K'
      _ = _ := by ring
  -- outside part
  have hW3 : ∑ α, ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM hH a0 α‖ ≤
      ((2 ^ K' * w') ^ 2)⁻¹ * (2 * (L * W : ℝ)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_norm_blockM_le hH hL a0 ⟨0, NeZero.pos W⟩)
      (by positivity)
  calc _ ≤ ∑ α, ((if dd α ≤ w' then Mwin * ‖spectralPole hH u α‖ ^ 2 else 0) +
        Mb * ∑ k ∈ Finset.range K',
          (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) +
        ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM hH a0 α‖) := Finset.sum_le_sum fun α _ => hpt α
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := by linarith

include hH in
/-- Crude `A_y ≤ 2N/η²`. -/
private theorem sum_pole_sq_blockM_le_crude (hL : 3 ≤ L) (a0 : ZMod L) {u : ℂ}
    (hη : 0 < u.im) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM hH a0 α‖ ≤ (u.im ^ 2)⁻¹ * (2 * (L * W : ℝ)) := by
  calc _ ≤ ∑ α, (u.im ^ 2)⁻¹ * ‖blockM hH a0 α‖ := by
        refine Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [← inv_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (pole_norm_le_inv_im hH hη α) 2
    _ = (u.im ^ 2)⁻¹ * ∑ α, ‖blockM hH a0 α‖ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_norm_blockM_le hH hL a0 ⟨0, NeZero.pos W⟩)
        (by positivity)

omit [NeZero W] in
include hH in
/-- Crude `Q_y ≤ 1/η`. -/
private theorem sum_pole_mass_le_crude {u : ℂ} (hη : 0 < u.im) (y : ZMod L × Fin W) :
    ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2 ≤ u.im⁻¹ := by
  calc _ ≤ ∑ γ, u.im⁻¹ * ‖hH.eigenvectorBasis γ y‖ ^ 2 :=
        Finset.sum_le_sum fun γ _ =>
          mul_le_mul_of_nonneg_right (pole_norm_le_inv_im hH hη γ) (by positivity)
    _ = u.im⁻¹ := by rw [← Finset.mul_sum, sum_sq_norm_eigenvectorBasis hH y, mul_one]

end Block

/-- **Spectral form of the `L₁` kernel** ((2.31) with the `β`-masses kept):
`L₁(u) ≤ 4 N⁻¹ ∑_y N⁻¹ A_y Q_y`, `A_y = ∑_α |p_α|²|M_{y,α}|`, `Q_y = ∑_γ |p_γ||u_γ(y)|²`,
for both resolvent signs. -/
private theorem paperL1Kernel_le_spectral (d : Gauss.Dims) (N : ℕ)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) {u : ℂ} (hη : 0 < u.im) :
    paperL1Kernel d N H u ≤
      4 * ((d.L N * d.W N : ℝ)⁻¹ * ∑ y : d.Idx N, (d.L N * d.W N : ℝ)⁻¹ *
        ((∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM hH y.1 α‖) *
          ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2)) := by
  have hL : 3 ≤ d.L N := d.three_le_L N
  have hcard : (Fintype.card (d.Idx N) : ℂ) = ((d.L N * d.W N : ℕ) : ℂ) := by
    simp [Fintype.card_prod, ZMod.card]
  have hN : (0 : ℝ) < (d.L N * d.W N : ℝ) := by
    exact_mod_cast Nat.mul_pos (NeZero.pos (d.L N)) (NeZero.pos (d.W N))
  set B : ℝ := (d.L N * d.W N : ℝ)⁻¹ * ∑ y : d.Idx N, (d.L N * d.W N : ℝ)⁻¹ *
        ((∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM hH y.1 α‖) *
          ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2) with hB
  have hterm : ∀ σ τ : Bool,
      ‖(Fintype.card (d.Idx N) : ℂ)⁻¹ *
        ∑ a : d.Idx N, ∑ b : d.Idx N,
          ((signedGreen H u σ * signedGreen H u σ) a a) *
            (centeredVarianceEntry d N a b : ℂ) * (signedGreen H u τ) b b‖ ≤ B := by
    intro σ τ
    have hsg : ∀ ς : Bool, signedGreen H u ς = Gsig H u ς := by
      intro ς; cases ς <;> rfl
    have hcv : ∀ a b : d.Idx N, (centeredVarianceEntry d N a b : ℂ) =
        Svar (d.L N) (d.W N) a b - ((d.L N * d.W N : ℕ) : ℂ)⁻¹ := by
      intro a b
      rw [centeredVarianceEntry, Svar_eq_ofReal]
      push_cast
      rw [hcard]
      push_cast
      ring
    rw [hcard, norm_mul, norm_inv, Complex.norm_natCast, Finset.sum_comm]
    push_cast
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
    refine Finset.sum_le_sum fun y _ => ?_
    obtain ⟨a0, β⟩ := y
    have h := norm_green_spectral_identity_blockM_le hH hL a0 β u hη σ τ
    simp only [spectralGsigPole_norm_eq_spectralPole, Complex.normSq_eq_norm_sq] at h
    have heq : (∑ x : d.Idx N, (signedGreen H u σ * signedGreen H u σ) x x *
        (centeredVarianceEntry d N x (a0, β) : ℂ) * signedGreen H u τ (a0, β) (a0, β)) =
        ∑ x : ZMod (d.L N) × Fin (d.W N), (Gsig H u σ ^ 2) x x *
          (Svar (d.L N) (d.W N) x (a0, β) - ((d.L N * d.W N : ℕ) : ℂ)⁻¹) *
          Gsig H u τ (a0, β) (a0, β) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hsg, hsg, hcv, pow_two]
    rw [heq]
    refine h.trans (le_of_eq ?_)
    ring
  unfold paperL1Kernel
  calc _ ≤ ∑ _σ : Bool, ∑ _τ : Bool, B :=
        Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => hterm σ τ
    _ = 4 * B := by simp; ring

/-- Nonnegativity of `L₁`. -/
private theorem paperL1Kernel_nonneg (d : Gauss.Dims) (N : ℕ) (H : Matrix (d.Idx N) (d.Idx N) ℂ)
    (u : ℂ) : 0 ≤ paperL1Kernel d N H u := by
  unfold paperL1Kernel
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem s3_card_idx (d : Gauss.Dims) (N : ℕ) :
    (Fintype.card (d.Idx N) : ℝ) = (d.L N * d.W N : ℝ) := by
  simp [Fintype.card_prod, ZMod.card]

open Step3KernelBounds in
/-- **Pointwise bound on the good event.** On the single-scale grid event, with the window
bound `θ` off the blocks `a₀` flagged `Bad`, the weighted kernel is bounded by the product of the
`Im m` rows, times `4 N⁻² ∑_y (α₁ + 1_{Bad} α₂) Q̄`. -/
private theorem s3_pointwise_good (d : Gauss.Dims) (N : ℕ)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) {ηt Cb w' θ α₁ α₂ Qb : ℝ} (hηu : 0 < u.im) (hηu' : u.im ≤ ηt)
    (hηw : ∀ j, 0 < (w j).im) (hηw' : ∀ j, (w j).im ≤ ηt) (hCb : 0 ≤ Cb) (hw' : 0 < w')
    (hθ : 0 ≤ θ) (K K' : ℕ)
    (hG1 : ∀ k ≤ K, GridGood H ηt Cb u.re (2 ^ k * ηt))
    (hG2 : ∀ k ≤ K', GridGood H ηt Cb u.re (2 ^ k * w'))
    (hG3 : GridGood H ηt Cb u.re 0)
    (hG4 : ∀ j, GridGood H ηt Cb (w j).re 0)
    (Bad : ZMod (d.L N) → Prop) [DecidablePred Bad]
    (hBad : ∀ a0, ¬ Bad a0 → ∀ α, |hH.eigenvalues α - u.re| ≤ w' → ‖blockM hH a0 α‖ ≤ θ)
    (hα₁ : θ * (ηt / u.im ^ 2 * ((d.L N * d.W N : ℝ) * Cb)) +
        4 * (d.L N * d.W N : ℝ) * ηt * Cb *
          (2 * (d.L N * d.W N : ℝ) * Cb * (4 / w' + 4 * ηt / w' ^ 2)) +
        ((2 ^ K' * w') ^ 2)⁻¹ * (2 * (d.L N * d.W N : ℝ)) ≤ α₁)
    (hα₂ : 4 * (d.L N * d.W N : ℝ) * ηt * Cb *
        (ηt / u.im ^ 2 * ((d.L N * d.W N : ℝ) * Cb)) ≤ α₂)
    (hQb : 6 * (ηt / u.im) * Cb + 8 * K * Cb + (2 ^ K * ηt)⁻¹ ≤ Qb) :
    (∏ j ∈ s, (stieltjes H (w j)).im) * paperL1Kernel d N H u ≤
      (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        (4 * ((d.L N * d.W N : ℝ)⁻¹ * ∑ y : d.Idx N, (d.L N * d.W N : ℝ)⁻¹ *
          ((α₁ + (if Bad y.1 then α₂ else 0)) * Qb))) := by
  have hL : 3 ≤ d.L N := d.three_le_L N
  have hηt : 0 < ηt := lt_of_lt_of_le hηu hηu'
  have hN : (0 : ℝ) < (d.L N * d.W N : ℝ) := by
    exact_mod_cast Nat.mul_pos (NeZero.pos (d.L N)) (NeZero.pos (d.W N))
  -- the `Im m` rows
  have hP : (∏ j ∈ s, (stieltjes H (w j)).im) ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) := by
    refine Finset.prod_le_prod₀ (fun j _ => (stieltjes_im_nonneg_le hH (hηw j)).1)
      fun j _ => stieltjes_im_le_of_grid hH (hηw j) (hηw' j) (hG4 j)
  have hP0 : 0 ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) :=
    Finset.prod_nonneg fun j _ => mul_nonneg (div_nonneg hηt.le (hηw j).le) hCb
  -- the `A_y` rows
  have hA : ∀ y : d.Idx N, ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM hH y.1 α‖ ≤
      α₁ + (if Bad y.1 then α₂ else 0) := by
    intro y
    have hRd : (2 : ℝ) ^ K' * w' ≤ 2 ^ K' * w' := le_rfl
    have hGd := hG2 K' le_rfl
    by_cases hb : Bad y.1
    · simp only [hb, ite_true]
      have hwin : ∀ α, |hH.eigenvalues α - u.re| ≤ w' →
          ‖blockM hH y.1 α‖ ≤ 4 * (d.L N * d.W N : ℝ) * ηt * Cb := by
        intro α hα
        have h1 : w' ≤ 2 ^ K' * w' := le_mul_of_one_le_left hw'.le (one_le_pow₀ (by norm_num))
        exact norm_blockM_le_of_grid hH hL y.1 hηt hGd (hα.trans h1)
      have h := sum_pole_sq_blockM_le hH hL y.1 hηu hηu' hCb hw' (by positivity) K' hRd hGd hG2
        hG3 hwin
      have hX : 0 ≤ θ * (ηt / u.im ^ 2 * ((d.L N * d.W N : ℝ) * Cb)) := by positivity
      linarith
    · simp only [hb, ite_false, add_zero]
      have h := sum_pole_sq_blockM_le hH hL y.1 hηu hηu' hCb hw' hθ K' hRd hGd hG2 hG3
        (hBad y.1 hb)
      linarith
  have hQ : ∀ y : d.Idx N, ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2 ≤ Qb :=
    fun y => (sum_pole_mass_le hH hηu hηu' hCb K hG1 y).trans hQb
  have hK := paperL1Kernel_le_spectral d N hH hηu
  have hK' : paperL1Kernel d N H u ≤
      4 * ((d.L N * d.W N : ℝ)⁻¹ * ∑ y : d.Idx N, (d.L N * d.W N : ℝ)⁻¹ *
        ((α₁ + (if Bad y.1 then α₂ else 0)) * Qb)) := by
    refine hK.trans ?_
    have hα₁0 : 0 ≤ α₁ := le_trans (by positivity) hα₁
    have hα₂0 : 0 ≤ α₂ := le_trans (by positivity) hα₂
    have hAy0 : ∀ y : d.Idx N, 0 ≤ α₁ + (if Bad y.1 then α₂ else 0) := fun y =>
      add_nonneg hα₁0 (by split_ifs <;> linarith)
    gcongr with y
    all_goals first | exact hA y | exact hQ y
  calc (∏ j ∈ s, (stieltjes H (w j)).im) * paperL1Kernel d N H u
      ≤ (∏ j ∈ s, (ηt / (w j).im * Cb)) * paperL1Kernel d N H u :=
        mul_le_mul_of_nonneg_right hP (paperL1Kernel_nonneg d N H u)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK' hP0

/-- **Crude pointwise bound**, valid for every sample: `∏ Im m(w_j) · L₁(u) ≤
∏ (Im w_j)⁻¹ · 8 (Im u)⁻³`. -/
private theorem s3_pointwise_crude (d : Gauss.Dims) (N : ℕ)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) (hηu : 0 < u.im) (hηw : ∀ j, 0 < (w j).im) :
    (∏ j ∈ s, (stieltjes H (w j)).im) * paperL1Kernel d N H u ≤
      (∏ j ∈ s, (w j).im⁻¹) * (8 * (u.im⁻¹) ^ 3) := by
  have hL : 3 ≤ d.L N := d.three_le_L N
  have hN : (0 : ℝ) < (d.L N * d.W N : ℝ) := by
    exact_mod_cast Nat.mul_pos (NeZero.pos (d.L N)) (NeZero.pos (d.W N))
  have hP : (∏ j ∈ s, (stieltjes H (w j)).im) ≤ ∏ j ∈ s, (w j).im⁻¹ :=
    Finset.prod_le_prod₀ (fun j _ => (stieltjes_im_nonneg_le hH (hηw j)).1)
      fun j _ => (stieltjes_im_nonneg_le hH (hηw j)).2
  have hP0 : 0 ≤ ∏ j ∈ s, (w j).im⁻¹ := Finset.prod_nonneg fun j _ => (inv_pos.2 (hηw j)).le
  have hK := paperL1Kernel_le_spectral d N hH hηu
  have hK' : paperL1Kernel d N H u ≤ 8 * (u.im⁻¹) ^ 3 := by
    refine hK.trans ?_
    calc 4 * ((d.L N * d.W N : ℝ)⁻¹ * ∑ y : d.Idx N, (d.L N * d.W N : ℝ)⁻¹ *
          ((∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM hH y.1 α‖) *
            ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2))
        ≤ 4 * ((d.L N * d.W N : ℝ)⁻¹ * ∑ _y : d.Idx N, (d.L N * d.W N : ℝ)⁻¹ *
          (((u.im ^ 2)⁻¹ * (2 * (d.L N * d.W N : ℝ))) * u.im⁻¹)) := by
          gcongr with y
          all_goals first | exact sum_pole_sq_blockM_le_crude hH hL y.1 hηu |
            exact sum_pole_mass_le_crude hH hηu y
      _ = 8 * (u.im⁻¹) ^ 3 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, s3_card_idx]
          have hW : (d.W N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.pos (d.W N)).ne'
          have hL' : (d.L N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.pos (d.L N)).ne'
          field_simp
          ring
  calc _ ≤ (∏ j ∈ s, (w j).im⁻¹) * paperL1Kernel d N H u :=
        mul_le_mul_of_nonneg_right hP (paperL1Kernel_nonneg d N H u)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK' hP0

end RBM

/-! ### Probabilistic inputs on the common carrier -/

namespace RBM.Gauss

open RBM RBM.Step3KernelBounds

/-- The spectral window (2.22) at energy `E`: `|Re z - E| ≤ C₀/N`,
`N^{-1-τ_U} ≤ Im z ≤ N^{-1+τ_U}`, with `N = L W` the matrix size. -/
def InWindow222 (d : Dims) (E C₀ τU : ℝ) (N : ℕ) (z : ℂ) : Prop :=
  |z.re - E| ≤ C₀ / ((ouCommonBand d).size N : ℝ) ∧
    ((ouCommonBand d).size N : ℝ) ^ (-1 - τU) ≤ z.im ∧ z.im ≤ ((ouCommonBand d).size N : ℝ) ^ (-1 + τU)

private theorem s3_measurable_green (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ) (x y : d.Idx N) :
    Measurable fun ω => green ((ouCommonFlow d).Ht N t ω) z x y := by
  have hH := ouCommonFlow_measurable d N t
  have hM : Measurable fun ω => (ouCommonFlow d).Ht N t ω -
      z • (1 : Matrix ((ouCommonBand d).Idx N) ((ouCommonBand d).Idx N) ℂ) :=
    Measurable.of_eval_matrix _ fun a b => by
      simp only [Matrix.sub_apply]
      exact hH.eval_matrix.sub measurable_const
  exact Gauss.measurable_matrix_inv_apply hM x y

private theorem s3_norm_green_le {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (x : n) : ‖green H z x x‖ ≤ z.im⁻¹ := by
  have hne : ∀ l, (hH.eigenvalues l : ℂ) ≠ z := by
    intro l h
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [green_apply_self hH hne]
  calc _ ≤ ∑ l, ‖(Complex.normSq (hH.eigenvectorBasis l x) : ℂ) /
        ((hH.eigenvalues l : ℂ) - z)‖ := norm_sum_le _ _
    _ ≤ ∑ l, ‖hH.eigenvectorBasis l x‖ ^ 2 * z.im⁻¹ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, div_eq_mul_inv,
          ← norm_inv]
        have := pole_norm_le_inv_im' hH hz l
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = z.im⁻¹ := by rw [← Finset.sum_mul, sum_sq_norm_eigenvectorBasis hH x, one_mul]

/-- Markov for one resolvent entry: a `2p`-th moment bound `M` gives
`P(Im G_xx(z) > Cb) ≤ M / Cb^{2p}`. -/
private theorem s3_prob_im_green_gt (d : Dims) (N : ℕ) (t : ℝ) {z : ℂ} (hz : 0 < z.im)
    (x : d.Idx N) (p : ℕ) {Cb M : ℝ} (hCb : 0 < Cb)
    (hM : ∫ ω, ‖green ((ouCommonFlow d).Ht N t ω) z x x‖ ^ (2 * p) ∂(ouCommonMeasure d) ≤ M) :
    (ouCommonMeasure d).real {ω | Cb < (green ((ouCommonFlow d).Ht N t ω) z x x).im} ≤
      M / Cb ^ (2 * p) := by
  set f : ouCommonOmega d → ℝ := fun ω => ‖green ((ouCommonFlow d).Ht N t ω) z x x‖ ^ (2 * p)
  have hfm : Measurable f := ((s3_measurable_green d N t z x x).norm).pow_const _
  have hfi : Integrable f (ouCommonMeasure d) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable ((z.im⁻¹) ^ (2 * p)) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (s3_norm_green_le ((ouCommonFlow d).hermitian N t ω) hz x) _
  have hsub : {ω | Cb < (green ((ouCommonFlow d).Ht N t ω) z x x).im} ⊆
      {ω | Cb ^ (2 * p) ≤ f ω} := by
    intro ω hω
    exact pow_le_pow_left₀ hCb.le (hω.le.trans (Complex.im_le_norm _)) _
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => by positivity) hfi (Cb ^ (2 * p))
  have hpos : 0 < Cb ^ (2 * p) := by positivity
  calc _ ≤ (ouCommonMeasure d).real {ω | Cb ^ (2 * p) ≤ f ω} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ M / Cb ^ (2 * p) := by
        rw [le_div_iff₀ hpos, mul_comm]
        exact hmk.trans hM

/-- Union bound over one covering grid and all sites. -/
private theorem s3_prob_not_gridGood (d : Dims) (N : ℕ) (t : ℝ) {ηt Cb E₀ r M : ℝ}
    (hηt : 0 < ηt) (hCb : 0 < Cb) (p : ℕ)
    (hM : ∀ j ∈ Finset.range (⌈r / ηt⌉₊ + 1), ∀ x : d.Idx N,
      ∫ ω, ‖green ((ouCommonFlow d).Ht N t ω)
          (((E₀ - r + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) x x‖ ^ (2 * p)
        ∂(ouCommonMeasure d) ≤ M) :
    (ouCommonMeasure d).real {ω | ¬ GridGood ((ouCommonFlow d).Ht N t ω) ηt Cb E₀ r} ≤
      ((⌈r / ηt⌉₊ + 1 : ℕ) : ℝ) * ((Fintype.card (d.Idx N) : ℝ) * (M / Cb ^ (2 * p))) := by
  have hsub : {ω | ¬ GridGood ((ouCommonFlow d).Ht N t ω) ηt Cb E₀ r} ⊆
      ⋃ j ∈ Finset.range (⌈r / ηt⌉₊ + 1), ⋃ x : d.Idx N,
        {ω | Cb < (green ((ouCommonFlow d).Ht N t ω)
          (((E₀ - r + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) x x).im} := by
    intro ω hω
    simp only [GridGood, not_forall, not_le, Set.mem_ofPred_eq] at hω
    obtain ⟨j, hj, x, hx⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨j, hj, x, hx⟩
  have hz : ∀ j : ℕ, 0 < ((((E₀ - r + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I)).im := by
    intro j; simpa using hηt
  calc _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range (⌈r / ηt⌉₊ + 1), (ouCommonMeasure d).real (⋃ x : d.Idx N,
        {ω | Cb < (green ((ouCommonFlow d).Ht N t ω)
          (((E₀ - r + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) x x).im}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (⌈r / ηt⌉₊ + 1), ∑ x : d.Idx N, (ouCommonMeasure d).real
        {ω | Cb < (green ((ouCommonFlow d).Ht N t ω)
          (((E₀ - r + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) x x).im} :=
        Finset.sum_le_sum fun j _ => measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j ∈ Finset.range (⌈r / ηt⌉₊ + 1), ∑ _x : d.Idx N, M / Cb ^ (2 * p) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun x _ =>
          s3_prob_im_green_gt d N t (hz j) x p hCb (hM j hj x)
    _ = _ := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-- Union bound over a finite family `S` of covering grids `(centre, radius)`. -/
private theorem s3_prob_not_gridGood_finset (d : Dims) (N : ℕ) (t : ℝ) {ηt Cb M : ℝ}
    (hηt : 0 < ηt) (hCb : 0 < Cb) (p : ℕ) (S : Finset (ℝ × ℝ)) (G : ℕ)
    (hG : ∀ q ∈ S, ⌈q.2 / ηt⌉₊ + 1 ≤ G) (hM0 : 0 ≤ M)
    (hM : ∀ q ∈ S, ∀ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), ∀ x : d.Idx N,
      ∫ ω, ‖green ((ouCommonFlow d).Ht N t ω)
          (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) x x‖ ^ (2 * p)
        ∂(ouCommonMeasure d) ≤ M) :
    (ouCommonMeasure d).real
        {ω | ¬ ∀ q ∈ S, GridGood ((ouCommonFlow d).Ht N t ω) ηt Cb q.1 q.2} ≤
      (S.card : ℝ) * ((G : ℝ) * ((Fintype.card (d.Idx N) : ℝ) * (M / Cb ^ (2 * p)))) := by
  have hsub : {ω | ¬ ∀ q ∈ S, GridGood ((ouCommonFlow d).Ht N t ω) ηt Cb q.1 q.2} ⊆
      ⋃ q ∈ S, {ω | ¬ GridGood ((ouCommonFlow d).Ht N t ω) ηt Cb q.1 q.2} := by
    intro ω hω
    simp only [not_forall, Set.mem_ofPred_eq] at hω
    obtain ⟨q, hq, hn⟩ := hω
    exact Set.mem_biUnion hq hn
  have hC : 0 ≤ (Fintype.card (d.Idx N) : ℝ) * (M / Cb ^ (2 * p)) := by positivity
  calc _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ q ∈ S, (ouCommonMeasure d).real
        {ω | ¬ GridGood ((ouCommonFlow d).Ht N t ω) ηt Cb q.1 q.2} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ S, (G : ℝ) * ((Fintype.card (d.Idx N) : ℝ) * (M / Cb ^ (2 * p))) := by
        refine Finset.sum_le_sum fun q hq => ?_
        refine (s3_prob_not_gridGood d N t hηt hCb p (hM q hq)).trans ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hG q hq) hC
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The bad event `B_{a₀}` of (2.29), uniformly in `t ∈ (0, t_U]`, from `FlowEq747`
(`measure_bad_flow_of_eq747` along every time sequence, then uniformization). -/
private theorem s3_bad_uniform (d : Dims) {κ τU : ℝ} (hκ : 0 < κ) (hτc : τU < d.c / 3)
    (hQUE : FlowEq747 d κ τU) (E : ℝ) (hE : |E| ≤ 2 - κ) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Ioc (0 : ℝ) ((ouCommonBand d).tPow τU N),
      ∀ a0 : ZMod ((ouCommonBand d).L N),
        (ouCommonBand d).P {ω | ∃ α, |((ouCommonFlow d).hermitian N t ω).eigenvalues α - E| ≤
            ((ouCommonBand d).size N : ℝ) ^ (-1 + (ouCommonBand d).c / 6) ∧
          ((ouCommonBand d).size N : ℝ) ^ (-((ouCommonBand d).c / 36)) ≤
            ‖blockM ((ouCommonFlow d).hermitian N t ω) a0 α‖} ≤
        ENNReal.ofReal (3 * ((ouCommonBand d).size N : ℝ) ^ (-((ouCommonBand d).c / 18))) := by
  set B := ouCommonBand d with hB
  have hc : 0 < B.c := B.c_pos
  have hT : ∀ N, (Set.Ioc (0 : ℝ) (B.tPow τU N)).Nonempty := fun N =>
    ⟨B.tPow τU N, Real.rpow_pos_of_pos (by exact_mod_cast B.one_le_size N) _, le_rfl⟩
  have hsize : Tendsto (fun N => (B.size N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp B.tendsto_size
  have hpos : (0 : ℝ) < B.c / 3 - τU := by
    have : B.c = d.c := rfl
    rw [this]; linarith
  have hev1 : ∀ᶠ N : ℕ in atTop, (16 : ℝ) ≤ (B.size N : ℝ) ^ (B.c / 3 - τU) :=
    ((tendsto_rpow_atTop hpos).comp hsize).eventually (eventually_ge_atTop 16)
  have hev2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (B.size N : ℝ) := hsize.eventually_ge_atTop 2
  refine eventually_forall_mem_of_forall_seq hT fun sq hsq => ?_
  have h747 := hQUE E hE sq fun N => ⟨(hsq N).1, (hsq N).2⟩
  have hζ : ∀ᶠ N : ℕ in atTop, 0 < ouZeta (sq N) ∧ ouZeta (sq N) ≤ 1 / 2 ∧
      ouZeta (sq N) ≤ B.queEtaN (B.c / 3) N / 16 := by
    filter_upwards [hev1, hev2, B.eventually_size_rpow_le_W_sq] with N h16 h2 hWc
    have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by linarith
    have hn0 : (0 : ℝ) < (B.size N : ℝ) := by linarith
    have ht0 : 0 < sq N := (hsq N).1
    have htU : sq N ≤ (B.size N : ℝ) ^ (-1 + τU) := (hsq N).2
    have hζt : ouZeta (sq N) ≤ sq N := by
      unfold ouZeta; linarith [Real.add_one_le_exp (-sq N)]
    have hζ0 : 0 < ouZeta (sq N) := by
      unfold ouZeta; linarith [Real.exp_lt_one_iff.2 (by linarith : -sq N < 0)]
    have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    have hq := rpow_le_queEta (τ := B.c / 3) hn1 hW0 hWc
    have hsplit : (B.size N : ℝ) ^ (-1 - B.c / 3 + 2 * B.c / 3) =
        (B.size N : ℝ) ^ (-1 + τU) * (B.size N : ℝ) ^ (B.c / 3 - τU) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    have hq' : 16 * (B.size N : ℝ) ^ (-1 + τU) ≤ B.queEtaN (B.c / 3) N := by
      refine le_trans ?_ hq
      rw [hsplit]
      have := Real.rpow_pos_of_pos hn0 (-1 + τU)
      nlinarith
    have hhalf : (B.size N : ℝ) ^ (-1 + τU) ≤ 1 / 2 := by
      have h1 : (B.size N : ℝ) ^ (-1 + τU) * 16 ≤ (B.size N : ℝ) ^ (-1 + τU) *
          (B.size N : ℝ) ^ (B.c / 3 - τU) :=
        mul_le_mul_of_nonneg_left h16 (by positivity)
      rw [← Real.rpow_add hn0] at h1
      have h2' : (B.size N : ℝ) ^ (-1 + τU + (B.c / 3 - τU)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hn1 (by
          have : B.c < 3 / 2 := by
            -- `B.c / 3 - τU > 0` and the exponent `-1 + c/3` is nonpositive once `c ≤ 3`
            by_contra hcon
            push Not at hcon
            have hWle : (B.W N : ℝ) ≤ B.size N := by
              have : B.W N ≤ B.size N := by
                unfold Band.size; exact Nat.le_mul_of_pos_left _ (by have := B.three_le_L N; omega)
              exact_mod_cast this
            have h3 : (B.size N : ℝ) ^ (1 + 2 * B.c) ≤ (B.size N : ℝ) ^ (2 : ℝ) := by
              rw [Real.rpow_two]; exact hWc.trans (pow_le_pow_left₀ hW0.le hWle 2)
            have h4 := (Real.rpow_le_rpow_left_iff (by linarith : (1 : ℝ) < B.size N)).1 h3
            linarith
          linarith)
      linarith
    exact ⟨hζ0, by linarith, by linarith⟩
  exact measure_bad_flow_of_eq747 (ouCommonFlow d) hκ sq (fun _ => E) (fun _ => hE)
    (fun N => ouZeta (sq N)) hζ h747


/-! ### Exponent bookkeeping (§2.2 rows), pure real arithmetic -/

private theorem s3_exists_dyadic {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ K : ℕ, 2 ^ K * a ≤ b ∧ b < 2 ^ (K + 1) * a := by
  classical
  have hex : ∃ K : ℕ, b < 2 ^ (K + 1) * a := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b / a) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ ha] at hn
    have : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
    nlinarith
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | k
  · simpa using hab
  · have hk : k < Nat.find hex := by omega
    have := Nat.find_min hex hk
    push Not at this
    exact this

/-- `c < 1/2` follows from (2.2) (`W² ≥ N^{1+2c}`, `N = LW`, `L ≥ 3`). -/
private theorem s3_c_lt_half (d : Dims) : d.c < 1 / 2 := by
  obtain ⟨N, hN⟩ := (ouCommonBand d).eventually_size_rpow_le_W_sq.exists
  have hc : (ouCommonBand d).c = d.c := rfl
  rw [hc] at hN
  by_contra hcon
  push Not at hcon
  set n : ℝ := ((ouCommonBand d).size N : ℝ)
  have hW0 : (0 : ℝ) < (ouCommonBand d).W N := by exact_mod_cast (ouCommonBand d).W_pos N
  have h3W : 3 * ((ouCommonBand d).W N : ℝ) ≤ n := by
    have : 3 * (ouCommonBand d).W N ≤ (ouCommonBand d).size N := by
      unfold Band.size
      exact Nat.mul_le_mul_right _ ((ouCommonBand d).three_le_L N)
    have h := (Nat.cast_le (α := ℝ)).2 this
    push_cast at h
    exact h
  have hW1 : (1 : ℝ) ≤ (ouCommonBand d).W N := by exact_mod_cast (ouCommonBand d).W_pos N
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have h2 : n ^ (2 : ℝ) ≤ n ^ (1 + 2 * d.c) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  rw [Real.rpow_two] at h2
  nlinarith

private theorem s3_rpow_mul {X : ℝ} (hX : 0 < X) (a b : ℝ) : X ^ a * X ^ b = X ^ (a + b) :=
  (Real.rpow_add hX a b).symm

/-- The `Q_y` row: `Q̄ = 6(η̃/η)N^δ + 8K N^δ + (2^K η̃)⁻¹ ≤ (6 + 16/τ + 8/κ) N^{3τ+δ}`. -/
private theorem s3_Qb_le {X τ δ κ η ηt : ℝ} {K : ℕ} (hX : 1 ≤ X) (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hηt : ηt = X ^ (-1 + 2 * τ)) (hη : X ^ (-1 - τ) ≤ η)
    (hK1 : 2 ^ K * ηt ≤ κ / 4) (hK2 : κ / 4 < 2 ^ (K + 1) * ηt) :
    6 * (ηt / η) * X ^ δ + 8 * K * X ^ δ + (2 ^ K * ηt)⁻¹ ≤
      (6 + 16 / τ + 8 / κ) * X ^ (3 * τ + δ) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  have h1 : ηt / η ≤ X ^ (3 * τ) := by
    calc ηt / η ≤ ηt / X ^ (-1 - τ) := div_le_div_of_nonneg_left hηt0.le (by positivity) hη
      _ = X ^ (3 * τ) := by rw [hηt, ← Real.rpow_sub hX0]; congr 1; ring
  have h2K : (2 : ℝ) ^ K ≤ X := by
    have hle : (2 : ℝ) ^ K * ηt ≤ 1 := by linarith
    have hinv : (2 : ℝ) ^ K ≤ ηt⁻¹ := by rw [le_inv_comm₀ (by positivity) hηt0]; rw [inv_eq_one_div, le_div_iff₀ (by positivity)]; linarith
    calc (2 : ℝ) ^ K ≤ ηt⁻¹ := hinv
      _ = X ^ (1 - 2 * τ) := by rw [hηt, ← Real.rpow_neg hX0.le]; congr 1; ring
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
      _ = X := Real.rpow_one X
  have hK : (K : ℝ) ≤ 2 * X ^ τ / τ := by
    have hlog : (K : ℝ) * Real.log 2 ≤ Real.log X := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2K
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      rw [one_div, Real.log_inv] at h
      linarith
    have hlr := Real.log_le_rpow_div hX0.le hτ
    have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
    have : (K : ℝ) * (1 / 2) ≤ X ^ τ / τ := by nlinarith
    rw [mul_div_assoc]; linarith
  have h3 : (2 ^ K * ηt)⁻¹ ≤ 8 / κ := by
    have : κ / 8 < 2 ^ K * ηt := by rw [pow_succ] at hK2; linarith
    rw [inv_le_comm₀ (by positivity) (by positivity)]
    rw [show (8 / κ)⁻¹ = κ / 8 by field_simp]; exact this.le
  have hA : X ^ (τ + δ) ≤ X ^ (3 * τ + δ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hB : (1 : ℝ) ≤ X ^ (3 * τ + δ) := Real.one_le_rpow hX (by linarith)
  have hδX : 0 < X ^ δ := by positivity
  calc 6 * (ηt / η) * X ^ δ + 8 * K * X ^ δ + (2 ^ K * ηt)⁻¹
      ≤ 6 * X ^ (3 * τ) * X ^ δ + 8 * (2 * X ^ τ / τ) * X ^ δ + 8 / κ := by
        gcongr
    _ = 6 * X ^ (3 * τ + δ) + 16 / τ * X ^ (τ + δ) + 8 / κ := by
        rw [← s3_rpow_mul hX0, ← s3_rpow_mul hX0]; ring
    _ ≤ 6 * X ^ (3 * τ + δ) + 16 / τ * X ^ (3 * τ + δ) + 8 / κ * X ^ (3 * τ + δ) := by
        gcongr
        · exact le_mul_of_one_le_right (by positivity) hB
    _ = _ := by ring

/-- The window/bulk/outside rows of `A_y` off the bad event:
`α₁ ≤ (193 + 128/κ²) N^{2 - c/36 + 4τ + 2δ}`. -/
private theorem s3_alpha1_le {X c τ δ κ η ηt w' θ : ℝ} {K' : ℕ} (hX : 1 ≤ X) (hc : 0 < c)
    (hc2 : c < 1 / 2) (hτ : 0 < τ) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hηt : ηt = X ^ (-1 + 2 * τ)) (hη : X ^ (-1 - τ) ≤ η) (hw' : w' = (2 * X ^ (1 - c / 6))⁻¹)
    (hθ : θ = X ^ (-(c / 36))) (hK2 : κ / 4 < 2 ^ (K' + 1) * w') :
    θ * (ηt / η ^ 2 * (X * X ^ δ)) +
        4 * X * ηt * X ^ δ * (2 * X * X ^ δ * (4 / w' + 4 * ηt / w' ^ 2)) +
        ((2 ^ K' * w') ^ 2)⁻¹ * (2 * X) ≤
      (193 + 128 / κ ^ 2) * X ^ (2 - c / 36 + 4 * τ + 2 * δ) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  set E₁ : ℝ := 2 - c / 36 + 4 * τ + 2 * δ with hE₁
  have hw0 : 0 < w' := by rw [hw']; positivity
  have hq : ηt / η ^ 2 ≤ X ^ (1 + 4 * τ) := by
    have hsq : X ^ (-1 - τ) * X ^ (-1 - τ) ≤ η ^ 2 := by
      rw [sq]; exact mul_le_mul hη hη (by positivity) hη0.le
    calc ηt / η ^ 2 ≤ ηt / (X ^ (-1 - τ) * X ^ (-1 - τ)) :=
          div_le_div_of_nonneg_left hηt0.le (by positivity) hsq
      _ = X ^ (1 + 4 * τ) := by
          rw [s3_rpow_mul hX0, hηt, ← Real.rpow_sub hX0]; congr 1; ring
  have hwi : 4 / w' = 8 * X ^ (1 - c / 6) := by rw [hw']; field_simp; ring
  have hwi2 : 4 * ηt / w' ^ 2 = 16 * X ^ (1 + 2 * τ - c / 3) := by
    rw [hw', hηt]
    have : X ^ (1 + 2 * τ - c / 3) = X ^ (-1 + 2 * τ) * (X ^ (1 - c / 6) * X ^ (1 - c / 6)) := by
      rw [s3_rpow_mul hX0, s3_rpow_mul hX0]; congr 1; ring
    rw [this]; field_simp; ring
  have ht1 : θ * (ηt / η ^ 2 * (X * X ^ δ)) ≤ X ^ E₁ := by
    calc θ * (ηt / η ^ 2 * (X * X ^ δ)) ≤ X ^ (-(c / 36)) * (X ^ (1 + 4 * τ) * (X ^ (1 : ℝ) * X ^ δ)) := by
          rw [hθ, Real.rpow_one]; gcongr
      _ = X ^ (-(c / 36) + (1 + 4 * τ + (1 + δ))) := by
          rw [s3_rpow_mul hX0, s3_rpow_mul hX0, s3_rpow_mul hX0]
      _ ≤ X ^ E₁ := Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
  have ht2 : 4 * X * ηt * X ^ δ * (2 * X * X ^ δ * (4 / w' + 4 * ηt / w' ^ 2)) ≤ 192 * X ^ E₁ := by
    rw [hwi, hwi2]
    have e1 : 4 * X * ηt * X ^ δ * (2 * X * X ^ δ * (8 * X ^ (1 - c / 6) +
        16 * X ^ (1 + 2 * τ - c / 3))) =
        64 * X ^ ((1 : ℝ) + (-1 + 2 * τ) + δ + 1 + δ + (1 - c / 6)) +
          128 * X ^ ((1 : ℝ) + (-1 + 2 * τ) + δ + 1 + δ + (1 + 2 * τ - c / 3)) := by
      simp only [← s3_rpow_mul hX0, Real.rpow_one, hηt]; ring
    rw [e1]
    have f1 : X ^ ((1 : ℝ) + (-1 + 2 * τ) + δ + 1 + δ + (1 - c / 6)) ≤ X ^ E₁ :=
      Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
    have f2 : X ^ ((1 : ℝ) + (-1 + 2 * τ) + δ + 1 + δ + (1 + 2 * τ - c / 3)) ≤ X ^ E₁ :=
      Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
    linarith
  have ht3 : ((2 ^ K' * w') ^ 2)⁻¹ * (2 * X) ≤ 128 / κ ^ 2 * X ^ E₁ := by
    have hb : κ / 8 < 2 ^ K' * w' := by rw [pow_succ] at hK2; linarith
    have hb2 : ((2 ^ K' * w') ^ 2)⁻¹ ≤ 64 / κ ^ 2 := by
      rw [inv_le_comm₀ (by positivity) (by positivity)]
      rw [show (64 / κ ^ 2)⁻¹ = (κ / 8) ^ 2 by field_simp; norm_num]
      exact pow_le_pow_left₀ (by positivity) hb.le 2
    have hXE : X ≤ X ^ E₁ := by
      calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
        _ ≤ X ^ E₁ := Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
    calc ((2 ^ K' * w') ^ 2)⁻¹ * (2 * X) ≤ 64 / κ ^ 2 * (2 * X ^ E₁) := by gcongr
      _ = 128 / κ ^ 2 * X ^ E₁ := by ring
  linarith

/-- The window row on the bad event: `α₂ = 4Nη̃N^δ · (η̃/η²) N N^δ ≤ 4 N^{2+6τ+2δ}`. -/
private theorem s3_alpha2_le {X τ δ η ηt : ℝ} (hX : 1 ≤ X)
    (hηt : ηt = X ^ (-1 + 2 * τ)) (hη : X ^ (-1 - τ) ≤ η) :
    4 * X * ηt * X ^ δ * (ηt / η ^ 2 * (X * X ^ δ)) ≤ 4 * X ^ (2 + 6 * τ + 2 * δ) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  have hq : ηt / η ^ 2 ≤ X ^ (1 + 4 * τ) := by
    have hsq : X ^ (-1 - τ) * X ^ (-1 - τ) ≤ η ^ 2 := by
      rw [sq]; exact mul_le_mul hη hη (by positivity) hη0.le
    calc ηt / η ^ 2 ≤ ηt / (X ^ (-1 - τ) * X ^ (-1 - τ)) :=
          div_le_div_of_nonneg_left hηt0.le (by positivity) hsq
      _ = X ^ (1 + 4 * τ) := by
          rw [s3_rpow_mul hX0, hηt, ← Real.rpow_sub hX0]; congr 1; ring
  calc 4 * X * ηt * X ^ δ * (ηt / η ^ 2 * (X * X ^ δ))
      ≤ 4 * X * ηt * X ^ δ * (X ^ (1 + 4 * τ) * (X * X ^ δ)) := by gcongr
    _ = 4 * X ^ ((1 : ℝ) + (-1 + 2 * τ) + δ + ((1 + 4 * τ) + (1 + δ))) := by
        simp only [← s3_rpow_mul hX0, Real.rpow_one, hηt]; ring
    _ = 4 * X ^ (2 + 6 * τ + 2 * δ) := by congr 2; ring


/-- **Assembly of the good part** (rows `Im m_t(w_j)`, `Q_y`, `A_y` off/on `B_y`, `L₁`):
`4 N⁻² P̄ Q̄ · N (α₁ + 3α₂ N^{-c/18}) ≤ ½ N^{1 - c/36 + (3|s|+16)τ}` once
`8 (C₁ + 12) C₂ ≤ N^{6τ}`; here `(|s|+3)δ ≤ τ` is the normalization of `δ`. -/
private theorem s3_good_total_le {X c τ δ C₁ C₂ : ℝ} {sc m : ℕ} (hX : 1 ≤ X) (hc : 0 ≤ c)
    (hτ : 0 < τ) (hδ : 0 ≤ δ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hsc : sc ≤ m)
    (hmδ : ((m : ℝ) + 3) * δ ≤ τ) (hslack : 8 * (C₁ + 12) * C₂ ≤ X ^ (6 * τ)) :
    X ^ ((3 * τ + δ) * sc) * 4 * X⁻¹ * X⁻¹ * (C₂ * X ^ (3 * τ + δ)) *
        (C₁ * X ^ (2 - c / 36 + 4 * τ + 2 * δ)) * X +
      X * (X ^ ((3 * τ + δ) * sc) * 4 * X⁻¹ * X⁻¹ * (C₂ * X ^ (3 * τ + δ)) *
        (4 * X ^ (2 + 6 * τ + 2 * δ)) * (3 * X ^ (-(c / 18)))) ≤
      1 / 2 * X ^ (1 - c / 36 + (3 * (sc : ℝ) + 16) * τ) := by
  have hX0 : 0 < X := by linarith
  set T : ℝ := 1 - c / 36 + (3 * (sc : ℝ) + 16) * τ with hT
  have hsc' : (sc : ℝ) ≤ m := by exact_mod_cast hsc
  set a : ℝ := (3 * τ + δ) * sc
  set b : ℝ := 3 * τ + δ
  set e : ℝ := 2 - c / 36 + 4 * τ + 2 * δ
  set f : ℝ := 2 + 6 * τ + 2 * δ
  set g : ℝ := -(c / 18)
  have r1 : X ^ (a + b + e - 1) = X ^ a * X ^ b * X ^ e / X := by
    rw [Real.rpow_sub hX0, Real.rpow_add hX0 (a + b) e, Real.rpow_add hX0 a b, Real.rpow_one]
  have r2 : X ^ (a + b + f + g - 1) = X ^ a * X ^ b * X ^ f * X ^ g / X := by
    rw [Real.rpow_sub hX0, Real.rpow_add hX0 (a + b + f) g, Real.rpow_add hX0 (a + b) f,
      Real.rpow_add hX0 a b, Real.rpow_one]
  have e1 : X ^ a * 4 * X⁻¹ * X⁻¹ * (C₂ * X ^ b) * (C₁ * X ^ e) * X =
      4 * C₁ * C₂ * X ^ (a + b + e - 1) := by
    rw [r1]
    generalize X ^ a = A
    generalize X ^ b = B
    generalize X ^ e = Ee
    field_simp
  have e2 : X * (X ^ a * 4 * X⁻¹ * X⁻¹ * (C₂ * X ^ b) * (4 * X ^ f) * (3 * X ^ g)) =
      48 * C₂ * X ^ (a + b + f + g - 1) := by
    rw [r2]
    generalize X ^ a = A
    generalize X ^ b = B
    generalize X ^ f = F
    generalize X ^ g = G
    field_simp
    ring
  rw [e1, e2]
  have hsd : (sc + 3 : ℝ) * δ ≤ τ := le_trans (by gcongr) hmδ
  have f1 : X ^ (a + b + e - 1) ≤ X ^ (T - 6 * τ) := by
    refine Real.rpow_le_rpow_of_exponent_le hX ?_
    simp only [a, b, e, hT]
    nlinarith
  have f2 : X ^ (a + b + f + g - 1) ≤ X ^ (T - 6 * τ) := by
    refine Real.rpow_le_rpow_of_exponent_le hX ?_
    simp only [a, b, f, g, hT]
    nlinarith
  have hsplit : X ^ T = X ^ (T - 6 * τ) * X ^ (6 * τ) := by
    rw [s3_rpow_mul hX0]; congr 1; ring
  have hpos : 0 ≤ X ^ (T - 6 * τ) := by positivity
  calc 4 * C₁ * C₂ * X ^ (a + b + e - 1) + 48 * C₂ * X ^ (a + b + f + g - 1)
      ≤ 4 * C₁ * C₂ * X ^ (T - 6 * τ) + 48 * C₂ * X ^ (T - 6 * τ) := by gcongr
    _ = 1 / 2 * (8 * (C₁ + 12) * C₂) * X ^ (T - 6 * τ) := by ring
    _ ≤ 1 / 2 * X ^ (6 * τ) * X ^ (T - 6 * τ) := by gcongr
    _ = 1 / 2 * X ^ T := by rw [hsplit]; ring

/-- **Assembly of the crude part** (row `Ξᶜ`): with `2pδ ≥ (1+τ)m + 7 + 3τ + δ`,
`8N^{(1+τ)(|s|+3)} · P(Ξᶜ) ≤ 16(3+m) N^{-1} ≤ ½ N^{1 - c/36 + (3|s|+16)τ}`. -/
private theorem s3_crude_total_le {X c τ δ : ℝ} {sc m p : ℕ} (hX : 1 ≤ X) (hτ : 0 < τ)
    (hc : c < 36) (hsc : sc ≤ m)
    (hp : (1 + τ) * m + 7 + 3 * τ + δ ≤ 2 * p * δ) (hXm : 32 * (3 + (m : ℝ)) ≤ X) :
    8 * X ^ ((1 + τ) * ((sc : ℝ) + 3)) *
        ((3 + (m : ℝ)) * X * (2 * X * (X * (X ^ δ / (X ^ δ) ^ (2 * p))))) ≤
      1 / 2 * X ^ (1 - c / 36 + (3 * (sc : ℝ) + 16) * τ) := by
  have hX0 : 0 < X := by linarith
  have hsc' : (sc : ℝ) ≤ m := by exact_mod_cast hsc
  have hpow : (X ^ δ) ^ (2 * p) = X ^ (δ * (2 * p : ℕ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
  set a : ℝ := (1 + τ) * ((sc : ℝ) + 3)
  set b : ℝ := δ * (2 * p : ℕ)
  have r : X ^ (a + 1 + 1 + 1 + δ - b) = X ^ a * X * X * X * X ^ δ / X ^ b := by
    rw [Real.rpow_sub hX0, Real.rpow_add hX0 (a + 1 + 1 + 1) δ, Real.rpow_add hX0 (a + 1 + 1) 1,
      Real.rpow_add hX0 (a + 1) 1, Real.rpow_add hX0 a 1, Real.rpow_one]
  have e : 8 * X ^ a * ((3 + (m : ℝ)) * X * (2 * X * (X * (X ^ δ / (X ^ δ) ^ (2 * p))))) =
      16 * (3 + (m : ℝ)) * X ^ (a + 1 + 1 + 1 + δ - b) := by
    rw [hpow, r]
    ring
  rw [e]
  have f : X ^ (a + 1 + 1 + 1 + δ - b) ≤ X ^ (-1 : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le hX ?_
    simp only [a, b]
    push_cast
    nlinarith
  have hT : (1 : ℝ) ≤ X ^ (1 - c / 36 + (3 * (sc : ℝ) + 16) * τ) :=
    Real.one_le_rpow hX (by
      have : (0 : ℝ) ≤ (3 * (sc : ℝ) + 16) * τ := by positivity
      linarith)
  rw [Real.rpow_neg_one] at f
  have h2 : 16 * (3 + (m : ℝ)) * X⁻¹ ≤ 1 / 2 := by
    rw [mul_inv_le_iff₀ hX0]; linarith
  calc 16 * (3 + (m : ℝ)) * X ^ (a + 1 + 1 + 1 + δ - b)
      ≤ 16 * (3 + (m : ℝ)) * X⁻¹ := by gcongr
    _ ≤ 1 / 2 := h2
    _ ≤ _ := by linarith

/-- Row `Im m_t(w_j)`, product form: `∏_{j∈s} (η̃/Im w_j) N^δ ≤ N^{(3τ+δ)|s|}`. -/
private theorem s3_prod_row_le {X τ δ ηt : ℝ} (hX : 1 ≤ X) (hηt : ηt = X ^ (-1 + 2 * τ))
    {m : ℕ} (s : Finset (Fin m)) (w : Fin m → ℂ) (hw : ∀ j, X ^ (-1 - τ) ≤ (w j).im) :
    ∏ j ∈ s, (ηt / (w j).im * X ^ δ) ≤ X ^ ((3 * τ + δ) * (s.card : ℝ)) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hwj : ∀ j, 0 < (w j).im := fun j => lt_of_lt_of_le (by positivity) (hw j)
  calc ∏ j ∈ s, (ηt / (w j).im * X ^ δ) ≤ ∏ _j ∈ s, X ^ (3 * τ + δ) := by
        refine Finset.prod_le_prod₀ (fun j _ => ?_) (fun j _ => ?_)
        · have := hwj j
          positivity
        · have h1 : ηt / (w j).im ≤ X ^ (3 * τ) := by
            calc ηt / (w j).im ≤ ηt / X ^ (-1 - τ) :=
                  div_le_div_of_nonneg_left hηt0.le (by positivity) (hw j)
              _ = X ^ (3 * τ) := by rw [hηt, ← Real.rpow_sub hX0]; congr 1; ring
          calc ηt / (w j).im * X ^ δ ≤ X ^ (3 * τ) * X ^ δ := by gcongr
            _ = X ^ (3 * τ + δ) := (Real.rpow_add hX0 _ _).symm
    _ = X ^ ((3 * τ + δ) * (s.card : ℝ)) := by
        rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]

/-- Row `Ξᶜ`, crude weight: `∏_{j∈s} (Im w_j)⁻¹ · 8 (Im u)⁻³ ≤ 8 N^{(1+τ)(|s|+3)}`. -/
private theorem s3_prod_crude_le {X τ : ℝ} (hX : 1 ≤ X) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) (hw : ∀ j, X ^ (-1 - τ) ≤ (w j).im) (hu : X ^ (-1 - τ) ≤ u.im) :
    (∏ j ∈ s, (w j).im⁻¹) * (8 * (u.im⁻¹) ^ 3) ≤ 8 * X ^ ((1 + τ) * ((s.card : ℝ) + 3)) := by
  have hX0 : 0 < X := by linarith
  have hinv : ∀ {y : ℝ}, X ^ (-1 - τ) ≤ y → y⁻¹ ≤ X ^ (1 + τ) := by
    intro y hy
    calc y⁻¹ ≤ (X ^ (-1 - τ))⁻¹ := inv_anti₀ (by positivity) hy
      _ = X ^ (1 + τ) := by rw [← Real.rpow_neg hX0.le]; congr 1; ring
  have hP : ∏ j ∈ s, (w j).im⁻¹ ≤ X ^ ((1 + τ) * (s.card : ℝ)) := by
    calc _ ≤ ∏ _j ∈ s, X ^ (1 + τ) :=
          Finset.prod_le_prod₀ (fun j _ => inv_nonneg.2 (le_trans (by positivity) (hw j)))
            (fun j _ => hinv (hw j))
      _ = _ := by rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
  have hU : (u.im⁻¹) ^ 3 ≤ X ^ ((1 + τ) * 3) := by
    calc (u.im⁻¹) ^ 3 ≤ (X ^ (1 + τ)) ^ 3 :=
          pow_le_pow_left₀ (inv_nonneg.2 (le_trans (by positivity) hu)) (hinv hu) 3
      _ = X ^ ((1 + τ) * 3) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hP0 : 0 ≤ ∏ j ∈ s, (w j).im⁻¹ :=
    Finset.prod_nonneg fun j _ => inv_nonneg.2 (le_trans (by positivity) (hw j))
  calc _ ≤ X ^ ((1 + τ) * (s.card : ℝ)) * (8 * X ^ ((1 + τ) * 3)) :=
        mul_le_mul hP (by linarith)
          (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.2 (le_trans (by positivity) hu)) 3))
          (by positivity)
    _ = 8 * X ^ ((1 + τ) * ((s.card : ℝ) + 3)) := by
        rw [mul_add, Real.rpow_add hX0]; ring

/-- Grid energies stay in the local-law domain (acceptance (iv)): a centre within `C` of `E`,
a radius `r ≤ κ/4` and `C + 2η̃ < κ/4` give `|E₀ - r + 2η̃j| ≤ 2 - κ/2` for `j ≤ ⌈r/η̃⌉₊`. -/
private theorem s3_grid_energy_le {E E₀ κ C r ηt : ℝ} {j : ℕ} (hηt : 0 < ηt)
    (hE : |E| ≤ 2 - κ) (hE₀ : |E₀ - E| ≤ C) (hr : 0 ≤ r) (hrκ : r ≤ κ / 4)
    (hC : C + 2 * ηt < κ / 4) (hj : j ∈ Finset.range (⌈r / ηt⌉₊ + 1)) :
    |E₀ - r + 2 * ηt * j| ≤ 2 - κ / 2 := by
  have hj' : (j : ℝ) < r / ηt + 1 := by
    have h1 := Finset.mem_range.1 hj
    have h2 : (j : ℝ) ≤ ⌈r / ηt⌉₊ := by exact_mod_cast Nat.lt_succ_iff.1 h1
    linarith [Nat.ceil_lt_add_one (div_nonneg hr hηt.le)]
  have hj2 : 2 * ηt * j < 2 * r + 2 * ηt := by
    have h := mul_lt_mul_of_pos_left hj' (by positivity : (0 : ℝ) < 2 * ηt)
    have he : 2 * ηt * (r / ηt + 1) = 2 * r + 2 * ηt := by field_simp
    linarith
  have hj0 : 0 ≤ 2 * ηt * j := by positivity
  rw [abs_le] at hE hE₀ ⊢
  constructor <;> linarith

/-- Integration of a simple majorant: a nonnegative `f` below
`A₀ + c_B ∑_y 1_{B_y} + C_r 1_T` (measurable `B_y`, `T`) has
`∫ f ≤ A₀ + c_B ∑_y P(B_y) + C_r P(T)`.  No integrability or measurability of `f` is needed. -/
private theorem s3_integral_le_of_majorant {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype ι] {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (Bm : ι → Set Ω)
    (hBm : ∀ y, MeasurableSet (Bm y)) {T : Set Ω} (hT : MeasurableSet T) (A0 cB Cr : ℝ)
    (hfg : ∀ ω, f ω ≤ A0 + cB * ∑ y, (Bm y).indicator 1 ω + Cr * T.indicator 1 ω) :
    ∫ ω, f ω ∂μ ≤ A0 + cB * ∑ y, μ.real (Bm y) + Cr * μ.real T := by
  have hint1 : ∀ A : Set Ω, MeasurableSet A → Integrable (A.indicator (1 : Ω → ℝ)) μ :=
    fun A hA => (integrable_const (1 : ℝ)).indicator hA
  have hS : Integrable (fun ω => ∑ y, (Bm y).indicator (1 : Ω → ℝ) ω) μ :=
    integrable_finsetSum _ fun y _ => hint1 _ (hBm y)
  have hgi : Integrable (fun ω => A0 + cB * ∑ y, (Bm y).indicator (1 : Ω → ℝ) ω +
      Cr * T.indicator 1 ω) μ :=
    ((integrable_const A0).add (hS.const_mul cB)).add ((hint1 T hT).const_mul Cr)
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall hf0) hgi
    (Filter.Eventually.of_forall hfg)).trans (le_of_eq ?_)
  have hI1 : Integrable (fun ω => A0 + cB * ∑ y, (Bm y).indicator (1 : Ω → ℝ) ω) μ :=
    (integrable_const A0).add (hS.const_mul cB)
  have hI2 : Integrable (fun ω => Cr * T.indicator (1 : Ω → ℝ) ω) μ := (hint1 T hT).const_mul Cr
  have hI3 : Integrable (fun ω => cB * ∑ y, (Bm y).indicator (1 : Ω → ℝ) ω) μ := hS.const_mul cB
  rw [integral_add hI1 hI2, integral_add (integrable_const A0) hI3, integral_const,
    integral_const_mul, integral_finsetSum _ fun y _ => hint1 _ (hBm y), integral_const_mul,
    integral_indicator_one hT]
  simp only [probReal_univ, one_smul, integral_indicator_one (hBm _)]

open Step3KernelBounds in
/-- **Good-event pointwise bound, normalized** (rows `Im m_t(w_j)`, `Q_y`, `A_y` off/on `B_y`,
`L₁` of §2.2 with `η̃ = n^{-1+2τ}`, `C_b = n^δ`, `w' = n^{-1+c/6}/2`, `θ = n^{-c/36}`). -/
private theorem s3_pointwise_good_norm (d : Dims) (N : ℕ)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) {n τ δ κ ηt w' θ : ℝ} {K K' : ℕ}
    (hn1 : 1 ≤ n) (hLW : (d.L N : ℝ) * (d.W N : ℝ) = n) (hc2 : d.c < 1 / 2) (hτ : 0 < τ)
    (hδ : 0 ≤ δ) (hκ : 0 < κ) (hκ2 : κ ≤ 2)
    (hηt : ηt = n ^ (-1 + 2 * τ)) (hw' : w' = (2 * n ^ (1 - d.c / 6))⁻¹)
    (hθ : θ = n ^ (-(d.c / 36)))
    (hηu1 : n ^ (-1 - τ) ≤ u.im) (hηu' : u.im ≤ ηt) (hηw1 : ∀ j, n ^ (-1 - τ) ≤ (w j).im)
    (hηw' : ∀ j, (w j).im ≤ ηt)
    (hK1 : 2 ^ K * ηt ≤ κ / 4) (hK2 : κ / 4 < 2 ^ (K + 1) * ηt)
    (hK2' : κ / 4 < 2 ^ (K' + 1) * w')
    (hG1 : ∀ k ≤ K, GridGood H ηt (n ^ δ) u.re (2 ^ k * ηt))
    (hG2 : ∀ k ≤ K', GridGood H ηt (n ^ δ) u.re (2 ^ k * w'))
    (hG3 : GridGood H ηt (n ^ δ) u.re 0)
    (hG4 : ∀ j, GridGood H ηt (n ^ δ) (w j).re 0)
    (Bad : ZMod (d.L N) → Prop) [DecidablePred Bad]
    (hBad : ∀ a0, ¬ Bad a0 → ∀ α, |hH.eigenvalues α - u.re| ≤ w' → ‖blockM hH a0 α‖ ≤ θ) :
    (∏ j ∈ s, (stieltjes H (w j)).im) * paperL1Kernel d N H u ≤
      n ^ ((3 * τ + δ) * (s.card : ℝ)) * 4 * n⁻¹ * n⁻¹ *
          ((6 + 16 / τ + 8 / κ) * n ^ (3 * τ + δ)) *
          ((193 + 128 / κ ^ 2) * n ^ (2 - d.c / 36 + 4 * τ + 2 * δ)) * n +
        n ^ ((3 * τ + δ) * (s.card : ℝ)) * 4 * n⁻¹ * n⁻¹ *
          ((6 + 16 / τ + 8 / κ) * n ^ (3 * τ + δ)) * (4 * n ^ (2 + 6 * τ + 2 * δ)) *
          ∑ y : d.Idx N, (if Bad y.1 then (1 : ℝ) else 0) := by
  have hn0 : 0 < n := by linarith
  have hc : 0 < d.c := d.c_pos
  have hηu : 0 < u.im := lt_of_lt_of_le (by positivity) hηu1
  have hηw : ∀ j, 0 < (w j).im := fun j => lt_of_lt_of_le (by positivity) (hηw1 j)
  have hw'0 : 0 < w' := by rw [hw']; positivity
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hα₁ := s3_alpha1_le (X := n) (c := d.c) (δ := δ) (κ := κ) (K' := K') hn1 hc hc2 hτ
    hδ hκ hηt hηu1 hw' hθ hK2'
  have hα₂ := s3_alpha2_le (X := n) (δ := δ) hn1 hηt hηu1
  have hQb := s3_Qb_le (X := n) (δ := δ) hn1 hτ hδ hκ hκ2 hηt hηu1 hK1 hK2
  have hgood := s3_pointwise_good d N hH s w u hηu hηu' hηw hηw' (by positivity) hw'0 hθ0 K K'
    hG1 hG2 hG3 hG4 Bad hBad (α₁ := (193 + 128 / κ ^ 2) * n ^ (2 - d.c / 36 + 4 * τ + 2 * δ))
    (α₂ := 4 * n ^ (2 + 6 * τ + 2 * δ)) (Qb := (6 + 16 / τ + 8 / κ) * n ^ (3 * τ + δ))
    (by rw [hLW]; exact hα₁) (by rw [hLW]; exact hα₂) hQb
  rw [hLW] at hgood
  refine hgood.trans ?_
  have hcard : (Fintype.card (d.Idx N) : ℝ) = n := by rw [s3_card_idx, hLW]
  generalize hA : (193 + 128 / κ ^ 2) * n ^ (2 - d.c / 36 + 4 * τ + 2 * δ) = α₁
  generalize hB : 4 * n ^ (2 + 6 * τ + 2 * δ) = α₂
  generalize hQ : (6 + 16 / τ + 8 / κ) * n ^ (3 * τ + δ) = Qb
  have hα₁0 : 0 ≤ α₁ := by rw [← hA]; positivity
  have hα₂0 : 0 ≤ α₂ := by rw [← hB]; positivity
  have hQ0 : 0 ≤ Qb := by rw [← hQ]; positivity
  have hsp : ∀ y : d.Idx N, n⁻¹ * ((α₁ + (if Bad y.1 then α₂ else 0)) * Qb) =
      n⁻¹ * α₁ * Qb + n⁻¹ * Qb * α₂ * (if Bad y.1 then (1 : ℝ) else 0) := by
    intro y; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun y _ => hsp y, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard, ← Finset.mul_sum]
  have hP := s3_prod_row_le (δ := δ) hn1 hηt s w hηw1
  have hI : 0 ≤ ∑ y : d.Idx N, (if Bad y.1 then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun y _ => by split_ifs <;> norm_num
  have e : ∀ Pb : ℝ, Pb * (4 * (n⁻¹ * (n * (n⁻¹ * α₁ * Qb) +
      n⁻¹ * Qb * α₂ * ∑ y : d.Idx N, (if Bad y.1 then (1 : ℝ) else 0)))) =
      Pb * (4 * n⁻¹ * n⁻¹ * Qb * α₁ * n +
        4 * n⁻¹ * n⁻¹ * Qb * α₂ * ∑ y : d.Idx N, (if Bad y.1 then (1 : ℝ) else 0)) := by
    intro Pb; ring
  rw [e]
  have hR0 : 0 ≤ 4 * n⁻¹ * n⁻¹ * Qb * α₁ * n +
      4 * n⁻¹ * n⁻¹ * Qb * α₂ * ∑ y : d.Idx N, (if Bad y.1 then (1 : ℝ) else 0) := by
    positivity
  calc _ ≤ n ^ ((3 * τ + δ) * (s.card : ℝ)) * (4 * n⁻¹ * n⁻¹ * Qb * α₁ * n +
        4 * n⁻¹ * n⁻¹ * Qb * α₂ * ∑ y : d.Idx N, (if Bad y.1 then (1 : ℝ) else 0)) :=
        mul_le_mul_of_nonneg_right hP hR0
    _ = _ := by ring

open Step3KernelBounds in
/-- **Fixed-time assembly** of `expect_L1_weighted_le` at one size `N`, one time `t`, and one
choice of `s, w, u`: all eventual conditions are passed as explicit numeric hypotheses. -/
private theorem s3_fixed_time (d : Dims) (N : ℕ) (t : ℝ) {κ τU δ C₀ E n : ℝ} (p m : ℕ)
    (hn : ((ouCommonBand d).size N : ℝ) = n)
    (hκ : 0 < κ) (hτU : 0 < τU) (hδ : 0 < δ) (hc2 : d.c < 1 / 2) (hκ2 : κ ≤ 2)
    (hmδ : ((m : ℝ) + 3) * δ ≤ τU) (hp : (1 + τU) * m + 7 + 3 * τU + δ ≤ 2 * p * δ)
    (hE : |E| ≤ 2 - κ)
    (h1 : 32 * (3 + (m : ℝ)) ≤ n) (h2 : 2 * C₀ ≤ n ^ (d.c / 6))
    (h3 : C₀ / n + 2 * n ^ (-1 + 2 * τU) < κ / 4) (h4 : n ^ (-1 + d.c / 6) < κ / 2)
    (h5 : 8 * ((193 + 128 / κ ^ 2) + 12) * (6 + 16 / τU + 8 / κ) ≤ n ^ (6 * τU))
    (hLLN : ∀ e : ℝ, |e| ≤ 2 - κ / 2 → ∀ x : d.Idx N,
      ∫ ω, ‖green ((ouCommonFlow d).Ht N t ω)
          ((e : ℂ) + ((n ^ (-1 + 2 * τU) : ℝ) : ℂ) * Complex.I) x x‖ ^ (2 * p)
        ∂(ouCommonMeasure d) ≤ n ^ δ)
    (hbadN : ∀ a0 : ZMod (d.L N),
      ouCommonMeasure d {ω | ∃ α, |((ouCommonFlow d).hermitian N t ω).eigenvalues α - E| ≤
          n ^ (-1 + d.c / 6) ∧
        n ^ (-(d.c / 36)) ≤ ‖blockM ((ouCommonFlow d).hermitian N t ω) a0 α‖} ≤
        ENNReal.ofReal (3 * n ^ (-(d.c / 18))))
    (s : Finset (Fin m)) (w : Fin m → ℂ) (u : ℂ)
    (hw : ∀ i, |(w i).re - E| ≤ C₀ / n ∧ n ^ (-1 - τU) ≤ (w i).im ∧
      (w i).im ≤ n ^ (-1 + τU))
    (hu : |u.re - E| ≤ C₀ / n ∧ n ^ (-1 - τU) ≤ u.im ∧ u.im ≤ n ^ (-1 + τU)) :
    ∫ ω, (∏ j ∈ s, (stieltjes ((ouCommonFlow d).Ht N t ω) (w j)).im) *
        paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) u ∂(ouCommonMeasure d) ≤
      n ^ (1 - d.c / 36 + (3 * (s.card : ℝ) + 16) * τU) := by
  classical
  have hc : 0 < d.c := d.c_pos
  have hn1 : 1 ≤ n := by have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith
  have hn0 : 0 < n := by linarith
  have hLW : ((d.L N : ℝ) * (d.W N : ℝ)) = n := by
    rw [← hn]; simp [Band.size, ouCommonBand]
  have hcard : (Fintype.card (d.Idx N) : ℝ) = n := by rw [s3_card_idx, hLW]
  obtain ⟨ηt, hηt⟩ : ∃ ηt : ℝ, ηt = n ^ (-1 + 2 * τU) := ⟨_, rfl⟩
  obtain ⟨w', hw'def⟩ : ∃ w' : ℝ, w' = n ^ (-1 + d.c / 6) / 2 := ⟨_, rfl⟩
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hCb0 : 0 < n ^ δ := by positivity
  have hw'0 : 0 < w' := by rw [hw'def]; positivity
  have hC₀n : 0 ≤ C₀ / n := le_trans (by positivity) hu.1
  have hηtκ : ηt ≤ κ / 4 := by rw [hηt]; linarith
  have hw'κ : w' ≤ κ / 4 := by rw [hw'def]; linarith
  have hw'eq : w' = (2 * n ^ (1 - d.c / 6))⁻¹ := by
    rw [hw'def, mul_inv, show -1 + d.c / 6 = -(1 - d.c / 6) by ring, Real.rpow_neg hn0.le]
    ring
  obtain ⟨K, hK1, hK2⟩ := s3_exists_dyadic hηt0 hηtκ
  obtain ⟨K', hK1', hK2'⟩ := s3_exists_dyadic hw'0 hw'κ
  have hure : |u.re - E| ≤ C₀ / n := hu.1
  have hηu1 : n ^ (-1 - τU) ≤ u.im := hu.2.1
  have hηu : 0 < u.im := lt_of_lt_of_le (by positivity) hηu1
  have hle_ηt : ∀ {y : ℝ}, y ≤ n ^ (-1 + τU) → y ≤ ηt := fun hy =>
    hy.trans (by rw [hηt]; exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hηu' : u.im ≤ ηt := hle_ηt hu.2.2
  have hηw1 : ∀ j, n ^ (-1 - τU) ≤ (w j).im := fun j => (hw j).2.1
  have hηw : ∀ j, 0 < (w j).im := fun j => lt_of_lt_of_le (by positivity) (hηw1 j)
  have hηw' : ∀ j, (w j).im ≤ ηt := fun j => hle_ηt (hw j).2.2
  -- the finite family of covering grids (centre, radius)
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (ℝ × ℝ), S =
      ((Finset.range (K + 1)).image fun k => (u.re, (2 : ℝ) ^ k * ηt)) ∪
        ((Finset.range (K' + 1)).image fun k => (u.re, (2 : ℝ) ^ k * w')) ∪
        {(u.re, 0)} ∪ (Finset.univ.image fun j => ((w j).re, (0 : ℝ))) := ⟨_, rfl⟩
  have hS : ∀ q ∈ S, |q.1 - E| ≤ C₀ / n ∧ 0 ≤ q.2 ∧ q.2 ≤ κ / 4 := by
    intro q hq
    simp only [hSdef, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton, Finset.mem_univ, true_and] at hq
    rcases hq with ((⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | rfl) | ⟨j, rfl⟩
    · refine ⟨hure, by positivity, le_trans ?_ hK1⟩
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hηt0.le
    · refine ⟨hure, by positivity, le_trans ?_ hK1'⟩
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hw'0.le
    · exact ⟨hure, le_rfl, by positivity⟩
    · exact ⟨(hw j).1, le_rfl, by positivity⟩
  have hSmem1 : ∀ k ≤ K, (u.re, (2 : ℝ) ^ k * ηt) ∈ S := fun k hk => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl (Or.inl (Or.inl ⟨k, by omega, rfl⟩))
  have hSmem2 : ∀ k ≤ K', (u.re, (2 : ℝ) ^ k * w') ∈ S := fun k hk => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨k, by omega, rfl⟩))
  have hSmem3 : (u.re, (0 : ℝ)) ∈ S := by
    rw [hSdef]; simp
  have hSmem4 : ∀ j, ((w j).re, (0 : ℝ)) ∈ S := fun j => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨j, rfl⟩
  -- sizes: `2^K ≤ n`, `2^{K'} ≤ n`, `#S ≤ (3+m) n`, grid size `≤ G ≤ 2n`
  have hηtinv : ηt⁻¹ ≤ n := by
    rw [hηt, ← Real.rpow_neg hn0.le]
    calc n ^ (-(-1 + 2 * τU)) ≤ n ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = n := Real.rpow_one n
  have h2K : (2 : ℝ) ^ K ≤ n := by
    calc (2 : ℝ) ^ K ≤ 1 / ηt := (le_div_iff₀ hηt0).2 (by linarith)
      _ = ηt⁻¹ := one_div _
      _ ≤ n := hηtinv
  have h2K' : (2 : ℝ) ^ K' ≤ n := by
    have hinv : (2 * w')⁻¹ ≤ n := by
      rw [hw'eq, mul_inv, inv_inv, ← mul_assoc, show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, one_mul]
      calc n ^ (1 - d.c / 6) ≤ n ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = n := Real.rpow_one n
    calc (2 : ℝ) ^ K' ≤ 1 / (2 * w') := (le_div_iff₀ (by positivity)).2 (by linarith)
      _ = (2 * w')⁻¹ := one_div _
      _ ≤ n := hinv
  have hScard : (S.card : ℝ) ≤ (3 + m) * n := by
    have hc1 : S.card ≤ (K + 1) + (K' + 1) + 1 + m := by
      rw [hSdef]
      refine (Finset.card_union_le _ _).trans ?_
      refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) ?_
      · refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) (by simp)
        refine Nat.add_le_add ?_ ?_
        · exact (Finset.card_image_le).trans (by simp)
        · exact (Finset.card_image_le).trans (by simp)
      · exact (Finset.card_image_le).trans (by simp)
    have hK : (K : ℝ) < n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_two_pow_self) h2K
    have hK' : (K' : ℝ) < n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_two_pow_self) h2K'
    have hc1' : (S.card : ℝ) ≤ (K + 1) + (K' + 1) + 1 + m := by exact_mod_cast hc1
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    nlinarith
  have hGS : ∀ q ∈ S, ⌈q.2 / ηt⌉₊ + 1 ≤ ⌈n⌉₊ + 1 := by
    intro q hq
    obtain ⟨-, hq0, hqκ⟩ := hS q hq
    have : q.2 / ηt ≤ n := by
      rw [div_eq_mul_inv]
      calc q.2 * ηt⁻¹ ≤ 1 * n := mul_le_mul (by linarith) hηtinv (by positivity) zero_le_one
        _ = n := one_mul n
    exact Nat.add_le_add_right (Nat.ceil_mono this) 1
  have hG : ((⌈n⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * n := by
    push_cast; linarith [Nat.ceil_lt_add_one hn0.le]
  -- local-law moments at every grid point (single scale `η̃`)
  have hM : ∀ q ∈ S, ∀ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), ∀ x : d.Idx N,
      ∫ ω, ‖green ((ouCommonFlow d).Ht N t ω)
          (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) x x‖ ^ (2 * p)
        ∂(ouCommonMeasure d) ≤ n ^ δ := by
    intro q hq j hj x
    obtain ⟨hq1, hq0, hqκ⟩ := hS q hq
    have he := s3_grid_energy_le hηt0 hE hq1 hq0 hqκ (by rw [hηt]; exact h3) hj
    have := hLLN _ he x
    rw [← hηt] at this
    exact this
  have hΞc := s3_prob_not_gridGood_finset d N t hηt0 hCb0 p S (⌈n⌉₊ + 1) hGS hCb0.le hM
  -- the events: grid failure `T`, bad blocks `Bm a₀` (measurable hulls)
  obtain ⟨T, hTdef⟩ : ∃ T : Set (ouCommonOmega d), T = toMeasurable (ouCommonMeasure d)
      {ω | ¬ ∀ q ∈ S, GridGood ((ouCommonFlow d).Ht N t ω) ηt (n ^ δ) q.1 q.2} := ⟨_, rfl⟩
  have hTm : MeasurableSet T := by rw [hTdef]; exact measurableSet_toMeasurable _ _
  have hTprob : (ouCommonMeasure d).real T ≤
      (3 + m) * n * (2 * n * (n * (n ^ δ / (n ^ δ) ^ (2 * p)))) := by
    rw [hTdef, Measure.real, measure_toMeasurable, ← Measure.real]
    refine hΞc.trans ?_
    rw [hcard]
    have hx : 0 ≤ n * (n ^ δ / (n ^ δ) ^ (2 * p)) := by positivity
    calc (S.card : ℝ) * (((⌈n⌉₊ + 1 : ℕ) : ℝ) * (n * (n ^ δ / (n ^ δ) ^ (2 * p))))
        ≤ ((3 + m) * n) * ((2 * n) * (n * (n ^ δ / (n ^ δ) ^ (2 * p)))) := by
          gcongr
      _ = _ := by ring
  obtain ⟨Bs, hBsdef⟩ : ∃ Bs : ZMod (d.L N) → Set (ouCommonOmega d), Bs = fun a0 =>
      {ω | ∃ α, |((ouCommonFlow d).hermitian N t ω).eigenvalues α - E| ≤ n ^ (-1 + d.c / 6) ∧
        n ^ (-(d.c / 36)) ≤ ‖blockM ((ouCommonFlow d).hermitian N t ω) a0 α‖} := ⟨_, rfl⟩
  obtain ⟨Bm, hBmdef⟩ : ∃ Bm : ZMod (d.L N) → Set (ouCommonOmega d),
      Bm = fun a0 => toMeasurable (ouCommonMeasure d) (Bs a0) := ⟨_, rfl⟩
  have hBmm : ∀ a0, MeasurableSet (Bm a0) := fun a0 => by
    rw [hBmdef]; exact measurableSet_toMeasurable _ _
  have hBprob : ∀ a0, (ouCommonMeasure d).real (Bm a0) ≤ 3 * n ^ (-(d.c / 18)) := by
    intro a0
    have h := hbadN a0
    rw [Measure.real, hBmdef]
    simp only [measure_toMeasurable]
    rw [hBsdef]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  -- the majorant constants
  have hsc : s.card ≤ m := by simpa using Finset.card_le_univ s
  obtain ⟨Pw, hPw⟩ : ∃ Pw : ℝ, Pw = n ^ ((3 * τU + δ) * (s.card : ℝ)) := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 193 + 128 / κ ^ 2 := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 6 + 16 / τU + 8 / κ := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hPw0 : 0 ≤ Pw := by rw [hPw]; positivity
  have hcB0 : 0 ≤ Pw * 4 * n⁻¹ * n⁻¹ * (C₂ * n ^ (3 * τU + δ)) *
      (4 * n ^ (2 + 6 * τU + 2 * δ)) := by positivity
  have hCr0 : 0 ≤ 8 * n ^ ((1 + τU) * ((s.card : ℝ) + 3)) := by positivity
  -- pointwise domination
  have hfg : ∀ ω, (∏ j ∈ s, (stieltjes ((ouCommonFlow d).Ht N t ω) (w j)).im) *
      paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) u ≤
      Pw * 4 * n⁻¹ * n⁻¹ * (C₂ * n ^ (3 * τU + δ)) *
          (C₁ * n ^ (2 - d.c / 36 + 4 * τU + 2 * δ)) * n +
        Pw * 4 * n⁻¹ * n⁻¹ * (C₂ * n ^ (3 * τU + δ)) * (4 * n ^ (2 + 6 * τU + 2 * δ)) *
          ∑ y : d.Idx N, (Bm y.1).indicator 1 ω +
        8 * n ^ ((1 + τU) * ((s.card : ℝ) + 3)) * T.indicator 1 ω := by
    intro ω
    have hH := (ouCommonFlow d).hermitian N t ω
    have hind : ∀ (A : Set (ouCommonOmega d)), 0 ≤ A.indicator (1 : ouCommonOmega d → ℝ) ω :=
      fun A => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have hA0 : 0 ≤ Pw * 4 * n⁻¹ * n⁻¹ * (C₂ * n ^ (3 * τU + δ)) *
        (C₁ * n ^ (2 - d.c / 36 + 4 * τU + 2 * δ)) * n := by positivity
    have hsum0 : 0 ≤ Pw * 4 * n⁻¹ * n⁻¹ * (C₂ * n ^ (3 * τU + δ)) *
        (4 * n ^ (2 + 6 * τU + 2 * δ)) * ∑ y : d.Idx N, (Bm y.1).indicator 1 ω :=
      mul_nonneg hcB0 (Finset.sum_nonneg fun y _ => hind _)
    by_cases hωT : ω ∈ T
    · -- crude row
      have hc1 := s3_pointwise_crude d N hH s w u hηu hηw
      have hc2 := s3_prod_crude_le hn1 s w u hηw1 hηu1
      have hTi : T.indicator (1 : ouCommonOmega d → ℝ) ω = 1 := by
        simp [Set.indicator_of_mem hωT]
      rw [hTi, mul_one]
      refine le_trans hc1 (le_trans hc2 ?_)
      linarith
    · -- good event
      have hΞ : ∀ q ∈ S, GridGood ((ouCommonFlow d).Ht N t ω) ηt (n ^ δ) q.1 q.2 := by
        by_contra hn'
        apply hωT
        rw [hTdef]
        exact subset_toMeasurable _ _ hn'
      have hBad : ∀ a0, ¬ (ω ∈ Bm a0) → ∀ α, |hH.eigenvalues α - u.re| ≤ w' →
          ‖blockM hH a0 α‖ ≤ n ^ (-(d.c / 36)) := by
        intro a0 hna α hα
        have hnb : ω ∉ Bs a0 := fun hb => hna (by rw [hBmdef]; exact subset_toMeasurable _ _ hb)
        rw [hBsdef] at hnb
        simp only [Set.mem_ofPred_eq, not_exists, not_and, not_le] at hnb
        refine (hnb α ?_).le
        have hsplit : n ^ (-1 + d.c / 6) = n ^ (d.c / 6) * n⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]; congr 1; ring
        have hC : C₀ / n ≤ n ^ (-1 + d.c / 6) / 2 := by
          rw [hsplit, div_eq_mul_inv]
          have := mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hn0.le)
          linarith
        calc |hH.eigenvalues α - E| ≤ |hH.eigenvalues α - u.re| + |u.re - E| :=
              abs_sub_le _ _ _
          _ ≤ w' + C₀ / n := add_le_add hα hure
          _ ≤ n ^ (-1 + d.c / 6) := by rw [hw'def]; linarith
      have hgood := s3_pointwise_good_norm d N hH s w u (δ := δ) hn1 hLW hc2 hτU hδ.le hκ hκ2
        hηt hw'eq rfl hηu1 hηu' hηw1 hηw' hK1 hK2 hK2'
        (fun k hk => hΞ (u.re, (2 : ℝ) ^ k * ηt) (hSmem1 k hk))
        (fun k hk => hΞ (u.re, (2 : ℝ) ^ k * w') (hSmem2 k hk)) (hΞ (u.re, 0) hSmem3)
        (fun j => hΞ ((w j).re, 0) (hSmem4 j)) (fun a0 => ω ∈ Bm a0) hBad
      have hsumeq : ∑ y : d.Idx N, (if ω ∈ Bm y.1 then (1 : ℝ) else 0) =
          ∑ y : d.Idx N, (Bm y.1).indicator 1 ω := by
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases hy : ω ∈ Bm y.1
        · simp [hy]
        · simp [hy]
      rw [hsumeq, ← hPw, ← hC₁, ← hC₂] at hgood
      have hTi0 : 0 ≤ 8 * n ^ ((1 + τU) * ((s.card : ℝ) + 3)) * T.indicator 1 ω :=
        mul_nonneg hCr0 (hind _)
      refine hgood.trans ?_
      linarith
  have hf0 : ∀ ω, 0 ≤ (∏ j ∈ s, (stieltjes ((ouCommonFlow d).Ht N t ω) (w j)).im) *
      paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) u := fun ω =>
    mul_nonneg (Finset.prod_nonneg fun j _ =>
        (stieltjes_im_nonneg_le ((ouCommonFlow d).hermitian N t ω) (hηw j)).1)
      (paperL1Kernel_nonneg d N _ u)
  refine (s3_integral_le_of_majorant hf0 (fun y : d.Idx N => Bm y.1) (fun y => hBmm y.1) hTm
    _ _ _ hfg).trans ?_
  -- final normalization: good part and crude part, each `≤ ½ n^{…}`
  have hsumB : ∑ y : d.Idx N, (ouCommonMeasure d).real (Bm y.1) ≤
      n * (3 * n ^ (-(d.c / 18))) := by
    calc _ ≤ ∑ _y : d.Idx N, 3 * n ^ (-(d.c / 18)) := Finset.sum_le_sum fun y _ => hBprob y.1
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hgoodT := s3_good_total_le (X := n) (c := d.c) (δ := δ) (C₁ := C₁) (C₂ := C₂)
    (sc := s.card) (m := m) hn1 hc.le hτU hδ.le hC₁0 hC₂0 hsc hmδ (by rw [hC₁, hC₂]; exact h5)
  have hcrudeT := s3_crude_total_le (X := n) (c := d.c) (δ := δ) (sc := s.card) (m := m) (p := p)
    hn1 hτU (by linarith) hsc hp h1
  rw [← hPw] at hgoodT
  have hA2 : Pw * 4 * n⁻¹ * n⁻¹ * (C₂ * n ^ (3 * τU + δ)) * (4 * n ^ (2 + 6 * τU + 2 * δ)) *
      ∑ y : d.Idx N, (ouCommonMeasure d).real (Bm y.1) ≤
      n * (Pw * 4 * n⁻¹ * n⁻¹ * (C₂ * n ^ (3 * τU + δ)) *
        (4 * n ^ (2 + 6 * τU + 2 * δ)) * (3 * n ^ (-(d.c / 18)))) := by
    calc _ ≤ Pw * 4 * n⁻¹ * n⁻¹ * (C₂ * n ^ (3 * τU + δ)) * (4 * n ^ (2 + 6 * τU + 2 * δ)) *
          (n * (3 * n ^ (-(d.c / 18)))) := mul_le_mul_of_nonneg_left hsumB hcB0
      _ = _ := by ring
  have hcrude' : 8 * n ^ ((1 + τU) * ((s.card : ℝ) + 3)) * (ouCommonMeasure d).real T ≤
      8 * n ^ ((1 + τU) * ((s.card : ℝ) + 3)) *
        ((3 + (m : ℝ)) * n * (2 * n * (n * (n ^ δ / (n ^ δ) ^ (2 * p))))) :=
    mul_le_mul_of_nonneg_left hTprob hCr0
  linarith

/-- **The weighted `L₁` kernel bound** (the `L₁` half of the per-time bound behind
(2.28)/(2.29)).  For `t ∈ (0, t_U]` and spectral parameters in the window (2.22),
`E[∏_{j∈s} Im m_t(w_j) · L₁(u)] ≤ N^{1 - c/36 + (3|s|+16)τ_U}`.  Uses `FlowLocalLaw` only at its
single scale `η̃ = N^{-1+2τ_U}` (via the covering lemma) and `FlowEq747` through
`measure_bad_flow_of_eq747`. -/
theorem expect_L1_weighted_le (d : Dims) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hτc : τU < d.c / 3) (hLL : FlowLocalLaw d κ τU) (hQUE : FlowEq747 d κ τU)
    (E : ℝ) (hE : |E| ≤ 2 - κ) {C₀ : ℝ} (hC₀ : 0 < C₀) (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Ioc (0 : ℝ) ((ouCommonBand d).tPow τU N),
      ∀ (s : Finset (Fin m)) (w : Fin m → ℂ) (u : ℂ),
        (∀ i, InWindow222 d E C₀ τU N (w i)) → InWindow222 d E C₀ τU N u →
        ∫ ω, (∏ j ∈ s, (stieltjes ((ouCommonFlow d).Ht N t ω) (w j)).im) *
            paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) u ∂(ouCommonMeasure d) ≤
          ((ouCommonBand d).size N : ℝ) ^ (1 - d.c / 36 + (3 * (s.card : ℝ) + 16) * τU) := by
  have hc : 0 < d.c := d.c_pos
  have hc2 : d.c < 1 / 2 := s3_c_lt_half d
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  -- parameters fixed before `N`: `δ = τ/(m+5)` and the moment order `p`
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = τU / (m + 5) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hmδ : ((m : ℝ) + 3) * δ ≤ τU := by
    rw [hδdef, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = ⌈((1 + τU) * m + 8 + 3 * τU + δ) / (2 * δ)⌉₊ := ⟨_, rfl⟩
  have hp : (1 + τU) * m + 7 + 3 * τU + δ ≤ 2 * p * δ := by
    have h1 := Nat.le_ceil (((1 + τU) * m + 8 + 3 * τU + δ) / (2 * δ))
    rw [← hpdef, div_le_iff₀ (by positivity)] at h1
    linarith
  have hsize : Tendsto (fun N => ((ouCommonBand d).size N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (ouCommonBand d).tendsto_size
  -- the eventual conditions on `N` (finitely many, uniform in `t, s, w, u`)
  have ev1 : ∀ᶠ N : ℕ in atTop, 32 * (3 + (m : ℝ)) ≤ ((ouCommonBand d).size N : ℝ) :=
    hsize.eventually_ge_atTop _
  have ev2 : ∀ᶠ N : ℕ in atTop, 2 * C₀ ≤ ((ouCommonBand d).size N : ℝ) ^ (d.c / 6) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  have ev3 : ∀ᶠ N : ℕ in atTop, C₀ / ((ouCommonBand d).size N : ℝ) +
      2 * ((ouCommonBand d).size N : ℝ) ^ (-1 + 2 * τU) < κ / 4 := by
    have h1 : Tendsto (fun N => C₀ / ((ouCommonBand d).size N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsize
    have h2 : Tendsto (fun N => ((ouCommonBand d).size N : ℝ) ^ (-1 + 2 * τU)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - 2 * τU) (by linarith)).comp hsize
      refine this.congr fun N => ?_
      simp only [Function.comp]; congr 1; ring
    have h3 := h1.add (h2.const_mul 2)
    simp only [mul_zero, add_zero] at h3
    exact h3.eventually_lt_const (by positivity)
  have ev4 : ∀ᶠ N : ℕ in atTop, ((ouCommonBand d).size N : ℝ) ^ (-1 + d.c / 6) < κ / 2 := by
    have h2 : Tendsto (fun N => ((ouCommonBand d).size N : ℝ) ^ (-1 + d.c / 6)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - d.c / 6) (by linarith)).comp hsize
      refine this.congr fun N => ?_
      simp only [Function.comp]; congr 1; ring
    exact h2.eventually_lt_const (by positivity)
  have ev5 : ∀ᶠ N : ℕ in atTop, 8 * ((193 + 128 / κ ^ 2) + 12) * (6 + 16 / τU + 8 / κ) ≤
      ((ouCommonBand d).size N : ℝ) ^ (6 * τU) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  filter_upwards [hLL δ hδ p, s3_bad_uniform d hκ hτc hQUE E hE, ev1, ev2, ev3, ev4, ev5]
    with N hLLN hbadN h1 h2 h3 h4 h5
  intro t ht s w u hw hu
  exact s3_fixed_time d N t p m rfl hκ hτU hδ hc2 hκ2 hmδ hp hE h1 h2 h3 h4 h5
    (fun e he x => hLLN t ⟨ht.1.le, ht.2⟩ e he x) (fun a0 => hbadN t ht a0) s w u hw hu

end RBM.Gauss
