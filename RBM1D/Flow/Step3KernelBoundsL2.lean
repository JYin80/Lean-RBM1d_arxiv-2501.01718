/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Step3KernelBounds
import RBM1D.Flow.GreenSpectralL2

/-!
# Step 3 of Theorem 2.6: the weighted `L₂` kernel bound

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Theorem 2.6, Step 3.

* `RBM.Gauss.expect_L2_weighted_le`: the `L₂` half of the per-time bound behind (2.28)/(2.30), in
  the weighted form produced by (2.25), for the OU flow on the common carrier, from the
  single-scale local law `FlowLocalLaw` ((2.26) at `η̃ = N^{-1+2τ_U}`) and the flow QUE input
  `FlowEq747` ((2.27) via (7.47), pair form through `measure_bad2_le_of_que`).  The exponent is
  `1 - c/36 + (3|s|+16)τ_U`, as for `L₁` (`Step3KernelBounds.lean`).

Route: the pair spectral identity `green_spectral_identity_blockM2` writes `L₂` through
`A_y = ∑_{α,β} |p₁α|² |p₂β|² |M_{y,αβ}| |u_α(y)||u_β(y)|`.  Window pairs use the pair-QUE bound
`|M_{y,αβ}| ≤ N^{-c/36}`; the remaining pairs use `|M_{y,αβ}| ≤ N ∑_x s_x |u_α(x)||u_β(x)|` and
AM–GM, which reduces everything to the one-index sums `∑_α |p_α|² |u_α(z)|²` (zero-radius grid)
and their out-of-window parts (dyadic shells and the covering lemma).  The local law is used only
at its single scale `η̃`, at finitely many deterministic energies.
-/

open MeasureTheory Filter Matrix Topology
open scoped ENNReal

namespace RBM

open Step3KernelBounds

/-! ### One-index spectral sums -/

section Poles

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

private theorem l2_pole_norm_sq_eq {u : ℂ} (α : n) :
    ‖spectralPole hH u α‖ ^ 2 = ((hH.eigenvalues α - u.re) ^ 2 + u.im ^ 2)⁻¹ := by
  rw [spectralPole, norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
  ring

private theorem l2_pole_norm_sq_le_inv_im {u : ℂ} (hη : 0 < u.im) (α : n) :
    ‖spectralPole hH u α‖ ^ 2 ≤ (u.im⁻¹) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (pole_norm_le_inv_im' hH hη α) 2

private theorem l2_pole_norm_sq_le_inv_dist_sq {u : ℂ} (α : n)
    (hd : 0 < |hH.eigenvalues α - u.re|) :
    ‖spectralPole hH u α‖ ^ 2 ≤ (|hH.eigenvalues α - u.re| ^ 2)⁻¹ := by
  rw [l2_pole_norm_sq_eq]
  refine inv_anti₀ (by positivity) ?_
  rw [sq_abs]
  nlinarith [sq_nonneg u.im]

/-- Dyadic majorant (copy of a private helper of `Step3KernelBounds.lean`). -/
private theorem l2_dyadic_le_sum {f : ℝ → ℝ} (hf : ∀ a b, 0 < a → a ≤ b → f b ≤ f a)
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
      Finset.sum_nonneg fun k _ => by
        split_ifs <;> first | exact hf0 _ (by positivity) | exact le_rfl
    by_cases hd : d ≤ 2 ^ K * ρ
    · have := ih h1 hd
      have hlast : 0 ≤ (if d ≤ 2 ^ (K + 1) * ρ then f (2 ^ K * ρ) else 0) := by
        split_ifs; exact hf0 _ (by positivity)
      linarith
    · push Not at hd
      simp only [h2, ite_true]
      have := hf (2 ^ K * ρ) d (by positivity) hd.le
      linarith

private theorem l2_geom_half_sum_le (K : ℕ) : ∑ k ∈ Finset.range K, ((2 : ℝ) ^ k)⁻¹ ≤ 2 := by
  have h := sum_geometric_two_le K
  simpa [one_div, inv_pow] using h

include hH in
/-- Crude bound `0 ≤ Im m(w) ≤ 1/Im w`. -/
private theorem l2_stieltjes_im_nonneg_le [Nonempty n] {w : ℂ} (hη : 0 < w.im) :
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

omit [DecidableEq n] in
private theorem l2_gridGood_zero_stieltjes [DecidableEq n] [Nonempty n] {η Cb E₀ : ℝ}
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

include hH in
/-- `Im m(w) ≤ (η̃/Im w) Cb` from the zero-radius grid at `Re w`. -/
private theorem l2_stieltjes_im_le_of_grid [Nonempty n] {w : ℂ} (hη : 0 < w.im) {ηt Cb : ℝ}
    (hηη : w.im ≤ ηt) (hG : GridGood H ηt Cb w.re 0) :
    (stieltjes H w).im ≤ ηt / w.im * Cb := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hmono := stieltjes_eta_mul_im_mono H hH w.re w.im ηt hη hηη
  rw [← hw] at hmono
  have hT := l2_gridGood_zero_stieltjes (H := H) hG
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  rw [div_mul_eq_mul_div, le_div_iff₀ hη, mul_comm]
  exact hmono.trans (mul_le_mul_of_nonneg_left hT hηt.le)

/-- **The `Q` row.** `∑_α |p_α(u)|² |u_α(z)|² ≤ (η̃/η²) Cb` from the zero-radius grid at `Re u`. -/
private theorem l2_sum_pole_sq_mass_le_of_grid {u : ℂ} (hη : 0 < u.im) {ηt Cb : ℝ}
    (hηη : u.im ≤ ηt) (hG : GridGood H ηt Cb u.re 0) (z : n) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ ηt / u.im ^ 2 * Cb := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  have hGz : (green H ((u.re : ℂ) + ηt * Complex.I) z z).im ≤ Cb := by
    have := hG 0 (by simp) z
    simpa using this
  rw [im_green_apply_self hH u.re hηt.ne' z] at hGz
  have hterm : ∀ α : n, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤
      ηt / u.im ^ 2 * (ηt * Complex.normSq (hH.eigenvectorBasis α z) /
        ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) := by
    intro α
    rw [l2_pole_norm_sq_eq, Complex.normSq_eq_norm_sq]
    set x := (hH.eigenvalues α - u.re) ^ 2
    set v := ‖hH.eigenvectorBasis α z‖ ^ 2
    have hx : 0 ≤ x := sq_nonneg _
    have hv : 0 ≤ v := by positivity
    rw [show ηt / u.im ^ 2 * (ηt * v / (x + ηt ^ 2)) = ηt ^ 2 * v / (u.im ^ 2 * (x + ηt ^ 2)) by
      field_simp]
    rw [inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : u.im ^ 2 ≤ ηt ^ 2 := pow_le_pow_left₀ hη.le hηη 2
    have h3 : u.im ^ 2 * (x + ηt ^ 2) ≤ ηt ^ 2 * (x + u.im ^ 2) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hv]
  calc _ ≤ ∑ α : n, ηt / u.im ^ 2 * (ηt * Complex.normSq (hH.eigenvectorBasis α z) /
        ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) := Finset.sum_le_sum fun α _ => hterm α
    _ = ηt / u.im ^ 2 * ∑ α : n, ηt * Complex.normSq (hH.eigenvectorBasis α z) /
        ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2) := by rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

/-- Crude `Q` row: `∑_α |p_α(u)|² |u_α(z)|² ≤ (Im u)⁻²`. -/
private theorem l2_sum_pole_sq_mass_le_crude {u : ℂ} (hη : 0 < u.im) (z : n) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ (u.im⁻¹) ^ 2 := by
  calc _ ≤ ∑ α, (u.im⁻¹) ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 :=
        Finset.sum_le_sum fun α _ =>
          mul_le_mul_of_nonneg_right (l2_pole_norm_sq_le_inv_im hH hη α) (by positivity)
    _ = (u.im⁻¹) ^ 2 := by rw [← Finset.mul_sum, sum_sq_norm_eigenvectorBasis hH z, mul_one]

/-- `∑_α |p_α|² = ∑_z ∑_α |p_α|² |u_α(z)|²` (completeness of each eigenvector). -/
private theorem l2_sum_pole_sq_eq (u : ℂ) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 =
      ∑ z : n, ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.mul_sum, sum_sq_norm_eigenvector hH α, mul_one]

/-- **The `Q^out` row.** Out-of-window part (`|λ_α - Re u| > w'`) of `∑_α |p_α|² |u_α(z)|²`, from
the grids of radii `2^k w'`, `k ≤ K'` (dyadic shells and the covering lemma), and completeness
beyond `2^{K'} w'`. -/
private theorem l2_sum_pole_sq_mass_out_le {u : ℂ} {ηt Cb w' : ℝ} (hηt : 0 < ηt) (hCb : 0 ≤ Cb)
    (hw' : 0 < w') (K' : ℕ) (hG : ∀ k ≤ K', GridGood H ηt Cb u.re (2 ^ k * w')) (z : n) :
    ∑ α, (if |hH.eigenvalues α - u.re| ≤ w' then 0 else
        ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2) ≤
      Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹ := by
  set v : n → ℝ := fun γ => ‖hH.eigenvectorBasis γ z‖ ^ 2 with hv
  set dd : n → ℝ := fun γ => |hH.eigenvalues γ - u.re| with hdd
  have hv0 : ∀ γ, 0 ≤ v γ := fun γ => by positivity
  have hpt : ∀ γ, (if dd γ ≤ w' then 0 else ‖spectralPole hH u γ‖ ^ 2 * v γ) ≤
      ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
          (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) + ((2 ^ K' * w') ^ 2)⁻¹ * v γ := by
    intro γ
    have hS0 : 0 ≤ ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
        (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (by split_ifs <;> simp [hv0])
    have hT0 : 0 ≤ ((2 ^ K' * w') ^ 2)⁻¹ * v γ := mul_nonneg (by positivity) (hv0 γ)
    by_cases h1 : dd γ ≤ w'
    · simp only [h1, ite_true]; linarith
    · push Not at h1
      simp only [not_le.2 h1, ite_false]
      have hdpos : 0 < dd γ := lt_trans hw' h1
      have hpd := mul_le_mul_of_nonneg_right (l2_pole_norm_sq_le_inv_dist_sq hH γ hdpos) (hv0 γ)
      by_cases h2 : dd γ ≤ 2 ^ K' * w'
      · have hdy := l2_dyadic_le_sum (f := fun x => (x ^ 2)⁻¹)
          (fun a b ha hab => inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hab 2))
          (fun a ha => by positivity) hw' K' h1 h2
        have hdy' : (dd γ ^ 2)⁻¹ * v γ ≤ ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
            (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) := by
          calc (dd γ ^ 2)⁻¹ * v γ ≤ (∑ k ∈ Finset.range K',
                (if dd γ ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0)) * v γ :=
                mul_le_mul_of_nonneg_right hdy (hv0 γ)
            _ = _ := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => ?_
                split_ifs <;> ring
        linarith
      · push Not at h2
        have : (dd γ ^ 2)⁻¹ * v γ ≤ ((2 ^ K' * w') ^ 2)⁻¹ * v γ :=
          mul_le_mul_of_nonneg_right
            (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2.le 2)) (hv0 γ)
        linarith
  have hmass : ∀ r : ℝ, 0 ≤ r → GridGood H ηt Cb u.re r →
      ∑ γ, (if dd γ ≤ r then v γ else 0) ≤ 2 * (r + 2 * ηt) * Cb := by
    intro r hr hGr
    rw [← Finset.sum_filter]
    exact sum_mass_window_le_of_im_green_le hH hηt hr hCb u.re z fun j hj => hGr j hj z
  have hmk : ∀ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
      ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) ≤
        Cb * (4 / w' + 4 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ := by
    intro k hk
    have hkK : k + 1 ≤ K' := Finset.mem_range.1 hk
    have h := hmass (2 ^ (k + 1) * w') (by positivity) (hG (k + 1) hkK)
    have hp : (0 : ℝ) < 2 ^ k * w' := by positivity
    calc _ ≤ ((2 ^ k * w') ^ 2)⁻¹ * (2 * (2 ^ (k + 1) * w' + 2 * ηt) * Cb) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Cb * (4 / w' * ((2 : ℝ) ^ k)⁻¹ +
            4 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹) := by
          field_simp; ring
      _ ≤ Cb * (4 / w' * ((2 : ℝ) ^ k)⁻¹ + 4 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * 1) := by
          gcongr
          exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      _ = _ := by ring
  have hsumv : ∑ γ, v γ = 1 := sum_sq_norm_eigenvectorBasis hH z
  calc ∑ α, (if |hH.eigenvalues α - u.re| ≤ w' then 0 else
        ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2)
      = ∑ γ, (if dd γ ≤ w' then 0 else ‖spectralPole hH u γ‖ ^ 2 * v γ) := rfl
    _ ≤ ∑ γ, (∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
          (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) + ((2 ^ K' * w') ^ 2)⁻¹ * v γ) :=
        Finset.sum_le_sum fun γ _ => hpt γ
    _ = ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
            ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) +
          ((2 ^ K' * w') ^ 2)⁻¹ * ∑ γ, v γ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range K', Cb * (4 / w' + 4 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ +
          ((2 ^ K' * w') ^ 2)⁻¹ * 1 := by
        rw [hsumv]
        have := Finset.sum_le_sum hmk
        linarith
    _ = Cb * (4 / w' + 4 * ηt / w' ^ 2) * ∑ k ∈ Finset.range K', ((2 : ℝ) ^ k)⁻¹ +
          ((2 ^ K' * w') ^ 2)⁻¹ := by rw [Finset.mul_sum, mul_one]
    _ ≤ Cb * (4 / w' + 4 * ηt / w' ^ 2) * 2 + ((2 ^ K' * w') ^ 2)⁻¹ := by
        gcongr; exact l2_geom_half_sum_le K'
    _ = _ := by ring

end Poles

/-! ### Pair combinatorics (abstract) -/

section Pair

variable {ι : Type*} [Fintype ι]

/-- AM–GM on a (restricted) one-index sum: `∑_{α∉W} P_α a_α(x) a_α(y) ≤ o` whenever
`∑_{α∉W} P_α a_α(z)² ≤ o` for every `z`. -/
private theorem l2_amgm_sum (P : ι → ℝ) (a : ι → ι → ℝ) (W : ι → Prop) [DecidablePred W]
    (hP : ∀ α, 0 ≤ P α) {o : ℝ}
    (ho : ∀ z, ∑ α, (if W α then 0 else P α * a α z ^ 2) ≤ o) (x y : ι) :
    ∑ α, (if W α then 0 else P α * (a α x * a α y)) ≤ o := by
  have hpt : ∀ α, (if W α then 0 else P α * (a α x * a α y)) ≤
      (1 / 2) * (if W α then 0 else P α * a α x ^ 2) +
        (1 / 2) * (if W α then 0 else P α * a α y ^ 2) := by
    intro α
    split_ifs
    · simp
    · have := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (a α x) (a α y)) (hP α)
      nlinarith
  calc _ ≤ ∑ α, ((1 / 2) * (if W α then 0 else P α * a α x ^ 2) +
        (1 / 2) * (if W α then 0 else P α * a α y ^ 2)) := Finset.sum_le_sum fun α _ => hpt α
    _ = (1 / 2) * ∑ α, (if W α then 0 else P α * a α x ^ 2) +
        (1 / 2) * ∑ α, (if W α then 0 else P α * a α y ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (1 / 2) * o + (1 / 2) * o := by gcongr <;> [exact ho x; exact ho y]
    _ = o := by ring

private theorem l2_sum_ite_nonneg (P : ι → ℝ) (a : ι → ι → ℝ) (W : ι → Prop) [DecidablePred W]
    (hP : ∀ α, 0 ≤ P α) (ha : ∀ α x, 0 ≤ a α x) (x y : ι) :
    0 ≤ ∑ α, (if W α then 0 else P α * (a α x * a α y)) :=
  Finset.sum_nonneg fun α _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hP α) (mul_nonneg (ha α x) (ha α y))

/-- The "rest" sum factorizes: `∑_{α∉W₁} ∑_β P₁P₂ (N∑_x s_x a_α(x)a_β(x)) a_α(y)a_β(y)
= N ∑_x s_x F₁^{out}(x) F₂(x)`. -/
private theorem l2_rest_eq (P₁ P₂ : ι → ℝ) (a : ι → ι → ℝ) (s : ι → ℝ) (y : ι) (Nn : ℝ)
    (W₁ : ι → Prop) [DecidablePred W₁] :
    ∑ α, ∑ β, (if W₁ α then 0 else
        P₁ α * P₂ β * (Nn * ∑ x, s x * (a α x * a β x)) * (a α y * a β y)) =
      Nn * ∑ x, s x * ((∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y))) *
        ∑ β, P₂ β * (a β x * a β y)) := by
  have hpt : ∀ α β, (if W₁ α then 0 else
      P₁ α * P₂ β * (Nn * ∑ x, s x * (a α x * a β x)) * (a α y * a β y)) =
      ∑ x, Nn * (s x * ((if W₁ α then 0 else P₁ α * (a α x * a α y)) *
        (P₂ β * (a β x * a β y)))) := by
    intro α β
    split_ifs
    · simp
    · simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
  simp_rw [hpt]
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]

/-- **Pair combinatorics.** Window pairs (`W₁ × W₂`, where `M ≤ θ`) plus the rest (where
`M ≤ N ∑_x s_x a_α(x) a_β(x)`), each reduced by AM–GM to the one-index bounds `q_i`, `o_i`
(out-of-window) and `S_i` (total weight). -/
private theorem l2_pair_abstract (P₁ P₂ : ι → ℝ) (a M : ι → ι → ℝ) (s : ι → ℝ) (y : ι)
    {Nn θ q₁ q₂ o₁ o₂ S₁ S₂ : ℝ} (W₁ W₂ : ι → Prop) [DecidablePred W₁] [DecidablePred W₂]
    (hP₁ : ∀ α, 0 ≤ P₁ α) (hP₂ : ∀ α, 0 ≤ P₂ α) (ha : ∀ α x, 0 ≤ a α x)
    (hs : ∀ x, 0 ≤ s x) (hsum : ∑ x, s x ≤ 2) (hN : 0 ≤ Nn) (hθ : 0 ≤ θ)
    (hM : ∀ α β, M α β ≤ Nn * ∑ x, s x * (a α x * a β x))
    (hMw : ∀ α β, W₁ α → W₂ β → M α β ≤ θ)
    (hq₁ : ∀ z, ∑ α, P₁ α * a α z ^ 2 ≤ q₁) (hq₂ : ∀ z, ∑ α, P₂ α * a α z ^ 2 ≤ q₂)
    (ho₁ : ∀ z, ∑ α, (if W₁ α then 0 else P₁ α * a α z ^ 2) ≤ o₁)
    (ho₂ : ∀ z, ∑ α, (if W₂ α then 0 else P₂ α * a α z ^ 2) ≤ o₂)
    (hS₁ : ∑ α, P₁ α ≤ S₁) (hS₂ : ∑ α, P₂ α ≤ S₂) :
    ∑ α, ∑ β, P₁ α * P₂ β * M α β * (a α y * a β y) ≤
      θ / 2 * (q₁ * S₂ + S₁ * q₂) + 2 * Nn * (o₁ * q₂ + q₁ * o₂) := by
  classical
  set X : ι → ι → ℝ := fun α β =>
    P₁ α * P₂ β * (Nn * ∑ x, s x * (a α x * a β x)) * (a α y * a β y) with hX
  have hX0 : ∀ α β, 0 ≤ X α β := fun α β => by
    have : 0 ≤ ∑ x, s x * (a α x * a β x) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hs x) (mul_nonneg (ha α x) (ha β x))
    have := hP₁ α; have := hP₂ β; have := ha α y; have := ha β y
    simp only [X]; positivity
  have hpt : ∀ α β, P₁ α * P₂ β * M α β * (a α y * a β y) ≤
      θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) +
        (if W₁ α then 0 else X α β) + (if W₂ β then 0 else X α β) := by
    intro α β
    have hc : 0 ≤ P₁ α * P₂ β * (a α y * a β y) :=
      mul_nonneg (mul_nonneg (hP₁ α) (hP₂ β)) (mul_nonneg (ha α y) (ha β y))
    have hθt : 0 ≤ θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) := by
      have := hP₁ α; have := hP₂ β; positivity
    have hrest : P₁ α * P₂ β * M α β * (a α y * a β y) ≤ X α β := by
      have := mul_le_mul_of_nonneg_left (hM α β) hc
      simp only [X]; nlinarith
    by_cases h1 : W₁ α <;> by_cases h2 : W₂ β
    · simp only [h1, h2, ite_true, add_zero]
      have hw := mul_le_mul_of_nonneg_left (hMw α β h1 h2) hc
      have hag := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (a α y) (a β y))
        (mul_nonneg (mul_nonneg hθ (hP₁ α)) (hP₂ β))
      nlinarith
    · simp only [h1, h2, ite_true, ite_false]; linarith
    · simp only [h1, h2, ite_true, ite_false, add_zero]; linarith
    · simp only [h1, h2, ite_false]; linarith [hX0 α β]
  -- the three sums
  have hq₁0 : 0 ≤ q₁ := le_trans (Finset.sum_nonneg fun α _ => by
    have := hP₁ α; positivity) (hq₁ y)
  have hq₂0 : 0 ≤ q₂ := le_trans (Finset.sum_nonneg fun α _ => by
    have := hP₂ α; positivity) (hq₂ y)
  have hG₁ : ∀ x, ∑ α, P₁ α * (a α x * a α y) ≤ q₁ := fun x => by
    simpa using l2_amgm_sum P₁ a (fun _ => False) hP₁ (o := q₁) (by simpa using hq₁) x y
  have hG₂ : ∀ x, ∑ α, P₂ α * (a α x * a α y) ≤ q₂ := fun x => by
    simpa using l2_amgm_sum P₂ a (fun _ => False) hP₂ (o := q₂) (by simpa using hq₂) x y
  have hG₁0 : ∀ x, 0 ≤ ∑ α, P₁ α * (a α x * a α y) := fun x =>
    Finset.sum_nonneg fun α _ => mul_nonneg (hP₁ α) (mul_nonneg (ha α x) (ha α y))
  have hG₂0 : ∀ x, 0 ≤ ∑ α, P₂ α * (a α x * a α y) := fun x =>
    Finset.sum_nonneg fun α _ => mul_nonneg (hP₂ α) (mul_nonneg (ha α x) (ha α y))
  have hS1 : ∑ α, ∑ β, θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) ≤
      θ / 2 * (q₁ * S₂ + S₁ * q₂) := by
    have e : ∑ α, ∑ β, θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) =
        θ / 2 * ((∑ α, P₁ α * a α y ^ 2) * (∑ β, P₂ β) +
          (∑ α, P₁ α) * ∑ β, P₂ β * a β y ^ 2) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    rw [e]
    have hP₂s : 0 ≤ ∑ β, P₂ β := Finset.sum_nonneg fun β _ => hP₂ β
    have hP₁s : 0 ≤ ∑ α, P₁ α := Finset.sum_nonneg fun α _ => hP₁ α
    have hQ₂0 : 0 ≤ ∑ β, P₂ β * a β y ^ 2 := Finset.sum_nonneg fun β _ => by
      have := hP₂ β; positivity
    have hS₁0 : 0 ≤ S₁ := hP₁s.trans hS₁
    gcongr
    · exact hq₁ y
    · exact hq₂ y
  have hS2 : ∑ α, ∑ β, (if W₁ α then 0 else X α β) ≤ 2 * Nn * (o₁ * q₂) := by
    rw [l2_rest_eq P₁ P₂ a s y Nn W₁]
    have hF : ∀ x, ∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y)) ≤ o₁ :=
      fun x => l2_amgm_sum P₁ a W₁ hP₁ ho₁ x y
    have hF0 : ∀ x, 0 ≤ ∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y)) :=
      fun x => l2_sum_ite_nonneg P₁ a W₁ hP₁ ha x y
    have ho₁0 : 0 ≤ o₁ := (hF0 y).trans (hF y)
    calc Nn * ∑ x, s x * ((∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y))) *
          ∑ β, P₂ β * (a β x * a β y)) ≤ Nn * ∑ x, s x * (o₁ * q₂) := by
          gcongr with x
          all_goals first | exact hs x | exact hF x | exact hG₂ x | exact hG₂0 x
      _ = Nn * (∑ x, s x) * (o₁ * q₂) := by rw [← Finset.sum_mul, mul_assoc]
      _ ≤ Nn * 2 * (o₁ * q₂) := by gcongr
      _ = _ := by ring
  have hS3 : ∑ α, ∑ β, (if W₂ β then 0 else X α β) ≤ 2 * Nn * (q₁ * o₂) := by
    have e : ∀ α β, (if W₂ β then 0 else X α β) = (if W₂ β then 0 else
        P₂ β * P₁ α * (Nn * ∑ x, s x * (a β x * a α x)) * (a β y * a α y)) := by
      intro α β
      simp only [X]
      rw [show ∑ x, s x * (a β x * a α x) = ∑ x, s x * (a α x * a β x) from
        Finset.sum_congr rfl fun x _ => by ring]
      split_ifs <;> ring
    simp_rw [e]
    rw [Finset.sum_comm, l2_rest_eq P₂ P₁ a s y Nn W₂]
    have hF : ∀ x, ∑ α, (if W₂ α then 0 else P₂ α * (a α x * a α y)) ≤ o₂ :=
      fun x => l2_amgm_sum P₂ a W₂ hP₂ ho₂ x y
    have hF0 : ∀ x, 0 ≤ ∑ α, (if W₂ α then 0 else P₂ α * (a α x * a α y)) :=
      fun x => l2_sum_ite_nonneg P₂ a W₂ hP₂ ha x y
    have ho₂0 : 0 ≤ o₂ := (hF0 y).trans (hF y)
    calc Nn * ∑ x, s x * ((∑ α, (if W₂ α then 0 else P₂ α * (a α x * a α y))) *
          ∑ β, P₁ β * (a β x * a β y)) ≤ Nn * ∑ x, s x * (o₂ * q₁) := by
          gcongr with x
          all_goals first | exact hs x | exact hF x | exact hG₁ x | exact hG₁0 x
      _ = Nn * (∑ x, s x) * (o₂ * q₁) := by rw [← Finset.sum_mul, mul_assoc]
      _ ≤ Nn * 2 * (o₂ * q₁) := by gcongr
      _ = _ := by ring
  calc _ ≤ ∑ α, ∑ β, (θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) +
        (if W₁ α then 0 else X α β) + (if W₂ β then 0 else X α β)) :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hpt α β
    _ = ∑ α, ∑ β, θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) +
        ∑ α, ∑ β, (if W₁ α then 0 else X α β) + ∑ α, ∑ β, (if W₂ β then 0 else X α β) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ _ := by linarith

end Pair

/-! ### The pair block profile and the spectral form of `L₂` -/

section Block

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {Hm : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : Hm.IsHermitian)

omit [NeZero W] in
private theorem l2_eigOverlap_diagonal (dg : ZMod L × Fin W → ℂ) (i j : ZMod L × Fin W) :
    eigOverlap hH (diagonal dg) i j =
      ∑ p, dg p * (star (hH.eigenvectorBasis i p) * hH.eigenvectorBasis j p) := by
  simp only [eigOverlap, dotProduct, mulVec_diagonal, Pi.star_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

omit [NeZero W] in
/-- `M_{y,α,β} = N ∑_x ψ_α(x) ψ_β(x)* S°_{xy}` (copy of the private helper `blockM2_eq` of
`GreenSpectralL2.lean`). -/
private theorem l2_blockM2_eq (hL : 3 ≤ L) (a0 : ZMod L) (β0 : Fin W)
    (α β : ZMod L × Fin W) :
    blockM2 hH a0 α β = ((L * W : ℕ) : ℂ) * ∑ x, (hH.eigenvectorBasis α x *
        star (hH.eigenvectorBasis β x)) * (Svar L W x (a0, β0) - ((L * W : ℕ) : ℂ)⁻¹) := by
  set T : Finset (ZMod L) := {a0 - 1, a0, a0 + 1} with hT
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero_zmod L hL
  have h2 : (2 : ZMod L) ≠ 0 := two_ne_zero_zmod L hL
  have hcard : T.card = 3 := by
    have e1 : a0 - 1 ≠ a0 := fun h => h1 (by linear_combination -h)
    have e2 : a0 - 1 ≠ a0 + 1 := fun h => h2 (by linear_combination -h)
    have e3 : a0 ≠ a0 + 1 := fun h => h1 (by linear_combination -h)
    rw [hT, Finset.card_insert_of_notMem (by simp [e1, e2]),
      Finset.card_insert_of_notMem (by simp [e3]), Finset.card_singleton]
  have hmemT : ∀ b : ZMod L, b ∈ T ↔ b - a0 ∈ sbSupport L := by
    intro b
    rw [sub_mem_sbSupport_iff, hT]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h | h)
      · right; left; linear_combination -h
      · left; linear_combination -h
      · right; right; linear_combination -h
    · rintro (h | h | h)
      · right; left; linear_combination -h
      · left; linear_combination -h
      · right; right; linear_combination -h
  have hdiag : ∀ a : ZMod L, eigOverlap hH (Eblk L W a - ((L * W : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ))
      β α = ∑ p, ((if p.1 = a then (W : ℂ)⁻¹ else 0) - ((L * W : ℕ) : ℂ)⁻¹) *
        (hH.eigenvectorBasis α p * star (hH.eigenvectorBasis β p)) := by
    intro a
    rw [← queObs_singleton, queObs_eq_diagonal, l2_eigOverlap_diagonal]
    simp only [Finset.card_singleton, Nat.cast_one, inv_one, one_mul, Finset.mem_singleton]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  simp only [blockM2, ← hT, hdiag]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, hcard]
  have hS : Svar L W p (a0, β0) = (if p.1 ∈ T then (3 : ℂ)⁻¹ else 0) * (W : ℂ)⁻¹ := by
    obtain ⟨b, γ⟩ := p
    rw [Svar_apply, SB_apply, sbKernel]
    simp only [hmemT]
  rw [hS, Finset.sum_ite_eq]
  split_ifs <;> push_cast <;> ring

omit [NeZero L] [NeZero W] in
private theorem l2_centered_profile_norm_le (x y : ZMod L × Fin W) :
    ‖Svar L W x y - ((L * W : ℕ) : ℂ)⁻¹‖ ≤ Sblk L W x y + (L * W : ℝ)⁻¹ := by
  calc ‖Svar L W x y - ((L * W : ℕ) : ℂ)⁻¹‖ ≤
        ‖Svar L W x y‖ + ‖((L * W : ℕ) : ℂ)⁻¹‖ := norm_sub_le _ _
    _ = Sblk L W x y + (L * W : ℝ)⁻¹ := by
      rw [Svar_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Sblk_nonneg x y), norm_inv, Complex.norm_natCast]
      simp only [Nat.cast_mul]

omit [NeZero W] in
include hH in
/-- **Row `|M_{y,αβ}|`, crude form.** `|M_{y,αβ}| ≤ N ∑_x s_x |u_α(x)||u_β(x)|`,
`s_x = S_{xy} + N⁻¹`. -/
private theorem l2_norm_blockM2_le (hL : 3 ≤ L) (a0 : ZMod L) (β0 : Fin W)
    (α β : ZMod L × Fin W) :
    ‖blockM2 hH a0 α β‖ ≤ (L * W : ℝ) * ∑ x, (Sblk L W x (a0, β0) + (L * W : ℝ)⁻¹) *
      (‖hH.eigenvectorBasis α x‖ * ‖hH.eigenvectorBasis β x‖) := by
  rw [l2_blockM2_eq hH hL a0 β0 α β, norm_mul, Complex.norm_natCast, Nat.cast_mul]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
  refine Finset.sum_le_sum fun x _ => ?_
  rw [norm_mul, norm_mul, norm_star, mul_comm]
  exact mul_le_mul_of_nonneg_right (l2_centered_profile_norm_le x (a0, β0)) (by positivity)

private theorem l2_sum_profile_eq (hL : 3 ≤ L) (y : ZMod L × Fin W) :
    ∑ x : ZMod L × Fin W, (Sblk L W x y + (L * W : ℝ)⁻¹) = 2 := by
  have hN : (0 : ℝ) < (L * W : ℝ) := by
    exact_mod_cast Nat.mul_pos (NeZero.pos L) (NeZero.pos W)
  rw [Finset.sum_add_distrib, sum_Sblk_col hL y, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  norm_num

end Block

/-- **Spectral form of the `L₂` kernel** ((2.30) with the pair moments kept):
`L₂(u₁,u₂) ≤ 4 N⁻² ∑_y N⁻¹ A_y`, `A_y = ∑_{α,β} |p₁α|²|p₂β|²|M_{y,αβ}||u_α(y)||u_β(y)|`,
for all four resolvent signs. -/
private theorem l2_paperL2Kernel_le_spectral (d : Gauss.Dims) (N : ℕ)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) {u₁ u₂ : ℂ} (hη₁ : 0 < u₁.im)
    (hη₂ : 0 < u₂.im) :
    paperL2Kernel d N H u₁ u₂ ≤
      4 * ((d.L N * d.W N : ℝ)⁻¹ * ((d.L N * d.W N : ℝ)⁻¹ *
        ∑ y : d.Idx N, (d.L N * d.W N : ℝ)⁻¹ *
          ∑ α, ∑ β, ‖spectralPole hH u₁ α‖ ^ 2 * ‖spectralPole hH u₂ β‖ ^ 2 *
            ‖blockM2 hH y.1 α β‖ *
              (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖))) := by
  have hL : 3 ≤ d.L N := d.three_le_L N
  have hcard : (Fintype.card (d.Idx N) : ℂ) = ((d.L N * d.W N : ℕ) : ℂ) := by
    simp [Fintype.card_prod, ZMod.card]
  set B : ℝ := (d.L N * d.W N : ℝ)⁻¹ * ((d.L N * d.W N : ℝ)⁻¹ *
        ∑ y : d.Idx N, (d.L N * d.W N : ℝ)⁻¹ *
          ∑ α, ∑ β, ‖spectralPole hH u₁ α‖ ^ 2 * ‖spectralPole hH u₂ β‖ ^ 2 *
            ‖blockM2 hH y.1 α β‖ *
              (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖)) with hB
  have hterm : ∀ σ τ : Bool,
      ‖(Fintype.card (d.Idx N) : ℂ)⁻¹ * (Fintype.card (d.Idx N) : ℂ)⁻¹ *
        ∑ a : d.Idx N, ∑ b : d.Idx N,
          ((signedGreen H u₁ σ * signedGreen H u₁ σ) a b) *
            (centeredVarianceEntry d N a b : ℂ) *
            ((signedGreen H u₂ τ * signedGreen H u₂ τ) b a)‖ ≤ B := by
    intro σ τ
    have hsg : ∀ (z : ℂ) (ς : Bool), signedGreen H z ς = Gsig H z ς := by
      intro z ς; cases ς <;> rfl
    have hcv : ∀ a b : d.Idx N, (centeredVarianceEntry d N a b : ℂ) =
        Svar (d.L N) (d.W N) a b - ((d.L N * d.W N : ℕ) : ℂ)⁻¹ := by
      intro a b
      rw [centeredVarianceEntry, Svar_eq_ofReal]
      push_cast
      rw [hcard]
      push_cast
      ring
    rw [hcard, norm_mul, norm_mul, norm_inv, Complex.norm_natCast, Finset.sum_comm]
    push_cast
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
    refine Finset.sum_le_sum fun y _ => ?_
    obtain ⟨a0, β0⟩ := y
    have heq : (∑ x : d.Idx N, (signedGreen H u₁ σ * signedGreen H u₁ σ) x (a0, β0) *
        (centeredVarianceEntry d N x (a0, β0) : ℂ) *
          (signedGreen H u₂ τ * signedGreen H u₂ τ) (a0, β0) x) =
        ∑ x : ZMod (d.L N) × Fin (d.W N), (Gsig H u₁ σ ^ 2) x (a0, β0) *
          (Svar (d.L N) (d.W N) x (a0, β0) - ((d.L N * d.W N : ℕ) : ℂ)⁻¹) *
          (Gsig H u₂ τ ^ 2) (a0, β0) x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hsg, hsg, hcv, pow_two, pow_two]
    rw [heq, green_spectral_identity_blockM2 hH hL a0 β0 u₁ u₂ hη₁ hη₂ σ τ, norm_mul, norm_inv,
      Complex.norm_natCast]
    push_cast
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
    refine Finset.sum_le_sum fun α _ => (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_star,
      spectralGsigPole_norm_eq_spectralPole, spectralGsigPole_norm_eq_spectralPole]
    ring
  unfold paperL2Kernel
  calc _ ≤ ∑ _σ : Bool, ∑ _τ : Bool, B :=
        Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => hterm σ τ
    _ = 4 * B := by simp; ring

private theorem l2_card_idx (d : Gauss.Dims) (N : ℕ) :
    (Fintype.card (d.Idx N) : ℝ) = (d.L N * d.W N : ℝ) := by
  simp [Fintype.card_prod, ZMod.card]

/-- Nonnegativity of `L₂`. -/
private theorem l2_paperL2Kernel_nonneg (d : Gauss.Dims) (N : ℕ)
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) (u₁ u₂ : ℂ) : 0 ≤ paperL2Kernel d N H u₁ u₂ := by
  unfold paperL2Kernel
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem l2_ite_abs_neg_one (x t : ℝ) : (if |x| ≤ -1 then (0 : ℝ) else t) = t := by
  have h : ¬ |x| ≤ -1 := by linarith [abs_nonneg x]
  simp [h]

/-- **The `A_y` row.** For a window radius `w'` (take `w' < 0` for no window), with window pairs
bounded by `θ`: `A_y ≤ (θ/2)(q₁ N q₂ + N q₁ q₂) + 2N(o₁q₂ + q₁o₂)`. -/
private theorem l2_A_le (d : Gauss.Dims) (N : ℕ) {H : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hH : H.IsHermitian) (u₁ u₂ : ℂ) (y : d.Idx N) {θ q₁ q₂ o₁ o₂ w' : ℝ} (hθ : 0 ≤ θ)
    (hMw : ∀ α β, |hH.eigenvalues α - u₁.re| ≤ w' → |hH.eigenvalues β - u₂.re| ≤ w' →
      ‖blockM2 hH y.1 α β‖ ≤ θ)
    (hq₁ : ∀ z, ∑ α, ‖spectralPole hH u₁ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ q₁)
    (hq₂ : ∀ z, ∑ α, ‖spectralPole hH u₂ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ q₂)
    (ho₁ : ∀ z, ∑ α, (if |hH.eigenvalues α - u₁.re| ≤ w' then 0 else
      ‖spectralPole hH u₁ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2) ≤ o₁)
    (ho₂ : ∀ z, ∑ α, (if |hH.eigenvalues α - u₂.re| ≤ w' then 0 else
      ‖spectralPole hH u₂ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2) ≤ o₂) :
    ∑ α, ∑ β, ‖spectralPole hH u₁ α‖ ^ 2 * ‖spectralPole hH u₂ β‖ ^ 2 *
        ‖blockM2 hH y.1 α β‖ * (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖) ≤
      θ / 2 * (q₁ * ((d.L N * d.W N : ℝ) * q₂) + ((d.L N * d.W N : ℝ) * q₁) * q₂) +
        2 * (d.L N * d.W N : ℝ) * (o₁ * q₂ + q₁ * o₂) := by
  have hL : 3 ≤ d.L N := d.three_le_L N
  have hS : ∀ (u : ℂ) (q : ℝ),
      (∀ z, ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ q) →
      ∑ α, ‖spectralPole hH u α‖ ^ 2 ≤ (d.L N * d.W N : ℝ) * q := by
    intro u q hq
    rw [l2_sum_pole_sq_eq hH u]
    calc _ ≤ ∑ _z : d.Idx N, q := Finset.sum_le_sum fun z _ => hq z
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, l2_card_idx]
  obtain ⟨a0, β0⟩ := y
  refine l2_pair_abstract (fun α => ‖spectralPole hH u₁ α‖ ^ 2)
    (fun α => ‖spectralPole hH u₂ α‖ ^ 2) (fun γ x => ‖hH.eigenvectorBasis γ x‖)
    (fun α β => ‖blockM2 hH a0 α β‖)
    (fun x => Sblk (d.L N) (d.W N) x (a0, β0) + (d.L N * d.W N : ℝ)⁻¹) (a0, β0)
    (fun α => |hH.eigenvalues α - u₁.re| ≤ w') (fun β => |hH.eigenvalues β - u₂.re| ≤ w')
    (fun α => by positivity) (fun α => by positivity) (fun α x => norm_nonneg _)
    (fun x => add_nonneg (Sblk_nonneg _ _) (by positivity))
    (le_of_eq (l2_sum_profile_eq hL (a0, β0))) (by positivity) hθ
    (fun α β => l2_norm_blockM2_le hH hL a0 β0 α β) (fun α β h1 h2 => hMw α β h1 h2)
    hq₁ hq₂ ho₁ ho₂ (hS u₁ q₁ hq₁) (hS u₂ q₂ hq₂)

open Step3KernelBounds in
/-- **Pointwise bound on the good event.** On the single-scale grid event, with window pairs
bounded by `θ` off the blocks flagged `Bad`, the weighted kernel is bounded by the product of the
`Im m` rows times `4 N⁻² ∑_y N⁻¹ (A_good + 1_{Bad} A_bad)`. -/
private theorem l2_pointwise_good (d : Gauss.Dims) (N : ℕ)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u₁ u₂ : ℂ) {ηt Cb w' θ Ag Ab : ℝ} (hη₁ : 0 < u₁.im) (hη₁' : u₁.im ≤ ηt)
    (hη₂ : 0 < u₂.im) (hη₂' : u₂.im ≤ ηt)
    (hηw : ∀ j, 0 < (w j).im) (hηw' : ∀ j, (w j).im ≤ ηt) (hCb : 0 ≤ Cb) (hw' : 0 < w')
    (hθ : 0 ≤ θ) (K' : ℕ)
    (hG1 : ∀ k ≤ K', GridGood H ηt Cb u₁.re (2 ^ k * w'))
    (hG2 : ∀ k ≤ K', GridGood H ηt Cb u₂.re (2 ^ k * w'))
    (hG3 : GridGood H ηt Cb u₁.re 0) (hG4 : GridGood H ηt Cb u₂.re 0)
    (hG5 : ∀ j, GridGood H ηt Cb (w j).re 0)
    (Bad : ZMod (d.L N) → Prop) [DecidablePred Bad]
    (hBad : ∀ a0, ¬ Bad a0 → ∀ α β, |hH.eigenvalues α - u₁.re| ≤ w' →
      |hH.eigenvalues β - u₂.re| ≤ w' → ‖blockM2 hH a0 α β‖ ≤ θ)
    (hAg : θ / 2 * ((ηt / u₁.im ^ 2 * Cb) * ((d.L N * d.W N : ℝ) * (ηt / u₂.im ^ 2 * Cb)) +
        ((d.L N * d.W N : ℝ) * (ηt / u₁.im ^ 2 * Cb)) * (ηt / u₂.im ^ 2 * Cb)) +
      2 * (d.L N * d.W N : ℝ) *
        ((Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹) * (ηt / u₂.im ^ 2 * Cb) +
          (ηt / u₁.im ^ 2 * Cb) * (Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹)) ≤
      Ag)
    (hAb : 4 * (d.L N * d.W N : ℝ) * ((ηt / u₁.im ^ 2 * Cb) * (ηt / u₂.im ^ 2 * Cb)) ≤ Ab) :
    (∏ j ∈ s, (stieltjes H (w j)).im) * paperL2Kernel d N H u₁ u₂ ≤
      (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        (4 * ((d.L N * d.W N : ℝ)⁻¹ * ((d.L N * d.W N : ℝ)⁻¹ *
          ∑ y : d.Idx N, (d.L N * d.W N : ℝ)⁻¹ * (Ag + (if Bad y.1 then Ab else 0))))) := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη₁ hη₁'
  have hN : (0 : ℝ) < (d.L N * d.W N : ℝ) := by
    exact_mod_cast Nat.mul_pos (NeZero.pos (d.L N)) (NeZero.pos (d.W N))
  have hP : (∏ j ∈ s, (stieltjes H (w j)).im) ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) := by
    refine Finset.prod_le_prod₀ (fun j _ => (l2_stieltjes_im_nonneg_le hH (hηw j)).1)
      fun j _ => l2_stieltjes_im_le_of_grid hH (hηw j) (hηw' j) (hG5 j)
  have hP0 : 0 ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) :=
    Finset.prod_nonneg fun j _ => mul_nonneg (div_nonneg hηt.le (hηw j).le) hCb
  have hq₁ := l2_sum_pole_sq_mass_le_of_grid hH hη₁ hη₁' hG3
  have hq₂ := l2_sum_pole_sq_mass_le_of_grid hH hη₂ hη₂' hG4
  have ho₁ := l2_sum_pole_sq_mass_out_le hH hηt hCb hw' K' hG1
  have ho₂ := l2_sum_pole_sq_mass_out_le hH hηt hCb hw' K' hG2
  have hq₁0 : 0 ≤ ηt / u₁.im ^ 2 * Cb := by positivity
  have hq₂0 : 0 ≤ ηt / u₂.im ^ 2 * Cb := by positivity
  have hAb0 : 0 ≤ Ab := le_trans (by positivity) hAb
  have hA : ∀ y : d.Idx N, ∑ α, ∑ β, ‖spectralPole hH u₁ α‖ ^ 2 * ‖spectralPole hH u₂ β‖ ^ 2 *
      ‖blockM2 hH y.1 α β‖ * (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖) ≤
        Ag + (if Bad y.1 then Ab else 0) := by
    intro y
    by_cases hb : Bad y.1
    · simp only [hb, ite_true]
      -- no window: `w' = -1`
      have h := l2_A_le d N hH u₁ u₂ y (θ := 0) (w' := -1) le_rfl
        (fun α β h1 _ => absurd h1 (by linarith [abs_nonneg (hH.eigenvalues α - u₁.re)]))
        hq₁ hq₂ (o₁ := ηt / u₁.im ^ 2 * Cb) (o₂ := ηt / u₂.im ^ 2 * Cb)
        (fun z => by simp_rw [l2_ite_abs_neg_one]; exact hq₁ z)
        (fun z => by simp_rw [l2_ite_abs_neg_one]; exact hq₂ z)
      have hAg0 : 0 ≤ Ag := le_trans (by positivity) hAg
      nlinarith
    · simp only [hb, ite_false, add_zero]
      exact (l2_A_le d N hH u₁ u₂ y hθ (hBad y.1 hb) hq₁ hq₂ ho₁ ho₂).trans hAg
  have hK := l2_paperL2Kernel_le_spectral d N hH hη₁ hη₂
  have hK' : paperL2Kernel d N H u₁ u₂ ≤
      4 * ((d.L N * d.W N : ℝ)⁻¹ * ((d.L N * d.W N : ℝ)⁻¹ *
        ∑ y : d.Idx N, (d.L N * d.W N : ℝ)⁻¹ * (Ag + (if Bad y.1 then Ab else 0)))) := by
    refine hK.trans ?_
    gcongr with y
    exact hA y
  calc (∏ j ∈ s, (stieltjes H (w j)).im) * paperL2Kernel d N H u₁ u₂
      ≤ (∏ j ∈ s, (ηt / (w j).im * Cb)) * paperL2Kernel d N H u₁ u₂ :=
        mul_le_mul_of_nonneg_right hP (l2_paperL2Kernel_nonneg d N H u₁ u₂)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK' hP0

/-- **Crude pointwise bound**, valid for every sample: `∏ Im m(w_j) · L₂(u₁,u₂) ≤
∏ (Im w_j)⁻¹ · 16 (Im u₁)⁻² (Im u₂)⁻²`. -/
private theorem l2_pointwise_crude (d : Gauss.Dims) (N : ℕ)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u₁ u₂ : ℂ) (hη₁ : 0 < u₁.im) (hη₂ : 0 < u₂.im) (hηw : ∀ j, 0 < (w j).im) :
    (∏ j ∈ s, (stieltjes H (w j)).im) * paperL2Kernel d N H u₁ u₂ ≤
      (∏ j ∈ s, (w j).im⁻¹) * (16 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2)) := by
  have hN : (0 : ℝ) < (d.L N * d.W N : ℝ) := by
    exact_mod_cast Nat.mul_pos (NeZero.pos (d.L N)) (NeZero.pos (d.W N))
  have hP : (∏ j ∈ s, (stieltjes H (w j)).im) ≤ ∏ j ∈ s, (w j).im⁻¹ :=
    Finset.prod_le_prod₀ (fun j _ => (l2_stieltjes_im_nonneg_le hH (hηw j)).1)
      fun j _ => (l2_stieltjes_im_nonneg_le hH (hηw j)).2
  have hP0 : 0 ≤ ∏ j ∈ s, (w j).im⁻¹ := Finset.prod_nonneg fun j _ => (inv_pos.2 (hηw j)).le
  have hq₁ := l2_sum_pole_sq_mass_le_crude hH hη₁
  have hq₂ := l2_sum_pole_sq_mass_le_crude hH hη₂
  have hA : ∀ y : d.Idx N, ∑ α, ∑ β, ‖spectralPole hH u₁ α‖ ^ 2 * ‖spectralPole hH u₂ β‖ ^ 2 *
      ‖blockM2 hH y.1 α β‖ * (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖) ≤
        4 * (d.L N * d.W N : ℝ) * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2) := by
    intro y
    have h := l2_A_le d N hH u₁ u₂ y (θ := 0) (w' := -1) le_rfl
      (fun α β h1 _ => absurd h1 (by linarith [abs_nonneg (hH.eigenvalues α - u₁.re)]))
      hq₁ hq₂ (o₁ := (u₁.im⁻¹) ^ 2) (o₂ := (u₂.im⁻¹) ^ 2)
      (fun z => by simp_rw [l2_ite_abs_neg_one]; exact hq₁ z)
      (fun z => by simp_rw [l2_ite_abs_neg_one]; exact hq₂ z)
    nlinarith
  have hK' : paperL2Kernel d N H u₁ u₂ ≤ 16 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2) := by
    refine (l2_paperL2Kernel_le_spectral d N hH hη₁ hη₂).trans ?_
    calc _ ≤ 4 * ((d.L N * d.W N : ℝ)⁻¹ * ((d.L N * d.W N : ℝ)⁻¹ *
          ∑ _y : d.Idx N, (d.L N * d.W N : ℝ)⁻¹ *
            (4 * (d.L N * d.W N : ℝ) * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2)))) := by
          gcongr with y
          exact hA y
      _ = 16 * (d.L N * d.W N : ℝ)⁻¹ * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, l2_card_idx]
          field_simp
          ring
      _ ≤ 16 * 1 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2) := by
          have h1 : (1 : ℝ) ≤ (d.L N * d.W N : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.2
              (Nat.mul_ne_zero (NeZero.ne (d.L N)) (NeZero.ne (d.W N)))
          gcongr
          exact inv_le_one_of_one_le₀ h1
      _ = _ := by ring
  calc _ ≤ (∏ j ∈ s, (w j).im⁻¹) * paperL2Kernel d N H u₁ u₂ :=
        mul_le_mul_of_nonneg_right hP (l2_paperL2Kernel_nonneg d N H u₁ u₂)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK' hP0

end RBM

/-! ### Probabilistic inputs on the common carrier -/

namespace RBM.Gauss

open RBM RBM.Step3KernelBounds

private theorem l2_measurable_green (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ) (x y : d.Idx N) :
    Measurable fun ω => green ((ouCommonFlow d).Ht N t ω) z x y := by
  have hH := ouCommonFlow_measurable d N t
  have hM : Measurable fun ω => (ouCommonFlow d).Ht N t ω -
      z • (1 : Matrix ((ouCommonBand d).Idx N) ((ouCommonBand d).Idx N) ℂ) :=
    Measurable.of_eval_matrix _ fun a b => by
      simp only [Matrix.sub_apply]
      exact hH.eval_matrix.sub measurable_const
  exact Gauss.measurable_matrix_inv_apply hM x y

private theorem l2_norm_green_le {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
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

/-- Markov for one resolvent entry. -/
private theorem l2_prob_im_green_gt (d : Dims) (N : ℕ) (t : ℝ) {z : ℂ} (hz : 0 < z.im)
    (x : d.Idx N) (p : ℕ) {Cb M : ℝ} (hCb : 0 < Cb)
    (hM : ∫ ω, ‖green ((ouCommonFlow d).Ht N t ω) z x x‖ ^ (2 * p) ∂(ouCommonMeasure d) ≤ M) :
    (ouCommonMeasure d).real {ω | Cb < (green ((ouCommonFlow d).Ht N t ω) z x x).im} ≤
      M / Cb ^ (2 * p) := by
  set f : ouCommonOmega d → ℝ := fun ω => ‖green ((ouCommonFlow d).Ht N t ω) z x x‖ ^ (2 * p)
  have hfm : Measurable f := ((l2_measurable_green d N t z x x).norm).pow_const _
  have hfi : Integrable f (ouCommonMeasure d) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable ((z.im⁻¹) ^ (2 * p)) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (l2_norm_green_le ((ouCommonFlow d).hermitian N t ω) hz x) _
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
private theorem l2_prob_not_gridGood (d : Dims) (N : ℕ) (t : ℝ) {ηt Cb E₀ r M : ℝ}
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
          l2_prob_im_green_gt d N t (hz j) x p hCb (hM j hj x)
    _ = _ := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Union bound over a finite family `S` of covering grids `(centre, radius)`. -/
private theorem l2_prob_not_gridGood_finset (d : Dims) (N : ℕ) (t : ℝ) {ηt Cb M : ℝ}
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
        refine (l2_prob_not_gridGood d N t hηt hCb p (hM q hq)).trans ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hG q hq) hC
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The pair bad event `B̃_{a₀}` of (2.30)**, uniformly in `t ∈ (0, t_U]`, from `FlowEq747`
(pair form of `measure_bad_flow_of_eq747`: `que_flow_of_eq747` along every time sequence, then
`measure_bad2_le_of_que`, then uniformization). -/
private theorem l2_bad2_uniform (d : Dims) {κ τU : ℝ} (hκ : 0 < κ) (hτc : τU < d.c / 3)
    (hQUE : FlowEq747 d κ τU) (E : ℝ) (hE : |E| ≤ 2 - κ) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Ioc (0 : ℝ) ((ouCommonBand d).tPow τU N),
      ∀ a0 : ZMod ((ouCommonBand d).L N),
        (ouCommonBand d).P {ω | ∃ α β,
          |((ouCommonFlow d).hermitian N t ω).eigenvalues α - E| ≤
            ((ouCommonBand d).size N : ℝ) ^ (-1 + (ouCommonBand d).c / 6) ∧
          |((ouCommonFlow d).hermitian N t ω).eigenvalues β - E| ≤
            ((ouCommonBand d).size N : ℝ) ^ (-1 + (ouCommonBand d).c / 6) ∧
          ((ouCommonBand d).size N : ℝ) ^ (-((ouCommonBand d).c / 36)) ≤
            ‖blockM2 ((ouCommonFlow d).hermitian N t ω) a0 α β‖} ≤
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
    have hζt : ouZeta (sq N) ≤ sq N := by
      unfold ouZeta; linarith [Real.add_one_le_exp (-sq N)]
    have hζ0 : 0 < ouZeta (sq N) := by
      unfold ouZeta; linarith [Real.exp_lt_one_iff.2 (by linarith : -sq N < 0)]
    have htU : sq N ≤ (B.size N : ℝ) ^ (-1 + τU) := (hsq N).2
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
  have hque := (que_flow_of_eq747 (ouCommonFlow d) hκ sq (fun _ => E) (fun _ => hE)
    (fun N => ouZeta (sq N)) hζ h747).1
  filter_upwards [hque, B.eventually_size_rpow_le_W_sq] with N hN hWc a0
  have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
  have hn0 : (0 : ℝ) < (B.size N : ℝ) := by linarith
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hw : (B.size N : ℝ) ^ (-1 + B.c / 6) ≤ B.queEtaN (B.c / 3) N := by
    refine le_trans ?_ (rpow_le_queEta hn1 hW0 hWc)
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hθ : ((B.size N : ℝ) ^ (-(B.c / 36))) ^ 2 = (B.size N : ℝ) ^ (-(B.c / 3 / 6)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; push_cast; ring
  have e18 : (B.size N : ℝ) ^ (-(B.c / 18)) = (B.size N : ℝ) ^ (-(B.c / 3 / 6)) := by
    congr 1; ring
  rw [e18]
  refine measure_bad2_le_of_que ((ouCommonFlow d).hermitian N (sq N)) hw (by positivity) a0
    fun a => ?_
  rw [hθ]
  exact hN a

/-! ### Exponent bookkeeping (§2.2 rows for `L₂`), pure real arithmetic -/

private theorem l2_exists_dyadic {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
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
private theorem l2_c_lt_half (d : Dims) : d.c < 1 / 2 := by
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

private theorem l2_rpow_mul {X : ℝ} (hX : 0 < X) (a b : ℝ) : X ^ a * X ^ b = X ^ (a + b) :=
  (Real.rpow_add hX a b).symm

/-- Row `Q_i`: `(η̃/η²) N^δ ≤ N^{1+4τ+δ}`. -/
private theorem l2_q_le {X τ δ η ηt : ℝ} (hX : 1 ≤ X) (hηt : ηt = X ^ (-1 + 2 * τ))
    (hη : X ^ (-1 - τ) ≤ η) : ηt / η ^ 2 * X ^ δ ≤ X ^ (1 + 4 * τ + δ) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  have hq : ηt / η ^ 2 ≤ X ^ (1 + 4 * τ) := by
    have hsq : X ^ (-1 - τ) * X ^ (-1 - τ) ≤ η ^ 2 := by
      rw [sq]; exact mul_le_mul hη hη (by positivity) hη0.le
    calc ηt / η ^ 2 ≤ ηt / (X ^ (-1 - τ) * X ^ (-1 - τ)) :=
          div_le_div_of_nonneg_left hηt0.le (by positivity) hsq
      _ = X ^ (1 + 4 * τ) := by
          rw [l2_rpow_mul hX0, hηt, ← Real.rpow_sub hX0]; congr 1; ring
  calc ηt / η ^ 2 * X ^ δ ≤ X ^ (1 + 4 * τ) * X ^ δ := by gcongr
    _ = X ^ (1 + 4 * τ + δ) := l2_rpow_mul hX0 _ _

/-- Row `Q_i^out`: `N^δ(8/w' + 8η̃/w'²) + (2^{K'}w')⁻² ≤ (48 + 64/κ²) N^{1-c/6+2τ+δ}`. -/
private theorem l2_o_le {X c τ δ κ ηt w' : ℝ} {K' : ℕ} (hX : 1 ≤ X) (hc : 0 < c)
    (hc2 : c < 1 / 2) (hτ : 0 < τ) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hηt : ηt = X ^ (-1 + 2 * τ)) (hw' : w' = (2 * X ^ (1 - c / 6))⁻¹)
    (hK2 : κ / 4 < 2 ^ (K' + 1) * w') :
    X ^ δ * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹ ≤
      (48 + 64 / κ ^ 2) * X ^ (1 - c / 6 + 2 * τ + δ) := by
  have hX0 : 0 < X := by linarith
  set E₁ : ℝ := 1 - c / 6 + 2 * τ + δ with hE₁
  have hw0 : 0 < w' := by rw [hw']; positivity
  have hwi : 8 / w' = 16 * X ^ (1 - c / 6) := by rw [hw']; field_simp; ring
  have hwi2 : 8 * ηt / w' ^ 2 = 32 * X ^ (1 + 2 * τ - c / 3) := by
    rw [hw', hηt]
    have : X ^ (1 + 2 * τ - c / 3) = X ^ (-1 + 2 * τ) * (X ^ (1 - c / 6) * X ^ (1 - c / 6)) := by
      rw [l2_rpow_mul hX0, l2_rpow_mul hX0]; congr 1; ring
    rw [this]; field_simp; ring
  have ht1 : X ^ δ * (8 / w' + 8 * ηt / w' ^ 2) ≤ 48 * X ^ E₁ := by
    rw [hwi, hwi2]
    have e1 : X ^ δ * (16 * X ^ (1 - c / 6) + 32 * X ^ (1 + 2 * τ - c / 3)) =
        16 * X ^ (δ + (1 - c / 6)) + 32 * X ^ (δ + (1 + 2 * τ - c / 3)) := by
      rw [← l2_rpow_mul hX0, ← l2_rpow_mul hX0]; ring
    rw [e1]
    have f1 : X ^ (δ + (1 - c / 6)) ≤ X ^ E₁ :=
      Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
    have f2 : X ^ (δ + (1 + 2 * τ - c / 3)) ≤ X ^ E₁ :=
      Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
    linarith
  have ht2 : ((2 ^ K' * w') ^ 2)⁻¹ ≤ 64 / κ ^ 2 * X ^ E₁ := by
    have hb : κ / 8 < 2 ^ K' * w' := by rw [pow_succ] at hK2; linarith
    have hb2 : ((2 ^ K' * w') ^ 2)⁻¹ ≤ 64 / κ ^ 2 := by
      rw [inv_le_comm₀ (by positivity) (by positivity)]
      rw [show (64 / κ ^ 2)⁻¹ = (κ / 8) ^ 2 by field_simp; norm_num]
      exact pow_le_pow_left₀ (by positivity) hb.le 2
    have hXE : (1 : ℝ) ≤ X ^ E₁ := Real.one_le_rpow hX (by rw [hE₁]; linarith)
    calc _ ≤ 64 / κ ^ 2 := hb2
      _ ≤ 64 / κ ^ 2 * X ^ E₁ := le_mul_of_one_le_right (by positivity) hXE
  linarith

/-- Row `A_y`, good: `θ N q₁ q₂ + 2N(o q₂ + q₁ o) ≤ (193 + 256/κ²) N^{3-c/36+8τ+2δ}`. -/
private theorem l2_Ag_le {X c τ δ κ θ q₁ q₂ o : ℝ} (hX : 1 ≤ X) (hc : 0 < c) (hτ : 0 < τ)
    (hκ : 0 < κ) (hθ : θ = X ^ (-(c / 36)))
    (hq₁ : q₁ ≤ X ^ (1 + 4 * τ + δ)) (hq₂0 : 0 ≤ q₂)
    (hq₂ : q₂ ≤ X ^ (1 + 4 * τ + δ)) (ho0 : 0 ≤ o)
    (ho : o ≤ (48 + 64 / κ ^ 2) * X ^ (1 - c / 6 + 2 * τ + δ)) :
    θ / 2 * (q₁ * (X * q₂) + (X * q₁) * q₂) + 2 * X * (o * q₂ + q₁ * o) ≤
      (193 + 256 / κ ^ 2) * X ^ (3 - c / 36 + 8 * τ + 2 * δ) := by
  have hX0 : 0 < X := by linarith
  set E₁ : ℝ := 3 - c / 36 + 8 * τ + 2 * δ with hE₁
  set R : ℝ := X ^ (1 + 4 * τ + δ)
  set Co : ℝ := 48 + 64 / κ ^ 2
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hq12 : q₁ * q₂ ≤ R * R := mul_le_mul hq₁ hq₂ hq₂0 (by positivity)
  have hoq₂ : o * q₂ ≤ Co * X ^ (1 - c / 6 + 2 * τ + δ) * R :=
    mul_le_mul ho hq₂ hq₂0 (by positivity)
  have hq₁o : q₁ * o ≤ R * (Co * X ^ (1 - c / 6 + 2 * τ + δ)) :=
    mul_le_mul hq₁ ho ho0 (by positivity)
  have e1 : θ / 2 * (q₁ * (X * q₂) + (X * q₁) * q₂) = θ * X * (q₁ * q₂) := by ring
  have f1 : θ * X * (R * R) ≤ X ^ E₁ := by
    rw [hθ]
    have : X ^ (-(c / 36)) * X * (R * R) =
        X ^ (-(c / 36) + 1 + (1 + 4 * τ + δ) + (1 + 4 * τ + δ)) := by
      simp only [R, ← l2_rpow_mul hX0, Real.rpow_one]; ring
    rw [this]
    exact le_of_eq (by congr 1; rw [hE₁]; ring)
  have f2 : 2 * X * (Co * X ^ (1 - c / 6 + 2 * τ + δ) * R + R * (Co * X ^ (1 - c / 6 + 2 * τ + δ)))
      ≤ 4 * Co * X ^ E₁ := by
    have : 2 * X * (Co * X ^ (1 - c / 6 + 2 * τ + δ) * R + R * (Co * X ^ (1 - c / 6 + 2 * τ + δ)))
        = 4 * Co * X ^ ((1 : ℝ) + (1 - c / 6 + 2 * τ + δ) + (1 + 4 * τ + δ)) := by
      simp only [R, ← l2_rpow_mul hX0, Real.rpow_one]; ring
    rw [this]
    have hCo : 0 ≤ Co := by positivity
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)) (by positivity)
  have g1 : θ * X * (q₁ * q₂) ≤ θ * X * (R * R) :=
    mul_le_mul_of_nonneg_left hq12 (by positivity)
  have g2 : 2 * X * (o * q₂ + q₁ * o) ≤
      2 * X * (Co * X ^ (1 - c / 6 + 2 * τ + δ) * R + R * (Co * X ^ (1 - c / 6 + 2 * τ + δ))) := by
    gcongr
  rw [e1]
  have : (193 + 256 / κ ^ 2) * X ^ E₁ = X ^ E₁ + 4 * Co * X ^ E₁ := by simp only [Co]; ring
  linarith

/-- Row `A_y`, bad block: `4N q₁ q₂ ≤ 4 N^{3+8τ+2δ}`. -/
private theorem l2_Ab_le {X τ δ q₁ q₂ : ℝ} (hX : 1 ≤ X)
    (hq₁ : q₁ ≤ X ^ (1 + 4 * τ + δ)) (hq₂0 : 0 ≤ q₂) (hq₂ : q₂ ≤ X ^ (1 + 4 * τ + δ)) :
    4 * X * (q₁ * q₂) ≤ 4 * X ^ (3 + 8 * τ + 2 * δ) := by
  have hX0 : 0 < X := by linarith
  have h := mul_le_mul hq₁ hq₂ hq₂0 (by positivity)
  calc 4 * X * (q₁ * q₂) ≤ 4 * X * (X ^ (1 + 4 * τ + δ) * X ^ (1 + 4 * τ + δ)) := by gcongr
    _ = 4 * X ^ ((1 : ℝ) + (1 + 4 * τ + δ) + (1 + 4 * τ + δ)) := by
        simp only [← l2_rpow_mul hX0, Real.rpow_one]; ring
    _ = 4 * X ^ (3 + 8 * τ + 2 * δ) := by congr 2; ring

/-- **Assembly of the good part**: `P̄·4N⁻²A_good + P̄·4N⁻³A_bad·N·3N^{-c/18} ≤
½ N^{1-c/36+(3|s|+16)τ}` once `8(C₁+12) ≤ N^{6τ}`, with `(m+3)δ ≤ τ`. -/
private theorem l2_good_total_le {X c τ δ C₁ : ℝ} {sc m : ℕ} (hX : 1 ≤ X) (hc : 0 ≤ c)
    (hτ : 0 < τ) (hδ : 0 ≤ δ) (hC₁ : 0 ≤ C₁) (hsc : sc ≤ m)
    (hmδ : ((m : ℝ) + 3) * δ ≤ τ) (hslack : 8 * (C₁ + 12) ≤ X ^ (6 * τ)) :
    X ^ ((3 * τ + δ) * sc) * (4 * X⁻¹ * X⁻¹ * (C₁ * X ^ (3 - c / 36 + 8 * τ + 2 * δ))) +
      X ^ ((3 * τ + δ) * sc) * (4 * X⁻¹ * X⁻¹ * X⁻¹ * (4 * X ^ (3 + 8 * τ + 2 * δ))) *
        (X * (3 * X ^ (-(c / 18)))) ≤
      1 / 2 * X ^ (1 - c / 36 + (3 * (sc : ℝ) + 16) * τ) := by
  have hX0 : 0 < X := by linarith
  set T : ℝ := 1 - c / 36 + (3 * (sc : ℝ) + 16) * τ with hT
  have hsc' : (sc : ℝ) ≤ m := by exact_mod_cast hsc
  set a : ℝ := (3 * τ + δ) * sc
  set e : ℝ := 3 - c / 36 + 8 * τ + 2 * δ
  set f : ℝ := 3 + 8 * τ + 2 * δ
  set g : ℝ := -(c / 18)
  have r1 : X ^ (a + e - 2) = X ^ a * X ^ e / X / X := by
    rw [show a + e - 2 = a + e - 1 - 1 by ring, Real.rpow_sub hX0, Real.rpow_sub hX0,
      Real.rpow_add hX0 a e, Real.rpow_one]
  have r2 : X ^ (a + f + g - 2) = X ^ a * X ^ f * X ^ g / X / X := by
    rw [show a + f + g - 2 = a + f + g - 1 - 1 by ring, Real.rpow_sub hX0, Real.rpow_sub hX0,
      Real.rpow_add hX0 (a + f) g, Real.rpow_add hX0 a f, Real.rpow_one]
  have e1 : X ^ a * (4 * X⁻¹ * X⁻¹ * (C₁ * X ^ e)) = 4 * C₁ * X ^ (a + e - 2) := by
    rw [r1]
    generalize X ^ a = A
    generalize X ^ e = Ee
    field_simp
  have e2 : X ^ a * (4 * X⁻¹ * X⁻¹ * X⁻¹ * (4 * X ^ f)) * (X * (3 * X ^ g)) =
      48 * X ^ (a + f + g - 2) := by
    rw [r2]
    generalize X ^ a = A
    generalize X ^ f = F
    generalize X ^ g = G
    field_simp
    ring
  rw [e1, e2]
  have hsd : (sc + 3 : ℝ) * δ ≤ τ := le_trans (by gcongr) hmδ
  have f1 : X ^ (a + e - 2) ≤ X ^ (T - 6 * τ) := by
    refine Real.rpow_le_rpow_of_exponent_le hX ?_
    simp only [a, e, hT]
    nlinarith
  have f2 : X ^ (a + f + g - 2) ≤ X ^ (T - 6 * τ) := by
    refine Real.rpow_le_rpow_of_exponent_le hX ?_
    simp only [a, f, g, hT]
    nlinarith
  have hsplit : X ^ T = X ^ (T - 6 * τ) * X ^ (6 * τ) := by
    rw [l2_rpow_mul hX0]; congr 1; ring
  have hpos : 0 ≤ X ^ (T - 6 * τ) := by positivity
  calc 4 * C₁ * X ^ (a + e - 2) + 48 * X ^ (a + f + g - 2)
      ≤ 4 * C₁ * X ^ (T - 6 * τ) + 48 * X ^ (T - 6 * τ) := by gcongr
    _ = 1 / 2 * (8 * (C₁ + 12)) * X ^ (T - 6 * τ) := by ring
    _ ≤ 1 / 2 * X ^ (6 * τ) * X ^ (T - 6 * τ) := by gcongr
    _ = 1 / 2 * X ^ T := by rw [hsplit]; ring

/-- **Assembly of the crude part** (row `Ξᶜ`): with `2pδ ≥ (1+τ)(m+4) + 4 + δ`,
`16N^{(1+τ)(|s|+4)} · P(Ξᶜ) ≤ 32(3+m) N^{-1} ≤ ½ N^{1 - c/36 + (3|s|+16)τ}`. -/
private theorem l2_crude_total_le {X c τ δ : ℝ} {sc m p : ℕ} (hX : 1 ≤ X) (hτ : 0 < τ)
    (hc : c < 36) (hsc : sc ≤ m)
    (hp : (1 + τ) * ((m : ℝ) + 4) + 4 + δ ≤ 2 * p * δ) (hXm : 64 * (3 + (m : ℝ)) ≤ X) :
    16 * X ^ ((1 + τ) * ((sc : ℝ) + 4)) *
        ((3 + (m : ℝ)) * X * (2 * X * (X * (X ^ δ / (X ^ δ) ^ (2 * p))))) ≤
      1 / 2 * X ^ (1 - c / 36 + (3 * (sc : ℝ) + 16) * τ) := by
  have hX0 : 0 < X := by linarith
  have hsc' : (sc : ℝ) ≤ m := by exact_mod_cast hsc
  have hpow : (X ^ δ) ^ (2 * p) = X ^ (δ * (2 * p : ℕ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
  set a : ℝ := (1 + τ) * ((sc : ℝ) + 4)
  set b : ℝ := δ * (2 * p : ℕ)
  have r : X ^ (a + 1 + 1 + 1 + δ - b) = X ^ a * X * X * X * X ^ δ / X ^ b := by
    rw [Real.rpow_sub hX0, Real.rpow_add hX0 (a + 1 + 1 + 1) δ, Real.rpow_add hX0 (a + 1 + 1) 1,
      Real.rpow_add hX0 (a + 1) 1, Real.rpow_add hX0 a 1, Real.rpow_one]
  have e : 16 * X ^ a * ((3 + (m : ℝ)) * X * (2 * X * (X * (X ^ δ / (X ^ δ) ^ (2 * p))))) =
      32 * (3 + (m : ℝ)) * X ^ (a + 1 + 1 + 1 + δ - b) := by
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
  have h2 : 32 * (3 + (m : ℝ)) * X⁻¹ ≤ 1 / 2 := by
    rw [mul_inv_le_iff₀ hX0]; linarith
  calc 32 * (3 + (m : ℝ)) * X ^ (a + 1 + 1 + 1 + δ - b)
      ≤ 32 * (3 + (m : ℝ)) * X⁻¹ := by gcongr
    _ ≤ 1 / 2 := h2
    _ ≤ _ := by linarith

/-- Row `Im m_t(w_j)`, product form: `∏_{j∈s} (η̃/Im w_j) N^δ ≤ N^{(3τ+δ)|s|}`. -/
private theorem l2_prod_row_le {X τ δ ηt : ℝ} (hX : 1 ≤ X) (hηt : ηt = X ^ (-1 + 2 * τ))
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

/-- Row `Ξᶜ`, crude weight: `∏_{j∈s} (Im w_j)⁻¹ · 16 (Im u₁)⁻²(Im u₂)⁻² ≤
16 N^{(1+τ)(|s|+4)}`. -/
private theorem l2_prod_crude_le {X τ : ℝ} (hX : 1 ≤ X) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u₁ u₂ : ℂ) (hw : ∀ j, X ^ (-1 - τ) ≤ (w j).im)
    (hu₁ : X ^ (-1 - τ) ≤ u₁.im) (hu₂ : X ^ (-1 - τ) ≤ u₂.im) :
    (∏ j ∈ s, (w j).im⁻¹) * (16 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2)) ≤
      16 * X ^ ((1 + τ) * ((s.card : ℝ) + 4)) := by
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
  have hU : ∀ {y : ℝ}, X ^ (-1 - τ) ≤ y → (y⁻¹) ^ 2 ≤ X ^ ((1 + τ) * 2) := by
    intro y hy
    calc (y⁻¹) ^ 2 ≤ (X ^ (1 + τ)) ^ 2 :=
          pow_le_pow_left₀ (inv_nonneg.2 (le_trans (by positivity) hy)) (hinv hy) 2
      _ = X ^ ((1 + τ) * 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hP0 : 0 ≤ ∏ j ∈ s, (w j).im⁻¹ :=
    Finset.prod_nonneg fun j _ => inv_nonneg.2 (le_trans (by positivity) (hw j))
  have hUU : (u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2 ≤ X ^ ((1 + τ) * 2) * X ^ ((1 + τ) * 2) :=
    mul_le_mul (hU hu₁) (hU hu₂) (by positivity) (by positivity)
  calc _ ≤ X ^ ((1 + τ) * (s.card : ℝ)) *
        (16 * (X ^ ((1 + τ) * 2) * X ^ ((1 + τ) * 2))) :=
        mul_le_mul hP (by linarith) (by positivity) (by positivity)
    _ = 16 * X ^ ((1 + τ) * ((s.card : ℝ) + 4)) := by
        rw [show (16 : ℝ) * X ^ ((1 + τ) * ((s.card : ℝ) + 4)) =
          16 * (X ^ ((1 + τ) * (s.card : ℝ)) * (X ^ ((1 + τ) * 2) * X ^ ((1 + τ) * 2))) by
          rw [l2_rpow_mul hX0, l2_rpow_mul hX0]; congr 2; ring]
        ring

/-- Grid energies stay in the local-law domain (acceptance (iv)). -/
private theorem l2_grid_energy_le {E E₀ κ C r ηt : ℝ} {j : ℕ} (hηt : 0 < ηt)
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

/-- Integration of a simple majorant (copy of a private helper of `Step3KernelBounds.lean`). -/
private theorem l2_integral_le_of_majorant {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
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
/-- **Fixed-time assembly** of `expect_L2_weighted_le` at one size `N`, one time `t`, and one
choice of `s, w, u₁, u₂`: all eventual conditions are passed as explicit numeric hypotheses. -/
private theorem l2_fixed_time (d : Dims) (N : ℕ) (t : ℝ) {κ τU δ C₀ E n : ℝ} (p m : ℕ)
    (hn : ((ouCommonBand d).size N : ℝ) = n)
    (hκ : 0 < κ) (hτU : 0 < τU) (hδ : 0 < δ) (hc2 : d.c < 1 / 2)
    (hmδ : ((m : ℝ) + 3) * δ ≤ τU) (hp : (1 + τU) * ((m : ℝ) + 4) + 4 + δ ≤ 2 * p * δ)
    (hE : |E| ≤ 2 - κ)
    (h1 : 64 * (3 + (m : ℝ)) ≤ n) (h2 : 2 * C₀ ≤ n ^ (d.c / 6))
    (h3 : C₀ / n + 2 * n ^ (-1 + 2 * τU) < κ / 4) (h4 : n ^ (-1 + d.c / 6) < κ / 2)
    (h5 : 8 * ((193 + 256 / κ ^ 2) + 12) ≤ n ^ (6 * τU))
    (hLLN : ∀ e : ℝ, |e| ≤ 2 - κ / 2 → ∀ x : d.Idx N,
      ∫ ω, ‖green ((ouCommonFlow d).Ht N t ω)
          ((e : ℂ) + ((n ^ (-1 + 2 * τU) : ℝ) : ℂ) * Complex.I) x x‖ ^ (2 * p)
        ∂(ouCommonMeasure d) ≤ n ^ δ)
    (hbadN : ∀ a0 : ZMod (d.L N),
      ouCommonMeasure d {ω | ∃ α β,
          |((ouCommonFlow d).hermitian N t ω).eigenvalues α - E| ≤ n ^ (-1 + d.c / 6) ∧
          |((ouCommonFlow d).hermitian N t ω).eigenvalues β - E| ≤ n ^ (-1 + d.c / 6) ∧
          n ^ (-(d.c / 36)) ≤ ‖blockM2 ((ouCommonFlow d).hermitian N t ω) a0 α β‖} ≤
        ENNReal.ofReal (3 * n ^ (-(d.c / 18))))
    (s : Finset (Fin m)) (w : Fin m → ℂ) (u₁ u₂ : ℂ)
    (hw : ∀ i, |(w i).re - E| ≤ C₀ / n ∧ n ^ (-1 - τU) ≤ (w i).im ∧
      (w i).im ≤ n ^ (-1 + τU))
    (hu₁ : |u₁.re - E| ≤ C₀ / n ∧ n ^ (-1 - τU) ≤ u₁.im ∧ u₁.im ≤ n ^ (-1 + τU))
    (hu₂ : |u₂.re - E| ≤ C₀ / n ∧ n ^ (-1 - τU) ≤ u₂.im ∧ u₂.im ≤ n ^ (-1 + τU)) :
    ∫ ω, (∏ j ∈ s, (stieltjes ((ouCommonFlow d).Ht N t ω) (w j)).im) *
        paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) u₁ u₂ ∂(ouCommonMeasure d) ≤
      n ^ (1 - d.c / 36 + (3 * (s.card : ℝ) + 16) * τU) := by
  classical
  have hc : 0 < d.c := d.c_pos
  have hn1 : 1 ≤ n := by have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith
  have hn0 : 0 < n := by linarith
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hLW : ((d.L N : ℝ) * (d.W N : ℝ)) = n := by
    rw [← hn]; simp [Band.size, ouCommonBand]
  have hcard : (Fintype.card (d.Idx N) : ℝ) = n := by rw [l2_card_idx, hLW]
  obtain ⟨ηt, hηt⟩ : ∃ ηt : ℝ, ηt = n ^ (-1 + 2 * τU) := ⟨_, rfl⟩
  obtain ⟨w', hw'def⟩ : ∃ w' : ℝ, w' = n ^ (-1 + d.c / 6) / 2 := ⟨_, rfl⟩
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hCb0 : 0 < n ^ δ := by positivity
  have hw'0 : 0 < w' := by rw [hw'def]; positivity
  have hw'κ : w' ≤ κ / 4 := by rw [hw'def]; linarith
  have hw'eq : w' = (2 * n ^ (1 - d.c / 6))⁻¹ := by
    rw [hw'def, mul_inv, show -1 + d.c / 6 = -(1 - d.c / 6) by ring, Real.rpow_neg hn0.le]
    ring
  obtain ⟨K', hK1', hK2'⟩ := l2_exists_dyadic hw'0 hw'κ
  have hu₁re : |u₁.re - E| ≤ C₀ / n := hu₁.1
  have hu₂re : |u₂.re - E| ≤ C₀ / n := hu₂.1
  have hη₁1 : n ^ (-1 - τU) ≤ u₁.im := hu₁.2.1
  have hη₂1 : n ^ (-1 - τU) ≤ u₂.im := hu₂.2.1
  have hη₁ : 0 < u₁.im := lt_of_lt_of_le (by positivity) hη₁1
  have hη₂ : 0 < u₂.im := lt_of_lt_of_le (by positivity) hη₂1
  have hle_ηt : ∀ {y : ℝ}, y ≤ n ^ (-1 + τU) → y ≤ ηt := fun hy =>
    hy.trans (by rw [hηt]; exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hη₁' : u₁.im ≤ ηt := hle_ηt hu₁.2.2
  have hη₂' : u₂.im ≤ ηt := hle_ηt hu₂.2.2
  have hηw1 : ∀ j, n ^ (-1 - τU) ≤ (w j).im := fun j => (hw j).2.1
  have hηw : ∀ j, 0 < (w j).im := fun j => lt_of_lt_of_le (by positivity) (hηw1 j)
  have hηw' : ∀ j, (w j).im ≤ ηt := fun j => hle_ηt (hw j).2.2
  -- the finite family of covering grids (centre, radius)
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (ℝ × ℝ), S =
      ((Finset.range (K' + 1)).image fun k => (u₁.re, (2 : ℝ) ^ k * w')) ∪
        ((Finset.range (K' + 1)).image fun k => (u₂.re, (2 : ℝ) ^ k * w')) ∪
        {(u₁.re, 0)} ∪ {(u₂.re, 0)} ∪ (Finset.univ.image fun j => ((w j).re, (0 : ℝ))) :=
    ⟨_, rfl⟩
  have hrad : ∀ k ∈ Finset.range (K' + 1), (2 : ℝ) ^ k * w' ≤ κ / 4 := fun k hk =>
    le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.1 hk; omega)) hw'0.le) hK1'
  have hS : ∀ q ∈ S, |q.1 - E| ≤ C₀ / n ∧ 0 ≤ q.2 ∧ q.2 ≤ κ / 4 := by
    intro q hq
    simp only [hSdef, Finset.mem_union, Finset.mem_image,
      Finset.mem_singleton, Finset.mem_univ, true_and] at hq
    rcases hq with (((⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | rfl) | rfl) | ⟨j, rfl⟩
    · exact ⟨hu₁re, by positivity, hrad k hk⟩
    · exact ⟨hu₂re, by positivity, hrad k hk⟩
    · exact ⟨hu₁re, le_rfl, by positivity⟩
    · exact ⟨hu₂re, le_rfl, by positivity⟩
    · exact ⟨(hw j).1, le_rfl, by positivity⟩
  have hSmem1 : ∀ k ≤ K', (u₁.re, (2 : ℝ) ^ k * w') ∈ S := fun k hk => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨k, by omega, rfl⟩)))
  have hSmem2 : ∀ k ≤ K', (u₂.re, (2 : ℝ) ^ k * w') ∈ S := fun k hk => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k, by omega, rfl⟩)))
  have hSmem3 : (u₁.re, (0 : ℝ)) ∈ S := by rw [hSdef]; simp
  have hSmem4 : (u₂.re, (0 : ℝ)) ∈ S := by rw [hSdef]; simp
  have hSmem5 : ∀ j, ((w j).re, (0 : ℝ)) ∈ S := fun j => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨j, rfl⟩
  -- sizes: `2^{K'} ≤ n`, `#S ≤ (3+m) n`, grid size `≤ 2n`
  have hηtinv : ηt⁻¹ ≤ n := by
    rw [hηt, ← Real.rpow_neg hn0.le]
    calc n ^ (-(-1 + 2 * τU)) ≤ n ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = n := Real.rpow_one n
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
    have hc1 : S.card ≤ (K' + 1) + (K' + 1) + 1 + 1 + m := by
      rw [hSdef]
      refine (Finset.card_union_le _ _).trans ?_
      refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) ?_
      · refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) (by simp)
        refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) (by simp)
        refine Nat.add_le_add ?_ ?_
        · exact (Finset.card_image_le).trans (by simp)
        · exact (Finset.card_image_le).trans (by simp)
      · exact (Finset.card_image_le).trans (by simp)
    have hK' : (K' : ℝ) + 1 ≤ n := by
      have : K' + 1 ≤ 2 ^ K' := Nat.lt_two_pow_self
      have h' : ((K' + 1 : ℕ) : ℝ) ≤ ((2 ^ K' : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      linarith
    have hc1' : (S.card : ℝ) ≤ (K' + 1) + (K' + 1) + 1 + 1 + m := by exact_mod_cast hc1
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
    have he := l2_grid_energy_le hηt0 hE hq1 hq0 hqκ (by rw [hηt]; exact h3) hj
    have := hLLN _ he x
    rw [← hηt] at this
    exact this
  have hΞc := l2_prob_not_gridGood_finset d N t hηt0 hCb0 p S (⌈n⌉₊ + 1) hGS hCb0.le hM
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
      {ω | ∃ α β,
        |((ouCommonFlow d).hermitian N t ω).eigenvalues α - E| ≤ n ^ (-1 + d.c / 6) ∧
        |((ouCommonFlow d).hermitian N t ω).eigenvalues β - E| ≤ n ^ (-1 + d.c / 6) ∧
        n ^ (-(d.c / 36)) ≤ ‖blockM2 ((ouCommonFlow d).hermitian N t ω) a0 α β‖} := ⟨_, rfl⟩
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
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 193 + 256 / κ ^ 2 := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hPw0 : 0 ≤ Pw := by rw [hPw]; positivity
  obtain ⟨Ag, hAgdef⟩ : ∃ Ag : ℝ, Ag = C₁ * n ^ (3 - d.c / 36 + 8 * τU + 2 * δ) := ⟨_, rfl⟩
  obtain ⟨Ab, hAbdef⟩ : ∃ Ab : ℝ, Ab = 4 * n ^ (3 + 8 * τU + 2 * δ) := ⟨_, rfl⟩
  have hAg0 : 0 ≤ Ag := by rw [hAgdef]; positivity
  have hAb0 : 0 ≤ Ab := by rw [hAbdef]; positivity
  have hcB0 : 0 ≤ Pw * (4 * n⁻¹ * n⁻¹ * n⁻¹ * Ab) := by positivity
  have hCr0 : 0 ≤ 16 * n ^ ((1 + τU) * ((s.card : ℝ) + 4)) := by positivity
  -- the one-index rows, deterministic
  have hq₁ := l2_q_le (δ := δ) hn1 hηt hη₁1
  have hq₂ := l2_q_le (δ := δ) hn1 hηt hη₂1
  have ho := l2_o_le (X := n) (c := d.c) (δ := δ) (κ := κ) (K' := K') hn1 hc hc2 hτU hδ.le hκ
    hηt hw'eq hK2'
  have hq₁0 : 0 ≤ ηt / u₁.im ^ 2 * n ^ δ := by positivity
  have hq₂0 : 0 ≤ ηt / u₂.im ^ 2 * n ^ δ := by positivity
  have ho0 : 0 ≤ n ^ δ * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹ := by positivity
  have hAg : n ^ (-(d.c / 36)) / 2 * ((ηt / u₁.im ^ 2 * n ^ δ) * (n * (ηt / u₂.im ^ 2 * n ^ δ)) +
      (n * (ηt / u₁.im ^ 2 * n ^ δ)) * (ηt / u₂.im ^ 2 * n ^ δ)) +
      2 * n * ((n ^ δ * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹) *
          (ηt / u₂.im ^ 2 * n ^ δ) +
        (ηt / u₁.im ^ 2 * n ^ δ) * (n ^ δ * (8 / w' + 8 * ηt / w' ^ 2) +
          ((2 ^ K' * w') ^ 2)⁻¹)) ≤ Ag := by
    rw [hAgdef, hC₁]
    exact l2_Ag_le hn1 hc hτU hκ rfl hq₁ hq₂0 hq₂ ho0 ho
  have hAb : 4 * n * ((ηt / u₁.im ^ 2 * n ^ δ) * (ηt / u₂.im ^ 2 * n ^ δ)) ≤ Ab := by
    rw [hAbdef]; exact l2_Ab_le hn1 hq₁ hq₂0 hq₂
  -- pointwise domination
  have hfg : ∀ ω, (∏ j ∈ s, (stieltjes ((ouCommonFlow d).Ht N t ω) (w j)).im) *
      paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) u₁ u₂ ≤
      Pw * (4 * n⁻¹ * n⁻¹ * Ag) +
        Pw * (4 * n⁻¹ * n⁻¹ * n⁻¹ * Ab) * ∑ y : d.Idx N, (Bm y.1).indicator 1 ω +
        16 * n ^ ((1 + τU) * ((s.card : ℝ) + 4)) * T.indicator 1 ω := by
    intro ω
    have hH := (ouCommonFlow d).hermitian N t ω
    have hind : ∀ (A : Set (ouCommonOmega d)), 0 ≤ A.indicator (1 : ouCommonOmega d → ℝ) ω :=
      fun A => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have hA0 : 0 ≤ Pw * (4 * n⁻¹ * n⁻¹ * Ag) := by positivity
    have hsum0 : 0 ≤ Pw * (4 * n⁻¹ * n⁻¹ * n⁻¹ * Ab) * ∑ y : d.Idx N, (Bm y.1).indicator 1 ω :=
      mul_nonneg hcB0 (Finset.sum_nonneg fun y _ => hind _)
    by_cases hωT : ω ∈ T
    · -- crude row
      have hc1 := l2_pointwise_crude d N hH s w u₁ u₂ hη₁ hη₂ hηw
      have hc2' := l2_prod_crude_le hn1 s w u₁ u₂ hηw1 hη₁1 hη₂1
      have hTi : T.indicator (1 : ouCommonOmega d → ℝ) ω = 1 := by
        simp [Set.indicator_of_mem hωT]
      rw [hTi, mul_one]
      refine le_trans hc1 (le_trans hc2' ?_)
      linarith
    · -- good event
      have hΞ : ∀ q ∈ S, GridGood ((ouCommonFlow d).Ht N t ω) ηt (n ^ δ) q.1 q.2 := by
        by_contra hn'
        apply hωT
        rw [hTdef]
        exact subset_toMeasurable _ _ hn'
      have hBad : ∀ a0, ¬ (ω ∈ Bm a0) → ∀ α β, |hH.eigenvalues α - u₁.re| ≤ w' →
          |hH.eigenvalues β - u₂.re| ≤ w' → ‖blockM2 hH a0 α β‖ ≤ n ^ (-(d.c / 36)) := by
        intro a0 hna α β hα hβ
        have hnb : ω ∉ Bs a0 := fun hb => hna (by rw [hBmdef]; exact subset_toMeasurable _ _ hb)
        rw [hBsdef] at hnb
        simp only [Set.mem_ofPred_eq, not_exists, not_and, not_le] at hnb
        have hsplit : n ^ (-1 + d.c / 6) = n ^ (d.c / 6) * n⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]; congr 1; ring
        have hC : C₀ / n ≤ n ^ (-1 + d.c / 6) / 2 := by
          rw [hsplit, div_eq_mul_inv]
          have := mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hn0.le)
          linarith
        have hwin : ∀ (γ : ZMod (d.L N) × Fin (d.W N)) (v : ℂ), |v.re - E| ≤ C₀ / n →
            |hH.eigenvalues γ - v.re| ≤ w' → |hH.eigenvalues γ - E| ≤ n ^ (-1 + d.c / 6) := by
          intro γ v hv hγ
          calc |hH.eigenvalues γ - E| ≤ |hH.eigenvalues γ - v.re| + |v.re - E| :=
                abs_sub_le _ _ _
            _ ≤ w' + C₀ / n := add_le_add hγ hv
            _ ≤ n ^ (-1 + d.c / 6) := by rw [hw'def]; linarith
        exact (hnb α β (hwin α u₁ hu₁re hα) (hwin β u₂ hu₂re hβ)).le
      have hLW' : (d.L N * d.W N : ℝ) = n := by exact_mod_cast hLW
      have hgood := l2_pointwise_good d N hH s w u₁ u₂ (Cb := n ^ δ) (θ := n ^ (-(d.c / 36)))
        (Ag := Ag) (Ab := Ab) hη₁ hη₁' hη₂ hη₂' hηw hηw' hCb0.le hw'0 (by positivity) K'
        (fun k hk => hΞ (u₁.re, (2 : ℝ) ^ k * w') (hSmem1 k hk))
        (fun k hk => hΞ (u₂.re, (2 : ℝ) ^ k * w') (hSmem2 k hk))
        (hΞ (u₁.re, 0) hSmem3) (hΞ (u₂.re, 0) hSmem4) (fun j => hΞ ((w j).re, 0) (hSmem5 j))
        (fun a0 => ω ∈ Bm a0) hBad (by rw [hLW']; exact hAg) (by rw [hLW']; exact hAb)
      rw [hLW'] at hgood
      have hP := l2_prod_row_le (δ := δ) hn1 hηt s w hηw1
      rw [← hPw] at hP
      have hsumeq : ∑ y : d.Idx N, n⁻¹ * (Ag + (if ω ∈ Bm y.1 then Ab else 0)) =
          n * (n⁻¹ * Ag) + n⁻¹ * Ab * ∑ y : d.Idx N, (Bm y.1).indicator 1 ω := by
        rw [Finset.mul_sum]
        have : ∀ y : d.Idx N, n⁻¹ * (Ag + (if ω ∈ Bm y.1 then Ab else 0)) =
            n⁻¹ * Ag + n⁻¹ * Ab * (Bm y.1).indicator 1 ω := by
          intro y
          by_cases hy : ω ∈ Bm y.1
          · simp [hy]; ring
          · simp [hy]
        rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, hcard]
      rw [hsumeq] at hgood
      have hR0 : 0 ≤ 4 * (n⁻¹ * (n⁻¹ * (n * (n⁻¹ * Ag) +
          n⁻¹ * Ab * ∑ y : d.Idx N, (Bm y.1).indicator 1 ω))) := by
        have := Finset.sum_nonneg fun (y : d.Idx N) (_ : y ∈ Finset.univ) =>
          hind (Bm y.1)
        positivity
      have hstep := hgood.trans (mul_le_mul_of_nonneg_right hP hR0)
      have hTi0 : 0 ≤ 16 * n ^ ((1 + τU) * ((s.card : ℝ) + 4)) * T.indicator 1 ω :=
        mul_nonneg hCr0 (hind _)
      have e : Pw * (4 * (n⁻¹ * (n⁻¹ * (n * (n⁻¹ * Ag) +
          n⁻¹ * Ab * ∑ y : d.Idx N, (Bm y.1).indicator 1 ω)))) =
          Pw * (4 * n⁻¹ * n⁻¹ * Ag) +
            Pw * (4 * n⁻¹ * n⁻¹ * n⁻¹ * Ab) * ∑ y : d.Idx N, (Bm y.1).indicator 1 ω := by
        field_simp
      rw [e] at hstep
      exact hstep.trans (le_add_of_nonneg_right hTi0)
  have hf0 : ∀ ω, 0 ≤ (∏ j ∈ s, (stieltjes ((ouCommonFlow d).Ht N t ω) (w j)).im) *
      paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) u₁ u₂ := fun ω =>
    mul_nonneg (Finset.prod_nonneg fun j _ =>
        (l2_stieltjes_im_nonneg_le ((ouCommonFlow d).hermitian N t ω) (hηw j)).1)
      (l2_paperL2Kernel_nonneg d N _ u₁ u₂)
  refine (l2_integral_le_of_majorant hf0 (fun y : d.Idx N => Bm y.1) (fun y => hBmm y.1) hTm
    _ _ _ hfg).trans ?_
  -- final normalization: good part and crude part, each `≤ ½ n^{…}`
  have hsumB : ∑ y : d.Idx N, (ouCommonMeasure d).real (Bm y.1) ≤
      n * (3 * n ^ (-(d.c / 18))) := by
    calc _ ≤ ∑ _y : d.Idx N, 3 * n ^ (-(d.c / 18)) := Finset.sum_le_sum fun y _ => hBprob y.1
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hgoodT := l2_good_total_le (X := n) (c := d.c) (δ := δ) (C₁ := C₁)
    (sc := s.card) (m := m) hn1 hc.le hτU hδ.le hC₁0 hsc hmδ (by rw [hC₁]; exact h5)
  have hcrudeT := l2_crude_total_le (X := n) (c := d.c) (δ := δ) (sc := s.card) (m := m)
    (p := p) hn1 hτU (by linarith) hsc hp h1
  rw [← hPw, ← hAgdef, ← hAbdef] at hgoodT
  have hA2 : Pw * (4 * n⁻¹ * n⁻¹ * n⁻¹ * Ab) *
      ∑ y : d.Idx N, (ouCommonMeasure d).real (Bm y.1) ≤
      Pw * (4 * n⁻¹ * n⁻¹ * n⁻¹ * Ab) * (n * (3 * n ^ (-(d.c / 18)))) :=
    mul_le_mul_of_nonneg_left hsumB hcB0
  have hcrude' : 16 * n ^ ((1 + τU) * ((s.card : ℝ) + 4)) * (ouCommonMeasure d).real T ≤
      16 * n ^ ((1 + τU) * ((s.card : ℝ) + 4)) *
        ((3 + (m : ℝ)) * n * (2 * n * (n * (n ^ δ / (n ^ δ) ^ (2 * p))))) :=
    mul_le_mul_of_nonneg_left hTprob hCr0
  linarith

/-- **The weighted `L₂` kernel bound** (the `L₂` half of the per-time bound behind
(2.28)/(2.30)).  For `t ∈ (0, t_U]` and spectral parameters in the window (2.22),
`E[∏_{j∈s} Im m_t(w_j) · L₂(u₁,u₂)] ≤ N^{1 - c/36 + (3|s|+16)τ_U}`.  Uses `FlowLocalLaw` only at
its single scale `η̃ = N^{-1+2τ_U}` (via the covering lemma) and `FlowEq747` through
`que_flow_of_eq747` and the pair bound `measure_bad2_le_of_que`. -/
theorem expect_L2_weighted_le (d : Dims) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hτc : τU < d.c / 3) (hLL : FlowLocalLaw d κ τU) (hQUE : FlowEq747 d κ τU)
    (E : ℝ) (hE : |E| ≤ 2 - κ) {C₀ : ℝ} (hC₀ : 0 < C₀) (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Ioc (0 : ℝ) ((ouCommonBand d).tPow τU N),
      ∀ (s : Finset (Fin m)) (w : Fin m → ℂ) (u₁ u₂ : ℂ),
        (∀ i, InWindow222 d E C₀ τU N (w i)) → InWindow222 d E C₀ τU N u₁ →
        InWindow222 d E C₀ τU N u₂ →
        ∫ ω, (∏ j ∈ s, (stieltjes ((ouCommonFlow d).Ht N t ω) (w j)).im) *
            paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) u₁ u₂ ∂(ouCommonMeasure d) ≤
          ((ouCommonBand d).size N : ℝ) ^ (1 - d.c / 36 + (3 * (s.card : ℝ) + 16) * τU) := by
  have hc : 0 < d.c := d.c_pos
  have hc2 : d.c < 1 / 2 := l2_c_lt_half d
  -- parameters fixed before `N`: `δ = τ/(m+5)` and the moment order `p`
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = τU / (m + 5) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hmδ : ((m : ℝ) + 3) * δ ≤ τU := by
    rw [hδdef, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = ⌈((1 + τU) * ((m : ℝ) + 4) + 5 + δ) / (2 * δ)⌉₊ :=
    ⟨_, rfl⟩
  have hp : (1 + τU) * ((m : ℝ) + 4) + 4 + δ ≤ 2 * p * δ := by
    have h1 := Nat.le_ceil (((1 + τU) * ((m : ℝ) + 4) + 5 + δ) / (2 * δ))
    rw [← hpdef, div_le_iff₀ (by positivity)] at h1
    linarith
  have hsize : Tendsto (fun N => ((ouCommonBand d).size N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (ouCommonBand d).tendsto_size
  -- the eventual conditions on `N` (finitely many, uniform in `t, s, w, u₁, u₂`)
  have ev1 : ∀ᶠ N : ℕ in atTop, 64 * (3 + (m : ℝ)) ≤ ((ouCommonBand d).size N : ℝ) :=
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
  have ev5 : ∀ᶠ N : ℕ in atTop, 8 * ((193 + 256 / κ ^ 2) + 12) ≤
      ((ouCommonBand d).size N : ℝ) ^ (6 * τU) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  filter_upwards [hLL δ hδ p, l2_bad2_uniform d hκ hτc hQUE E hE, ev1, ev2, ev3, ev4, ev5]
    with N hLLN hbadN h1 h2 h3 h4 h5
  intro t ht s w u₁ u₂ hw hu₁ hu₂
  exact l2_fixed_time d N t p m rfl hκ hτU hδ hc2 hmδ hp hE h1 h2 h3 h4 h5
    (fun e he x => hLLN t ⟨ht.1.le, ht.2⟩ e he x) (fun a0 => hbadN t ht a0) s w u₁ u₂ hw hu₁ hu₂

end RBM.Gauss
