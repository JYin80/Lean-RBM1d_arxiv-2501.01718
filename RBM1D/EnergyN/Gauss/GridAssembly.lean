/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridAssembly

/-!
# Time sums along the grid at an `N`-dependent energy

Three statements at an `N`-dependent energy `E : ℕ → ℝ`: the time sum
`Σ_j step / η_{u_j} ≤ (mE (E N)).im⁻¹ log N` over the grid
(`RBM.Gauss.Grid.sum_step_div_eta_le_of_etaN`, and `RBM.Gauss.Grid.sum_step_div_eta_le_plainN`
under the plain pair), and the private `etaT_inv_le_of_hAcN`. No energy-dependent constant is
fixed in this file: `(mE (E N)).im⁻¹` appears only in the conclusion, not as a constant fixed
ahead of the eventual statement, and no `κ` is used.

`sum_step_div_eta_le_of_etaN` takes `hη` directly from the caller; `etaT_inv_le_of_hAcN` uses
only `(band d).dim` (`E`-free) and the energy-free `etaT_pos_of_lt_one'`;
`sum_step_div_eta_le_plainN` is a one-line corollary.
-/

namespace RBM.Gauss.Grid

open Finset MeasureTheory ProbabilityTheory Filter Matrix RBM

/-! ### Private helpers

Neither carries an `E`-binder. They are declared in this file because Lean's `private`
visibility is file-local, even within the same namespace. -/

private lemma log_sub_le_of_pos_le (x y : ℝ) (hy : 0 < y) (hxy : y ≤ x) :
    (x - y) / x ≤ Real.log x - Real.log y := by
  have hx : 0 < x := lt_of_lt_of_le hy hxy
  have hr : 0 < y / x := div_pos hy hx
  have h1 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos hr
  have hlogdiv : Real.log (y / x) = Real.log y - Real.log x := Real.log_div hy.ne' hx.ne'
  rw [hlogdiv] at h1
  have h3 : y / x - 1 = -((x - y) / x) := by field_simp; ring
  rw [h3] at h1
  linarith

private lemma telescoping_sum_le (f g : ℕ → ℝ) (m : ℕ)
    (h : ∀ j < m, g j ≤ f j - f (j + 1)) :
    ∑ j ∈ range m, g j ≤ f 0 - f m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h m (by omega)
    linarith

/-- **`Σ_j step / η_{u_j} ≤ (mE (E N)).im⁻¹ log N` eventually**, over the grid of `K N` steps,
given `η_t⁻¹ ≤ N` eventually. No energy-dependent constant is fixed here: no `κ` anywhere, `hη`
is supplied by the caller. -/
theorem sum_step_div_eta_le_of_etaN (d : Dims) {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hη : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ))
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      ∑ j ∈ range (K N), step s t K N / etaT (E N) (time s t K N j)
        ≤ (mE (E N)).im⁻¹ * Real.log N := by
  filter_upwards [hη, Filter.eventually_ge_atTop 1]
    with N hetaN hN1
  have hmim : 0 < (mE (E N)).im := mE_im_pos (hE N)
  have hmimle1 : (mE (E N)).im ≤ 1 := by
    rw [mE_im]
    have hle : Real.sqrt (4 - (E N) ^ 2) ≤ Real.sqrt 4 :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (E N)])
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [h4] at hle
    linarith
  have hΔ0 : 0 ≤ step s t K N := by
    unfold step
    exact div_nonneg (by linarith [hst N]) (Nat.cast_nonneg _)
  have hlin : ∀ j, time s t K N (j + 1) = time s t K N j + step s t K N := by
    intro j; unfold time; push_cast; ring
  have hstep_eq : (K N : ℝ) * step s t K N = t N - s N := by
    have hKne : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hK0 N)
    unfold step; field_simp
  have hle_t : ∀ j : ℕ, (j : ℝ) ≤ (K N : ℝ) → time s t K N j ≤ t N := by
    intro j hj
    have hmul : (j : ℝ) * step s t K N ≤ (K N : ℝ) * step s t K N :=
      mul_le_mul_of_nonneg_right hj hΔ0
    unfold time
    linarith [hmul, hstep_eq]
  have key : ∀ j < K N, step s t K N / (1 - time s t K N j)
      ≤ Real.log (1 - time s t K N j) - Real.log (1 - time s t K N (j + 1)) := by
    intro j hj
    have hj1K : ((j + 1 : ℕ) : ℝ) ≤ (K N : ℝ) := by exact_mod_cast hj
    have hjK : (j : ℝ) ≤ (K N : ℝ) := by
      have : j ≤ K N := le_of_lt hj
      exact_mod_cast this
    have hujle : time s t K N j ≤ t N := hle_t j hjK
    have huj1le : time s t K N (j + 1) ≤ t N := hle_t (j + 1) hj1K
    have hy0 : 0 < 1 - time s t K N (j + 1) := by linarith [huj1le, ht1 N]
    have hxy : (1 - time s t K N (j + 1)) ≤ (1 - time s t K N j) := by
      rw [hlin j]; linarith [hΔ0]
    have hlog := log_sub_le_of_pos_le (1 - time s t K N j) (1 - time s t K N (j + 1)) hy0 hxy
    have heq : (1 - time s t K N j) - (1 - time s t K N (j + 1)) = step s t K N := by
      rw [hlin j]; ring
    rwa [heq] at hlog
  have htel := telescoping_sum_le (fun j => Real.log (1 - time s t K N j))
    (fun j => step s t K N / (1 - time s t K N j)) (K N) key
  rw [time_zero, time_last s t K N (hK0 N)] at htel
  have hsum_eq : ∑ j ∈ range (K N), step s t K N / etaT (E N) (time s t K N j)
      = (mE (E N)).im⁻¹ * ∑ j ∈ range (K N), step s t K N / (1 - time s t K N j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have heta : etaT (E N) (time s t K N j) = (1 - time s t K N j) * (mE (E N)).im := rfl
    rw [heta]
    field_simp
  rw [hsum_eq]
  have hlogs_le : Real.log (1 - s N) ≤ 0 :=
    Real.log_nonpos (by linarith [hst N, ht1 N]) (by linarith [hs0 N])
  have hNle : (1 - t N)⁻¹ ≤ (mE (E N)).im * N := by
    have heta_t : etaT (E N) (t N) = (1 - t N) * (mE (E N)).im := rfl
    have h1 : ((1 - t N) * (mE (E N)).im)⁻¹ ≤ (N : ℝ) := heta_t ▸ hetaN
    rw [mul_inv] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 hmim.le
    rw [mul_assoc, inv_mul_cancel₀ hmim.ne', mul_one, mul_comm] at h2
    exact h2
  have hN0 : (0 : ℝ) < N := by
    have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    linarith
  have hlogNt : -Real.log (1 - t N) ≤ Real.log ((mE (E N)).im * N) := by
    have h1t : 0 < 1 - t N := by linarith [ht1 N]
    have h2 : Real.log ((1 - t N)⁻¹) = -Real.log (1 - t N) := Real.log_inv _
    rw [← h2]
    exact Real.log_le_log (by positivity) hNle
  have hlogmN : Real.log ((mE (E N)).im * N) ≤ Real.log N := by
    have hmNpos : 0 < (mE (E N)).im * N := by positivity
    have : (mE (E N)).im * N ≤ N := by nlinarith [hmimle1, hN0.le]
    exact Real.log_le_log hmNpos this
  have hfinal : Real.log (1 - s N) - Real.log (1 - t N) ≤ Real.log N := by linarith
  have hgoal : ∑ j ∈ range (K N), step s t K N / (1 - time s t K N j) ≤ Real.log N :=
    htel.trans hfinal
  calc (mE (E N)).im⁻¹ * ∑ j ∈ range (K N), step s t K N / (1 - time s t K N j)
      ≤ (mE (E N)).im⁻¹ * Real.log N := by
        apply mul_le_mul_of_nonneg_left hgoal (inv_nonneg.mpr hmim.le)
    _ = (mE (E N)).im⁻¹ * Real.log N := rfl

/-- **`η_t⁻¹ ≤ N` eventually**, from `N^c ≤ W ℓ_t η_t` eventually. No energy-dependent constant
is fixed here: no `κ`, only `(band d).dim` (`E`-free) and `etaT_pos_of_lt_one'`. -/
private theorem etaT_inv_le_of_hAcN (d : Dims) {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    {t : ℕ → ℝ} (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) := by
  filter_upwards [hAc, (band d).dim, eventually_ge_atTop 1] with N hAcN hdimN hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hηt : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE N) (ht1 N)
  have hellle : (band d).ell N (t N) ≤ ((band d).L N : ℝ) := min_le_right _ _
  have hW0 : (0 : ℝ) ≤ ((band d).W N : ℝ) := Nat.cast_nonneg _
  have hscale_le :
      (band d).scale (E N) N (t N) ≤
        ((band d).W N : ℝ) * ((band d).L N : ℝ) * etaT (E N) (t N) := by
    show ((band d).W N : ℝ) * (band d).ell N (t N) * etaT (E N) (t N) ≤ _
    have h1 : ((band d).W N : ℝ) * (band d).ell N (t N)
        ≤ ((band d).W N : ℝ) * ((band d).L N : ℝ) := mul_le_mul_of_nonneg_left hellle hW0
    exact mul_le_mul_of_nonneg_right h1 hηt.le
  have hWLN : ((band d).W N : ℝ) * ((band d).L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdimN.1
  have hchain : (N : ℝ) ^ c ≤ (N : ℝ) * etaT (E N) (t N) :=
    calc (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N) := hAcN
      _ ≤ ((band d).W N : ℝ) * ((band d).L N : ℝ) * etaT (E N) (t N) := hscale_le
      _ ≤ (N : ℝ) * etaT (E N) (t N) := mul_le_mul_of_nonneg_right hWLN hηt.le
  have h1c : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0.le
  have hbig : (1 : ℝ) ≤ (N : ℝ) * etaT (E N) (t N) := h1c.trans hchain
  have h := mul_le_mul_of_nonneg_right hbig (inv_nonneg.2 hηt.le)
  rwa [one_mul, mul_assoc, mul_inv_cancel₀ hηt.ne', mul_one] at h

/-- **The same time sum under the plain pair** `(η_s/η_t)^30 ≤ W ℓ_t η_t` and
`N^c ≤ W ℓ_t η_t`, using `etaT_inv_le_of_hAcN`. No energy-dependent constant is fixed here. -/
theorem sum_step_div_eta_le_plainN (d : Dims) {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      ∑ j ∈ range (K N), step s t K N / etaT (E N) (time s t K N j)
        ≤ (mE (E N)).im⁻¹ * Real.log N :=
  sum_step_div_eta_le_of_etaN d hE hs0 hst ht1 (etaT_inv_le_of_hAcN d hE ht1 hc0 hAc) K hK0

section Compat

end Compat

end RBM.Gauss.Grid
