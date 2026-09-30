/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GUEPhaseStep
import RBM1D.Flow.GUEPhaseEntry
import RBM1D.Flow.GUEPhaseKTilde
import RBM1D.Hierarchy.GUEPhaseG
import RBM1D.Gauss.GridDuhamelTail
import RBM1D.Flow.EnergyUniformReg
import RBM1D.Flow.GUEPhaseHyp
import RBM1D.Hierarchy.GUEPhaseGEven

/-!
# The output of the §7.2 random layer: `gueGrid_pathBounds`

Under the hypotheses below, the GUE-phase grid path `gueH` satisfies
`GUEPathBounds`: (7.28) at every grid time `k ≤ gueGridK n0 N` for `1 ≤ n ≤ n₀` against the
primitive family `Kt`, and `‖G̃ - m‖_max ≺ (N η_u)^{-1/2}`.

Route:
* the bootstraps: `GUEPhase.eq727GE` (even lengths, `n₀' = 2n₀`) with the processes of
  `Flow/GUEPhaseProc.lean` and
  `gueBds_h745E`, then `GUEPhase.eq728G` with `gueBds_h746`;
* the step-`0` local law from `hB.localLaw`, transferred by the one-time law `map_gueH_zero`;
* **unfreezing**: on the intersection of the w.h.p. events (the two bootstrap outputs, the entry
  bound `gueGrid_entry_bound` with `δ = N^{-τU/4}`, the step-`0` local law, the increment truncation
  `gue_highProb_incr_le`), an induction over the grid shows that the a-priori threshold
  `gueDelta τU` is never reached (the entry bound + `Lm(2) ≺ Λ` + `W⁻¹ ≤ Λ` at the previous step,
  then the one-step bound `gueDev_succ_le`), so the freezing index `gueStop` never acts and the
  frozen processes agree with the true ones at every grid time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace RBM.Gauss.GUEGrid

/-! ### Elementary helpers (private) -/

section GueBoundsHelpers

/-- `Im m^{(E)} ≤ 1` (`|m^{(E)}| = 1`). -/
private theorem gueBounds_mE_im_le_one {E : ℝ} (hE : |E| < 2) : (mE E).im ≤ 1 :=
  le_of_abs_le ((Complex.abs_im_le_norm _).trans (norm_mE hE.le).le)

/-- Before `firstHit` has reached `k`, i.e. if no index `i ≤ k ≤ K` hits the threshold, then
`k ≤ firstHit`. -/
private theorem gueBounds_le_firstHit {Ω' : Type*} (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) (ω : Ω')
    {k : ℕ} (hk : k ≤ K) (h : ∀ i ≤ k, J i ω < θ) : k ≤ Grid.firstHit J θ K ω := by
  by_contra hlt
  push Not at hlt
  have hlt' : Grid.firstHit J θ K ω < K := lt_of_lt_of_le hlt hk
  have hmem : J (Grid.firstHit J θ K ω) ω ∈ Set.Ici θ :=
    MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt (u := J) (s := Set.Ici θ) (n := 0) hlt'
  exact absurd (h _ hlt.le) (not_lt.2 hmem)

/-- The unfreezing induction, in abstract form. -/
private theorem gueBounds_unfreeze {K : ℕ} (dev : ℕ → ℝ) (σ : ℕ) {δ : ℝ}
    (hσ : ∀ k ≤ K, (∀ i ≤ k, dev i < δ) → k ≤ σ)
    (h0 : dev 0 < δ)
    (hstep : ∀ j < K, j ≤ σ → dev j < δ → dev j ≤ δ / 4)
    (hjump : ∀ j < K, dev (j + 1) ≤ dev j + δ / 2) (hδ : 0 < δ) :
    ∀ k ≤ K, ∀ i ≤ k, dev i < δ := by
  intro k
  induction k with
  | zero =>
      intro _ i hi
      have : i = 0 := by omega
      subst this
      exact h0
  | succ k ih =>
      intro hk i hi
      have ih' := ih (by omega)
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · exact ih' i (by omega)
      · have hi' : i = k + 1 := by omega
        subst hi'
        have hkσ := hσ k (by omega) ih'
        have h1 := hstep k (by omega) hkσ (ih' k le_rfl)
        have h2 := hjump k (by omega)
        linarith

/-- The entry-bound arithmetic: `x² ≤ p(9 L + 2 w)`, `L ≤ p Λ`, `w ≤ Λ`, `Λ ≤ q` give
`x² ≤ 11 p² q`. -/
private theorem gueBounds_sq_le {x p L Λ w q : ℝ} (hp1 : 1 ≤ p) (hL : L ≤ p * Λ) (hw : w ≤ Λ)
    (hΛq : Λ ≤ q) (hΛ0 : 0 ≤ Λ) (hx2 : x ^ 2 ≤ p * (9 * L + 2 * w)) :
    x ^ 2 ≤ 11 * p ^ 2 * Λ ∧ 11 * p ^ 2 * Λ ≤ 11 * p ^ 2 * q := by
  have hp0 : 0 ≤ p := by linarith
  have hΛp : Λ ≤ p * Λ := le_mul_of_one_le_left hΛ0 hp1
  have h1 : 9 * L + 2 * w ≤ 11 * (p * Λ) := by linarith
  refine ⟨?_, ?_⟩
  · calc x ^ 2 ≤ p * (9 * L + 2 * w) := hx2
      _ ≤ p * (11 * (p * Λ)) := mul_le_mul_of_nonneg_left h1 hp0
      _ = 11 * p ^ 2 * Λ := by ring
  · have : 0 ≤ 11 * p ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hΛq this

/-- The one-step jump of `‖G - m‖_max` (row J2) is at most `δ/2`. -/
private theorem gueBounds_jump {N : ℕ} (hN : 1 ≤ N) {S e Δ Sg δ : ℝ} (hS1 : 1 ≤ S)
    (hSN : S ≤ N) (he : 0 ≤ e) (heS : e ≤ S) (hΔ0 : 0 ≤ Δ) (hΔ : Δ * ((N : ℝ) + 1) ^ 64 ≤ 1)
    (hSg0 : 0 ≤ Sg) (hSg : Sg ≤ S ^ 2 * N) (hδ : 1 / (N : ℝ) ≤ δ) :
    e ^ 2 * (Real.sqrt (Δ / S) * Sg + Δ) ≤ δ / 2 := by
  set X : ℝ := (N : ℝ) + 1 with hX
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX1 : 1 ≤ X := by rw [hX]; linarith
  have hX2 : 2 ≤ X := by rw [hX]; linarith
  have hX0 : 0 < X := by linarith
  have hNX : (N : ℝ) ≤ X := by rw [hX]; linarith
  set r : ℝ := Real.sqrt (Δ / S) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hX32 : 1 ≤ X ^ 32 := one_le_pow₀ hX1
  have hX64 : X ^ 64 = X ^ 32 * X ^ 32 := by rw [← pow_add]
  -- `r X^32 ≤ 1`
  have hrX : r * X ^ 32 ≤ 1 := by
    have hDS : Δ / S ≤ Δ := div_le_self hΔ0 hS1
    have hsq : (r * X ^ 32) ^ 2 ≤ 1 := by
      rw [mul_pow, hr, Real.sq_sqrt (div_nonneg hΔ0 (by linarith)), ← pow_mul]
      calc Δ / S * X ^ (32 * 2) ≤ Δ * X ^ (32 * 2) :=
            mul_le_mul_of_nonneg_right hDS (by positivity)
        _ ≤ 1 := by simpa using hΔ
    have h0 : 0 ≤ r * X ^ 32 := by positivity
    exact (pow_le_one_iff_of_nonneg h0 two_ne_zero).1 hsq
  have hΔX : Δ * X ^ 32 ≤ 1 := by
    have : Δ * X ^ 32 ≤ Δ * X ^ 64 := by
      rw [hX64]
      have : X ^ 32 ≤ X ^ 32 * X ^ 32 := le_mul_of_one_le_right (by positivity) hX32
      exact mul_le_mul_of_nonneg_left this hΔ0
    linarith
  have he2 : e ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ he (by linarith) 2
  have hSgX : Sg ≤ X ^ 3 := by
    have hS2 : S ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc Sg ≤ S ^ 2 * N := hSg
      _ ≤ X ^ 2 * X := mul_le_mul hS2 hNX (by linarith) (by positivity)
      _ = X ^ 3 := by ring
  have hinner : r * Sg + Δ ≤ X ^ 3 * (r + Δ) := by
    have h1 : r * Sg ≤ r * X ^ 3 := mul_le_mul_of_nonneg_left hSgX hr0
    have h2 : Δ ≤ X ^ 3 * Δ := le_mul_of_one_le_left hΔ0 (one_le_pow₀ hX1)
    calc r * Sg + Δ ≤ r * X ^ 3 + X ^ 3 * Δ := add_le_add h1 h2
      _ = X ^ 3 * (r + Δ) := by ring
  have hsum : (r + Δ) * X ^ 32 ≤ 2 := by rw [add_mul]; linarith
  have hmain : e ^ 2 * (r * Sg + Δ) * X ^ 32 ≤ 2 * X ^ 5 := by
    have h0 : 0 ≤ r * Sg + Δ := by positivity
    calc e ^ 2 * (r * Sg + Δ) * X ^ 32 ≤ X ^ 2 * (X ^ 3 * (r + Δ)) * X ^ 32 := by
          gcongr
      _ = X ^ 5 * ((r + Δ) * X ^ 32) := by ring
      _ ≤ X ^ 5 * 2 := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * X ^ 5 := by ring
  -- `4 N X^5 ≤ X^32`
  have hbig : 4 * (N : ℝ) * X ^ 5 ≤ X ^ 32 := by
    have h26 : (2 : ℝ) ^ 26 ≤ X ^ 26 := pow_le_pow_left₀ (by norm_num) hX2 26
    have h4 : (4 : ℝ) ≤ X ^ 26 := le_trans (by norm_num) h26
    calc 4 * (N : ℝ) * X ^ 5 ≤ X ^ 26 * X * X ^ 5 := by
          have : 0 ≤ X ^ 5 := by positivity
          have : 4 * (N : ℝ) ≤ X ^ 26 * X := mul_le_mul h4 hNX (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = X ^ 32 := by ring
  have hNpos : (0 : ℝ) < N := by linarith
  have hX32pos : 0 < X ^ 32 := by positivity
  have hfin : e ^ 2 * (r * Sg + Δ) ≤ 1 / (N : ℝ) / 2 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have h1 : e ^ 2 * (r * Sg + Δ) * X ^ 32 * (N * 2) ≤ 2 * X ^ 5 * (N * 2) :=
      mul_le_mul_of_nonneg_right hmain (by positivity)
    have h2 : 2 * X ^ 5 * (N * 2) ≤ X ^ 32 := by
      calc 2 * X ^ 5 * (N * 2) = 4 * (N : ℝ) * X ^ 5 := by ring
        _ ≤ X ^ 32 := hbig
    have h3 : e ^ 2 * (r * Sg + Δ) * (N * 2) * X ^ 32 ≤ 1 * X ^ 32 := by
      calc e ^ 2 * (r * Sg + Δ) * (N * 2) * X ^ 32
          = e ^ 2 * (r * Sg + Δ) * X ^ 32 * (N * 2) := by ring
        _ ≤ 2 * X ^ 5 * (N * 2) := h1
        _ ≤ X ^ 32 := h2
        _ = 1 * X ^ 32 := by ring
    exact le_of_mul_le_mul_right h3 hX32pos
  linarith

/-- The exponent bookkeeping of rows A1–A2: `11 p² q ≤ (δ/4)²` for `p = N^{τ₁}`, `q = N^{-τU}`,
`δ = N^{-τU/4}`, once `N^{2τ₁ - τU/2} ≤ 1/176`. -/
private theorem gueBounds_rpow_key {N : ℕ} (hN : 1 ≤ N) {τ₁ τU : ℝ}
    (hsmall : (N : ℝ) ^ (2 * τ₁ - τU / 2) ≤ 1 / 176) :
    11 * ((N : ℝ) ^ τ₁) ^ 2 * (N : ℝ) ^ (-τU) ≤ (gueDelta τU N / 4) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : ((N : ℝ) ^ τ₁) ^ 2 = (N : ℝ) ^ (2 * τ₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  have e2 : (gueDelta τU N) ^ 2 = (N : ℝ) ^ (-(τU / 2)) := by
    unfold gueDelta
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  have e3 : (N : ℝ) ^ (2 * τ₁) * (N : ℝ) ^ (-τU) =
      (N : ℝ) ^ (2 * τ₁ - τU / 2) * (N : ℝ) ^ (-(τU / 2)) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1; ring
  have hδ2 : 0 ≤ (N : ℝ) ^ (-(τU / 2)) := Real.rpow_nonneg hN0.le _
  calc 11 * ((N : ℝ) ^ τ₁) ^ 2 * (N : ℝ) ^ (-τU)
      = 11 * ((N : ℝ) ^ (2 * τ₁ - τU / 2) * (N : ℝ) ^ (-(τU / 2))) := by
        rw [e1, mul_assoc, e3]
    _ ≤ 11 * (1 / 176 * (N : ℝ) ^ (-(τU / 2))) := by gcongr
    _ = (gueDelta τU N / 4) ^ 2 := by rw [div_pow, e2]; ring

/-- `x ≤ p √Λ`, `Λ ≤ q`, `11 p² q ≤ (δ/4)²` give `x ≤ δ/4`. -/
private theorem gueBounds_le_of_sqrt {x p Λ q δ : ℝ} (hx : 0 ≤ x) (hΛ0 : 0 ≤ Λ)
    (hΛq : Λ ≤ q) (hδ : 0 ≤ δ) (hkey : 11 * p ^ 2 * q ≤ (δ / 4) ^ 2)
    (h : x ≤ p * Real.sqrt Λ) : x ≤ δ / 4 := by
  have h2 : x ^ 2 ≤ p ^ 2 * Λ := by
    have := pow_le_pow_left₀ hx h 2
    rwa [mul_pow, Real.sq_sqrt hΛ0] at this
  have hp2 : 0 ≤ p ^ 2 := by positivity
  have h3 : x ^ 2 ≤ (δ / 4) ^ 2 := by
    have : p ^ 2 * Λ ≤ 11 * p ^ 2 * q := by nlinarith
    linarith
  exact (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).1 h3

/-- `x² ≤ 11 p² q ≤ (δ/4)²` gives `x ≤ δ/4`. -/
private theorem gueBounds_le_of_sq {x y δ : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ) (h1 : x ^ 2 ≤ y)
    (h2 : y ≤ (δ / 4) ^ 2) : x ≤ δ / 4 :=
  (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).1 (h1.trans h2)

/-- `x² ≤ 11 p² Λ` and `4 p ≤ P` give `x ≤ P √Λ`. -/
private theorem gueBounds_final {x p P Λ : ℝ} (hx : 0 ≤ x) (hΛ : 0 ≤ Λ) (hp : 0 ≤ p)
    (hP : 4 * p ≤ P) (h : x ^ 2 ≤ 11 * p ^ 2 * Λ) : x ≤ P * Real.sqrt Λ := by
  have hP0 : 0 ≤ P := by linarith
  have hy : 0 ≤ P * Real.sqrt Λ := mul_nonneg hP0 (Real.sqrt_nonneg _)
  refine (pow_le_pow_iff_left₀ hx hy two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt hΛ]
  have h16 : 11 * p ^ 2 ≤ P ^ 2 := by nlinarith
  calc x ^ 2 ≤ 11 * p ^ 2 * Λ := h
    _ ≤ P ^ 2 * Λ := mul_le_mul_of_nonneg_right h16 hΛ

end GueBoundsHelpers

variable (d : Dims)

section GueBoundsGrid

/-- An entry of `G_k - m` is at most `gueDev`. -/
private theorem gueBounds_entry_le_dev (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (ω : Grid.Ωg d)
    (a b : d.Idx N) :
    ‖(green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) -
        mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) a b‖ ≤ gueDev d E t1 t0 K N k ω := by
  unfold gueDev
  exact le_ciSup (f := fun ij : d.Idx N × d.Idx N =>
    ‖(green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) -
        mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖)
    (Set.finite_range _).bddAbove (a, b)

/-- `gueDev` is at most any nonnegative entrywise bound. -/
private theorem gueBounds_dev_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (ω : Grid.Ωg d)
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a b : d.Idx N, ‖(green (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) -
        mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) a b‖ ≤ c) :
    gueDev d E t1 t0 K N k ω ≤ c := by
  unfold gueDev
  exact Real.iSup_le (fun ij => h ij.1 ij.2) hc

/-- A loop deviation is at most `gueDmax`. -/
private theorem gueBounds_le_dmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N n k : ℕ) (ω : Grid.Ωg d)
    (x : LoopData (d.L N) n) :
    ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) x.idx -
        Kt N (Grid.time t1 t0 K N k) x.idx‖ ≤ gueDmax d E t1 t0 K Kt N n k ω := by
  unfold gueDmax
  exact le_ciSup (f := fun y : LoopData (d.L N) n =>
    ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) (Grid.time t1 t0 K N k)) y.idx -
        Kt N (Grid.time t1 t0 K N k) y.idx‖)
    (Set.finite_range _).bddAbove x

/-- The sum of the entries of an increment, on the truncation event. -/
private theorem gueBounds_sum_le (N : ℕ) (w : Ω d)
    (h : ∀ i j : d.Idx N, ‖Xmat d N w i j‖ ≤ N) :
    ∑ i : d.Idx N, ∑ j : d.Idx N, ‖Xmat d N w i j‖ ≤
      ((ouMatrixSize d N : ℕ) : ℝ) ^ 2 * N := by
  have hcard : (Fintype.card (d.Idx N) : ℝ) = ((ouMatrixSize d N : ℕ) : ℝ) := by
    unfold ouMatrixSize
    simp [Fintype.card_prod, ZMod.card]
  calc ∑ i : d.Idx N, ∑ j : d.Idx N, ‖Xmat d N w i j‖
      ≤ ∑ _i : d.Idx N, ∑ _j : d.Idx N, (N : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = (Fintype.card (d.Idx N) : ℝ) ^ 2 * N := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ = _ := by rw [hcard]

/-- **Step 1, local law at step `0`** (row A1): `hB.localLaw` transferred to `Pgue` by the
one-time law `map_gueH_zero`, with `ℓ_{t₁} = L` (`hell`). No measurability of the failure set
is needed (`toMeasurable`). -/
private theorem gueBounds_init {E t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) (ht1 : ∀ N, 0 ≤ t1 N)
    (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1)
    (hell : ∀ᶠ N : ℕ in atTop, (d.L N : ℝ) ^ 2 * (1 - t1 N) ≤ 1)
    (hB : BoundsCoreN (sample d) E t1) :
    StochDom (Pgue d)
      (fun N (ij : d.Idx N × d.Idx N) ω =>
        ‖(green (gueH d t1 t0 K N 0 ω) (zt (E N) (t1 N)) -
          mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖)
      (fun N _ _ => (gueScale d E N (t1 N))⁻¹ ^ ((1 : ℝ) / 2)) := by
  intro τ hτ D hD
  filter_upwards [hB.localLaw τ hτ D hD, hell] with N hN hellN
  have ht1lt : t1 N < 1 := lt_of_le_of_lt (ht10 N) (ht0 N)
  have hscale : (band d).scale (E N) N (t1 N) = gueScale d E N (t1 N) := by
    unfold RBM.Band.scale RBM.Band.ell gueScale
    rw [band_W, band_L, GUEPhase.ellHat_eq_L ht1lt hellN]
    push_cast; ring
  set c : ℝ := (N : ℝ) ^ τ * (gueScale d E N (t1 N))⁻¹ ^ ((1 : ℝ) / 2) with hcdef
  set A : Set (Matrix (d.Idx N) (d.Idx N) ℂ) := ⋃ ij : d.Idx N × d.Idx N,
    {M | c < ‖(green M (zt (E N) (t1 N)) -
      mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖} with hAdef
  have h1 : badSet (fun N (ij : d.Idx N × d.Idx N) ω =>
        ‖(green (gueH d t1 t0 K N 0 ω) (zt (E N) (t1 N)) -
          mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖)
      (fun N _ _ => (gueScale d E N (t1 N))⁻¹ ^ ((1 : ℝ) / 2)) τ N =
      gueH d t1 t0 K N 0 ⁻¹' A := by
    ext ω
    simp only [badSet, Set.mem_ofPred_eq, Set.mem_preimage, hAdef, Set.mem_iUnion, hcdef]
  have h2 : badSet (fun N (ij : (band d).Idx N × (band d).Idx N) ω =>
        (sample d).llErr (E N) N (t1 N) ω ij)
      (fun N _ _ => ((band d).scale (E N) N (t1 N))⁻¹ ^ ((1 : ℝ) / 2)) τ N =
      Hflow d N (t1 N) ⁻¹' A := by
    ext ω
    simp only [badSet, Set.mem_ofPred_eq, Set.mem_preimage, hAdef, Set.mem_iUnion, hscale,
      hcdef]
    rfl
  have hmeasH : Measurable (Hflow d N (t1 N)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Hflow d N (t1 N) i j
  have hmeasG := gueH_measurable d t1 t0 K N 0
  have hmap := map_gueH_zero d t1 t0 K N (ht1 N)
  have hA : MeasurableSet A :=
    MeasurableSet.iUnion fun ij => measurableSet_lt measurable_const (by
      simp only [Matrix.sub_apply]
      exact ((gueEntry_meas_green _ ij.1 ij.2).sub_const _).norm)
  rw [h1, ← Measure.map_apply hmeasG hA, hmap, Measure.map_apply hmeasH hA, ← h2]
  exact hN

end GueBoundsGrid

/-- **(T3)** `W⁻¹ ≤ (S η_u)⁻¹` on `[t₁, t₀]` (`L η_u ≤ L(1 - t₁) ≤ L²(1 - t₁) ≤ 1`). -/
private theorem gueBounds_T3 {E t1 t0 : ℕ → ℝ} (N : ℕ) (hEb : |E N| < 2) (ht0 : t0 N < 1)
    (hellN : (d.L N : ℝ) ^ 2 * (1 - t1 N) ≤ 1) {u : ℝ} (hu : u ∈ Set.Icc (t1 N) (t0 N)) :
    ((d.W N : ℕ) : ℝ)⁻¹ ≤ (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u)⁻¹ := by
  have hmim : 0 < (mE (E N)).im := mE_im_pos hEb
  have hmim1 : (mE (E N)).im ≤ 1 := gueBounds_mE_im_le_one hEb
  have hW : (0 : ℝ) < ((d.W N : ℕ) : ℝ) := by exact_mod_cast d.W_pos N
  have hL1 : (1 : ℝ) ≤ (d.L N : ℝ) := by
    have := d.three_le_L N; exact_mod_cast (by omega : 1 ≤ d.L N)
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have h1t : 0 ≤ 1 - t1 N := by linarith [hu.1]
  have hηpos : 0 < etaT (E N) u := mul_pos hu1 hmim
  have hSpos : (0 : ℝ) < ((d.L N * d.W N : ℕ) : ℝ) := by
    have := d.W_pos N; have := d.three_le_L N; positivity
  have hstep1 : (1 - u) * (mE (E N)).im ≤ (1 - t1 N) * 1 :=
    mul_le_mul (by linarith [hu.1]) hmim1 hmim.le h1t
  have hLη : (d.L N : ℝ) * etaT (E N) u ≤ 1 := by
    change (d.L N : ℝ) * ((1 - u) * (mE (E N)).im) ≤ 1
    calc (d.L N : ℝ) * ((1 - u) * (mE (E N)).im) ≤ (d.L N : ℝ) * ((1 - t1 N) * 1) :=
          mul_le_mul_of_nonneg_left hstep1 (by linarith)
      _ = (d.L N : ℝ) * (1 - t1 N) := by rw [mul_one]
      _ ≤ (d.L N : ℝ) * (d.L N : ℝ) * (1 - t1 N) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) hL1) h1t
      _ = (d.L N : ℝ) ^ 2 * (1 - t1 N) := by rw [sq]
      _ ≤ 1 := hellN
  have hSη : ((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u ≤ ((d.W N : ℕ) : ℝ) := by
    have e : ((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u
        = ((d.W N : ℕ) : ℝ) * ((d.L N : ℝ) * etaT (E N) u) := by push_cast; ring
    rw [e]
    calc ((d.W N : ℕ) : ℝ) * ((d.L N : ℝ) * etaT (E N) u) ≤ ((d.W N : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hLη hW.le
      _ = ((d.W N : ℕ) : ℝ) := mul_one _
  exact inv_anti₀ (mul_pos hSpos hηpos) hSη

/-- **Row J2**: the increment term of `gueDev_succ_le` is at most `δ_N / 2` on the truncation
event. -/
private theorem gueBounds_jump_le {τU : ℝ} (n0 : ℕ) {E t1 t0 : ℕ → ℝ} (N : ℕ) (hN1 : 1 ≤ N)
    (hτU : 0 < τU) (hEb : |E N| < 2) (ht1 : 0 ≤ t1 N) (ht10 : t1 N ≤ t0 N) (ht0 : t0 N < 1)
    (hscN : ∀ t ∈ Set.Icc (t1 N) (t0 N),
      (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) t)⁻¹ ≤ (N : ℝ) ^ (-τU))
    (hdimN : d.W N * d.L N ≤ N) (j : ℕ) (ω : Grid.Ωg d)
    (hF : ∀ i i' : d.Idx N, ‖Xmat d N (ω (j + 1)) i i'‖ ≤ N) :
    (etaT (E N) (t0 N))⁻¹ ^ 2 *
        (Real.sqrt (Grid.step t1 t0 (gueGridK n0) N / (ouMatrixSize d N : ℝ)) *
          ∑ i : d.Idx N, ∑ i' : d.Idx N, ‖Xmat d N (ω (j + 1)) i i'‖ +
          Grid.step t1 t0 (gueGridK n0) N) ≤ gueDelta τU N / 2 := by
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hK0 : gueGridK n0 N ≠ 0 := gueGridK_ne_zero n0 N
  have hmim : 0 < (mE (E N)).im := mE_im_pos hEb
  have hmim1 : (mE (E N)).im ≤ 1 := gueBounds_mE_im_le_one hEb
  have hMpos : (0 : ℝ) < (ouMatrixSize d N : ℝ) := by exact_mod_cast ouMatrixSize_pos d N
  have hS1 : (1 : ℝ) ≤ (ouMatrixSize d N : ℝ) := by exact_mod_cast ouMatrixSize_pos d N
  have hSN : (ouMatrixSize d N : ℝ) ≤ N := by
    unfold ouMatrixSize; rw [Nat.mul_comm]; exact_mod_cast hdimN
  have ht0m : t0 N ∈ Set.Icc (t1 N) (t0 N) := ⟨ht10, le_rfl⟩
  have hη0 : 0 < etaT (E N) (t0 N) := mul_pos (by linarith) hmim
  have hsc0 : ((ouMatrixSize d N : ℝ) * etaT (E N) (t0 N))⁻¹ ≤ (N : ℝ) ^ (-τU) :=
    hscN (t0 N) ht0m
  have hq1 : (N : ℝ) ^ (-τU) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  have hone : 1 ≤ (ouMatrixSize d N : ℝ) * etaT (E N) (t0 N) := by
    have := hsc0.trans hq1
    rwa [inv_le_one₀ (mul_pos hMpos hη0)] at this
  have heS : (etaT (E N) (t0 N))⁻¹ ≤ (ouMatrixSize d N : ℝ) := by
    calc (etaT (E N) (t0 N))⁻¹ = (etaT (E N) (t0 N))⁻¹ * 1 := (mul_one _).symm
      _ ≤ (etaT (E N) (t0 N))⁻¹ * ((ouMatrixSize d N : ℝ) * etaT (E N) (t0 N)) :=
          mul_le_mul_of_nonneg_left hone (inv_nonneg.2 hη0.le)
      _ = (ouMatrixSize d N : ℝ) := by field_simp
  have hΔ0 : 0 ≤ Grid.step t1 t0 (gueGridK n0) N := gueEntry_step_nonneg ht10
  have hΔ : Grid.step t1 t0 (gueGridK n0) N * ((N : ℝ) + 1) ^ 64 ≤ 1 := by
    have hKc : ((gueGridK n0 N : ℕ) : ℝ) = ((N : ℝ) + 1) ^ (32 * n0 + 64) := by
      unfold gueGridK; push_cast; ring
    have hKpos : (0 : ℝ) < (gueGridK n0 N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hK0
    have hXK : ((N : ℝ) + 1) ^ 64 ≤ (gueGridK n0 N : ℝ) := by
      rw [hKc]; exact pow_le_pow_right₀ (by linarith) (by omega)
    calc Grid.step t1 t0 (gueGridK n0) N * ((N : ℝ) + 1) ^ 64
        ≤ Grid.step t1 t0 (gueGridK n0) N * (gueGridK n0 N : ℝ) :=
          mul_le_mul_of_nonneg_left hXK hΔ0
      _ = t0 N - t1 N := by unfold Grid.step; field_simp
      _ ≤ 1 := by linarith
  have hSg := gueBounds_sum_le d N (ω (j + 1)) hF
  have hδ1 : 1 / (N : ℝ) ≤ gueDelta τU N := by
    have hη01 : etaT (E N) (t0 N) ≤ 1 := by
      change (1 - t0 N) * (mE (E N)).im ≤ 1
      calc (1 - t0 N) * (mE (E N)).im ≤ 1 * 1 :=
            mul_le_mul (by linarith) hmim1 hmim.le (by norm_num)
        _ = 1 := one_mul 1
    calc 1 / (N : ℝ) ≤ (ouMatrixSize d N : ℝ)⁻¹ := by
          rw [one_div]; exact inv_anti₀ hMpos hSN
      _ ≤ ((ouMatrixSize d N : ℝ) * etaT (E N) (t0 N))⁻¹ :=
          inv_anti₀ (mul_pos hMpos hη0) (mul_le_of_le_one_right hMpos.le hη01)
      _ ≤ (N : ℝ) ^ (-τU) := hsc0
      _ ≤ gueDelta τU N := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hSg0 : 0 ≤ ∑ i : d.Idx N, ∑ i' : d.Idx N, ‖Xmat d N (ω (j + 1)) i i'‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  exact gueBounds_jump hN1 hS1 hSN (inv_nonneg.2 hη0.le) heS hΔ0 hΔ hSg0 hSg hδ1

/-- **Unfreezing and conclusion, pathwise at a fixed `N` and `ω`** (rows
A1–A2, J2, T3): on the good events, the a-priori threshold `gueDelta τU` is never reached on the
grid, the freezing index never acts, and the bootstrap outputs give (7.28) and the local law at
every grid time. -/
private theorem gueBounds_path {τU : ℝ} (n0 : ℕ) (hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ}
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) (N : ℕ) (hN1 : 1 ≤ N) (hτU : 0 < τU)
    (hEb : |E N| < 2) (ht1 : 0 ≤ t1 N) (ht10 : t1 N ≤ t0 N) (ht0 : t0 N < 1)
    {τ τ₁ : ℝ} (hτ₁0 : 0 < τ₁) (hτ₁τ : τ₁ < τ)
    (hscN : ∀ t ∈ Set.Icc (t1 N) (t0 N),
      (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) t)⁻¹ ≤ (N : ℝ) ^ (-τU))
    (hellN : (d.L N : ℝ) ^ 2 * (1 - t1 N) ≤ 1)
    (hdimN : d.W N * d.L N ≤ N)
    (hsmallN : (N : ℝ) ^ (2 * τ₁ - τU / 2) ≤ 1 / 176)
    (h4N : 4 ≤ (N : ℝ) ^ (τ - τ₁))
    (ω : Grid.Ωg d)
    (hA : ∀ u : TimeIcc t1 t0 N × Set.Icc 2 (2 * n0),
      gueLproc d E t1 t0 (gueGridK n0) (gueDelta τU) N u.2 u.1 ω ≤
        (N : ℝ) ^ τ₁ * (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u.1)⁻¹ ^ ((u.2 : ℕ) - 1))
    (hB : ∀ u : TimeIcc t1 t0 N × Set.Icc 1 n0,
      gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N u.2 u.1 ω ≤
        (N : ℝ) ^ τ₁ * (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u.1)⁻¹ ^ (u.2 : ℕ))
    (hC : ∀ u : Fin (gueGridK n0 N + 1) × (d.Idx N × d.Idx N),
      {ω' | ∀ i j, ‖(green (gueH d t1 t0 (gueGridK n0) N u.1 ω')
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N u.1)) -
            mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j‖ ≤ gueDelta τU N}.indicator
          (fun ω' => ‖(green (gueH d t1 t0 (gueGridK n0) N u.1 ω')
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N u.1)) -
            mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) u.2.1 u.2.2‖ ^ 2) ω ≤
        (N : ℝ) ^ τ₁ * (9 * loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N u.1 ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N u.1)) 2 + 2 * ((d.W N : ℕ) : ℝ)⁻¹))
    (hD : ∀ ij : d.Idx N × d.Idx N,
      ‖(green (gueH d t1 t0 (gueGridK n0) N 0 ω) (zt (E N) (t1 N)) -
          mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖ ≤
        (N : ℝ) ^ τ₁ * (gueScale d E N (t1 N))⁻¹ ^ ((1 : ℝ) / 2))
    (hF : ∀ k, 1 ≤ k → k ≤ gueGridK n0 N → ∀ i j : d.Idx N, ‖Xmat d N (ω k) i j‖ ≤ N) :
    (∀ n, 1 ≤ n → n ≤ n0 → ∀ (k : Fin (gueGridK n0 N + 1)) (x : LoopData (d.L N) n),
        ‖gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N k ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) x.idx
          - Kt N (Grid.time t1 t0 (gueGridK n0) N k) x.idx‖ ≤
          (N : ℝ) ^ τ * (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^ n) ∧
      (∀ (k : Fin (gueGridK n0 N + 1)) (i j : d.Idx N),
        ‖(green (gueH d t1 t0 (gueGridK n0) N k ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) -
          mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j‖ ≤
          (N : ℝ) ^ τ * (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^
            ((1 : ℝ) / 2)) := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hp1 : 1 ≤ (N : ℝ) ^ τ₁ := Real.one_le_rpow hN1' hτ₁0.le
  have hp0 : 0 ≤ (N : ℝ) ^ τ₁ := by linarith
  have hδpos : 0 < gueDelta τU N := Real.rpow_pos_of_pos hN0 _
  have hK0 : gueGridK n0 N ≠ 0 := gueGridK_ne_zero n0 N
  have hmim : 0 < (mE (E N)).im := mE_im_pos hEb
  have hmim1 : (mE (E N)).im ≤ 1 := gueBounds_mE_im_le_one hEb
  have hSpos : (0 : ℝ) < ((d.L N * d.W N : ℕ) : ℝ) :=
    Nat.cast_pos.2 (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (d.W_pos N))
  have hη : ∀ u ∈ Set.Icc (t1 N) (t0 N), 0 < etaT (E N) u := fun u hu =>
    mul_pos (by linarith [hu.2]) hmim
  have htime : ∀ k ≤ gueGridK n0 N,
      Grid.time t1 t0 (gueGridK n0) N k ∈ Set.Icc (t1 N) (t0 N) :=
    fun k hk => ⟨gueEntry_time_ge ht10, gueEntry_time_le ht10 hK0 hk⟩
  have hΛ0 : ∀ u ∈ Set.Icc (t1 N) (t0 N),
      0 ≤ (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u)⁻¹ :=
    fun u hu => (inv_pos.2 (mul_pos hSpos (hη u hu))).le
  have hT3 : ∀ u ∈ Set.Icc (t1 N) (t0 N),
      ((d.W N : ℕ) : ℝ)⁻¹ ≤ (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u)⁻¹ :=
    fun u hu => gueBounds_T3 d N hEb ht0 hellN hu
  have hkey : 11 * ((N : ℝ) ^ τ₁) ^ 2 * (N : ℝ) ^ (-τU) ≤ (gueDelta τU N / 4) ^ 2 :=
    gueBounds_rpow_key hN1 hsmallN
  -- D4a at an unfrozen step below the threshold: `|(G_j - m)_{ab}|² ≤ 11 p² Λ_{u_j}`
  have hsq : ∀ j ≤ gueGridK n0 N, j ≤ gueStop d E t1 t0 (gueGridK n0) (gueDelta τU) N ω →
      gueDev d E t1 t0 (gueGridK n0) N j ω < gueDelta τU N → ∀ a b : d.Idx N,
      ‖(green (gueH d t1 t0 (gueGridK n0) N j ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) -
        mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) a b‖ ^ 2 ≤
        11 * ((N : ℝ) ^ τ₁) ^ 2 *
          (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ := by
    intro j hj hjσ hdev a b
    have hmem : ω ∈ {ω' | ∀ i j', ‖(green (gueH d t1 t0 (gueGridK n0) N j ω')
        (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) -
        mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j'‖ ≤ gueDelta τU N} :=
      fun i j' => (gueBounds_entry_le_dev d E t1 t0 (gueGridK n0) N j ω i j').trans hdev.le
    have hCj := hC (⟨j, Nat.lt_succ_of_le hj⟩, (a, b))
    rw [Set.indicator_of_mem hmem] at hCj
    have hAj := hA (⟨Grid.time t1 t0 (gueGridK n0) N j, htime j hj⟩, ⟨2, le_rfl, by omega⟩)
    have hAj' : loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
        (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) 2 ≤ (N : ℝ) ^ τ₁ *
          (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ := by
      have e := gueLproc_time d E t1 t0 (gueGridK n0) (gueDelta τU) N 2 j ht10 hj ω
      rw [Nat.min_eq_left hjσ] at e
      have h21 : (2 : ℕ) - 1 = 1 := rfl
      have h : gueLproc d E t1 t0 (gueGridK n0) (gueDelta τU) N 2
          (Grid.time t1 t0 (gueGridK n0) N j) ω ≤ (N : ℝ) ^ τ₁ *
          (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ ^
            ((2 : ℕ) - 1) := hAj
      rw [e, h21, pow_one] at h
      exact h
    exact (gueBounds_sq_le hp1 hAj' (hT3 _ (htime j hj)) (hscN _ (htime j hj))
      (hΛ0 _ (htime j hj)) hCj).1
  have hσ : ∀ k ≤ gueGridK n0 N,
      (∀ i ≤ k, gueDev d E t1 t0 (gueGridK n0) N i ω < gueDelta τU N) →
      k ≤ gueStop d E t1 t0 (gueGridK n0) (gueDelta τU) N ω :=
    fun k hk h => gueBounds_le_firstHit
      (fun k ω' => gueDev d E t1 t0 (gueGridK n0) N k ω') (gueDelta τU N) (gueGridK n0 N) ω hk h
  -- row A1: step `0`
  have h0 : gueDev d E t1 t0 (gueGridK n0) N 0 ω < gueDelta τU N := by
    have hle : gueDev d E t1 t0 (gueGridK n0) N 0 ω ≤ gueDelta τU N / 4 := by
      refine gueBounds_dev_le d E t1 t0 (gueGridK n0) N 0 ω (by positivity) fun a b => ?_
      have h := hD (a, b)
      rw [← Real.sqrt_eq_rpow] at h
      have hmem1 : t1 N ∈ Set.Icc (t1 N) (t0 N) := ⟨le_rfl, ht10⟩
      have hx := gueBounds_le_of_sqrt (norm_nonneg _) (hΛ0 _ hmem1) (hscN _ hmem1) hδpos.le
        hkey h
      rw [Grid.time_zero]
      exact hx
    linarith
  -- row J2: the one-step jump
  have hjump : ∀ j < gueGridK n0 N, gueDev d E t1 t0 (gueGridK n0) N (j + 1) ω ≤
      gueDev d E t1 t0 (gueGridK n0) N j ω + gueDelta τU N / 2 := fun j hj =>
    (gueDev_succ_le d E t1 t0 (gueGridK n0) N j hEb ht10 ht0 hj ω).trans
      (add_le_add le_rfl (gueBounds_jump_le d n0 N hN1 hτU hEb ht1 ht10 ht0 hscN hdimN j ω
        (fun a b => hF (j + 1) (by omega) (by omega) a b)))
  -- row A2: the inductive step below the threshold
  have hstep : ∀ j < gueGridK n0 N, j ≤ gueStop d E t1 t0 (gueGridK n0) (gueDelta τU) N ω →
      gueDev d E t1 t0 (gueGridK n0) N j ω < gueDelta τU N →
      gueDev d E t1 t0 (gueGridK n0) N j ω ≤ gueDelta τU N / 4 := by
    intro j hj hjσ hdev
    refine gueBounds_dev_le d E t1 t0 (gueGridK n0) N j ω (by positivity) fun a b => ?_
    have hq : 11 * ((N : ℝ) ^ τ₁) ^ 2 *
        (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ ≤
        11 * ((N : ℝ) ^ τ₁) ^ 2 * (N : ℝ) ^ (-τU) :=
      mul_le_mul_of_nonneg_left (hscN _ (htime j hj.le)) (by positivity)
    exact gueBounds_le_of_sq (norm_nonneg _) hδpos.le (hsq j hj.le hjσ hdev a b) (hq.trans hkey)
  have hall := gueBounds_unfreeze (K := gueGridK n0 N)
    (fun k => gueDev d E t1 t0 (gueGridK n0) N k ω)
    (gueStop d E t1 t0 (gueGridK n0) (gueDelta τU) N ω) hσ h0 hstep hjump hδpos
  have hdev : ∀ k ≤ gueGridK n0 N, gueDev d E t1 t0 (gueGridK n0) N k ω < gueDelta τU N :=
    fun k hk => hall k hk k le_rfl
  have hkσ : ∀ k ≤ gueGridK n0 N, k ≤ gueStop d E t1 t0 (gueGridK n0) (gueDelta τU) N ω :=
    fun k hk => hσ k hk (hall k hk)
  have hpτ : (N : ℝ) ^ τ₁ ≤ (N : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hN1' hτ₁τ.le
  refine ⟨fun n hn1 hn k x => ?_, fun k i j => ?_⟩
  · have hk : (k : ℕ) ≤ gueGridK n0 N := Nat.lt_succ_iff.1 k.2
    have h1 := gueBounds_le_dmax d E t1 t0 (gueGridK n0) Kt N n k ω x
    have h2 := gueDproc_time d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N n k ht10 hk ω
    rw [Nat.min_eq_left (hkσ k hk)] at h2
    have h3 : gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N n
        (Grid.time t1 t0 (gueGridK n0) N k) ω ≤ (N : ℝ) ^ τ₁ *
        (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^ n :=
      hB (⟨Grid.time t1 t0 (gueGridK n0) N k, htime k hk⟩, ⟨n, hn1, hn⟩)
    rw [h2] at h3
    calc _ ≤ _ := h1
      _ ≤ _ := h3
      _ ≤ (N : ℝ) ^ τ * (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right hpτ (pow_nonneg (hΛ0 _ (htime k hk)) n)
  · have hk : (k : ℕ) ≤ gueGridK n0 N := Nat.lt_succ_iff.1 k.2
    have hx2 := hsq k hk (hkσ k hk) (hdev k hk) i j
    have hP : 4 * (N : ℝ) ^ τ₁ ≤ (N : ℝ) ^ τ := by
      have e : (N : ℝ) ^ τ = (N : ℝ) ^ (τ - τ₁) * (N : ℝ) ^ τ₁ := by
        rw [← Real.rpow_add hN0]; ring_nf
      rw [e]; exact mul_le_mul_of_nonneg_right h4N hp0
    have hΛ := hΛ0 _ (htime k hk)
    rw [← Real.sqrt_eq_rpow]
    change _ ≤ (N : ℝ) ^ τ * Real.sqrt
      (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) (Grid.time t1 t0 (gueGridK n0) N k))⁻¹
    exact gueBounds_final (norm_nonneg _) hΛ hp0 hP hx2

/-! ### The main statement -/

theorem gueGrid_pathBounds {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 2 ≤ n0)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ) (ht1 : ∀ N, 0 ≤ t1 N)
    (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1)
    (h730 : ∀ᶠ N : ℕ in atTop, t0 N - t1 N ≤ (N : ℝ) ^ (-τU) * etaT (E N) (t0 N))
    (hscale : ∀ᶠ N : ℕ in atTop, (gueScale d E N (t0 N))⁻¹ ≤ (N : ℝ) ^ (-τU))
    (hell : ∀ᶠ N : ℕ in atTop, (d.L N : ℝ) ^ 2 * (1 - t1 N) ≤ 1)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ)
    (hKinit : ∀ N I, Kt N (t1 N) I = (band d).Kval (E N) N (t1 N) I)
    (hK : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (d.L N)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt N s I) (GUEPhase.primRhsGUE (d.L N) (d.W N) (Kt N t) I)
        (Set.Icc (t1 N) (t0 N)) t)
    (hB : BoundsCoreN (sample d) E t1) :
    GUEPathBounds d E t1 t0 (gueGridK n0) n0 Kt := by
  classical
  /- Deterministic facts on `η = etaT (E N)` (the side conditions of the bootstraps). -/
  have hEb : ∀ N, |E N| < 2 := fun N => lt_of_le_of_lt (hE N) (by linarith)
  have hmim : ∀ N, 0 < (mE (E N)).im := fun N => mE_im_pos (hEb N)
  have hmim1 : ∀ N, (mE (E N)).im ≤ 1 := fun N => gueBounds_mE_im_le_one (hEb N)
  have hηeq : ∀ N u, etaT (E N) u = (1 - u) * (mE (E N)).im := fun N u => rfl
  have hη : ∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), 0 < etaT (E N) t := fun N t ht => by
    rw [hηeq]; exact mul_pos (by linarith [ht.2, ht0 N]) (hmim N)
  have hanti : ∀ N, ∀ u ∈ Set.Icc (t1 N) (t0 N), ∀ t ∈ Set.Icc (t1 N) (t0 N), u ≤ t →
      etaT (E N) t ≤ etaT (E N) u := fun N u _ t _ hut => by
    rw [hηeq, hηeq]; exact mul_le_mul_of_nonneg_right (by linarith) (hmim N).le
  have hηc : ∀ N, ContinuousOn (etaT (E N)) (Set.Icc (t1 N) (t0 N)) := fun N => by
    have e : etaT (E N) = fun u => (1 - u) * (mE (E N)).im := funext fun u => rfl
    rw [e]; exact ((continuous_const.sub continuous_id).mul continuous_const).continuousOn
  have hSpos : ∀ N, (0 : ℝ) < ((d.L N * d.W N : ℕ) : ℝ) := fun N =>
    Nat.cast_pos.2 (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (d.W_pos N))
  have ht0mem : ∀ N, t0 N ∈ Set.Icc (t1 N) (t0 N) := fun N => ⟨ht10 N, le_rfl⟩
  have h730' : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (t1 N) (t0 N),
      t - t1 N ≤ (N : ℝ) ^ (-τU) * etaT (E N) t := by
    filter_upwards [h730] with N hN t ht
    have h1 := hanti N t ht (t0 N) (ht0mem N) ht.2
    calc t - t1 N ≤ t0 N - t1 N := by linarith [ht.2]
      _ ≤ (N : ℝ) ^ (-τU) * etaT (E N) (t0 N) := hN
      _ ≤ (N : ℝ) ^ (-τU) * etaT (E N) t :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hscale' : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (t1 N) (t0 N),
      (((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) t)⁻¹ ≤ (N : ℝ) ^ (-τU) := by
    filter_upwards [hscale] with N hN t ht
    refine le_trans ?_ hN
    unfold gueScale
    have h0 := hη N (t0 N) (ht0mem N)
    have h1 := hanti N t ht (t0 N) (ht0mem N) ht.2
    exact inv_anti₀ (mul_pos (hSpos N) h0) (mul_le_mul_of_nonneg_left h1 (hSpos N).le)
  /- The bootstraps: `eq727GE` at `2 n₀`, then `eq728G`. -/
  have hN : ∀ N, (0 : ℝ) < ((d.L N * d.W N : ℕ) : ℝ) := hSpos
  have h727 := GUEPhase.eq727GE (P := Pgue d) (n0 := 2 * n0) (even_two_mul n0)
    (fun N => ((d.L N * d.W N : ℕ) : ℝ)) (fun N => etaT (E N)) t1 t0
    (fun N m t ω => gueLproc d E t1 t0 (gueGridK n0) (gueDelta τU) N m t ω)
    (fun N m t ω => gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N m t ω)
    (fun N m t => gueKproc d t1 t0 (gueGridK n0) Kt N m t)
    hN ht10 hη hanti hηc hτU h730' hscale'
    (fun N m t ω => gueLproc_nonneg d E t1 t0 _ _ N m t ω)
    (fun N m t ω => gueDproc_nonneg d E t1 t0 _ _ Kt N m t ω)
    (fun N ω m _ t _ => gueLproc_le d E t1 t0 _ _ Kt N m t ω)
    (fun N ω m _ t _ => gueDproc_le d E t1 t0 _ _ Kt N m t ω)
    (fun N ω l hl _ t _ => gueLproc_odd d E t1 t0 _ _ N l hl t ω)
    (gueKproc_unifDetDom d hκ hτU n0 hE ht1 ht10 ht0 h730 hscale hell Kt hKinit hK)
    (HighProb.of_eventually_univ (Filter.Eventually.of_forall
      fun N ω m _ _ => gueLproc_continuousOn d E t1 t0 _ _ N m ω))
    (gueBds_h745E d hκ hτU n0 hn0 hE ht1 ht10 ht0 h730 hscale hell Kt hKinit hK hB)
  have h728 := GUEPhase.eq728G (P := Pgue d) (n0 := n0)
    (fun N => ((d.L N * d.W N : ℕ) : ℝ)) (fun N => etaT (E N)) t1 t0
    (fun N m t ω => gueLproc d E t1 t0 (gueGridK n0) (gueDelta τU) N m t ω)
    (fun N m t ω => gueDproc d E t1 t0 (gueGridK n0) (gueDelta τU) Kt N m t ω)
    hN ht10 hη hanti hηc hτU h730' hscale'
    (fun N m t ω => gueLproc_nonneg d E t1 t0 _ _ N m t ω)
    (fun N m t ω => gueDproc_nonneg d E t1 t0 _ _ Kt N m t ω) h727
    (HighProb.of_eventually_univ (Filter.Eventually.of_forall
      fun N ω m _ => gueDproc_continuousOn d E t1 t0 _ _ Kt N m ω))
    (gueBds_h746 d hκ hτU n0 hn0 hE ht1 ht10 ht0 h730 hscale hell Kt hKinit hK hB)
  /- The other random inputs: the entry bound with `δ = N^{-τU/4}`, the step-`0` local law,
  truncation. -/
  have hD4 := gueGrid_entry_bound d hκ hτU n0 hE ht1 ht10 ht0 h730
    (δ := gueDelta τU) (fun N => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := τU / 4)
    (by positivity) (Filter.Eventually.of_forall fun N => le_rfl)
  have hinit := gueBounds_init d (gueGridK n0) (t0 := t0) ht1 ht10 ht0 hell hB
  have hF := gue_highProb_incr_le (d := d) n0
  /- Unfreezing and conclusion on the intersection of the good events. -/
  have hmain : ∀ τ > (0 : ℝ), HighProb (Pgue d) (fun N => {ω |
      (∀ n, 1 ≤ n → n ≤ n0 → ∀ (k : Fin (gueGridK n0 N + 1)) (x : LoopData (d.L N) n),
        ‖gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N k ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) x.idx
          - Kt N (Grid.time t1 t0 (gueGridK n0) N k) x.idx‖ ≤
          (N : ℝ) ^ τ * (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^ n) ∧
      (∀ (k : Fin (gueGridK n0 N + 1)) (i j : d.Idx N),
        ‖(green (gueH d t1 t0 (gueGridK n0) N k ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) -
          mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j‖ ≤
          (N : ℝ) ^ τ * (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^
            ((1 : ℝ) / 2))}) := by
    intro τ hτ
    set τ₁ : ℝ := min τ τU / 16 with hτ₁
    have hτ₁0 : 0 < τ₁ := by have := lt_min hτ hτU; positivity
    have hτ₁τ : τ₁ < τ := by have := min_le_left τ τU; have := lt_min hτ hτU; linarith
    have hτ₁U : τ₁ ≤ τU / 16 := by have := min_le_right τ τU; linarith
    have hev := ((((h727.highProb hτ₁0).inter (h728.highProb hτ₁0)).inter
      (hD4.highProb hτ₁0)).inter (hinit.highProb hτ₁0)).inter hF
    refine hev.mono ?_
    have hneg : 2 * τ₁ - τU / 2 < 0 := by linarith
    filter_upwards [hscale', hscale, hell, d.dim, eventually_ge_atTop 1,
      GUEPhase.eventually_rpow_le_of_neg hneg (by norm_num : (0 : ℝ) < 1 / 176),
      RBM.eventually_le_rpow 4 (sub_pos.2 hτ₁τ)]
      with N hscN hsc0N hellN hdimN hN1 hsmallN h4N
    rintro ω ⟨⟨⟨⟨hA, hBω⟩, hC⟩, hD⟩, hFω⟩
    exact gueBounds_path d n0 hn0 Kt N hN1 hτU (hEb N) (ht1 N) (ht10 N) (ht0 N) hτ₁0 hτ₁τ hscN hellN
      hdimN.1 hsmallN h4N ω hA hBω hC hD hFω
  refine ⟨fun n hn1 hn => ?_, ?_⟩
  · exact GUEPhase.stochDom_of_forall_highProb fun τ hτ =>
      (hmain τ hτ).mono (Filter.Eventually.of_forall fun N ω hω u => hω.1 n hn1 hn u.1 u.2)
  · exact GUEPhase.stochDom_of_forall_highProb fun τ hτ =>
      (hmain τ hτ).mono (Filter.Eventually.of_forall fun N ω hω u => hω.2 u.1 u.2.1 u.2.2)

end RBM.Gauss.GUEGrid
