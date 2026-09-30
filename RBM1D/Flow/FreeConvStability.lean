/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.FreeConvolution
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Stability of the free convolution near the semicircle

Deterministic input for Theorem 2.6 Step 1: if the Stieltjes
transform of `v` (already shifted by `E₀`) is `ε`-close to that of the semicircle of variance
`s = 1 - t` on a region `Im w ≥ c₀ t / 4`, then the free convolution `v ⊞ sc_t`
(`freeConvST`, [51, (2.5)]) is `C₀ ε`-close to `m_sc(E₀ + iη)`, and the limit
`ρ_fc,t(0) = lim_{η↓0} Im m_fc,t(iη)/π` of [51, (2.6)] exists and is `C₀ ε`-close to `ρ_sc(E₀)`.

Route: `ω_sc(η) = iη + t m_sc(E₀ + iη)` solves the unperturbed subordination equation; the map
`F(ω) = iη + t m_v(ω)` is a `1/2`-contraction of `B̄(ω_sc, 2tε)` into itself (Cauchy estimates
for `m_v - m_ref` on discs of radius `≍ t`, and the explicit Lipschitz bound of `m_sc` in the
bulk); the fixed point is identified with `freeConvST` by the uniqueness of
`Flow/FreeConvolution.lean`; the fixed points are
`2`-Lipschitz in `η`, which gives the limit `η ↓ 0`.  Continuity of `m_sc` up to the real axis
in the bulk (`msc (E + iη) → mE E`) is proved here.

* `FreeConvStability.freeConv_stable_local`: the stability statement above, with the closeness
  hypothesis only on the bulk strip `|Re w| ≤ min κ 1 / 16`, `Im w ≤ 1/2` (conclusion for
  `η ≤ 1/4`); this is the form that bulk local laws can supply.
-/

open Filter Topology

namespace RBM.Gauss

/-! ### 1. The semicircle Stieltjes transform: stability, continuity, differentiability -/

/-- Difference identity for two roots of `m² + z m + 1 = 0`. -/
private lemma fcs_quad_diff {a z : ℂ} (ha : a * (a + z) = -1) (z' : ℂ) :
    (msc z' - a) * (a + msc z' + z') = -((z' - z) * a) := by
  have h := msc_mul z'
  linear_combination h - ha

private lemma fcs_im_le_denom (a : ℂ) {z' : ℂ} (hz' : 0 < z'.im) :
    a.im ≤ (a + msc z' + z').im := by
  have h := msc_add_eq_neg_inv hz'
  have hm := msc_im_pos hz'
  have hne : msc z' ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hm; exact lt_irrefl _ hm
  have hpos : 0 < (msc z' + z').im := by
    rw [h, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hm (Complex.normSq_pos.mpr hne)
  have : (a + msc z' + z').im = a.im + (msc z' + z').im := by
    simp only [Complex.add_im]; ring
  linarith

/-- **Stability of the upper root**: if `a (a + z) = -1` with `Im a ≥ 0`, then
`‖m_sc(z') - a‖ Im a ≤ ‖z' - z‖ ‖a‖` for `Im z' > 0`. -/
private lemma fcs_msc_sub_mul_im_le {a z z' : ℂ} (ha : a * (a + z) = -1)
    (hz' : 0 < z'.im) : ‖msc z' - a‖ * a.im ≤ ‖z' - z‖ * ‖a‖ := by
  have h1 : a.im ≤ ‖a + msc z' + z'‖ :=
    (fcs_im_le_denom a hz').trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  calc ‖msc z' - a‖ * a.im ≤ ‖msc z' - a‖ * ‖a + msc z' + z'‖ :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖z' - z‖ * ‖a‖ := by
        rw [← norm_mul, fcs_quad_diff ha z', norm_neg, norm_mul]

private lemma fcs_msc_lip {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im) :
    ‖msc z' - msc z‖ * (msc z).im ≤ ‖z' - z‖ := by
  refine (fcs_msc_sub_mul_im_le (msc_mul z) hz').trans ?_
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_msc_lt_one hz).le

private lemma fcs_eventually_im_pos {z : ℂ} (hz : 0 < z.im) : ∀ᶠ z' in 𝓝 z, 0 < z'.im :=
  (Complex.continuous_im.tendsto z).eventually (lt_mem_nhds hz)

private lemma fcs_msc_continuousAt {z : ℂ} (hz : 0 < z.im) : ContinuousAt msc z := by
  have hm := msc_im_pos hz
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun z' : ℂ => ‖z' - z‖ / (msc z).im) (𝓝 z) (𝓝 0) := by
    have h1 : Tendsto (fun z' : ℂ => ‖z' - z‖) (𝓝 z) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_id (x := 𝓝 z))
    simpa using h1.div_const (msc z).im
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [fcs_eventually_im_pos hz] with z' hz'
  rw [le_div_iff₀ hm]
  exact fcs_msc_lip hz hz'

private lemma fcs_msc_hasDerivAt {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt msc (-(msc z) / (msc z + msc z + z)) z := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hden : ∀ z' : ℂ, 0 < z'.im → msc z + msc z' + z' ≠ 0 := fun z' hz' h0 => by
    have h := fcs_im_le_denom (msc z) hz'
    rw [h0, Complex.zero_im] at h
    exact absurd (msc_im_pos hz) (not_lt.mpr h)
  have hcont : Tendsto (fun z' => -(msc z) / (msc z + msc z' + z')) (𝓝 z)
      (𝓝 (-(msc z) / (msc z + msc z + z))) :=
    tendsto_const_nhds.div ((tendsto_const_nhds.add (fcs_msc_continuousAt hz)).add tendsto_id)
      (hden z hz)
  refine (hcont.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (fcs_eventually_im_pos hz),
    self_mem_nhdsWithin] with z' hz' hne
  have hne' : z' - z ≠ 0 := sub_ne_zero.mpr hne
  rw [slope_def_field, div_eq_div_iff (hden z' hz') hne']
  have hq := fcs_quad_diff (msc_mul z) z'
  linear_combination (-1 : ℂ) * hq

private lemma fcs_msc_differentiableAt {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ msc z :=
  (fcs_msc_hasDerivAt hz).differentiableAt

/-- **Bulk lower bound**: `Im m_sc(z) ≥ κ'/12` for `|Re z| ≤ 2 - κ'/2`, `0 < Im z ≤ 3`. -/
private lemma fcs_msc_im_ge {κ' : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) {z : ℂ}
    (hre : |z.re| ≤ 2 - κ' / 2) (him0 : 0 < z.im) (him1 : z.im ≤ 3) :
    κ' / 12 ≤ (msc z).im := by
  set a := msc z with ha_def
  have hapos : 0 < a.im := msc_im_pos him0
  have hne : a ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hapos; exact lt_irrefl _ hapos
  have hnz : ‖z‖ ≤ 5 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him0] at this
    have h2 : |z.re| ≤ 2 := by linarith
    linarith
  set R := Complex.normSq a with hR_def
  have hRpos : 0 < R := Complex.normSq_pos.mpr hne
  have hR : (1 : ℝ) / 36 ≤ R := by
    have h1 := lemT_ge him0
    unfold lemT at h1
    rw [hR_def, Complex.normSq_eq_norm_sq]
    have h2 : ((1 + 5 : ℝ) ^ 2)⁻¹ ≤ ((1 + ‖z‖) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [norm_nonneg z])
    calc (1 : ℝ) / 36 = ((1 + 5 : ℝ) ^ 2)⁻¹ := by norm_num
      _ ≤ ((1 + ‖z‖) ^ 2)⁻¹ := h2
      _ ≤ ‖msc z‖ ^ 2 := h1
  have hre_rel : z.re * R = -(a.re * (R + 1)) := by
    have h := congrArg Complex.re (msc_add_eq_neg_inv him0)
    simp only [Complex.add_re, Complex.neg_re, Complex.inv_re] at h
    rw [← ha_def, ← hR_def] at h
    field_simp at h
    linear_combination h
  have hsq : z.re ^ 2 * R ^ 2 = a.re ^ 2 * (R + 1) ^ 2 := by
    have := congrArg (· ^ 2) hre_rel
    linear_combination this
  have hx : a.re ^ 2 * (4 * R) ≤ z.re ^ 2 * R ^ 2 := by
    rw [hsq]
    have : 4 * R ≤ (R + 1) ^ 2 := by nlinarith [sq_nonneg (R - 1)]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hx2 : a.re ^ 2 * 4 ≤ z.re ^ 2 * R := by
    have h := hx
    have : a.re ^ 2 * (4 * R) = (a.re ^ 2 * 4) * R := by ring
    rw [this, show z.re ^ 2 * R ^ 2 = (z.re ^ 2 * R) * R by ring] at h
    exact le_of_mul_le_mul_right h hRpos
  have hzre2 : z.re ^ 2 ≤ (2 - κ' / 2) ^ 2 := by
    have h0 : 0 ≤ |z.re| := abs_nonneg _
    have := mul_le_mul hre hre h0 (by linarith)
    rw [← sq, sq_abs] at this
    simpa [sq] using this
  have hRdef : R = a.re ^ 2 + a.im ^ 2 := by
    rw [hR_def, Complex.normSq_apply]; ring
  have hy2 : κ' ^ 2 / 144 ≤ a.im ^ 2 := by
    have h1 : a.re ^ 2 * 4 ≤ (2 - κ' / 2) ^ 2 * R :=
      hx2.trans (mul_le_mul_of_nonneg_right hzre2 hRpos.le)
    have h2 : R * (κ' / 4) ≤ a.im ^ 2 := by nlinarith
    have h3 : κ' / 144 ≤ R * (κ' / 4) := by nlinarith
    nlinarith
  by_contra hcon
  push Not at hcon
  have : a.im ^ 2 < (κ' / 12) ^ 2 := by
    have := mul_lt_mul'' hcon hcon hapos.le hapos.le
    nlinarith
  nlinarith

private lemma fcs_mk_zero (η : ℝ) : (⟨0, η⟩ : ℂ) = (η : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

private lemma fcs_norm_mk_zero (η : ℝ) : ‖(⟨0, η⟩ : ℂ)‖ = |η| := by
  rw [fcs_mk_zero, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- `m_sc` up to the real axis: `‖m_sc(E + iη) - m^{(E)}‖ Im m^{(E)} ≤ η`. -/
private lemma fcs_msc_sub_mE_le {E η : ℝ} (hE : |E| < 2) (hη : 0 < η) :
    ‖msc ⟨E, η⟩ - mE E‖ * (mE E).im ≤ η := by
  have h := fcs_msc_sub_mul_im_le (a := mE E) (z := (E : ℂ)) (z' := ⟨E, η⟩) (mE_mul hE.le) hη
  rw [norm_mE hE.le, mul_one] at h
  have h2 : (⟨E, η⟩ : ℂ) - E = ⟨0, η⟩ := by apply Complex.ext <;> simp
  rw [h2, fcs_norm_mk_zero, abs_of_pos hη] at h
  exact h

/-- **Continuity of `m_sc` up to the real axis in the bulk.** -/
theorem FreeConvStability.msc_tendsto_mE {E : ℝ} (hE : |E| < 2) :
    Tendsto (fun η : ℝ => msc ⟨E, η⟩) (𝓝[>] 0) (𝓝 (mE E)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hm := mE_im_pos hE
  have hlim : Tendsto (fun η : ℝ => η / (mE E).im) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun η : ℝ => η / (mE E).im) (𝓝 0) (𝓝 (0 / (mE E).im)) :=
      tendsto_id.div_const _
    rw [zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [le_div_iff₀ hm]
  exact fcs_msc_sub_mE_le hE hη

/-- Uniqueness of the upper root. -/
private lemma fcs_eq_msc {μ z : ℂ} (hμ : μ * (μ + z) = -1) (hμim : 0 < μ.im) (hz : 0 < z.im) :
    μ = msc z := by
  have h := msc_mul z
  have hfac : (μ - msc z) * (μ + msc z + z) = 0 := by linear_combination hμ - h
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have h2 := congrArg Complex.im h1
    simp only [Complex.add_im, Complex.zero_im] at h2
    have := msc_im_pos hz
    linarith

/-! ### 2. Elementary facts about `stieltjesVec` -/

private lemma fcs_sub_ne_zero {a : ℝ} {ω : ℂ} (hω : 0 < ω.im) : (a : ℂ) - ω ≠ 0 := by
  intro h
  have h2 := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] at h2
  linarith

private lemma fcs_stieltjesVec_im_pos {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) {ω : ℂ}
    (hω : 0 < ω.im) : 0 < (stieltjesVec v ω).im := by
  have hform : (stieltjesVec v ω).im =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ * ∑ i, ω.im / Complex.normSq ((v i : ℂ) - ω) := by
    unfold stieltjesVec
    rw [show (((Fintype.card n : ℕ) : ℂ))⁻¹ = ((((Fintype.card n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by
      rw [Complex.ofReal_inv, Complex.ofReal_natCast], Complex.im_ofReal_mul, Complex.im_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.inv_im, Complex.sub_im, Complex.ofReal_im]
    ring
  rw [hform]
  have hc : (0 : ℝ) < ((Fintype.card n : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
  refine mul_pos (by positivity) (Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty)
  exact div_pos hω (Complex.normSq_pos.mpr (fcs_sub_ne_zero hω))

private lemma fcs_stieltjesVec_differentiableAt {n : Type*} [Fintype n] (v : n → ℝ) {ω : ℂ}
    (hω : 0 < ω.im) : DifferentiableAt ℂ (stieltjesVec v) ω := by
  have e : stieltjesVec v = fun z => (Fintype.card n : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z)⁻¹ := rfl
  rw [e]
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.fun_sum fun i _ => ?_
  exact ((differentiableAt_const _).sub differentiableAt_id).inv (fcs_sub_ne_zero hω)

/-- Shift identity: the fixed-point equation for `m` is `m = m_v(z + t m)`. -/
private lemma fcs_stieltjesVec_shift {n : Type*} [Fintype n] (v : n → ℝ) (z t m : ℂ) :
    stieltjesVec v (z + t * m) =
      ((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - t * m)⁻¹ := by
  unfold stieltjesVec
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

/-! ### 3. The reference transform and the working rectangle -/

/-- `m_ref(w) = s^{-1/2} m_sc(s^{-1/2}(w + E₀))`: the Stieltjes transform of the semicircle of
variance `s`, shifted by `-E₀`. -/
private noncomputable def fcsRef (s E₀ : ℝ) (w : ℂ) : ℂ :=
  (Real.sqrt s : ℂ)⁻¹ * msc ((Real.sqrt s : ℂ)⁻¹ * (w + E₀))

/-- The working rectangle `{|Re w| ≤ κ'/32, (κ'/12) t/4 ≤ Im w ≤ ηmax + 1/8}`. -/
private def fcsRect (κ' t ηmax : ℝ) : Set ℂ :=
  {w : ℂ | |w.re| ≤ κ' / 32 ∧ κ' / 12 * t / 4 ≤ w.im ∧ w.im ≤ ηmax + 1 / 8}

private lemma fcsRect_convex (κ' t ηmax : ℝ) : Convex ℝ (fcsRect κ' t ηmax) := by
  intro x hx y hy a b ha hb hab
  simp only [fcsRect, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul] at hx hy ⊢
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · calc |a * x.re + b * y.re| ≤ |a * x.re| + |b * y.re| := abs_add_le _ _
      _ = a * |x.re| + b * |y.re| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (κ' / 32) + b * (κ' / 32) := by gcongr
      _ = κ' / 32 := by rw [← add_mul, hab, one_mul]
  · calc κ' / 12 * t / 4 = a * (κ' / 12 * t / 4) + b * (κ' / 12 * t / 4) := by
          rw [← add_mul, hab, one_mul]
      _ ≤ a * x.im + b * y.im :=
          add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hb)
  · calc a * x.im + b * y.im ≤ a * (ηmax + 1 / 8) + b * (ηmax + 1 / 8) :=
          add_le_add (mul_le_mul_of_nonneg_left hx3 ha) (mul_le_mul_of_nonneg_left hy3 hb)
      _ = ηmax + 1 / 8 := by rw [← add_mul, hab, one_mul]

/-- Facts about `σ = s^{-1/2}` for `s = 1 - t`, `0 < t ≤ 1/2`. -/
private lemma fcs_sigma {s t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2) (hs : s = 1 - t) :
    0 < Real.sqrt s ∧ 1 ≤ (Real.sqrt s)⁻¹ ∧ (Real.sqrt s)⁻¹ ≤ 1 + 2 * t ∧
      (Real.sqrt s)⁻¹ ^ 2 ≤ 2 := by
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hs1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr (by rw [hs]; linarith)
  have hs2 : 1 - t ≤ Real.sqrt s := by
    rw [show 1 - t = Real.sqrt ((1 - t) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt (by rw [hs]; nlinarith)
  refine ⟨hsq, ?_, ?_, ?_⟩
  · rw [le_inv_comm₀ one_pos hsq, inv_one]; exact hs1
  · rw [inv_le_comm₀ hsq (by positivity)]
    refine le_trans ?_ hs2
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith
  · rw [inv_pow, Real.sq_sqrt hs0.le, inv_le_comm₀ hs0 (by norm_num)]
    rw [hs]; linarith

/-- In `z = σ (w + E₀)` coordinates, the working region lies in the bulk region of
`fcs_msc_im_ge`. -/
private lemma fcs_zregion {κ' : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) {t E₀ σ : ℝ} (ht : 0 < t)
    (htc : t ≤ κ' / 240) (hE : |E₀| ≤ 2 - κ') (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 1 + 2 * t) {w : ℂ}
    (hre : |w.re| ≤ κ' / 16) (him0 : 0 < w.im) (him1 : w.im ≤ 5 / 4) :
    κ' / 12 ≤ (msc ((σ : ℂ) * (w + E₀))).im := by
  apply fcs_msc_im_ge hκ0 hκ1
  · rw [Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re, abs_mul,
      abs_of_pos (by linarith : (0 : ℝ) < σ)]
    have h1 : |w.re + E₀| ≤ 2 - 15 * κ' / 16 := (abs_add_le _ _).trans (by linarith)
    have h2 : 0 ≤ 2 - 15 * κ' / 16 := by linarith
    calc σ * |w.re + E₀| ≤ (1 + 2 * t) * (2 - 15 * κ' / 16) :=
          mul_le_mul hσ2 h1 (abs_nonneg _) (by linarith)
      _ ≤ 2 - κ' / 2 := by nlinarith
  · rw [Complex.im_ofReal_mul, Complex.add_im, Complex.ofReal_im, add_zero]
    exact mul_pos (by linarith) him0
  · rw [Complex.im_ofReal_mul, Complex.add_im, Complex.ofReal_im, add_zero]
    nlinarith

private lemma fcsRef_eq (s E₀ : ℝ) (w : ℂ) :
    fcsRef s E₀ w = (((Real.sqrt s)⁻¹ : ℝ) : ℂ) * msc ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) * (w + E₀)) := by
  rw [fcsRef, Complex.ofReal_inv]

private lemma fcsRef_differentiableAt (s E₀ : ℝ) (hs : 0 < Real.sqrt s) {w : ℂ} (hw : 0 < w.im) :
    DifferentiableAt ℂ (fcsRef s E₀) w := by
  have e : fcsRef s E₀ = fun w => (((Real.sqrt s)⁻¹ : ℝ) : ℂ) *
      msc ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) * (w + E₀)) := funext (fcsRef_eq s E₀)
  rw [e]
  refine DifferentiableAt.const_mul ?_ _
  have hz : 0 < ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) * (w + E₀)).im := by
    rw [Complex.im_ofReal_mul, Complex.add_im, Complex.ofReal_im, add_zero]
    exact mul_pos (inv_pos.mpr hs) hw
  exact (fcs_msc_differentiableAt hz).comp w
    (show DifferentiableAt ℂ (fun w : ℂ => (((Real.sqrt s)⁻¹ : ℝ) : ℂ) * (w + E₀)) w by fun_prop)

/-- **Lipschitz bound for the reference** on the bulk region. -/
private lemma fcsRef_lip {κ' : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) {s t E₀ : ℝ} (ht : 0 < t)
    (htc : t ≤ κ' / 240) (hs : s = 1 - t) (hE : |E₀| ≤ 2 - κ') {ω₁ ω₂ : ℂ}
    (h1re : |ω₁.re| ≤ κ' / 16) (h1im0 : 0 < ω₁.im) (h1im1 : ω₁.im ≤ 5 / 4) (h2im : 0 < ω₂.im) :
    ‖fcsRef s E₀ ω₂ - fcsRef s E₀ ω₁‖ ≤ 24 / κ' * ‖ω₂ - ω₁‖ := by
  obtain ⟨hsq, hσ1, hσ2, hσsq⟩ := fcs_sigma ht (by linarith) hs
  set σ := (Real.sqrt s)⁻¹ with hσ_def
  have hσpos : 0 < σ := by linarith
  set z₁ := (σ : ℂ) * (ω₁ + E₀)
  set z₂ := (σ : ℂ) * (ω₂ + E₀)
  have hz₁ : 0 < z₁.im := by
    simp only [z₁, Complex.im_ofReal_mul, Complex.add_im, Complex.ofReal_im, add_zero]
    exact mul_pos hσpos h1im0
  have hz₂ : 0 < z₂.im := by
    simp only [z₂, Complex.im_ofReal_mul, Complex.add_im, Complex.ofReal_im, add_zero]
    exact mul_pos hσpos h2im
  have hb := fcs_zregion hκ0 hκ1 ht htc hE hσ1 hσ2 h1re h1im0 h1im1
  have hlip := fcs_msc_lip hz₁ hz₂
  have hzd : ‖z₂ - z₁‖ = σ * ‖ω₂ - ω₁‖ := by
    rw [show z₂ - z₁ = (σ : ℂ) * (ω₂ - ω₁) by simp only [z₁, z₂]; ring, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hσpos.le]
  have hm : ‖msc z₂ - msc z₁‖ ≤ σ * ‖ω₂ - ω₁‖ / (κ' / 12) := by
    rw [le_div_iff₀ (by positivity), ← hzd]
    calc ‖msc z₂ - msc z₁‖ * (κ' / 12) ≤ ‖msc z₂ - msc z₁‖ * (msc z₁).im :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ ≤ _ := hlip
  rw [fcsRef_eq, fcsRef_eq, ← hσ_def, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hσpos.le]
  calc σ * ‖msc z₂ - msc z₁‖ ≤ σ * (σ * ‖ω₂ - ω₁‖ / (κ' / 12)) :=
        mul_le_mul_of_nonneg_left hm hσpos.le
    _ = σ ^ 2 * ‖ω₂ - ω₁‖ * (12 / κ') := by field_simp
    _ ≤ 2 * ‖ω₂ - ω₁‖ * (12 / κ') := by gcongr
    _ = 24 / κ' * ‖ω₂ - ω₁‖ := by ring

/-- **Unperturbed subordination**: `m_ref(iη + t m_sc(E₀ + iη)) = m_sc(E₀ + iη)`. -/
private lemma fcsRef_omega_sc {s t E₀ η : ℝ} (ht : 0 < t) (hs : s = 1 - t) (hs0 : 0 < s)
    (hη : 0 < η) :
    fcsRef s E₀ ((⟨0, η⟩ : ℂ) + (t : ℂ) * msc ⟨E₀, η⟩) = msc ⟨E₀, η⟩ := by
  set m := msc ⟨E₀, η⟩ with hm_def
  have hmim : 0 < m.im := msc_im_pos (z := ⟨E₀, η⟩) hη
  have hmm := msc_mul (⟨E₀, η⟩ : ℂ)
  rw [← hm_def] at hmm
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  set r : ℂ := (Real.sqrt s : ℂ) with hr_def
  have hr0 : r ≠ 0 := Complex.ofReal_ne_zero.mpr hsq.ne'
  have hr2 : r ^ 2 = (s : ℂ) := by
    rw [hr_def, ← Complex.ofReal_pow, Real.sq_sqrt hs0.le]
  have hζ : (⟨0, η⟩ : ℂ) + (t : ℂ) * m + E₀ = (⟨E₀, η⟩ : ℂ) + t * m := by
    apply Complex.ext <;> simp; ring
  have key : r * m = msc (r⁻¹ * ((⟨0, η⟩ : ℂ) + (t : ℂ) * m + E₀)) := by
    apply fcs_eq_msc
    · rw [hζ]
      have e1 : r * m * (r * m + r⁻¹ * ((⟨E₀, η⟩ : ℂ) + t * m)) =
          r ^ 2 * m ^ 2 + m * ((⟨E₀, η⟩ : ℂ) + t * m) := by
        field_simp
      have hs' : (s : ℂ) = 1 - t := by rw [hs]; push_cast; ring
      rw [e1, hr2]
      linear_combination hmm + m ^ 2 * hs'
    · rw [hr_def, Complex.im_ofReal_mul]
      exact mul_pos hsq hmim
    · rw [hζ, hr_def, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
      refine mul_pos (inv_pos.mpr hsq) ?_
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero]
      positivity
  unfold fcsRef
  rw [← hr_def, ← key]
  field_simp

/-! ### 4. The contraction on the working rectangle -/

/-- **Cauchy estimate and mean value**: `g = m_v - m_ref` is `ε/ρ`-Lipschitz on the rectangle,
`ρ = (κ'/12) t / 8`. -/
private lemma fcs_g_lip {κ' ηmax : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1)
    {n : Type*} [Fintype n] (v : n → ℝ) {s t E₀ ε : ℝ} (ht : 0 < t) (htc : t ≤ κ' / 240)
    (hs : s = 1 - t)
    (hyp : ∀ w : ℂ, |w.re| ≤ κ' / 16 → κ' / 240 * t / 4 ≤ w.im → w.im ≤ ηmax + 1 / 4 →
      ‖stieltjesVec v w - fcsRef s E₀ w‖ ≤ ε)
    {ω₁ ω₂ : ℂ} (h₁ : ω₁ ∈ fcsRect κ' t ηmax) (h₂ : ω₂ ∈ fcsRect κ' t ηmax) :
    ‖(stieltjesVec v ω₂ - fcsRef s E₀ ω₂) - (stieltjesVec v ω₁ - fcsRef s E₀ ω₁)‖ ≤
      ε / (κ' / 12 * t / 8) * ‖ω₂ - ω₁‖ := by
  obtain ⟨hsq, -, -, -⟩ := fcs_sigma ht (by linarith) hs
  set g : ℂ → ℂ := fun w => stieltjesVec v w - fcsRef s E₀ w with hg
  set ρ : ℝ := κ' / 12 * t / 8 with hρ
  have hρpos : 0 < ρ := by positivity
  have hκt : 0 < κ' * t := mul_pos hκ0 ht
  have hdiff : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ g w := fun w hw =>
    (fcs_stieltjesVec_differentiableAt v hw).sub (fcsRef_differentiableAt s E₀ hsq hw)
  have hball : ∀ x ∈ fcsRect κ' t ηmax, ∀ w ∈ Metric.closedBall x ρ,
      |w.re| ≤ κ' / 16 ∧ κ' / 240 * t / 4 ≤ w.im ∧ w.im ≤ ηmax + 1 / 4 := by
    intro x hx w hw
    obtain ⟨hx1, hx2, hx3⟩ := hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hre : |w.re - x.re| ≤ ρ := by
      have := Complex.abs_re_le_norm (w - x); rw [Complex.sub_re] at this; linarith
    have him : |w.im - x.im| ≤ ρ := by
      have := Complex.abs_im_le_norm (w - x); rw [Complex.sub_im] at this; linarith
    have hρ1 : ρ ≤ κ' / 32 := by rw [hρ]; nlinarith
    have hρ2 : ρ ≤ 1 / 8 := by rw [hρ]; nlinarith
    rw [abs_le] at hre him hx1
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · rw [hρ] at him; linarith
    · linarith
  have hderiv : ∀ x ∈ fcsRect κ' t ηmax, ‖deriv g x‖ ≤ ε / ρ := by
    intro x hx
    have hU : DifferentiableOn ℂ g {w : ℂ | 0 < w.im} := fun w hw =>
      (hdiff w hw).differentiableWithinAt
    have hsub : Metric.closedBall x ρ ⊆ {w : ℂ | 0 < w.im} := fun w hw => by
      have h1 := (hball x hx w hw).2.1
      change 0 < w.im
      have : 0 < κ' / 240 * t / 4 := by positivity
      linarith
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρpos (hU.diffContOnCl_ball hsub) ?_
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hball x hx w (Metric.sphere_subset_closedBall hw)
    exact hyp w h1 h2 h3
  have hrect_im : ∀ x ∈ fcsRect κ' t ηmax, 0 < x.im := fun x hx =>
    lt_of_lt_of_le (by positivity) hx.2.1
  exact (fcsRect_convex κ' t ηmax).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => hdiff x (hrect_im x hx)) hderiv h₁ h₂

/-- **The `1/2`-contraction**: `t m_v` is `1/2`-Lipschitz on the rectangle. -/
private lemma fcs_contract {κ' ηmax : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) (hη1 : ηmax ≤ 1)
    {n : Type*} [Fintype n] (v : n → ℝ) {s t E₀ ε : ℝ} (ht : 0 < t) (htc : t ≤ κ' / 240)
    (hs : s = 1 - t) (hE : |E₀| ≤ 2 - κ') (hεc : ε ≤ κ' / 240)
    (hyp : ∀ w : ℂ, |w.re| ≤ κ' / 16 → κ' / 240 * t / 4 ≤ w.im → w.im ≤ ηmax + 1 / 4 →
      ‖stieltjesVec v w - fcsRef s E₀ w‖ ≤ ε)
    {ω₁ ω₂ : ℂ} (h₁ : ω₁ ∈ fcsRect κ' t ηmax) (h₂ : ω₂ ∈ fcsRect κ' t ηmax) :
    t * ‖stieltjesVec v ω₂ - stieltjesVec v ω₁‖ ≤ 1 / 2 * ‖ω₂ - ω₁‖ := by
  have hg := fcs_g_lip hκ0 hκ1 v ht htc hs hyp h₁ h₂
  obtain ⟨h1re, h1im, h1im'⟩ := h₁
  have hκt : 0 < κ' / 12 * t / 4 := by positivity
  have href := fcsRef_lip hκ0 hκ1 ht htc hs hE (ω₁ := ω₁) (ω₂ := ω₂) (by linarith)
    (by linarith) (by linarith) (lt_of_lt_of_le hκt h₂.2.1)
  have htri : ‖stieltjesVec v ω₂ - stieltjesVec v ω₁‖ ≤
      ‖(stieltjesVec v ω₂ - fcsRef s E₀ ω₂) - (stieltjesVec v ω₁ - fcsRef s E₀ ω₁)‖ +
        ‖fcsRef s E₀ ω₂ - fcsRef s E₀ ω₁‖ := by
    calc ‖stieltjesVec v ω₂ - stieltjesVec v ω₁‖ =
        ‖((stieltjesVec v ω₂ - fcsRef s E₀ ω₂) - (stieltjesVec v ω₁ - fcsRef s E₀ ω₁)) +
          (fcsRef s E₀ ω₂ - fcsRef s E₀ ω₁)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have hcoef : t * (ε / (κ' / 12 * t / 8) + 24 / κ') ≤ 1 / 2 := by
    have e : t * (ε / (κ' / 12 * t / 8) + 24 / κ') = (96 * ε + 24 * t) / κ' := by
      field_simp
      ring
    rw [e, div_le_iff₀ hκ0]
    linarith
  calc t * ‖stieltjesVec v ω₂ - stieltjesVec v ω₁‖ ≤
        t * (ε / (κ' / 12 * t / 8) * ‖ω₂ - ω₁‖ + 24 / κ' * ‖ω₂ - ω₁‖) :=
        mul_le_mul_of_nonneg_left (htri.trans (add_le_add hg href)) ht.le
    _ = t * (ε / (κ' / 12 * t / 8) + 24 / κ') * ‖ω₂ - ω₁‖ := by ring
    _ ≤ 1 / 2 * ‖ω₂ - ω₁‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

/-- **Fixed point near `ω_sc(η)`** (Banach), identified with `freeConvST` by the uniqueness
of `freeConv_existsUnique`. -/
private lemma fcs_fixed {κ' ηmax : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) (hη1 : ηmax ≤ 1)
    {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) {s t E₀ ε : ℝ} (ht : 0 < t)
    (htc : t ≤ κ' / 240) (hs : s = 1 - t) (hE : |E₀| ≤ 2 - κ') (hε0 : 0 ≤ ε)
    (hεc : ε ≤ κ' / 240)
    (hyp : ∀ w : ℂ, |w.re| ≤ κ' / 16 → κ' / 240 * t / 4 ≤ w.im → w.im ≤ ηmax + 1 / 4 →
      ‖stieltjesVec v w - fcsRef s E₀ w‖ ≤ ε)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ηmax) :
    ((⟨0, η⟩ : ℂ) + (t : ℂ) * freeConvST v t ⟨0, η⟩) ∈ fcsRect κ' t ηmax ∧
      ‖((⟨0, η⟩ : ℂ) + (t : ℂ) * freeConvST v t ⟨0, η⟩) -
        ((⟨0, η⟩ : ℂ) + (t : ℂ) * msc ⟨E₀, η⟩)‖ ≤ 2 * t * ε := by
  have hs0 : 0 < s := by rw [hs]; linarith
  set ζ : ℂ := ⟨E₀, η⟩ with hζ
  set M := msc ζ with hM
  have hMn : ‖M‖ < 1 := norm_msc_lt_one (z := ζ) hη
  have hMb : κ' / 12 ≤ M.im :=
    fcs_msc_im_ge hκ0 hκ1 (z := ζ) (by change |E₀| ≤ _; linarith) hη (by change η ≤ 3; linarith)
  have hMre : |M.re| ≤ 1 := (Complex.abs_re_le_norm M).trans hMn.le
  have hMim1 : M.im ≤ 1 := (le_abs_self _).trans ((Complex.abs_im_le_norm M).trans hMn.le)
  set ωs : ℂ := (⟨0, η⟩ : ℂ) + (t : ℂ) * M with hωs
  have hωs_re : ωs.re = t * M.re := by simp [ωs]
  have hωs_im : ωs.im = η + t * M.im := by simp [ωs]
  have htMre : |ωs.re| ≤ t := by
    rw [hωs_re, abs_mul, abs_of_pos ht]; exact mul_le_of_le_one_right ht.le hMre
  have htMb : t * (κ' / 12) ≤ t * M.im := mul_le_mul_of_nonneg_left hMb ht.le
  have htM1 : t * M.im ≤ t := mul_le_of_le_one_right ht.le hMim1
  set r : ℝ := 2 * t * ε with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ t * κ' / 120 := by
    have := mul_le_mul_of_nonneg_left hεc (by positivity : (0 : ℝ) ≤ 2 * t)
    rw [hr]; linarith
  have hr2 : t * κ' ≤ t := mul_le_of_le_one_right ht.le hκ1
  set S := Metric.closedBall ωs r with hS
  have hSC : S ⊆ fcsRect κ' t ηmax := by
    intro w hw
    rw [hS, Metric.mem_closedBall, dist_eq_norm] at hw
    have hre : |w.re - ωs.re| ≤ r := by
      have := Complex.abs_re_le_norm (w - ωs); rw [Complex.sub_re] at this; linarith
    have him : |w.im - ωs.im| ≤ r := by
      have := Complex.abs_im_le_norm (w - ωs); rw [Complex.sub_im] at this; linarith
    rw [abs_le] at hre him htMre
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · rw [hωs_im] at him; linarith
    · rw [hωs_im] at him; linarith
  set F : ℂ → ℂ := fun w => (⟨0, η⟩ : ℂ) + (t : ℂ) * stieltjesVec v w with hF
  have hFdist : ∀ x ∈ fcsRect κ' t ηmax, ∀ y ∈ fcsRect κ' t ηmax,
      dist (F x) (F y) ≤ 1 / 2 * dist x y := by
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    have e : F x - F y = (t : ℂ) * (stieltjesVec v x - stieltjesVec v y) := by
      simp only [F]; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    exact fcs_contract hκ0 hκ1 hη1 v ht htc hs hE hεc hyp hy hx
  have hωsS : ωs ∈ S := Metric.mem_closedBall_self hr0
  have hFωs : ‖F ωs - ωs‖ ≤ t * ε := by
    have e : F ωs - ωs = (t : ℂ) * (stieltjesVec v ωs - fcsRef s E₀ ωs) := by
      rw [hωs, hM, hζ, fcsRef_omega_sc ht hs hs0 hη]; simp only [F]; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    refine mul_le_mul_of_nonneg_left (hyp ωs ?_ ?_ ?_) ht.le
    · linarith
    · rw [hωs_im]; nlinarith
    · rw [hωs_im]; linarith
  have hmaps : Set.MapsTo F S S := by
    intro w hw
    have hwC := hSC hw
    rw [hS, Metric.mem_closedBall] at hw ⊢
    calc dist (F w) ωs ≤ dist (F w) (F ωs) + dist (F ωs) ωs := dist_triangle _ _ _
      _ ≤ 1 / 2 * dist w ωs + t * ε :=
          add_le_add (hFdist w hwC ωs (hSC hωsS)) (by rw [dist_eq_norm]; exact hFωs)
      _ ≤ 1 / 2 * r + t * ε := by gcongr
      _ = r := by rw [hr]; ring
  have hcontr : ContractingWith (2⁻¹ : NNReal) (hmaps.restrict F S S) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq]
    simp only [Set.MapsTo.val_restrict_apply]
    have := hFdist x (hSC x.2) y (hSC y.2)
    simpa using this
  obtain ⟨y, hyS, hyfix, -, -⟩ :=
    hcontr.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps hωsS (edist_ne_top _ _)
  have hyC := hSC hyS
  have hyim : 0 < y.im := lt_of_lt_of_le (by positivity) hyC.2.1
  set m := stieltjesVec v y with hm
  have hmim : 0 < m.im := fcs_stieltjesVec_im_pos v hyim
  have hFy : (⟨0, η⟩ : ℂ) + (t : ℂ) * m = y := hyfix
  have heq : m = ((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - ⟨0, η⟩ - (t : ℂ) * m)⁻¹ := by
    rw [← fcs_stieltjesVec_shift, hFy]
  have hz : 0 < (⟨0, η⟩ : ℂ).im := hη
  have hfc : freeConvST v t ⟨0, η⟩ = m :=
    (freeConv_existsUnique v ht.le hz).unique (isFreeConv51_freeConvST v ht.le _ hz) ⟨hmim, heq⟩
  have hW : (⟨0, η⟩ : ℂ) + (t : ℂ) * freeConvST v t ⟨0, η⟩ = y := by rw [hfc, hFy]
  rw [hW]
  refine ⟨hyC, ?_⟩
  rw [hS, Metric.mem_closedBall, dist_eq_norm] at hyS
  exact hyS

/-! ### 5. The core estimate and the limit `η ↓ 0` -/

private lemma fcs_core {κ' ηmax : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) (hη0 : 0 < ηmax)
    (hη1 : ηmax ≤ 1) {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) {s t E₀ ε : ℝ}
    (ht : 0 < t) (htc : t ≤ κ' / 240) (hs : s = 1 - t) (hE : |E₀| ≤ 2 - κ') (hε0 : 0 ≤ ε)
    (hεc : ε ≤ κ' / 240)
    (hyp : ∀ w : ℂ, |w.re| ≤ κ' / 16 → κ' / 240 * t / 4 ≤ w.im → w.im ≤ ηmax + 1 / 4 →
      ‖stieltjesVec v w - (Real.sqrt s : ℂ)⁻¹ * msc ((Real.sqrt s : ℂ)⁻¹ * (w + E₀))‖ ≤ ε) :
    ∃ ρ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
      |ρ - rhoSc E₀| ≤ 2 * ε ∧
      ∀ η ∈ Set.Ioc (0 : ℝ) ηmax, ‖freeConvST v t ⟨0, η⟩ - msc ⟨E₀, η⟩‖ ≤ 2 * ε := by
  have hyp' : ∀ w : ℂ, |w.re| ≤ κ' / 16 → κ' / 240 * t / 4 ≤ w.im → w.im ≤ ηmax + 1 / 4 →
      ‖stieltjesVec v w - fcsRef s E₀ w‖ ≤ ε := hyp
  set W : ℝ → ℂ := fun η => (⟨0, η⟩ : ℂ) + (t : ℂ) * freeConvST v t ⟨0, η⟩ with hW
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hfcW : ∀ η : ℝ, (W η - ⟨0, η⟩) / t = freeConvST v t ⟨0, η⟩ := fun η => by
    simp only [W]; field_simp; ring
  have hfcsv : ∀ η : ℝ, 0 < η → freeConvST v t ⟨0, η⟩ = stieltjesVec v (W η) := fun η hη => by
    simp only [W]
    rw [fcs_stieltjesVec_shift]
    exact (isFreeConv51_freeConvST v ht.le _ hη).2
  -- the pointwise bound
  have hbound : ∀ η ∈ Set.Ioc (0 : ℝ) ηmax,
      ‖freeConvST v t ⟨0, η⟩ - msc ⟨E₀, η⟩‖ ≤ 2 * ε := by
    rintro η ⟨hη, hηle⟩
    have h := (fcs_fixed hκ0 hκ1 hη1 v ht htc hs hE hε0 hεc hyp' hη hηle).2
    have e : ((⟨0, η⟩ : ℂ) + (t : ℂ) * freeConvST v t ⟨0, η⟩) -
        ((⟨0, η⟩ : ℂ) + (t : ℂ) * msc ⟨E₀, η⟩) =
        (t : ℂ) * (freeConvST v t ⟨0, η⟩ - msc ⟨E₀, η⟩) := by ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le] at h
    have h2 : t * ‖freeConvST v t ⟨0, η⟩ - msc ⟨E₀, η⟩‖ ≤ t * (2 * ε) := by linarith
    exact le_of_mul_le_mul_left h2 ht
  -- the fixed points are `2`-Lipschitz in `η`
  have hWlip : ∀ η₁ ∈ Set.Ioc (0 : ℝ) ηmax, ∀ η₂ ∈ Set.Ioc (0 : ℝ) ηmax,
      ‖W η₁ - W η₂‖ ≤ 2 * |η₁ - η₂| := by
    rintro η₁ ⟨h1, h1'⟩ η₂ ⟨h2, h2'⟩
    have hC1 := (fcs_fixed hκ0 hκ1 hη1 v ht htc hs hE hε0 hεc hyp' h1 h1').1
    have hC2 := (fcs_fixed hκ0 hκ1 hη1 v ht htc hs hE hε0 hεc hyp' h2 h2').1
    have hc := fcs_contract hκ0 hκ1 hη1 v ht htc hs hE hεc hyp' hC2 hC1
    have e : W η₁ - W η₂ = (⟨0, η₁ - η₂⟩ : ℂ) +
        (t : ℂ) * (stieltjesVec v (W η₁) - stieltjesVec v (W η₂)) := by
      rw [← hfcsv η₁ h1, ← hfcsv η₂ h2]
      simp only [W]
      apply Complex.ext <;> simp <;> ring
    have hc' : t * ‖stieltjesVec v (W η₁) - stieltjesVec v (W η₂)‖ ≤
        1 / 2 * ‖W η₁ - W η₂‖ := hc
    have h3 : ‖W η₁ - W η₂‖ ≤ |η₁ - η₂| + 1 / 2 * ‖W η₁ - W η₂‖ := by
      calc ‖W η₁ - W η₂‖ = ‖(⟨0, η₁ - η₂⟩ : ℂ) +
            (t : ℂ) * (stieltjesVec v (W η₁) - stieltjesVec v (W η₂))‖ := by rw [e]
        _ ≤ ‖(⟨0, η₁ - η₂⟩ : ℂ)‖ +
            ‖(t : ℂ) * (stieltjesVec v (W η₁) - stieltjesVec v (W η₂))‖ := norm_add_le _ _
        _ ≤ |η₁ - η₂| + 1 / 2 * ‖W η₁ - W η₂‖ := by
          rw [fcs_norm_mk_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
          linarith
    linarith
  -- Cauchy along `η ↓ 0`
  have hcau : Cauchy (map W (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun δ hδ => ⟨W '' Set.Ioo 0 (min (δ / 4) ηmax), ?_, ?_⟩⟩
    · exact mem_map.mpr (mem_of_superset (Ioo_mem_nhdsGT (lt_min (by positivity) hη0))
        (Set.subset_preimage_image _ _))
    · rintro _ ⟨x, ⟨hx0, hx1⟩, rfl⟩ _ ⟨y, ⟨hy0, hy1⟩, rfl⟩
      have hm1 := min_le_left (δ / 4) ηmax
      have hm2 := min_le_right (δ / 4) ηmax
      have h := hWlip x ⟨hx0, by linarith⟩ y ⟨hy0, by linarith⟩
      have hxy : |x - y| < δ / 4 := by rw [abs_lt]; constructor <;> linarith
      rw [dist_eq_norm]
      linarith
  obtain ⟨W₀, hW₀⟩ := CompleteSpace.complete hcau
  have hWt : Tendsto W (𝓝[>] 0) (𝓝 W₀) := hW₀
  have hmk : Tendsto (fun η : ℝ => (⟨0, η⟩ : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun η : ℝ => (η : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.mul continuous_const
    have h0 := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul] at h0
    simp_rw [fcs_mk_zero]
    exact h0.mono_left nhdsWithin_le_nhds
  have hfc : Tendsto (fun η : ℝ => freeConvST v t ⟨0, η⟩) (𝓝[>] 0) (𝓝 ((W₀ - 0) / t)) :=
    ((hWt.sub hmk).div_const (t : ℂ)).congr hfcW
  set m₀ := (W₀ - 0) / (t : ℂ) with hm₀
  have hρlim : Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0)
      (𝓝 (m₀.im / Real.pi)) :=
    ((Complex.continuous_im.tendsto m₀).comp hfc).div_const Real.pi
  have hE2 : |E₀| < 2 := by linarith
  have hlim2 : Tendsto (fun η : ℝ => ‖freeConvST v t ⟨0, η⟩ - msc ⟨E₀, η⟩‖) (𝓝[>] 0)
      (𝓝 ‖m₀ - mE E₀‖) :=
    (hfc.sub (FreeConvStability.msc_tendsto_mE hE2)).norm
  have hm₀b : ‖m₀ - mE E₀‖ ≤ 2 * ε := by
    refine le_of_tendsto hlim2 ?_
    filter_upwards [Ioo_mem_nhdsGT hη0] with η hη
    exact hbound η ⟨hη.1, hη.2.le⟩
  refine ⟨m₀.im / Real.pi, hρlim, ?_, hbound⟩
  rw [rhoSc_eq_mE_im (by linarith : |E₀| ≤ 2), ← sub_div, abs_div, abs_of_pos Real.pi_pos]
  have h1 : |m₀.im - (mE E₀).im| ≤ ‖m₀ - mE E₀‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  calc |m₀.im - (mE E₀).im| / Real.pi ≤ 2 * ε / Real.pi := by
        gcongr; exact h1.trans hm₀b
    _ ≤ 2 * ε := div_le_self (by positivity) (by linarith [Real.pi_gt_three])

/-! ### 6. The main statement and its bulk-local form -/

/-- **Bulk-local form of the stability statement** (strictly stronger, same constants): the
closeness hypothesis is only needed on the bulk strip `|Re w| ≤ min κ 1 / 16`,
`c₀ t/4 ≤ Im w ≤ 1/2` (in `z = s^{-1/2}(w + E₀)` coordinates: `|Re z| ≤ 2 - min κ 1 / 2`,
`Im z ≤ 1`, the domain of the bulk local laws), and the conclusion holds for `η ∈ (0, 1/4]`
together with the same limit statement. -/
theorem FreeConvStability.freeConv_stable_local {κ : ℝ} (hκ : 0 < κ) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ ∀ {n}
    [Fintype n] [Nonempty n] (v : n → ℝ) (s t E₀ ε : ℝ), 0 < t → t ≤ c₀ → s = 1 - t →
    |E₀| ≤ 2 - κ → 0 ≤ ε → ε ≤ c₀ →
    (∀ w : ℂ, |w.re| ≤ min κ 1 / 16 → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
      ‖stieltjesVec v w - (Real.sqrt s : ℂ)⁻¹ * msc ((Real.sqrt s : ℂ)⁻¹ * (w + E₀))‖ ≤ ε) →
    ∃ ρ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
      |ρ - rhoSc E₀| ≤ C₀ * ε ∧
      ∀ η ∈ Set.Ioc (0:ℝ) (1 / 4), ‖freeConvST v t ⟨0, η⟩ - msc ⟨E₀, η⟩‖ ≤ C₀ * ε := by
  have hκ0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ1 : min κ 1 ≤ 1 := min_le_right _ _
  have hκκ : min κ 1 ≤ κ := min_le_left _ _
  refine ⟨min κ 1 / 240, 2, by positivity, two_pos, ?_⟩
  intro n _ _ v s t E₀ ε ht htc hs hE hε0 hεc hyp
  exact fcs_core hκ0 hκ1 (by norm_num) (by norm_num) v ht htc hs (by linarith) hε0 hεc
    (fun w h1 h2 h3 => hyp w h1 h2 (by linarith))

/-! ### 7. Satisfiability: Stieltjes' electrostatic (Hermite) configuration

The closeness hypothesis is satisfied by a deterministic `v`: the zeros `h_1, …, h_N` of the Hermite
polynomial `He_N`, scaled by `N^{-1/2}` (their empirical measure approximates the semicircle),
then by `s^{1/2}` and shifted by `-E₀`.  `He_N'' = x He_N' - N He_N` forces every complex root
to be simple and to satisfy `Σ_{j≠i} 1/(h_i - h_j) = h_i/2`; comparing imaginary parts at the root
of maximal (minimal) imaginary part shows that all roots are real.  For `u = h/√N` and
`a_i = (u_i - z)⁻¹` one has exactly `N² (m_u² + z m_u + 1) = Σ a_i²`, hence
`|m_u² + z m_u + 1| ≤ 1/(N Im² z)`, and the stability of the upper root gives
`|m_u(z) - m_sc(z)| ≤ 1/(N Im² z Im m_sc(z))`. -/

section Hermite

open Polynomial

variable {P : ℂ[X]} {N : ℕ}

end Hermite

end RBM.Gauss
