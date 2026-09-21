/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CondDom
import RBM1D.Gauss.Lemma41Glue

/-!
# Discharging the local-law side hypotheses of `hIBP` — T119

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4 (pp. 49-51).

`RBM.Gauss.trace_green_sub_mul_Eblk_stochDom_of_localLaw` (T112, `RBM1D/Gauss/CondDom.lean`)
carries four hypotheses that belong to no ticket: `hloc`, `hrepl`, the pair `hstabP`/`hstabM`,
and `hΩ` = (4.4).  **The first three are discharged here**; (4.4) stays, with a bridge from the
weak local law.

## `hloc` and `hrepl`

`hloc` is (4.3) with its indicator removed by (4.4): `RBM.Gauss.diag_bound_gauss` plus
`RBM.StochDom.of_indicator`.

`hrepl` is (4.9) restated for `RBM.Gauss.greenMinorMat` and with the control `L_max`.  The
identification `greenMinorMat = minorGreen` needs no event — `H_t` is Hermitian and
`Im z_t ≠ 0`, so the resolvent and every diagonal entry are invertible for *every* `ω`.  The
estimate is then (4.2) with the control `L_max`
(`RBM.Gauss.stochDom_indicator_normSq_green_offdiag_Lmax`), not T85's deterministic `Ψ²`.

## `hstabP` / `hstabM`: `E_i[L_max] ≺ L_max`

T112 flagged this as "the genuinely new probabilistic input".  It is not: **`L_max` is
essentially deterministic.**  Ward's identity gives `L_max ≤ η_t⁻² W⁻¹` on the whole space
(`RBM.Gauss.Lmax_Hflow_le_inv_W`), and the event (4.1) gives `W⁻¹ ≤ 4 L_max`
(`RBM.inv_W_le_Lmax`).  Since `t < 1` is a *fixed* real, `η_t` does not depend on `N`, so
`L_max ≺ W⁻¹ ≺ L_max`.  The row integral is then the T112 envelope tool with the row-free
control `W⁻¹`.

Caveat for the time-indexed versions of this estimate (`Gauss/EntryBoundTime.lean`,
`Gauss/Lemma41FlowGauss.lean`): if `t = t(N) → 1`, then `η_t⁻²` is no longer a constant and
`RBM.Gauss.stochDom_Lmax_inv_W` fails as a `≺`.  The proxy then has to be the minor's `L_max`
and the comparison becomes genuine local-law input; `RBM.Gauss.LmaxRowProxy` is the interface
for that case.

## Main results

* `RBM.Gauss.stochDom_normSq_green_diag_sub_Lmax` — `hloc`.
* `RBM.Gauss.stochDom_greenDiagCentered_sub_minor_Lmax` — `hrepl`.
* `RBM.Gauss.Lmax_Hflow_le_inv_W` — `L_max ≤ η_t⁻² W⁻¹`, from Ward's identity.
* `RBM.Gauss.LmaxRowProxy`, `RBM.Gauss.condStable_Lmax_of_rowProxy` — the interface for
  `E_i[L_max] ≺ L_max`, and its proof from a row-free two-sided proxy.
* `RBM.Gauss.lmaxRowProxy_inv_W`, `RBM.Gauss.condStable_Lmax` — the proxy `W⁻¹`, hence
  `hstabP`/`hstabM`.
* `RBM.Gauss.highProb_goodSet_of_stochDom` — (4.4) from the weak local law.
* `RBM.Gauss.condExpDiag_stochDom_of_highProb`,
  `RBM.Gauss.trace_green_sub_mul_Eblk_stochDom_of_highProb` — the compile-time check that these
  really fill the frozen slots of `RBM1D/Gauss/CondDom.lean`.
-/

namespace RBM.Gauss

open MeasureTheory Filter

/-! ### `hloc`: (4.3) without its indicator -/

/-- **`hloc`**: `|G_{ii} - m|² ≺ L_max`, i.e. Lemma 4.1 (4.3) with the indicator of the event
`Ω(t,c)` removed by (4.4). -/
theorem stochDom_normSq_green_diag_sub_Lmax (d : Dims) {E κ t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδc : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀))
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ)) :
    StochDom (P d)
      (fun N (i : d.Idx N) ω => ‖green (Hflow d N t ω) (zt E t) i i - mE E‖ ^ 2)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) :=
  StochDom.of_indicator hΩ (diag_bound_gauss hκ0 hκ1 hE ht0 ht1 hδ0 hc₀ hδc)

/-! ### `hrepl`: the minor replacement (4.9) with the control `L_max` -/

/-- **(4.2) with the control `L_max`.**  On the event `Ω(t,c)` of (4.1) the nine two-loops in the
right-hand side of (4.2) are each at most `L_max` (`RBM.Gauss.sum_sum_Lre_le`) and the stray
`W⁻¹` is at most `4 L_max` (`RBM.inv_W_le_Lmax`); so `1_Ω |G_{ij}|² ≺ L_max` for `i ≠ j`. -/
theorem stochDom_indicator_normSq_green_offdiag_Lmax (d : Dims) {E κ t : ℝ} (hκ0 : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδc : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) :
    StochDom (P d)
      (fun N (v : OffPair d.L d.W N) ω =>
        (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ N).indicator
          (fun ω => ‖green (Hflow d N t ω) (zt E t) v.1.1 v.1.2‖ ^ 2) ω)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hzt : (zt E t).im ≠ 0 := zt_im_ne_zero hκ0 hE ht1
  refine StochDom.of_det (entry_bound_gauss ht0 ht1.le hzt (norm_mE hE2) hδ0 hc₀ hδc)
    (fun N _ ω => Lmax_nonneg (Hflow_isHermitian d N t ω)) hδ0 hc₀ hδc
    (ε₀ := 1 / 2) (by norm_num) 13 1 ?_
  intro N ω Φ hΦ1 _ hδε hAB v
  have hL0 := Lmax_nonneg (z := zt E t) (Hflow_isHermitian d N t ω)
  by_cases hω : ω ∈ goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ N
  · have hGE : GoodEvent (green (Hflow d N t ω) (zt E t)) (mE E) (δ N) := hω
    have hB := hAB v
    have hsum := sum_sum_Lre_le d N E t ω v.1.1.1 v.1.2.1
    have hW := inv_W_le_Lmax (Hflow_isHermitian d N t ω) (norm_mE hE2) hGE hδε
    have hif : (if v.1.1.1 - v.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        ≤ 4 * Lmax (Hflow d N t ω) (zt E t) := by
      split
      · exact hW
      · linarith
    have hΦ0 : (0 : ℝ) ≤ Φ := by linarith
    have hkey : Φ * ((∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
          Lre (Hflow d N t ω) (zt E t) (v.1.2.1 + b) (v.1.1.1 + a))
        + if v.1.1.1 - v.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        ≤ 13 * Φ ^ 1 * Lmax (Hflow d N t ω) (zt E t) := by
      rw [pow_one]
      nlinarith
    exact hB.trans hkey
  · rw [Set.indicator_of_notMem hω]
    have hΦ0 : (0 : ℝ) ≤ Φ := by linarith
    positivity

/-- **`hrepl`**: `|G_{ll} - G^{(κ)}_{ll}| ≺ L_max` for `l ≠ κ`, in the exact shape the slot of
`RBM.Gauss.condExpDiag_stochDom_of_localLaw` asks for.

Two things have to be bridged relative to T85's `RBM.Gauss.minorReplace_diag_stochDom`.

* The statement is about `RBM.Gauss.greenMinorMat` (a *total* matrix inverse), not about the
  explicit formula (4.9).  The two agree by `RBM.Gauss.greenMinorMat_eq_minorGreen`, whose two
  side conditions are free along the flow: `H_t` is Hermitian and `Im z_t ≠ 0`, so both
  `RBM.Gauss.isUnit_det_Hflow_sub` and `RBM.Gauss.green_Hflow_diag_ne_zero` hold for *every*
  `ω` — no event is needed for the identification.
* The control is the random `L_max`, not a deterministic `Ψ²`.  Rather than compare the two
  controls, the estimate is redone from (4.2) with the control `L_max`
  (`RBM.Gauss.stochDom_indicator_normSq_green_offdiag_Lmax`): by (4.9) the error is
  `|G_{lκ}| |G_{κl}| / |G_{κκ}| ≤ 2 |G_{lκ}| |G_{κl}| ≤ |G_{lκ}|² + |G_{κl}|²`. -/
theorem stochDom_greenDiagCentered_sub_minor_Lmax (d : Dims) {E κ t : ℝ} (hκ0 : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδc : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀))
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ)) :
    StochDom (P d)
      (fun N (v : OffPair d.L d.W N) ω =>
        ‖greenDiagCentered d N t (zt E t) (mE E) v.1.2 ω
          - greenMinorDiagCentered d N t (zt E t) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hzt : (zt E t).im ≠ 0 := zt_im_ne_zero hκ0 hE ht1
  refine StochDom.of_indicator hΩ ?_
  refine StochDom.of_det
    (stochDom_indicator_normSq_green_offdiag_Lmax d hκ0 hE ht0 ht1 hδ0 hc₀ hδc)
    (fun N _ ω => Lmax_nonneg (Hflow_isHermitian d N t ω)) hδ0 hc₀ hδc
    (ε₀ := 1 / 2) (by norm_num) 26 1 ?_
  intro N ω Φ hΦ1 _ hδε hAB v
  have hL0 := Lmax_nonneg (z := zt E t) (Hflow_isHermitian d N t ω)
  have hΦ0 : (0 : ℝ) ≤ Φ := by linarith
  by_cases hω : ω ∈ goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ N
  · rw [Set.indicator_of_mem hω]
    have hGE : GoodEvent (green (Hflow d N t ω) (zt E t)) (mE E) (δ N) := hω
    have hid : greenDiagCentered d N t (zt E t) (mE E) v.1.2 ω
        - greenMinorDiagCentered d N t (zt E t) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω
        = -(greenMinor (green (Hflow d N t ω) (zt E t)) v.1.1 v.1.2 v.1.2
            - green (Hflow d N t ω) (zt E t) v.1.2 v.1.2) := by
      simp only [greenDiagCentered, greenMinorDiagCentered]
      rw [greenMinorMat_eq_minorGreen d N t (zt E t) v.1.1 ω
        (isUnit_det_Hflow_sub d N t ω hzt) (green_Hflow_diag_ne_zero d N t ω hzt v.1.1),
        minorGreen_eq_greenMinor]
      ring
    rw [hid, norm_neg]
    have h1 := hGE.norm_greenMinor_sub_le (norm_mE hE2) hδε v.1.1 v.1.2 v.1.2
    have h2 := hAB v
    have h3 := hAB (⟨(v.1.2, v.1.1), Ne.symm v.2⟩ : OffPair d.L d.W N)
    rw [Set.indicator_of_mem hω] at h2 h3
    simp only at h2 h3
    have hsq : 2 * (‖green (Hflow d N t ω) (zt E t) v.1.2 v.1.1‖
          * ‖green (Hflow d N t ω) (zt E t) v.1.1 v.1.2‖)
        ≤ ‖green (Hflow d N t ω) (zt E t) v.1.2 v.1.1‖ ^ 2
          + ‖green (Hflow d N t ω) (zt E t) v.1.1 v.1.2‖ ^ 2 := by
      nlinarith [sq_nonneg (‖green (Hflow d N t ω) (zt E t) v.1.2 v.1.1‖
        - ‖green (Hflow d N t ω) (zt E t) v.1.1 v.1.2‖)]
    rw [pow_one]
    nlinarith
  · rw [Set.indicator_of_notMem hω]
    positivity

/-! ### `hΩ`: (4.4) from the weak local law -/

/-- **(4.4) from the weak local law.**  The event `Ω(t,c)` of (4.1) asks for a *deterministic*
bound `‖G - m‖_max ≤ δ_N`; Definition 2.1 (i) gives `‖G - m‖_max ≤ N^τ Ψ_N` off an event of
probability `N^{-D}`.  So (4.4) is exactly the weak local law with a polynomial margin,
`N^τ Ψ_N ≤ δ_N` for one `τ > 0`. -/
theorem highProb_goodSet_of_stochDom (d : Dims) {E t : ℝ} {δ Ψ : ℕ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hll : StochDom (P d)
      (fun N (ij : d.Idx N × d.Idx N) ω =>
        ‖green (Hflow d N t ω) (zt E t) ij.1 ij.2 - (if ij.1 = ij.2 then mE E else 0)‖)
      (fun N _ _ => Ψ N))
    (hΨ : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ τ * Ψ N ≤ δ N) :
    HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ) := by
  refine (hll.highProb hτ).mono ?_
  filter_upwards [hΨ] with N hN ω hω
  exact fun x y => (hω (x, y)).trans hN

/-! ### `hstabP` / `hstabM`: `E_i[L_max] ≺ L_max` -/

section Stab

variable {E t : ℝ} {δ : ℕ → ℝ} {d : Dims} {N : ℕ}

/-- The **deterministic envelope of `L_max`** along the flow: every two-loop is an average of
`W²` squared Green function entries, each at most `η_t⁻²`. -/
theorem Lmax_Hflow_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ) (ω : Ω d) :
    Lmax (Hflow d N u ω) (zt E t) ≤ ((etaT E t)⁻¹) ^ 2 := by
  refine Finset.sup'_le _ _ fun p _ => ?_
  rw [Lre_eq (Hflow_isHermitian d N u ω)]
  have hWpos : (0 : ℝ) < ((d.W N : ℕ) : ℝ) := by exact_mod_cast d.W_pos N
  have hinner : ∀ _β : Fin (d.W N),
      (∑ α : Fin (d.W N), ‖green (Hflow d N u ω) (zt E t) (p.2, _β) (p.1, α)‖ ^ 2)
        ≤ ((d.W N : ℕ) : ℝ) * ((etaT E t)⁻¹) ^ 2 := by
    intro β
    calc (∑ α : Fin (d.W N), ‖green (Hflow d N u ω) (zt E t) (p.2, β) (p.1, α)‖ ^ 2)
        ≤ ∑ _α : Fin (d.W N), ((etaT E t)⁻¹) ^ 2 :=
          Finset.sum_le_sum fun α _ => by
            have := norm_green_apply_le_etaT hE ht u (p.2, β) (p.1, α) ω
            have h0 := norm_nonneg (green (Hflow d N u ω) (zt E t) (p.2, β) (p.1, α))
            nlinarith
      _ = ((d.W N : ℕ) : ℝ) * ((etaT E t)⁻¹) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum : (∑ β : Fin (d.W N), ∑ α : Fin (d.W N),
        ‖green (Hflow d N u ω) (zt E t) (p.2, β) (p.1, α)‖ ^ 2)
      ≤ ((d.W N : ℕ) : ℝ) * (((d.W N : ℕ) : ℝ) * ((etaT E t)⁻¹) ^ 2) := by
    calc (∑ β : Fin (d.W N), ∑ α : Fin (d.W N),
          ‖green (Hflow d N u ω) (zt E t) (p.2, β) (p.1, α)‖ ^ 2)
        ≤ ∑ _β : Fin (d.W N), ((d.W N : ℕ) : ℝ) * ((etaT E t)⁻¹) ^ 2 :=
          Finset.sum_le_sum fun β _ => hinner β
      _ = ((d.W N : ℕ) : ℝ) * (((d.W N : ℕ) : ℝ) * ((etaT E t)⁻¹) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfac : (((d.W N : ℕ) : ℝ)⁻¹) ^ 2
      * (((d.W N : ℕ) : ℝ) * (((d.W N : ℕ) : ℝ) * ((etaT E t)⁻¹) ^ 2))
      = ((etaT E t)⁻¹) ^ 2 := by
    field_simp
  calc (((d.W N : ℕ) : ℝ)⁻¹) ^ 2 * ∑ β : Fin (d.W N), ∑ α : Fin (d.W N),
        ‖green (Hflow d N u ω) (zt E t) (p.2, β) (p.1, α)‖ ^ 2
      ≤ (((d.W N : ℕ) : ℝ)⁻¹) ^ 2
          * (((d.W N : ℕ) : ℝ) * (((d.W N : ℕ) : ℝ) * ((etaT E t)⁻¹) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((etaT E t)⁻¹) ^ 2 := hfac

/-- `L_max` is integrable along any row: it is measurable and bounded by `η_t⁻²`. -/
theorem integrable_Lmax_rowSplit (hE : |E| < 2) (ht : t < 1) (k : d.Idx N) (ω : Ω d) :
    Integrable (fun ω' => Lmax (Hflow d N t (rowSplit d N k ω ω')) (zt E t)) (P d) := by
  refine Integrable.mono' (integrable_const (((etaT E t)⁻¹) ^ 2))
    (((measurable_Lmax d N t (zt E t)).comp
      (measurable_rowSplit_right d N k ω)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω' => ?_
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Lmax_nonneg (Hflow_isHermitian d N t (rowSplit d N k ω ω')))]
  exact Lmax_Hflow_le_env hE ht t _

/-- **`L_max ≤ η_t⁻² W⁻¹` on the whole space.**

Ward's identity `∑_p |G_{pq}|² = Im G_{qq} / η` (`RBM.im_green_apply_eq_mul_sum_normSq`) turns
the `W²` summands of a two-loop `L_{(+,-),(a,b)} = W⁻² ∑_{β,α} |G_{(b,β),(a,α)}|²` into `W`
column sums, each at most `η_t⁻²`.  The prefactor `W⁻²` then leaves one factor `W⁻¹`.

This is what makes `L_max` an *essentially deterministic* control: combined with the lower
bound `W⁻¹ ≤ 4 L_max` of `RBM.inv_W_le_Lmax`, valid on the event (4.1), it pins `L_max` between
`W⁻¹/4` and `η_t⁻² W⁻¹` with constants that do not depend on `N`. -/
theorem Lmax_Hflow_le_inv_W (hE : |E| < 2) (ht : t < 1) (u : ℝ) (ω : Ω d) :
    Lmax (Hflow d N u ω) (zt E t) ≤ ((etaT E t)⁻¹) ^ 2 * ((d.W N : ℕ) : ℝ)⁻¹ := by
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  have hzim : (zt E t).im = etaT E t := (etaT_eq_zt_im E t).symm
  have hzne : (zt E t).im ≠ 0 := by rw [hzim]; exact hη.ne'
  have hH := Hflow_isHermitian d N u ω
  have hU : IsUnit (Hflow d N u ω - (zt E t) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_Hflow_sub d N u ω hzne)
  have hU' : IsUnit (Hflow d N u ω
      - ((starRingEnd ℂ) (zt E t)) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_Hflow_sub d N u ω
      (by rw [Complex.conj_im]; exact neg_ne_zero.2 hzne))
  have hWpos : (0 : ℝ) < ((d.W N : ℕ) : ℝ) := by exact_mod_cast d.W_pos N
  have hcol : ∀ q : d.Idx N,
      (∑ p : d.Idx N, ‖green (Hflow d N u ω) (zt E t) p q‖ ^ 2) ≤ ((etaT E t)⁻¹) ^ 2 := by
    intro q
    have hw := im_green_apply_eq_mul_sum_normSq hH hU hU' q
    rw [hzim] at hw
    have hsum : (∑ p : d.Idx N, ‖green (Hflow d N u ω) (zt E t) p q‖ ^ 2)
        = ∑ p : d.Idx N, Complex.normSq (green (Hflow d N u ω) (zt E t) p q) :=
      Finset.sum_congr rfl fun p _ => (Complex.normSq_eq_norm_sq _).symm
    rw [hsum]
    have him : (green (Hflow d N u ω) (zt E t) q q).im ≤ (etaT E t)⁻¹ :=
      le_trans (Complex.im_le_norm _) (norm_green_apply_le_etaT hE ht u q q ω)
    have hs : etaT E t * ∑ p : d.Idx N, Complex.normSq (green (Hflow d N u ω) (zt E t) p q)
        ≤ (etaT E t)⁻¹ := by rw [← hw]; exact him
    have hkey := mul_le_mul_of_nonneg_left hs (le_of_lt (inv_pos.2 hη))
    have he : (etaT E t)⁻¹ * (etaT E t
        * ∑ p : d.Idx N, Complex.normSq (green (Hflow d N u ω) (zt E t) p q))
        = ∑ p : d.Idx N, Complex.normSq (green (Hflow d N u ω) (zt E t) p q) := by
      field_simp
    rw [he] at hkey
    calc (∑ p : d.Idx N, Complex.normSq (green (Hflow d N u ω) (zt E t) p q))
        ≤ (etaT E t)⁻¹ * (etaT E t)⁻¹ := hkey
      _ = ((etaT E t)⁻¹) ^ 2 := by ring
  refine Finset.sup'_le _ _ fun p _ => ?_
  rw [Lre_eq hH, Finset.sum_comm]
  have hinner : ∀ _α : Fin (d.W N),
      (∑ β : Fin (d.W N), ‖green (Hflow d N u ω) (zt E t) (p.2, β) (p.1, _α)‖ ^ 2)
        ≤ ((etaT E t)⁻¹) ^ 2 := by
    intro α
    refine le_trans ?_ (hcol (p.1, α))
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (f := fun b : ZMod (d.L N) => ∑ β : Fin (d.W N),
      ‖green (Hflow d N u ω) (zt E t) (b, β) (p.1, α)‖ ^ 2)
      (fun b _ => Finset.sum_nonneg fun β _ => sq_nonneg _) (Finset.mem_univ p.2)
  have htot : (∑ α : Fin (d.W N), ∑ β : Fin (d.W N),
        ‖green (Hflow d N u ω) (zt E t) (p.2, β) (p.1, α)‖ ^ 2)
      ≤ ((d.W N : ℕ) : ℝ) * ((etaT E t)⁻¹) ^ 2 := by
    calc (∑ α : Fin (d.W N), ∑ β : Fin (d.W N),
          ‖green (Hflow d N u ω) (zt E t) (p.2, β) (p.1, α)‖ ^ 2)
        ≤ ∑ _α : Fin (d.W N), ((etaT E t)⁻¹) ^ 2 := Finset.sum_le_sum fun α _ => hinner α
      _ = ((d.W N : ℕ) : ℝ) * ((etaT E t)⁻¹) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (((d.W N : ℕ) : ℝ))⁻¹ ^ 2 * ∑ α : Fin (d.W N), ∑ β : Fin (d.W N),
        ‖green (Hflow d N u ω) (zt E t) (p.2, β) (p.1, α)‖ ^ 2
      ≤ (((d.W N : ℕ) : ℝ))⁻¹ ^ 2 * (((d.W N : ℕ) : ℝ) * ((etaT E t)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left htot (by positivity)
    _ = ((etaT E t)⁻¹) ^ 2 * ((d.W N : ℕ) : ℝ)⁻¹ := by field_simp

/-- **The comparison that `E_i[L_max] ≺ L_max` needs.**

`RBM.Gauss.CondStable d U k L_max L_max` — the hypothesis `hstabP` / `hstabM` of
`RBM.Gauss.condExpDiag_stochDom_of_localLaw` — is not automatic: `L_max` is a function of the
whole matrix, so it does read row `i`, and the exceptional event of Definition 2.1 (i) survives
the row integral.  What makes it true is a **row-`i`-free two-sided proxy**: a family `Λ_i`
that does not read row `i` and satisfies `L_max ≺ Λ_i` and `Λ_i ≺ L_max`.

The obvious candidate is `L_max` built from the minor `H^{(i)}`, and finding it was expected to
need a local law.  It does not: the proxy can be taken **deterministic**, `Λ_i := W⁻¹`.  Ward's
identity pins `L_max ≤ η_t⁻² W⁻¹` on the whole space (`RBM.Gauss.Lmax_Hflow_le_inv_W`), and the
event (4.1) pins `W⁻¹ ≤ 4 L_max` (`RBM.inv_W_le_Lmax`); since `t < 1` is a *fixed* real, `η_t⁻²`
is an `N`-independent constant and both comparisons are `≺`.  See
`RBM.Gauss.lmaxRowProxy_inv_W`. -/
def LmaxRowProxy (d : Dims) (E t : ℝ) (U : ℕ → Type*) (k : ∀ N, U N → d.Idx N) : Prop :=
  ∃ Λ : ∀ N, U N → Ω d → ℝ,
    (∀ (N : ℕ) (u : U N), Measurable (Λ N u)) ∧
    (∀ (N : ℕ) (u : U N) (ω : Ω d), 0 ≤ Λ N u ω) ∧
    (∀ (N : ℕ) (u : U N), FinDepOffRow d N (k N u) (Λ N u)) ∧
    StochDom (P d) (fun N (_ : U N) ω => Lmax (Hflow d N t ω) (zt E t)) Λ ∧
    StochDom (P d) Λ (fun N (_ : U N) ω => Lmax (Hflow d N t ω) (zt E t))

/-- **`E_i[L_max] ≺ L_max` from a row-free two-sided proxy.**

Given `RBM.Gauss.LmaxRowProxy`, the passage of `L_max` through `E_i` is
`RBM.Gauss.stochDom_condRow_of_envelope` applied with control `ζ := Λ_i` and target
`χ := L_max`:

* `‖L_max‖ ≺ Λ_i` is the first half of the proxy;
* `Λ_i` *is* its own `E_i` (`RBM.Gauss.CondStable.of_finDepOffRow`), so `E_i[Λ_i] ≺ L_max` is the
  second half;
* the deterministic envelope is `L_max ≤ η_t⁻²` (`RBM.Gauss.Lmax_Hflow_le_env`);
* `N⁻¹ ≺ L_max` is `RBM.Gauss.stochDom_rpow_neg_one_Lmax` (T112). -/
theorem condStable_Lmax_of_rowProxy {U : ℕ → Type*} [∀ N, Fintype (U N)]
    (d : Dims) (hE : |E| < 2) (ht : t < 1) {Ccard : ℝ} (hCcard : 0 ≤ Ccard)
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ))
    {k : ∀ N, U N → d.Idx N} (hproxy : LmaxRowProxy d E t U k) :
    CondStable d U k (fun N (_ : U N) ω => Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : U N) ω => Lmax (Hflow d N t ω) (zt E t)) := by
  obtain ⟨Λ, hΛmeas, hΛ0, hΛfd, hup, hlow⟩ := hproxy
  have hL0 : ∀ (N : ℕ) (u : U N) (ω : Ω d), 0 ≤ Lmax (Hflow d N t ω) (zt E t) :=
    fun N _ ω => Lmax_nonneg (Hflow_isHermitian d N t ω)
  refine ⟨fun N u ω => integrable_Lmax_rowSplit hE ht (k N u) ω, ?_⟩
  -- the complex lift of `L_max`, so that the general tool applies
  set X : ∀ N, U N → Ω d → ℂ :=
    fun N _ ω => ((Lmax (Hflow d N t ω) (zt E t) : ℝ) : ℂ) with hX
  have hXnorm : ∀ (N : ℕ) (u : U N) (ω : Ω d),
      ‖X N u ω‖ = Lmax (Hflow d N t ω) (zt E t) := by
    intro N u ω
    rw [hX, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hL0 N u ω)]
  have hcondRow : ∀ (N : ℕ) (u : U N) (ω : Ω d),
      ‖condRow d N (k N u) (X N u) ω‖
        = condRowReal d N (k N u) (fun η => Lmax (Hflow d N t η) (zt E t)) ω := by
    intro N u ω
    have he : condRow d N (k N u) (X N u) ω
        = ((condRowReal d N (k N u) (fun η => Lmax (Hflow d N t η) (zt E t)) ω : ℝ) : ℂ) := by
      rw [condRow_apply, condRowReal_apply]
      exact integral_complex_ofReal
    rw [he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (condRowReal_nonneg (fun η => hL0 N u η) ω)]
  have hstab : CondStable d U k Λ (fun N (_ : U N) ω => Lmax (Hflow d N t ω) (zt E t)) := by
    refine ⟨fun N u ω => ?_, ?_⟩
    · have h : (fun ω' => Λ N u (rowSplit d N (k N u) ω ω')) = fun _ => Λ N u ω := by
        funext ω'; exact (hΛfd N u).rowSplit_eq ω ω'
      rw [h]; exact integrable_const _
    · have h : (fun N (u : U N) ω => condRowReal d N (k N u) (Λ N u) ω) = Λ := by
        funext N u; exact condRowReal_of_finDepOffRow (hΛfd N u)
      rw [h]; exact hlow
  have htool : StochDom (P d)
      (fun N (u : U N) ω => ‖condRow d N (k N u) (X N u) ω‖)
      (fun N (_ : U N) ω => Lmax (Hflow d N t ω) (zt E t)) := by
    refine stochDom_condRow_of_envelope hCcard hcard
      (fun N u => Complex.measurable_ofReal.comp (measurable_Lmax d N t (zt E t)))
      hΛmeas hΛ0 hL0 (Kenv := 1) (by norm_num) (B := 1) (by norm_num)
      (Env := fun _ => ((etaT E t)⁻¹) ^ 2) ?_ ?_
      (stochDom_rpow_neg_one_Lmax d _ hE.le hδ hΩ) hstab ?_
    · intro N u ω
      rw [hXnorm N u ω]
      exact Lmax_Hflow_le_env hE ht t ω
    · exact eventually_le_rpow (((etaT E t)⁻¹) ^ 2) one_pos
    · exact StochDom.of_le_left (fun N u ω => le_of_eq (hXnorm N u ω)) hup
  exact StochDom.of_le_left
    (fun N u ω => le_of_eq (hcondRow N u ω).symm) htool

/-- **`W⁻¹ ≺ L_max`.**  On the event (4.1) the diagonal of `G` has modulus at least `1/2`, hence
`W⁻¹ ≤ 4 L_max` (`RBM.inv_W_le_Lmax`). -/
theorem stochDom_inv_W_Lmax (d : Dims) (U : ℕ → Type*) (hE : |E| ≤ 2)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ)) :
    StochDom (P d) (fun N (_ : U N) (_ : Ω d) => ((d.W N : ℕ) : ℝ)⁻¹)
      (fun N (_ : U N) ω => Lmax (Hflow d N t ω) (zt E t)) := by
  intro τ hτ D hD
  filter_upwards [hΩ D hD, hδ, eventually_le_rpow 4 hτ] with N hΩN hδN h4N
  refine (measure_mono ?_).trans hΩN
  rintro ω ⟨u, hu⟩
  simp only at hu
  refine Set.mem_compl fun hω => ?_
  have hGE : GoodEvent (green (Hflow d N t ω) (zt E t)) (mE E) (δ N) := hω
  have h1 := inv_W_le_Lmax (Hflow_isHermitian d N t ω) (norm_mE hE) hGE hδN
  have hL0 := Lmax_nonneg (z := zt E t) (Hflow_isHermitian d N t ω)
  have h3 : 4 * Lmax (Hflow d N t ω) (zt E t) ≤ (N : ℝ) ^ τ * Lmax (Hflow d N t ω) (zt E t) :=
    mul_le_mul_of_nonneg_right h4N hL0
  linarith

/-- **`L_max ≺ W⁻¹`.**  Deterministic: `RBM.Gauss.Lmax_Hflow_le_inv_W`, with the `N`-independent
constant `η_t⁻²`. -/
theorem stochDom_Lmax_inv_W (d : Dims) (U : ℕ → Type*) (hE : |E| < 2) (ht : t < 1) :
    StochDom (P d) (fun N (_ : U N) ω => Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : U N) (_ : Ω d) => ((d.W N : ℕ) : ℝ)⁻¹) :=
  StochDom.of_le_left (fun N u ω => Lmax_Hflow_le_inv_W hE ht t ω)
    (StochDom.const_mul_left (c := ((etaT E t)⁻¹) ^ 2) (by positivity)
      (fun N u ω => inv_nonneg.2 (Nat.cast_nonneg _))
      (StochDom.refl fun N u ω => inv_nonneg.2 (Nat.cast_nonneg _)))

/-- **The proxy exists, and it is deterministic**: `Λ_i := W⁻¹` for every `i`.

A constant reads no coordinate at all, so it is trivially row-`i`-free; the two comparisons are
`RBM.Gauss.stochDom_Lmax_inv_W` and `RBM.Gauss.stochDom_inv_W_Lmax`.  Together with
`RBM.Gauss.condStable_Lmax_of_rowProxy` this discharges `hstabP` and `hstabM` outright. -/
theorem lmaxRowProxy_inv_W {U : ℕ → Type*} (d : Dims) (k : ∀ N, U N → d.Idx N)
    (hE : |E| < 2) (ht : t < 1) (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ)) :
    LmaxRowProxy d E t U k :=
  ⟨fun N _ _ => ((d.W N : ℕ) : ℝ)⁻¹, fun N u => measurable_const,
    fun N u ω => inv_nonneg.2 (Nat.cast_nonneg _),
    fun N u => ⟨∅, by simp, fun _ _ _ => rfl⟩,
    stochDom_Lmax_inv_W d U hE ht, stochDom_inv_W_Lmax d U hE.le hδ hΩ⟩

/-- **`hstabP` / `hstabM`, unconditionally**: `E_i[L_max] ≺ L_max`. -/
theorem condStable_Lmax {U : ℕ → Type*} [∀ N, Fintype (U N)] (d : Dims) (hE : |E| < 2)
    (ht : t < 1) {Ccard : ℝ} (hCcard : 0 ≤ Ccard)
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ))
    (k : ∀ N, U N → d.Idx N) :
    CondStable d U k (fun N (_ : U N) ω => Lmax (Hflow d N t ω) (zt E t))
      (fun N (_ : U N) ω => Lmax (Hflow d N t ω) (zt E t)) :=
  condStable_Lmax_of_rowProxy d hE ht hCcard hcard hδ hΩ (lmaxRowProxy_inv_W d k hE ht hδ hΩ)

end Stab

/-! ### The assembly: `hIBP`'s local-law side, with only (4.4) left -/

section Assembly

variable {E t : ℝ} {δ : ℕ → ℝ}

/-- `δ_N ≤ N^{-c₀}` gives `δ_N ≤ 1/2` eventually. -/
theorem eventually_delta_le_half {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδc : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2 := by
  filter_upwards [hδc, eventually_le_rpow 2 hc₀, eventually_ge_atTop 1] with N hN h2N hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have h1 : (N : ℝ) ^ (-c₀) ≤ 1 / 2 := by
    rw [Real.rpow_neg hNpos.le, inv_le_comm₀ (Real.rpow_pos_of_pos hNpos _) (by norm_num)]
    simpa using h2N
  linarith

/-- The Definition 2.1 (i) cardinality bound for `RBM.OffPair`. -/
theorem card_OffPair_le (d : Dims) :
    ∀ᶠ N : ℕ in atTop, (Fintype.card (OffPair d.L d.W N) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
  filter_upwards [card_Idx_prod_le d] with N hN
  refine le_trans ?_ hN
  exact_mod_cast Fintype.card_subtype_le (fun p : d.Idx N × d.Idx N => p.1 ≠ p.2)

/-- **`hIBP`'s local-law side, assembled.**  This is
`RBM.Gauss.condExpDiag_stochDom_of_localLaw` with all four of `hstabP`, `hstabM`, `hloc` and
`hrepl` discharged.  Only (4.4) is left. -/
theorem condExpDiag_stochDom_of_highProb (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδc : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀))
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ)) :
    StochDom (P d)
      (fun N (i : d.Idx N) ω => ‖condExpDiag d N t (zt E t) (mE E) i ω
        - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N t ω) (zt E t) k k - mE E)‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) := by
  have hE2 : |E| < 2 := by linarith
  have hhalf := eventually_delta_le_half hc₀ hδc
  exact condExpDiag_stochDom_of_localLaw (gaussIBP d) hE2 ht0 ht1 hδ0 hc₀ hδc hΩ
    (condStable_Lmax d hE2 ht1 (by norm_num) (card_Idx_prod_le d) hhalf hΩ _)
    (condStable_Lmax d hE2 ht1 (by norm_num) (card_OffPair_le d) hhalf hΩ _)
    (stochDom_normSq_green_diag_sub_Lmax d hκ0 hκ1 hEκ ht0 ht1 hδ0 hc₀ hδc hΩ)
    (stochDom_greenDiagCentered_sub_minor_Lmax d hκ0 hEκ ht0 ht1 hδ0 hc₀ hδc hΩ)

/-- **(4.5) with `hIBP`, `hstabP`, `hstabM`, `hloc` and `hrepl` all discharged.**

`RBM.Gauss.trace_green_sub_mul_Eblk_stochDom_of_localLaw` carries eight hypotheses beyond the
model and the parameters: `hG`, `hΩ`, `hstabP`, `hstabM`, `hloc`, `hrepl`, `hFArow`, `hFAblk`.
This version carries three — `hΩ` (4.4) and the two fluctuation averaging inputs.  `hG` is
`RBM.Gauss.gaussIBP` (T104); `hstabP`/`hstabM` are `RBM.Gauss.condStable_Lmax`; `hloc` is
`RBM.Gauss.stochDom_normSq_green_diag_sub_Lmax`; `hrepl` is
`RBM.Gauss.stochDom_greenDiagCentered_sub_minor_Lmax`.

Its only role is to check at compile time that what is proved above really fills the frozen
slots; no signature in `RBM1D/Gauss/CondDom.lean`, `RBM1D/Gauss/IBP.lean`,
`RBM1D/Gauss/FlucAvg.lean`, `RBM1D/Gauss/MinorReplace.lean` or `RBM1D/Green/EntryBound.lean` is
touched. -/
theorem trace_green_sub_mul_Eblk_stochDom_of_highProb (d : Dims) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδc : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀))
    (hΩ : HighProb (P d)
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N t ω) (zt E t) (mE E) δ))
    (hFArow : StochDom (P d)
      (fun N (i : d.Idx N) ω =>
        ‖flucAvg d N t (zt E t) (mE E) (fun j => Sblk (d.L N) (d.W N) i j) ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)))
    (hFAblk : StochDom (P d)
      (fun N (a : ZMod (d.L N)) ω =>
        ‖flucAvg d N t (zt E t) (mE E) (blkCoef (d.L N) (d.W N) a) ω‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t))) :
    StochDom (P d)
      (fun N (a : ZMod (d.L N)) ω => ‖Matrix.trace ((green (Hflow d N t ω) (zt E t)
        - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) a)‖)
      (fun N _ ω => Lmax (Hflow d N t ω) (zt E t)) :=
  trace_green_sub_mul_Eblk_stochDom d hκ0 hκ1 hEκ ht0 ht1
    (condExpDiag_stochDom_of_highProb d hκ0 hκ1 hEκ ht0 ht1 hδ0 hc₀ hδc hΩ)
    hFArow hFAblk

end Assembly

end RBM.Gauss
