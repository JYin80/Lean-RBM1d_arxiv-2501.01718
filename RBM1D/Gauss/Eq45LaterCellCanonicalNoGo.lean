/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Eq45FlowGrid

/-!
# T1333: the later-cell canonical deterministic majorant obstruction

For the actual growing-dimension witness and p. 24 grid exponent 1/480, the cell
1 - W^(-1/480) to 1 - W^(-2/480) is eventually a genuine positive-length later cell below
1 - N^(-1/2). At its right endpoint, the honest deterministic majorant from (2.75) forces
4 W Ψ² to grow at least as a positive power of N. This contradicts the literal hΨW
consumer in Eq45FlowGrid.eq45FlowInputs_of_localLaw_gain_budget'.

This is only an obstruction to that canonical deterministic-majorant route. It assumes neither
the local law nor Eq45FlowInputs, and it says nothing against (4.5).
-/

namespace RBM.Gauss.Eq45LaterCellCanonicalNoGo

open Filter

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The p. 24 grid exponent selected by Band.eventually_flow_grid' at τ = 1/2. -/
noncomputable def alpha : ℝ := 1 / 480

/-- The first and second p. 24 grid endpoints after the initial point 0. -/
noncomputable def sCell (N : ℕ) : ℝ := 1 - (d.W N : ℝ) ^ (-alpha)

noncomputable def tCell (N : ℕ) : ℝ := 1 - (d.W N : ℝ) ^ (-2 * alpha)

/-- The endpoint scale uses the repository definitions W ℓ_t η_t. -/
noncomputable def endpointScale (N : ℕ) : ℝ :=
  (band d).scale 0 N (tCell N)

theorem alpha_eq_iteration_choice :
    alpha = ((min (1 / 2 : ℝ) 1) / 2) / 120 := by
  norm_num [alpha]

/-- The chosen endpoints are exactly gridS W α 1 and gridS W α 2. -/
theorem endpoints_are_gridS (N : ℕ) :
    sCell N = gridS (d.W N : ℝ) alpha 1 ∧
      tCell N = gridS (d.W N : ℝ) alpha 2 := by
  constructor <;> simp [sCell, tCell, alpha, gridS]

private theorem tendsto_W :
    Tendsto (fun N : ℕ => (d.W N : ℝ)) atTop atTop := by
  change Tendsto (fun N : ℕ => (Dims.growW N : ℝ)) atTop atTop
  exact tendsto_natCast_atTop_atTop.comp Dims.tendsto_growW

private theorem eventually_W_le_N :
    ∀ᶠ N : ℕ in atTop, (d.W N : ℝ) ≤ (N : ℝ) := by
  filter_upwards [d.dim] with N hdim
  have hprod : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hdim.1
  have hL : 1 ≤ (d.L N : ℝ) := by
    exact_mod_cast (show 1 ≤ d.L N from le_trans (by omega) (d.three_le_L N))
  have hW : 0 ≤ (d.W N : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hW (sub_nonneg.mpr hL)]

private theorem pow_sqrt_cell (N : ℕ) :
    Real.sqrt (1 - tCell N) = (d.W N : ℝ) ^ (-alpha) := by
  have hW : 0 ≤ (d.W N : ℝ) := Nat.cast_nonneg _
  have hsub : 1 - tCell N = (d.W N : ℝ) ^ (-2 * alpha) := by
    simp [tCell]
  rw [hsub, Real.sqrt_eq_rpow, ← Real.rpow_mul hW]
  congr 1
  ring

private theorem inv_pow_neg_alpha (N : ℕ) :
    1 / ((d.W N : ℝ) ^ (-alpha)) = (d.W N : ℝ) ^ alpha := by
  have hW : 0 ≤ (d.W N : ℝ) := Nat.cast_nonneg _
  rw [Real.rpow_neg hW]
  simp

private theorem eta_endpoint (N : ℕ) :
    etaT 0 (tCell N) = (d.W N : ℝ) ^ (-2 * alpha) := by
  have hm : (mE 0).im = 1 := by
    rw [mE_im]
    rw [show (4 - (0 : ℝ) ^ 2 : ℝ) = 4 by norm_num]
    have hsq : (Real.sqrt (4 : ℝ)) ^ 2 = 4 := by
      rw [Real.sq_sqrt (show 0 ≤ (4 : ℝ) by norm_num)]
    have hnonneg : 0 ≤ Real.sqrt (4 : ℝ) := Real.sqrt_nonneg _
    have hsqrt : Real.sqrt (4 : ℝ) = 2 := by nlinarith
    rw [hsqrt]
    norm_num
  simp [etaT, tCell, hm]

private theorem tCell_lt_one (N : ℕ) : tCell N < 1 := by
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hq : 0 < (d.W N : ℝ) ^ (-2 * alpha) := Real.rpow_pos_of_pos hW _
  change 1 - (d.W N : ℝ) ^ (-2 * alpha) < 1
  linarith

private theorem ell_endpoint_le (N : ℕ) :
    (band d).ell N (tCell N) ≤ (d.W N : ℝ) ^ alpha := by
  have ht := tCell_lt_one N
  change ellHat (d.L N) (tCell N : ℂ) ≤ (d.W N : ℝ) ^ alpha
  rw [ellHat_ofReal _ ht, pow_sqrt_cell, inv_pow_neg_alpha]
  exact min_le_left _ _

private theorem ell_endpoint_pos (N : ℕ) :
    0 < (band d).ell N (tCell N) := by
  have hL : 0 < (d.L N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (d.three_le_L N))
  have hgap : 0 < 1 - tCell N := sub_pos.mpr (tCell_lt_one N)
  change 0 < ellHat (d.L N) (tCell N : ℂ)
  rw [ellHat_ofReal _ (tCell_lt_one N)]
  apply lt_min_iff.mpr
  constructor
  · exact one_div_pos.mpr (Real.sqrt_pos_of_pos hgap)
  · exact hL

/-- The paper's exact W ℓ_t η_t scale at the right endpoint has
ℓ_t η_t ≤ 2 W^(-α) (the source definitions give the stronger constant 1). -/
theorem ell_eta_endpoint_le (N : ℕ) :
    (band d).ell N (tCell N) * etaT 0 (tCell N) ≤
      2 * (d.W N : ℝ) ^ (-alpha) := by
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have heta : 0 < etaT 0 (tCell N) := by
    rw [eta_endpoint]
    exact Real.rpow_pos_of_pos hW _
  rw [eta_endpoint]
  calc
    (band d).ell N (tCell N) * (d.W N : ℝ) ^ (-2 * alpha)
        ≤ (d.W N : ℝ) ^ alpha * (d.W N : ℝ) ^ (-2 * alpha) :=
          mul_le_mul_of_nonneg_right (ell_endpoint_le N)
            (Real.rpow_nonneg hW.le _)
    _ = (d.W N : ℝ) ^ (-alpha) := by
      rw [← Real.rpow_add hW]
      congr 1
      ring
    _ ≤ 2 * (d.W N : ℝ) ^ (-alpha) := by
      nlinarith [Real.rpow_pos_of_pos hW (-alpha)]

private theorem endpoint_scale_eq (N : ℕ) :
    endpointScale N = (d.W N : ℝ) *
      ((band d).ell N (tCell N) * etaT 0 (tCell N)) := by
  unfold endpointScale
  change (d.W N : ℝ) * (band d).ell N (tCell N) * etaT 0 (tCell N) =
    (d.W N : ℝ) * ((band d).ell N (tCell N) * etaT 0 (tCell N))
  ring

private theorem endpoint_scale_pos (N : ℕ) : 0 < endpointScale N := by
  rw [endpoint_scale_eq]
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have heta : 0 < etaT 0 (tCell N) := by
    rw [eta_endpoint]
    exact Real.rpow_pos_of_pos hW _
  have hell : 0 < (band d).ell N (tCell N) := ell_endpoint_pos N
  exact mul_pos hW (mul_pos hell heta)

private theorem endpoint_scale_canonical_lower
    (N : ℕ) (ΨN : ℝ)
    (hmaj : (endpointScale N)⁻¹ ^ ((1 : ℝ) / 2) ≤ ΨN) :
    2 * (d.W N : ℝ) ^ alpha ≤ 4 * (d.W N : ℝ) * (ΨN * ΨN) := by
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hScale : 0 < endpointScale N := endpoint_scale_pos N
  have hRoot : 0 < (endpointScale N)⁻¹ ^ ((1 : ℝ) / 2) := by positivity
  have hΨ : 0 ≤ ΨN := hRoot.le.trans hmaj
  have hRootSq :
      ((endpointScale N)⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 = (endpointScale N)⁻¹ := by
    calc
      ((endpointScale N)⁻¹ ^ ((1 : ℝ) / 2)) ^ 2
          = (endpointScale N)⁻¹ ^ (((1 : ℝ) / 2) * 2) :=
              (Real.rpow_mul_natCast (inv_nonneg.mpr hScale.le) _ _).symm
      _ = (endpointScale N)⁻¹ := by norm_num
  have hSq : (endpointScale N)⁻¹ ≤ ΨN * ΨN := by
    have hprod := mul_nonneg (sub_nonneg.mpr hmaj)
      (add_nonneg hRoot.le hΨ)
    nlinarith [hprod, hRootSq]
  have hprodPos :
      0 < (band d).ell N (tCell N) * etaT 0 (tCell N) := by
    exact mul_pos (ell_endpoint_pos N)
      (by
        rw [eta_endpoint]
        exact Real.rpow_pos_of_pos hW _)
  have hprodBound := ell_eta_endpoint_le N
  have hInvBound := inv_anti₀ hprodPos hprodBound
  have hCancel :
      (d.W N : ℝ) * (endpointScale N)⁻¹ =
        ((band d).ell N (tCell N) * etaT 0 (tCell N))⁻¹ := by
    rw [endpoint_scale_eq]
    field_simp [ne_of_gt hW, ne_of_gt hprodPos]
  have hRecip :
      (2 * (d.W N : ℝ) ^ (-alpha))⁻¹ =
        (1 / 2) * (d.W N : ℝ) ^ alpha := by
    rw [Real.rpow_neg (by positivity : 0 ≤ (d.W N : ℝ))]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hW alpha)]
  have hWSq :
      (1 / 2) * (d.W N : ℝ) ^ alpha ≤ (d.W N : ℝ) * (ΨN * ΨN) := by
    calc
      (1 / 2) * (d.W N : ℝ) ^ alpha
          = (2 * (d.W N : ℝ) ^ (-alpha))⁻¹ := hRecip.symm
      _ ≤ ((band d).ell N (tCell N) * etaT 0 (tCell N))⁻¹ := hInvBound
      _ = (d.W N : ℝ) * (endpointScale N)⁻¹ := hCancel.symm
      _ ≤ (d.W N : ℝ) * (ΨN * ΨN) :=
        mul_le_mul_of_nonneg_left hSq hW.le
  nlinarith

/-- A time-independent canonical majorant forces a genuine polynomial loss on this cell.
The second conjunct is the quantitative witness 4 W Ψ² ≥ 2 N^(5/3840). -/
theorem eventually_canonical_majorant_forces_power
    {Ψ : ℕ → ℝ}
    (hmaj : ∀ᶠ N : ℕ in atTop,
      (endpointScale N)⁻¹ ^ ((1 : ℝ) / 2) ≤ Ψ N) :
    ∀ᶠ N : ℕ in atTop,
      2 * (d.W N : ℝ) ^ alpha ≤ 4 * (d.W N : ℝ) * (Ψ N * Ψ N) ∧
        2 * (N : ℝ) ^ ((5 : ℝ) / 3840) ≤ 2 * (d.W N : ℝ) ^ alpha := by
  have hbw := Dims.bandwidth_grow
  have hN1 := eventually_ge_atTop 1
  filter_upwards [hmaj, hbw, hN1] with N hmajN hbwN hN
  have hWLower : (N : ℝ) ^ ((5 : ℝ) / 8) ≤ (d.W N : ℝ) := by
    have heq : (5 : ℝ) / 8 = (1 / 2 : ℝ) + 1 / 8 := by norm_num
    rw [heq]
    exact hbwN
  have hβ : ((5 : ℝ) / 8) * alpha = (5 : ℝ) / 3840 := by
    norm_num [alpha]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hWpow :
      (N : ℝ) ^ ((5 : ℝ) / 3840) ≤ (d.W N : ℝ) ^ alpha := by
    calc
      (N : ℝ) ^ ((5 : ℝ) / 3840)
          = (N : ℝ) ^ (((5 : ℝ) / 8) * alpha) := by rw [hβ]
      _ = ((N : ℝ) ^ ((5 : ℝ) / 8)) ^ alpha := by
        rw [Real.rpow_mul hNpos.le]
      _ ≤ (d.W N : ℝ) ^ alpha :=
        Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hWLower (by norm_num [alpha])
  constructor
  · exact endpoint_scale_canonical_lower N (Ψ N) hmajN
  · exact mul_le_mul_of_nonneg_left hWpow (by norm_num)

/-- The canonical deterministic majorant route cannot meet the literal hΨW budget consumed
by Eq45FlowGrid.eq45FlowInputs_of_localLaw_gain_budget'. -/
theorem no_deterministic_canonical_majorant_with_hPsiW :
    ¬ ∃ Ψ : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop,
        (endpointScale N)⁻¹ ^ ((1 : ℝ) / 2) ≤ Ψ N) ∧
      (∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        4 * (d.W N : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ ε) := by
  rintro ⟨Ψ, hmaj, hbudget⟩
  let ε : ℝ := 5 / 7680
  have hε : 0 < ε := by norm_num [ε]
  have hupper := hbudget ε hε
  have hlower := eventually_canonical_majorant_forces_power hmaj
  have hN1 := eventually_ge_atTop 1
  have hFalse : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hupper, hlower, hN1] with N hu hl hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNpow : (N : ℝ) ^ ε ≤ (N : ℝ) ^ ((5 : ℝ) / 3840) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (by omega : 1 ≤ N)
      · norm_num [ε]
    have hβpos : 0 < (N : ℝ) ^ ((5 : ℝ) / 3840) :=
      Real.rpow_pos_of_pos hNpos _
    have hβleW : (N : ℝ) ^ ((5 : ℝ) / 3840) ≤ (d.W N : ℝ) ^ alpha := by
      nlinarith [hl.2]
    have hstrict : (N : ℝ) ^ ε < 2 * (d.W N : ℝ) ^ alpha := by
      calc
        (N : ℝ) ^ ε ≤ (N : ℝ) ^ ((5 : ℝ) / 3840) := hNpow
        _ ≤ (d.W N : ℝ) ^ alpha := hβleW
        _ < 2 * (d.W N : ℝ) ^ alpha := by nlinarith [hβpos, hβleW]
    have hle : 2 * (d.W N : ℝ) ^ alpha ≤ (N : ℝ) ^ ε := le_trans hl.1 hu
    exact lt_irrefl _ (lt_of_le_of_lt hle hstrict)
  rcases (eventually_atTop.1 hFalse) with ⟨n, hn⟩
  exact hn n (le_rfl)

/-- A nondegenerate witness for the theorem's domain: at E = 0, this later cell is strictly
inside [1/2, 1 - N^(-1/2)] and has positive length eventually. -/
theorem eventually_later_cell_domain :
    ∀ᶠ N : ℕ in atTop,
      1 / 2 < sCell N ∧ sCell N < tCell N ∧
        tCell N ≤ 1 - (N : ℝ) ^ (-(1 / 2 : ℝ)) ∧ tCell N < 1 := by
  have hsmall := (tendsto_rpow_neg_atTop (by norm_num [alpha] : 0 < alpha)).comp tendsto_W
  have hWlarge := tendsto_atTop.1 tendsto_W 2
  have hWleN := eventually_W_le_N
  have hN1 := eventually_ge_atTop 1
  filter_upwards [hsmall.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hWlarge, hWleN, hN1] with N hsmallN hWlargeN hWleNN hN1N
  have hsmallWN : (d.W N : ℝ) ^ (-alpha) < 1 / 2 := by
    simpa only [Function.comp_apply] using hsmallN
  have hW : 1 < (d.W N : ℝ) := by linarith
  have hW0 : 0 < (d.W N : ℝ) := by linarith
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hpowPos : 0 < (d.W N : ℝ) ^ (-alpha) := Real.rpow_pos_of_pos hW0 _
  have hpowLt : (d.W N : ℝ) ^ (-2 * alpha) < (d.W N : ℝ) ^ (-alpha) := by
    apply Real.rpow_lt_rpow_of_exponent_lt hW
    norm_num [alpha]
  have hNexp :
      (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (N : ℝ) ^ (-(2 * alpha)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1N) (by norm_num [alpha])
  have hInvMono :
      (N : ℝ) ^ (-(2 * alpha)) ≤ (d.W N : ℝ) ^ (-(2 * alpha)) := by
    have hpow : (d.W N : ℝ) ^ (2 * alpha) ≤ (N : ℝ) ^ (2 * alpha) :=
      Real.rpow_le_rpow (by positivity) hWleNN (by norm_num [alpha])
    have hinv := inv_anti₀
      (Real.rpow_pos_of_pos hW0 (2 * alpha)) hpow
    rw [Real.rpow_neg (Nat.cast_nonneg N) (2 * alpha),
      Real.rpow_neg (Nat.cast_nonneg (d.W N)) (2 * alpha)]
    exact hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 1 / 2 < 1 - (d.W N : ℝ) ^ (-alpha)
    linarith [hsmallWN]
  · change 1 - (d.W N : ℝ) ^ (-alpha) <
      1 - (d.W N : ℝ) ^ (-2 * alpha)
    linarith [hpowLt]
  · change 1 - (d.W N : ℝ) ^ (-2 * alpha) ≤
      1 - (N : ℝ) ^ (-(1 / 2 : ℝ))
    have htime := hNexp.trans hInvMono
    have hexp : -(2 * alpha) = -2 * alpha := by ring
    rw [hexp] at htime
    calc
      1 - (d.W N : ℝ) ^ (-2 * alpha)
          = 1 + (-(d.W N : ℝ) ^ (-2 * alpha)) := by ring
      _ ≤ 1 + (-(N : ℝ) ^ (-(1 / 2 : ℝ))) := by
        exact add_le_add_right (neg_le_neg htime) 1
      _ = 1 - (N : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
  · change 1 - (d.W N : ℝ) ^ (-2 * alpha) < 1
    linarith [Real.rpow_pos_of_pos hW0 (-2 * alpha)]

end RBM.Gauss.Eq45LaterCellCanonicalNoGo

#print axioms RBM.Gauss.Eq45LaterCellCanonicalNoGo.endpoints_are_gridS
#print axioms RBM.Gauss.Eq45LaterCellCanonicalNoGo.ell_eta_endpoint_le
#print axioms RBM.Gauss.Eq45LaterCellCanonicalNoGo.eventually_canonical_majorant_forces_power
#print axioms RBM.Gauss.Eq45LaterCellCanonicalNoGo.no_deterministic_canonical_majorant_with_hPsiW
#print axioms RBM.Gauss.Eq45LaterCellCanonicalNoGo.eventually_later_cell_domain
