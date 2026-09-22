/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GoodSetFlow
import RBM1D.Gauss.MinorDiffCond
import RBM1D.Flow.Step345Producer

/-!
# The fifth-slot grid scales — T279

The old interface makes the good-event threshold and the time mesh share one parameter.
The negative result isolates its contradiction.  The primed input producers use separate
parameters and feed slot 5 without changing the frozen interface.
-/

namespace RBM.Gauss

open MeasureTheory Filter

/-- The first cell of the truncated p. 24 grid with terminal time `1/2` has positive length
for all sufficiently large `N`. -/
theorem first_cell_window_nondegenerate (d : Dims) {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
        < gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1 :=
  eventually_gridT_zero_lt_gridT_one (band d) hτ'
    (Eventually.of_forall fun _ => by norm_num)

/-- On the first cell of the paper's truncated grid, the event used by the three moduli is
eventually inhabited whenever the uniform local law supplies the good event.  The cell has
positive length; hence none of the modulus statements is justified by a collapsed window or
an empty good event. -/
theorem first_cell_flowNetEvent_nonempty (d : Dims) {E τ' : ℝ} (hτ' : 0 < τ')
    {tEnd δ : ℕ → ℝ} (htEnd : ∀ᶠ N : ℕ in atTop, 0 < tEnd N)
    (hΩ : HighProb (P d)
      (goodSetFlow d E
        (fun N => gridT ((band d).W N : ℝ) τ' (tEnd N) 0)
        (fun N => gridT ((band d).W N : ℝ) τ' (tEnd N) 1) δ)) :
    ∀ᶠ N : ℕ in atTop,
      gridT ((band d).W N : ℝ) τ' (tEnd N) 0
        < gridT ((band d).W N : ℝ) τ' (tEnd N) 1 ∧
      (flowNetEvent d E
        (fun N => gridT ((band d).W N : ℝ) τ' (tEnd N) 0)
        (fun N => gridT ((band d).W N : ℝ) τ' (tEnd N) 1) δ N).Nonempty := by
  have hwin := eventually_gridT_zero_lt_gridT_one (band d) hτ' htEnd
  have hev := (highProb_flowNetEvent d hΩ).nonempty measure_univ
  exact hwin.and hev

#print axioms first_cell_window_nondegenerate
#print axioms first_cell_flowNetEvent_nonempty

/-- The net accuracy in T124 and the fluctuation scale in (4.12) cannot share the same
parameter `δ`: the first forces `δ ≤ 1/(16N²)` while the second forces
`δ ≥ Ψ ≳ W⁻¹ᐟ² ≥ N⁻¹ᐟ²`. -/
theorem no_joint_grid_scales (d : Dims) {E : ℝ} {s t δ Ψ : ℕ → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hΨpos : ∀ N, 0 < Ψ N)
    (hmargin : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ τ * Ψ N ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΨW : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * Ψ N ^ 2) : False := by
  obtain ⟨N, ⟨⟨hN2, hWN⟩, hmN⟩, hfN⟩ :=
    (eventually_ge_atTop 2 |>.and (W_le_self d) |>.and hmargin |>.and hfine).exists
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hw : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hwn : (d.W N : ℝ) ≤ N := by exact_mod_cast hWN
  have he : 1 ≤ (etaT E (t N))⁻¹ := one_le_inv_etaT hE (le_trans (hs0 N) (hst N)) (ht1 N)
  have hp : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow (by linarith) hτ.le
  have hψ : 0 ≤ Ψ N := (hΨpos N).le
  have hδψ : Ψ N ≤ δ N := by nlinarith
  have hδ : 0 ≤ δ N := le_trans hψ hδψ
  have hx : 0 ≤ Real.sqrt (δ N) := Real.sqrt_nonneg _
  have hx2 : (Real.sqrt (δ N)) ^ 2 = δ N := Real.sq_sqrt hδ
  rw [← Real.sqrt_eq_rpow] at hfN
  have hq : (N : ℝ) ≤ ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) := by
    have he3 : (1 : ℝ) ≤ ((etaT E (t N))⁻¹) ^ 3 := one_le_pow₀ he
    have hn3 : (N : ℝ) ≤ (N : ℝ) ^ (3 : ℕ) := by nlinarith [sq_nonneg ((N : ℝ) - 1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr he3) (show 0 ≤ (N : ℝ) ^ (3 : ℕ) by positivity)]
  have hsmall : 4 * (N : ℝ) * Real.sqrt (δ N) ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) hx]
  have hδsmall : 16 * (N : ℝ) ^ 2 * δ N ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsmall)
      (show 0 ≤ 1 + 4 * (N : ℝ) * Real.sqrt (δ N) by positivity)]
  have hδ1 : δ N ≤ 1 := by
    have hfac : 0 ≤ 16 * (N : ℝ) ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg hδ hfac]
  have hψ2 : Ψ N ^ 2 ≤ δ N := by nlinarith [sq_nonneg (δ N - Ψ N)]
  have hscale : 1 ≤ 4 * (N : ℝ) * Ψ N ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (hΨW N) hw.le
    have hi : (d.W N : ℝ) * ((d.W N : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
    nlinarith [mul_nonneg (sub_nonneg.mpr hwn) (sq_nonneg (Ψ N))]
  have hbound : 1 ≤ 4 * (N : ℝ) * δ N := by
    nlinarith [mul_nonneg (show 0 ≤ 4 * (N : ℝ) by positivity)
      (sub_nonneg.mpr hψ2)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hbound)
    (show 0 ≤ 4 * (N : ℝ) by positivity)]

#print axioms no_joint_grid_scales

/-- The obstruction applies on the **first, non-degenerate cell** of the truncated grid
`u_k = min(1-W^{-kτ'}, 1/2)` from p. 24. -/
theorem no_joint_grid_scales_first_cell (d : Dims) {τ' τ : ℝ}
    (hτ' : 0 < τ') (hτ : 0 < τ) {δ Ψ : ℕ → ℝ}
    (hΨpos : ∀ N, 0 < Ψ N)
    (hmargin : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ τ * Ψ N ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹) ^ 3
        * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΨW : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * Ψ N ^ 2) : False := by
  have hs0 : ∀ N, 0 ≤ gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0 := by
    intro N
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have ht1 : ∀ N, gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1 < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
      ≤ gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1 := by
    intro N
    exact gridT_mono (by exact_mod_cast (band d).one_le_W N) hτ'.le (1 / 2 : ℝ)
      (Nat.zero_le 1)
  exact no_joint_grid_scales d hτ (by norm_num) hs0 ht1 hst hΨpos hmargin hfine hΨW

#print axioms no_joint_grid_scales_first_cell

/-! ### The repaired fifth-slot producer -/

/-- The three inputs of (4.5) with the good-event threshold `δ` and the time spacing `μ`
separated.  The remaining hypotheses are the existing local-law, modulus-regime, and
budgeted-gain inputs. -/
theorem eq45FlowInputs_of_localLaw_gain_budget' (d : Dims) {E : ℝ} {s t δ μ Ψ : ℕ → ℝ}
    {K Kc Kenv B Kll Bll : ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hst : ∀ N, s N ≤ t N) (hK : 0 ≤ K)
    (hμ0 : ∀ N, 0 ≤ μ N) (hμ1 : ∀ᶠ N : ℕ in atTop, μ N ≤ 1)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hμnet : ∀ᶠ N : ℕ in atTop,
      1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ μ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * μ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hKll : 0 ≤ Kll) (hBll : 0 ≤ Bll)
    (hKbig : ∀ᶠ N : ℕ in atTop,
      (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ * ((N : ℝ) + 1) ≤ (N : ℝ) ^ Kll)
    (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hΨlowLL : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-Bll) ≤ Ψ N)
    (hll : LocalLawUnifIcc d E s t Ψ)
    {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ τ * Ψ N ≤ δ N)
    (hKc : ∀ᶠ N : ℕ in atTop,
      ((etaT E (t N))⁻¹) ^ 2 * (2 * (N : ℝ) ^ 2 + (N : ℝ) + 7 / 2) ≤ (N : ℝ) ^ Kc)
    (hKtot : HolConst E t Kc K)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hΨW : ∀ τ' > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ')
    {Bp : ℕ → ℕ → ℝ} {Kp : ℕ → ℝ}
    (hg : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N u (zt E u) (mE E) (Bp p N) (2 * Ψ N) (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBK : ∀ p N, Bp p N ≤ Kp p * Ψ N)
    (hΨpos : ∀ N, 0 < Ψ N) (hΨhalf : ∀ N, 2 * Ψ N ≤ 1)
    (hΨW' : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * Ψ N ^ 2) :
    RBM.Eq45FlowInputs (sample d) E s t := by
  let hΩ : HighProb (P d) (goodSetFlow d E s t δ) :=
    highProb_goodSetFlow_of_localLaw d hτ hE hs0 ht1 hst hKll hBll hKbig hΨ0 hΨlowLL
      hll hmargin
  let x : ∀ N, RBM.TimeIcc s t N → Ω d → d.Idx N → ℂ :=
    fun N u ω i => condExpDiag d N (u : ℝ) (zt E (u : ℝ)) (mE E) i ω
  have hIBP : IBPFlow (sample d) E s t x := by
    exact ibpFlow_of_unifDom'
      (y := fun N u ω i => condExpDiag d N u (zt E u) (mE E) i ω)
      d hE hs0 ht1 hst hK hμ0 hδ1 hμ1 hμnet hfine hΩ
      (holIBP_of_inputs (δ := δ) d hE hs0 ht1 hKc hKtot)
      (unifDomIcc_condExpDiag_flow (δ := δ) d hE hs0 ht1 hΨ0 hKenv hB hEnv hΨlow
        hΨ1 hδ1 hΨW hΩ hll)
  have hRow : FlucRowFlow (sample d) E s t x := by
    exact flucRowFlow_of_unifDom'
      (y := fun N u ω i => condExpDiag d N u (zt E u) (mE E) i ω)
      d hE hs0 ht1 hst hK hμ0 hδ1 hμ1 hμnet hfine hΩ
      (holRow_of_inputs (δ := δ) d hE hs0 ht1 hKc hKtot)
      (unifDomIcc_flucRow_condExpDiag_psi_budget (δ := δ) d hE ht1 hg hKp hBK
        hΨpos hΨhalf hΨW' hδ1 hΩ hΨW)
  have hBlk : FlucBlkFlow (sample d) E s t x := by
    exact flucBlkFlow_of_unifDom'
      (y := fun N u ω i => condExpDiag d N u (zt E u) (mE E) i ω)
      d hE hs0 ht1 hst hK hμ0 hδ1 hμ1 hμnet hfine hΩ
      (holBlk_of_inputs (δ := δ) d hE hs0 ht1 hKc hKtot)
      (unifDomIcc_flucBlk_condExpDiag_psi_budget (δ := δ) d hE ht1 hg hKp hBK
        hΨpos hΨhalf hΨW' hδ1 hΩ hΨW)
  exact ⟨x, hIBP, hRow, hBlk⟩

#print axioms eq45FlowInputs_of_localLaw_gain_budget'

/-! ### A genuinely finer independent time mesh -/

/-- With `η_t⁻¹ ≤ N`, the explicit mesh `μ_N=N⁻¹⁶` meets both net requirements at `K=6`.
The threshold `δ` does not occur in either requirement. -/
theorem mesh_pow_sixteen_feasible {E : ℝ} {t : ℕ → ℝ}
    (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (hη : ∀ᶠ N : ℕ in atTop, (etaT E (t N))⁻¹ ≤ (N : ℝ)) :
    (∀ N : ℕ, 0 ≤ (N : ℝ) ^ (-(16 : ℝ))) ∧
    (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(16 : ℝ)) ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop,
      1 / (N : ℝ) ^ (((6 : ℝ) + 2 + 1) / ((1 : ℝ) / 2))
        ≤ (N : ℝ) ^ (-(16 : ℝ))) ∧
    (∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ)
        * ((N : ℝ) ^ (-(16 : ℝ))) ^ ((1 : ℝ) / 2) ≤ 1) := by
  refine ⟨fun N => Real.rpow_nonneg (Nat.cast_nonneg N) _, ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    convert Real.rpow_le_rpow_of_exponent_le hn1 (show -(18 : ℝ) ≤ -(16 : ℝ) by norm_num)
      using 1; norm_num [Real.rpow_neg hn.le, Real.rpow_natCast]
  · filter_upwards [hη, eventually_ge_atTop 2] with N hηN hN
    have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hn0 : (0 : ℝ) < N := by linarith
    have hη0 : (0 : ℝ) ≤ (etaT E (t N))⁻¹ :=
      (inv_pos.mpr (etaT_pos_of_lt_one' hE (ht1 N))).le
    have hη3 : ((etaT E (t N))⁻¹) ^ 3 ≤ (N : ℝ) ^ (3 : ℕ) := by gcongr
    have hμsqrt : ((N : ℝ) ^ (-(16 : ℝ))) ^ ((1 : ℝ) / 2)
        = ((N : ℝ) ^ (8 : ℕ))⁻¹ := by
      rw [← Real.rpow_mul hn0.le]
      norm_num
    rw [hμsqrt]
    have hN8 : (0 : ℝ) < (N : ℝ) ^ (8 : ℕ) := by positivity
    calc
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * ((N : ℝ) ^ (8 : ℕ))⁻¹
          ≤ 4 * (N : ℝ) ^ (3 : ℕ) * (N : ℝ) ^ (3 : ℕ)
              * ((N : ℝ) ^ (8 : ℕ))⁻¹ := by gcongr
      _ ≤ 1 := by
        rw [mul_inv_le_iff₀ hN8]
        nlinarith [sq_nonneg ((N : ℝ) - 2)]

#print axioms mesh_pow_sixteen_feasible

/-- On the first truncated grid cell at `E=0`, the spectral factor is bounded by `N`.
This supplies the premise of `mesh_pow_sixteen_feasible`. -/
theorem first_cell_eta_inv_le {d : Dims} {τ' : ℝ} :
    ∀ᶠ N : ℕ in atTop,
      (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ ≤ (N : ℝ) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have ht : gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1 ≤ 1 / 2 :=
    gridT_le (1 / 2 : ℝ) 1
  have he : etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1) =
      1 - gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1 := by
    have hs : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp [etaT, mE_im, hs]
  rw [he]
  have hp : (0 : ℝ) < 1 - gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1 := by
    linarith
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hi : (1 - gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hp]
    linarith
  linarith

#print axioms first_cell_eta_inv_le

/-- The paper's actual ratio `R=η_{u₀}/η_{u₁}` is strictly greater than one on the
non-degenerate first grid cell. -/
theorem first_cell_eta_ratio_gt_one (d : Dims) {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      1 < etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0) /
        etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1) := by
  filter_upwards [first_cell_window_nondegenerate d hτ'] with N hst
  have hs : gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0 = 0 :=
    gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have ht : gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1 ≤ 1 / 2 :=
    gridT_le (1 / 2 : ℝ) 1
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs' : gridT ((d.W N : ℝ)) τ' (2⁻¹ : ℝ) 0 = 0 :=
    gridT_zero (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  have ht' : gridT ((d.W N : ℝ)) τ' (2⁻¹ : ℝ) 1 ≤ 2⁻¹ := gridT_le _ _
  have hst' : 0 < gridT ((d.W N : ℝ)) τ' (2⁻¹ : ℝ) 1 := by
    have h := hst
    rw [hs] at h
    simpa only [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, band_W] using h
  simp [etaT, mE_im, hsqrt]
  rw [hs', lt_div_iff₀ (by linarith :
    (0 : ℝ) < 1 - gridT ((d.W N : ℝ)) τ' (2⁻¹ : ℝ) 1)]
  linarith

#print axioms first_cell_eta_ratio_gt_one

/-- Explicit simultaneous good-event and mesh scales on the first p. 24 cell.  The
bandwidth is the growing example, `δ=N^(1/16) Ψ`, and `μ=N^(-16)`. -/
theorem first_cell_joint_grid_scales {τ' : ℝ} (hτ' : 0 < τ') :
    let d := Dims.exampleGrow
    let Ψ : ℕ → ℝ := fun N => ((d.W N : ℝ) ^ (-(1 : ℝ) / 2)) / 2
    let δ : ℕ → ℝ := fun N => (N : ℝ) ^ ((1 : ℝ) / 16) * Ψ N
    let μ : ℕ → ℝ := fun N => (N : ℝ) ^ (-(16 : ℝ))
    (∀ N, 0 < Ψ N) ∧ (∀ N, 2 * Ψ N ≤ 1) ∧
    (∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * Ψ N ^ 2) ∧
    (∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 : ℝ)) ≤ Ψ N * Ψ N) ∧
    (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 : ℝ)) ≤ Ψ N) ∧
    (∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ) ∧
    (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 16) * Ψ N ≤ δ N) ∧
    (∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2) ∧
    (∀ N, 0 ≤ μ N) ∧
    (∀ᶠ N : ℕ in atTop, μ N ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop,
      1 / (N : ℝ) ^ (((6 : ℝ) + 2 + 1) / ((1 : ℝ) / 2)) ≤ μ N) ∧
    (∀ᶠ N : ℕ in atTop,
      4 * ((etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹) ^ 3
        * (N : ℝ) ^ (3 : ℕ) * μ N ^ ((1 : ℝ) / 2) ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop,
      gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
        < gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1) ∧
    (∀ᶠ N : ℕ in atTop,
      1 < etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0) /
        etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1)) := by
  dsimp
  let d := Dims.exampleGrow
  let Ψ : ℕ → ℝ := fun N => ((d.W N : ℝ) ^ (-(1 : ℝ) / 2)) / 2
  let δ : ℕ → ℝ := fun N => (N : ℝ) ^ ((1 : ℝ) / 16) * Ψ N
  let μ : ℕ → ℝ := fun N => (N : ℝ) ^ (-(16 : ℝ))
  have hΨpos : ∀ N, 0 < Ψ N := by
    intro N
    dsimp [Ψ]
    have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
    positivity
  have hΨhalf : ∀ N, 2 * Ψ N ≤ 1 := by
    intro N
    dsimp [Ψ]
    have hw : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
    have hp : (1 : ℝ) ≤ (d.W N : ℝ) ^ ((1 : ℝ) / 2) := by
      simpa using (Real.one_le_rpow hw (by norm_num : (0 : ℝ) ≤ 1 / 2))
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ d.W N)]
    have hi : ((d.W N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hp
    linarith
  have hΨWeq : ∀ N, ((d.W N : ℝ))⁻¹ = 4 * Ψ N ^ 2 := by
    intro N
    have hw : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
    dsimp [Ψ]
    have hs : ((d.W N : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = ((d.W N : ℝ))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw]
      norm_num [Real.rpow_neg hw]
    rw [div_pow, hs]
    ring
  have hΨW : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * Ψ N ^ 2 :=
    fun N => (hΨWeq N).le
  have hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1 :=
    Filter.Eventually.of_forall fun N => by
      have h0 := hΨpos N
      have h1 := hΨhalf N
      nlinarith
  have hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 : ℝ)) ≤ Ψ N * Ψ N := by
    filter_upwards [W_le_self d, eventually_ge_atTop 4] with N hWN hN
    have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
    have hwn : (d.W N : ℝ) ≤ N := by exact_mod_cast hWN
    have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
    have hscale : 1 ≤ 4 * (N : ℝ) * Ψ N ^ 2 := by
      have h := mul_le_mul_of_nonneg_left (hΨW N) hw.le
      have hi : (d.W N : ℝ) * ((d.W N : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
      nlinarith [mul_nonneg (sub_nonneg.mpr hwn) (sq_nonneg (Ψ N))]
    have hscale2 : 1 ≤ (N : ℝ) ^ (2 : ℕ) * Ψ N ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - 4)
        (sq_nonneg (Ψ N))]
    have hn2 : (0 : ℝ) < (N : ℝ) ^ (2 : ℕ) := by positivity
    have h := (inv_le_iff_one_le_mul₀ hn2).mpr
      (show 1 ≤ Ψ N ^ 2 * (N : ℝ) ^ (2 : ℕ) by nlinarith [hscale2])
    simpa [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (N : ℝ)),
      Real.rpow_natCast, pow_two] using h
  have hΨlowLL : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 : ℝ)) ≤ Ψ N := by
    filter_upwards [hΨlow, hΨ1] with N hlow h1
    have hpos := hΨpos N
    nlinarith
  have hΨWpoly : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ := by
    intro τ hτ
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
    have heq : 4 * (d.W N : ℝ) * (Ψ N * Ψ N) = 1 := by
      calc 4 * (d.W N : ℝ) * (Ψ N * Ψ N)
          = (d.W N : ℝ) * (4 * Ψ N ^ 2) := by ring
        _ = (d.W N : ℝ) * ((d.W N : ℝ))⁻¹ := by rw [hΨWeq N]
        _ = 1 := mul_inv_cancel₀ hw.ne'
    rw [heq]
    exact Real.one_le_rpow hn hτ.le
  have hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2 := by
    filter_upwards [Dims.bandwidth_grow, eventually_ge_atTop 1] with N hW hN
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
    have hpow : (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (d.W N : ℝ) := by
      calc (N : ℝ) ^ ((1 : ℝ) / 8)
          ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) :=
            Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
        _ ≤ (d.W N : ℝ) := by simpa [d] using hW
    have hroot : (N : ℝ) ^ ((1 : ℝ) / 16) ≤
        (d.W N : ℝ) ^ ((1 : ℝ) / 2) := by
      have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8))
        hpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
      convert h using 1; rw [← Real.rpow_mul (by positivity)]; norm_num
    dsimp [δ, Ψ]
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hw.le]
    have hroot0 : 0 < (d.W N : ℝ) ^ ((1 : ℝ) / 2) := by positivity
    have hprod : (N : ℝ) ^ ((1 : ℝ) / 16) *
        ((d.W N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hroot0]
      simpa using hroot
    linarith
  obtain ⟨hμ0, hμ1, hμnet, hfine⟩ :=
    mesh_pow_sixteen_feasible (E := 0)
      (t := fun N => gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1)
      (by norm_num) (fun N => (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
      first_cell_eta_inv_le
  refine ⟨hΨpos, hΨhalf, hΨW, hΨ1, hΨlow, hΨlowLL, hΨWpoly, ?_, hδ1,
    hμ0, hμ1, hμnet, hfine,
    first_cell_window_nondegenerate d hτ', first_cell_eta_ratio_gt_one d hτ'⟩
  exact Filter.Eventually.of_forall fun N => le_refl _

#print axioms first_cell_joint_grid_scales

/-- The spectral inverse on the truncated first cell has an absolute bound. -/
theorem first_cell_eta_inv_le_two (d : Dims) (τ' : ℝ) (N : ℕ) :
    (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ ≤ 2 := by
  have ht : gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1 ≤ 1 / 2 :=
    gridT_le (1 / 2 : ℝ) 1
  have hs : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have he : etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1) =
      1 - gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1 := by
    simp [etaT, mE_im, hs]
  rw [he, inv_le_iff_one_le_mul₀ (by linarith :
    (0 : ℝ) < 1 - gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1)]
  linarith

/-- All polynomial spectral hypotheses of the split producer hold on this cell with
`K=6`, `Kc=4`, `Kll=3`, and `Kenv=2`. -/
theorem first_cell_polynomial_regime (d : Dims) (τ' : ℝ) :
    let t : ℕ → ℝ := fun N => gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1
    (∀ᶠ N : ℕ in atTop,
      (etaT 0 (t N))⁻¹ * (etaT 0 (t N))⁻¹ * ((N : ℝ) + 1) ≤ (N : ℝ) ^ (3 : ℝ)) ∧
    (∀ᶠ N : ℕ in atTop,
      ((etaT 0 (t N))⁻¹) ^ 2 *
        (2 * (N : ℝ) ^ 2 + (N : ℝ) + 7 / 2) ≤ (N : ℝ) ^ (4 : ℝ)) ∧
    HolConst 0 t 4 6 ∧
    (∀ᶠ N : ℕ in atTop,
      ((etaT 0 (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ (2 : ℝ)) := by
  dsimp
  have hnum : ∀ᶠ N : ℕ in atTop,
      ((etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ *
        (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ * ((N : ℝ) + 1)
          ≤ (N : ℝ) ^ (3 : ℝ)) ∧
      (((etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹) ^ 2 *
        (2 * (N : ℝ) ^ 2 + (N : ℝ) + 7 / 2) ≤ (N : ℝ) ^ (4 : ℝ)) ∧
      ((N : ℝ) ^ (4 : ℝ) +
        (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ *
          (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ * ((N : ℝ) + 1) +
        ((etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ + 1)
          ≤ (N : ℝ) ^ (6 : ℝ)) ∧
      (((etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ + 1) ^ 2
        ≤ (N : ℝ) ^ (2 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
    have hp : 0 < (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ := by
      apply inv_pos.mpr
      exact etaT_pos_of_lt_one' (by norm_num) ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
    have hb := first_cell_eta_inv_le_two d τ' N
    have hpow2 : (16 : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
    have hpow4 : 16 * (N : ℝ) ^ (2 : ℕ) ≤ (N : ℝ) ^ (4 : ℕ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) - 16)
        (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ (2 : ℕ))]
    have hpow6 : 16 * (N : ℝ) ^ (4 : ℕ) ≤ (N : ℝ) ^ (6 : ℕ) := by
      have hm : 0 ≤ ((N : ℝ) ^ (2 : ℕ) - 16) * (N : ℝ) ^ (4 : ℕ) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith
    have hinv2 : ((etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹) ^ 2
        ≤ 4 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 -
        (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹)
        (by linarith : (0 : ℝ) ≤ 2 +
          (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹)]
    have hkll : (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ *
        (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ * ((N : ℝ) + 1)
        ≤ (N : ℝ) ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 -
        (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹)
        (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)]
    have hkc : ((etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹) ^ 2 *
        (2 * (N : ℝ) ^ 2 + (N : ℝ) + 7 / 2) ≤ (N : ℝ) ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
      have hf : 0 ≤ 2 * (N : ℝ) ^ 2 + (N : ℝ) + 7 / 2 := by positivity
      have hm := mul_le_mul_of_nonneg_right hinv2 hf
      nlinarith [hpow4, sq_nonneg ((N : ℝ) - 4)]
    have henv : ((etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ + 1) ^ 2
        ≤ (N : ℝ) ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    refine ⟨hkll, hkc, ?_, henv⟩
    rw [show (4 : ℝ) = (4 : ℕ) by norm_num, show (6 : ℝ) = (6 : ℕ) by norm_num,
      Real.rpow_natCast, Real.rpow_natCast]
    have h34 : (N : ℝ) ^ (3 : ℕ) ≤ (N : ℝ) ^ (4 : ℕ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - 1)
        (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ (3 : ℕ))]
    have hpow4_ge : (1 : ℝ) ≤ (N : ℝ) ^ (4 : ℕ) := by nlinarith [hpow4, hpow2]
    have hterm : (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ + 1
        ≤ 3 := by linarith
    have hkll' : (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ *
        (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ * ((N : ℝ) + 1)
        ≤ (N : ℝ) ^ (3 : ℕ) := by
          convert hkll using 1
          norm_num [Real.rpow_natCast]
    calc
      (N : ℝ) ^ (4 : ℕ) +
          (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ *
            (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ * ((N : ℝ) + 1) +
          ((etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ + 1)
          ≤ (N : ℝ) ^ (4 : ℕ) + (N : ℝ) ^ (3 : ℕ) + 3 := by
            exact add_le_add (add_le_add (le_refl _) hkll') hterm
      _ ≤ 2 * (N : ℝ) ^ (4 : ℕ) + 3 := by linarith [h34]
      _ ≤ 16 * (N : ℝ) ^ (4 : ℕ) := by linarith [hpow4_ge]
      _ ≤ (N : ℝ) ^ (6 : ℕ) := hpow6
  refine ⟨hnum.mono (fun N h => h.1), hnum.mono (fun N h => h.2.1), ?_,
    hnum.mono (fun N h => h.2.2.2)⟩
  change ∀ᶠ N : ℕ in atTop,
    (N : ℝ) ^ (4 : ℝ) +
      (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ *
        (etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ * ((N : ℝ) + 1) +
      ((etaT 0 (gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 1))⁻¹ + 1)
        ≤ (N : ℝ) ^ (6 : ℝ)
  exact hnum.mono (fun N h => h.2.2.1)

#print axioms first_cell_eta_inv_le_two
#print axioms first_cell_polynomial_regime

/-! ### First-cell instantiation of the fifth-slot producer -/

noncomputable def firstCellS (τ' : ℝ) : ℕ → ℝ :=
  fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 0

noncomputable def firstCellT (τ' : ℝ) : ℕ → ℝ :=
  fun N => gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 1

noncomputable def firstCellPsi : ℕ → ℝ :=
  fun N => ((Dims.exampleGrow.W N : ℝ) ^ (-(1 : ℝ) / 2)) / 2

noncomputable def firstCellDelta : ℕ → ℝ :=
  fun N => (N : ℝ) ^ ((1 : ℝ) / 16) * firstCellPsi N

noncomputable def firstCellMu : ℕ → ℝ :=
  fun N => (N : ℝ) ^ (-(16 : ℝ))

/-- On the non-degenerate first cell, all deterministic conditions for the split producer
are discharged.  Only the uniform local law and the existing budgeted gain input remain. -/
theorem first_cell_eq45FlowInputs_of_localLaw_gain' {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi)
    {Bp : ℕ → ℕ → ℝ} {Kp : ℕ → ℝ}
    (hg : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
      FlucGainUpTo' Dims.exampleGrow N u (zt 0 u) (mE 0) (Bp p N)
        (2 * firstCellPsi N) (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p)
    (hBK : ∀ p N, Bp p N ≤ Kp p * firstCellPsi N) :
    RBM.Eq45FlowInputs (sample Dims.exampleGrow) 0 (firstCellS τ') (firstCellT τ') := by
  let d := Dims.exampleGrow
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := by
    intro N
    change 0 ≤ gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have ht1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := by
    intro N
    exact gridT_mono (by exact_mod_cast (band d).one_le_W N) hτ'.le (1 / 2 : ℝ)
      (Nat.zero_le 1)
  obtain ⟨hΨpos, hΨhalf, hΨW, hΨ1, hΨlow, hΨlowLL, hΨWpoly,
    hmargin, hδ1, hμ0, hμ1, hμnet, hfine, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  obtain ⟨hKbig, hKc, hKtot, hEnv⟩ := first_cell_polynomial_regime d τ'
  exact eq45FlowInputs_of_localLaw_gain_budget'
    (d := d) (E := 0) (s := firstCellS τ') (t := firstCellT τ')
    (δ := firstCellDelta) (μ := firstCellMu) (Ψ := firstCellPsi)
    (K := 6) (Kc := 4) (Kenv := 2) (B := 2) (Kll := 3) (Bll := 2)
    (by norm_num) hs0 ht1 hst (by norm_num) hμ0 hμ1 hδ1 hμnet hfine
    (by norm_num) (by norm_num) hKbig (fun N => (hΨpos N).le) hΨlowLL
    hll (by norm_num) hmargin hKc hKtot (by norm_num) (by norm_num)
    hEnv hΨlow hΨ1 hΨWpoly hg hKp hBK hΨpos hΨhalf hΨW

#print axioms first_cell_eq45FlowInputs_of_localLaw_gain'

/-- The repaired first-cell inputs occupy slot 5 of the merged assembly. -/
theorem first_cell_step5_of_localLaw_gain' {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi)
    {Bp : ℕ → ℕ → ℝ} {Kp : ℕ → ℝ}
    (hg : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
      FlucGainUpTo' Dims.exampleGrow N u (zt 0 u) (mE 0) (Bp p N)
        (2 * firstCellPsi N) (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p)
    (hBK : ∀ p N, Bp p N ≤ Kp p * firstCellPsi N) :
    RBM.StepGlue.Eq45Flow (sample Dims.exampleGrow) 0 (firstCellS τ') (firstCellT τ') := by
  apply RBM.eq45Flow_of_eq45FlowInputs (sample Dims.exampleGrow)
    (κ := 1) (by norm_num) (by norm_num) (by norm_num)
  · intro N
    change 0 ≤ gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 0
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  · exact first_cell_eq45FlowInputs_of_localLaw_gain' hτ' hll hg hKp hBK

#print axioms first_cell_step5_of_localLaw_gain'

/-- Under the uniform local-law input, the repaired good event is inhabited on the
non-degenerate first cell; the mesh `μ` is independent of this event. -/
theorem first_cell_flowNetEvent_nonempty_of_localLaw {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    ∀ᶠ N : ℕ in atTop,
      firstCellS τ' N < firstCellT τ' N ∧
        (flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
          firstCellDelta N).Nonempty := by
  let d := Dims.exampleGrow
  obtain ⟨hΨpos, _, _, _, _, hΨlowLL, _, hmargin, _, _, _, _, _, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  obtain ⟨hKbig, _, _, _⟩ := first_cell_polynomial_regime d τ'
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := by
    intro N
    change 0 ≤ gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have ht1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := by
    intro N
    exact gridT_mono (by exact_mod_cast (band d).one_le_W N) hτ'.le (1 / 2 : ℝ)
      (Nat.zero_le 1)
  have hΩ : HighProb (P d)
      (goodSetFlow d 0 (firstCellS τ') (firstCellT τ') firstCellDelta) :=
    highProb_goodSetFlow_of_localLaw d (by norm_num : (0 : ℝ) < 1 / 16)
      (by norm_num) hs0 ht1 hst (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (0 : ℝ) ≤ 2) hKbig (fun N => (hΨpos N).le)
      hΨlowLL hll hmargin
  exact first_cell_flowNetEvent_nonempty d hτ'
    (tEnd := fun _ => (1 / 2 : ℝ)) (Filter.Eventually.of_forall fun _ => by norm_num) hΩ

#print axioms first_cell_flowNetEvent_nonempty_of_localLaw

end RBM.Gauss
