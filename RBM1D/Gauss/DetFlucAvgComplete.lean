/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DetFlucThreshold

/-!
# Fixed-time fluctuation averaging at the deterministic entry scale

The moment consumer below takes the bandwidth comparison only eventually.  This is
essential: its all-size version fails at `N = 0` for the movable threshold.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-- The budgeted moment-to-domination consumer with the coefficient comparison only
eventually in `N`. -/
theorem unifDomIcc_flucAvg_iter_budget_eventually {E : ℝ} {s t : ℕ → ℝ}
    {V : ℕ → Type*} (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    {Tw : ∀ N, V N → d.Idx N → ℝ} {cw : ℕ → ℝ}
    {Aw : ∀ N, V N → Finset (d.Idx N)}
    {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N u (zt E u) (mE E) (Bp p N) (ep N) (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N)
    (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ᶠ N : ℕ in atTop, cw N ≤ ep N ^ 2)
    (hw : ∀ N (a : V N), UniformWeight (Tw N a) (cw N) (Aw N a))
    (hcardA : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ a : V N, 2 * p ≤ (Aw N a).card) :
    UnifDomIcc (P d) s t
      (fun N u (a : V N) ω => ‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖)
      (fun N _ _ _ => ep N * Bm N) := by
  refine unifDomIcc_of_moment (fun N => hpos N) (fun p N u hu a => ?_) ?_
  · exact integrable_norm_flucAvg_pow
      (flucBound_env hE (lt_of_le_of_lt hu.2 (ht1 N)) d N u).flucDiag_le p
  · intro ε hε p
    have hK0 : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) :=
      pow_nonneg (mul_nonneg (by positivity) (hKp p)) _
    have hc1 : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) := by positivity
    have hcoef : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
        * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) := mul_nonneg hc1 hK0
    refine ⟨((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
      * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) + 1, by linarith, ?_⟩
    filter_upwards [hcardA p, hg p, hcρ, eventually_ge_atTop 1]
      with N h2 hgN hcρN hN1 u hu a
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hrw : (fun ω => |‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖| ^ (2 * p))
        = fun ω => ‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖ ^ (2 * p) := by
      funext ω; rw [abs_norm]
    rw [hrw]
    have hmain := integral_norm_flucAvg_pow_le_iter_budget hE hu1 (hgN u hu) le_rfl le_rfl
      (hρ1 N) hcρN (hw N a) (h2 a)
    have hep0 : (0 : ℝ) ≤ ep N := (hgN u hu).rho_nonneg
    have hBp0 : (0 : ℝ) ≤ Bp p N := (hgN u hu).B_nonneg
    have hstep1 : ((2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N) ^ (2 * p)
        ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep N * Bm N) ^ (2 * p) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      calc (2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N
          ≤ (2 : ℝ) ^ (2 * p - 1) * ep N * (Kp p * Bm N) :=
            mul_le_mul_of_nonneg_left (hBK p N) (by positivity)
        _ = ((2 : ℝ) ^ (2 * p - 1) * Kp p) * (ep N * Bm N) := by ring
    have hmain2 : ∫ ω, ‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖ ^ (2 * p) ∂(P d)
        ≤ (((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
            * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p)) * (ep N * Bm N) ^ (2 * p) := by
      refine le_trans hmain ?_
      calc ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * ((2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N) ^ (2 * p)
          ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * (((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep N * Bm N) ^ (2 * p)) :=
            mul_le_mul_of_nonneg_left hstep1 hc1
        _ = _ := by ring
    have hNe : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
    have hpow : (0 : ℝ) ≤ (ep N * Bm N) ^ (2 * p) :=
      pow_nonneg (mul_nonneg hep0 (hBm N)) _
    refine le_trans hmain2 ?_
    nlinarith [mul_nonneg hcoef hpow, hpow, hNe, hcoef]

/-- For each fixed moment order, the local law supplies the actual row or block average
at the movable control `4 δ²`. -/
theorem fixedMoment_flucAvg_budget_family (d : Dims) {E : ℝ} {u Ψ : ℕ → ℝ}
    {a K θ : ℝ} (hE : |E| < 2) (hu0 : ∀ N, 0 ≤ u N)
    (hu1 : ∀ N, u N < 1) (ha : 0 < a) (hK : 0 ≤ K)
    (hθ0 : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N))
    (hΨlo : ∀ᶠ N : ℕ in atTop, ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hll : LocalLawUnifIcc d E u u Ψ)
    {V : ℕ → Type*} {Tw : ∀ N, V N → d.Idx N → ℝ}
    {cw : ℕ → ℝ} {Aw : ∀ N, V N → Finset (d.Idx N)}
    (hw : ∀ N (b : V N), UniformWeight (Tw N b) (cw N) (Aw N b))
    (hcW : ∀ N, cw N ≤ ((d.W N : ℝ))⁻¹)
    (hcard : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ b : V N, 2 * p ≤ (Aw N b).card) :
    UnifDomIcc (P d) u u
      (fun N v (b : V N) ω => ‖flucAvg d N v (zt E v) (mE E) (Tw N b) ω‖)
      (fun N _ _ _ => 4 * detFlucDelta Ψ θ N ^ 2) := by
  let δ := detFlucDelta Ψ θ
  have hg : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Icc (u N) (u N),
      FlucGainUpTo' d N v (zt E v) (mE E)
        ((8 * minorDiffC (2 * p) + 4) * δ N) (4 * δ N) (2 * p) (2 * p) := by
    intro p
    have h := (fixedMoment_gain_of_localLaw d hE hu0 hu1 ha hK hθ0 hθa hθ1
      hη hΨlo hΨhi hll p).1
    filter_upwards [h] with N hN v hv
    convert hN v hv using 1 <;> ring
  have hcρ : ∀ᶠ N : ℕ in atTop, cw N ≤ (4 * δ N) ^ 2 := by
    have h := (fixedMoment_gain_of_localLaw d hE hu0 hu1 ha hK hθ0 hθa hθ1
      hη hΨlo hΨhi hll 0).2
    filter_upwards [h] with N hN
    exact (hcW N).trans hN
  have hδpos : ∀ N, 0 < δ N := detFlucDelta_pos Ψ θ
  have hδ4 : ∀ N, δ N ≤ 1 / 4 := detFlucDelta_le_quarter Ψ θ
  have hKp : ∀ p, (0 : ℝ) ≤ 8 * minorDiffC (2 * p) + 4 := by
    intro p
    have hC := minorDiffC_nonneg (2 * p)
    linarith
  have h := unifDomIcc_flucAvg_iter_budget_eventually d hE hu1 hg hKp
    (fun N => (hδpos N).le) (fun p N => le_refl _)
    (fun N => mul_pos (by linarith [hδpos N]) (hδpos N))
    (fun N => by linarith [hδ4 N]) hcρ hw hcard
  convert h using 1
  funext N v b ω
  ring

/-- Once the bandwidth scale is reached, the floor in the threshold is below `Ψ`.
The remaining loss is at most `N^(2θ)`. -/
theorem detFlucDelta_le_rpow_mul_psi (d : Dims) {Ψ : ℕ → ℝ} {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hΨlo : ∀ᶠ N : ℕ in atTop, ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N) :
    ∀ᶠ N : ℕ in atTop,
      detFlucDelta Ψ θ N ≤ (N : ℝ) ^ (2 * θ) * Ψ N := by
  filter_upwards [hΨlo, W_le_self d, eventually_ge_atTop 4]
    with N hΨN hWN hN4
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : (0 : ℝ) < N := by linarith
  have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hwr : (d.W N : ℝ) ≤ N := by exact_mod_cast hWN
  have hfloorN : ((N : ℝ) + 4) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (by norm_num)
  have hNhalf : (N : ℝ) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hWhalf : (N : ℝ) ^ (-(1 : ℝ) / 2) ≤
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hw hwr (by norm_num)
  have hfloor : ((N : ℝ) + 4) ^ (-(2 : ℝ)) ≤ Ψ N :=
    (hfloorN.trans hNhalf).trans (hWhalf.trans hΨN)
  have hmax : max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ))) = Ψ N :=
    max_eq_left hfloor
  have hΨ0 : 0 ≤ Ψ N := le_trans (Real.rpow_nonneg hw.le _) hΨN
  have hN4r : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hN2 : (N : ℝ) + 4 ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
  have hpow : ((N : ℝ) + 4) ^ θ ≤ (N : ℝ) ^ (2 * θ) := by
    calc
      ((N : ℝ) + 4) ^ θ ≤ ((N : ℝ) ^ (2 : ℕ)) ^ θ :=
        Real.rpow_le_rpow (by positivity) hN2 hθ
      _ = (N : ℝ) ^ (2 * θ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        ring
  calc
    detFlucDelta Ψ θ N ≤ ((N : ℝ) + 4) ^ θ *
        max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ))) := min_le_right _ _
    _ = ((N : ℝ) + 4) ^ θ * Ψ N := by rw [hmax]
    _ ≤ (N : ℝ) ^ (2 * θ) * Ψ N :=
      mul_le_mul_of_nonneg_right hpow hΨ0

/-- Absorb the movable threshold's polynomial loss with half of the requested
stochastic-domination tolerance. -/
theorem detFlucDelta_scale_absorb (d : Dims) {Ψ : ℕ → ℝ} {τ θ : ℝ}
    (hτ : 0 < τ) (hθ0 : 0 ≤ θ) (hθτ : θ ≤ τ / 16)
    (hΨlo : ∀ᶠ N : ℕ in atTop, ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (τ / 2) * (4 * detFlucDelta Ψ θ N ^ 2) ≤
        (N : ℝ) ^ τ * Ψ N ^ 2 := by
  filter_upwards [detFlucDelta_le_rpow_mul_psi d hθ0 hΨlo,
    eventually_ge_atTop 1, eventually_le_rpow 4 (by linarith : 0 < τ / 4)]
      with N hδ hN1 h4
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hδ0 : 0 ≤ detFlucDelta Ψ θ N := (detFlucDelta_pos Ψ θ N).le
  have hsq : detFlucDelta Ψ θ N ^ 2 ≤
      ((N : ℝ) ^ (2 * θ) * Ψ N) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
  have hPowExp : (N : ℝ) ^ (4 * θ) ≤ (N : ℝ) ^ (τ / 4) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hpow2 : ((N : ℝ) ^ (2 * θ)) ^ 2 = (N : ℝ) ^ (4 * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    ring
  have hΨsq : 0 ≤ Ψ N ^ 2 := sq_nonneg _
  calc
    (N : ℝ) ^ (τ / 2) * (4 * detFlucDelta Ψ θ N ^ 2)
      = 4 * (N : ℝ) ^ (τ / 2) * detFlucDelta Ψ θ N ^ 2 := by ring
    _ ≤ 4 * (N : ℝ) ^ (τ / 2) *
        (((N : ℝ) ^ (2 * θ) * Ψ N) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 4 * (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (4 * θ) * Ψ N ^ 2 := by
      rw [mul_pow, hpow2]; ring
    _ ≤ 4 * (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 4) * Ψ N ^ 2 := by
      gcongr
    _ ≤ (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (τ / 2) *
        (N : ℝ) ^ (τ / 4) * Ψ N ^ 2 := by
      gcongr
    _ = (N : ℝ) ^ τ * Ψ N ^ 2 := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 1
      ring

/-- A family of positive thresholds gives domination at the original squared entry
control, because the threshold exponent can be chosen after the requested tolerance. -/
theorem fixedMoment_budgetFamily_absorb (d : Dims) {u Ψ : ℕ → ℝ} {a : ℝ}
    (ha : 0 < a)
    (hΨlo : ∀ᶠ N : ℕ in atTop, ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    {V : ℕ → Type*} {ξ : ∀ N, ℝ → V N → Ω d → ℝ}
    (hfamily : ∀ θ : ℝ, 0 < θ → θ ≤ a / 4 → θ ≤ 1 / 4 →
      UnifDomIcc (P d) u u ξ
        (fun N _ _ _ => 4 * detFlucDelta Ψ θ N ^ 2)) :
    UnifDomIcc (P d) u u ξ (fun N _ _ _ => Ψ N ^ 2) := by
  intro τ hτ D hD
  let θ := detFlucTheta a τ
  obtain ⟨hθ0, hθa, hθτ, hθ1⟩ := detFlucTheta_specs ha hτ
  have hsource := hfamily θ hθ0 hθa.le hθ1 (τ / 2) (by linarith) D hD
  filter_upwards [hsource, detFlucDelta_scale_absorb d hτ hθ0.le hθτ.le hΨlo]
    with N hN hscale v hv b
  refine (measure_mono ?_).trans (hN v hv b)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt hscale hω

/-- The proposition `fixedTimeFAStatement` holds for the actual Gaussian row and block
weights from its stated entry local law and deterministic size hypotheses. -/
theorem fixedTimeFAStatement_proved (d : Dims) (E : ℝ) (u Ψ : ℕ → ℝ) (a K : ℝ) :
    fixedTimeFAStatement d E u Ψ a K := by
  intro ha hK hE hu hη hΨ hll
  have hu0 : ∀ N, 0 ≤ u N := fun N => (hu N).1
  have hu1 : ∀ N, u N < 1 := fun N => (hu N).2
  have hΨlo : ∀ᶠ N : ℕ in atTop, ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N :=
    hΨ.mono (fun N hN => hN.1)
  have hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a) :=
    hΨ.mono (fun N hN => hN.2)
  constructor
  · apply fixedMoment_budgetFamily_absorb d ha hΨlo
    intro θ hθ0 hθa hθ1
    refine fixedMoment_flucAvg_budget_family d hE hu0 hu1 ha hK hθ0 hθa hθ1
      hη hΨlo hΨhi hll (fun N i => uniformWeight_Sblk i) ?_ ?_
    · intro N
      have hw : (0 : ℝ) < d.W N := Nat.cast_pos.2 (d.W_pos N)
      have h3w : (d.W N : ℝ) ≤ (3 * d.W N : ℝ) := by
        push_cast
        linarith
      exact inv_anti₀ hw h3w
    · intro p
      filter_upwards [eventually_le_W d (2 * p)] with N hN i
      rw [card_Sblk_support]
      omega
  · apply fixedMoment_budgetFamily_absorb d ha hΨlo
    intro θ hθ0 hθa hθ1
    refine fixedMoment_flucAvg_budget_family d hE hu0 hu1 ha hK hθ0 hθa hθ1
      hη hΨlo hΨhi hll (fun N b => uniformWeight_blockAvg b) ?_ ?_
    · intro N
      exact le_refl _
    · intro p
      filter_upwards [eventually_le_W d (2 * p)] with N hN b
      rw [card_blockAvg_support]
      exact hN

/-- Restrict a time-uniform fixed-time bound to its deterministic right endpoint. -/
theorem UnifDomIcc.at_right {d : Dims} {s t : ℕ → ℝ} {V : ℕ → Type*}
    {ξ ζ : ∀ N, ℝ → V N → Ω d → ℝ}
    (h : UnifDomIcc (P d) s t ξ ζ) (hst : ∀ N, s N ≤ t N) :
    UnifDomIcc (P d) t t ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN v hv b
  exact hN v ⟨(hst N).trans hv.1, hv.2⟩ b

/-- The previously compiled first-cell fluctuation theorem supplies an independent
positive-time check at its original scale. -/
theorem firstCell_flucAvg_at_positive_time :
    ∃ τ' : ℝ, 0 < τ' ∧
      (∀ᶠ N : ℕ in atTop, 0 < firstCellT τ' N) ∧
      (UnifDomIcc (P Dims.exampleGrow) (firstCellT τ') (firstCellT τ')
        (fun N v (i : Dims.exampleGrow.Idx N) ω =>
          ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0)
            (fun j => Sblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) i j) ω‖)
        (fun N _ _ _ => firstCellPsi N ^ 2) ∧
       UnifDomIcc (P Dims.exampleGrow) (firstCellT τ') (firstCellT τ')
        (fun N v (b : ZMod (Dims.exampleGrow.L N)) ω =>
          ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0)
            (blkCoef (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) b) ω‖)
        (fun N _ _ _ => firstCellPsi N ^ 2)) := by
  obtain ⟨τ', hτ', hll⟩ := firstCell_localLawUnifIcc_of_step1
  have hwin := first_cell_window_nondegenerate Dims.exampleGrow hτ'
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < firstCellT τ' N := by
    filter_upwards [hwin] with N hN
    change firstCellS τ' N < firstCellT τ' N at hN
    rw [firstCellS_eq_zero] at hN
    exact hN
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := by
    intro N
    change gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 0 ≤
      gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 1
    exact gridT_mono (by exact_mod_cast (band Dims.exampleGrow).one_le_W N)
      hτ'.le (1 / 2 : ℝ) (Nat.zero_le 1)
  obtain ⟨hrow, hblk⟩ := firstCellFlucAvg_psiSq_of_localLaw hτ' hll
  exact ⟨τ', hτ', hpos, hrow.at_right hst, hblk.at_right hst⟩

/-- A nondegenerate Gaussian instance of the general fixed-time theorem at the
positive right endpoint of the first flow cell. -/
theorem fixedTimeFA_gaussian_witness_pos :
    ∃ τ' : ℝ, 0 < τ' ∧
      (∀ᶠ N : ℕ in atTop, 0 < firstCellT τ' N) ∧
      (∀ N, 0 ≤ firstCellT τ' N ∧ firstCellT τ' N < 1) ∧
      (∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT 0 (firstCellT τ' N)) ∧
      (∀ᶠ N : ℕ in atTop,
        ((Dims.exampleGrow.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ 2 * firstCellPsi N ∧
          2 * firstCellPsi N ≤ (N : ℝ) ^ (-(1 : ℝ) / 8)) ∧
      LocalLawUnifIcc Dims.exampleGrow 0 (firstCellT τ') (firstCellT τ')
        (fun N => 2 * firstCellPsi N) ∧
      (UnifDomIcc (P Dims.exampleGrow) (firstCellT τ') (firstCellT τ')
        (fun N v (i : Dims.exampleGrow.Idx N) ω =>
          ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0)
            (fun j => Sblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) i j) ω‖)
        (fun N _ _ _ => (2 * firstCellPsi N) ^ 2) ∧
       UnifDomIcc (P Dims.exampleGrow) (firstCellT τ') (firstCellT τ')
        (fun N v (b : ZMod (Dims.exampleGrow.L N)) ω =>
          ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0)
            (blkCoef (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) b) ω‖)
        (fun N _ _ _ => (2 * firstCellPsi N) ^ 2)) := by
  obtain ⟨τ', hτ', hpos, hll, hlo, hhi, hη⟩ :=
    detFlucThreshold_gaussian_witness_pos
  have hu0 : ∀ N, 0 ≤ firstCellT τ' N := by
    intro N
    have hst : firstCellS τ' N ≤ firstCellT τ' N := by
      change gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 0 ≤
        gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 1
      exact gridT_mono (by exact_mod_cast (band Dims.exampleGrow).one_le_W N)
        hτ'.le (1 / 2 : ℝ) (Nat.zero_le 1)
    simpa only [firstCellS_eq_zero] using hst
  have hu1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hhi' : ∀ᶠ N : ℕ in atTop,
      2 * firstCellPsi N ≤ (N : ℝ) ^ (-( (1 : ℝ) / 8)) := by
    filter_upwards [hhi] with N hN
    convert hN using 1 <;> ring
  have hfa := fixedTimeFAStatement_proved Dims.exampleGrow 0
    (firstCellT τ') (fun N => 2 * firstCellPsi N) (1 / 8) 1
    (by norm_num) (by norm_num) (by norm_num)
    (fun N => ⟨hu0 N, hu1 N⟩) hη (hlo.and hhi') hll
  exact ⟨τ', hτ', hpos, (fun N => ⟨hu0 N, hu1 N⟩), hη,
    hlo.and hhi, hll, hfa⟩

#print axioms unifDomIcc_flucAvg_iter_budget_eventually
#print axioms fixedMoment_flucAvg_budget_family
#print axioms detFlucDelta_le_rpow_mul_psi
#print axioms detFlucDelta_scale_absorb
#print axioms fixedMoment_budgetFamily_absorb
#print axioms fixedTimeFAStatement_proved
#print axioms firstCell_flucAvg_at_positive_time
#print axioms fixedTimeFA_gaussian_witness_pos

end RBM.Gauss
