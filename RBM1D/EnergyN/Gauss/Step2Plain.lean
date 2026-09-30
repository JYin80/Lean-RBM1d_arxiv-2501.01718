/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Plain
import RBM1D.EnergyN.Hierarchy.SumZeroDyn
import RBM1D.EnergyN.Hierarchy.StepGlue

/-!
# Step 2 for the Gaussian flow under the plain pair, first part, at an `N`-dependent energy

The first part of Step 2 for the Gaussian flow at an `N`-dependent energy `E : ℕ → ℝ`: (2.72)
from the plain pair (`cond272_of_plainN`), the eventual scale facts
(`eventually_step_facts_plainN`, `grid_phi_premises'N`, `etaT_inv_le_of_plainN`,
`plain_endpointN`, `scale_endpointN`, `thr_le_sqrtN_plainN`), the deterministic threshold
improvement on the grid (`grid_thr_improve'N`), the initial bound on the grid
(`highProb_init_grid_plainN`), the martingale bounds (`hsubG_gridTau_plainN`,
`highProb_azuma_grid_plainN`) and the Chebyshev bound at the stopping index
(`cheb_grid_at_tau_plainN`). The second part is in `RBM1D/EnergyN/Gauss/Step2Gauss.lean`.

## The external `κ`

`eventually_step_facts_plainN` involves `(mE (E N)).im` in two constants,
`2 cTail + ((mE (E N)).im²)⁻¹` and `cStep (mE (E N)).im + 1`, and `grid_phi_premises'N` calls it
and involves `cStep (mE (E N)).im + 3`; all must be bounded before `∀ᶠ N`. Both take `κ : ℝ`,
`hκ0 : 0 < κ`, `hE : ∀ N, |E N| ≤ 2 - κ`, and use the uniform `mκ := √(2κ')/2 ≤ (mE (E N)).im`
for every `N` (`κ' := min κ 1`, `mE_im_ge`, as in `GridGoodEvent.lean`).
`Step2.cStep m = 4 + e + (36e+2) m⁻¹` is antitone in `m > 0` (its only `m`-term is
`(36e+2) m⁻¹`), proved inline as the `xiK`-antitone argument there. The later statements of this
file (`grid_thr_improve'N` onward) use `κ` only through these two, with no further
energy-dependent constant.

`Cond272N`, `BoundsCoreN` (used by `highProb_init_grid_plainN`'s `hB`) are in
`Flow/EnergyUniform.lean`. `StepGlue.eventually_R4_le_scale_of_cond272N`
(`RBM1D/EnergyN/Hierarchy/StepGlue.lean`) and `SumZeroDyn.flow_crudeN`
(`RBM1D/EnergyN/Hierarchy/SumZeroDyn.lean`) are the energy-dependent inputs; all other inputs
(`driftCoef'`, `phiG'`, `grid_step_bound'`, `Agrid`/`Zvec`/`Yvec`/`Dgrid`/`Rgrid`, `jSMat`,
`Step2.thr`/`xiK`/`cStep`/`tT`, `qGrid`, `phi_arith'`, the measure-theoretic kernel lemmas, …)
are energy-free or generic, used at `E N`. The three `private` helpers
`ofFn_pm_eq_pmLoop_pl`, `Lval_band_eq_pl`, `Kv_band_eq_pl` of `highProb_init_grid_plainN` take a
plain `E : ℝ` argument and are called at `E N`.
-/

noncomputable section

namespace RBM.Step2

open Finset Real MeasureTheory Filter

section PlainFactsN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **(2.72) from the plain pair**: `(η_s/η_t)^30 ≤ W ℓ_t η_t` eventually gives `Cond272N`. -/
theorem cond272_of_plainN (hE : ∀ N, |E N| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N)) :
    Cond272N B E s t := by
  filter_upwards [hreg0] with N hN
  have ht := ht1 N
  have hs1 : s N < 1 := (hst N).trans_lt ht
  have hR := etaT_ratio (hE N) (s N) (t N)
  have h1t : 0 < 1 - t N := by linarith
  have h1s : 0 < 1 - s N := by linarith
  have hR0 : 0 < (1 - s N) / (1 - t N) := div_pos h1s h1t
  rw [hR] at hN
  have hpos : 0 < ((1 - s N) / (1 - t N)) ^ 30 := pow_pos hR0 30
  calc (B.scale (E N) N (t N))⁻¹ ≤ (((1 - s N) / (1 - t N)) ^ 30)⁻¹ := inv_anti₀ hpos hN
    _ = ((1 - t N) / (1 - s N)) ^ 30 := by rw [← inv_pow, inv_div]

/-- **The eventual scale facts of Step 2**: eventually `e ≤ W`, `cStep < N^{6δ/8}`,
`xiK ≤ N^{δ/8}`, `1 ≤ W ℓ_s η_s`, and three inequalities between `N^{δ/8}`, `(η_s/η_v)^{10}` and
`W ℓ_v η_v` at every `v ∈ [s, t]`. The two constants `2 cTail + ((mE (E N)).im²)⁻¹` and
`cStep (mE (E N)).im + 1` are bounded by the uniform κ-bounds `2 cTail + mκ⁻²` and
`cStep mκ + 1`, with `mκ ≤ (mE (E N)).im` for every `N` (`mE_im_ge`); `cStep` is antitone in its
argument (its only term is `(36e+2) m⁻¹`). -/
theorem eventually_step_facts_plainN {κ : ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (_hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : 90 * δ ≤ c) (hD : 60 ≤ D) :
    ∀ᶠ N : ℕ in atTop, exp 1 ≤ (B.W N : ℝ) ∧ 1 ≤ (N : ℝ) ^ (δ / 8) ∧
      cStep (mE (E N)).im < ((N : ℝ) ^ (δ / 8)) ^ 6 ∧
      xiK (B.L N) (B.W N) (mE (E N)).im ≤ (N : ℝ) ^ (δ / 8) ∧ 1 ≤ B.scale (E N) N (s N) ∧
      ∀ v : TimeIcc s t N,
        ((N : ℝ) ^ (δ / 8)) ^ 17 * (etaT (E N) (s N) / etaT (E N) v) ^ 10 ≤ B.scale (E N) N v ∧
        (B.scale (E N) N v)⁻¹ ^ ((3 : ℝ) / 7) *
          (((N : ℝ) ^ (δ / 8)) ^ 24 * (etaT (E N) (s N) / etaT (E N) v) ^ 10) ≤ 1 ∧
        (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D) * ((N : ℝ) ^ (δ / 8)) ^ 17 *
          (etaT (E N) (s N) / etaT (E N) v) ^ 10 ≤ 1 := by
  have hE2 : ∀ N, |E N| < 2 := fun N => lt_of_le_of_lt (hE N) (by linarith)
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'2 : κ' ≤ 2 := hκ'1.trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hmκpos : 0 < mκ := by positivity
  have hmge : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have h272 := cond272_of_plainN hE2 hst ht1 hreg0
  have hδ16 : 0 < δ / 16 := by positivity
  filter_upwards [hreg0, hAc, SumZeroDyn.flow_crudeN hE2 hs0 hst ht1 h272, B.dim,
    eventually_le_W_sq B,
    (tendsto_W B).eventually_ge_atTop (exp 400),
    (tendsto_W B).eventually (eventually_exp_mul_log_rpow_le 1 hδ16),
    eventually_le_rpow (2 * cTail + (mκ ^ 2)⁻¹) hδ16, eventually_le_rpow 2 hδ16,
    eventually_le_rpow (cStep mκ + 1) (by positivity : (0 : ℝ) < 3 * δ / 4),
    eventually_ge_atTop 1] with N hreg' hAcN hcr hdim hW2 hWe hWexp hC1' hC2 hC3' hN1
  obtain ⟨hLN, hWN, -, hsc⟩ := hcr
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : ℝ) < B.W N := by linarith
  set x := (N : ℝ) ^ (δ / 8) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow hN (by positivity)
  have hm0 := mE_im_pos (hE2 N)
  have hC1 : 2 * cTail + ((mE (E N)).im ^ 2)⁻¹ ≤ (N : ℝ) ^ (δ / 16) := by
    have hle : mκ ^ 2 ≤ (mE (E N)).im ^ 2 := by nlinarith [hmge N, hmκpos.le]
    have hinv2 : ((mE (E N)).im ^ 2)⁻¹ ≤ (mκ ^ 2)⁻¹ := inv_anti₀ (by positivity) hle
    linarith
  have hC3 : cStep (mE (E N)).im + 1 ≤ (N : ℝ) ^ (3 * δ / 4) := by
    have hinv : (mE (E N)).im⁻¹ ≤ mκ⁻¹ := inv_anti₀ hmκpos (hmge N)
    have h36 : (0 : ℝ) ≤ 36 * Real.exp 1 + 2 := by positivity
    have hcm : cStep (mE (E N)).im ≤ cStep mκ := by
      unfold cStep
      have := mul_le_mul_of_nonneg_left hinv h36
      linarith
    linarith
  clear hC1' hC3' hmge hEκ' hκ'2 hκ'1 hκ'0 hκ'def hmκpos hmκdef mκ κ' h272
  set m := (mE (E N)).im with hm
  refine ⟨le_trans (exp_le_exp.2 (by norm_num)) hWe, hx1, ?_, ?_, (hsc ⟨s N, le_rfl, hst N⟩).1,
    ?_⟩
  · -- `C < x⁶`
    rw [hx, natCast_rpow_pow]
    have : δ / 8 * ((6 : ℕ) : ℝ) = 3 * δ / 4 := by push_cast; ring
    rw [this]; linarith
  · -- `Ξ ≤ x`
    have hLW : (B.L N : ℝ) ≤ (B.W N : ℝ) ^ 2 := hLN.trans hW2
    have hexpL : 2 * (B.L N : ℝ) * exp (-(log (B.W N) ^ (3 / 2 : ℝ) / 8)) ≤ 1 := by
      have := two_mul_sq_mul_exp_le hWe
      have h0 := exp_pos (-(log (B.W N) ^ (3 / 2 : ℝ) / 8))
      nlinarith
    have hct := cTail_nonneg
    have h1 : cTail * (1 + 2 * B.L N * exp (-(log (B.W N) ^ (3 / 2 : ℝ) / 8))) ≤ 2 * cTail := by
      nlinarith
    have h2 : exp (log (B.W N) ^ (3 / 4 : ℝ)) ≤ (N : ℝ) ^ (δ / 16) := by
      have := hWexp
      rw [one_mul] at this
      exact this.trans (Real.rpow_le_rpow hW0.le hWN hδ16.le)
    have hsplit : (N : ℝ) ^ (δ / 16) * (N : ℝ) ^ (δ / 16) = x := by
      rw [← Real.rpow_add hN0, hx]; ring_nf
    unfold xiK
    have h3 : 0 ≤ (N : ℝ) ^ (δ / 16) := Real.rpow_nonneg hN0.le _
    nlinarith
  · intro v
    have hv0 : (0 : ℝ) ≤ (v : ℝ) := (hs0 N).trans v.2.1
    have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have h1v : 0 < 1 - (v : ℝ) := by linarith
    have h1t : 0 < 1 - t N := by linarith [ht1 N]
    have h1s : 0 < 1 - s N := by linarith
    set R := etaT (E N) (s N) / etaT (E N) v with hR
    have hRe : R = (1 - s N) / (1 - v) := etaT_ratio (hE2 N) _ _
    have hR1 : 1 ≤ R := by rw [hRe, le_div_iff₀ h1v]; linarith [v.2.1]
    have hRt : R ≤ etaT (E N) (s N) / etaT (E N) (t N) := by
      rw [hRe, etaT_ratio (hE2 N)]
      exact div_le_div_of_nonneg_left h1s.le h1t (by linarith [v.2.2])
    have hRN : R ≤ N := by
      rw [hRe]
      calc (1 - s N) / (1 - v) ≤ 1 / (1 - v) :=
            div_le_div_of_nonneg_right (by linarith [hs0 N]) h1v.le
        _ = (1 - (v : ℝ))⁻¹ := one_div _
        _ ≤ N := (hsc v).2.2
    have hAv : B.scale (E N) N (t N) ≤ B.scale (E N) N v := flowScale_antitoneOn hW0.le (B.L N)
      (E N) (Set.mem_Iic.2 hv1.le) (Set.mem_Iic.2 (ht1 N).le) v.2.2
    have hR0 : 0 ≤ R := by linarith
    have hx0 : 0 ≤ x := by linarith
    -- the two plain inputs at `v`
    have hRA : R ^ 30 ≤ B.scale (E N) N v :=
      (pow_le_pow_left₀ hR0 hRt 30).trans (hreg'.trans hAv)
    have hNA : (N : ℝ) ^ c ≤ B.scale (E N) N v := hAcN.trans hAv
    have hApos : 0 < B.scale (E N) N v := B.scale_pos' (hE2 N) N hv0 hv1
    refine ⟨?_, ?_, ?_⟩
    · -- `x^{17} R^{10} ≤ A_v`
      have hx51 : x ^ 51 ≤ B.scale (E N) N v ^ 2 :=
        natCast_rpow_pow_le_of_le hN (by push_cast; linarith) hNA
      have h3 : (x ^ 17 * R ^ 10) ^ 3 ≤ B.scale (E N) N v ^ 3 := by
        calc (x ^ 17 * R ^ 10) ^ 3 = x ^ 51 * R ^ 30 := by ring
          _ ≤ B.scale (E N) N v ^ 2 * B.scale (E N) N v :=
              mul_le_mul hx51 hRA (by positivity) (by positivity)
          _ = B.scale (E N) N v ^ 3 := by ring
      exact (pow_le_pow_iff_left₀ (by positivity) hApos.le (by norm_num)).1 h3
    · -- `A^{-3/7} x^{24} R^{10} ≤ 1`
      have hx504 : x ^ 504 ≤ B.scale (E N) N v ^ 2 :=
        natCast_rpow_pow_le_of_le hN (by push_cast; linarith) hNA
      have hy0 : 0 ≤ x ^ 24 * R ^ 10 := by positivity
      have ha37 : 0 ≤ B.scale (E N) N v ^ ((3 : ℝ) / 7) := Real.rpow_nonneg hApos.le _
      have hpow : (B.scale (E N) N v ^ ((3 : ℝ) / 7)) ^ 21 = B.scale (E N) N v ^ 9 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hApos.le, ← Real.rpow_natCast]
        norm_num
      have h21 : (x ^ 24 * R ^ 10) ^ 21 ≤ (B.scale (E N) N v ^ ((3 : ℝ) / 7)) ^ 21 := by
        rw [hpow]
        calc (x ^ 24 * R ^ 10) ^ 21 = x ^ 504 * (R ^ 30) ^ 7 := by ring
          _ ≤ B.scale (E N) N v ^ 2 * B.scale (E N) N v ^ 7 :=
              mul_le_mul hx504 (pow_le_pow_left₀ (by positivity) hRA 7) (by positivity)
                (by positivity)
          _ = B.scale (E N) N v ^ 9 := by ring
      have hle := (pow_le_pow_iff_left₀ hy0 ha37 (by norm_num)).1 h21
      rw [Real.inv_rpow hApos.le, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hApos _), mul_one]
      exact hle
    · -- `W L W^{-D} x^{17} R^{10} ≤ 1` (no scale input)
      have hWD : (N : ℝ) ^ 30 ≤ (B.W N : ℝ) ^ D := by
        calc (N : ℝ) ^ 30 ≤ ((B.W N : ℝ) ^ 2) ^ 30 := pow_le_pow_left₀ hN0.le hW2 30
          _ = (B.W N : ℝ) ^ ((60 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; ring
          _ ≤ (B.W N : ℝ) ^ D := Real.rpow_le_rpow_of_exponent_le hW1 (by push_cast; linarith)
      have hWLN : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
      have hxN : x ≤ N := by
        rw [hx]
        calc (N : ℝ) ^ (δ / 8) ≤ (N : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hN (by linarith)
          _ = N := Real.rpow_one _
      have hWDpos : 0 < (B.W N : ℝ) ^ D := Real.rpow_pos_of_pos hW0 D
      rw [Real.rpow_neg hW0.le]
      have h1 : (B.W N : ℝ) * B.L N * ((B.W N : ℝ) ^ D)⁻¹ * x ^ 17 * R ^ 10
          ≤ N * ((N : ℝ) ^ 30)⁻¹ * N ^ 17 * N ^ 10 := by
        gcongr
      refine h1.trans ?_
      have e : (N : ℝ) * ((N : ℝ) ^ 30)⁻¹ * N ^ 17 * N ^ 10 = ((N : ℝ) ^ 2)⁻¹ := by
        field_simp
      rw [e]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ hN)

section CompatN

end CompatN

end PlainFactsN

end RBM.Step2

namespace RBM.Gauss.Grid

open RBM Finset MeasureTheory Filter Real

section ImprovePlainN

variable {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℕ → ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ}

/-- **`η_t⁻¹ ≤ N` eventually**, from `N^c ≤ W ℓ_t η_t` eventually. -/
theorem etaT_inv_le_of_plainN (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N)) :
    ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) := by
  filter_upwards [hAc, B.dim, eventually_ge_atTop 1] with N hAcN hdimN hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hηt : 0 < etaT (E N) (t N) := Step2.etaT_pos' (hE N) (ht1 N)
  have hellle : B.ell N (t N) ≤ (B.L N : ℝ) := min_le_right _ _
  have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
  have hscale_le : B.scale (E N) N (t N) ≤ (B.W N : ℝ) * (B.L N : ℝ) * etaT (E N) (t N) := by
    change (B.W N : ℝ) * B.ell N (t N) * etaT (E N) (t N) ≤ _
    have h1 : (B.W N : ℝ) * B.ell N (t N) ≤ (B.W N : ℝ) * (B.L N : ℝ) :=
      mul_le_mul_of_nonneg_left hellle hW0
    exact mul_le_mul_of_nonneg_right h1 hηt.le
  have hWLN : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdimN.1
  have hchain : (N : ℝ) ^ c ≤ (N : ℝ) * etaT (E N) (t N) :=
    calc (N : ℝ) ^ c ≤ B.scale (E N) N (t N) := hAcN
      _ ≤ (B.W N : ℝ) * (B.L N : ℝ) * etaT (E N) (t N) := hscale_le
      _ ≤ (N : ℝ) * etaT (E N) (t N) := mul_le_mul_of_nonneg_right hWLN hηt.le
  have h1c : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0.le
  have hbig : (1 : ℝ) ≤ (N : ℝ) * etaT (E N) (t N) := h1c.trans hchain
  have h := mul_le_mul_of_nonneg_right hbig (inv_nonneg.2 hηt.le)
  rwa [one_mul, mul_assoc, mul_inv_cancel₀ hηt.ne', mul_one] at h

/-- **The premises of the grid bound**: the facts of `eventually_step_facts_plainN` with
`cStep + 2`, and `2 ≤ N`, `W L ≤ N`, `η_t⁻¹ ≤ N`. The constant `Step2.cStep (mE (E N)).im + 3` is
bounded by the uniform κ-bound `cStep mκ + 3` (as for `eventually_step_facts_plainN` above). -/
theorem grid_phi_premises'N {κ : ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : 90 * δ ≤ c) (hD : 64 ≤ D) :
    ∀ᶠ N : ℕ in atTop, exp 1 ≤ (B.W N : ℝ) ∧ 1 ≤ (N : ℝ) ^ (δ / 8) ∧
      Step2.cStep (mE (E N)).im + 2 < ((N : ℝ) ^ (δ / 8)) ^ 6 ∧
      Step2.xiK (B.L N) (B.W N) (mE (E N)).im ≤ (N : ℝ) ^ (δ / 8) ∧ 2 ≤ N ∧
      (B.W N : ℝ) * B.L N ≤ N ∧ (etaT (E N) (t N))⁻¹ ≤ N ∧
      ∀ v ∈ Set.Icc (s N) (t N),
        ((N : ℝ) ^ (δ / 8)) ^ 17 * (etaT (E N) (s N) / etaT (E N) v) ^ 10 ≤ B.scale (E N) N v ∧
        (B.scale (E N) N v)⁻¹ ^ ((3 : ℝ) / 7) *
          (((N : ℝ) ^ (δ / 8)) ^ 24 * (etaT (E N) (s N) / etaT (E N) v) ^ 10) ≤ 1 ∧
        (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D) * ((N : ℝ) ^ (δ / 8)) ^ 17 *
          (etaT (E N) (s N) / etaT (E N) v) ^ 10 ≤ 1 := by
  have hE2 : ∀ N, |E N| < 2 := fun N => lt_of_le_of_lt (hE N) (by linarith)
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'2 : κ' ≤ 2 := hκ'1.trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hmκpos : 0 < mκ := by positivity
  have hmge : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  filter_upwards [Step2.eventually_step_facts_plainN (D := D) hκ0 hE hs0 hst ht1 hc0 hreg0 hAc
      hδ0 hδ1 hδc (by linarith), eventually_le_rpow (Step2.cStep mκ + 3)
      (by positivity : (0 : ℝ) < 3 * δ / 4), B.dim, eventually_ge_atTop 2,
      etaT_inv_le_of_plainN B hE2 ht1 hc0 hAc] with N hF hC' hdim hN2 hη
  obtain ⟨hWe, hx1, -, hΞ, -, hvF⟩ := hF
  have hC : Step2.cStep (mE (E N)).im + 3 ≤ (N : ℝ) ^ (3 * δ / 4) := by
    have hinv : (mE (E N)).im⁻¹ ≤ mκ⁻¹ := inv_anti₀ hmκpos (hmge N)
    have h36 : (0 : ℝ) ≤ 36 * Real.exp 1 + 2 := by positivity
    have hcm : Step2.cStep (mE (E N)).im ≤ Step2.cStep mκ := by
      unfold Step2.cStep
      have := mul_le_mul_of_nonneg_left hinv h36
      linarith
    linarith
  clear hC' hκ'0 hκ'1 hκ'2 hκ'def hmge hEκ' hmκpos hmκdef mκ κ'
  refine ⟨hWe, hx1, ?_, hΞ, hN2, by exact_mod_cast hdim.1, hη, fun v hv => hvF ⟨v, hv⟩⟩
  rw [Step2.natCast_rpow_pow]
  have : δ / 8 * ((6 : ℕ) : ℝ) = 3 * δ / 4 := by push_cast; ring
  rw [this]; linarith

/-- **The deterministic threshold improvement on the grid**: given the grid Duhamel expansion of
`Agrid` and bounds on its initial value, drift, martingale and remainder terms, at each grid
time `k`, `jSMat ≤ cStep N^{2δ/8} (η_s/η_{u_k})^4 + 2 < thr`. It uses the κ-bound through
`grid_phi_premises'N`; no further energy-dependent constant. -/
theorem grid_thr_improve'N {κ : ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N))
    {δ D ζ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : 90 * δ ≤ c) (hD : 64 ≤ D) (hζ : 0 ≤ ζ) :
    ∀ᶠ N : ℕ in atTop, ∀ Mi Mg Mm : ℝ, 0 ≤ Mi → 0 ≤ Mg → Mi ≤ (N : ℝ) ^ (δ / 8) →
      65 * (N : ℝ) ^ (3 * ζ) * Mg ≤ (N : ℝ) ^ (δ / 8) → Mm ≤ (N : ℝ) ^ (δ / 8) →
      1 ≤ K N → step s t K N ≤ (N : ℝ) ^ (-(2 * D + 76)) →
      ∀ k, k ≤ K N → ∀ ω : Ωg B.toDims,
      (∀ b : LoopArg (B.L N) 2, Agrid B (E N) s t K N k ω b
          = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (time s t K N k : ℂ)
                (Agrid B (E N) s t K N 0 ω) b
            + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
                (Zvec B (E N) s t K N (j + 1) ω)) b
            + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
                (Yvec B (E N) s t K N (j + 1) ω)) b
            + (∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
                (Dgrid B (E N) s t K N j ω)) b
            + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
                (Rgrid B (E N) s t K N j ω)) b) →
      (∀ b, ‖Agrid B (E N) s t K N 0 ω b‖ ≤
        Mi * Step2.tT B (E N) N D (time s t K N 0) (zdist (B.L N) (b 0 - b 1))) →
      (∀ j < k, ∀ b, ‖Dgrid B (E N) s t K N j ω b‖ ≤
        driftCoef' B (E N) s δ D ζ Mg N (time s t K N j) *
          Step2.tT B (E N) N D (time s t K N j) (zdist (B.L N) (b 0 - b 1))) →
      (∀ b, ‖(∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
          (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
          (Zvec B (E N) s t K N (j + 1) ω)) b‖ ≤
        Mm * ((etaT (E N) (s N) / etaT (E N) (time s t K N k)) ^ 2 + 1) *
          Step2.tT B (E N) N D (time s t K N k) (zdist (B.L N) (b 0 - b 1))) →
      (∀ b, ‖(∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
          (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
          (Yvec B (E N) s t K N (j + 1) ω)) b‖ ≤
        Step2.tT B (E N) N D (time s t K N k) (zdist (B.L N) (b 0 - b 1))) →
      (∀ j < k, ∀ b, ‖Rgrid B (E N) s t K N j ω b‖ ≤
        stepErr B (E N) N (time s t K N j) (time s t K N (j + 1)) (step s t K N)) →
      jSMat B.toDims (E N) D N (time s t K N k) (H B.toDims s t K N k ω) ≤
          Step2.cStep (mE (E N)).im * ((N : ℝ) ^ (δ / 8)) ^ 2 *
            (etaT (E N) (s N) / etaT (E N) (time s t K N k)) ^ 4 + 2 ∧
        Step2.cStep (mE (E N)).im * ((N : ℝ) ^ (δ / 8)) ^ 2 *
            (etaT (E N) (s N) / etaT (E N) (time s t K N k)) ^ 4 + 2
          < Step2.thr (E N) s δ N (time s t K N k) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => lt_of_le_of_lt (hE N) (by linarith)
  filter_upwards [grid_phi_premises'N B hκ0 hE hs0 hst ht1 hc0 hreg0 hAc hδ0 hδ1 hδc hD]
    with N hF Mi Mg Mm hMi hMg hMix hMgx hMmx hK1 hΔR k hk ω hexp hinit hdrift hZ hY hRstep
  obtain ⟨hWe, hx1, hCx, hΞ, hN2, hWL, hηt, hvF⟩ := hF
  set x := (N : ℝ) ^ (δ / 8) with hx
  have hN1 : 1 ≤ N := by omega
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hm0 := mE_im_pos (hE2 N)
  set m := (mE (E N)).im with hm
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  set u := time s t K N k with hu
  have huk : u ≤ t N := time_le_t s t K N (hst N) hK1 hk
  have hsu : s N ≤ u := s_le_time s t K N (hst N) k
  have hu1 : u < 1 := huk.trans_lt (ht1 N)
  have hu0 : 0 ≤ u := (hs0 N).trans hsu
  -- (T1)
  have hstep := grid_step_bound' B (hE2 N) (hs0 N) (hst N) (ht1 N) hK1 hk hWe hN2 hWL hηt
    (by linarith : (0 : ℝ) ≤ D) hMi hMg hΔR ω hexp hinit hdrift hZ hY hRstep
  have hJ := jSMat_le_of_Agrid B hstep
  -- the arithmetic
  obtain ⟨hvA, hvα, hvε⟩ := hvF u ⟨hsu, huk⟩
  set R := etaT (E N) (s N) / etaT (E N) u with hR
  have hRe : R = (1 - s N) / (1 - u) := Step2.etaT_ratio (hE2 N) _ _
  have h1u : 0 < 1 - u := by linarith
  have hR1 : 1 ≤ R := by rw [hRe, le_div_iff₀ h1u]; linarith
  have hN8 : (N : ℝ) ^ δ = x ^ 8 := by
    rw [hx, Step2.natCast_rpow_pow]; congr 1; push_cast; ring
  have hthr : Step2.thr (E N) s δ N u = x ^ 8 * R ^ 4 := by rw [Step2.thr, hN8]
  set c65 := 65 * (N : ℝ) ^ (3 * ζ) with hc65
  have hc65_1 : 1 ≤ c65 := by
    have : 1 ≤ (N : ℝ) ^ (3 * ζ) := Real.one_le_rpow hN1' (by positivity)
    rw [hc65]; linarith
  have hc65_0 : 0 < c65 := by linarith
  set q := qGrid B s ζ N u with hq
  have hq0 : 0 ≤ q := qGrid_nonneg B ζ u hs1 hu1
  have hqle : q ≤ c65 * R ^ ((3 : ℝ) / 2) := by
    have := qGrid_le B (hE2 N) hN1 hζ hsu hu1
    rw [hq, hc65]; linarith
  set q' := q / c65 with hq'
  have hq'0 : 0 ≤ q' := div_nonneg hq0 hc65_0.le
  have hq'le : q' ≤ R ^ ((3 : ℝ) / 2) := by
    rw [hq', div_le_iff₀ hc65_0]; linarith
  set A := B.scale (E N) N u with hA
  have hApos : 0 < A := B.scale_pos' (hE2 N) N hu0 hu1
  set α := A⁻¹ ^ ((3 : ℝ) / 7) with hα
  have hα0 : 0 ≤ α := Real.rpow_nonneg (inv_nonneg.2 hApos.le) _
  set ε := (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D) with hε
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hε0 : 0 ≤ ε := by have := Real.rpow_nonneg hW0.le (-D); positivity
  set Ξ := Step2.xiK (B.L N) (B.W N) m with hΞdef
  have hΞ0 : 0 ≤ Ξ := Step2.xiK_nonneg _ _ _
  have key := phi_arith' (x := x) (R := R) (Ξ := Ξ) (m := m) (A := A) (ε := ε) (q := q')
    (α := α) hx1 hR1 hΞ hm0 hvA hε0 hvε hq'0 hq'le hα0 hvα
  have hx0 : 0 ≤ x := by linarith
  have hR2 : 0 ≤ R ^ 2 := by positivity
  set Λ := x ^ 8 * R ^ 4 with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  -- `Mg (q + αΛ³) ≤ x (q' + αΛ³)`
  have hMgq : Mg * (q + α * Λ ^ 3) ≤ x * (q' + α * Λ ^ 3) := by
    have e1 : Mg * q = (c65 * Mg) * q' := by
      rw [hq']; field_simp
    have h1 : (c65 * Mg) * q' ≤ x * q' := mul_le_mul_of_nonneg_right hMgx hq'0
    have h2 : Mg * (α * Λ ^ 3) ≤ x * (α * Λ ^ 3) := by
      have : Mg ≤ c65 * Mg := le_mul_of_one_le_left hMg hc65_1
      exact mul_le_mul_of_nonneg_right (this.trans hMgx) (by positivity)
    rw [mul_add, mul_add, e1]
    linarith
  have hphi : phiG' B (E N) s δ D ζ Mi Mg Mm N u + 1 ≤
      x * R ^ 2 * Ξ + Ξ * (exp 1 * Λ ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
        + x * m⁻¹ * R ^ 2 * (q' + α * Λ ^ 3)) + x * (R ^ 2 + 1) + 1 + 2 := by
    have hphiG : phiG' B (E N) s δ D ζ Mi Mg Mm N u = Mi * R ^ 2 * Ξ
        + Ξ * (exp 1 * Λ ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
          + Mg * m⁻¹ * R ^ 2 * (q + α * Λ ^ 3)) + Mm * (R ^ 2 + 1) + 1 + 1 := by
      unfold phiG'
      rw [hthr]
    rw [hphiG]
    have t1 : Mi * R ^ 2 * Ξ ≤ x * R ^ 2 * Ξ := by gcongr
    have t2 : Ξ * (Mg * m⁻¹ * R ^ 2 * (q + α * Λ ^ 3)) ≤
        Ξ * (x * m⁻¹ * R ^ 2 * (q' + α * Λ ^ 3)) := by
      have hmR : 0 ≤ m⁻¹ * R ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hMgq hmR
      have e1 : Mg * m⁻¹ * R ^ 2 * (q + α * Λ ^ 3) = m⁻¹ * R ^ 2 * (Mg * (q + α * Λ ^ 3)) := by
        ring
      have e2 : x * m⁻¹ * R ^ 2 * (q' + α * Λ ^ 3) = m⁻¹ * R ^ 2 * (x * (q' + α * Λ ^ 3)) := by
        ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left this hΞ0
    have t3 : Mm * (R ^ 2 + 1) ≤ x * (R ^ 2 + 1) := by gcongr
    rw [mul_add Ξ, mul_add Ξ]
    linarith [t1, t2, t3]
  have hbound : phiG' B (E N) s δ D ζ Mi Mg Mm N u + 1 ≤ Step2.cStep m * x ^ 2 * R ^ 4 + 2 := by
    linarith
  refine ⟨hJ.trans hbound, ?_⟩
  -- `cStep x² R⁴ + 2 < x⁸ R⁴`
  rw [hthr]
  have hP1 : 1 ≤ x ^ 2 * R ^ 4 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx1) (one_le_pow₀ hR1)
  have e : Λ = x ^ 6 * (x ^ 2 * R ^ 4) := by rw [hΛ]; ring
  rw [e]
  have h1 : (Step2.cStep m + 2) * (x ^ 2 * R ^ 4) < x ^ 6 * (x ^ 2 * R ^ 4) :=
    mul_lt_mul_of_pos_right hCx (by linarith)
  have h2 : (Step2.cStep m + 2) * (x ^ 2 * R ^ 4) = Step2.cStep m * x ^ 2 * R ^ 4
      + 2 * (x ^ 2 * R ^ 4) := by ring
  linarith

/-- **The plain pair at every time**: `(η_s/η_u)^30 ≤ W ℓ_u η_u` eventually, for
`u N ∈ [s N, t N]`. -/
theorem plain_endpointN (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, t N < 1)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N))
    (u : ∀ N, TimeIcc s t N) :
    ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (u N : ℝ)) ^ 30 ≤ B.scale (E N) N (u N : ℝ) := by
  filter_upwards [hreg0] with N hN
  have hsu : s N ≤ (u N : ℝ) := (u N).2.1
  have hut : (u N : ℝ) ≤ t N := (u N).2.2
  have hu1 : (u N : ℝ) < 1 := hut.trans_lt (ht1 N)
  have ha : 0 < 1 - (u N : ℝ) := by linarith
  have ht0 : 0 < 1 - t N := by linarith [ht1 N]
  have hc0 : 0 < 1 - s N := by linarith
  have hRu : etaT (E N) (s N) / etaT (E N) (u N : ℝ) = (1 - s N) / (1 - (u N : ℝ)) :=
    Step2.etaT_ratio (hE N) _ _
  have hRt : etaT (E N) (s N) / etaT (E N) (t N) = (1 - s N) / (1 - t N) :=
    Step2.etaT_ratio (hE N) _ _
  have hRut : (1 - s N) / (1 - (u N : ℝ)) ≤ (1 - s N) / (1 - t N) :=
    div_le_div_of_nonneg_left hc0.le ht0 (by linarith)
  have hRu0 : 0 ≤ (1 - s N) / (1 - (u N : ℝ)) := div_nonneg hc0.le ha.le
  have hscale : B.scale (E N) N (t N) ≤ B.scale (E N) N (u N : ℝ) :=
    flowScale_antitoneOn (Nat.cast_nonneg _) _ (E N) (Set.mem_Iic.2 hu1.le)
      (Set.mem_Iic.2 (ht1 N).le) hut
  rw [hRu]
  rw [hRt] at hN
  exact (pow_le_pow_left₀ hRu0 hRut 30).trans (hN.trans hscale)

/-- **`N^c ≤ W ℓ_u η_u` eventually**, for `u N ∈ [s N, t N]`, from the same bound at `t`. There is
no bound on `E` among the hypotheses. -/
theorem scale_endpointN (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N)) (u : ∀ N, TimeIcc s t N) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (u N : ℝ) := by
  filter_upwards [hAc] with N hN
  have hut : (u N : ℝ) ≤ t N := (u N).2.2
  have hu1 : (u N : ℝ) < 1 := hut.trans_lt (ht1 N)
  exact hN.trans (flowScale_antitoneOn (Nat.cast_nonneg _) _ (E N) (Set.mem_Iic.2 hu1.le)
    (Set.mem_Iic.2 (ht1 N).le) hut)

section CompatN

end CompatN

end ImprovePlainN

end RBM.Gauss.Grid

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

section GoodEventPlainN

variable {d : Dims}

/-- **`thr(v) ≤ N^{1/2}` eventually**, for all `v ∈ [s, t]`, when `δ ≤ c/90`. -/
theorem thr_le_sqrtN_plainN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδc : δ ≤ c / 90) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, s N ≤ v → v ≤ t N →
      Step2.thr (E N) s δ N v ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
  filter_upwards [hreg0, hAc, d.dim, eventually_ge_atTop 1] with N hN hNc hdim hN1 v hsv hvt
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hm0 := mE_im_pos (hE N)
  have hm1 := mE_im_le_one (E := E N) (hE N)
  have ht1' := ht1 N
  have hs1 : s N < 1 := (hst N).trans_lt ht1'
  have hηs := Step2.etaT_pos' (hE N) hs1
  have hηt := Step2.etaT_pos' (hE N) ht1'
  have hηv := Step2.etaT_pos' (hE N) (hvt.trans_lt ht1')
  have hηtv : etaT (E N) (t N) ≤ etaT (E N) v := by
    simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  set Rt := etaT (E N) (s N) / etaT (E N) (t N) with hRt
  set Rv := etaT (E N) (s N) / etaT (E N) v with hRv
  have hRv0 : 0 ≤ Rv := by positivity
  have hRvt : Rv ≤ Rt := div_le_div_of_nonneg_left hηs.le hηt hηtv
  have hscale : (band d).scale (E N) N (t N) ≤ N := by
    have hℓ : (band d).ell N (t N) ≤ (d.L N : ℝ) := by
      simp only [Band.ell, ellHat]; exact min_le_right _ _
    have hℓ0 : 0 ≤ (band d).ell N (t N) :=
      (Step3.ellHat_pos_of_lt_one ((band d).one_le_L N) ht1').le
    have hη1 : etaT (E N) (t N) ≤ 1 := by
      simp only [Step2.etaT_eq]
      have := hs0 N; have := hst N
      calc (1 - t N) * (mE (E N)).im ≤ 1 * 1 := mul_le_mul (by linarith) hm1 hm0.le zero_le_one
        _ = 1 := one_mul 1
    have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
    have hW0 : (0 : ℝ) ≤ (d.W N : ℝ) := Nat.cast_nonneg _
    calc (band d).scale (E N) N (t N) = (d.W N : ℝ) * (band d).ell N (t N) * etaT (E N) (t N) :=
          rfl
      _ ≤ (d.W N : ℝ) * (d.L N : ℝ) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hℓ hW0) hη1 hηt.le
          exact mul_nonneg hW0 (Nat.cast_nonneg _)
      _ ≤ N := by linarith
  set A := (band d).scale (E N) N (t N) with hA
  have hA1 : 1 ≤ A := (Real.one_le_rpow hN1' hc0.le).trans hNc
  set x := (N : ℝ) ^ δ with hx
  have hx90 : x ^ 90 ≤ A ^ 1 :=
    Step2.natCast_rpow_pow_le_of_le hN1' (by push_cast; linarith) hNc
  rw [pow_one] at hx90
  unfold Step2.thr
  rw [← hx, ← hRv]
  have hX0 : 0 ≤ x * Rv ^ 4 := by positivity
  have hsq : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (90 : ℕ) = (N : ℝ) ^ (45 : ℕ) := by
    rw [Step2.natCast_rpow_pow, ← Real.rpow_natCast]; norm_num
  have hRv30 : Rv ^ 30 ≤ A := (pow_le_pow_left₀ hRv0 hRvt 30).trans hN
  have key : (x * Rv ^ 4) ^ (90 : ℕ) ≤ ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (90 : ℕ) := by
    rw [hsq]
    calc (x * Rv ^ 4) ^ (90 : ℕ) = x ^ 90 * (Rv ^ 30) ^ 12 := by ring
      _ ≤ A * A ^ 12 := mul_le_mul hx90 (pow_le_pow_left₀ (by positivity) hRv30 12)
          (by positivity) (by linarith)
      _ = A ^ 13 := by ring
      _ ≤ (N : ℝ) ^ 13 := pow_le_pow_left₀ (by linarith) hscale 13
      _ ≤ (N : ℝ) ^ 45 := pow_le_pow_right₀ hN1' (by norm_num)
  exact (pow_le_pow_iff_left₀ hX0 (Real.rpow_nonneg hN0.le _) (by norm_num)).1 key

-- local copies of the private helpers (used by `highProb_init_grid_plainN`)
private theorem ofFn_pm_eq_pmLoop_pl {L : ℕ} (b : LoopArg L 2) :
    (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod L)) = pmLoop (b 0) (b 1) := by
  simp [pmLoop, List.ofFn_succ]

private theorem Lval_band_eq_pl (E : ℝ) (N : ℕ) (v : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (b : LoopArg (d.L N) 2) :
    Lval (band d) E N v M b = gloop (d.L N) (d.W N) M (zt E v) (pmLoop (b 0) (b 1)) := by
  change gloop (d.L N) (d.W N) M (zt E v) ⟨[true, false], List.ofFn b⟩ = _
  rw [ofFn_pm_eq_pmLoop_pl]

private theorem Kv_band_eq_pl (E : ℝ) (N : ℕ) (v : ℝ) (b : LoopArg (d.L N) 2) :
    Kv (band d) E N v b = (band d).Kval E N v (pmLoop (b 0) (b 1)) := by
  unfold Kv pmLoop
  congr 2

/-- **The initial bound on the grid**: with high probability `|Agrid_0| ≤ N^{δ/16} T_{u_0,D}` and
`jSMat(u_0) < thr(u_0)`, from (2.68)–(2.70) at `s` (`hB : BoundsCoreN (sample d) E s`,
`Flow/EnergyUniform.lean`). -/
theorem highProb_init_grid_plainN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t u : ℕ → ℝ}
    (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hD : 0 < D) (hsu : ∀ N, s N ≤ u N) (K : ℕ → ℕ)
    (hK0 : ∀ N, K N ≠ 0) :
    HighProb (Pg d) (fun N => {ω |
      (∀ b : LoopArg (d.L N) 2, ‖Agrid (band d) (E N) s u K N 0 ω b‖ ≤
        (N : ℝ) ^ (δ / 16) * Step2.tT (band d) (E N) N D (time s u K N 0)
          (zdist (d.L N) (b 0 - b 1)))
      ∧ jSMat d (E N) D N (time s u K N 0) (H d s u K N 0 ω)
        < Step2.thr (E N) s δ N (time s u K N 0)}) := by
  have hδ16 : 0 < δ / 16 := by positivity
  have G := (hB.decay D hD).highProb hδ16
  set S : ∀ N, Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
    fun N => initSet (d := d) (E N) N (s N) D ((N : ℝ) ^ (δ / 16)) with hSdef
  have hSmeas : ∀ N, MeasurableSet (S N) := fun N => measurableSet_initSet _ _ _ _ _
  have hscale : ∀ᶠ N : ℕ in atTop, 1 ≤ (band d).scale (E N) N (s N) := by
    filter_upwards [StepGlue.eventually_R4_le_scale_of_cond272N (B := band d) hE hs0 hst ht1
      (Step2.cond272_of_plainN hE hst ht1 hreg0) hAc, eventually_ge_atTop 1] with N hN hN1
    have h1 := (hN ⟨s N, le_rfl, hst N⟩).2
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact (Real.one_le_rpow hN1' hc0.le).trans h1
  have Gflow : HighProb (P d) (fun N => {ω | Hflow d N (s N) ω ∈ S N}) := by
    refine G.mono ?_
    filter_upwards [hscale] with N hN ω hω b
    have h1 := hω (b 0, b 1)
    have e : ‖Lval (band d) (E N) N (s N) (Hflow d N (s N) ω) b
          - Kv (band d) (E N) N (s N) b‖ =
        (sample d).lkErr (E N) N (s N) ω (pmLoop (b 0) (b 1)) := by
      rw [Lval_band_eq_pl, Kv_band_eq_pl]
      rfl
    change ‖Lval (band d) (E N) N (s N) (Hflow d N (s N) ω) b
      - Kv (band d) (E N) N (s N) b‖ ≤ _
    rw [e]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Step2.decayProf_le_tT (B := band d) hN (b 0) (b 1)
  have Ggrid : HighProb (Pg d) (fun N => {ω | H d s u K N 0 ω ∈ S N}) := by
    intro D' hD'
    filter_upwards [Gflow D' hD'] with N hN
    have hHmeas : Measurable (H d s u K N 0) :=
      (H_measurable_filt d s u K N 0).mono ((filt d).le 0) le_rfl
    have hHflowmeas : Measurable (Hflow d N (s N)) := RBM.measurable_H (sample d) N (s N)
    have heq : (Pg d) {ω | H d s u K N 0 ω ∈ S N}ᶜ = (P d) {ω | Hflow d N (s N) ω ∈ S N}ᶜ := by
      change (Pg d) ((H d s u K N 0) ⁻¹' S N)ᶜ = (P d) ((Hflow d N (s N)) ⁻¹' S N)ᶜ
      rw [← Set.preimage_compl, ← Set.preimage_compl,
        ← Measure.map_apply hHmeas (hSmeas N).compl,
        ← Measure.map_apply hHflowmeas (hSmeas N).compl,
        map_H_eq s u K N 0 (hs0 N) (hsu N) (hK0 N), time_zero]
    rw [heq]; exact hN
  refine Ggrid.mono ?_
  filter_upwards [eventually_le_rpow 2 hδ16, eventually_ge_atTop 1] with N h2 hN1 ω hω
  have hω' : H d s u K N 0 ω ∈ S N := hω
  refine ⟨fun b => ?_, ?_⟩
  · have := hω' b
    change ‖Lval (band d) (E N) N (time s u K N 0) (H d s u K N 0 ω) b
      - Kv (band d) (E N) N (time s u K N 0) b‖ ≤ _
    rw [time_zero]
    exact this
  · rw [time_zero]
    have hj := jSMat_le_of_mem_initSet hω'
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have hη : etaT (E N) (s N) ≠ 0 := (Step2.etaT_pos' (hE N) hs1).ne'
    have hthr : Step2.thr (E N) s δ N (s N) = (N : ℝ) ^ δ := by
      unfold Step2.thr; rw [div_self hη]; ring
    rw [hthr]
    set y := (N : ℝ) ^ (δ / 16) with hy
    have hpow : y ^ (16 : ℕ) = (N : ℝ) ^ δ := by
      rw [hy, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]; congr 1; push_cast; ring
    have hy1 : (1 : ℝ) ≤ y := by linarith
    have h16 : y ^ (2 : ℕ) ≤ y ^ (16 : ℕ) := pow_le_pow_right₀ hy1 (by norm_num)
    rw [← hpow]
    nlinarith

/-- **Conditional sub-Gaussian bounds for the stopped martingale increments**: eventually, for
`k ≤ K N`, `j < k` and every `a`, the real and imaginary parts of
`1(j < gridTau) · (U_{u_{j+1}, u_k} Z_{j+1})_a` are conditionally sub-Gaussian with variance
proxy `cZ`. -/
theorem hsubG_gridTau_plainN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t u : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδc : δ ≤ c / 90) {D : ℝ} (hD0 : 0 ≤ D)
    (τ₁ ε ζCtr τ3 τ57 : ℝ) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N)
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0) (Cc : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2, ∀ j < k,
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω'}.indicator
          (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
            (time s u K N k : ℂ) (Zvec (band d) (E N) s u K N (j + 1) ω') a) ω).re)
        (cZ d (E N) s u K δ ε D τ₁ Cc N k a j).toNNReal (Pg d) ∧
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω'}.indicator
          (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
            (time s u K N k : ℂ) (Zvec (band d) (E N) s u K N (j + 1) ω') a) ω).im)
        (cZ d (E N) s u K δ ε D τ₁ Cc N k a j).toNNReal (Pg d) := by
  filter_upwards [thr_le_sqrtN_plainN hE hs0 hst ht1 hc0 hreg0 hAc hδ0 hδc, eventually_le_W d 3]
    with N hthr hW3 k hk a j hjk
  set S : Set (Ωg d) := {ω' | j < gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω'} with hSdef
  have hS : MeasurableSet[filt d j] S :=
    lt_gridTau_measurableSet (hE N) D δ τ₁ ε ζCtr τ3 τ57 s u K N j
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  have htK : time s u K N (K N) = u N := time_last s u K N (hK0 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  set uv := time s u K N (j + 1) with hvdef
  set uw := time s u K N k with hwdef
  set uj := time s u K N j with hujdef
  have hsuj : s N ≤ uj := by
    have := time_mono_of_le (K := K) (hsu N) (Nat.zero_le j); rwa [time_zero] at this
  have huj0 : 0 ≤ uj := (hs0 N).trans hsuj
  have hujv : uj ≤ uv := time_mono_of_le (hsu N) (Nat.le_succ j)
  have hvw : uv ≤ uw := time_mono_of_le (hsu N) hjk
  have hwu : uw ≤ u N := by rw [← htK]; exact time_mono_of_le (hsu N) hk
  have hw1 : uw < 1 := (hwu.trans (hut N)).trans_lt (ht1 N)
  have hv1 : uv < 1 := hvw.trans_lt hw1
  have hv0 : 0 ≤ uv := huj0.trans hujv
  have huj1 : uj < 1 := hujv.trans_lt hv1
  have hujt : uj ≤ t N := (hujv.trans hvw).trans (hwu.trans (hut N))
  have hΦ : ∀ a', TestFun d N (Φgrid (band d) (E N) N uv a') := fun a' =>
    Φgrid_testFun (band d) (hE N) N hv1 a'
  have hc0 : 0 ≤ cZ d (E N) s u K δ ε D τ₁ Cc N k a j := cZ_nonneg (hsu N) k a j
  have hcnn : (cZ d (E N) s u K δ ε D τ₁ Cc N k a j).toNNReal
      = ⟨cZ d (E N) s u K δ ε D τ₁ Cc N k a j, hc0⟩ := Real.toNNReal_of_nonneg hc0
  have hkey : ∀ ω', Uker (d.L N) (fun _ => (1 : ℂ)) (uv : ℂ) (uw : ℂ)
      (Zvec (band d) (E N) s u K N (j + 1) ω') a
        = (stepZ d s u K N j (Φgrid (band d) (E N) N uv) (ukerMat (d.L N) uv uw) a ω' : ℂ) :=
    fun ω' => (stepZ_ukerMat_eq_Uker d s u K N j (Φgrid (band d) (E N) N uv) hv0 hvw hw1 a ω').symm
  constructor
  · -- the real part
    have hfun : (fun ω => (S.indicator (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (uv : ℂ)
        (uw : ℂ) (Zvec (band d) (E N) s u K N (j + 1) ω') a) ω).re)
        = fun ω => S.indicator
            (fun ω => stepZ d s u K N j (Φgrid (band d) (E N) N uv)
              (ukerMat (d.L N) uv uw) a ω) ω := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        have h := congrArg Complex.re (hkey ω)
        rw [Complex.ofReal_re] at h
        exact h
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Complex.zero_re]
    rw [hfun, hcnn]
    refine stepDecomp_Z_subG d s u K N j hΦ _ a S hS _ hc0 ?_
    intro ω hω
    have hU : ukerMat (d.L N) uv uw
        = fun b' a' => (∏ i : Fin 2, edgeKer (d.L N) 1 (uv : ℂ) (uw : ℂ) (b' i) (a' i)).re :=
      funext fun b' => funext fun a' => ukerMat_eq_prod_re (d.L N) uv uw b' a'
    rw [hU]
    obtain ⟨hjS, hG⟩ := lt_gridTau_imp hω
    obtain ⟨⟨⟨⟨⟨hqvS, hjg⟩, -⟩, -⟩, -⟩, -⟩ := hG
    have hM : (H d s u K N j ω).IsHermitian := H_isHermitian d s u K N j ω
    have hjS' : jSMat d (E N) D N uj (H d s u K N j ω) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
      hjS.le.trans (hthr uj hsuj hujt)
    have hqv0 := hqvS huj1 hjS'
    have hℓs : 0 < (band d).ell N (s N) := Step3.ellHat_pos_of_lt_one ((band d).one_le_L N) hs1
    have hℓuj : 0 < (band d).ell N uj := Step3.ellHat_pos_of_lt_one ((band d).one_le_L N) huj1
    have hJ'0 : 0 ≤ jGMat d (E N) N uj ((band d).ell N uj) (etaT (E N) uj) D (H d s u K N j ω) :=
      jGMat_nonneg (E N) N uj hℓuj hW3 _
    have hJ'J : jGMat d (E N) N uj ((band d).ell N uj) (etaT (E N) uj) D (H d s u K N j ω)
        ≤ qvJ (E N) s δ ε N uj := by
      refine hjg.trans ?_
      unfold qvJ
      exact mul_le_mul_of_nonneg_left hjS.le (by positivity)
    have hqv' : ∀ a' : LoopArg (d.L N) 2,
        Gauss.quadVar d N
            (fun M' => MomentDuhamel.lkFun (Gauss.band d) (E N) N uj M' Step2.sigPM a')
            (H d s u K N j ω)
          ≤ (N : ℝ) ^ τ₁ * QVEndpoint.diagShape' (Gauss.band d) N
              ((Gauss.band d).ell N uj) ((band d).ell N (s N)) (etaT (E N) uj) D
              (jGMat d (E N) N uj ((band d).ell N uj) (etaT (E N) uj) D (H d s u K N j ω))
              (EarlyQVRateEv.sDet (Gauss.band d) (E N) N uj ((band d).ell N (s N)))
              (EEDef.nearEpsilon ((Gauss.band d).W N : ℝ) ((Gauss.band d).L N : ℝ)
                ((Gauss.band d).ell N uj) (etaT (E N) uj) D
                (jGMat d (E N) N uj ((band d).ell N uj) (etaT (E N) uj) D
                  (H d s u K N j ω))) a' := by
      intro a'
      have h1 := hqv0 a'
      unfold qvVal at h1
      rw [dite_eq_left_of_eq_true (eq_true hM)] at h1
      exact h1
    have hu'1 : uj + step s u K N < 1 := by rw [hujdef, ← time_succ_eq]; exact hv1
    have hstep := quadVar_step_le d N (hE N) huj0 hΔ0 hu'1 hD0 hℓs hJ'0 hJ'J hM hqv'
    have hm0 := mE_im_pos (hE N)
    have hm1 := mE_im_le_one (E := E N) (hE N)
    have hQ : 0 ≤ Qprime d (E N) s u K δ ε D τ₁ N j := by
      unfold Qprime
      have := QVSum.Qd_nonneg (band d) (hE N) (s := s) (δ := δ) (ε := ε) (D := D) (N := N)
        hs1 huj0 huj1
      have : 0 ≤ qvTimeShiftConst d N (E N) (time s u K N (j + 1)) :=
        qvTimeShiftConst_nonneg _ _ _ _
      have : 0 ≤ ((band d).W N : ℝ) ^ (2 * D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    have hqvΦ : ∀ a' : LoopArg (d.L N) 2,
        Gauss.quadVar d N (Φgrid (band d) (E N) N uv a') (H d s u K N j ω)
          ≤ Qprime d (E N) s u K δ ε D τ₁ N j *
            (tailT (d.W N : ℝ) (ellHat (d.L N) (uv : ℂ)) ((1 - uv) * (mE (E N)).im) D
              (zdist (d.L N) (a' 0 - a' 1))) ^ 2 := by
      intro a'
      rw [quadVar_Φgrid_eq (hE N) N hv1 a' hM]
      have h1 := hstep a'
      rw [hujdef, ← time_succ_eq] at h1
      exact h1
    have hWe : Real.exp 1 ≤ (d.W N : ℝ) := by
      have h1 : (3 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast hW3
      have h2 : Real.exp 1 ≤ (3 : ℝ) := by
        have := Real.exp_one_lt_d9
        nlinarith
      linarith
    have hAuv : (d.W N : ℝ) * ellHat (d.L N) (uw : ℂ) * ((1 - uw) * (mE (E N)).im)
        ≤ (d.W N : ℝ) * ellHat (d.L N) (uv : ℂ) * ((1 - uv) * (mE (E N)).im) :=
      flowScale_antitoneOn (Nat.cast_nonneg _) (d.L N) (E N) (Set.mem_Iic.2 hv1.le)
        (Set.mem_Iic.2 hw1.le) hvw
    have hvAb := v_Ab_le_H (Φ := Φgrid (band d) (E N) N uv) hΦ
      (fun a' A hA => Φgrid_im_eq_zero (band d) (hE N).le N hv0 hv1 a' hA) (d.three_le_L N) hm0 hm1
      hv0 hvw (hv0.trans hvw) hw1 hWe hQ hAuv a ω hqvΦ
    have hfl : 0 ≤ step s u K N * (N : ℝ) ^ (-Cc) :=
      mul_nonneg hΔ0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc step s u K N * v N (Ab d s u K N j (Φgrid (band d) (E N) N uv)
          (fun b' a' => (∏ i : Fin 2, edgeKer (d.L N) 1 (uv : ℂ) (uw : ℂ) (b' i) (a' i)).re) a ω)
        ≤ step s u K N * (Real.sqrt (Qprime d (E N) s u K δ ε D τ₁ N j)
            * ((1 - uv) / (1 - uw)) ^ 2 * Step2.xiK (d.L N) (d.W N) (mE (E N)).im
            * Step2.tT (band d) (E N) N D uw (zdist (d.L N) (a 0 - a 1))) ^ 2 :=
          mul_le_mul_of_nonneg_left hvAb hΔ0
      _ ≤ cZ d (E N) s u K δ ε D τ₁ Cc N k a j := by
          unfold cZ
          linarith
  · -- the imaginary part: identically zero
    have hz0 : ∀ ω, stepZ d s u K N j (Φgrid (band d) (E N) N uv) (fun _ _ => (0 : ℝ)) a ω = 0 := by
      intro ω; simp [stepZ, Ab, lin]
    have hfun : (fun ω => (S.indicator (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (uv : ℂ)
        (uw : ℂ) (Zvec (band d) (E N) s u K N (j + 1) ω') a) ω).im)
        = fun ω => S.indicator
            (fun ω => stepZ d s u K N j (Φgrid (band d) (E N) N uv)
              (fun _ _ => (0 : ℝ)) a ω) ω := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hz0]
        have h := congrArg Complex.im (hkey ω)
        rw [Complex.ofReal_im] at h
        exact h
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Complex.zero_im]
    rw [hfun, hcnn]
    refine stepDecomp_Z_subG d s u K N j hΦ _ a S hS _ hc0 ?_
    intro ω _
    have hAb : Ab d s u K N j (Φgrid (band d) (E N) N uv) (fun _ _ => (0 : ℝ)) a ω = 0 := by
      simp [Ab]
    have hv0' : RBM.Gauss.Grid.v N (0 : Matrix (d.Idx N) (d.Idx N) ℂ) = 0 := by
      simp [Gauss.Grid.v, linVar, lin]
    rw [hAb, hv0', mul_zero]
    exact hc0


/-- **The stopped martingale is below `xZ` with high probability**, at all grid times `k ≤ K N` and
pairs `a` (Azuma). -/
theorem highProb_azuma_grid_plainN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t u : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {δ : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 90) {D : ℝ} (hD0 : 0 ≤ D)
    (τ₁ ε ζCtr τ3 τ57 : ℝ) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N)
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0) {C : ℝ}
    (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) (Cc Cx : ℝ) :
    HighProb (Pg d) (fun N => {ω | ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (min k (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω)),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (Zvec (band d) (E N) s u K N (j + 1) ω)) a‖
        < xZ d (E N) s u K δ ε D τ₁ Cc Cx N k a}) := by
  intro D' hD'
  have hδ8 : 0 < δ / 8 := by positivity
  filter_upwards [hsubG_gridTau_plainN hE hs0 hst ht1 hc0 hreg0 hAc hδ0.le hδc hD0 τ₁ ε ζCtr τ3 τ57
      hsu hut K hK0 Cc, hKcard, eventually_mul_exp_neg_rpow_le 4 (C + 2) hδ8 D', d.dim,
      eventually_ge_atTop 1] with N hsub hKN hsmall hdim hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set τN : Ωg d → ℕ := fun ω => gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω with hτN
  set Ev : Set (Ωg d) := {ω | ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (min k (τN ω)),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (Zvec (band d) (E N) s u K N (j + 1) ω)) a‖
        < xZ d (E N) s u K δ ε D τ₁ Cc Cx N k a} with hEv
  change (Pg d) Evᶜ ≤ _
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  rcases hΔ0.eq_or_lt with hΔ | hΔ
  · -- `Δ = 0`: every sum vanishes, the event is everything
    have hall : Evᶜ = ∅ := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not, hEv,
        Set.mem_ofPred_eq]
      intro k _ a
      have h0 : ∀ j, Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
          (time s u K N k : ℂ) (Zvec (band d) (E N) s u K N (j + 1) ω) a = 0 := fun j =>
        Uker_apply_eq_zero_of _ _ _ (fun b => Zvec_succ_eq_zero_of_step (E := E N) hΔ.symm j ω b) a
      rw [Finset.sum_apply]
      simp only [h0, Finset.sum_const_zero, norm_zero]
      exact xZ_pos hN1 (hsu N) k a
    rw [hall, measure_empty]; exact zero_le
  · -- `Δ > 0`
    have hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τN ω} := fun j =>
      lt_gridTau_measurableSet (hE N) D δ τ₁ ε ζCtr τ3 τ57 s u K N j
    have hZ : ∀ i, StronglyMeasurable[filt d i] (ZvecCut (d := d) (E N) s u K N i) := fun i =>
      stronglyMeasurable_ZvecCut (hE N) hsu hut ht1 hK0 N i
    have hsub' : ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2, ∀ j < k,
        HasCondSubgaussianMGF (filt d j) ((filt d).le j)
          (fun ω => ({ω' | j < τN ω'}.indicator
            (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
              (time s u K N k : ℂ) (ZvecCut (d := d) (E N) s u K N (j + 1) ω') a) ω).re)
          (cZ d (E N) s u K δ ε D τ₁ Cc N k a j).toNNReal (Pg d) ∧
        HasCondSubgaussianMGF (filt d j) ((filt d).le j)
          (fun ω => ({ω' | j < τN ω'}.indicator
            (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
              (time s u K N k : ℂ) (ZvecCut (d := d) (E N) s u K N (j + 1) ω') a) ω).im)
          (cZ d (E N) s u K δ ε D τ₁ Cc N k a j).toNNReal (Pg d) := by
      intro k hk a j hj
      rw [ZvecCut_succ (by omega)]
      exact hsub k hk a j hj
    have hx : ∀ k ≤ K N, ∀ a, 0 ≤ xZ d (E N) s u K δ ε D τ₁ Cc Cx N k a :=
      fun k _ a => (xZ_pos hN1 (hsu N) k a).le
    have hx0 : ∀ a, 0 < xZ d (E N) s u K δ ε D τ₁ Cc Cx N 0 a := fun a => xZ_pos hN1 (hsu N) 0 a
    have hU := stopped_duhamel_azuma_union (μ := Pg d) (d.L N) (ξ := fun _ => (1 : ℂ))
      (u := time s u K N) hτmeas hZ (K N) hsub' hx hx0
    set Sbad : Set (Ωg d) := {ω | ∃ k ≤ K N, ∃ a, xZ d (E N) s u K δ ε D τ₁ Cc Cx N k a ≤
        ‖(∑ j ∈ Finset.range (min k (τN ω)), Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (ZvecCut (d := d) (E N) s u K N (j + 1) ω)) a‖} with hSbad
    have hsubset : Evᶜ ⊆ Sbad := by
      intro ω hω
      simp only [hEv, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_lt] at hω
      obtain ⟨k, hk, a, ha⟩ := hω
      refine ⟨k, hk, a, ?_⟩
      have hsum : (∑ j ∈ Finset.range (min k (τN ω)), Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (ZvecCut (d := d) (E N) s u K N (j + 1) ω))
          = ∑ j ∈ Finset.range (min k (τN ω)), Uker (d.L N) (fun _ => (1 : ℂ))
            (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
              (Zvec (band d) (E N) s u K N (j + 1) ω) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j < min k (τN ω) := Finset.mem_range.1 hj
        rw [ZvecCut_succ (by omega)]
      rw [hsum]; exact ha
    -- the per-summand bound
    have hterm : ∀ k ∈ Finset.Icc 1 (K N), ∀ a : LoopArg (d.L N) 2,
        4 * Real.exp (-(xZ d (E N) s u K δ ε D τ₁ Cc Cx N k a) ^ 2 /
          (4 * ∑ j ∈ Finset.range k, ((cZ d (E N) s u K δ ε D τ₁ Cc N k a j).toNNReal : ℝ)))
          ≤ 4 * Real.exp (-(N : ℝ) ^ (δ / 8)) := by
      intro k hk a
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
      have hcoe : ∑ j ∈ Finset.range k, ((cZ d (E N) s u K δ ε D τ₁ Cc N k a j).toNNReal : ℝ)
          = ∑ j ∈ Finset.range k, cZ d (E N) s u K δ ε D τ₁ Cc N k a j :=
        Finset.sum_congr rfl fun j _ => Real.coe_toNNReal _ (cZ_nonneg (hsu N) k a j)
      rw [hcoe]
      set Sk := ∑ j ∈ Finset.range k, cZ d (E N) s u K δ ε D τ₁ Cc N k a j with hSk
      have hSk0 : 0 < Sk := by
        have h1 : step s u K N * (N : ℝ) ^ (-Cc) ≤ Sk := by
          have := Finset.single_le_sum (f := fun j => cZ d (E N) s u K δ ε D τ₁ Cc N k a j)
            (fun j _ => cZ_nonneg (hsu N) k a j) (Finset.mem_range.2 hk1)
          exact (floor_le_cZ (hsu N) k a 0).trans this
        exact lt_of_lt_of_le (mul_pos hΔ (Real.rpow_pos_of_pos hN0 _)) h1
      have hsq := xZ_sq (E := E N) (K := K) (δ := δ) (ε := ε) (D := D) (τ₁ := τ₁) (Cc := Cc)
        (Cx := Cx) (hsu N) k a
      rw [← hSk] at hsq
      have hle : (N : ℝ) ^ (δ / 8) * (4 * Sk) ≤ xZ d (E N) s u K δ ε D τ₁ Cc Cx N k a ^ 2 := by
        rw [hsq]
        have := Real.rpow_nonneg hN0.le (-Cx)
        have := Real.rpow_nonneg hN0.le (δ / 8)
        nlinarith
      have h4S : 0 < 4 * Sk := by linarith
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ h4S]
      exact hle
    have hLN : (d.L N : ℝ) ≤ N := by
      have hW : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
      have h := hdim.1
      have h' : (d.W N : ℝ) * d.L N ≤ N := by exact_mod_cast h
      nlinarith [(Nat.cast_nonneg (d.L N) : (0 : ℝ) ≤ d.L N)]
    have hsum_le : ∑ k ∈ Finset.Icc 1 (K N), ∑ a : LoopArg (d.L N) 2,
        4 * Real.exp (-(xZ d (E N) s u K δ ε D τ₁ Cc Cx N k a) ^ 2 /
          (4 * ∑ j ∈ Finset.range k, ((cZ d (E N) s u K δ ε D τ₁ Cc N k a j).toNNReal : ℝ)))
        ≤ (N : ℝ) ^ (-D') := by
      calc _ ≤ ∑ _k ∈ Finset.Icc 1 (K N), ∑ _a : LoopArg (d.L N) 2,
            4 * Real.exp (-(N : ℝ) ^ (δ / 8)) :=
            Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ => hterm k hk a
        _ = (K N : ℝ) * ((d.L N : ℝ) ^ 2 * (4 * Real.exp (-(N : ℝ) ^ (δ / 8)))) := by
            rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, card_loopArg_two,
              Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul]
            push_cast; ring
        _ ≤ (N : ℝ) ^ C * ((N : ℝ) ^ (2 : ℝ) * (4 * Real.exp (-(N : ℝ) ^ (δ / 8)))) := by
            have hK : (K N : ℝ) ≤ (N : ℝ) ^ C := by
              have : (K N : ℝ) ≤ ((K N + 1 : ℕ) : ℝ) := by push_cast; linarith
              exact this.trans hKN
            have hL2 : (d.L N : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 : ℝ) := by
              rw [Real.rpow_two]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hLN 2
            have he : 0 ≤ 4 * Real.exp (-(N : ℝ) ^ (δ / 8)) := by positivity
            have hL0 : 0 ≤ (d.L N : ℝ) ^ 2 := by positivity
            gcongr
        _ = 4 * (N : ℝ) ^ (C + 2) * Real.exp (-(N : ℝ) ^ (δ / 8)) := by
            rw [Real.rpow_add hN0]; ring
        _ ≤ (N : ℝ) ^ (-D') := hsmall
    calc (Pg d) Evᶜ ≤ (Pg d) Sbad := measure_mono hsubset
      _ = ENNReal.ofReal ((Pg d).real Sbad) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal (hU.trans hsum_le)


/-- **Chebyshev bound at the stopping index `gridTau`**: eventually, the probability that the
propagated drift sum `Σ_{j < τ} U_{u_{j+1}, u_τ} Y_{j+1}` reaches `Step2.tT` at some pair is at
most `N^{-D₁}`. -/
theorem cheb_grid_at_tau_plainN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t u : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {D : ℝ} (hD0 : 0 ≤ D) (δ τ₁ ε ζCtr τ3 τ57 : ℝ) (hsu : ∀ N, s N ≤ u N)
    (hut : ∀ N, u N ≤ t N) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (Pg d) {ω | ∃ a : LoopArg (d.L N) 2,
        Step2.tT (band d) (E N) N D
            (time s u (gridK D D₁) N (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N ω))
            (zdist (d.L N) (a 0 - a 1)) ≤
          ‖(∑ j ∈ Finset.range (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N ω),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s u (gridK D D₁) N (j + 1) : ℂ)
                (time s u (gridK D D₁) N
                  (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N ω) : ℂ)
                (Yvec (band d) (E N) s u (gridK D D₁) N (j + 1) ω)) a‖}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
  intro D₁ hD₁
  filter_upwards [etaT_inv_le_of_plainN (band d) hE ht1 hc0 hAc, d.dim, eventually_ge_atTop 2]
    with N hηt hdim hN2
  set K : ℕ → ℕ := gridK D D₁ with hKdef
  have hK0 : ∀ N, K N ≠ 0 := gridK_ne_zero D D₁
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hm0 := mE_im_pos (hE N)
  have hm1 := mE_im_le_one (E := E N) (hE N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have huN1 : u N < 1 := (hut N).trans_lt (ht1 N)
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  have hus : u N - s N ≤ 1 := by linarith [hs0 N]
  have hΔCK : step s u K N ≤ (N : ℝ) ^ (-CK D D₁) := step_gridK_le (by omega) hus
  have hKΔ : (K N : ℝ) * step s u K N ≤ 1 := by
    have hKne : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hK0 N)
    have : (K N : ℝ) * step s u K N = u N - s N := by unfold step; field_simp
    rw [this]; exact hus
  set τN : Ωg d → ℕ := fun ω => gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω with hτN
  have hτK : ∀ ω, τN ω ≤ K N := fun ω => gridTau_le (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω
  have hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τN ω} := fun j =>
    lt_gridTau_measurableSet (hE N) D δ τ₁ ε ζCtr τ3 τ57 s u K N j
  have hY : ∀ i, StronglyMeasurable[filt d i] (YvecCut (d := d) (E N) s u K N i) := fun i =>
    stronglyMeasurable_YvecCut (hE N) hsu hut ht1 hK0 N i
  have hu0 : 0 ≤ time s u K N 0 := by rw [time_zero]; exact hs0 N
  have hu_succ : ∀ j, time s u K N j ≤ time s u K N (j + 1) := fun j =>
    time_mono_of_le (hsu N) (Nat.le_succ j)
  have hutK : time s u K N (K N) = u N := time_last s u K N (hK0 N)
  have hηt0 : 0 < etaT (E N) (t N) := Step2.etaT_pos' (hE N) (ht1 N)
  have hcard := card_idx_le hdim.1
  set eb : ℝ := 2 ^ 22 * (N : ℝ) ^ 19 * step s u K N ^ 2 with heb
  -- per-step inputs
  have hstep : ∀ b : LoopArg (d.L N) 2, ∀ j < K N,
      let S : Set (Ωg d) := {ω | j < τN ω}
      let Φ := Φgrid (band d) (E N) N (time s u K N (j + 1))
      let U := ukerMat (d.L N) (time s u K N (j + 1)) (u N)
      (fun ω => S.indicator (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (u N : ℂ) (YvecCut (d := d) (E N) s u K N (j + 1) ω') b) ω)
        =ᵐ[Pg d] S.indicator (stepY d s u K N j Φ U b) ∧
      (∀ a A, A.IsHermitian → (Φ a A).im = 0) ∧ (∀ a, TestFun d N (Φ a)) ∧
      (∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ (Fintype.card (d.Idx N) : ℝ) *
          ((2 : ℝ) ^ 2 * (2 * (1 + (etaT (E N) (t N))⁻¹) ^ 3) ^ 2)) ∧
      ∑ a : LoopArg (d.L N) 2, |U b a| ≤ (N : ℝ) ^ 2 := by
    intro b j hj S Φ U
    have hv0 : 0 ≤ time s u K N (j + 1) := hu0.trans
      (by have := time_mono_of_le (K := K) (hsu N) (Nat.zero_le (j + 1)); rwa [time_zero] at this ⊢)
    have hvw : time s u K N (j + 1) ≤ u N := by
      rw [← hutK]; exact time_mono_of_le (hsu N) hj
    have hv1 : time s u K N (j + 1) < 1 := hvw.trans_lt huN1
    have hΦ : ∀ a, TestFun d N (Φ a) := fun a => Φgrid_testFun (band d) (hE N) N hv1 a
    have hae := stepY_ukerMat_eq_Uker_ae d s u K N j hΦ hv0 hvw huN1
    refine ⟨?_, fun a A hA => Φgrid_im_eq_zero (band d) (hE N).le N hv0 hv1 a hA, hΦ, ?_, ?_⟩
    · filter_upwards [hae] with ω hω
      by_cases hωS : ω ∈ S
      · rw [Set.indicator_of_mem hωS, Set.indicator_of_mem hωS, YvecCut_succ hj, hω b]
        rfl
      · rw [Set.indicator_of_notMem hωS, Set.indicator_of_notMem hωS]
    · intro a A
      have hzη : etaT (E N) (t N) ≤ |(zt (E N) (time s u K N (j + 1))).im| := by
        rw [zt_im]
        refine le_trans ?_ (le_abs_self _)
        simp only [Step2.etaT_eq]
        exact mul_le_mul_of_nonneg_right (by linarith [hut N]) hm0.le
      exact Φgrid_bdd2 (band d) (hE N) N hv1 hηt0 hzη a A
    · refine (sum_abs_ukerMat_le (d.L N) (d.three_le_L N) hv0 hvw huN1 b).trans ?_
      have h1 : (1 - time s u K N (j + 1)) / (1 - u N) ≤ N := by
        have h1u : 0 < 1 - u N := by linarith
        have h1t : 0 < 1 - t N := by linarith [ht1 N]
        calc (1 - time s u K N (j + 1)) / (1 - u N) ≤ 1 / (1 - t N) := by
              rw [div_le_div_iff₀ h1u h1t]; nlinarith [hut N]
          _ ≤ (etaT (E N) (t N))⁻¹ := by
              rw [Step2.etaT_eq, one_div, mul_inv]
              have : 1 ≤ ((mE (E N)).im)⁻¹ := (one_le_inv₀ hm0).2 hm1
              have h0 : 0 < (1 - t N)⁻¹ := inv_pos.2 h1t
              nlinarith
          _ ≤ N := hηt
      have h0 : 0 ≤ (1 - time s u K N (j + 1)) / (1 - u N) :=
        div_nonneg (by linarith) (by linarith)
      exact pow_le_pow_left₀ h0 h1 2
  have hηi0 : 0 ≤ (etaT (E N) (t N))⁻¹ := inv_nonneg.2 hηt0.le
  have hM4 : ∀ j, ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) ≤ 3 * (Fintype.card (d.Idx N) : ℝ) :=
    fun j => integral_norm_Xmat_incr_four_le N j
  have hM40 : ∀ j, 0 ≤ ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) :=
    fun j => integral_nonneg fun _ => by positivity
  have hcheb := stopped_duhamel_cheb_tail (μ := Pg d) (d.L N) (d.three_le_L N)
    (ξ := fun _ => (1 : ℂ)) (fun _ => by simp) (u := time s u K N) (t := u N) hu0 hu_succ hutK
    huN1 hτK hτmeas hY (e := fun _ => eb)
    (fun b j hj => by
      obtain ⟨hf, hR, hΦ, hC₂, _⟩ := hstep b j hj
      have hS := hτmeas j
      refine (condExp_congr_ae (hf.fun_comp Complex.re)).trans ?_
      exact condExp_indicator_stepY_re s u K N j hΦ hR hC₂ hΔ0 _ b hS)
    (fun b j hj => by
      obtain ⟨hf, hR, hΦ, hC₂, _⟩ := hstep b j hj
      have hS := hτmeas j
      refine (condExp_congr_ae (hf.fun_comp Complex.im)).trans ?_
      exact condExp_indicator_stepY_im s u K N j hΦ hR hC₂ hΔ0 _ b hS)
    (fun b j hj => by
      obtain ⟨hf, hR, hΦ, hC₂, _⟩ := hstep b j hj
      have hm := ((memLp_stepY' s u K N j hΦ hR hC₂ hΔ0
        (ukerMat (d.L N) (time s u K N (j + 1)) (u N)) b).indicator
        ((filt d).le j _ (hτmeas j))).re
      exact hm.ae_eq (hf.fun_comp Complex.re).symm)
    (fun b j hj => by
      obtain ⟨hf, hR, hΦ, hC₂, _⟩ := hstep b j hj
      have hm := ((memLp_stepY' s u K N j hΦ hR hC₂ hΔ0
        (ukerMat (d.L N) (time s u K N (j + 1)) (u N)) b).indicator
        ((filt d).le j _ (hτmeas j))).im
      exact hm.ae_eq (hf.fun_comp Complex.im).symm)
    (fun b j hj => by
      obtain ⟨hf, hR, hΦ, hC₂, hrow⟩ := hstep b j hj
      have hS := hτmeas j
      have e1 := integral_congr_ae (hf.fun_comp (fun z : ℂ => z.re ^ 2))
      have e2 := integral_congr_ae (hf.fun_comp (fun z : ℂ => z.im ^ 2))
      simp only [Function.comp_def] at e1 e2
      rw [e1, e2]
      have hC₂0 : 0 ≤ (Fintype.card (d.Idx N) : ℝ) *
          ((2 : ℝ) ^ 2 * (2 * (1 + (etaT (E N) (t N))⁻¹) ^ 3) ^ 2) := by positivity
      refine (integral_sq_indicator_stepY_le s u K N j hΦ hR hC₂ hΔ0 _ b hS hrow hC₂0).trans ?_
      exact cheb_e_le hN1' (by positivity) le_rfl (Nat.cast_nonneg _) hcard hηi0 hηt
        (hM40 j) (hM4 j))
    (x := ((d.W N : ℝ) ^ (-D)) / 4)
    (div_pos (Real.rpow_pos_of_pos (by exact_mod_cast d.W_pos N) _) (by norm_num))
  -- the event inclusion
  set Sbad : Set (Ωg d) := {ω | ∃ a, 2 ^ 2 * (((d.W N : ℝ) ^ (-D)) / 4) ≤
      ‖(∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
        (time s u K N (τN ω) : ℂ) (YvecCut (d := d) (E N) s u K N (j + 1) ω)) a‖} with hSbad
  have hsub : {ω | ∃ a : LoopArg (d.L N) 2,
        Step2.tT (band d) (E N) N D (time s u K N (τN ω)) (zdist (d.L N) (a 0 - a 1)) ≤
          ‖(∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ))
            (time s u K N (j + 1) : ℂ) (time s u K N (τN ω) : ℂ)
              (Yvec (band d) (E N) s u K N (j + 1) ω)) a‖} ⊆ Sbad := by
    intro ω hω
    obtain ⟨a, ha⟩ := hω
    refine ⟨a, ?_⟩
    have hsum : (∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ))
        (time s u K N (j + 1) : ℂ) (time s u K N (τN ω) : ℂ)
          (YvecCut (d := d) (E N) s u K N (j + 1) ω))
        = ∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (time s u K N (τN ω) : ℂ)
            (Yvec (band d) (E N) s u K N (j + 1) ω) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have : j < K N := lt_of_lt_of_le (Finset.mem_range.1 hj) (hτK ω)
      rw [YvecCut_succ this]
    rw [hsum]
    have hT : (d.W N : ℝ) ^ (-D) ≤
        Step2.tT (band d) (E N) N D (time s u K N (τN ω)) (zdist (d.L N) (a 0 - a 1)) :=
      rpow_neg_le_tailT _
    calc 2 ^ 2 * (((d.W N : ℝ) ^ (-D)) / 4) = (d.W N : ℝ) ^ (-D) := by ring
      _ ≤ _ := hT
      _ ≤ _ := ha
  -- the arithmetic
  have hWN : (d.W N : ℝ) ≤ N := by
    have hL : (1 : ℝ) ≤ d.L N := by exact_mod_cast (by have := d.three_le_L N; omega : 1 ≤ d.L N)
    have h' : (d.W N : ℝ) * d.L N ≤ N := by exact_mod_cast hdim.1
    have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
    nlinarith
  have hLN : (d.L N : ℝ) ≤ N := by
    have hW : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
    have h' : (d.W N : ℝ) * d.L N ≤ N := by exact_mod_cast hdim.1
    nlinarith [(Nat.cast_nonneg (d.L N) : (0 : ℝ) ≤ d.L N)]
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hx0 : 0 < ((d.W N : ℝ) ^ (-D)) / 4 := div_pos (Real.rpow_pos_of_pos hW0 _) (by norm_num)
  have hfinal : (d.L N : ℝ) ^ 2 * (∑ _j ∈ Finset.range (K N), eb) /
      (((d.W N : ℝ) ^ (-D)) / 4) ^ 2 ≤ (N : ℝ) ^ (-D₁) := by
    rw [div_le_iff₀ (pow_pos hx0 2), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- `x² ≥ N^{-2D}/16`
    have hWD : (N : ℝ) ^ (-D) ≤ (d.W N : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
    have hx2 : (N : ℝ) ^ (-(2 * D)) / 16 ≤ (((d.W N : ℝ) ^ (-D)) / 4) ^ 2 := by
      have e : (N : ℝ) ^ (-(2 * D)) = ((N : ℝ) ^ (-D)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
      rw [e, div_pow]
      have := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hWD 2
      norm_num; linarith
    -- `L² K e ≤ 2²² N²¹ Δ`
    have hKe : (K N : ℝ) * eb ≤ 2 ^ 22 * (N : ℝ) ^ 19 * step s u K N := by
      rw [heb]
      have : (K N : ℝ) * (2 ^ 22 * (N : ℝ) ^ 19 * step s u K N ^ 2)
          = 2 ^ 22 * (N : ℝ) ^ 19 * step s u K N * ((K N : ℝ) * step s u K N) := by ring
      rw [this]
      have h0 : 0 ≤ 2 ^ 22 * (N : ℝ) ^ 19 * step s u K N := by positivity
      calc _ ≤ 2 ^ 22 * (N : ℝ) ^ 19 * step s u K N * 1 := mul_le_mul_of_nonneg_left hKΔ h0
        _ = _ := mul_one _
    have hL2 : (d.L N : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hLN 2
    have hKe0 : 0 ≤ (K N : ℝ) * eb := by positivity
    have hA : (d.L N : ℝ) ^ 2 * ((K N : ℝ) * eb) ≤
        2 ^ 22 * (N : ℝ) ^ 21 * (N : ℝ) ^ (-CK D D₁) := by
      calc (d.L N : ℝ) ^ 2 * ((K N : ℝ) * eb)
          ≤ (N : ℝ) ^ 2 * (2 ^ 22 * (N : ℝ) ^ 19 * step s u K N) :=
            mul_le_mul hL2 hKe hKe0 (by positivity)
        _ = 2 ^ 22 * (N : ℝ) ^ 21 * step s u K N := by ring
        _ ≤ 2 ^ 22 * (N : ℝ) ^ 21 * (N : ℝ) ^ (-CK D D₁) :=
            mul_le_mul_of_nonneg_left hΔCK (by positivity)
    -- `2²⁶ N²¹ N^{-C_K} ≤ N^{-D₁} N^{-2D}`
    have hB : 2 ^ 22 * (N : ℝ) ^ 21 * (N : ℝ) ^ (-CK D D₁) ≤
        (N : ℝ) ^ (-D₁) * ((N : ℝ) ^ (-(2 * D)) / 16) := by
      have e1 : (N : ℝ) ^ (-CK D D₁) = (N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D)) *
          (N : ℝ) ^ (-80 : ℝ) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; unfold CK; congr 1; ring
      have e2 : (N : ℝ) ^ 21 * (N : ℝ) ^ (-80 : ℝ) = (N : ℝ) ^ (-59 : ℝ) := by
        rw [show ((N : ℝ) ^ 21) = (N : ℝ) ^ ((21 : ℕ) : ℝ) by rw [Real.rpow_natCast],
          ← Real.rpow_add hN0]; norm_num
      have h59 : (N : ℝ) ^ (-59 : ℝ) ≤ 1 / 2 ^ 26 := by
        rw [Real.rpow_neg hN0.le, show (59 : ℝ) = ((59 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : (2 : ℝ) ^ 59 ≤ (N : ℝ) ^ 59 := pow_le_pow_left₀ (by norm_num) hN2' 59
        nlinarith
      rw [e1]
      have hP : 0 ≤ (N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D)) := by positivity
      calc 2 ^ 22 * (N : ℝ) ^ 21 * ((N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D)) * (N : ℝ) ^ (-80 : ℝ))
          = 2 ^ 22 * ((N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D))) *
              ((N : ℝ) ^ 21 * (N : ℝ) ^ (-80 : ℝ)) := by ring
        _ = 2 ^ 22 * ((N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D))) * (N : ℝ) ^ (-59 : ℝ) := by
            rw [e2]
        _ ≤ 2 ^ 22 * ((N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D))) * (1 / 2 ^ 26) :=
            mul_le_mul_of_nonneg_left h59 (by positivity)
        _ = (N : ℝ) ^ (-D₁) * ((N : ℝ) ^ (-(2 * D)) / 16) := by ring
    calc (d.L N : ℝ) ^ 2 * ((K N : ℝ) * eb) ≤ _ := hA
      _ ≤ _ := hB
      _ ≤ (N : ℝ) ^ (-D₁) * (((d.W N : ℝ) ^ (-D)) / 4) ^ 2 :=
          mul_le_mul_of_nonneg_left hx2 (by positivity)
  calc (Pg d) _ ≤ (Pg d) Sbad := measure_mono hsub
    _ = ENNReal.ofReal ((Pg d).real Sbad) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := ENNReal.ofReal_le_ofReal (hcheb.trans hfinal)

section CompatN

end CompatN

end GoodEventPlainN

end RBM.Gauss.Grid

end
