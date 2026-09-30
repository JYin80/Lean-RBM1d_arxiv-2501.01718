/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.EnergyN.Gauss.Step2Plain
import RBM1D.EnergyN.Gauss.GridGoodSet
import RBM1D.EnergyN.Gauss.GridGoodEvent
import RBM1D.EnergyN.Gauss.Lemma514Holder
import RBM1D.EnergyN.Gauss.EntryBoundTime
import RBM1D.EnergyN.Hierarchy.Step1
import RBM1D.EnergyN.Hierarchy.Step2
import RBM1D.EnergyN.Hierarchy.StepGlue
import RBM1D.EnergyN.Gauss.GridBootstrap
import RBM1D.EnergyN.Gauss.Step2Close
import RBM1D.EnergyN.Gauss.Steps12Gauss

/-!
# Steps 1–2 for the Gaussian flow under the plain pair, at an `N`-dependent energy

The second half of Step 2 for the Gaussian flow at an `N`-dependent energy `E : ℕ → ℝ`: the
quadratic-variation time sums (`qv_time_sum_le_plainN`, `qv_time_sum_le_plain'N`), the martingale
bound `xZ ≤ azumaMm …` (`xZ_le_azumaMm_plainN`), the grid good event and its consequences
(`goodEvent_grid_plainN`, `goodEvent_grid_imp_plainN`), (2.76) from its pointwise form
(`h276_of_pointwise_plainN`), the scalar facts of the drift bound
(`drift_point_le_heG_scalars_plainN`), the pointwise grid bound (`gridPointwise'_gauss_plainN`),
and Step 2 itself: (2.75) and (2.76) (`step2_gauss_of_pointwise_plainN`, `step2_gauss_plainN`) and
Steps 1–2 together (`steps12_gauss_plainN`). The first part is in
`RBM1D/EnergyN/Gauss/Step2Plain.lean`.

## The external `κ`

None of these fixes an energy-dependent constant itself. Two of them call statements that do:

* `goodEvent_grid_imp_plainN` — its statement contains `azumaMm (E N) … N ≤ N^{δ/8}`, so it
  takes `{κ:ℝ}(hκ0:0<κ)(hE:∀N,|E N|≤2−κ)` rather than `(hE:∀N,|E N|<2)` and calls `azumaMm_leN`
  (`GridGoodEvent.lean`).
* `h276_of_pointwise_plainN` — its proof calls `hKb_flowN` (`Lemma514Holder.lean`), so it takes
  `{κ:ℝ}(hκ0:0<κ)(hκ1:κ≤1)(hEκ:∀N,|E N|≤2−κ)` rather than `(hE:∀N,|E N|<2)`.

Neither propagates outward: the only call site of each (`gridPointwise'_gauss_plainN` and
`step2_gauss_of_pointwise_plainN` respectively) already carries a `κ` of the required strength.
Inside `goodEvent_grid_plainN`, the call of `highProb_grid_goodSetN`, which needs `κ ≤ 1`, uses
the clamp `κ' := min κ 1`, with no change of signature.

`heG_coef_eq_driftCoef'`, `drift_of_goodSet'`, `Qd`, `Qd_mul_le_plain`, `Qd_nonneg`,
`final_arith`, `mgDrift`/`mgDrift_le`, `gridK`/`gridK_ne_zero`/`gridK_card_le`/`step_gridK_le`,
`min_firstHit_eq_of_at`, `lk_le_of_jS`, `eventually_cNear2_le_rpow`, and the measure-theoretic
kernel lemmas are energy-free/generic, used at `E N`. `GridPointwise'N` (the predicate that
`gridPointwise'_gauss_plainN` concludes) is in `GridBootstrap.lean`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open Finset Real MeasureTheory Filter

section QVSumN

open QVSum in
/-- **The quadratic-variation time sum**: for every `κ > 0`, eventually, for all grids on
`[s, T] ⊆ [s, t]` and `k ≤ Kq`, `Σ_{j<k} step · Qd(u_j) ((1 - u_j)/(1 - u_k))^4` is at most
`qvSumConst · N^κ ((η_s/η_{u_k})^4 + 1)`. -/
theorem qv_time_sum_le_plainN {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) {E : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (_hcond : Cond272N B E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N))
    {δ ε D : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 90) (_hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ)
    (hD : 60 ≤ D) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ N : ℕ in atTop, ∀ (T : ℕ → ℝ) (Kq : ℕ → ℕ),
      s N ≤ T N → T N ≤ t N → 1 ≤ Kq N → ∀ k : ℕ, k ≤ Kq N →
        ∑ j ∈ Finset.range k, step s T Kq N * Qd B (E N) s δ ε D N (time s T Kq N j) *
            ((1 - time s T Kq N j) / (1 - time s T Kq N k)) ^ 4
          ≤ qvSumConst (E N) * (N : ℝ) ^ κ *
              ((etaT (E N) (s N) / etaT (E N) (time s T Kq N k)) ^ 4 + 1) := by
  intro κ hκ
  filter_upwards [eventually_cNear2_le_rpow B hκ,
    (Step2.tendsto_W B).eventually_ge_atTop (Real.exp ((4 * D) ^ 2 + 4)),
    hreg0, hAc, B.dim, Step2.eventually_le_W_sq B, eventually_ge_atTop 1]
    with N hcN hWbig hregN hAcN hdim hNW hN1 T Kq hsT hTt hK k hk
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
  have hm0 : 0 < (mE (E N)).im := mE_im_pos (hE N)
  have hm1 : (mE (E N)).im ≤ 1 := mE_im_le_one (hE N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hKpos : (0 : ℝ) < (Kq N : ℝ) := by exact_mod_cast hK
  have hΔ0 : 0 ≤ step s T Kq N := div_nonneg (by linarith) hKpos.le
  have hKΔ : (Kq N : ℝ) * step s T Kq N = T N - s N := by
    unfold step; field_simp
  have hjΔ : ∀ j : ℕ, j ≤ k → (j : ℝ) * step s T Kq N ≤ T N - s N := by
    intro j hj
    have : (j : ℝ) ≤ Kq N := by exact_mod_cast hj.trans hk
    rw [← hKΔ]; exact mul_le_mul_of_nonneg_right this hΔ0
  have hvt : time s T Kq N k ≤ t N := by
    unfold time; linarith [hjΔ k le_rfl]
  have hsv : s N ≤ time s T Kq N k := by
    unfold time; have : 0 ≤ (k : ℝ) * step s T Kq N := by positivity
    linarith
  have hmem : ∀ j ∈ Finset.range k, s N ≤ time s T Kq N j ∧ time s T Kq N j ≤ time s T Kq N k := by
    intro j hj
    have hjk : (j : ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.1 hj).le
    unfold time
    constructor
    · have : 0 ≤ (j : ℝ) * step s T Kq N := by positivity
      linarith
    · have := mul_le_mul_of_nonneg_right hjk hΔ0
      linarith
  set M : ℝ := (34 * (N : ℝ) ^ κ + 1152) *
      (etaT (E N) (s N) ^ 3 / etaT (E N) (time s T Kq N k) ^ 4)
      + 3 * (etaT (E N) (s N) / etaT (E N) (time s T Kq N k)) ^ 4 with hMdef
  have hv1 : time s T Kq N k < 1 := hvt.trans_lt (ht1 N)
  have hηv : 0 < etaT (E N) (time s T Kq N k) := Step2.etaT_pos' (hE N) hv1
  have hηs : 0 < etaT (E N) (s N) := Step2.etaT_pos' (hE N) hs1
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hterm : ∀ j ∈ Finset.range k,
      step s T Kq N * Qd B (E N) s δ ε D N (time s T Kq N j) *
          ((1 - time s T Kq N j) / (1 - time s T Kq N k)) ^ 4 ≤ step s T Kq N * M := by
    intro j hj
    obtain ⟨h1, h2⟩ := hmem j hj
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (Qd_mul_le_plain B (hE N) hN1' (hs0 N) h1 h2 hvt (ht1 N) hc0 hregN hAcN hδ0.le (by linarith)
        hεδ hD hWbig hWL hNW hcN) hΔ0
  have hkΔ : (k : ℝ) * step s T Kq N ≤ 1 - s N := by
    have := hjΔ k le_rfl
    linarith [hTt, ht1 N]
  have hXY : (1 - s N) * (etaT (E N) (s N) ^ 3 / etaT (E N) (time s T Kq N k) ^ 4) =
      (mE (E N)).im⁻¹ * (etaT (E N) (s N) / etaT (E N) (time s T Kq N k)) ^ 4 := by
    have e : etaT (E N) (s N) = (1 - s N) * (mE (E N)).im := rfl
    rw [e]; field_simp
  have hb : 1 ≤ (mE (E N)).im⁻¹ := (one_le_inv₀ hm0).2 hm1
  have ha : 1 ≤ (N : ℝ) ^ κ := Real.one_le_rpow hN1' hκ.le
  calc ∑ j ∈ Finset.range k, step s T Kq N * Qd B (E N) s δ ε D N (time s T Kq N j) *
          ((1 - time s T Kq N j) / (1 - time s T Kq N k)) ^ 4
      ≤ ∑ _j ∈ Finset.range k, step s T Kq N * M := Finset.sum_le_sum hterm
    _ = (k : ℝ) * step s T Kq N * M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ (1 - s N) * M := mul_le_mul_of_nonneg_right hkΔ hM0
    _ = (34 * (N : ℝ) ^ κ + 1152) *
          ((mE (E N)).im⁻¹ * (etaT (E N) (s N) / etaT (E N) (time s T Kq N k)) ^ 4)
          + 3 * (1 - s N) * (etaT (E N) (s N) / etaT (E N) (time s T Kq N k)) ^ 4 := by
        rw [hMdef, ← hXY]; ring
    _ ≤ 1200 * (mE (E N)).im⁻¹ * (N : ℝ) ^ κ *
          ((etaT (E N) (s N) / etaT (E N) (time s T Kq N k)) ^ 4 + 1) :=
        final_arith ha hb (by positivity) (by linarith [hs0 N])
    _ = qvSumConst (E N) * (N : ℝ) ^ κ *
          ((etaT (E N) (s N) / etaT (E N) (time s T Kq N k)) ^ 4 + 1) := by
        unfold qvSumConst; ring

open QVSum in
/-- **The same time sum with the factor `((1 - u_{j+1})/(1 - u_k))^4`.** -/
theorem qv_time_sum_le_plain'N {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) {E : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272N B E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N))
    {δ ε D : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 90) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ)
    (hD : 60 ≤ D) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ N : ℕ in atTop, ∀ (T : ℕ → ℝ) (Kq : ℕ → ℕ),
      s N ≤ T N → T N ≤ t N → 1 ≤ Kq N → ∀ k : ℕ, k ≤ Kq N →
        ∑ j ∈ Finset.range k, step s T Kq N * Qd B (E N) s δ ε D N (time s T Kq N j) *
            ((1 - time s T Kq N (j + 1)) / (1 - time s T Kq N k)) ^ 4
          ≤ qvSumConst (E N) * (N : ℝ) ^ κ *
              ((etaT (E N) (s N) / etaT (E N) (time s T Kq N k)) ^ 4 + 1) := by
  intro κ hκ
  filter_upwards [qv_time_sum_le_plainN B hE hs0 hst ht1 hcond hc0 hreg0 hAc hδ0 hδc hε0 hεδ hD κ
      hκ] with N hN T Kq hsT hTt hK k hk
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) (hN T Kq hsT hTt hK k hk)
  have hjk : j + 1 ≤ k := Finset.mem_range.1 hj
  have hKpos : (0 : ℝ) < (Kq N : ℝ) := by exact_mod_cast hK
  have hΔ0 : 0 ≤ step s T Kq N := div_nonneg (by linarith) hKpos.le
  have hKΔ : (Kq N : ℝ) * step s T Kq N = T N - s N := by
    unfold step; field_simp
  have hkΔ : (k : ℝ) * step s T Kq N ≤ T N - s N := by
    have : (k : ℝ) ≤ Kq N := by exact_mod_cast hk
    rw [← hKΔ]; exact mul_le_mul_of_nonneg_right this hΔ0
  have hjk' : ((j + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hjk
  have hv1 : time s T Kq N k < 1 := by
    unfold time; linarith [ht1 N]
  have hj1 : time s T Kq N j ≤ time s T Kq N (j + 1) := by
    unfold time; push_cast; nlinarith
  have hj1k : time s T Kq N (j + 1) ≤ time s T Kq N k := by
    unfold time; have := mul_le_mul_of_nonneg_right hjk' hΔ0; linarith
  have hj0 : 0 ≤ time s T Kq N j := by
    unfold time; have : 0 ≤ (j : ℝ) * step s T Kq N := by positivity
    linarith [hs0 N]
  have hjlt1 : time s T Kq N j < 1 := by linarith
  have hQ : 0 ≤ Qd B (E N) s δ ε D N (time s T Kq N j) :=
    Qd_nonneg B (hE N) ((hst N).trans_lt (ht1 N)) hj0 hjlt1
  have hden : 0 < 1 - time s T Kq N k := by linarith
  have hfac : ((1 - time s T Kq N (j + 1)) / (1 - time s T Kq N k)) ^ 4 ≤
      ((1 - time s T Kq N j) / (1 - time s T Kq N k)) ^ 4 :=
    pow_le_pow_left₀ (div_nonneg (by linarith) hden.le)
      (div_le_div_of_nonneg_right (by linarith) hden.le) 4
  exact mul_le_mul_of_nonneg_left hfac (mul_nonneg hΔ0 hQ)

end QVSumN

section GoodEventPlainN2

variable {d : Dims}

set_option maxHeartbeats 1000000 in
-- a long chain of `set`-bound real quantities (as in `eventually_step_facts_plainN`)
/-- **`xZ ≤ azumaMm ((η_s/η_{u_k})^2 + 1) T_{u_k,D}`** eventually, at all grid times `k ≤ K N` and
pairs `a`. -/
theorem xZ_le_azumaMm_plainN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t u : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272N (band d) E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {δ ε D τ₁ : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 90) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ)
    (hD : 60 ≤ D) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) (K : ℕ → ℕ)
    (hK0 : ∀ N, K N ≠ 0) (hΔ : ∀ᶠ N : ℕ in atTop, step s u K N ≤ (N : ℝ) ^ (-(D + 10)))
    {Cc Cx : ℝ} (hCc : 2 * D ≤ Cc) (hCx : 2 * D ≤ Cx) :
    ∀ᶠ N : ℕ in atTop, ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      xZ d (E N) s u K δ ε D τ₁ Cc Cx N k a ≤ azumaMm d (E N) δ τ₁ N *
        ((etaT (E N) (s N) / etaT (E N) (time s u K N k)) ^ 2 + 1) *
        Step2.tT (band d) (E N) N D (time s u K N k) (zdist (d.L N) (a 0 - a 1)) := by
  filter_upwards [qv_time_sum_le_plain'N (band d) hE hs0 hst ht1 hcond hc0 hreg0 hAc hδ0 hδc hε0
      hεδ hD (δ / 64) (by positivity), etaT_inv_le_of_plainN (band d) hE ht1 hc0 hAc, hΔ, d.dim,
      eventually_ge_atTop 64] with N hqv hηt hΔN hdim hN64 k hk a
  have hN64' : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hK1 : 1 ≤ K N := Nat.one_le_iff_ne_zero.2 (hK0 N)
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  have hm0 := mE_im_pos (hE N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  set uk := time s u K N k with huk
  have huk1 : uk < 1 := time_lt_one_of_le hsu hut ht1 hK0 hk
  have hukt : uk ≤ t N := by
    have := time_mono_of_le (K := K) (hsu N) hk
    rw [time_last s u K N (hK0 N)] at this; linarith [hut N]
  have hkΔ : (k : ℝ) * step s u K N ≤ 1 := by
    have hKne : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hK0 N)
    have hKΔ : (K N : ℝ) * step s u K N = u N - s N := by unfold step; field_simp
    have : (k : ℝ) ≤ K N := by exact_mod_cast hk
    have := mul_le_mul_of_nonneg_right this hΔ0
    linarith [hs0 N, hut N, ht1 N]
  set R := etaT (E N) (s N) / etaT (E N) uk with hR
  have hRe : R = (1 - s N) / (1 - uk) := Step2.etaT_ratio (hE N) _ _
  have h1uk : 0 < 1 - uk := by linarith
  have hR0 : 0 ≤ R := by rw [hRe]; exact div_nonneg (by linarith) h1uk.le
  have hr : ∀ j ∈ Finset.range k, 0 ≤ (1 - time s u K N (j + 1)) / (1 - uk) ∧
      (1 - time s u K N (j + 1)) / (1 - uk) ≤ R := by
    intro j hj
    have hjk : j + 1 ≤ k := Finset.mem_range.1 hj
    have h1 := time_mono_of_le (K := K) (hsu N) hjk
    have h2 := time_mono_of_le (K := K) (hsu N) (Nat.zero_le (j + 1))
    rw [time_zero] at h2
    rw [hRe]
    exact ⟨div_nonneg (by linarith) h1uk.le, div_le_div_of_nonneg_right (by linarith) h1uk.le⟩
  have hcard := card_idx_le hdim.1
  have hηt0 : 0 < etaT (E N) (t N) := Step2.etaT_pos' (hE N) (ht1 N)
  have hWN : ((band d).W N : ℝ) ≤ N := by
    have hL : (1 : ℝ) ≤ d.L N := by exact_mod_cast (by have := d.three_le_L N; omega : 1 ≤ d.L N)
    have h' : (d.W N : ℝ) * d.L N ≤ N := by exact_mod_cast hdim.1
    have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
    change (d.W N : ℝ) ≤ N
    nlinarith
  have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by exact_mod_cast d.W_pos N
  have hCsh : ∀ j ∈ Finset.range k, 2 * qvTimeShiftConst d N (E N) (time s u K N (j + 1)) ^ 2 *
      step s u K N ^ 2 * ((band d).W N : ℝ) ^ (2 * D) ≤ 1 := by
    intro j hj
    have hjk : j + 1 ≤ k := Finset.mem_range.1 hj
    have hv : time s u K N (j + 1) ≤ t N := (time_mono_of_le (hsu N) hjk).trans hukt
    have hηv : etaT (E N) (t N) ≤ etaT (E N) (time s u K N (j + 1)) := by
      simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
    have hηv0 : 0 < etaT (E N) (time s u K N (j + 1)) := lt_of_lt_of_le hηt0 hηv
    have hinv : (etaT (E N) (time s u K N (j + 1)))⁻¹ ≤ N := (inv_anti₀ hηt0 hηv).trans hηt
    exact two_Csh_sq_step_sq_le hN64' hD0 (qvTimeShiftConst_nonneg _ _ _ _)
      (qvTimeShiftConst_le hN1' hcard hinv (inv_nonneg.2 hηv0.le)) hΔ0 hΔN hW1 hWN
  set ξ := Step2.xiK (d.L N) (d.W N) (mE (E N)).im with hξ
  set T := Step2.tT (band d) (E N) N D uk (zdist (d.L N) (a 0 - a 1)) with hT
  have hTW : ((band d).W N : ℝ) ^ (-D) ≤ T := rpow_neg_le_tailT _
  have hTN : (N : ℝ) ^ (-D) ≤ T :=
    (Real.rpow_le_rpow_of_nonpos (by linarith) hWN (by linarith)).trans hTW
  have hNmD : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hT0 : 0 < T := lt_of_lt_of_le hNmD hTN
  have hT2 : (N : ℝ) ^ (-(2 * D)) ≤ T ^ 2 := by
    calc (N : ℝ) ^ (-(2 * D)) = ((N : ℝ) ^ (-D)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
      _ ≤ T ^ 2 := pow_le_pow_left₀ hNmD.le hTN 2
  -- termwise bound on `cZ`
  have hcZ : ∀ j ∈ Finset.range k, cZ d (E N) s u K δ ε D τ₁ Cc N k a j ≤
      ξ ^ 2 * T ^ 2 * (2 * (N : ℝ) ^ τ₁ * (step s u K N * Qd (band d) (E N) s δ ε D N
        (time s u K N j) * ((1 - time s u K N (j + 1)) / (1 - uk)) ^ 4)
        + step s u K N * R ^ 4) + step s u K N * (N : ℝ) ^ (-Cc) := by
    intro j hj
    obtain ⟨hr0, hrR⟩ := hr j hj
    set r := (1 - time s u K N (j + 1)) / (1 - uk) with hrdef
    have hjk : j < k := Finset.mem_range.1 hj
    have huj : time s u K N j < 1 :=
      (time_mono_of_le (hsu N) hjk.le).trans_lt huk1
    have huj0 : 0 ≤ time s u K N j := by
      have := time_mono_of_le (K := K) (hsu N) (Nat.zero_le j); rw [time_zero] at this
      linarith [hs0 N]
    have hQd := QVSum.Qd_nonneg (band d) (hE N) (s := s) (δ := δ) (ε := ε) (D := D) (N := N) hs1
      huj0 huj
    have hQ : 0 ≤ Qprime d (E N) s u K δ ε D τ₁ N j := by
      unfold Qprime
      have := qvTimeShiftConst_nonneg d N (E N) (time s u K N (j + 1))
      have : 0 ≤ ((band d).W N : ℝ) ^ (2 * D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    have hr4 : r ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ hr0 hrR 4
    have hcsh := hCsh j hj
    have e1 : cZ d (E N) s u K δ ε D τ₁ Cc N k a j = ξ ^ 2 * T ^ 2 *
        (step s u K N * Qprime d (E N) s u K δ ε D τ₁ N j * r ^ 4) +
        step s u K N * (N : ℝ) ^ (-Cc) := by
      unfold cZ
      rw [← hrdef, ← huk, ← hξ, ← hT]
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hQ, ← pow_mul]
      ring
    rw [e1]
    have e2 : step s u K N * Qprime d (E N) s u K δ ε D τ₁ N j * r ^ 4 =
        2 * (N : ℝ) ^ τ₁ * (step s u K N * Qd (band d) (E N) s δ ε D N (time s u K N j) * r ^ 4)
        + (2 * qvTimeShiftConst d N (E N) (time s u K N (j + 1)) ^ 2 * step s u K N ^ 2 *
          ((band d).W N : ℝ) ^ (2 * D)) * (step s u K N * r ^ 4) := by
      unfold Qprime; ring
    rw [e2]
    have h3 : (2 * qvTimeShiftConst d N (E N) (time s u K N (j + 1)) ^ 2 * step s u K N ^ 2 *
          ((band d).W N : ℝ) ^ (2 * D)) * (step s u K N * r ^ 4) ≤ step s u K N * R ^ 4 := by
      have hsr : 0 ≤ step s u K N * r ^ 4 := by positivity
      calc _ ≤ 1 * (step s u K N * r ^ 4) := mul_le_mul_of_nonneg_right hcsh hsr
        _ ≤ step s u K N * R ^ 4 := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hr4 hΔ0
    have hξT : 0 ≤ ξ ^ 2 * T ^ 2 := by positivity
    nlinarith
  -- summed bound
  have hqvk := hqv u K (hsu N) (hut N) hK1 k hk
  set SQ := ∑ j ∈ Finset.range k, step s u K N * Qd (band d) (E N) s δ ε D N (time s u K N j) *
    ((1 - time s u K N (j + 1)) / (1 - uk)) ^ 4 with hSQ
  have hs := sum_le_affine_sum (ξ ^ 2 * T ^ 2) (2 * (N : ℝ) ^ τ₁) (step s u K N * R ^ 4)
    (step s u K N * (N : ℝ) ^ (-Cc)) hcZ
  rw [← hSQ] at hs
  set P0 := (N : ℝ) ^ (τ₁ + δ / 64) with hP0
  have hNτ : (N : ℝ) ^ τ₁ * (N : ℝ) ^ (δ / 64) = P0 := by rw [hP0, Real.rpow_add hN0]
  have hq0 : 0 ≤ qvSumConst (E N) := by unfold qvSumConst; positivity
  have hSQ' : 2 * (N : ℝ) ^ τ₁ * SQ ≤ 2 * qvSumConst (E N) * P0 * (R ^ 4 + 1) := by
    calc 2 * (N : ℝ) ^ τ₁ * SQ ≤ 2 * (N : ℝ) ^ τ₁ * (qvSumConst (E N) * (N : ℝ) ^ (δ / 64) *
          (R ^ 4 + 1)) := mul_le_mul_of_nonneg_left hqvk (by positivity)
      _ = 2 * qvSumConst (E N) * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (δ / 64)) * (R ^ 4 + 1) := by ring
      _ = 2 * qvSumConst (E N) * P0 * (R ^ 4 + 1) := by rw [hNτ]
  have hkR : (k : ℝ) * (step s u K N * R ^ 4) ≤ R ^ 4 := by
    calc (k : ℝ) * (step s u K N * R ^ 4) = ((k : ℝ) * step s u K N) * R ^ 4 := by ring
      _ ≤ R ^ 4 := by
          have hR40 : 0 ≤ R ^ 4 := by positivity
          calc ((k:ℝ) * step s u K N) * R^4 ≤ 1 * R^4 := mul_le_mul_of_nonneg_right hkΔ hR40
            _ = R^4 := one_mul _
  have hNc : 0 ≤ (N : ℝ) ^ (-Cc) := Real.rpow_nonneg hN0.le _
  have hkC : (k : ℝ) * (step s u K N * (N : ℝ) ^ (-Cc)) ≤ (N : ℝ) ^ (-Cc) := by
    calc (k : ℝ) * (step s u K N * (N : ℝ) ^ (-Cc))
        = ((k : ℝ) * step s u K N) * (N : ℝ) ^ (-Cc) := by ring
      _ ≤ 1 * (N : ℝ) ^ (-Cc) := mul_le_mul_of_nonneg_right hkΔ hNc
      _ = _ := one_mul _
  have hinnerB : 2 * (N : ℝ) ^ τ₁ * SQ + (k : ℝ) * (step s u K N * R ^ 4) ≤
      (2 * qvSumConst (E N) * P0 + 2) * (R ^ 4 + 1) := by
    have hR4 : 0 ≤ R ^ 4 := by positivity
    have e : (2 * qvSumConst (E N) * P0 + 2) * (R ^ 4 + 1)
        = 2 * qvSumConst (E N) * P0 * (R ^ 4 + 1) + 2 * R ^ 4 + 2 := by ring
    rw [e]; linarith
  have hsumcZ : ∑ j ∈ Finset.range k, cZ d (E N) s u K δ ε D τ₁ Cc N k a j ≤
      ξ ^ 2 * T ^ 2 * ((2 * qvSumConst (E N) * P0 + 2) * (R ^ 4 + 1)) + (N : ℝ) ^ (-Cc) := by
    have hξT : 0 ≤ ξ ^ 2 * T ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hinnerB hξT
    linarith
  have hNCc : (N : ℝ) ^ (-Cc) ≤ T ^ 2 :=
    (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)).trans hT2
  have hNCx : (N : ℝ) ^ (-Cx) ≤ T ^ 2 :=
    (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)).trans hT2
  have hsqrt := sqrt_floor_arith hT0.le
    (mul_nonneg (mul_nonneg (by norm_num) hq0) (Real.rpow_nonneg hN0.le _)) hsumcZ hNCc hNCx
  unfold xZ azumaMm
  rw [← hξ, ← hP0]
  calc (N : ℝ) ^ (δ / 16) * Real.sqrt (4 * ∑ j ∈ Finset.range k,
        cZ d (E N) s u K δ ε D τ₁ Cc N k a j + (N : ℝ) ^ (-Cx))
      ≤ (N : ℝ) ^ (δ / 16) * (T * (R ^ 2 + 1) *
          Real.sqrt (4 * ξ ^ 2 * (2 * qvSumConst (E N) * P0 + 2) + 5)) :=
        mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ (δ / 16) * Real.sqrt (4 * ξ ^ 2 * (2 * qvSumConst (E N) * P0 + 2) + 5) *
          (R ^ 2 + 1) * T := by ring

/-- **The grid good event `goodEventGrid` fails with probability at most `N^{-D₁}`**, eventually.
`κ` is explicit. The call of `highProb_grid_goodSetN` needs `κ ≤ 1`; it uses
`κ' := min κ 1`, which satisfies `0 < κ'`, `κ' ≤ 1`, `κ' ≤ κ`, so `hE' : ∀N,|E N|≤2−κ'`
follows from `hE`. -/
theorem goodEvent_grid_plainN {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t u : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 90) (hD : 60 ≤ D)
    {τ₁ ε ζCtr τ3 τ57 : ℝ} (hτ₁ : 0 < τ₁) (hε : 0 < ε) (hζ : 0 < ζCtr) (hτ3 : 0 < τ3)
    (hτ57 : 0 < τ57) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (Pg d) (goodEventGrid d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1))
        (2 * D + 2) (2 * D + 2) N)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
  intro D₁ hD₁
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hD0 : 0 ≤ D := by linarith
  set K : ℕ → ℕ := gridK D (D₁ + 1) with hKdef
  have hK0 : ∀ N, K N ≠ 0 := gridK_ne_zero D (D₁ + 1)
  have hCK : 0 ≤ CK D (D₁ + 1) := by unfold CK; linarith
  have hKcard := gridK_card_le hCK
  have hregp : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N) := hAc
  have H3 := highProb_azuma_grid_plainN hE2 hs0 hst ht1 hc0 hreg0 hAc hδ0 hδc hD0 τ₁ ε ζCtr τ3 τ57
    hsu hut K hK0 hKcard (2 * D + 2) (2 * D + 2)
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  have HG := highProb_grid_goodSetN d hκ'0 hκ'1 hEκ' hB hs0 hst ht1 hcond hc0 hregp hD hτ₁ hε hζ
    hτ3 hτ57 hsu hut K hK0 (by linarith) hKcard
  have H5 := highProb_init_grid_plainN (u := u) hE2 hB hs0 hst ht1 hc0 hreg0 hAc hδ0
    (by linarith : (0 : ℝ) < D) hsu K hK0
  have Hint := (H3.inter HG).inter H5
  have HY := cheb_grid_at_tau_plainN hE2 hs0 hst ht1 hc0 hAc hD0 δ τ₁ ε ζCtr τ3 τ57 hsu hut
    (D₁ + 1) (by linarith)
  clear hκ'1 hκ'0 hκ'def
  filter_upwards [Hint (D₁ + 1) (by linarith), HY, eventually_ge_atTop 2] with N h1 h2 hN2
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  set G := goodEventGrid d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K (2 * D + 2) (2 * D + 2) N with hG
  set Ybad : Set (Ωg d) := {ω | ∃ a : LoopArg (d.L N) 2,
        Step2.tT (band d) (E N) N D
            (time s u K N (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω))
            (zdist (d.L N) (a 0 - a 1)) ≤
          ‖(∑ j ∈ Finset.range (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
                (time s u K N (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω) : ℂ)
                (Yvec (band d) (E N) s u K N (j + 1) ω)) a‖} with hYbad
  set I3 := {ω | ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (min k (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω)),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (Zvec (band d) (E N) s u K N (j + 1) ω)) a‖
        < xZ d (E N) s u K δ ε D τ₁ (2 * D + 2) (2 * D + 2) N k a} ∩
      {ω | ∀ k : Fin (K N + 1), H d s u K N k ω ∈
        goodSet d (E N) N (time s u K N k) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D} ∩
      {ω | (∀ b : LoopArg (d.L N) 2, ‖Agrid (band d) (E N) s u K N 0 ω b‖ ≤
        (N : ℝ) ^ (δ / 16) * Step2.tT (band d) (E N) N D (time s u K N 0)
          (zdist (d.L N) (b 0 - b 1)))
      ∧ jSMat d (E N) D N (time s u K N 0) (H d s u K N 0 ω)
        < Step2.thr (E N) s δ N (time s u K N 0)} with hI3
  have hsub : Gᶜ ⊆ I3ᶜ ∪ Ybad := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hI, hYn⟩ := hcon
    apply hω
    obtain ⟨⟨hA, hGs⟩, hIn⟩ := hI
    refine ⟨⟨⟨hA, fun a => ?_⟩, hGs⟩, hIn⟩
    by_contra hlt
    exact hYn ⟨a, not_lt.1 hlt⟩
  calc (Pg d) Gᶜ ≤ (Pg d) (I3ᶜ ∪ Ybad) := measure_mono hsub
    _ ≤ (Pg d) I3ᶜ + (Pg d) Ybad := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1))) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D₁ + 1))) := by
        rw [← ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)]
        ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show -(D₁ + 1) = -D₁ + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
        have h0 : 0 ≤ (N : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
        have : 2 * (N : ℝ)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hN0]; exact hN2'
        nlinarith

/-- **Consequences of the grid good event**: eventually `1 ≤ gridK`, the step is at most
`N^{-(2D+76)}`, `0 ≤ azumaMm ≤ N^{δ/8}`, and on `goodEventGrid` the initial value and the
stopped martingale sum are bounded. Its statement contains `azumaMm E δ τ₁ N ≤ N^{δ/8}`, so it
takes `{κ:ℝ}(hκ0:0<κ)(hE:∀N,|E N|≤2−κ)` and calls `azumaMm_leN`. The only call site
(`gridPointwise'_gauss_plainN`) already carries this `κ`. -/
theorem goodEvent_grid_imp_plainN {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t u : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) {c : ℝ}
    (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 90) (hD : 60 ≤ D)
    {τ₁ ε : ℝ} (ζCtr τ3 τ57 : ℝ) (hτ₁δ : τ₁ ≤ δ / 32) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ)
    (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (1 ≤ gridK D (D₁ + 1) N ∧
        step s u (gridK D (D₁ + 1)) N ≤ (N : ℝ) ^ (-(2 * D + 76)) ∧
        0 ≤ azumaMm d (E N) δ τ₁ N ∧ azumaMm d (E N) δ τ₁ N ≤ (N : ℝ) ^ (δ / 8)) ∧
      ∀ ω ∈ goodEventGrid d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1))
          (2 * D + 2) (2 * D + 2) N,
        (∀ b : LoopArg (d.L N) 2, ‖Agrid (band d) (E N) s u (gridK D (D₁ + 1)) N 0 ω b‖ ≤
          (N : ℝ) ^ (δ / 16) * Step2.tT (band d) (E N) N D (time s u (gridK D (D₁ + 1)) N 0)
            (zdist (d.L N) (b 0 - b 1))) ∧
        (∀ b : LoopArg (d.L N) 2,
          ‖(∑ j ∈ Finset.range
                (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s u (gridK D (D₁ + 1)) N (j + 1) : ℂ)
                (time s u (gridK D (D₁ + 1)) N
                  (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω) : ℂ)
                (Zvec (band d) (E N) s u (gridK D (D₁ + 1)) N (j + 1) ω)) b‖ ≤
            azumaMm d (E N) δ τ₁ N * ((etaT (E N) (s N) / etaT (E N) (time s u
              (gridK D (D₁ + 1)) N
              (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω))) ^ 2 + 1) *
              Step2.tT (band d) (E N) N D (time s u (gridK D (D₁ + 1)) N
                (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω))
                (zdist (d.L N) (b 0 - b 1))) ∧
        (∀ b : LoopArg (d.L N) 2,
          ‖(∑ j ∈ Finset.range
                (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s u (gridK D (D₁ + 1)) N (j + 1) : ℂ)
                (time s u (gridK D (D₁ + 1)) N
                  (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω) : ℂ)
                (Yvec (band d) (E N) s u (gridK D (D₁ + 1)) N (j + 1) ω)) b‖ ≤
            Step2.tT (band d) (E N) N D (time s u (gridK D (D₁ + 1)) N
                (gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω))
                (zdist (d.L N) (b 0 - b 1))) ∧
        (∀ j < gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω,
          jSMat d (E N) D N (time s u (gridK D (D₁ + 1)) N j)
              (H d s u (gridK D (D₁ + 1)) N j ω)
            < Step2.thr (E N) s δ N (time s u (gridK D (D₁ + 1)) N j) ∧
          H d s u (gridK D (D₁ + 1)) N j ω ∈ goodSet d (E N) N
            (time s u (gridK D (D₁ + 1)) N j)
            ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D) ∧
        (∀ j ≤ gridK D (D₁ + 1) N,
          H d s u (gridK D (D₁ + 1)) N j ω ∈ goodSet d (E N) N
            (time s u (gridK D (D₁ + 1)) N j)
            ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D) ∧
        jSMat d (E N) D N (time s u (gridK D (D₁ + 1)) N 0) (H d s u (gridK D (D₁ + 1)) N 0 ω)
          < Step2.thr (E N) s δ N (time s u (gridK D (D₁ + 1)) N 0) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  intro D₁ hD₁
  have hD0 : 0 ≤ D := by linarith
  set K : ℕ → ℕ := gridK D (D₁ + 1) with hKdef
  have hK0 : ∀ N, K N ≠ 0 := gridK_ne_zero D (D₁ + 1)
  have hstepCK : ∀ᶠ N : ℕ in atTop, step s u K N ≤ (N : ℝ) ^ (-CK D (D₁ + 1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact step_gridK_le hN (by linarith [hs0 N, hut N, ht1 N])
  have hΔ10 : ∀ᶠ N : ℕ in atTop, step s u K N ≤ (N : ℝ) ^ (-(D + 10)) := by
    filter_upwards [hstepCK, eventually_ge_atTop 1] with N hN hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact hN.trans (Real.rpow_le_rpow_of_exponent_le hN1' (by unfold CK; linarith))
  filter_upwards [xZ_le_azumaMm_plainN hE2 hs0 hst ht1 hcond hc0 hreg0 hAc hδ0 hδc hε0 hεδ hD hsu
      hut K hK0 hΔ10 (by linarith : 2 * D ≤ 2 * D + 2) (by linarith : 2 * D ≤ 2 * D + 2),
    azumaMm_leN (d := d) hκ0 hE hδ0 hτ₁δ, hstepCK, eventually_ge_atTop 1]
    with N hxZ hMm hΔN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  refine ⟨⟨Nat.one_le_iff_ne_zero.2 (hK0 N),
    hΔN.trans (Real.rpow_le_rpow_of_exponent_le hN1' (by unfold CK; linarith)),
    azumaMm_nonneg (E N) δ τ₁ N, hMm⟩, ?_⟩
  intro ω hω
  obtain ⟨⟨⟨hA, hY⟩, hG⟩, hI⟩ := hω
  set τω := gridTau d (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω with hτω
  have hτK : τω ≤ K N := gridTau_le (E N) D δ τ₁ ε ζCtr τ3 τ57 s u K N ω
  refine ⟨hI.1, fun b => ?_, fun b => (hY b).le, fun j hj => lt_gridTau_imp hj,
    fun j hj => hG ⟨j, by omega⟩, hI.2⟩
  have h1 := hA τω hτK b
  rw [min_self] at h1
  exact h1.le.trans (hxZ τω hτK b)

end GoodEventPlainN2

open scoped Matrix.Norms.L2Operator

set_option maxHeartbeats 4000000 in
-- a long proof; raise the heartbeat limit
/-- **(2.76) uniformly in `u ∈ [s, t]`** from its form `hpt` at each time sequence. The proof
calls `hKb_flowN` (the loop-length-2 kernel bound), which needs an explicit `κ`; every other use
of `hEκ` in the proof is pointwise (`|E N|<2`, via `hE2 N`). The only call site
(`step2_gauss_of_pointwise_plainN`) already carries this `κ`,`κ≤1`. -/
theorem h276_of_pointwise_plainN (d : Dims) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (hpt : ∀ D : ℝ, 0 < D → ∀ u : ∀ N, RBM.TimeIcc s t N, StochDom (P d)
      (fun N (p : ZMod ((band d).L N) × ZMod ((band d).L N)) ω =>
        (sample d).lkErr (E N) N (u N) ω (pmLoop p.1 p.2))
      (fun N p _ => (etaT (E N) (s N) / etaT (E N) (u N)) ^ 4 *
        ((band d).scale (E N) N (u N))⁻¹ ^ 2 * (band d).decayProf N (u N) D p.1 p.2)) :
    ∀ D : ℝ, 0 < D → StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT (E N) (s N) / etaT (E N) p.1) ^ 4 * ((band d).scale (E N) N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  intro D hD0
  -- the net spacing exponent, fixed once `D` is fixed
  set A : ℝ := 4 * D + 40 with hA_def
  have hApos : (0 : ℝ) ≤ A := by rw [hA_def]; linarith
  have hlen : ∀ N, t N - s N ≤ (1 : ℝ) := fun N => by linarith [hs0 N, ht1 N]
  -- `T1`, in the two forms used below
  have hreg1 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) :=
    etaT_inv_le_of_plainN (band d) hE2 ht1 hc0 hAc
  have hreg1' : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ (1 : ℝ) := by
    filter_upwards [hreg1] with N hN; rwa [Real.rpow_one]
  -- the envelope on `K` at loop length `2`, from (2.59)
  have hKb2raw := hKb_flowN (band d) hκ0 hκ1 hEκ ht1 zero_le_one (2 : ℕ) hreg1'
  have he3 : (1 : ℝ) * ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
  have hKb2 : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (t N),
      ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF → 2 ≤ J.length → J.length ≤ 2 →
        ‖(band d).Kval (E N) N w J‖ ≤ (N : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hKb2raw] with N hN w hw J hJ h2 h2'
    have := hN w hw J hJ h2 h2'
    rwa [he3] at this
  -- the four exponent gaps, one per factor of `bnd`, all fixed once `D` is fixed
  have hEtaGap : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) * (N : ℝ) ^ (-A) ≤ (1 / 10) * (N : ℝ) ^ (-1 : ℝ) :=
    eventually_mul_rpow_le_mul_rpow 1 (1 / 10) (by norm_num) (by rw [hA_def]; linarith)
  have hScaleGap : ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) * (N : ℝ) ^ (2 - A / 2) ≤ (1 / 10) * (N : ℝ) ^ (-1 : ℝ) :=
    eventually_mul_rpow_le_mul_rpow 2 (1 / 10) (by norm_num) (by rw [hA_def]; linarith)
  have hDecayGap : ∀ᶠ N : ℕ in atTop,
      Real.sqrt (1 / 2) * (N : ℝ) ^ (1 - A / 4) ≤ (1 / 10) * (N : ℝ) ^ (-D) :=
    eventually_mul_rpow_le_mul_rpow (Real.sqrt (1 / 2)) (1 / 10) (by norm_num)
      (by rw [hA_def]; linarith)
  have hLkGap : ∀ᶠ N : ℕ in atTop,
      (8 : ℝ) * (N : ℝ) ^ (8 - A / 2) ≤ (1 : ℝ) * (N : ℝ) ^ (-(D + 4)) :=
    eventually_mul_rpow_le_mul_rpow 8 1 (by norm_num) (by rw [hA_def]; linarith)
  have hNinv_eq : ∀ N : ℕ, (N : ℝ) ^ (-1 : ℝ) = (N : ℝ)⁻¹ := fun N => by
    rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_one]
  have hκ7 : (11 / 10 : ℝ) ^ 7 ≤ 2 := by norm_num
  -- `hlow`
  have hlow : ∀ᶠ N : ℕ in atTop, ∀ (p : RBM.TimeIcc s t N × (ZMod ((band d).L N) ×
      ZMod ((band d).L N))) (ω : Ω d), (N : ℝ) ^ (-(D + 2)) ≤
        (etaT (E N) (s N) / etaT (E N) (p.1 : ℝ)) ^ 4 * ((band d).scale (E N) N (p.1 : ℝ))⁻¹ ^ 2 *
          (band d).decayProf N (p.1 : ℝ) D p.2.1 p.2.2 := by
    filter_upwards [(band d).dim, eventually_ge_atTop 1] with N hdimN hN1 p ω
    obtain ⟨u, a, b⟩ := p
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hu_lo : s N ≤ (u : ℝ) := u.2.1
    have hu_hi : (u : ℝ) ≤ t N := u.2.2
    have hu_lo0 : (0 : ℝ) ≤ (u : ℝ) := le_trans (hs0 N) hu_lo
    have hu_lt1 : (u : ℝ) < 1 := lt_of_le_of_lt hu_hi (ht1 N)
    have hηu : 0 < etaT (E N) (u : ℝ) := etaT_pos_of_lt_one' (hE2 N) hu_lt1
    have hηs_ge : etaT (E N) (u : ℝ) ≤ etaT (E N) (s N) := etaT_le_of_le (hE2 N) hu_lo
    have hratio1 : (1 : ℝ) ≤ etaT (E N) (s N) / etaT (E N) (u : ℝ) :=
      (one_le_div₀ hηu).mpr hηs_ge
    have hratio4 : (1 : ℝ) ≤ (etaT (E N) (s N) / etaT (E N) (u : ℝ)) ^ 4 :=
      one_le_pow₀ hratio1
    have hscale_pos : 0 < (band d).scale (E N) N (u : ℝ) :=
      (band d).scale_pos' (hE2 N) N hu_lo0 hu_lt1
    have hellle : (band d).ell N (u : ℝ) ≤ ((band d).L N : ℝ) := min_le_right _ _
    have hW0 : (0 : ℝ) ≤ ((band d).W N : ℝ) := Nat.cast_nonneg _
    have hscale_le :
        (band d).scale (E N) N (u : ℝ) ≤
          ((band d).W N : ℝ) * ((band d).L N : ℝ) * etaT (E N) (u : ℝ) := by
      show ((band d).W N : ℝ) * (band d).ell N (u : ℝ) * etaT (E N) (u : ℝ) ≤ _
      have h1 : ((band d).W N : ℝ) * (band d).ell N (u : ℝ)
          ≤ ((band d).W N : ℝ) * ((band d).L N : ℝ) := mul_le_mul_of_nonneg_left hellle hW0
      exact mul_le_mul_of_nonneg_right h1 hηu.le
    have hWLN : ((band d).W N : ℝ) * ((band d).L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdimN.1
    have hscale_leN : (band d).scale (E N) N (u : ℝ) ≤ (N : ℝ) := by
      refine hscale_le.trans ?_
      calc ((band d).W N : ℝ) * ((band d).L N : ℝ) * etaT (E N) (u : ℝ)
          ≤ (N : ℝ) * etaT (E N) (u : ℝ) := mul_le_mul_of_nonneg_right hWLN hηu.le
        _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left (etaT_le_one (hE2 N) hu_lo0) hN0.le
        _ = (N : ℝ) := mul_one _
    have hscaleinv_ge : (N : ℝ)⁻¹ ≤ ((band d).scale (E N) N (u : ℝ))⁻¹ :=
      inv_anti₀ hscale_pos hscale_leN
    have hscaleinv2 : (N : ℝ)⁻¹ ^ 2 ≤ ((band d).scale (E N) N (u : ℝ))⁻¹ ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.2 (Nat.cast_nonneg N)) hscaleinv_ge 2
    have hWNpos : (0 : ℝ) < ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
    have hWleN : ((band d).W N : ℝ) ≤ (N : ℝ) := by
      have hL1 : 1 ≤ (band d).L N := by have := (band d).three_le_L N; omega
      have : (band d).W N ≤ N :=
        le_trans (Nat.le_mul_of_pos_right _ hL1) hdimN.1
      exact_mod_cast this
    have hWD_le : (N : ℝ) ^ (-D) ≤ ((band d).W N : ℝ) ^ (-D) := by
      have hpow_le : ((band d).W N : ℝ) ^ D ≤ (N : ℝ) ^ D :=
        Real.rpow_le_rpow hWNpos.le hWleN hD0.le
      have hpow_pos : (0 : ℝ) < ((band d).W N : ℝ) ^ D := Real.rpow_pos_of_pos hWNpos D
      have := inv_anti₀ hpow_pos hpow_le
      rwa [← Real.rpow_neg hWNpos.le, ← Real.rpow_neg (Nat.cast_nonneg N)] at this
    have hdecay_ge : (N : ℝ) ^ (-D) ≤ (band d).decayProf N (u : ℝ) D a b := by
      have h1 : (0 : ℝ) ≤
          Real.exp (-(((zdist ((band d).L N) (a - b) : ℝ)) / (band d).ell N (u : ℝ)) ^
            ((1 : ℝ) / 2)) := (Real.exp_pos _).le
      show (N : ℝ) ^ (-D) ≤ _ + ((band d).W N : ℝ) ^ (-D)
      linarith [hWD_le]
    have hbase_nonneg : (0 : ℝ) ≤ (etaT (E N) (s N) / etaT (E N) (u : ℝ)) ^ 4 * (N : ℝ)⁻¹ ^ 2 := by
      positivity
    calc (N : ℝ) ^ (-(D + 2))
        = (N : ℝ) ^ (-(2 : ℝ)) * (N : ℝ) ^ (-D) := by
          rw [← Real.rpow_add hN0]; ring_nf
      _ = (N : ℝ)⁻¹ ^ 2 * (N : ℝ) ^ (-D) := by
          rw [show (-(2:ℝ)) = ((-1:ℝ) * 2 : ℝ) from by ring, Real.rpow_mul (Nat.cast_nonneg N),
            hNinv_eq]
          norm_num
      _ ≤ (etaT (E N) (s N) / etaT (E N) (u : ℝ)) ^ 4 * ((band d).scale (E N) N (u : ℝ))⁻¹ ^ 2
            * (band d).decayProf N (u : ℝ) D a b := by
          have h1 : (N:ℝ)⁻¹ ^ 2 * (N:ℝ)^(-D) ≤
              (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4 * (N:ℝ)⁻¹^2 * (N:ℝ)^(-D) := by
            have hX0 : (0:ℝ) ≤ (N:ℝ)⁻¹^2 * (N:ℝ)^(-D) := by positivity
            calc (N:ℝ)⁻¹^2 * (N:ℝ)^(-D) = 1 * ((N:ℝ)⁻¹^2 * (N:ℝ)^(-D)) := (one_mul _).symm
              _ ≤ (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4 * ((N:ℝ)⁻¹^2 * (N:ℝ)^(-D)) :=
                  mul_le_mul_of_nonneg_right hratio4 hX0
              _ = (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4 * (N:ℝ)⁻¹^2 * (N:ℝ)^(-D) := by ring
          refine h1.trans ?_
          have h2 : (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4 * (N:ℝ)⁻¹^2 * (N:ℝ)^(-D)
              ≤ (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4 *
                ((band d).scale (E N) N (u:ℝ))⁻¹^2 * (N:ℝ)^(-D) := by
            have hnn : (0:ℝ) ≤ (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4 := by positivity
            have := mul_le_mul_of_nonneg_left hscaleinv2 hnn
            exact mul_le_mul_of_nonneg_right this (by positivity)
          refine h2.trans ?_
          have hnn2 : (0:ℝ) ≤ (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4 *
              ((band d).scale (E N) N (u:ℝ))⁻¹^2 := by positivity
          exact mul_le_mul_of_nonneg_left hdecay_ge hnn2
  -- `hclose`
  have hclose : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)},
      ∀ u u' : RBM.TimeIcc s t N, |(u : ℝ) - (u' : ℝ)| ≤ (N : ℝ) ^ (-A) →
      ∀ v : ZMod ((band d).L N) × ZMod ((band d).L N),
        (sample d).lkErr (E N) N (u : ℝ) ω (pmLoop v.1 v.2) ≤
          (sample d).lkErr (E N) N (u' : ℝ) ω (pmLoop v.1 v.2) + (N : ℝ) ^ (-((D + 2) + 2)) ∧
        (etaT (E N) (s N) / etaT (E N) (u' : ℝ)) ^ 4 * ((band d).scale (E N) N (u' : ℝ))⁻¹ ^ 2 *
            (band d).decayProf N (u' : ℝ) D v.1 v.2 ≤
          2 * ((etaT (E N) (s N) / etaT (E N) (u : ℝ)) ^ 4 *
            ((band d).scale (E N) N (u : ℝ))⁻¹ ^ 2 *
            (band d).decayProf N (u : ℝ) D v.1 v.2) := by
    filter_upwards [hreg1, hKb2, (band d).dim, eventually_ge_atTop 1,
        hEtaGap, hScaleGap, hDecayGap, hLkGap] with
      N hreg1N hKb2N hdimN hN1 hEtaGapN hScaleGapN hDecayGapN hLkGapN ω hωΞ u u' huu' v
    obtain ⟨a, b⟩ := v
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hu_lo : s N ≤ (u : ℝ) := u.2.1
    have hu_hi : (u : ℝ) ≤ t N := u.2.2
    have hu'_lo : s N ≤ (u' : ℝ) := u'.2.1
    have hu'_hi : (u' : ℝ) ≤ t N := u'.2.2
    have hu_lo0 : (0 : ℝ) ≤ (u : ℝ) := le_trans (hs0 N) hu_lo
    have hu'_lo0 : (0 : ℝ) ≤ (u' : ℝ) := le_trans (hs0 N) hu'_lo
    have hu_lt1 : (u : ℝ) < 1 := lt_of_le_of_lt hu_hi (ht1 N)
    have hu'_lt1 : (u' : ℝ) < 1 := lt_of_le_of_lt hu'_hi (ht1 N)
    have hu_Icc0T : (u : ℝ) ∈ Set.Icc (0 : ℝ) (t N) := ⟨hu_lo0, hu_hi⟩
    have hu'_Icc0T : (u' : ℝ) ∈ Set.Icc (0 : ℝ) (t N) := ⟨hu'_lo0, hu'_hi⟩
    have hηt : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE2 N) (ht1 N)
    have hηu : 0 < etaT (E N) (u : ℝ) := etaT_pos_of_lt_one' (hE2 N) hu_lt1
    have hηu' : 0 < etaT (E N) (u' : ℝ) := etaT_pos_of_lt_one' (hE2 N) hu'_lt1
    have hηtlow : (N : ℝ)⁻¹ ≤ etaT (E N) (t N) := by
      have := inv_anti₀ (inv_pos.2 hηt) hreg1N
      rwa [inv_inv] at this
    have hηu_ge_ηt : etaT (E N) (t N) ≤ etaT (E N) (u : ℝ) := etaT_le_of_le (hE2 N) hu_hi
    have hηu'_ge_ηt : etaT (E N) (t N) ≤ etaT (E N) (u' : ℝ) := etaT_le_of_le (hE2 N) hu'_hi
    have hηu_ge : (N : ℝ)⁻¹ ≤ etaT (E N) (u : ℝ) := hηtlow.trans hηu_ge_ηt
    have hηu'_ge : (N : ℝ)⁻¹ ≤ etaT (E N) (u' : ℝ) := hηtlow.trans hηu'_ge_ηt
    have h1t : (0 : ℝ) < 1 - t N := by linarith [ht1 N]
    have hTinv : (1 - t N)⁻¹ ≤ (N : ℝ) := by
      have hle : etaT (E N) (t N) ≤ 1 - t N := etaT_le (hE2 N).le (ht1 N).le
      exact (inv_anti₀ hηt hle).trans hreg1N
    have hWNpos : (0 : ℝ) < ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
    have hLpos1 : 1 ≤ (band d).L N := by have := (band d).three_le_L N; omega
    have hWleN : ((band d).W N : ℝ) ≤ (N : ℝ) := by
      have hle : (band d).W N ≤ N := le_trans (Nat.le_mul_of_pos_right _ hLpos1) hdimN.1
      exact_mod_cast hle
    have hLleN : ((band d).L N : ℝ) ≤ (N : ℝ) := by
      have hle : (band d).L N ≤ N :=
        le_trans (Nat.le_mul_of_pos_left _ ((band d).W_pos N)) hdimN.1
      exact_mod_cast hle
    have hsqrt_le : Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ (N : ℝ) ^ (-A / 2) :=
      sqrt_abs_sub_le_rpow huu'
    -- generic rpow-combination helpers, at this fixed `N`
    have hpow_add1 : ∀ e : ℝ, (N : ℝ) * (N : ℝ) ^ e = (N : ℝ) ^ (1 + e) := fun e => by
      have h1 : (N : ℝ) ^ (1 + e) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ e := Real.rpow_add hN0 1 e
      rw [h1, Real.rpow_one]
    have hpow_add2 : ∀ e : ℝ, (N : ℝ) * ((N : ℝ) * (N : ℝ) ^ e) = (N : ℝ) ^ (2 + e) := fun e => by
      have h1 : (N : ℝ) ^ (1 + (1 + e)) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 + e) :=
        Real.rpow_add hN0 1 (1 + e)
      rw [show (2 + e : ℝ) = 1 + (1 + e) from by ring, h1, Real.rpow_one, hpow_add1 e]
    have hpow_nat_rpow : ∀ (k : ℕ) (e : ℝ), (N : ℝ) ^ k * (N : ℝ) ^ e = (N : ℝ) ^ ((k : ℝ) + e) :=
      fun k e => by rw [← Real.rpow_natCast (N : ℝ) k, ← Real.rpow_add hN0]
    ------------------------------------------------------------------
    -- (a) the η factor
    ------------------------------------------------------------------
    have hη_close : |etaT (E N) (u : ℝ) - etaT (E N) (u' : ℝ)| ≤ (N : ℝ) ^ (-A) :=
      (abs_etaT_sub_le (hE2 N).le _ _).trans huu'
    have hη_ratio : etaT (E N) (u : ℝ) ≤ (11 / 10) * etaT (E N) (u' : ℝ) := by
      have h1 := (abs_le.mp hη_close).2
      have h2 : (N : ℝ) ^ (-A) ≤ (1 / 10) * (N : ℝ) ⁻¹ := by
        rw [← hNinv_eq]
        have := hEtaGapN
        linarith [this]
      linarith [h1, h2, hηu'_ge]
    ------------------------------------------------------------------
    -- (b) the scale factor
    ------------------------------------------------------------------
    have hscale_pos : 0 < (band d).scale (E N) N (u : ℝ) :=
      (band d).scale_pos' (hE2 N) N hu_lo0 hu_lt1
    have hscale'_pos : 0 < (band d).scale (E N) N (u' : ℝ) :=
      (band d).scale_pos' (hE2 N) N hu'_lo0 hu'_lt1
    have hscale_ge_eta : etaT (E N) (u' : ℝ) ≤ (band d).scale (E N) N (u' : ℝ) := by
      have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
      have hell1 : (1 : ℝ) ≤ (band d).ell N (u' : ℝ) :=
        one_le_ellHat _ ((band d).three_le_L N) hu'_lo0 hu'_lt1
      show etaT (E N) (u' : ℝ) ≤ ((band d).W N : ℝ) * (band d).ell N (u' : ℝ) * etaT (E N) (u' : ℝ)
      have hη0 : (0:ℝ) ≤ etaT (E N) (u' : ℝ) := hηu'.le
      calc etaT (E N) (u' : ℝ) = 1 * 1 * etaT (E N) (u' : ℝ) := by ring
        _ ≤ ((band d).W N : ℝ) * (band d).ell N (u' : ℝ) * etaT (E N) (u' : ℝ) := by gcongr
    have hscale'_ge : (N : ℝ)⁻¹ ≤ (band d).scale (E N) N (u' : ℝ) := hηu'_ge.trans hscale_ge_eta
    have hscale_close : |(band d).scale (E N) N (u : ℝ) - (band d).scale (E N) N (u' : ℝ)| ≤
        ((band d).W N : ℝ) * ((1 - t N)⁻¹ + ((band d).L N : ℝ)) *
          Real.sqrt |(u : ℝ) - (u' : ℝ)| :=
      abs_scale_sub_le (hE2 N) N (ht1 N) hu_Icc0T hu'_Icc0T
    have hscale_close' : |(band d).scale (E N) N (u : ℝ) - (band d).scale (E N) N (u' : ℝ)| ≤
        (2 : ℝ) * (N : ℝ) ^ (2 - A / 2) := by
      have hpoly : ((band d).W N : ℝ) * ((1 - t N)⁻¹ + ((band d).L N : ℝ)) ≤
          (N : ℝ) * (2 * (N : ℝ)) := by
        have h2 : (1 - t N)⁻¹ + ((band d).L N : ℝ) ≤ 2 * (N : ℝ) := by linarith [hTinv, hLleN]
        have hnn : (0:ℝ) ≤ (1 - t N)⁻¹ + ((band d).L N : ℝ) :=
          add_nonneg (inv_pos.2 h1t).le (Nat.cast_nonneg _)
        exact mul_le_mul hWleN h2 hnn hN0.le
      calc |(band d).scale (E N) N (u : ℝ) - (band d).scale (E N) N (u' : ℝ)|
          ≤ ((band d).W N : ℝ) * ((1 - t N)⁻¹ + ((band d).L N : ℝ))
              * Real.sqrt |(u : ℝ) - (u' : ℝ)| := hscale_close
        _ ≤ (N:ℝ) * (2 * (N:ℝ)) * Real.sqrt |(u : ℝ) - (u' : ℝ)| :=
            mul_le_mul_of_nonneg_right hpoly (Real.sqrt_nonneg _)
        _ ≤ (N:ℝ) * (2 * (N:ℝ)) * (N : ℝ) ^ (-A / 2) :=
            mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
        _ = 2 * (N:ℝ) ^ (2 - A / 2) := by
            rw [show (N:ℝ) * (2 * (N:ℝ)) * (N : ℝ) ^ (-A / 2)
                  = 2 * ((N:ℝ) * ((N:ℝ) * (N : ℝ) ^ (-A / 2))) from by ring,
              hpow_add2 (-A / 2)]
            congr 2
            ring
    have hscale_ratio : (band d).scale (E N) N (u : ℝ) ≤
        (11 / 10) * (band d).scale (E N) N (u' : ℝ) := by
      have h1 := (abs_le.mp hscale_close').2
      have h2 : (2 : ℝ) * (N:ℝ) ^ (2 - A / 2) ≤ (1 / 10) * (N : ℝ)⁻¹ := by
        rw [← hNinv_eq]; exact hScaleGapN
      linarith [h1, h2, hscale'_ge]
    have hscaleinv_ratio :
        ((band d).scale (E N) N (u' : ℝ))⁻¹ ≤ (11 / 10) * ((band d).scale (E N) N (u : ℝ))⁻¹ :=
      inv_le_const_mul_inv_of_le_const_mul hscale_pos hscale'_pos hscale_ratio
    have hscaleinv2 : ((band d).scale (E N) N (u' : ℝ))⁻¹ ^ 2 ≤
        (11 / 10) ^ 2 * ((band d).scale (E N) N (u : ℝ))⁻¹ ^ 2 := by
      have h1 := pow_le_pow_left₀ (inv_nonneg.2 hscale'_pos.le) hscaleinv_ratio 2
      calc ((band d).scale (E N) N (u' : ℝ))⁻¹ ^ 2
          ≤ ((11 / 10) * ((band d).scale (E N) N (u : ℝ))⁻¹) ^ 2 := h1
        _ = (11 / 10) ^ 2 * ((band d).scale (E N) N (u : ℝ))⁻¹ ^ 2 := by ring
    ------------------------------------------------------------------
    -- (c) the η ratio to the 4th power
    ------------------------------------------------------------------
    have hηs_pos : 0 < etaT (E N) (s N) := lt_of_lt_of_le hηu (etaT_le_of_le (hE2 N) hu_lo)
    have hη4 : (etaT (E N) (s N) / etaT (E N) (u' : ℝ)) ^ 4 ≤
        (11 / 10) ^ 4 * (etaT (E N) (s N) / etaT (E N) (u : ℝ)) ^ 4 := by
      have heq : etaT (E N) (s N) / etaT (E N) (u' : ℝ) =
          (etaT (E N) (s N) / etaT (E N) (u : ℝ)) * (etaT (E N) (u : ℝ) / etaT (E N) (u' : ℝ)) := by
        field_simp
      rw [heq, mul_pow]
      have hratio_le : etaT (E N) (u : ℝ) / etaT (E N) (u' : ℝ) ≤ 11 / 10 := by
        rw [div_le_iff₀ hηu']; linarith [hη_ratio]
      have hratio_nn : (0 : ℝ) ≤ etaT (E N) (u : ℝ) / etaT (E N) (u' : ℝ) := by positivity
      have hpow_le : (etaT (E N) (u : ℝ) / etaT (E N) (u' : ℝ)) ^ 4 ≤ (11 / 10) ^ 4 :=
        pow_le_pow_left₀ hratio_nn hratio_le 4
      have hbase_nn : (0 : ℝ) ≤ (etaT (E N) (s N) / etaT (E N) (u : ℝ)) ^ 4 := by positivity
      calc (etaT (E N) (s N) / etaT (E N) (u : ℝ)) ^ 4 *
            (etaT (E N) (u : ℝ) / etaT (E N) (u' : ℝ)) ^ 4
          ≤ (etaT (E N) (s N) / etaT (E N) (u : ℝ)) ^ 4 * (11 / 10) ^ 4 :=
            mul_le_mul_of_nonneg_left hpow_le hbase_nn
        _ = (11 / 10) ^ 4 * (etaT (E N) (s N) / etaT (E N) (u : ℝ)) ^ 4 := by ring
    ------------------------------------------------------------------
    -- (d) the decayProf ratio
    ------------------------------------------------------------------
    set z : ℝ := (zdist ((band d).L N) (a - b) : ℝ) with hz_def
    have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg _
    have hzLe : 2 * z ≤ ((band d).L N : ℝ) := by
      rw [hz_def]
      exact_mod_cast two_mul_zdist_le ((band d).L N) (a - b)
    have hellu1 : (1 : ℝ) ≤ (band d).ell N (u : ℝ) :=
      one_le_ellHat _ ((band d).three_le_L N) hu_lo0 hu_lt1
    have hellu'1 : (1 : ℝ) ≤ (band d).ell N (u' : ℝ) :=
      one_le_ellHat _ ((band d).three_le_L N) hu'_lo0 hu'_lt1
    have hellclose : |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)| ≤
        (1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)| := by
      show |ellHat ((band d).L N) ((u : ℝ) : ℂ) - ellHat ((band d).L N) ((u' : ℝ) : ℂ)| ≤ _
      exact abs_ellHat_sub_le _ (ht1 N) hu_Icc0T hu'_Icc0T
    have hprod_le : z * |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)| ≤
        (1 / 2) * (N : ℝ) ^ (2 - A / 2) := by
      have h1 : z * |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)| ≤
          (((band d).L N : ℝ) / 2) * ((1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)|) := by
        calc z * |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)|
            ≤ z * ((1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)|) :=
              mul_le_mul_of_nonneg_left hellclose hz0
          _ ≤ (((band d).L N : ℝ) / 2) * ((1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)|) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith [hzLe]
      refine h1.trans ?_
      have h2 : (((band d).L N : ℝ) / 2) * ((1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)|) ≤
          ((N : ℝ) / 2) * ((N : ℝ) * (N : ℝ) ^ (-A / 2)) := by
        have h3 : (1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ (N : ℝ) * (N : ℝ) ^ (-A / 2) :=
          mul_le_mul hTinv hsqrt_le (Real.sqrt_nonneg _) hN0.le
        exact mul_le_mul (by linarith [hLleN]) h3 (by positivity) (by positivity)
      refine h2.trans (le_of_eq ?_)
      rw [show (N : ℝ) / 2 * ((N : ℝ) * (N : ℝ) ^ (-A / 2))
            = (1 / 2) * ((N : ℝ) * ((N : ℝ) * (N : ℝ) ^ (-A / 2))) from by ring,
        hpow_add2 (-A / 2)]
      congr 2
      ring
    have hg_diff : |Real.sqrt (z / (band d).ell N (u : ℝ)) -
        Real.sqrt (z / (band d).ell N (u' : ℝ))| ≤ Real.sqrt (1 / 2) * (N : ℝ) ^ (1 - A / 4) := by
      have hstep1 : |Real.sqrt (z / (band d).ell N (u : ℝ)) -
          Real.sqrt (z / (band d).ell N (u' : ℝ))| =
          Real.sqrt z * |1 / Real.sqrt ((band d).ell N (u : ℝ)) -
            1 / Real.sqrt ((band d).ell N (u' : ℝ))| := by
        have heq : Real.sqrt (z / (band d).ell N (u : ℝ)) -
            Real.sqrt (z / (band d).ell N (u' : ℝ)) =
            Real.sqrt z * (1 / Real.sqrt ((band d).ell N (u : ℝ)) -
              1 / Real.sqrt ((band d).ell N (u' : ℝ))) := by
          rw [Real.sqrt_div hz0, Real.sqrt_div hz0, mul_sub, mul_one_div, mul_one_div]
        rw [heq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg z)]
      have hden1 : (1 : ℝ) ≤ Real.sqrt ((band d).ell N (u : ℝ)) :=
        Real.one_le_sqrt.2 (by linarith [hellu1])
      have hden2 : (1 : ℝ) ≤ Real.sqrt ((band d).ell N (u' : ℝ)) :=
        Real.one_le_sqrt.2 (by linarith [hellu'1])
      have hstep2 : |1 / Real.sqrt ((band d).ell N (u : ℝ)) -
          1 / Real.sqrt ((band d).ell N (u' : ℝ))| ≤
          |Real.sqrt ((band d).ell N (u' : ℝ)) - Real.sqrt ((band d).ell N (u : ℝ))| := by
        have heq : (1:ℝ) / Real.sqrt ((band d).ell N (u : ℝ)) -
            1 / Real.sqrt ((band d).ell N (u' : ℝ)) =
            (Real.sqrt ((band d).ell N (u' : ℝ)) - Real.sqrt ((band d).ell N (u : ℝ))) /
              (Real.sqrt ((band d).ell N (u : ℝ)) * Real.sqrt ((band d).ell N (u' : ℝ))) := by
          field_simp
        rw [heq, abs_div]
        have hd1 : (1:ℝ) ≤ Real.sqrt ((band d).ell N (u : ℝ)) *
            Real.sqrt ((band d).ell N (u' : ℝ)) := by
          nlinarith [hden1, hden2]
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt ((band d).ell N (u : ℝ)) *
          Real.sqrt ((band d).ell N (u' : ℝ)))]
        rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.sqrt ((band d).ell N (u : ℝ)) *
          Real.sqrt ((band d).ell N (u' : ℝ)))]
        nlinarith [abs_nonneg (Real.sqrt ((band d).ell N (u' : ℝ)) -
          Real.sqrt ((band d).ell N (u : ℝ))), hd1]
      have hstep3 : |Real.sqrt ((band d).ell N (u' : ℝ)) - Real.sqrt ((band d).ell N (u : ℝ))| ≤
          Real.sqrt |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)| := by
        have := abs_sqrt_sub_sqrt_le ((band d).ell N (u' : ℝ)) ((band d).ell N (u : ℝ))
        rwa [abs_sub_comm ((band d).ell N (u' : ℝ)) ((band d).ell N (u : ℝ))] at this
      have hstep4 : Real.sqrt z * |1 / Real.sqrt ((band d).ell N (u : ℝ)) -
          1 / Real.sqrt ((band d).ell N (u' : ℝ))| ≤
          Real.sqrt z * Real.sqrt |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)| :=
        mul_le_mul_of_nonneg_left (hstep2.trans hstep3) (Real.sqrt_nonneg _)
      refine hstep1.le.trans (hstep4.trans ?_)
      rw [← Real.sqrt_mul hz0]
      calc Real.sqrt (z * |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)|)
          ≤ Real.sqrt ((1 / 2) * (N : ℝ) ^ (2 - A / 2)) := Real.sqrt_le_sqrt hprod_le
        _ = Real.sqrt (1 / 2) * (N : ℝ) ^ (1 - A / 4) := by
            rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/2)]
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
            congr 1
            ring
    have hdecay_ratio : (band d).decayProf N (u' : ℝ) D a b ≤
        (11 / 10) * (band d).decayProf N (u : ℝ) D a b := by
      have hWD_le : (N : ℝ) ^ (-D) ≤ ((band d).W N : ℝ) ^ (-D) := by
        have hpow_le : ((band d).W N : ℝ) ^ D ≤ (N : ℝ) ^ D :=
          Real.rpow_le_rpow hWNpos.le hWleN hD0.le
        have hpow_pos : (0 : ℝ) < ((band d).W N : ℝ) ^ D := Real.rpow_pos_of_pos hWNpos D
        have := inv_anti₀ hpow_pos hpow_le
        rwa [← Real.rpow_neg hWNpos.le, ← Real.rpow_neg (Nat.cast_nonneg N)] at this
      have hgap := hDecayGapN
      have hexp_diff : Real.exp (-(Real.sqrt (z / (band d).ell N (u' : ℝ)))) ≤
          Real.exp (-(Real.sqrt (z / (band d).ell N (u : ℝ)))) +
            Real.sqrt (1 / 2) * (N : ℝ) ^ (1 - A / 4) := by
        have hexpb : |Real.exp (-(Real.sqrt (z / (band d).ell N (u : ℝ)))) -
            Real.exp (-(Real.sqrt (z / (band d).ell N (u' : ℝ))))| ≤
            Real.sqrt (1 / 2) * (N : ℝ) ^ (1 - A / 4) :=
          (abs_exp_neg_sub_exp_neg_le (Real.sqrt_nonneg (z / (band d).ell N (u : ℝ)))
            (Real.sqrt_nonneg (z / (band d).ell N (u' : ℝ)))).trans hg_diff
        have := (abs_le.mp hexpb).1
        linarith [this]
      have hexp_nonneg : (0:ℝ) ≤ Real.exp (-(Real.sqrt (z / (band d).ell N (u : ℝ)))) :=
        (Real.exp_pos _).le
      have hWD_nonneg : (0:ℝ) ≤ ((band d).W N : ℝ) ^ (-D) := by positivity
      show Real.exp (-(z / (band d).ell N (u' : ℝ)) ^ ((1:ℝ)/2)) + ((band d).W N : ℝ) ^ (-D) ≤
        (11/10) * (Real.exp (-(z / (band d).ell N (u : ℝ)) ^ ((1:ℝ)/2))
          + ((band d).W N : ℝ) ^ (-D))
      rw [show (z / (band d).ell N (u' : ℝ)) ^ ((1:ℝ)/2) = Real.sqrt (z / (band d).ell N (u' : ℝ))
            from (Real.sqrt_eq_rpow _).symm,
          show (z / (band d).ell N (u : ℝ)) ^ ((1:ℝ)/2) = Real.sqrt (z / (band d).ell N (u : ℝ))
            from (Real.sqrt_eq_rpow _).symm]
      nlinarith [hexp_diff, hgap, hWD_le, hexp_nonneg, hWD_nonneg]
    ------------------------------------------------------------------
    -- (e) the lkErr additive bound
    ------------------------------------------------------------------
    have hlk_bound : (sample d).lkErr (E N) N (u : ℝ) ω (pmLoop a b) ≤
        (sample d).lkErr (E N) N (u' : ℝ) ω (pmLoop a b) + (N : ℝ) ^ (-((D + 2) + 2)) := by
      rw [lkErr_eq_norm_lkT, lkErr_eq_norm_lkT]
      have hKbBk : ∀ w ∈ Set.Icc (0 : ℝ) (t N), ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
          2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval (E N) N w J‖ ≤ (N : ℝ) ^ (3 : ℝ) := hKb2N
      have hmod := norm_lkT_flow_sub_le d N (hE2 N) (ht1 N) hu_Icc0T hu'_Icc0T ω
        (n := 2) (by norm_num) (![true, false], (![a, b] : LoopArg ((band d).L N) 2))
        (Bk := (N : ℝ) ^ (3 : ℝ)) (by positivity) hKbBk
      have hnormsub := norm_sub_norm_le
        (SumZeroDyn.lkT (sample d) (E N) N (u : ℝ) ω (![true, false])
          (![a, b] : LoopArg ((band d).L N) 2))
        (SumZeroDyn.lkT (sample d) (E N) N (u' : ℝ) ω (![true, false])
          (![a, b] : LoopArg ((band d).L N) 2))
      have hXle : ‖Xmat d N ω‖ + 1 ≤ 2 * (N : ℝ) := by linarith [hωΞ]
      have hηTinv_pos : (0:ℝ) ≤ (etaT (E N) (t N))⁻¹ := by positivity
      have hConst_le : (2 : ℝ) * ((etaT (E N) (t N))⁻¹ * (etaT (E N) (t N))⁻¹ *
            (‖Xmat d N ω‖ + 1) * (etaT (E N) (t N))⁻¹ ^ (2 - 1)) +
          ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * ((N : ℝ) ^ (3 : ℝ)) ^ 2 ≤
          (8 : ℝ) * (N : ℝ) ^ (8 : ℕ) := by
        have e1 : (etaT (E N) (t N))⁻¹ ^ (2 - 1) = (etaT (E N) (t N))⁻¹ := by norm_num
        have e3 : ((N:ℝ) ^ (3 : ℝ)) ^ 2 = (N:ℝ) ^ (6 : ℕ) := by
          rw [← Real.rpow_natCast ((N:ℝ) ^ (3:ℝ)) 2, ← Real.rpow_mul hN0.le]
          norm_num
        rw [e1, e3]
        have h1 : (etaT (E N) (t N))⁻¹ * (etaT (E N) (t N))⁻¹ * (‖Xmat d N ω‖ + 1) *
            (etaT (E N) (t N))⁻¹ ≤ (N:ℝ) ^ (4:ℕ) * 2 := by
          have hh : (etaT (E N) (t N))⁻¹ * (etaT (E N) (t N))⁻¹ * (‖Xmat d N ω‖ + 1) *
              (etaT (E N) (t N))⁻¹ ≤ (N:ℝ) * (N:ℝ) * (2*(N:ℝ)) * (N:ℝ) :=
            mul_le_mul (mul_le_mul (mul_le_mul hreg1N hreg1N hηTinv_pos hN0.le) hXle
              (by positivity) (by positivity)) hreg1N hηTinv_pos (by positivity)
          refine hh.trans (le_of_eq ?_)
          ring
        have h2 : ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * (N:ℝ) ^ (6:ℕ) ≤
            (N:ℝ) ^ (8:ℕ) * 4 := by
          have hh : ((band d).W N : ℝ) * ((band d).L N : ℝ) ≤ (N:ℝ) * (N:ℝ) :=
            mul_le_mul hWleN hLleN (Nat.cast_nonneg _) hN0.le
          have hnn : (0:ℝ) ≤ (2:ℝ)^2 * (N:ℝ)^(6:ℕ) := by positivity
          have hstep : ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * (N:ℝ)^(6:ℕ)
              ≤ ((N:ℝ)*(N:ℝ)) * ((2:ℝ)^2 * (N:ℝ)^(6:ℕ)) := by
            calc ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * (N:ℝ)^(6:ℕ)
                = (((band d).W N : ℝ) * ((band d).L N:ℝ)) * ((2:ℝ)^2 * (N:ℝ)^(6:ℕ)) := by ring
              _ ≤ ((N:ℝ)*(N:ℝ)) * ((2:ℝ)^2 * (N:ℝ)^(6:ℕ)) := mul_le_mul_of_nonneg_right hh hnn
          refine hstep.trans (le_of_eq ?_)
          ring
        have h5 : (N:ℝ) ^ (4:ℕ) ≤ (N:ℝ) ^ (8:ℕ) := by
          have h2' : (1:ℝ) ≤ (N:ℝ)^(4:ℕ) := one_le_pow₀ (by linarith [hN1'] : (1:ℝ) ≤ (N:ℝ))
          have heq : (N:ℝ)^(8:ℕ) = (N:ℝ)^(4:ℕ) * (N:ℝ)^(4:ℕ) := by ring
          rw [heq]
          calc (N:ℝ)^(4:ℕ) = (N:ℝ)^(4:ℕ) * 1 := (mul_one _).symm
            _ ≤ (N:ℝ)^(4:ℕ) * (N:ℝ)^(4:ℕ) := mul_le_mul_of_nonneg_left h2' (by positivity)
        nlinarith [h1, h2, h5]
      have hmod' : ‖SumZeroDyn.lkT (sample d) (E N) N (u : ℝ) ω (![true, false])
            (![a, b] : LoopArg ((band d).L N) 2) -
          SumZeroDyn.lkT (sample d) (E N) N (u' : ℝ) ω (![true, false])
            (![a, b] : LoopArg ((band d).L N) 2)‖ ≤
          (8 : ℝ) * (N : ℝ) ^ (8 : ℕ) * Real.sqrt |(u : ℝ) - (u' : ℝ)| :=
        hmod.trans (mul_le_mul_of_nonneg_right hConst_le (Real.sqrt_nonneg _))
      have hfinal : (8 : ℝ) * (N : ℝ) ^ (8 : ℕ) * Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤
          (N : ℝ) ^ (-((D + 2) + 2)) := by
        refine (mul_le_mul_of_nonneg_left hsqrt_le (by positivity)).trans ?_
        rw [mul_assoc, hpow_nat_rpow 8 (-A / 2)]
        have := hLkGapN
        have heq : (8:ℝ) - A/2 = ((8:ℕ):ℝ) + (-A/2) := by push_cast; ring
        rw [← heq]
        have heq2 : -((D + 2) + 2) = -(D + 4) := by ring
        rw [heq2]
        linarith [this]
      linarith [hnormsub, hmod', hfinal]
    have hbnd_nonneg : (0:ℝ) ≤ (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4 *
        ((band d).scale (E N) N (u:ℝ))⁻¹^2 * (band d).decayProf N (u:ℝ) D a b := by
      have h3 : (0:ℝ) ≤ (band d).decayProf N (u:ℝ) D a b := by
        unfold Band.decayProf; positivity
      positivity
    have hstep1 : (etaT (E N) (s N)/etaT (E N) (u':ℝ))^4 *
        ((band d).scale (E N) N (u':ℝ))⁻¹^2 ≤
        ((11/10)^4 * (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4) *
          ((11/10)^2 * ((band d).scale (E N) N (u:ℝ))⁻¹^2) := by
      have hB_nn : (0:ℝ) ≤ (11/10)^4 * (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4 := by positivity
      exact mul_le_mul hη4 hscaleinv2 (by positivity) hB_nn
    have hstep2 : (etaT (E N) (s N)/etaT (E N) (u':ℝ))^4 *
        ((band d).scale (E N) N (u':ℝ))⁻¹^2 *
        (band d).decayProf N (u':ℝ) D a b ≤
        (((11/10)^4 * (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4) *
            ((11/10)^2 * ((band d).scale (E N) N (u:ℝ))⁻¹^2)) *
          ((11/10) * (band d).decayProf N (u:ℝ) D a b) := by
      have hC_nn : (0:ℝ) ≤ (band d).decayProf N (u':ℝ) D a b := by
        unfold Band.decayProf; positivity
      have hD_nn : (0:ℝ) ≤ ((11/10)^4 * (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4) *
          ((11/10)^2 * ((band d).scale (E N) N (u:ℝ))⁻¹^2) := by positivity
      exact mul_le_mul hstep1 hdecay_ratio hC_nn hD_nn
    have heq : (((11/10)^4 * (etaT (E N) (s N)/etaT (E N) (u:ℝ))^4) *
          ((11/10)^2 * ((band d).scale (E N) N (u:ℝ))⁻¹^2)) *
        ((11/10) * (band d).decayProf N (u:ℝ) D a b)
      = (11/10)^7 * ((etaT (E N) (s N)/etaT (E N) (u:ℝ))^4 *
          ((band d).scale (E N) N (u:ℝ))⁻¹^2 *
          (band d).decayProf N (u:ℝ) D a b) := by ring
    refine ⟨hlk_bound, hstep2.trans (le_of_eq heq |>.trans ?_)⟩
    exact mul_le_mul_of_nonneg_right hκ7 hbnd_nonneg
  exact netLift_of_relaxed
    (ξ := fun N (p : RBM.TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
      (sample d).lkErr (E N) N (p.1 : ℝ) ω (pmLoop p.2.1 p.2.2))
    (ζ := fun N p (_ : Ω d) => (etaT (E N) (s N) / etaT (E N) (p.1 : ℝ)) ^ 4 *
      ((band d).scale (E N) N (p.1 : ℝ))⁻¹ ^ 2 * (band d).decayProf N (p.1 : ℝ) D p.2.1 p.2.2)
    (ξ' := fun N (p : RBM.TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
      (sample d).lkErr (E N) N (p.1 : ℝ) ω (pmLoop p.2.1 p.2.2))
    (ζ' := fun N p (_ : Ω d) => (etaT (E N) (s N) / etaT (E N) (p.1 : ℝ)) ^ 4 *
      ((band d).scale (E N) N (p.1 : ℝ))⁻¹ ^ 2 * (band d).decayProf N (p.1 : ℝ) D p.2.1 p.2.2)
    hst one_pos hlen hApos (hpt D hD0) (highProb_norm_Xmat_le d) hlow hclose (hpt D hD0)

section DriftScalarsN

open Real Finset RBM RBM.Step2FarInputs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Scalar facts for the drift bound**: eventually `1 ≤ N`, `8 ≤ W`, `L ≤ W`, `N ≤ W²`,
`2D² ≤ log W`, and for `u ∈ [s, t]`, `N^{2ε} thr(u) ≤ W ℓ_u η_u` and
`L W^{-D/2} ≤ ℓ_u (W ℓ_u η_u)^{-1}`. -/
theorem drift_point_le_heG_scalars_plainN (B : Band Ω) {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in Filter.atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N))
    {δ ε D : ℝ} (hδ0 : 0 ≤ δ) (hδc : δ ≤ c / 90) (hεδ : 2 * ε ≤ δ) (hD : 4 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, (1 : ℝ) ≤ N ∧ 8 ≤ (B.W N : ℝ) ∧ (B.L N : ℝ) ≤ B.W N ∧
      (N : ℝ) ≤ (B.W N : ℝ) ^ 2 ∧ 2 * D ^ 2 ≤ Real.log (B.W N : ℝ) ∧
      ∀ u : ℝ, s N ≤ u → u ≤ t N →
        (N : ℝ) ^ (2 * ε) * Step2.thr (E N) s δ N u ≤ B.scale (E N) N u ∧
        (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D)) ≤ B.ell N u * (B.scale (E N) N u)⁻¹ := by
  filter_upwards [Filter.eventually_ge_atTop 1, (Step2.tendsto_W B).eventually_ge_atTop 8,
    B.dim, Step2.eventually_le_W_sq B,
    (Real.tendsto_log_atTop.comp (Step2.tendsto_W B)).eventually_ge_atTop (2 * D ^ 2), hreg0,
    hAc] with N hN1 hW8 hdim hNW hlog hregN hAcN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hW1 : (1 : ℝ) ≤ B.W N := by linarith
  have hLW : (B.L N : ℝ) ≤ B.W N := by
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
    nlinarith
  refine ⟨hN1', hW8, hLW, hNW, hlog, fun u hsu hut => ?_⟩
  have hu1 : u < 1 := lt_of_le_of_lt hut (ht1 N)
  have hu0 : 0 ≤ u := (hs0 N).trans hsu
  have hs1 : s N < 1 := lt_of_le_of_lt hsu hu1
  have hm0 : 0 < (mE (E N)).im := mE_im_pos (hE N)
  have hm1 : (mE (E N)).im ≤ 1 := mE_im_le_one (hE N)
  have ha : 0 < 1 - u := by linarith
  have ht0 : 0 < 1 - t N := by linarith [ht1 N]
  have hc0' : 0 < 1 - s N := by linarith
  refine ⟨?_, ?_⟩
  · -- `N^{2ε} thr(u) ≤ x² R_u⁴ ≤ A_u`: `(x² R_u⁴)^{45} = x^{90} (R_u^{30})⁶ ≤ A_u⁷ ≤ A_u^{45}`
    have hx1 : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1' hδ0
    have hNε : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hN1' hεδ
    have hRu : etaT (E N) (s N) / etaT (E N) u = (1 - s N) / (1 - u) :=
      Step2.etaT_ratio (hE N) _ _
    have hRt : etaT (E N) (s N) / etaT (E N) (t N) = (1 - s N) / (1 - t N) :=
      Step2.etaT_ratio (hE N) _ _
    have hRu1 : 1 ≤ (1 - s N) / (1 - u) := by rw [le_div_iff₀ ha]; linarith
    have hRut : (1 - s N) / (1 - u) ≤ (1 - s N) / (1 - t N) :=
      div_le_div_of_nonneg_left hc0'.le ht0 (by linarith)
    have hscale : B.scale (E N) N (t N) ≤ B.scale (E N) N u :=
      flowScale_antitoneOn hW0.le (B.L N) (E N) (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 (ht1 N).le)
        hut
    have hA1 : 1 ≤ B.scale (E N) N u := (Real.one_le_rpow hN1' hc0.le).trans (hAcN.trans hscale)
    have hx90 : ((N : ℝ) ^ δ) ^ 90 ≤ B.scale (E N) N u := by
      have h : ((N : ℝ) ^ δ) ^ 90 ≤ B.scale (E N) N u ^ 1 :=
        Step2.natCast_rpow_pow_le_of_le hN1' (by push_cast; linarith) (hAcN.trans hscale)
      rwa [pow_one] at h
    have hR30 : ((1 - s N) / (1 - u)) ^ 30 ≤ B.scale (E N) N u := by
      have h := hregN
      rw [hRt] at h
      exact (pow_le_pow_left₀ (by linarith) hRut 30).trans (h.trans hscale)
    have key : ((N : ℝ) ^ δ) ^ 2 * ((1 - s N) / (1 - u)) ^ 4 ≤ B.scale (E N) N u := by
      have h45 : (((N : ℝ) ^ δ) ^ 2 * ((1 - s N) / (1 - u)) ^ 4) ^ 45 ≤
          B.scale (E N) N u ^ 45 := by
        calc (((N : ℝ) ^ δ) ^ 2 * ((1 - s N) / (1 - u)) ^ 4) ^ 45
            = ((N : ℝ) ^ δ) ^ 90 * (((1 - s N) / (1 - u)) ^ 30) ^ 6 := by ring
          _ ≤ B.scale (E N) N u * B.scale (E N) N u ^ 6 :=
              mul_le_mul hx90 (pow_le_pow_left₀ (by positivity) hR30 6) (by positivity)
                (by linarith)
          _ = B.scale (E N) N u ^ 7 := by ring
          _ ≤ B.scale (E N) N u ^ 45 := pow_le_pow_right₀ hA1 (by norm_num)
      exact (pow_le_pow_iff_left₀ (by positivity) (by linarith) (by norm_num)).1 h45
    unfold Step2.thr
    rw [hRu]
    calc (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ δ * ((1 - s N) / (1 - u)) ^ 4)
        ≤ (N : ℝ) ^ δ * ((N : ℝ) ^ δ * ((1 - s N) / (1 - u)) ^ 4) :=
          mul_le_mul_of_nonneg_right hNε (by positivity)
      _ = ((N : ℝ) ^ δ) ^ 2 * ((1 - s N) / (1 - u)) ^ 4 := by ring
      _ ≤ B.scale (E N) N u := key
  · -- `L √(W^{-D}) ≤ L W^{-2} ≤ W⁻¹ ≤ (W η_u)⁻¹ = ℓ_u A_u⁻¹`
    have hℓ1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
    have hℓ0 : 0 < B.ell N u := by linarith
    have hη0 : 0 < etaT (E N) u := etaT_pos_of_lt_one' (hE N) hu1
    have hη1 : etaT (E N) u ≤ 1 := by
      rw [Step2.etaT_eq]
      calc (1 - u) * (mE (E N)).im ≤ 1 * 1 := mul_le_mul (by linarith) hm1 hm0.le zero_le_one
        _ = 1 := one_mul 1
    have hWD : (B.W N : ℝ) ^ (-D) ≤ ((B.W N : ℝ) ^ 2 * (B.W N : ℝ) ^ 2)⁻¹ := by
      calc (B.W N : ℝ) ^ (-D) ≤ (B.W N : ℝ) ^ (-(4 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
        _ = ((B.W N : ℝ) ^ 2 * (B.W N : ℝ) ^ 2)⁻¹ := by
            rw [Real.rpow_neg hW0.le, ← pow_add]; norm_cast
    have hsq : √((B.W N : ℝ) ^ (-D)) ≤ ((B.W N : ℝ) ^ 2)⁻¹ := by
      calc √((B.W N : ℝ) ^ (-D)) ≤ √(((B.W N : ℝ) ^ 2 * (B.W N : ℝ) ^ 2)⁻¹) :=
            Real.sqrt_le_sqrt hWD
        _ = ((B.W N : ℝ) ^ 2)⁻¹ := by
            rw [Real.sqrt_inv, Real.sqrt_mul_self (by positivity)]
    have hrhs : B.ell N u * (B.scale (E N) N u)⁻¹ = ((B.W N : ℝ) * etaT (E N) u)⁻¹ := by
      change B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT (E N) u)⁻¹ =
        ((B.W N : ℝ) * etaT (E N) u)⁻¹
      field_simp
    rw [hrhs]
    calc (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D)) ≤ (B.W N : ℝ) * ((B.W N : ℝ) ^ 2)⁻¹ :=
          mul_le_mul hLW hsq (Real.sqrt_nonneg _) hW0.le
      _ = ((B.W N : ℝ) * 1)⁻¹ := by field_simp
      _ ≤ ((B.W N : ℝ) * etaT (E N) u)⁻¹ := by
          apply inv_anti₀ (by positivity)
          exact mul_le_mul_of_nonneg_left hη1 hW0.le

end DriftScalarsN

section GridPointwiseN

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-- **The pointwise grid bound `GridPointwise'N` for the Gaussian flow**, under the plain pair,
with `{κ}(hκ0)(hκ1){E}(hEκ)`. It calls `goodEvent_grid_plainN`, `goodEvent_grid_imp_plainN`
(same `κ`), `drift_point_le_heG_scalars_plainN`; `cond272_of_plainN`, `grid_thr_improve'N`,
`plain_endpointN`, `scale_endpointN`; `highProb_grid_rowSetN`, `SumZeroDyn.flow_crudeN`; and the
deterministic, `E`-free `mgDrift`/`mgDrift_le`. -/
theorem gridPointwise'_gauss_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    GridPointwise'N d E s t := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hcond : Cond272N (band d) E s t := Step2.cond272_of_plainN hE2 hst ht1 hreg0
  have hreg' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N) := hAc
  intro D hD u
  set D' : ℝ := max (D + 4) 64 with hD'def
  have hD'64 : (64 : ℝ) ≤ D' := le_max_right _ _
  have hDD : D + 4 ≤ D' := le_max_left _ _
  refine ⟨min (c / 90) 1, lt_min (by positivity) one_pos, fun δ hδ0 hδδ₀ D₁ hD₁ => ?_⟩
  have hδc : δ ≤ c / 90 := hδδ₀.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδδ₀.trans (min_le_right _ _)
  set ζ : ℝ := δ / 96 with hζdef
  set ε : ℝ := δ / 4 with hεdef
  set τ₁ : ℝ := δ / 32 with hτ₁def
  have hζ0 : 0 < ζ := by positivity
  have hε0 : 0 < ε := by positivity
  have hτ₁0 : 0 < τ₁ := by positivity
  have hεδ : 2 * ε ≤ δ := by rw [hεdef]; linarith
  have hDζ : 8 + 2 * ζ ≤ D' := by rw [hζdef]; linarith
  set uR : ℕ → ℝ := fun N => (u N : ℝ) with huRdef
  have hsu : ∀ N, s N ≤ uR N := fun N => (u N).2.1
  have hut : ∀ N, uR N ≤ t N := fun N => (u N).2.2
  have hu1 : ∀ N, uR N < 1 := fun N => (hut N).trans_lt (ht1 N)
  set K : ℕ → ℕ := gridK D' (D₁ + 1 + 1) with hKdef
  have hK0 : ∀ N, K N ≠ 0 := gridK_ne_zero D' (D₁ + 1 + 1)
  have hCK : 0 ≤ CK D' (D₁ + 1 + 1) := by unfold CK; linarith
  refine ⟨K, hK0, ⟨CK D' (D₁ + 1 + 1) + 2, by linarith, gridK_card_le hCK⟩, ?_⟩
  -- the probabilistic inputs, and the deterministic premises, eventually in `N`
  have hGood := goodEvent_grid_plainN (d := d) hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg0 hAc hδ0 hδc
    (by linarith : (60 : ℝ) ≤ D') hτ₁0 hε0 hζ0 hζ0 (by positivity : (0 : ℝ) < ζ / 2) hsu hut
    (D₁ + 1) (by linarith)
  have hImp := goodEvent_grid_imp_plainN (d := d) hκ0 hEκ hs0 hst ht1 hcond hc0 hreg0 hAc hδ0 hδc
    (by linarith : (60 : ℝ) ≤ D') ζ ζ (ζ / 2) (le_of_eq hτ₁def) hε0.le hεδ hsu hut (D₁ + 1)
    (by linarith)
  have hRow := highProb_grid_rowSetN d hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg' (ζ / 2)
    (by positivity) hsu hut K hK0 (by linarith : (0 : ℝ) ≤ CK D' (D₁ + 1 + 1) + 2)
    (gridK_card_le hCK)
  have hThr := grid_thr_improve'N (band d) (K := K) hκ0 hEκ hs0 hsu hu1 hc0
    (plain_endpointN (band d) hE2 ht1 hreg0 u) (scale_endpointN (band d) ht1 hAc u) hδ0 hδ1
    (by linarith : 90 * δ ≤ c) hD'64 hζ0.le
  have hMgN : ∀ᶠ N : ℕ in atTop,
      65 * (N : ℝ) ^ (3 * ζ) * mgDrift (band d) ζ N ≤ (N : ℝ) ^ (δ / 8) := by
    filter_upwards [mgDrift_le (band d) (κ := δ / 32) (ζ := ζ) (by positivity) hζ0.le,
      eventually_le_rpow 178880 (by positivity : (0 : ℝ) < δ / 32), eventually_ge_atTop 1]
      with N hM hC hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have e1 : (N : ℝ) ^ (3 * ζ) * (N : ℝ) ^ (δ / 32 + 3 * ζ) = (N : ℝ) ^ (3 * δ / 32) := by
      rw [← Real.rpow_add hN0]; congr 1; rw [hζdef]; ring
    have e2 : (N : ℝ) ^ (δ / 8) = (N : ℝ) ^ (3 * δ / 32) * (N : ℝ) ^ (δ / 32) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have h3 : 0 ≤ 65 * (N : ℝ) ^ (3 * ζ) := by positivity
    have h4 : 0 ≤ (N : ℝ) ^ (3 * δ / 32) := Real.rpow_nonneg hN0.le _
    calc 65 * (N : ℝ) ^ (3 * ζ) * mgDrift (band d) ζ N
        ≤ 65 * (N : ℝ) ^ (3 * ζ) * (2752 * (N : ℝ) ^ (δ / 32 + 3 * ζ)) :=
          mul_le_mul_of_nonneg_left hM h3
      _ = 178880 * (N : ℝ) ^ (3 * δ / 32) := by rw [← e1]; ring
      _ ≤ (N : ℝ) ^ (δ / 32) * (N : ℝ) ^ (3 * δ / 32) := mul_le_mul_of_nonneg_right hC h4
      _ = (N : ℝ) ^ (δ / 8) := by rw [e2]; ring
  have hScal := drift_point_le_heG_scalars_plainN (band d) hE2 hs0 ht1 hc0 hreg0 hAc hδ0.le hδc
    hεδ (by linarith : (4 : ℝ) ≤ D')
  have hcr := SumZeroDyn.flow_crudeN hE2 hs0 hst ht1 hcond
  have hW2 := Step2.eventually_le_W_sq (band d)
  have hae : ∀ N, ∀ᵐ ω ∂(Pg d), s N < uR N → GridAE d (E N) s uR K N ω := by
    intro N
    by_cases hlt : s N < uR N
    · filter_upwards [ae_gridAE d (hE2 N) (hs0 N) hlt (hu1 N) (hK0 N)] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hlt
  filter_upwards [hGood, hImp, hRow (D₁ + 1) (by linarith), hThr, hScal, hMgN, hcr, hW2,
    eventually_ge_atTop 2] with N hGN hImpN hRowN hThrN hScalN hMgN' hcrN hW2N hN2
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1' : (1 : ℝ) ≤ N := by linarith
  obtain ⟨⟨hK1, hΔR, _hMm0, hMmle⟩, hImpω⟩ := hImpN
  obtain ⟨_, hW8, hLW, hNW, hlog, hv⟩ := hScalN
  set Gd : Set (Ωg d) :=
    goodEventGrid d (E N) D' δ τ₁ ε ζ ζ (ζ / 2) s uR K (2 * D' + 2) (2 * D' + 2) N with hGd
  set Rw : Set (Ωg d) := {ω | ∀ k : Fin (K N + 1), H d s uR K N k ω ∈
    rowSet d (E N) N (time s uR K N k) ((band d).ell N (s N)) (ζ / 2)} with hRw
  set Ae : Set (Ωg d) := {ω | ¬ (s N < uR N → GridAE d (E N) s uR K N ω)} with hAe
  have hAe0 : Pg d Ae = 0 := ae_iff.1 (hae N)
  -- the pointwise core: on the good event, `J_K < thr(u N)`
  have hcore : ∀ ω, ω ∈ Gd → ω ∈ Rw → (s N < uR N → GridAE d (E N) s uR K N ω) →
      jSMat d (E N) D' N (uR N) (H d s uR K N (K N) ω) < Step2.thr (E N) s δ N (uR N) := by
    intro ω hGω hRω hAω
    obtain ⟨hinit, hZ, hY, hbefore, hgoodAll, hJ0⟩ := hImpω ω hGω
    set τω := gridTau d (E N) D' δ τ₁ ε ζ ζ (ζ / 2) s uR K N ω with hτω
    have hτK : τω ≤ K N := gridTau_le (E N) D' δ τ₁ ε ζ ζ (ζ / 2) s uR K N ω
    have hat : jSMat d (E N) D' N (time s uR K N τω) (H d s uR K N τω ω)
        < Step2.thr (E N) s δ N (time s uR K N τω) := by
      rcases lt_or_eq_of_le (hsu N) with hlt' | heq
      · obtain ⟨hexp, hRst⟩ := hAω hlt'
        have hdrift : ∀ j < τω, ∀ b : LoopArg ((band d).L N) 2,
            ‖Dgrid (band d) (E N) s uR K N j ω b‖ ≤
              driftCoef' (band d) (E N) s δ D' ζ (mgDrift (band d) ζ N) N (time s uR K N j) *
                Step2.tT (band d) (E N) N D' (time s uR K N j)
                  (zdist ((band d).L N) (b 0 - b 1)) := by
          intro j hj
          obtain ⟨hjS, hjG⟩ := hbefore j hj
          have hjK : j ≤ K N := (le_of_lt hj).trans hτK
          have hmem := mem_Icc_time s uR K N j (hs0 N) (hsu N) hjK
          obtain ⟨hJA, hDreg⟩ := hv (time s uR K N j) hmem.1 (hmem.2.trans (hut N))
          exact drift_of_goodSet' d (hE2 N) hN1' (hs0 N) hmem.1 (hmem.2.trans_lt (hu1 N)) hδ0.le
            hε0.le hεδ hζ0.le hDζ hW8 hLW hNW hlog hJA hDreg hjG
            (hRω ⟨j, Nat.lt_succ_of_le hjK⟩) hjS.le
        have h := hThrN ((N : ℝ) ^ (δ / 16)) (mgDrift (band d) ζ N) (azumaMm d (E N) δ τ₁ N)
          (Real.rpow_nonneg hN0.le _) (mgDrift_nonneg d ζ N)
          (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)) hMgN' hMmle hK1 hΔR τω hτK ω
          (hexp τω hτK) hinit hdrift hZ hY (fun j hj b => hRst j (lt_of_lt_of_le hj hτK) b)
        exact lt_of_le_of_lt h.1 h.2
      · rw [H_eq_H_zero_of_eq d heq, time_eq_time_zero_of_eq heq]
        exact hJ0
    have hτeq : τω = K N :=
      min_firstHit_eq_of_at
        (fun j (ω : Ωg d) => jSMat d (E N) D' N (time s uR K N j) (H d s uR K N j ω))
        (fun j (ω : Ωg d) => (goodSet d (E N) N (time s uR K N j) ((band d).ell N (s N)) τ₁ ε ζ ζ
          (ζ / 2) D')ᶜ.indicator (fun _ => (1 : ℝ)) (H d s uR K N j ω))
        (fun j => Step2.thr (E N) s δ N (time s uR K N j)) (1 / 2) (K N)
        (fun j hj => by
          rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 (hgoodAll j hj))]
          norm_num)
        hat
    rw [hτeq, time_last s uR K N (hK0 N)] at hat
    exact hat
  -- the event inclusion
  have hsub : {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
      (N : ℝ) ^ δ * ((etaT (E N) (s N) / etaT (E N) (uR N)) ^ 4 *
        ((band d).scale (E N) N (uR N))⁻¹ ^ 2 * (band d).decayProf N (uR N) D p.1 p.2)
      < lkErrMat d (E N) N (uR N) (H d s uR K N (K N) ω) (pmLoop p.1 p.2)} ⊆
      (Gdᶜ ∪ Rwᶜ) ∪ Ae := by
    intro ω hω
    by_contra hcon
    have hGω : ω ∈ Gd := by by_contra h; exact hcon (Or.inl (Or.inl h))
    have hRω : ω ∈ Rw := by by_contra h; exact hcon (Or.inl (Or.inr h))
    have hAω : s N < uR N → GridAE d (E N) s uR K N ω := by by_contra h; exact hcon (Or.inr h)
    obtain ⟨p, hp⟩ := hω
    have hJK := hcore ω hGω hRω hAω
    have hlk := lk_le_of_jS d (H_isHermitian d s uR K N (K N) ω) hDD (hcrN.2.2.2 (u N)).1
      ((hcrN.2.2.2 (u N)).2.1.trans hW2N) hJK.le p.1 p.2
    have e : Step2.thr (E N) s δ N (uR N) * ((band d).scale (E N) N (uR N))⁻¹ ^ 2 *
          (band d).decayProf N (uR N) D p.1 p.2
        = (N : ℝ) ^ δ * ((etaT (E N) (s N) / etaT (E N) (uR N)) ^ 4 *
          ((band d).scale (E N) N (uR N))⁻¹ ^ 2 * (band d).decayProf N (uR N) D p.1 p.2) := by
      unfold Step2.thr; ring
    linarith
  refine le_trans (measure_mono hsub) ?_
  have hp0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D₁ + 1)) := Real.rpow_nonneg hN0.le _
  calc Pg d ((Gdᶜ ∪ Rwᶜ) ∪ Ae) ≤ Pg d (Gdᶜ ∪ Rwᶜ) + Pg d Ae := measure_union_le _ _
    _ ≤ (Pg d Gdᶜ + Pg d Rwᶜ) + 0 := by
        rw [hAe0]; exact add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1)))) + 0 :=
        add_le_add (add_le_add hGN hRowN) le_rfl
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D₁ + 1))) := by
        rw [add_zero, ← ENNReal.ofReal_add hp0 hp0]
        ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show -(D₁ + 1) = -D₁ + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
        have h0 : 0 ≤ (N : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
        have : 2 * (N : ℝ)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hN0]; exact hN2'
        nlinarith

end GridPointwiseN

section CompatAllN

open MeasureTheory ProbabilityTheory Filter Matrix RBM

end CompatAllN

end RBM.Gauss.Grid

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-- **Step 2 from the pointwise (2.76)**: the local law (2.75) and (2.76), uniformly in time. It
calls `Grid.h276_of_pointwise_plainN` (with the same `κ`,`κ≤1`), `step1Hyp_gauss_of_scale''N`,
`Step1.weakLawN`, `Step2.localLaw_of_scale_factsN`,
`StepGlue.eventually_R4_le_scale_of_cond272N`; `cond272_of_plainN`. -/
theorem step2_gauss_of_pointwise_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (hpt : ∀ D : ℝ, 0 < D → ∀ u : ∀ N, TimeIcc s t N, StochDom (P d)
      (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
        (sample d).lkErr (E N) N (u N) ω (pmLoop p.1 p.2))
      (fun N p _ => (etaT (E N) (s N) / etaT (E N) (u N)) ^ 4 *
        ((band d).scale (E N) N (u N))⁻¹ ^ 2 * (band d).decayProf N (u N) D p.1 p.2)) :
    StochDom (band d).P
      (fun N (p : TimeIcc s t N × ((band d).Idx N × (band d).Idx N)) ω =>
        (sample d).llErr (E N) N p.1 ω p.2)
      (fun N p _ => ((band d).scale (E N) N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT (E N) (s N) / etaT (E N) p.1) ^ 4 * ((band d).scale (E N) N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have h276 := Grid.h276_of_pointwise_plainN d hκ0 hκ1 hEκ hs0 hst ht1 hc0 hAc hpt
  have hc272 : Cond272N (band d) E s t := Step2.cond272_of_plainN hE2 hst ht1 hreg0
  have h1 : Step1.HypN (sample d) E s t :=
    step1Hyp_gauss_of_scale''N d hκ0 hEκ hB hs0 hst ht1 hc272 hc0 hAc
  have h274 := Step1.weakLawN (sample d) hκ0 hEκ hB hs0 hst ht1 hc272 hc0 hAc h1
  exact ⟨Step2.localLaw_of_scale_factsN (sample d) hκ0 hκ1 hEκ hs0 hst ht1 hc0
    (StepGlue.eventually_R4_le_scale_of_cond272N (B := band d) hE2 hs0 hst ht1 hc272 hAc) h276
    h274 h1.lemma41, h276⟩

/-- **Step 2 for the Gaussian flow**: (2.75) and (2.76), uniformly in time, from (2.68)–(2.70) at
`s` and the plain pair. -/
theorem step2_gauss_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    StochDom (band d).P
      (fun N (p : TimeIcc s t N × ((band d).Idx N × (band d).Idx N)) ω =>
        (sample d).llErr (E N) N p.1 ω p.2)
      (fun N p _ => ((band d).scale (E N) N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT (E N) (s N) / etaT (E N) p.1) ^ 4 * ((band d).scale (E N) N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) :=
  step2_gauss_of_pointwise_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
    (Grid.hpt_of_gridPointwise'N d hs0
      (Grid.gridPointwise'_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc))

/-- **Steps 1–2 for the Gaussian flow** (`Steps12N`), from (2.68)–(2.70) at `s` and the plain
pair. -/
theorem steps12_gauss_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    Steps12N (sample d) E s t := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hcond : Cond272N (band d) E s t := Step2.cond272_of_plainN hE2 hst ht1 hreg0
  have h1 : Step1.HypN (sample d) E s t :=
    step1Hyp_gauss_of_scale''N d hκ0 hEκ hB hs0 hst ht1 hcond hc0 hAc
  obtain ⟨hlocal, hdecay⟩ := step2_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  exact
    { apriori := Step1.aprioriN (sample d) hκ0 hEκ hB hs0 hst ht1 hcond hc0 hAc h1
      weakLaw := Step1.weakLawN (sample d) hκ0 hEκ hB hs0 hst ht1 hcond hc0 hAc h1
      localLaw := hlocal
      aprioriDecay := hdecay }

section CompatAllN

end CompatAllN

end RBM.Gauss
