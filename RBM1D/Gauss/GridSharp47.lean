/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridFarStop
import RBM1D.Gauss.GridDriftSplit
import RBM1D.Gauss.GridNearDriftSum

/-!
# Pass 1 (the first improvement) as a bootstrap at the far stopping index

## Main results

* `goodEventSharp47` — Step 2's per-endpoint good event ∩ rows ∩ `GridAE` ∩ the Chebyshev event
  at the far stopping index `gridTauFar`.
* `cSharp47` — the explicit constant `16 + e + (36e + 16)/m`, a function of `E` only.
* `Sharp47.coef_le`, `Sharp47.drift_sum_split`, `Sharp47.far1_le`, `Sharp47.far2_le`,
  `Sharp47.final_arith` — the deterministic pieces of Step 2's grid Duhamel closure at an
  arbitrary grid index `k`, with the **unmerged** drift of `GridDriftSplit.lean` at `Λ = thr` and
  the **joint** near sum of `GridNearDriftSum.lean`; output
  `J*_{u_k} ≤ cSharp47 N^{δ/2}(r_k² + 1) < thrFar(u_k)`.

## Route

The drift coefficient of `GridDriftSplit.lean` is split (`Sharp47.coef_le`) into a near part
`64 N^{3ζ} c_near(W,1) η⁻¹ (ℓ_u/ℓ_s)³`, an `η⁻¹`-part with constant evaluated at `u_k`
(far terms 1, 2 of (5.35), the ρ-residue, the `36 η⁻¹A⁻¹` part of (5.34)/(5.50)) and the
`W L W^{-D}` part; the time sums (`Sharp47.drift_sum_split`) use `nearDrift_grid_sum_le`
for the near part (no sup × length step) and the `η`-pairing for the rest. The closure
(`far1_le`, `far2_le`, `final_arith`) uses only the plain-pair premises of Step 2.
`driftCoef'` (the merged `A^{-3/7} thr³` coefficient) is not used. In the bootstrap at
`τ′ = gridTauFar` the `Y` bound and the Azuma `Z` bound are used only at `k = gridTauFar`; `gridTau`
enters only through `gridTauFar_le_gridTau`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM Finset
open scoped NNReal ENNReal Matrix.Norms.L2Operator

namespace Sharp47

variable {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ}
  {N : ℕ}

/-- The drift time sum with a split coefficient `CN η_j⁻¹ (ℓ_j/ℓ_s)³ + P η_j⁻¹ + Q`: the near
part through the joint grid sum `nearDrift_grid_sum_le`, the `η⁻¹` part through the
pairing `eta_inv_mul_weight_le` (as in `drift_sum_le'`), the constant part through `Σ Δ w² ≤ R²`. -/
theorem drift_sum_split (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hK1 : 1 ≤ K N) {k : ℕ} (hk : k ≤ K N) (hW : Real.exp 1 ≤ (B.W N : ℝ)) {D CN P Q : ℝ}
    (hCN : 0 ≤ CN) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (Dv : ℕ → LoopArg (B.L N) 2 → ℂ)
    (hdrift : ∀ j < k, ∀ b, ‖Dv j b‖ ≤
      (CN * ((etaT E (time s t K N j))⁻¹ * (B.ell N (time s t K N j) / B.ell N (s N)) ^ 3)
        + P * (etaT E (time s t K N j))⁻¹ + Q) *
      Step2.tT B E N D (time s t K N j) (zdist (B.L N) (b 0 - b 1)))
    (a : LoopArg (B.L N) 2) :
    ‖(∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
        (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dv j)) a‖ ≤
      Step2.xiK (B.L N) (B.W N) (mE E).im *
        (CN * (2 * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E (time s t K N k)) ^ 2)
          + P * (((mE E).im)⁻¹ * (etaT E (s N) / etaT E (time s t K N k)) ^ 2)
          + Q * (etaT E (s N) / etaT E (time s t K N k)) ^ 2) *
        Step2.tT B E N D (time s t K N k) (zdist (B.L N) (a 0 - a 1)) := by
  classical
  set u : ℕ → ℝ := fun j => time s t K N j with hudef
  set Δ := step s t K N with hΔ
  have hΔ0 : 0 ≤ Δ := step_nonneg' s t K N hst
  have hm0 := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  set m := (mE E).im with hm
  have hW0 : (0 : ℝ) < B.W N := lt_of_lt_of_le (Real.exp_pos 1) hW
  have hs1 : s N < 1 := hst.trans_lt ht1
  have huk : u k ≤ t N := time_le_t s t K N hst hK1 hk
  have huk1 : u k < 1 := huk.trans_lt ht1
  have hsu : ∀ j, s N ≤ u j := fun j => s_le_time s t K N hst j
  have hu_succ : ∀ j, u j ≤ u (j + 1) := fun j => time_mono' s t K N hst (Nat.le_succ j)
  have hu0 : 0 ≤ u 0 := hs0.trans (hsu 0)
  have hkΔ : (k : ℝ) * Δ = u k - s N := by simp only [hudef, time_eq]; ring
  set q : ℕ → ℝ := fun j => B.ell N (u j) / B.ell N (s N) with hqdef
  set coef : ℕ → ℝ := fun j => CN * ((etaT E (u j))⁻¹ * q j ^ 3) + P * (etaT E (u j))⁻¹ + Q
    with hcoef
  set M : ℕ → ℝ := fun j => max (coef j) 0 with hMdef
  have hM0 : ∀ j, 0 ≤ M j := fun j => le_max_right _ _
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
  have hMj : ∀ j < k, M j = coef j := by
    intro j hj
    have hj1 : u j < 1 := (time_mono' s t K N hst hj.le).trans_lt huk1
    have hη := Step2.etaT_pos' hE hj1
    have hℓu : 0 < B.ell N (u j) := Step3.ellHat_pos_of_lt_one hL1 hj1
    have hq0 : 0 ≤ q j := div_nonneg hℓu.le hℓs.le
    refine max_eq_left ?_
    simp only [hcoef]
    have : 0 ≤ (etaT E (u j))⁻¹ := inv_nonneg.2 hη.le
    positivity
  have hA : ∀ j < k, ∀ b, ‖Dv j b‖ ≤
      M j * tailT (B.W N) (ellHat (B.L N) (u j : ℂ)) ((1 - u j) * m) D
        (zdist (B.L N) (b 0 - b 1)) := by
    intro j hj b
    rw [hMj j hj]; exact hdrift j hj b
  have hAuv : ∀ j < k, (B.W N : ℝ) * ellHat (B.L N) (u k : ℂ) * ((1 - u k) * m)
      ≤ (B.W N : ℝ) * ellHat (B.L N) (u (j + 1) : ℂ) * ((1 - u (j + 1)) * m) := by
    intro j hj
    exact flowScale_antitoneOn hW0.le (B.L N) E
      (Set.mem_Iic.2 ((time_mono' s t K N hst (by omega : j + 1 ≤ k)).trans huk1.le))
      (Set.mem_Iic.2 huk1.le) (time_mono' s t K N hst (by omega : j + 1 ≤ k))
  have hwd := weighted_duhamel_sum_le (B.L N) (B.three_le_L N) hm0 hm1 u hu0 hu_succ huk1 hW
    hΔ0 Dv M hM0 hA hAuv a
  refine hwd.trans ?_
  have hT0 : 0 ≤ Step2.tT B E N D (time s t K N k) (zdist (B.L N) (a 0 - a 1)) :=
    tailT_nonneg hW0.le _
  refine mul_le_mul_of_nonneg_right ?_ hT0
  set Ξ := Step2.xiK (B.L N) (B.W N) m with hΞ
  have hΞ0 : 0 ≤ Ξ := Step2.xiK_nonneg _ _ _
  set R := etaT E (s N) / etaT E (u k) with hR
  have hRe : R = (1 - s N) / (1 - u k) := Step2.etaT_ratio hE _ _
  set w : ℕ → ℝ := fun j => (1 - u (j + 1)) / (1 - u k) with hw
  have h1k : 0 < 1 - u k := by linarith
  -- termwise identity
  have hterm : ∀ j ∈ Finset.range k, Δ * M j * w j ^ 2 * Ξ =
      Ξ * (CN * (Δ * (etaT E (u j))⁻¹ * w j ^ 2 * q j ^ 3)
        + P * (Δ * ((etaT E (u j))⁻¹ * w j ^ 2)) + Q * (Δ * w j ^ 2)) := by
    intro j hj
    rw [hMj j (Finset.mem_range.mp hj)]
    simp only [hcoef]
    ring
  -- the three time sums
  have hSn : ∑ j ∈ Finset.range k, Δ * (etaT E (u j))⁻¹ * w j ^ 2 * q j ^ 3 ≤
      2 * m⁻¹ * R ^ 2 := by
    have h := nearDrift_grid_sum_le B hE hs0 hst ht1 hK1 hk
    exact h
  have hS1 : ∑ j ∈ Finset.range k, Δ * ((etaT E (u j))⁻¹ * w j ^ 2) ≤ m⁻¹ * R ^ 2 := by
    have hb : ∀ j ∈ Finset.range k, Δ * ((etaT E (u j))⁻¹ * w j ^ 2) ≤
        Δ * (m⁻¹ * ((1 - s N) / (1 - u k) ^ 2)) := by
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hj1k : u (j + 1) ≤ u k := time_mono' s t K N hst (by omega)
      have hpair := eta_inv_mul_weight_le hE (hu_succ j) hj1k huk1
      refine mul_le_mul_of_nonneg_left (hpair.trans ?_) hΔ0
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hm0.le)
      exact div_le_div_of_nonneg_right (by linarith [hsu j]) (by positivity)
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, hkΔ, hRe]
    rw [show (u k - s N) * (m⁻¹ * ((1 - s N) / (1 - u k) ^ 2))
        = m⁻¹ * ((u k - s N) * (1 - s N) / (1 - u k) ^ 2) by ring, div_pow]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hm0.le)
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [sq]
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hS2 : ∑ j ∈ Finset.range k, Δ * w j ^ 2 ≤ R ^ 2 := by
    have hb : ∀ j ∈ Finset.range k, Δ * w j ^ 2 ≤ Δ * R ^ 2 := by
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hj1k : u (j + 1) ≤ u k := time_mono' s t K N hst (by omega)
      refine mul_le_mul_of_nonneg_left ?_ hΔ0
      rw [hRe]
      refine pow_le_pow_left₀ (div_nonneg (by linarith) h1k.le) ?_ 2
      exact div_le_div_of_nonneg_right (by linarith [hsu (j + 1)]) h1k.le
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, hkΔ]
    have : u k - s N ≤ 1 := by linarith [hsu k]
    have : 0 ≤ u k - s N := by linarith [hsu k]
    nlinarith [sq_nonneg R]
  calc ∑ j ∈ Finset.range k, Δ * M j * ((1 - u (j + 1)) / (1 - u k)) ^ 2 * Ξ
      = ∑ j ∈ Finset.range k, Ξ * (CN * (Δ * (etaT E (u j))⁻¹ * w j ^ 2 * q j ^ 3)
          + P * (Δ * ((etaT E (u j))⁻¹ * w j ^ 2)) + Q * (Δ * w j ^ 2)) :=
        Finset.sum_congr rfl hterm
    _ = Ξ * (CN * ∑ j ∈ Finset.range k, Δ * (etaT E (u j))⁻¹ * w j ^ 2 * q j ^ 3
          + P * ∑ j ∈ Finset.range k, Δ * ((etaT E (u j))⁻¹ * w j ^ 2)
          + Q * ∑ j ∈ Finset.range k, Δ * w j ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.mul_sum, Finset.mul_sum]
    _ ≤ Ξ * (CN * (2 * m⁻¹ * R ^ 2) + P * (m⁻¹ * R ^ 2) + Q * R ^ 2) := by gcongr

/-- Per-step coefficient bound (`s N ≤ u ≤ v < 1`): the unmerged drift coefficient of
`GridDriftSplit.lean` at
`Λ = thr(u)`, `ε = δ/4`, `ζ = δ/96`, is bounded by a near part (`cNear(W,1)`, the ratio
`(ℓ_u/ℓ_s)³` kept at `u`), an `η_u⁻¹`-part whose constant is evaluated at `v` (monotonicity), and
the `W L W^{-D}` part of the quadratic at `v`. The ρ-residue is bounded crudely by
`8 N^{-20} η_u⁻¹`. -/
theorem coef_le (hE : |E| < 2) {δ D : ℝ} (hδ1 : δ ≤ 1) (hs0 : 0 ≤ s N)
    {u v : ℝ} (hsu : s N ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (hN1 : (1 : ℝ) ≤ N) (hW1 : (1 : ℝ) ≤ B.W N)
    (hLN : (B.L N : ℝ) ≤ N) (hηv : (etaT E v)⁻¹ ≤ N)
    (hWD : (B.W N : ℝ) ^ (-D) ≤ ((N : ℝ) ^ 32)⁻¹)
    (hex : Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) ≤ N) (hAu : B.scale E N u ≤ N)
    (hJ : (N : ℝ) ^ (2 * (δ / 4)) * Step2.thr E s δ N v ≤ (N : ℝ) ^ 6) :
    drNear B E s (δ / 96) N u
        + drRes B E s (δ / 96) N u
            (2 * (etaT E u)⁻¹ * ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr E s δ N u) *
              (B.W N : ℝ) ^ (-D))
        + drFar B E s δ (δ / 4) (δ / 96) D (Step2.thr E s δ N u) N u
      ≤ 64 * ((N : ℝ) ^ (δ / 96)) ^ 3 * Lemma57.cNear (B.W N : ℝ) 1 *
            ((etaT E u)⁻¹ * (B.ell N u / B.ell N (s N)) ^ 3)
        + (Lemma57.cFar (B.W N : ℝ) 1 *
              (4 * (N : ℝ) ^ (δ / 96) * B.ell N v / B.ell N (s N)) ^ ((3 : ℝ) / 2) *
              (√(B.scale E N v))⁻¹ * ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr E s δ N v)
            + 169 * (4 * (N : ℝ) ^ (δ / 96) * B.ell N v / B.ell N (s N)) * (B.scale E N v)⁻¹ *
              ((N : ℝ) ^ (2 * (δ / 4)) * Step2.thr E s δ N v) ^ ((3 : ℝ) / 2)
            + 8 * ((N : ℝ) ^ 20)⁻¹
            + Real.exp 1 * Step2.thr E s δ N v ^ 2 * 36 * (B.scale E N v)⁻¹) * (etaT E u)⁻¹
        + Real.exp 1 * Step2.thr E s δ N v ^ 2 * ((B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D)) := by
  have hu1 : u < 1 := huv.trans_lt hv1
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hℓs1 : 1 ≤ B.ell N (s N) := one_le_ellHat_of_nonneg hL1 hs0 hs1
  have hℓu1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg hL1 hu0 hu1
  have hℓuv : B.ell N u ≤ B.ell N v := Step3.ellHat_mono huv hv1
  have hm0 := mE_im_pos hE
  have hηu : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hηv0 : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hηuv : (etaT E u)⁻¹ ≤ (etaT E v)⁻¹ := by
    refine inv_anti₀ hηv0 ?_
    simp only [Step2.etaT_eq]
    exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  have hηu0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hηu.le
  have hAu0 : 0 < B.scale E N u := B.scale_pos' hE N hu0 hu1
  have hAv0 : 0 < B.scale E N v := B.scale_pos' hE N (hu0.trans huv) hv1
  have hAvu : B.scale E N v ≤ B.scale E N u := flowScale_antitoneOn (Nat.cast_nonneg _) (B.L N) E
    (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 hv1.le) huv
  have hAinv : (B.scale E N u)⁻¹ ≤ (B.scale E N v)⁻¹ := inv_anti₀ hAv0 hAvu
  have hsqinv : (√(B.scale E N u))⁻¹ ≤ (√(B.scale E N v))⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hAv0) (Real.sqrt_le_sqrt hAvu)
  have hNz0 : 0 ≤ (N : ℝ) ^ (δ / 96) := Real.rpow_nonneg hN0.le _
  have hNe0 : 0 ≤ (N : ℝ) ^ (2 * (δ / 4)) := Real.rpow_nonneg hN0.le _
  have hthruv : Step2.thr E s δ N u ≤ Step2.thr E s δ N v := thr_mono hE δ hs1 huv hv1
  have hthru0 : 0 ≤ Step2.thr E s δ N u := thr_nonneg δ u
  set Ju := (N : ℝ) ^ (2 * (δ / 4)) * Step2.thr E s δ N u with hJudef
  set Jv := (N : ℝ) ^ (2 * (δ / 4)) * Step2.thr E s δ N v with hJvdef
  have hJuv : Ju ≤ Jv := mul_le_mul_of_nonneg_left hthruv hNe0
  have hJu0 : 0 ≤ Ju := mul_nonneg hNe0 hthru0
  set ru := 4 * (N : ℝ) ^ (δ / 96) * B.ell N u / B.ell N (s N) with hrudef
  set rv := 4 * (N : ℝ) ^ (δ / 96) * B.ell N v / B.ell N (s N) with hrvdef
  have hru0 : 0 ≤ ru := div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  have hruv : ru ≤ rv :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hℓuv (by positivity)) (by linarith)
  have hW0 : (0 : ℝ) < B.W N := by linarith
  set cN1 := Lemma57.cNear (B.W N : ℝ) 1 with hcN1
  set cF1 := Lemma57.cFar (B.W N : ℝ) 1 with hcF1
  have hcN1_0 : 0 ≤ cN1 := Lemma57.cNear_nonneg hW1 one_pos
  have hcF1_0 : 0 ≤ cF1 := Lemma57.cFar_nonneg hW1 one_pos
  set εW := (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D) with hεW
  have hεW0 : 0 ≤ εW := by have := Real.rpow_nonneg hW0.le (-D); positivity
  -- near
  have hnear : drNear B E s (δ / 96) N u ≤ 64 * ((N : ℝ) ^ (δ / 96)) ^ 3 * cN1 *
      ((etaT E u)⁻¹ * (B.ell N u / B.ell N (s N)) ^ 3) := by
    unfold drNear
    have hc := Step2FarInputs.cNear_le_cNear_one hW1 hℓu1
    have hcu0 : 0 ≤ Lemma57.cNear (B.W N : ℝ) (B.ell N u) := Lemma57.cNear_nonneg hW1 (by linarith)
    have e : (4 * (N : ℝ) ^ (δ / 96) * B.ell N u / B.ell N (s N)) ^ 3
        = 64 * ((N : ℝ) ^ (δ / 96)) ^ 3 * (B.ell N u / B.ell N (s N)) ^ 3 := by ring
    rw [e]
    have hq0 : 0 ≤ (B.ell N u / B.ell N (s N)) ^ 3 :=
      pow_nonneg (div_nonneg (by linarith) (by linarith)) 3
    have hX : 0 ≤ 64 * ((N : ℝ) ^ (δ / 96)) ^ 3 * (B.ell N u / B.ell N (s N)) ^ 3 := by
      positivity
    calc (etaT E u)⁻¹ * Lemma57.cNear (B.W N : ℝ) (B.ell N u) *
          (64 * ((N : ℝ) ^ (δ / 96)) ^ 3 * (B.ell N u / B.ell N (s N)) ^ 3)
        ≤ (etaT E u)⁻¹ * cN1 *
          (64 * ((N : ℝ) ^ (δ / 96)) ^ 3 * (B.ell N u / B.ell N (s N)) ^ 3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hηu0) hX
      _ = _ := by ring
  -- residue
  have hres : drRes B E s (δ / 96) N u (2 * (etaT E u)⁻¹ * Ju * (B.W N : ℝ) ^ (-D)) ≤
      8 * ((N : ℝ) ^ 20)⁻¹ * (etaT E u)⁻¹ := by
    set ρ := 2 * (etaT E u)⁻¹ * Ju * (B.W N : ℝ) ^ (-D) with hρ
    have hℓu0 : B.ell N u ≠ 0 := by linarith
    have hηne : etaT E u ≠ 0 := hηu.ne'
    have e : drRes B E s (δ / 96) N u ρ = (etaT E u)⁻¹ *
        (4 * (N : ℝ) ^ (δ / 96) * (B.ell N (s N))⁻¹ * (B.L N : ℝ) * ρ *
          (Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) * B.scale E N u ^ 2)) := by
      unfold drRes
      field_simp
    rw [e, mul_comm (8 * ((N : ℝ) ^ 20)⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ hηu0
    have hNz : (N : ℝ) ^ (δ / 96) ≤ N := by
      calc (N : ℝ) ^ (δ / 96) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = N := Real.rpow_one _
    have hℓsi : (B.ell N (s N))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hℓs1
    have hℓsi0 : 0 ≤ (B.ell N (s N))⁻¹ := inv_nonneg.2 (by linarith)
    have hWD0 : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
    have hρ0 : 0 ≤ ρ := by positivity
    have hρle : ρ ≤ 2 * N * (N : ℝ) ^ 6 * ((N : ℝ) ^ 32)⁻¹ := by
      have h1 : (etaT E u)⁻¹ ≤ N := hηuv.trans hηv
      have h2 : Ju ≤ (N : ℝ) ^ 6 := hJuv.trans hJ
      calc ρ = 2 * (etaT E u)⁻¹ * Ju * (B.W N : ℝ) ^ (-D) := rfl
        _ ≤ 2 * N * (N : ℝ) ^ 6 * ((N : ℝ) ^ 32)⁻¹ := by gcongr
    have hex0 : 0 ≤ Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) := (Real.exp_pos _).le
    have hexA : Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) * B.scale E N u ^ 2 ≤
        N * (N : ℝ) ^ 2 :=
      mul_le_mul hex (pow_le_pow_left₀ hAu0.le hAu 2) (by positivity) hN0.le
    calc 4 * (N : ℝ) ^ (δ / 96) * (B.ell N (s N))⁻¹ * (B.L N : ℝ) * ρ *
          (Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) * B.scale E N u ^ 2)
        ≤ 4 * N * 1 * N * (2 * N * (N : ℝ) ^ 6 * ((N : ℝ) ^ 32)⁻¹) * (N * (N : ℝ) ^ 2) := by
          gcongr
      _ = 8 * ((N : ℝ) ^ 20)⁻¹ := by field_simp; ring
  -- far
  have hF1 : Lemma57.cFar (B.W N : ℝ) (B.ell N u) * ru ^ ((3 : ℝ) / 2) *
      (√(B.scale E N u))⁻¹ * Ju ≤ cF1 * rv ^ ((3 : ℝ) / 2) * (√(B.scale E N v))⁻¹ * Jv := by
    have hc := Step2FarInputs.cFar_le_cFar_one hW1 hℓu1
    have hcu0 : 0 ≤ Lemma57.cFar (B.W N : ℝ) (B.ell N u) := Lemma57.cFar_nonneg hW1 (by linarith)
    have hr32 : ru ^ ((3 : ℝ) / 2) ≤ rv ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hru0 hruv (by norm_num)
    have hr320 : 0 ≤ ru ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hru0 _
    have hsq0 : 0 ≤ (√(B.scale E N u))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have hrv32 : 0 ≤ rv ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (hru0.trans hruv) _
    have hsqv0 : 0 ≤ (√(B.scale E N v))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    exact mul_le_mul (mul_le_mul (mul_le_mul hc hr32 hr320 hcF1_0) hsqinv hsq0
            (mul_nonneg hcF1_0 hrv32)) hJuv hJu0 (mul_nonneg (mul_nonneg hcF1_0 hrv32) hsqv0)
  have hF2 : 169 * ru * (B.scale E N u)⁻¹ * Ju ^ ((3 : ℝ) / 2) ≤
      169 * rv * (B.scale E N v)⁻¹ * Jv ^ ((3 : ℝ) / 2) := by
    have hJ32 : Ju ^ ((3 : ℝ) / 2) ≤ Jv ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow hJu0 hJuv (by norm_num)
    have hAi0 : 0 ≤ (B.scale E N u)⁻¹ := inv_nonneg.2 hAu0.le
    have hrv0 : 0 ≤ rv := hru0.trans hruv
    have hAvi0 : 0 ≤ (B.scale E N v)⁻¹ := inv_nonneg.2 hAv0.le
    have hJ320 : 0 ≤ Ju ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hJu0 _
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hruv (by norm_num)) hAinv hAi0
            (by positivity)) hJ32 hJ320 (by positivity)
  have hQ1 : Real.exp 1 * Step2.thr E s δ N u ^ 2 * (36 * ((etaT E u)⁻¹ * (B.scale E N u)⁻¹)) ≤
      Real.exp 1 * Step2.thr E s δ N v ^ 2 * 36 * (B.scale E N v)⁻¹ * (etaT E u)⁻¹ := by
    have ht2 : Step2.thr E s δ N u ^ 2 ≤ Step2.thr E s δ N v ^ 2 := pow_le_pow_left₀ hthru0 hthruv 2
    have hAi0 : 0 ≤ (B.scale E N u)⁻¹ := inv_nonneg.2 hAu0.le
    calc Real.exp 1 * Step2.thr E s δ N u ^ 2 * (36 * ((etaT E u)⁻¹ * (B.scale E N u)⁻¹))
        ≤ Real.exp 1 * Step2.thr E s δ N v ^ 2 * (36 * ((etaT E u)⁻¹ * (B.scale E N v)⁻¹)) := by
          gcongr
      _ = _ := by ring
  have hQ2 : Real.exp 1 * Step2.thr E s δ N u ^ 2 * εW ≤
      Real.exp 1 * Step2.thr E s δ N v ^ 2 * εW := by
    have ht2 : Step2.thr E s δ N u ^ 2 ≤ Step2.thr E s δ N v ^ 2 := pow_le_pow_left₀ hthru0 hthruv 2
    gcongr
  have hfar : drFar B E s δ (δ / 4) (δ / 96) D (Step2.thr E s δ N u) N u ≤
      (cF1 * rv ^ ((3 : ℝ) / 2) * (√(B.scale E N v))⁻¹ * Jv
        + 169 * rv * (B.scale E N v)⁻¹ * Jv ^ ((3 : ℝ) / 2)) * (etaT E u)⁻¹
      + Real.exp 1 * Step2.thr E s δ N v ^ 2 * 36 * (B.scale E N v)⁻¹ * (etaT E u)⁻¹
      + Real.exp 1 * Step2.thr E s δ N v ^ 2 * εW := by
    unfold drFar
    rw [← hJudef, ← hrudef, ← hεW]
    have h12 := mul_le_mul_of_nonneg_left (add_le_add hF1 hF2) hηu0
    refine (le_of_eq ?_).trans ((add_le_add h12 (add_le_add hQ1 hQ2)).trans (le_of_eq ?_))
    all_goals ring
  refine (add_le_add (add_le_add hnear hres) hfar).trans (le_of_eq ?_)
  ring

/-- (5.35)-far term 1 closure: `(Ξ P₁)² ≤ 64 Ξ² c_F² z³ · x^{24}R^{10} ≤ x⁸ A`. -/
theorem far1_le {Ξ cF z r R A x J : ℝ} (hΞ : 0 ≤ Ξ) (hcF : 0 ≤ cF) (hr0 : 0 ≤ r)
    (hr3 : r ^ 3 ≤ 64 * z ^ 3 * R ^ 2) (hA : 0 < A)
    (hJ : J = x ^ 12 * R ^ 4) (hxA : x ^ 24 * R ^ 10 ≤ A)
    (hC : 64 * Ξ ^ 2 * cF ^ 2 * z ^ 3 ≤ x ^ 8) :
    Ξ * (cF * r ^ ((3 : ℝ) / 2) * (√A)⁻¹ * J) ≤ x ^ 4 := by
  have hJ0 : 0 ≤ J := by rw [hJ]; positivity
  have hsr : √r ^ 2 = r := Real.sq_sqrt hr0
  have hL0 : 0 ≤ Ξ * cF * r * √r * J := by positivity
  have hL2 : (Ξ * cF * r * √r * J) ^ 2 ≤ (x ^ 4 * √A) ^ 2 := by
    rw [show (Ξ * cF * r * √r * J) ^ 2 = Ξ ^ 2 * cF ^ 2 * (r ^ 2 * √r ^ 2) * J ^ 2 by ring, hsr,
      mul_pow, Real.sq_sqrt hA.le, hJ]
    have hr3' : r ^ 2 * r ≤ 64 * z ^ 3 * R ^ 2 := by rw [← pow_succ]; exact hr3
    calc Ξ ^ 2 * cF ^ 2 * (r ^ 2 * r) * (x ^ 12 * R ^ 4) ^ 2
        ≤ Ξ ^ 2 * cF ^ 2 * (64 * z ^ 3 * R ^ 2) * (x ^ 12 * R ^ 4) ^ 2 := by gcongr
      _ = (64 * Ξ ^ 2 * cF ^ 2 * z ^ 3) * (x ^ 24 * R ^ 10) := by ring
      _ ≤ x ^ 8 * A := mul_le_mul hC hxA (by positivity) (by positivity)
      _ = (x ^ 4) ^ 2 * A := by ring
  have hL : Ξ * cF * r * √r * J ≤ x ^ 4 * √A :=
    (pow_le_pow_iff_left₀ hL0 (by positivity) two_ne_zero).1 hL2
  have hsA : 0 < √A := Real.sqrt_pos.2 hA
  rw [DrSplit.rpow_three_halves hr0]
  calc Ξ * (cF * (r * √r) * (√A)⁻¹ * J) = (Ξ * cF * r * √r * J) * (√A)⁻¹ := by ring
    _ ≤ (x ^ 4 * √A) * (√A)⁻¹ := mul_le_mul_of_nonneg_right hL (inv_nonneg.2 hsA.le)
    _ = x ^ 4 := by field_simp

/-- (5.35)-far term 2 closure: `(Ξ P₂)² ≤ Ξ² 169² 16 z² R · x^{36}R^{12} ≤ x⁸ A²`. -/
theorem far2_le {Ξ z r R A x J : ℝ} (hΞ : 0 ≤ Ξ) (hr0 : 0 ≤ r)
    (hr2 : r ^ 2 ≤ 16 * z ^ 2 * R) (hA : 0 < A) (hx1 : 1 ≤ x) (hR1 : 1 ≤ R)
    (hJ : J = x ^ 12 * R ^ 4) (hxA : x ^ 24 * R ^ 10 ≤ A)
    (hC : Ξ ^ 2 * 169 ^ 2 * 16 * z ^ 2 ≤ x ^ 20) :
    Ξ * (169 * r * A⁻¹ * J ^ ((3 : ℝ) / 2)) ≤ x ^ 4 := by
  have hJ0 : 0 ≤ J := by rw [hJ]; positivity
  have hsJ : √J ^ 2 = J := Real.sq_sqrt hJ0
  have hx0 : 0 ≤ x := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hL0 : 0 ≤ Ξ * 169 * r * J * √J := by positivity
  have hL2 : (Ξ * 169 * r * J * √J) ^ 2 ≤ (x ^ 4 * A) ^ 2 := by
    rw [show (Ξ * 169 * r * J * √J) ^ 2 = Ξ ^ 2 * 169 ^ 2 * r ^ 2 * (J ^ 2 * √J ^ 2) by ring, hsJ,
      hJ]
    have hR13 : R ^ 13 ≤ R ^ 20 := pow_le_pow_right₀ hR1 (by norm_num)
    have hA2 : (x ^ 24 * R ^ 10) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) hxA 2
    calc Ξ ^ 2 * 169 ^ 2 * r ^ 2 * ((x ^ 12 * R ^ 4) ^ 2 * (x ^ 12 * R ^ 4))
        ≤ Ξ ^ 2 * 169 ^ 2 * (16 * z ^ 2 * R) * ((x ^ 12 * R ^ 4) ^ 2 * (x ^ 12 * R ^ 4)) := by
          gcongr
      _ = (Ξ ^ 2 * 169 ^ 2 * 16 * z ^ 2) * x ^ 36 * R ^ 13 := by ring
      _ ≤ x ^ 20 * x ^ 36 * R ^ 20 := by gcongr
      _ = x ^ 8 * (x ^ 24 * R ^ 10) ^ 2 := by ring
      _ ≤ x ^ 8 * A ^ 2 := mul_le_mul_of_nonneg_left hA2 (by positivity)
      _ = (x ^ 4 * A) ^ 2 := by ring
  have hL : Ξ * 169 * r * J * √J ≤ x ^ 4 * A :=
    (pow_le_pow_iff_left₀ hL0 (by positivity) two_ne_zero).1 hL2
  rw [DrSplit.rpow_three_halves hJ0]
  calc Ξ * (169 * r * A⁻¹ * (J * √J)) = (Ξ * 169 * r * J * √J) * A⁻¹ := by ring
    _ ≤ (x ^ 4 * A) * A⁻¹ := mul_le_mul_of_nonneg_right hL (inv_nonneg.2 hA.le)
    _ = x ^ 4 := by field_simp

/-- The final allocation into `cSharp47 · x⁴ (R² + 1)`. -/
theorem final_arith {x R Ξ m Mi Mm CN P1 P2 P3 A εW thr : ℝ} (hx1 : 1 ≤ x) (hR1 : 1 ≤ R)
    (hΞ0 : 0 ≤ Ξ) (hΞx : Ξ ≤ x) (hm0 : 0 < m) (hMix : Mi ≤ x) (hMmx : Mm ≤ x)
    (hCN : Ξ * CN ≤ 4 * x ^ 4) (hP1 : Ξ * P1 ≤ x ^ 4) (hP2 : Ξ * P2 ≤ x ^ 4)
    (hP3 : Ξ * P3 ≤ x ^ 4) (hthr : thr = x ^ 8 * R ^ 4) (hA0 : 0 < A)
    (hA : x ^ 17 * R ^ 10 ≤ A) (hε0 : 0 ≤ εW) (hε : εW * x ^ 17 * R ^ 10 ≤ 1) :
    Mi * R ^ 2 * Ξ
        + Ξ * (CN * (2 * m⁻¹ * R ^ 2)
          + (P1 + P2 + P3 + Real.exp 1 * thr ^ 2 * 36 * A⁻¹) * (m⁻¹ * R ^ 2)
          + Real.exp 1 * thr ^ 2 * εW * R ^ 2)
        + Mm * (R ^ 2 + 1) + 1 + 1 + 1
      ≤ (16 + Real.exp 1 + (36 * Real.exp 1 + 16) / m) * x ^ 4 * (R ^ 2 + 1) := by
  have hx0 : 0 ≤ x := by linarith
  have hS0 : 0 ≤ R ^ 2 := sq_nonneg R
  have hmi0 : 0 < m⁻¹ := inv_pos.2 hm0
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx1
  have hx2 : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  have hxx4 : x ≤ x ^ 4 := by simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 4)
  -- the pieces
  have t1 : Mi * R ^ 2 * Ξ ≤ x ^ 4 * R ^ 2 := by
    calc Mi * R ^ 2 * Ξ ≤ x * R ^ 2 * x := by gcongr
      _ = x ^ 2 * R ^ 2 := by ring
      _ ≤ x ^ 4 * R ^ 2 := by gcongr
  have t2 : Ξ * (CN * (2 * m⁻¹ * R ^ 2)) ≤ 8 * m⁻¹ * (x ^ 4 * R ^ 2) := by
    calc Ξ * (CN * (2 * m⁻¹ * R ^ 2)) = (Ξ * CN) * (2 * m⁻¹ * R ^ 2) := by ring
      _ ≤ (4 * x ^ 4) * (2 * m⁻¹ * R ^ 2) := by gcongr
      _ = 8 * m⁻¹ * (x ^ 4 * R ^ 2) := by ring
  have hxA' : Ξ * (x ^ 16 * R ^ 10) ≤ A := by
    calc Ξ * (x ^ 16 * R ^ 10) ≤ x * (x ^ 16 * R ^ 10) := by gcongr
      _ = x ^ 17 * R ^ 10 := by ring
      _ ≤ A := hA
  have t3 : Ξ * ((P1 + P2 + P3 + Real.exp 1 * thr ^ 2 * 36 * A⁻¹) * (m⁻¹ * R ^ 2)) ≤
      3 * m⁻¹ * (x ^ 4 * R ^ 2) + 36 * Real.exp 1 * m⁻¹ := by
    have h4 : Ξ * (Real.exp 1 * thr ^ 2 * 36 * A⁻¹) * (m⁻¹ * R ^ 2) ≤ 36 * Real.exp 1 * m⁻¹ := by
      rw [hthr]
      have e : Ξ * (Real.exp 1 * (x ^ 8 * R ^ 4) ^ 2 * 36 * A⁻¹) * (m⁻¹ * R ^ 2)
          = 36 * Real.exp 1 * m⁻¹ * ((Ξ * (x ^ 16 * R ^ 10)) * A⁻¹) := by ring
      rw [e]
      have : (Ξ * (x ^ 16 * R ^ 10)) * A⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ hA0, one_mul]; exact hxA'
      calc 36 * Real.exp 1 * m⁻¹ * ((Ξ * (x ^ 16 * R ^ 10)) * A⁻¹)
          ≤ 36 * Real.exp 1 * m⁻¹ * 1 := by gcongr
        _ = _ := by ring
    have h123 : Ξ * (P1 + P2 + P3) * (m⁻¹ * R ^ 2) ≤ 3 * m⁻¹ * (x ^ 4 * R ^ 2) := by
      calc Ξ * (P1 + P2 + P3) * (m⁻¹ * R ^ 2) = (Ξ * P1 + Ξ * P2 + Ξ * P3) * (m⁻¹ * R ^ 2) := by
            ring
        _ ≤ (x ^ 4 + x ^ 4 + x ^ 4) * (m⁻¹ * R ^ 2) := by gcongr
        _ = 3 * m⁻¹ * (x ^ 4 * R ^ 2) := by ring
    have e : Ξ * ((P1 + P2 + P3 + Real.exp 1 * thr ^ 2 * 36 * A⁻¹) * (m⁻¹ * R ^ 2))
        = Ξ * (P1 + P2 + P3) * (m⁻¹ * R ^ 2)
          + Ξ * (Real.exp 1 * thr ^ 2 * 36 * A⁻¹) * (m⁻¹ * R ^ 2) := by ring
    rw [e]; linarith
  have t4 : Ξ * (Real.exp 1 * thr ^ 2 * εW * R ^ 2) ≤ Real.exp 1 := by
    rw [hthr]
    have e : Ξ * (Real.exp 1 * (x ^ 8 * R ^ 4) ^ 2 * εW * R ^ 2)
        = Real.exp 1 * (εW * (Ξ * (x ^ 16 * R ^ 10))) := by ring
    rw [e]
    have : εW * (Ξ * (x ^ 16 * R ^ 10)) ≤ 1 := by
      calc εW * (Ξ * (x ^ 16 * R ^ 10)) ≤ εW * (x * (x ^ 16 * R ^ 10)) := by gcongr
        _ = εW * x ^ 17 * R ^ 10 := by ring
        _ ≤ 1 := hε
    calc Real.exp 1 * (εW * (Ξ * (x ^ 16 * R ^ 10))) ≤ Real.exp 1 * 1 := by gcongr
      _ = _ := by ring
  have t5 : Mm * (R ^ 2 + 1) ≤ x ^ 4 * (R ^ 2 + 1) :=
    mul_le_mul_of_nonneg_right (hMmx.trans hxx4) (by positivity)
  -- the target
  have hdiv : (36 * Real.exp 1 + 16) / m = 36 * Real.exp 1 * m⁻¹ + 16 * m⁻¹ := by
    rw [div_eq_mul_inv]; ring
  rw [hdiv]
  have hX : 0 ≤ x ^ 4 * R ^ 2 := by positivity
  have hY1 : 1 ≤ x ^ 4 * (R ^ 2 + 1) := by
    have : x ^ 4 * (R ^ 2 + 1) = x ^ 4 * R ^ 2 + x ^ 4 := by ring
    rw [this]; linarith
  have k1 : Real.exp 1 ≤ Real.exp 1 * (x ^ 4 * (R ^ 2 + 1)) := le_mul_of_one_le_right he0.le hY1
  have k2 : 36 * Real.exp 1 * m⁻¹ ≤ 36 * Real.exp 1 * m⁻¹ * (x ^ 4 * (R ^ 2 + 1)) :=
    le_mul_of_one_le_right (by positivity) hY1
  have k3 : 11 * m⁻¹ * (x ^ 4 * R ^ 2) ≤ 16 * m⁻¹ * (x ^ 4 * (R ^ 2 + 1)) := by
    have e : 16 * m⁻¹ * (x ^ 4 * (R ^ 2 + 1)) - 11 * m⁻¹ * (x ^ 4 * R ^ 2)
        = m⁻¹ * (5 * (x ^ 4 * R ^ 2) + 16 * x ^ 4) := by ring
    have : 0 ≤ m⁻¹ * (5 * (x ^ 4 * R ^ 2) + 16 * x ^ 4) := by positivity
    linarith
  have e : (16 + Real.exp 1 + (36 * Real.exp 1 * m⁻¹ + 16 * m⁻¹)) * x ^ 4 * (R ^ 2 + 1)
      = 16 * (x ^ 4 * (R ^ 2 + 1)) + Real.exp 1 * (x ^ 4 * (R ^ 2 + 1))
        + 36 * Real.exp 1 * m⁻¹ * (x ^ 4 * (R ^ 2 + 1))
        + 16 * m⁻¹ * (x ^ 4 * (R ^ 2 + 1)) := by ring
  rw [e]
  have e2 : x ^ 4 * (R ^ 2 + 1) = x ^ 4 * R ^ 2 + x ^ 4 := by ring
  have e3 : 16 * (x ^ 4 * (R ^ 2 + 1)) = 16 * (x ^ 4 * R ^ 2) + 16 * x ^ 4 := by ring
  have e4 : 8 * m⁻¹ * (x ^ 4 * R ^ 2) + 3 * m⁻¹ * (x ^ 4 * R ^ 2)
      = 11 * m⁻¹ * (x ^ 4 * R ^ 2) := by ring
  have e5 : Ξ * (CN * (2 * m⁻¹ * R ^ 2)
          + (P1 + P2 + P3 + Real.exp 1 * thr ^ 2 * 36 * A⁻¹) * (m⁻¹ * R ^ 2)
          + Real.exp 1 * thr ^ 2 * εW * R ^ 2)
      = Ξ * (CN * (2 * m⁻¹ * R ^ 2))
        + Ξ * ((P1 + P2 + P3 + Real.exp 1 * thr ^ 2 * 36 * A⁻¹) * (m⁻¹ * R ^ 2))
        + Ξ * (Real.exp 1 * thr ^ 2 * εW * R ^ 2) := by ring
  rw [e5]
  have e6 : x ^ 4 * (R ^ 2 + 1) = x ^ 4 * R ^ 2 + x ^ 4 := by ring
  rw [e6] at t5
  linarith [t1, t2, t3, t4, t5, k1, k2, k3, e4, e3, hX, hx4]

/-- The output vs the stopping level `thrFar`: `R ≥ 1` and `2c < x⁴` give
`c x⁴ (R² + 1) < x⁸ R^{13/4}`. -/
theorem second_conj {x R cS : ℝ} (hR1 : 1 ≤ R) (hx0 : 0 < x) (h2 : 2 * cS < x ^ 4) (hc : 0 < cS) :
    cS * x ^ 4 * (R ^ 2 + 1) < x ^ 8 * R ^ ((13 : ℝ) / 4) := by
  have hR2 : R ^ 2 ≤ R ^ ((13 : ℝ) / 4) := by
    calc R ^ 2 = R ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast R 2).symm
      _ ≤ R ^ ((13 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hx4 : 0 < x ^ 4 := by positivity
  have hR21 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
  have hRR : R ^ 2 + 1 ≤ 2 * R ^ 2 := by linarith
  have hXR : 0 < x ^ 4 * R ^ 2 := by positivity
  calc cS * x ^ 4 * (R ^ 2 + 1) ≤ cS * x ^ 4 * (2 * R ^ 2) :=
        mul_le_mul_of_nonneg_left hRR (by positivity)
    _ = (2 * cS) * (x ^ 4 * R ^ 2) := by ring
    _ < x ^ 4 * (x ^ 4 * R ^ 2) := mul_lt_mul_of_pos_right h2 hXR
    _ = x ^ 8 * R ^ 2 := by ring
    _ ≤ x ^ 8 * R ^ ((13 : ℝ) / 4) := mul_le_mul_of_nonneg_left hR2 (by positivity)

end Sharp47

/-! ## The main statements -/

variable (d : Dims)

/-- Step 2's per-endpoint good event
∩ **the Chebyshev bound at the stopping index `gridTauFar`** (the fourth component). -/
def goodEventSharp47 (E D δ : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) : Set (Ωg d) :=
  goodEventGrid d E D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) s u K (2 * D + 2) (2 * D + 2) N
  ∩ {ω | ∀ k : Fin (K N + 1), H d s u K N k ω ∈
        rowSet d E N (time s u K N k) ((band d).ell N (s N)) (δ / 192)}
  ∩ {ω | s N < u N → GridAE d E s u K N ω}
  ∩ {ω | ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range
            (gridTauFar d E D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) s u K N ω),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
            (time s u K N
              (gridTauFar d E D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) s u K N ω) : ℂ)
            (Yvec (band d) E s u K N (j + 1) ω)) a‖
        < Step2.tT (band d) E N D (time s u K N
            (gridTauFar d E D δ (δ / 32) (δ / 4) (δ / 96) (δ / 96) (δ / 192) s u K N ω))
            (zdist (d.L N) (a 0 - a 1))}

/-- explicit constant, a function of `E` only -/
noncomputable def cSharp47 (E : ℝ) : ℝ := 16 + Real.exp 1 + (36 * Real.exp 1 + 16) / (mE E).im

namespace Sharp47

end Sharp47

namespace Sharp47

end Sharp47

end RBM.Gauss.Grid

end
