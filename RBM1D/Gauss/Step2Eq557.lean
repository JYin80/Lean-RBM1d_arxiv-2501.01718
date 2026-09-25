/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.EntryBoundTime
import RBM1D.Gauss.APrimeGoodSetFlowGeneralDims
import RBM1D.Hierarchy.Lemma57
import RBM1D.Hierarchy.EEBridge

/-!
# T1492: (4.2) ⇒ (5.57) at (2.73)-reduced strength, on one high-probability event

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, the single-`G` block-average bound (5.57), for every `d : Gauss.Dims`, at the
(2.73)-reduced strength, uniformly in `u ∈ [s_N, t_N]`, both in column and row form.

Target M2 of `docs/reports/T1488-prove.md` §3.  The route is exactly the one named there:

* `RBM.Gauss.entryBoundFlow_floor` — the floored, time-uniform (4.2), no large-deviation
  hypothesis, for every `d`;
* `RBM.Step1.apriori` at `n = 2` (the `(+,-)` `2`-loop `L_{(+,-)}`), discharged by
  `RBM.Gauss.step1Hyp_gauss_of_scale''`;
* `RBM.APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow` for the diagonal entries;
* the deterministic facts `η_u ℓ_u ≤ 1` (`RBM.etaT_mul_ellHat_le`) and `ℓ_s ≤ ℓ_u` for
  `u ∈ [s_N, t_N]` (`RBM.Step3.ellHat_mono`).

## Method

Fix `u`, a block label `x` and a point `p`.  Write `nrm v := ‖G_u(v, p)‖`.  Cauchy–Schwarz on
the `blkW`-weighted average, together with `∑_v blkW(v, x) = 1`
(`RBM.Lemma57.sum_blkW`), gives

`(∑_v blkW(v,x) nrm v)² ≤ ∑_v blkW(v,x) nrm(v)²`.

Split the right side at `v = p` (the point excluded from `RBM.OffPair`): the term at `v = p`
is bounded by the diagonal clause of `RBM.GoodEvent` (`‖G_pp‖ ≤ 1 + δ_N`); every other term is
bounded, via `RBM.Gauss.EntryBoundFlow'`, by `∑_{a,b ∈ sbSupport} L_{(+,-)}(p.1+b, v.1+a) +
W⁻¹·1(...) + fl_N`, and each `L_{(+,-)}` term is bounded via `RBM.Step1.apriori` at `n = 2` by
`N^τ (ℓ_u/ℓ_s) A_u⁻¹`.  Assembling the nine `sbSupport` terms, the near-block `W⁻¹` term (which
is `≤ A_u⁻¹` because `η_u ℓ_u ≤ 1`) and the floor (which is `≤ A_u⁻¹` once the floor exponent is
taken `≥ 2`, using `A_u ≤ N`) gives the (2.73)-reduced control claimed by M2.

The row form is the same argument with the roles of the two `green` arguments exchanged; the
control `RBM.Gauss.EntryBoundFlow'` gives does not distinguish the two orientations of an
off-diagonal pair, so the same numeric bound serves both.

## Main results

* `RBM.Gauss.Step2.highProb_eq557_colRow` — (T2): the column and row forms of (5.57) at
  (2.73)-reduced strength, on one high-probability event, for every `d : Gauss.Dims`.
* `RBM.Gauss.Step2.highProb_eq557_col` — (T1): the column form alone, by
  `RBM.HighProb.mono` from the previous statement.
-/

namespace RBM.Gauss.Step2

open Filter MeasureTheory Set RBM RBM.Gauss

-- The pointwise numeric assembly of `highProb_eq557_colRow` (Cauchy-Schwarz + the nine
-- `sbSupport` terms + growth absorption) has many arithmetic steps; the default heartbeat
-- budget is too small for it.
set_option maxHeartbeats 1000000

/-! ### Elementary real-analysis helpers -/

/-- Subadditivity of `Real.sqrt` on the nonnegative reals. -/
private theorem sqrt_add_le_aux {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsum : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- **The combinatorial core of (5.57).**  Given a diagonal bound `nrm i0 i0 ≤ 1 + δ` and an
off-diagonal control `nrm v i0 ^ 2 ≤ Cx v.1 i0.1` for every `v ≠ i0`, the `blkW`-weighted
average of `nrm` over a block is controlled by `√(Cx blk i0.1) + √(Wb⁻¹)(1 + δ)`.  This is the
Cauchy–Schwarz step (5.56) applied to a single `G`, rather than to the `3`-loop of
`RBM.Lemma57.norm_gloop_three_le_schwarz`. -/
private theorem blockSum_le {L Wb : ℕ} [NeZero L] [NeZero Wb]
    (nrm : (ZMod L × Fin Wb) → (ZMod L × Fin Wb) → ℝ)
    (hnrm0 : ∀ i j, 0 ≤ nrm i j)
    (i0 : ZMod L × Fin Wb) {δ : ℝ} (hδ0 : 0 ≤ δ) (hdiag : nrm i0 i0 ≤ 1 + δ)
    (Cx : ZMod L → ZMod L → ℝ) (hCx0 : ∀ a b, 0 ≤ Cx a b)
    (hoff : ∀ v : ZMod L × Fin Wb, v ≠ i0 → nrm v i0 ^ 2 ≤ Cx v.1 i0.1)
    (blk : ZMod L) :
    ∑ v : ZMod L × Fin Wb, Lemma57.blkW L Wb v blk * nrm v i0 ≤
      Real.sqrt (Cx blk i0.1) + Real.sqrt ((Wb : ℝ)⁻¹) * (1 + δ) := by
  classical
  have hS0 : 0 ≤ ∑ v : ZMod L × Fin Wb, Lemma57.blkW L Wb v blk * nrm v i0 :=
    Finset.sum_nonneg fun v _ => mul_nonneg (Lemma57.blkW_nonneg L Wb v blk) (hnrm0 v i0)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod L × Fin Wb))
    (fun v => Real.sqrt (Lemma57.blkW L Wb v blk))
    (fun v => Real.sqrt (Lemma57.blkW L Wb v blk) * nrm v i0)
  have heq1 : ∀ v : ZMod L × Fin Wb,
      Real.sqrt (Lemma57.blkW L Wb v blk) *
        (Real.sqrt (Lemma57.blkW L Wb v blk) * nrm v i0)
      = Lemma57.blkW L Wb v blk * nrm v i0 := fun v => by
    rw [← mul_assoc, Real.mul_self_sqrt (Lemma57.blkW_nonneg L Wb v blk)]
  have heq2 : ∀ v : ZMod L × Fin Wb,
      Real.sqrt (Lemma57.blkW L Wb v blk) ^ 2 = Lemma57.blkW L Wb v blk :=
    fun v => Real.sq_sqrt (Lemma57.blkW_nonneg L Wb v blk)
  have heq3 : ∀ v : ZMod L × Fin Wb,
      (Real.sqrt (Lemma57.blkW L Wb v blk) * nrm v i0) ^ 2
      = Lemma57.blkW L Wb v blk * nrm v i0 ^ 2 := fun v => by rw [mul_pow, heq2]
  simp only [heq1, heq2, heq3] at hcs
  rw [Lemma57.sum_blkW, one_mul] at hcs
  have hmem : i0 ∈ (Finset.univ : Finset (ZMod L × Fin Wb)) := Finset.mem_univ i0
  have hsplit :
      (∑ v : ZMod L × Fin Wb, Lemma57.blkW L Wb v blk * nrm v i0 ^ 2) =
        (∑ v ∈ (Finset.univ : Finset (ZMod L × Fin Wb)).erase i0,
          Lemma57.blkW L Wb v blk * nrm v i0 ^ 2)
          + Lemma57.blkW L Wb i0 blk * nrm i0 i0 ^ 2 := by
    rw [Finset.sum_erase_add _ _ hmem]
  have hdiagTerm : Lemma57.blkW L Wb i0 blk * nrm i0 i0 ^ 2 ≤ (Wb : ℝ)⁻¹ * (1 + δ) ^ 2 := by
    have hb : Lemma57.blkW L Wb i0 blk ≤ (Wb : ℝ)⁻¹ := by
      unfold Lemma57.blkW
      split_ifs
      · exact le_refl _
      · positivity
    have hn2 : nrm i0 i0 ^ 2 ≤ (1 + δ) ^ 2 := pow_le_pow_left₀ (hnrm0 i0 i0) hdiag 2
    calc Lemma57.blkW L Wb i0 blk * nrm i0 i0 ^ 2
        ≤ (Wb : ℝ)⁻¹ * nrm i0 i0 ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
      _ ≤ (Wb : ℝ)⁻¹ * (1 + δ) ^ 2 := mul_le_mul_of_nonneg_left hn2 (by positivity)
  have hoffTerm :
      (∑ v ∈ (Finset.univ : Finset (ZMod L × Fin Wb)).erase i0,
        Lemma57.blkW L Wb v blk * nrm v i0 ^ 2) ≤ Cx blk i0.1 := by
    have hstep : ∀ v ∈ (Finset.univ : Finset (ZMod L × Fin Wb)).erase i0,
        Lemma57.blkW L Wb v blk * nrm v i0 ^ 2 ≤ Lemma57.blkW L Wb v blk * Cx blk i0.1 := by
      intro v hv
      have hvne : v ≠ i0 := (Finset.mem_erase.1 hv).1
      by_cases hvb : v.1 = blk
      · have hoffv := hoff v hvne
        rw [hvb] at hoffv
        exact mul_le_mul_of_nonneg_left hoffv (Lemma57.blkW_nonneg L Wb v blk)
      · have hz : Lemma57.blkW L Wb v blk = 0 := by unfold Lemma57.blkW; rw [if_neg hvb]
        rw [hz]; simp
    calc (∑ v ∈ (Finset.univ : Finset (ZMod L × Fin Wb)).erase i0,
        Lemma57.blkW L Wb v blk * nrm v i0 ^ 2)
        ≤ ∑ v ∈ (Finset.univ : Finset (ZMod L × Fin Wb)).erase i0,
            Lemma57.blkW L Wb v blk * Cx blk i0.1 := Finset.sum_le_sum hstep
      _ = (∑ v ∈ (Finset.univ : Finset (ZMod L × Fin Wb)).erase i0,
            Lemma57.blkW L Wb v blk) * Cx blk i0.1 := by rw [Finset.sum_mul]
      _ ≤ (∑ v : ZMod L × Fin Wb, Lemma57.blkW L Wb v blk) * Cx blk i0.1 :=
          mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun v _ _ => Lemma57.blkW_nonneg L Wb v blk))
            (hCx0 blk i0.1)
      _ = Cx blk i0.1 := by rw [Lemma57.sum_blkW]; ring
  have hSqLe :
      (∑ v : ZMod L × Fin Wb, Lemma57.blkW L Wb v blk * nrm v i0 ^ 2) ≤
        Cx blk i0.1 + (Wb : ℝ)⁻¹ * (1 + δ) ^ 2 := by
    rw [hsplit]; exact add_le_add hoffTerm hdiagTerm
  have hSsq :
      (∑ v : ZMod L × Fin Wb, Lemma57.blkW L Wb v blk * nrm v i0) ^ 2 ≤
        Cx blk i0.1 + (Wb : ℝ)⁻¹ * (1 + δ) ^ 2 := hcs.trans hSqLe
  have hfinal :
      (∑ v : ZMod L × Fin Wb, Lemma57.blkW L Wb v blk * nrm v i0) ≤
        Real.sqrt (Cx blk i0.1 + (Wb : ℝ)⁻¹ * (1 + δ) ^ 2) :=
    (Real.le_sqrt hS0 (add_nonneg (hCx0 blk i0.1) (by positivity))).2 hSsq
  calc (∑ v : ZMod L × Fin Wb, Lemma57.blkW L Wb v blk * nrm v i0)
      ≤ Real.sqrt (Cx blk i0.1 + (Wb : ℝ)⁻¹ * (1 + δ) ^ 2) := hfinal
    _ ≤ Real.sqrt (Cx blk i0.1) + Real.sqrt ((Wb : ℝ)⁻¹ * (1 + δ) ^ 2) :=
        sqrt_add_le_aux (hCx0 _ _) (by positivity)
    _ = Real.sqrt (Cx blk i0.1) + Real.sqrt ((Wb : ℝ)⁻¹) * (1 + δ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]

/-! ### The main statement -/

/-- **(T2): (4.2) ⇒ (5.57), column and row forms, at (2.73)-reduced strength.**

For every `d : Gauss.Dims`, under the Step-1 hypotheses (the hypothesis list of
`RBM.Gauss.step1Hyp_gauss_of_scale''`), for every `τ > 0`: with high probability, for every
`u ∈ [s_N, t_N]` and every pair of block labels `x, y`, both orientations of the single-`G`
block average are at most `N^τ √(ℓ_u/ℓ_s) (√A_u)⁻¹`. -/
theorem highProb_eq557_colRow (d : Dims) {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N))
    (τ : ℝ) (hτ : 0 < τ) :
    HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N, ∀ x y : ZMod (d.L N),
      (∀ p : ZMod (d.L N) × Fin (d.W N), p.1 = y →
        ∑ r, Lemma57.blkW (d.L N) (d.W N) r x *
          ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) r p‖ ≤
        (N : ℝ) ^ τ * Real.sqrt ((band d).ell N (u : ℝ) / (band d).ell N (s N)) *
          (Real.sqrt ((band d).scale E N (u : ℝ)))⁻¹) ∧
      (∀ r : ZMod (d.L N) × Fin (d.W N), r.1 = x →
        ∑ p, Lemma57.blkW (d.L N) (d.W N) p y *
          ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) r p‖ ≤
        (N : ℝ) ^ τ * Real.sqrt ((band d).ell N (u : ℝ) / (band d).ell N (s N)) *
          (Real.sqrt ((band d).scale E N (u : ℝ)))⁻¹)}) := by
  have hE2 : |E| < 2 := by linarith
  have hStep : Step1.Hyp (sample d) E s t :=
    step1Hyp_gauss_of_scale'' d hκ hE hB hs0 hst ht1 hcond hc0 hreg
  have hCond272Reg : Cond272Reg (band d) E s t c := ⟨hcond, hreg⟩
  have hGoodHP : HighProb (P d) (goodSetFlow d E s t (flowDelta d E t)) :=
    APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow d hE2 hs0 hst ht1 hc0 hCond272Reg hB
  set τ0 : ℝ := τ / 4 with hτ0def
  have hτ0 : 0 < τ0 := by rw [hτ0def]; linarith
  have hEntry : EntryBoundFlow' d E s t (fun N => 2 * (N : ℝ) ^ (-(2 : ℝ))) :=
    entryBoundFlow_floor d hE2 hs0 hst ht1 (K := 1) zero_le_one
      (rpow_neg_one_le_etaT_of_scale_ge d hE2 ht1 hc0 hreg) (c₀ := c / 6) (by linarith)
      (flowDelta_le_rpow_neg d hreg) (B := 2) (by norm_num)
  have hEntryHP := StochDom.highProb hEntry hτ0
  have hApriori :=
    Step1.apriori (sample d) hκ hE hB hs0 hst ht1 hcond hc0 hreg hStep 2 (by norm_num)
  have hAprioriHP := StochDom.highProb hApriori hτ0
  have hAll := (hGoodHP.inter hEntryHP).inter hAprioriHP
  refine hAll.mono ?_
  filter_upwards [flowDelta_le_rpow_neg d hreg, d.dim,
    eventually_le_rpow (2 * Real.sqrt 11) (show (0 : ℝ) < 3 * τ / 4 by linarith),
    eventually_le_rpow (4 : ℝ) hτ, Filter.eventually_ge_atTop (2 : ℕ)] with
    N hδN hdimN hgrow11 hgrow4 hN2 ω hω u x y
  obtain ⟨⟨hωgood, hωentry⟩, hωapriori⟩ := hω
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 N)
  obtain ⟨hAu_pos, hηu_pos, hηu_le1, hℓu_ge1, hℓu_leL⟩ :=
    EEBridge.eeFacts (band d) hE2 hs0 ht1 N u
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hℓs_ge1 : (1 : ℝ) ≤ (band d).ell N (s N) :=
    one_le_ellHat_of_nonneg ((band d).one_le_L N) (hs0 N) hs1
  have hℓs_pos : (0 : ℝ) < (band d).ell N (s N) := by linarith
  have hℓmono : (band d).ell N (s N) ≤ (band d).ell N (u : ℝ) := Step3.ellHat_mono u.2.1 hu1
  set ru : ℝ := (band d).ell N (u : ℝ) / (band d).ell N (s N) with hrudef
  have hr_ge1 : (1 : ℝ) ≤ ru := (le_div_iff₀ hℓs_pos).2 (by linarith)
  set Au : ℝ := (band d).scale E N (u : ℝ) with hAudef
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdimN.1
  have hWpos : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hAu_le_N : Au ≤ (N : ℝ) := by
    rw [hAudef]
    show (d.W N : ℝ) * (band d).ell N (u : ℝ) * etaT E (u : ℝ) ≤ (N : ℝ)
    calc (d.W N : ℝ) * (band d).ell N (u : ℝ) * etaT E (u : ℝ)
        ≤ (d.W N : ℝ) * (d.L N : ℝ) * 1 := by
          have hL := hℓu_leL
          have hLd : (band d).ell N (u : ℝ) ≤ (d.L N : ℝ) := by
            simpa [band_L] using hL
          gcongr
      _ = (d.W N : ℝ) * (d.L N : ℝ) := mul_one _
      _ ≤ (N : ℝ) := hWL
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hAu_le_W : Au ≤ (d.W N : ℝ) := by
    rw [hAudef]
    show (d.W N : ℝ) * (band d).ell N (u : ℝ) * etaT E (u : ℝ) ≤ (d.W N : ℝ)
    have hle1 : (band d).ell N (u : ℝ) * etaT E (u : ℝ) ≤ 1 := by
      have hb : (band d).ell N (u : ℝ) = ellHat (d.L N) ((u : ℝ) : ℂ) := rfl
      rw [hb, mul_comm]
      exact etaT_mul_ellHat_le (d.three_le_L N) hE2.le hu0 hu1
    calc (d.W N : ℝ) * (band d).ell N (u : ℝ) * etaT E (u : ℝ)
        = (d.W N : ℝ) * ((band d).ell N (u : ℝ) * etaT E (u : ℝ)) := by ring
      _ ≤ (d.W N : ℝ) * 1 := by gcongr
      _ = (d.W N : ℝ) := mul_one _
  have hW_inv_le_Au_inv : (d.W N : ℝ)⁻¹ ≤ Au⁻¹ := by
    have h := one_div_le_one_div_of_le hAu_pos hAu_le_W
    simpa [one_div] using h
  have hAu_le_Nsq_half : Au ≤ (N : ℝ) ^ 2 / 2 := by
    have h1 : (N : ℝ) ≤ (N : ℝ) ^ 2 / 2 := by nlinarith
    linarith [hAu_le_N, h1]
  have hfl_le_Au_inv : 2 * (N : ℝ) ^ (-(2 : ℝ)) ≤ Au⁻¹ := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hrpow : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ) ^ 2)⁻¹ := by
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hNpos.le,
        Real.rpow_natCast]
    rw [hrpow]
    have hXpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have hcross : 2 * Au ≤ (N : ℝ) ^ 2 := by linarith [hAu_le_Nsq_half]
    have hdiv : (2 : ℝ) / ((N : ℝ) ^ 2) ≤ 1 / Au := by
      rw [div_le_div_iff₀ hXpos hAu_pos]
      linarith [hcross]
    rw [div_eq_mul_inv, div_eq_mul_inv, one_mul] at hdiv
    exact hdiv
  have hδ0 : (0 : ℝ) ≤ flowDelta d E t N := by
    unfold flowDelta
    exact Real.rpow_nonneg (inv_nonneg.2 ((band d).scale_nonneg E N (ht1 N).le)) _
  have hδle1 : flowDelta d E t N ≤ 1 := by
    have hc6 : (0 : ℝ) < c / 6 := by linarith
    have h1 : (N : ℝ) ^ (-(c / 6)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
    exact hδN.trans h1
  have hτ0_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ τ0 := Real.one_le_rpow hN1' hτ0.le
  have hru_sqrt_ge1 : (1 : ℝ) ≤ Real.sqrt ru :=
    (Real.le_sqrt (by norm_num) (by linarith)).2 (by simpa using hr_ge1)
  have hAu_sqrt_pos : (0 : ℝ) < Real.sqrt Au := Real.sqrt_pos.2 hAu_pos
  have hgrowFinal : Real.sqrt 11 * (N : ℝ) ^ τ0 ≤ (N : ℝ) ^ τ / 2 := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hcomb : (2 * Real.sqrt 11) * (N : ℝ) ^ τ0 ≤ (N : ℝ) ^ (3 * τ / 4) * (N : ℝ) ^ τ0 :=
      mul_le_mul_of_nonneg_right hgrow11 (Real.rpow_nonneg hNpos.le _)
    have heq : (N : ℝ) ^ (3 * τ / 4) * (N : ℝ) ^ τ0 = (N : ℝ) ^ τ := by
      rw [← Real.rpow_add hNpos, hτ0def]; congr 1; ring
    rw [heq] at hcomb
    linarith
  have hCxRaw_nonneg : ∀ a b : ZMod (d.L N),
      (0 : ℝ) ≤ (∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
          Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
        + (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        + 2 * (N : ℝ) ^ (-(2 : ℝ)) := by
    intro a b
    have hL1 : ∀ a' b' : ZMod (d.L N),
        (0 : ℝ) ≤ Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a') := fun a' b' =>
      Lre_nonneg (Hflow_isHermitian d N (u : ℝ) ω) (b + b') (a + a')
    have h1 : (0 : ℝ) ≤ ∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
        Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a') :=
      Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ => hL1 a' b'
    have h2 : (0 : ℝ) ≤ if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0 := by
      split_ifs <;> positivity
    have h3 : (0 : ℝ) ≤ 2 * (N : ℝ) ^ (-(2 : ℝ)) := by positivity
    linarith
  have hAprioriBound : ∀ a' b' : ZMod (d.L N),
      Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) a' b' ≤ (N : ℝ) ^ τ0 * ru * Au⁻¹ := by
    intro a' b'
    have hmem := hωapriori (u, (![true, false], ![a', b']))
    simp [LoopData.idx, List.ofFn_succ] at hmem
    rw [← hrudef, ← hAudef] at hmem
    have hre := Complex.re_le_norm
      (gloop (d.L N) (d.W N) (Hflow d N (u : ℝ) ω) (zt E (u : ℝ))
        (⟨[true, false], [a', b']⟩ : LoopIdx (ZMod (d.L N))))
    have hLreDef : Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) a' b' =
        (gloop (d.L N) (d.W N) (Hflow d N (u : ℝ) ω) (zt E (u : ℝ))
          (⟨[true, false], [a', b']⟩ : LoopIdx (ZMod (d.L N)))).re := rfl
    rw [hLreDef]
    calc (gloop (d.L N) (d.W N) (Hflow d N (u : ℝ) ω) (zt E (u : ℝ))
          (⟨[true, false], [a', b']⟩ : LoopIdx (ZMod (d.L N)))).re
        ≤ ‖gloop (d.L N) (d.W N) (Hflow d N (u : ℝ) ω) (zt E (u : ℝ))
          (⟨[true, false], [a', b']⟩ : LoopIdx (ZMod (d.L N)))‖ := hre
      _ ≤ (N : ℝ) ^ τ0 * (ru * Au⁻¹) := hmem
      _ = (N : ℝ) ^ τ0 * ru * Au⁻¹ := by ring
  have hCxRaw_le : ∀ a b : ZMod (d.L N),
      (∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
          Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
        + (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        + 2 * (N : ℝ) ^ (-(2 : ℝ))
        ≤ (9 * (N : ℝ) ^ τ0 + 2) * ru * Au⁻¹ := by
    intro a b
    have hsum9 : (∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
        Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
        ≤ 9 * ((N : ℝ) ^ τ0 * ru * Au⁻¹) := by
      have hcard := card_sbSupport (d.L N) (d.three_le_L N)
      have hinner : ∀ a' ∈ sbSupport (d.L N), (∑ b' ∈ sbSupport (d.L N),
          Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
          ≤ (sbSupport (d.L N)).card * ((N : ℝ) ^ τ0 * ru * Au⁻¹) := by
        intro a' _
        calc (∑ b' ∈ sbSupport (d.L N),
            Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
            ≤ ∑ _b' ∈ sbSupport (d.L N), (N : ℝ) ^ τ0 * ru * Au⁻¹ :=
              Finset.sum_le_sum fun b' _ => hAprioriBound (b + b') (a + a')
          _ = (sbSupport (d.L N)).card * ((N : ℝ) ^ τ0 * ru * Au⁻¹) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      calc (∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
          Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
          ≤ ∑ _a' ∈ sbSupport (d.L N),
              (sbSupport (d.L N)).card * ((N : ℝ) ^ τ0 * ru * Au⁻¹) :=
            Finset.sum_le_sum hinner
        _ = (sbSupport (d.L N)).card * ((sbSupport (d.L N)).card
              * ((N : ℝ) ^ τ0 * ru * Au⁻¹)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = 9 * ((N : ℝ) ^ τ0 * ru * Au⁻¹) := by rw [hcard]; ring
    have hind : (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0) ≤ Au⁻¹ := by
      split_ifs
      · exact hW_inv_le_Au_inv
      · positivity
    have hindr : Au⁻¹ ≤ ru * Au⁻¹ := by
      have hAuinv0 : (0 : ℝ) ≤ Au⁻¹ := by positivity
      nlinarith [hr_ge1, hAuinv0]
    have hflr : 2 * (N : ℝ) ^ (-(2 : ℝ)) ≤ ru * Au⁻¹ :=
      hfl_le_Au_inv.trans hindr
    have hindr2 : (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0) ≤ ru * Au⁻¹ :=
      hind.trans hindr
    nlinarith [hsum9, hindr2, hflr]
  have hnumeric : ∀ a b : ZMod (d.L N),
      Real.sqrt ((N : ℝ) ^ τ0 * ((∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
          Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
        + (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        + 2 * (N : ℝ) ^ (-(2 : ℝ))))
        + Real.sqrt ((d.W N : ℝ)⁻¹) * (1 + flowDelta d E t N) ≤
      (N : ℝ) ^ τ * Real.sqrt ru * (Real.sqrt Au)⁻¹ := by
    intro a b
    have hstep1 : (N : ℝ) ^ τ0 * ((∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
          Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
        + (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        + 2 * (N : ℝ) ^ (-(2 : ℝ)))
        ≤ 11 * ((N : ℝ) ^ τ0 * (N : ℝ) ^ τ0) * ru * Au⁻¹ := by
      have h1 := hCxRaw_le a b
      have h2 : (N : ℝ) ^ τ0 * ((9 * (N : ℝ) ^ τ0 + 2) * ru * Au⁻¹)
          ≤ 11 * ((N : ℝ) ^ τ0 * (N : ℝ) ^ τ0) * ru * Au⁻¹ := by
        have hru0 : (0 : ℝ) ≤ ru := by linarith
        have hAuinv0 : (0 : ℝ) ≤ Au⁻¹ := by positivity
        have hruAu0 : (0 : ℝ) ≤ ru * Au⁻¹ := mul_nonneg hru0 hAuinv0
        have hcoef : (N : ℝ) ^ τ0 * (9 * (N : ℝ) ^ τ0 + 2) ≤ 11 * ((N : ℝ) ^ τ0 * (N : ℝ) ^ τ0) := by
          nlinarith [hτ0_ge1]
        calc (N : ℝ) ^ τ0 * ((9 * (N : ℝ) ^ τ0 + 2) * ru * Au⁻¹)
            = ((N : ℝ) ^ τ0 * (9 * (N : ℝ) ^ τ0 + 2)) * (ru * Au⁻¹) := by ring
          _ ≤ (11 * ((N : ℝ) ^ τ0 * (N : ℝ) ^ τ0)) * (ru * Au⁻¹) :=
              mul_le_mul_of_nonneg_right hcoef hruAu0
          _ = 11 * ((N : ℝ) ^ τ0 * (N : ℝ) ^ τ0) * ru * Au⁻¹ := by ring
      calc (N : ℝ) ^ τ0 * ((∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
            Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
          + (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
          + 2 * (N : ℝ) ^ (-(2 : ℝ)))
          ≤ (N : ℝ) ^ τ0 * ((9 * (N : ℝ) ^ τ0 + 2) * ru * Au⁻¹) := by
            apply mul_le_mul_of_nonneg_left h1
            exact Real.rpow_nonneg (by linarith) _
        _ ≤ 11 * ((N : ℝ) ^ τ0 * (N : ℝ) ^ τ0) * ru * Au⁻¹ := h2
    have hstep2 : Real.sqrt ((N : ℝ) ^ τ0 * ((∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
          Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
        + (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        + 2 * (N : ℝ) ^ (-(2 : ℝ))))
        ≤ Real.sqrt 11 * (N : ℝ) ^ τ0 * Real.sqrt ru * (Real.sqrt Au)⁻¹ := by
      have hrhs_eq : 11 * ((N : ℝ) ^ τ0 * (N : ℝ) ^ τ0) * ru * Au⁻¹
          = (Real.sqrt 11 * (N : ℝ) ^ τ0 * Real.sqrt ru * (Real.sqrt Au)⁻¹) ^ 2 := by
        have h11 : (0 : ℝ) ≤ (11 : ℝ) := by norm_num
        have hNnn : (0 : ℝ) ≤ (N : ℝ) ^ τ0 := Real.rpow_nonneg (by linarith) _
        have hrunn : (0 : ℝ) ≤ ru := by linarith
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt h11, Real.sq_sqrt hrunn,
          inv_pow, Real.sq_sqrt hAu_pos.le]
        ring
      have hnn : (0 : ℝ) ≤ Real.sqrt 11 * (N : ℝ) ^ τ0 * Real.sqrt ru * (Real.sqrt Au)⁻¹ := by
        positivity
      have hle : (N : ℝ) ^ τ0 * ((∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
            Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
          + (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
          + 2 * (N : ℝ) ^ (-(2 : ℝ)))
          ≤ (Real.sqrt 11 * (N : ℝ) ^ τ0 * Real.sqrt ru * (Real.sqrt Au)⁻¹) ^ 2 := by
        rw [← hrhs_eq]; exact hstep1
      calc Real.sqrt ((N : ℝ) ^ τ0 * ((∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
              Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
            + (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
            + 2 * (N : ℝ) ^ (-(2 : ℝ))))
          ≤ Real.sqrt ((Real.sqrt 11 * (N : ℝ) ^ τ0 * Real.sqrt ru * (Real.sqrt Au)⁻¹) ^ 2) :=
            Real.sqrt_le_sqrt hle
        _ = Real.sqrt 11 * (N : ℝ) ^ τ0 * Real.sqrt ru * (Real.sqrt Au)⁻¹ := Real.sqrt_sq hnn
    have hstep3 : Real.sqrt 11 * (N : ℝ) ^ τ0 * Real.sqrt ru * (Real.sqrt Au)⁻¹
        ≤ ((N : ℝ) ^ τ / 2) * Real.sqrt ru * (Real.sqrt Au)⁻¹ := by
      have hnn : (0 : ℝ) ≤ Real.sqrt ru * (Real.sqrt Au)⁻¹ := by positivity
      have := mul_le_mul_of_nonneg_right hgrowFinal hnn
      calc Real.sqrt 11 * (N : ℝ) ^ τ0 * Real.sqrt ru * (Real.sqrt Au)⁻¹
          = (Real.sqrt 11 * (N : ℝ) ^ τ0) * (Real.sqrt ru * (Real.sqrt Au)⁻¹) := by ring
        _ ≤ ((N : ℝ) ^ τ / 2) * (Real.sqrt ru * (Real.sqrt Au)⁻¹) := this
        _ = ((N : ℝ) ^ τ / 2) * Real.sqrt ru * (Real.sqrt Au)⁻¹ := by ring
    have hdiagbound : Real.sqrt ((d.W N : ℝ)⁻¹) * (1 + flowDelta d E t N)
        ≤ ((N : ℝ) ^ τ / 2) * Real.sqrt ru * (Real.sqrt Au)⁻¹ := by
      have h1 : Real.sqrt ((d.W N : ℝ)⁻¹) ≤ Real.sqrt Au⁻¹ := Real.sqrt_le_sqrt hW_inv_le_Au_inv
      have h2 : Real.sqrt Au⁻¹ = (Real.sqrt Au)⁻¹ := Real.sqrt_inv Au
      have h3 : (1 : ℝ) + flowDelta d E t N ≤ 2 := by linarith
      have hAuinvnn : (0 : ℝ) ≤ (Real.sqrt Au)⁻¹ := by positivity
      have hchain : Real.sqrt ((d.W N : ℝ)⁻¹) * (1 + flowDelta d E t N)
          ≤ (Real.sqrt Au)⁻¹ * 2 := by
        rw [← h2]
        calc Real.sqrt ((d.W N : ℝ)⁻¹) * (1 + flowDelta d E t N)
            ≤ Real.sqrt Au⁻¹ * (1 + flowDelta d E t N) :=
              mul_le_mul_of_nonneg_right h1 (by linarith)
          _ ≤ Real.sqrt Au⁻¹ * 2 := by
              apply mul_le_mul_of_nonneg_left h3
              rw [h2]; positivity
      have h4 : (Real.sqrt Au)⁻¹ * 2 ≤ (Real.sqrt Au)⁻¹ * Real.sqrt ru * ((N : ℝ) ^ τ / 2) := by
        have h4a : (2 : ℝ) ≤ Real.sqrt ru * ((N : ℝ) ^ τ / 2) * 1 := by
          have h4b : (2 : ℝ) ≤ (N : ℝ) ^ τ / 2 := by linarith [hgrow4]
          calc (2 : ℝ) ≤ (N : ℝ) ^ τ / 2 := h4b
            _ ≤ Real.sqrt ru * ((N : ℝ) ^ τ / 2) := by
                nlinarith [hru_sqrt_ge1, (by linarith [hgrow4] : (0:ℝ) ≤ (N:ℝ)^τ/2)]
            _ = Real.sqrt ru * ((N : ℝ) ^ τ / 2) * 1 := by ring
        calc (Real.sqrt Au)⁻¹ * 2 ≤ (Real.sqrt Au)⁻¹ * (Real.sqrt ru * ((N : ℝ) ^ τ / 2) * 1) := by
              apply mul_le_mul_of_nonneg_left _ hAuinvnn
              linarith [h4a]
          _ = (Real.sqrt Au)⁻¹ * Real.sqrt ru * ((N : ℝ) ^ τ / 2) := by ring
      calc Real.sqrt ((d.W N : ℝ)⁻¹) * (1 + flowDelta d E t N)
          ≤ (Real.sqrt Au)⁻¹ * 2 := hchain
        _ ≤ (Real.sqrt Au)⁻¹ * Real.sqrt ru * ((N : ℝ) ^ τ / 2) := h4
        _ = ((N : ℝ) ^ τ / 2) * Real.sqrt ru * (Real.sqrt Au)⁻¹ := by ring
    calc Real.sqrt ((N : ℝ) ^ τ0 * ((∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
            Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
          + (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
          + 2 * (N : ℝ) ^ (-(2 : ℝ))))
        + Real.sqrt ((d.W N : ℝ)⁻¹) * (1 + flowDelta d E t N)
        ≤ Real.sqrt 11 * (N : ℝ) ^ τ0 * Real.sqrt ru * (Real.sqrt Au)⁻¹
          + Real.sqrt ((d.W N : ℝ)⁻¹) * (1 + flowDelta d E t N) := by linarith [hstep2]
      _ ≤ ((N : ℝ) ^ τ / 2) * Real.sqrt ru * (Real.sqrt Au)⁻¹
          + ((N : ℝ) ^ τ / 2) * Real.sqrt ru * (Real.sqrt Au)⁻¹ := add_le_add hstep3 hdiagbound
      _ = (N : ℝ) ^ τ * Real.sqrt ru * (Real.sqrt Au)⁻¹ := by ring
  have hdiag0 : ∀ i : ZMod (d.L N) × Fin (d.W N),
      ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) i i‖ ≤ 1 + flowDelta d E t N := by
    intro i
    have hgd : GoodEvent (green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ))) (mE E)
        (flowDelta d E t N) := hωgood (u : ℝ) u.2
    exact hgd.norm_diag_le (norm_mE hE2.le) i
  have hoffcol : ∀ p v : ZMod (d.L N) × Fin (d.W N), v ≠ p →
      ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) v p‖ ^ 2
        ≤ (N : ℝ) ^ τ0 * ((∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
            Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (p.1 + b') (v.1 + a'))
          + (if v.1 - p.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
          + 2 * (N : ℝ) ^ (-(2 : ℝ))) := by
    intro p v hvp
    have hmemgood : (u : ℝ) ∈ Set.Icc (s N) (t N) := u.2
    have hmemq := hωentry (u, (⟨(v, p), hvp⟩ : OffPair d.L d.W N))
    simp only [Set.mem_ofPred_eq] at hmemq
    have hginmem : ω ∈ goodSet (fun N ω => Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (mE E)
        (flowDelta d E t) N := hωgood (u : ℝ) hmemgood
    rw [Set.indicator_of_mem hginmem] at hmemq
    exact hmemq
  have hoffrow : ∀ r v : ZMod (d.L N) × Fin (d.W N), v ≠ r →
      ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) r v‖ ^ 2
        ≤ (N : ℝ) ^ τ0 * ((∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
            Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (v.1 + b') (r.1 + a'))
          + (if r.1 - v.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
          + 2 * (N : ℝ) ^ (-(2 : ℝ))) := by
    intro r v hvr
    have hrv : r ≠ v := fun h => hvr h.symm
    have hmemgood : (u : ℝ) ∈ Set.Icc (s N) (t N) := u.2
    have hmemq := hωentry (u, (⟨(r, v), hrv⟩ : OffPair d.L d.W N))
    simp only [Set.mem_ofPred_eq] at hmemq
    have hginmem : ω ∈ goodSet (fun N ω => Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (mE E)
        (flowDelta d E t) N := hωgood (u : ℝ) hmemgood
    rw [Set.indicator_of_mem hginmem] at hmemq
    exact hmemq
  refine ⟨?_, ?_⟩
  · intro p hp
    have hb := blockSum_le
      (nrm := fun i j => ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) i j‖)
      (hnrm0 := fun i j => norm_nonneg _)
      (i0 := p) (δ := flowDelta d E t N) hδ0 (hdiag0 p)
      (Cx := fun a b => (N : ℝ) ^ τ0 * ((∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
          Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (b + b') (a + a'))
        + (if a - b ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        + 2 * (N : ℝ) ^ (-(2 : ℝ))))
      (hCx0 := fun a b => mul_nonneg (Real.rpow_nonneg (by linarith) _) (hCxRaw_nonneg a b))
      (hoff := fun v hv => hoffcol p v hv) (blk := x)
    rw [hp] at hb
    exact hb.trans (hnumeric x y)
  · intro r hr
    have hb := blockSum_le
      (nrm := fun i j => ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) j i‖)
      (hnrm0 := fun i j => norm_nonneg _)
      (i0 := r) (δ := flowDelta d E t N) hδ0 (hdiag0 r)
      (Cx := fun a b => (N : ℝ) ^ τ0 * ((∑ a' ∈ sbSupport (d.L N), ∑ b' ∈ sbSupport (d.L N),
          Lre (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (a + b') (b + a'))
        + (if b - a ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        + 2 * (N : ℝ) ^ (-(2 : ℝ))))
      (hCx0 := fun a b => mul_nonneg (Real.rpow_nonneg (by linarith) _) (hCxRaw_nonneg b a))
      (hoff := fun v hv => hoffrow r v hv) (blk := y)
    rw [hr] at hb
    exact hb.trans (hnumeric x y)

/-- **(T1): (4.2) ⇒ (5.57), column form, at (2.73)-reduced strength.**

The column half of `RBM.Gauss.Step2.highProb_eq557_colRow`, on the same event. -/
theorem highProb_eq557_col (d : Dims) {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N))
    (τ : ℝ) (hτ : 0 < τ) :
    HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N, ∀ x y : ZMod (d.L N),
      ∀ p : ZMod (d.L N) × Fin (d.W N), p.1 = y →
        ∑ r, Lemma57.blkW (d.L N) (d.W N) r x *
          ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) r p‖ ≤
        (N : ℝ) ^ τ * Real.sqrt ((band d).ell N (u : ℝ) / (band d).ell N (s N)) *
          (Real.sqrt ((band d).scale E N (u : ℝ)))⁻¹}) := by
  refine (highProb_eq557_colRow d hκ hE hB hs0 hst ht1 hcond hc0 hreg τ hτ).mono ?_
  filter_upwards with N ω hω u x y p hp
  exact (hω u x y).1 p hp

end RBM.Gauss.Step2
