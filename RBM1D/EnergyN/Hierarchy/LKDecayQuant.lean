/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.LKDecayQuant
import RBM1D.Flow.Scales

/-!
# The flow decay at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.4, Lemma 5.9.

`RBM.LKDecayQuant.highProb_flowDec_of_aprioriDecayN`: from the a priori decay (2.76), the flow
decay event `FlowDec` holds with high probability, at an `N`-dependent energy `E : ℕ → ℝ`.

## The external `κ`

The proof needs `(max 1 (mE (E N)).im⁻¹)^2 ≤ N` for large `N`, and `(mE (E N)).im` depends on
`N`. The theorem takes an explicit `κ` with `|E N| ≤ 2 - κ`, derives the `N`-independent bound
`mκ := √(2κ')/2 ≤ (mE (E N)).im` for every `N` (`κ' := min κ 1`, `mE_im_ge`,
`Flow/Scales.lean`), and applies `tendsto_natCast_atTop_atTop.eventually_ge_atTop` to the fixed
constant `(max 1 mκ⁻¹)^2`; a pointwise bound then gives `(max 1 (mE (E N)).im⁻¹)^2 ≤ N`. Every
other constant of the proof (`cKbound`, `cKexp`, `cZero`, the `L`/`W` bandwidth bounds) is
`E`-free. `RBM.LKDecayQuant.prefactor_le` takes its `(mE E).im`-bound as a hypothesis, so it is
used at `E N` directly.
-/

namespace RBM

namespace LKDecayQuant

open MeasureTheory Filter Real SumZeroDyn

section ProduceN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℕ → ℝ} {s t : ℕ → ℝ}

-- The proof carries a fixed-`κ` bound on top of a long arithmetic chain; raise the heartbeat
-- limit accordingly.
set_option maxHeartbeats 1000000 in
/-- **The flow decay event `FlowDec` with high probability, from (2.76), at an `N`-dependent
energy.** The constant `max 1 (mE (E N)).im⁻¹` is bounded by the uniform `max 1 mκ⁻¹`
(`κ' := min κ 1`, `mκ := √(2κ')/2 ≤ (mE (E N)).im` for every `N`, by `mE_im_ge`; only `0 < κ`
is assumed, as in `RBM.Step1.eq52_halfN`). -/
theorem highProb_flowDec_of_aprioriDecayN {κ : ℝ} (hκ0 : 0 < κ)
    (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {τ : ℝ} (hτ : 0 < τ)
    {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT (E N) (s N) / etaT (E N) p.1) ^ 4 * (B.scale (E N) N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2)) :
    HighProb B.P (fun N => FlowDec X (E N) s t (fun N => (N : ℝ) ^ (-c)) τ N) := by
  classical
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hD₀0 : (0 : ℝ) < 30 + 2 * c := by linarith
  have hc0 := cZero_pos
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'2 : κ' ≤ 2 := (min_le_right κ 1).trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hmκ0 : 0 < mκ := by rw [hmκdef]; positivity
  have hm : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hCκ : ∀ N, (max 1 ((mE (E N)).im)⁻¹) ^ 2 ≤ (max 1 mκ⁻¹) ^ 2 := fun N =>
    pow_le_pow_left₀ (by positivity) (max_le_max le_rfl (inv_anti₀ hmκ0 (hm N))) 2
  refine ((hdecay (30 + 2 * c) hD₀0).highProb one_pos).mono ?_
  filter_upwards [eventually_L_le (B := B), B.bandwidth,
    SumZeroDyn.eventually_exp_small 4 (14 + c) 1 one_pos (show (0 : ℝ) < τ / 4 by linarith),
    SumZeroDyn.eventually_exp_small (2 * cKbound 2) (((2 * cKexp 2 : ℕ) : ℝ) + c) (cZero / 2)
      (by linarith) (show (0 : ℝ) < τ / 2 / 2 by linarith),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((max 1 mκ⁻¹) ^ 2),
    SumZeroDyn.eventually_const_mul_rpow_le 2 (show τ / 4 < τ / 2 by linarith),
    eventually_ge_atTop 4] with N hLN hWN hexp1 hexp2 hCE' h2N hN4
  have hCE : (max 1 ((mE (E N)).im)⁻¹) ^ 2 ≤ (N : ℝ) := (hCκ N).trans hCE'
  intro ω hω u a b hfar
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN4' : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  set uu : ℝ := (u : ℝ) with huu
  have hu0 : 0 ≤ uu := le_trans (hs0 N) u.2.1
  have hu1 : uu < 1 := lt_of_le_of_lt u.2.2 (ht1 N)
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hL0 : (0 : ℝ) < (B.L N : ℝ) := by exact_mod_cast (by omega : 0 < B.L N)
  have hA1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) :=
    Real.one_le_rpow hN1 (by linarith)
  by_cases hcut : 1 ≤ (B.L N : ℝ) * Real.sqrt (1 - uu)
  · -- the cut-off in `ℓ̂` is inactive: `ℓ_u √(1-u) = 1`
    have hell : B.ell N uu * Real.sqrt (1 - uu) = 1 := ellHat_mul_sqrt_eq_one _ hu1 hcut
    have hell1 : (1 : ℝ) ≤ B.ell N uu := one_le_ellHat_of_nonneg (by omega : 1 ≤ B.L N) hu0 hu1
    have hell0 : 0 < B.ell N uu := lt_of_lt_of_le one_pos hell1
    have hsqrt0 : 0 < Real.sqrt (1 - uu) := Real.sqrt_pos.2 (by linarith)
    have hv0 : (0 : ℝ) < 1 - uu := by linarith
    have hv1 : (1 : ℝ) - uu ≤ 1 := by linarith
    have hsqN : 1 / (N : ℝ) ≤ Real.sqrt (1 - uu) := by
      rw [div_le_iff₀ hN0]; nlinarith
    have hvN : 1 / (1 - uu) ≤ (N : ℝ) ^ 2 := by
      have hsq : Real.sqrt (1 - uu) * Real.sqrt (1 - uu) = 1 - uu := Real.mul_self_sqrt (by linarith)
      have hm2 : 1 / (N : ℝ) * (1 / (N : ℝ)) ≤ 1 - uu := by
        rw [← hsq]; exact mul_le_mul hsqN hsqN (by positivity) (Real.sqrt_nonneg _)
      rw [div_le_iff₀ hv0]
      calc (1 : ℝ) = (N : ℝ) ^ 2 * (1 / (N : ℝ) * (1 / (N : ℝ))) := by field_simp
        _ ≤ (N : ℝ) ^ 2 * (1 - uu) := mul_le_mul_of_nonneg_left hm2 (by positivity)
    -- `L^{re} ≤ |L - K| + |K|`
    have hre : Lre (X.H N uu ω) (zt (E N) uu) a b ≤ ‖X.Lval (E N) N uu ω (pmLoop a b)‖ := by
      have habs := Complex.abs_re_le_norm (X.Lval (E N) N uu ω (pmLoop a b))
      have h0 : (X.Lval (E N) N uu ω (pmLoop a b)).re = Lre (X.H N uu ω) (zt (E N) uu) a b := rfl
      rw [h0] at habs
      exact le_trans (le_abs_self _) habs
    have hsplit : Lre (X.H N uu ω) (zt (E N) uu) a b
        ≤ X.lkErr (E N) N uu ω (pmLoop a b) + ‖B.Kval (E N) N uu (pmLoop a b)‖ := by
      refine hre.trans ?_
      have h2 : X.Lval (E N) N uu ω (pmLoop a b)
          = (X.Lval (E N) N uu ω (pmLoop a b) - B.Kval (E N) N uu (pmLoop a b))
            + B.Kval (E N) N uu (pmLoop a b) := by ring
      rw [h2]
      exact norm_add_le _ _
    -- the `L - K` half
    have hpre : (etaT (E N) (s N) / etaT (E N) uu) ^ 4 * (B.scale (E N) N uu)⁻¹ ^ 2
        ≤ (N : ℝ) ^ (13 : ℝ) :=
      prefactor_le (hE2 N) (hs0 N) u.2.1 hu1 hvN hN1 hell1 hCE
    have hprof : B.decayProf N uu (30 + 2 * c) a b
        ≤ exp (-((N : ℝ) ^ (τ / 4))) + (N : ℝ) ^ (-(15 + c)) := by
      have hfar' : (N : ℝ) ^ (τ / 2) ≤ (zdist (B.L N) (a - b) : ℝ) / B.ell N uu := by
        rw [le_div_iff₀ hell0]; linarith [hfar]
      have hmono : (N : ℝ) ^ (τ / 4)
          ≤ ((zdist (B.L N) (a - b) : ℝ) / B.ell N uu) ^ ((1 : ℝ) / 2) := by
        have he : (N : ℝ) ^ (τ / 4) = ((N : ℝ) ^ (τ / 2)) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_mul hN0.le]; ring_nf
        rw [he]
        exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hfar' (by norm_num)
      have hW : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (B.W N : ℝ) := by
        refine le_trans ?_ hWN
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [B.c_pos])
      have hWpow : (B.W N : ℝ) ^ (-(30 + 2 * c)) ≤ (N : ℝ) ^ (-(15 + c)) := by
        have hx0 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hN0 _
        have h1 : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (30 + 2 * c) ≤ ((B.W N : ℝ)) ^ (30 + 2 * c) :=
          Real.rpow_le_rpow hx0.le hW hD₀0.le
        have h2 : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (30 + 2 * c) = (N : ℝ) ^ (15 + c) := by
          rw [← Real.rpow_mul hN0.le]; ring_nf
        rw [Real.rpow_neg (by positivity), Real.rpow_neg hN0.le]
        rw [h2] at h1
        simpa [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN0 _) h1
      unfold Band.decayProf
      exact add_le_add (Real.exp_le_exp.2 (by linarith)) hWpow
    have hlk : X.lkErr (E N) N uu ω (pmLoop a b)
        ≤ (N : ℝ) ^ (1 : ℝ) * ((N : ℝ) ^ (13 : ℝ)
            * (exp (-((N : ℝ) ^ (τ / 4))) + (N : ℝ) ^ (-(15 + c)))) := by
      refine (hω (u, (a, b))).trans ?_
      have hp0 : (0 : ℝ) ≤ B.decayProf N uu (30 + 2 * c) a b := by
        unfold Band.decayProf; positivity
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN0.le _)
      exact mul_le_mul hpre hprof hp0 (Real.rpow_nonneg hN0.le _)
    -- the three numerical bounds
    have hpow14 : (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (13 : ℝ) = (N : ℝ) ^ (14 : ℝ) := by
      rw [← Real.rpow_add hN0]; norm_num
    have hb1 : (N : ℝ) ^ (14 : ℝ) * exp (-((N : ℝ) ^ (τ / 4))) ≤ 1 / 4 * (N : ℝ) ^ (-c) := by
      refine le_rpow_neg_of_mul_le hN0 ?_
      have hk : (N : ℝ) ^ (14 + c) = (N : ℝ) ^ (14 : ℝ) * (N : ℝ) ^ c := Real.rpow_add hN0 _ _
      rw [hk, one_mul] at hexp1
      nlinarith [Real.exp_pos (-((N : ℝ) ^ (τ / 4))), Real.rpow_nonneg hN0.le (14 : ℝ),
        Real.rpow_nonneg hN0.le c]
    have hb2 : (N : ℝ) ^ (14 : ℝ) * (N : ℝ) ^ (-(15 + c)) ≤ 1 / 4 * (N : ℝ) ^ (-c) := by
      refine le_rpow_neg_of_mul_le hN0 ?_
      rw [mul_assoc, ← Real.rpow_add hN0, ← Real.rpow_add hN0,
        show (14 : ℝ) + (-(15 + c) + c) = -1 by ring, Real.rpow_neg_one]
      rw [inv_eq_one_div, div_le_div_iff₀ hN0 (by norm_num)]
      linarith
    -- the `K` half
    have hK : ‖B.Kval (E N) N uu (pmLoop a b)‖
        ≤ Decay.cKdecay 2 (1 - uu)
            * exp (-(cor35Rate (1 - uu) * (B.ell N uu * (N : ℝ) ^ (τ / 2)))) := by
      have hKd := Decay.loopDecay_Kgen (B.L N) hL3 (B.W N) (norm_mSigma_le_one (hE2 N)) hu0 hu1
        (δ := 1 - uu) hv0 (Decay.one_sub_le_norm_one_sub (norm_mSigma_le_one (hE2 N)) hu0) 2
        (ℓ := B.ell N uu * (N : ℝ) ^ (τ / 2)) (by positivity)
      exact hKd (pmLoop a b) rfl (by norm_num [LoopIdx.length, pmLoop]) a (by simp [pmLoop])
        b (by simp [pmLoop]) hfar
    have hexpo : cZero / 2 * (N : ℝ) ^ (τ / 2 / 2)
        ≤ cor35Rate (1 - uu) * (B.ell N uu * (N : ℝ) ^ (τ / 2)) := by
      have hid : cor35Rate (1 - uu) * (B.ell N uu * (N : ℝ) ^ (τ / 2))
          = cZero / 4 * (N : ℝ) ^ (τ / 2) * (B.ell N uu * Real.sqrt (1 - uu)) := by
        unfold cor35Rate; ring
      rw [hid, hell, mul_one, show τ / 2 / 2 = τ / 4 by ring]
      nlinarith [Real.rpow_nonneg hN0.le (τ / 4)]
    have hterm2 : Decay.cKdecay 2 (1 - uu)
        * exp (-(cor35Rate (1 - uu) * (B.ell N uu * (N : ℝ) ^ (τ / 2))))
        ≤ 1 / 2 * (N : ℝ) ^ (-c) :=
      term2_le (m := 2) (τ := τ / 2) hN0 hv0 hv1 hvN hexpo hexp2
    calc Lre (X.H N uu ω) (zt (E N) uu) a b
        ≤ X.lkErr (E N) N uu ω (pmLoop a b) + ‖B.Kval (E N) N uu (pmLoop a b)‖ := hsplit
      _ ≤ (N : ℝ) ^ (1 : ℝ) * ((N : ℝ) ^ (13 : ℝ)
            * (exp (-((N : ℝ) ^ (τ / 4))) + (N : ℝ) ^ (-(15 + c))))
          + Decay.cKdecay 2 (1 - uu)
            * exp (-(cor35Rate (1 - uu) * (B.ell N uu * (N : ℝ) ^ (τ / 2)))) :=
          add_le_add hlk hK
      _ ≤ (N : ℝ) ^ (-c) := by
          have he : (N : ℝ) ^ (1 : ℝ) * ((N : ℝ) ^ (13 : ℝ)
              * (exp (-((N : ℝ) ^ (τ / 4))) + (N : ℝ) ^ (-(15 + c))))
              = (N : ℝ) ^ (14 : ℝ) * exp (-((N : ℝ) ^ (τ / 4)))
                + (N : ℝ) ^ (14 : ℝ) * (N : ℝ) ^ (-(15 + c)) := by
            rw [← hpow14]; ring
          rw [he]
          linarith
  · -- the cut-off is active: `ℓ_u = L`, and the radius already exceeds the diameter `L/2`
    push Not at hcut
    have hellL : B.ell N uu = (B.L N : ℝ) := ellHat_eq_L _ hu1 hcut
    have hhalf : (B.L N : ℝ) / 2 < B.ell N uu * (N : ℝ) ^ (τ / 2) := by
      rw [hellL]
      have h1 : (B.L N : ℝ) * 1 ≤ (B.L N : ℝ) * (N : ℝ) ^ (τ / 2) :=
        mul_le_mul_of_nonneg_left hA1 hL0.le
      linarith
    exact absurd (lt_of_lt_of_le (lt_of_le_of_lt (zdist_le_half (a - b)) hhalf) hfar) (lt_irrefl _)

end ProduceN

end LKDecayQuant

end RBM
