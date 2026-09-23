/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingQVProfile

/-!
# T590: deterministic absorption of the general-moving QV profile

This module performs only the pointwise deterministic simplification after
T584.  It keeps the two distinct `W⁻ᴰ` leakages and the square of the whole
endpoint-normalized root sum.
-/

namespace RBM.APrimeGeneralMovingQVAbsorption

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private theorem scale_le_N (hE : |E| < 2) {s t : Nat -> Real}
    (hs0 : forall N, 0 <= s N) (ht1 : forall N, t N < 1)
    {N : Nat} (hdim : B.W N * B.L N <= N) (u : TimeIcc s t N) :
    B.scale E N (u : Real) <= (N : Real) := by
  obtain ⟨_, heta0, heta1, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N u
  have hWL : (B.W N : Real) * (B.L N : Real) <= (N : Real) := by
    exact_mod_cast hdim
  change (B.W N : Real) * B.ell N (u : Real) * etaT E (u : Real) <= (N : Real)
  calc
    _ <= (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
    _ = (B.W N : Real) * (B.L N : Real) := by ring
    _ <= (N : Real) := hWL

private theorem rootProfile_nonneg (E : Real) (N : Nat)
    (u v D ellSource J Smax epsilon : Real) (a : LoopArg (B.L N) 2) :
    0 <= APrimeFullQV.rootProfile B E N u v D ellSource J Smax epsilon a := by
  have hT : 0 <= Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
    simpa only [Step2.tT] using
      tailT_nonneg (show 0 <= (B.W N : Real) by positivity)
        (zdist (B.L N) (a 0 - a 1))
  have hxi : 0 <= Step2.xiK (B.L N) (B.W N : Real) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  have hchi : 0 <= (if (zdist (B.L N) (a 0 - a 1) : Real) <=
      6 * ellStar (B.W N : Real) (B.ell N v) then (1 : Real) else 0) := by
    split_ifs <;> norm_num
  unfold APrimeFullQV.rootProfile
  positivity

/-- The exact near source coefficient after inserting T491's `sourceEll`. -/
noncomputable def nearSourceRate (E : Real) (s : Nat -> Real)
    (zetaSrc : Real) (N : Nat) (u : Real) : Real :=
  4 * (N : Real) ^ zetaSrc * (etaT E u)⁻¹ *
    Lemma57.cNear2 (B.W N : Real) (B.ell N u) *
    (B.ell N u / B.ell N (s N)) ^ 5

/-- The paper-style far coefficient after the quadratic source is weakened
from `A⁻¹²` to `A⁻¹³`. -/
noncomputable def absorbedFarRate (E : Real) (N : Nat) (u J : Real) : Real :=
  1200 * (etaT E u)⁻¹ * (B.scale E N u) ^ (-(1 / 3 : Real)) * J ^ 3

/-- The endpoint-normalized root profile after the complete far absorption.
The near source, repaired residual, and propagated endpoint leakage all
remain literal. -/
noncomputable def absorbedRootProfile (E : Real) (s : Nat -> Real)
    (zetaSrc : Real) (N : Nat) (u v D J : Real)
    (a : LoopArg (B.L N) 2) : Real :=
  Step2Moment.ratR E s N u ^ (-(2 : Real)) *
    Step2Moment.ratR E s N v ^ (-(2 : Real)) *
    (√(nearSourceRate E s zetaSrc N u + 2 * (B.W N : Real)⁻¹) *
        (Step2.xiK (B.L N) (B.W N : Real) (mE E).im *
            (if (zdist (B.L N) (a 0 - a 1) : Real) <=
                6 * ellStar (B.W N : Real) (B.ell N v) then 1 else 0) +
          256 * Real.exp 3 * (B.W N : Real) ^ (-D)) +
      √(absorbedFarRate E N u J) *
        Step2.xiK (B.L N) (B.W N : Real) (mE E).im)

/-- Exact cancellation of the endpoint tail and the fourth-power drift
normalization.  This is the source of `R_u⁻² R_v⁻²`, including both closed
running endpoints. -/
theorem endpoint_normalization_identity
    {E s0 u v D : Real} (hE : |E| < 2)
    (hsu : s0 <= u) (huv : u <= v) (hv1 : v < 1)
    (N : Nat) (a : LoopArg (B.L N) 2) :
    (APrimeDriftTimeFamily.driftScale d E D N a s0 v)⁻¹ *
        (((1 - u) / (1 - v)) ^ 2 *
          Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))) =
      (etaT E s0 / etaT E u) ^ (-(2 : Real)) *
        (etaT E s0 / etaT E v) ^ (-(2 : Real)) := by
  let T := Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))
  let Ru := etaT E s0 / etaT E u
  let Rv := etaT E s0 / etaT E v
  have hs1 : s0 < 1 := (hsu.trans huv).trans_lt hv1
  have hu1 : u < 1 := huv.trans_lt hv1
  have hT : 0 < T := by
    dsimp [T, Step2.tT]
    exact tailT_pos (by exact_mod_cast B.W_pos N) _
  have hEs : 0 < etaT E s0 := Step2.etaT_pos' hE hs1
  have hEu : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hEv : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hRu : 0 < Ru := by dsimp [Ru]; exact div_pos hEs hEu
  have hRv : 0 < Rv := by dsimp [Rv]; exact div_pos hEs hEv
  have hratio : (1 - u) / (1 - v) = Rv / Ru := by
    rw [← Step2.etaT_ratio hE]
    dsimp [Ru, Rv]
    field_simp [hEs.ne', hEu.ne', hEv.ne']
  change (T * Rv ^ 4)⁻¹ * (((1 - u) / (1 - v)) ^ 2 * T) =
    Ru ^ (-(2 : Real)) * Rv ^ (-(2 : Real))
  rw [hratio, Real.rpow_neg hRu.le, Real.rpow_neg hRv.le]
  field_simp [hT.ne', hRu.ne', hRv.ne']
  norm_num [Real.rpow_natCast]
  ring

/-- Square root of T491's cubic source monomial, with all three positive
factors kept separate. -/
theorem sqrt_cubic_source {N zeta r A : Real}
    (hN : 0 < N) (hr : 0 < r) (hA : 0 < A) :
    √(N ^ zeta * r ^ (3 : Nat) * A⁻¹ ^ (3 : Nat)) =
      N ^ (zeta / 2) * r ^ ((3 : Real) / 2) *
        A ^ (-(3 / 2 : Real)) := by
  have hNpow : (N ^ (zeta / 2)) ^ (2 : Nat) = N ^ zeta := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    ring
  have hrpow : (r ^ ((3 : Real) / 2)) ^ (2 : Nat) = r ^ (3 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le,
      ← Real.rpow_natCast]
    congr 1
    ring
  have hApow : (A ^ (-(3 / 2 : Real))) ^ (2 : Nat) = A⁻¹ ^ (3 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le,
      ← Real.rpow_natCast, ← Real.rpow_neg_one A,
      ← Real.rpow_mul hA.le]
    congr 1
    ring
  apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2
  calc
    N ^ zeta * r ^ (3 : Nat) * A⁻¹ ^ (3 : Nat) =
        (N ^ (zeta / 2)) ^ (2 : Nat) *
          (r ^ ((3 : Real) / 2)) ^ (2 : Nat) *
          (A ^ (-(3 / 2 : Real))) ^ (2 : Nat) := by
      rw [hNpow, hrpow, hApow]
    _ = (N ^ (zeta / 2) * r ^ ((3 : Real) / 2) *
          A ^ (-(3 / 2 : Real))) *
        (N ^ (zeta / 2) * r ^ ((3 : Real) / 2) *
          A ^ (-(3 / 2 : Real))) := by ring

/-- Exact root identity for the literal T491 `sourceC4`. -/
theorem sourceC4_root_identity {E zetaSrc : Real} {s : Nat -> Real}
    {N : Nat} {u : Real}
    (hN : 1 <= N) (hells : 0 < B.ell N (s N))
    (hellu : 0 < B.ell N u) (hA : 0 < B.scale E N u) :
    B.scale E N u *
        (2 * √(APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)) =
      2 * (N : Real) ^ (zetaSrc / 2) *
        (B.ell N u / B.ell N (s N)) ^ ((3 : Real) / 2) *
        (B.scale E N u) ^ (-(1 / 2 : Real)) := by
  have hNr : 0 < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hr : 0 < B.ell N u / B.ell N (s N) := div_pos hellu hells
  rw [APrimeGeneralMovingRawSources.sourceC4,
    sqrt_cubic_source hNr hr hA]
  have hpow : B.scale E N u * (B.scale E N u) ^ (-(3 / 2 : Real)) =
      (B.scale E N u) ^ (-(1 / 2 : Real)) := by
    calc
      _ = (B.scale E N u) ^ (1 : Real) *
          (B.scale E N u) ^ (-(3 / 2 : Real)) := by rw [Real.rpow_one]
      _ = (B.scale E N u) ^ ((1 : Real) + (-(3 / 2 : Real))) := by
        rw [Real.rpow_add hA]
      _ = _ := by congr 1 <;> ring
  calc
    _ = 2 * (N : Real) ^ (zetaSrc / 2) *
        (B.ell N u / B.ell N (s N)) ^ ((3 : Real) / 2) *
        (B.scale E N u * (B.scale E N u) ^ (-(3 / 2 : Real))) := by ring
    _ = _ := by rw [hpow]

/-- Fifth-power identity behind the exact near coefficient. -/
theorem sourceEll_ratio_fifth {s : Nat -> Real} {zetaSrc : Real}
    {N : Nat} {u : Real}
    (hN : 1 <= N) (hells : 0 < B.ell N (s N)) :
    (B.ell N u /
        APrimeGeneralMovingRawSources.sourceEll s zetaSrc N) ^ (5 : Nat) =
      2 * (N : Real) ^ zetaSrc *
        (B.ell N u / B.ell N (s N)) ^ (5 : Nat) := by
  have hNr : 0 < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hq : 0 < 2 * (N : Real) ^ zetaSrc := by positivity
  have hpow : ((2 * (N : Real) ^ zetaSrc) ^ (-(1 / 5 : Real))) ^
      (5 : Nat) = (2 * (N : Real) ^ zetaSrc)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    norm_num [Real.rpow_neg_one]
  unfold APrimeGeneralMovingRawSources.sourceEll
  rw [div_pow, mul_pow, hpow, div_pow]
  field_simp

/-- Literal T491 near source plus the repaired residual. -/
theorem diagNearRate_source_eq {E zetaSrc : Real} {s : Nat -> Real}
    {N : Nat} {u : Real}
    (hN : 1 <= N) (hells : 0 < B.ell N (s N)) :
    APrimeQVEndpoint.diagNearRate B N (B.ell N u)
        (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N) (etaT E u) +
        2 * (B.W N : Real)⁻¹ =
      nearSourceRate E s zetaSrc N u + 2 * (B.W N : Real)⁻¹ := by
  unfold APrimeQVEndpoint.diagNearRate nearSourceRate
  rw [sourceEll_ratio_fifth hN hells]
  ring

/-- The full moving-window `cFar2` is uniformly subpolynomial.  Unlike the
older first-cell lemma, this statement is uniform in every `u in [s_N,t_N]`. -/
theorem eventually_cFar2_le_half {s t : Nat -> Real}
    (hs0 : forall N, 0 <= s N) (ht1 : forall N, t N < 1)
    {tauG : Real} (htauG : 0 < tauG) :
    ∀ᶠ N : Nat in atTop, forall u : TimeIcc s t N,
      Lemma57.cFar2 (B.W N : Real) (B.ell N (u : Real)) <=
        (N : Real) ^ (tauG / 2) := by
  have ha : 0 < tauG / 8 := by positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop ((3 : Real) / 2) ha).eventuallyLE
  have hlogW := (Step2.tendsto_W B).eventually hlog
  have hexpW := (Step2.tendsto_W B).eventually
    (eventually_exp_mul_log_rpow_le 1 ha)
  have hconst := eventually_le_rpow 8 ha
  filter_upwards [hlogW, hexpW, hconst, B.dim, eventually_ge_atTop 1]
    with N hlogN hexpN hconstN hdim hN u
  have hNr : (1 : Real) <= N := by exact_mod_cast hN
  have hN0 : (0 : Real) < N := by linarith
  have hW1 : (1 : Real) <= B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : Real) < B.W N := by linarith
  have hL1 : (1 : Real) <= B.L N := by exact_mod_cast B.one_le_L N
  have hWN : (B.W N : Real) <= N := by
    have hWL : (B.W N : Real) * (B.L N : Real) <= N := by
      exact_mod_cast hdim.1
    nlinarith
  have hell : (1 : Real) <= B.ell N (u : Real) :=
    one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans u.2.1)
      (u.2.2.trans_lt (ht1 N))
  have hlog0 : 0 <= Real.log (B.W N : Real) ^ ((3 : Real) / 2) :=
    Real.rpow_nonneg (Real.log_nonneg hW1) _
  have hWa0 : 0 <= (B.W N : Real) ^ (tauG / 8) := by positivity
  have hNa0 : 0 <= (N : Real) ^ (tauG / 8) := by positivity
  have hlogBd : Real.log (B.W N : Real) ^ ((3 : Real) / 2) <=
      (B.W N : Real) ^ (tauG / 8) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hWa0]
      using hlogN
  have hWaN : (B.W N : Real) ^ (tauG / 8) <=
      (N : Real) ^ (tauG / 8) := Real.rpow_le_rpow hW0.le hWN ha.le
  have hpoly : 4 * Real.log (B.W N : Real) ^ ((3 : Real) / 2) +
      4 / B.ell N (u : Real) <= 8 * (N : Real) ^ (tauG / 8) := by
    have hdiv : 4 / B.ell N (u : Real) <= 4 :=
      (div_le_iff₀ (by linarith : 0 < B.ell N (u : Real))).2 (by nlinarith)
    have hNa1 : 1 <= (N : Real) ^ (tauG / 8) := Real.one_le_rpow hNr ha.le
    nlinarith
  have hexpN' : Real.exp (Real.log (B.W N : Real) ^ ((3 : Real) / 4)) <=
      (N : Real) ^ (tauG / 8) := by simpa only [one_mul] using hexpN.trans hWaN
  have hcf : Lemma57.cFar2 (B.W N : Real) (B.ell N (u : Real)) <=
      8 * (N : Real) ^ (tauG / 8) * (N : Real) ^ (tauG / 8) := by
    unfold Lemma57.cFar2 Lemma57.loss1
    exact mul_le_mul hpoly hexpN' (Real.exp_pos _).le (by positivity)
  have hprod : 8 * (N : Real) ^ (tauG / 8) * (N : Real) ^ (tauG / 8) <=
      (N : Real) ^ (tauG / 8) * (N : Real) ^ (tauG / 8) *
        (N : Real) ^ (tauG / 8) := by gcongr
  calc
    _ <= 8 * (N : Real) ^ (tauG / 8) * (N : Real) ^ (tauG / 8) := hcf
    _ <= _ := hprod
    _ = (N : Real) ^ (3 * (tauG / 8)) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      ring
    _ <= (N : Real) ^ (tauG / 2) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by linarith)

/-- T585's scalar quadratic-source comparison from the closed room
conditions.  The centered loss is deliberately absent. -/
theorem eventually_quadratic_source_comparison
    {E c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    {zetaSrc tauG delta : Real}
    (hzetaSrc : 0 < zetaSrc) (htauG : 0 < tauG) (hdelta : 0 < delta)
    (hzetaTau : zetaSrc <= tauG) (htauDelta : tauG <= delta / 16)
    (hdeltaC : delta <= c / 20) :
    ∀ᶠ N : Nat in atTop, forall u : TimeIcc s t N,
      Lemma57.cFar2 (B.W N : Real) (B.ell N (u : Real)) *
          (N : Real) ^ (zetaSrc / 2) *
          (B.ell N (u : Real) / B.ell N (s N)) ^ ((3 : Real) / 2) <=
        B.scale E N (u : Real) ^ ((1 : Real) / 6) *
          APrimeGeneralMovingQVProfile.generalMovingBlockCap
            E s tauG delta N (u : Real) := by
  have he : 0 <= tauG / 2 + zetaSrc / 2 := by positivity
  have hb : 0 <= (3 / 4 : Real) := by norm_num
  have hec : (tauG / 2 + zetaSrc / 2) / c <= (1 / 320 : Real) := by
    apply (div_le_iff₀ hc).2
    nlinarith
  have hsum : (tauG / 2 + zetaSrc / 2) / c + (3 / 4 : Real) / 30 <=
      (1 / 6 : Real) := by
    calc
      _ <= (1 / 320 : Real) + (3 / 4 : Real) / 30 := by linarith
      _ <= (1 / 6 : Real) := by norm_num
  have hmargin := hreg.margin hE hst ht1 hc he hb hsum
  have hcf := eventually_cFar2_le_half hs0 ht1 htauG
  filter_upwards [hmargin, hcf, eventually_ge_atTop 1] with N hmarginN hcfN hN u
  have hNr : (1 : Real) <= N := by exact_mod_cast hN
  have hN0 : (0 : Real) < N := by linarith
  have hu1 : (u : Real) < 1 := u.2.2.trans_lt (ht1 N)
  have hellu : 0 < B.ell N (u : Real) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans u.2.1) hu1
    simpa only [Band.ell] using (show 0 < ellHat (B.L N) ((u : Real) : Complex) by
      linarith)
  have hells : 0 < B.ell N (s N) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N)
      ((hst N).trans_lt (ht1 N))
    simpa only [Band.ell] using (show 0 < ellHat (B.L N) (s N : Complex) by
      linarith)
  let r : Real := B.ell N (u : Real) / B.ell N (s N)
  let R : Real := Step2Moment.ratR E s N (u : Real)
  have hr0 : 0 <= r := by dsimp [r]; positivity
  have hR1 : 1 <= R := Step2Moment.one_le_ratR hE u.2.1 hu1
  have hR0 : 0 <= R := zero_le_one.trans hR1
  have hratio : r ^ (2 : Nat) <= R := by
    exact Step2MomentStep.ratio_sq_le (B := B) (s := s) hE u.2.1 hu1
  have hrpow : r ^ ((3 : Real) / 2) <= R ^ ((3 : Real) / 4) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hr0 2) hratio
      (by norm_num : (0 : Real) <= (3 : Real) / 4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0] at hh
    convert hh using 1 <;> norm_num
  have hNpow : (N : Real) ^ (tauG / 2) * (N : Real) ^ (zetaSrc / 2) =
      (N : Real) ^ (tauG / 2 + zetaSrc / 2) := (Real.rpow_add hN0 _ _).symm
  have hJ1 : (1 : Real) <=
      APrimeGeneralMovingQVProfile.generalMovingBlockCap
        E s tauG delta N (u : Real) := by
    unfold APrimeGeneralMovingQVProfile.generalMovingBlockCap
    apply le_add_of_nonneg_right
    have houter : 0 <= (N : Real) ^ tauG := by positivity
    have hinner : 0 <= 9 * Real.exp (Real.sqrt 3) *
        ((4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta) *
          Step2Moment.ratR E s N (u : Real) ^ 4) + 2 := by positivity
    positivity
  have hleft : Lemma57.cFar2 (B.W N : Real) (B.ell N (u : Real)) *
        (N : Real) ^ (zetaSrc / 2) * r ^ ((3 : Real) / 2) <=
      (N : Real) ^ (tauG / 2 + zetaSrc / 2) * R ^ ((3 : Real) / 4) := by
    calc
      _ <= (N : Real) ^ (tauG / 2) *
          (N : Real) ^ (zetaSrc / 2) * r ^ ((3 : Real) / 2) := by
        gcongr
        exact hcfN u
      _ = (N : Real) ^ (tauG / 2 + zetaSrc / 2) *
          r ^ ((3 : Real) / 2) := by rw [hNpow]
      _ <= _ := by gcongr
  dsimp [r, R] at hleft
  exact hleft.trans ((hmarginN u).trans
    (le_mul_of_one_le_right (Real.rpow_nonneg (B.scale_nonneg E N hu1.le) _) hJ1))

/-- The scalar quadratic-source row.  The hypothesis is exactly T585's
comparison `cFar2 N^(zeta/2) r^(3/2) <= A^(1/6) J`; no other source loss is
hidden in this lemma. -/
theorem quadratic_source_row_le
    {eta cFar N zeta r A J S : Real}
    (heta : 0 < eta) (hN : 0 < N) (hr : 0 <= r) (hA : 1 <= A)
    (hJ : 1 <= J)
    (hsource : A * (2 * √S) =
      2 * N ^ (zeta / 2) * r ^ ((3 : Real) / 2) * A ^ (-(1 / 2 : Real)))
    (hquad : cFar * N ^ (zeta / 2) * r ^ ((3 : Real) / 2) <=
      A ^ ((1 : Real) / 6) * J) :
    2 * eta⁻¹ *
        (cFar * ((2 * J) ^ 2 * (A * (2 * √S)))) <=
      16 * eta⁻¹ * A ^ (-(1 / 3 : Real)) * J ^ 3 := by
  have hetaInv : 0 < eta⁻¹ := inv_pos.mpr heta
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hJ0 : 0 <= J := le_trans (by norm_num) hJ
  have hpow : A ^ ((1 : Real) / 6) * A ^ (-(1 / 2 : Real)) =
      A ^ (-(1 / 3 : Real)) := by
    rw [← Real.rpow_add hA0]
    congr 1
    ring
  rw [hsource]
  have hmul : cFar * N ^ (zeta / 2) * r ^ ((3 : Real) / 2) *
      A ^ (-(1 / 2 : Real)) * J <= A ^ (-(1 / 3 : Real)) * J ^ 2 := by
    calc
      _ = (cFar * N ^ (zeta / 2) * r ^ ((3 : Real) / 2)) *
          (A ^ (-(1 / 2 : Real)) * J) := by ring
      _ <= (A ^ ((1 : Real) / 6) * J) *
          (A ^ (-(1 / 2 : Real)) * J) :=
        mul_le_mul_of_nonneg_right hquad
          (mul_nonneg (Real.rpow_nonneg hA0.le _) hJ0)
      _ = A ^ (-(1 / 3 : Real)) * J ^ 2 := by
        rw [mul_mul_mul_comm, hpow]
        simp only [pow_two]
  have hmulEta := mul_le_mul_of_nonneg_left hmul hetaInv.le
  nlinarith

/-- The three exact rows of `diagFarRate` sum to `1200=16+1152+32`.
The left side retains the literal source amplitude `S`. -/
theorem diagFarRate_le_absorbed
    {W L ell eta D J S N zeta r A : Real}
    (heta : 0 < eta) (hN : 0 < N) (hr : 0 <= r) (hA : 1 <= A)
    (hJ : 1 <= J) (hW : 1 <= W) (hL : 0 <= L)
    (hsource : A * (2 * √S) =
      2 * N ^ (zeta / 2) * r ^ ((3 : Real) / 2) * A ^ (-(1 / 2 : Real)))
    (hquad : Lemma57.cFar2 W ell * N ^ (zeta / 2) *
      r ^ ((3 : Real) / 2) <= A ^ ((1 : Real) / 6) * J)
    (hleak : W * L * W ^ (-D) <= eta⁻¹ * A⁻¹) :
    2 * eta⁻¹ *
        (Lemma57.cFar2 W ell * ((2 * J) ^ 2 * (A * (2 * √S))) +
          72 * (2 * J) ^ 3 * A⁻¹) +
        4 * W * L * W ^ (-D) * (2 * J) ^ 3 <=
      1200 * eta⁻¹ * A ^ (-(1 / 3 : Real)) * J ^ 3 := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hJ0 : 0 <= J := le_trans (by norm_num) hJ
  have hAinv : A⁻¹ <= A ^ (-(1 / 3 : Real)) := by
    rw [← Real.rpow_neg_one A]
    exact Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hq := quadratic_source_row_le heta hN hr hA hJ hsource hquad
  have hcubic : 2 * eta⁻¹ * (72 * (2 * J) ^ 3 * A⁻¹) <=
      1152 * eta⁻¹ * A ^ (-(1 / 3 : Real)) * J ^ 3 := by
    have := mul_le_mul_of_nonneg_left hAinv
      (mul_nonneg (inv_nonneg.mpr heta.le) (pow_nonneg hJ0 3))
    nlinarith
  have hleakA : W * L * W ^ (-D) <=
      eta⁻¹ * A ^ (-(1 / 3 : Real)) :=
    hleak.trans (mul_le_mul_of_nonneg_left hAinv (inv_nonneg.mpr heta.le))
  have hleak' := mul_le_mul_of_nonneg_right hleakA (pow_nonneg hJ0 3)
  have hspatial : 4 * W * L * W ^ (-D) * (2 * J) ^ 3 <=
      32 * eta⁻¹ * A ^ (-(1 / 3 : Real)) * J ^ 3 := by
    nlinarith [hleak']
  nlinarith

/-- The complete literal T491 far rate, including `sourceC4`, is bounded by
the exact coefficient `1200`. -/
theorem diagFarRate_source_le_absorbed
    {E zetaSrc : Real} {s : Nat -> Real} {N : Nat} {u D J : Real}
    (hN : 1 <= N) (hells : 0 < B.ell N (s N))
    (hellu : 0 < B.ell N u) (heta : 0 < etaT E u)
    (hA : 1 <= B.scale E N u) (hJ : 1 <= J)
    (hquad : Lemma57.cFar2 (B.W N : Real) (B.ell N u) *
        (N : Real) ^ (zetaSrc / 2) *
        (B.ell N u / B.ell N (s N)) ^ ((3 : Real) / 2) <=
      B.scale E N u ^ ((1 : Real) / 6) * J)
    (hleak : (B.W N : Real) * (B.L N : Real) *
        (B.W N : Real) ^ (-D) <=
      (etaT E u)⁻¹ * (B.scale E N u)⁻¹) :
    APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT E u) D J
        (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u) <=
      absorbedFarRate E N u J := by
  have hNr : 0 < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hr : 0 <= B.ell N u / B.ell N (s N) := by positivity
  have hsource := sourceC4_root_identity
    (E := E) (zetaSrc := zetaSrc) (s := s) (N := N) (u := u)
    hN hells hellu (lt_of_lt_of_le zero_lt_one hA)
  have hraw := diagFarRate_le_absorbed
    (W := (B.W N : Real)) (L := (B.L N : Real))
    (ell := B.ell N u) (eta := etaT E u) (D := D) (J := J)
    (S := APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
    (N := (N : Real)) (zeta := zetaSrc)
    (r := B.ell N u / B.ell N (s N)) (A := B.scale E N u)
    heta hNr hr hA hJ (by exact_mod_cast B.W_pos N) (by positivity)
    hsource hquad hleak
  simpa only [APrimeQVEndpoint.diagFarRate, absorbedFarRate, Band.scale] using hraw

/-- Exact endpoint-normalized root-profile corollary.  The right side is a
single sum under one outer square in downstream use; this theorem does not
split or square its summands. -/
theorem normalized_rootProfile_le_absorbed
    {E zetaSrc : Real} {s : Nat -> Real} {N : Nat} {u v D J : Real}
    (hE : |E| < 2) (hsu : s N <= u) (huv : u <= v) (hv1 : v < 1)
    (hN : 1 <= N) (hells : 0 < B.ell N (s N))
    (hfar : APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT E u) D J
        (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u) <=
      absorbedFarRate E N u J)
    (a : LoopArg (B.L N) 2) :
    (APrimeDriftTimeFamily.driftScale d E D N a (s N) v)⁻¹ *
        APrimeFullQV.rootProfile B E N u v D
          (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N) J
          (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
          ((B.W N : Real)⁻¹) a <=
      absorbedRootProfile E s zetaSrc N u v D J a := by
  let T := Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))
  let q := ((1 - u) / (1 - v)) ^ 2 * T
  let xi := Step2.xiK (B.L N) (B.W N : Real) (mE E).im
  let chi : Real := if (zdist (B.L N) (a 0 - a 1) : Real) <=
      6 * ellStar (B.W N : Real) (B.ell N v) then 1 else 0
  let wd := (B.W N : Real) ^ (-D)
  let near := APrimeQVEndpoint.diagNearRate B N (B.ell N u)
      (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N) (etaT E u) +
        2 * (B.W N : Real)⁻¹
  let far := APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT E u) D J
      (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
  let far' := absorbedFarRate E N u J
  let F := Step2Moment.ratR E s N u ^ (-(2 : Real)) *
      Step2Moment.ratR E s N v ^ (-(2 : Real))
  have hnear : near = nearSourceRate E s zetaSrc N u +
      2 * (B.W N : Real)⁻¹ := by
    dsimp [near]
    exact diagNearRate_source_eq hN hells
  have hnorm :
      (APrimeDriftTimeFamily.driftScale d E D N a (s N) v)⁻¹ * q = F := by
    dsimp [q, T, F, Step2Moment.ratR]
    exact endpoint_normalization_identity hE hsu huv hv1 N a
  have hxi : 0 <= xi := by dsimp [xi]; exact Step2.xiK_nonneg _ _ _
  have hs1 : s N < 1 := (hsu.trans huv).trans_lt hv1
  have hu1 : u < 1 := huv.trans_lt hv1
  have hRu : 0 <= Step2Moment.ratR E s N u := by
    unfold Step2Moment.ratR
    exact (div_pos (Step2.etaT_pos' hE hs1) (Step2.etaT_pos' hE hu1)).le
  have hRv : 0 <= Step2Moment.ratR E s N v := by
    unfold Step2Moment.ratR
    exact (div_pos (Step2.etaT_pos' hE hs1) (Step2.etaT_pos' hE hv1)).le
  have hF : 0 <= F := by
    dsimp [F]
    exact mul_nonneg (Real.rpow_nonneg hRu _) (Real.rpow_nonneg hRv _)
  have hsqrt : √far <= √far' := Real.sqrt_le_sqrt hfar
  have hrootFactor : APrimeFullQV.rootProfile B E N u v D
      (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N) J
      (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
      ((B.W N : Real)⁻¹) a =
      q * (√near * (xi * chi + 256 * Real.exp 3 * wd) + √far * xi) := by
    unfold APrimeFullQV.rootProfile
    rw [show (if (zdist (B.L N) (a 0 - a 1) : Real) <=
        6 * ellStar (B.W N : Real) (B.ell N v) then 1 else 0) = chi from rfl]
    dsimp only [q, T, xi, wd, near, far]
    ring
  have habsorbedFactor : absorbedRootProfile E s zetaSrc N u v D J a =
      F * (√(nearSourceRate E s zetaSrc N u + 2 * (B.W N : Real)⁻¹) *
          (xi * chi + 256 * Real.exp 3 * wd) + √far' * xi) := by
    unfold absorbedRootProfile
    rw [show (if (zdist (B.L N) (a 0 - a 1) : Real) <=
        6 * ellStar (B.W N : Real) (B.ell N v) then 1 else 0) = chi from rfl]
  calc
    _ = ((APrimeDriftTimeFamily.driftScale d E D N a (s N) v)⁻¹ * q) *
        (√near * (xi * chi + 256 * Real.exp 3 * wd) + √far * xi) := by
      rw [hrootFactor]
      ring
    _ = F * (√near * (xi * chi + 256 * Real.exp 3 * wd) + √far * xi) := by
      rw [hnorm]
    _ <= F * (√near * (xi * chi + 256 * Real.exp 3 * wd) + √far' * xi) := by
      gcongr
    _ = F * (√(nearSourceRate E s zetaSrc N u + 2 * (B.W N : Real)⁻¹) *
          (xi * chi + 256 * Real.exp 3 * wd) + √far' * xi) := by
      rw [hnear]
    _ = absorbedRootProfile E s zetaSrc N u v D J a := habsorbedFactor.symm

/-- The actual positive-cell T584 consumer with the complete deterministic
absorption.  `k=0` is intentionally absent: it is handled only after time
integration over its degenerate interval. -/
theorem eventually_qv_le_absorbed_on_common_support
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N) (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG delta : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hdelta : 0 < delta)
    (hzetaTau : zetaSrc <= tauG)
    (htauDelta : tauG <= delta / 16)
    (hdeltaC : delta <= c / 20)
    (hcapRoom : tauG + 2 * delta + (2 : Real) / 15 < 1)
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      1 <= k ->
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      ∀ omega ∈ APrimeGeneralMovingCommonSources.commonEvent
          E D s t zetaSrc zetaCtr tauG N,
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
        (APrimeGeneralMovingDetFields.J E D s) s t
        (APrimeGeneralMovingMesh.targetMesh D) delta p N k omega ->
      ∀ u ∈ Set.Icc (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
      forall a : LoopArg (d.L N) 2,
        let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
        let Jbar := APrimeGeneralMovingQVProfile.generalMovingBlockCap
          E s tauG delta N u
        APrimeJG.jG (Gauss.sample d) E N u omega
            (B.ell N u) (etaT E u) D <= Jbar /\
        APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v u omega <=
          (absorbedRootProfile E s zetaSrc N u v D Jbar a) ^ 2 := by
  have hprofile :=
    APrimeGeneralMovingQVProfile.eventually_qv_profile_on_common_support
      hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG hdelta
      hcapRoom p hp
  have hquad := eventually_quadratic_source_comparison
    hE hs0 hst ht1 hc hreg hzetaSrc htauG hdelta
    hzetaTau htauDelta hdeltaC
  have hscale := Step1.eventually_scale_facts hE hst ht1 hreg.1 hreg.2
  have hNW := Step2.eventually_le_W_sq B
  filter_upwards [hprofile, hquad, hscale, d.dim, hNW,
    eventually_ge_atTop 1] with N hprofileN hquadN hscaleN hdimN hNWN hN
  intro k hk hkTop omega homega hwide u hu a
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  let Jbar := APrimeGeneralMovingQVProfile.generalMovingBlockCap
    E s tauG delta N u
  have hv : v ∈ Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have huWindow : u ∈ Set.Icc (s N) (t N) := ⟨hu.1, hu.2.trans hv.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  obtain ⟨hJ, hqv⟩ := hprofileN k hk hkTop omega homega hwide u hu a
  have hNr : (1 : Real) <= N := by exact_mod_cast hN
  have hu0 : 0 <= u := (hs0 N).trans hu.1
  have hu1 : u < 1 := hu.2.trans hv.2 |>.trans_lt (ht1 N)
  have hellu : 0 < B.ell N u := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (u : Complex) by linarith)
  have hells : 0 < B.ell N (s N) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N)
      ((hst N).trans_lt (ht1 N))
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (s N : Complex) by linarith)
  have heta : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hA : 1 <= B.scale E N u :=
    (Real.one_le_rpow hNr hc.le).trans (hscaleN uu).1
  have hAN : B.scale E N u <= (N : Real) :=
    scale_le_N hE hs0 ht1 hdimN.1 uu
  have hWL : (B.W N : Real) * (B.L N : Real) <= (N : Real) := by
    exact_mod_cast hdimN.1
  have heta1 : etaT E u <= 1 := etaT_le_one hE hu0
  have hW1 : (1 : Real) <= B.W N := by exact_mod_cast B.W_pos N
  have hleak : (B.W N : Real) * (B.L N : Real) *
      (B.W N : Real) ^ (-D) <= (etaT E u)⁻¹ * (B.scale E N u)⁻¹ :=
    APrimeFullQV.ExponentRows.leak_paid_by_dims hW1 hNr
      (lt_of_lt_of_le zero_lt_one hA) heta hWL hAN hNWN heta1 (by linarith)
  have hJ1 : (1 : Real) <= Jbar := by
    dsimp [Jbar, APrimeGeneralMovingQVProfile.generalMovingBlockCap]
    apply le_add_of_nonneg_right
    positivity
  have hfar := diagFarRate_source_le_absorbed
    (E := E) (zetaSrc := zetaSrc) (s := s) (N := N) (u := u)
    (D := D) (J := Jbar) hN hells hellu heta hA hJ1
    (hquadN uu) hleak
  have hroot := normalized_rootProfile_le_absorbed
    (E := E) (zetaSrc := zetaSrc) (s := s) (N := N) (u := u)
    (v := v) (D := D) (J := Jbar) hE hu.1 hu.2
    (hv.2.trans_lt (ht1 N)) hN hells hfar a
  have hscaleInv : 0 <=
      (APrimeDriftTimeFamily.driftScale d E D N a (s N) v)⁻¹ :=
    (inv_pos.mpr (APrimeDriftTimeFamily.driftScale_pos d hE hv.1
      (hv.2.trans_lt (ht1 N)) N a)).le
  have hroot0 : 0 <= APrimeFullQV.rootProfile B E N u v D
      (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N) Jbar
      (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
      ((B.W N : Real)⁻¹) a :=
    rootProfile_nonneg E N u v D
      (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N) Jbar
      (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
      ((B.W N : Real)⁻¹) a
  have hsq := pow_le_pow_left₀ (mul_nonneg hscaleInv hroot0) hroot 2
  exact ⟨hJ, hqv.trans hsq⟩

/-- A genuine positive-duration first cell realizes all room assumptions,
the literal common event, and positive widened support simultaneously. -/
theorem positive_cell_absorption_hypotheses_witness :
    exists c : Real, exists s t : Nat -> Real,
      exists delta tauG zetaSrc zetaCtr : Real,
      0 < c /\ 0 < delta /\ 0 < tauG /\
      0 < zetaSrc /\ 0 < zetaCtr /\
      zetaSrc <= tauG /\ tauG <= delta / 16 /\ delta <= c / 20 /\
      tauG + 2 * delta + (2 : Real) / 15 < 1 /\
      (forall N, s N = 0) /\
      (forall N, 0 <= s N) /\
      (forall N, s N <= t N) /\
      (forall N, t N < 1) /\
      Cond272Reg B 0 s t c /\
      BoundsCore (Gauss.sample d) 0 s /\
      ∀ᶠ N : Nat in atTop,
        s N < t N /\
        exists omega,
          omega ∈ APrimeGeneralMovingCommonSources.commonEvent
            0 60 s t zetaSrc zetaCtr tauG N /\
          1 <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N /\
          0 < APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t
              (APrimeGeneralMovingMesh.targetMesh 60)) 1
            (APrimeGeneralMovingDetFields.J 0 60 s) s t
            (APrimeGeneralMovingMesh.targetMesh 60) delta 1 N 1 omega := by
  obtain ⟨_tauPrime, _htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, _hStep, hw⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  let delta : Real := min (c / 40) (1 / 100)
  let tauG : Real := delta / 32
  let zetaSrc : Real := tauG / 2
  let zetaCtr : Real := tauG / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by positivity) (by norm_num)
  have htauG : 0 < tauG := by dsimp [tauG]; positivity
  have hzetaSrc : 0 < zetaSrc := by dsimp [zetaSrc]; positivity
  have hzetaCtr : 0 < zetaCtr := by dsimp [zetaCtr]; positivity
  have hzetaTau : zetaSrc <= tauG := by dsimp [zetaSrc]; linarith
  have htauDelta : tauG <= delta / 16 := by dsimp [tauG]; linarith
  have hdeltaC : delta <= c / 20 := by
    have hdc : delta <= c / 40 := min_le_left _ _
    linarith
  have hdeltaSmall : delta <= 1 / 100 := min_le_right _ _
  have hcapRoom : tauG + 2 * delta + (2 : Real) / 15 < 1 := by
    dsimp [tauG]
    linarith
  refine ⟨c, s, t, delta, tauG, zetaSrc, zetaCtr, hc, hdelta, htauG,
    hzetaSrc, hzetaCtr, hzetaTau, htauDelta, hdeltaC, hcapRoom,
    hsEq, hs0, hst, ht1, hreg, hB, ?_⟩
  have h := hw zetaSrc zetaCtr tauG delta
    hzetaSrc hzetaCtr htauG hdelta
  filter_upwards [h] with N hN
  obtain ⟨hlen, omega, homega, hactive, hwide⟩ := hN
  exact ⟨hlen, omega, homega, hactive, by rw [hwide 1]; norm_num⟩

#print axioms nearSourceRate
#print axioms absorbedFarRate
#print axioms absorbedRootProfile
#print axioms endpoint_normalization_identity
#print axioms sqrt_cubic_source
#print axioms sourceC4_root_identity
#print axioms sourceEll_ratio_fifth
#print axioms diagNearRate_source_eq
#print axioms eventually_cFar2_le_half
#print axioms eventually_quadratic_source_comparison
#print axioms quadratic_source_row_le
#print axioms diagFarRate_le_absorbed
#print axioms diagFarRate_source_le_absorbed
#print axioms normalized_rootProfile_le_absorbed
#print axioms eventually_qv_le_absorbed_on_common_support
#print axioms positive_cell_absorption_hypotheses_witness

end
end RBM.APrimeGeneralMovingQVAbsorption
