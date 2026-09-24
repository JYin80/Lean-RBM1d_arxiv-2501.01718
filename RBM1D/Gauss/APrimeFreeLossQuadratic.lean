/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeDriftIntegralBudget
import RBM1D.Gauss.APrimeFullQV
import RBM1D.Gauss.APrimeGeneralMovingCommonSources

/-!
# T1299: corrected-loss negative-power bound for the literal T615 quadratic row

The integrand is exactly T615's `quadCap` with both transport ratios.  Both
positive terms of its bracket are retained, including the spatial leakage
`W L W^(-D)`.  The `Cond272Reg` scale margin pays the capped `jS` by
`N^(c/10) R_u^27`, leaving a strictly negative power of `N` after integration.
-/

namespace RBM.APrimeFreeLossQuadratic

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The corrected schedule's actual smooth-weight loss. -/
noncomputable def deltaWeight (lambda : Real) : Real := lambda

/-- The corrected schedule's support buffer. -/
noncomputable def xi (lambda : Real) : Real := lambda

/-- The corrected schedule's source, center, gradient, and scalar losses. -/
noncomputable def sourceLoss (lambda : Real) : Real := lambda / 1000

/-- The corrected schedule's cap loss. -/
noncomputable def deltaCap (lambda : Real) : Real := 2 * lambda

/-- The literal quadratic summand in the T615 profile, including both
transport ratios and the complete capped bracket. -/
noncomputable def normalizedQuadratic (E D : Real) (s : Nat → Real)
    (capLoss : Real) (N : Nat) (v u : Real) : Real :=
  Step2.xiK (d.L N) (d.W N) (mE E).im *
    Step2Moment.ratR E s N u ^ (-2 : Real) *
    Step2Moment.ratR E s N v ^ (-2 : Real) *
    APrimeGeneralMovingSmoothDriftNormBudget.quadCap E D s capLoss N u

/-- The exact arithmetic rooms in the corrected schedule. -/
theorem corrected_schedule_room {c lambda : Real} (hc : 0 < c)
    (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    0 < deltaWeight lambda ∧ 0 < xi lambda ∧
    0 < sourceLoss lambda ∧ 0 < deltaCap lambda ∧
    deltaWeight lambda = lambda ∧ xi lambda = lambda ∧
    deltaWeight lambda + xi lambda = deltaCap lambda ∧
    sourceLoss lambda ≤ lambda / 16 ∧
    sourceLoss lambda ≤ deltaCap lambda / 16 ∧
    deltaCap lambda ≤ c / 20 ∧
    sourceLoss lambda + 4 * lambda + (2 : Real) / 15 < 1 := by
  have hlambda1 : lambda ≤ 1 / 10000 := hsmall.trans (min_le_left _ _)
  have hlambdac : lambda ≤ c / 10000 := hsmall.trans (min_le_right _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [deltaWeight] using hlambda
  · simpa [xi] using hlambda
  · dsimp [sourceLoss]
    positivity
  · dsimp [deltaCap]
    positivity
  · rfl
  · rfl
  · dsimp [deltaWeight, xi, deltaCap]
    ring
  · dsimp [sourceLoss]
    nlinarith
  · dsimp [sourceLoss, deltaCap]
    nlinarith
  · dsimp [deltaCap]
    nlinarith [hc, hlambdac]
  · dsimp [sourceLoss]
    nlinarith [hlambda1]

private theorem ratR_eq_ratio {E : Real} {s : Nat → Real} {N : Nat}
    {u : Real} (hE : |E| < 2) :
    Step2Moment.ratR E s N u = APrimeDriftIntegralBudget.ratio (s N) u := by
  unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
  rw [Step2.etaT_ratio hE]

private theorem integral_ratio_neg_twentyone {E a v : Real}
    (hE : |E| < 2) (hav : a ≤ v) (hv1 : v < 1) :
    (∫ u in a..v,
      APrimeDriftIntegralBudget.ratio a u ^ (-(21 : Real)) *
        (etaT E u)⁻¹) =
      (1 - APrimeDriftIntegralBudget.ratio a v ^ (-(21 : Real))) /
        (21 * (mE E).im) := by
  have hm := mE_im_pos hE
  have hfun :
      (fun u => APrimeDriftIntegralBudget.ratio a u ^ (-(21 : Real)) *
        (etaT E u)⁻¹) =
      (fun u => APrimeDriftIntegralBudget.ratio a u ^ (-(21 : Real)) /
        ((mE E).im * (1 - u))) := by
    funext u
    rw [Step2.etaT_eq]
    field_simp
    <;> ring
  rw [hfun, APrimeDriftIntegralBudget.integral_ratio_power
    (hav.trans_lt hv1) hav hv1 hm.ne' (by norm_num : (-(21 : Real)) ≠ 0)]
  ring

private theorem scale_six_inv_le_interpolated {N R A c : Real}
    (hN : 0 < N) (hR : 0 < R) (hA : 0 < A)
    (hmargin : N ^ (c / 10) * R ^ (27 : Real) ≤ A) :
    R ^ (6 : Real) * A⁻¹ ≤
      N ^ (-(c / 10)) * R ^ (-(21 : Real)) := by
  have hprod : 0 < N ^ (c / 10) * R ^ (27 : Real) := by positivity
  have hinv := inv_anti₀ hprod hmargin
  have hinv' : A⁻¹ ≤ N ^ (-(c / 10)) * R ^ (-(27 : Real)) := by
    calc
      A⁻¹ ≤ (N ^ (c / 10) * R ^ (27 : Real))⁻¹ := hinv
      _ = N ^ (-(c / 10)) * R ^ (-(27 : Real)) := by
        rw [mul_inv, ← Real.rpow_neg hN.le, ← Real.rpow_neg hR.le]
  calc
    R ^ (6 : Real) * A⁻¹ ≤
        R ^ (6 : Real) * (N ^ (-(c / 10)) * R ^ (-(27 : Real))) :=
      mul_le_mul_of_nonneg_left hinv' (Real.rpow_nonneg hR.le _)
    _ = N ^ (-(c / 10)) * (R ^ (6 : Real) * R ^ (-(27 : Real))) := by ring
    _ = N ^ (-(c / 10)) * R ^ (-(21 : Real)) := by
      rw [← Real.rpow_add hR]
      congr 1
      norm_num

private theorem quadratic_core_interpolated
    {N R A eta leak c K n : Real}
    (hN : 0 < N) (hR : 0 < R) (hA : 0 < A) (heta : 0 < eta)
    (hleak0 : 0 ≤ leak) (hleak : leak ≤ eta⁻¹ * A⁻¹)
    (hmargin : N ^ (c / 10) * R ^ (27 : Real) ≤ A)
    (hK : 0 ≤ K) (hn : 0 ≤ n) :
    R ^ (-(2 : Real)) *
      (Real.exp 1 * (K * n * R ^ (4 : Nat)) ^ 2 *
        (36 * (eta⁻¹ * A⁻¹) + leak)) ≤
      (37 * Real.exp 1 * K ^ 2 * n ^ 2) *
        (N ^ (-(c / 10)) * (R ^ (-(21 : Real)) * eta⁻¹)) := by
  have hbr : 36 * (eta⁻¹ * A⁻¹) + leak ≤
      37 * (eta⁻¹ * A⁻¹) := by nlinarith
  have hpow : R ^ (-(2 : Real)) * (R ^ (4 : Nat)) ^ 2 =
      R ^ (6 : Real) := by
    rw [← pow_mul, ← Real.rpow_natCast R 8, ← Real.rpow_add hR]
    norm_num
  have hscale := scale_six_inv_le_interpolated hN hR hA hmargin
  calc
    _ = (Real.exp 1 * K ^ 2 * n ^ 2) * R ^ (6 : Real) *
        (36 * (eta⁻¹ * A⁻¹) + leak) := by
      rw [mul_pow, mul_pow]
      calc
        _ = (Real.exp 1 * K ^ 2 * n ^ 2) *
            (R ^ (-(2 : Real)) * (R ^ (4 : Nat)) ^ 2) *
            (36 * (eta⁻¹ * A⁻¹) + leak) := by ring
        _ = _ := by rw [hpow]
    _ ≤ (Real.exp 1 * K ^ 2 * n ^ 2) * R ^ (6 : Real) *
        (37 * (eta⁻¹ * A⁻¹)) := by gcongr
    _ = (37 * Real.exp 1 * K ^ 2 * n ^ 2) *
        ((R ^ (6 : Real) * A⁻¹) * eta⁻¹) := by ring
    _ ≤ (37 * Real.exp 1 * K ^ 2 * n ^ 2) *
        (N ^ (-(c / 10)) * (R ^ (-(21 : Real)) * eta⁻¹)) := by
      have hscaled := mul_le_mul_of_nonneg_right hscale
        (inv_nonneg.mpr heta.le)
      have hscaled' :
          (R ^ (6 : Real) * A⁻¹) * eta⁻¹ ≤
            N ^ (-(c / 10)) * (R ^ (-(21 : Real)) * eta⁻¹) := by
        nlinarith [hscaled]
      exact mul_le_mul_of_nonneg_left hscaled'
        (by positivity : 0 ≤ 37 * Real.exp 1 * K ^ 2 * n ^ 2)

private theorem pointwise_quadratic_le
    {E D c lambda : Real} {s : Nat → Real} {N : Nat} {v u : Real}
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hsu : s N ≤ u)
    (huv : u ≤ v) (hv1 : v < 1) (hD : 60 ≤ D)
    (hdim : B.W N * B.L N ≤ N)
    (hNW : (N : Real) ≤ (B.W N : Real) ^ 2)
    (hmargin : (N : Real) ^ (c / 10) *
        (Step2Moment.ratR E s N u) ^ (27 : Real) ≤ B.scale E N u) :
    normalizedQuadratic E D s (deltaCap lambda) N v u ≤
      (37 * Real.exp 1 * (4 * Real.exp 1 + 2) ^ 2) *
        Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (8 * lambda - c / 10) *
        Step2Moment.ratR E s N v ^ (-(2 : Real)) *
        (APrimeDriftIntegralBudget.ratio (s N) u ^ (-(21 : Real)) *
          (etaT E u)⁻¹) := by
  let R := Step2Moment.ratR E s N u
  let A := B.scale E N u
  let eta := etaT E u
  let leak := (B.W N : Real) * (B.L N : Real) * (B.W N : Real) ^ (-D)
  let K := 4 * Real.exp 1 + 2
  let n := (N : Real) ^ (4 * lambda)
  have hu1 : u < 1 := huv.trans_lt hv1
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hR : 0 < R := Step2Moment.ratR_pos hE hs1 hu1
  have heta : 0 < eta := Step2.etaT_pos' hE hu1
  have hA : 0 < A := B.scale_pos' hE N hu0 hu1
  have hW1 : (1 : Real) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hN1 : (1 : Real) ≤ N := by
    have hL1 : 1 ≤ B.L N := B.one_le_L N
    have hWnat : 1 ≤ B.W N := B.W_pos N
    have hNnat : 1 ≤ N := by nlinarith [hdim]
    exact_mod_cast hNnat
  have hAN : A ≤ (N : Real) := by
    have hellL : B.ell N u ≤ (B.L N : Real) :=
      SumZeroDyn.ellHat_real_le_L hu1
    have heta1 : eta ≤ 1 := etaT_le_one hE hu0
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ N := by
      exact_mod_cast hdim
    change (B.W N : Real) * B.ell N u * eta ≤ (N : Real)
    calc
      _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
      _ = (B.W N : Real) * (B.L N : Real) := by ring
      _ ≤ (N : Real) := hWL
  have hWL : (B.W N : Real) * (B.L N : Real) ≤ N := by
    exact_mod_cast hdim
  have heta1 : eta ≤ 1 := etaT_le_one hE hu0
  have hleak : leak ≤ eta⁻¹ * A⁻¹ := by
    dsimp [leak, A, eta, Band.scale]
    exact APrimeFullQV.ExponentRows.leak_paid_by_dims hW1 hN1 hA heta
      hWL hAN hNW heta1 (by linarith)
  have hleak0 : 0 ≤ leak := by dsimp [leak]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hmargin' : (N : Real) ^ (c / 10) * R ^ (27 : Real) ≤ A := by
    simpa only [R, A] using hmargin
  have hcore := quadratic_core_interpolated
    (by positivity : 0 < (N : Real)) hR hA heta hleak0 hleak hmargin' hK hn
  have hxi : 0 ≤ Step2.xiK (d.L N) (d.W N) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  have hRv : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have houter : 0 ≤ Step2.xiK (d.L N) (d.W N) (mE E).im *
      Step2Moment.ratR E s N v ^ (-(2 : Real)) := by positivity
  have hn2 : n ^ 2 = (N : Real) ^ (8 * lambda) := by
    dsimp [n]
    rw [← Real.rpow_natCast ((N : Real) ^ (4 * lambda)) 2,
      ← Real.rpow_mul (by positivity : (0 : Real) ≤ N)]
    congr 1
    ring
  have hcapn : (N : Real) ^ (2 * (2 * lambda)) = n := by
    dsimp [n]
    congr 1
    ring
  calc
    normalizedQuadratic E D s (deltaCap lambda) N v u =
      (Step2.xiK (d.L N) (d.W N) (mE E).im *
        Step2Moment.ratR E s N v ^ (-(2 : Real))) *
      (R ^ (-(2 : Real)) *
        (Real.exp 1 * (K * n * R ^ (4 : Nat)) ^ 2 *
          (36 * (eta⁻¹ * A⁻¹) + leak))) := by
      dsimp [normalizedQuadratic,
        APrimeGeneralMovingSmoothDriftNormBudget.quadCap,
        APrimeGeneralMovingSmoothDriftNormBudget.jSCap,
        deltaCap, R, A, eta, leak, K, n, Band.scale]
      rw [hcapn]
      ring
    _ ≤ (Step2.xiK (d.L N) (d.W N) (mE E).im *
        Step2Moment.ratR E s N v ^ (-(2 : Real))) *
        ((37 * Real.exp 1 * K ^ 2 * n ^ 2) *
          ((N : Real) ^ (-(c / 10)) *
            (R ^ (-(21 : Real)) * eta⁻¹))) :=
      mul_le_mul_of_nonneg_left hcore houter
    _ = _ := by
      rw [hn2]
      dsimp [R, eta, K]
      simp_rw [ratR_eq_ratio hE]
      have hpowN : (N : Real) ^ (8 * lambda) *
          (N : Real) ^ (-(c / 10)) =
            (N : Real) ^ (8 * lambda - c / 10) := by
        rw [← Real.rpow_add (by positivity : (0 : Real) < (N : Real))]
        congr 1
      calc
        _ = (37 * Real.exp 1 * (4 * Real.exp 1 + 2) ^ 2) *
            Step2.xiK (d.L N) (d.W N) (mE E).im *
            ((N : Real) ^ (8 * lambda) * (N : Real) ^ (-(c / 10))) *
            (APrimeDriftIntegralBudget.ratio (s N) v ^ (-(2 : Real))) *
            (APrimeDriftIntegralBudget.ratio (s N) u ^ (-(21 : Real)) *
              (etaT E u)⁻¹) := by
          dsimp [d]
          ring_nf
        _ = (37 * Real.exp 1 * (4 * Real.exp 1 + 2) ^ 2) *
            Step2.xiK (d.L N) (d.W N) (mE E).im *
            (N : Real) ^ (8 * lambda - c / 10) *
            (APrimeDriftIntegralBudget.ratio (s N) v ^ (-(2 : Real))) *
          (APrimeDriftIntegralBudget.ratio (s N) u ^ (-(21 : Real)) *
              (etaT E u)⁻¹) := by rw [hpowN]

private theorem intervalIntegrable_normalizedQuadratic
    {E D : Real} {s : Nat → Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (capLoss : Real) :
    IntervalIntegrable (fun u => normalizedQuadratic E D s capLoss N v u)
      volume (s N) v := by
  let I := Icc (s N) v
  have hRat : ContinuousOn (fun u => Step2Moment.ratR E s N u) I := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u; exact ratR_eq_ratio hE]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) I :=
      continuousOn_const.sub continuousOn_id
    have hden0 : ∀ u, u ∈ I → 1 - u ≠ 0 := by
      intro u hu
      dsimp [I] at hu
      linarith [hu.2]
    exact continuousOn_const.div hden hden0
  have hRatPos : ∀ u, u ∈ I → 0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE (hsv.trans_lt hv1) (hu.2.trans_lt hv1)
  have hRatInv : ContinuousOn
      (fun u => Step2Moment.ratR E s N u ^ (-(2 : Real))) I :=
    hRat.rpow_const (fun u hu => Or.inl (ne_of_gt (hRatPos u hu)))
  have hEta : ContinuousOn (fun u => etaT E u) I := by
    rw [show (fun u => etaT E u) =
      (fun u => (mE E).im * (1 - u)) by
        funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hEtaPos : ∀ u, u ∈ I → 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hEtaInv : ContinuousOn (fun u => (etaT E u)⁻¹) I :=
    hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
  have hEll : ContinuousOn (fun u => B.ell N u) I :=
    Step2.continuousOn_ell B N hv1
  have hScaleInv : ContinuousOn (fun u =>
      ((d.W N : Real) * B.ell N u * etaT E u)⁻¹) I := by
    apply ContinuousOn.inv₀ ((continuousOn_const.mul hEll).mul hEta)
    intro u hu
    have hW : (0 : Real) < d.W N := by exact_mod_cast B.W_pos N
    exact (mul_pos (mul_pos hW
      (zero_lt_one.trans_le (one_le_ellHat_of_nonneg (B.one_le_L N)
        (hs0.trans hu.1) (hu.2.trans_lt hv1)))) (hEtaPos u hu)).ne'
  have hJSCap : ContinuousOn
      (fun u => APrimeGeneralMovingSmoothDriftNormBudget.jSCap
        E s capLoss N u) I := by
    unfold APrimeGeneralMovingSmoothDriftNormBudget.jSCap
    exact continuousOn_const.mul (hRat.pow 4)
  have hQuad : ContinuousOn
      (fun u => APrimeGeneralMovingSmoothDriftNormBudget.quadCap
        E D s capLoss N u) I := by
    unfold APrimeGeneralMovingSmoothDriftNormBudget.quadCap
    have hfirst : ContinuousOn (fun u =>
        36 * ((etaT E u)⁻¹ *
          (((d.W N : Real) * B.ell N u * etaT E u)⁻¹))) I :=
      continuousOn_const.mul (hEtaInv.mul hScaleInv)
    have hsecond : ContinuousOn (fun _u : Real =>
        (d.W N : Real) * (d.L N : Real) * (d.W N : Real) ^ (-D)) I :=
      continuousOn_const
    exact (continuousOn_const.mul (hJSCap.pow 2)).mul (hfirst.add hsecond)
  have hNorm : ContinuousOn
      (fun u => normalizedQuadratic E D s capLoss N v u) I := by
    unfold normalizedQuadratic
    fun_prop
  exact hNorm.intervalIntegrable_of_Icc hsv

/-- The corrected same-loss schedule bounds the exact T615 quadratic integral
by a negative power of `N`, retaining endpoint `R_v^(-2)` and the leakage
summand.  Structural data are fixed before `lambda`; no moment order is used
in this deterministic row. -/
theorem eventually_t615_quadratic_integral_le
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (_hB : BoundsCore (Gauss.sample d) E s)
    {lambda : Real} (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      (∫ u in (s N)..v,
        normalizedQuadratic E D s (deltaCap lambda) N v u) ≤
        ((N : Real) ^ (-(c / 20)) *
          Step2Moment.ratR E s N v ^ (-(2 : Real))) /
          (21 * (mE E).im) := by
  have hmargin := Cond272Reg.margin hE hst ht1 hc hreg
    (e := c / 10) (b := 27) (a := 1)
    (by positivity) (by norm_num) (by
      have hc0 : c ≠ 0 := ne_of_gt hc
      field_simp [hc0]
      norm_num)
  have hsource : 0 < sourceLoss lambda := by
    dsimp [sourceLoss]
    positivity
  have hxi := Step2FarInputs.eventually_xiK_le B (mE E).im hsource
  let C : Real := 37 * Real.exp 1 * (4 * Real.exp 1 + 2) ^ 2
  have hC0 : 0 < C := by dsimp [C]; positivity
  have hgap : 0 < -(c / 20) -
      (sourceLoss lambda + (8 * lambda - c / 10)) := by
    have hlambdac : lambda ≤ c / 10000 := hsmall.trans (min_le_right _ _)
    dsimp [sourceLoss]
    nlinarith [hc, hlambdac]
  have hconst := eventually_le_rpow C hgap
  have hNW := Step2.eventually_le_W_sq B
  filter_upwards [hmargin, hxi, hconst, hNW, d.dim,
    eventually_ge_atTop 1] with N hmarginN hxiN hconstN hNWN hdimN hN
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hs1 : s N < 1 := hv.1.trans_lt hv1
  have hRv : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have hRvInv : 0 ≤ Step2Moment.ratR E s N v ^ (-(2 : Real)) := by positivity
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have hNWreal : (N : Real) ≤ (B.W N : Real) ^ 2 := hNWN
  have hcoef : C * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real) ^ (8 * lambda - c / 10) ≤ (N : Real) ^ (-(c / 20)) := by
    have hxiN' : Step2.xiK (d.L N) (d.W N) (mE E).im ≤
        (N : Real) ^ sourceLoss lambda := by
      simpa only [B, d, band] using hxiN
    have hexp : (N : Real) ^ (-(c / 20) -
        (sourceLoss lambda + (8 * lambda - c / 10))) *
        ((N : Real) ^ sourceLoss lambda *
          (N : Real) ^ (8 * lambda - c / 10)) =
        (N : Real) ^ (-(c / 20)) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      dsimp [sourceLoss]
      ring
    calc
      _ ≤ C * (N : Real) ^ sourceLoss lambda *
          (N : Real) ^ (8 * lambda - c / 10) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxiN' hC0.le)
          (Real.rpow_nonneg hNpos.le _)
      _ ≤ (N : Real) ^ (-(c / 20) -
            (sourceLoss lambda + (8 * lambda - c / 10))) *
          ((N : Real) ^ sourceLoss lambda *
            (N : Real) ^ (8 * lambda - c / 10)) := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_right hconstN
            (mul_nonneg
              (Real.rpow_nonneg hNpos.le (sourceLoss lambda))
              (Real.rpow_nonneg hNpos.le (8 * lambda - c / 10))))
      _ = (N : Real) ^ (-(c / 20)) := hexp
  let Ccell : Real :=
    (N : Real) ^ (-(c / 20)) *
      Step2Moment.ratR E s N v ^ (-(2 : Real))
  have hCcell : 0 ≤ Ccell := by dsimp [Ccell]; positivity
  have hsrcInt : IntervalIntegrable
      (fun u => normalizedQuadratic E D s (deltaCap lambda) N v u)
      volume (s N) v :=
    intervalIntegrable_normalizedQuadratic hE (hs0 N) hv.1 hv1
      (deltaCap lambda)
  have hkernelInt : IntervalIntegrable
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u ^
          (-(21 : Real)) * (etaT E u)⁻¹)
      volume (s N) v := by
    have hh := APrimeDriftIntegralBudget.intervalIntegrable_powerRate
      (s := s N) (v := v) (q := (-(21 : Real))) hv.1 hv1 hm.ne'
    have heq :
        (fun u => APrimeDriftIntegralBudget.powerRate (mE E).im
          (s N) (-(21 : Real)) u) =
        (fun u => APrimeDriftIntegralBudget.ratio (s N) u ^
          (-(21 : Real)) * (etaT E u)⁻¹) := by
      funext u
      rw [APrimeDriftIntegralBudget.powerRate, Step2.etaT_eq]
      field_simp
      <;> ring
    rw [← heq]
    exact hh
  have hpoint : ∀ u ∈ Icc (s N) v,
      normalizedQuadratic E D s (deltaCap lambda) N v u ≤
        Ccell * (APrimeDriftIntegralBudget.ratio (s N) u ^
          (-(21 : Real)) * (etaT E u)⁻¹) := by
    intro u hu
    let uu : TimeIcc s t N := ⟨u, ⟨hu.1, hu.2.trans hv.2⟩⟩
    have hmu : (N : Real) ^ (c / 10) *
        (Step2Moment.ratR E s N u) ^ (27 : Real) ≤ B.scale E N u := by
      have hh := hmarginN uu
      simpa only [Step2Moment.ratR, Real.rpow_one] using hh
    have hh := pointwise_quadratic_le hE ((hs0 N).trans hu.1)
      hu.1 hu.2 hv1 hD hdimN.1 hNWreal hmu (lambda := lambda)
    apply le_trans hh
    have hu1 : u < 1 := hu.2.trans_lt hv1
    have hRu : 0 < Step2Moment.ratR E s N u :=
      Step2Moment.ratR_pos hE hs1 hu1
    have hetaU : 0 < etaT E u := Step2.etaT_pos' hE hu1
    have hkernel : 0 ≤
        APrimeDriftIntegralBudget.ratio (s N) u ^ (-(21 : Real)) *
          (etaT E u)⁻¹ := by
      rw [← ratR_eq_ratio (u := u) hE]
      exact mul_nonneg (Real.rpow_nonneg hRu.le _)
        (inv_nonneg.mpr hetaU.le)
    have hcoefRv := mul_le_mul_of_nonneg_right hcoef hRvInv
    have heq : Ccell = (N : Real) ^ (-(c / 20)) *
        Step2Moment.ratR E s N v ^ (-(2 : Real)) := rfl
    simpa [Ccell, heq, C, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_right hcoefRv hkernel)
  have hmono := intervalIntegral.integral_mono_on hv.1 hsrcInt
    (hkernelInt.const_mul Ccell) hpoint
  have hInt :
      (∫ u in (s N)..v,
        normalizedQuadratic E D s (deltaCap lambda) N v u) ≤
      Ccell * ((1 - APrimeDriftIntegralBudget.ratio (s N) v ^
        (-(21 : Real))) / (21 * (mE E).im)) := by
    calc
      _ ≤ ∫ u in (s N)..v,
          Ccell * (APrimeDriftIntegralBudget.ratio (s N) u ^
            (-(21 : Real)) * (etaT E u)⁻¹) := hmono
      _ = Ccell * (∫ u in (s N)..v,
          APrimeDriftIntegralBudget.ratio (s N) u ^
            (-(21 : Real)) * (etaT E u)⁻¹) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_ratio_neg_twentyone hE hv.1 hv1]
  have hkernelBound :
      (1 - APrimeDriftIntegralBudget.ratio (s N) v ^ (-(21 : Real))) /
          (21 * (mE E).im) ≤ 1 / (21 * (mE E).im) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hR0 : 0 ≤
        APrimeDriftIntegralBudget.ratio (s N) v ^ (-(21 : Real)) := by
      rw [← ratR_eq_ratio (u := v) hE]
      positivity
    nlinarith
  calc
    _ ≤ Ccell * ((1 - APrimeDriftIntegralBudget.ratio (s N) v ^
          (-(21 : Real))) / (21 * (mE E).im)) := hInt
    _ ≤ Ccell * (1 / (21 * (mE E).im)) :=
      mul_le_mul_of_nonneg_left hkernelBound hCcell
    _ = ((N : Real) ^ (-(c / 20)) *
          Step2Moment.ratR E s N v ^ (-(2 : Real))) /
          (21 * (mE E).im) := by
      dsimp [Ccell]
      ring

/-- The corrected losses coexist with the literal common event on a positive
first cell, and the same sample has positive actual smooth weight. -/
theorem corrected_schedule_same_event_witness :
    ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      ∃ lambda : Real, 0 < lambda ∧
        lambda ≤ min (1 / 10000 : Real) (c / 10000) ∧
        ∀ᶠ N : Nat in atTop,
          s N < t N ∧
          ∃ omega,
            omega ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t (sourceLoss lambda) (sourceLoss lambda)
                (sourceLoss lambda) N ∧
            1 ≤ cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh 60) N ∧
            0 < APrimeGeneralMovingSmoothDriftNormBudget.weight
              0 60 s t (deltaWeight lambda) 1 N 1 omega := by
  obtain ⟨_tauPrime, _htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, hStep, hresident⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  let lambda : Real := min (1 / 10000 : Real) (c / 10000) / 2
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000) := by
    dsimp [lambda]
    have hmin : 0 ≤ min (1 / 10000 : Real) (c / 10000) := by positivity
    linarith
  have hpositive := hresident (sourceLoss lambda) (sourceLoss lambda)
    (sourceLoss lambda) (deltaWeight lambda)
    (by dsimp [sourceLoss]; positivity)
    (by dsimp [sourceLoss]; positivity)
    (by dsimp [sourceLoss]; positivity)
    (by dsimp [deltaWeight]; exact hlambda)
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
    lambda, hlambda, hsmall, ?_⟩
  filter_upwards [hpositive] with N hN
  obtain ⟨hlen, omega, homega, hactive, hwide⟩ := hN
  have hwideOne :
      APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh 60)) 1
        (APrimeGeneralMovingDetFields.J 0 60 s) s t
        (APrimeGeneralMovingMesh.targetMesh 60)
        (deltaWeight lambda) 1 N 1 omega = 1 := by
    simpa only [APrimeGeneralMovingDetFields.J] using hwide 1
  have hactual := APrimeSmoothWeightActual.widenedW_le_weight_canonical d
    (E := 0) (D := 60) (δ := deltaWeight lambda)
    (s := s) (t := t) (mesh := APrimeGeneralMovingMesh.targetMesh 60)
    (by norm_num) hlambda.le N 1 1 omega (hst N) (ht1 N)
    (APrimeGeneralMovingMesh.targetMesh_pos 60 N)
  have hweightPos : 0 <
      APrimeGeneralMovingSmoothDriftNormBudget.weight
        0 60 s t (deltaWeight lambda) 1 N 1 omega := by
    have hwpos : 0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh 60)) 1
        (APrimeGeneralMovingDetFields.J 0 60 s) s t
        (APrimeGeneralMovingMesh.targetMesh 60)
        (deltaWeight lambda) 1 N 1 omega := by
      rw [hwideOne]
      norm_num
    have hwle := hwpos.trans_le hactual
    simpa [APrimeGeneralMovingSmoothDriftNormBudget.weight] using hwle
  exact ⟨hlen, omega, homega, hactive, hweightPos⟩

#print axioms corrected_schedule_room
#print axioms eventually_t615_quadratic_integral_le
#print axioms corrected_schedule_same_event_witness

end
end RBM.APrimeFreeLossQuadratic
