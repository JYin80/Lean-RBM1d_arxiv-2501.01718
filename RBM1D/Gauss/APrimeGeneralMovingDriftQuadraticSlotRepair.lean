/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeDriftIntegralBudget
import RBM1D.Gauss.APrimeInit
import RBM1D.Gauss.APrimeFullQV

/-! # T1023: literal T615 quadratic drift row, integrated on every active cell -/

namespace RBM.APrimeGeneralMovingDriftQuadraticSlotRepair

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The exact T615 quadratic cap with both positive terms and the two transport ratios. -/
noncomputable def normalizedQuadratic (E D : Real) (s : Nat → Real)
    (deltaCap : Real) (N : Nat) (v u : Real) : Real :=
  Step2.xiK (d.L N) (d.W N) (mE E).im *
    Step2Moment.ratR E s N u ^ (-2 : Real) *
    Step2Moment.ratR E s N v ^ (-2 : Real) *
    APrimeGeneralMovingSmoothDriftNormBudget.quadCap E D s deltaCap N u

private theorem ratR_eq_ratio {E : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hE : |E| < 2) :
    Step2Moment.ratR E s N u = APrimeDriftIntegralBudget.ratio (s N) u := by
  unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
  rw [Step2.etaT_ratio hE]

private theorem integral_ratio_neg_twentyfour {E a v : Real}
    (hE : |E| < 2) (hav : a ≤ v) (hv1 : v < 1) :
    (∫ u in a..v, APrimeDriftIntegralBudget.ratio a u ^ (-(24 : Real)) *
      (etaT E u)⁻¹) =
      (1 - APrimeDriftIntegralBudget.ratio a v ^ (-(24 : Real))) /
        (24 * (mE E).im) := by
  have hm := mE_im_pos hE
  have hfun : (fun u => APrimeDriftIntegralBudget.ratio a u ^ (-(24 : Real)) *
      (etaT E u)⁻¹) =
      (fun u => APrimeDriftIntegralBudget.ratio a u ^ (-(24 : Real)) /
        ((mE E).im * (1 - u))) := by
    funext u
    rw [Step2.etaT_eq]
    field_simp
    <;> ring
  rw [hfun, APrimeDriftIntegralBudget.integral_ratio_power
    (hav.trans_lt hv1) hav hv1 hm.ne' (by norm_num : (-(24 : Real)) ≠ 0)]
  ring

/-- The exact room after the `xiK` allowance and the square of `jSCap`. -/
theorem quadratic_exponent_gap (δ : Real) :
    5 * δ / 32 -
      (δ / 100 + 4 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) =
        53 * δ / 800 := by
  dsimp [APrimeGeneralMovingSlotLossSchedule.deltaCap]
  ring

private theorem exponent_gap {δ : Real} (hδ : 0 < δ) :
    0 < 5 * δ / 32 -
      (δ / 100 + 4 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) := by
  rw [quadratic_exponent_gap]
  positivity

private theorem ratio_six_inv_scale {R A : Real} (hR : 0 < R)
    (hR30 : R ^ (30 : Nat) ≤ A) :
    R ^ (6 : Real) * A⁻¹ ≤ R ^ (-(24 : Real)) := by
  have hInv : A⁻¹ ≤ (R ^ (30 : Nat))⁻¹ :=
    inv_anti₀ (pow_pos hR _) hR30
  calc
    R ^ (6 : Real) * A⁻¹ ≤ R ^ (6 : Real) * (R ^ (30 : Nat))⁻¹ :=
      mul_le_mul_of_nonneg_left hInv (Real.rpow_nonneg hR.le _)
    _ = R ^ (-(24 : Real)) := by
      rw [← Real.rpow_natCast R 30, ← Real.rpow_neg hR.le,
        ← Real.rpow_add hR]
      norm_num

private theorem quadratic_core {R A eta leak K n : Real}
    (hR : 0 < R) (hA : 0 < A) (heta : 0 < eta)
    (hleak0 : 0 ≤ leak) (hleak : leak ≤ eta⁻¹ * A⁻¹)
    (hR30 : R ^ (30 : Nat) ≤ A) (hK : 0 ≤ K) (hn : 0 ≤ n) :
    R ^ (-(2 : Real)) *
      (Real.exp 1 * (K * n * R ^ (4 : Nat)) ^ 2 *
        (36 * (eta⁻¹ * A⁻¹) + leak)) ≤
      (37 * Real.exp 1 * K ^ 2 * n ^ 2) *
        (R ^ (-(24 : Real)) * eta⁻¹) := by
  have hbr : 36 * (eta⁻¹ * A⁻¹) + leak ≤ 37 * (eta⁻¹ * A⁻¹) := by
    linarith
  have hpow : R ^ (-(2 : Real)) * (R ^ (4 : Nat)) ^ 2 =
      R ^ (6 : Real) := by
    rw [← pow_mul, ← Real.rpow_natCast R 8, ← Real.rpow_add hR]
    norm_num
  have hscale := ratio_six_inv_scale hR hR30
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
        (R ^ (-(24 : Real)) * eta⁻¹) := by gcongr

private theorem pointwise_le
    {E D : Real} {s : Nat → Real} {N : Nat} {v u δ : Real}
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hsu : s N ≤ u)
    (huv : u ≤ v) (hv1 : v < 1) (hD : 60 ≤ D)
    (hdim : B.W N * B.L N ≤ N)
    (hNW : (N : Real) ≤ (B.W N : Real) ^ 2)
    (hR30 : (Step2Moment.ratR E s N u) ^ (30 : Nat) ≤ B.scale E N u) :
    normalizedQuadratic E D s δ N v u ≤
      (37 * Real.exp 1 * (4 * Real.exp 1 + 2) ^ 2) *
        Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (4 * δ) *
        Step2Moment.ratR E s N v ^ (-(2 : Real)) *
        (APrimeDriftIntegralBudget.ratio (s N) u ^ (-(24 : Real)) *
          (etaT E u)⁻¹) := by
  let R := Step2Moment.ratR E s N u
  let A := B.scale E N u
  let η := etaT E u
  let F := (B.W N : Real) * (B.L N : Real) * (B.W N : Real) ^ (-D)
  let K := 4 * Real.exp 1 + 2
  let n := (N : Real) ^ (2 * δ)
  have hu1 : u < 1 := huv.trans_lt hv1
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hR : 0 < R := Step2Moment.ratR_pos hE hs1 hu1
  have hη : 0 < η := Step2.etaT_pos' hE hu1
  have hA : 0 < A := B.scale_pos' hE N hu0 hu1
  have hW1 : (1 : Real) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hN1 : (1 : Real) ≤ N := by
    have hL1 : 1 ≤ B.L N := B.one_le_L N
    have hWnat : 1 ≤ B.W N := B.W_pos N
    have hNnat : 1 ≤ N := by nlinarith [hdim]
    exact_mod_cast hNnat
  have hAN : A ≤ (N : Real) := by
    have hellL : B.ell N u ≤ (B.L N : Real) := SumZeroDyn.ellHat_real_le_L hu1
    have hη1 : η ≤ 1 := etaT_le_one hE hu0
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ N := by exact_mod_cast hdim
    change (B.W N : Real) * B.ell N u * η ≤ (N : Real)
    calc
      _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
      _ = (B.W N : Real) * (B.L N : Real) := by ring
      _ ≤ (N : Real) := hWL
  have hWL : (B.W N : Real) * (B.L N : Real) ≤ N := by exact_mod_cast hdim
  have hη1 : η ≤ 1 := etaT_le_one hE hu0
  have hF : F ≤ η⁻¹ * A⁻¹ :=
    APrimeFullQV.ExponentRows.leak_paid_by_dims hW1 hN1 hA hη
      hWL hAN hNW hη1 (by linarith)
  have hF0 : 0 ≤ F := by
    dsimp [F]
    positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hcore := quadratic_core hR hA hη hF0 hF hR30 hK hn
  have hxi : 0 ≤ Step2.xiK (d.L N) (d.W N) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  have hRv : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have houter : 0 ≤ Step2.xiK (d.L N) (d.W N) (mE E).im *
      Step2Moment.ratR E s N v ^ (-(2 : Real)) := by positivity
  have hn2 : n ^ 2 = (N : Real) ^ (4 * δ) := by
    dsimp [n]
    rw [← Real.rpow_natCast ((N : Real) ^ (2 * δ)) 2,
      ← Real.rpow_mul (by linarith : (0 : Real) ≤ N)]
    congr 1 <;> ring
  calc
    normalizedQuadratic E D s δ N v u =
      (Step2.xiK (d.L N) (d.W N) (mE E).im *
        Step2Moment.ratR E s N v ^ (-(2 : Real))) *
      (R ^ (-(2 : Real)) *
        (Real.exp 1 * (K * n * R ^ (4 : Nat)) ^ 2 *
          (36 * (η⁻¹ * A⁻¹) + F))) := by
      dsimp [normalizedQuadratic, APrimeGeneralMovingSmoothDriftNormBudget.quadCap,
        APrimeGeneralMovingSmoothDriftNormBudget.jSCap, R, A, η, F, K, n,
        Band.scale]
      ring
    _ ≤ (Step2.xiK (d.L N) (d.W N) (mE E).im *
        Step2Moment.ratR E s N v ^ (-(2 : Real))) *
      ((37 * Real.exp 1 * K ^ 2 * n ^ 2) *
        (R ^ (-(24 : Real)) * η⁻¹)) :=
          mul_le_mul_of_nonneg_left hcore houter
    _ = _ := by
      rw [hn2]
      dsimp [R, η, K]
      rw [ratR_eq_ratio (u := u) hE]
      ring

/-- The exact normalized row is integrable even on a degenerate cell. -/
theorem intervalIntegrable_normalizedQuadratic
    {E D : Real} {s : Nat → Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (δ : Real) :
    IntervalIntegrable (fun u => normalizedQuadratic E D s δ N v u)
      volume (s N) v := by
  let I := Icc (s N) v
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hRat : ContinuousOn (fun u => Step2Moment.ratR E s N u) I := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u; exact ratR_eq_ratio hE]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) I :=
      continuousOn_const.sub continuousOn_id
    have hden0 : ∀ u, u ∈ I → 1 - u ≠ 0 := by
      intro u hu; dsimp [I] at hu; linarith [hu.2]
    exact continuousOn_const.div hden hden0
  have hRatPos : ∀ u, u ∈ I → 0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)
  have hRatInv : ContinuousOn
      (fun u => Step2Moment.ratR E s N u ^ (-(2 : Real))) I :=
    hRat.rpow_const (fun u hu => Or.inl (ne_of_gt (hRatPos u hu)))
  have hRat4 : ContinuousOn
      (fun u => Step2Moment.ratR E s N u ^ (4 : Nat)) I := hRat.pow 4
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
  have hEllPos : ∀ u, u ∈ I → 0 < B.ell N u := by
    intro u hu
    exact zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0.trans hu.1)
        (hu.2.trans_lt hv1))
  have hA : ContinuousOn
      (fun u => (d.W N : Real) * B.ell N u * etaT E u) I :=
    (continuousOn_const.mul hEll).mul hEta
  have hAInv : ContinuousOn
      (fun u => ((d.W N : Real) * B.ell N u * etaT E u)⁻¹) I :=
    hA.inv₀ (fun u hu =>
      mul_ne_zero (mul_ne_zero (by exact_mod_cast (B.W_pos N).ne')
        (hEllPos u hu).ne') (hEtaPos u hu).ne')
  have hCap : ContinuousOn
      (fun u => APrimeGeneralMovingSmoothDriftNormBudget.jSCap E s δ N u) I := by
    unfold APrimeGeneralMovingSmoothDriftNormBudget.jSCap
    fun_prop
  have hQuad : ContinuousOn
      (fun u => APrimeGeneralMovingSmoothDriftNormBudget.quadCap E D s δ N u) I := by
    unfold APrimeGeneralMovingSmoothDriftNormBudget.quadCap
    fun_prop
  have hNorm : ContinuousOn
      (fun u => normalizedQuadratic E D s δ N v u) I := by
    unfold normalizedQuadratic
    fun_prop
  exact hNorm.intervalIntegrable_of_Icc hsv

/-- The active index zero has exactly zero running quadratic contribution. -/
theorem zero_cell_integral_eq_zero
    (E D δ : Real) (s : Nat → Real) (N : Nat) :
    (∫ u in (s N)..(cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0),
      normalizedQuadratic E D s δ N
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) u) = 0 := by
  simp only [cutNetPt_zero, intervalIntegral.integral_same]

private theorem eventually_coefficient_le {E δ : Real} (hδ : 0 < δ) :
    ∀ᶠ N : Nat in atTop,
      (37 * Real.exp 1 * (4 * Real.exp 1 + 2) ^ 2) *
        Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (4 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) ≤
      (N : Real) ^ (5 * δ / 32) := by
  let C : Real := 37 * Real.exp 1 * (4 * Real.exp 1 + 2) ^ 2
  let α : Real := δ / 100 + 4 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ
  have hgap : 0 < 5 * δ / 32 - α := exponent_gap hδ
  have hxi := Step2FarInputs.eventually_xiK_le B (mE E).im
    (by positivity : 0 < δ / 100)
  have hconst := eventually_le_rpow C hgap
  filter_upwards [hxi, hconst, eventually_ge_atTop 1] with N hxiN hCN hN
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : Real) < N := by linarith
  have hxiN : Step2.xiK (d.L N) (d.W N) (mE E).im ≤
      (N : Real) ^ (δ / 100) := by
    simpa only [B, d, band] using hxiN
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hpow : (N : Real) ^ (δ / 100) *
      (N : Real) ^ (4 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) =
      (N : Real) ^ α := by
    dsimp [α]
    rw [← Real.rpow_add hN0]
  have hpow2 : (N : Real) ^ (5 * δ / 32 - α) * (N : Real) ^ α =
      (N : Real) ^ (5 * δ / 32) := by
    rw [← Real.rpow_add hN0]
    congr 1 <;> ring
  calc
    _ ≤ C * (N : Real) ^ (δ / 100) *
        (N : Real) ^ (4 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) := by
      have hh := mul_le_mul_of_nonneg_right hxiN
        (Real.rpow_nonneg hN0.le (4 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ))
      simpa only [C, d, B, band, mul_assoc] using
        (mul_le_mul_of_nonneg_left hh hC0)
    _ = C * (N : Real) ^ α := by
      calc
        _ = C * ((N : Real) ^ (δ / 100) *
            (N : Real) ^ (4 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ)) := by ring
        _ = _ := by rw [hpow]
    _ ≤ (N : Real) ^ (5 * δ / 32 - α) * (N : Real) ^ α := by
      exact mul_le_mul_of_nonneg_right hCN (by positivity)
    _ = _ := hpow2

/-- The full literal T615 quadratic cap, with its actual Step2 cap and both
positive summands, fits the A-prime small slot uniformly over active cells. -/
theorem eventually_quadratic_integral_le_small_slot
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (_hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ) (_hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      (∫ u in (s N)..v,
        normalizedQuadratic E D s
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) ≤
        (1 / (mE E).im) * (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
  have hcoef := eventually_coefficient_le (E := E) hδ
  have hthirty := Cond272.pow_thirty_le hE hst ht1 hreg.1
  have hNW := Step2.eventually_le_W_sq B
  filter_upwards [hcoef, hthirty, hNW, d.dim, eventually_ge_atTop 1]
    with N hcoefN hthirtyN hNWN hdimN hN
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hs1 : s N < 1 := hv.1.trans_lt hv1
  have hRv1 : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hv.1 hv1
  have hRv : 0 < Step2Moment.ratR E s N v := by linarith
  have hRvInv : 0 ≤ Step2Moment.ratR E s N v ^ (-(2 : Real)) := by positivity
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNWreal : (N : Real) ≤ (B.W N : Real) ^ 2 := hNWN
  let C : Real :=
    (37 * Real.exp 1 * (4 * Real.exp 1 + 2) ^ 2) *
      Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real) ^ (4 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ) *
      Step2Moment.ratR E s N v ^ (-(2 : Real))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
    positivity
  have hsrcInt : IntervalIntegrable
      (fun u => normalizedQuadratic E D s
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u)
      volume (s N) v :=
    intervalIntegrable_normalizedQuadratic hE (hs0 N) hv.1 hv1 _
  have hkernelInt : IntervalIntegrable
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u ^ (-(24 : Real)) *
        (etaT E u)⁻¹) volume (s N) v := by
    have hh := APrimeDriftIntegralBudget.intervalIntegrable_powerRate
      (s := s N) (v := v) (q := (-(24 : Real))) hv.1 hv1 hm.ne'
    have heq : (fun u => APrimeDriftIntegralBudget.powerRate (mE E).im (s N)
        (-(24 : Real)) u) =
        (fun u => APrimeDriftIntegralBudget.ratio (s N) u ^ (-(24 : Real)) *
          (etaT E u)⁻¹) := by
      funext u
      rw [APrimeDriftIntegralBudget.powerRate, Step2.etaT_eq]
      field_simp
      <;> ring
    rw [← heq]
    exact hh
  have hpoint : ∀ u ∈ Icc (s N) v,
      normalizedQuadratic E D s
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u ≤
      C * (APrimeDriftIntegralBudget.ratio (s N) u ^ (-(24 : Real)) *
        (etaT E u)⁻¹) := by
    intro u hu
    let uu : TimeIcc s t N := ⟨u, ⟨hu.1, hu.2.trans hv.2⟩⟩
    have hR30 : (Step2Moment.ratR E s N u) ^ (30 : Nat) ≤
        B.scale E N u := by
      have hh := hthirtyN uu
      simpa only [Step2Moment.ratR] using hh
    have hh := pointwise_le hE ((hs0 N).trans hu.1) hu.1 hu.2 hv1 hD
      hdimN.1 hNWreal hR30
      (δ := APrimeGeneralMovingSlotLossSchedule.deltaCap δ)
    simpa only [C, mul_assoc, mul_left_comm, mul_comm] using hh
  have hmono := intervalIntegral.integral_mono_on hv.1 hsrcInt
    (hkernelInt.const_mul C) hpoint
  have hInt : (∫ u in (s N)..v,
        normalizedQuadratic E D s
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) ≤
      C * ((1 - APrimeDriftIntegralBudget.ratio (s N) v ^ (-(24 : Real))) /
        (24 * (mE E).im)) := by
    calc
      _ ≤ ∫ u in (s N)..v,
          C * (APrimeDriftIntegralBudget.ratio (s N) u ^ (-(24 : Real)) *
            (etaT E u)⁻¹) := hmono
      _ = C * (∫ u in (s N)..v,
          APrimeDriftIntegralBudget.ratio (s N) u ^ (-(24 : Real)) *
            (etaT E u)⁻¹) := by rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_ratio_neg_twentyfour hE hv.1 hv1]
  have hkernelBound :
      (1 - APrimeDriftIntegralBudget.ratio (s N) v ^ (-(24 : Real))) /
        (24 * (mE E).im) ≤ 1 / (24 * (mE E).im) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hR0 : 0 ≤ APrimeDriftIntegralBudget.ratio (s N) v ^ (-(24 : Real)) := by
      rw [← ratR_eq_ratio (u := v) hE]
      positivity
    nlinarith
  have hcoefC : C ≤ (N : Real) ^ (5 * δ / 32) *
      Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
    dsimp [C]
    exact mul_le_mul_of_nonneg_right hcoefN hRvInv
  calc
    _ ≤ C * ((1 - APrimeDriftIntegralBudget.ratio (s N) v ^ (-(24 : Real))) /
        (24 * (mE E).im)) := hInt
    _ ≤ C * (1 / (24 * (mE E).im)) :=
      mul_le_mul_of_nonneg_left hkernelBound hC0
    _ ≤ ((N : Real) ^ (5 * δ / 32) *
        Step2Moment.ratR E s N v ^ (-(2 : Real))) *
        (1 / (24 * (mE E).im)) := by gcongr
    _ ≤ (1 / (mE E).im) * (N : Real) ^ (5 * δ / 32) *
        Step2Moment.ratR E s N v ^ (-(2 : Real)) := by
      have hfrac : 1 / (24 * (mE E).im) ≤ 1 / (mE E).im := by
        apply (div_le_div_iff₀ (by positivity) hm).2
        nlinarith [hm]
      have hprod : 0 ≤ (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-(2 : Real)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hfrac hprod]

/-- The T995 event remains nonempty at an active positive first cell. -/
noncomputable abbrev same_event_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms normalizedQuadratic
#print axioms intervalIntegrable_normalizedQuadratic
#print axioms zero_cell_integral_eq_zero
#print axioms quadratic_exponent_gap
#print axioms eventually_quadratic_integral_le_small_slot
#print axioms same_event_positive_cell_witness

end
end RBM.APrimeGeneralMovingDriftQuadraticSlotRepair
