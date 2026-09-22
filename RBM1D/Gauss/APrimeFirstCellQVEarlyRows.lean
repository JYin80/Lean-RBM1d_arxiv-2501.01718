/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVCurrentRows
import RBM1D.Gauss.APrimeFirstCellQVEarlyRaw

/-!
# T447: actual stored-time full QV three-row bound

T438's complete fixed-two coefficient estimate is inserted into T439's
literal stored-time normalization.  Thus the near row, repaired `W⁻¹` row,
both far powers, and the `WL W⁻⁶⁰` row are all paid before the three stored
time powers are exposed.
-/

namespace RBM.APrimeFirstCellQVEarlyRows

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable def storedRowsRate (δ ν : ℝ) (N : ℕ) (v u : ℝ) : ℝ :=
  16384 * (N : ℝ) ^ (ν - 4 * δ) * (etaT 0 0)⁻¹ *
    (APrimeFirstCellLoopCap.xRate u ^ (-(9 / 2 : ℝ)) +
      (N : ℝ) ^ (4 * δ + 2 * (δ / 16)) *
        (APrimeFirstCellLoopCap.endpointScale N v) ^ (-(1 / 2 : ℝ)) *
          APrimeFirstCellLoopCap.xRate u ^ (7 / 4 : ℝ) +
      (N : ℝ) ^ (6 * δ + 3 * (δ / 16)) *
        (APrimeFirstCellLoopCap.endpointScale N v)⁻¹ *
          APrimeFirstCellLoopCap.xRate u ^ (5 : ℝ))

/-- The full T439 normalized quadratic variation bounded by the three
stored-time rows. -/
def storedRowsAt (δ ν : ℝ) (N : ℕ) (ω : Ω d) (v u : ℝ)
    (a : LoopArg (d.L N) 2) : Prop :=
  Gauss.quadVar B.toDims N
      (fun M' => MomentDuhamel.lkFun B 0 N u M' Step2.sigPM a)
      ((sample d).H N u ω) /
        (Step2.tT B 0 N 60 u (zdist (d.L N) (a 0 - a 1)) ^ 2 *
          APrimeFirstCellLoopCap.xRate u ^ 8 *
            ((N : ℝ) ^ (2 * δ)) ^ 2) ≤
    storedRowsRate δ ν N v u

private theorem normalized_preRows_identity
    {N : ℕ} {δ τ ν A x Av : ℝ}
    (hN : 0 < (N : ℝ)) (hx : 0 < x) :
    (16384 * (N : ℝ) ^ ν * A * x *
        (x ^ (5 / 2 : ℝ) +
          (N : ℝ) ^ (4 * δ + 2 * τ) * Av ^ (-(1 / 2 : ℝ)) *
            x ^ (35 / 4 : ℝ) +
          (N : ℝ) ^ (6 * δ + 3 * τ) * Av⁻¹ * x ^ (12 : ℝ))) /
      (x ^ 8 * ((N : ℝ) ^ (2 * δ)) ^ 2) =
    16384 * (N : ℝ) ^ (ν - 4 * δ) * A *
      (x ^ (-(9 / 2 : ℝ)) +
        (N : ℝ) ^ (4 * δ + 2 * τ) * Av ^ (-(1 / 2 : ℝ)) *
          x ^ (7 / 4 : ℝ) +
        (N : ℝ) ^ (6 * δ + 3 * τ) * Av⁻¹ * x ^ (5 : ℝ)) := by
  have hNpow : ((N : ℝ) ^ (2 * δ)) ^ 2 = (N : ℝ) ^ (4 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    ring
  have hNsub : (N : ℝ) ^ (ν - 4 * δ) =
      (N : ℝ) ^ ν / (N : ℝ) ^ (4 * δ) := Real.rpow_sub hN _ _
  have hx1 : x ^ (-(9 / 2 : ℝ)) =
      (x * x ^ (5 / 2 : ℝ)) / x ^ 8 := by
    rw [show -(9 / 2 : ℝ) = (1 + 5 / 2) - 8 by ring,
      Real.rpow_sub hx, Real.rpow_add hx, Real.rpow_one]
    norm_num only [Real.rpow_ofNat]
  have hx2 : x ^ (7 / 4 : ℝ) =
      (x * x ^ (35 / 4 : ℝ)) / x ^ 8 := by
    rw [show (7 / 4 : ℝ) = (1 + 35 / 4) - 8 by ring,
      Real.rpow_sub hx, Real.rpow_add hx, Real.rpow_one]
    norm_num only [Real.rpow_ofNat]
  have hx3 : x ^ (5 : ℝ) = (x * x ^ (12 : ℝ)) / x ^ 8 := by
    rw [show (5 : ℝ) = (1 + 12) - 8 by ring,
      Real.rpow_sub hx, Real.rpow_add hx, Real.rpow_one]
    norm_num only [Real.rpow_ofNat]
  rw [hNpow, hNsub, hx1, hx2, hx3]
  field_simp [(Real.rpow_pos_of_pos hN _).ne',
    (Real.rpow_pos_of_pos hx _).ne']

/-- Insert T438's complete fixed-two coefficient estimate into the exact
T439 stored-time normalization. -/
theorem storedRowsAt_of_raw_of_scales {δ ν : ℝ}
    (hδ : 0 ≤ δ) (hν : 0 < ν) (N : ℕ) {ω : Ω d} {v u : ℝ}
    (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (hN : 1 ≤ (N : ℝ))
    (hWexp : Real.exp 1 ≤ (d.W N : ℝ))
    (hAN : (d.W N : ℝ) * B.ell N u * etaT 0 u ≤ N)
    (hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N)
    (hNW : (N : ℝ) ≤ (d.W N : ℝ) ^ 2)
    (hNear : Lemma57.cNear2 (d.W N : ℝ) (B.ell N u) ≤
      (N : ℝ) ^ (ν / 8))
    (hFar : Lemma57.cFar2 (d.W N : ℝ) (B.ell N u) ≤
      (N : ℝ) ^ (ν / 8))
    (a : LoopArg (d.L N) 2)
    (hraw : APrimeFirstCellQVEarlyRaw.fixedTwoEarlyRawAt
      δ ν N ω u a) : storedRowsAt δ ν N ω v u a := by
  have hu1 : u < 1 := huv.trans_lt hv1
  have hv0 : 0 ≤ v := hu0.trans huv
  have hηu : 0 < etaT 0 u := etaT_pos_of_lt_one (by norm_num) hu1
  have hη1 : etaT 0 u ≤ 1 := etaT_le_one (by norm_num) hu0
  have hη0 : 0 < etaT 0 0 := etaT_pos_of_lt_one (by norm_num) (by norm_num)
  have hW1 : 1 ≤ (d.W N : ℝ) :=
    (Real.one_le_exp (by norm_num)).trans hWexp
  have hAr : 0 < B.scale 0 N u :=
    B.scale_pos' (by norm_num) N hu0 hu1
  have hAN' : B.scale 0 N u ≤ (N : ℝ) := by
    change (d.W N : ℝ) * B.ell N u * etaT 0 u ≤ (N : ℝ)
    exact hAN
  have hLeak : (d.W N : ℝ) * (d.L N : ℝ) *
      (d.W N : ℝ) ^ (-(60 : ℝ)) ≤
        (etaT 0 u)⁻¹ * (B.scale 0 N u)⁻¹ :=
    APrimeFullQV.ExponentRows.leak_paid_by_dims hW1 hN hAr hηu
      hWL hAN' hNW hη1 (by norm_num)
  let ζ := APrimeFirstCellEGAllOutputRunning.sourceLoss ν
  have hζ : 0 < ζ := by
    dsimp [ζ]
    exact APrimeFirstCellEGAllOutputRunning.sourceLoss_pos hν
  have hellS : 0 < APrimeFirstCellSourceAllTime.ellSource ζ N := by
    unfold APrimeFirstCellSourceAllTime.ellSource
    positivity
  have hNz : 1 ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hN hζ.le
  have hbase : 1 ≤ 2 * (N : ℝ) ^ ζ := by nlinarith
  have hellS1 : APrimeFirstCellSourceAllTime.ellSource ζ N ≤ 1 := by
    unfold APrimeFirstCellSourceAllTime.ellSource
    exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num)
  have hell1 : 1 ≤ B.ell N u :=
    one_le_ellHat (d.L N) (d.three_le_L N) hu0 hu1
  have hratio : 1 ≤ B.ell N u /
      APrimeFirstCellSourceAllTime.ellSource ζ N := by
    apply (le_div_iff₀ hellS).2
    nlinarith
  have hFloor : (d.W N : ℝ)⁻¹ ≤ (etaT 0 u)⁻¹ *
      (B.ell N u / APrimeFirstCellSourceAllTime.ellSource ζ N) ^ (5 : ℕ) :=
    APrimeFullQV.ExponentRows.floor_paid hW1 hηu hη1 hratio
  have hC : 1 ≤ (N : ℝ) ^ (ν / 8) :=
    Real.one_le_rpow hN (by positivity)
  have hcoeff := APrimeFirstCellQVCurrentRows.fixed_two_coefficient_le
    N hu0 huv hv1 hN hζ.le hδ (by positivity : 0 ≤ δ / 16) hC
      hNear hFar hLeak hFloor
  have hζle : ζ ≤ ν / 128 := by
    dsimp [ζ, APrimeFirstCellEGAllOutputRunning.sourceLoss,
      APrimeFirstCellEGFarSmallRunning.sourceLoss]
    calc
      min ((ν / 2) / 64) (1 / 64) ≤ (ν / 2) / 64 := min_le_left _ _
      _ = ν / 128 := by ring
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hNloss : (N : ℝ) ^ (ν / 8) * (N : ℝ) ^ ζ ≤
      (N : ℝ) ^ ν := by
    calc
      _ = (N : ℝ) ^ (ν / 8 + ζ) := by rw [Real.rpow_add hNpos]
      _ ≤ (N : ℝ) ^ ν := by
        apply Real.rpow_le_rpow_of_exponent_le hN
        linarith
  have hpre0 : 0 ≤ APrimeFirstCellQVCurrentRows.preRows
      δ (δ / 16) N v u := by
    unfold APrimeFirstCellQVCurrentRows.preRows
    have hAv : 0 < APrimeFirstCellLoopCap.endpointScale N v :=
      B.scale_pos' (by norm_num) N hv0 hv1
    have hN0 : (0 : ℝ) ≤ N := zero_le_one.trans hN
    have hx0 : 0 ≤ APrimeFirstCellLoopCap.xRate u := by
      unfold APrimeFirstCellLoopCap.xRate
      exact (div_pos hη0 hηu).le
    exact add_nonneg
      (add_nonneg (Real.rpow_nonneg hx0 _)
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hN0 _)
            (Real.rpow_nonneg hAv.le _))
          (Real.rpow_nonneg hx0 _)))
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hN0 _) (inv_nonneg.mpr hAv.le))
        (Real.rpow_nonneg hx0 _))
  have hfac0 : 0 ≤ (etaT 0 u)⁻¹ *
      APrimeFirstCellQVCurrentRows.preRows δ (δ / 16) N v u :=
    mul_nonneg (inv_nonneg.mpr hηu.le) hpre0
  have hcoeff' :
      APrimeQVEndpoint.diagNearRate B N (B.ell N u)
          (APrimeFirstCellSourceAllTime.ellSource ζ N) (etaT 0 u) +
        2 * (d.W N : ℝ)⁻¹ +
        APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT 0 u) 60 2
          (APrimeFirstCellSourceAllTime.sourceC4 ζ N u) ≤
      16384 * (N : ℝ) ^ ν * (etaT 0 u)⁻¹ *
        APrimeFirstCellQVCurrentRows.preRows δ (δ / 16) N v u := by
    calc
      _ ≤ 16384 * (N : ℝ) ^ (ν / 8) * (N : ℝ) ^ ζ *
          (etaT 0 u)⁻¹ *
            APrimeFirstCellQVCurrentRows.preRows δ (δ / 16) N v u := hcoeff
      _ ≤ 16384 * (N : ℝ) ^ ν * (etaT 0 u)⁻¹ *
          APrimeFirstCellQVCurrentRows.preRows δ (δ / 16) N v u := by
        have hh := mul_le_mul_of_nonneg_left hNloss (by norm_num : (0 : ℝ) ≤ 16384)
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh hfac0
  have hx : 0 < APrimeFirstCellLoopCap.xRate u := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos hη0 hηu
  have hηeq : (etaT 0 u)⁻¹ =
      (etaT 0 0)⁻¹ * APrimeFirstCellLoopCap.xRate u := by
    simp [APrimeFirstCellLoopCap.xRate, etaT, mE_zero]
  have hden : 0 ≤ APrimeFirstCellLoopCap.xRate u ^ 8 *
      ((N : ℝ) ^ (2 * δ)) ^ 2 := by positivity
  unfold storedRowsAt
  unfold APrimeFirstCellQVEarlyRaw.fixedTwoEarlyRawAt at hraw
  calc
    _ ≤ (APrimeQVEndpoint.diagNearRate B N (B.ell N u)
          (APrimeFirstCellSourceAllTime.ellSource ζ N) (etaT 0 u) +
        2 * (d.W N : ℝ)⁻¹ +
        APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT 0 u) 60 2
          (APrimeFirstCellSourceAllTime.sourceC4 ζ N u)) /
        (APrimeFirstCellLoopCap.xRate u ^ 8 *
          ((N : ℝ) ^ (2 * δ)) ^ 2) := by
      simpa only [ζ, APrimeFirstCellLoopCap.xRate] using hraw
    _ ≤ (16384 * (N : ℝ) ^ ν * (etaT 0 u)⁻¹ *
          APrimeFirstCellQVCurrentRows.preRows δ (δ / 16) N v u) /
        (APrimeFirstCellLoopCap.xRate u ^ 8 *
          ((N : ℝ) ^ (2 * δ)) ^ 2) :=
      div_le_div_of_nonneg_right hcoeff' hden
    _ = storedRowsRate δ ν N v u := by
      rw [hηeq]
      unfold APrimeFirstCellQVCurrentRows.preRows storedRowsRate
      simpa only [mul_assoc] using
        (normalized_preRows_identity
          (δ := δ) (τ := δ / 16) (ν := ν)
          (A := (etaT 0 0)⁻¹)
          (x := APrimeFirstCellLoopCap.xRate u)
          (Av := APrimeFirstCellLoopCap.endpointScale N v) hNpos hx)

/-- Every actual stored `j<k` on the T434 event carries all three early-QV
rows with the moving endpoint `v=u_k`. -/
def rowsOnStoredPrefixes (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      ∀ j < k,
        let u := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N j
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
        u ∈ Set.Icc (0 : ℝ) v ∧
        v ≤ firstCellT τ' N ∧
        (APrimeFirstCellLoopCap.endpointScale N v ≤ B.scale 0 N u) ∧
        ∀ a : LoopArg (d.L N) 2, storedRowsAt δ ν N ω v u a

theorem eventually_rows_on_stored_prefixes {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 ≤ δ) (hν : 0 < ν) :
    rowsOnStoredPrefixes τ' δ ν := by
  filter_upwards [
    APrimeFirstCellQVEarlyRaw.eventually_earlyRaw_on_stored_prefixes hτ',
    APrimeFirstCellQVRunningSmall.eventually_coefficients_uniform
      (show 0 < ν / 8 by positivity),
    APrimeFirstCellQVRunningProfile.eventually_running_scales,
    eventually_ge_atTop 2] with N hraw hcoeff hscale hN2
  intro ω hω N0 p k m hN0 hp hm hk1 hk hw j hjk
  dsimp only
  have hj := hraw ω hω N0 p k m hN0 hp hm hk1 hk hw j hjk
  let u := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j
  let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k
  have hvCell := MomentDuhamelCut.netFinset_subset_Icc
    (APrimeSupportRunning.firstT_bounds hτ' N).1
    (APrimeSupportRunning.mesh_pos N) v (cutNetPt_mem_netFinset hk)
  have huv : u ≤ v := by
    have hcast : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk.le
    have hdiv := (div_le_div_iff_of_pos_right
      (APrimeSupportRunning.mesh_pos N)).2 hcast
    simpa only [u, v, cutNetPt, zero_add] using hdiv
  have huHalf : u ∈ Set.Icc (0 : ℝ) (1 / 2) := hj.1
  have hvHalf : v ≤ (1 / 2 : ℝ) :=
    hvCell.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2
  have hv1 : v < 1 := hvHalf.trans_lt (by norm_num)
  obtain ⟨hWexp, _hlog4, _hlog, hN, _heta, _hAu, hAN, hWL, hNW⟩ :=
    hscale u huHalf
  obtain ⟨hNear, hFar⟩ := hcoeff u huHalf
  have hAvAu : APrimeFirstCellLoopCap.endpointScale N v ≤ B.scale 0 N u := by
    rw [APrimeFirstCellLoopCap.endpointScale, B.scale_eq_flowScale,
      B.scale_eq_flowScale]
    exact flowScale_antitoneOn (show (0 : ℝ) ≤ B.W N by positivity)
      (B.L N) 0 (Set.mem_Iic.2 (huv.trans_lt hv1).le)
        (Set.mem_Iic.2 hv1.le) huv
  refine ⟨⟨huHalf.1, huv⟩, hvCell.2, hAvAu, ?_⟩
  intro a
  exact storedRowsAt_of_raw_of_scales hδ hν N huHalf.1 huv hv1 hN
    hWexp hAN hWL hNW hNear hFar a (hj.2.2.2.2.2.2 a)

/-- A single positive `k=2` resident carries the `j=0` and positive `j=1`
stored rows for every label. -/
def positiveRowsPlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N,
    let u0 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0
    let u1 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1
    let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2
    u0 = 0 ∧ 0 < u1 ∧ u1 < v ∧ v ≤ firstCellT τ' N ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    (∀ a : LoopArg (d.L N) 2, storedRowsAt δ ν N ω v u0 a) ∧
    ∀ a : LoopArg (d.L N) 2, storedRowsAt δ ν N ω v u1 a

theorem positiveRowsPlateau_of_raw {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 ≤ δ) (hν : 0 < ν)
    (hpositive : APrimeFirstCellQVEarlyRaw.positiveEarlyRawPlateau
      τ' δ ν) : positiveRowsPlateau τ' δ ν := by
  filter_upwards [hpositive,
    APrimeFirstCellQVRunningSmall.eventually_coefficients_uniform
      (show 0 < ν / 8 by positivity),
    APrimeFirstCellQVRunningProfile.eventually_running_scales,
    eventually_ge_atTop 2] with N hpositive hcoeff hscale hN2
  dsimp only [APrimeFirstCellQVEarlyRaw.positiveEarlyRawPlateau] at hpositive
  obtain ⟨ω, hω, hu1pos, hu12, hvle, hw, hu0,
    _hsource0, _hsource1, _hJ0, _hJ1, _hratio0, _hratio1,
    hraw0, hraw1⟩ := hpositive
  let u0 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0
  let u1 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1
  let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2
  have hvHalf : v ≤ (1 / 2 : ℝ) :=
    hvle.trans (APrimeSupportRunning.firstT_bounds hτ' N).2
  have hv1 : v < 1 := hvHalf.trans_lt (by norm_num)
  have hu0Half : u0 ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    dsimp [u0]
    rw [hu0]
    norm_num
  have hu1Half : u1 ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hu1pos.le, hu12.le.trans hvHalf⟩
  obtain ⟨hW0, _hl40, _hl0, hN0, _he0, _hA0, hAN0, hWL0, hNW0⟩ :=
    hscale u0 hu0Half
  obtain ⟨hW1, _hl41, _hl1, hN1, _he1, _hA1, hAN1, hWL1, hNW1⟩ :=
    hscale u1 hu1Half
  obtain ⟨hNear0, hFar0⟩ := hcoeff u0 hu0Half
  obtain ⟨hNear1, hFar1⟩ := hcoeff u1 hu1Half
  have hu0v : u0 ≤ v := by
    dsimp only [u0, v]
    rw [hu0]
    exact hu1pos.le.trans hu12.le
  have hrows0 : ∀ a : LoopArg (d.L N) 2,
      storedRowsAt δ ν N ω v u0 a := by
    intro a
    exact storedRowsAt_of_raw_of_scales hδ hν N hu0Half.1 hu0v
      hv1 hN0 hW0 hAN0 hWL0 hNW0 hNear0 hFar0 a (hraw0 a)
  have hrows1 : ∀ a : LoopArg (d.L N) 2,
      storedRowsAt δ ν N ω v u1 a := by
    intro a
    exact storedRowsAt_of_raw_of_scales hδ hν N hu1Half.1 hu12.le
      hv1 hN1 hW1 hAN1 hWL1 hNW1 hNear1 hFar1 a (hraw1 a)
  exact ⟨ω, hω, hu0, hu1pos, hu12, hvle, hw, hrows0, hrows1⟩

/-- Closed T447 producer with the T434 parameter order unchanged. -/
theorem exists_rows_on_stored_prefixes_with_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ ν : ℝ, 0 < ν →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ ν) ∧
        rowsOnStoredPrefixes τ' δ ν ∧
        positiveRowsPlateau τ' δ ν := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellQVEarlyRaw.exists_earlyRaw_on_stored_prefixes_with_plateau
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 ν hν
  obtain ⟨hmeas, hp, _hraw, hpositive⟩ := hall δ hδ hδ100 ν hν
  exact ⟨hmeas, hp, eventually_rows_on_stored_prefixes hτ' hδ.le hν,
    positiveRowsPlateau_of_raw hτ' hδ.le hν hpositive⟩

#print axioms storedRowsAt_of_raw_of_scales
#print axioms eventually_rows_on_stored_prefixes
#print axioms positiveRowsPlateau_of_raw
#print axioms exists_rows_on_stored_prefixes_with_plateau

end RBM.APrimeFirstCellQVEarlyRows
