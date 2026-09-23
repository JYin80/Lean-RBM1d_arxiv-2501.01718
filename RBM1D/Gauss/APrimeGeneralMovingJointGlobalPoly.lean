/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeCrossJointSplit
import RBM1D.Gauss.APrimeQVGlobalPoly
import RBM1D.Gauss.APrimeGeneralMovingMesh
import RBM1D.Gauss.EntryBoundTime

/-!
# T617: all-sample general-moving joint polynomial envelope

This module bounds the literal product of the smooth-prefix gradient and the
square root of the current evolved quadratic variation.  The estimate is
event-free, uniform in every active target-net prefix (including `k = 0`),
and holds at both endpoints of the closed running-time interval.
-/

namespace RBM.APrimeGeneralMovingJointGlobalPoly

open Filter Set Real CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

/-- Deterministic all-sample envelope for the literal prefix gradient. -/
noncomputable def prefixEnvelope (D : ℝ) (N : ℕ) : ℝ :=
  2 ^ (15 : ℕ) * (N : ℝ) ^ (D + 8)

/-- Deterministic all-sample envelope for the prefix/current-QV product. -/
noncomputable def jointEnvelope (D : ℝ) (N : ℕ) : ℝ :=
  2 ^ (26 : ℕ) * (N : ℝ) ^ (2 * D + 16)

theorem prefixEnvelope_nonneg (D : ℝ) (N : ℕ) :
    0 ≤ prefixEnvelope D N := by
  unfold prefixEnvelope
  positivity

theorem jointEnvelope_nonneg (D : ℝ) (N : ℕ) :
    0 ≤ jointEnvelope D N := by
  unfold jointEnvelope
  positivity

private theorem coordWeight_le (N : ℕ)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N) :
    Gauss.coordWeight d N ≤ 8 * (N : ℝ) ^ 2 := by
  have h := APrimeQVGlobalPoly.coordWt2_le d N hcard
  simpa [Gauss.coordWeight, APrimeDuhamelModel.coordWt2, pow_two] using h

/-- The raw length-two coordinate observable has a matrix-independent
quadratic-variation square-root bound once `N⁻¹ ≤ etaT E u`. -/
theorem sqrt_quadVar_coordFun_le_poly
    {E : ℝ} (N : ℕ) (hE : |E| < 2) (hN : 1 ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N)
    {u : ℝ} (hu1 : u < 1)
    (hη : (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E u)
    (a : LoopArg (d.L N) 2)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d E N u a) M) ≤
      2 ^ (15 : ℕ) * (N : ℝ) ^ (8 : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hN0 : (0 : ℝ) ≤ N := hNpos.le
  have hηpos : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hηinv : (etaT E u)⁻¹ ≤ (N : ℝ) := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hNpos (-(1 : ℝ))) hη
    simpa only [Real.rpow_neg_one, inv_inv] using hi
  let x : ℝ := (etaT E u)⁻¹
  let y : ℝ := 1 + x
  let Bres : ℝ := 2 * y ^ 3
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxy : x ≤ y := by dsimp [y]; linarith
  have hy1 : 1 ≤ y := by dsimp [y]; linarith
  have hy0 : 0 ≤ y := zero_le_one.trans hy1
  have hyN : y ≤ 2 * (N : ℝ) := by
    dsimp [y, x]
    linarith
  have hx3 : x ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hx0 hxy 3
  have hy_le_cube : y ≤ y ^ 3 := by
    calc
      y = y * 1 := (mul_one y).symm
      _ ≤ y * y ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hy1) hy0
      _ = y ^ 3 := by ring
  have hySq_le_cube : y ^ 2 ≤ y ^ 3 := by
    calc
      y ^ 2 = y ^ 2 * 1 := (mul_one (y ^ 2)).symm
      _ ≤ y ^ 2 * y := mul_le_mul_of_nonneg_left hy1 (pow_nonneg hy0 2)
      _ = y ^ 3 := by ring
  have hBa : (etaT E u)⁻¹ ≤ Bres := by
    dsimp [x, Bres] at hxy ⊢
    calc
      (etaT E u)⁻¹ ≤ y := hxy
      _ ≤ y ^ 3 := hy_le_cube
      _ ≤ 2 * y ^ 3 := by nlinarith [pow_nonneg hy0 3]
  have hBb : (etaT E u)⁻¹ * (etaT E u)⁻¹ ≤ Bres := by
    have hxx : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx0 hxy 2
    dsimp [x, Bres]
    calc
      (etaT E u)⁻¹ * (etaT E u)⁻¹ = x ^ 2 := by ring
      _ ≤ y ^ 2 := hxx
      _ ≤ y ^ 3 := hySq_le_cube
      _ ≤ 2 * y ^ 3 := by nlinarith [pow_nonneg hy0 3]
  have hBc : 2 * ((etaT E u)⁻¹ * (etaT E u)⁻¹ * (etaT E u)⁻¹) ≤ Bres := by
    dsimp [x, Bres]
    have : (etaT E u)⁻¹ * (etaT E u)⁻¹ * (etaT E u)⁻¹ = x ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hx3 (by norm_num)
  have hBres : Bres ≤ 16 * (N : ℝ) ^ 3 := by
    have hp := pow_le_pow_left₀ hy0 hyN 3
    dsimp [Bres]
    calc
      2 * y ^ 3 ≤ 2 * (2 * (N : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = 16 * (N : ℝ) ^ 3 := by ring
  have hz : (zt E u).im ≠ 0 := by
    rw [← etaT_eq_zt_im]
    exact hηpos.ne'
  have hzη : etaT E u ≤ |(zt E u).im| := by
    rw [← etaT_eq_zt_im, abs_of_pos hηpos]
  let I : LoopIdx (ZMod (d.L N)) :=
    LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)
  have hq := Gauss.quadVar_loopObs_sub_le (d := d) (N := N)
    hz hηpos hzη hBa hBb hBc (I := I)
    (LoopData.idx_wf ((Step2.sigPM, a) : LoopData (d.L N) 2))
    ((Gauss.band d).Kval E N u I) M
  have hlen : I.a.length = 2 := by
    change I.length = 2
    exact LoopData.idx_length ((Step2.sigPM, a) : LoopData (d.L N) 2)
  dsimp [I] at hq
  change Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d E N u a) M ≤
    ((Fintype.card (d.Idx N) : ℝ) *
      (((LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)).a.length : ℝ) *
        Bres ^ (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)).a.length) + 0) ^ 2 *
      Gauss.coordWeight d N at hq
  have hq' :
      Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d E N u a) M ≤
        ((Fintype.card (d.Idx N) : ℝ) * (2 * Bres ^ 2) + 0) ^ 2 *
          Gauss.coordWeight d N := by
    simpa only [show
      (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)).a.length = 2 from hlen,
      Nat.cast_ofNat] using hq
  have hcoef0 :
      0 ≤ (Fintype.card (d.Idx N) : ℝ) * (2 * Bres ^ 2) + 0 := by
    positivity
  have hcoef :
      (Fintype.card (d.Idx N) : ℝ) * (2 * Bres ^ 2) + 0 ≤
        512 * (N : ℝ) ^ 7 := by
    have hBres0 : 0 ≤ Bres := by dsimp [Bres]; positivity
    have hBsq := pow_le_pow_left₀ hBres0 hBres 2
    have htwoB : 2 * Bres ^ 2 ≤ 2 * (16 * (N : ℝ) ^ 3) ^ 2 :=
      mul_le_mul_of_nonneg_left hBsq (by norm_num)
    have hmul :
      (Fintype.card (d.Idx N) : ℝ) * (2 * Bres ^ 2) ≤
          (N : ℝ) * (2 * (16 * (N : ℝ) ^ 3) ^ 2) :=
      mul_le_mul hcard htwoB (by positivity) hN0
    calc
      (Fintype.card (d.Idx N) : ℝ) * (2 * Bres ^ 2) + 0
          ≤ (N : ℝ) * (2 * (16 * (N : ℝ) ^ 3) ^ 2) := by simpa using hmul
      _ = 512 * (N : ℝ) ^ 7 := by ring
  have hwt := coordWeight_le N hcard
  have hsqrtWt : √(Gauss.coordWeight d N) ≤ 3 * (N : ℝ) := by
    calc
      √(Gauss.coordWeight d N) ≤ √(8 * (N : ℝ) ^ 2) := Real.sqrt_le_sqrt hwt
      _ ≤ √(9 * (N : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (N : ℝ)])
      _ = 3 * (N : ℝ) := by
        rw [show 9 * (N : ℝ) ^ 2 = (3 * (N : ℝ)) ^ 2 by ring,
          Real.sqrt_sq (mul_nonneg (by norm_num) hN0)]
  have hsqrt' :
      √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d E N u a) M) ≤
        ((Fintype.card (d.Idx N) : ℝ) * (2 * Bres ^ 2) + 0) *
          √(Gauss.coordWeight d N) := by
    calc
      √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d E N u a) M) ≤
          √((((Fintype.card (d.Idx N) : ℝ) * (2 * Bres ^ 2) + 0) ^ 2) *
            Gauss.coordWeight d N) := Real.sqrt_le_sqrt hq'
      _ = √(((Fintype.card (d.Idx N) : ℝ) * (2 * Bres ^ 2) + 0) ^ 2) *
            √(Gauss.coordWeight d N) :=
          Real.sqrt_mul (sq_nonneg
            ((Fintype.card (d.Idx N) : ℝ) * (2 * Bres ^ 2) + 0)) _
      _ = ((Fintype.card (d.Idx N) : ℝ) * (2 * Bres ^ 2) + 0) *
            √(Gauss.coordWeight d N) := by rw [Real.sqrt_sq hcoef0]
  calc
    √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d E N u a) M)
        ≤ ((Fintype.card (d.Idx N) : ℝ) * (2 * Bres ^ 2) + 0) *
            √(Gauss.coordWeight d N) := hsqrt'
    _ ≤ (512 * (N : ℝ) ^ 7) * (3 * (N : ℝ)) :=
      mul_le_mul hcoef hsqrtWt (Real.sqrt_nonneg _) (by positivity)
    _ ≤ 2 ^ (15 : ℕ) * (N : ℝ) ^ (8 : ℕ) := by
      norm_num
      nlinarith [pow_nonneg hN0 8]
    _ = 2 ^ (15 : ℕ) * (N : ℝ) ^ (8 : ℝ) := by
      congr 1
      exact (Real.rpow_natCast (N : ℝ) 8).symm

/-- Division by the literal `W⁻ᴰ` floor of the tail costs at most `Nᴰ`. -/
theorem rawPrefixRate_le_poly
    {E D : ℝ} (N : ℕ) (hE : |E| < 2) (hD : 0 ≤ D)
    (hN : 1 ≤ N) (hWN : (d.W N : ℝ) ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N)
    {u : ℝ} (hu1 : u < 1)
    (hη : (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E u)
    (a : LoopArg (d.L N) 2)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d E N u a) M) /
        Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1)) ≤
      prefixEnvelope D N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hWpos : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hT : 0 < Step2.tT (Gauss.band d) E N D u
      (zdist (d.L N) (a 0 - a 1)) := by
    unfold Step2.tT
    exact tailT_pos hWpos _
  have hfloor : (d.W N : ℝ) ^ (-D) ≤
      Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1)) := by
    unfold Step2.tT
    exact rpow_neg_le_tailT _
  have hinvFloor :
      (Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1)))⁻¹ ≤
        (d.W N : ℝ) ^ D := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hWpos (-D)) hfloor
    rw [Real.rpow_neg hWpos.le, inv_inv] at hi
    exact hi
  have hWpow : (d.W N : ℝ) ^ D ≤ (N : ℝ) ^ D :=
    Real.rpow_le_rpow hWpos.le hWN hD
  have hinv := hinvFloor.trans hWpow
  have hraw := sqrt_quadVar_coordFun_le_poly N hE hN hcard hu1 hη a M
  rw [div_eq_mul_inv]
  calc
    √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d E N u a) M) *
          (Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1)))⁻¹
        ≤ (2 ^ (15 : ℕ) * (N : ℝ) ^ (8 : ℝ)) * (N : ℝ) ^ D :=
      mul_le_mul hraw hinv (inv_nonneg.2 hT.le) (by positivity)
    _ = prefixEnvelope D N := by
      unfold prefixEnvelope
      rw [mul_assoc, Real.rpow_add hNpos]
      ring

/-- Pointwise all-sample prefix-gradient bound at an active target-net prefix. -/
theorem prefixGradient_le_poly
    {E D : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (_hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (N k : ℕ) (hN : 1 ≤ N) (hdim : d.W N * d.L N ≤ N)
    (hηt : (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E (t N))
    (hk : k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N)
    (omega : Gauss.Ω d) :
    APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
        (APrimeGeneralMovingMesh.targetMesh D) N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N) omega ≤
      prefixEnvelope D N := by
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL1 : 1 ≤ d.L N := le_trans (by norm_num) (d.three_le_L N)
  have hWNnat : d.W N ≤ N := by nlinarith
  have hWN : (d.W N : ℝ) ≤ N := by exact_mod_cast hWNnat
  have hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N := by
    have hc : (Fintype.card (d.Idx N) : ℝ) =
        (d.W N : ℝ) * (d.L N : ℝ) := by
      change ((Fintype.card (ZMod (d.L N) × Fin (d.W N)) : ℕ) : ℝ) = _
      rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]
      push_cast
      ring
    rw [hc]
    exact_mod_cast hdim
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hmesh := APrimeGeneralMovingMesh.targetMesh_pos D N
  have huWindow : ∀ j < k,
      cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j ∈ Set.Icc (s N) (t N) := by
    intro j hj
    have hjtop : j ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N := by omega
    exact MomentDuhamelCut.netFinset_subset_Icc (hst N) hmesh _
      (cutNetPt_mem_netFinset hjtop)
  have hu : ∀ j < k,
      cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j < 1 := by
    intro j hj
    exact (huWindow j hj).2.trans_lt (ht1 N)
  let K : ℝ := prefixEnvelope D N
  have hK0 : 0 ≤ K := prefixEnvelope_nonneg D N
  have hD0 : 0 ≤ D := by linarith
  have hKraw : ∀ j < k, ∀ a : LoopArg (d.L N) 2,
      √(Gauss.quadVar d N
          (APrimeSmoothPrefix.coordFun d E N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j) a)
          ((Real.sqrt
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j) : ℂ) •
              Gauss.Xmat d N omega)) /
        Step2.tT (Gauss.band d) E N D
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j)
          (zdist (d.L N) (a 0 - a 1)) ≤ K := by
    intro j hj a
    have hηu : (N : ℝ) ^ (-(1 : ℝ)) ≤
        etaT E (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j) :=
      hηt.trans (Gauss.etaT_le_of_le hE (huWindow j hj).2)
    exact rawPrefixRate_le_poly N hE hD0 hN hWN hcard (hu j hj) hηu a _
  have hK : ∀ j < k,
      Real.sqrt (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j) *
        (((Step2Moment.ratR E s N
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j)) ^ 4)⁻¹ * K) ≤ K := by
    intro j hj
    have hjmem := huWindow j hj
    have hR1 : 1 ≤ Step2Moment.ratR E s N
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j) :=
      Step2Moment.one_le_ratR hE hjmem.1 (hjmem.2.trans_lt (ht1 N))
    have hR4 : 1 ≤ (Step2Moment.ratR E s N
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j)) ^ 4 :=
      one_le_pow₀ hR1
    have hRinv : ((Step2Moment.ratR E s N
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j)) ^ 4)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hR4
    have hsqrt : Real.sqrt
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j) ≤ 1 :=
      Real.sqrt_le_one.2 (by linarith [_hs0 N, hjmem.1, hjmem.2, ht1 N])
    calc
      Real.sqrt (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j) *
          (((Step2Moment.ratR E s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j)) ^ 4)⁻¹ * K)
        ≤ 1 * (1 * K) := by gcongr
      _ = K := by ring
  have hnum := APrimeSmoothWeightActual.sqrt_quadVar_prefixMatrix_le_exp d
    (E := E) (D := D) (s := s)
    (mesh := APrimeGeneralMovingMesh.targetMesh D) (N := N) (k := k)
    (m := APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)
    hE hs1 hNpos
    (APrimeSmoothWeightActual.canonicalM_pos d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)
    hu (Gauss.Xmat d N omega) (fun _ => K) K hK0
    (APrimeSmoothWeightActual.canonicalM_calibration d s t
      (APrimeGeneralMovingMesh.targetMesh D) N k hk)
    hKraw hK
  have hpow : 1 ≤ (N : ℝ) ^ (2 * deltaWeight) :=
    Real.one_le_rpow hNr (by linarith)
  have htheta : Real.exp 1 ≤ APrimeSmoothWeightActual.threshold deltaWeight N := by
    unfold APrimeSmoothWeightActual.threshold
    have hc0 : 0 ≤ 8 * (Real.exp 1) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg (Real.exp 1))
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    calc
      Real.exp 1 ≤ 8 * (Real.exp 1) ^ 2 := by
        nlinarith [sq_nonneg (Real.exp 1)]
      _ = (8 * (Real.exp 1) ^ 2) * 1 := by ring
      _ ≤ (8 * (Real.exp 1) ^ 2) * (N : ℝ) ^ (2 * deltaWeight) :=
        mul_le_mul_of_nonneg_left hpow hc0
  have hthetaPos :=
    APrimeSmoothWeightActual.threshold_pos (δ := deltaWeight) hNpos
  unfold APrimeCrossJointSplit.prefixGradient
  calc
    √(Gauss.quadVar d N
        (fun M => ((APrimeSmoothWeightActual.prefixMatrix d E D s
          (APrimeGeneralMovingMesh.targetMesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t
            (APrimeGeneralMovingMesh.targetMesh D) N) M : ℝ) : ℂ))
        (Gauss.Xmat d N omega)) / APrimeSmoothWeightActual.threshold deltaWeight N
      ≤ (Real.exp 1 * K) / APrimeSmoothWeightActual.threshold deltaWeight N :=
        div_le_div_of_nonneg_right hnum hthetaPos.le
    _ ≤ K := (div_le_iff₀ hthetaPos).2 <| by
      simpa [mul_comm] using mul_le_mul_of_nonneg_right htheta hK0
    _ = prefixEnvelope D N := rfl

/-- Eventual all-sample prefix-gradient estimate on the target mesh and with
the canonical smoothing order. -/
theorem eventually_prefixGradient_le_poly
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ omega : Gauss.Ω d,
        APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
            (APrimeGeneralMovingMesh.targetMesh D) N k
            (APrimeSmoothWeightActual.canonicalM d s t
              (APrimeGeneralMovingMesh.targetMesh D) N) omega ≤
          prefixEnvelope D N := by
  have heta := Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  filter_upwards [d.dim, eventually_ge_atTop 1, heta] with N hdim hN hetaN
  intro k hk omega
  exact prefixGradient_le_poly hE hD hs0 hst ht1 hdeltaWeight
    N k hN hdim.1 hetaN hk omega

/-- Square-root adapter for the global evolved-QV polynomial estimate. -/
theorem sqrt_qvAt_le_poly
    {E D : ℝ} (N : ℕ) (hN : 1 ≤ N)
    (sigma : Fin 2 → Bool) (a : LoopArg (d.L N) 2)
    (s v r : ℝ) (omega : Gauss.Ω d)
    (hq : APrimeDriftTimeFamily.qvAt d E D N sigma a s v r omega ≤
      2 ^ (21 : ℕ) * (N : ℝ) ^ (2 * D + 16)) :
    √(APrimeDriftTimeFamily.qvAt d E D N sigma a s v r omega) ≤
      2 ^ (11 : ℕ) * (N : ℝ) ^ (D + 8) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hpow : ((N : ℝ) ^ (D + 8)) ^ 2 =
      (N : ℝ) ^ ((D + 8) * 2) := by
    rw [Real.rpow_mul hNpos.le, Real.rpow_ofNat]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      APrimeDriftTimeFamily.qvAt d E D N sigma a s v r omega
          ≤ 2 ^ (21 : ℕ) * (N : ℝ) ^ (2 * D + 16) := hq
      _ ≤ 2 ^ (22 : ℕ) * (N : ℝ) ^ (2 * D + 16) :=
        mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hNpos.le _)
      _ = (2 ^ (11 : ℕ) * (N : ℝ) ^ (D + 8)) ^ 2 := by
        rw [mul_pow]
        norm_num
        rw [hpow]
        congr 1
        ring

/-- Literal all-sample joint envelope, uniform in arbitrary charge word,
output, closed running time, and sample. -/
theorem eventually_prefixGradient_mul_sqrt_qvAt_le_poly
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ sigma : Fin 2 → Bool,
      ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Set.Icc (s N)
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
      ∀ omega : Gauss.Ω d,
        APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
            (APrimeGeneralMovingMesh.targetMesh D) N k
            (APrimeSmoothWeightActual.canonicalM d s t
              (APrimeGeneralMovingMesh.targetMesh D) N) omega *
          √(APrimeDriftTimeFamily.qvAt d E D N sigma a (s N)
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r omega) ≤
          jointEnvelope D N := by
  have hpref := eventually_prefixGradient_le_poly hE hD hs0 hst ht1 hc hreg
    hdeltaWeight
  have heta := Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  have hqev := APrimeQVGlobalPoly.eventually_qvAt_le_poly d
    (E := E) (D := D) (Kη := 1) hE (by linarith) (by norm_num)
  filter_upwards [hpref, heta, hqev, eventually_ge_atTop 1] with
      N hprefN hetaN hqN hN
  intro k hk sigma a r hr omega
  have hv : cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k ∈
      Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k < 1 :=
    hv.2.trans_lt (ht1 N)
  have hηv : (N : ℝ) ^ (-(1 : ℝ)) ≤
      etaT E (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) :=
    hetaN.trans (Gauss.etaT_le_of_le hE hv.2)
  have hq := hqN (s N)
    (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)
    (hs0 N) hv.1 hv1 hηv sigma a r hr omega
  have hq' : APrimeDriftTimeFamily.qvAt d E D N sigma a (s N)
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r omega ≤
        2 ^ (21 : ℕ) * (N : ℝ) ^ (2 * D + 16) := by
    convert hq.2 using 1 <;> ring
  have hsqrt := sqrt_qvAt_le_poly N hN sigma a (s N)
    (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r omega hq'
  have hp := hprefN k hk omega
  have hp0 : 0 ≤ APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N) omega := by
    unfold APrimeCrossJointSplit.prefixGradient
    exact div_nonneg (Real.sqrt_nonneg _)
      (APrimeSmoothWeightActual.threshold_pos (δ := deltaWeight)
        (by omega)).le
  calc
    APrimeCrossJointSplit.prefixGradient d E D deltaWeight s
          (APrimeGeneralMovingMesh.targetMesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t
            (APrimeGeneralMovingMesh.targetMesh D) N) omega *
        √(APrimeDriftTimeFamily.qvAt d E D N sigma a (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r omega)
      ≤ prefixEnvelope D N *
          (2 ^ (11 : ℕ) * (N : ℝ) ^ (D + 8)) :=
        mul_le_mul hp hsqrt (Real.sqrt_nonneg _) (prefixEnvelope_nonneg D N)
    _ = jointEnvelope D N := by
      unfold prefixEnvelope jointEnvelope
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      calc
        (2 ^ (15 : ℕ) * (N : ℝ) ^ (D + 8)) *
            (2 ^ (11 : ℕ) * (N : ℝ) ^ (D + 8)) =
          2 ^ (26 : ℕ) *
            ((N : ℝ) ^ (D + 8) * (N : ℝ) ^ (D + 8)) := by
              norm_num
              ring
        _ = 2 ^ (26 : ℕ) * (N : ℝ) ^ ((D + 8) + (D + 8)) := by
          rw [← Real.rpow_add hNpos]
        _ = 2 ^ (26 : ℕ) * (N : ℝ) ^ (2 * D + 16) := by ring

/-- The one-extra-power payment adapter used on a high-probability
complement. -/
theorem eventually_jointEnvelope_le_rpow {D : ℝ} (_hD : 60 ≤ D) :
    ∀ᶠ N : ℕ in atTop,
      jointEnvelope D N ≤ (N : ℝ) ^ (2 * D + 17) := by
  filter_upwards [eventually_ge_atTop (2 ^ (26 : ℕ))] with N hN
  have hconst : (2 : ℝ) ^ (26 : ℕ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  unfold jointEnvelope
  calc
    2 ^ (26 : ℕ) * (N : ℝ) ^ (2 * D + 16) ≤
        (N : ℝ) * (N : ℝ) ^ (2 * D + 16) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (2 * D + 16) := by
      rw [Real.rpow_one]
    _ = (N : ℝ) ^ ((1 : ℝ) + (2 * D + 16)) :=
      (Real.rpow_add hNpos 1 (2 * D + 16)).symm
    _ = (N : ℝ) ^ (2 * D + 17) := by ring

/-- The deterministic assumptions used by the envelope admit a genuine
positive-duration first-cell window in the fixed growing Gaussian model. -/
theorem envelope_hypotheses_witness :
    ∃ E D c : ℝ, ∃ s t : ℕ → ℝ,
      E = 0 ∧ D = 60 ∧ |E| < 2 ∧ 60 ≤ D ∧
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ 0 < c ∧
      Cond272Reg (Gauss.band d) E s t c ∧
      ∀ᶠ N : ℕ in atTop, s N < t N := by
  have hcap : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-1 + (1 : ℝ) / 2) ≤ 1 - (1 / 2 : ℝ) := by
    filter_upwards [eventually_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_ge_atTop 1] with N hNpow hN
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hEq : (N : ℝ) ^ (-1 + (1 : ℝ) / 2) =
        ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [show -1 + (1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
        Real.rpow_neg hN0]
    rw [hEq]
    have hInv : ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ (2 : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hNpow)
    norm_num at hInv ⊢
    exact hInv
  obtain ⟨tauPrime, htauPrime, c, hc, _n0, hgrid⟩ :=
    cond272Reg_grid_step_domain B (κ := 1) (τ := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)
  obtain ⟨_, hsteps⟩ := hgrid 0 (by norm_num) (fun _ => (1 / 2 : ℝ))
    (fun _ => by norm_num) hcap
  obtain ⟨hs0, hst, ht1, hreg⟩ := hsteps 0
  let s : ℕ → ℝ := fun N => gridT (B.W N) tauPrime (1 / 2 : ℝ) 0
  let t : ℕ → ℝ := fun N => gridT (B.W N) tauPrime (1 / 2 : ℝ) 1
  have hstrict : ∀ᶠ N : ℕ in atTop, s N < t N := by
    simpa only [s, t] using
      (Gauss.eventually_gridT_zero_lt_gridT_one B htauPrime
        (Eventually.of_forall fun _ => by norm_num :
          ∀ᶠ N : ℕ in atTop, 0 < (1 / 2 : ℝ)))
  refine ⟨0, 60, c, s, t, rfl, rfl, by norm_num, by norm_num, ?_⟩
  simpa only [s, t] using
    And.intro hs0 (And.intro hst (And.intro ht1 (And.intro hc
      (And.intro hreg hstrict))))

#print axioms prefixEnvelope
#print axioms jointEnvelope
#print axioms prefixEnvelope_nonneg
#print axioms jointEnvelope_nonneg
#print axioms sqrt_quadVar_coordFun_le_poly
#print axioms rawPrefixRate_le_poly
#print axioms prefixGradient_le_poly
#print axioms eventually_prefixGradient_le_poly
#print axioms sqrt_qvAt_le_poly
#print axioms eventually_prefixGradient_mul_sqrt_qvAt_le_poly
#print axioms eventually_jointEnvelope_le_rpow
#print axioms envelope_hypotheses_witness

end RBM.APrimeGeneralMovingJointGlobalPoly
