/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVEarlyRows
import RBM1D.Gauss.APrimeCrossJointSplit

/-!
# T455: same-event favorable prefix-gradient rate

The stored early quadratic-variation rows of T447 are contracted through the
actual smooth prefix of T333.  The result stops at the unabsorbed maximum
`bSharp`; no current-time quadratic variation or time integration enters.
-/

namespace RBM.APrimeFirstCellPrefixGoodRows

open Filter Set Real Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private theorem band_toDims_eq (d' : Dims) : (band d').toDims = d' := by
  cases d'
  rfl

/-- The three literal stored-time rows, with `tau = delta / 16`. -/
noncomputable def earlyRows (delta : Real) (N : Nat) (v u : Real) : Real :=
  APrimeFirstCellLoopCap.xRate u ^ (-(9 / 2 : Real)) +
    (N : Real) ^ (4 * delta + 2 * (delta / 16)) *
      APrimeFirstCellLoopCap.endpointScale N v ^ (-(1 / 2 : Real)) *
        APrimeFirstCellLoopCap.xRate u ^ (7 / 4 : Real) +
    (N : Real) ^ (6 * delta + 3 * (delta / 16)) *
      APrimeFirstCellLoopCap.endpointScale N v ^ (-1 : Real) *
        APrimeFirstCellLoopCap.xRate u ^ (5 : Real)

/-- The exact unabsorbed favorable prefix-gradient rate. -/
noncomputable def bSharp (delta nu : Real) (N k : Nat) : Real :=
  if hk : 0 < k then
    (16 / Real.exp 1) * (N : Real) ^ (nu / 2 - 2 * delta) *
      (Finset.range k).sup' ⟨0, Finset.mem_range.mpr hk⟩ (fun j =>
        Real.sqrt (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) *
          Real.sqrt (earlyRows delta N
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j)))
  else 0

theorem earlyRows_nonneg (delta : Real) {N : Nat} (hN : 0 < N)
    {v u : Real} (hu0 : 0 <= u) (hu1 : u < 1) (hv0 : 0 <= v) (hv1 : v < 1) :
    0 <= earlyRows delta N v u := by
  have hNreal : 0 <= (N : Real) := by positivity
  have hx : 0 <= APrimeFirstCellLoopCap.xRate u := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_nonneg (Step2.etaT_pos' (by norm_num) (by norm_num)).le
      (Step2.etaT_pos' (by norm_num) hu1).le
  have hAv : 0 <= APrimeFirstCellLoopCap.endpointScale N v := by
    exact (B.scale_pos' (by norm_num) N hv0 hv1).le
  unfold earlyRows
  exact add_nonneg
    (add_nonneg (Real.rpow_nonneg hx _)
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hNreal _) (Real.rpow_nonneg hAv _))
        (Real.rpow_nonneg hx _)))
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hNreal _) (Real.rpow_nonneg hAv _))
      (Real.rpow_nonneg hx _))

theorem cutChi_pos_of_one_lt_of_lt_two {x : Real}
    (h1 : 1 < x) (h2 : x < 2) : 0 < Cutoff.cutChi x := by
  have ht0 : 0 < x - 1 := by linarith
  have ht1 : x - 1 < 1 := by linarith
  have hm1 : max (x - 1) 0 = x - 1 := max_eq_left ht0.le
  have hm2 : max (x - 2) 0 = 0 := max_eq_right (by linarith)
  rw [Cutoff.cutChi, hm1, hm2]
  have hid :
      1 - (6 * (x - 1) ^ 5 - 15 * (x - 1) ^ 4 + 10 * (x - 1) ^ 3) =
        (1 - (x - 1)) ^ 3 * (1 + 3 * (x - 1) + 6 * (x - 1) ^ 2) := by
    ring
  rw [hid]
  have hleft : 0 < (1 - (x - 1)) ^ 3 := pow_pos (by linarith) _
  have hright : 0 < 1 + 3 * (x - 1) + 6 * (x - 1) ^ 2 := by
    nlinarith [sq_nonneg (x - 1)]
  positivity

theorem actualWeight_pos_of_transition {tauPrime delta : Real}
    {N0 p N k m : Nat} {omega : Ω d}
    (hN0 : N0 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (htrans : omega ∈ APrimeCrossJointSplit.transition d 0 60 delta
      (fun _ => 0) APrimeSmoothTransition.transitionMesh N k m) :
    0 < APrimeSupportRunning.weight delta (firstCellT tauPrime)
      N0 p N k m omega := by
  unfold APrimeSupportRunning.weight APrimeSmoothWeightActual.weight
  rw [if_pos ⟨hk, hN0⟩]
  exact pow_pos (cutChi_pos_of_one_lt_of_lt_two htrans.1 htrans.2) _

theorem quadVar_coordFun_eq_stored (N : Nat) (u : Real) (hu : u < 1) (omega : Ω d)
    (a : LoopArg (d.L N) 2) :
    Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d 0 N u a)
        ((Real.sqrt u : Complex) • Gauss.Xmat d N omega) =
      Gauss.quadVar d N
        (fun M' => MomentDuhamel.lkFun B 0 N u M' Step2.sigPM a)
        (Gauss.Hflow d N u omega) := by
  have hz : (zt 0 u).im ≠ 0 := Gauss.zt_im_ne_zero_of_lt_one (by norm_num) hu
  have hherm := Gauss.Hflow_isHermitian d N u omega
  calc
    _ = Gauss.quadVar d N
        (Gauss.loopObs d N (zt 0 u)
          (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)))
        (Gauss.Hflow d N u omega) := by
          rw [Gauss.Hflow_eq_realSmul]
          exact Gauss.quadVar_sub_const _ _ _
    _ = _ := by
      have hh := (EarlyQVRate.quadVar_lkFun_eq_quadVar_loopObs
        (B := B) hz Step2.sigPM hherm a).symm
      have hd : (band d).toDims = d := band_toDims_eq d
      cases hd
      exact hh

/-- Square-root form of one stored T447 row, in the normalization used by
the T333 prefix contraction. -/
theorem normalized_coordFun_le {delta nu : Real} {N : Nat} (hN : 0 < N)
    {omega : Ω d} {v u : Real} (hu0 : 0 <= u) (huv : u <= v)
    (hv : v <= 1 / 2) (a : LoopArg (d.L N) 2)
    (hrow : APrimeFirstCellQVEarlyRows.storedRowsAt delta nu N omega v u a) :
    (APrimeFirstCellLoopCap.xRate u ^ 4)⁻¹ *
        (Real.sqrt (Gauss.quadVar d N
          (APrimeSmoothPrefix.coordFun d 0 N u a)
          ((Real.sqrt u : Complex) • Gauss.Xmat d N omega)) /
          Step2.tT B 0 N 60 u (zdist (d.L N) (a 0 - a 1))) /
        (N : Real) ^ (2 * delta) <=
      128 * (N : Real) ^ (nu / 2 - 2 * delta) *
        Real.sqrt (earlyRows delta N v u) := by
  have hu1 : u < 1 := (huv.trans hv).trans_lt (by norm_num)
  have hv0 : 0 <= v := hu0.trans huv
  have hv1 : v < 1 := hv.trans_lt (by norm_num)
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hx : 0 < APrimeFirstCellLoopCap.xRate u := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) hu1)
  have hT : 0 < Step2.tT B 0 N 60 u (zdist (d.L N) (a 0 - a 1)) :=
    tailT_pos (by exact_mod_cast B.W_pos N) _
  have hNp : 0 < (N : Real) ^ (2 * delta) :=
    Real.rpow_pos_of_pos hNreal _
  have hE : 0 <= earlyRows delta N v u :=
    earlyRows_nonneg delta hN hu0 hu1 hv0 hv1
  let q : Real := Gauss.quadVar d N
    (APrimeSmoothPrefix.coordFun d 0 N u a)
    ((Real.sqrt u : Complex) • Gauss.Xmat d N omega)
  let T : Real := Step2.tT B 0 N 60 u (zdist (d.L N) (a 0 - a 1))
  let x : Real := APrimeFirstCellLoopCap.xRate u
  let z : Real := (x ^ 4)⁻¹ * (Real.sqrt q / T) / (N : Real) ^ (2 * delta)
  let C : Real := 128 * (N : Real) ^ (nu / 2 - 2 * delta) *
    Real.sqrt (earlyRows delta N v u)
  have hq : 0 <= q := Gauss.quadVar_nonneg _ _
  have hz0 : 0 <= z := by
    dsimp [z]
    positivity
  have hC0 : 0 <= C := by
    dsimp [C]
    positivity
  have hzsq : z ^ 2 = q /
      (T ^ 2 * x ^ 8 * ((N : Real) ^ (2 * delta)) ^ 2) := by
    dsimp [z]
    field_simp [hx.ne', hT.ne', hNp.ne']
    rw [Real.sq_sqrt hq]
  have hNsq : ((N : Real) ^ (nu / 2 - 2 * delta)) ^ 2 =
      (N : Real) ^ (nu - 4 * delta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNreal.le]
    congr 1
    ring
  have hCsq : C ^ 2 =
      16384 * (N : Real) ^ (nu - 4 * delta) *
        earlyRows delta N v u := by
    dsimp [C]
    rw [mul_pow, mul_pow, hNsq, Real.sq_sqrt hE]
    norm_num
  have hstored : q /
      (T ^ 2 * x ^ 8 * ((N : Real) ^ (2 * delta)) ^ 2) <=
      16384 * (N : Real) ^ (nu - 4 * delta) *
        earlyRows delta N v u := by
    have hr0 := hrow
    change Gauss.quadVar (band d).toDims N
          (fun M' => MomentDuhamel.lkFun (band d) 0 N u M' Step2.sigPM a)
          ((sample d).H N u omega) /
        (Step2.tT (band d) 0 N 60 u (zdist (d.L N) (a 0 - a 1)) ^ 2 *
          APrimeFirstCellLoopCap.xRate u ^ 8 *
            ((N : Real) ^ (2 * delta)) ^ 2) <=
        APrimeFirstCellQVEarlyRows.storedRowsRate delta nu N v u at hr0
    have hr : Gauss.quadVar d N
          (fun M' => MomentDuhamel.lkFun B 0 N u M' Step2.sigPM a)
          (Gauss.Hflow d N u omega) /
        (Step2.tT B 0 N 60 u (zdist (d.L N) (a 0 - a 1)) ^ 2 *
          APrimeFirstCellLoopCap.xRate u ^ 8 *
            ((N : Real) ^ (2 * delta)) ^ 2) <=
        APrimeFirstCellQVEarlyRows.storedRowsRate delta nu N v u := by
      rw [Gauss.sample_H] at hr0
      have hd : (band d).toDims = d := band_toDims_eq d
      cases hd
      exact hr0
    rw [← quadVar_coordFun_eq_stored N u hu1 omega a] at hr
    dsimp [q, T, x]
    simpa [
      APrimeFirstCellQVEarlyRows.storedRowsRate, earlyRows, etaT, mE_zero,
      Real.rpow_neg_one] using hr
  change z <= C
  nlinarith [hstored, hzsq, hCsq]

/-- T333 contracts all stored T447 rows into the exact unabsorbed rate. -/
theorem prefixGradient_le_bSharp_of_rows {tauPrime delta nu : Real}
    (hTau : 0 < tauPrime) {N k : Nat} (hN : 0 < N) (hk : 0 < k)
    (hkTop : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (omega : Ω d)
    (hrows : ∀ j < k,
      let u := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j
      let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k
      u ∈ Set.Icc (0 : Real) v ∧
      v <= firstCellT tauPrime N ∧
      APrimeFirstCellLoopCap.endpointScale N v <= B.scale 0 N u ∧
      ∀ a : LoopArg (d.L N) 2,
        APrimeFirstCellQVEarlyRows.storedRowsAt delta nu N omega v u a) :
    APrimeCrossJointSplit.prefixGradient d 0 60 delta (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
        (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
          (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega <=
      bSharp delta nu N k := by
  classical
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k
  have hvT : v <= firstCellT tauPrime N := (hrows 0 hk).2.1
  have hvHalf : v <= 1 / 2 :=
    hvT.trans (APrimeSupportRunning.firstT_bounds hTau N).2
  have hm : 1 <= m := by
    exact APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hu1 : ∀ j < k,
      cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j < 1 := by
    intro j hj
    exact ((hrows j hj).1.2.trans hvHalf).trans_lt (by norm_num)
  let Kraw : Nat -> Real := fun j =>
    (Finset.univ : Finset (LoopArg (d.L N) 2)).sup' Finset.univ_nonempty
      (fun a =>
        Real.sqrt (Gauss.quadVar d N
          (APrimeSmoothPrefix.coordFun d 0 N
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) a)
          ((Real.sqrt (cutNetPt (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N j) : Complex) •
              Gauss.Xmat d N omega)) /
        Step2.tT B 0 N 60
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j)
          (zdist (d.L N) (a 0 - a 1)))
  let G : Nat -> Real := fun j =>
    Real.sqrt (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) *
      ((Step2Moment.ratR 0 (fun _ => 0) N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ^ 4)⁻¹ *
          Kraw j)
  let R : Real := (Finset.range k).sup' ⟨0, Finset.mem_range.mpr hk⟩ (fun j =>
    Real.sqrt (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) *
      Real.sqrt (earlyRows delta N v
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j)))
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hNp : 0 < (N : Real) ^ (2 * delta) := Real.rpow_pos_of_pos hNreal _
  have hpow : (N : Real) ^ (nu / 2 - 2 * delta) *
      (N : Real) ^ (2 * delta) = (N : Real) ^ (nu / 2) := by
    rw [← Real.rpow_add hNreal]
    congr 1
    ring
  have hKraw : ∀ j < k,
      Kraw j <= 128 * (N : Real) ^ (nu / 2) *
        (APrimeFirstCellLoopCap.xRate
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ^ 4 *
          Real.sqrt (earlyRows delta N v
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j))) := by
    intro j hj
    apply Finset.sup'_le
    intro a _ha
    have hgeom := hrows j hj
    let u := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j
    have hn := normalized_coordFun_le hN hgeom.1.1 hgeom.1.2 hvHalf a
      (hgeom.2.2.2 a)
    have hx : 0 < APrimeFirstCellLoopCap.xRate u := by
      unfold APrimeFirstCellLoopCap.xRate
      exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
        (Step2.etaT_pos' (by norm_num) (hu1 j hj))
    have hmul := mul_le_mul_of_nonneg_right hn
      (mul_nonneg (pow_nonneg hx.le 4) hNp.le)
    dsimp only [u] at hx hmul ⊢
    calc
      _ = ((APrimeFirstCellLoopCap.xRate
              (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ^ 4)⁻¹ *
            (Real.sqrt (Gauss.quadVar d N
              (APrimeSmoothPrefix.coordFun d 0 N
                (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) a)
              ((Real.sqrt (cutNetPt (fun _ => 0)
                APrimeSmoothTransition.transitionMesh N j) : Complex) •
                  Gauss.Xmat d N omega)) /
              Step2.tT B 0 N 60
                (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j)
                (zdist (d.L N) (a 0 - a 1))) /
            (N : Real) ^ (2 * delta)) *
          (APrimeFirstCellLoopCap.xRate
              (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ^ 4 *
            (N : Real) ^ (2 * delta)) := by
          field_simp [hx.ne', hNp.ne']
      _ <= (128 * (N : Real) ^ (nu / 2 - 2 * delta) *
            Real.sqrt (earlyRows delta N v
              (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j))) *
          (APrimeFirstCellLoopCap.xRate
              (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ^ 4 *
            (N : Real) ^ (2 * delta)) := hmul
      _ = _ := by
        calc
          _ = 128 * ((N : Real) ^ (nu / 2 - 2 * delta) *
                (N : Real) ^ (2 * delta)) *
              (APrimeFirstCellLoopCap.xRate
                (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ^ 4 *
              Real.sqrt (earlyRows delta N v
                (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j))) := by ring
          _ = _ := by rw [hpow]
  have hG : ∀ j < k,
      G j <= 128 * (N : Real) ^ (nu / 2) *
        (Real.sqrt (cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N j) *
        Real.sqrt (earlyRows delta N v
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j))) := by
    intro j hj
    have hkraw := hKraw j hj
    dsimp only [G]
    have hxinv : 0 <= (Step2Moment.ratR 0 (fun _ => 0) N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ^ 4)⁻¹ := by
      positivity
    have hsqrt : 0 <= Real.sqrt (cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N j) := Real.sqrt_nonneg _
    calc
      _ <= Real.sqrt (cutNetPt (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N j) *
          ((Step2Moment.ratR 0 (fun _ => 0) N
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ^ 4)⁻¹ *
            (128 * (N : Real) ^ (nu / 2) *
              (APrimeFirstCellLoopCap.xRate
                (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ^ 4 *
              Real.sqrt (earlyRows delta N v
                (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkraw hxinv) hsqrt
      _ = _ := by
        have hrat : Step2Moment.ratR 0 (fun _ => 0) N
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) =
            APrimeFirstCellLoopCap.xRate
              (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) := rfl
        have hratpos : 0 < APrimeFirstCellLoopCap.xRate
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) := by
          unfold APrimeFirstCellLoopCap.xRate
          exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
            (Step2.etaT_pos' (by norm_num) (hu1 j hj))
        rw [hrat]
        field_simp [hratpos.ne']
  have hS : (Finset.range k).sup' ⟨0, Finset.mem_range.mpr hk⟩ G <=
      128 * (N : Real) ^ (nu / 2) * R := by
    apply Finset.sup'_le
    intro j hjmem
    have hj : j < k := Finset.mem_range.mp hjmem
    calc
      G j <= 128 * (N : Real) ^ (nu / 2) *
          (Real.sqrt (cutNetPt (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N j) *
          Real.sqrt (earlyRows delta N v
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j))) := hG j hj
      _ <= 128 * (N : Real) ^ (nu / 2) * R :=
        mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun i =>
            Real.sqrt (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N i) *
              Real.sqrt (earlyRows delta N v
                (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N i))) hjmem)
          (by positivity)
  have hpref := APrimeSmoothWeightActual.sqrt_quadVar_prefixMatrix_le_exp_max d
    (E := 0) (D := 60) (s := fun _ => 0)
    (mesh := APrimeSmoothTransition.transitionMesh) (N := N) (k := k) (m := m)
    (by norm_num) (by norm_num) hN hk hm hu1
    (APrimeSmoothWeightActual.canonicalM_calibration d (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N k hkTop)
    (Gauss.Xmat d N omega)
  have hpref' : Real.sqrt (Gauss.quadVar d N
      (fun X => ((APrimeSmoothWeightActual.prefixMatrix d 0 60 (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k m X : Real) : Complex))
      (Gauss.Xmat d N omega)) <=
      Real.exp 1 * (Finset.range k).sup' ⟨0, Finset.mem_range.mpr hk⟩ G := by
    simpa only [G, Kraw] using hpref
  have htheta : 0 < APrimeSmoothWeightActual.threshold delta N :=
    APrimeSmoothWeightActual.threshold_pos (δ := delta) hN
  change Real.sqrt (Gauss.quadVar d N
      (fun X => ((APrimeSmoothWeightActual.prefixMatrix d 0 60 (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k m X : Real) : Complex))
      (Gauss.Xmat d N omega)) /
      APrimeSmoothWeightActual.threshold delta N <= bSharp delta nu N k
  calc
    _ <= (Real.exp 1 * (Finset.range k).sup' ⟨0, Finset.mem_range.mpr hk⟩ G) /
        APrimeSmoothWeightActual.threshold delta N :=
      div_le_div_of_nonneg_right hpref' htheta.le
    _ <= (Real.exp 1 * (128 * (N : Real) ^ (nu / 2) * R)) /
        APrimeSmoothWeightActual.threshold delta N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS (Real.exp_pos 1).le)
        htheta.le
    _ = bSharp delta nu N k := by
      rw [bSharp, dif_pos hk]
      dsimp only [R, v, APrimeSmoothWeightActual.threshold]
      rw [Real.rpow_sub hNreal, show (N : Real) ^ (nu / 2) =
        (N : Real) ^ (nu / 2 - 2 * delta) * (N : Real) ^ (2 * delta) by
          rw [hpow]]
      field_simp [(Real.exp_pos 1).ne', hNp.ne']
      ring

/-- Every transition sample in the literal T434 event satisfies the exact
favorable prefix-gradient bound. -/
theorem eventually_prefixGradient_le_bSharp {tauPrime delta nu : Real}
    (hTau : 0 < tauPrime) (hDelta : 0 <= delta) (hNu : 0 < nu) :
    ∀ᶠ N in atTop,
      ∀ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta nu N,
      ∀ k, 1 <= k ->
        k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
          APrimeSmoothTransition.transitionMesh N ->
        omega ∈ APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) ->
        APrimeCrossJointSplit.prefixGradient d 0 60 delta (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k
            (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
              (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega <=
          bSharp delta nu N k := by
  filter_upwards [APrimeFirstCellQVEarlyRows.eventually_rows_on_stored_prefixes
      hTau hDelta hNu, eventually_ge_atTop 2] with N hrows hN2
  intro omega homega k hk1 hkTop htrans
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hm : 1 <= m := APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hw : 0 < APrimeSupportRunning.weight delta (firstCellT tauPrime)
      2 1 N k m omega :=
    actualWeight_pos_of_transition hN2 hkTop htrans
  have hrs := hrows omega homega 2 1 k m hN2 (by norm_num) hm hk1 hkTop hw
  exact prefixGradient_le_bSharp_of_rows hTau (by omega) (by omega) hkTop omega hrs

/-- Named closed predicate for the transition-sample conclusion. -/
def transitionPrefixBound (tauPrime delta nu : Real) : Prop :=
  ∀ᶠ N in atTop,
    ∀ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta nu N,
    ∀ k, 1 <= k ->
      k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ->
      omega ∈ APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
        (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
          (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) ->
      APrimeCrossJointSplit.prefixGradient d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega <=
        bSharp delta nu N k

/-- Closed T455 producer: the event remains measurable and high probability,
the exact transition bound holds, and T447's positive `k=2` resident remains
on that same event. -/
theorem exists_transitionPrefixBound_with_plateau :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 / 100 ->
      ∀ nu : Real, 0 < nu ->
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta nu N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent tauPrime delta nu) ∧
        transitionPrefixBound tauPrime delta nu ∧
        APrimeFirstCellQVEarlyRows.positiveRowsPlateau tauPrime delta nu := by
  obtain ⟨tauPrime, hTau, hall⟩ :=
    APrimeFirstCellQVEarlyRows.exists_rows_on_stored_prefixes_with_plateau
  refine ⟨tauPrime, hTau, ?_⟩
  intro delta hDelta hDelta100 nu hNu
  obtain ⟨hmeas, hprob, _hrows, hpositive⟩ :=
    hall delta hDelta hDelta100 nu hNu
  exact ⟨hmeas, hprob,
    by simpa only [transitionPrefixBound] using
      (eventually_prefixGradient_le_bSharp hTau hDelta.le hNu),
    hpositive⟩

/-- The empty prefix has zero favorable rate. -/
@[simp] theorem bSharp_zero (delta nu : Real) (N : Nat) :
    bSharp delta nu N 0 = 0 := by
  simp [bSharp]

/-- The first prefix only stores `u_0=0`, hence its favorable rate is zero. -/
@[simp] theorem bSharp_one (delta nu : Real) (N : Nat) :
    bSharp delta nu N 1 = 0 := by
  simp [bSharp, cutNetPt_zero]

/-- The actual empty-prefix gradient itself is zero. -/
theorem prefixGradient_zero (delta : Real) (N m : Nat) (hm : 1 <= m)
    (omega : Ω d) :
    APrimeCrossJointSplit.prefixGradient d 0 60 delta (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0 m omega = 0 := by
  have hmatrix : ∀ M : Matrix (d.Idx N) (d.Idx N) Complex,
      APrimeSmoothWeightActual.prefixMatrix d 0 60 (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 0 m M = 0 := by
    intro M
    simp only [APrimeSmoothWeightActual.prefixMatrix,
      Step2Bootstrap.softMax, Finset.range_zero, Finset.sum_empty]
    have hm0 : (0 : Real) < (m : Real) := by exact_mod_cast (by omega : 0 < m)
    exact Real.zero_rpow (ne_of_gt (by positivity : (0 : Real) < 1 / (2 * (m : Real))))
  unfold APrimeCrossJointSplit.prefixGradient
  simp_rw [hmatrix]
  simp [Gauss.quadVar, Gauss.coordD1]

/-- On transition samples, the `k=1` gradient is exactly zero. -/
theorem eventually_prefixGradient_one_eq_zero {tauPrime delta nu : Real}
    (hTau : 0 < tauPrime) (hDelta : 0 <= delta) (hNu : 0 < nu) :
    ∀ᶠ N in atTop,
      ∀ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta nu N,
      1 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
          APrimeSmoothTransition.transitionMesh N ->
      omega ∈ APrimeCrossJointSplit.transition d 0 60 delta (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 1
        (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
          (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) ->
      APrimeCrossJointSplit.prefixGradient d 0 60 delta (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N 1
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega = 0 := by
  filter_upwards [eventually_prefixGradient_le_bSharp hTau hDelta hNu,
    eventually_ge_atTop 1] with N hbound hN
  intro omega homega hk htrans
  have hle := hbound omega homega 1 (by norm_num) hk htrans
  rw [bSharp_one] at hle
  have hnonneg : 0 <= APrimeCrossJointSplit.prefixGradient d 0 60 delta
      (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega := by
    unfold APrimeCrossJointSplit.prefixGradient
    exact div_nonneg (Real.sqrt_nonneg _)
      (APrimeSmoothWeightActual.threshold_pos (δ := delta) (by omega)).le
  exact le_antisymm hle hnonneg

/-- T447's positive `k=2` resident supplies a genuine `j=1` stored row on
the same event.  No inhabitance of the transition set is asserted. -/
theorem positive_two_same_event_geometry {tauPrime delta nu : Real}
    (hpositive : APrimeFirstCellQVEarlyRows.positiveRowsPlateau
      tauPrime delta nu) :
    ∀ᶠ N in atTop,
      ∃ omega ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          tauPrime delta nu N,
      let u0 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0
      let u1 := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1
      let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2
      u0 = 0 ∧ 0 < u1 ∧ u1 < v ∧ v <= firstCellT tauPrime N ∧
      2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N ∧
      bSharp delta nu N 0 = 0 ∧ bSharp delta nu N 1 = 0 ∧
      (∀ a : LoopArg (d.L N) 2,
        APrimeFirstCellQVEarlyRows.storedRowsAt delta nu N omega v u0 a) ∧
      ∀ a : LoopArg (d.L N) 2,
        APrimeFirstCellQVEarlyRows.storedRowsAt delta nu N omega v u1 a := by
  filter_upwards [hpositive] with N hN
  obtain ⟨omega, homega, hu0, hu1, hu12, hv, _hw, hrow0, hrow1⟩ := hN
  have hk2 : 2 <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N := by
    unfold cutNetTop
    apply Nat.le_floor
    rw [← div_le_iff₀ (APrimeSupportRunning.mesh_pos N)]
    simpa only [cutNetPt, zero_add, Nat.cast_ofNat, sub_zero] using hv
  exact ⟨omega, homega, hu0, hu1, hu12, hv, hk2, bSharp_zero _ _ _,
    bSharp_one _ _ _, hrow0, hrow1⟩

#print axioms cutChi_pos_of_one_lt_of_lt_two
#print axioms quadVar_coordFun_eq_stored
#print axioms normalized_coordFun_le
#print axioms prefixGradient_le_bSharp_of_rows
#print axioms eventually_prefixGradient_le_bSharp
#print axioms exists_transitionPrefixBound_with_plateau
#print axioms bSharp_zero
#print axioms bSharp_one
#print axioms prefixGradient_zero
#print axioms eventually_prefixGradient_one_eq_zero
#print axioms positive_two_same_event_geometry

end RBM.APrimeFirstCellPrefixGoodRows
