/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeCrossJointSplit
import RBM1D.Gauss.APrimeQVGlobalPoly
import RBM1D.Gauss.APrimeSupportRunning

/-!
# T449: all-sample first-cell prefix-gradient envelope

This module supplies the deterministic polynomial complement bound required by
the literal `hAll` input of `APrimeCrossJointSplit.jointRate_norm_le_event`.
-/

namespace RBM.APrimeFirstCellPrefixGlobalPoly

open Filter Set Real CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow

/-- A convenient explicit constant larger than `5832 * sqrt 8`. -/
noncomputable def prefixConst : ℝ := 2 ^ (15 : ℕ)

/-- The product of `prefixConst` and the QV square-root constant `2^11`. -/
noncomputable def jointConst : ℝ := 2 ^ (26 : ℕ)

theorem prefixConst_pos : 0 < prefixConst := by
  unfold prefixConst
  positivity

theorem jointConst_pos : 0 < jointConst := by
  unfold jointConst
  positivity

private theorem coordWeight_le (N : ℕ)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N) :
    Gauss.coordWeight d N ≤ 8 * (N : ℝ) ^ 2 := by
  have h := APrimeQVGlobalPoly.coordWt2_le d N hcard
  simpa [Gauss.coordWeight, APrimeDuhamelModel.coordWt2, pow_two] using h

/-- The raw two-loop numerator has a global matrix-QV bound on the first cell.
The estimate is independent of the norm of the matrix argument. -/
theorem sqrt_quadVar_coordFun_le (N : ℕ) (hN : 1 ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N)
    {u : ℝ} (_hu0 : 0 ≤ u) (huhalf : u ≤ 1 / 2)
    (a : LoopArg (d.L N) 2) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d 0 N u a) M) ≤
      prefixConst * (N : ℝ) ^ 2 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hηeq : etaT 0 u = 1 - u := by
    norm_num [etaT, Gauss.mE_zero]
  have hηhalf : (1 / 2 : ℝ) ≤ etaT 0 u := by
    rw [hηeq]
    linarith
  have hη : 0 < etaT 0 u := lt_of_lt_of_le (by norm_num) hηhalf
  have hinv0 : 0 ≤ (etaT 0 u)⁻¹ := inv_nonneg.2 hη.le
  have hinv : (etaT 0 u)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (one_div_le hη (by norm_num)).2 hηhalf
  have hinvSq : (etaT 0 u)⁻¹ * (etaT 0 u)⁻¹ ≤ 4 := by
    nlinarith [sq_nonneg (2 - (etaT 0 u)⁻¹)]
  have hinvCube :
      (etaT 0 u)⁻¹ * (etaT 0 u)⁻¹ * (etaT 0 u)⁻¹ ≤ 8 := by
    have hm := mul_nonneg (sub_nonneg.mpr hinvSq) hinv0
    nlinarith
  have hz : (zt 0 u).im ≠ 0 := by
    rw [← etaT_eq_zt_im]
    exact hη.ne'
  have hzη : etaT 0 u ≤ |(zt 0 u).im| := by
    rw [← etaT_eq_zt_im, abs_of_pos hη]
  have hBa : (etaT 0 u)⁻¹ ≤ (54 : ℝ) := by linarith
  have hBb : (etaT 0 u)⁻¹ * (etaT 0 u)⁻¹ ≤ (54 : ℝ) := by linarith
  have hBc : 2 * ((etaT 0 u)⁻¹ * (etaT 0 u)⁻¹ * (etaT 0 u)⁻¹) ≤ (54 : ℝ) := by
    linarith
  let I : LoopIdx (ZMod (d.L N)) :=
    LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)
  have hq := Gauss.quadVar_loopObs_sub_le (d := d) (N := N)
    hz hη hzη hBa hBb hBc (I := I)
    (LoopData.idx_wf ((Step2.sigPM, a) : LoopData (d.L N) 2))
    ((Gauss.band d).Kval 0 N u I) M
  have hlen : I.a.length = 2 := by
    change I.length = 2
    exact LoopData.idx_length ((Step2.sigPM, a) : LoopData (d.L N) 2)
  dsimp [I] at hq
  change Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d 0 N u a) M ≤
    ((Fintype.card (d.Idx N) : ℝ) *
      (((LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)).a.length : ℝ) *
        (54 : ℝ) ^
          (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)).a.length) + 0) ^ 2 *
      Gauss.coordWeight d N at hq
  have hq' :
      Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d 0 N u a) M ≤
        ((Fintype.card (d.Idx N) : ℝ) * (2 * (54 : ℝ) ^ 2) + 0) ^ 2 *
          Gauss.coordWeight d N := by
    simpa only [show
      (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)).a.length = 2 from hlen,
      Nat.cast_ofNat] using hq
  have hcoef0 : 0 ≤ (Fintype.card (d.Idx N) : ℝ) * (2 * (54 : ℝ) ^ 2) + 0 := by
    positivity
  have hcoef :
      (Fintype.card (d.Idx N) : ℝ) * (2 * (54 : ℝ) ^ 2) + 0 ≤
        5832 * (N : ℝ) := by
    calc
      (Fintype.card (d.Idx N) : ℝ) * (2 * (54 : ℝ) ^ 2) + 0 =
          5832 * Fintype.card (d.Idx N) := by ring
      _ ≤ 5832 * (N : ℝ) := mul_le_mul_of_nonneg_left hcard (by norm_num)
  have hwt0 : 0 ≤ Gauss.coordWeight d N := Gauss.coordWeight_nonneg d N
  have hwt := coordWeight_le N hcard
  have hsqrtWt : √(Gauss.coordWeight d N) ≤ 3 * (N : ℝ) := by
    calc
      √(Gauss.coordWeight d N) ≤ √(8 * (N : ℝ) ^ 2) := Real.sqrt_le_sqrt hwt
      _ ≤ √(9 * (N : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (N : ℝ)])
      _ = 3 * (N : ℝ) := by
        rw [show 9 * (N : ℝ) ^ 2 = (3 * (N : ℝ)) ^ 2 by ring,
          Real.sqrt_sq (mul_nonneg (by norm_num) hN0)]
  have hsqrt' :
      √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d 0 N u a) M) ≤
        ((Fintype.card (d.Idx N) : ℝ) * (2 * (54 : ℝ) ^ 2) + 0) *
          √(Gauss.coordWeight d N) := by
    calc
      √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d 0 N u a) M) ≤
          √((((Fintype.card (d.Idx N) : ℝ) * (2 * (54 : ℝ) ^ 2) + 0) ^ 2) *
            Gauss.coordWeight d N) := Real.sqrt_le_sqrt hq'
      _ = √(((Fintype.card (d.Idx N) : ℝ) * (2 * (54 : ℝ) ^ 2) + 0) ^ 2) *
            √(Gauss.coordWeight d N) :=
          Real.sqrt_mul (sq_nonneg
            ((Fintype.card (d.Idx N) : ℝ) * (2 * (54 : ℝ) ^ 2) + 0)) _
      _ = ((Fintype.card (d.Idx N) : ℝ) * (2 * (54 : ℝ) ^ 2) + 0) *
            √(Gauss.coordWeight d N) := by rw [Real.sqrt_sq hcoef0]
  calc
    √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d 0 N u a) M)
        ≤ ((Fintype.card (d.Idx N) : ℝ) * (2 * (54 : ℝ) ^ 2) + 0) *
            √(Gauss.coordWeight d N) := hsqrt'
    _ ≤ (5832 * (N : ℝ)) * (3 * (N : ℝ)) :=
      mul_le_mul hcoef hsqrtWt (Real.sqrt_nonneg _) (by positivity)
    _ ≤ prefixConst * (N : ℝ) ^ 2 := by
      unfold prefixConst
      norm_num
      nlinarith [sq_nonneg (N : ℝ)]

/-- After division by the `D=60` tail, every raw prefix coordinate rate costs
at most `N^62`. -/
theorem rawPrefixRate_le (N : ℕ) (hN : 1 ≤ N)
    (hWN : (d.W N : ℝ) ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N)
    {u : ℝ} (hu0 : 0 ≤ u) (huhalf : u ≤ 1 / 2)
    (a : LoopArg (d.L N) 2) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d 0 N u a) M) /
        Step2.tT (Gauss.band d) 0 N 60 u (zdist (d.L N) (a 0 - a 1)) ≤
      prefixConst * (N : ℝ) ^ (62 : ℕ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hT : 0 < Step2.tT (Gauss.band d) 0 N 60 u
      (zdist (d.L N) (a 0 - a 1)) := by
    unfold Step2.tT
    exact tailT_pos hW0 _
  have hfloor : (d.W N : ℝ) ^ (-(60 : ℝ)) ≤
      Step2.tT (Gauss.band d) 0 N 60 u (zdist (d.L N) (a 0 - a 1)) := by
    unfold Step2.tT
    exact rpow_neg_le_tailT _
  have hinvFloor :
      (Step2.tT (Gauss.band d) 0 N 60 u (zdist (d.L N) (a 0 - a 1)))⁻¹ ≤
        (d.W N : ℝ) ^ (60 : ℕ) := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hW0 (-(60 : ℝ))) hfloor
    rw [Real.rpow_neg hW0.le, inv_inv] at hi
    calc
      (Step2.tT (Gauss.band d) 0 N 60 u (zdist (d.L N) (a 0 - a 1)))⁻¹ ≤
          (d.W N : ℝ) ^ (60 : ℝ) := hi
      _ = (d.W N : ℝ) ^ (60 : ℕ) := Real.rpow_natCast _ _
  have hWpow : (d.W N : ℝ) ^ (60 : ℕ) ≤ (N : ℝ) ^ (60 : ℕ) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hWN _
  have hinv :
      (Step2.tT (Gauss.band d) 0 N 60 u (zdist (d.L N) (a 0 - a 1)))⁻¹ ≤
        (N : ℝ) ^ (60 : ℕ) := hinvFloor.trans hWpow
  have hraw := sqrt_quadVar_coordFun_le N hN hcard hu0 huhalf a M
  rw [div_eq_mul_inv]
  calc
    √(Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d 0 N u a) M) *
          (Step2.tT (Gauss.band d) 0 N 60 u (zdist (d.L N) (a 0 - a 1)))⁻¹
        ≤ (prefixConst * (N : ℝ) ^ (2 : ℕ)) * (N : ℝ) ^ (60 : ℕ) :=
      mul_le_mul hraw hinv (inv_nonneg.2 hT.le) (by unfold prefixConst; positivity)
    _ = prefixConst * (N : ℝ) ^ (62 : ℕ) := by
      rw [mul_assoc, ← pow_add]

/-- The empty prefix has exactly zero gradient. -/
theorem prefixGradient_zero (δ : ℝ) (N m : ℕ) (hm : 1 ≤ m)
    (ω : Gauss.Ω d) :
    APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0 m ω = 0 := by
  have hmatrix : ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      APrimeSmoothWeightActual.prefixMatrix d 0 60 (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 0 m M = 0 := by
    intro M
    simp only [APrimeSmoothWeightActual.prefixMatrix,
      Step2Bootstrap.softMax, Finset.range_zero, Finset.sum_empty]
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    exact Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < 1 / (2 * (m : ℝ))))
  unfold APrimeCrossJointSplit.prefixGradient
  simp_rw [hmatrix]
  simp [Gauss.quadVar, Gauss.coordD1]

/-- Pointwise all-sample prefix-gradient bound at the actual moving first-cell
net point.  The hypotheses are exactly the dimension and net-range facts later
supplied eventually. -/
theorem prefixGradient_le_poly {τ' δ : ℝ} (hτ' : 0 < τ') (hδ : 0 ≤ δ)
    (N k : ℕ) (hN : 1 ≤ N) (hdim : d.W N * d.L N ≤ N)
    (hk : k ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (ω : Gauss.Ω d) :
    APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
        (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
          (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω ≤
      prefixConst * (N : ℝ) ^ (62 : ℕ) := by
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
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hmesh := APrimeSupportRunning.mesh_pos N
  have hu : ∀ j < k,
      cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j < 1 := by
    intro j hj
    have hjtop : j ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
        APrimeSmoothTransition.transitionMesh N := by omega
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc ht.1 hmesh _
      (cutNetPt_mem_netFinset hjtop)
    linarith [hjmem.2, ht.2]
  let K : ℝ := prefixConst * (N : ℝ) ^ (62 : ℕ)
  have hK0 : 0 ≤ K := by
    dsimp [K, prefixConst]
    positivity
  have hKraw : ∀ j < k, ∀ a : LoopArg (d.L N) 2,
      √(Gauss.quadVar d N
          (APrimeSmoothPrefix.coordFun d 0 N
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) a)
          ((Real.sqrt
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) : ℂ) •
              Gauss.Xmat d N ω)) /
        Step2.tT (Gauss.band d) 0 N 60
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j)
          (zdist (d.L N) (a 0 - a 1)) ≤ K := by
    intro j hj a
    have hjtop : j ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
        APrimeSmoothTransition.transitionMesh N := by omega
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc ht.1 hmesh _
      (cutNetPt_mem_netFinset hjtop)
    exact rawPrefixRate_le N hN hWN hcard hjmem.1 (hjmem.2.trans ht.2) a _
  have hK : ∀ j < k,
      Real.sqrt (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) *
        (((Step2Moment.ratR 0 (fun _ => 0) N
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j)) ^ 4)⁻¹ *
            K) ≤ K := by
    intro j hj
    have hjtop : j ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
        APrimeSmoothTransition.transitionMesh N := by omega
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc ht.1 hmesh _
      (cutNetPt_mem_netFinset hjtop)
    have hju1 : cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j < 1 :=
      hu j hj
    have hR1 : 1 ≤ Step2Moment.ratR 0 (fun _ => 0) N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) :=
      Step2Moment.one_le_ratR (s := fun _ => 0) (by norm_num) hjmem.1 hju1
    have hR4 : 1 ≤ (Step2Moment.ratR 0 (fun _ => 0) N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j)) ^ 4 :=
      one_le_pow₀ hR1
    have hRinv : ((Step2Moment.ratR 0 (fun _ => 0) N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j)) ^ 4)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hR4
    have hsqrt : Real.sqrt
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ≤ 1 :=
      Real.sqrt_le_one.2 (by linarith [hjmem.2, ht.2])
    calc
      Real.sqrt (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) *
          (((Step2Moment.ratR 0 (fun _ => 0) N
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j)) ^ 4)⁻¹ * K)
        ≤ 1 * (1 * K) := by
          gcongr
      _ = K := by ring
  have hnum := APrimeSmoothWeightActual.sqrt_quadVar_prefixMatrix_le_exp d
    (E := 0) (D := 60) (s := fun _ => 0)
    (mesh := APrimeSmoothTransition.transitionMesh) (N := N) (k := k)
    (m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
      (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
    (by norm_num) (by norm_num) hNpos
    (APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N)
    hu (Gauss.Xmat d N ω) (fun _ => K) K hK0
    (APrimeSmoothWeightActual.canonicalM_calibration d (fun _ => 0)
      (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N k hk)
    hKraw hK
  have hpow : 1 ≤ (N : ℝ) ^ (2 * δ) := Real.one_le_rpow hNr (by linarith)
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hθ : Real.exp 1 ≤ APrimeSmoothWeightActual.threshold δ N := by
    unfold APrimeSmoothWeightActual.threshold
    have hc0 : 0 ≤ 8 * (Real.exp 1) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg (Real.exp 1))
    calc
      Real.exp 1 ≤ 8 * (Real.exp 1) ^ 2 := by
        nlinarith [Real.exp_pos (1 : ℝ)]
      _ = (8 * (Real.exp 1) ^ 2) * 1 := by ring
      _ ≤ (8 * (Real.exp 1) ^ 2) * (N : ℝ) ^ (2 * δ) :=
        mul_le_mul_of_nonneg_left hpow hc0
  have hθpos := APrimeSmoothWeightActual.threshold_pos (δ := δ) hNpos
  unfold APrimeCrossJointSplit.prefixGradient
  calc
    √(Gauss.quadVar d N
        (fun M => ((APrimeSmoothWeightActual.prefixMatrix d 0 60 (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N) M : ℝ) : ℂ))
        (Gauss.Xmat d N ω)) / APrimeSmoothWeightActual.threshold δ N
      ≤ (Real.exp 1 * K) / APrimeSmoothWeightActual.threshold δ N :=
        div_le_div_of_nonneg_right hnum hθpos.le
    _ ≤ K := (div_le_iff₀ hθpos).2 <| by
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hθ hK0
    _ = prefixConst * (N : ℝ) ^ (62 : ℕ) := rfl

/-- Eventual form of the all-sample prefix-gradient estimate. -/
theorem eventually_prefixGradient_le_poly {τ' δ : ℝ} (hτ' : 0 < τ')
    (hδ : 0 ≤ δ) :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      ∀ ω : Gauss.Ω d,
        APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k
            (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
              (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω ≤
          prefixConst * (N : ℝ) ^ (62 : ℕ) := by
  filter_upwards [d.dim, eventually_ge_atTop 1] with N hdim hN
  intro k hk ω
  exact prefixGradient_le_poly hτ' hδ N k hN hdim.1 hk ω

/-- The `j=0` pullback in the actual prefix derivative is exactly zero. -/
theorem zero_pullback_rate (N : ℕ) (Kraw : ℝ) :
    Real.sqrt (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0) *
      (((Step2Moment.ratR 0 (fun _ => 0) N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0)) ^ 4)⁻¹ *
          Kraw) = 0 := by
  rw [cutNetPt_zero]
  simp

/-- T378's first-cell QV polynomial bound has square root at most `2^11 N^68`. -/
theorem sqrt_qvAt_le_poly (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (v r : ℝ) (ω : Gauss.Ω d)
    (hq : APrimeDriftTimeFamily.qvAt d 0 60 N σ a 0 v r ω ≤
      2 ^ (21 : ℕ) * (N : ℝ) ^ (136 : ℝ)) :
    √(APrimeDriftTimeFamily.qvAt d 0 60 N σ a 0 v r ω) ≤
      2 ^ (11 : ℕ) * (N : ℝ) ^ (68 : ℕ) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      APrimeDriftTimeFamily.qvAt d 0 60 N σ a 0 v r ω ≤
          2 ^ (21 : ℕ) * (N : ℝ) ^ (136 : ℝ) := hq
      _ = 2 ^ (21 : ℕ) * (N : ℝ) ^ (136 : ℕ) := by
        congr 1
        exact Real.rpow_natCast (N : ℝ) 136
      _ ≤ 2 ^ (22 : ℕ) * (N : ℝ) ^ (136 : ℕ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hN0 _)
      _ = (2 ^ (11 : ℕ) * (N : ℝ) ^ (68 : ℕ)) ^ 2 := by ring

/-- Literal all-sample `hAll` producer for T361, at every actual moving
first-cell endpoint and every current time below it. -/
theorem eventually_prefixGradient_mul_sqrt_qvAt_le_poly {τ' δ : ℝ}
    (hτ' : 0 < τ') (hδ : 0 ≤ δ) :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      ∀ (a : LoopArg (d.L N) 2)
        (r : ℝ), r ∈ Set.Icc (0 : ℝ)
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) →
      ∀ ω : Gauss.Ω d,
        APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N k
            (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
              (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω *
          √(APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r ω) ≤
          jointConst * (N : ℝ) ^ (130 : ℕ) := by
  have hqev := APrimeQVGlobalPoly.eventually_qvAt_le_poly d
    (E := 0) (D := 60) (Kη := 1) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [d.dim, eventually_ge_atTop 2, hqev] with N hdim hN hqN
  intro k hk a r hr ω
  have hN1 : 1 ≤ N := by omega
  have hpref := prefixGradient_le_poly hτ' hδ N k hN1 hdim.1 hk ω
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k < 1 := by
    linarith [hv.2, ht.2]
  have hNr2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hη : (N : ℝ) ^ (-(1 : ℝ)) ≤
      etaT 0 (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) := by
    rw [Real.rpow_neg_one]
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hNr2
    simp only [etaT, Gauss.mE_zero, Complex.I_im, mul_one]
    norm_num at hi
    linarith [hv.2, ht.2]
  have hq := hqN 0
    (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k)
    (by norm_num) hv.1 hv1 hη Step2.sigPM a r hr ω
  have hq' : APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r ω ≤
        2 ^ (21 : ℕ) * (N : ℝ) ^ (136 : ℝ) := by
    convert hq.2 using 1 <;> norm_num
  have hsqrt := sqrt_qvAt_le_poly N hN1 Step2.sigPM a
    (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r ω hq'
  have hp0 : 0 ≤ APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N k
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω := by
    unfold APrimeCrossJointSplit.prefixGradient
    exact div_nonneg (Real.sqrt_nonneg _)
      (APrimeSmoothWeightActual.threshold_pos (δ := δ) (by omega)).le
  calc
    APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
          (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
            (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω *
        √(APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
          (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k) r ω)
      ≤ (prefixConst * (N : ℝ) ^ (62 : ℕ)) *
          (2 ^ (11 : ℕ) * (N : ℝ) ^ (68 : ℕ)) :=
        mul_le_mul hpref hsqrt (Real.sqrt_nonneg _)
          (mul_nonneg (by unfold prefixConst; positivity) (pow_nonneg (by positivity) _))
    _ = jointConst * (N : ℝ) ^ (130 : ℕ) := by
      unfold prefixConst jointConst
      ring

private theorem eventually_firstT_eq_half {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, Gauss.firstCellT τ' N = 1 / 2 := by
  have ht : Tendsto (fun N : ℕ => (d.W N : ℝ) ^ (-τ'))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hτ').comp (Step2.tendsto_W (Gauss.band d))
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with N hN
  change gridT ((Gauss.band d).W N : ℝ) τ' (1 / 2) 1 = 1 / 2
  apply gridT_of_le
  rw [gridS]
  norm_num
  change (Gauss.Dims.growW N : ℝ) ^ (-τ') < 1 / 2 at hN
  linarith

/-- The first genuinely positive prefix (`k=2`, with its `j=1` entry) is an
actual first-cell resident eventually, and satisfies the same all-sample
bound. -/
theorem eventually_positive_two_prefix_le_poly {τ' δ : ℝ} (hτ' : 0 < τ')
    (hδ : 0 ≤ δ) :
    ∀ᶠ N : ℕ in atTop,
      0 < cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1 ∧
      2 ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
        APrimeSmoothTransition.transitionMesh N ∧
      ∀ ω : Gauss.Ω d,
        APrimeCrossJointSplit.prefixGradient d 0 60 δ (fun _ => 0)
            APrimeSmoothTransition.transitionMesh N 2
            (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
              (Gauss.firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω ≤
          prefixConst * (N : ℝ) ^ (62 : ℕ) := by
  filter_upwards [eventually_firstT_eq_half hτ',
    eventually_prefixGradient_le_poly hτ' hδ,
    eventually_ge_atTop 4] with N ht hprefix hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hm4 : (4 : ℝ) ≤ APrimeSmoothTransition.transitionMesh N := by
    unfold APrimeSmoothTransition.transitionMesh
    rw [max_eq_right hn1]
    have hn := pow_le_pow_right₀ hn1 (by norm_num : 1 ≤ 248)
    rw [pow_one] at hn
    exact hn4.trans hn
  have hk : 2 ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ')
      APrimeSmoothTransition.transitionMesh N := by
    unfold cutNetTop
    rw [ht]
    apply Nat.le_floor
    simp only [sub_zero]
    linarith
  have hu1 : 0 < cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 1 := by
    simp only [cutNetPt, zero_add, Nat.cast_one, one_div]
    exact inv_pos.mpr (APrimeSupportRunning.mesh_pos N)
  exact ⟨hu1, hk, hprefix 2 hk⟩

#print axioms sqrt_quadVar_coordFun_le
#print axioms rawPrefixRate_le
#print axioms prefixGradient_zero
#print axioms prefixGradient_le_poly
#print axioms eventually_prefixGradient_le_poly
#print axioms zero_pullback_rate
#print axioms sqrt_qvAt_le_poly
#print axioms eventually_prefixGradient_mul_sqrt_qvAt_le_poly
#print axioms eventually_positive_two_prefix_le_poly

end RBM.APrimeFirstCellPrefixGlobalPoly
