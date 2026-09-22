/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeDriftTimeFamily
import RBM1D.Gauss.APrimeSmoothTransition

/-!
# The actual moving-endpoint coordinate identity in the first cell

This file identifies the normalized endpoint bootstrap quantity with the literal family of
`APrimeDriftTimeFamily.coordAt` coordinates at the moving endpoint.  It is deterministic and
does not assert a weighted moment or membership in a probabilistic event.
-/

namespace RBM.APrimeFirstCellEndpointCoord

open Real Filter Step2Bootstrap CutHypTheta

/-- The maximum of the literal endpoint coordinate family. -/
noncomputable def endpointCoordMax (d : Gauss.Dims) (N : ℕ) (v : ℝ)
    (ω : Gauss.Ω d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a : LoopArg (d.L N) 2 =>
    ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0 v v
      (Gauss.Hflow d N v ω)‖

/-- The maximum appearing in the literal definition of `J*` before endpoint normalization. -/
noncomputable def endpointRatioMax (d : Gauss.Dims) (N : ℕ) (v : ℝ)
    (ω : Gauss.Ω d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a : LoopArg (d.L N) 2 =>
    ‖Step2.lk (Gauss.sample d) 0 N v ω a‖ /
      Step2.tT (Gauss.band d) 0 N 60 v (zdist (d.L N) (a 0 - a 1))

/-- At the right endpoint, `U_(v,v)=id`, so each actual normalized coordinate is the
corresponding `(L-K)` entry divided by `T_(v,60) R_v^4`. -/
theorem norm_coordAt_endpoint (d : Gauss.Dims) (N : ℕ) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (ω : Gauss.Ω d)
    (a : LoopArg (d.L N) 2) :
    ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0 v v
        (Gauss.Hflow d N v ω)‖ =
      (‖Step2.lk (Gauss.sample d) 0 N v ω a‖ /
        Step2.tT (Gauss.band d) 0 N 60 v (zdist (d.L N) (a 0 - a 1))) /
        Step2Moment.ratR 0 (fun _ => 0) N v ^ 4 := by
  have hU := congrFun (Uker_self (d.L N) (d.three_le_L N)
    (ξ := xiOf (mSigma 0) Step2.sigPM) (t := ((v : ℝ) : ℂ)) (by
      intro i
      rw [norm_mul, norm_xiOf_mSigma (by norm_num) Step2.sigPM i, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]
      exact hv1)
    (SumZeroDyn.lkT (Gauss.sample d) 0 N v ω Step2.sigPM)) a
  have hflow := APrimeDriftTimeFamily.flowY_coordAt d 0 60 N Step2.sigPM a
    (s := 0) (v := v) (by norm_num) hv0 hv1 v ω
  rw [hU] at hflow
  change ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0 v v
      (Gauss.Hflow d N v ω)‖ = _ at hflow
  rw [hflow]
  change ‖Step2.lk (Gauss.sample d) 0 N v ω a‖ /
      (Step2.tT (Gauss.band d) 0 N 60 v (zdist (d.L N) (a 0 - a 1)) *
        Step2Moment.ratR 0 (fun _ => 0) N v ^ 4) = _
  ring

/-- The endpoint coordinate maximum is the literal `J* - 1` maximum divided by `R_v^4`. -/
theorem endpointCoordMax_eq (d : Gauss.Dims) (N : ℕ) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (ω : Gauss.Ω d) :
    endpointCoordMax d N v ω =
      endpointRatioMax d N v ω /
        Step2Moment.ratR 0 (fun _ => 0) N v ^ 4 := by
  have hR : 0 < Step2Moment.ratR 0 (fun _ => 0) N v :=
    Step2Moment.ratR_pos (by norm_num) (by norm_num) hv1
  have hR4 : 0 < Step2Moment.ratR 0 (fun _ => 0) N v ^ 4 := pow_pos hR _
  unfold endpointCoordMax endpointRatioMax
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    rw [norm_coordAt_endpoint d N hv0 hv1 ω a]
    exact (div_le_div_iff_of_pos_right hR4).2
      (Finset.le_sup' (fun b : LoopArg (d.L N) 2 =>
        ‖Step2.lk (Gauss.sample d) 0 N v ω b‖ /
          Step2.tT (Gauss.band d) 0 N 60 v (zdist (d.L N) (b 0 - b 1)))
        (Finset.mem_univ a))
  · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun a : LoopArg (d.L N) 2 =>
        ‖Step2.lk (Gauss.sample d) 0 N v ω a‖ /
          Step2.tT (Gauss.band d) 0 N 60 v (zdist (d.L N) (a 0 - a 1)))
    rw [hsup, ← norm_coordAt_endpoint d N hv0 hv1 ω a]
    exact Finset.le_sup' (fun b : LoopArg (d.L N) 2 =>
      ‖APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM b 0 v v
        (Gauss.Hflow d N v ω)‖) (Finset.mem_univ a)

/-- The literal moving-endpoint identity from (5.27)--(5.29) and (5.43). -/
theorem jSnorm_endpoint_eq (d : Gauss.Dims) (N : ℕ) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (ω : Gauss.Ω d) :
    Step2Moment.jSnorm (Gauss.sample d) 0 60 (fun _ => 0) N v ω =
      1 / Step2Moment.ratR 0 (fun _ => 0) N v ^ 4 +
        endpointCoordMax d N v ω := by
  change (endpointRatioMax d N v ω + 1) /
      Step2Moment.ratR 0 (fun _ => 0) N v ^ 4 = _
  rw [endpointCoordMax_eq d N hv0 hv1 ω]
  ring

/-- On the first-cell window the endpoint ratio satisfies `R_v ≥ 1`. -/
theorem one_le_endpoint_ratR (N : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    1 ≤ Step2Moment.ratR 0 (fun _ => 0) N v :=
  Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0) (by norm_num) hv0 hv1

/-- The normalized endpoint bootstrap quantity is bounded by one plus the largest literal
endpoint coordinate. -/
theorem jSnorm_endpoint_le (d : Gauss.Dims) (N : ℕ) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (ω : Gauss.Ω d) :
    Step2Moment.jSnorm (Gauss.sample d) 0 60 (fun _ => 0) N v ω ≤
      1 + endpointCoordMax d N v ω := by
  rw [jSnorm_endpoint_eq d N hv0 hv1 ω]
  have hR1 : 1 ≤ Step2Moment.ratR 0 (fun _ => 0) N v :=
    Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0) (by norm_num) hv0 hv1
  have hR4 : 1 ≤ Step2Moment.ratR 0 (fun _ => 0) N v ^ 4 := one_le_pow₀ hR1
  have hRpos : 0 < Step2Moment.ratR 0 (fun _ => 0) N v ^ 4 :=
    lt_of_lt_of_le (by norm_num) hR4
  have hinv : 1 / Step2Moment.ratR 0 (fun _ => 0) N v ^ 4 ≤ 1 :=
    (div_le_one hRpos).2 hR4
  linarith

/-- The exact identity and its bound at every active first-cell moving endpoint `v=u_k`. -/
theorem firstCell_endpoint_identity {τ : ℝ} (hτ : 0 < τ) (N k : ℕ)
    (hk : k ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ)
      APrimeSmoothTransition.transitionMesh N)
    (ω : Gauss.Ω Gauss.Dims.exampleGrow) :
    let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k
    1 ≤ Step2Moment.ratR 0 (fun _ => 0) N v ∧
      Step2Moment.jSnorm (Gauss.sample Gauss.Dims.exampleGrow) 0 60
          (fun _ => 0) N v ω =
        1 / Step2Moment.ratR 0 (fun _ => 0) N v ^ 4 +
          endpointCoordMax Gauss.Dims.exampleGrow N v ω ∧
      Step2Moment.jSnorm (Gauss.sample Gauss.Dims.exampleGrow) 0 60
          (fun _ => 0) N v ω ≤
        1 + endpointCoordMax Gauss.Dims.exampleGrow N v ω := by
  let d := Gauss.Dims.exampleGrow
  let mesh := APrimeSmoothTransition.transitionMesh
  let t := Gauss.firstCellT τ
  let v := cutNetPt (fun _ => 0) mesh N k
  have hmesh : 0 < mesh N := by
    dsimp [mesh, APrimeSmoothTransition.transitionMesh]
    positivity
  have ht0 : (0 : ℝ) ≤ t N := by
    have hmono := gridT_mono
      (W := ((Gauss.band d).W N : ℝ))
      (by exact_mod_cast (Gauss.band d).one_le_W N)
      hτ.le (1 / 2 : ℝ) (Nat.zero_le 1)
    change (0 : ℝ) ≤ gridT ((Gauss.band d).W N : ℝ) τ (1 / 2 : ℝ) 1
    simpa only [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hmono
  have hvIcc : v ∈ Set.Icc (0 : ℝ) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc ht0 hmesh v
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hvIcc.2.trans_lt
    ((gridT_le (W := ((Gauss.band d).W N : ℝ))
      (τ' := τ) (1 / 2 : ℝ) 1).trans_lt (by norm_num))
  exact ⟨Step2Moment.one_le_ratR (E := 0) (s := fun _ => 0)
      (by norm_num) hvIcc.1 hv1,
    jSnorm_endpoint_eq d N hvIcc.1 hv1 ω,
    jSnorm_endpoint_le d N hvIcc.1 hv1 ω⟩

/-- The empty-prefix endpoint is the same identity with `R_0=1`. -/
theorem firstCell_endpoint_zero (d : Gauss.Dims) (N : ℕ) (ω : Gauss.Ω d) :
    Step2Moment.jSnorm (Gauss.sample d) 0 60 (fun _ => 0) N 0 ω =
      1 + endpointCoordMax d N 0 ω := by
  have h := jSnorm_endpoint_eq d N (v := 0) (by norm_num) (by norm_num) ω
  have hR : Step2Moment.ratR 0 (fun _ => 0) N 0 = 1 := by
    unfold Step2Moment.ratR
    exact div_self (Step2.etaT_pos' (E := 0) (by norm_num) (by norm_num)).ne'
  rw [hR] at h
  norm_num at h ⊢
  exact h

/-- A strictly positive `k=2` endpoint on the actual zero scalar Gaussian sample. -/
theorem eventually_positive_two_endpoint_sample {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop,
      let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2
      0 < v ∧
        2 ≤ cutNetTop (fun _ => 0) (Gauss.firstCellT τ)
          APrimeSmoothTransition.transitionMesh N ∧
        Step2Moment.jSnorm (Gauss.sample Gauss.Dims.exampleGrow) 0 60
            (fun _ => 0) N v
            (APrimeSmoothTransition.scalarSample Gauss.Dims.exampleGrow 0) =
          1 / Step2Moment.ratR 0 (fun _ => 0) N v ^ 4 +
            endpointCoordMax Gauss.Dims.exampleGrow N v
              (APrimeSmoothTransition.scalarSample Gauss.Dims.exampleGrow 0) ∧
        Step2Moment.jSnorm (Gauss.sample Gauss.Dims.exampleGrow) 0 60
            (fun _ => 0) N v
            (APrimeSmoothTransition.scalarSample Gauss.Dims.exampleGrow 0) ≤
          1 + endpointCoordMax Gauss.Dims.exampleGrow N v
            (APrimeSmoothTransition.scalarSample Gauss.Dims.exampleGrow 0) := by
  filter_upwards [APrimeSmoothTransition.eventually_exampleGrow_transition
    hτ (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (1 / 100 : ℝ) < 1 / 4)]
      with N hN
  let v := cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 2
  have hmesh : 0 < APrimeSmoothTransition.transitionMesh N := inv_pos.mp hN.1
  have hv : 0 < v := by
    dsimp [v]
    simp only [cutNetPt, Nat.cast_ofNat, zero_add]
    exact div_pos (by norm_num) hmesh
  have hid := firstCell_endpoint_identity hτ N 2 hN.2.1
    (APrimeSmoothTransition.scalarSample Gauss.Dims.exampleGrow 0)
  exact ⟨hv, hN.2.1, hid.2.1, hid.2.2⟩

#print axioms norm_coordAt_endpoint
#print axioms endpointCoordMax_eq
#print axioms jSnorm_endpoint_eq
#print axioms jSnorm_endpoint_le
#print axioms firstCell_endpoint_identity
#print axioms firstCell_endpoint_zero
#print axioms eventually_positive_two_endpoint_sample

end RBM.APrimeFirstCellEndpointCoord
