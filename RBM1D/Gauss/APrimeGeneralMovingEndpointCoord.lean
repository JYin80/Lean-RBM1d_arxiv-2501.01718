/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellEndpointCoord
import RBM1D.Gauss.APrimeGeneralMovingDetFields

/-!
# T489: actual endpoint coordinates on a general moving window

The first-cell endpoint calculation is repeated with the bulk energy,
decay exponent, and left endpoint left free.  The calculation is
deterministic: at the moving right endpoint the evolution kernel is the
identity, and the normalization is exactly the fourth power of the scale
ratio used in `Step2Moment.jSnorm`.
-/

namespace RBM.APrimeGeneralMovingEndpointCoord

open Filter Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The maximum of the actual normalized coordinates at the moving
endpoint. -/
noncomputable def endpointCoordMax (E D : Real) (s : Nat → Real)
    (N : Nat) (v : Real) (omega : Ω d) : Real :=
  Finset.univ.sup' Finset.univ_nonempty fun a : LoopArg (d.L N) 2 =>
    ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v v
      (Hflow d N v omega)‖

/-- The maximum in the literal definition of `J*`, before division by the
moving scale ratio. -/
noncomputable def endpointRatioMax (E D : Real) (N : Nat) (v : Real)
    (omega : Ω d) : Real :=
  Finset.univ.sup' Finset.univ_nonempty fun a : LoopArg (d.L N) 2 =>
    ‖Step2.lk (sample d) E N v omega a‖ /
      Step2.tT B E N D v (zdist (d.L N) (a 0 - a 1))

/-- At `r=v`, the actual normalized coordinate is the corresponding
`(L-K)` entry divided by `T_(v,D) R_v^4`. -/
theorem norm_coordAt_endpoint {E D : Real} {s : Nat → Real} (N : Nat)
    {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v)
    (hv1 : v < 1) (omega : Ω d) (a : LoopArg (d.L N) 2) :
    ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v v
        (Hflow d N v omega)‖ =
      (‖Step2.lk (sample d) E N v omega a‖ /
        Step2.tT B E N D v (zdist (d.L N) (a 0 - a 1))) /
        Step2Moment.ratR E s N v ^ 4 := by
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hU := congrFun (Uker_self (d.L N) (d.three_le_L N)
    (ξ := xiOf (mSigma E) Step2.sigPM) (t := ((v : Real) : Complex)) (by
      intro i
      rw [norm_mul, norm_xiOf_mSigma hE.le Step2.sigPM i, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]
      exact hv1)
    (SumZeroDyn.lkT (sample d) E N v omega Step2.sigPM)) a
  have hflow := APrimeDriftTimeFamily.flowY_coordAt
    d E D N Step2.sigPM a (s := s N) (v := v) hE hsv hv1 v omega
  rw [hU] at hflow
  change ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v v
      (Hflow d N v omega)‖ = _ at hflow
  rw [hflow]
  change ‖Step2.lk (sample d) E N v omega a‖ /
      (Step2.tT B E N D v (zdist (d.L N) (a 0 - a 1)) *
        Step2Moment.ratR E s N v ^ 4) = _
  ring

/-- The endpoint coordinate maximum is the literal `J* - 1` maximum
divided by `R_v^4`. -/
theorem endpointCoordMax_eq {E D : Real} {s : Nat → Real} (N : Nat)
    {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v)
    (hv1 : v < 1) (omega : Ω d) :
    endpointCoordMax E D s N v omega =
      endpointRatioMax E D N v omega /
        Step2Moment.ratR E s N v ^ 4 := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hR : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have hR4 : 0 < Step2Moment.ratR E s N v ^ 4 := pow_pos hR _
  unfold endpointCoordMax endpointRatioMax
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    rw [norm_coordAt_endpoint N hE hs0 hsv hv1 omega a]
    exact (div_le_div_iff_of_pos_right hR4).2
      (Finset.le_sup' (fun b : LoopArg (d.L N) 2 =>
        ‖Step2.lk (sample d) E N v omega b‖ /
          Step2.tT B E N D v (zdist (d.L N) (b 0 - b 1)))
        (Finset.mem_univ a))
  · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup'
      Finset.univ_nonempty (fun a : LoopArg (d.L N) 2 =>
        ‖Step2.lk (sample d) E N v omega a‖ /
          Step2.tT B E N D v (zdist (d.L N) (a 0 - a 1)))
    rw [hsup, ← norm_coordAt_endpoint N hE hs0 hsv hv1 omega a]
    exact Finset.le_sup' (fun b : LoopArg (d.L N) 2 =>
      ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM b (s N) v v
        (Hflow d N v omega)‖) (Finset.mem_univ a)

/-- The exact moving-endpoint identity for arbitrary bulk energy, decay
exponent, and deterministic left endpoint. -/
theorem jSnorm_endpoint_eq {E D : Real} {s : Nat → Real} (N : Nat)
    {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v)
    (hv1 : v < 1) (omega : Ω d) :
    Step2Moment.jSnorm (sample d) E D s N v omega =
      1 / Step2Moment.ratR E s N v ^ 4 +
        endpointCoordMax E D s N v omega := by
  change (endpointRatioMax E D N v omega + 1) /
      Step2Moment.ratR E s N v ^ 4 = _
  rw [endpointCoordMax_eq N hE hs0 hsv hv1 omega]
  ring

/-- The endpoint scale ratio is at least one throughout the moving
window. -/
theorem one_le_endpoint_ratR {E : Real} {s : Nat → Real} {N : Nat}
    {v : Real} (hE : |E| < 2) (hsv : s N ≤ v) (hv1 : v < 1) :
    1 ≤ Step2Moment.ratR E s N v :=
  Step2Moment.one_le_ratR (s := s) hE hsv hv1

/-- The normalized bootstrap quantity is bounded by one plus the largest
actual endpoint coordinate. -/
theorem jSnorm_endpoint_le {E D : Real} {s : Nat → Real} (N : Nat)
    {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v)
    (hv1 : v < 1) (omega : Ω d) :
    Step2Moment.jSnorm (sample d) E D s N v omega ≤
      1 + endpointCoordMax E D s N v omega := by
  rw [jSnorm_endpoint_eq N hE hs0 hsv hv1 omega]
  have hR1 : 1 ≤ Step2Moment.ratR E s N v :=
    one_le_endpoint_ratR hE hsv hv1
  have hR4 : 1 ≤ Step2Moment.ratR E s N v ^ 4 := one_le_pow₀ hR1
  have hRpos : 0 < Step2Moment.ratR E s N v ^ 4 :=
    lt_of_lt_of_le (by norm_num) hR4
  have hinv : 1 / Step2Moment.ratR E s N v ^ 4 ≤ 1 :=
    (div_le_one hRpos).2 hR4
  linarith

/-- Exact endpoint fields at every active point of a deterministic moving
net.  The quantifier includes `k=0`. -/
def MovingEndpointIdentity (E D : Real) (s t mesh : Nat → Real) : Prop :=
  ∀ N k, k ≤ cutNetTop s t mesh N → ∀ omega : Ω d,
    let v := cutNetPt s mesh N k
    1 ≤ Step2Moment.ratR E s N v ∧
      Step2Moment.jSnorm (sample d) E D s N v omega =
        1 / Step2Moment.ratR E s N v ^ 4 +
          endpointCoordMax E D s N v omega ∧
      Step2Moment.jSnorm (sample d) E D s N v omega ≤
        1 + endpointCoordMax E D s N v omega

/-- General moving-window producer.  The lower bound `D>=60` required by
the surrounding A-prime package is recorded in the signature, although the
endpoint identity itself is valid for every real `D`. -/
theorem movingEndpointIdentity_on_window {E D : Real}
    {s t mesh : Nat → Real} (hE : |E| < 2) (_hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hmesh : ∀ N, 0 < mesh N) :
    MovingEndpointIdentity E D s t mesh := by
  intro N k hk omega
  let v := cutNetPt s mesh N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N) (hmesh N) v
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  exact ⟨one_le_endpoint_ratR hE hv.1 hv1,
    jSnorm_endpoint_eq N hE (hs0 N) hv.1 hv1 omega,
    jSnorm_endpoint_le N hE (hs0 N) hv.1 hv1 omega⟩

/-- The empty-prefix endpoint is exactly the left endpoint, where `R=1`.
This is the explicit `k=0` boundary of the moving-net theorem. -/
theorem endpoint_zero {E D : Real} {s t mesh : Nat → Real}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (N : Nat) (omega : Ω d) :
    let v := cutNetPt s mesh N 0
    v = s N ∧
      Step2Moment.jSnorm (sample d) E D s N v omega =
        1 + endpointCoordMax E D s N v omega := by
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have heq := jSnorm_endpoint_eq (E := E) (D := D) (s := s)
    N hE (hs0 N) le_rfl hs1 omega
  have hR : Step2Moment.ratR E s N (s N) = 1 := by
    unfold Step2Moment.ratR
    exact div_self (Step2.etaT_pos' hE hs1).ne'
  simp only [cutNetPt_zero]
  refine ⟨trivial, ?_⟩
  rw [hR] at heq
  norm_num at heq ⊢
  exact heq

/-- T483's positive-length admissible window carries the endpoint identity
at every point of its target mesh, on the same concrete model. -/
theorem positive_length_admissible_endpoint_witness :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
        (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
        (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
        (∀ᶠ N : Nat in atTop, s N < t N) ∧
        APrimeGeneralMovingDetFields.DetFieldPackage 0 60 s t ∧
        MovingEndpointIdentity 0 60 s t
          (APrimeGeneralMovingMesh.targetMesh 60) := by
  obtain ⟨tauPrime, hTau, c, hc, s, t, hs0, hst, ht1, hreg,
    hpositive, hfields⟩ :=
    APrimeGeneralMovingDetFields.positive_length_det_field_package_witness
  refine ⟨tauPrime, hTau, c, hc, s, t, hs0, hst, ht1, hreg,
    hpositive, hfields, ?_⟩
  exact movingEndpointIdentity_on_window (by norm_num) (by norm_num)
    hs0 hst ht1 (APrimeGeneralMovingMesh.targetMesh_pos 60)

end

end RBM.APrimeGeneralMovingEndpointCoord

namespace RBM.APrimeGeneralMovingEndpointCoord

#print axioms norm_coordAt_endpoint
#print axioms endpointCoordMax_eq
#print axioms jSnorm_endpoint_eq
#print axioms jSnorm_endpoint_le
#print axioms movingEndpointIdentity_on_window
#print axioms endpoint_zero
#print axioms positive_length_admissible_endpoint_witness

end RBM.APrimeGeneralMovingEndpointCoord
