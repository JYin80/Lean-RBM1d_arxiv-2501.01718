/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingEndpointCoord
import RBM1D.Gauss.APrimeInit

/-!
# T493: pointwise endpoint maximum-to-family bridge

At every active endpoint of a general moving window, T489 bounds the actual
normalized `jSnorm` by one plus the maximum of the actual endpoint
coordinates.  The finite maximum-to-family inequality from T280b then gives
the literal coordinate-family sum, pointwise in every Gaussian sample.
-/

namespace RBM.APrimeGeneralMovingEndpointFamily

open Filter Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The literal maximum-to-family bound at one endpoint.  The moment order
assumption matches the A-prime consumer; the finite-family inequality is in
fact valid at order zero as well. -/
theorem cutTrunc_jSnorm_pow_le_endpoint_family
    {E D : Real} {s : Nat → Real} (N : Nat) {v theta : Real} {p : Nat}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v)
    (hv1 : v < 1) (_hp : 1 ≤ p) (omega : Ω d) :
    |MomentDuhamelCut.cutTrunc theta
        (Step2Moment.jSnorm (sample d) E D s N v omega)| ^ (2 * p) ≤
      2 ^ (2 * p - 1) *
        (1 + ∑ a : LoopArg (d.L N) 2,
          ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
            (s N) v v (Hflow d N v omega)‖ ^ (2 * p)) := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hJ0 : 0 ≤ Step2Moment.jSnorm (sample d) E D s N v omega :=
    Step2Moment.jSnorm_nonneg (sample d) (E := E) (D := D) (s := s)
      hE hs1 hv1 omega
  have hJ :=
    APrimeGeneralMovingEndpointCoord.jSnorm_endpoint_le
      (E := E) (D := D) (s := s) N hE hs0 hsv hv1 omega
  have hJ' : Step2Moment.jSnorm (sample d) E D s N v omega ≤
      1 + (Finset.univ : Finset (LoopArg (d.L N) 2)).sup'
        Finset.univ_nonempty (fun a =>
          |‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
            (s N) v v (Hflow d N v omega)‖|) := by
    simpa [d, APrimeGeneralMovingEndpointCoord.endpointCoordMax,
      abs_norm] using hJ
  have hfamily := APrimeInit.cutTrunc_pow_le_family
    (Finset.univ : Finset (LoopArg (d.L N) 2)) Finset.univ_nonempty
    (fun a =>
      ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
        (s N) v v (Hflow d N v omega)‖)
    (J := Step2Moment.jSnorm (sample d) E D s N v omega)
    (θ := theta) hJ0 hJ' p
  simpa only [Finset.sum_filter, Finset.mem_univ, ite_true, abs_norm] using hfamily

/-- Pointwise family bounds at all active endpoints of one deterministic
moving net.  The quantifier includes `k=0`. -/
def MovingEndpointFamilyBound
    (E D : Real) (s t mesh : Nat → Real) : Prop :=
  ∀ N k, k ≤ cutNetTop s t mesh N → ∀ theta : Real,
    ∀ p : Nat, 1 ≤ p → ∀ omega : Ω d,
      let v := cutNetPt s mesh N k
      |MomentDuhamelCut.cutTrunc theta
          (Step2Moment.jSnorm (sample d) E D s N v omega)| ^ (2 * p) ≤
        2 ^ (2 * p - 1) *
          (1 + ∑ a : LoopArg (d.L N) 2,
            ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
              (s N) v v (Hflow d N v omega)‖ ^ (2 * p))

/-- Uniform producer over every active endpoint of a general moving
window. -/
theorem movingEndpointFamilyBound_on_window
    {E D : Real} {s t mesh : Nat → Real}
    (hE : |E| < 2) (_hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hmesh : ∀ N, 0 < mesh N) :
    MovingEndpointFamilyBound E D s t mesh := by
  intro N k hk theta p hp omega
  let v := cutNetPt s mesh N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N) (hmesh N) v
      (cutNetPt_mem_netFinset hk)
  exact cutTrunc_jSnorm_pow_le_endpoint_family N hE (hs0 N) hv.1
    (hv.2.trans_lt (ht1 N)) hp omega

/-- Explicit empty-prefix boundary.  Here the active endpoint is
`v=cutNetPt ... 0=s_N`. -/
theorem endpointFamily_zero
    {E D : Real} {s t mesh : Nat → Real}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (N : Nat) (theta : Real) (p : Nat) (hp : 1 ≤ p) (omega : Ω d) :
    let v := cutNetPt s mesh N 0
    v = s N ∧
      |MomentDuhamelCut.cutTrunc theta
          (Step2Moment.jSnorm (sample d) E D s N v omega)| ^ (2 * p) ≤
        2 ^ (2 * p - 1) *
          (1 + ∑ a : LoopArg (d.L N) 2,
            ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
              (s N) v v (Hflow d N v omega)‖ ^ (2 * p)) := by
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hbound := cutTrunc_jSnorm_pow_le_endpoint_family
    (E := E) (D := D) (s := s) (theta := theta)
    N hE (hs0 N) le_rfl hs1 hp omega
  simp only [cutNetPt_zero]
  exact ⟨trivial, hbound⟩

/-- T489's same positive-length admissible window also carries the family
bound at every endpoint of the target mesh. -/
theorem positive_length_admissible_family_witness :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
        (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
        (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
        (∀ᶠ N : Nat in atTop, s N < t N) ∧
        APrimeGeneralMovingDetFields.DetFieldPackage 0 60 s t ∧
        APrimeGeneralMovingEndpointCoord.MovingEndpointIdentity 0 60 s t
          (APrimeGeneralMovingMesh.targetMesh 60) ∧
        MovingEndpointFamilyBound 0 60 s t
          (APrimeGeneralMovingMesh.targetMesh 60) := by
  obtain ⟨tauPrime, hTau, c, hc, s, t, hs0, hst, ht1, hreg,
    hpositive, hfields, hidentity⟩ :=
    APrimeGeneralMovingEndpointCoord.positive_length_admissible_endpoint_witness
  refine ⟨tauPrime, hTau, c, hc, s, t, hs0, hst, ht1, hreg,
    hpositive, hfields, hidentity, ?_⟩
  exact movingEndpointFamilyBound_on_window (by norm_num) (by norm_num)
    hs0 hst ht1 (APrimeGeneralMovingMesh.targetMesh_pos 60)

end

end RBM.APrimeGeneralMovingEndpointFamily

namespace RBM.APrimeGeneralMovingEndpointFamily

#print axioms cutTrunc_jSnorm_pow_le_endpoint_family
#print axioms movingEndpointFamilyBound_on_window
#print axioms endpointFamily_zero
#print axioms positive_length_admissible_family_witness

end RBM.APrimeGeneralMovingEndpointFamily
