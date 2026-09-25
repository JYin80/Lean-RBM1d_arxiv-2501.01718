/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossQVRoot

/-!
# T1325: public interface for the complete free-loss absorbed root

Expose T1301's complete absorbed-root estimate with a public positive
constant, in the exact profile shape consumed by T1315.  The joint witness
also places this quantitative premise on the positive-length exampleGrow
Gaussian window supplied by T1301.
-/

namespace RBM.APrimeFreeLossRootInterface

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open Lean Elab Term

private def t1301RootConstName : Name :=
  Name.str
    (Name.str
      (Name.str
        (Name.num
          (Name.str
            (Name.str
              (Name.str (Name.str Name.anonymous "_private") "RBM1D") "Gauss")
            "APrimeFreeLossQVRoot")
          0)
        "RBM")
    "APrimeFreeLossQVRoot")
    "rootConst"

-- Re-export the exact private source constant.  The report records the source
-- SHA because this generated name is intentionally tied to the T1301 artifact.
elab "t1301RootConst" : term => do
  let env ← getEnv
  let some _ := env.find? t1301RootConstName
    | throwError "T1301's private rootConst was not found; check its source SHA"
  return mkConst t1301RootConstName

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d

/-- Public alias for T1301's exact private root constant. -/
noncomputable def rootInterfaceConst : Real := t1301RootConst

theorem rootInterfaceConst_pos : 0 < rootInterfaceConst := by
  unfold rootInterfaceConst
  change 0 < Real.sqrt 6 * (1 + 256 * Real.exp 3) +
    Real.sqrt (1200 *
      (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2))^3)
  positivity

/-- T1315's complete `hAbsorbed` premise, with its constant existentially
fixed before the eventual index.  The profile includes every residual,
leakage, spatial indicator, and absorbed far term. -/
theorem exists_positive_C_A_eventually_absorbed_root_le
    {E D c lambda : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hlambda : 0 < lambda)
    (hsmall : lambda ≤ min (1 / 10000 : Real) (c / 10000)) :
    ∃ C_A : Real, 0 < C_A ∧
      ∀ᶠ N : Nat in atTop,
        ∀ k : Nat,
          k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
          ∀ a : LoopArg (d.L N) 2,
            let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
            ∀ u ∈ Icc (s N) v,
              APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s
                (lambda / 1000) N u v D
                (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s
                  (lambda / 1000) (2 * lambda) N u) a ≤
              C_A * (N : Real)^(2 * (lambda / 1000)) *
                (etaT E (s N))^(-(1 / 2 : Real)) *
                Step2Moment.ratR E s N v^(-(2 : Real)) := by
  refine ⟨rootInterfaceConst, rootInterfaceConst_pos, ?_⟩
  have hroot := APrimeFreeLossQVRoot.eventually_absorbed_root_le
    hE hD hs0 hst ht1 hc hreg hlambda hsmall
  filter_upwards [hroot] with N hrootN
  intro k hk a v u hu
  simpa [v, APrimeGeneralMovingQVNormBudget.endpoint, rootInterfaceConst] using
      hrootN k hk u hu a

/-- The exact public absorbed-root interface is jointly satisfiable with the
structural hypotheses on one positive-length `Dims.exampleGrow` Gaussian
window.  The common-event sample and the quantitative root estimate use the
same `E = 0`, `D = 60`, `s`, `t`, and `lambda`. -/
theorem free_loss_root_interface_joint_witness :
    ∃ c : Real, 0 < c ∧
    ∃ s t : Nat → Real,
      (∀ N, s N = 0) ∧
      (∀ N, 0 ≤ s N) ∧
      (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∃ lambda : Real,
        0 < lambda ∧
        lambda ≤ min (1/10000 : Real) (c/10000) ∧
        0 < lambda/1000 ∧
        0 < 2*lambda ∧
        lambda + lambda = 2*lambda ∧
        lambda/1000 ≤ (2*lambda)/16 ∧
        2*lambda ≤ c/20 ∧
        lambda/1000 + 2*(lambda+lambda) + (2 : Real)/15 < 1 ∧
        ∃ C_A : Real, 0 < C_A ∧
          ∀ᶠ N : Nat in atTop,
            (∀ k : Nat,
              k ≤ cutNetTop s t
                (APrimeGeneralMovingMesh.targetMesh (60 : Real)) N →
              ∀ a : LoopArg (d.L N) 2,
                let v := cutNetPt s
                  (APrimeGeneralMovingMesh.targetMesh (60 : Real)) N k
                ∀ u ∈ Icc (s N) v,
                  APrimeGeneralMovingQVAbsorption.absorbedRootProfile 0 s
                    (lambda / 1000) N u v 60
                    (APrimeGeneralMovingQVProfile.generalMovingBlockCap 0 s
                      (lambda / 1000) (2 * lambda) N u) a ≤
                  C_A * (N : Real)^(2 * (lambda / 1000)) *
                    (etaT 0 (s N))^(-(1 / 2 : Real)) *
                    Step2Moment.ratR 0 s N v^(-(2 : Real))) ∧
            s N < t N ∧
            ∃ omega,
              omega ∈ APrimeGeneralMovingCommonSources.commonEvent
                0 60 s t (lambda/1000) (lambda/1000) (lambda/1000) N ∧
              1 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N ∧
              APrimeWeight.widenedW
                (APrimeWeight.canonicalR s t
                  (APrimeGeneralMovingMesh.targetMesh 60)) 1
                (APrimeGeneralMovingDetFields.J 0 60 s) s t
                (APrimeGeneralMovingMesh.targetMesh 60) (2*lambda) 1 N 1 omega = 1 := by
  obtain ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
      lambda, hlambda, hsmall, hh, hcap, hcapEq, hcapTau, hcapC,
      hroom, hcommon⟩ :=
    APrimeFreeLossQVRoot.free_loss_hypotheses_witness
  have hroot := exists_positive_C_A_eventually_absorbed_root_le
    (E := 0) (D := 60) (c := c) (lambda := lambda)
    (s := s) (t := t)
    (by norm_num : |(0 : Real)| < 2)
    (by norm_num : (60 : Real) ≤ 60)
    hs0 hst ht1 hc hreg hlambda hsmall
  obtain ⟨C_A, hCA, hrootEv⟩ := hroot
  have hjoint := hrootEv.and hcommon
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    lambda, hlambda, hsmall, hh, hcap, hcapEq, hcapTau, hcapC,
    hroom, C_A, hCA, ?_⟩
  filter_upwards [hjoint] with N ⟨hrootN, hcommonN⟩
  exact ⟨hrootN, hcommonN⟩

#print axioms rootInterfaceConst
#print axioms rootInterfaceConst_pos
#print axioms exists_positive_C_A_eventually_absorbed_root_le
#print axioms free_loss_root_interface_joint_witness

end
end RBM.APrimeFreeLossRootInterface
