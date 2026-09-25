/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCommonSources
import RBM1D.Gauss.PermutationFourierExampleGrowJointPositive

/-! # T985: measurability of the literal centered event

At fixed `N`, the two-charge, all-time event is an arbitrary intersection of
closed norm sublevel sets.  Each test trace is continuous in the sample at its
fixed time.  The final theorem reuses the accepted T971 witness to record that
the literal event's hypotheses are satisfiable at energy zero on the nontrivial
half-time interval.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator

namespace RBM.APrimeGeneralMovingCenteredEventMeasurable

open Gauss

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- For a fixed time below one, either-charge centered block trace varies
continuously with the Gaussian sample. -/
private theorem continuous_centeredTrace_fixed (E : ℝ) (hE : |E| < 2)
    (N : ℕ) (u : ℝ) (hu : u < 1) (σ : Bool) (b : ZMod (d.L N)) :
    Continuous (fun ω : Ω d =>
      APrimeGeneralMovingTwoChargeModulus.centeredTrace E N u ω σ b) := by
  have hG : Continuous (fun ω : Ω d =>
      Gsig (Hflow d N u ω) (zt E u) σ) :=
    continuous_Gsig_Hflow d N u (zt_im_ne_zero_of_lt_one hE hu) σ
  let T : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ := fun A =>
    Matrix.trace ((A - mSigma E σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
      Eblk (d.L N) (d.W N) b)
  have hT : Continuous T := by
    dsimp [T]
    exact continuous_matrixTrace.comp
      ((continuous_id.sub continuous_const).mul continuous_const)
  have h := hT.comp hG
  convert h using 1
  ext ω
  rfl

/-- The literal fixed-`N` two-charge centered event is measurable.

The theorem assumes only the spectral-domain condition `|E| < 2` and that the
right endpoint lies below one.  For every time index in `TimeIcc`, the latter
ensures `zt E u` has nonzero imaginary part.  `Gsig` uses its conjugate for the
false charge, which also stays away from the real axis. -/
theorem measurableSet_centeredEvent {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (N : ℕ) (htN : t N < 1) (ζ : ℝ) :
    MeasurableSet (APrimeGeneralMovingCommonSources.centeredEvent E s t ζ N) := by
  have heq : APrimeGeneralMovingCommonSources.centeredEvent E s t ζ N =
      ⋂ σ : Bool, ⋂ p : TimeIcc s t N × ZMod (d.L N),
        {ω : Ω d |
          ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace E N (p.1 : ℝ)
              ω σ p.2‖ ≤
            (N : ℝ)^ζ * (2 * APrimeGeneralMovingControlExtension.qExt
              E s t N (p.1 : ℝ))} := by
    ext ω
    simp only [APrimeGeneralMovingCommonSources.centeredEvent,
      Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  apply IsClosed.measurableSet
  apply isClosed_iInter
  intro σ
  apply isClosed_iInter
  intro p
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt htN
  have htrace := continuous_centeredTrace_fixed E hE N (p.1 : ℝ) hu1 σ p.2
  exact isClosed_le htrace.norm continuous_const

/-- The accepted T971 carrier supplies actual nonzero, zero-variance-compatible
samples in the literal centered event for `E = 0` and the closed interval
`[0,1/2]`, eventually for every fixed positive loss exponent. -/
theorem eventually_nonempty_centeredEvent_E0_halfTime_nondegenerate
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∃ ω : Ω d,
        ω ∈ APrimeGeneralMovingCommonSources.centeredEvent 0
          (fun _ => 0) (fun _ => 1 / 2) ζ N ∧
        Xmat d N ω ≠ 0 ∧
        (∀ c : Coord d, (gvar d c : ℝ) = 0 → ω c = 0) := by
  filter_upwards [
    Gauss.eventually_exampleGrow_joint_goodSetFlow_centeredEvent_pos_nondegenerate hζ]
    with N hN
  rcases hN.2 with ⟨ω, _hgood, hcenter, hnonzero, hzero⟩
  exact ⟨ω, hcenter, hnonzero, hzero⟩

#print axioms measurableSet_centeredEvent
#print axioms eventually_nonempty_centeredEvent_E0_halfTime_nondegenerate

end RBM.APrimeGeneralMovingCenteredEventMeasurable
