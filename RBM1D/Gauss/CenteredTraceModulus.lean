/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.TwoChargeOneLoop
import RBM1D.Hierarchy.Step2Near47
import RBM1D.Gauss.Step6Hyp
import Mathlib.Analysis.Calculus.Deriv.Abs
import RBM1D.Hierarchy.DriftDef
import RBM1D.Gauss.MomentDuhamelGauss
import RBM1D.Gauss.TestFunHerm
import RBM1D.Gauss.WeightedSumSqrt
import RBM1D.Gauss.EarlyQVRate
import RBM1D.Flow.FirstCell
import RBM1D.Gauss.EarlyQVRateEv
import RBM1D.Gauss.Lemma514Moment
import RBM1D.Gauss.QVEndpoint
import RBM1D.Gauss.Lemma514Holder
import RBM1D.Hierarchy.DriftBound
import RBM1D.Gauss.Step1Hyp

/-!
# Generic actual centered-trace time modulus

For every `Dims`: the matrix-norm event `‖Xmat d N ω‖ ≤ N` (`normGood`), which holds with
high probability (`highProb_normGood`), and the centered block trace of the Gaussian resolvent
flow for either charge (`centeredTrace`); the minus-charge trace is the complex conjugate of the
plus-charge trace (`centeredTrace_false_eq_conj_true`).
-/

namespace RBM.CenteredTraceModulus

open Filter MeasureTheory Set Gauss

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The actual Gaussian norm event at dimension `d` and size `N`. -/
def normGood (d : Dims) (N : ℕ) : Set (Ω d) :=
  {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)}

/-- The actual centered block trace for either resolvent charge. -/
noncomputable def centeredTrace (d : Dims) (E : ℝ) (N : ℕ) (u : ℝ)
    (ω : Ω d) (σ : Bool) (b : ZMod (d.L N)) : ℂ :=
  Matrix.trace ((Gsig (Hflow d N u ω) (zt E u) σ
    - mSigma E σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
      Eblk (d.L N) (d.W N) b)

theorem highProb_normGood (d : Dims) :
    HighProb (P d) (fun N => normGood d N) := by
  change HighProb (P d)
    (fun N => {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)})
  exact Gauss.highProb_norm_Xmat_le d

/-- The minus-charge centered trace is the conjugate of the plus-charge trace,
pointwise in the same dimension, time, block, and Gaussian sample. -/
theorem centeredTrace_false_eq_conj_true (d : Dims) (E : ℝ) (N : ℕ)
    (u : ℝ) (ω : Ω d) (b : ZMod (d.L N)) :
    centeredTrace d E N u ω false b =
      (starRingEnd ℂ) (centeredTrace d E N u ω true b) := by
  rw [centeredTrace, centeredTrace, mSigma_false, mSigma_true]
  exact TwoChargeOneLoop.centered_block_trace_false_eq_conj_true
    (d.L N) (d.W N) (Hflow d N u ω) (Hflow_isHermitian d N u ω)
      (zt E u) (mE E) b

end
end RBM.CenteredTraceModulus
