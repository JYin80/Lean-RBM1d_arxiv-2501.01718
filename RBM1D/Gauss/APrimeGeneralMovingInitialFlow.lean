/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingInitialBudget
import RBM1D.Gauss.APrimeDriftTimeFamily

/-!
# T610: left-endpoint flow connector for the general moving initial budget

This file identifies the normalized flow coordinate at the moving left endpoint
with T600's propagated initial observable.  It adds no estimate, event or support
hypothesis, time integral, or A-prime closure statement.
-/

namespace RBM.APrimeGeneralMovingInitialFlow

open Set Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- At every moving endpoint, the `sigPM` flow coordinate at the left time is
exactly the initial observable used by the general-moving initial budget. -/
theorem flowY_left_eq_initialEvolvedNormAt
    {E D : Real} {s t : Nat -> Real} (N : Nat)
    (v : TimeIcc s t N) (hE : |E| < 2) (ht1 : t N < 1)
    (a : LoopArg (d.L N) 2) :
    APrimeDuhamelModel.flowY d N
        (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
          (s N) v) (s N) =
      APrimeAssembly.initialEvolvedNormAt (sample d) E D s N v a := by
  funext omega
  rw [APrimeDriftTimeFamily.flowY_coordAt d E D N Step2.sigPM a
    hE v.2.1 (v.2.2.trans_lt ht1)]
  rfl

#print axioms flowY_left_eq_initialEvolvedNormAt

end
end RBM.APrimeGeneralMovingInitialFlow
