/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelBddT

/-!
# Clean drift-time definitions for the Gaussian A-prime family

This core owns the endpoint scale, normalized coordinate, and its quadratic-variation rate
without importing the downstream Step 2 hierarchy.
-/

namespace RBM.APrimeDriftTimeFamily

open Set

/-- The endpoint normalization with `Step2.tT` expanded definitionally. -/
noncomputable def driftScale (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (a : LoopArg (d.L N) 2) (s v : ℝ) : ℝ :=
  tailT (d.W N) ((Gauss.band d).ell N v) (etaT E v) D
      (zdist (d.L N) (a 0 - a 1)) *
    (etaT E s / etaT E v) ^ 4

theorem driftScale_pos (d : Gauss.Dims) {E D s v : ℝ} (hE : |E| < 2)
    (hsv : s ≤ v) (hv1 : v < 1) (N : ℕ) (a : LoopArg (d.L N) 2) :
    0 < driftScale d E D N a s v := by
  have hs1 : s < 1 := hsv.trans_lt hv1
  have hηs : 0 < etaT E s := by
    rw [show etaT E s = (1 - s) * (mE E).im from rfl]
    exact mul_pos (by linarith) (mE_im_pos hE)
  have hηv : 0 < etaT E v := by
    rw [show etaT E v = (1 - v) * (mE E).im from rfl]
    exact mul_pos (by linarith) (mE_im_pos hE)
  have hR : 0 < etaT E s / etaT E v := div_pos hηs hηv
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hT : 0 < tailT (d.W N) ((Gauss.band d).ell N v) (etaT E v) D
      (zdist (d.L N) (a 0 - a 1)) := tailT_pos hW _
  exact mul_pos hT (pow_pos hR _)

/-- The endpoint-normalized evolved coordinate at an arbitrary matrix. -/
noncomputable def coordAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v r : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  Gauss.ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
    (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r M /
      ((driftScale d E D N a s v : ℝ) : ℂ)

/-- The model-pinned quadratic-variation rate for the normalized coordinate. -/
noncomputable def qvAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v r : ℝ)
    (ω : Gauss.Ω d) : ℝ :=
  Gauss.quadVar d N (coordAt d E D N σ a s v r) (Gauss.Hflow d N r ω)

#print axioms RBM.APrimeDriftTimeFamily.driftScale
#print axioms RBM.APrimeDriftTimeFamily.driftScale_pos
#print axioms RBM.APrimeDriftTimeFamily.coordAt
#print axioms RBM.APrimeDriftTimeFamily.qvAt

end RBM.APrimeDriftTimeFamily
