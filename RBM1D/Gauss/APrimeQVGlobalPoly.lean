/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeQVGlobalPolyCore
import RBM1D.Gauss.APrimeDuhamelModel

/-! # Downstream compatibility facade for the global polynomial QV bounds -/

namespace RBM.APrimeQVGlobalPoly

/-- A deliberately coarse, dimension-explicit bound on the weighted matrix
directions appearing in the actual Gaussian quadratic variation. -/
theorem coordWt2_le (d : Gauss.Dims) (N : ℕ)
    (hM : (Fintype.card (d.Idx N) : ℝ) ≤ N) :
    APrimeDuhamelModel.coordWt2 d N ≤ 8 * (N : ℝ) ^ 2 := by
  have h := coordWeight_le d N hM
  simpa [Gauss.coordWeight, APrimeDuhamelModel.coordWt2, pow_two] using h

#print axioms RBM.APrimeQVGlobalPoly.coordWt2_le

end RBM.APrimeQVGlobalPoly
