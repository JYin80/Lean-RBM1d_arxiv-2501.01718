/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DimsExample
import RBM1D.Flow.Universality
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Fixed-time Gaussian OU marginals

This module constructs the fixed-time marginal

`exp (-t / 2) X + sqrt (1 - exp (-t)) G`

on the explicit product of the existing Gaussian band-matrix space and an independent normalized
Hermitian GUE coordinate space.  It proves the finite-coordinate joint Gaussian law and the
covariance profile `(1 - ζ) S + ζ / M` stated in (7.25), where `ζ = 1 - exp (-t)` and
`M = L N * W N = (Gauss.band d).size N`.

This is a fixed-time marginal construction only.  The common-G interpolation is not the Brownian
OU path in (2.19), since it does not have independent increments.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal ComplexConjugate

namespace RBM.Gauss

/-- The number of rows and columns at the paper's matrix size `M`.  This is definitionally
`(Gauss.band d).size N = L N * W N`; in particular it is positive even at parameter `N = 0`. -/
def ouMatrixSize (d : Dims) (N : ℕ) : ℕ := d.L N * d.W N

theorem ouMatrixSize_pos (d : Dims) (N : ℕ) : 0 < ouMatrixSize d N := by
  exact Nat.mul_pos (by have := d.three_le_L N; omega) (d.W_pos N)

/-- Real-coordinate variance of a normalized Hermitian GUE matrix.  A diagonal entry is real with
variance `1/M`; each off-diagonal real or imaginary component has variance `1/(2M)`. -/
noncomputable def gueCoordVar (d : Dims) (N : ℕ) (c : Coord d) : ℝ≥0 :=
  if c.2.1 = c.2.2.1 then
    (1 : ℝ≥0) / (ouMatrixSize d N : ℝ≥0)
  else
    (1 : ℝ≥0) / (2 * (ouMatrixSize d N : ℝ≥0))

/-- An independent normalized GUE coordinate field at size `M=L N*W N`. -/
noncomputable def gueMeasure (d : Dims) (N : ℕ) : Measure (Ω d) :=
  Measure.infinitePi fun c => gaussianReal 0 (gueCoordVar d N c)

instance gueMeasure_isProbabilityMeasure (d : Dims) (N : ℕ) :
    IsProbabilityMeasure (gueMeasure d N) := by
  unfold gueMeasure
  infer_instance

/-- The explicit common probability space is the product of the actual band Gaussian field `P d`
and an independent normalized GUE coordinate field. -/
noncomputable def ouProductMeasure (d : Dims) (N : ℕ) :
    Measure (Ω d × Ω d) := (P d).prod (gueMeasure d N)

instance ouProductMeasure_isProbabilityMeasure (d : Dims) (N : ℕ) :
    IsProbabilityMeasure (ouProductMeasure d N) := by
  unfold ouProductMeasure
  infer_instance

/-- The matrix `X` from the existing Gaussian band source on the first product coordinate. -/
noncomputable def ouBandMatrix (d : Dims) (N : ℕ) (ω : Ω d × Ω d) :
    Matrix (d.Idx N) (d.Idx N) ℂ := Xmat d N ω.1

/-- The independent normalized Hermitian GUE matrix on the second product coordinate. -/
noncomputable def ouGueMatrix (d : Dims) (N : ℕ) (ω : Ω d × Ω d) :
    Matrix (d.Idx N) (d.Idx N) ℂ := Xmat d N ω.2

/-- The OU time fraction used by (7.25). -/
noncomputable def ouZeta (t : ℝ) : ℝ := 1 - Real.exp (-t)

/-- The first fixed-time interpolation coefficient in (2.19). -/
noncomputable def ouBandCoeff (t : ℝ) : ℝ := Real.exp (-t / 2)

/-- The second fixed-time interpolation coefficient in (2.19). -/
noncomputable def ouGueCoeff (t : ℝ) : ℝ := Real.sqrt (ouZeta t)

/-- The product sample carrying the linearly interpolated independent real coordinates. -/
noncomputable def ouInterpolatedSample (d : Dims) (_N : ℕ) (t : ℝ)
    (ω : Ω d × Ω d) : Ω d :=
  fun c => ouBandCoeff t * ω.1 c + ouGueCoeff t * ω.2 c

/-- The matrix obtained from the interpolated real coordinates using the actual `Xentry` layout. -/
noncomputable def ouInterpolatedMatrix (d : Dims) (N : ℕ) (t : ℝ)
    (ω : Ω d × Ω d) : Matrix (d.Idx N) (d.Idx N) ℂ :=
  Xmat d N (ouInterpolatedSample d N t ω)

/-- The fixed-time matrix interpolation `e^(-t/2) X + sqrt(1-e^(-t)) G`. -/
noncomputable def ouMatrix (d : Dims) (N : ℕ) (t : ℝ) (ω : Ω d × Ω d) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  (ouBandCoeff t : ℂ) • ouBandMatrix d N ω +
    (ouGueCoeff t : ℂ) • ouGueMatrix d N ω

private theorem gueCoordinates_iIndep (d : Dims) (N : ℕ) :
    iIndepFun (fun c : Coord d => fun ω : Ω d => ω c) (gueMeasure d N) := by
  simpa only [gueMeasure] using
    (iIndepFun_infinitePi
      (P := fun c : Coord d => gaussianReal 0 (gueCoordVar d N c))
      (X := fun _ (x : ℝ) => x) (fun _ => measurable_id))

theorem gueCoord_hasGaussianLaw (d : Dims) (N : ℕ) (c : Coord d) :
    HasGaussianLaw (fun ω : Ω d => ω c) (gueMeasure d N) := by
  refine ⟨(measurable_pi_apply c).aemeasurable, ?_⟩
  unfold gueMeasure
  rw [Measure.infinitePi_map_eval]
  infer_instance

theorem gueCoordinateVector_jointGaussian (d : Dims) (N : ℕ)
    (I : Finset (Coord d)) :
    HasGaussianLaw (fun ω : Ω d => fun c : I => ω c.1) (gueMeasure d N) := by
  have hind : iIndepFun (fun c : I => fun ω : Ω d => ω c.1) (gueMeasure d N) :=
    (gueCoordinates_iIndep d N).precomp
      (g := fun c : I => (c : Coord d)) (by intro a b h; exact Subtype.ext h)
  exact hind.hasGaussianLaw (fun c => gueCoord_hasGaussianLaw d N c.1)

theorem ouInterpolatedSample_eq_band_at_zero (d : Dims) (N : ℕ) (ω : Ω d × Ω d) :
    ouInterpolatedSample d N 0 ω = ω.1 := by
  funext c
  simp [ouInterpolatedSample, ouBandCoeff, ouGueCoeff, ouZeta]

theorem ouMatrix_eq_interpolatedMatrix (d : Dims) (N : ℕ) (t : ℝ)
    (ω : Ω d × Ω d) :
    ouMatrix d N t ω = ouInterpolatedMatrix d N t ω := by
  ext i j
  simp only [ouMatrix, ouBandMatrix, ouGueMatrix, ouInterpolatedMatrix,
    Matrix.add_apply, Matrix.smul_apply, Xmat_apply, smul_eq_mul]
  unfold Xentry
  split_ifs <;> simp only [ouInterpolatedSample, Complex.ofReal_add, Complex.ofReal_mul] <;>
    ring

theorem ouMatrix_isHermitian (d : Dims) (N : ℕ) (t : ℝ) (ω : Ω d × Ω d) :
    (ouMatrix d N t ω).IsHermitian := by
  rw [ouMatrix_eq_interpolatedMatrix]
  exact Xmat_isHermitian d N (ouInterpolatedSample d N t ω)

theorem ouMatrix_start (d : Dims) (N : ℕ) (ω : Ω d × Ω d) :
    ouMatrix d N 0 ω = ouBandMatrix d N ω := by
  rw [ouMatrix_eq_interpolatedMatrix, ouInterpolatedMatrix,
    ouInterpolatedSample_eq_band_at_zero]
  rfl

theorem gueCoordVar_diag (d : Dims) (N : ℕ) (i : d.Idx N) (b : Bool) :
    (gueCoordVar d N ⟨N, i, i, b⟩ : ℝ) = 1 / (ouMatrixSize d N : ℝ) := by
  simp [gueCoordVar, ouMatrixSize]

theorem gueCoordVar_offDiag (d : Dims) (N : ℕ) (i j : d.Idx N) (b : Bool)
    (hij : i ≠ j) :
    (gueCoordVar d N ⟨N, i, j, b⟩ : ℝ) = 1 / (2 * (ouMatrixSize d N : ℝ)) := by
  simp [gueCoordVar, ouMatrixSize, hij]

/-- The squared first coefficient is `1-ζ`, with `ζ=1-exp(-t)`. -/
theorem ouBandCoeff_sq (t : ℝ) : (ouBandCoeff t) ^ 2 = 1 - ouZeta t := by
  rw [ouBandCoeff, ouZeta]
  calc
    Real.exp (-t / 2) ^ 2 = Real.exp ((-t / 2) + (-t / 2)) := by
      rw [pow_two, ← Real.exp_add]
    _ = Real.exp (-t) := by congr 1; ring
    _ = 1 - (1 - Real.exp (-t)) := by ring

/-- The squared GUE coefficient is exactly `ζ`; nonnegativity of the time is what makes the
square-root interpolation real. -/
theorem ouGueCoeff_sq (t : ℝ) (ht : 0 ≤ t) :
    (ouGueCoeff t) ^ 2 = ouZeta t := by
  have he : Real.exp (-t) ≤ 1 :=
    (Real.exp_le_one_iff).2 (by linarith)
  unfold ouGueCoeff
  exact Real.sq_sqrt (sub_nonneg.mpr he)

end RBM.Gauss
