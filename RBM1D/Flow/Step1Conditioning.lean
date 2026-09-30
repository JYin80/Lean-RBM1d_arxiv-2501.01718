/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GUEUnitaryInvariance
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Stationarity of `H_∞` and conditioning on the initial matrix

For test functions `RBM.IsTestFun O` (Theorem 2.6, Step 1):

* `law_gue_interp`: the linear combination `e^{-t/2} G' + √ζ G` of two independent copies `G', G`
  of the standard GUE field, with `ζ = 1 - e^{-t}`, has exactly the law of one GUE copy, for every
  `0 ≤ t`.
* `ouPairing_eq_integral`: conditioning the fixed-time OU pairing on the band matrix `H`, the
  inner pairing is the DBM pairing `corrPairing gueMeasure (dbmMatrix (e^{-t/2} λ(H) - E₀) ζ)`.
* `gueMatPairing_eq_integral`: the same identity for `H_∞`, through `law_gue_interp`.

The Fubini step in `ouPairing_eq_integral` and `gueMatPairing_eq_integral` needs integrability of
the correlation-sum integrand on the product measure; a test function is bounded and continuous,
which provides it. For merely continuous `O` the identity can fail (Bochner junk value on the joint
side).

## Route

`(ouBandCoeff t)² + (ouGueCoeff t)² = 1` for every `t` (`ouBandCoeff_sq`, `ouGueCoeff_sq`), so each
real coordinate of the combined field `ouInterpolatedSample d N t` has the *same* Gaussian variance
`gueCoordVar d N c` as a single GUE copy (`RBM.Gauss.gueCoord_hasGaussianLaw`). Independence
across different coordinates `c₁ ≠ c₂` of the combined field follows from vanishing covariance
(`HasGaussianLaw.iIndepFun_of_covariance_eq_zero`): the four covariance terms in the bilinear
expansion vanish either because they come from different, independent coordinates of the *same*
GUE copy, or because they come from different copies entirely (`covariance_fst_snd_prod`).
Independence on every finite subfamily (`iIndepFun_iff_finset`) then upgrades, together with the
matching one-dimensional marginals, to full law equality on `Ω d = Coord d → ℝ`
(`iIndepFun_iff_hasLaw_Pi_infinitePi`), i.e. the interpolated field has the law of `gueMeasure d
N`. Composing with the deterministic matrix map `Xmat d N` (using
`ouMatrix_eq_interpolatedMatrix`'s pointwise identity, valid for any sample regardless of the
underlying measure) gives `law_gue_interp`.
-/

open MeasureTheory Filter Matrix Topology ProbabilityTheory
open scoped ComplexConjugate NNReal ENNReal

namespace RBM.Gauss

variable (d : Dims)

/-! ### Coordinates of `gueMeasure d N` are mutually independent, each with a known law -/

/-- Reproved here (file-local): the coordinates of `gueMeasure d N` are mutually
independent, exactly as `gueCoordinates_iIndep` in `OUMarginalGaussian.lean` (which is `private`
there and hence not reusable). -/
private theorem Step1Conditioning.gueCoordinates_iIndep (d : Dims) (N : ℕ) :
    iIndepFun (fun c : Coord d => fun ω : Ω d => ω c) (gueMeasure d N) := by
  simpa only [gueMeasure] using
    (iIndepFun_infinitePi (P := fun c : Coord d => gaussianReal 0 (gueCoordVar d N c))
      (X := fun _ (x : ℝ) => x) (fun _ => measurable_id))

/-- Reproved here (file-local): the one-dimensional marginal law of a coordinate of `gueMeasure d
N`. -/
private theorem Step1Conditioning.gueCoord_hasLaw (d : Dims) (N : ℕ) (c : Coord d) :
    HasLaw (fun ω : Ω d => ω c) (gaussianReal 0 (gueCoordVar d N c)) (gueMeasure d N) := by
  refine ⟨(measurable_pi_apply c).aemeasurable, ?_⟩
  unfold gueMeasure
  exact Measure.infinitePi_map_eval _ c

private theorem Step1Conditioning.gueCoord_fst_hasLaw (d : Dims) (N : ℕ) (c : Coord d) :
    HasLaw (fun p : Ω d × Ω d => p.1 c) (gaussianReal 0 (gueCoordVar d N c))
      ((gueMeasure d N).prod (gueMeasure d N)) :=
  (Step1Conditioning.gueCoord_hasLaw d N c).fun_comp
    (measurePreserving_fst (μ := gueMeasure d N) (ν := gueMeasure d N)).hasLaw

private theorem Step1Conditioning.gueCoord_snd_hasLaw (d : Dims) (N : ℕ) (c : Coord d) :
    HasLaw (fun p : Ω d × Ω d => p.2 c) (gaussianReal 0 (gueCoordVar d N c))
      ((gueMeasure d N).prod (gueMeasure d N)) :=
  (Step1Conditioning.gueCoord_hasLaw d N c).fun_comp
    (measurePreserving_snd (μ := gueMeasure d N) (ν := gueMeasure d N)).hasLaw

private theorem Step1Conditioning.memLp_gueCoord (d : Dims) (N : ℕ) (c : Coord d) :
    MemLp (fun ω : Ω d => ω c) 2 (gueMeasure d N) :=
  (Step1Conditioning.gueCoord_hasLaw d N c).memLp IsGaussian.memLp_two_id

/-! ### Independence of the two coordinates of the same copy, pulled back to the product -/

/-- Pairwise independence of two *different* coordinates of the first product factor. -/
private theorem Step1Conditioning.indepFun_fst_of_ne (d : Dims) (N : ℕ) {c1 c2 : Coord d}
    (h : c1 ≠ c2) :
    IndepFun (fun p : Ω d × Ω d => p.1 c1) (fun p : Ω d × Ω d => p.1 c2)
      ((gueMeasure d N).prod (gueMeasure d N)) := by
  have hf : Measurable (fun ω : Ω d => ω c1) := measurable_pi_apply c1
  have hg : Measurable (fun ω : Ω d => ω c2) := measurable_pi_apply c2
  have hbase := (Step1Conditioning.gueCoordinates_iIndep d N).indepFun h
  have e1 : (fun p : Ω d × Ω d => p.1 c1) = (fun ω : Ω d => ω c1) ∘ Prod.fst := rfl
  have e2 : (fun p : Ω d × Ω d => p.1 c2) = (fun ω : Ω d => ω c2) ∘ Prod.fst := rfl
  rw [e1, e2, indepFun_iff_map_prod_eq_prod_map_map (hf.comp measurable_fst).aemeasurable
    (hg.comp measurable_fst).aemeasurable]
  simp only [Function.comp_apply]
  have hpair : (fun p : Ω d × Ω d => ((fun ω : Ω d => ω c1) p.1, (fun ω : Ω d => ω c2) p.1)) =
      (fun ω : Ω d => (ω c1, ω c2)) ∘ Prod.fst := rfl
  rw [hpair, ← Measure.map_map (hf.prodMk hg) measurable_fst,
    (measurePreserving_fst (μ := gueMeasure d N) (ν := gueMeasure d N)).map_eq,
    (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mp hbase,
    ← Measure.map_map hf measurable_fst, ← Measure.map_map hg measurable_fst,
    (measurePreserving_fst (μ := gueMeasure d N) (ν := gueMeasure d N)).map_eq]

/-- Pairwise independence of two *different* coordinates of the second product factor. -/
private theorem Step1Conditioning.indepFun_snd_of_ne (d : Dims) (N : ℕ) {c1 c2 : Coord d}
    (h : c1 ≠ c2) :
    IndepFun (fun p : Ω d × Ω d => p.2 c1) (fun p : Ω d × Ω d => p.2 c2)
      ((gueMeasure d N).prod (gueMeasure d N)) := by
  have hf : Measurable (fun ω : Ω d => ω c1) := measurable_pi_apply c1
  have hg : Measurable (fun ω : Ω d => ω c2) := measurable_pi_apply c2
  have hbase := (Step1Conditioning.gueCoordinates_iIndep d N).indepFun h
  have e1 : (fun p : Ω d × Ω d => p.2 c1) = (fun ω : Ω d => ω c1) ∘ Prod.snd := rfl
  have e2 : (fun p : Ω d × Ω d => p.2 c2) = (fun ω : Ω d => ω c2) ∘ Prod.snd := rfl
  rw [e1, e2, indepFun_iff_map_prod_eq_prod_map_map (hf.comp measurable_snd).aemeasurable
    (hg.comp measurable_snd).aemeasurable]
  simp only [Function.comp_apply]
  have hpair : (fun p : Ω d × Ω d => ((fun ω : Ω d => ω c1) p.2, (fun ω : Ω d => ω c2) p.2)) =
      (fun ω : Ω d => (ω c1, ω c2)) ∘ Prod.snd := rfl
  rw [hpair, ← Measure.map_map (hf.prodMk hg) measurable_snd,
    (measurePreserving_snd (μ := gueMeasure d N) (ν := gueMeasure d N)).map_eq,
    (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mp hbase,
    ← Measure.map_map hf measurable_snd, ← Measure.map_map hg measurable_snd,
    (measurePreserving_snd (μ := gueMeasure d N) (ν := gueMeasure d N)).map_eq]

/-! ### Each interpolated coordinate has the law of a single GUE copy -/

/-- **`ouBandCoeff`/`ouGueCoeff` sum of squares to `1`.** -/
private theorem Step1Conditioning.coeff_sq_sum (t : ℝ) (ht : 0 ≤ t) :
    (ouBandCoeff t) ^ 2 + (ouGueCoeff t) ^ 2 = 1 := by
  rw [ouBandCoeff_sq, ouGueCoeff_sq t ht]; ring

private theorem Step1Conditioning.interp_coord_hasLaw (d : Dims) (N : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (c : Coord d) :
    HasLaw (fun p : Ω d × Ω d => ouInterpolatedSample d N t p c) (gaussianReal 0 (gueCoordVar d N c))
      ((gueMeasure d N).prod (gueMeasure d N)) := by
  have hIndep : (fun p : Ω d × Ω d => p.1 c) ⟂ᵢ[(gueMeasure d N).prod (gueMeasure d N)]
      (fun p => p.2 c) := indepFun_prod (measurable_pi_apply c) (measurable_pi_apply c)
  have hScaled :
      (fun p : Ω d × Ω d => ouBandCoeff t * p.1 c) ⟂ᵢ[(gueMeasure d N).prod (gueMeasure d N)]
        (fun p => ouGueCoeff t * p.2 c) := hIndep.comp (by fun_prop) (by fun_prop)
  have hX := gaussianReal_const_mul (Step1Conditioning.gueCoord_fst_hasLaw d N c) (ouBandCoeff t)
  have hY := gaussianReal_const_mul (Step1Conditioning.gueCoord_snd_hasLaw d N c) (ouGueCoeff t)
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hScaled hX hY
  have hmeas : Measurable (fun p : Ω d × Ω d => ouInterpolatedSample d N t p c) := by
    dsimp [ouInterpolatedSample]; fun_prop
  refine ⟨hmeas.aemeasurable, ?_⟩
  have hvar :
      (⟨(ouBandCoeff t) ^ 2, sq_nonneg _⟩ * gueCoordVar d N c +
        ⟨(ouGueCoeff t) ^ 2, sq_nonneg _⟩ * gueCoordVar d N c) = gueCoordVar d N c := by
    apply Subtype.ext
    show (ouBandCoeff t) ^ 2 * (gueCoordVar d N c : ℝ) +
        (ouGueCoeff t) ^ 2 * (gueCoordVar d N c : ℝ) = (gueCoordVar d N c : ℝ)
    rw [← add_mul, Step1Conditioning.coeff_sq_sum t ht, one_mul]
  have hdist : gaussianReal (ouBandCoeff t * 0 + ouGueCoeff t * 0)
      (⟨(ouBandCoeff t) ^ 2, sq_nonneg _⟩ * gueCoordVar d N c +
        ⟨(ouGueCoeff t) ^ 2, sq_nonneg _⟩ * gueCoordVar d N c) =
      gaussianReal 0 (gueCoordVar d N c) := by
    rw [show ouBandCoeff t * 0 + ouGueCoeff t * 0 = 0 by ring, hvar]
  calc
    ((gueMeasure d N).prod (gueMeasure d N)).map (fun p => ouInterpolatedSample d N t p c) =
        ((gueMeasure d N).prod (gueMeasure d N)).map
          ((fun p : Ω d × Ω d => ouBandCoeff t * p.1 c) + fun p => ouGueCoeff t * p.2 c) := by
      congr 1
    _ = gaussianReal 0 (gueCoordVar d N c) := hsum.trans hdist

/-! ### Vanishing covariance between different interpolated coordinates -/

private theorem Step1Conditioning.interp_covariance_eq_zero (d : Dims) (N : ℕ) (t : ℝ)
    {c1 c2 : Coord d} (h : c1 ≠ c2) :
    cov[fun p : Ω d × Ω d => ouInterpolatedSample d N t p c1,
        fun p : Ω d × Ω d => ouInterpolatedSample d N t p c2;
        (gueMeasure d N).prod (gueMeasure d N)] = 0 := by
  have hL2c : ∀ c : Coord d, MemLp (fun ω : Ω d => ω c) 2 (gueMeasure d N) :=
    Step1Conditioning.memLp_gueCoord d N
  have hL2fst : ∀ c : Coord d, MemLp (fun p : Ω d × Ω d => p.1 c) 2
      ((gueMeasure d N).prod (gueMeasure d N)) := fun c => (hL2c c).comp_fst (gueMeasure d N)
  have hL2snd : ∀ c : Coord d, MemLp (fun p : Ω d × Ω d => p.2 c) 2
      ((gueMeasure d N).prod (gueMeasure d N)) := fun c => (hL2c c).comp_snd (gueMeasure d N)
  have hXX : cov[fun p : Ω d × Ω d => p.1 c1, fun p : Ω d × Ω d => p.1 c2;
      (gueMeasure d N).prod (gueMeasure d N)] = 0 :=
    (Step1Conditioning.indepFun_fst_of_ne d N h).covariance_eq_zero (hL2fst c1) (hL2fst c2)
  have hYY : cov[fun p : Ω d × Ω d => p.2 c1, fun p : Ω d × Ω d => p.2 c2;
      (gueMeasure d N).prod (gueMeasure d N)] = 0 :=
    (Step1Conditioning.indepFun_snd_of_ne d N h).covariance_eq_zero (hL2snd c1) (hL2snd c2)
  have hXY : cov[fun p : Ω d × Ω d => p.1 c1, fun p : Ω d × Ω d => p.2 c2;
      (gueMeasure d N).prod (gueMeasure d N)] = 0 := covariance_fst_snd_prod (hL2c c1) (hL2c c2)
  have hYX : cov[fun p : Ω d × Ω d => p.2 c1, fun p : Ω d × Ω d => p.1 c2;
      (gueMeasure d N).prod (gueMeasure d N)] = 0 := by
    rw [covariance_comm]; exact covariance_fst_snd_prod (hL2c c2) (hL2c c1)
  have hL2X2Y2 : MemLp (fun p : Ω d × Ω d => ouBandCoeff t * p.1 c2 + ouGueCoeff t * p.2 c2) 2
      ((gueMeasure d N).prod (gueMeasure d N)) :=
    ((hL2fst c2).const_mul (ouBandCoeff t)).add ((hL2snd c2).const_mul (ouGueCoeff t))
  have hstep1 : cov[fun p : Ω d × Ω d => ouInterpolatedSample d N t p c1,
      fun p : Ω d × Ω d => ouInterpolatedSample d N t p c2;
      (gueMeasure d N).prod (gueMeasure d N)] =
        cov[fun p : Ω d × Ω d => ouBandCoeff t * p.1 c1,
            fun p : Ω d × Ω d => ouBandCoeff t * p.1 c2 + ouGueCoeff t * p.2 c2;
            (gueMeasure d N).prod (gueMeasure d N)] +
        cov[fun p : Ω d × Ω d => ouGueCoeff t * p.2 c1,
            fun p : Ω d × Ω d => ouBandCoeff t * p.1 c2 + ouGueCoeff t * p.2 c2;
            (gueMeasure d N).prod (gueMeasure d N)] := by
    show cov[(fun p : Ω d × Ω d => ouBandCoeff t * p.1 c1) + fun p => ouGueCoeff t * p.2 c1,
        (fun p : Ω d × Ω d => ouBandCoeff t * p.1 c2) + fun p => ouGueCoeff t * p.2 c2;
        (gueMeasure d N).prod (gueMeasure d N)] = _
    exact covariance_add_left ((hL2fst c1).const_mul (ouBandCoeff t))
      ((hL2snd c1).const_mul (ouGueCoeff t)) hL2X2Y2
  have hstep2a : cov[fun p : Ω d × Ω d => ouBandCoeff t * p.1 c1,
      fun p : Ω d × Ω d => ouBandCoeff t * p.1 c2 + ouGueCoeff t * p.2 c2;
      (gueMeasure d N).prod (gueMeasure d N)] = 0 := by
    rw [covariance_const_mul_left]
    show ouBandCoeff t * cov[fun p : Ω d × Ω d => p.1 c1,
        (fun p : Ω d × Ω d => ouBandCoeff t * p.1 c2) + fun p => ouGueCoeff t * p.2 c2;
        (gueMeasure d N).prod (gueMeasure d N)] = 0
    rw [covariance_add_right (hL2fst c1) ((hL2fst c2).const_mul (ouBandCoeff t))
        ((hL2snd c2).const_mul (ouGueCoeff t)),
      covariance_const_mul_right, covariance_const_mul_right, hXX, hXY]
    ring
  have hstep2b : cov[fun p : Ω d × Ω d => ouGueCoeff t * p.2 c1,
      fun p : Ω d × Ω d => ouBandCoeff t * p.1 c2 + ouGueCoeff t * p.2 c2;
      (gueMeasure d N).prod (gueMeasure d N)] = 0 := by
    rw [covariance_const_mul_left]
    show ouGueCoeff t * cov[fun p : Ω d × Ω d => p.2 c1,
        (fun p : Ω d × Ω d => ouBandCoeff t * p.1 c2) + fun p => ouGueCoeff t * p.2 c2;
        (gueMeasure d N).prod (gueMeasure d N)] = 0
    rw [covariance_add_right (hL2snd c1) ((hL2fst c2).const_mul (ouBandCoeff t))
        ((hL2snd c2).const_mul (ouGueCoeff t)),
      covariance_const_mul_right, covariance_const_mul_right, hYX, hYY]
    ring
  rw [hstep1, hstep2a, hstep2b, add_zero]

/-! ### Full independence of the interpolated coordinate family, and its law -/

private theorem Step1Conditioning.interp_iIndepFun_finset (d : Dims) (N : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (s : Finset (Coord d)) :
    iIndepFun (fun c : s => fun p : Ω d × Ω d => ouInterpolatedSample d N t p c.1)
      ((gueMeasure d N).prod (gueMeasure d N)) := by
  let Xv : Ω d → s → ℝ := fun ω c => ω c.1
  have hX : HasGaussianLaw Xv (gueMeasure d N) := by
    simpa [Xv] using gueCoordinateVector_jointGaussian d N s
  have hX1 : HasGaussianLaw (fun p : Ω d × Ω d => Xv p.1) ((gueMeasure d N).prod (gueMeasure d N)) := by
    refine ⟨by fun_prop, ?_⟩
    change IsGaussian (Measure.map (Xv ∘ Prod.fst) ((gueMeasure d N).prod (gueMeasure d N)))
    rw [← Measure.map_map (show Measurable Xv from by fun_prop) measurable_fst,
      (measurePreserving_fst (μ := gueMeasure d N) (ν := gueMeasure d N)).map_eq]
    exact hX.isGaussian_map
  have hX2 : HasGaussianLaw (fun p : Ω d × Ω d => Xv p.2) ((gueMeasure d N).prod (gueMeasure d N)) := by
    refine ⟨by fun_prop, ?_⟩
    change IsGaussian (Measure.map (Xv ∘ Prod.snd) ((gueMeasure d N).prod (gueMeasure d N)))
    rw [← Measure.map_map (show Measurable Xv from by fun_prop) measurable_snd,
      (measurePreserving_snd (μ := gueMeasure d N) (ν := gueMeasure d N)).map_eq]
    exact hX.isGaussian_map
  have hIndep : (fun p : Ω d × Ω d => Xv p.1) ⟂ᵢ[(gueMeasure d N).prod (gueMeasure d N)]
      (fun p => Xv p.2) := indepFun_prod (by fun_prop) (by fun_prop)
  let T : ((s → ℝ) × (s → ℝ)) →L[ℝ] (s → ℝ) :=
    (ouBandCoeff t) • ContinuousLinearMap.fst ℝ (s → ℝ) (s → ℝ) +
      (ouGueCoeff t) • ContinuousLinearMap.snd ℝ (s → ℝ) (s → ℝ)
  have hPair : HasGaussianLaw (fun p => (Xv p.1, Xv p.2)) ((gueMeasure d N).prod (gueMeasure d N)) :=
    hIndep.hasGaussianLaw hX1 hX2
  have hOut := hPair.map_fun T
  have hEq : (fun p : Ω d × Ω d => fun c : s => ouInterpolatedSample d N t p c.1) =
      T ∘ fun p : Ω d × Ω d => (Xv p.1, Xv p.2) := by
    funext p c
    simp [T, ouInterpolatedSample, Xv]
  have hHasGaussianLaw : HasGaussianLaw
      (fun p : Ω d × Ω d => fun c : s => ouInterpolatedSample d N t p c.1)
      ((gueMeasure d N).prod (gueMeasure d N)) := by
    rw [hEq]; exact hOut
  refine HasGaussianLaw.iIndepFun_of_covariance_eq_zero hHasGaussianLaw fun c1 c2 hc12 => ?_
  exact Step1Conditioning.interp_covariance_eq_zero d N t (fun h => hc12 (Subtype.ext h))

private theorem Step1Conditioning.interp_iIndepFun (d : Dims) (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    iIndepFun (fun c : Coord d => fun p : Ω d × Ω d => ouInterpolatedSample d N t p c)
      ((gueMeasure d N).prod (gueMeasure d N)) :=
  iIndepFun_iff_finset.mpr fun s => Step1Conditioning.interp_iIndepFun_finset d N t ht s

/-- The interpolated field `ouInterpolatedSample d N t` has exactly the law of `gueMeasure d N`. -/
private theorem Step1Conditioning.interp_hasLaw (d : Dims) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((gueMeasure d N).prod (gueMeasure d N)).map (ouInterpolatedSample d N t) = gueMeasure d N := by
  have hmeasAll : Measurable
      (fun p : Ω d × Ω d => fun c : Coord d => ouInterpolatedSample d N t p c) := by
    apply measurable_pi_iff.mpr; intro c
    dsimp [ouInterpolatedSample]; fun_prop
  have hHasLaw := (iIndepFun_iff_hasLaw_Pi_infinitePi
      (X := fun c : Coord d => fun p : Ω d × Ω d => ouInterpolatedSample d N t p c)
      (μ := fun c : Coord d => gaussianReal 0 (gueCoordVar d N c))
      (fun c => Step1Conditioning.interp_coord_hasLaw d N ht c)
      hmeasAll.aemeasurable).mp (Step1Conditioning.interp_iIndepFun d N t ht)
  rw [show (fun p : Ω d × Ω d => fun c => ouInterpolatedSample d N t p c) =
      ouInterpolatedSample d N t from rfl] at hHasLaw
  rw [hHasLaw.map_eq]
  rfl

/-! ### `law_gue_interp` -/

/-- **Stationarity** of the GUE law `H_∞` under the OU interpolation. -/
theorem law_gue_interp (d : Dims) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((gueMeasure d N).prod (gueMeasure d N)).map
        (fun p : Ω d × Ω d =>
          (ouBandCoeff t : ℂ) • Xmat d N p.1 + (ouGueCoeff t : ℂ) • Xmat d N p.2) =
      (gueMeasure d N).map (Xmat d N) := by
  have hmeasInterp : Measurable (ouInterpolatedSample d N t) := by
    apply measurable_pi_iff.mpr; intro c
    dsimp [ouInterpolatedSample]; fun_prop
  have hfun : (fun p : Ω d × Ω d =>
      (ouBandCoeff t : ℂ) • Xmat d N p.1 + (ouGueCoeff t : ℂ) • Xmat d N p.2) =
      Xmat d N ∘ ouInterpolatedSample d N t := by
    funext p
    show (ouBandCoeff t : ℂ) • Xmat d N p.1 + (ouGueCoeff t : ℂ) • Xmat d N p.2 =
      Xmat d N (ouInterpolatedSample d N t p)
    rw [show Xmat d N (ouInterpolatedSample d N t p) = ouMatrix d N t p from
      (ouMatrix_eq_interpolatedMatrix d N t p).symm]
    rfl
  rw [hfun, ← Measure.map_map (measurable_Xmat d N) hmeasInterp,
    Step1Conditioning.interp_hasLaw d N ht]

/-! ### Conditioning on the first matrix (targets 1-2) -/

/-- Hermitianity of the interpolated matrix `a X(x) + b X(y)` (definitionally `ouMatrix` at
`(x, y)`). -/
private theorem Step1Conditioning.interp_isHermitian (d : Dims) (N : ℕ) (t : ℝ) (x y : Ω d) :
    ((ouBandCoeff t : ℂ) • Xmat d N x + (ouGueCoeff t : ℂ) • Xmat d N y).IsHermitian :=
  ouMatrix_isHermitian d N t (x, y)

private theorem Step1Conditioning.measurable_interp (d : Dims) (N : ℕ) (t : ℝ) :
    Measurable (fun p : Ω d × Ω d =>
      (ouBandCoeff t : ℂ) • Xmat d N p.1 + (ouGueCoeff t : ℂ) • Xmat d N p.2) := by
  have hs : Measurable (ouInterpolatedSample d N t) := by
    apply measurable_pi_iff.mpr; intro c
    simp only [ouInterpolatedSample]; fun_prop
  have heq : (fun p : Ω d × Ω d =>
      (ouBandCoeff t : ℂ) • Xmat d N p.1 + (ouGueCoeff t : ℂ) • Xmat d N p.2) =
      Xmat d N ∘ ouInterpolatedSample d N t :=
    funext fun p => ouMatrix_eq_interpolatedMatrix d N t p
  rw [heq]
  exact (measurable_Xmat d N).comp hs

/-- Conjugation by a fixed unitary matrix does not change `corrPairing` (equal characteristic
polynomials, hence equal eigenvalues). File-local restatement. -/
private theorem Step1Conditioning.corrPairing_conj {n : Type*} [Fintype n] [DecidableEq n]
    {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) {H H' : Ω' → Matrix n n ℂ}
    (hH : ∀ ω, (H ω).IsHermitian) (hH' : ∀ ω, (H' ω).IsHermitian)
    (hconj : ∀ ω, H' ω = Uᴴ * H ω * U) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ) :
    RBM.corrPairing μ H' hH' k O E = RBM.corrPairing μ H hH k O E := by
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hchar : ∀ ω, (H' ω).charpoly = (H ω).charpoly := by
    intro ω
    rw [hconj ω, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold RBM.corrPairing
  have heig : ∀ ω, (hH' ω).eigenvalues = (hH ω).eigenvalues := fun ω =>
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff (hH' ω) (hH ω)).mpr (hchar ω)
  simp_rw [heig]

/-- The inner (conditional) identity at a fixed first sample `x`. -/
private theorem Step1Conditioning.inner_eq (d : Dims) (N : ℕ) (t : ℝ) (k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : Continuous O) (E₀ : ℝ) (x : Ω d) :
    RBM.corrPairing (gueMeasure d N)
        (fun y => (ouBandCoeff t : ℂ) • Xmat d N x + (ouGueCoeff t : ℂ) • Xmat d N y)
        (fun y => Step1Conditioning.interp_isHermitian d N t x y) k O E₀ =
      RBM.corrPairing (gueMeasure d N)
        (dbmMatrix d N (fun i => ouBandCoeff t * (Xmat_isHermitian d N x).eigenvalues i - E₀)
          (ouZeta t)) (dbmMatrix_isHermitian _ _ _ _) k O 0 := by
  set hX := Xmat_isHermitian d N x with hX_def
  set v : d.Idx N → ℝ := fun i => ouBandCoeff t * hX.eigenvalues i - E₀ with hv_def
  set V : Matrix (d.Idx N) (d.Idx N) ℂ :=
    (hX.eigenvectorUnitary : Matrix (d.Idx N) (d.Idx N) ℂ) with hV_def
  have hV : V ∈ Matrix.unitaryGroup (d.Idx N) ℂ := hX.eigenvectorUnitary.2
  have h2 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  set D : Matrix (d.Idx N) (d.Idx N) ℂ := Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ))
    with hD_def
  have hXeq : Xmat d N x = V * D * Vᴴ := by
    have hspec := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at hspec
    have hDeq : Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) =
        Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) := by
      congr 1
    rw [hDeq] at hspec
    exact hspec
  have hVXV : Vᴴ * Xmat d N x * V = D := by
    rw [hXeq, show Vᴴ * (V * D * Vᴴ) * V = (Vᴴ * V) * D * (Vᴴ * V) by
      simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]
  have hVV : Vᴴ * ((E₀ : ℂ) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * V =
      (E₀ : ℂ) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h2]
  -- the Hermitian family after the energy shift
  have hs : ∀ y, ((ouBandCoeff t : ℂ) • Xmat d N x + (ouGueCoeff t : ℂ) • Xmat d N y -
      (E₀ : ℂ) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).IsHermitian := fun y =>
    (Step1Conditioning.interp_isHermitian d N t x y).sub
      (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))
  -- the conjugated family
  let K : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ := fun y =>
    Matrix.diagonal (fun i => (v i : ℂ)) + (Real.sqrt (ouZeta t) : ℂ) • (Vᴴ * Xmat d N y * V)
  have hK : ∀ y, K y = Vᴴ * ((ouBandCoeff t : ℂ) • Xmat d N x + (ouGueCoeff t : ℂ) • Xmat d N y -
      (E₀ : ℂ) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * V := by
    intro y
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hVXV, hVV]
    have hdiag : Matrix.diagonal (fun i => (v i : ℂ)) =
        (ouBandCoeff t : ℂ) • D - (E₀ : ℂ) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) := by
      ext i j
      rw [hD_def]
      by_cases hij : i = j
      · subst hij; simp [hv_def]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    change Matrix.diagonal (fun i => (v i : ℂ)) +
      (Real.sqrt (ouZeta t) : ℂ) • (Vᴴ * Xmat d N y * V) = _
    rw [hdiag]
    simp only [ouGueCoeff]
    abel
  have hKh : ∀ y, (K y).IsHermitian := by
    intro y
    rw [hK y]
    change (Vᴴ * _ * V)ᴴ = Vᴴ * _ * V
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (hs y).eq, Matrix.mul_assoc]
  refine (corrPairing_shift (gueMeasure d N)
    (fun y => Step1Conditioning.interp_isHermitian d N t x y) E₀ k O).symm.trans ?_
  rw [← Step1Conditioning.corrPairing_conj (gueMeasure d N) hV hs hKh hK k O 0]
  -- law of `K` is the law of `dbmMatrix v ζ` (`gueMeasure_map_conj`)
  have hcont : Continuous (fun Y : Matrix (d.Idx N) (d.Idx N) ℂ =>
      Matrix.diagonal (fun i => (v i : ℂ)) + (Real.sqrt (ouZeta t) : ℂ) • Y) := by fun_prop
  have hmeasV : Measurable (fun y => Vᴴ * Xmat d N y * V) := by
    have hc : Continuous (fun Y : Matrix (d.Idx N) (d.Idx N) ℂ => Vᴴ * Y * V) := by fun_prop
    exact hc.measurable.comp (measurable_Xmat d N)
  have hfun1 : K = (fun Y => Matrix.diagonal (fun i => (v i : ℂ)) +
      (Real.sqrt (ouZeta t) : ℂ) • Y) ∘ (fun y => Vᴴ * Xmat d N y * V) := rfl
  have hfun2 : dbmMatrix d N v (ouZeta t) = (fun Y => Matrix.diagonal (fun i => (v i : ℂ)) +
      (Real.sqrt (ouZeta t) : ℂ) • Y) ∘ (Xmat d N) := by
    funext y
    rfl
  have hlaw : (gueMeasure d N).map K = (gueMeasure d N).map (dbmMatrix d N v (ouZeta t)) := by
    rw [hfun1, hfun2, ← Measure.map_map hcont.measurable hmeasV,
      ← Measure.map_map hcont.measurable (measurable_Xmat d N), gueMeasure_map_conj d N hV]
  exact corrPairing_congr_law (gueMeasure d N) (gueMeasure d N) (hcont.measurable.comp hmeasV)
    (hcont.measurable.comp (measurable_Xmat d N)) hKh
    (dbmMatrix_isHermitian d N v (ouZeta t)) (by rw [← hfun1, ← hfun2]; exact hlaw) k hO 0

/-- The conditioning identity on `μ ⊗ gueMeasure`, for any probability measure `μ` on the first
factor: Fubini (licensed by the boundedness of a test function) plus the inner identity. -/
private theorem Step1Conditioning.conditioning (d : Dims) (N : ℕ) (μ : Measure (Ω d))
    [IsProbabilityMeasure μ] (t : ℝ) (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : RBM.IsTestFun O)
    (E₀ : ℝ) :
    RBM.corrPairing (μ.prod (gueMeasure d N))
        (fun p : Ω d × Ω d =>
          (ouBandCoeff t : ℂ) • Xmat d N p.1 + (ouGueCoeff t : ℂ) • Xmat d N p.2)
        (fun p => Step1Conditioning.interp_isHermitian d N t p.1 p.2) k O E₀ =
      ∫ ω, RBM.corrPairing (gueMeasure d N)
        (dbmMatrix d N (fun i => ouBandCoeff t * (Xmat_isHermitian d N ω).eigenvalues i - E₀)
          (ouZeta t)) (dbmMatrix_isHermitian _ _ _ _) k O 0 ∂μ := by
  have hcont : Continuous O := hO.1.continuous
  obtain ⟨B, hB⟩ := hO.2.exists_bound_of_continuous hcont
  set C : ℝ := (Fintype.card (d.Idx N) : ℝ) ^ k *
    (((Fintype.card (d.Idx N) - k).factorial : ℝ) / (Fintype.card (d.Idx N)).factorial) with hC
  let F : Ω d × Ω d → ℝ := fun p => ∑ f : Fin k ↪ d.Idx N,
    O (fun j => (Fintype.card (d.Idx N) : ℝ) *
      ((Step1Conditioning.interp_isHermitian d N t p.1 p.2).eigenvalues (f j) - E₀))
  have hmeasF : Measurable F :=
    measurable_corrSum (Step1Conditioning.measurable_interp d N t)
      (fun p => Step1Conditioning.interp_isHermitian d N t p.1 p.2) k hcont
      (Fintype.card (d.Idx N) : ℝ) E₀
  have hint : Integrable F (μ.prod (gueMeasure d N)) := by
    refine Integrable.of_bound hmeasF.aestronglyMeasurable
      ((Fintype.card (Fin k ↪ d.Idx N) : ℝ) * B) (Eventually.of_forall fun p => ?_)
    calc ‖F p‖ ≤ ∑ f : Fin k ↪ d.Idx N, ‖O (fun j => (Fintype.card (d.Idx N) : ℝ) *
          ((Step1Conditioning.interp_isHermitian d N t p.1 p.2).eigenvalues (f j) - E₀))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _f : Fin k ↪ d.Idx N, B := Finset.sum_le_sum fun f _ => hB _
      _ = (Fintype.card (Fin k ↪ d.Idx N) : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc RBM.corrPairing (μ.prod (gueMeasure d N))
        (fun p : Ω d × Ω d =>
          (ouBandCoeff t : ℂ) • Xmat d N p.1 + (ouGueCoeff t : ℂ) • Xmat d N p.2)
        (fun p => Step1Conditioning.interp_isHermitian d N t p.1 p.2) k O E₀
        = C * ∫ p, F p ∂(μ.prod (gueMeasure d N)) := rfl
    _ = C * ∫ x, ∫ y, F (x, y) ∂(gueMeasure d N) ∂μ := by rw [integral_prod F hint]
    _ = ∫ x, C * ∫ y, F (x, y) ∂(gueMeasure d N) ∂μ := (integral_const_mul C _).symm
    _ = ∫ x, RBM.corrPairing (gueMeasure d N)
          (fun y => (ouBandCoeff t : ℂ) • Xmat d N x + (ouGueCoeff t : ℂ) • Xmat d N y)
          (fun y => Step1Conditioning.interp_isHermitian d N t x y) k O E₀ ∂μ := rfl
    _ = _ := integral_congr_ae (Eventually.of_forall fun x =>
          Step1Conditioning.inner_eq d N t k hcont E₀ x)

/-- **Conditioning** the OU pairing on the band matrix `H`
turns it into the `[51]`-type DBM pairing started at `diag(e^{-t/2} λ(H) - E₀)`. -/
theorem ouPairing_eq_integral (d : Dims) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : RBM.IsTestFun O) (E₀ : ℝ) :
    ouPairing d N t k O E₀ =
      ∫ ω, RBM.corrPairing (gueMeasure d N)
        (dbmMatrix d N (fun i => ouBandCoeff t * (Xmat_isHermitian d N ω).eigenvalues i - E₀)
          (ouZeta t)) (dbmMatrix_isHermitian _ _ _ _) k O 0 ∂(P d) :=
  Step1Conditioning.conditioning d N (P d) t k hO E₀

/-- **The same conditioning** for `H_∞`, written via
`law_gue_interp` as `e^{-t/2} G' + √ζ G` on `gueMeasure ⊗ gueMeasure` and conditioned on `G'`. -/
theorem gueMatPairing_eq_integral (d : Dims) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : RBM.IsTestFun O) (E₀ : ℝ) :
    gueMatPairing d N k O E₀ =
      ∫ ω, RBM.corrPairing (gueMeasure d N)
        (dbmMatrix d N (fun i => ouBandCoeff t * (Xmat_isHermitian d N ω).eigenvalues i - E₀)
          (ouZeta t)) (dbmMatrix_isHermitian _ _ _ _) k O 0 ∂(gueMeasure d N) := by
  have hlaw := corrPairing_congr_law (gueMeasure d N) ((gueMeasure d N).prod (gueMeasure d N))
    (measurable_Xmat d N) (Step1Conditioning.measurable_interp d N t) (Xmat_isHermitian d N)
    (fun p => Step1Conditioning.interp_isHermitian d N t p.1 p.2) (law_gue_interp d N ht).symm
    k hO.1.continuous E₀
  exact hlaw.trans (Step1Conditioning.conditioning d N (gueMeasure d N) t k hO E₀)

/-! ### Nondegenerate instance of the hypotheses (`t = 1`, `k = 1`, a bump `O`) -/

end RBM.Gauss
