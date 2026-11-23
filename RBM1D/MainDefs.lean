module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Contracting

@[expose] public section

/-!
# The definitions used by the main statements

Every definition that the statements of `Challenge.lean` use, moved unchanged from the files
named in the section headings. This file depends on Mathlib only; the definition part of
`Challenge.lean` is a copy of it.
-/

/-! ### From `RBM1D/Defs/Block.lean` -/

section

namespace RBM

open Finset Matrix

section Defs

variable (L : ℕ)

/-- The nearest-neighbour support `{0, 1, -1} ⊆ ZMod L`. -/
def sbSupport : Finset (ZMod L) := {0, 1, -1}

/-- The generating kernel of `S^(B)`: the value `1/3` on `{0, 1, -1}`, zero elsewhere. -/
noncomputable def sbKernel : ZMod L → ℂ :=
  fun u => if u ∈ sbSupport L then (3 : ℂ)⁻¹ else 0

/-- The block covariance matrix `S^(B)` of Section 2.1. -/
noncomputable def SB : Matrix (ZMod L) (ZMod L) ℂ := circulant (sbKernel L)

end Defs

end RBM

end

/-! ### From `RBM1D/Delocalization.lean` -/

section

namespace RBM

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Green's function `G(z) = (H - z)⁻¹`. -/
noncomputable def green (H : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ := (H - z • 1)⁻¹

end RBM

end

/-! ### From `RBM1D/Defs/StochDom.lean` -/

section

namespace RBM

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

section Defs

variable {U : ℕ → Type*}

/-- The failure event `{∃ u, ξ(N,u) > N^τ ζ(N,u)}`. -/
def badSet (ξ ζ : ∀ N, U N → Ω → ℝ) (τ : ℝ) (N : ℕ) : Set Ω :=
  {ω | ∃ u, (N : ℝ) ^ τ * ζ N u ω < ξ N u ω}

/-- **Definition 2.1 (i)**: `ξ ≺ ζ`, uniformly in `u ∈ U(N)`. -/
def StochDom (ξ ζ : ∀ N, U N → Ω → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    P (badSet ξ ζ τ N) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))

end Defs

namespace StochDom

variable {P} {U : ℕ → Type*} {ξ ζ χ ξ₁ ξ₂ ζ₁ ζ₂ : ∀ N, U N → Ω → ℝ}

/-- A failure event eventually contained in the failure event of a single domination. -/
theorem of_subset (h : StochDom P ξ₁ ζ₁)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      badSet ξ ζ τ N ⊆ badSet ξ₁ ζ₁ τ' N) : StochDom P ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with N h1 h2
  exact (measure_mono h1).trans h2

end StochDom

end RBM

end

/-! ### From `RBM1D/Defs/Model.lean` -/

section

namespace RBM

open Matrix Finset
open scoped Kronecker

section Kronecker

variable (L W : ℕ)

/-- The normalized block projection `E_a` of (2.5): `(E_a)_{ij} = δ_{ij} W⁻¹ 1(i ∈ I_a)`. -/
noncomputable def Eblk (a : ZMod L) : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  diagonal fun p => if p.1 = a then (W : ℂ)⁻¹ else 0

end Kronecker

end RBM

end

/-! ### From `RBM1D/Loop/Index.lean` -/

section

namespace RBM

/-- Index data `(σ, a)` of a `G`-loop: charges (`true` for `+`) and block labels. -/
@[ext]
structure LoopIdx (α : Type*) where
  σ : List Bool
  a : List α
  deriving DecidableEq

end RBM

end

/-! ### From `RBM1D/Loop/GLoop.lean` -/

section

namespace RBM

open Matrix

section Gsig

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `G(σ)`: the resolvent at `z` for `σ = true` (the paper's `+`) and at `conj z`
for `σ = false`. -/
noncomputable def Gsig (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) : Matrix n n ℂ :=
  green H (if σ then z else (starRingEnd ℂ) z)

@[simp] theorem Gsig_true {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (z : ℂ) :
    Gsig H z true = green H z := rfl

@[simp] theorem Gsig_false (H : Matrix n n ℂ) (z : ℂ) :
    Gsig H z false = green H ((starRingEnd ℂ) z) := rfl

end Gsig

section Loop

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The matrix product `∏_i G(σ_i) E_{a_i}` of (2.41). -/
noncomputable def gloopProd (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  (I.σ.zip I.a).foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M) 1

/-- **The `n`-`G` loop of (2.41)**, `L_{σ,a} = ⟨∏_i G(σ_i) E_{a_i}⟩`. -/
noncomputable def gloop (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) : ℂ :=
  Matrix.trace (gloopProd L W H z I)

variable {L W} {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

@[simp] theorem gloopProd_cons (s : Bool) (b : ZMod L) (σ : List Bool) (a : List (ZMod L)) :
    gloopProd L W H z ⟨s :: σ, b :: a⟩
      = Gsig H z s * Eblk L W b * gloopProd L W H z ⟨σ, a⟩ := rfl

end Loop

end RBM

end

/-! ### From `RBM1D/Defs/Semicircle.lean` -/

section

namespace RBM

open Complex

section mE

/-- `m^{(E)} = (-E + i√(4 - E²))/2`, the root of `m(m + E) = -1` with `Im m > 0` when
`|E| < 2`. -/
noncomputable def mE (E : ℝ) : ℂ := (-E + Real.sqrt (4 - E ^ 2) * I) / 2

theorem mE_im (E : ℝ) : (mE E).im = Real.sqrt (4 - E ^ 2) / 2 := by simp [mE]

theorem sq_sqrt_four_sub {E : ℝ} (hE : |E| ≤ 2) : Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := by
  refine Real.sq_sqrt ?_
  have := abs_le.mp hE
  nlinarith

theorem mE_mul {E : ℝ} (hE : |E| ≤ 2) : mE E * (mE E + E) = -1 := by
  have hs : ((Real.sqrt (4 - E ^ 2) : ℝ) : ℂ) ^ 2 = 4 - (E : ℂ) ^ 2 := by
    exact_mod_cast sq_sqrt_four_sub hE
  have hI : I ^ 2 = -1 := I_sq
  simp only [mE]
  linear_combination ((Real.sqrt (4 - E ^ 2) : ℂ) ^ 2 / 4) * hI - (1 / 4 : ℂ) * hs

theorem mE_im_pos {E : ℝ} (hE : |E| < 2) : 0 < (mE E).im := by
  rw [mE_im]
  have := abs_lt.mp hE
  have : 0 < 4 - E ^ 2 := by nlinarith
  positivity

/-- Uniqueness: `m^{(E)}` is the only root of `m(m + E) = -1` with `Im m > 0`. -/
theorem eq_mE {E : ℝ} (hE : |E| < 2) {m : ℂ} (hm : m * (m + E) = -1) (him : 0 < m.im) :
    m = mE E := by
  have h0 := mE_mul hE.le
  have h : (m - mE E) * (m + mE E + E) = 0 := by linear_combination hm - h0
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have him' := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] at him'
    have := mE_im_pos hE
    linarith

end mE

section msc

/-- A square root of `z² - 4`. -/
noncomputable def mscDisc (z : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (z ^ 2 - 4) (n := 2) (by norm_num))

theorem mscDisc_sq (z : ℂ) : mscDisc z ^ 2 = z ^ 2 - 4 :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (z ^ 2 - 4) (n := 2) (by norm_num))

/-- The two roots of `m² + z m + 1 = 0`. -/
noncomputable def mscRoot₁ (z : ℂ) : ℂ := (-z + mscDisc z) / 2

noncomputable def mscRoot₂ (z : ℂ) : ℂ := (-z - mscDisc z) / 2

/-- The Stieltjes transform of the semicircle law: the root of `m² + z m + 1 = 0` with
positive imaginary part (for `Im z > 0`). -/
noncomputable def msc (z : ℂ) : ℂ := if 0 < (mscRoot₁ z).im then mscRoot₁ z else mscRoot₂ z

theorem msc_mul (z : ℂ) : msc z * (msc z + z) = -1 := by
  have hd := mscDisc_sq z
  unfold msc mscRoot₁ mscRoot₂
  split_ifs <;> linear_combination (1 / 4 : ℂ) * hd

theorem msc_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (msc z).im := by
  have hd := mscDisc_sq z
  unfold msc
  split_ifs with h
  · exact h
  · push Not at h
    set r₁ := mscRoot₁ z
    set r₂ := mscRoot₂ z
    have hmul : r₁ * r₂ = 1 := by
      simp only [r₁, r₂, mscRoot₁, mscRoot₂]
      linear_combination (-1 / 4 : ℂ) * hd
    have hsum : r₁.im + r₂.im = -z.im := by
      have : r₁ + r₂ = -z := by simp only [r₁, r₂, mscRoot₁, mscRoot₂]; ring
      simpa using congrArg Complex.im this
    have hr₁ : r₁ ≠ 0 := left_ne_zero_of_mul_eq_one hmul
    have hr₂ : r₂ = r₁⁻¹ := eq_inv_of_mul_eq_one_right hmul
    have hN : 0 < Complex.normSq r₁ := Complex.normSq_pos.mpr hr₁
    have him : r₂.im * Complex.normSq r₁ = -r₁.im := by
      rw [hr₂, Complex.inv_im]
      field_simp
    by_contra hneg
    push Not at hneg
    have h1 : r₂.im * Complex.normSq r₁ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hN.le
    have h2 : r₁.im = 0 := by linarith
    have h3 : r₂.im < 0 := by linarith
    have h4 : r₂.im * Complex.normSq r₁ < 0 := mul_neg_of_neg_of_pos h3 hN
    linarith

end msc

section Flow

/-- Definition 2.7: `z_t^{(E)} = E + (1 - t) m^{(E)}`. -/
noncomputable def zt (E t : ℝ) : ℂ := E + (1 - t) * mE E

end Flow

section Lemma28

/-- The energy of Lemma 2.8: `E = -2 Re m_sc(z) / |m_sc(z)|`. -/
noncomputable def lemE (z : ℂ) : ℝ := -2 * (msc z).re / ‖msc z‖

/-- The time of Lemma 2.8: `t = |m_sc(z)|²`. -/
noncomputable def lemT (z : ℂ) : ℝ := ‖msc z‖ ^ 2

variable {z : ℂ} (hz : 0 < z.im)
include hz

theorem norm_msc_pos : 0 < ‖msc z‖ :=
  norm_pos_iff.mpr fun h => by
    have := msc_im_pos hz
    rw [h, Complex.zero_im] at this
    exact lt_irrefl _ this

theorem lemT_pos : 0 < lemT z := by
  have := norm_msc_pos hz
  unfold lemT
  positivity

/-- Real and imaginary parts of `u = m_sc(z)/|m_sc(z)|`, and `|u| = 1`. -/
theorem msc_div_norm_facts :
    let r := ‖msc z‖
    ((msc z / r).re ^ 2 + (msc z / r).im ^ 2 = 1) ∧ 0 < (msc z / r).im := by
  intro r
  have hr : 0 < r := norm_msc_pos hz
  have hr2 : r ^ 2 = (msc z).re ^ 2 + (msc z).im ^ 2 := by
    simp only [r, Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [Complex.div_ofReal_re, Complex.div_ofReal_im]
  refine ⟨?_, div_pos (msc_im_pos hz) hr⟩
  field_simp
  linarith

theorem abs_lemE_lt_two : |lemE z| < 2 := by
  obtain ⟨h1, h2⟩ := msc_div_norm_facts hz
  have hre : lemE z = -2 * (msc z / (‖msc z‖ : ℂ)).re := by
    rw [lemE, Complex.div_ofReal_re]
    ring
  rw [hre, abs_lt]
  constructor <;> nlinarith

/-- The key step of Lemma 2.8: `m^{(E)} = m_sc(z) / |m_sc(z)|`. -/
theorem mE_lemE : mE (lemE z) = msc z / (‖msc z‖ : ℂ) := by
  obtain ⟨h1, h2⟩ := msc_div_norm_facts hz
  symm
  refine eq_mE (abs_lemE_lt_two hz) ?_ h2
  set u := msc z / (‖msc z‖ : ℂ) with hu
  have hre : lemE z = -2 * u.re := by
    rw [lemE, hu, Complex.div_ofReal_re]
    ring
  rw [hre]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, Complex.neg_re, Complex.one_re]
    nlinarith
  · simp only [Complex.mul_im, Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, Complex.neg_im, Complex.one_im]
    ring

/-- (2.37): `z = t^{-1/2} z_t^{(E)}`. -/
theorem eq_inv_sqrt_mul_zt : z = (Real.sqrt (lemT z) : ℂ)⁻¹ * zt (lemE z) (lemT z) := by
  set r := ‖msc z‖ with hr_def
  have hr : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_msc_pos hz).ne'
  set u := mE (lemE z) with hu_def
  set E := lemE z
  have hu : u * (u + E) = -1 := mE_mul (abs_lemE_lt_two hz).le
  have hmu : msc z = r * u := by
    rw [hu_def, mE_lemE hz, ← hr_def]
    field_simp
  have hm := msc_mul z
  rw [hmu] at hm
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  have hsqrt : Real.sqrt (lemT z) = r := by rw [lemT, Real.sqrt_sq (norm_nonneg _)]
  rw [hsqrt, zt, lemT, ← hr_def]
  push_cast
  have key : (z * r - (E + (1 - r ^ 2) * u)) * u = 0 := by
    linear_combination hm - hu
  have h2 : z * r = E + (1 - r ^ 2) * u := by
    have := (mul_eq_zero.mp key).resolve_right hu0
    linear_combination this
  field_simp
  linear_combination h2

end Lemma28

end RBM

end

/-! ### From `RBM1D/Propagator/Basic.lean` -/

section

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

section Defs

variable (L : ℕ) [NeZero L]

/-- Definition 2.13: the propagator `Θ_ξ = (1 - ξ S^(B))⁻¹`. -/
noncomputable def Theta (ξ : ℂ) : Matrix (ZMod L) (ZMod L) ℂ :=
  Ring.inverse (1 - ξ • SB L)

end Defs

end RBM

end
/-! ### From `RBM1D/Green/EntryBound.lean` -/

section

namespace RBM

open Matrix Finset

section Block

variable (L W : ℕ)

/-- The kernel of `S^(B)` as a real function: `1/3` on `{0, 1, -1}`, zero elsewhere. -/
noncomputable def sbKre (u : ZMod L) : ℝ := if u ∈ sbSupport L then 1 / 3 else 0

/-- The variance profile `S = S^(B) ⊗ S_W` of Section 2.1 as a real matrix on the
block/offset index: `S_{(a,α),(b,β)} = S^(B)_{ab} / W`. -/
noncomputable def Sblk (i j : ZMod L × Fin W) : ℝ := sbKre L (i.1 - j.1) / W

variable {L W}

theorem sbKre_nonneg (u : ZMod L) : 0 ≤ sbKre L u := by
  unfold sbKre; split_ifs <;> norm_num

variable [NeZero L]

variable [NeZero W]

omit [NeZero L] [NeZero W] in
theorem Sblk_nonneg (i j : ZMod L × Fin W) : 0 ≤ Sblk L W i j :=
  div_nonneg (sbKre_nonneg _) (Nat.cast_nonneg _)

end Block

end RBM

end

/-! ### From `RBM1D/Flow/Hypotheses.lean` -/

section

namespace RBM

open MeasureTheory Filter

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A pointwise smaller family is dominated by whatever dominates the larger one. -/
theorem StochDom.of_le_left {U : ℕ → Type*} {ξ ξ' ζ : ∀ N, U N → Ω → ℝ}
    (hle : ∀ N u ω, ξ N u ω ≤ ξ' N u ω) (h : StochDom P ξ' ζ) : StochDom P ξ ζ :=
  StochDom.of_subset h fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun N ω h =>
      h.elim fun u hu => ⟨u, lt_of_lt_of_le hu (hle N u ω)⟩⟩

end Generic

/-- **The band model: dimensions, bandwidth (2.2), probability measure.**

At index `N` the matrix has `L N` blocks of size `W N`.  The paper's `N = W L` is replaced by
`W L ≤ N ≤ 2 W L` for large `N` (a relation that can hold for every large `N`, unlike
`N = W L`).  `bandwidth` is (2.2) `W ≥ N^{1/2 + c}`. -/
structure Band (Ω : Type*) [MeasurableSpace Ω] where
  /-- The probability measure. -/
  P : Measure Ω
  isProbabilityMeasure : IsProbabilityMeasure P
  /-- The block size `W = W(N)`. -/
  W : ℕ → ℕ
  /-- The number of blocks `L = L(N)`. -/
  L : ℕ → ℕ
  W_pos : ∀ N, 0 < W N
  three_le_L : ∀ N, 3 ≤ L N
  /-- `N = W L` up to a factor `2`. -/
  dim : ∀ᶠ N : ℕ in atTop, W N * L N ≤ N ∧ N ≤ 2 * (W N * L N)
  /-- The constant `c > 0` of (2.2). -/
  c : ℝ
  c_pos : 0 < c
  /-- **(2.2)** `W ≥ N^{1/2 + c}`. -/
  bandwidth : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2 + c) ≤ W N

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

instance neZeroL (N : ℕ) : NeZero (B.L N) :=
  ⟨(Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) (B.three_le_L N)).ne'⟩

/-- The row index `ZMod L × Fin W` of the `N × N` matrices (block, offset). -/
abbrev Idx (N : ℕ) : Type := ZMod (B.L N) × Fin (B.W N)

end Band

/-- **The stochastic flow (2.34), per `N`.**  `H N t ω` is the matrix `H_t`; it is Hermitian,
`H_0 = 0` and entrywise measurable.  The law of the flow (a matrix Brownian motion with variance
profile `S`) is not formalized; its consequences enter as hypotheses: the fields of
`RBM.Transfer`, and the bounds of Lemmas 2.18–2.20 and Theorem 2.21 (`RBM.BoundsN`,
`RBM.Thm221N'` in `Flow/EnergyUniform.lean`). -/
structure Sample {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) where
  /-- The matrix flow `t ↦ H_t`. -/
  H : ∀ N, ℝ → Ω → Matrix (B.Idx N) (B.Idx N) ℂ
  hermitian : ∀ N t ω, Matrix.IsHermitian (H N t ω)
  /-- `H_0 = 0` (2.34). -/
  H_zero : ∀ N ω, H N 0 ω = 0
  measurable : ∀ N t i j, Measurable fun ω => H N t ω i j

namespace Sample

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B)

/-- **(2.36)** `G_t = (H_t - z_t)⁻¹`, `z_t = E + (1-t) m^{(E)}` (Definition 2.7). -/
noncomputable def G (E : ℝ) (N : ℕ) (t : ℝ) (ω : Ω) : Matrix (B.Idx N) (B.Idx N) ℂ :=
  green (X.H N t ω) (zt E t)

/-- **(2.41)** the `n`-`G` loop `L_{t,σ,a} = ⟨∏ G_t(σ_i) E_{a_i}⟩`. -/
noncomputable def Lval (E : ℝ) (N : ℕ) (t : ℝ) (ω : Ω) (I : LoopIdx (ZMod (B.L N))) : ℂ :=
  gloop (B.L N) (B.W N) (X.H N t ω) (zt E t) I

/-- The expectation `E L_{t,σ,a}`. -/
noncomputable def ELval (E : ℝ) (N : ℕ) (t : ℝ) (I : LoopIdx (ZMod (B.L N))) : ℂ :=
  ∫ ω, X.Lval E N t ω I ∂B.P

end Sample

/-- **The band matrix and the identities in law (2.39), (2.66)** (Lemma 2.8), written as
transfers of `≺`-bounds rather than equalities of laws.

For `Im z > 0` let `E = lemE z`, `t = lemT z` (Lemma 2.8, `RBM.lemE`, `RBM.lemT`; then
`z = t^{-1/2} z_t^{(E)}` and `m_sc(z) = t^{1/2} m^{(E)}` are proved in `Defs/Semicircle.lean`).
Since `H` and `t^{-1/2} H_t` have the same law, so do `G(z)` and `t^{1/2} G_t^{(E)}` (2.39), and
the loops `Tr G(z) E_a G(z) E_b`, `Tr G(z) E_a G(z)† E_b` and `t L_{t,(+,±),(a,b)}` (2.66).
Equality in law of finitely many measurable random variables transfers every bound of the form
`max_u |ξ(u) - c(u)| ≤ N^τ ζ(u)` with deterministic `c`, `ζ`; that is what is recorded.
Only the direction `G_t → G(z)` is used in the paper. -/
structure Transfer {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) where
  /-- The band matrix `H` of Section 2.1, one for each `N`. -/
  Hband : ∀ N, Ω → Matrix (B.Idx N) (B.Idx N) ℂ
  hermitian : ∀ N ω, Matrix.IsHermitian (Hband N ω)
  /-- **(2.39)** `G(z) ∼ t^{1/2} G_t^{(E)}`, entrywise, with deterministic centering `c`. -/
  green : ∀ z : ℕ → ℂ, (∀ N, 0 < (z N).im) →
    ∀ (c : ∀ N, B.Idx N × B.Idx N → ℂ) (ζ : ∀ N, B.Idx N × B.Idx N → ℝ),
    StochDom B.P
      (fun N ij ω => ‖(Real.sqrt (lemT (z N)) : ℂ) *
        X.G (lemE (z N)) N (lemT (z N)) ω ij.1 ij.2 - c N ij‖)
      (fun N ij _ => ζ N ij) →
    StochDom B.P (fun N ij ω => ‖RBM.green (Hband N ω) (z N) ij.1 ij.2 - c N ij‖)
      (fun N ij _ => ζ N ij)
  /-- **(2.66)** `Tr G(z) E_a G(z)^{(±)} E_b ∼ t L_{t,(+,±),(a,b)}`, with deterministic
  centering `c` (`σ₂ = true`: `G(z)`; `σ₂ = false`: `G(z)† = G(z̄)`). -/
  loop2 : ∀ z : ℕ → ℂ, (∀ N, 0 < (z N).im) → ∀ σ₂ : Bool,
    ∀ (c : ∀ N, ZMod (B.L N) × ZMod (B.L N) → ℂ) (ζ : ∀ N, ZMod (B.L N) × ZMod (B.L N) → ℝ),
    StochDom B.P
      (fun N ab ω => ‖(lemT (z N) : ℂ) *
        X.Lval (lemE (z N)) N (lemT (z N)) ω ⟨[true, σ₂], [ab.1, ab.2]⟩ - c N ab‖)
      (fun N ab _ => ζ N ab) →
    StochDom B.P
      (fun N ab ω => ‖gloop (B.L N) (B.W N) (Hband N ω) (z N) ⟨[true, σ₂], [ab.1, ab.2]⟩ -
        c N ab‖)
      (fun N ab _ => ζ N ab)
  /-- **(2.66) in expectation** (used for (2.8), (2.9) together with (2.62)). -/
  loop2_expect : ∀ z : ℕ → ℂ, (∀ N, 0 < (z N).im) → ∀ (σ₂ : Bool) (N : ℕ)
    (a b : ZMod (B.L N)),
    ∫ ω, gloop (B.L N) (B.W N) (Hband N ω) (z N) ⟨[true, σ₂], [a, b]⟩ ∂B.P =
      (lemT (z N) : ℂ) * X.ELval (lemE (z N)) N (lemT (z N)) ⟨[true, σ₂], [a, b]⟩

end RBM

end

/-! ### From `RBM1D/Flow/Scales.lean` -/

section

namespace RBM

open Real

section Dictionary

/-- `η ↦ min(η^{-1/2}, L) + 1`. -/
noncomputable def ellOf (L : ℕ) (η : ℝ) : ℝ := min (1 / Real.sqrt η) (L : ℝ) + 1

/-- The diffusion length at the block level (2.1): `ℓ(z) = min(η^{-1/2}, L) + 1`, `η = Im z`. -/
noncomputable def ellZ (L : ℕ) (z : ℂ) : ℝ := ellOf L z.im

end Dictionary

end RBM

end

/-! ### From `RBM1D/Flow/Consequences.lean` -/

section

namespace RBM

open MeasureTheory Filter

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

/-- The scale `W ℓ(z) η`, `η = Im z`, `ℓ(z) = min(η^{-1/2}, L) + 1` (2.1), of (2.3)–(2.9). -/
noncomputable def zScale (N : ℕ) (z : ℂ) : ℝ := (B.W N : ℝ) * ellZ (B.L N) z * z.im

end Band

end RBM

end

/-! ### From `RBM1D/Gauss/Model.lean` -/

section

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-- The dimension data of the band model: everything in `RBM.Band` except the probability
measure (which this file constructs).  The fields are literally the fields of `RBM.Band`. -/
structure Dims where
  /-- The block size `W = W(N)`. -/
  W : ℕ → ℕ
  /-- The number of blocks `L = L(N)`. -/
  L : ℕ → ℕ
  W_pos : ∀ N, 0 < W N
  three_le_L : ∀ N, 3 ≤ L N
  /-- `N = W L` up to a factor `2`. -/
  dim : ∀ᶠ N : ℕ in atTop, W N * L N ≤ N ∧ N ≤ 2 * (W N * L N)
  /-- The constant `c > 0` of (2.2). -/
  c : ℝ
  c_pos : 0 < c
  /-- **(2.2)** `W ≥ N^{1/2 + c}`. -/
  bandwidth : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2 + c) ≤ W N

namespace Dims

variable (d : Dims)

instance neZeroW (N : ℕ) : NeZero (d.W N) := ⟨(d.W_pos N).ne'⟩

instance neZeroL (N : ℕ) : NeZero (d.L N) :=
  ⟨(Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) (d.three_le_L N)).ne'⟩

/-- The matrix index `ZMod L × Fin W` (block, offset); definitionally `RBM.Band.Idx`. -/
abbrev Idx (N : ℕ) : Type := ZMod (d.L N) × Fin (d.W N)

end Dims

/-- The injective key `W * a.val + α` on `Idx d N = ZMod (L N) × Fin (W N)`. -/
def idxKey (d : Dims) (N : ℕ) (i : d.Idx N) : ℕ := d.W N * i.1.val + (i.2 : ℕ)

theorem idxKey_injective (d : Dims) (N : ℕ) : Function.Injective (idxKey d N) := by
  rintro ⟨a, α⟩ ⟨b, β⟩ h
  simp only [idxKey] at h
  have hW : 0 < d.W N := d.W_pos N
  have hα : (α : ℕ) < d.W N := α.isLt
  have hβ : (β : ℕ) < d.W N := β.isLt
  have hmod := congrArg (· % d.W N) h
  have hdiv := congrArg (· / d.W N) h
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hα, Nat.mod_eq_of_lt hβ] at hmod
  simp only [Nat.mul_add_div hW, Nat.div_eq_of_lt hα, Nat.div_eq_of_lt hβ, add_zero] at hdiv
  have : a = b := ZMod.val_injective (d.L N) hdiv
  subst this
  exact Prod.ext rfl (Fin.ext hmod)

theorem idxKey_lt_or_eq_or_lt (d : Dims) (N : ℕ) (i j : d.Idx N) :
    idxKey d N i < idxKey d N j ∨ i = j ∨ idxKey d N j < idxKey d N i := by
  rcases lt_trichotomy (idxKey d N i) (idxKey d N j) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (idxKey_injective d N h))
  · exact Or.inr (Or.inr h)

/-- The independent real coordinates: `⟨N, i, j, b⟩` with `b = true` the real part and
`b = false` the imaginary part of the entry `X_ij` at size parameter `N`.  Only the pairs with
`idxKey i ≤ idxKey j` are read by `Xentry`. -/
abbrev Coord (d : Dims) : Type := Σ N : ℕ, d.Idx N × d.Idx N × Bool

/-- The sample space: one real coordinate per element of `Coord d`. -/
abbrev Ω (d : Dims) : Type := Coord d → ℝ

/-- The variance of the coordinate `⟨N, i, j, b⟩`: `S_ij` on the diagonal (one real Gaussian),
`S_ij / 2` off the diagonal (two independent real Gaussians), so that `E|X_ij|² = S_ij`
in both cases.  `S` is `RBM.Sblk`, the real form of `S = S^(B) ⊗ S_W`. -/
noncomputable def gvar (d : Dims) : Coord d → ℝ≥0 := fun c =>
  ⟨if c.2.1 = c.2.2.1 then Sblk (d.L c.1) (d.W c.1) c.2.1 c.2.2.1
    else Sblk (d.L c.1) (d.W c.1) c.2.1 c.2.2.1 / 2, by
      split_ifs
      · exact Sblk_nonneg _ _
      · exact div_nonneg (Sblk_nonneg _ _) (by norm_num)⟩

/-- The measure: the infinite product of the centred one-dimensional Gaussians
`gaussianReal 0 (gvar d c)`.  All coordinates are independent. -/
noncomputable def P (d : Dims) : Measure (Ω d) :=
  Measure.infinitePi fun c => gaussianReal 0 (gvar d c)

instance isProbabilityMeasure_P (d : Dims) : IsProbabilityMeasure (P d) := by
  unfold P; infer_instance

/-- The entry `X_ij`, read off from the coordinates of the pair `(min i j, max i j)` in the
`idxKey` order.  See the file header for the table. -/
noncomputable def Xentry (d : Dims) (N : ℕ) (ω : Ω d) (i j : d.Idx N) : ℂ :=
  if idxKey d N i < idxKey d N j then
    (ω ⟨N, i, j, true⟩ : ℂ) + Complex.I * (ω ⟨N, i, j, false⟩ : ℂ)
  else if idxKey d N j < idxKey d N i then
    (ω ⟨N, j, i, true⟩ : ℂ) - Complex.I * (ω ⟨N, j, i, false⟩ : ℂ)
  else (ω ⟨N, i, j, true⟩ : ℂ)

/-- The fixed Gaussian band matrix `X` at size parameter `N`. -/
noncomputable def Xmat (d : Dims) (N : ℕ) (ω : Ω d) : Matrix (d.Idx N) (d.Idx N) ℂ :=
  Matrix.of fun i j => Xentry d N ω i j

/-- `X_ji = conj X_ij`, **pointwise** in `ω`. -/
theorem Xentry_swap (d : Dims) (N : ℕ) (ω : Ω d) (i j : d.Idx N) :
    Xentry d N ω j i = (starRingEnd ℂ) (Xentry d N ω i j) := by
  unfold Xentry
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · rw [ite_eq_right (asymm h), ite_eq_left h, ite_eq_left h]
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  · subst h
    rw [ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
    simp only [Complex.conj_ofReal]
  · rw [ite_eq_left h, ite_eq_right (asymm h), ite_eq_left h]
    simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring

/-- **`X` is Hermitian** — the `hermitian` field of `RBM.Sample`. -/
theorem Xmat_isHermitian (d : Dims) (N : ℕ) (ω : Ω d) : (Xmat d N ω).IsHermitian := by
  ext i j
  exact (Xentry_swap d N ω j i).symm

/-- **Entrywise measurability** — the `measurable` field of `RBM.Sample` (before the scaling). -/
theorem measurable_Xentry (d : Dims) (N : ℕ) (i j : d.Idx N) :
    Measurable fun ω : Ω d => Xentry d N ω i j := by
  unfold Xentry
  split_ifs <;>
    exact by fun_prop

/-- **(2.34) in the moment route**: `H_u := √u • X`.  For each fixed `u ≥ 0` this has exactly
the law of the paper's `H_u`; the path `u ↦ H_u` is *not* a Brownian motion. -/
noncomputable def Hflow (d : Dims) (N : ℕ) (u : ℝ) (ω : Ω d) : Matrix (d.Idx N) (d.Idx N) ℂ :=
  (Real.sqrt u : ℂ) • Xmat d N ω

@[simp] theorem Hflow_apply (d : Dims) (N : ℕ) (u : ℝ) (ω : Ω d) (i j : d.Idx N) :
    Hflow d N u ω i j = (Real.sqrt u : ℂ) * Xentry d N ω i j := rfl

/-- `H_0 = 0` — the `H_zero` field of `RBM.Sample`. -/
@[simp] theorem Hflow_zero (d : Dims) (N : ℕ) (ω : Ω d) : Hflow d N 0 ω = 0 := by
  simp [Hflow]

theorem Hflow_isHermitian (d : Dims) (N : ℕ) (u : ℝ) (ω : Ω d) :
    (Hflow d N u ω).IsHermitian := by
  ext i j
  show (starRingEnd ℂ) ((Real.sqrt u : ℂ) * Xentry d N ω j i)
      = (Real.sqrt u : ℂ) * Xentry d N ω i j
  rw [map_mul, Complex.conj_ofReal, ← Xentry_swap]

theorem measurable_Hflow (d : Dims) (N : ℕ) (u : ℝ) (i j : d.Idx N) :
    Measurable fun ω : Ω d => Hflow d N u ω i j := by
  simp only [Hflow_apply]
  exact (measurable_Xentry d N i j).const_mul _

/-- The band model of `RBM1D/Flow/Hypotheses.lean` carried by the Gaussian space. -/
noncomputable def band (d : Dims) : RBM.Band (Ω d) where
  P := P d
  isProbabilityMeasure := isProbabilityMeasure_P d
  W := d.W
  L := d.L
  W_pos := d.W_pos
  three_le_L := d.three_le_L
  dim := d.dim
  c := d.c
  c_pos := d.c_pos
  bandwidth := d.bandwidth

/-- **The `RBM.Sample` of the moment route.**  The three fields `hermitian`, `H_zero`,
`measurable` are theorems, not hypotheses. -/
noncomputable def sample (d : Dims) : RBM.Sample (band d) where
  H := fun N u ω => Hflow d N u ω
  hermitian := fun N u ω => Hflow_isHermitian d N u ω
  H_zero := fun N ω => Hflow_zero d N ω
  measurable := fun N u i j => measurable_Hflow d N u i j

end RBM.Gauss

end

/-! ### From `RBM1D/Gauss/DistEq.lean` -/

section

namespace RBM.Gauss

open MeasureTheory Filter Matrix
open scoped NNReal ENNReal

section Algebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `(c • A)⁻¹ = c⁻¹ • A⁻¹` for a nonzero scalar, with no invertibility assumption on `A`
(`Matrix.inv_smul` needs `IsUnit A.det`; when `A` is singular both sides are `0`). -/
theorem inv_smul_of_ne_zero {c : ℂ} (hc : c ≠ 0) (A : Matrix n n ℂ) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · have : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul A c h, invOf_eq_inv c]
  · have hdet : A.det = 0 := by simpa [isUnit_iff_ne_zero] using h
    have h2 : ¬ IsUnit (c • A).det := by
      rw [Matrix.det_smul, hdet, mul_zero]
      simp
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h2, Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

/-- **The scaling of the Green function**: `G(cH, cz) = c⁻¹ G(H, z)`. -/
theorem green_smul_mul {c : ℂ} (hc : c ≠ 0) (H : Matrix n n ℂ) (z : ℂ) :
    RBM.green (c • H) (c * z) = c⁻¹ • RBM.green H z := by
  have hsub : c • H - (c * z) • (1 : Matrix n n ℂ) = c • (H - z • (1 : Matrix n n ℂ)) := by
    rw [smul_sub, smul_smul]
  unfold RBM.green
  rw [hsub, inv_smul_of_ne_zero hc]

/-- The same for `RBM.Gsig`: the scalar must be **real**, so that it commutes with the
conjugation of the `σ = false` branch. -/
theorem Gsig_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0) (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) :
    RBM.Gsig ((r : ℂ) • H) ((r : ℂ) * z) σ = ((r : ℂ))⁻¹ • RBM.Gsig H z σ := by
  cases σ with
  | true => simpa only [RBM.Gsig_true] using green_smul_mul hr H z
  | false =>
    rw [RBM.Gsig_false, RBM.Gsig_false, map_mul, Complex.conj_ofReal]
    exact green_smul_mul hr H _

end Algebra

section LoopAlgebra

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `∏ G(cH, cz)(σ_i) E_{a_i} = c⁻ⁿ ∏ G(H, z)(σ_i) E_{a_i}`. -/
theorem gloopProd_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : RBM.LoopIdx (ZMod L)) :
    RBM.gloopProd L W ((r : ℂ) • H) ((r : ℂ) * z) I
      = (((r : ℂ))⁻¹ ^ (I.σ.zip I.a).length) • RBM.gloopProd L W H z I := by
  obtain ⟨σ, a⟩ := I
  induction σ generalizing a with
  | nil => simp [RBM.gloopProd]
  | cons s σ ih =>
    cases a with
    | nil => simp [RBM.gloopProd]
    | cons b a =>
      rw [RBM.gloopProd_cons, RBM.gloopProd_cons, Gsig_smul_mul hr, ih, smul_mul_assoc,
        smul_mul_assoc, mul_smul_comm, smul_smul]
      simp only [List.zip_cons_cons, List.length_cons]
      congr 1
      ring

/-- **The scaling of the `n`-`G` loop**: `L(cH, cz) = c⁻ⁿ L(H, z)`. -/
theorem gloop_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : RBM.LoopIdx (ZMod L)) :
    RBM.gloop L W ((r : ℂ) • H) ((r : ℂ) * z) I
      = ((r : ℂ))⁻¹ ^ (I.σ.zip I.a).length * RBM.gloop L W H z I := by
  unfold RBM.gloop
  rw [gloopProd_smul_mul hr, Matrix.trace_smul, smul_eq_mul]

end LoopAlgebra

/-- **(2.37)** read forwards: `z_t^{(E)} = t^{1/2} z` for `E = lemE z`, `t = lemT z`. -/
theorem zt_eq_sqrt_lemT_mul {z : ℂ} (hz : 0 < z.im) :
    RBM.zt (RBM.lemE z) (RBM.lemT z) = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) * z := by
  have hs : ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (RBM.lemT_pos hz)).ne'
  calc RBM.zt (RBM.lemE z) (RBM.lemT z)
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) *
          (((Real.sqrt (RBM.lemT z) : ℝ) : ℂ)⁻¹ * RBM.zt (RBM.lemE z) (RBM.lemT z)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    _ = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) * z := by rw [← RBM.eq_inv_sqrt_mul_zt hz]

theorem sqrt_lemT_ne_zero {z : ℂ} (hz : 0 < z.im) :
    ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (RBM.lemT_pos hz)).ne'

variable (d : Dims)

/-- **(2.39) pointwise**, entrywise: `G(X(ω), z)_{ij} = t^{1/2} (G_t^{(E)}(ω))_{ij}`, an
*equality*, not merely an equality in law. -/
theorem green_Hflow_lemT_eq (N : ℕ) {z : ℂ} (hz : 0 < z.im) (ω : Ω d) (i j : d.Idx N) :
    RBM.green (Xmat d N ω) z i j
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) *
        RBM.green (Hflow d N (RBM.lemT z) ω) (RBM.zt (RBM.lemE z) (RBM.lemT z)) i j := by
  have hs := sqrt_lemT_ne_zero hz
  have hmat : RBM.green (Hflow d N (RBM.lemT z) ω) (RBM.zt (RBM.lemE z) (RBM.lemT z))
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ)⁻¹ • RBM.green (Xmat d N ω) z := by
    rw [zt_eq_sqrt_lemT_mul hz, show Hflow d N (RBM.lemT z) ω
        = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) • Xmat d N ω from rfl, green_smul_mul hs]
  rw [hmat, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- **(2.66) pointwise**, for a loop of any length `n`: the `n`-loop of `G(X(ω), z)` is
`t^{n/2} L_{t,σ,a}(ω)`. -/
theorem gloop_Hflow_lemT_eq (N : ℕ) {z : ℂ} (hz : 0 < z.im) (ω : Ω d)
    (σ : List Bool) (a : List (ZMod (d.L N))) :
    RBM.gloop (d.L N) (d.W N) (Xmat d N ω) z ⟨σ, a⟩
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) ^ (σ.zip a).length *
        RBM.gloop (d.L N) (d.W N) (Hflow d N (RBM.lemT z) ω)
          (RBM.zt (RBM.lemE z) (RBM.lemT z)) ⟨σ, a⟩ := by
  have hs := sqrt_lemT_ne_zero hz
  rw [zt_eq_sqrt_lemT_mul hz, show Hflow d N (RBM.lemT z) ω
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) • Xmat d N ω from rfl, gloop_smul_mul hs]
  show _ = _ * ((((Real.sqrt (RBM.lemT z) : ℝ) : ℂ))⁻¹ ^ (σ.zip a).length * _)
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]

/-- **(2.66)** for the 2-`G` loop, pointwise:
`Tr G(z) E_a G(z)^{(σ₂)} E_b = t · L_{t,(+,σ₂),(a,b)}`. -/
theorem gloop_two_Hflow_lemT_eq (N : ℕ) {z : ℂ} (hz : 0 < z.im) (ω : Ω d) (σ₂ : Bool)
    (a b : ZMod (d.L N)) :
    RBM.gloop (d.L N) (d.W N) (Xmat d N ω) z ⟨[true, σ₂], [a, b]⟩
      = ((RBM.lemT z : ℝ) : ℂ) *
        RBM.gloop (d.L N) (d.W N) (Hflow d N (RBM.lemT z) ω)
          (RBM.zt (RBM.lemE z) (RBM.lemT z)) ⟨[true, σ₂], [a, b]⟩ := by
  have hlen : (([true, σ₂] : List Bool).zip [a, b]).length = 2 := rfl
  rw [gloop_Hflow_lemT_eq d N hz ω [true, σ₂] [a, b], hlen, ← Complex.ofReal_pow,
    Real.sq_sqrt (RBM.lemT_pos hz).le]

/-- **The band matrix and the identities in law (2.39), (2.66)** for the moment route.
The band matrix is `X` itself and every field is an *equality* of random variables, so the
transfer of `≺`-bounds is a rewriting. -/
noncomputable def transfer_gauss : RBM.Transfer (sample d) where
  Hband := fun N ω => Xmat d N ω
  hermitian := fun N ω => Xmat_isHermitian d N ω
  green := by
    intro z hz c ζ h
    refine RBM.StochDom.of_le_left (fun N ij ω => le_of_eq ?_) h
    congr 2
    exact green_Hflow_lemT_eq d N (hz N) ω ij.1 ij.2
  loop2 := by
    intro z hz σ₂ c ζ h
    refine RBM.StochDom.of_le_left (fun N ab ω => le_of_eq ?_) h
    congr 2
    exact gloop_two_Hflow_lemT_eq d N (hz N) ω σ₂ ab.1 ab.2
  loop2_expect := by
    intro z hz σ₂ N a b
    have key : ∀ ω : Ω d,
        RBM.gloop (d.L N) (d.W N) (Xmat d N ω) (z N) ⟨[true, σ₂], [a, b]⟩
          = ((RBM.lemT (z N) : ℝ) : ℂ) *
            (sample d).Lval (RBM.lemE (z N)) N (RBM.lemT (z N)) ω ⟨[true, σ₂], [a, b]⟩ :=
      fun ω => gloop_two_Hflow_lemT_eq d N (hz N) ω σ₂ a b
    show ∫ ω, RBM.gloop (d.L N) (d.W N) (Xmat d N ω) (z N) ⟨[true, σ₂], [a, b]⟩ ∂(P d) = _
    simp only [key]
    rw [MeasureTheory.integral_const_mul]
    rfl

end RBM.Gauss

end

/-! ### From `RBM1D/Flow/Universality.lean` -/

section

namespace RBM

open Matrix MeasureTheory Filter
open scoped ComplexConjugate

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

/-- The overlap `ψ_i* A ψ_j` of two eigenvectors of `H` through a matrix `A`. -/
noncomputable def eigOverlap (A : Matrix n n ℂ) (i j : n) : ℂ :=
  star (fun x => hH.eigenvectorBasis i x) ⬝ᵥ (A *ᵥ fun x => hH.eigenvectorBasis j x)

end Spectral

section Scale

/-- **The spectral scale of Theorem 2.5**: `η = N^{-1-τ*} (W²/N)^{1/3}`; `J_E = [E - η, E + η]`. -/
noncomputable def queEta (N W τ : ℝ) : ℝ := N ^ (-1 - τ) * (W ^ 2 / N) ^ ((1 : ℝ) / 3)

variable {N W τ : ℝ}

end Scale

section Sequence

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Band

variable (B : Band Ω)

/-- The matrix size `N = L W` (the paper's `N`; the index of `RBM.Band` is only comparable). -/
def size (N : ℕ) : ℕ := B.L N * B.W N

end Band

/-- The spectral scale `η_N = N^{-1-τ*} (W²/N)^{1/3}` of Theorem 2.5 at index `N` (`N = L W`). -/
noncomputable def Band.queEtaN (B : Band Ω) (τ : ℝ) (N : ℕ) : ℝ :=
  queEta (B.size N : ℝ) (B.W N : ℝ) τ

/-- The event of **(2.12)**: `max_{λ_i, λ_j ∈ J_E} |N ψ_i* (E_a - N⁻¹ I) ψ_j|² ≥ ε`. -/
def queEvent212 {L W : ℕ} [NeZero L] {H : Ω → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : ∀ ω, (H ω).IsHermitian) (a : ZMod L) (E η ε : ℝ) : Set Ω :=
  {ω | ∃ i j, |(hH ω).eigenvalues i - E| ≤ η ∧ |(hH ω).eigenvalues j - E| ≤ η ∧
    ε ≤ ‖((L * W : ℕ) : ℂ) *
      eigOverlap (hH ω) (Eblk L W a - ((L * W : ℕ) : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) i j‖ ^ 2}

/-- The event of **(2.13)**: `max_{λ_k ∈ J_E} |∑_{a ∈ A} ∑_{x ∈ I_a} |ψ_k(x)|² - |A| W / N|
≥ |A| W / N^{1 + τ*/12}`. -/
def queEvent213 {L W : ℕ} [NeZero L] {H : Ω → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : ∀ ω, (H ω).IsHermitian) (A : Finset (ZMod L)) (E η τ : ℝ) : Set Ω :=
  {ω | ∃ k, |(hH ω).eigenvalues k - E| ≤ η ∧
    (A.card * W : ℕ) / ((L * W : ℕ) : ℝ) ^ (1 + τ / 12) ≤
      |∑ a ∈ A, ∑ x : Fin W, ‖(hH ω).eigenvectorBasis k (a, x)‖ ^ 2 -
        (A.card * W : ℕ) / ((L * W : ℕ) : ℝ)|}

end Sequence

section CorrelationFunctions

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The pairing `∫_{ℝ^k} O(α) ρ^{(k)}_H(E + α/N) dα`** for a random Hermitian `N × N` matrix `H`,
written without densities: if the unordered eigenvalues have joint density `ρ^{(N)}_H` and
`ρ^{(k)}_H` is its `k`-marginal (the paper's definition before Theorem 2.6), then by symmetry
`∫ O(α) ρ^{(k)}_H(E + α/N) dα
  = N^k (N-k)!/N! · E ∑_{i : Fin k ↪ [N]} O(N(λ_{i_1} - E), …, N(λ_{i_k} - E))`,
which is what is defined here (it makes sense with or without a density). -/
noncomputable def corrPairing {n : Type*} [Fintype n] [DecidableEq n] (P : Measure Ω)
    (H : Ω → Matrix n n ℂ) (hH : ∀ ω, (H ω).IsHermitian) (k : ℕ) (O : (Fin k → ℝ) → ℝ)
    (E : ℝ) : ℝ :=
  (Fintype.card n : ℝ) ^ k * (((Fintype.card n - k).factorial : ℝ) / (Fintype.card n).factorial) *
    ∫ ω, ∑ f : Fin k ↪ n, O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E)) ∂P

end CorrelationFunctions

section TheoremTwoSix

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The test functions of Theorem 2.6: smooth with compact support. -/
def IsTestFun {k : ℕ} (O : (Fin k → ℝ) → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) O ∧ HasCompactSupport O

end TheoremTwoSix

end RBM

end

/-! ### From `RBM1D/Flow/OUMarginalGaussian.lean` -/

section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal ComplexConjugate

namespace RBM.Gauss

/-- The number of rows and columns at the paper's matrix size `M`.  This is definitionally
`(Gauss.band d).size N = L N * W N`; in particular it is positive even at parameter `N = 0`. -/
def ouMatrixSize (d : Dims) (N : ℕ) : ℕ := d.L N * d.W N

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

end RBM.Gauss

end

/-! ### From `RBM1D/Flow/DBMInput.lean` -/

section

open MeasureTheory Filter Matrix Topology

namespace RBM.Gauss

variable (d : Dims)

/-- The matrix size `M = L W` as a real number. -/
noncomputable def msize (N : ℕ) : ℝ := (ouMatrixSize d N : ℝ)

/-- `∫ O(α) ρ^{(k)}_{GUE}(E + α/M) dα` for the GUE matrix `H_∞` (size `M = L W`,
`E|h_ij|² = 1/M`). -/
noncomputable def gueMatPairing (N k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ) : ℝ :=
  RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k O E

/-- `∫ O(α) ρ^{(k)}_H(E + α/M) dα` for the band matrix `H`. -/
noncomputable def bandPairing (N k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ) : ℝ :=
  RBM.corrPairing (P d) (Xmat d N) (Xmat_isHermitian d N) k O E

/-- **(2.18) against the GUE matrix model**. -/
def BulkUniversalityMat (κ : ℝ) : Prop :=
  ∀ E : ℝ, |E| ≤ 2 - κ → ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, RBM.IsTestFun O →
    Tendsto (fun N => bandPairing d N k O E - gueMatPairing d N k O E) atTop (𝓝 0)

/-- `m_V(z) = N^{-1} ∑_i (v_i - z)^{-1}`, the Stieltjes transform of the diagonal matrix `V`. -/
noncomputable def stieltjesVec {n : Type*} [Fintype n] (v : n → ℝ) (z : ℂ) : ℂ :=
  (Fintype.card n : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z)⁻¹

/-- **[51, Definition 2.1]**: `V = diag v` is `(g,G)`-regular, (2.2) and (2.3). -/
def IsRegular51 {n : Type*} [Fintype n] (v : n → ℝ) (g G c C CV : ℝ) : Prop :=
  (∀ E η : ℝ, |E| ≤ G → g ≤ η → η ≤ 10 →
      c ≤ (stieltjesVec v ⟨E, η⟩).im ∧ (stieltjesVec v ⟨E, η⟩).im ≤ C) ∧
    ∀ i, |v i| ≤ (Fintype.card n : ℝ) ^ CV

/-- **[51, (2.5)]**: `m` solves the free-convolution equation on the upper half plane, with
`Im m > 0`. -/
def IsFreeConv51 {n : Type*} [Fintype n] (v : n → ℝ) (t : ℝ) (m : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → 0 < (m z).im ∧
    m z = (Fintype.card n : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m z)⁻¹

/-- **[51, (2.1)]** with GOE → GUE: `H_t = V + √t W`, `V = diag v`, `W = Xmat` (under
`gueMeasure`, the standard GUE). -/
noncomputable def dbmMatrix (N : ℕ) (v : d.Idx N → ℝ) (t : ℝ) (ω : Ω d) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  Matrix.diagonal (fun i => (v i : ℂ)) + (Real.sqrt t : ℂ) • Xmat d N ω

theorem dbmMatrix_isHermitian (N : ℕ) (v : d.Idx N → ℝ) (t : ℝ) (ω : Ω d) :
    (dbmMatrix d N v t ω).IsHermitian := by
  unfold dbmMatrix
  refine Matrix.IsHermitian.add ?_ ?_
  · exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      ext i; simp [Pi.star_apply])
  · have hX := Xmat_isHermitian d N ω
    unfold Matrix.IsHermitian at hX ⊢
    rw [Matrix.conjTranspose_smul, hX]
    simp

/-- **[51, (2.4)]** (= the paper's semicircle density): `ρ_sc(E) = (2π)^{-1} 1_{|E|≤2} √(4-E²)`. -/
noncomputable def rhoSc (E : ℝ) : ℝ :=
  if |E| ≤ 2 then Real.sqrt (4 - E ^ 2) / (2 * Real.pi) else 0

end RBM.Gauss

end

/-! ### From `RBM1D/Flow/DBMInputNorm.lean` -/

section

open MeasureTheory Filter Matrix Topology

namespace RBM.Gauss

variable (d : Dims)

/-- **[51, Theorem 2.2] at unit density.** The premises are those of [51, Theorem 2.2]. The
conclusion is (2.9) with the factors `ρ_fc^{-k}`, `ρ_sc^{-k}` (`docs/PAPER-VS-LEAN.md` §4.2):
equivalently, the test function is dilated by each side's own density. -/
def LSY22' : Prop :=
  ∀ (δ σ q c C CV : ℝ), 0 < δ → 0 < σ → 0 < q → q < 1 → 0 < c →
  ∀ (g G t E : ℕ → ℝ) (v : ∀ N, d.Idx N → ℝ) (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ),
    (∀ᶠ N in atTop,
      msize d N ^ δ / msize d N ≤ g N ∧ g N ≤ msize d N ^ (-δ) ∧ G N ≤ msize d N ^ (-δ) ∧
      g N * msize d N ^ σ ≤ t N ∧ t N ≤ msize d N ^ (-σ) * G N ^ 2 ∧ |E N| ≤ q * G N ∧
      IsRegular51 (v N) (g N) (G N) c C CV ∧ IsFreeConv51 (v N) (t N) (m N) ∧
      Tendsto (fun η : ℝ => (m N ⟨E N, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρ N))) →
    ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, RBM.IsTestFun O →
      Tendsto (fun N =>
        RBM.corrPairing (gueMeasure d N) (dbmMatrix d N (v N) (t N))
            (dbmMatrix_isHermitian d N (v N) (t N)) k (fun β => O (fun j => ρ N * β j)) (E N) -
          RBM.corrPairing (gueMeasure d N) (Xmat d N) (Xmat_isHermitian d N) k
            (fun β => O (fun j => rhoSc (E N) * β j)) (E N))
        atTop (𝓝 0)

end RBM.Gauss

end

