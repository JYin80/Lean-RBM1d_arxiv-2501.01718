/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Generator
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The quadratic variation of (5.25), and the resolvent's global `C²` bounds

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2.  This file belongs to the **moment route** for the stochastic layer: it
identifies the second-order term of the generator identity of `RBM1D/Gauss/Generator.lean`
with the quadratic variation of (5.25), and bounds the resolvent and its first two derivatives
on the whole matrix space.

## The pivot

With `Φ = |F|^{2p}` the generator identity's second-order term splits as

  `d/du E|F_u|^{2p} = 2p Re E[|F|^{2p-2} F̄ 𝓛F] + ∑_α S_α E[|F|^{2p-2}(2p(p-1)Re(F̄∂_αF)²/|F|²
        + p ‖∂_αF‖²)]`,

and after `Re(F̄∂_αF)² ≤ ‖F‖²‖∂_αF‖²` the second term is at most
`p(2p-1) E[|F|^{2p-2} ∑_α S_α‖∂_αF‖²]`.  The coefficient `∑_α S_α ‖∂_αF‖²` is **exactly** the
quadratic variation of (5.25):

  `∑_{α ∈ usedCoord} S_α ‖∂_α F‖² = ∑_{i,j} |E^{(M)}(α)|²`,  `E^{(M)}(α) = (S_ij)^{1/2} ∂_{H_ij}F`

(`secondOrder_eq_quadVar`).  Since the paper's `U_{u,t,σ}` is a *deterministic linear*
operator, taking `F := fun M => (U ∘ L(M))_a` makes the right-hand side literally the
integrand of (5.25), i.e. the right-hand side of BDG (5.24).

## Main definitions

* `RBM.Gauss.wirtFirst` — `∂_{M_ij}F` in the Wirtinger convention (the first-derivative
  companion of `RBM.Gauss.wirtSecond`).
* `RBM.Gauss.EmartCoeff` — `E^{(M)}_{t,σ,a}(α) = (S_ij)^{1/2} ∂_{(H_t)_ij} F` of §5.2.
* `RBM.Gauss.quadVar` / `RBM.Gauss.quadVarPairs` — the two sides of the fulcrum: the
  coordinate sum `∑_α S_α‖∂_αF‖²` and the paper's `∑_α |E^{(M)}(α)|²`.
* `RBM.Gauss.genD` — `𝓛F = ½ ∑_α S_α ∂_α²F`.
* `RBM.Gauss.BddC2` — `C²` with globally bounded value, first and second derivative.
* `RBM.Gauss.resH` — the resolvent pre-composed with the Hermitian projection `hermCLM`.

## Main results

* **`RBM.Gauss.secondOrder_eq_quadVar`** — the fulcrum, see above.
* `RBM.Gauss.norm_resH_le`, `RBM.Gauss.norm_fderiv_resH_le`, `RBM.Gauss.norm_fderiv2_resH_le`
  — `‖G‖ ≤ η⁻¹`, `‖∂G‖ ≤ η⁻²`, `‖∂²G‖ ≤ 2η⁻³`, **on the whole matrix space**, so no good event
  is needed; `RBM.Gauss.contDiff_resH` — `resH` is `C²`.

## Deviations from the paper

* The flow is `H_u = √u X`, not a Brownian motion (`docs/PAPER-VS-LEAN.md` §5.1);
  in particular `𝓛` here is the generator of that flow, not an Itô differential.
* `E^{(M)}(α)` is defined here with `∂_{H_ij}` in the Wirtinger convention (`wirtFirst`),
  matching `RBM.Gauss.wirtSecond`; the paper writes `∂_{(H_t)_ij}` without fixing a
  convention.
* The paper states (5.25) after a Schwarz inequality that splits `E^{(M)}(α)` into its `n`
  edge terms `E^{(M)}(α, k)` (cost `C_n`).  `secondOrder_eq_quadVar` is the identity
  *before* that split, i.e. `∑_α |E^{(M)}(α)|²`; the `∑_k` form of (5.25) follows from it by
  the same Schwarz step, which is not formalized here.
* `secondOrder_eq_quadVar` is stated for a function `F` of the matrix, not for the loop
  observable `L_{t,σ,a}`.
* `BddC2` asks for *global* bounds, which is stronger than anything the paper states and is
  legitimate exactly because of the global resolvent bound `‖G‖ ≤ η⁻¹`.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator NNReal

/-! ### Directional derivatives along a line -/

section LineDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The affine line `s ↦ M + s • B` (with the **real** scalar action) has derivative `B`. -/
theorem hasDerivAt_lineShift (M B : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + s • B) B t := by
  simpa using ((hasDerivAt_id t).smul_const B).const_add M

/-- The first directional derivative, read along the line `s ↦ M + s • B`. -/
theorem hasDerivAt_dir {F : E → V} (hF : ContDiff ℝ 1 F) (M B : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (M + s • B)) (fderiv ℝ F (M + t • B) B) t := by
  have h := ((hF.differentiable one_ne_zero (M + t • B)).hasFDerivAt).comp_hasDerivAt t
    (hasDerivAt_lineShift M B t)
  simpa [Function.comp_def] using h

/-- **The mixed second directional derivative**, read along the line `s ↦ M + s • B` at
`t = 0` with the first slot frozen at `A`. -/
theorem hasDerivAt_dir2' {F : E → V} (hF : ContDiff ℝ 2 F) (M A B : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ F (M + t • B) A) (fderiv ℝ (fderiv ℝ F) M B A) 0 := by
  have hd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have happ : HasFDerivAt (fun M' => fderiv ℝ F M' A)
      ((fderiv ℝ (fderiv ℝ F) M).flip A) ((fun s : ℝ => M + s • B) 0) := by
    have hc := ((hd M).hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) A M)
    simpa using hc
  have key := happ.comp_hasDerivAt (0 : ℝ) (hasDerivAt_lineShift M B 0)
  simpa [Function.comp_def] using key

end LineDeriv

section MomentFun

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mul_conj_eq (z : ℂ) : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

end MomentFun

/-! ### The fulcrum: the second-order term is the quadratic variation of (5.25) -/

section QuadVar

variable {d : Dims} {N : ℕ}

/-- **`∂_{M_ij} F` in the Wirtinger convention.**

For `i ≠ j` the entry `M_ij = a + i b` with `M_ji = conj M_ij`, and `∂_ij = (∂_a - i ∂_b)/2`;
on the diagonal `M_ii` is real and `∂_ii = ∂_a`.  This is the first-derivative companion of
`RBM.Gauss.wirtSecond`. -/
noncomputable def wirtFirst (d : Dims) (N : ℕ) (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) : ℂ :=
  if i = j then coordD1 d N F M (i, i, true)
  else (2⁻¹ : ℂ) * (coordD1 d N F M (i, j, true) - Complex.I * coordD1 d N F M (i, j, false))

/-- **`E^{(M)}_{t,σ,a}(α)` of §5.2** at `α = (i, j)`: the paper defines it as
`(S_ij)^{1/2} · ∂_{(H_t)_ij} L_{t,σ,a}`.  Here `F` plays the role of `L_{t,σ,a}` read as a
function of the matrix; because `U_{u,t,σ}` is a *deterministic linear* operator, taking
`F := fun M => (U ∘ L(M))_a` turns this into `(U ∘ E^{(M)}(α))_a`, which is the quantity
actually squared in (5.25). -/
noncomputable def EmartCoeff (d : Dims) (N : ℕ) (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) : ℂ :=
  (Real.sqrt (Sblk (d.L N) (d.W N) i j) : ℂ) * wirtFirst d N F M i j

/-- **The second-order coefficient of the generator identity**, `∑_α S_α ‖∂_α F‖²`, the sum
running over the independent Gaussian coordinates of `RBM1D/Gauss/Model.lean`. -/
noncomputable def quadVar (d : Dims) (N : ℕ) (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) * ‖coordD1 d N F M q‖ ^ 2

/-- **The quadratic-variation integrand of (5.25)**, `∑_α |E^{(M)}(α)|²`, the sum running over
the index pairs `α = (i, j)` of the paper. -/
noncomputable def quadVarPairs (d : Dims) (N : ℕ) (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  ∑ i : d.Idx N, ∑ j : d.Idx N, ‖EmartCoeff d N F M i j‖ ^ 2

theorem quadVar_nonneg (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : 0 ≤ quadVar d N F M :=
  Finset.sum_nonneg fun q _ => mul_nonneg (gvar d (crd d N q)).2 (by positivity)

/-! #### The two elementary ingredients -/

/-- The real direction is symmetric in the pair. -/
theorem coordD1_swap_true (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) :
    coordD1 d N F M (j, i, true) = coordD1 d N F M (i, j, true) := by
  show fderiv ℝ F M (Bmat d N j i true) = fderiv ℝ F M (Bmat d N i j true)
  rw [Bmat_swap_true d N i j]

/-- The imaginary direction changes sign under the swap (off the diagonal). -/
theorem coordD1_swap_false (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) {i j : d.Idx N} (hij : i ≠ j) :
    coordD1 d N F M (j, i, false) = -coordD1 d N F M (i, j, false) := by
  show fderiv ℝ F M (Bmat d N j i false) = -fderiv ℝ F M (Bmat d N i j false)
  rw [Bmat_swap_false d N hij, map_neg]

/-- **The parallelogram identity behind the fulcrum.**  The two Wirtinger derivatives
`∂_ij = (∂_a - i ∂_b)/2` and `∂_ji = (∂_a + i ∂_b)/2` of one unordered pair have squared
moduli adding up to *half* of `‖∂_a‖² + ‖∂_b‖²` — which is exactly the factor by which the
paper's sum over **ordered** pairs `(i, j)`, weighted `S_ij`, matches the coordinate sum over
**one** representative per pair, weighted `S_ij/2`. -/
theorem norm_sq_wirt_pair (x y : ℂ) :
    ‖(2⁻¹ : ℂ) * (x - Complex.I * y)‖ ^ 2 + ‖(2⁻¹ : ℂ) * (x + Complex.I * y)‖ ^ 2
      = 2⁻¹ * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hpar := parallelogram_law_with_norm ℝ x (Complex.I * y)
  have hIy : ‖Complex.I * y‖ = ‖y‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  rw [hIy] at hpar
  have hc : ‖(2⁻¹ : ℂ)‖ = 2⁻¹ := by norm_num
  rw [norm_mul, norm_mul, hc, mul_pow, mul_pow]
  nlinarith [hpar, sq_nonneg (‖x + Complex.I * y‖), sq_nonneg (‖x - Complex.I * y‖)]

/-! #### The bookkeeping lemma, in the form the fulcrum needs -/

/-- A companion of `RBM.Gauss.sum_used_eq_sum_pairs`: the coordinate sum over `usedCoord`
equals a double sum over **ordered** index pairs as soon as the diagonal terms match and the
two off-diagonal terms of each unordered pair together match the coordinate contribution. -/
theorem sum_used_eq_sum_pairs_of_swap {ι : Type*} [Fintype ι] [DecidableEq ι] {V : Type*}
    [AddCommGroup V] [Module ℝ V] (κ : ι → ℕ) (hκ : Function.Injective κ)
    (S : ι → ι → ℝ) (f : ι × ι × Bool → V) (h : ι → ι → V)
    (hdiag : ∀ i, S i i • f (i, i, true) = h i i)
    (hoff : ∀ i j, i ≠ j →
      (S i j / 2) • f (i, j, true) + (S i j / 2) • f (i, j, false) = h i j + h j i) :
    ∑ p ∈ Finset.univ.filter
        (fun p : ι × ι × Bool => κ p.1 < κ p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)),
      (if p.1 = p.2.1 then S p.1 p.2.1 else S p.1 p.2.1 / 2) • f p
      = ∑ i : ι, ∑ j : ι, h i j := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine sum_sum_eq_of_swap_add_eq _ _ ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [← hdiag i]
    simp
  · have hji : ¬ (j = i) := fun hh => hij hh.symm
    rcases lt_trichotomy (κ i) (κ j) with hlt | heq | hgt
    · simp only [hij, hji, hlt, asymm hlt, false_and, or_false, ite_true, ite_false,
        and_true, add_zero]
      exact hoff i j hij
    · exact absurd (hκ heq) hij
    · simp only [hij, hji, hgt, asymm hgt, false_and, or_false, ite_true, ite_false,
        and_true, add_zero, zero_add]
      rw [hoff j i hji, add_comm]

/-! #### The fulcrum -/

/-- **`secondOrder_eq_quadVar`: the second-order term of the generator identity *is* the
quadratic variation of (5.25).**

The left side is the coefficient that multiplies `|F|^{2p-2}` in the second-order part of
`d/du E|F(H_u)|^{2p}`; the right side is
`∑_α |E^{(M)}(α)|²`, the integrand of the quadratic variation computed in (5.25) — the
right-hand side of the BDG inequality (5.24).  Since `U_{u,t,σ}` is a deterministic linear
operator, applying this with `F := fun M => (U ∘ L(M))_a` gives (5.25) itself.

This is the identity on which the whole moment route turns: it says that replacing
Duhamel + BDG by the generator identity + Grönwall costs nothing, because the two routes have
literally the same second-order input. -/
theorem secondOrder_eq_quadVar (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    quadVar d N F M = quadVarPairs d N F M := by
  have hnorm : ∀ i j : d.Idx N,
      ‖EmartCoeff d N F M i j‖ ^ 2 = Sblk (d.L N) (d.W N) i j * ‖wirtFirst d N F M i j‖ ^ 2 := by
    intro i j
    rw [EmartCoeff, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Sblk_nonneg i j)]
  have hrhs : quadVarPairs d N F M
      = ∑ i : d.Idx N, ∑ j : d.Idx N,
          Sblk (d.L N) (d.W N) i j * ‖wirtFirst d N F M i j‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hnorm i j
  rw [hrhs, quadVar]
  have hlhs : ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) * ‖coordD1 d N F M q‖ ^ 2
      = ∑ q ∈ Finset.univ.filter
          (fun q : d.Idx N × d.Idx N × Bool =>
            idxKey d N q.1 < idxKey d N q.2.1 ∨ (q.1 = q.2.1 ∧ q.2.2 = true)),
        (if q.1 = q.2.1 then Sblk (d.L N) (d.W N) q.1 q.2.1
          else Sblk (d.L N) (d.W N) q.1 q.2.1 / 2) • ‖coordD1 d N F M q‖ ^ 2 :=
    Finset.sum_congr rfl fun q _ => by rw [gvar_crd, smul_eq_mul]
  rw [hlhs]
  refine sum_used_eq_sum_pairs_of_swap (idxKey d N) (idxKey_injective d N)
    (Sblk (d.L N) (d.W N)) _ _ (fun i => ?_) (fun i j hij => ?_)
  · rw [smul_eq_mul, wirtFirst, ite_eq_left rfl]
  · have hwij : wirtFirst d N F M i j
        = (2⁻¹ : ℂ) * (coordD1 d N F M (i, j, true)
            - Complex.I * coordD1 d N F M (i, j, false)) := by
      rw [wirtFirst, ite_eq_right hij]
    have hwji : wirtFirst d N F M j i
        = (2⁻¹ : ℂ) * (coordD1 d N F M (i, j, true)
            + Complex.I * coordD1 d N F M (i, j, false)) := by
      rw [wirtFirst, ite_eq_right (Ne.symm hij), coordD1_swap_true, coordD1_swap_false F M hij]
      ring
    rw [hwij, hwji, Sblk_comm (d.L N) (d.W N) j i, smul_eq_mul, smul_eq_mul]
    have key := norm_sq_wirt_pair (coordD1 d N F M (i, j, true)) (coordD1 d N F M (i, j, false))
    linear_combination (-(Sblk (d.L N) (d.W N) i j)) * key

end QuadVar

/-! ### The second-order term of `d/du E|F|^{2p}` -/

section MomentSecondOrder

variable {d : Dims} {N : ℕ} {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- **`𝓛F := ½ ∑_α S_α ∂_α² F`**, the generator of the moment route applied to `F` itself.
(For `Φ = |F|^{2p}` the generator identity gives `d/du E[Φ(H_u)] = E[(𝓛Φ)(H_u)]`, and the
first term of the expansion of `𝓛Φ` is the one built out of `𝓛F`.) -/
noncomputable def genD (d : Dims) (N : ℕ) (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  (2⁻¹ : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) • coordD2 d N F M q

end MomentSecondOrder

section MomentGenerator

variable {d : Dims} {N : ℕ} {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {p : ℕ}

end MomentGenerator

section Gronwall

variable {d : Dims} {N : ℕ} {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {p : ℕ}

end Gronwall

/-! ### Globally bounded `C²` functions -/

section TestFunBuild

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **What `TestFun` asks of the inner function `F`**: `C²` with globally bounded value, first
and second derivative.  This is `RBM.Gauss.TestFun` transported to `F`; the resolvent
observables of the moment route satisfy it, thanks to the global bound `‖G‖ ≤ η⁻¹`. -/
structure BddC2 (F : E → ℂ) : Prop where
  /-- `F` is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 F
  /-- `F` is globally bounded. -/
  bdd₀ : ∃ C : ℝ, ∀ M, ‖F M‖ ≤ C
  /-- `DF` is globally bounded. -/
  bdd₁ : ∃ C : ℝ, ∀ M, ‖fderiv ℝ F M‖ ≤ C
  /-- `D²F` is globally bounded. -/
  bdd₂ : ∃ C : ℝ, ∀ M, ‖fderiv ℝ (fderiv ℝ F) M‖ ≤ C

end TestFunBuild

/-! ### The concrete `F`: a linear observable of the resolvent -/

section ResolventC2

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `‖(A + Aᴴ)/2‖ ≤ ‖A‖`: the Hermitian projection is a contraction (the `ℓ² → ℓ²` operator
norm is a C*-norm, so `‖Aᴴ‖ = ‖A‖`). -/
theorem norm_hermCLM_le (A : Matrix n n ℂ) : ‖hermCLM n A‖ ≤ ‖A‖ := by
  rw [hermCLM_apply, norm_smul]
  have h1 : ‖Matrix.conjTranspose A‖ = ‖A‖ := norm_star A
  have h2 := norm_add_le A (Matrix.conjTranspose A)
  rw [h1] at h2
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2⁻¹ : ℝ))]
  linarith

/-- A five-factor product monotonicity step (all factors nonnegative). -/
theorem mul5_le {a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 : ℝ}
    (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) (h4 : a4 ≤ b4) (h5 : a5 ≤ b5)
    (n1 : 0 ≤ a1) (n2 : 0 ≤ a2) (n3 : 0 ≤ a3) (n4 : 0 ≤ a4) (n5 : 0 ≤ a5) :
    a1 * a2 * a3 * a4 * a5 ≤ b1 * b2 * b3 * b4 * b5 := by
  have m1 : 0 ≤ b1 := le_trans n1 h1
  have m2 : 0 ≤ b2 := le_trans n2 h2
  have m3 : 0 ≤ b3 := le_trans n3 h3
  have m4 : 0 ≤ b4 := le_trans n4 h4
  exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1 h2 n2 m1) h3 n3
    (mul_nonneg m1 m2)) h4 n4 (mul_nonneg (mul_nonneg m1 m2) m3)) h5 n5
    (mul_nonneg (mul_nonneg (mul_nonneg m1 m2) m3) m4)

/-- **`G_z` pre-composed with the Hermitian projection**: globally defined and `C^∞`, and
equal to the Green function at every Hermitian matrix (`hermCLM_of_isHermitian`).  This is the
fix flagged in `RBM1D/Gauss/Generator.lean`: `(M - z)⁻¹` is not defined for every `M`. -/
noncomputable def resH (z : ℂ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  Ring.inverse (hermCLM n M - z • (1 : Matrix n n ℂ))

theorem resH_eq_green (z : ℂ) (M : Matrix n n ℂ) : resH z M = green (hermCLM n M) z := by
  show Ring.inverse (hermCLM n M - z • (1 : Matrix n n ℂ))
    = (hermCLM n M - z • (1 : Matrix n n ℂ))⁻¹
  rw [Matrix.nonsing_inv_eq_ringInverse]

theorem resH_of_isHermitian {z : ℂ} {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    resH z M = green M z := by
  rw [resH_eq_green, hermCLM_of_isHermitian hM]

theorem isUnit_resH_arg {z : ℂ} (hz : z.im ≠ 0) (M : Matrix n n ℂ) :
    IsUnit (hermCLM n M - z • (1 : Matrix n n ℂ)) :=
  isUnit_sub_smul_one_of_im_ne_zero (isHermitian_hermCLM M) hz

/-- **The global bound `‖G‖ ≤ η⁻¹`, for `resH`** — on the whole matrix space. -/
theorem norm_resH_le {z : ℂ} {η : ℝ} (hη : 0 < η) (hzη : η ≤ |z.im|) (M : Matrix n n ℂ) :
    ‖resH z M‖ ≤ η⁻¹ := by
  rw [resH_eq_green]
  exact norm_green_le (isHermitian_hermCLM M) hη hzη

theorem contDiff_resH {z : ℂ} (hz : z.im ≠ 0) : ContDiff ℝ 2 (resH (n := n) z) := by
  rw [contDiff_iff_contDiffAt]
  intro M
  have hT : ContDiff ℝ 2 fun M' : Matrix n n ℂ => hermCLM n M' - z • (1 : Matrix n n ℂ) :=
    (hermCLM n).contDiff.sub contDiff_const
  obtain ⟨u, hus⟩ : ∃ u : (Matrix n n ℂ)ˣ,
      (u : Matrix n n ℂ) = hermCLM n M - z • (1 : Matrix n n ℂ) :=
    ⟨(isUnit_resH_arg hz M).unit, IsUnit.unit_spec _⟩
  have hg : ContDiffAt ℝ 2 (Ring.inverse (M₀ := Matrix n n ℂ))
      ((fun M' : Matrix n n ℂ => hermCLM n M' - z • (1 : Matrix n n ℂ)) M) := by
    show ContDiffAt ℝ 2 _ (hermCLM n M - z • (1 : Matrix n n ℂ))
    rw [← hus]
    exact contDiffAt_ringInverse ℝ u
  exact hg.comp M hT.contDiffAt

theorem hasFDerivAt_resH {z : ℂ} (hz : z.im ≠ 0) (M : Matrix n n ℂ) :
    HasFDerivAt (resH z)
      (-((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (resH z M) (resH z M)).comp
        (hermCLM n))) M := by
  obtain ⟨u, hus⟩ : ∃ u : (Matrix n n ℂ)ˣ,
      (u : Matrix n n ℂ) = hermCLM n M - z • (1 : Matrix n n ℂ) :=
    ⟨(isUnit_resH_arg hz M).unit, IsUnit.unit_spec _⟩
  have hinv : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = resH z M := by
    rw [resH, ← hus, Ring.inverse_unit]
  have hT : HasFDerivAt (fun M' : Matrix n n ℂ => hermCLM n M' - z • (1 : Matrix n n ℂ))
      (hermCLM n) M := (hermCLM n).hasFDerivAt.sub_const _
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹) ↑u⁻¹))
      ((fun M' : Matrix n n ℂ => hermCLM n M' - z • (1 : Matrix n n ℂ)) M) := by
    show HasFDerivAt _ _ (hermCLM n M - z • (1 : Matrix n n ℂ))
    rw [← hus]
    exact hasFDerivAt_ringInverse u
  have key := hF.comp M hT
  rw [hinv] at key
  have hcomp : (Ring.inverse (M₀ := Matrix n n ℂ))
      ∘ (fun M' : Matrix n n ℂ => hermCLM n M' - z • (1 : Matrix n n ℂ)) = resH z := rfl
  rw [hcomp, ContinuousLinearMap.neg_comp] at key
  exact key

/-- `∂_A G = -G (A + Aᴴ)/2 G`. -/
theorem fderiv_resH_apply {z : ℂ} (hz : z.im ≠ 0) (M A : Matrix n n ℂ) :
    fderiv ℝ (resH z) M A = -(resH z M * hermCLM n A * resH z M) := by
  rw [(hasFDerivAt_resH hz M).fderiv]
  simp [ContinuousLinearMap.mulLeftRight_apply]

/-- `∂_B ∂_A G = G B' G A' G + G A' G B' G` with `X' = (X + Xᴴ)/2`. -/
theorem fderiv2_resH_apply {z : ℂ} (hz : z.im ≠ 0) (M A B : Matrix n n ℂ) :
    fderiv ℝ (fderiv ℝ (resH z)) M B A
      = resH z M * hermCLM n B * resH z M * hermCLM n A * resH z M
        + resH z M * hermCLM n A * resH z M * hermCLM n B * resH z M := by
  have hcd : ContDiff ℝ 2 (resH (n := n) z) := contDiff_resH hz
  have hzero : M + (0 : ℝ) • B = M := by simp
  have hlhs : HasDerivAt (fun t : ℝ => fderiv ℝ (resH z) (M + t • B) A)
      (fderiv ℝ (fderiv ℝ (resH z)) M B A) 0 := hasDerivAt_dir2' hcd M A B
  have hrd : HasDerivAt (fun t : ℝ => resH z (M + t • B))
      (-(resH z M * hermCLM n B * resH z M)) 0 := by
    have h := hasDerivAt_dir (hcd.of_le (by norm_num)) M B 0
    rw [hzero, fderiv_resH_apply hz M B] at h
    exact h
  have hfun : (fun t : ℝ => fderiv ℝ (resH z) (M + t • B) A)
      = fun t : ℝ => -(resH z (M + t • B) * hermCLM n A * resH z (M + t • B)) :=
    funext fun t => fderiv_resH_apply hz (M + t • B) A
  rw [hfun] at hlhs
  have hprod := ((hrd.mul (hasDerivAt_const (0 : ℝ) (hermCLM n A))).mul hrd).neg
  have hkey := hlhs.unique hprod
  rw [hkey]
  simp only [Pi.mul_apply, hzero]
  noncomm_ring

theorem norm_fderiv_resH_le {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    (M : Matrix n n ℂ) : ‖fderiv ℝ (resH z) M‖ ≤ η⁻¹ * η⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
  rw [fderiv_resH_apply hz M A, norm_neg]
  have hR := norm_resH_le hη hzη M
  have hL := norm_hermCLM_le A
  calc ‖resH z M * hermCLM n A * resH z M‖
      ≤ ‖resH z M * hermCLM n A‖ * ‖resH z M‖ := norm_mul_le _ _
    _ ≤ ‖resH z M‖ * ‖hermCLM n A‖ * ‖resH z M‖ := by
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ η⁻¹ * ‖A‖ * η⁻¹ := by
        have h0 : (0 : ℝ) ≤ η⁻¹ := by positivity
        exact mul_le_mul (mul_le_mul hR hL (norm_nonneg _) h0) hR (norm_nonneg _)
          (by positivity)
    _ = η⁻¹ * η⁻¹ * ‖A‖ := by ring

theorem norm_fderiv2_resH_le {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    (M : Matrix n n ℂ) : ‖fderiv ℝ (fderiv ℝ (resH z)) M‖ ≤ 2 * (η⁻¹ * η⁻¹ * η⁻¹) := by
  have h0 : (0 : ℝ) ≤ η⁻¹ := by positivity
  have hR := norm_resH_le hη hzη M
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun B => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
  rw [fderiv2_resH_apply hz M A B]
  -- each of the two products of five factors is at most `η⁻³ ‖A‖ ‖B‖`
  have hfive : ∀ X Y : Matrix n n ℂ,
      ‖resH z M * hermCLM n X * resH z M * hermCLM n Y * resH z M‖
        ≤ η⁻¹ * η⁻¹ * η⁻¹ * (‖X‖ * ‖Y‖) := by
    intro X Y
    have e : ‖resH z M * hermCLM n X * resH z M * hermCLM n Y * resH z M‖
        ≤ ‖resH z M‖ * ‖hermCLM n X‖ * ‖resH z M‖ * ‖hermCLM n Y‖ * ‖resH z M‖ := by
      calc ‖resH z M * hermCLM n X * resH z M * hermCLM n Y * resH z M‖
          ≤ ‖resH z M * hermCLM n X * resH z M * hermCLM n Y‖ * ‖resH z M‖ := norm_mul_le _ _
        _ ≤ ‖resH z M * hermCLM n X * resH z M‖ * ‖hermCLM n Y‖ * ‖resH z M‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ ‖resH z M * hermCLM n X‖ * ‖resH z M‖ * ‖hermCLM n Y‖ * ‖resH z M‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
        _ ≤ ‖resH z M‖ * ‖hermCLM n X‖ * ‖resH z M‖ * ‖hermCLM n Y‖ * ‖resH z M‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
              (norm_nonneg _)) (norm_nonneg _)
    refine le_trans e ?_
    have key := mul5_le hR (norm_hermCLM_le X) hR (norm_hermCLM_le Y) hR
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    calc ‖resH z M‖ * ‖hermCLM n X‖ * ‖resH z M‖ * ‖hermCLM n Y‖ * ‖resH z M‖
        ≤ η⁻¹ * ‖X‖ * η⁻¹ * ‖Y‖ * η⁻¹ := key
      _ = η⁻¹ * η⁻¹ * η⁻¹ * (‖X‖ * ‖Y‖) := by ring
  calc ‖resH z M * hermCLM n B * resH z M * hermCLM n A * resH z M
          + resH z M * hermCLM n A * resH z M * hermCLM n B * resH z M‖
      ≤ ‖resH z M * hermCLM n B * resH z M * hermCLM n A * resH z M‖
        + ‖resH z M * hermCLM n A * resH z M * hermCLM n B * resH z M‖ := norm_add_le _ _
    _ ≤ η⁻¹ * η⁻¹ * η⁻¹ * (‖B‖ * ‖A‖) + η⁻¹ * η⁻¹ * η⁻¹ * (‖A‖ * ‖B‖) :=
        add_le_add (hfive B A) (hfive A B)
    _ = 2 * (η⁻¹ * η⁻¹ * η⁻¹) * ‖B‖ * ‖A‖ := by ring

end ResolventC2

end RBM.Gauss

