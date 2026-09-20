/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Model
import RBM1D.Loop.Continuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The generator identity of the moment route (T71)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*.  This file is the analytic core of the **moment route** for the stochastic layer
(project note `claude/moment-route-plan.md`): with the flow realized as `H_u = √u • X`
(`RBM1D/Gauss/Model.lean`, T69), the identity

  `∂_u E[Φ(H_u)] = ½ ∑_{ij} S_ij E[∂_ij ∂_ji Φ(H_u)]`

replaces Itô's formula.  Together with Grönwall (T72) it replaces Duhamel + BDG.

## The two ingredients

1. **Differentiation under the integral sign.**  `Φ(H_u) = Φ(√u • X)` and
   `d/du = (2√u)⁻¹ ∂_X`, so `∂_u E[Φ(H_u)] = (2√u)⁻¹ ∑_α E[ω_α ∂_α Φ(H_u)]`, the sum running
   over the *independent Gaussian coordinates* `α` of T69.
2. **Stein's identity**, applied to each coordinate: `E[ω_α g] = gvar_α E[∂_α g]`.  Moving the
   coordinate `α` moves the matrix argument by `√u • Bmat α`, so `∂_α` of `∂_α Φ(H_u)` is
   `√u ∂_α ∂_α Φ(H_u)`, and the `√u` cancels the `(2√u)⁻¹`.  The result is
   `½ ∑_α gvar_α E[∂_α ∂_α Φ(H_u)]`, which is `hasDerivAt_integral_Phi`.

The `∑_{ij} S_ij` form of the paper is `hasDerivAt_integral_Phi_pairs`: the coordinate sum and
the index-pair sum agree once `∂_ij`, `∂_ji` are read in the Wirtinger convention, see
`wirtSecond`.

## The indexing convention (verbatim from `RBM1D/Gauss/Model.lean`)

`idxKey d N (a, α) = W · a.val + α`; "`i < j`" always means `idxKey i < idxKey j`;
`Coord d = Σ N, Idx × Idx × Bool` with `true` the real part and `false` the imaginary part;
`gvar ⟨N,i,j,b⟩ = S_ij` for `i = j` and `S_ij / 2` otherwise, the same for both tags.
The coordinates *read* by `Xentry` are exactly `usedCoord d N`: the pairs with
`idxKey i < idxKey j` with both tags, plus the diagonal pairs with the real tag.  Every sum
over coordinates in this file is restricted to `usedCoord`; the redundant coordinates
(`idxKey j < idxKey i`, and the diagonal imaginary tags) never occur.

## Main definitions

* `RBM.Gauss.Bmat d N i j b` — the fixed Hermitian matrix direction attached to the
  coordinate `⟨N, i, j, b⟩`: `E_ij + E_ji` for the real tag, `I E_ij - I E_ji` for the
  imaginary tag, `E_ii` on the diagonal.
* `RBM.Gauss.usedCoord d N` — the coordinates actually read by `Xentry`.
* `RBM.Gauss.coordD1`, `RBM.Gauss.coordD2` — the first and second directional derivatives of
  `Φ` along `Bmat`.
* `RBM.Gauss.wirtSecond` — `∂_ij ∂_ji Φ` in the Wirtinger convention, i.e.
  `(∂_a² + ∂_b²)/4` off the diagonal and `∂_a²` on it.
* `RBM.Gauss.hermCLM` — the `ℝ`-linear projection onto the Hermitian matrices.
* `RBM.Gauss.TestFun` — the class of admissible `Φ`: `C²` with globally bounded value, first
  and second derivative.
* `RBM.Gauss.MatrixStein` — **the hypothesis owed by T70** (see below).

## Main results

* `RBM.Gauss.Xmat_eq_sum` : `X = ∑_{α ∈ usedCoord} ω_α • Bmat α` — the coordinate
  decomposition; `RBM.Gauss.Xmat_update` : `X` is affine in each coordinate with slope
  `Bmat α`; `RBM.Gauss.Bmat_isHermitian`.
* `RBM.Gauss.norm_green_le` : **`‖G‖ ≤ η⁻¹` on the whole space** for Hermitian `H` and
  `|Im z| ≥ η > 0` (`ℓ² → ℓ²` operator norm); `RBM.Gauss.norm_iteratedDeriv_green_le` :
  **every derivative of order `k` of `s ↦ G(M + sA)` is bounded globally by
  `k! η^{-(k+1)} ‖A‖^k`**.  This is the "global bound" that makes every domination hypothesis
  downstream a constant.
* `RBM.Gauss.hasDerivAt_Phi_Hflow` : `d/du Φ(H_u) = (2√u)⁻¹ ∂_X Φ(H_u)`, pathwise.
* `RBM.Gauss.hasDerivAt_coordD1_update` : `∂_α [∂_α Φ(H_u)] = √u · ∂_α ∂_α Φ(H_u)`.
* `RBM.Gauss.hasDerivAt_integral_Phi` : **the generator identity, coordinate form** —
  `∂_u E[Φ(H_u)] = ½ ∑_{α ∈ usedCoord} gvar_α E[∂_α ∂_α Φ(H_u)]`, for `u > 0`.
  This is the form T72 consumes: its right-hand side is literally the quadratic variation
  of (5.25).
* `RBM.Gauss.hasDerivAt_integral_Phi_pairs` : **the paper's form** —
  `∂_u E[Φ(H_u)] = ½ ∑_i ∑_j S_ij E[∂_ij ∂_ji Φ(H_u)]`.

## Hypotheses (nothing here is an `axiom`)

* `RBM.Gauss.MatrixStein d` — Gaussian integration by parts for one coordinate of `P d`,
  in the exact form used here.  **T70 owes this.**  Its one field is
  `∫ ω, ω c • g ω ∂P = gvar c • ∫ ω, g' ω ∂P` for `g, g' : Ω d → ℂ` continuous and globally
  bounded with `g'` the partial derivative of `g` in the coordinate `c`
  (`HasDerivAt (fun t => g (Function.update ω c t)) (g' ω) (ω c)`), and both reading only
  finitely many coordinates (`RBM.Gauss.FinDep`, so that `P_map_restrict` reduces the
  infinite product to a `Measure.pi`).  This *is* the real /
  imaginary split of `E[X_ij F(X)] = S_ij E[∂_ji F(X)]`: the two tags of the pair `(i,j)`
  carry variance `S_ij/2` each off the diagonal and `S_ij` on it, so the two coordinate
  identities add up to the matrix one.  T70's one-dimensional
  `RBM.integral_mul_gaussianReal` plus a Fubini over `P_map_restrict` should give it.
* `RBM.Gauss.TestFun d N Φ` — the regularity and global bounds on `Φ`.  For the only `Φ` we
  ever use, `Φ = |F|^{2p}` with `F` a polynomial in `G`, these come from `norm_green_le` and
  `norm_iteratedDeriv_green_le`; **assembling them for a concrete `F` is T72's job**, and is
  not done here.  Note that `(M - z)⁻¹` is *not* defined for every matrix `M`, only near the
  Hermitian ones; `RBM.Gauss.hermCLM`, the `ℝ`-linear projection `M ↦ (M + Mᴴ)/2`, is
  provided precisely so that `Φ := (|F ∘ G|^{2p}) ∘ hermCLM` is globally defined and `C^∞`
  without changing any value or directional derivative we use (all base points and all
  directions `Bmat` on used coordinates are Hermitian — `Bmat_isHermitian`).
* `u > 0` is required (the chain rule factor `(2√u)⁻¹` blows up at `u = 0`); the paper's
  hierarchy is only ever used for `u > 0`.

## Deviations from the paper (for `docs/paper-deltas.md`)

* The flow is `H_u = √u X`, not a Brownian motion — the T69 delta, inherited.
* `∂_ij ∂_ji` is *defined* here (`wirtSecond`) as the Wirtinger second derivative written out
  in the two real directions.  The paper writes `∂_ij ∂_ji` without saying which convention;
  the one used here is the only one for which the identity is true, and it is the standard
  one for Hermitian matrix ensembles.
* The sum on the right of the paper's identity runs over all ordered pairs `(i, j)`; the
  coordinate form sums instead over `usedCoord`.  The two agree
  (`sum_used_eq_sum_pairs_coordD2`), with the diagonal counted once and each off-diagonal
  pair twice.
* `TestFun` asks for *global* bounds on `Φ`, `DΦ`, `D²Φ`, which is stronger than anything the
  paper states, and is legitimate exactly because of `norm_green_le`.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

/-! ### The global resolvent bound

This section is the *domination engine* of the whole moment route.  Every `Φ` we feed to the
generator identity is a polynomial expression in `G = (H - z)⁻¹` with `Im z ≥ η > 0`, and the
point is that `‖G‖ ≤ η⁻¹` holds **on the whole matrix space**, not on a good event: the
resolvent of a Hermitian matrix is bounded by the distance to the real axis, period.  Hence
every derivative of `G` along a Hermitian direction is bounded globally as well, by
`k! η^{-(k+1)} ‖A‖^k`, and the domination hypotheses of
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are discharged by constants.

The norm is the `ℓ² → ℓ²` operator norm (`Matrix.Norms.L2Operator`), the only one for which
`η⁻¹` is the right constant. -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The imaginary part of `⟪v, H v⟫` vanishes for a Hermitian matrix `H`. -/
theorem im_inner_toEuclideanCLM_self {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (v : EuclideanSpace ℂ n) :
    (⟪v, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H v⟫_ℂ).im = 0 := by
  have := hH.im_star_dotProduct_mulVec_self (WithLp.ofLp v)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct_comm] using this

/-- The quantitative lower bound `|Im z| ‖v‖ ≤ ‖(H - z) v‖` for Hermitian `H`.  This is the
whole content of `‖(H - z)⁻¹‖ ≤ |Im z|⁻¹`. -/
theorem abs_im_mul_norm_le_norm_sub_smul_one {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ)
    (v : EuclideanSpace ℂ n) :
    |z.im| * ‖v‖ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (H - z • (1 : Matrix n n ℂ)) v‖ := by
  set T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (H - z • (1 : Matrix n n ℂ)) with hT
  have hTv : T v = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H v - z • v := by
    simp [hT, map_sub, map_smul]
  have hinner : ⟪v, T v⟫_ℂ
      = ⟪v, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H v⟫_ℂ - z * ⟪v, v⟫_ℂ := by
    rw [hTv, inner_sub_right, inner_smul_right]
  have hvv_im : (⟪v, v⟫_ℂ).im = 0 := by
    simpa [RCLike.im_to_complex] using inner_self_im (𝕜 := ℂ) v
  have hvv_re : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
    simpa [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) v
  have him : (⟪v, T v⟫_ℂ).im = -(z.im * ‖v‖ ^ 2) := by
    rw [hinner, Complex.sub_im, Complex.mul_im, hvv_im, hvv_re,
      im_inner_toEuclideanCLM_self hH v]
    ring
  have hcs : ‖⟪v, T v⟫_ℂ‖ ≤ ‖v‖ * ‖T v‖ := norm_inner_le_norm v (T v)
  have h1 : |z.im| * ‖v‖ ^ 2 ≤ ‖v‖ * ‖T v‖ := by
    refine le_trans ?_ hcs
    have hle := Complex.abs_im_le_norm ⟪v, T v⟫_ℂ
    rw [him] at hle
    calc |z.im| * ‖v‖ ^ 2 = |(-(z.im * ‖v‖ ^ 2))| := by
          rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖ ^ 2)]
      _ ≤ _ := hle
  rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
  · simp [← hv]
  · exact (mul_le_mul_iff_of_pos_left hv).mp
      (by linarith [h1] : ‖v‖ * (|z.im| * ‖v‖) ≤ ‖v‖ * ‖T v‖)

/-- **`‖G‖ ≤ η⁻¹` on the whole space.**  For Hermitian `H` and `|Im z| ≥ η > 0` the Green
function `G = (H - z)⁻¹` of `RBM1D/Delocalization.lean` is bounded by `η⁻¹`, with no
exceptional set. -/
theorem norm_green_le {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) : ‖green H z‖ ≤ η⁻¹ := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  set A : Matrix n n ℂ := H - z • (1 : Matrix n n ℂ) with hA
  have hAu : IsUnit A := isUnit_sub_smul_one_of_im_ne_zero hH hzim
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAu
  show ‖A⁻¹‖ ≤ η⁻¹
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  set w := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A⁻¹ v with hw
  have hAw : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A w = v := by
    have hmul : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
        * Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A⁻¹ = 1 := by
      rw [← map_mul, Matrix.mul_nonsing_inv A hdet, map_one]
    calc Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A w
        = (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
            * Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A⁻¹) v := rfl
      _ = v := by rw [hmul]; rfl
  have hkey := abs_im_mul_norm_le_norm_sub_smul_one hH z w
  rw [hAw] at hkey
  have hfin : η * ‖w‖ ≤ ‖v‖ := le_trans (by nlinarith [norm_nonneg w]) hkey
  rw [inv_mul_eq_div, le_div_iff₀ hη]
  linarith [hfin]

/-- The affine line `s ↦ M + s • A` has derivative `A`. -/
theorem hasDerivAt_line (M A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

/-- Along the line `t ↦ M + t • A`, the inverse has derivative `-R A R`. -/
theorem hasDerivAt_lineInverse {M A : Matrix n n ℂ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A))
      (-(Ring.inverse (M + (t : ℂ) • A) * A * Ring.inverse (M + (t : ℂ) • A))) t := by
  set u : (Matrix n n ℂ)ˣ := (hU t).unit
  have hus : (u : Matrix n n ℂ) = M + (t : ℂ) • A := IsUnit.unit_spec _
  have hinv : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)
      = Ring.inverse (M + (t : ℂ) • A) := by
    rw [← hus, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹) ↑u⁻¹)
      (M + (t : ℂ) • A) := by
    rw [← hus]; exact hasFDerivAt_ringInverse u
  have hcomp := hF.comp_hasDerivAt t (hasDerivAt_line M A t)
  simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, hinv] using hcomp

/-- The chain of derivatives: `d/dt [(R A)^k R] = -(k+1) (R A)^{k+1} R`. -/
theorem hasDerivAt_lineInversePow {M A : Matrix n n ℂ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A)) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (Ring.inverse (M + (s : ℂ) • A) * A) ^ k
        * Ring.inverse (M + (s : ℂ) • A))
      ((-((k : ℝ) + 1)) • ((Ring.inverse (M + (t : ℂ) • A) * A) ^ (k + 1)
        * Ring.inverse (M + (t : ℂ) • A))) t := by
  induction k with
  | zero => simpa using hasDerivAt_lineInverse hU t
  | succ k ih =>
      have h1 : HasDerivAt (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A) * A)
          (-(Ring.inverse (M + (t : ℂ) • A) * A * Ring.inverse (M + (t : ℂ) • A)) * A) t :=
        (hasDerivAt_lineInverse hU t).mul_const A
      have hmul := h1.mul ih
      have key : (fun s : ℝ => (Ring.inverse (M + (s : ℂ) • A) * A) ^ (k + 1)
            * Ring.inverse (M + (s : ℂ) • A))
          = (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A) * A)
            * (fun s : ℝ => (Ring.inverse (M + (s : ℂ) • A) * A) ^ k
                * Ring.inverse (M + (s : ℂ) • A)) := by
        funext s
        simp [Pi.mul_apply, pow_succ', mul_assoc]
      rw [key]
      convert hmul using 1
      set R := Ring.inverse (M + (t : ℂ) • A)
      have e1 : -(R * A * R) * A * ((R * A) ^ k * R)
          = -((R * A) ^ (k + 1 + 1) * R) := by
        rw [pow_succ' (R * A) (k + 1), pow_succ' (R * A) k]
        simp [mul_assoc]
      have e2 : R * A * ((-((k : ℝ) + 1)) • ((R * A) ^ (k + 1) * R))
          = (-((k : ℝ) + 1)) • ((R * A) ^ (k + 1 + 1) * R) := by
        rw [mul_smul_comm, pow_succ' (R * A) (k + 1)]
        simp [mul_assoc]
      rw [e1, e2]
      push_cast
      module

/-- The `k`-th derivative of the resolvent along a line, as an equality of functions. -/
theorem iteratedDeriv_lineInverse_eq {M A : Matrix n n ℂ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A)) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A))
      = fun t : ℝ => ((-1 : ℝ) ^ k * (k.factorial : ℝ)) •
          ((Ring.inverse (M + (t : ℂ) • A) * A) ^ k * Ring.inverse (M + (t : ℂ) • A)) := by
  induction k with
  | zero => funext t; simp
  | succ k ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have hd : HasDerivAt
          (fun s : ℝ => ((-1 : ℝ) ^ k * (k.factorial : ℝ)) •
            ((Ring.inverse (M + (s : ℂ) • A) * A) ^ k * Ring.inverse (M + (s : ℂ) • A)))
          (((-1 : ℝ) ^ k * (k.factorial : ℝ)) • ((-((k : ℝ) + 1)) •
            ((Ring.inverse (M + (t : ℂ) • A) * A) ^ (k + 1)
              * Ring.inverse (M + (t : ℂ) • A)))) t :=
        (hasDerivAt_lineInversePow hU k t).const_smul
          ((-1 : ℝ) ^ k * (k.factorial : ℝ))
      rw [hd.deriv, smul_smul]
      congr 1
      push_cast [Nat.factorial_succ]
      ring

/-- The `k`-th derivative of the resolvent along a line is `(-1)^k k! (R A)^k R`. -/
theorem iteratedDeriv_lineInverse {M A : Matrix n n ℂ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A)) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A)) t
      = ((-1 : ℝ) ^ k * (k.factorial : ℝ)) •
          ((Ring.inverse (M + (t : ℂ) • A) * A) ^ k * Ring.inverse (M + (t : ℂ) • A)) :=
  congrFun (iteratedDeriv_lineInverse_eq hU k) t

/-- Submultiplicativity bound for `(R A)^k R`. -/
theorem norm_lineInversePow_le {M A : Matrix n n ℂ} {K : ℝ}
    (hK : ∀ t : ℝ, ‖Ring.inverse (M + (t : ℂ) • A)‖ ≤ K) (k : ℕ) (t : ℝ) :
    ‖(Ring.inverse (M + (t : ℂ) • A) * A) ^ k * Ring.inverse (M + (t : ℂ) • A)‖
      ≤ K ^ (k + 1) * ‖A‖ ^ k := by
  have hRK : ‖Ring.inverse (M + (t : ℂ) • A)‖ ≤ K := hK t
  have hK0 : (0 : ℝ) ≤ K := le_trans (norm_nonneg _) hRK
  set R := Ring.inverse (M + (t : ℂ) • A)
  have hRA : ‖R * A‖ ≤ K * ‖A‖ := le_trans (norm_mul_le _ _) (by gcongr)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hRK
  · have hpow : ‖(R * A) ^ k‖ ≤ (K * ‖A‖) ^ k :=
      le_trans (norm_pow_le' _ hk) (pow_le_pow_left₀ (norm_nonneg _) hRA k)
    calc ‖(R * A) ^ k * R‖ ≤ ‖(R * A) ^ k‖ * ‖R‖ := norm_mul_le _ _
      _ ≤ (K * ‖A‖) ^ k * K := by
          have h0 : (0 : ℝ) ≤ (K * ‖A‖) ^ k := by positivity
          exact mul_le_mul hpow hRK (norm_nonneg _) h0
      _ = K ^ (k + 1) * ‖A‖ ^ k := by ring

/-- **The abstract global bound.**  If the resolvent is bounded by `K` on the whole line, every
derivative of order `k` is bounded by `k! K^{k+1} ‖A‖^k`. -/
theorem norm_iteratedDeriv_lineInverse_le {M A : Matrix n n ℂ} {K : ℝ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A))
    (hK : ∀ t : ℝ, ‖Ring.inverse (M + (t : ℂ) • A)‖ ≤ K) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A)) t‖
      ≤ (k.factorial : ℝ) * K ^ (k + 1) * ‖A‖ ^ k := by
  rw [iteratedDeriv_lineInverse hU k t, norm_smul, mul_assoc]
  have h1 : ‖(-1 : ℝ) ^ k * (k.factorial : ℝ)‖ = (k.factorial : ℝ) := by simp
  rw [h1]
  exact mul_le_mul_of_nonneg_left (norm_lineInversePow_le hK k t) (Nat.cast_nonneg _)

omit [Fintype n] [DecidableEq n] in
/-- A real multiple of a Hermitian matrix added to a Hermitian matrix is Hermitian. -/
theorem isHermitian_add_realSmul {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) (s : ℝ) : (M + (s : ℂ) • A).IsHermitian := by
  refine hM.add ?_
  show Matrix.conjTranspose ((s : ℂ) • A) = (s : ℂ) • A
  rw [Matrix.conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal]

/-- **The global derivative bound, in the form every later file needs.**

For Hermitian `M` and a Hermitian direction `A`, and `|Im z| ≥ η > 0`, every derivative of
order `k` of `s ↦ G(M + s A) = (M + s A - z)⁻¹` is bounded, **at every point of the whole
line**, by `k! η^{-(k+1)} ‖A‖^k`.  Because the bound is a constant, the `bound_integrable`
hypothesis of the parametric-integral lemma is discharged by
`RBM.Gauss.integrable_of_continuous_of_bound`. -/
theorem norm_iteratedDeriv_green_le {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (fun s : ℝ => green (M + (s : ℂ) • A) z) t‖
      ≤ (k.factorial : ℝ) * η⁻¹ ^ (k + 1) * ‖A‖ ^ k := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  have hgr : (fun s : ℝ => green (M + (s : ℂ) • A) z)
      = fun s : ℝ => Ring.inverse (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    funext s
    show (M + (s : ℂ) • A - z • (1 : Matrix n n ℂ))⁻¹ = _
    rw [Matrix.nonsing_inv_eq_ringInverse]
    congr 1
    abel
  have hU : ∀ s : ℝ, IsUnit (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    intro s
    have he : M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A
        = (M + (s : ℂ) • A) - z • (1 : Matrix n n ℂ) := by abel
    rw [he]
    exact isUnit_sub_smul_one_of_im_ne_zero (isHermitian_add_realSmul hM hA s) hzim
  have hK : ∀ s : ℝ, ‖Ring.inverse (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A)‖ ≤ η⁻¹ := by
    intro s
    have he : Ring.inverse (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A)
        = green (M + (s : ℂ) • A) z := (congrFun hgr s).symm
    rw [he]
    exact norm_green_le (isHermitian_add_realSmul hM hA s) hη hz
  rw [hgr]
  exact norm_iteratedDeriv_lineInverse_le hU hK k t

end Resolvent

/-! ### The coordinate directions -/

/-- The coordinate of `Coord d` attached to a triple `(i, j, b)` at size parameter `N`. -/
abbrev crd (d : Dims) (N : ℕ) (p : d.Idx N × d.Idx N × Bool) : Coord d := ⟨N, p⟩

theorem crd_injective (d : Dims) (N : ℕ) : Function.Injective (crd d N) := by
  rintro p q h
  simpa using h

/-- The Hermitian matrix direction attached to the coordinate `⟨N, i, j, b⟩`:
`E_ij + E_ji` for the real tag `b = true` and `I·E_ij - I·E_ji` for the imaginary tag
`b = false`; on the diagonal `i = j` the real tag gives `E_ii`. -/
noncomputable def Bmat (d : Dims) (N : ℕ) (i j : d.Idx N) (b : Bool) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  Matrix.of fun k l =>
    if k = i ∧ l = j then (if b then 1 else Complex.I)
    else if k = j ∧ l = i then (if b then 1 else -Complex.I)
    else 0

theorem Bmat_apply (d : Dims) (N : ℕ) (i j : d.Idx N) (b : Bool) (k l : d.Idx N) :
    Bmat d N i j b k l =
      if k = i ∧ l = j then (if b then 1 else Complex.I)
      else if k = j ∧ l = i then (if b then 1 else -Complex.I)
      else 0 := rfl

/-- The coordinates actually read by `Xentry`: the pairs `idxKey i < idxKey j` with both tags,
and the diagonal pairs with the real tag only. -/
def usedCoord (d : Dims) (N : ℕ) : Finset (d.Idx N × d.Idx N × Bool) :=
  Finset.univ.filter fun p => idxKey d N p.1 < idxKey d N p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)

theorem mem_usedCoord {d : Dims} {N : ℕ} {p : d.Idx N × d.Idx N × Bool} :
    p ∈ usedCoord d N ↔
      idxKey d N p.1 < idxKey d N p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true) := by
  simp [usedCoord]

/-- **The coordinate decomposition of `X`.**  `X` is the `ℝ`-linear combination of the fixed
Hermitian directions `Bmat` with the independent Gaussian coordinates as coefficients. -/
theorem Xmat_eq_sum (d : Dims) (N : ℕ) (ω : Ω d) :
    Xmat d N ω = ∑ p ∈ usedCoord d N, ω (crd d N p) • Bmat d N p.1 p.2.1 p.2.2 := by
  ext k l
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Complex.real_smul]
  rcases idxKey_lt_or_eq_or_lt d N k l with h | h | h
  · -- `idxKey k < idxKey l`
    have hkl : k ≠ l := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hsub : ({(k, l, true), (k, l, false)} : Finset (d.Idx N × d.Idx N × Bool)) ⊆
        usedCoord d N := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact mem_usedCoord.2 (Or.inl h)
    rw [← Finset.sum_subset hsub, Finset.sum_pair (by simp)]
    · show Xentry d N ω k l = _
      rw [Xentry, ite_eq_left h]
      simp [Bmat_apply]
      ring
    · rintro ⟨i, j, b⟩ hx hnx
      have hu := mem_usedCoord.1 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hnx
      have hne1 : ¬ (k = i ∧ l = j) := by
        rintro ⟨rfl, rfl⟩
        cases b <;> simp at hnx
      have hne2 : ¬ (k = j ∧ l = i) := by
        rintro ⟨rfl, rfl⟩
        rcases hu with hu | hu
        · exact absurd hu (asymm h)
        · exact hkl hu.1.symm
      simp [Bmat_apply, hne1, hne2]
  · -- `k = l`
    subst h
    have hsub : ({(k, k, true)} : Finset (d.Idx N × d.Idx N × Bool)) ⊆ usedCoord d N := by
      intro x hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      exact mem_usedCoord.2 (Or.inr ⟨rfl, rfl⟩)
    rw [← Finset.sum_subset hsub, Finset.sum_singleton]
    · show Xentry d N ω k k = _
      rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
      simp [Bmat_apply]
    · rintro ⟨i, j, b⟩ hx hnx
      have hu := mem_usedCoord.1 hx
      simp only [Finset.mem_singleton] at hnx
      have hne : ¬ (k = i ∧ k = j) := by
        rintro ⟨rfl, rfl⟩
        rcases hu with hu | hu
        · exact absurd hu (lt_irrefl _)
        · have hb : b = true := hu.2
          subst hb
          exact hnx rfl
      have hne' : ¬ (k = j ∧ k = i) := fun h' => hne ⟨h'.2, h'.1⟩
      rw [Bmat_apply, ite_eq_right hne, ite_eq_right hne', mul_zero]
  · -- `idxKey l < idxKey k`
    have hkl : l ≠ k := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hsub : ({(l, k, true), (l, k, false)} : Finset (d.Idx N × d.Idx N × Bool)) ⊆
        usedCoord d N := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact mem_usedCoord.2 (Or.inl h)
    rw [← Finset.sum_subset hsub, Finset.sum_pair (by simp)]
    · show Xentry d N ω k l = _
      rw [Xentry, ite_eq_right (asymm h), ite_eq_left h]
      simp [Bmat_apply, hkl, Ne.symm hkl]
      ring
    · rintro ⟨i, j, b⟩ hx hnx
      have hu := mem_usedCoord.1 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hnx
      have hne1 : ¬ (k = i ∧ l = j) := by
        rintro ⟨rfl, rfl⟩
        rcases hu with hu | hu
        · exact absurd hu (asymm h)
        · exact hkl hu.1.symm
      have hne2 : ¬ (k = j ∧ l = i) := by
        rintro ⟨rfl, rfl⟩
        cases b <;> simp at hnx
      simp [Bmat_apply, hne1, hne2]

/-- Every direction attached to a **used** coordinate is Hermitian (the redundant coordinate
`⟨N, i, i, false⟩` is the one exception, and it is never read). -/
theorem Bmat_isHermitian {d : Dims} {N : ℕ} {p : d.Idx N × d.Idx N × Bool}
    (hp : p ∈ usedCoord d N) : (Bmat d N p.1 p.2.1 p.2.2).IsHermitian := by
  obtain ⟨i, j, b⟩ := p
  have hij : i ≠ j ∨ b = true := by
    rcases mem_usedCoord.1 hp with h | h
    · exact Or.inl fun he => absurd (he ▸ h) (lt_irrefl _)
    · exact Or.inr h.2
  ext k l
  show (starRingEnd ℂ) (Bmat d N i j b l k) = Bmat d N i j b k l
  rw [Bmat_apply, Bmat_apply]
  rcases hij with hij | hb
  · by_cases hA : k = i ∧ l = j
    · have hB : ¬ (l = i ∧ k = j) := fun hB => hij (by rw [← hA.1]; exact hB.2)
      rw [ite_eq_right hB, ite_eq_left (⟨hA.2, hA.1⟩ : l = j ∧ k = i), ite_eq_left hA]
      cases b <;> simp
    · by_cases hB : k = j ∧ l = i
      · rw [ite_eq_left (⟨hB.2, hB.1⟩ : l = i ∧ k = j), ite_eq_right hA, ite_eq_left hB]
        cases b <;> simp
      · rw [ite_eq_right (fun h => hB ⟨h.2, h.1⟩), ite_eq_right (fun h => hA ⟨h.2, h.1⟩),
          ite_eq_right hA, ite_eq_right hB]
        simp
  · subst hb
    by_cases hA : k = i ∧ l = j
    · rw [ite_eq_left hA]
      by_cases hB : l = i ∧ k = j
      · rw [ite_eq_left hB]; simp
      · rw [ite_eq_right hB, ite_eq_left (⟨hA.2, hA.1⟩ : l = j ∧ k = i)]; simp
    · rw [ite_eq_right hA]
      by_cases hB : k = j ∧ l = i
      · rw [ite_eq_left (⟨hB.2, hB.1⟩ : l = i ∧ k = j), ite_eq_left hB]; simp
      · rw [ite_eq_right (fun h => hB ⟨h.2, h.1⟩), ite_eq_right (fun h => hA ⟨h.2, h.1⟩),
          ite_eq_right hB]
        simp

/-- **`X` is affine in each independent coordinate**, with slope the direction `Bmat`.  This is
what turns a partial derivative in a Gaussian coordinate into a directional derivative of the
matrix argument. -/
theorem Xmat_update (d : Dims) (N : ℕ) (ω : Ω d) {p : d.Idx N × d.Idx N × Bool}
    (hp : p ∈ usedCoord d N) (t : ℝ) :
    Xmat d N (Function.update ω (crd d N p) t)
      = Xmat d N ω + (t - ω (crd d N p)) • Bmat d N p.1 p.2.1 p.2.2 := by
  rw [Xmat_eq_sum, Xmat_eq_sum, ← Finset.add_sum_erase _ _ hp, ← Finset.add_sum_erase _ _ hp]
  have hrest : ∀ q ∈ (usedCoord d N).erase p,
      (Function.update ω (crd d N p) t) (crd d N q) • Bmat d N q.1 q.2.1 q.2.2
        = ω (crd d N q) • Bmat d N q.1 q.2.1 q.2.2 := by
    intro q hq
    rw [Function.update_of_ne fun h => (Finset.ne_of_mem_erase hq) (crd_injective d N h)]
  rw [Finset.sum_congr rfl hrest, Function.update_self, sub_smul]
  abel

/-- `H_u = √u • X` with the **real** scalar action. -/
theorem Hflow_eq_realSmul (d : Dims) (N : ℕ) (u : ℝ) (ω : Ω d) :
    Hflow d N u ω = Real.sqrt u • Xmat d N ω := by
  ext k l
  show (Real.sqrt u : ℂ) * Xentry d N ω k l = Real.sqrt u • Xentry d N ω k l
  rw [Complex.real_smul]

/-! ### Continuity and integrability -/

theorem continuous_Xmat (d : Dims) (N : ℕ) : Continuous fun ω : Ω d => Xmat d N ω := by
  have h : (fun ω : Ω d => Xmat d N ω)
      = fun ω : Ω d => ∑ p ∈ usedCoord d N, ω (crd d N p) • Bmat d N p.1 p.2.1 p.2.2 :=
    funext fun ω => Xmat_eq_sum d N ω
  rw [h]
  exact continuous_finsetSum _ fun p _ => (continuous_apply (crd d N p)).smul continuous_const

theorem continuous_Hflow (d : Dims) (N : ℕ) (u : ℝ) :
    Continuous fun ω : Ω d => Hflow d N u ω := by
  have h : (fun ω : Ω d => Hflow d N u ω) = fun ω : Ω d => Real.sqrt u • Xmat d N ω :=
    funext fun ω => Hflow_eq_realSmul d N u ω
  rw [h]
  exact (continuous_Xmat d N).const_smul (Real.sqrt u)

/-- A bounded continuous function on the Gaussian space is integrable. -/
theorem integrable_of_continuous_of_bound {d : Dims} {E : Type*} [NormedAddCommGroup E]
    {f : Ω d → E} (hf : Continuous f) {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable f (P d) :=
  (memLp_top_of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)).integrable le_top

/-- Each Gaussian coordinate is integrable (first moment of a centred Gaussian). -/
theorem integrable_coord (d : Dims) (c : Coord d) : Integrable (fun ω : Ω d => ω c) (P d) := by
  have hf : AEMeasurable (fun ω : Ω d => ω c) (P d) := (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x) ((P d).map fun ω => ω c) := by
    rw [P_map_eval]
    exact (memLp_id_gaussianReal (μ := 0) (v := gvar d c) 1).integrable le_rfl
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

/-! ### Directional derivatives along the coordinate directions -/

section Deriv

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- `∂_p Φ (M)`: the first directional derivative of `Φ` at `M` along the direction `Bmat p`
of the coordinate `p`. -/
noncomputable def coordD1 (d : Dims) (N : ℕ) (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (p : d.Idx N × d.Idx N × Bool) : ℂ :=
  fderiv ℝ Φ M (Bmat d N p.1 p.2.1 p.2.2)

/-- `∂_p ∂_p Φ (M)`: the second directional derivative of `Φ` at `M`, twice along `Bmat p`. -/
noncomputable def coordD2 (d : Dims) (N : ℕ) (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (p : d.Idx N × d.Idx N × Bool) : ℂ :=
  fderiv ℝ (fderiv ℝ Φ) M (Bmat d N p.1 p.2.1 p.2.2) (Bmat d N p.1 p.2.1 p.2.2)

/-- **The class of test functions** for the generator identity: `C²` with globally bounded
value, first and second derivative.  This is exactly what the global resolvent bound of the
last section delivers for `Φ = |F|^{2p}` with `F` a polynomial in `G = (H - z)⁻¹`. -/
structure TestFun (d : Dims) (N : ℕ) (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) : Prop where
  /-- `Φ` is twice continuously differentiable as a function of the real coordinates. -/
  contDiff : ContDiff ℝ 2 Φ
  /-- `Φ` is globally bounded. -/
  bdd₀ : ∃ C : ℝ, ∀ M, ‖Φ M‖ ≤ C
  /-- The first derivative of `Φ` is globally bounded. -/
  bdd₁ : ∃ C : ℝ, ∀ M, ‖fderiv ℝ Φ M‖ ≤ C
  /-- The second derivative of `Φ` is globally bounded. -/
  bdd₂ : ∃ C : ℝ, ∀ M, ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C

namespace TestFun

theorem differentiable (h : TestFun d N Φ) : Differentiable ℝ Φ :=
  h.contDiff.differentiable (by norm_num)

theorem contDiff_fderiv (h : TestFun d N Φ) : ContDiff ℝ 1 (fderiv ℝ Φ) :=
  h.contDiff.fderiv_right (by norm_num)

theorem differentiable_fderiv (h : TestFun d N Φ) : Differentiable ℝ (fderiv ℝ Φ) :=
  h.contDiff_fderiv.differentiable (by norm_num)

theorem continuous_fderiv (h : TestFun d N Φ) : Continuous (fderiv ℝ Φ) :=
  h.contDiff_fderiv.continuous

theorem continuous_fderiv2 (h : TestFun d N Φ) : Continuous (fderiv ℝ (fderiv ℝ Φ)) :=
  (h.contDiff_fderiv.fderiv_right (m := 0) (by norm_num)).continuous

end TestFun

/-- Differentiating `M ↦ fderiv ℝ Φ M A` in `M`. -/
theorem hasFDerivAt_fderiv_apply (h : TestFun d N Φ) (A M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    HasFDerivAt (fun M' => fderiv ℝ Φ M' A) ((fderiv ℝ (fderiv ℝ Φ) M).flip A) M := by
  have hc := ((h.differentiable_fderiv M).hasFDerivAt).clm_apply
    (hasFDerivAt_const (𝕜 := ℝ) A M)
  simpa using hc

/-- The first derivative of `Φ` in the direction `X` is the coordinate sum of the
directional derivatives. -/
theorem fderiv_apply_Xmat (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (ω : Ω d) :
    fderiv ℝ Φ M (Xmat d N ω)
      = ∑ p ∈ usedCoord d N, ω (crd d N p) • coordD1 d N Φ M p := by
  conv_lhs => rw [Xmat_eq_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

/-- **The `u`-derivative of the integrand.**  `d/du Φ(√u X) = (2√u)⁻¹ ∂_X Φ(√u X)`. -/
theorem hasDerivAt_Phi_Hflow (h : TestFun d N Φ) {u : ℝ} (hu : 0 < u) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => Φ (Hflow d N s ω))
      ((1 / (2 * Real.sqrt u)) • fderiv ℝ Φ (Hflow d N u ω) (Xmat d N ω)) u := by
  have hfun : (fun s : ℝ => Φ (Hflow d N s ω))
      = (Φ ∘ fun s : ℝ => Real.sqrt s • Xmat d N ω) := by
    funext s
    simp [Hflow_eq_realSmul]
  have hline : HasDerivAt (fun s : ℝ => Real.sqrt s • Xmat d N ω)
      ((1 / (2 * Real.sqrt u)) • Xmat d N ω) u :=
    (Real.hasDerivAt_sqrt hu.ne').smul_const _
  have key : HasDerivAt (Φ ∘ fun s : ℝ => Real.sqrt s • Xmat d N ω)
      (fderiv ℝ Φ (Real.sqrt u • Xmat d N ω)
        ((1 / (2 * Real.sqrt u)) • Xmat d N ω)) u :=
    ((h.differentiable _).hasFDerivAt).comp_hasDerivAt u hline
  rw [map_smul, ← Hflow_eq_realSmul] at key
  rw [hfun]
  exact key

/-- **The coordinate derivative of the first directional derivative.**  Moving the Gaussian
coordinate `p` moves the matrix argument along `√u • Bmat p`; this is where Stein's identity
turns `X_ij` into a second derivative. -/
theorem hasDerivAt_coordD1_update (h : TestFun d N Φ) (u : ℝ) (ω : Ω d)
    {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) :
    HasDerivAt
      (fun t : ℝ => coordD1 d N Φ (Hflow d N u (Function.update ω (crd d N p) t)) p)
      (Real.sqrt u • coordD2 d N Φ (Hflow d N u ω) p) (ω (crd d N p)) := by
  set c := crd d N p with hc
  set B := Bmat d N p.1 p.2.1 p.2.2 with hB
  have hline : ∀ t : ℝ, Hflow d N u (Function.update ω c t)
      = Hflow d N u ω + (Real.sqrt u * (t - ω c)) • B := by
    intro t
    rw [Hflow_eq_realSmul, Hflow_eq_realSmul, Xmat_update d N ω hp t, smul_add, smul_smul]
  have hscal : HasDerivAt (fun t : ℝ => Real.sqrt u * (t - ω c)) (Real.sqrt u) (ω c) := by
    simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul (Real.sqrt u)
  have hpath : HasDerivAt (fun t : ℝ => Hflow d N u (Function.update ω c t))
      (Real.sqrt u • B) (ω c) := by
    have h1 : HasDerivAt (fun t : ℝ => Hflow d N u ω + (Real.sqrt u * (t - ω c)) • B)
        (Real.sqrt u • B) (ω c) := (hscal.smul_const B).const_add _
    exact h1.congr_of_eventuallyEq (Eventually.of_forall fun t => hline t)
  have hself : Hflow d N u (Function.update ω c (ω c)) = Hflow d N u ω := by
    rw [Function.update_eq_self]
  have key := (hasFDerivAt_fderiv_apply h B
    (Hflow d N u (Function.update ω c (ω c)))).comp_hasDerivAt (ω c) hpath
  rw [hself] at key
  have hval : ((fderiv ℝ (fderiv ℝ Φ) (Hflow d N u ω)).flip B) (Real.sqrt u • B)
      = Real.sqrt u • coordD2 d N Φ (Hflow d N u ω) p := by
    rw [ContinuousLinearMap.flip_apply, map_smul]
    rfl
  rw [hval] at key
  exact key

end Deriv

/-! ### Continuity and bounds for the directional derivatives -/

section Bounds

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

theorem continuous_coordD1 (h : TestFun d N Φ) (u : ℝ) (p : d.Idx N × d.Idx N × Bool) :
    Continuous fun ω : Ω d => coordD1 d N Φ (Hflow d N u ω) p :=
  (h.continuous_fderiv.comp (continuous_Hflow d N u)).clm_apply continuous_const

theorem continuous_coordD2 (h : TestFun d N Φ) (u : ℝ) (p : d.Idx N × d.Idx N × Bool) :
    Continuous fun ω : Ω d => coordD2 d N Φ (Hflow d N u ω) p :=
  ((h.continuous_fderiv2.comp (continuous_Hflow d N u)).clm_apply
    continuous_const).clm_apply continuous_const

theorem norm_coordD1_le {C : ℝ} (hC : ∀ M, ‖fderiv ℝ Φ M‖ ≤ C)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (p : d.Idx N × d.Idx N × Bool) :
    ‖coordD1 d N Φ M p‖ ≤ C * ‖Bmat d N p.1 p.2.1 p.2.2‖ :=
  le_trans ((fderiv ℝ Φ M).le_opNorm _) (mul_le_mul_of_nonneg_right (hC M) (norm_nonneg _))

theorem norm_coordD2_le {C : ℝ} (hC : ∀ M, ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (p : d.Idx N × d.Idx N × Bool) :
    ‖coordD2 d N Φ M p‖
      ≤ C * ‖Bmat d N p.1 p.2.1 p.2.2‖ * ‖Bmat d N p.1 p.2.1 p.2.2‖ :=
  le_trans ((fderiv ℝ (fderiv ℝ Φ) M (Bmat d N p.1 p.2.1 p.2.2)).le_opNorm _)
    (mul_le_mul_of_nonneg_right
      (le_trans ((fderiv ℝ (fderiv ℝ Φ) M).le_opNorm _)
        (mul_le_mul_of_nonneg_right (hC M) (norm_nonneg _))) (norm_nonneg _))

end Bounds

/-! ### Dependence on finitely many coordinates -/

/-- `g : Ω d → V` reads only finitely many Gaussian coordinates.  Every function we feed to
Stein's identity has this property (`finDep_of_Hflow`), which lets T70 reduce the identity on
the infinite product `P d` to one on a finite `MeasureTheory.Measure.pi`, via
`RBM.Gauss.P_map_restrict`. -/
def FinDep (d : Dims) {V : Type*} (g : Ω d → V) : Prop :=
  ∃ I : Finset (Coord d), ∀ ω ω' : Ω d, (∀ e ∈ I, ω e = ω' e) → g ω = g ω'

/-- `H_u` reads only the coordinates of `usedCoord d N`. -/
theorem Hflow_congr_of_agree (d : Dims) (N : ℕ) (u : ℝ) (ω ω' : Ω d)
    (h : ∀ e ∈ (usedCoord d N).image (crd d N), ω e = ω' e) :
    Hflow d N u ω = Hflow d N u ω' := by
  rw [Hflow_eq_realSmul, Hflow_eq_realSmul, Xmat_eq_sum, Xmat_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [h (crd d N p) (Finset.mem_image_of_mem _ hp)]

/-- Anything read off `H_u` reads only finitely many coordinates. -/
theorem finDep_of_Hflow (d : Dims) (N : ℕ) (u : ℝ) {V : Type*}
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → V) : FinDep d fun ω => F (Hflow d N u ω) :=
  ⟨(usedCoord d N).image (crd d N), fun ω ω' h => by
    show F (Hflow d N u ω) = F (Hflow d N u ω')
    rw [Hflow_congr_of_agree d N u ω ω' h]⟩

/-! ### The matrix-level Stein identity — the hypothesis carried from T70 -/

/-- **Gaussian integration by parts, matrix level**, stated in the coordinate convention of
`RBM1D/Gauss/Model.lean`.

`c` ranges over `Coord d`, whose Gaussian law is `gaussianReal 0 (gvar d c)`
(`RBM.Gauss.P_map_eval`); `Function.update ω c t` is the move of that single coordinate, and
`g'` is the corresponding partial derivative.  Since `X_ij = ω⟨N,i,j,tt⟩ + I ω⟨N,i,j,ff⟩` and
`X_ji = conj X_ij` pointwise, this *is* the real/imaginary split of
`E[X_ij F(X)] = S_ij E[∂_ji F(X)]`: the two tags of the pair `(i, j)` carry the variance
`gvar = S_ij / 2` each off the diagonal and `S_ij` on it, so the two coordinate identities add
up to the matrix one.

The regularity hypotheses (`Continuous`, `FinDep` and global bounds on `g` and `g'`) are
deliberately strong: they are exactly what `RBM.Gauss.TestFun` supplies, and they make the
identity as cheap as possible to discharge.  In particular `FinDep` says `g` reads only
finitely many coordinates, so `RBM.Gauss.P_map_restrict` turns the infinite product `P d`
into a `MeasureTheory.Measure.pi`, and the identity reduces to a Fubini over the other
coordinates plus the one-dimensional `RBM.integral_mul_gaussianReal` of `Gauss/Stein.lean`.
**T70 owes this structure.** -/
structure MatrixStein (d : Dims) : Prop where
  /-- `E[ω_c · g] = gvar_c · E[∂_c g]` for one Gaussian coordinate. -/
  stein : ∀ (c : Coord d) (g g' : Ω d → ℂ), Continuous g → Continuous g' →
    FinDep d g → FinDep d g' →
    (∀ ω, HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c)) →
    (∃ C : ℝ, ∀ ω, ‖g ω‖ ≤ C) → (∃ C : ℝ, ∀ ω, ‖g' ω‖ ≤ C) →
    ∫ ω, ω c • g ω ∂(P d) = (gvar d c : ℝ) • ∫ ω, g' ω ∂(P d)

/-! ### The generator identity -/

section Generator

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- **The generator identity of the moment route, coordinate form.**

`∂_u E[Φ(H_u)] = ½ ∑_α S_α E[∂_α ∂_α Φ(H_u)]`, the sum running over the independent Gaussian
coordinates `α` of `RBM1D/Gauss/Model.lean` with their variances `gvar`.  This is the form
T72 uses: its second-order term is literally the quadratic variation of (5.25).

The proof is: differentiate under the integral sign (the `√u`-chain rule gives
`(2√u)⁻¹ ∑_α ω_α ∂_α Φ`), then apply Stein's identity to each coordinate, which replaces
`ω_α` by `gvar_α ∂_α` and produces a factor `√u` that cancels the `(2√u)⁻¹`. -/
theorem hasDerivAt_integral_Phi (hst : MatrixStein d) (h : TestFun d N Φ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ (Hflow d N s ω) ∂(P d))
      ((1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
        ∫ ω, coordD2 d N Φ (Hflow d N u ω) p ∂(P d)) u := by
  obtain ⟨C₀, hC₀⟩ := h.bdd₀
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  have hC₁0 : 0 ≤ C₁ := le_trans (norm_nonneg _) (hC₁ 0)
  have hu2 : (0 : ℝ) < u / 2 := by linarith
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hcontF : ∀ x : ℝ, Continuous fun ω : Ω d => Φ (Hflow d N x ω) := fun x =>
    h.contDiff.continuous.comp (continuous_Hflow d N x)
  have hcontF' : ∀ x : ℝ, Continuous fun ω : Ω d =>
      (1 / (2 * Real.sqrt x)) • ∑ p ∈ usedCoord d N,
        ω (crd d N p) • coordD1 d N Φ (Hflow d N x ω) p := by
    intro x
    have hsum : Continuous fun ω : Ω d => ∑ p ∈ usedCoord d N,
        ω (crd d N p) • coordD1 d N Φ (Hflow d N x ω) p :=
      continuous_finsetSum (usedCoord d N) fun p _ =>
        (continuous_apply (crd d N p)).smul (continuous_coordD1 h x p)
    exact hsum.const_smul (1 / (2 * Real.sqrt x))
  have hcg' : ∀ p : d.Idx N × d.Idx N × Bool,
      Continuous fun ω : Ω d => Real.sqrt u • coordD2 d N Φ (Hflow d N u ω) p := by
    intro p
    exact (continuous_coordD2 h u p).const_smul (Real.sqrt u)
  -- domination
  have hbound : ∀ᵐ ω ∂(P d), ∀ x ∈ Set.Ioi (u / 2),
      ‖(1 / (2 * Real.sqrt x)) • ∑ p ∈ usedCoord d N,
          ω (crd d N p) • coordD1 d N Φ (Hflow d N x ω) p‖
        ≤ (1 / (2 * Real.sqrt (u / 2))) * ∑ p ∈ usedCoord d N,
            |ω (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖) := by
    refine Eventually.of_forall fun ω x hx => ?_
    have hx0 : 0 < x := lt_trans hu2 hx
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hs2 : 0 < Real.sqrt (u / 2) := Real.sqrt_pos.2 hu2
    have hmono : Real.sqrt (u / 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt (le_of_lt hx)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖∑ p ∈ usedCoord d N, ω (crd d N p) • coordD1 d N Φ (Hflow d N x ω) p‖
        ≤ ∑ p ∈ usedCoord d N, |ω (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖) := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_coordD1_le hC₁ _ p) (abs_nonneg _)
    have h2 : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt (u / 2)) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
  have hbndint : Integrable (fun ω : Ω d => (1 / (2 * Real.sqrt (u / 2))) *
      ∑ p ∈ usedCoord d N, |ω (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖)) (P d) :=
    Integrable.const_mul (integrable_finsetSum _ fun p _ =>
      ((integrable_coord d (crd d N p)).abs).mul_const _) _
  have hdiff : ∀ᵐ ω ∂(P d), ∀ x ∈ Set.Ioi (u / 2),
      HasDerivAt (fun s : ℝ => Φ (Hflow d N s ω))
        ((1 / (2 * Real.sqrt x)) • ∑ p ∈ usedCoord d N,
          ω (crd d N p) • coordD1 d N Φ (Hflow d N x ω) p) x := by
    refine Eventually.of_forall fun ω x hx => ?_
    have := hasDerivAt_Phi_Hflow h (lt_trans hu2 hx) ω
    rwa [fderiv_apply_Xmat] at this
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := P d) (𝕜 := ℝ)
    (F := fun (s : ℝ) (ω : Ω d) => Φ (Hflow d N s ω))
    (F' := fun (s : ℝ) (ω : Ω d) => (1 / (2 * Real.sqrt s)) • ∑ p ∈ usedCoord d N,
      ω (crd d N p) • coordD1 d N Φ (Hflow d N s ω) p)
    (x₀ := u) (s := Set.Ioi (u / 2))
    (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun x => (hcontF x).aestronglyMeasurable)
    (integrable_of_continuous_of_bound (hcontF u) fun ω => hC₀ _)
    (hcontF' u).aestronglyMeasurable hbound hbndint hdiff
  -- Stein, coordinate by coordinate
  have hint : ∀ p ∈ usedCoord d N,
      Integrable (fun ω : Ω d => ω (crd d N p) • coordD1 d N Φ (Hflow d N u ω) p) (P d) := by
    intro p _
    exact (integrable_coord d (crd d N p)).smul_bdd (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖)
      (continuous_coordD1 h u p).aestronglyMeasurable
      (Eventually.of_forall fun ω => norm_coordD1_le hC₁ _ p)
  have hstein : ∀ p ∈ usedCoord d N,
      ∫ ω, ω (crd d N p) • coordD1 d N Φ (Hflow d N u ω) p ∂(P d)
        = (gvar d (crd d N p) : ℝ) •
            (Real.sqrt u • ∫ ω, coordD2 d N Φ (Hflow d N u ω) p ∂(P d)) := by
    intro p hp
    rw [hst.stein (crd d N p) _ (fun ω => Real.sqrt u • coordD2 d N Φ (Hflow d N u ω) p)
        (continuous_coordD1 h u p)
        (hcg' p)
        (finDep_of_Hflow d N u fun M => coordD1 d N Φ M p)
        (finDep_of_Hflow d N u fun M => Real.sqrt u • coordD2 d N Φ M p)
        (fun ω => hasDerivAt_coordD1_update h u ω hp)
        ⟨C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖, fun ω => norm_coordD1_le hC₁ _ p⟩
        ⟨|Real.sqrt u| * (C₂ * ‖Bmat d N p.1 p.2.1 p.2.2‖ * ‖Bmat d N p.1 p.2.1 p.2.2‖),
          fun ω => by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (norm_coordD2_le hC₂ _ p) (abs_nonneg _)⟩,
      integral_smul]
  have hIcalc : ∫ ω, ((1 / (2 * Real.sqrt u)) • ∑ p ∈ usedCoord d N,
        ω (crd d N p) • coordD1 d N Φ (Hflow d N u ω) p) ∂(P d)
      = (1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
        ∫ ω, coordD2 d N Φ (Hflow d N u ω) p ∂(P d) := by
    rw [integral_smul, integral_finsetSum _ hint, Finset.sum_congr rfl hstein,
      Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [smul_smul]
    congr 1
    field_simp
  rw [← hIcalc]
  exact hmain.2

/-- `deriv` form of `hasDerivAt_integral_Phi`, for feeding into Grönwall (T72). -/
theorem deriv_integral_Phi (hst : MatrixStein d) (h : TestFun d N Φ) {u : ℝ} (hu : 0 < u) :
    deriv (fun s : ℝ => ∫ ω, Φ (Hflow d N s ω) ∂(P d)) u
      = (1 / 2 : ℝ) • ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
        ∫ ω, coordD2 d N Φ (Hflow d N u ω) p ∂(P d) :=
  (hasDerivAt_integral_Phi hst h hu).deriv

end Generator

/-! ### The paper's `∑_{ij} S_ij ∂_ij ∂_ji` form -/

section Wirtinger

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- The real direction is symmetric in the pair: `Bmat j i true = Bmat i j true`. -/
theorem Bmat_swap_true (d : Dims) (N : ℕ) (i j : d.Idx N) :
    Bmat d N j i true = Bmat d N i j true := by
  ext k l
  rw [Bmat_apply, Bmat_apply]
  by_cases h1 : k = i ∧ l = j
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_left h1]
    · rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left h1]; simp
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]; simp
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]

/-- The imaginary direction is antisymmetric in the pair (off the diagonal):
`Bmat j i false = -Bmat i j false`. -/
theorem Bmat_swap_false (d : Dims) (N : ℕ) {i j : d.Idx N} (hij : i ≠ j) :
    Bmat d N j i false = -Bmat d N i j false := by
  ext k l
  show Bmat d N j i false k l = -(Bmat d N i j false k l)
  rw [Bmat_apply, Bmat_apply]
  by_cases h1 : k = i ∧ l = j
  · have h2 : ¬ (k = j ∧ l = i) := by
      rintro ⟨hkj, _⟩
      refine hij ?_
      rw [← h1.1]
      exact hkj
    rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left h1]; simp
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]; simp
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1, neg_zero]

/-- `coordD2` is unchanged when the two indices of the coordinate are swapped: the real
direction is symmetric and the imaginary one only changes sign, and `coordD2` is quadratic. -/
theorem coordD2_swap (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) (b : Bool) :
    coordD2 d N Φ M (i, j, b) = coordD2 d N Φ M (j, i, b) := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  cases b
  · show fderiv ℝ (fderiv ℝ Φ) M (Bmat d N i j false) (Bmat d N i j false)
      = fderiv ℝ (fderiv ℝ Φ) M (Bmat d N j i false) (Bmat d N j i false)
    rw [Bmat_swap_false d N hij]
    simp
  · show fderiv ℝ (fderiv ℝ Φ) M (Bmat d N i j true) (Bmat d N i j true)
      = fderiv ℝ (fderiv ℝ Φ) M (Bmat d N j i true) (Bmat d N j i true)
    rw [Bmat_swap_true d N i j]

/-- **`∂_ij ∂_ji Φ` in the Wirtinger convention of the paper.**

For `i ≠ j` the entry `H_ij = a + i b` with `H_ji = conj H_ij`, and the Wirtinger derivatives
are `∂_ij = (∂_a - i ∂_b)/2`, `∂_ji = (∂_a + i ∂_b)/2`; since `∂_a` and `∂_b` commute,
`∂_ij ∂_ji = (∂_a² + ∂_b²)/4`, which is what is written here in terms of the two real
directional derivatives `coordD2 (i,j,true)` and `coordD2 (i,j,false)`.  On the diagonal
`H_ii` is real and `∂_ii = ∂_a`, so `∂_ii ∂_ii = ∂_a²`.

This is symmetric in `(i, j)` (`coordD2_swap`), as `∂_ij ∂_ji = ∂_ji ∂_ij` must be. -/
noncomputable def wirtSecond (d : Dims) (N : ℕ) (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) : ℂ :=
  if i = j then coordD2 d N Φ M (i, i, true)
  else (1 / 4 : ℝ) • (coordD2 d N Φ M (i, j, true) + coordD2 d N Φ M (i, j, false))

theorem wirtSecond_symm (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) :
    wirtSecond d N Φ M i j = wirtSecond d N Φ M j i := by
  unfold wirtSecond
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), coordD2_swap Φ M i j true,
      coordD2_swap Φ M i j false]

/-- The variance of a coordinate, read off from the index pair. -/
theorem gvar_crd (d : Dims) (N : ℕ) (p : d.Idx N × d.Idx N × Bool) :
    (gvar d (crd d N p) : ℝ)
      = if p.1 = p.2.1 then Sblk (d.L N) (d.W N) p.1 p.2.1
        else Sblk (d.L N) (d.W N) p.1 p.2.1 / 2 := by
  obtain ⟨i, j, b⟩ := p
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl]; exact gvar_diag d N i b
  · rw [ite_eq_right hij]; exact gvar_offDiag d N i j b hij

theorem integrable_coordD2 (h : TestFun d N Φ) (u : ℝ) (p : d.Idx N × d.Idx N × Bool) :
    Integrable (fun ω : Ω d => coordD2 d N Φ (Hflow d N u ω) p) (P d) := by
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  exact integrable_of_continuous_of_bound (continuous_coordD2 h u p)
    (fun ω => norm_coordD2_le hC₂ _ p)

/-- The expectation of `∂_ij ∂_ji Φ`, in terms of the two real directional derivatives. -/
theorem integral_wirtSecond (h : TestFun d N Φ) (u : ℝ) (i j : d.Idx N) :
    ∫ ω, wirtSecond d N Φ (Hflow d N u ω) i j ∂(P d)
      = if i = j then ∫ ω, coordD2 d N Φ (Hflow d N u ω) (i, i, true) ∂(P d)
        else (1 / 4 : ℝ) • (∫ ω, coordD2 d N Φ (Hflow d N u ω) (i, j, true) ∂(P d)
          + ∫ ω, coordD2 d N Φ (Hflow d N u ω) (i, j, false) ∂(P d)) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show wirtSecond d N Φ (Hflow d N u ω) i i = _
    rw [wirtSecond, ite_eq_left rfl]
  · rw [ite_eq_right hij]
    have hpt : (fun ω : Ω d => wirtSecond d N Φ (Hflow d N u ω) i j)
        = fun ω : Ω d => (1 / 4 : ℝ) • (coordD2 d N Φ (Hflow d N u ω) (i, j, true)
            + coordD2 d N Φ (Hflow d N u ω) (i, j, false)) := by
      funext ω
      rw [wirtSecond, ite_eq_right hij]
    rw [hpt, integral_smul, integral_add (integrable_coordD2 h u _) (integrable_coordD2 h u _)]

/-! #### From the coordinate sum to the paper's index-pair sum -/

/-- Halving is injective on an `ℝ`-module: `X + X = Y + Y` forces `X = Y`. -/
theorem eq_of_add_self_eq_add_self {V : Type*} [AddCommGroup V] [Module ℝ V] {X Y : V}
    (h : X + X = Y + Y) : X = Y := by
  have h2 : ((2 : ℝ)⁻¹ * 2) • X = ((2 : ℝ)⁻¹ * 2) • Y := by
    rw [mul_smul, mul_smul, two_smul, two_smul, h]
  have hc : ((2 : ℝ)⁻¹ * 2) = 1 := by norm_num
  rwa [hc, one_smul, one_smul] at h2

/-- The off-diagonal bookkeeping: a quarter of each of the two copies, twice over, is a
half.  This is the factor `2` between the coordinate sum (one representative per unordered
pair) and the paper's sum over all ordered pairs. -/
theorem smul_quarter_pair {V : Type*} [AddCommGroup V] [Module ℝ V] (c : ℝ) (A B : V) :
    (c / 2) • A + (c / 2) • B =
      c • (1 / 4 : ℝ) • (A + B) + c • (1 / 4 : ℝ) • (A + B) := by
  rw [smul_smul, ← two_smul ℝ, smul_smul,
    show (2 * (c * (1 / 4)) : ℝ) = c / 2 by ring, smul_add]

/-- A double sum over a square index set is determined by the swap-symmetrization of its
summand: if `g i j + g j i = h i j + h j i` pointwise, the two double sums agree. -/
theorem sum_sum_eq_of_swap_add_eq {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V]
    [Module ℝ V] (g h : ι → ι → V) (key : ∀ i j, g i j + g j i = h i j + h j i) :
    (∑ i, ∑ j, g i j) = ∑ i, ∑ j, h i j := by
  have e1 : ∀ F : ι → ι → V,
      (∑ i, ∑ j, (F i j + F j i)) = (∑ i, ∑ j, F i j) + (∑ i, ∑ j, F j i) := by
    intro F
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  have hg : (∑ i, ∑ j, g i j) = ∑ i, ∑ j, g j i := Finset.sum_comm
  have hh : (∑ i, ∑ j, h i j) = ∑ i, ∑ j, h j i := Finset.sum_comm
  refine eq_of_add_self_eq_add_self ?_
  calc (∑ i, ∑ j, g i j) + (∑ i, ∑ j, g i j)
      = (∑ i, ∑ j, g i j) + (∑ i, ∑ j, g j i) := by rw [← hg]
    _ = ∑ i, ∑ j, (g i j + g j i) := (e1 g).symm
    _ = ∑ i, ∑ j, (h i j + h j i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
    _ = (∑ i, ∑ j, h i j) + (∑ i, ∑ j, h j i) := e1 h
    _ = (∑ i, ∑ j, h i j) + (∑ i, ∑ j, h i j) := by rw [← hh]

/-- **The bookkeeping lemma.**  Summing a symmetric weight `S` against a symmetric family `f`
over the "used" index set (one representative per unordered pair, both tags, plus the
diagonal with the real tag) equals the full double sum over ordered pairs, with the diagonal
treated separately and the off-diagonal terms weighted by `1/4`.

Applied with `κ = idxKey`, `S = Sblk` and `f = E[∂_α ∂_α Φ]`, this is exactly the passage from
`∑_{α ∈ usedCoord} gvar_α (…)` to `∑_{ij} S_ij (…)`. -/
theorem sum_used_eq_sum_pairs {ι : Type*} [Fintype ι] [DecidableEq ι] {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (κ : ι → ℕ) (hκ : Function.Injective κ)
    (S : ι → ι → ℝ) (hS : ∀ i j, S i j = S j i)
    (f : ι × ι × Bool → V)
    (htt : ∀ i j, f (i, j, true) = f (j, i, true))
    (hff : ∀ i j, f (i, j, false) = f (j, i, false)) :
    ∑ p ∈ Finset.univ.filter
        (fun p : ι × ι × Bool => κ p.1 < κ p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)),
      (if p.1 = p.2.1 then S p.1 p.2.1 else S p.1 p.2.1 / 2) • f p
      = ∑ i : ι, ∑ j : ι, S i j •
          (if i = j then f (i, i, true)
           else (1 / 4 : ℝ) • (f (i, j, true) + f (i, j, false))) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine sum_sum_eq_of_swap_add_eq _ _ ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : ¬ (j = i) := fun hh => hij hh.symm
    rcases lt_trichotomy (κ i) (κ j) with hlt | heq | hgt
    · simp only [hij, hji, hlt, asymm hlt, hS j i, htt j i, hff j i, false_and, or_false,
        ite_true, ite_false, and_true, add_zero]
      exact smul_quarter_pair _ _ _
    · exact absurd (hκ heq) hij
    · simp only [hij, hji, hgt, asymm hgt, hS j i, htt j i, hff j i, false_and, or_false,
        ite_true, ite_false, and_true, add_zero, zero_add]
      exact smul_quarter_pair _ _ _

/-- The coordinate sum of the generator identity equals the paper's sum over index pairs. -/
theorem sum_used_eq_sum_pairs_coordD2 (h : TestFun d N Φ) (u : ℝ) :
    ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
        ∫ ω, coordD2 d N Φ (Hflow d N u ω) p ∂(P d)
      = ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          ∫ ω, wirtSecond d N Φ (Hflow d N u ω) i j ∂(P d) := by
  have hswap : ∀ (i j : d.Idx N) (b : Bool),
      (∫ ω, coordD2 d N Φ (Hflow d N u ω) (i, j, b) ∂(P d))
        = ∫ ω, coordD2 d N Φ (Hflow d N u ω) (j, i, b) ∂(P d) := fun i j b =>
    integral_congr_ae (Eventually.of_forall fun ω => coordD2_swap Φ _ i j b)
  have hlhs : ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) •
        ∫ ω, coordD2 d N Φ (Hflow d N u ω) p ∂(P d)
      = ∑ p ∈ usedCoord d N,
        (if p.1 = p.2.1 then Sblk (d.L N) (d.W N) p.1 p.2.1
         else Sblk (d.L N) (d.W N) p.1 p.2.1 / 2) •
        ∫ ω, coordD2 d N Φ (Hflow d N u ω) p ∂(P d) :=
    Finset.sum_congr rfl fun p _ => by rw [gvar_crd]
  rw [hlhs, show usedCoord d N = Finset.univ.filter
      (fun p : d.Idx N × d.Idx N × Bool =>
        idxKey d N p.1 < idxKey d N p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
    sum_used_eq_sum_pairs (idxKey d N) (idxKey_injective d N) (Sblk (d.L N) (d.W N))
      (Sblk_comm (d.L N) (d.W N)) _ (fun i j => hswap i j true) (fun i j => hswap i j false)]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [integral_wirtSecond h u i j]

/-- **The generator identity in the paper's form.**

`∂_u E[Φ(H_u)] = ½ ∑_i ∑_j S_ij E[∂_ij ∂_ji Φ(H_u)]`, with `∂_ij ∂_ji` the Wirtinger second
derivative `wirtSecond`. -/
theorem hasDerivAt_integral_Phi_pairs (hst : MatrixStein d) (h : TestFun d N Φ) {u : ℝ}
    (hu : 0 < u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ (Hflow d N s ω) ∂(P d))
      ((1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
        ∫ ω, wirtSecond d N Φ (Hflow d N u ω) i j ∂(P d)) u := by
  rw [← sum_used_eq_sum_pairs_coordD2 h u]
  exact hasDerivAt_integral_Phi hst h hu

end Wirtinger

/-! ### The Hermitian projection

`TestFun` asks for `Φ` to be `C²` and bounded on the **whole** matrix space, while the `Φ` of
the application, `|F(G(M))|^{2p}` with `G(M) = (M - z)⁻¹`, is only defined where `M - z` is
invertible — which for a non-Hermitian `M` can fail.  The fix costs nothing: pre-compose with
the `ℝ`-linear projection `M ↦ (M + Mᴴ)/2` onto the Hermitian matrices.  It is a continuous
linear map, hence `C^∞`; it is the identity on Hermitian matrices, so it changes neither the
value nor any directional derivative along a Hermitian direction at a Hermitian point — and
all our base points (`Hflow`) and directions (`Bmat`, on used coordinates) are Hermitian. -/

section HermProj

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `ℝ`-linear projection onto the Hermitian matrices, `M ↦ (M + Mᴴ)/2`, as a continuous
linear map (hence `C^∞`). -/
noncomputable def hermCLM (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
      map_add' := by
        intro M M'
        rw [Matrix.conjTranspose_add]
        module
      map_smul' := by
        intro r M
        rw [RingHom.id_apply, Matrix.conjTranspose_smul, star_trivial]
        module }

theorem hermCLM_apply (M : Matrix n n ℂ) :
    hermCLM n M = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M) := rfl

/-- The projection lands in the Hermitian matrices. -/
theorem isHermitian_hermCLM (M : Matrix n n ℂ) : (hermCLM n M).IsHermitian := by
  show Matrix.conjTranspose ((2⁻¹ : ℝ) • (M + Matrix.conjTranspose M))
      = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]

/-- The projection is the identity on Hermitian matrices. -/
theorem hermCLM_of_isHermitian {M : Matrix n n ℂ} (hM : M.IsHermitian) : hermCLM n M = M := by
  rw [hermCLM_apply, hM]
  module

end HermProj


end RBM.Gauss


