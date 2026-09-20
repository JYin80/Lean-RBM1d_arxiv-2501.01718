/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Model
import RBM1D.Gauss.Domination
import RBM1D.Gauss.Moments
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Algebra.Order.Chebyshev

/-!
# The operator norm of the Gaussian band matrix: `‖X‖ ≺ 1` (T100)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*: the operator-norm bound
`‖X‖ ≺ 1` for the Gaussian band matrix `X` of `RBM1D/Gauss/Model.lean`, i.e. the field
`RBM.Gauss.OpNormBound.norm_X`.  This is the gap recorded in `docs/paper-deltas.md` #49.

## The route: `E‖X‖^{2p} ≤ E Tr(X^{2p})`, then Markov

Everything except the combinatorics of the trace is done here.  The chain is

1. `RBM.Gauss.l2_opNorm_sq_le_frobSq` : `‖A‖² ≤ ∑_{ij} |A_ij|²` (Cauchy–Schwarz on the rows);
2. `RBM.Gauss.l2_opNorm_pow_two_pow` : `‖A^{2^m}‖ = ‖A‖^{2^m}` for Hermitian `A`, by iterating
   the `C*`-identity `‖AᴴA‖ = ‖A‖²` (`Matrix.l2_opNorm_conjTranspose_mul_self`);
3. hence `RBM.Gauss.l2_opNorm_pow_le_frobSq` : `‖A‖^{2q} ≤ ∑_{ij} |(A^q)_{ij}|²` for `q = 2^m`,
   which by `RBM.Gauss.trace_pow_eq_frobSq` is exactly `‖A‖^{2q} ≤ Tr(A^{2q})`;
4. `RBM.Gauss.integrable_norm_Xmat_pow` : all moments of `‖X‖` exist (`‖X‖²` is dominated by
   `2 ∑_c ω_c²`, a finite sum of squares of the independent Gaussian coordinates);
5. `RBM.Gauss.momentDom_norm_Xmat` : the trace bound `E Tr(X^{2p}) ≤ C_p N` is turned into the
   `RBM.Gauss.MomentDom` input of T73.  The factor `N` is *not* of the form `N^{εp}` for small
   `ε`, so one first goes to a high power: `RBM.Gauss.pow_le_add_inv_mul_pow` gives
   `g^{2p} ≤ M^{2p} + M^{-2r} g^{2(p+r)}`, and with `M = N^{ε/2}`, `q = p + r = 2^m` and
   `εr ≥ 1` the second term is `O(1)`, leaving `E‖X‖^{2p} ≤ (1 + C_q) N^{εp}`;
6. `RBM.Gauss.stochDom_norm_Xmat` : `RBM.Gauss.stochDom_one_of_momentDom` (T73) with the
   one-point parameter set `Unit`, giving literally
   `RBM.StochDom (P d) (fun N _ ω => ‖Xmat d N ω‖) (fun _ _ _ => 1)`;
7. `RBM.Gauss.opNormBound_of_traceMomentBound` : the `OpNormBound` structure.

## The one remaining hypothesis

`RBM.Gauss.TraceMomentBound d`:

  `∀ p, ∃ C > 0, ∀ᶠ N, E [∑_{ij} |(X^p)_{ij}|²] ≤ C · N`,  i.e.  `E Tr(X^{2p}) ≤ C_p N`.

This is the walk-counting half of the moment method and it is **not proved here**.  What it
needs, and what Mathlib does not have, is:

* Wick's (Isserlis') formula for the family `{X_ij}`, or at least the two facts that the
  expectation factorises over the independent pairs `{i,j}` and that `E[z^m z̄^n] = 0` for
  `m ≠ n`, so that only closed walks traversing every edge at least twice survive;
* the counting of such walks: a closed walk of length `2p` with every edge repeated visits at
  most `p + 1` distinct vertices, and the band support of `S` (`RBM.sbSupport`,
  `RBM.Sblk_le : S_ij ≤ W⁻¹` on the band) bounds the number of them by `O(N · W^p)` while
  each contributes `O(p! · W^{-p})`, giving `C_p N`.

The `p = 1` case *is* proved unconditionally, as `RBM.Gauss.traceMomentBound_one`: there
`E Tr(X²) = ∑_{ij} S_ij = W·L ≤ N` by `RBM.sum_Sblk_row` and `RBM.Gauss.Dims.dim`.  It is the
sanity check that the constant in `TraceMomentBound` is the right shape.

## Main definitions

* `RBM.Gauss.frobSq` — `∑_{ij} |A_ij|²`, written out so as not to depend on which scoped
  matrix-norm instance is open.
* `RBM.Gauss.TraceMomentBound` — the combinatorial input `E Tr(X^{2p}) ≤ C_p N`.

## Main results

* `RBM.Gauss.l2_opNorm_sq_le_frobSq`, `RBM.Gauss.norm_entry_le_l2_opNorm`,
  `RBM.Gauss.l2_opNorm_pow_two_pow`, `RBM.Gauss.l2_opNorm_pow_le_frobSq`,
  `RBM.Gauss.trace_pow_eq_frobSq` — the deterministic half.
* `RBM.Gauss.measurable_norm_Xmat`, `RBM.Gauss.integrable_norm_Xmat_pow`,
  `RBM.Gauss.integrable_frobSq_Xmat_pow` — measurability and all moments.
* `RBM.Gauss.traceMomentBound_one` — `E Tr(X²) = W·L`, unconditionally.
* `RBM.Gauss.stochDom_norm_Xmat`, `RBM.Gauss.opNormBound_of_traceMomentBound` — `‖X‖ ≺ 1`
  and the `OpNormBound` of `RBM1D/Gauss/Model.lean`, **granted `TraceMomentBound`**.

## What is **not** done here

`RBM.Gauss.TraceMomentBound` itself, for `p ≥ 2`.  No `sorry` and no `axiom` is used: the
statement is carried as a hypothesis, exactly like the fields of `RBM.Bounds` in
`RBM1D/Flow/Hypotheses.lean` and like `OpNormBound` itself was.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ### Deterministic linear algebra -/

section Deterministic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **squared Frobenius norm** `∑_{ij} |A_ij|²` of a matrix, written out as a sum so that
it does not depend on which of Mathlib's scoped matrix-norm instances is open.  For a Hermitian
`A` one has `frobSq (A ^ p) = Tr (A ^ (2p))`. -/
noncomputable def frobSq (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq n] in
theorem frobSq_nonneg (A : Matrix n n ℂ) : 0 ≤ frobSq A := by
  unfold frobSq; positivity

/-- **The operator norm is bounded by the Frobenius norm**: `‖A‖² ≤ ∑_{ij} |A_ij|²`. -/
theorem l2_opNorm_sq_le_frobSq (A : Matrix n n ℂ) : ‖A‖ ^ 2 ≤ frobSq A := by
  have hF0 : 0 ≤ frobSq A := frobSq_nonneg A
  have hbd : ‖A‖ ≤ Real.sqrt (frobSq A) := by
    rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have hsq : ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x‖ ^ 2 ≤ frobSq A * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, frobSq, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have hrow : ‖((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x).ofLp i‖
          ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
        rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hrow 2) ?_
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    nlinarith [Real.sq_sqrt hF0, norm_nonneg ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x),
      norm_nonneg x, Real.sqrt_nonneg (frobSq A),
      mul_nonneg (Real.sqrt_nonneg (frobSq A)) (norm_nonneg x)]
  nlinarith [Real.sq_sqrt hF0, norm_nonneg A, Real.sqrt_nonneg (frobSq A)]

/-- Every entry of a matrix is bounded by its `ℓ² → ℓ²` operator norm. -/
theorem norm_entry_le_l2_opNorm (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  set x : EuclideanSpace ℂ n := WithLp.toLp 2 (Pi.single j (1 : ℂ)) with hx
  have hxnorm : ‖x‖ = 1 := by
    have : ‖x‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      rw [Finset.sum_eq_single j]
      · simp [hx]
      · intro b _ hb; simp [hx, hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    nlinarith [norm_nonneg x, this]
  have hval : ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x).ofLp i = A i j := by
    rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j]
    · simp [hx]
    · intro b _ hb; simp [hx, hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hle : ‖((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x).ofLp i‖ ^ 2
      ≤ ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (f := fun k => ‖((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A)
      x).ofLp k‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  have hop : ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x‖ ≤ ‖A‖ := by
    have := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm x
    rw [hxnorm, mul_one] at this
    rwa [← Matrix.cstar_norm_def] at this
  rw [hval] at hle
  nlinarith [norm_nonneg (A i j), norm_nonneg ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x),
    norm_nonneg A]

/-- The Frobenius norm is bounded by the operator norm, at the cost of a factor `(card n)²`. -/
theorem frobSq_le_card_sq_mul (A : Matrix n n ℂ) :
    frobSq A ≤ (Fintype.card n : ℝ) ^ 2 * ‖A‖ ^ 2 := by
  have h : ∀ i : n, ∑ j : n, ‖A i j‖ ^ 2 ≤ (Fintype.card n : ℝ) * ‖A‖ ^ 2 := by
    intro i
    calc ∑ j : n, ‖A i j‖ ^ 2 ≤ ∑ _j : n, ‖A‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _)
            (norm_entry_le_l2_opNorm A i j) 2
      _ = (Fintype.card n : ℝ) * ‖A‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc frobSq A ≤ ∑ _i : n, (Fintype.card n : ℝ) * ‖A‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = (Fintype.card n : ℝ) ^ 2 * ‖A‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- For a Hermitian matrix, `‖A^{2^m}‖ = ‖A‖^{2^m}`: the `C*`-identity `‖A*A‖ = ‖A‖²`,
iterated. -/
theorem l2_opNorm_pow_two_pow {A : Matrix n n ℂ} (hA : A.IsHermitian) (m : ℕ) :
    ‖A ^ 2 ^ m‖ = ‖A‖ ^ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hB : (A ^ 2 ^ m).IsHermitian := hA.pow _
    have hstep : A ^ 2 ^ (m + 1) = (A ^ 2 ^ m)ᴴ * A ^ 2 ^ m := by
      rw [hB]
      rw [← pow_add]
      congr 1
      rw [pow_succ]
      ring
    rw [hstep, Matrix.l2_opNorm_conjTranspose_mul_self, ih, ← pow_add]
    congr 1
    rw [pow_succ]
    ring

/-- **The moment-method inequality** `‖A‖^{2q} ≤ Tr(A^{2q})` at `q = 2^m`, written with the
Frobenius norm of `A^{2^m}` (which is `Tr(A^{2^{m+1}})` for Hermitian `A`). -/
theorem l2_opNorm_pow_le_frobSq {A : Matrix n n ℂ} (hA : A.IsHermitian) (m : ℕ) :
    ‖A‖ ^ (2 * 2 ^ m) ≤ frobSq (A ^ 2 ^ m) := by
  have h1 : ‖A‖ ^ (2 * 2 ^ m) = ‖A ^ 2 ^ m‖ ^ 2 := by
    rw [l2_opNorm_pow_two_pow hA, ← pow_mul, mul_comm]
  rw [h1]
  exact l2_opNorm_sq_le_frobSq _

/-- **`∑_{ij} |(A^p)_{ij}|² = Tr(A^{2p})`** for Hermitian `A`: `frobSq (A ^ p)` really is the
`2p`-th trace moment of the paper. -/
theorem trace_pow_eq_frobSq {A : Matrix n n ℂ} (hA : A.IsHermitian) (p : ℕ) :
    (A ^ (2 * p)).trace = (frobSq (A ^ p) : ℂ) := by
  have h1 : A ^ (2 * p) = (A ^ p)ᴴ * A ^ p := by
    rw [hA.pow p, ← pow_add]; congr 1; ring
  have h2 : ((A ^ p)ᴴ * A ^ p).trace = ((∑ i, ∑ j, ‖(A ^ p) j i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.trace, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_apply, ← starRingEnd_apply, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [h1, h2, frobSq]
  congr 1
  exact Finset.sum_comm

end Deterministic

/-! ### Measurability and integrability

`‖X‖` is a continuous function of the (measurable) entries, and it is dominated by a finite
sum of squares of the independent Gaussian coordinates, so all its moments exist. -/

section Integrability

variable (d : Dims) (N : ℕ)

/-- `ω ↦ X(ω)` is measurable (the matrix measurable space is the entrywise one). -/
theorem measurable_Xmat : Measurable fun ω : Ω d => Xmat d N ω :=
  Measurable.of_eval_matrix _ fun i j => measurable_Xentry d N i j

/-- `ω ↦ ‖X(ω)‖` is measurable. -/
theorem measurable_norm_Xmat : Measurable fun ω : Ω d => ‖Xmat d N ω‖ :=
  continuous_norm.measurable.comp (measurable_Xmat d N)

/-- Every polynomial moment of a single coordinate exists.  (The `k = 2` case is
`RBM.Gauss.integrable_sq_coord`.) -/
theorem integrable_pow_coord (c : Coord d) (k : ℕ) :
    Integrable (fun ω : Ω d => (ω c) ^ k) (P d) := by
  have hf : AEMeasurable (fun ω : Ω d => ω c) (P d) := (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ k) ((P d).map fun ω => ω c) := by
    rw [P_map_eval]
    exact RBM.integrable_pow_gaussianReal _ k
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

/-- The sum of the squares of all coordinates that `X` at size parameter `N` can read. -/
noncomputable def coordSq (ω : Ω d) : ℝ := ∑ t : d.Idx N × d.Idx N × Bool, (ω ⟨N, t⟩) ^ 2

theorem coordSq_nonneg (ω : Ω d) : 0 ≤ coordSq d N ω := by
  unfold coordSq; positivity

variable {d N}

/-- Each `|X_ij|²` is bounded by the four coordinates of the pairs `(i,j)` and `(j,i)`. -/
theorem normSq_Xentry_le (ω : Ω d) (i j : d.Idx N) :
    ‖Xentry d N ω i j‖ ^ 2
      ≤ (∑ b : Bool, (ω ⟨N, i, j, b⟩) ^ 2) + ∑ b : Bool, (ω ⟨N, j, i, b⟩) ^ 2 := by
  have hexp : ∀ (x y : d.Idx N), (∑ b : Bool, (ω ⟨N, x, y, b⟩) ^ 2)
      = (ω ⟨N, x, y, true⟩) ^ 2 + (ω ⟨N, x, y, false⟩) ^ 2 := by
    intro x y; rw [Fintype.sum_bool]
  rw [hexp, hexp]
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · have hX : ‖Xentry d N ω i j‖ ^ 2
        = (ω ⟨N, i, j, true⟩) ^ 2 + (ω ⟨N, i, j, false⟩) ^ 2 := by
      rw [Xentry, ite_eq_left h, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    rw [hX]
    nlinarith [sq_nonneg (ω ⟨N, j, i, true⟩), sq_nonneg (ω ⟨N, j, i, false⟩)]
  · subst h
    have hX : ‖Xentry d N ω i i‖ ^ 2 = (ω ⟨N, i, i, true⟩) ^ 2 := by
      rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    rw [hX]
    nlinarith [sq_nonneg (ω ⟨N, i, i, false⟩)]
  · have hX : ‖Xentry d N ω i j‖ ^ 2
        = (ω ⟨N, j, i, true⟩) ^ 2 + (ω ⟨N, j, i, false⟩) ^ 2 := by
      rw [Xentry, ite_eq_right (asymm h), ite_eq_left h, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    rw [hX]
    nlinarith [sq_nonneg (ω ⟨N, i, j, true⟩), sq_nonneg (ω ⟨N, i, j, false⟩)]

/-- **The deterministic domination**: `∑_{ij} |X_ij|² ≤ 2 ∑_c ω_c²`. -/
theorem frobSq_Xmat_le (ω : Ω d) : frobSq (Xmat d N ω) ≤ 2 * coordSq d N ω := by
  have hsplit : coordSq d N ω
      = ∑ i : d.Idx N, ∑ j : d.Idx N, ∑ b : Bool, (ω ⟨N, i, j, b⟩) ^ 2 := by
    unfold coordSq; simp [Fintype.sum_prod_type]
  have hswap : (∑ i : d.Idx N, ∑ j : d.Idx N, ∑ b : Bool, (ω ⟨N, j, i, b⟩) ^ 2)
      = ∑ i : d.Idx N, ∑ j : d.Idx N, ∑ b : Bool, (ω ⟨N, i, j, b⟩) ^ 2 :=
    Finset.sum_comm
  have hmain : frobSq (Xmat d N ω)
      ≤ (∑ i : d.Idx N, ∑ j : d.Idx N, ∑ b : Bool, (ω ⟨N, i, j, b⟩) ^ 2)
        + ∑ i : d.Idx N, ∑ j : d.Idx N, ∑ b : Bool, (ω ⟨N, j, i, b⟩) ^ 2 := by
    unfold frobSq
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => normSq_Xentry_le ω i j
  rw [hswap] at hmain
  rw [hsplit]
  linarith

variable (d N)

/-- All moments of `‖X‖` exist. -/
theorem integrable_norm_Xmat_pow (p : ℕ) :
    Integrable (fun ω : Ω d => ‖Xmat d N ω‖ ^ (2 * p)) (P d) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp only [Nat.mul_zero, pow_zero]
    exact integrable_const (1 : ℝ)
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  set s : Finset (d.Idx N × d.Idx N × Bool) := Finset.univ with hs
  -- the dominating function
  set G : Ω d → ℝ := fun ω =>
    2 ^ (k + 1) * ((s.card : ℝ) ^ k * ∑ t ∈ s, ((ω ⟨N, t⟩) ^ 2) ^ (k + 1)) with hG
  have hGint : Integrable G (P d) := by
    refine Integrable.const_mul (Integrable.const_mul ?_ _) _
    refine integrable_finsetSum _ fun t _ => ?_
    have := integrable_pow_coord d ⟨N, t⟩ (2 * (k + 1))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [← pow_mul]
  refine Integrable.mono' hGint
    (((measurable_norm_Xmat d N).pow_const _).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ ‖Xmat d N ω‖ ^ (2 * (k + 1)) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have h1 : ‖Xmat d N ω‖ ^ (2 * (k + 1)) = (‖Xmat d N ω‖ ^ 2) ^ (k + 1) := by
    rw [← pow_mul, mul_comm]
  have h2 : (‖Xmat d N ω‖ ^ 2) ^ (k + 1) ≤ (2 * coordSq d N ω) ^ (k + 1) :=
    pow_le_pow_left₀ (by positivity)
      ((l2_opNorm_sq_le_frobSq _).trans (frobSq_Xmat_le ω)) _
  have h3 : (2 * coordSq d N ω) ^ (k + 1)
      = 2 ^ (k + 1) * (∑ t ∈ s, (ω ⟨N, t⟩) ^ 2) ^ (k + 1) := by
    rw [mul_pow]; rfl
  have h4 : (∑ t ∈ s, (ω ⟨N, t⟩) ^ 2) ^ (k + 1)
      ≤ (s.card : ℝ) ^ k * ∑ t ∈ s, ((ω ⟨N, t⟩) ^ 2) ^ (k + 1) :=
    pow_sum_le_card_mul_sum_pow (fun t _ => by positivity) k
  rw [h1]
  refine h2.trans ?_
  rw [h3, hG]
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

/-- `ω ↦ X(ω)^p` is measurable. -/
theorem measurable_Xmat_pow (p : ℕ) : Measurable fun ω : Ω d => Xmat d N ω ^ p := by
  induction p with
  | zero =>
    simp only [pow_zero]
    exact measurable_const
  | succ p ih =>
    refine Measurable.of_eval_matrix _ fun i j => ?_
    have : ∀ ω : Ω d, (Xmat d N ω ^ (p + 1)) i j
        = ∑ k, (Xmat d N ω ^ p) i k * Xmat d N ω k j := by
      intro ω; rw [pow_succ, Matrix.mul_apply]
    simp only [this]
    exact Finset.measurable_sum _ fun k _ =>
      (ih.eval_matrix).mul ((measurable_Xmat d N).eval_matrix)

/-- `ω ↦ ∑_{ij} |(X^p)_{ij}|²` is measurable. -/
theorem measurable_frobSq_Xmat_pow (p : ℕ) :
    Measurable fun ω : Ω d => frobSq (Xmat d N ω ^ p) := by
  unfold frobSq
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    ((measurable_Xmat_pow d N p).eval_matrix).norm.pow_const 2

/-- `Tr(X^{2p}) = ∑_{ij} |(X^p)_{ij}|²` is integrable. -/
theorem integrable_frobSq_Xmat_pow (p : ℕ) (hp : 0 < p) :
    Integrable (fun ω : Ω d => frobSq (Xmat d N ω ^ p)) (P d) := by
  refine Integrable.mono'
    (g := fun ω : Ω d => (Fintype.card (d.Idx N) : ℝ) ^ 2 * ‖Xmat d N ω‖ ^ (2 * p))
    ((integrable_norm_Xmat_pow d N p).const_mul _)
    (measurable_frobSq_Xmat_pow d N p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (frobSq_nonneg _)]
  refine (frobSq_le_card_sq_mul _).trans ?_
  have hpow : ‖Xmat d N ω ^ p‖ ≤ ‖Xmat d N ω‖ ^ p := norm_pow_le' _ hp
  have h2 : ‖Xmat d N ω ^ p‖ ^ 2 ≤ (‖Xmat d N ω‖ ^ p) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hpow 2
  have h3 : (‖Xmat d N ω‖ ^ p) ^ 2 = ‖Xmat d N ω‖ ^ (2 * p) := by
    rw [← pow_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← h3]; exact h2

end Integrability

/-! ### From the trace moments to `≺` -/

section Reduction

/-- **The combinatorial input of the moment method.**

`E Tr(X^{2p}) ≤ C_p N` for every `p`, eventually in `N`, with a constant `C_p` that does not
depend on `N`.  The trace is written as `∑_{ij} |(X^p)_{ij}|²`, which equals `Tr(X^{2p})`
because `X` is Hermitian.

This is exactly the output of the moment (walk-counting) method for a band matrix with
`∑_j S_ij = 1`: after Wick's formula only walks in which every edge is used at least twice
survive, such a walk of length `2p` visits at most `p + 1` distinct vertices, and the band
structure of `S` makes the number of such walks `O(N · W^p)` while each contributes
`O(W^{-p})`.  **It is not proved in this file**; see the file header. -/
def TraceMomentBound (d : Dims) : Prop :=
  ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    ∫ ω, frobSq (Xmat d N ω ^ p) ∂(P d) ≤ C * N

/-- `|X_ij|²` is integrable. -/
theorem integrable_normSq_Xentry (d : Dims) (N : ℕ) (i j : d.Idx N) :
    Integrable (fun ω : Ω d => ‖Xentry d N ω i j‖ ^ 2) (P d) := by
  refine Integrable.mono'
    (g := fun ω : Ω d => (∑ b : Bool, (ω ⟨N, i, j, b⟩) ^ 2) + ∑ b : Bool, (ω ⟨N, j, i, b⟩) ^ 2)
    ((integrable_finsetSum _ fun b _ => integrable_pow_coord d ⟨N, i, j, b⟩ 2).add
      (integrable_finsetSum _ fun b _ => integrable_pow_coord d ⟨N, j, i, b⟩ 2))
    (((measurable_Xentry d N i j).norm.pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact normSq_Xentry_le ω i j

/-- **`E Tr(X²) = ∑_{ij} S_ij = W·L`**, unconditionally: the `p = 1` case of
`RBM.Gauss.TraceMomentBound`.  It is the sanity check that the normalisation
`∑_j S_ij = 1` (`RBM.sum_Sblk_row`) really produces a factor `N` and not more. -/
theorem integral_frobSq_Xmat_one (d : Dims) (N : ℕ) :
    ∫ ω, frobSq (Xmat d N ω ^ 1) ∂(P d) = ((d.L N * d.W N : ℕ) : ℝ) := by
  have hrow : ∀ i : d.Idx N, ∑ j, Sblk (d.L N) (d.W N) i j = 1 :=
    fun i => RBM.sum_Sblk_row (d.three_le_L N) i
  have hinner : ∀ i : d.Idx N,
      ∫ ω, ∑ j, ‖Xentry d N ω i j‖ ^ 2 ∂(P d) = ∑ j, Sblk (d.L N) (d.W N) i j := by
    intro i
    rw [integral_finsetSum _ fun j _ => integrable_normSq_Xentry d N i j]
    exact Finset.sum_congr rfl fun j _ => integral_normSq_Xentry d N i j
  simp only [pow_one]
  unfold frobSq
  simp only [Xmat_apply]
  rw [integral_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_normSq_Xentry d N i j]
  simp only [hinner, hrow]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  norm_cast
  simp [ZMod.card, mul_comm]

/-- The `p = 1` case of `RBM.Gauss.TraceMomentBound`, with the constant `C = 1`. -/
theorem traceMomentBound_one (d : Dims) :
    ∀ᶠ N : ℕ in atTop, ∫ ω, frobSq (Xmat d N ω ^ 1) ∂(P d) ≤ 1 * (N : ℝ) := by
  filter_upwards [d.dim] with N hN
  rw [integral_frobSq_Xmat_one, one_mul]
  have h : d.W N * d.L N ≤ N := hN.1
  have h' : d.L N * d.W N ≤ N := by rw [Nat.mul_comm]; exact h
  exact_mod_cast h'

/-- The elementary splitting `g^{2p} ≤ M^{2p} + M^{-2r} g^{2(p+r)}`, valid for every `g ≥ 0`
and `M > 0`.  It is what converts a moment bound with a factor `N` into one with a factor
`N^{εp}`: taking `M = N^{ε/2}` and `r` with `εr ≥ 1` the second term is `O(1)`. -/
theorem pow_le_add_inv_mul_pow {g M : ℝ} (hg : 0 ≤ g) (hM : 0 < M) (p r : ℕ) :
    g ^ (2 * p) ≤ M ^ (2 * p) + (M ^ (2 * r))⁻¹ * g ^ (2 * (p + r)) := by
  have hsplit : g ^ (2 * (p + r)) = g ^ (2 * p) * g ^ (2 * r) := by
    rw [← pow_add]; congr 1; ring
  rcases le_or_gt g M with h | h
  · have h1 : g ^ (2 * p) ≤ M ^ (2 * p) := pow_le_pow_left₀ hg h _
    have h2 : 0 ≤ (M ^ (2 * r))⁻¹ * g ^ (2 * (p + r)) := by positivity
    linarith
  · have hMr : M ^ (2 * r) ≤ g ^ (2 * r) := pow_le_pow_left₀ hM.le h.le _
    have hMrpos : (0 : ℝ) < M ^ (2 * r) := by positivity
    have hkey : g ^ (2 * p) * M ^ (2 * r) ≤ g ^ (2 * (p + r)) := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hMr (by positivity)
    have h3 : g ^ (2 * p) ≤ (M ^ (2 * r))⁻¹ * g ^ (2 * (p + r)) := by
      rw [← le_div_iff₀ hMrpos, div_eq_inv_mul] at hkey
      exact hkey
    have h4 : (0 : ℝ) ≤ M ^ (2 * p) := by positivity
    linarith

variable {d : Dims}

/-- **`E‖X‖^{2q} ≤ E Tr(X^{2q})` at `q = 2^m`**: the moment-method inequality, integrated. -/
theorem integral_norm_Xmat_pow_le (N m : ℕ) :
    ∫ ω, ‖Xmat d N ω‖ ^ (2 * 2 ^ m) ∂(P d)
      ≤ ∫ ω, frobSq (Xmat d N ω ^ 2 ^ m) ∂(P d) :=
  integral_mono (integrable_norm_Xmat_pow d N (2 ^ m))
    (integrable_frobSq_Xmat_pow d N (2 ^ m) (by positivity))
    fun ω => l2_opNorm_pow_le_frobSq (Xmat_isHermitian d N ω) m

/-- **The moment input of `RBM.Gauss.stochDom_one_of_momentDom`**, produced from the trace
moments.  The factor `N` of `TraceMomentBound` is traded for `N^{εp}` by
`RBM.Gauss.pow_le_add_inv_mul_pow` at `M = N^{ε/2}` and a large power `q = 2^m`. -/
theorem momentDom_norm_Xmat (h : TraceMomentBound d) (ε : ℝ) (hε : 0 < ε) (p : ℕ) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ _u : Unit,
      ∫ ω, |‖Xmat d N ω‖| ^ (2 * p) ∂(P d) ≤ C * (N : ℝ) ^ (ε * p) := by
  -- choose `q = 2^m` with `q - p ≥ ⌈1/ε⌉`
  set m : ℕ := p + ⌈(1 : ℝ) / ε⌉₊ with hm
  set q : ℕ := 2 ^ m with hq
  have hmq : m < q := Nat.lt_two_pow_self
  have hpq : p ≤ q := by omega
  set r : ℕ := q - p with hr
  have hpr : p + r = q := by omega
  have hrge : ⌈(1 : ℝ) / ε⌉₊ ≤ r := by omega
  have hεr : (1 : ℝ) ≤ ε * r := by
    have h1 : (1 : ℝ) / ε ≤ (⌈(1 : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(1 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrge
    have h3 : (1 : ℝ) / ε ≤ (r : ℝ) := le_trans h1 h2
    rw [div_le_iff₀ hε] at h3
    linarith [h3]
  obtain ⟨C, hC0, hCN⟩ := h q
  refine ⟨1 + C, by linarith, ?_⟩
  filter_upwards [hCN, eventually_ge_atTop 1] with N hN hN1 _u
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  set M : ℝ := (N : ℝ) ^ (ε / 2) with hM
  have hMpos : 0 < M := Real.rpow_pos_of_pos hNpos _
  -- the two explicit powers of `M`
  have hMp : M ^ (2 * p) = (N : ℝ) ^ (ε * p) := by
    rw [hM, ← Real.rpow_natCast ((N : ℝ) ^ (ε / 2)) (2 * p), ← Real.rpow_mul hNpos.le]
    congr 1
    push_cast
    ring
  have hMr : (N : ℝ) ≤ M ^ (2 * r) := by
    have : M ^ (2 * r) = (N : ℝ) ^ (ε * r) := by
      rw [hM, ← Real.rpow_natCast ((N : ℝ) ^ (ε / 2)) (2 * r), ← Real.rpow_mul hNpos.le]
      congr 1
      push_cast
      ring
    rw [this]
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (ε * r) := Real.rpow_le_rpow_of_exponent_le hN1' hεr
  -- integrate the pointwise splitting
  have hpt : ∀ ω : Ω d, |‖Xmat d N ω‖| ^ (2 * p)
      ≤ M ^ (2 * p) + (M ^ (2 * r))⁻¹ * ‖Xmat d N ω‖ ^ (2 * q) := by
    intro ω
    rw [abs_of_nonneg (norm_nonneg _), ← hpr]
    exact pow_le_add_inv_mul_pow (norm_nonneg _) hMpos p r
  have hint1 : Integrable (fun ω : Ω d => |‖Xmat d N ω‖| ^ (2 * p)) (P d) := by
    refine (integrable_norm_Xmat_pow d N p).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [abs_norm]
  have hint2 : Integrable (fun ω : Ω d =>
      M ^ (2 * p) + (M ^ (2 * r))⁻¹ * ‖Xmat d N ω‖ ^ (2 * q)) (P d) :=
    (integrable_const _).add ((integrable_norm_Xmat_pow d N q).const_mul _)
  have hstep := integral_mono hint1 hint2 hpt
  rw [integral_add (integrable_const _) ((integrable_norm_Xmat_pow d N q).const_mul _),
    integral_const, integral_const_mul] at hstep
  simp only [probReal_univ, smul_eq_mul, one_mul] at hstep
  -- bound the second term by `C`
  have htrace : ∫ ω, ‖Xmat d N ω‖ ^ (2 * q) ∂(P d) ≤ C * N := le_trans
    (integral_norm_Xmat_pow_le (d := d) N m) hN
  have hMrpos : (0 : ℝ) < M ^ (2 * r) := by positivity
  have hsecond : (M ^ (2 * r))⁻¹ * ∫ ω, ‖Xmat d N ω‖ ^ (2 * q) ∂(P d) ≤ C := by
    have h1 : (M ^ (2 * r))⁻¹ * (∫ ω, ‖Xmat d N ω‖ ^ (2 * q) ∂(P d)) ≤ (M ^ (2 * r))⁻¹ * (C * N) :=
      mul_le_mul_of_nonneg_left htrace (by positivity)
    have h2 : (M ^ (2 * r))⁻¹ * (C * N) ≤ C := by
      rw [inv_mul_le_iff₀ hMrpos]
      nlinarith [hMr, hC0.le, hNpos.le]
    linarith
  have hNε : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) :=
    Real.one_le_rpow hN1' (by positivity)
  calc ∫ ω, |‖Xmat d N ω‖| ^ (2 * p) ∂(P d)
      ≤ M ^ (2 * p) + (M ^ (2 * r))⁻¹ * ∫ ω, ‖Xmat d N ω‖ ^ (2 * q) ∂(P d) := hstep
    _ ≤ (N : ℝ) ^ (ε * p) + C := by rw [hMp]; linarith
    _ ≤ (1 + C) * (N : ℝ) ^ (ε * p) := by nlinarith [hNε, hC0.le]

/-- **`‖X‖ ≺ 1`**, granted the trace moments.  This is exactly the field `norm_X` of
`RBM.Gauss.OpNormBound`. -/
theorem stochDom_norm_Xmat (h : TraceMomentBound d) :
    RBM.StochDom (P d) (fun N (_ : Unit) ω => ‖Xmat d N ω‖) fun _ _ _ => (1 : ℝ) := by
  refine stochDom_one_of_momentDom (Ccard := 0) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    simp [Real.rpow_zero]
  · intro p N _u
    refine (integrable_norm_Xmat_pow d N p).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [abs_norm]
  · intro ε hε p
    exact momentDom_norm_Xmat h ε hε p

/-- **The `OpNormBound` of `RBM1D/Gauss/Model.lean`, discharged from the trace moments.** -/
theorem opNormBound_of_traceMomentBound (h : TraceMomentBound d) : OpNormBound d :=
  ⟨stochDom_norm_Xmat h⟩

end Reduction

end RBM.Gauss
