/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Eq45FlowInputs

/-!
# The modulus of `E_k(G_{kk} - m)` in the time — T129

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, the `u`-uniformisation of (4.5) on p. 51.

`RBM1D/Gauss/Eq45FlowInputs.lean` (T124) reduces the three time-indexed inputs of (4.5) to a
time net, and the net needs a Hölder modulus in `u` for each dominated quantity.  For the
Green's function the modulus is `RBM.Gauss.norm_green_flow_sub_le` (T106); for
`RBM.Gauss.condExpDiag` it is *not* a corollary of that pointwise modulus, because the random
constant `‖X‖` of T106 sits **inside** the row-conditional-expectation integral:

  `E_k[G_u]‖ - E_k[G_v]` is `∫ (G_u - G_v)(rowSplit k ω ω') dP(ω')`,

and the pointwise bound on the integrand carries `‖X (rowSplit k ω ω')‖`, a norm of a matrix
whose row `k` is *resampled*, not the `‖X(ω)‖` that the good event controls.  This file supplies
the missing estimate.

## Step 0 (the route the ticket asks to test): the random constant, and `C ≺ 1`

The modulus is proved with the random constant `C(ω) = E_k[‖X‖](ω)` exactly as suggested, and
the constant is shown to be `≺ 1`.  What makes it work is that `E_k[‖X‖]` admits a **pointwise**
bound by a polynomial in `‖X(ω)‖`:

  `RBM.Gauss.integral_norm_Xmat_rowSplit_le` : `E_k[‖X‖](ω) ≤ ‖X(ω)‖ + 2‖X(ω)‖² + 5/2`.

Two remarks on how this is obtained, both of which matter:

* The T112 route (`RBM.Gauss.stochDom_condRow_of_envelope`, preservation of `≺` under `E_k`)
  is **not** used and could not be: it asks for a *deterministic* envelope for the dominated
  quantity, and `‖X‖` has none — the Gaussian coordinates are unbounded.  What replaces the
  envelope here is that the resampling touches **one row only**: writing
  `σ = rowSplit k ω ω'`, the matrices `X(σ)` and `X(ω)` differ only on row and column `k`
  (`RBM.Gauss.Xentry_rowSplit_of_row` together with `RBM.Gauss.Xentry_congr_of_ne`), so
  `‖X(σ) - X(ω)‖² ≤ ‖X(σ) - X(ω)‖_F² ≤ 2 rowFrobSq_k(ω') + 2 rowFrobSq_k(ω)`.  The `ω`-half is
  deterministic in `ω` (`rowFrobSq_k(ω) ≤ 2‖X(ω)‖²`, which is `∑_i |M_{ik}|² ≤ ‖M‖²`), and the
  `ω'`-half has an **exact** expectation, `∫ rowFrobSq_k ≤ ∑_j S_{kj} + ∑_i S_{ik} = 2`, by
  `RBM.Gauss.integral_normSq_Xentry` and `RBM.sum_Sblk_row`.  The square root is removed by the
  elementary `x ≤ (1 + x²)/2`, so no `∫ √· ≤ √∫·` is needed.
* `C ≺ 1` is then `RBM.Gauss.stochDom_condRow_norm_Xmat`, deduced from `‖X‖ ≺ 1` (T109,
  `RBM.Gauss.stochDom_norm_Xmat_gauss`) and the pointwise bound.  The square in the pointwise
  bound is why the deduction is not literally `StochDom.mono`: `‖X‖ ≤ N^{τ/4}` is what has to
  be assumed to conclude `‖X‖ + 2‖X‖² + 5/2 ≤ N^τ`.

## Does T124's net engine accept a random Hölder constant?

**Yes, in the only sense that is needed, and no reshaping of the engine is required.**
`RBM.Gauss.stochDom_timeIcc_of_unifDom` takes `hHol` with a deterministic constant `N^K` but
*restricted to a high-probability event* `Ξ`, and its own docstring points at this: "use
`RBM.StochDom.highProb` on `‖X‖ ≺ 1` to put a random constant there".  The event that T124
already uses, `RBM.Gauss.flowNetEvent`, contains `{‖X‖ ≤ N}`, and the constant of the modulus
proved here is a polynomial in `‖X(ω)‖` — so it is `≤ N^K` on that event.  This is the content
of `RBM.Gauss.norm_condExpDiag_flow_sub_le_rpow`.

The one genuinely new hypothesis this forces is the **regime bound on `η_{t_N}`**, `hK` below:
the modulus carries `η_u^{-1} η_v^{-1}`, and turning that into `N^K` needs
`η_{t_N}^{-1} ≤ N^{c}`.  This is the same `hη` that T125 had to carry explicitly in
`RBM1D/Gauss/Step1Hyp.lean`; it comes from (2.72) and is not proved here.

## Main definitions

* `RBM.Gauss.rowFrobSq` — `∑_{(i,j) : i = k ∨ j = k} |X_{ij}|²`, the Frobenius mass of row and
  column `k`.  It is the quantity that the resampling can change and whose expectation is `≤ 2`.

## Main results

* `RBM.Gauss.norm_Xmat_rowSplit_le` — the deterministic one-row perturbation estimate
  `‖X(rowSplit k ω ω')‖ ≤ ‖X(ω)‖ + 2‖X(ω)‖² + rowFrobSq_k(ω') + 1/2`.
* `RBM.Gauss.integral_norm_Xmat_rowSplit_le` — `E_k[‖X‖](ω) ≤ ‖X(ω)‖ + 2‖X(ω)‖² + 5/2`.
* `RBM.Gauss.stochDom_condRow_norm_Xmat` — **`E_k[‖X‖] ≺ 1`**, uniformly in `k`.
* `RBM.Gauss.norm_condExpDiag_flow_sub_le` — **the modulus**, with the random constant:
  `‖E_k(G_u)_{kk} - E_k(G_v)_{kk}‖ ≤ η_u^{-1}η_v^{-1}(|√u-√v|(‖X‖+2‖X‖²+5/2) + |u-v|)`.
* `RBM.Gauss.norm_condExpDiag_flow_sub_le_rpow` — the same in the `hHol` shape of
  `RBM.Gauss.stochDom_timeIcc_Lmax_of_unifDom`: on `RBM.Gauss.flowNetEvent`, with the
  deterministic constant `N^K` and the Hölder exponent `1/2`.
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset Matrix

open scoped Matrix.Norms.L2Operator

variable {d : Dims} {N : ℕ}

/-! ### The entries that the row-`k` resampling rewrites -/

/-- `RBM.Gauss.rowSplit` takes an entry on row or column `k` from the *second* argument.
This is the companion of `RBM.Gauss.Xentry_congr_of_ne`, which says that it takes every other
entry from the first. -/
theorem Xentry_rowSplit_of_row (d : Dims) (N : ℕ) (k : d.Idx N) (ω ω' : Ω d) {i j : d.Idx N}
    (h : i = k ∨ j = k) :
    Xentry d N (rowSplit d N k ω ω') i j = Xentry d N ω' i j := by
  have h1 : ∀ b : Bool, rowSplit d N k ω ω' ⟨N, i, j, b⟩ = ω' ⟨N, i, j, b⟩ := fun b =>
    rowSplit_apply_of_isRowCoord k ω ω' (by rw [isRowCoord_mk]; exact h)
  have h2 : ∀ b : Bool, rowSplit d N k ω ω' ⟨N, j, i, b⟩ = ω' ⟨N, j, i, b⟩ := fun b =>
    rowSplit_apply_of_isRowCoord k ω ω' (by rw [isRowCoord_mk]; exact h.symm)
  unfold Xentry
  split_ifs
  · rw [h1, h1]
  · rw [h2, h2]
  · rw [h1]

/-- **`∑_i |M_{ik}|² ≤ ‖M‖²`**: the `ℓ²` norm of a column is at most the operator norm.  It is
`(Mᴴ M)_{kk}` read off by `RBM.Gauss.norm_entry_le_l2_opNorm` and the C*-identity
`‖MᴴM‖ = ‖M‖²`.  Note this is *not* the crude `frobSq ≤ card · ‖M‖²`; the sharp form is what
keeps `RBM.Gauss.integral_norm_Xmat_rowSplit_le` free of a factor `N`, and hence what makes
`RBM.Gauss.stochDom_condRow_norm_Xmat` a `≺ 1` rather than a `≺ N`. -/
theorem sum_normSq_col_le {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (k : n) :
    ∑ i, ‖M i k‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  have hid : (Mᴴ * M) k k = ((∑ i, ‖M i k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  have h1 : ‖(Mᴴ * M) k k‖ ≤ ‖Mᴴ * M‖ := norm_entry_le_l2_opNorm _ k k
  rw [hid, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ∑ i, ‖M i k‖ ^ 2),
    Matrix.l2_opNorm_conjTranspose_mul_self] at h1
  rw [sq]
  exact h1

/-- A "row `k` or column `k`" double sum is at most the sum of the row and the column. -/
theorem sum_row_ite_le {f : d.Idx N → d.Idx N → ℝ} (hf : ∀ i j, 0 ≤ f i j) (k : d.Idx N) :
    ∑ i, ∑ j, (if i = k ∨ j = k then f i j else 0) ≤ (∑ j, f k j) + ∑ i, f i k := by
  have hterm : ∀ i j : d.Idx N, (if i = k ∨ j = k then f i j else 0)
      ≤ (if i = k then f i j else 0) + (if j = k then f i j else 0) := by
    intro i j
    by_cases h1 : i = k <;> by_cases h2 : j = k <;> simp [h1, h2, hf]
  have hsum : ∑ i, ∑ j, (if i = k ∨ j = k then f i j else 0)
      ≤ ∑ i, ∑ j, ((if i = k then f i j else 0) + (if j = k then f i j else 0)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  refine hsum.trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib]
  congr 1
  · have hstep : ∀ i : d.Idx N,
        (∑ j, if i = k then f i j else 0) = if i = k then ∑ j, f i j else 0 := by
      intro i; split_ifs <;> simp
    simp only [hstep]
    simp
  · rw [Finset.sum_comm]
    have hstep : ∀ j : d.Idx N,
        (∑ i, if j = k then f i j else 0) = if j = k then ∑ i, f i j else 0 := by
      intro j; split_ifs <;> simp
    simp only [hstep]
    simp

/-! ### `rowFrobSq`: the Frobenius mass of row and column `k` -/

/-- `∑_{(i,j) : i = k ∨ j = k} |X_{ij}|²`.  This is the only part of `X` that `E_k` resamples,
and the whole file rests on its two properties: it is `≤ 2‖X‖²` pointwise
(`RBM.Gauss.rowFrobSq_le`) and its expectation is `≤ 2` (`RBM.Gauss.integral_rowFrobSq_le`). -/
noncomputable def rowFrobSq (d : Dims) (N : ℕ) (k : d.Idx N) (ω : Ω d) : ℝ :=
  ∑ i, ∑ j, if i = k ∨ j = k then ‖Xentry d N ω i j‖ ^ 2 else 0

theorem rowFrobSq_nonneg (d : Dims) (N : ℕ) (k : d.Idx N) (ω : Ω d) :
    0 ≤ rowFrobSq d N k ω :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- The row-`k` mass of the resampled point is read entirely off the resampling copy. -/
theorem rowFrobSq_rowSplit (d : Dims) (N : ℕ) (k : d.Idx N) (ω ω' : Ω d) :
    rowFrobSq d N k (rowSplit d N k ω ω') = rowFrobSq d N k ω' := by
  unfold rowFrobSq
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [Xentry_rowSplit_of_row d N k ω ω' h]
  · rfl

/-- `rowFrobSq_k ≤ 2‖X‖²`: a row and a column each have `ℓ²` norm at most `‖X‖`. -/
theorem rowFrobSq_le (d : Dims) (N : ℕ) (k : d.Idx N) (ω : Ω d) :
    rowFrobSq d N k ω ≤ 2 * ‖Xmat d N ω‖ ^ 2 := by
  have hcol : ∑ i, ‖Xentry d N ω i k‖ ^ 2 ≤ ‖Xmat d N ω‖ ^ 2 :=
    sum_normSq_col_le (Xmat d N ω) k
  have hrow : ∑ j, ‖Xentry d N ω k j‖ ^ 2 ≤ ‖Xmat d N ω‖ ^ 2 := by
    have hswap : ∀ j : d.Idx N, ‖Xentry d N ω k j‖ = ‖Xentry d N ω j k‖ := by
      intro j; rw [Xentry_swap d N ω j k, RCLike.norm_conj]
    calc ∑ j, ‖Xentry d N ω k j‖ ^ 2 = ∑ j, ‖Xentry d N ω j k‖ ^ 2 := by
          exact Finset.sum_congr rfl fun j _ => by rw [hswap j]
      _ ≤ ‖Xmat d N ω‖ ^ 2 := hcol
  have h := sum_row_ite_le (f := fun i j => ‖Xentry d N ω i j‖ ^ 2)
    (fun i j => by positivity) k
  unfold rowFrobSq
  linarith

theorem integrable_rowFrobSq (d : Dims) (N : ℕ) (k : d.Idx N) :
    Integrable (fun ω : Ω d => rowFrobSq d N k ω) (P d) := by
  unfold rowFrobSq
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  by_cases h : i = k ∨ j = k
  · simpa [h] using integrable_normSq_Xentry d N i j
  · simp [h]

/-- **`E[rowFrobSq_k] ≤ 2`**, by `E|X_{ij}|² = S_{ij}` (`RBM.Gauss.integral_normSq_Xentry`) and
the normalisation `∑_j S_{kj} = 1` (`RBM.sum_Sblk_row`).  The two ones are the row and the
column; the diagonal is counted twice, which only helps. -/
theorem integral_rowFrobSq_le (d : Dims) (N : ℕ) (k : d.Idx N) :
    ∫ ω, rowFrobSq d N k ω ∂(P d) ≤ 2 := by
  have heq : ∫ ω, rowFrobSq d N k ω ∂(P d)
      = ∑ i, ∑ j, if i = k ∨ j = k then Sblk (d.L N) (d.W N) i j else 0 := by
    unfold rowFrobSq
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => by
      by_cases h : i = k ∨ j = k
      · simpa [h] using integrable_normSq_Xentry d N i j
      · simp [h]]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => by
      by_cases h : i = k ∨ j = k
      · simpa [h] using integrable_normSq_Xentry d N i j
      · simp [h]]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i = k ∨ j = k
    · simpa [h] using integral_normSq_Xentry d N i j
    · simp [h]
  rw [heq]
  have h := sum_row_ite_le (f := fun i j => Sblk (d.L N) (d.W N) i j)
    (fun i j => Sblk_nonneg i j) k
  have h1 : ∑ j, Sblk (d.L N) (d.W N) k j = 1 := RBM.sum_Sblk_row (d.three_le_L N) k
  have h2 : ∑ i, Sblk (d.L N) (d.W N) i k = 1 := by
    rw [show (fun i => Sblk (d.L N) (d.W N) i k) = fun i => Sblk (d.L N) (d.W N) k i from
      funext fun i => Sblk_comm _ _ i k]
    exact h1
  linarith

/-! ### `E_k[‖X‖]`: the random constant of the modulus -/

/-- **The one-row perturbation estimate.**  `X(rowSplit k ω ω')` and `X(ω)` differ only on row
and column `k`, so their difference has Frobenius mass `≤ 2 rowFrobSq_k(ω') + 2 rowFrobSq_k(ω)`;
`‖·‖ ≤ ‖·‖_F` and `x ≤ (1 + x²)/2` then remove the square root without any integration. -/
theorem norm_Xmat_rowSplit_le (d : Dims) (N : ℕ) (k : d.Idx N) (ω ω' : Ω d) :
    ‖Xmat d N (rowSplit d N k ω ω')‖
      ≤ ‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + rowFrobSq d N k ω' + 1 / 2 := by
  have hagree : AgreeOffRow d N k ω (rowSplit d N k ω ω') := agreeOffRow_rowSplit k ω ω'
  have hterm : ∀ i j : d.Idx N,
      ‖(Xmat d N (rowSplit d N k ω ω') - Xmat d N ω) i j‖ ^ 2
        ≤ 2 * (if i = k ∨ j = k then ‖Xentry d N ω' i j‖ ^ 2 else 0)
          + 2 * (if i = k ∨ j = k then ‖Xentry d N ω i j‖ ^ 2 else 0) := by
    intro i j
    by_cases h : i = k ∨ j = k
    · rw [ite_eq_left h, ite_eq_left h, Matrix.sub_apply, Xmat_apply, Xmat_apply,
        Xentry_rowSplit_of_row d N k ω ω' h]
      have h1 := norm_sub_le (Xentry d N ω' i j) (Xentry d N ω i j)
      nlinarith [norm_nonneg (Xentry d N ω' i j), norm_nonneg (Xentry d N ω i j),
        sq_nonneg (‖Xentry d N ω' i j‖ - ‖Xentry d N ω i j‖),
        norm_nonneg (Xentry d N ω' i j - Xentry d N ω i j)]
    · rw [not_or] at h
      rw [ite_eq_right (by rw [not_or]; exact h), ite_eq_right (by rw [not_or]; exact h),
        Matrix.sub_apply, Xmat_apply, Xmat_apply, ← Xentry_congr_of_ne hagree h.1 h.2]
      simp
  have hfrob : frobSq (Xmat d N (rowSplit d N k ω ω') - Xmat d N ω)
      ≤ 2 * rowFrobSq d N k ω' + 2 * rowFrobSq d N k ω := by
    unfold frobSq rowFrobSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hterm i j
  have h1 : ‖Xmat d N (rowSplit d N k ω ω') - Xmat d N ω‖ ^ 2
      ≤ 2 * rowFrobSq d N k ω' + 2 * rowFrobSq d N k ω :=
    (l2_opNorm_sq_le_frobSq _).trans hfrob
  have h2 : rowFrobSq d N k ω ≤ 2 * ‖Xmat d N ω‖ ^ 2 := rowFrobSq_le d N k ω
  have h3 : ‖Xmat d N (rowSplit d N k ω ω')‖ - ‖Xmat d N ω‖
      ≤ ‖Xmat d N (rowSplit d N k ω ω') - Xmat d N ω‖ := norm_sub_norm_le _ _
  nlinarith [sq_nonneg (‖Xmat d N (rowSplit d N k ω ω') - Xmat d N ω‖ - 1),
    norm_nonneg (Xmat d N (rowSplit d N k ω ω') - Xmat d N ω)]

/-- **`E_k[‖X‖](ω) ≤ ‖X(ω)‖ + 2‖X(ω)‖² + 5/2`.**  This is the step the ticket calls for: the
random constant of the modulus is bounded *pointwise* by a polynomial in `‖X(ω)‖`, so no
transfer of `≺` through the conditional expectation (T112) is needed — and none would be
available, `‖X‖` having no deterministic envelope. -/
theorem integral_norm_Xmat_rowSplit_le (d : Dims) (N : ℕ) (k : d.Idx N) (ω : Ω d) :
    ∫ ω', ‖Xmat d N (rowSplit d N k ω ω')‖ ∂(P d)
      ≤ ‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + 5 / 2 := by
  have hg : Integrable (fun ω' : Ω d =>
      rowFrobSq d N k ω' + (‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + 1 / 2)) (P d) :=
    (integrable_rowFrobSq d N k).add (integrable_const _)
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω' : Ω d => norm_nonneg (Xmat d N (rowSplit d N k ω ω')))
    hg (Filter.Eventually.of_forall fun ω' : Ω d => by
      linarith [norm_Xmat_rowSplit_le d N k ω ω'])
  refine hmono.trans ?_
  rw [integral_add (integrable_rowFrobSq d N k) (integrable_const _)]
  rw [integral_const, smul_eq_mul]
  have huniv : (P d).real Set.univ = 1 := by simp
  rw [huniv]
  linarith [integral_rowFrobSq_le d N k]

/-- **`E_k[‖X‖] ≺ 1`, uniformly in `k`** — the `C ≺ 1` of the ticket's step 0.  It is *not*
`RBM.Gauss.stochDom_condRow_of_envelope` (T112): that theorem needs a deterministic envelope,
which `‖X‖` does not have.  It is `‖X‖ ≺ 1` (T109) fed through the pointwise bound
`RBM.Gauss.integral_norm_Xmat_rowSplit_le`, at the cost of splitting `τ` into `τ/4` to absorb
the square. -/
theorem stochDom_condRow_norm_Xmat (d : Dims) :
    RBM.StochDom (P d) (U := fun N => d.Idx N)
      (fun N k ω => ∫ ω', ‖Xmat d N (rowSplit d N k ω ω')‖ ∂(P d))
      (fun _ _ _ => (1 : ℝ)) := by
  refine StochDom.of_subset_union (stochDom_norm_Xmat_gauss d) (stochDom_norm_Xmat_gauss d)
    fun τ hτ => ⟨τ / 4, by linarith, ?_⟩
  filter_upwards [eventually_le_rpow 2 (show (0:ℝ) < τ / 4 by linarith),
    eventually_ge_atTop 1] with N h2N hN1
  rintro ω ⟨k, hk⟩
  by_contra hno
  simp only [Set.mem_union, badSet, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  have hX : ‖Xmat d N ω‖ ≤ (N : ℝ) ^ (τ / 4) := by
    have := hno.1 (); simpa using this
  have hb := integral_norm_Xmat_rowSplit_le d N k ω
  have hNpos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hpow : ((N : ℝ) ^ (τ / 4)) ^ (4 : ℕ) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (τ / 4)) 4, ← Real.rpow_mul hNpos]
    norm_num
  have hy : (2 : ℝ) ≤ (N : ℝ) ^ (τ / 4) := h2N
  have hkey : (N : ℝ) ^ (τ / 4) + 2 * ((N : ℝ) ^ (τ / 4)) ^ 2 + 5 / 2
      ≤ ((N : ℝ) ^ (τ / 4)) ^ (4 : ℕ) := by
    set y : ℝ := (N : ℝ) ^ (τ / 4) with hy_def
    have h4 : (4 : ℝ) ≤ y ^ 2 := by nlinarith [hy]
    have h5 : 2 * y ≤ y ^ 2 := by nlinarith [hy]
    have hA : 4 * y ^ 2 ≤ (y ^ 2) ^ 2 := by nlinarith [h4]
    have hpow4 : y ^ (4 : ℕ) = (y ^ 2) ^ 2 := by ring
    linarith [hA, h5, hy, hpow4]
  have hX0 : (0 : ℝ) ≤ ‖Xmat d N ω‖ := norm_nonneg _
  have hsq : ‖Xmat d N ω‖ ^ 2 ≤ ((N : ℝ) ^ (τ / 4)) ^ 2 := by nlinarith [hX, hX0]
  rw [mul_one] at hk
  rw [hpow] at hkey
  linarith

/-! ### The modulus of `condExpDiag` in the time -/

/-- **The modulus of `E_k(G_{kk} - m)` in `u`, with the random constant.**

`RBM.Gauss.norm_green_flow_sub_le` (T106) applies to the *resampled* point
`rowSplit k ω ω'`, so the constant it produces is `‖X(rowSplit k ω ω')‖`, which lives inside
the integral.  `RBM.Gauss.norm_Xmat_rowSplit_le` splits that constant into a part depending
only on `ω` and the row mass `rowFrobSq_k(ω')`, and the latter integrates to `≤ 2`. -/
theorem norm_condExpDiag_flow_sub_le (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {u v : ℝ}
    (hu1 : u < 1) (hv1 : v < 1) (k : d.Idx N) (ω : Ω d) :
    ‖condExpDiag d N u (zt E u) (mE E) k ω - condExpDiag d N v (zt E v) (mE E) k ω‖
      ≤ (etaT E u)⁻¹ * (etaT E v)⁻¹
          * (|Real.sqrt u - Real.sqrt v| * (‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + 5 / 2)
            + |u - v|) := by
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hηv : 0 < etaT E v := etaT_pos_of_lt_one' hE hv1
  set c : ℝ := (etaT E u)⁻¹ * (etaT E v)⁻¹ with hc_def
  have hc0 : 0 ≤ c := by positivity
  set A : ℝ := ‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + 1 / 2 with hA_def
  set a : ℝ := c * |Real.sqrt u - Real.sqrt v| with ha_def
  have ha0 : 0 ≤ a := mul_nonneg hc0 (abs_nonneg _)
  set b : ℝ := c * (|Real.sqrt u - Real.sqrt v| * A + |u - v|) with hb_def
  -- step 1: the difference of the two conditional expectations is one integral
  have hint : condExpDiag d N u (zt E u) (mE E) k ω - condExpDiag d N v (zt E v) (mE E) k ω
      = ∫ ω', (greenDiagCentered d N u (zt E u) (mE E) k (rowSplit d N k ω ω')
          - greenDiagCentered d N v (zt E v) (mE E) k (rowSplit d N k ω ω')) ∂(P d) := by
    rw [integral_sub (rowIntegrable_greenDiagCentered (t := u) hE hu1 u k ω)
      (rowIntegrable_greenDiagCentered (t := v) hE hv1 v k ω)]
    rfl
  rw [hint]
  -- step 2: pull the norm inside
  refine (norm_integral_le_integral_norm _).trans ?_
  -- step 3: the pointwise modulus, with the random constant inside the integral
  have hpt : ∀ ω' : Ω d,
      ‖greenDiagCentered d N u (zt E u) (mE E) k (rowSplit d N k ω ω')
        - greenDiagCentered d N v (zt E v) (mE E) k (rowSplit d N k ω ω')‖
      ≤ a * rowFrobSq d N k ω' + b := by
    intro ω'
    set σ : Ω d := rowSplit d N k ω ω' with hσ
    have hentry : greenDiagCentered d N u (zt E u) (mE E) k σ
        - greenDiagCentered d N v (zt E v) (mE E) k σ
        = (green (Hflow d N u σ) (zt E u) - green (Hflow d N v σ) (zt E v)) k k := by
      simp only [greenDiagCentered, Matrix.sub_apply]
      ring
    rw [hentry]
    have h1 : ‖(green (Hflow d N u σ) (zt E u) - green (Hflow d N v σ) (zt E v)) k k‖
        ≤ ‖green (Hflow d N u σ) (zt E u) - green (Hflow d N v σ) (zt E v)‖ :=
      norm_apply_le_l2_opNorm _ _ _
    have h2 := norm_green_flow_sub_le d N hE hu1 hv1 σ
    have h3 : ‖Xmat d N σ‖ ≤ A + rowFrobSq d N k ω' := by
      have := norm_Xmat_rowSplit_le d N k ω ω'
      rw [hA_def]; linarith
    have h4 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt v| := abs_nonneg _
    have h5 : c * (|Real.sqrt u - Real.sqrt v| * ‖Xmat d N σ‖ + |u - v|)
        ≤ a * rowFrobSq d N k ω' + b := by
      rw [ha_def, hb_def]
      nlinarith [mul_le_mul_of_nonneg_left h3 h4, hc0]
    have h6 : (etaT E u)⁻¹ * (|Real.sqrt u - Real.sqrt v| * ‖Xmat d N σ‖ + |u - v|)
        * (etaT E v)⁻¹ = c * (|Real.sqrt u - Real.sqrt v| * ‖Xmat d N σ‖ + |u - v|) := by
      rw [hc_def]; ring
    rw [h6] at h2
    linarith
  -- step 4: integrate the pointwise bound
  have hg : Integrable (fun ω' : Ω d => a * rowFrobSq d N k ω' + b) (P d) :=
    ((integrable_rowFrobSq d N k).const_mul a).add (integrable_const _)
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω' => norm_nonneg _) hg
    (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_add ((integrable_rowFrobSq d N k).const_mul a) (integrable_const _),
    integral_const, smul_eq_mul, integral_const_mul]
  have huniv : (P d).real Set.univ = 1 := by simp
  rw [huniv, one_mul, hb_def, ha_def, hA_def]
  have hI := integral_rowFrobSq_le d N k
  nlinarith [hc0, abs_nonneg (Real.sqrt u - Real.sqrt v)]

/-- **The modulus in the shape the net engine consumes.**

This is `hHol` of `RBM.Gauss.stochDom_timeIcc_Lmax_of_unifDom` for the `condExpDiag` half of
the (4.5) integration-by-parts input: Hölder exponent `1/2`, deterministic constant `N^K`,
valid on `RBM.Gauss.flowNetEvent` — whose second half `{‖X‖ ≤ N}` is exactly what turns the
random constant of `RBM.Gauss.norm_condExpDiag_flow_sub_le` into `N^K`.

`hK` is the regime hypothesis: it holds as soon as `η_{t_N}^{-1} ≤ N^{c}` for some `c` and `K`
is taken `≥ 2c + 3`.  That lower bound on `η_{t_N}` is (2.72); it is carried explicitly here,
exactly as `RBM1D/Gauss/Step1Hyp.lean` carries its `hη`.

A consumer combining this with the Green's-function half of the same `hHol`
(`RBM.Gauss.norm_green_flow_sub_le`, T106) only needs `|‖x‖ - ‖y‖| ≤ ‖x - y‖` and the triangle
inequality; the extra terms are `|u-v|(η^{-1}+1)` from the prefactor `u` and
`η^{-2}(‖X‖+1)|u-v|^{1/2}` from `∑_k S_{ik}(G_{kk}-m)`, using `∑_k S_{ik} = 1`. -/
theorem norm_condExpDiag_flow_sub_le_rpow (d : Dims) {E : ℝ} (hE : |E| < 2) {s t δ : ℕ → ℝ}
    {K : ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hK : ∀ᶠ N : ℕ in atTop,
      ((etaT E (t N))⁻¹) ^ 2 * (2 * (N : ℝ) ^ 2 + (N : ℝ) + 7 / 2) ≤ (N : ℝ) ^ K) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ k : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        ‖condExpDiag d N u (zt E u) (mE E) k ω - condExpDiag d N v (zt E v) (mE E) k ω‖
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2) := by
  filter_upwards [hK] with N hKN ω hω k u hu v hv
  obtain ⟨-, hωX⟩ := hω
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
  have hu0 : (0 : ℝ) ≤ u := (hs0 N).trans hu.1
  have hv0 : (0 : ℝ) ≤ v := (hs0 N).trans hv.1
  set η : ℝ := etaT E (t N) with hη_def
  have hηpos : 0 < η := etaT_pos_of_lt_one' hE (ht1 N)
  have hiu : (etaT E u)⁻¹ ≤ η⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hηpos (etaT_le_of_le hE hu.2)
  have hiv : (etaT E v)⁻¹ ≤ η⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hηpos (etaT_le_of_le hE hv.2)
  have hiu0 : (0 : ℝ) < (etaT E u)⁻¹ := inv_pos.2 (etaT_pos_of_lt_one' hE hu1)
  have hiv0 : (0 : ℝ) < (etaT E v)⁻¹ := inv_pos.2 (etaT_pos_of_lt_one' hE hv1)
  set h : ℝ := |u - v| ^ ((1 : ℝ) / 2) with hh_def
  have hh0 : (0 : ℝ) ≤ h := Real.rpow_nonneg (abs_nonneg _) _
  have hd1 : |u - v| ≤ 1 := by
    rw [abs_le]; constructor <;> [linarith; linarith]
  have hsq : |Real.sqrt u - Real.sqrt v| ≤ h := by
    have hx := RBM.abs_sqrt_sub_sqrt_le hu0 hv0
    rwa [show Real.sqrt |u - v| = |u - v| ^ ((1 : ℝ) / 2) from Real.sqrt_eq_rpow _] at hx
  have hlin : |u - v| ≤ h := self_le_rpow_half (abs_nonneg _) hd1
  have hX0 : (0 : ℝ) ≤ ‖Xmat d N ω‖ := norm_nonneg _
  have hXN : ‖Xmat d N ω‖ ≤ (N : ℝ) := hωX
  have hCbound : ‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + 5 / 2
      ≤ 2 * (N : ℝ) ^ 2 + (N : ℝ) + 5 / 2 := by nlinarith [hXN, hX0]
  have hC0 : (0 : ℝ) ≤ ‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + 5 / 2 := by positivity
  have hmain := norm_condExpDiag_flow_sub_le d N hE hu1 hv1 k ω
  have hstep : (etaT E u)⁻¹ * (etaT E v)⁻¹
      * (|Real.sqrt u - Real.sqrt v| * (‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + 5 / 2)
        + |u - v|)
      ≤ (η⁻¹) ^ 2 * (2 * (N : ℝ) ^ 2 + (N : ℝ) + 7 / 2) * h := by
    have hprod : (etaT E u)⁻¹ * (etaT E v)⁻¹ ≤ (η⁻¹) ^ 2 := by
      have := mul_le_mul hiu hiv hiv0.le (le_of_lt (inv_pos.2 hηpos))
      nlinarith [this]
    have hinner : |Real.sqrt u - Real.sqrt v| * (‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + 5 / 2)
        + |u - v| ≤ (2 * (N : ℝ) ^ 2 + (N : ℝ) + 7 / 2) * h := by
      nlinarith [hsq, hlin, hC0, hCbound, hh0, abs_nonneg (Real.sqrt u - Real.sqrt v)]
    have hinner0 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt v|
        * (‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + 5 / 2) + |u - v| := by positivity
    have hpos2 : (0 : ℝ) ≤ (η⁻¹) ^ 2 := by positivity
    calc (etaT E u)⁻¹ * (etaT E v)⁻¹ * (|Real.sqrt u - Real.sqrt v|
            * (‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + 5 / 2) + |u - v|)
        ≤ (η⁻¹) ^ 2 * (|Real.sqrt u - Real.sqrt v|
            * (‖Xmat d N ω‖ + 2 * ‖Xmat d N ω‖ ^ 2 + 5 / 2) + |u - v|) :=
          mul_le_mul_of_nonneg_right hprod hinner0
      _ ≤ (η⁻¹) ^ 2 * ((2 * (N : ℝ) ^ 2 + (N : ℝ) + 7 / 2) * h) :=
          mul_le_mul_of_nonneg_left hinner hpos2
      _ = (η⁻¹) ^ 2 * (2 * (N : ℝ) ^ 2 + (N : ℝ) + 7 / 2) * h := by ring
  refine hmain.trans (hstep.trans ?_)
  exact mul_le_mul_of_nonneg_right hKN hh0

end RBM.Gauss
