/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridStepDecomp
import RBM1D.Gauss.GridQVConv

/-!
# (5.42), part (i): the conditional variance of `Z` as a quadratic form in the
single-label quadratic variations (T1512)

Formalization of `docs/supervisor/2026-09-25-2045.md` §3 (i): the conditional variance proxy
`v N (Ab ω)` of T1505's linear martingale-difference part `Z` is a quadratic form in the
single-label quadratic variations `quadVar d N Φ_a M`, and the deterministic Cauchy–Schwarz
bound this quadratic form satisfies packages exactly into T1509's `qv_conv_le`.

## Main declarations

* `RBM.Gauss.Grid.vB` (**T1**) — the symmetric bilinear covariance form underlying `v`.
* `RBM.Gauss.Grid.v_sum_eq` (**T1**) — `v` of a real-weighted sum of directions is the
  associated `vB`-quadratic form.
* `RBM.Gauss.Grid.abs_vB_le` (**T1**) — the Cauchy–Schwarz bound `|vB A A'| ≤ √(v A) √(v A')`.
* `RBM.Gauss.Grid.v_gradMat_eq_quadVar` (**T2**) — `v N (gradMat Φ M) = quadVar d N Φ M` for
  `Φ` real on the Hermitian submanifold.
* `RBM.Gauss.Grid.v_Ab_le` (**T3**) — the packaged deterministic bound on
  `v N (Σ_a (K(b,a) : ℂ) • gradMat Φ_a M)` for an arbitrary Hermitian `M`, obtained by feeding
  `qv_conv_le` with the `EE`/`R` of (T1)/(T2).
* `RBM.Gauss.Grid.v_Ab_le_H` (**T3**, corollary) — the same bound in T1505's `Ab` form at
  `M = H_j ω`.
* `RBM.Gauss.Grid.step_mul_v_Ab_le` (**T3**, corollary) — the `Δ`-multiplied form, in exactly
  the shape of T1505 (T4)'s `hbound` (`stepDecomp_Z_subG`), under `0 ≤ step s t K N`;
  `step_mul_bound_nonneg` supplies the companion `hc`.

## Step 0 (read-only checks, recorded here per the ticket)

* `v`, `lin`, `coordFinset`, `linVar` (`Gauss/GridMarkov.lean`, `Gauss/LinearForm.lean`): `v N A`
  unfolds (via the private `v_eq_sum` in `GridMarkov.lean`, reproved here since it is private)
  to `∑ c ∈ coordFinset N, (lin N A (Xmat (single c)))² * gvar c`; `coordFinset N` is the image
  of **all** raw coordinates `d.Idx N × d.Idx N × Bool` under `crd d N`, not just `usedCoord`.
* `quadVar` (`Gauss/MomentGronwall.lean:349`) sums only over `usedCoord d N`, the canonical
  representative of each unordered coordinate pair. The coordinates of `coordFinset N` outside
  the image of `usedCoord d N` are exactly the ones `Xmat` does not read (`Xentry` always reads
  off the `(min, max)`-ordered representative in `idxKey` order); on these, `Xmat d N
  (Pi.single c 1) = 0` (`Xmat_eq_sum`), so the corresponding terms of `v`'s sum vanish
  identically. This is the "extra terms equal `0`" case the ticket's (T2) anticipates, so (T2)
  is proved as an **equality**, not merely `≤`.
* `qv_conv_le`, `Uker_one_nonneg` (`Gauss/GridQVConv.lean`, T1509) are used exactly as stated:
  `EE a a' := (vB N (gradMat Φ_a M) (gradMat Φ_a' M) : ℂ)`, `R a := quadVar d N Φ_a M`, and the
  hypothesis `‖EE a a'‖ ≤ √(R a) √(R a')` is exactly (T1)'s Cauchy–Schwarz combined with (T2).
* The `quadVar` bound `RBM.highProb_quadVar_diagShape_of_jS` gives on the stopped event
  (`Gauss/Step2QVEvent.lean`) is, after its `diagShape' ≤ Q·tailT²` step, a pointwise bound
  `quadVar d N Φ_a M ≤ Q * (tailT ... (dist a))²` at the sample matrix `M = H_j ω` — exactly the
  shape (T3)'s `hqv` hypothesis below consumes. No mismatch.
-/

noncomputable section

namespace RBM.Gauss.Grid

open Matrix

variable {d : Dims}

/-! ### (T1) : `vB`, the linear identity, and its Cauchy–Schwarz bound -/

/-- **`vB`** (T1): the symmetric bilinear covariance form underlying `v`: the weighted sum, over
the raw coordinates read by `Xmat d N`, of the coordinate variance times the product of the
coefficients of that coordinate in `lin N A ∘ Xmat d N` and `lin N A' ∘ Xmat d N`.
`vB N A A = v N A` (`vB_self`). -/
noncomputable def vB (N : ℕ) (A A' : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  ∑ c ∈ coordFinset N, (gvar d c : ℝ) * lin N A (Xmat d N (Pi.single c 1))
      * lin N A' (Xmat d N (Pi.single c 1))

/-- **`vB` on the diagonal is `v`.** By `rfl`-level unfolding of `v`, `linVar` and `vB`, followed
by a per-term `ring` rearrangement. -/
theorem vB_self (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) : vB N A A = v N A := by
  unfold vB v linVar
  push_cast [NNReal.coe_mk]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem vB_nonneg_diag (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) : 0 ≤ vB N A A := by
  rw [vB_self]; exact v_nonneg N A

/-- `lin` is real-linear in the direction argument, for a finite real-weighted sum of
directions. The direction-argument analogue of `lin_add`/`lin_smul` (`GridMarkov.lean`, stated
there only for the sample-point argument). -/
private theorem lin_sum_smul {ι : Type*} [Fintype ι] (N : ℕ) (r : ι → ℝ)
    (A : ι → Matrix (d.Idx N) (d.Idx N) ℂ) (X : Matrix (d.Idx N) (d.Idx N) ℂ) :
    lin N (∑ i : ι, (r i : ℂ) • A i) X = ∑ i : ι, r i * lin N (A i) X := by
  unfold lin
  rw [Matrix.sum_mul, Matrix.trace_sum]
  have hstep : ∀ i : ι, Matrix.trace ((r i : ℂ) • A i * X)
      = (r i : ℂ) * Matrix.trace (A i * X) := by
    intro i
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => hstep i, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- **`v_sum_eq`** (T1): `v` of a real-weighted sum of directions is the associated
`vB`-quadratic form. Proved by unfolding `v` to its coordinate sum, expanding the square of the
`lin`-linear combination, and swapping the (finite) order of summation between the coordinate
sum and the double label sum. -/
theorem v_sum_eq {ι : Type*} [Fintype ι] (N : ℕ) (r : ι → ℝ)
    (A : ι → Matrix (d.Idx N) (d.Idx N) ℂ) :
    v N (∑ i : ι, (r i : ℂ) • A i) = ∑ i : ι, ∑ i' : ι, r i * r i' * vB N (A i) (A i') := by
  classical
  have hv : v N (∑ i : ι, (r i : ℂ) • A i)
      = ∑ c ∈ coordFinset N, (gvar d c : ℝ) *
          (∑ i : ι, r i * lin N (A i) (Xmat d N (Pi.single c 1))) ^ 2 := by
    unfold v linVar
    push_cast [NNReal.coe_mk]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [lin_sum_smul]
    ring
  rw [hv]
  have hexpand : ∀ c : Coord d, (gvar d c : ℝ) *
      (∑ i : ι, r i * lin N (A i) (Xmat d N (Pi.single c 1))) ^ 2
      = ∑ i : ι, ∑ i' : ι, (gvar d c : ℝ) * r i * r i'
          * lin N (A i) (Xmat d N (Pi.single c 1)) * lin N (A i') (Xmat d N (Pi.single c 1)) := by
    intro c
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    ring
  rw [Finset.sum_congr rfl fun c _ => hexpand c]
  rw [show (∑ c ∈ coordFinset N, ∑ i : ι, ∑ i' : ι, (gvar d c : ℝ) * r i * r i'
        * lin N (A i) (Xmat d N (Pi.single c 1)) * lin N (A i') (Xmat d N (Pi.single c 1)))
      = ∑ i : ι, ∑ c ∈ coordFinset N, ∑ i' : ι, (gvar d c : ℝ) * r i * r i'
          * lin N (A i) (Xmat d N (Pi.single c 1)) * lin N (A i') (Xmat d N (Pi.single c 1))
      from Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (∑ c ∈ coordFinset N, ∑ i' : ι, (gvar d c : ℝ) * r i * r i'
        * lin N (A i) (Xmat d N (Pi.single c 1)) * lin N (A i') (Xmat d N (Pi.single c 1)))
      = ∑ i' : ι, ∑ c ∈ coordFinset N, (gvar d c : ℝ) * r i * r i'
          * lin N (A i) (Xmat d N (Pi.single c 1)) * lin N (A i') (Xmat d N (Pi.single c 1))
      from Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  show (∑ c ∈ coordFinset N, (gvar d c : ℝ) * r i * r i'
      * lin N (A i) (Xmat d N (Pi.single c 1)) * lin N (A i') (Xmat d N (Pi.single c 1)))
      = r i * r i' * vB N (A i) (A i')
  rw [vB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **The Cauchy–Schwarz bound on `vB`** (T1): `|vB A A'| ≤ √(v A) √(v A')`. Proved by applying
the finite Cauchy–Schwarz inequality `Finset.sum_mul_sq_le_sq_mul_sq` to `f c := √(gvar c) ·
lin N A (...)`, `g c := √(gvar c) · lin N A' (...)`. -/
theorem abs_vB_le (N : ℕ) (A A' : Matrix (d.Idx N) (d.Idx N) ℂ) :
    |vB N A A'| ≤ Real.sqrt (v N A) * Real.sqrt (v N A') := by
  classical
  set f : Coord d → ℝ := fun c => Real.sqrt (gvar d c : ℝ) * lin N A (Xmat d N (Pi.single c 1))
    with hf_def
  set g : Coord d → ℝ := fun c => Real.sqrt (gvar d c : ℝ) * lin N A' (Xmat d N (Pi.single c 1))
    with hg_def
  have hfg : ∀ c ∈ coordFinset N, f c * g c = (gvar d c : ℝ)
      * lin N A (Xmat d N (Pi.single c 1)) * lin N A' (Xmat d N (Pi.single c 1)) := by
    intro c _
    have hsq : Real.sqrt (gvar d c : ℝ) * Real.sqrt (gvar d c : ℝ) = (gvar d c : ℝ) :=
      Real.mul_self_sqrt (gvar d c).2
    change Real.sqrt (gvar d c : ℝ) * lin N A (Xmat d N (Pi.single c 1))
        * (Real.sqrt (gvar d c : ℝ) * lin N A' (Xmat d N (Pi.single c 1)))
        = (gvar d c : ℝ) * lin N A (Xmat d N (Pi.single c 1)) * lin N A' (Xmat d N (Pi.single c 1))
    conv_rhs => rw [← hsq]
    ring
  have hf2 : ∀ c ∈ coordFinset N,
      f c ^ 2 = (gvar d c : ℝ) * lin N A (Xmat d N (Pi.single c 1)) ^ 2 := by
    intro c _
    have hsq : Real.sqrt (gvar d c : ℝ) ^ 2 = (gvar d c : ℝ) := Real.sq_sqrt (gvar d c).2
    change (Real.sqrt (gvar d c : ℝ) * lin N A (Xmat d N (Pi.single c 1))) ^ 2
        = (gvar d c : ℝ) * lin N A (Xmat d N (Pi.single c 1)) ^ 2
    conv_rhs => rw [← hsq]
    ring
  have hg2 : ∀ c ∈ coordFinset N,
      g c ^ 2 = (gvar d c : ℝ) * lin N A' (Xmat d N (Pi.single c 1)) ^ 2 := by
    intro c _
    have hsq : Real.sqrt (gvar d c : ℝ) ^ 2 = (gvar d c : ℝ) := Real.sq_sqrt (gvar d c).2
    change (Real.sqrt (gvar d c : ℝ) * lin N A' (Xmat d N (Pi.single c 1))) ^ 2
        = (gvar d c : ℝ) * lin N A' (Xmat d N (Pi.single c 1)) ^ 2
    conv_rhs => rw [← hsq]
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (coordFinset N) f g
  have hvBeq : vB N A A' = ∑ c ∈ coordFinset N, f c * g c :=
    (Finset.sum_congr rfl hfg).symm
  have hvAeq : v N A = ∑ c ∈ coordFinset N, f c ^ 2 := by
    have hv : v N A = ∑ c ∈ coordFinset N, (gvar d c : ℝ)
        * lin N A (Xmat d N (Pi.single c 1)) ^ 2 := by
      unfold v linVar
      push_cast [NNReal.coe_mk]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hv]
    exact Finset.sum_congr rfl fun c hc => (hf2 c hc).symm
  have hvA'eq : v N A' = ∑ c ∈ coordFinset N, g c ^ 2 := by
    have hv : v N A' = ∑ c ∈ coordFinset N, (gvar d c : ℝ)
        * lin N A' (Xmat d N (Pi.single c 1)) ^ 2 := by
      unfold v linVar
      push_cast [NNReal.coe_mk]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hv]
    exact Finset.sum_congr rfl fun c hc => (hg2 c hc).symm
  rw [← hvBeq, ← hvAeq, ← hvA'eq] at hCS
  have hnn : 0 ≤ v N A * v N A' := mul_nonneg (v_nonneg N A) (v_nonneg N A')
  have hstep : |vB N A A'| = Real.sqrt ((vB N A A') ^ 2) := (Real.sqrt_sq_eq_abs _).symm
  rw [hstep]
  calc Real.sqrt ((vB N A A') ^ 2) ≤ Real.sqrt (v N A * v N A') :=
        Real.sqrt_le_sqrt hCS
    _ = Real.sqrt (v N A) * Real.sqrt (v N A') := Real.sqrt_mul (v_nonneg N A) _

/-! ### (T2) : `v N (gradMat Φ M) = quadVar d N Φ M` -/

variable {N : ℕ}

/-- **`v_gradMat_eq_quadVar`** (T2): for `Φ` in T1505's `TestFun` class, real-valued on the
Hermitian submanifold, and `M` Hermitian, the conditional-variance proxy `v N (gradMat Φ M)`
equals the single-label quadratic variation `quadVar d N Φ M`.

Route: `coordFinset N` is reindexed as the image of `crd d N` over the full raw index type; the
coordinates outside `usedCoord d N` read `Xmat d N (Pi.single c 1) = 0` (`Xmat_eq_sum`), so they
contribute `0` on both sides and (T2) is an equality, not merely `≤`. On `usedCoord d N`,
`Xmat d N (Pi.single (crd p) 1) = Bmat d N p.1 p.2.1 p.2.2` (again `Xmat_eq_sum`), and
`lin N (gradMat Φ M) (Bmat p) = (coordD1 d N Φ M p).re` (T1505's `lin_eq_fderiv`, since
`coordD1 Φ M p` is definitionally `fderiv ℝ Φ M (Bmat p)`); `coordD1 Φ M p` is real
(`fderiv_im_eq_zero_of_herm`, using `hReal`), so `‖coordD1 Φ M p‖² = (coordD1 Φ M p).re²`. -/
theorem v_gradMat_eq_quadVar {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : TestFun d N Φ)
    (hReal : ∀ A, A.IsHermitian → (Φ A).im = 0) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) :
    v N (gradMat Φ M) = quadVar d N Φ M := by
  classical
  have hv : v N (gradMat Φ M)
      = ∑ c ∈ coordFinset N, (gvar d c : ℝ)
          * (lin N (gradMat Φ M) (Xmat d N (Pi.single c 1))) ^ 2 := by
    unfold v linVar
    push_cast [NNReal.coe_mk]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hv]
  have hreindex : ∑ c ∈ coordFinset N, (gvar d c : ℝ)
      * (lin N (gradMat Φ M) (Xmat d N (Pi.single c 1))) ^ 2
      = ∑ p : d.Idx N × d.Idx N × Bool, (gvar d (crd d N p) : ℝ)
          * (lin N (gradMat Φ M) (Xmat d N (Pi.single (crd d N p) 1))) ^ 2 := by
    unfold coordFinset
    rw [Finset.sum_map]
    rfl
  rw [hreindex]
  have hzero : ∀ p : d.Idx N × d.Idx N × Bool, p ∉ usedCoord d N →
      lin N (gradMat Φ M) (Xmat d N (Pi.single (crd d N p) 1)) = 0 := by
    intro p hp
    have hXz : Xmat d N (Pi.single (crd d N p) 1) = 0 := by
      rw [Xmat_eq_sum]
      refine Finset.sum_eq_zero fun q hq => ?_
      have hne : crd d N q ≠ crd d N p := fun he => hp (crd_injective d N he ▸ hq)
      rw [Pi.single_apply, if_neg hne, zero_smul]
    rw [hXz]
    unfold lin
    simp
  have hsub : ∑ p : d.Idx N × d.Idx N × Bool, (gvar d (crd d N p) : ℝ)
      * (lin N (gradMat Φ M) (Xmat d N (Pi.single (crd d N p) 1))) ^ 2
      = ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ)
          * (lin N (gradMat Φ M) (Xmat d N (Pi.single (crd d N p) 1))) ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [hzero p hp]
    ring
  rw [hsub]
  unfold quadVar
  refine Finset.sum_congr rfl fun p hp => ?_
  have hX : Xmat d N (Pi.single (crd d N p) 1) = Bmat d N p.1 p.2.1 p.2.2 := by
    rw [Xmat_eq_sum]
    rw [Finset.sum_eq_single p]
    · rw [Pi.single_apply, if_pos rfl, one_smul]
    · intro q _ hqp
      have hne : crd d N q ≠ crd d N p := fun he => hqp (crd_injective d N he)
      rw [Pi.single_apply, if_neg hne, zero_smul]
    · intro hpn
      exact absurd hp hpn
  rw [hX]
  have hBherm : (Bmat d N p.1 p.2.1 p.2.2).IsHermitian := Bmat_isHermitian hp
  have hcoordD1 : coordD1 d N Φ M p = fderiv ℝ Φ M (Bmat d N p.1 p.2.1 p.2.2) := rfl
  have hlin : lin N (gradMat Φ M) (Bmat d N p.1 p.2.1 p.2.2) = (coordD1 d N Φ M p).re := by
    rw [hcoordD1]
    exact (lin_eq_fderiv hΦ hM hBherm).symm
  have him : (coordD1 d N Φ M p).im = 0 := by
    rw [hcoordD1]
    exact fderiv_im_eq_zero_of_herm hΦ hReal hM hBherm
  rw [hlin]
  have hz : coordD1 d N Φ M p = ((coordD1 d N Φ M p).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hnormsq : ‖coordD1 d N Φ M p‖ ^ 2 = (coordD1 d N Φ M p).re ^ 2 := by
    conv_lhs => rw [hz]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnormsq]

/-! ### (T3) : the packaged deterministic bound, for arbitrary Hermitian `M`, and its `Ab` forms -/

/-- **`v_Ab_le`** (T3): the packaged deterministic bound, for an **arbitrary** Hermitian matrix
`M`. The transport kernel `K(b,a) = ∏ᵢ edgeKer (d.L N) 1 u v (b i) (a i)` is the (real) kernel of
`Uker (d.L N) (fun _ => 1) u v` (T1509); the pointwise hypothesis `hqv` is the per-label
`quadVar` bound at `M` (the shape T1497 (amend-1) supplies on the stopped event, at `M = H_j ω`).

Route: (T1)'s `v_sum_eq` turns `v N (Σ_a (K(b,a).re : ℂ) • gradMat Φ_a M)` into the
`vB`-quadratic form in the real kernel entries; `Uker_one_nonneg` identifies each kernel entry
with its own real part (as a complex number); `qv_conv_le` (T1509) is then applied with
`EE a a' := (vB N (gradMat Φ_a M) (gradMat Φ_a' M) : ℂ)` and `R a := quadVar d N Φ_a M`, whose
Cauchy–Schwarz hypothesis is (T1)'s `abs_vB_le` combined with (T2)'s `v_gradMat_eq_quadVar`.
The right-hand side is exactly `qv_conv_le`'s: no extra loss. -/
theorem v_Ab_le
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : ∀ a, TestFun d N (Φ a)) (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0)
    (hL : 3 ≤ d.L N) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) {u vt : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ vt)
    (hv0 : 0 ≤ vt) (hv1 : vt < 1) {W D Q : ℝ} (hW : Real.exp 1 ≤ W) (hQ : 0 ≤ Q)
    (hAuv : W * ellHat (d.L N) (vt : ℂ) * ((1 - vt) * m)
        ≤ W * ellHat (d.L N) (u : ℂ) * ((1 - u) * m))
    (b : LoopArg (d.L N) 2) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hqv : ∀ a : LoopArg (d.L N) 2, quadVar d N (Φ a) M
        ≤ Q * (tailT W (ellHat (d.L N) (u : ℂ)) ((1 - u) * m) D
            (zdist (d.L N) (a 0 - a 1))) ^ 2) :
    v N (∑ a : LoopArg (d.L N) 2,
        ((∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)).re : ℂ) • gradMat (Φ a) M)
      ≤ (Real.sqrt Q * ((1 - u) / (1 - vt)) ^ 2 * Step2.xiK (d.L N) W m *
          tailT W (ellHat (d.L N) (vt : ℂ)) ((1 - vt) * m) D (zdist (d.L N) (b 0 - b 1))) ^ 2 := by
  classical
  set r : LoopArg (d.L N) 2 → ℝ :=
    fun a => (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)).re with hr_def
  set A : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ := fun a => gradMat (Φ a) M with hA_def
  have hsum_eq : (∑ a : LoopArg (d.L N) 2,
      ((∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)).re : ℂ) • gradMat (Φ a) M)
      = ∑ a : LoopArg (d.L N) 2, (r a : ℂ) • A a := rfl
  rw [hsum_eq, v_sum_eq]
  have hker : ∀ a : LoopArg (d.L N) 2,
      (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)) = (r a : ℂ) := by
    intro a
    obtain ⟨ra, hra0, hraeq⟩ := Uker_one_nonneg hL hu0 huv hv1 b a
    have hre : r a = ra := by rw [hr_def]; simp only [hraeq, Complex.ofReal_re]
    rw [hre, hraeq]
  set EE : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℂ :=
    fun a a' => (vB N (A a) (A a') : ℂ) with hEE_def
  set R : LoopArg (d.L N) 2 → ℝ := fun a => quadVar d N (Φ a) M with hR_def
  have hR0 : ∀ a, 0 ≤ R a := fun a => quadVar_nonneg (Φ a) M
  have hREq : ∀ a, R a = v N (A a) := by
    intro a
    rw [hR_def, hA_def]
    exact (v_gradMat_eq_quadVar (hΦ a) (hReal a) hM).symm
  have hEE : ∀ a a' : LoopArg (d.L N) 2, ‖EE a a'‖ ≤ Real.sqrt (R a) * Real.sqrt (R a') := by
    intro a a'
    rw [hEE_def]
    have h1 : ‖(vB N (A a) (A a') : ℂ)‖ = |vB N (A a) (A a')| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h1, hREq a, hREq a']
    exact abs_vB_le N (A a) (A a')
  have hqR : ∀ a, R a ≤ Q * (tailT W (ellHat (d.L N) (u : ℂ)) ((1 - u) * m) D
      (zdist (d.L N) (a 0 - a 1))) ^ 2 := hqv
  have hconv := qv_conv_le hL hm0 hm1 hu0 huv hv0 hv1 hW hQ hAuv hR0 hqR hEE b
  have hnonneg : 0 ≤ (∑ a : LoopArg (d.L N) 2, ∑ a' : LoopArg (d.L N) 2,
      r a * r a' * vB N (A a) (A a') : ℝ) := by
    have h := v_nonneg N (∑ a : LoopArg (d.L N) 2, (r a : ℂ) • A a)
    rwa [v_sum_eq] at h
  have hcast : ((∑ a : LoopArg (d.L N) 2, ∑ a' : LoopArg (d.L N) 2,
      r a * r a' * vB N (A a) (A a') : ℝ) : ℂ)
      = ∑ a : LoopArg (d.L N) 2, ∑ a' : LoopArg (d.L N) 2,
          (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)) *
          (starRingEnd ℂ) (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a' i))
          * EE a a' := by
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [hker a, hker a', Complex.conj_ofReal]
  have heq2 : (∑ a : LoopArg (d.L N) 2, ∑ a' : LoopArg (d.L N) 2,
      r a * r a' * vB N (A a) (A a') : ℝ)
      = ‖∑ a : LoopArg (d.L N) 2, ∑ a' : LoopArg (d.L N) 2,
          (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a i)) *
          (starRingEnd ℂ) (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b i) (a' i))
          * EE a a'‖ := by
    rw [← hcast, Complex.norm_of_nonneg hnonneg]
  rw [heq2]
  exact hconv

/-- **`v_Ab_le_H`** (T3, `Ab`-form corollary): `v_Ab_le` at the grid sample `M = H_j ω`, stated
on T1505's `Ab` with the real kernel `U b' a' := (∏ᵢ edgeKer (b' i) (a' i)).re`. `Ab … b ω` is
definitionally the sum in `v_Ab_le` at `M = H d s t K N j ω`, which is Hermitian by
`H_isHermitian`. -/
theorem v_Ab_le_H {s t : ℕ → ℝ} {K : ℕ → ℕ} {j : ℕ}
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : ∀ a, TestFun d N (Φ a)) (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0)
    (hL : 3 ≤ d.L N) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) {u vt : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ vt)
    (hv0 : 0 ≤ vt) (hv1 : vt < 1) {W D Q : ℝ} (hW : Real.exp 1 ≤ W) (hQ : 0 ≤ Q)
    (hAuv : W * ellHat (d.L N) (vt : ℂ) * ((1 - vt) * m)
        ≤ W * ellHat (d.L N) (u : ℂ) * ((1 - u) * m))
    (b : LoopArg (d.L N) 2) (ω : Ωg d)
    (hqv : ∀ a : LoopArg (d.L N) 2, quadVar d N (Φ a) (H d s t K N j ω)
        ≤ Q * (tailT W (ellHat (d.L N) (u : ℂ)) ((1 - u) * m) D
            (zdist (d.L N) (a 0 - a 1))) ^ 2) :
    v N (Ab d s t K N j Φ
        (fun b' a' => (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b' i) (a' i)).re) b ω)
      ≤ (Real.sqrt Q * ((1 - u) / (1 - vt)) ^ 2 * Step2.xiK (d.L N) W m *
          tailT W (ellHat (d.L N) (vt : ℂ)) ((1 - vt) * m) D (zdist (d.L N) (b 0 - b 1))) ^ 2 :=
  v_Ab_le hΦ hReal hL hm0 hm1 hu0 huv hv0 hv1 hW hQ hAuv b (H_isHermitian d s t K N j ω) hqv

/-- **`step_mul_v_Ab_le`** (T3, `Δ`-form corollary): exactly the `hbound` hypothesis of T1505
(T4)'s `stepDecomp_Z_subG`, `∀ ω ∈ E, step s t K N * v N (Ab … b ω) ≤ c`, with
`c := step s t K N * (√Q · ((1-u)/(1-v))² · xiK · tailT(v)(dist b))²`, on any event `E` on which
the pointwise `quadVar` bound holds at `H_j ω`. Since `step s t K N = (t N - s N)/K N` may be
negative, the nonnegativity `0 ≤ step s t K N` is an explicit hypothesis (it is also needed for
`hbound`'s companion `0 ≤ c`, see `step_mul_bound_nonneg`). -/
theorem step_mul_v_Ab_le {s t : ℕ → ℝ} {K : ℕ → ℕ} {j : ℕ}
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : ∀ a, TestFun d N (Φ a)) (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0)
    (hL : 3 ≤ d.L N) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) {u vt : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ vt)
    (hv0 : 0 ≤ vt) (hv1 : vt < 1) {W D Q : ℝ} (hW : Real.exp 1 ≤ W) (hQ : 0 ≤ Q)
    (hAuv : W * ellHat (d.L N) (vt : ℂ) * ((1 - vt) * m)
        ≤ W * ellHat (d.L N) (u : ℂ) * ((1 - u) * m))
    (hstep : 0 ≤ step s t K N)
    (b : LoopArg (d.L N) 2) (E : Set (Ωg d))
    (hqvE : ∀ ω ∈ E, ∀ a : LoopArg (d.L N) 2, quadVar d N (Φ a) (H d s t K N j ω)
        ≤ Q * (tailT W (ellHat (d.L N) (u : ℂ)) ((1 - u) * m) D
            (zdist (d.L N) (a 0 - a 1))) ^ 2) :
    ∀ ω ∈ E, step s t K N * v N (Ab d s t K N j Φ
        (fun b' a' => (∏ i : Fin 2, edgeKer (d.L N) 1 (u : ℂ) (vt : ℂ) (b' i) (a' i)).re) b ω)
      ≤ step s t K N * (Real.sqrt Q * ((1 - u) / (1 - vt)) ^ 2 * Step2.xiK (d.L N) W m *
          tailT W (ellHat (d.L N) (vt : ℂ)) ((1 - vt) * m) D (zdist (d.L N) (b 0 - b 1))) ^ 2 :=
  fun ω hω => mul_le_mul_of_nonneg_left
    (v_Ab_le_H hΦ hReal hL hm0 hm1 hu0 huv hv0 hv1 hW hQ hAuv b ω (hqvE ω hω)) hstep

/-- The companion `hc : 0 ≤ c` of `stepDecomp_Z_subG` for the `c` of `step_mul_v_Ab_le`. -/
theorem step_mul_bound_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} (hstep : 0 ≤ step s t K N) (B : ℝ) :
    0 ≤ step s t K N * B ^ 2 :=
  mul_nonneg hstep (sq_nonneg B)

end RBM.Gauss.Grid

end
