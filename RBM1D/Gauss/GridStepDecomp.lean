/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridMarkov
import RBM1D.Gauss.GridOneStep
import RBM1D.Gauss.GridStopFilt
import RBM1D.Gauss.LoopC2
import RBM1D.Gauss.MomentGronwall
import RBM1D.Gauss.OpNorm
import RBM1D.Hierarchy.Kernel
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Mul

/-!
# T1505 — the pathwise `Z`/`Y` decomposition of one grid step

Formalization of the bridge ticket of the True-Path track, pilot P4/P5,
`docs/claude-team/pilot-P4P5-paper.md` §4 and `docs/supervisor/2026-09-25-2045.md` §2 items
(a)-(c): the pathwise decomposition of a single grid step of a label-indexed vector of test
functions into an exactly-linear martingale-difference part `Z` (fed to
`RBM.Gauss.Grid.hasCondSubgaussianMGF_linear`, T1482) and a quadratic remainder `Y`.

## Main results

* `RBM.Gauss.Grid.lin_eq_fderiv` (**T1**) — the real-linear directional derivative of a test
  function at a Hermitian direction is `RBM.Gauss.Grid.lin` of an explicit gradient matrix
  `RBM.Gauss.Grid.gradMat`, built from `wirtFirst`. Proved via the stronger *complex* identity
  `RBM.Gauss.Grid.fderiv_eq_trace_gradMat`, itself obtained by decomposing an arbitrary Hermitian
  direction along the `Bmat` coordinate basis (`RBM.Gauss.Grid.herm_eq_sum_Bmat`, the
  ω-independent generalisation of `RBM.Gauss.Xmat_eq_sum`).
* `RBM.Gauss.Grid.stepDecomp` (**T2**) — the pathwise `Z`/`Y` decomposition of one grid step for
  a label-indexed test-function family `Φ`, real on the Hermitian submanifold, transported by a
  real deterministic backward kernel `U`.
* `RBM.Gauss.Grid.stepDecomp_Y_sq` (**T3**) — the `L²` bound on `Y`.
* `RBM.Gauss.Grid.stepDecomp_Z_subG` (**T4**) — `Z` satisfies the hypotheses of
  `hasCondSubgaussianMGF_linear`.

## Step 0 checks (read-only, recorded here per the ticket)

* `wirtFirst`/`coordD1` (`Gauss/MomentGronwall.lean`, `Gauss/Generator.lean`) are Wirtinger
  derivatives of a test function read off through the `Bmat` coordinate basis; `gradMat` below is
  their matrix transpose, chosen so that `Matrix.trace (gradMat Φ M * X) = fderiv ℝ Φ M X` for
  Hermitian `X` (`fderiv_eq_trace_gradMat`).
* `BddC2C`/`bddC2C_loopObs` (`Gauss/LoopC2.lean`) are read only as the *source* of the uniform
  `C₀, C₁, C₂` constants a downstream ticket will plug into the `TestFun`/`hC₁`/`hC₂` hypotheses
  here; this file does not re-derive them.
* `hasCondSubgaussianMGF_linear`/`condExp_linear_eq_zero` (`Gauss/GridMarkov.lean`, T1482,
  merged) are used exactly as stated, with `A := Ab` below.
* `Kval` (deterministic drift correction) never appears: it does not depend on the sample and so
  cancels identically between `(L - K)_{u_{j+1}}(H_{j+1})` and its own conditional mean, exactly
  as the ticket's Step 0 records.

## A modelling choice recorded for `docs/paper-deltas.md`

The ticket's wording gives `Z b ω := √Δ · lin N (Ab ω) (Xmat d N (ω (j+1)))`, i.e. **only the
real part** of the complex first-order Taylor term `Σ_a U(b,a) · fderiv (Φ a) (H_j ω) (X (ω
(j+1)))`. For the identity `ξ = Z + Y` together with the *stated* pathwise bound
`‖Y b ω‖ ≤ C₂' Δ ‖X (ω (j+1))‖² + (its conditional mean)` to hold (rather than a strictly weaker
`O(√Δ ‖X‖)` bound coming from an uncancelled imaginary linear part), the construction needs the
first-order linear term itself to be real. This is guaranteed by two hypotheses that are
harmless and satisfiable, and match the intended downstream instantiation (`Φ a` a real
`(L-K)_{u,(+,-),a}`-type combination, `U` a real backward kernel `Uker`):

* `hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0` — each `Φ a` is real-valued on the Hermitian
  submanifold (it need not be real off it, where the `TestFun` machinery also uses it);
* `U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ` — the transport kernel has **real** entries.

Tagged for the dispatcher as a temporary `T1505a` entry in `docs/paper-deltas.md`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal MeasureTheory Matrix.Norms.L2Operator

/-! ### T1 : directional derivative = `lin` of an explicit gradient matrix -/

section GradMat

variable {d : Dims} {N : ℕ}

/-- **The gradient matrix** of a test function `Φ` at `M`: the transpose of the Wirtinger
derivative matrix `wirtFirst`, chosen so that `Matrix.trace (gradMat Φ M * X) = fderiv ℝ Φ M X`
for every Hermitian `X` (`fderiv_eq_trace_gradMat`). -/
def gradMat (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  Matrix.of fun i j => wirtFirst d N Φ M j i

/-- **The real coordinates of a Hermitian matrix** read along the `usedCoord` basis: the real
part at a `true`-tagged pair, the imaginary part at a `false`-tagged one. Agrees with the
ω-coordinates `Xentry` reads off when `X = Xmat d N ω`. -/
def hermCoord (X : Matrix (d.Idx N) (d.Idx N) ℂ) (p : d.Idx N × d.Idx N × Bool) : ℝ :=
  if p.2.2 then (X p.1 p.2.1).re else (X p.1 p.2.1).im

/-- **The `Bmat` coordinate decomposition of an arbitrary Hermitian matrix.** The
ω-independent generalisation of `RBM.Gauss.Xmat_eq_sum`: every Hermitian `X` (not just a sample
`Xmat d N ω`) is the real-linear combination of the fixed Hermitian directions `Bmat` with
coefficients `hermCoord X`. -/
theorem herm_eq_sum_Bmat {X : Matrix (d.Idx N) (d.Idx N) ℂ} (hX : X.IsHermitian) :
    X = ∑ p ∈ usedCoord d N, (hermCoord X p : ℂ) • Bmat d N p.1 p.2.1 p.2.2 := by
  ext k l
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rcases idxKey_lt_or_eq_or_lt d N k l with h | h | h
  · -- `idxKey k < idxKey l`
    have hkl : k ≠ l := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hsub : ({(k, l, true), (k, l, false)} : Finset (d.Idx N × d.Idx N × Bool)) ⊆
        usedCoord d N := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact mem_usedCoord.2 (Or.inl h)
    rw [← Finset.sum_subset hsub, Finset.sum_pair (by simp)]
    · show X k l = (hermCoord X (k, l, true) : ℂ) * Bmat d N k l true k l
          + (hermCoord X (k, l, false) : ℂ) * Bmat d N k l false k l
      simp only [Bmat_apply, hermCoord, and_self, if_true, ite_true, Bool.false_eq_true, if_false,
        ite_false, mul_one]
      exact (Complex.re_add_im (X k l)).symm
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
    · show X k k = (hermCoord X (k, k, true) : ℂ) * Bmat d N k k true k k
      simp only [Bmat_apply, hermCoord, and_self, if_true, ite_true, mul_one]
      have hreal : (X k k).im = 0 := by
        have hstar := hX.apply k k
        have him : ((starRingEnd ℂ) (X k k)).im = (X k k).im := congrArg Complex.im hstar
        simp only [Complex.conj_im] at him
        linarith
      apply Complex.ext
      · simp
      · simpa using hreal
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
      simp [Bmat_apply, hne, hne']
  · -- `idxKey l < idxKey k`
    have hkl : l ≠ k := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hsub : ({(l, k, true), (l, k, false)} : Finset (d.Idx N × d.Idx N × Bool)) ⊆
        usedCoord d N := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact mem_usedCoord.2 (Or.inl h)
    rw [← Finset.sum_subset hsub, Finset.sum_pair (by simp)]
    · show X k l = (hermCoord X (l, k, true) : ℂ) * Bmat d N l k true k l
          + (hermCoord X (l, k, false) : ℂ) * Bmat d N l k false k l
      have hne1 : ¬ (k = l ∧ l = k) := fun hh => hkl hh.2
      simp only [Bmat_apply, hermCoord, hne1, if_false, and_self, if_true, ite_true,
        Bool.false_eq_true, ite_false, mul_one, mul_neg, mul_one]
      have hconj : X k l = (starRingEnd ℂ) (X l k) := (hX.apply k l).symm
      rw [hconj]
      apply Complex.ext <;> simp
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

/-- A real cast acting by `ℂ`-scalar multiplication on a complex matrix agrees with the native
`ℝ`-scalar multiplication. -/
private theorem complexSmul_eq_realSmul (r : ℝ) (Mx : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (r : ℂ) • Mx = r • Mx := by
  rw [← congrFun Complex.coe_algebraMap r]
  exact algebraMap_smul ℂ r Mx

/-- `Bmat` off the diagonal is the sum of the two elementary matrices at its two nonzero
positions. -/
private theorem Bmat_eq_single_add_single {i j : d.Idx N} (hij : i ≠ j) (b : Bool) :
    Bmat d N i j b = Matrix.single i j (if b then (1 : ℂ) else Complex.I)
      + Matrix.single j i (if b then (1 : ℂ) else -Complex.I) := by
  ext k l
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, Bmat_apply]
  by_cases h1 : k = i ∧ l = j
  · have h2 : ¬ (j = k ∧ i = l) := by rintro ⟨rfl, rfl⟩; exact hij h1.1.symm
    obtain ⟨rfl, rfl⟩ := h1
    simp [h2]
  · by_cases h2 : k = j ∧ l = i
    · have h3 : ¬ (i = k ∧ j = l) := by rintro ⟨rfl, rfl⟩; exact hij h2.1
      obtain ⟨rfl, rfl⟩ := h2
      simp [h1, h3]
    · have h3 : ¬ (i = k ∧ j = l) := fun h => h1 ⟨h.1.symm, h.2.symm⟩
      have h4 : ¬ (j = k ∧ i = l) := fun h => h2 ⟨h.1.symm, h.2.symm⟩
      simp [h1, h2, h3, h4]

/-- **The trace pairing against `Bmat`, off the diagonal.** -/
private theorem trace_mul_Bmat_off_diag (A : Matrix (d.Idx N) (d.Idx N) ℂ) {i j : d.Idx N}
    (hij : i ≠ j) (b : Bool) :
    Matrix.trace (A * Bmat d N i j b)
      = A j i * (if b then 1 else Complex.I) + A i j * (if b then 1 else -Complex.I) := by
  rw [Bmat_eq_single_add_single hij, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_mul_single, Matrix.trace_mul_single]
  simp [mul_comm]

/-- **The trace pairing against `Bmat`, on the diagonal.** -/
private theorem trace_mul_Bmat_diag (A : Matrix (d.Idx N) (d.Idx N) ℂ) (i : d.Idx N) :
    Matrix.trace (A * Bmat d N i i true) = A i i := by
  have heq : Bmat d N i i true = Matrix.single i i (1 : ℂ) := by
    ext k l
    rw [Matrix.single_apply, Bmat_apply]
    by_cases h : k = i ∧ l = i
    · simp [h]
    · have h' : ¬ (i = k ∧ i = l) := fun hh => h ⟨hh.1.symm, hh.2.symm⟩
      simp [h, h']
  rw [heq, Matrix.trace_mul_single]
  simp

/-- **The single-coordinate identity behind T1.** For a coordinate `p` read by `Xmat`/`Bmat`,
`coordD1 Φ M p` is the trace pairing of the corresponding `Bmat` direction against `gradMat`. -/
private theorem coordD1_eq_trace_gradMat_Bmat {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) :
    coordD1 d N Φ M p = Matrix.trace (gradMat Φ M * Bmat d N p.1 p.2.1 p.2.2) := by
  obtain ⟨i, j, b⟩ := p
  rcases mem_usedCoord.1 hp with hlt | ⟨heq, hbtrue⟩
  · have hij : i ≠ j := fun he => absurd (he ▸ hlt) (lt_irrefl _)
    rw [trace_mul_Bmat_off_diag (gradMat Φ M) hij b]
    unfold gradMat
    simp only [Matrix.of_apply]
    have hwi : wirtFirst d N Φ M i j
        = (2⁻¹ : ℂ) *
          (coordD1 d N Φ M (i, j, true) - Complex.I * coordD1 d N Φ M (i, j, false)) := by
      unfold wirtFirst; rw [if_neg hij]
    have hwj : wirtFirst d N Φ M j i
        = (2⁻¹ : ℂ) *
          (coordD1 d N Φ M (i, j, true) + Complex.I * coordD1 d N Φ M (i, j, false)) := by
      unfold wirtFirst
      rw [if_neg (Ne.symm hij), coordD1_swap_true Φ M i j, coordD1_swap_false Φ M hij]
      ring
    rw [hwi, hwj]
    rcases b with _ | _
    · -- `b = false`
      simp only [Bool.false_eq_true, if_false, ite_false]
      linear_combination coordD1 d N Φ M (i, j, false) * Complex.I_mul_I
    · -- `b = true`
      simp only [if_true, ite_true]
      ring
  · have heq' : i = j := heq
    have hbtrue' : b = true := hbtrue
    subst heq'; subst hbtrue'
    rw [trace_mul_Bmat_diag (gradMat Φ M) i]
    unfold gradMat wirtFirst
    simp

/-- **The complex identity behind T1.** For Hermitian `X`, the directional derivative of `Φ` at
`M` along `X` is the trace pairing of `X` against the gradient matrix `gradMat Φ M`. Proved by
decomposing `X` along the `Bmat` coordinate basis (`herm_eq_sum_Bmat`), applying the (real-)
linearity of `fderiv ℝ Φ M` and of `Matrix.trace (gradMat Φ M * ·)`, and matching the two
resulting sums coordinate by coordinate via `coordD1_eq_trace_gradMat_Bmat`. -/
theorem fderiv_eq_trace_gradMat {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) {X : Matrix (d.Idx N) (d.Idx N) ℂ} (hX : X.IsHermitian) :
    fderiv ℝ Φ M X = Matrix.trace (gradMat Φ M * X) := by
  have key : ∀ S : Finset (d.Idx N × d.Idx N × Bool), (∀ p ∈ S, p ∈ usedCoord d N) →
      ∀ c : d.Idx N × d.Idx N × Bool → ℝ,
      fderiv ℝ Φ M (∑ p ∈ S, (c p : ℂ) • Bmat d N p.1 p.2.1 p.2.2)
        = Matrix.trace (gradMat Φ M * ∑ p ∈ S, (c p : ℂ) • Bmat d N p.1 p.2.1 p.2.2) := by
    intro S
    induction S using Finset.induction with
    | empty => intro _ c; simp
    | insert a s ha ih =>
        intro hSub c
        have haU : a ∈ usedCoord d N := hSub a (Finset.mem_insert_self a s)
        have hsU : ∀ p ∈ s, p ∈ usedCoord d N := fun p hp => hSub p (Finset.mem_insert_of_mem hp)
        rw [Finset.sum_insert ha, map_add, Matrix.mul_add, Matrix.trace_add, ih hsU c]
        congr 1
        rw [complexSmul_eq_realSmul (c a) (Bmat d N a.1 a.2.1 a.2.2), map_smul, Matrix.mul_smul,
          Matrix.trace_smul]
        congr 1
        exact coordD1_eq_trace_gradMat_Bmat M haU
  conv_lhs => rw [herm_eq_sum_Bmat hX]
  conv_rhs => rw [herm_eq_sum_Bmat hX]
  exact key (usedCoord d N) (fun p hp => hp) (hermCoord X)

/-- **T1: `RBM.Gauss.Grid.lin_eq_fderiv`.** For a `TestFun`-class `Φ` and Hermitian `M`, the
real-linear directional derivative of `Φ` at `M` along a Hermitian `X` is `lin N (gradMat Φ M) X`.
Immediate from the complex identity `fderiv_eq_trace_gradMat` and the definition of `lin`. -/
theorem lin_eq_fderiv {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (_h : TestFun d N Φ)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (_hM : M.IsHermitian)
    {X : Matrix (d.Idx N) (d.Idx N) ℂ} (hX : X.IsHermitian) :
    (fderiv ℝ Φ M X).re = lin N (gradMat Φ M) X := by
  rw [fderiv_eq_trace_gradMat M hX]; rfl

/-- **T1, the imaginary part.** The same identity read off in the imaginary part: it is the
imaginary part of the very same trace pairing that `lin` reads the real part of. -/
theorem lin_eq_fderiv_im {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (_h : TestFun d N Φ)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (_hM : M.IsHermitian)
    {X : Matrix (d.Idx N) (d.Idx N) ℂ} (hX : X.IsHermitian) :
    (fderiv ℝ Φ M X).im = (Matrix.trace (gradMat Φ M * X)).im := by
  rw [fderiv_eq_trace_gradMat M hX]

end GradMat

/-! ### The pathwise second-order Taylor remainder, needed for (T2)/(T3) -/

section TaylorRemainder

variable {d : Dims} {N : ℕ}

private theorem hasDerivAt_add_smul (M y : Matrix (d.Idx N) (d.Idx N) ℂ) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => M + t' • y) y t := by
  simpa using ((hasDerivAt_id t).smul_const y).const_add M

/-- **The pathwise second-order Taylor remainder bound.** For a `TestFun`-class `Φ` with second
derivative bounded by `C₂`, the Taylor remainder of `Φ` at `M` in the direction `y`, evaluated at
parameter `s ≥ 0`, is bounded by `(C₂ / 2) · s² · ‖y‖²`. Proved by two applications of the
one-variable fencing (mean value) theorem: first bounding `k(t) := fderiv ℝ Φ (M + t•y) y`'s
displacement from `k 0` linearly in `t` (using the uniform bound on the second derivative), then
bounding the Taylor remainder itself by the quadratic boundary function this linear bound
integrates to. -/
theorem norm_taylor_remainder_le {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (h : TestFun d N Φ)
    {C₂ : ℝ} (hC₂ : ∀ A, ‖fderiv ℝ (fderiv ℝ Φ) A‖ ≤ C₂)
    (M y : Matrix (d.Idx N) (d.Idx N) ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ‖Φ (M + s • y) - Φ M - s • fderiv ℝ Φ M y‖ ≤ (C₂ / 2) * s ^ 2 * ‖y‖ ^ 2 := by
  -- the first derivative along the path, in its naturally inferred form
  have hp : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y)) (fderiv ℝ Φ (M + t • y) y) t :=
    fun t => ((h.differentiable _).hasFDerivAt).comp_hasDerivAt t (hasDerivAt_add_smul M y t)
  -- the second derivative along the path
  have hk : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => fderiv ℝ Φ (M + t' • y) y)
      (fderiv ℝ (fderiv ℝ Φ) (M + t • y) y y) t := by
    intro t
    have h1 := (hasFDerivAt_fderiv_apply h y (M + t • y)).comp_hasDerivAt t
      (hasDerivAt_add_smul M y t)
    simp only [Function.comp, ContinuousLinearMap.flip_apply] at h1
    exact h1
  set k : ℝ → ℂ := fun t => fderiv ℝ Φ (M + t • y) y with hk_def
  have hkCont : Continuous k := continuous_iff_continuousAt.2 fun t => (hk t).continuousAt
  have hlevel1 : ∀ t ∈ Set.Icc (0 : ℝ) s, ‖k t - k 0‖ ≤ C₂ * ‖y‖ ^ 2 * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment
      hkCont.continuousOn (fun t _ => (hk t).hasDerivWithinAt)
      (fun t _ => by
        have h2 := norm_fderiv2_apply_le hC₂ (M + t • y) y y
        nlinarith [h2])
  -- the remainder function and its derivative
  have hg : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (M + t' • y) - Φ M - t' • fderiv ℝ Φ M y)
      (k t - k 0) t := by
    intro t
    have h1 := (hp t).sub_const (Φ M)
    have h2 : HasDerivAt (fun t' : ℝ => t' • fderiv ℝ Φ M y) (fderiv ℝ Φ M y) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ Φ M y)
    have h3 := h1.sub h2
    have hk0 : k 0 = fderiv ℝ Φ M y := by simp [hk_def]
    rw [hk0]
    exact h3
  set g : ℝ → ℂ := fun t' => Φ (M + t' • y) - Φ M - t' • fderiv ℝ Φ M y with hg_def
  have hgCont : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  set B : ℝ → ℝ := fun t => (C₂ / 2) * ‖y‖ ^ 2 * t ^ 2 with hB_def
  have hB : ∀ t : ℝ, HasDerivAt B (C₂ * ‖y‖ ^ 2 * t) t := by
    intro t
    have h1 : HasDerivAt (fun t' : ℝ => t' ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 := h1.const_mul (C₂ / 2 * ‖y‖ ^ 2)
    have heq : C₂ / 2 * ‖y‖ ^ 2 * (2 * t) = C₂ * ‖y‖ ^ 2 * t := by ring
    rw [heq] at h2
    exact h2
  have ha0 : ‖g 0‖ ≤ B 0 := by simp [hg_def, hB_def]
  have hfinal := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    hgCont.continuousOn (fun t _ => (hg t).hasDerivWithinAt) ha0 hB
    (fun t ht => by simpa using hlevel1 t ⟨ht.1, ht.2.le⟩)
  have hgs := hfinal (Set.right_mem_Icc.2 hs)
  simp only [hg_def, hB_def] at hgs
  have heq : C₂ / 2 * ‖y‖ ^ 2 * s ^ 2 = C₂ / 2 * s ^ 2 * ‖y‖ ^ 2 := by ring
  linarith [hgs, heq]

end TaylorRemainder

/-! ### T2 : the pathwise `Z`/`Y` decomposition of one grid step -/

section StepDecomp

variable {d : Dims} {N : ℕ}

/-- A test function real on the Hermitian submanifold has a real-valued directional derivative
along Hermitian directions, at a Hermitian base point. -/
theorem fderiv_im_eq_zero_of_herm {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : TestFun d N Φ) (hReal : ∀ A, A.IsHermitian → (Φ A).im = 0)
    {M X : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (hX : X.IsHermitian) :
    (fderiv ℝ Φ M X).im = 0 := by
  have hp0 : HasDerivAt (fun t' : ℝ => Φ (M + t' • X)) (fderiv ℝ Φ M X) 0 := by
    have h1 : HasFDerivAt Φ (fderiv ℝ Φ (M + (0 : ℝ) • X)) (M + (0 : ℝ) • X) :=
      (hΦ.differentiable _).hasFDerivAt
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h1 (hasDerivAt_add_smul M X 0)
    simp only [zero_smul, add_zero, Function.comp_def] at h2
    exact h2
  have hpath0 : ∀ t' : ℝ, (Φ (M + t' • X)).im = 0 := by
    intro t'
    have hcast : M + t' • X = M + (t' : ℂ) • X := by rw [complexSmul_eq_realSmul]
    have hHt : (M + t' • X).IsHermitian := by
      rw [hcast]
      exact hM.add (hX.smul (Complex.conj_ofReal t'))
    exact hReal _ hHt
  have him0 : HasDerivAt (fun t' : ℝ => (Φ (M + t' • X)).im) ((fderiv ℝ Φ M X).im) 0 := by
    have h1 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) Complex.imCLM.hasFDerivAt hp0
    simpa [Function.comp_def] using h1
  have hconst : (fun t' : ℝ => (Φ (M + t' • X)).im) = fun _ : ℝ => (0 : ℝ) := funext hpath0
  rw [hconst] at him0
  exact him0.unique (hasDerivAt_const 0 0)

/-- **`Ab`**: the `filt d j`-measurable direction attached to a label-indexed test-function
family `Φ`, a real backward kernel `U`, and a target label `b`:
`Ab ω := Σ_a U(b,a) • gradMat (Φ a) (H_j ω)`. -/
noncomputable def Ab (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) (ω : Ωg d) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) • gradMat (Φ a) (H d s t K N j ω)

/-- **`stepZ`**: the exactly-linear part of one grid step,
`Z b ω = √Δ · lin N (Ab ω) (Xmat d N (ω (j+1)))`. -/
noncomputable def stepZ (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) (ω : Ωg d) : ℝ :=
  Real.sqrt (step s t K N) * lin N (Ab d s t K N j Φ U b ω) (Xmat d N (ω (j + 1)))

/-- **`stepXi`**: the observable minus its own conditional mean,
`ξ b ω := (U (Φvec_{u_{j+1}}(H_{j+1})))b(ω) − E[·|F_j](ω)`. -/
noncomputable def stepXi (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) (ω : Ωg d) : ℂ :=
  (∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω))
    - (Pg d)[fun ω' => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω')
        | filt d j] ω

/-- **`stepY`**: the remainder, `Y b ω := ξ b ω − Z b ω`. -/
noncomputable def stepY (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) (ω : Ωg d) : ℂ :=
  stepXi d s t K N j Φ U b ω - (stepZ d s t K N j Φ U b ω : ℂ)

/-- `Ab` is `filt d j`-measurable: it is a continuous (via `TestFun`) function of the
`filt d j`-adapted grid flow `H_j`. -/
theorem measurable_Ab (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : ∀ a, TestFun d N (Φ a)) (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ)
    (b : LoopArg (d.L N) 2) :
    Measurable[filt d j] (fun ω : Ωg d => Ab d s t K N j Φ U b ω) := by
  have hHmeas : Measurable[filt d j] (fun ω : Ωg d => H d s t K N j ω) :=
    H_measurable_filt d s t K N j
  have hgradCont : ∀ a, Continuous (gradMat (Φ a)) := by
    intro a
    apply continuous_pi; intro i; apply continuous_pi; intro k
    unfold gradMat wirtFirst
    simp only [Matrix.of_apply]
    split_ifs
    · exact (hΦ a).continuous_fderiv.clm_apply continuous_const
    · exact (((hΦ a).continuous_fderiv.clm_apply continuous_const).sub
        ((continuous_const).mul ((hΦ a).continuous_fderiv.clm_apply continuous_const))).const_smul
        (2⁻¹ : ℂ)
  exact Finset.measurable_sum _ fun a _ =>
    (((hgradCont a).measurable.comp hHmeas)).const_smul (U b a : ℂ)

/-- `lin` is real-linear in its direction argument, specialised to the `Ab` combination. -/
private theorem lin_Ab_eq_sum (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)
    (ω : Ωg d) (X : Matrix (d.Idx N) (d.Idx N) ℂ) :
    lin N (Ab d s t K N j Φ U b ω) X
      = ∑ a : LoopArg (d.L N) 2, U b a * lin N (gradMat (Φ a) (H d s t K N j ω)) X := by
  unfold lin Ab
  rw [Matrix.sum_mul, Matrix.trace_sum]
  have hstep : ∀ a : LoopArg (d.L N) 2,
      Matrix.trace ((U b a : ℂ) • gradMat (Φ a) (H d s t K N j ω) * X)
        = (U b a : ℂ) * Matrix.trace (gradMat (Φ a) (H d s t K N j ω) * X) := by
    intro a
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun a _ => hstep a, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- **The key algebraic bridge.** The `Ab`-weighted real-linear term matches `stepZ` exactly,
given each `Φ a` real on the Hermitian submanifold (`hReal`) and the real kernel `U`: this is
where the imaginary residual of the naive complex linear term cancels identically. -/
theorem sum_fderiv_eq_stepZ (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : ∀ a, TestFun d N (Φ a)) (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) (ω : Ωg d) :
    (Real.sqrt (step s t K N) : ℂ) *
      (∑ a : LoopArg (d.L N) 2, (U b a : ℂ) *
        fderiv ℝ (Φ a) (H d s t K N j ω) (Xmat d N (ω (j + 1))))
      = (stepZ d s t K N j Φ U b ω : ℂ) := by
  have hHherm := H_isHermitian d s t K N j ω
  have hXherm := Xmat_isHermitian d N (ω (j + 1))
  have hterm : ∀ a : LoopArg (d.L N) 2, (U b a : ℂ) *
      fderiv ℝ (Φ a) (H d s t K N j ω) (Xmat d N (ω (j + 1)))
      = ((U b a * lin N (gradMat (Φ a) (H d s t K N j ω)) (Xmat d N (ω (j + 1)))) : ℝ) := by
    intro a
    have h1 := fderiv_im_eq_zero_of_herm (hΦ a) (hReal a) hHherm hXherm
    have h2 := lin_eq_fderiv (hΦ a) hHherm hXherm
      (Φ := Φ a) (M := H d s t K N j ω) (X := Xmat d N (ω (j + 1)))
    have h3 : fderiv ℝ (Φ a) (H d s t K N j ω) (Xmat d N (ω (j + 1)))
        = ((lin N (gradMat (Φ a) (H d s t K N j ω)) (Xmat d N (ω (j + 1)))) : ℝ) :=
      Complex.ext (by simpa using h2) (by simpa using h1)
    rw [h3]; push_cast; ring
  simp only [hterm]
  rw [← Complex.ofReal_sum, ← lin_Ab_eq_sum d s t K N j Φ U b ω (Xmat d N (ω (j + 1)))]
  unfold stepZ
  push_cast
  ring

/-- The grid flow at the next step is the current one shifted by `√Δ • X(ω(j+1))`. -/
theorem H_succ_eq (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ) (ω : Ωg d) :
    H d s t K N (j + 1) ω
      = H d s t K N j ω + Real.sqrt (step s t K N) • Xmat d N (ω (j + 1)) := by
  rw [← complexSmul_eq_realSmul]
  unfold H
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1), smul_add]
  abel

/-- A measurable, globally bounded ℂ-valued function on the grid sample space is integrable. -/
private theorem integrable_of_measurable_of_bound {f : Ωg d → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f (Pg d) :=
  (memLp_top_of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)).integrable
    le_top

/-- `Φ a` evaluated along the grid flow is integrable: it is measurable (`TestFun` is
continuous) and globally bounded (`TestFun.bdd₀`). -/
theorem integrable_Phi_H (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ)
    {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : TestFun d N Φ) :
    Integrable (fun ω : Ωg d => Φ (H d s t K N k ω)) (Pg d) := by
  obtain ⟨C, hC⟩ := hΦ.bdd₀
  have hHm : Measurable (fun ω : Ωg d => H d s t K N k ω) :=
    (H_measurable_filt d s t K N k).mono ((filt d).le k) le_rfl
  exact integrable_of_measurable_of_bound (hΦ.contDiff.continuous.measurable.comp hHm)
    (fun ω => hC (H d s t K N k ω))

/-- **`Rlabel`**: the per-label Taylor remainder of one grid step,
`R_a ω := Φ_a(H_{j+1}ω) - Φ_a(H_jω) - √Δ • fderiv ℝ (Φ a) (H_jω) (X(ω(j+1)))`. -/
noncomputable def Rlabel (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (ω : Ωg d) : ℂ :=
  Φ (H d s t K N (j + 1) ω) - Φ (H d s t K N j ω)
    - Real.sqrt (step s t K N) • fderiv ℝ Φ (H d s t K N j ω) (Xmat d N (ω (j + 1)))

/-- **The pathwise Taylor remainder bound.** -/
theorem norm_Rlabel_le (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : TestFun d N Φ) {C₂ : ℝ}
    (hC₂ : ∀ A, ‖fderiv ℝ (fderiv ℝ Φ) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N) (ω : Ωg d) :
    ‖Rlabel d s t K N j Φ ω‖ ≤ (C₂ / 2) * step s t K N * ‖Xmat d N (ω (j + 1))‖ ^ 2 := by
  unfold Rlabel
  rw [H_succ_eq]
  have hkey := norm_taylor_remainder_le hΦ hC₂ (H d s t K N j ω) (Xmat d N (ω (j + 1)))
    (Real.sqrt_nonneg (step s t K N))
  rwa [Real.sq_sqrt hΔ] at hkey

/-- `‖X(ω(k+1))‖²` is integrable: it is the pull-back, along the independent increment
`ω ↦ ω (k+1)`, of the (integrable) squared operator norm of a single sample of `X`. -/
theorem integrable_normSq_incr (d : Dims) (N k : ℕ) :
    Integrable (fun ω : Ωg d => ‖Xmat d N (ω (k + 1))‖ ^ 2) (Pg d) := by
  have hg : Integrable (fun x : Ω d => ‖Xmat d N x‖ ^ 2) (P d) := by
    have h := integrable_norm_Xmat_pow d N 1
    simpa using h
  have hf : AEMeasurable (fun ω : Ωg d => ω (k + 1)) (Pg d) :=
    (measurable_pi_apply (k + 1)).aemeasurable
  have hmap : (Pg d).map (fun ω : Ωg d => ω (k + 1)) = P d := map_incr d k
  have hgASM : AEStronglyMeasurable (fun x : Ω d => ‖Xmat d N x‖ ^ 2)
      ((Pg d).map fun ω => ω (k + 1)) := by
    rw [hmap]; exact hg.aestronglyMeasurable
  exact (integrable_map_measure hgASM hf).1 (by rw [hmap]; exact hg)

/-- `‖X(ω(k+1))‖⁴` is integrable: the fourth-moment analogue of `integrable_normSq_incr`, needed
for the `L²` bound on `Y` (T3). -/
theorem integrable_normPow4_incr (d : Dims) (N k : ℕ) :
    Integrable (fun ω : Ωg d => ‖Xmat d N (ω (k + 1))‖ ^ 4) (Pg d) := by
  have hg : Integrable (fun x : Ω d => ‖Xmat d N x‖ ^ 4) (P d) := by
    have h := integrable_norm_Xmat_pow d N 2
    simpa using h
  have hf : AEMeasurable (fun ω : Ωg d => ω (k + 1)) (Pg d) :=
    (measurable_pi_apply (k + 1)).aemeasurable
  have hmap : (Pg d).map (fun ω : Ωg d => ω (k + 1)) = P d := map_incr d k
  have hgASM : AEStronglyMeasurable (fun x : Ω d => ‖Xmat d N x‖ ^ 4)
      ((Pg d).map fun ω => ω (k + 1)) := by
    rw [hmap]; exact hg.aestronglyMeasurable
  exact (integrable_map_measure hgASM hf).1 (by rw [hmap]; exact hg)

/-- The grid flow `H` is continuous in `ω`. -/
theorem continuous_H (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    Continuous (fun ω : Ωg d => H d s t K N k ω) := by
  unfold H
  have hc0 : Continuous (fun ω : Ωg d => ω 0) := continuous_apply (0 : ℕ)
  have hci : ∀ i : ℕ, Continuous (fun ω : Ωg d => ω i) := fun i => continuous_apply i
  have hconst1 : Continuous (fun _ : Ωg d => (Real.sqrt (s N) : ℂ)) := continuous_const
  have hconst2 : Continuous (fun _ : Ωg d => (Real.sqrt (step s t K N) : ℂ)) := continuous_const
  refine Continuous.add ?_ ?_
  · exact hconst1.smul ((continuous_Xmat d N).comp hc0)
  · exact hconst2.smul
      (continuous_finsetSum _ fun i _ => (continuous_Xmat d N).comp (hci i))

/-- `Rlabel` is continuous in `ω`. -/
theorem continuous_Rlabel (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : TestFun d N Φ) :
    Continuous (fun ω : Ωg d => Rlabel d s t K N j Φ ω) := by
  unfold Rlabel
  have hH1 : Continuous (fun ω : Ωg d => H d s t K N (j + 1) ω) := continuous_H d s t K N (j + 1)
  have hHj : Continuous (fun ω : Ωg d => H d s t K N j ω) := continuous_H d s t K N j
  have h1 : Continuous (fun ω : Ωg d => Φ (H d s t K N (j + 1) ω)) :=
    hΦ.contDiff.continuous.comp hH1
  have h2 : Continuous (fun ω : Ωg d => Φ (H d s t K N j ω)) := hΦ.contDiff.continuous.comp hHj
  have h3 : Continuous (fun ω : Ωg d => fderiv ℝ Φ (H d s t K N j ω) (Xmat d N (ω (j + 1)))) :=
    (hΦ.continuous_fderiv.comp hHj).clm_apply
      ((continuous_Xmat d N).comp (continuous_apply (j + 1)))
  have hconst : Continuous (fun _ : Ωg d => (Real.sqrt (step s t K N) : ℝ)) := continuous_const
  exact (h1.sub h2).sub (hconst.smul h3)

/-- **The pathwise bound on the `Ab`-weighted sum of Taylor remainders**: `O(Δ)` pathwise in
`‖X(ω(j+1))‖²`, with the explicit constant `(Σ_a |U(b,a)|)·(C₂/2)`. -/
theorem norm_Rlabel_sum_le (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) (ω : Ωg d) :
    ‖∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω‖
      ≤ (∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N)
        * ‖Xmat d N (ω (j + 1))‖ ^ 2 := by
  calc ‖∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω‖
      ≤ ∑ a : LoopArg (d.L N) 2, ‖(U b a : ℂ) * Rlabel d s t K N j (Φ a) ω‖ := norm_sum_le _ _
    _ = ∑ a : LoopArg (d.L N) 2, |U b a| * ‖Rlabel d s t K N j (Φ a) ω‖ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [norm_mul, show ‖(U b a : ℂ)‖ = |U b a| from RCLike.norm_ofReal (U b a)]
    _ ≤ ∑ a : LoopArg (d.L N) 2,
          |U b a| * ((C₂ / 2) * step s t K N * ‖Xmat d N (ω (j + 1))‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left (norm_Rlabel_le d s t K N j (hΦ a) (hC₂ a) hΔ ω)
          (abs_nonneg _)
    _ = (∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N)
          * ‖Xmat d N (ω (j + 1))‖ ^ 2 := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring

/-- **The `Ab`-weighted sum of Taylor remainders is integrable**, dominated by a constant
multiple of the (integrable) squared norm of the fresh increment. -/
theorem integrable_Rlabel_sum (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) :
    Integrable (fun ω : Ωg d => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω)
      (Pg d) := by
  have hcont : Continuous (fun ω : Ωg d =>
      ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω) :=
    continuous_finsetSum _ fun a _ =>
      continuous_const.mul (continuous_Rlabel d s t K N j (hΦ a))
  have hgint : Integrable (fun ω : Ωg d =>
      (∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N)
        * ‖Xmat d N (ω (j + 1))‖ ^ 2) (Pg d) :=
    (integrable_normSq_incr d N j).const_mul _
  exact hgint.mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => norm_Rlabel_sum_le d s t K N j hΦ hC₂ hΔ U b ω)

/-- **`Z` has conditional mean zero, complex-valued.** Lifted from the real-valued
`condExp_linear_eq_zero` (T1482) along the continuous ℝ-linear embedding `ℝ ↪ ℂ`. -/
theorem condExp_stepZ_eq_zero (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)
    (hIntReal : Integrable (stepZ d s t K N j Φ U b) (Pg d)) :
    (Pg d)[fun ω => (stepZ d s t K N j Φ U b ω : ℂ) | filt d j] =ᵐ[Pg d] fun _ => (0 : ℂ) := by
  have hreal : (Pg d)[stepZ d s t K N j Φ U b | filt d j] =ᵐ[Pg d] fun _ => (0 : ℝ) := by
    have h := condExp_linear_eq_zero s t K N j (measurable_Ab d s t K N j hΦ U b)
      Set.univ MeasurableSet.univ (show Integrable
        (fun ω => Real.sqrt (step s t K N) * lin N (Ab d s t K N j Φ U b ω) (Xmat d N (ω (j + 1))))
        (Pg d) from hIntReal)
    rw [Set.indicator_univ] at h
    unfold stepZ
    exact h
  have hlift := ContinuousLinearMap.comp_condExp_comm (μ := Pg d) (m := filt d j)
    hIntReal Complex.ofRealCLM
  have hlift' : (fun ω => (((Pg d)[stepZ d s t K N j Φ U b | filt d j]) ω : ℂ))
      =ᵐ[Pg d] (Pg d)[fun ω => (stepZ d s t K N j Φ U b ω : ℂ) | filt d j] := by
    simpa [Function.comp_def] using hlift
  refine hlift'.symm.trans ?_
  filter_upwards [hreal] with ω hω
  simp [hω]

/-- **The pointwise identity.** `Φ_a(H_{j+1}ω)`, `Ab`-weighted and summed, splits exactly into
the F_j-measurable "self" term, `stepZ`, and the `Ab`-weighted Taylor remainder. -/
theorem g_eq_pointwise (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) (ω : Ωg d) :
    (∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω))
      = (∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N j ω))
        + (stepZ d s t K N j Φ U b ω : ℂ)
        + ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω := by
  have hZ := sum_fderiv_eq_stepZ d s t K N j hΦ hReal U b ω
  have hexpand : ∀ a : LoopArg (d.L N) 2,
      (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω)
        = (U b a : ℂ) * Φ a (H d s t K N j ω)
          + (Real.sqrt (step s t K N) : ℂ) * ((U b a : ℂ) *
              fderiv ℝ (Φ a) (H d s t K N j ω) (Xmat d N (ω (j + 1))))
          + (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω := by
    intro a
    have hR : Rlabel d s t K N j (Φ a) ω
        = Φ a (H d s t K N (j + 1) ω) - Φ a (H d s t K N j ω)
          - (Real.sqrt (step s t K N) : ℂ) *
            fderiv ℝ (Φ a) (H d s t K N j ω) (Xmat d N (ω (j + 1))) := by
      unfold Rlabel; rw [Complex.real_smul]
    rw [hR]; ring
  rw [Finset.sum_congr rfl fun a _ => hexpand a, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hZ]

/-- `h0 := Σ_a U(b,a)·Φ_a(H_jω)` is `filt d j`-measurable. -/
theorem measurable_h0 (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) :
    Measurable[filt d j]
      (fun ω : Ωg d => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N j ω)) := by
  have hHm : Measurable[filt d j] (fun ω : Ωg d => H d s t K N j ω) :=
    H_measurable_filt d s t K N j
  exact Finset.measurable_sum _ fun a _ =>
    Measurable.const_mul (((hΦ a).contDiff.continuous.measurable.comp hHm)) (U b a : ℂ)

/-- `h0` is integrable: it is a finite sum of bounded functions. -/
theorem integrable_h0 (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) :
    Integrable
      (fun ω : Ωg d => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N j ω)) (Pg d) :=
  integrable_finsetSum _ fun a _ =>
    (integrable_Phi_H d s t K N j (hΦ a)).const_mul (U b a : ℂ)

/-- `Z`, cast to `ℂ`, is integrable (the real cast of an integrable real function). -/
theorem integrable_stepZ_complex (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)
    (hIntReal : Integrable (stepZ d s t K N j Φ U b) (Pg d)) :
    Integrable (fun ω => (stepZ d s t K N j Φ U b ω : ℂ)) (Pg d) :=
  hIntReal.ofReal

/-- **The a.e. identity behind (T2).** `ξ b` agrees a.e. with `Z b` plus the `Ab`-weighted
Taylor-remainder martingale difference. -/
theorem stepXi_eq_ae (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)
    (hIntReal : Integrable (stepZ d s t K N j Φ U b) (Pg d)) :
    stepXi d s t K N j Φ U b
      =ᵐ[Pg d] fun ω => (stepZ d s t K N j Φ U b ω : ℂ)
        + ((∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω)
          - (Pg d)[fun ω' => ∑ a : LoopArg (d.L N) 2,
              (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω' | filt d j] ω) := by
  set h0 : Ωg d → ℂ :=
    fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N j ω) with hh0def
  set R : Ωg d → ℂ :=
    fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω with hRdef
  set Zc : Ωg d → ℂ := fun ω => (stepZ d s t K N j Φ U b ω : ℂ) with hZcdef
  set g : Ωg d → ℂ :=
    fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω) with hgdef
  have hgeq : g = h0 + Zc + R := funext fun ω => g_eq_pointwise d s t K N j hΦ hReal U b ω
  have hh0meas := measurable_h0 d s t K N j hΦ U b
  have hh0int := integrable_h0 d s t K N j hΦ U b
  have hZcint := integrable_stepZ_complex d s t K N j U b hIntReal
  have hRint := integrable_Rlabel_sum d s t K N j hΦ hC₂ hΔ U b
  have hcondg : (Pg d)[g | filt d j]
      =ᵐ[Pg d] (Pg d)[h0 | filt d j] + (Pg d)[Zc | filt d j] + (Pg d)[R | filt d j] := by
    rw [hgeq]
    exact (condExp_add (hh0int.add hZcint) hRint (filt d j)).trans
      ((condExp_add hh0int hZcint (filt d j)).add (EventuallyEq.refl _ _))
  have hh0cond : (Pg d)[h0 | filt d j] =ᵐ[Pg d] h0 := by
    rw [condExp_of_stronglyMeasurable ((filt d).le j) hh0meas.stronglyMeasurable hh0int]
  have hZccond : (Pg d)[Zc | filt d j] =ᵐ[Pg d] fun _ => (0 : ℂ) :=
    condExp_stepZ_eq_zero d s t K N j hΦ U b hIntReal
  have hstepXi : stepXi d s t K N j Φ U b = fun ω => g ω - (Pg d)[g | filt d j] ω := rfl
  rw [hstepXi]
  filter_upwards [hcondg, hh0cond, hZccond] with ω hω1 hω2 hω3
  have hω1' : (Pg d)[g | filt d j] ω = h0 ω + (Pg d)[R | filt d j] ω := by
    rw [hω1]; simp only [Pi.add_apply, hω2, hω3, zero_add, add_zero]
  rw [hω1']
  have hgω : g ω = h0 ω + Zc ω + R ω := by rw [hgeq]; rfl
  rw [hgω]
  ring

/-- **`stepY` a.e. equals the `Ab`-weighted Taylor remainder minus its own conditional mean.**
Immediate from `stepXi_eq_ae` and `stepY := stepXi - Z` (pointwise). -/
theorem stepY_eq_ae (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)
    (hIntReal : Integrable (stepZ d s t K N j Φ U b) (Pg d)) :
    stepY d s t K N j Φ U b
      =ᵐ[Pg d] fun ω => (∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω)
        - (Pg d)[fun ω' => ∑ a : LoopArg (d.L N) 2,
            (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω' | filt d j] ω := by
  have hXi := stepXi_eq_ae d s t K N j hΦ hReal hC₂ hΔ U b hIntReal
  filter_upwards [hXi] with ω hω
  show stepXi d s t K N j Φ U b ω - (stepZ d s t K N j Φ U b ω : ℂ) = _
  rw [hω]; ring

set_option maxHeartbeats 4000000 in
-- these lemmas chain several `set`-bound local `condExp` targets through
-- `calc`/`nlinarith`; the default heartbeat budget is not enough for the kernel
-- to re-check the resulting elaborated term.
/-- **The pathwise `L²`-bound on `Y`, a.e.** `‖Y b ω‖ ≤ C₂'·Δ·‖X(ω(j+1))‖² + (its conditional
mean)`, with the explicit constant `C₂' := (Σ_a |U(b,a)|)·(C₂/2)`. -/
theorem stepY_norm_le_ae (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)
    (hIntReal : Integrable (stepZ d s t K N j Φ U b) (Pg d)) :
    ∀ᵐ ω ∂(Pg d), ‖stepY d s t K N j Φ U b ω‖
      ≤ (∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N)
          * ‖Xmat d N (ω (j + 1))‖ ^ 2
        + (Pg d)[fun ω' => (∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N)
            * ‖Xmat d N (ω' (j + 1))‖ ^ 2 | filt d j] ω := by
  have hY := stepY_eq_ae d s t K N j hΦ hReal hC₂ hΔ U b hIntReal
  set R : Ωg d → ℂ :=
    fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω with hRdef
  set g : Ωg d → ℝ := fun ω => (∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N)
      * ‖Xmat d N (ω (j + 1))‖ ^ 2 with hgdef
  have hRnorm : ∀ ω, ‖R ω‖ ≤ g ω := fun ω => norm_Rlabel_sum_le d s t K N j hΦ hC₂ hΔ U b ω
  have hgint : Integrable g (Pg d) := (integrable_normSq_incr d N j).const_mul _
  have hRint : Integrable R (Pg d) := integrable_Rlabel_sum d s t K N j hΦ hC₂ hΔ U b
  have hcondRmono : (Pg d)[fun ω => ‖R ω‖ | filt d j] ≤ᵐ[Pg d] (Pg d)[g | filt d j] :=
    condExp_mono hRint.norm hgint (Filter.Eventually.of_forall hRnorm)
  have hnormcond : (fun x => ‖(Pg d)[R | filt d j] x‖) ≤ᵐ[Pg d] (Pg d)[fun x => ‖R x‖ | filt d j] :=
    _root_.norm_condExp_le R
  filter_upwards [hY, hcondRmono, hnormcond] with ω hω h2 h3
  rw [hω]
  calc ‖R ω - (Pg d)[R | filt d j] ω‖
      ≤ ‖R ω‖ + ‖(Pg d)[R | filt d j] ω‖ := norm_sub_le _ _
    _ ≤ g ω + (Pg d)[g | filt d j] ω := add_le_add (hRnorm ω) (le_trans h3 h2)

set_option maxHeartbeats 4000000 in
-- these lemmas chain several `set`-bound local `condExp` targets through
-- `calc`/`nlinarith`; the default heartbeat budget is not enough for the kernel
-- to re-check the resulting elaborated term.
/-- **(T2) `RBM.Gauss.Grid.stepDecomp`.** The pathwise `Z`/`Y` decomposition of one grid step:
`ξ b ω = Z b ω + Y b ω` (pointwise, by construction), `Ab` is `filt d j`-measurable, `Y`'s
pathwise `L²` bound holds a.e. with the explicit constant `(Σ_a|U(b,a)|)(C₂/2)`, and `Y` has
conditional mean zero. -/
theorem stepDecomp (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)
    (hIntReal : Integrable (stepZ d s t K N j Φ U b) (Pg d)) :
    (∀ ω, stepXi d s t K N j Φ U b ω
        = (stepZ d s t K N j Φ U b ω : ℂ) + stepY d s t K N j Φ U b ω)
      ∧ Measurable[filt d j] (fun ω => Ab d s t K N j Φ U b ω)
      ∧ (∀ᵐ ω ∂(Pg d), ‖stepY d s t K N j Φ U b ω‖
          ≤ (∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N)
              * ‖Xmat d N (ω (j + 1))‖ ^ 2
            + (Pg d)[fun ω' => (∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N)
                * ‖Xmat d N (ω' (j + 1))‖ ^ 2 | filt d j] ω)
      ∧ (Pg d)[stepY d s t K N j Φ U b | filt d j] =ᵐ[Pg d] fun _ => (0 : ℂ) :=
  ⟨fun ω => by unfold stepY; ring, measurable_Ab d s t K N j hΦ U b,
    stepY_norm_le_ae d s t K N j hΦ hReal hC₂ hΔ U b hIntReal,
    by
      have hY := stepY_eq_ae d s t K N j hΦ hReal hC₂ hΔ U b hIntReal
      have hRint := integrable_Rlabel_sum d s t K N j hΦ hC₂ hΔ U b
      have hcond : (Pg d)[fun ω => ∑ a : LoopArg (d.L N) 2,
          (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω
            - (Pg d)[fun ω' => ∑ a : LoopArg (d.L N) 2,
                (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω' | filt d j] ω | filt d j]
          =ᵐ[Pg d] fun _ => (0 : ℂ) := by
        set R : Ωg d → ℂ :=
          fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω with hRdef
        have hsub := condExp_sub hRint (integrable_condExp (f := R) (m := filt d j)) (filt d j)
        have hidem : (Pg d)[(Pg d)[R | filt d j] | filt d j] =ᵐ[Pg d] (Pg d)[R | filt d j] :=
          condExp_condExp_of_le (le_refl (filt d j)) ((filt d).le j)
        have hfe : (fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω
            - (Pg d)[R | filt d j] ω) = R - (Pg d)[R | filt d j] := by
          funext ω
          show R ω - (Pg d)[R | filt d j] ω = (R - (Pg d)[R | filt d j]) ω
          rw [Pi.sub_apply]
        rw [hfe]
        filter_upwards [hsub, hidem] with ω hω1 hω2
        rw [hω1]
        simp only [Pi.sub_apply]
        rw [hω2]
        ring
      exact (condExp_congr_ae hY).trans hcond⟩

set_option maxHeartbeats 4000000 in
-- these lemmas chain several `set`-bound local `condExp` targets through
-- `calc`/`nlinarith`; the default heartbeat budget is not enough for the kernel
-- to re-check the resulting elaborated term.
/-- **(T3) `RBM.Gauss.Grid.stepDecomp_Y_sq`.** The `L²` bound on `Y`:
`∫ ‖Y b‖² ≤ 4·((Σ_a|U(b,a)|)·(C₂/2))²·Δ²·∫‖Xmat‖⁴`. Proved from the pathwise bound `stepDecomp`
gives (`‖Y b ω‖ ≤ g ω + E[g|F_j] ω` with `g ω := (Σ_a|U(b,a)|)·((C₂/2)·Δ)·‖X(ω(j+1))‖²`) via
`(x+y)² ≤ 2x²+2y²`, the conditional Jensen inequality at the convex map `x ↦ x²`
(`ConvexOn.map_condExp_le_univ`) to bound `E[g|F_j]²` by `E[g²|F_j]`, the tower property
(`integral_condExp`) to identify `∫E[g²|F_j]` with `∫g²`, and the fourth moment of a single
increment of `Xmat` (`integrable_normPow4_incr`) to compute `∫g²` explicitly. -/
theorem stepDecomp_Y_sq (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
    (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)
    (hIntReal : Integrable (stepZ d s t K N j Φ U b) (Pg d)) :
    ∫ ω, ‖stepY d s t K N j Φ U b ω‖ ^ 2 ∂(Pg d)
      ≤ 4 * ((∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2)) ^ 2 * (step s t K N) ^ 2
          * ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) := by
  have hYbound := stepY_norm_le_ae d s t K N j hΦ hReal hC₂ hΔ U b hIntReal
  set g : Ωg d → ℝ := fun ω => (∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N)
      * ‖Xmat d N (ω (j + 1))‖ ^ 2 with hgdef
  -- the key algebraic identity behind `g²`, in the exact grouping the target constant needs
  have heqg2 : (fun ω => (g ω) ^ 2)
      = fun ω => (((∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2)) ^ 2 * (step s t K N) ^ 2)
        * ‖Xmat d N (ω (j + 1))‖ ^ 4 := by
    rw [hgdef]; funext ω; ring
  have hgint : Integrable g (Pg d) := by
    rw [hgdef]
    exact (integrable_normSq_incr d N j).const_mul
      ((∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N))
  have hg2int : Integrable (fun ω => (g ω) ^ 2) (Pg d) := by
    rw [heqg2]
    exact (integrable_normPow4_incr d N j).const_mul
      (((∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2)) ^ 2 * (step s t K N) ^ 2)
  have hg2eq : ∫ ω, (g ω) ^ 2 ∂(Pg d)
      = ((∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2)) ^ 2 * (step s t K N) ^ 2
          * ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) := by
    rw [heqg2, integral_const_mul]
  -- the conditional Jensen inequality at the convex map `x ↦ x²`
  have hcvx : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := Even.convexOn_pow even_two
  have hcont : LowerSemicontinuous (fun x : ℝ => x ^ 2) := (continuous_pow 2).lowerSemicontinuous
  have hJensen : (fun ω => ((Pg d)[g | filt d j] ω) ^ 2)
      ≤ᵐ[Pg d] (Pg d)[fun ω => (g ω) ^ 2 | filt d j] :=
    hcvx.map_condExp_le_univ ((filt d).le j) hcont hgint hg2int
  -- combine the pathwise bound with `(x+y)² ≤ 2x²+2y²` and the Jensen bound
  have hcomb : ∀ᵐ ω ∂(Pg d), ‖stepY d s t K N j Φ U b ω‖ ^ 2
      ≤ 2 * (g ω) ^ 2 + 2 * (Pg d)[fun ω' => (g ω') ^ 2 | filt d j] ω := by
    filter_upwards [hYbound, hJensen] with ω h1 h2
    have hsq : ‖stepY d s t K N j Φ U b ω‖ ^ 2
        ≤ (g ω + (Pg d)[g | filt d j] ω) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [hsq, h2, sq_nonneg (g ω - (Pg d)[g | filt d j] ω)]
  have hRHSint : Integrable (fun ω => 2 * (g ω) ^ 2
      + 2 * (Pg d)[fun ω' => (g ω') ^ 2 | filt d j] ω) (Pg d) :=
    (hg2int.const_mul 2).add (Integrable.const_mul integrable_condExp 2)
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    hRHSint hcomb
  rw [integral_add (hg2int.const_mul 2) (Integrable.const_mul integrable_condExp 2),
    integral_const_mul, integral_const_mul, integral_condExp ((filt d).le j), hg2eq] at hmono
  have hgoal : (2 : ℝ) * (((∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2)) ^ 2
        * (step s t K N) ^ 2 * ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d))
      + 2 * (((∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2)) ^ 2
        * (step s t K N) ^ 2 * ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d))
      = 4 * ((∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2)) ^ 2 * (step s t K N) ^ 2
        * ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) := by ring
  linarith [hmono, hgoal]

set_option maxHeartbeats 4000000 in
-- these lemmas chain several `set`-bound local `condExp` targets through
-- `calc`/`nlinarith`; the default heartbeat budget is not enough for the kernel
-- to re-check the resulting elaborated term.
/-- **(T4) `RBM.Gauss.Grid.stepDecomp_Z_subG`.** `Z b` satisfies the hypotheses of
`hasCondSubgaussianMGF_linear` (T1482, `Gauss/GridMarkov.lean:564`) with the deterministic
pointwise variance bound `c := Δ · v N (Ab ω)`, on any `filt d j`-event `E` where this bound holds
deterministically. Immediate from `hasCondSubgaussianMGF_linear` applied to `A := Ab ...` (which
is `filt d j`-measurable by `measurable_Ab`), since `stepZ` is *exactly* `Real.sqrt Δ · lin N
(Ab ω) (Xmat d N (ω (j+1)))`, the form `hasCondSubgaussianMGF_linear` consumes. -/
theorem stepDecomp_Z_subG (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)
    (E : Set (Ωg d)) (hE : MeasurableSet[filt d j] E) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ ω ∈ E, step s t K N * v N (Ab d s t K N j Φ U b ω) ≤ c) :
    HasCondSubgaussianMGF (filt d j) ((filt d).le j)
      (fun ω => E.indicator (fun ω => stepZ d s t K N j Φ U b ω) ω) ⟨c, hc⟩ (Pg d) := by
  have h := hasCondSubgaussianMGF_linear s t K N j (measurable_Ab d s t K N j hΦ U b) E hE c hc
    hbound
  simpa only [stepZ] using h

end StepDecomp

end RBM.Gauss.Grid

end
