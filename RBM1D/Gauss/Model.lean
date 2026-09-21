/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Hypotheses
import RBM1D.Green.EntryBound
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The Gaussian band matrix `X` and the flow `H_u = √u · X` (the "moment route")

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, (2.34).

This file builds an **explicit** probability space and an explicit `RBM.Sample`, replacing the
matrix Brownian motion of (2.34) by the scaling flow

  `H_u := √u • X`,  `X` a fixed Hermitian Gaussian band matrix with `E|X_ij|² = S_ij`.

## Why this is legitimate (and where it deviates from the paper)

For each fixed `u`, `√u · X` has exactly the law of the paper's `H_u` — the centred Gaussian
Hermitian matrix with variance profile `u S`, which is (2.34).  The whole loop hierarchy of the
paper only ever uses **one-time marginals**, so every statement we need about the law is
unchanged.

What is *not* the same: `u ↦ √u · X` is **not** a Brownian motion; its increments are not
independent, it is not a martingale, and there is no Itô calculus for it.  The three places
where the paper genuinely uses path properties (the stochastic integral of Lemma 5.3, BDG in
Lemma 5.5, and the stopping time of (5.43)) are replaced, elsewhere, by a generator identity
plus Grönwall (T71/T72) and by continuous induction (T75).  The uncountable union in
Definition 2.1 (i) is handled by an `N^{-C}` time net plus the deterministic Lipschitz bound
`RBM.Gauss.norm_Hflow_sub` proved here (T73).  **This is a major deviation; see
`docs/paper-deltas.md`.**

## The indexing convention (T70 and T71 must match this verbatim)

Everything is built on one big product of one-dimensional Gaussians.

* The matrix index at size parameter `N` is `Idx d N = ZMod (d.L N) × Fin (d.W N)`, the
  block/offset index of `RBM1D/Defs/Model.lean` (definitionally `RBM.Band.Idx`).
* `idxKey d N (a, α) = d.W N * a.val + α` is an **injective** `ℕ`-valued key on `Idx d N`
  (`RBM.Gauss.idxKey_injective`).  "`i < j`" always means `idxKey i < idxKey j`.  This is the
  linear order fixing which entries carry the independent coordinates.
* The coordinate index is `Coord d = Σ N : ℕ, Idx d N × Idx d N × Bool`; the `Bool` is
  `true` for the **real** part and `false` for the **imaginary** part.
* `Ω d = Coord d → ℝ` and `P d = Measure.infinitePi (fun c ↦ gaussianReal 0 (gvar d c))`,
  an infinite product of centred real Gaussians (so all coordinates are independent).
* The variance is `gvar d ⟨N, i, j, _⟩ = S_ij` if `i = j` and `S_ij / 2` otherwise,
  where `S_ij = RBM.Sblk (d.L N) (d.W N) i j` is the real variance profile
  `S = S^(B) ⊗ S_W` of Section 2.1.  Both tags of a pair carry the same variance.
* The matrix is read off by `RBM.Gauss.Xentry`:

  | case | value of `X_ij` |
  |---|---|
  | `idxKey i < idxKey j` | `ω⟨N,i,j,true⟩ + I · ω⟨N,i,j,false⟩` |
  | `idxKey j < idxKey i` | `ω⟨N,j,i,true⟩ - I · ω⟨N,j,i,false⟩` |
  | `i = j` | `ω⟨N,i,i,true⟩` (real) |

  So the **independent coordinates are exactly those of the pairs `i ≤ j`**, real and
  imaginary parts separately, and `X_ji = conj X_ij` holds *pointwise* in `ω`
  (`RBM.Gauss.Xmat_isHermitian`), not just almost surely.
* The coordinates `⟨N, i, j, b⟩` with `idxKey j < idxKey i`, and `⟨N, i, i, false⟩`, do exist in
  the product but are **never read** by `Xentry`.  They are harmless independent noise; any
  sum over coordinates in T71 should be restricted to the *used* ones (or note that
  `∂_c (Xmat) = 0` for the unused `c`).

With this convention `E|X_ij|² = S_ij` for every `i, j` — on the diagonal one real Gaussian of
variance `S_ii`, off the diagonal two independent ones of variance `S_ij / 2` each.  This is
**proved**, as `RBM.Gauss.integral_normSq_Xentry`; it is the sanity check that the `1/2` and the
diagonal case of `gvar` are right.

## Main definitions

* `RBM.Gauss.Dims`          — the dimensions `W, L` and the bandwidth condition (2.2);
  everything of `RBM.Band` except the probability measure.
* `RBM.Gauss.Coord`, `RBM.Gauss.Ω`, `RBM.Gauss.gvar`, `RBM.Gauss.P` — the probability space.
* `RBM.Gauss.Xentry`, `RBM.Gauss.Xmat` — the fixed Gaussian band matrix `X`.
* `RBM.Gauss.Hflow` — `H_u = √u • X`.
* `RBM.Gauss.band : RBM.Band (Ω d)` and `RBM.Gauss.sample : RBM.Sample (band d)` — the
  instantiation of the interface of `RBM1D/Flow/Hypotheses.lean`.
* `RBM.Gauss.OpNormBound` — `‖X‖ ≺ 1`.  Declared here as a one-field structure, but **proved**
  in `RBM1D/Gauss/TraceMoment.lean` (`RBM.Gauss.opNormBound_gauss`, T109); see below.

## Main results

* `RBM.Gauss.Xmat_isHermitian`, `RBM.Gauss.measurable_Xentry`, `RBM.Gauss.Hflow_zero` — the
  three fields of `RBM.Sample`.
* `RBM.Gauss.Hflow_sub` : `H_u - H_u' = (√u - √u') • X` (the algebraic form).
* `RBM.Gauss.norm_Hflow_sub_apply` : `‖(H_u - H_u')_{ij}‖ = |√u - √u'| ‖X_ij‖` (entrywise).
* `RBM.Gauss.norm_Hflow_sub` : `‖H_u - H_u'‖ = |√u - √u'| ‖X‖` for the `ℓ²→ℓ²` operator norm.
* `RBM.Gauss.abs_sqrt_sub_sqrt_le` : `|√u - √u'| ≤ √|u - u'|`, the form in which T73 turns a
  time net of spacing `N^{-C}` into an error `N^{-C/2}`.
* `RBM.Gauss.integral_normSq_Xentry` : `E|X_ij|² = S_ij`, for every `i, j`.
* `RBM.Gauss.P_map_eval` : the law of a single coordinate is `gaussianReal 0 (gvar d c)`;
  `RBM.Gauss.P_map_restrict` : the joint law of any **finite** set of coordinates is the
  `MeasureTheory.Measure.pi` of the corresponding one-dimensional Gaussians.  This is the
  entry point for the Stein identity of T70.

## Two items this header used to list as missing — both are now closed

* **`‖X‖ ≺ 1`** (the Gaussian tail of the operator norm) **is proved** (T109):
  `RBM.Gauss.opNormBound_gauss : ∀ d : Dims, OpNormBound d` in `RBM1D/Gauss/TraceMoment.lean`,
  via `E Tr(X^{2p}) ≤ C_p N` and `RBM.Gauss.opNormBound_of_traceMomentBound`
  (`RBM1D/Gauss/OpNorm.lean`).  The one-field structure `RBM.Gauss.OpNormBound` below is kept
  (it is a frozen signature, taken as a hypothesis by a number of downstream statements), but
  it is no longer an open assumption: it is discharged unconditionally.
  `docs/paper-deltas.md` #49 is closed.
* **An inhabitant of `RBM.Gauss.Dims`** is produced in `RBM1D/Gauss/DimsExample.lean` (T202):
  `RBM.Gauss.Dims.example` (`L ≡ 3`, `W = max 1 ⌊N/3⌋`, `c = 1/4`) and the non-degenerate
  `RBM.Gauss.Dims.exampleGrow` (`L ≈ N^{1/4} → ∞`, `W ≈ N^{3/4} → ∞`, `c = 1/8`).  So the
  moment route is no longer conditional on `Dims` being non-empty, and the statements
  quantified over `d : Dims` are not vacuous.

**No `axiom` is introduced anywhere in this file.**
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ### The dimensions -/

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

instance neZeroL (N : ℕ) : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩

/-- The matrix index `ZMod L × Fin W` (block, offset); definitionally `RBM.Band.Idx`. -/
abbrev Idx (N : ℕ) : Type := ZMod (d.L N) × Fin (d.W N)

end Dims

/-! ### The linear order on the index set

`idxKey` is the linear order that decides which of `X_ij`, `X_ji` carries the independent
coordinates.  `X_ij` for `idxKey i ≤ idxKey j` are the independent entries. -/

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

theorem eq_of_not_lt_not_lt {d : Dims} {N : ℕ} {i j : d.Idx N}
    (h₁ : ¬ idxKey d N i < idxKey d N j) (h₂ : ¬ idxKey d N j < idxKey d N i) : i = j :=
  idxKey_injective d N (le_antisymm (not_lt.1 h₂) (not_lt.1 h₁))

/-! ### The probability space -/

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

@[simp] theorem gvar_diag (d : Dims) (N : ℕ) (i : d.Idx N) (b : Bool) :
    (gvar d ⟨N, i, i, b⟩ : ℝ) = Sblk (d.L N) (d.W N) i i := by
  show (if i = i then Sblk (d.L N) (d.W N) i i else Sblk (d.L N) (d.W N) i i / 2) = _
  exact ite_eq_left rfl

theorem gvar_offDiag (d : Dims) (N : ℕ) (i j : d.Idx N) (b : Bool) (hij : i ≠ j) :
    (gvar d ⟨N, i, j, b⟩ : ℝ) = Sblk (d.L N) (d.W N) i j / 2 := by
  show (if i = j then Sblk (d.L N) (d.W N) i j else Sblk (d.L N) (d.W N) i j / 2) = _
  exact ite_eq_right hij

/-- The measure: the infinite product of the centred one-dimensional Gaussians
`gaussianReal 0 (gvar d c)`.  All coordinates are independent. -/
noncomputable def P (d : Dims) : Measure (Ω d) :=
  Measure.infinitePi fun c => gaussianReal 0 (gvar d c)

instance isProbabilityMeasure_P (d : Dims) : IsProbabilityMeasure (P d) := by
  unfold P; infer_instance

/-- **The law of one coordinate.**  Entry point for the one-dimensional Stein identity (T70). -/
theorem P_map_eval (d : Dims) (c : Coord d) :
    (P d).map (fun ω => ω c) = gaussianReal 0 (gvar d c) :=
  Measure.infinitePi_map_eval _ c

/-- **The joint law of finitely many coordinates** is the `Measure.pi` of the corresponding
one-dimensional Gaussians.  Entry point for the product form of Stein's identity (T70). -/
theorem P_map_restrict (d : Dims) (I : Finset (Coord d)) :
    (P d).map I.restrict = Measure.pi fun c : I => gaussianReal 0 (gvar d c) :=
  Measure.infinitePi_map_restrict _

/-! ### The Gaussian band matrix `X` -/

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

@[simp] theorem Xmat_apply (d : Dims) (N : ℕ) (ω : Ω d) (i j : d.Idx N) :
    Xmat d N ω i j = Xentry d N ω i j := rfl

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

/-! ### `E|X_ij|² = S_ij`

A sanity check on the indexing convention above: if the factor `1/2` in `gvar` were wrong, or
if the diagonal were treated like the off-diagonal, this would fail. -/

section SecondMoment

theorem Sblk_comm (L W : ℕ) (i j : ZMod L × Fin W) : Sblk L W i j = Sblk L W j i := by
  unfold Sblk
  rw [show j.1 - i.1 = -(i.1 - j.1) by ring, sbKre_neg]

theorem integrable_sq_coord (d : Dims) (c : Coord d) :
    Integrable (fun ω : Ω d => (ω c) ^ 2) (P d) := by
  have hf : AEMeasurable (fun ω : Ω d => ω c) (P d) := (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ 2) ((P d).map fun ω => ω c) := by
    rw [P_map_eval]
    exact (memLp_id_gaussianReal (μ := 0) (v := gvar d c) 2).integrable_sq
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

theorem integral_sq_coord (d : Dims) (c : Coord d) :
    ∫ ω, (ω c) ^ 2 ∂(P d) = (gvar d c : ℝ) := by
  have hf : AEMeasurable (fun ω : Ω d => ω c) (P d) := (measurable_pi_apply c).aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 2) ((P d).map fun ω => ω c) := by
    fun_prop
  rw [← integral_map hf hg, P_map_eval]
  have h := variance_fun_id_gaussianReal (μ := 0) (v := gvar d c)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- **`E|X_ij|² = S_ij`** — the defining second moment of the band matrix, for every pair
`(i, j)`, diagonal included. -/
theorem integral_normSq_Xentry (d : Dims) (N : ℕ) (i j : d.Idx N) :
    ∫ ω, ‖Xentry d N ω i j‖ ^ 2 ∂(P d) = Sblk (d.L N) (d.W N) i j := by
  have key : ∀ (p q : Coord d) (S : ℝ), (gvar d p : ℝ) = S / 2 → (gvar d q : ℝ) = S / 2 →
      (∫ ω, ((ω p) ^ 2 + (ω q) ^ 2) ∂(P d)) = S := by
    intro p q S hp hq
    rw [integral_add (integrable_sq_coord d p) (integrable_sq_coord d q),
      integral_sq_coord, integral_sq_coord, hp, hq]
    ring
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · -- `idxKey i < idxKey j`: `X_ij = ω(i,j,tt) + I ω(i,j,ff)`, each of variance `S_ij / 2`
    have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hX : ∀ ω : Ω d, ‖Xentry d N ω i j‖ ^ 2
        = (ω ⟨N, i, j, true⟩) ^ 2 + (ω ⟨N, i, j, false⟩) ^ 2 := by
      intro ω
      rw [Xentry, ite_eq_left h, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    simp only [hX]
    exact key _ _ _ (gvar_offDiag d N i j true hij) (gvar_offDiag d N i j false hij)
  · subst h
    have hX : ∀ ω : Ω d, ‖Xentry d N ω i i‖ ^ 2 = (ω ⟨N, i, i, true⟩) ^ 2 := by
      intro ω
      rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    simp only [hX]
    rw [integral_sq_coord, gvar_diag]
  · -- `idxKey j < idxKey i`: `X_ij = ω(j,i,tt) - I ω(j,i,ff)`
    have hij : j ≠ i := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hX : ∀ ω : Ω d, ‖Xentry d N ω i j‖ ^ 2
        = (ω ⟨N, j, i, true⟩) ^ 2 + (ω ⟨N, j, i, false⟩) ^ 2 := by
      intro ω
      rw [Xentry, ite_eq_right (asymm h), ite_eq_left h, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    simp only [hX]
    rw [key _ _ (Sblk (d.L N) (d.W N) j i) (gvar_offDiag d N j i true hij)
      (gvar_offDiag d N j i false hij)]
    exact (Sblk_comm _ _ i j).symm

end SecondMoment

/-! ### The flow `H_u = √u • X` -/

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

/-! ### The instance of the interface of `RBM1D/Flow/Hypotheses.lean` -/

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

@[simp] theorem band_P (d : Dims) : (band d).P = P d := rfl
@[simp] theorem band_W (d : Dims) : (band d).W = d.W := rfl
@[simp] theorem band_L (d : Dims) : (band d).L = d.L := rfl

/-- **The `RBM.Sample` of the moment route.**  The three fields `hermitian`, `H_zero`,
`measurable` are theorems, not hypotheses. -/
noncomputable def sample (d : Dims) : RBM.Sample (band d) where
  H := fun N u ω => Hflow d N u ω
  hermitian := fun N u ω => Hflow_isHermitian d N u ω
  H_zero := fun N ω => Hflow_zero d N ω
  measurable := fun N u i j => measurable_Hflow d N u i j

@[simp] theorem sample_H (d : Dims) (N : ℕ) (u : ℝ) (ω : Ω d) :
    (sample d).H N u ω = Hflow d N u ω := rfl

/-! ### The deterministic Lipschitz bound

This is the whole basis for removing the uncountable union of Definition 2.1 (i) (T73): on a
time net of spacing `δ` the flow moves by at most `√δ · ‖X‖`, deterministically in `ω`. -/

/-- `H_u - H_{u'} = (√u - √u') • X`. -/
theorem Hflow_sub (d : Dims) (N : ℕ) (u u' : ℝ) (ω : Ω d) :
    Hflow d N u ω - Hflow d N u' ω = ((Real.sqrt u - Real.sqrt u' : ℝ) : ℂ) • Xmat d N ω := by
  simp only [Hflow, Complex.ofReal_sub, sub_smul]

/-- **Entrywise Lipschitz bound**: `|(H_u - H_{u'})_{ij}| = |√u - √u'| · |X_ij|`. -/
theorem norm_Hflow_sub_apply (d : Dims) (N : ℕ) (u u' : ℝ) (ω : Ω d) (i j : d.Idx N) :
    ‖(Hflow d N u ω - Hflow d N u' ω) i j‖
      = |Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω i j‖ := by
  rw [Hflow_sub, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]

section OpNorm

open scoped Matrix.Norms.L2Operator

/-- **The deterministic Lipschitz bound** for the `ℓ² → ℓ²` operator norm:
`‖H_u - H_{u'}‖ = |√u - √u'| · ‖X‖`. -/
theorem norm_Hflow_sub (d : Dims) (N : ℕ) (u u' : ℝ) (ω : Ω d) :
    ‖Hflow d N u ω - Hflow d N u' ω‖ = |Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ := by
  rw [Hflow_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- **`‖X‖ ≺ 1`**, the Gaussian tail of the operator norm of the band matrix.

Packaged as a one-field structure so that downstream files can take it as a hypothesis, in the
style of `RBM.Bounds` in `RBM1D/Flow/Hypotheses.lean`.  The parameter set is `Unit`
(no parameter); the `≺` is `RBM.StochDom` of `RBM1D/Defs/StochDom.lean`.

**It is a theorem** (T109), not an open assumption:
`RBM.Gauss.opNormBound_gauss : ∀ d : Dims, OpNormBound d` in `RBM1D/Gauss/TraceMoment.lean`,
proved from `E Tr(X^{2p}) ≤ C_p N`.  The structure is kept only because a number of frozen
downstream signatures take it as an argument. -/
structure OpNormBound (d : Dims) : Prop where
  /-- `‖X‖ ≺ 1`.  (`RBM.NormStochDom` cannot be used: its value type is a single type, while
  `Xmat d N ω` lives in an `N`-dependent matrix type.  This is the same statement, with the
  norm written out.) -/
  norm_X : RBM.StochDom (P d) (fun N (_ : Unit) ω => ‖Xmat d N ω‖) fun _ _ _ => (1 : ℝ)

/-- With `‖X‖ ≺ 1`, the flow is `≺`-Lipschitz in `u`: `‖H_u - H_{u'}‖ ≺ |√u - √u'|`,
uniformly in `(u, u')`.  This is the form T73 feeds into the time net. -/
theorem OpNormBound.stochDom_norm_Hflow_sub {d : Dims} (h : OpNormBound d) :
    RBM.StochDom (P d)
      (fun N (p : ℝ × ℝ) ω => ‖Hflow d N p.1 ω - Hflow d N p.2 ω‖)
      (fun _ p _ => |Real.sqrt p.1 - Real.sqrt p.2|) := by
  have h1 := h.norm_X.precomp_param (V := fun _ => ℝ × ℝ) fun _ _ => ()
  refine RBM.StochDom.of_subset h1 fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N ω hω => ?_⟩
  obtain ⟨⟨u, u'⟩, hu⟩ := hω
  refine ⟨(u, u'), ?_⟩
  beta_reduce at hu ⊢
  rw [norm_Hflow_sub] at hu
  have habs : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt u'| := abs_nonneg _
  rcases eq_or_lt_of_le habs with h0 | hpos
  · rw [← h0] at hu; simp at hu
  · rw [mul_one]
    nlinarith [hu, hpos]

end OpNorm

/-- `|√u - √u'| ≤ √|u - u'|`: a net of spacing `δ` in `u` moves `H` by at most `√δ ‖X‖`. -/
theorem abs_sqrt_sub_sqrt_le (u u' : ℝ) :
    |Real.sqrt u - Real.sqrt u'| ≤ Real.sqrt |u - u'| := by
  wlog hle : u' ≤ u generalizing u u'
  · rw [abs_sub_comm, abs_sub_comm u u']
    exact this u' u (le_of_not_ge hle)
  have hsub : Real.sqrt u' ≤ Real.sqrt u := Real.sqrt_le_sqrt hle
  rw [abs_of_nonneg (sub_nonneg.2 hsub), abs_of_nonneg (sub_nonneg.2 hle), sub_le_iff_le_add']
  rcases le_or_gt 0 u' with hu' | hu'
  · have hd : (0 : ℝ) ≤ u - u' := sub_nonneg.2 hle
    have h1 : (0 : ℝ) ≤ Real.sqrt u' + Real.sqrt (u - u') := by positivity
    calc Real.sqrt u ≤ Real.sqrt ((Real.sqrt u' + Real.sqrt (u - u')) ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          have e1 : Real.sqrt u' ^ 2 = u' := Real.sq_sqrt hu'
          have e2 : Real.sqrt (u - u') ^ 2 = u - u' := Real.sq_sqrt hd
          nlinarith [mul_nonneg (Real.sqrt_nonneg u') (Real.sqrt_nonneg (u - u'))]
      _ = Real.sqrt u' + Real.sqrt (u - u') := Real.sqrt_sq h1
  · rw [Real.sqrt_eq_zero_of_nonpos hu'.le, zero_add]
    exact Real.sqrt_le_sqrt (by linarith)

end RBM.Gauss

