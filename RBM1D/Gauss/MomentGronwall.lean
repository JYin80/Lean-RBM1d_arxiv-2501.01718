/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Generator
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Moments, the quadratic variation of (5.25), and Grönwall (T72)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*.  This file is the second half of the **moment route** for the stochastic layer: it
turns the generator identity of `RBM1D/Gauss/Generator.lean` (T71) into a differential
inequality for `u ↦ E|F(H_u)|^{2p}` and closes it with Grönwall.

## The pivot

With `Φ = |F|^{2p}` the generator identity's second-order term splits as

  `d/du E|F_u|^{2p} = 2p Re E[|F|^{2p-2} F̄ 𝓛F] + ∑_α S_α E[|F|^{2p-2}(2p(p-1)Re(F̄∂_αF)²/|F|²
        + p ‖∂_αF‖²)]`,

and after `Re(F̄∂_αF)² ≤ ‖F‖²‖∂_αF‖²` the second term is at most
`p(2p-1) E[|F|^{2p-2} ∑_α S_α‖∂_αF‖²]` (`genMomentPt_le`).  The coefficient
`∑_α S_α ‖∂_αF‖²` is **exactly** the quadratic variation of (5.25):

  `∑_{α ∈ usedCoord} S_α ‖∂_α F‖² = ∑_{i,j} |E^{(M)}(α)|²`,  `E^{(M)}(α) = (S_ij)^{1/2} ∂_{H_ij}F`

(`secondOrder_eq_quadVar`).  Since the paper's `U_{u,t,σ}` is a *deterministic linear*
operator, taking `F := fun M => (U ∘ L(M))_a` makes the right-hand side literally the
integrand of (5.25), i.e. the right-hand side of BDG (5.24).  This is why the moment route can
replace Duhamel + BDG by the generator identity + Grönwall without losing anything.

## Main definitions

* `RBM.Gauss.momentFun F p` — `|F|^{2p}`, written `(F conj F)^p`.
* `RBM.Gauss.wirtFirst` — `∂_{M_ij}F` in the Wirtinger convention (the first-derivative
  companion of `RBM.Gauss.wirtSecond`).
* `RBM.Gauss.EmartCoeff` — `E^{(M)}_{t,σ,a}(α) = (S_ij)^{1/2} ∂_{(H_t)_ij} F` of §5.2.
* `RBM.Gauss.quadVar` / `RBM.Gauss.quadVarPairs` — the two sides of the fulcrum: the
  coordinate sum `∑_α S_α‖∂_αF‖²` and the paper's `∑_α |E^{(M)}(α)|²`.
* `RBM.Gauss.genD` — `𝓛F = ½ ∑_α S_α ∂_α²F`; `RBM.Gauss.genMomentPt` — `𝓛(|F|^{2p})`, real.
* `RBM.Gauss.momentIntegral` — `E|F(H_u)|^{2p}`.
* `RBM.Gauss.BddC2` — `C²` with globally bounded value, first and second derivative.
* `RBM.Gauss.resH`, `RBM.Gauss.greenObs` — the resolvent pre-composed with the Hermitian
  projection `hermCLM`, and a fixed continuous `ℝ`-linear observable of it.

## Main results

* `RBM.Gauss.fderiv2_momentFun'` / `RBM.Gauss.fderiv2_momentFun` — the mixed and diagonal
  second directional derivatives of `|F|^{2p}`; `RBM.Gauss.coordD2_momentFun_ofReal` is the
  real form used against the generator identity.
* **`RBM.Gauss.secondOrder_eq_quadVar`** — the fulcrum, see above.
* `RBM.Gauss.genMomentPt_le` (and `RBM.Gauss.genMomentPt_le_quadVarPairs`) —
  `𝓛(|F|^{2p}) ≤ 2p‖F‖^{2p-1}‖𝓛F‖ + p(2p-1)‖F‖^{2p-2} ∑_α S_α‖∂_αF‖²`.
* `RBM.Gauss.hasDerivAt_momentIntegral` — `d/du E|F(H_u)|^{2p} = E[𝓛(|F|^{2p})(H_u)]`
  for `u > 0`, a real-valued statement.
* `RBM.Gauss.le_gronwallBound_of_hasDerivWithinAt_le` and
  **`RBM.Gauss.momentIntegral_le_gronwallBound`** — Grönwall: from
  `d/du E|F|^{2p} ≤ K E|F|^{2p} + ε` on `[a,b)` with `a > 0`, the moment is bounded by
  Mathlib's `gronwallBound δ K ε (u - a)` on `[a,b]`.
* `RBM.Gauss.TestFun.of_bddC2` — `BddC2 F ⟹ TestFun d N (|F|^{2p})`, with explicit constants.
* `RBM.Gauss.bddC2_greenObs`, `RBM.Gauss.testFun_momentFun_greenObs`,
  `RBM.Gauss.hasDerivAt_momentIntegral_greenObs` — the concrete instance: `F = φ(G_z)` with
  `φ` a fixed continuous `ℝ`-linear functional and `G_z = (herm(·) - z)⁻¹`.  All the global
  bounds come from `RBM.Gauss.norm_green_le` (T71): `‖G‖ ≤ η⁻¹`, `‖∂G‖ ≤ η⁻²`,
  `‖∂²G‖ ≤ 2η⁻³`, **on the whole matrix space**, so no good event is needed.

## Hypotheses (nothing here is an `axiom`)

* `RBM.Gauss.MatrixStein d` — T71's hypothesis, owed by T70.  Carried through unchanged.
* `u > 0` in every statement that differentiates (the chain-rule factor `(2√u)⁻¹` of
  `H_u = √u X`), and `0 < a` for the Grönwall interval `[a, b]`.
* `1 ≤ p` in `genMomentPt_le` (for `p = 0` both sides vanish, but the exponents `2p-1`,
  `2p-2` are natural subtraction).
* The Grönwall step takes the differential inequality `∫ 𝓛(|F|^{2p}) ≤ K E|F|^{2p} + ε` as a
  hypothesis: turning `genMomentPt_le` into that inequality needs Hölder and the loop bounds,
  which live downstream.

## Deviations from the paper (for `docs/paper-deltas.md`)

* The flow is `H_u = √u X`, not a Brownian motion (the T69 delta, inherited through T71);
  in particular `𝓛` here is the generator of that flow, not an Itô differential.
* `E^{(M)}(α)` is defined here with `∂_{H_ij}` in the Wirtinger convention (`wirtFirst`),
  matching `RBM.Gauss.wirtSecond`; the paper writes `∂_{(H_t)_ij}` without fixing a
  convention.
* The paper states (5.25) after a Schwarz inequality that splits `E^{(M)}(α)` into its `n`
  edge terms `E^{(M)}(α, k)` (cost `C_n`).  `secondOrder_eq_quadVar` is the identity
  *before* that split, i.e. `∑_α |E^{(M)}(α)|²`; the `∑_k` form of (5.25) follows from it by
  the same Schwarz step, which is not formalized here.
* `secondOrder_eq_quadVar` is stated for a function `F` of the matrix, not for the loop
  observable `L_{t,σ,a}`: the repo's `(E ⊗ E)` (`RBM.SumZeroDyn.Hierarchy.EE`) is an abstract
  structure field with no definition in terms of derivatives, so the two cannot be *equated*
  in Lean today.  See the note below.
* `momentFun`, `BddC2` and the `TestFun` constants ask for *global* bounds, which is stronger
  than anything the paper states and is legitimate exactly because of `norm_green_le`.

## What the fulcrum does **not** yet connect to

`RBM.SumZeroDyn.Hierarchy` (`RBM1D/Hierarchy/SumZeroDyn.lean`) carries `E ⊗ E` as an
*uninterpreted* field `EE`, and states `bdg` / `bdgQ` as `≺`-implications about
`‖U_{u,v} ∘ EE_u‖`.  Nothing in the repo defines `EE` as
`∑_α E^{(M)}(α,k) E^{(M)}(α,k)`, and the loop side lives on `LoopArg`/`LoopIdx` rather than
on matrices.  So T74 (discharging `bdg`) still needs two bridges that are *not* in this file:

1. `L_{u,σ,a}` as a function of the matrix `H`, so that `wirtFirst` applies to it, and the
   identification of `EE` with `∑_α ∂_α L ⊗ ∂_α L` (Definition 5.4);
2. the loop/tensor representation bridge already flagged in `docs/STATUS.md`
   (`LoopIdx` ↔ `Fin n → ZMod L`).

Everything on the matrix side of those two bridges is done here.
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

/-- The second directional derivative, read along the line `s ↦ M + s • B` at `t = 0`. -/
theorem hasDerivAt_dir2 {F : E → V} (hF : ContDiff ℝ 2 F) (M B : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ F (M + t • B) B) (fderiv ℝ (fderiv ℝ F) M B B) 0 :=
  hasDerivAt_dir2' hF M B B

end LineDeriv

/-! ### `|F|^{2p}` and its two directional derivatives -/

section MomentFun

/-- The power rule for a `ℂ`-valued function of a real variable.  (Mathlib's
`HasDerivAt.pow` is stated through the `NormedCommRing` module structure on `ℂ`, which does
not unify with the `NormedSpace ℝ ℂ` one used everywhere else in this file.) -/
theorem hasDerivAt_cpow_succ {u : ℝ → ℂ} {u' : ℂ} {t : ℝ} (h : HasDerivAt u u' t) (n : ℕ) :
    HasDerivAt (fun s => u s ^ (n + 1)) (((n : ℂ) + 1) * u t ^ n * u') t := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      have hmul := h.mul ih
      have hfun : (fun s => u s ^ (n + 1 + 1)) = fun s => u s * u s ^ (n + 1) := by
        funext s; ring
      rw [hfun]
      refine hmul.congr_deriv ?_
      push_cast
      ring

/-- The power rule, in the form with natural subtraction. -/
theorem hasDerivAt_cpow {u : ℝ → ℂ} {u' : ℂ} {t : ℝ} (h : HasDerivAt u u' t) (n : ℕ) :
    HasDerivAt (fun s => u s ^ n) ((n : ℂ) * u t ^ (n - 1) * u') t := by
  cases n with
  | zero => simpa using hasDerivAt_const t (1 : ℂ)
  | succ n => simpa using hasDerivAt_cpow_succ h n

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `|F|^{2p}`, written as `(F · conj F)^p` so that it is manifestly a polynomial in the real
coordinates whenever `F` is. -/
noncomputable def momentFun (F : E → ℂ) (p : ℕ) : E → ℂ :=
  fun M => (F M * (starRingEnd ℂ) (F M)) ^ p

theorem mul_conj_eq (z : ℂ) : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `momentFun F p M = ‖F M‖^{2p}`, a nonnegative real number. -/
theorem momentFun_eq (F : E → ℂ) (p : ℕ) (M : E) :
    momentFun F p M = ((‖F M‖ ^ (2 * p) : ℝ) : ℂ) := by
  rw [momentFun, mul_conj_eq, ← Complex.ofReal_pow, ← pow_mul]

theorem contDiff_conj {n : WithTop ℕ∞} {F : E → ℂ} (hF : ContDiff ℝ n F) :
    ContDiff ℝ n fun M => (starRingEnd ℂ) (F M) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp hF

theorem contDiff_momentFun {n : WithTop ℕ∞} {F : E → ℂ} (hF : ContDiff ℝ n F) (p : ℕ) :
    ContDiff ℝ n (momentFun F p) :=
  (hF.mul (contDiff_conj hF)).pow p

/-- **The first directional derivative of `|F|^{2p}`.** -/
theorem fderiv_momentFun {F : E → ℂ} (hF : ContDiff ℝ 1 F) (p : ℕ) (M B : E) :
    fderiv ℝ (momentFun F p) M B
      = (p : ℂ) * (F M * (starRingEnd ℂ) (F M)) ^ (p - 1)
        * (fderiv ℝ F M B * (starRingEnd ℂ) (F M)
            + F M * (starRingEnd ℂ) (fderiv ℝ F M B)) := by
  set f : ℝ → ℂ := fun s => F (M + s • B) with hf
  set g : ℝ → ℂ := fun s => fderiv ℝ F (M + s • B) B with hg
  have hzero : M + (0 : ℝ) • B = M := by simp
  have hfd : ∀ t : ℝ, HasDerivAt f (g t) t := fun t => hasDerivAt_dir hF M B t
  have hcd : ∀ t : ℝ, HasDerivAt (fun s => (starRingEnd ℂ) (f s)) ((starRingEnd ℂ) (g t)) t := by
    intro t
    have := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt).comp_hasDerivAt t (hfd t)
    simpa [Function.comp_def] using this
  have hprod : ∀ t : ℝ, HasDerivAt (fun s => f s * (starRingEnd ℂ) (f s))
      (g t * (starRingEnd ℂ) (f t) + f t * (starRingEnd ℂ) (g t)) t := fun t =>
    (hfd t).mul (hcd t)
  have hpow : HasDerivAt (fun s => (f s * (starRingEnd ℂ) (f s)) ^ p)
      ((p : ℂ) * (f 0 * (starRingEnd ℂ) (f 0)) ^ (p - 1)
        * (g 0 * (starRingEnd ℂ) (f 0) + f 0 * (starRingEnd ℂ) (g 0))) 0 := by
    simpa using hasDerivAt_cpow (hprod 0) p
  have hlhs : HasDerivAt (fun s : ℝ => momentFun F p (M + s • B))
      (fderiv ℝ (momentFun F p) M B) 0 := by
    have := hasDerivAt_dir (contDiff_momentFun hF p) M B 0
    rwa [hzero] at this
  have hfun : (fun s : ℝ => momentFun F p (M + s • B))
      = fun s : ℝ => (f s * (starRingEnd ℂ) (f s)) ^ p := rfl
  rw [hfun] at hlhs
  have := hlhs.unique hpow
  simpa [hf, hg, hzero] using this

/-- **The mixed second directional derivative of `|F|^{2p}`.**  With `R = F conj F`,
`R'_X = ∂_XF conj F + F conj ∂_XF`,

`∂_B∂_A|F|^{2p} = p ( (p-1) R^{p-2} R'_A R'_B
  + R^{p-1} (∂_B∂_AF conj F + ∂_AF conj ∂_BF + ∂_BF conj ∂_AF + F conj ∂_B∂_AF) )`. -/
theorem fderiv2_momentFun' {F : E → ℂ} (hF : ContDiff ℝ 2 F) (p : ℕ) (M A B : E) :
    fderiv ℝ (fderiv ℝ (momentFun F p)) M B A
      = (p : ℂ) * ((((p - 1 : ℕ)) : ℂ) * (F M * (starRingEnd ℂ) (F M)) ^ (p - 2)
            * ((fderiv ℝ F M A * (starRingEnd ℂ) (F M)
                + F M * (starRingEnd ℂ) (fderiv ℝ F M A))
              * (fderiv ℝ F M B * (starRingEnd ℂ) (F M)
                + F M * (starRingEnd ℂ) (fderiv ℝ F M B)))
          + (F M * (starRingEnd ℂ) (F M)) ^ (p - 1)
            * (fderiv ℝ (fderiv ℝ F) M B A * (starRingEnd ℂ) (F M)
              + fderiv ℝ F M A * (starRingEnd ℂ) (fderiv ℝ F M B)
              + fderiv ℝ F M B * (starRingEnd ℂ) (fderiv ℝ F M A)
              + F M * (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ F) M B A))) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  set f : ℝ → ℂ := fun s => F (M + s • B) with hf
  set gB : ℝ → ℂ := fun s => fderiv ℝ F (M + s • B) B with hgB
  set gA : ℝ → ℂ := fun s => fderiv ℝ F (M + s • B) A with hgA
  set c : ℂ := fderiv ℝ (fderiv ℝ F) M B A with hc
  have hzero : M + (0 : ℝ) • B = M := by simp
  have hf0 : f 0 = F M := by simp [hf]
  have hgB0 : gB 0 = fderiv ℝ F M B := by simp [hgB]
  have hgA0 : gA 0 = fderiv ℝ F M A := by simp [hgA]
  have hfd : ∀ t : ℝ, HasDerivAt f (gB t) t := fun t => hasDerivAt_dir hF1 M B t
  have hgd : HasDerivAt gA c 0 := hasDerivAt_dir2' hF M A B
  have hcd : ∀ t : ℝ, HasDerivAt (fun s => (starRingEnd ℂ) (f s)) ((starRingEnd ℂ) (gB t)) t := by
    intro t
    have := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt).comp_hasDerivAt t (hfd t)
    simpa [Function.comp_def] using this
  have hcgd : HasDerivAt (fun s => (starRingEnd ℂ) (gA s)) ((starRingEnd ℂ) c) 0 := by
    have := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hgd
    simpa [Function.comp_def] using this
  have hR : ∀ t : ℝ, HasDerivAt (fun s => f s * (starRingEnd ℂ) (f s))
      (gB t * (starRingEnd ℂ) (f t) + f t * (starRingEnd ℂ) (gB t)) t := fun t =>
    (hfd t).mul (hcd t)
  have hu : HasDerivAt (fun s => (f s * (starRingEnd ℂ) (f s)) ^ (p - 1))
      (((p - 1 : ℕ) : ℂ) * (f 0 * (starRingEnd ℂ) (f 0)) ^ (p - 1 - 1)
        * (gB 0 * (starRingEnd ℂ) (f 0) + f 0 * (starRingEnd ℂ) (gB 0))) 0 := by
    simpa using hasDerivAt_cpow (hR 0) (p - 1)
  have hv : HasDerivAt (fun s => gA s * (starRingEnd ℂ) (f s) + f s * (starRingEnd ℂ) (gA s))
      (c * (starRingEnd ℂ) (f 0) + gA 0 * (starRingEnd ℂ) (gB 0)
        + (gB 0 * (starRingEnd ℂ) (gA 0) + f 0 * (starRingEnd ℂ) c)) 0 :=
    (hgd.mul (hcd 0)).add ((hfd 0).mul hcgd)
  have hrhs := ((hu.mul hv).const_mul ((p : ℂ)))
  have hlhs : HasDerivAt (fun t : ℝ => fderiv ℝ (momentFun F p) (M + t • B) A)
      (fderiv ℝ (fderiv ℝ (momentFun F p)) M B A) 0 :=
    hasDerivAt_dir2' (contDiff_momentFun hF p) M A B
  have hcongr : (fun t : ℝ => fderiv ℝ (momentFun F p) (M + t • B) A)
      = fun t : ℝ => (p : ℂ) * ((f t * (starRingEnd ℂ) (f t)) ^ (p - 1)
        * (gA t * (starRingEnd ℂ) (f t) + f t * (starRingEnd ℂ) (gA t))) := by
    funext t
    rw [fderiv_momentFun hF1 p (M + t • B) A, mul_assoc]
  rw [hcongr] at hlhs
  have := hlhs.unique hrhs
  rw [this, hf0, hgB0, hgA0, Nat.sub_sub]
  ring

/-- **The second directional derivative of `|F|^{2p}`** along one direction: the diagonal of
`fderiv2_momentFun'`.  This is the expansion the ticket asks for, before taking real parts:
with `R = F conj F`, `R' = ∂F conj F + F conj ∂F` and `R'' = ∂²F conj F + 2 ∂F conj ∂F +
F conj ∂²F`, `∂²|F|^{2p} = p ((p-1) R^{p-2} (R')² + R^{p-1} R'')`. -/
theorem fderiv2_momentFun {F : E → ℂ} (hF : ContDiff ℝ 2 F) (p : ℕ) (M B : E) :
    fderiv ℝ (fderiv ℝ (momentFun F p)) M B B
      = (p : ℂ) * ((((p - 1 : ℕ)) : ℂ) * (F M * (starRingEnd ℂ) (F M)) ^ (p - 2)
            * ((fderiv ℝ F M B * (starRingEnd ℂ) (F M)
                + F M * (starRingEnd ℂ) (fderiv ℝ F M B))
              * (fderiv ℝ F M B * (starRingEnd ℂ) (F M)
                + F M * (starRingEnd ℂ) (fderiv ℝ F M B)))
          + (F M * (starRingEnd ℂ) (F M)) ^ (p - 1)
            * (fderiv ℝ (fderiv ℝ F) M B B * (starRingEnd ℂ) (F M)
              + 2 * (fderiv ℝ F M B * (starRingEnd ℂ) (fderiv ℝ F M B))
              + F M * (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ F) M B B))) := by
  rw [fderiv2_momentFun' hF p M B B]
  ring

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
`d/du E|F(H_u)|^{2p}` (see `RBM.Gauss.sum_coordD2_momentFun_le`); the right side is
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

/-- `z conj w + w conj z = 2 Re(conj w · z)`. -/
theorem add_conj_mul (z w : ℂ) :
    z * (starRingEnd ℂ) w + w * (starRingEnd ℂ) z
      = ((2 * ((starRingEnd ℂ) w * z).re : ℝ) : ℂ) := by
  have h : w * (starRingEnd ℂ) z = (starRingEnd ℂ) (z * (starRingEnd ℂ) w) := by
    simp [mul_comm]
  rw [h, Complex.add_conj, mul_comm z ((starRingEnd ℂ) w)]

/-- **The real form of the second directional derivative of `|F|^{2p}`.**

`∂_α²|F|^{2p} = p ( (p-1) (|F|²)^{p-2} · 4 Re(F̄ ∂_αF)²
                  + (|F|²)^{p-1} · (2‖∂_αF‖² + 2 Re(F̄ ∂_α²F)) )`,

a **real** number (`Φ = |F|^{2p}` is real-valued, so all its real directional derivatives
are). -/
theorem coordD2_momentFun_ofReal (hF : ContDiff ℝ 2 F) (p : ℕ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (q : d.Idx N × d.Idx N × Bool) :
    coordD2 d N (momentFun F p) M q
      = (((p : ℝ) * ((((p - 1 : ℕ)) : ℝ) * (‖F M‖ ^ 2) ^ (p - 2)
              * (4 * ((starRingEnd ℂ) (F M) * coordD1 d N F M q).re ^ 2)
            + (‖F M‖ ^ 2) ^ (p - 1)
              * (2 * ‖coordD1 d N F M q‖ ^ 2
                + 2 * ((starRingEnd ℂ) (F M) * coordD2 d N F M q).re)) : ℝ) : ℂ) := by
  set B := Bmat d N q.1 q.2.1 q.2.2 with hB
  set D1 : ℂ := fderiv ℝ F M B with hD1
  set D2 : ℂ := fderiv ℝ (fderiv ℝ F) M B B with hD2
  have hgoal : coordD2 d N (momentFun F p) M q
      = fderiv ℝ (fderiv ℝ (momentFun F p)) M B B := rfl
  rw [hgoal, fderiv2_momentFun hF p M B]
  have hA : F M * (starRingEnd ℂ) (F M) = ((‖F M‖ ^ 2 : ℝ) : ℂ) := mul_conj_eq (F M)
  have hBB : D1 * (starRingEnd ℂ) (F M) + F M * (starRingEnd ℂ) D1
      = ((2 * ((starRingEnd ℂ) (F M) * D1).re : ℝ) : ℂ) := add_conj_mul D1 (F M)
  have hE : D2 * (starRingEnd ℂ) (F M) + 2 * (D1 * (starRingEnd ℂ) D1)
        + F M * (starRingEnd ℂ) D2
      = ((2 * ((starRingEnd ℂ) (F M) * D2).re + 2 * ‖D1‖ ^ 2 : ℝ) : ℂ) := by
    rw [show D2 * (starRingEnd ℂ) (F M) + 2 * (D1 * (starRingEnd ℂ) D1)
          + F M * (starRingEnd ℂ) D2
        = (D2 * (starRingEnd ℂ) (F M) + F M * (starRingEnd ℂ) D2)
          + 2 * (D1 * (starRingEnd ℂ) D1) by ring,
      add_conj_mul D2 (F M), mul_conj_eq D1]
    push_cast
    ring
  have hc1 : coordD1 d N F M q = D1 := rfl
  have hc2 : coordD2 d N F M q = D2 := rfl
  have hpc : ((p : ℂ)) = (((p : ℝ)) : ℂ) := by norm_cast
  have hpc1 : (((p - 1 : ℕ)) : ℂ) = ((((p - 1 : ℕ)) : ℝ) : ℂ) := by norm_cast
  rw [hA, hBB, hE, hc1, hc2, hpc, hpc1]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  rw [Complex.ofReal_inj]
  ring

/-- `∂_α²|F|^{2p}` is real. -/
theorem coordD2_momentFun_re_ofReal (hF : ContDiff ℝ 2 F) (p : ℕ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (q : d.Idx N × d.Idx N × Bool) :
    (((coordD2 d N (momentFun F p) M q).re : ℝ) : ℂ) = coordD2 d N (momentFun F p) M q := by
  rw [coordD2_momentFun_ofReal hF p M q]
  simp only [Complex.ofReal_re]

/-- **`𝓛F := ½ ∑_α S_α ∂_α² F`**, the generator of the moment route applied to `F` itself.
(For `Φ = |F|^{2p}` the generator identity gives `d/du E[Φ(H_u)] = E[(𝓛Φ)(H_u)]`; the first
term of the expansion below is the one built out of `𝓛F`.) -/
noncomputable def genD (d : Dims) (N : ℕ) (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  (2⁻¹ : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) • coordD2 d N F M q

/-- **`𝓛(|F|^{2p})`**, as a real number. -/
noncomputable def genMomentPt (d : Dims) (N : ℕ) (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (p : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  (2⁻¹ : ℝ) * ∑ q ∈ usedCoord d N,
    (gvar d (crd d N q) : ℝ) * (coordD2 d N (momentFun F p) M q).re

theorem ofReal_genMomentPt (hF : ContDiff ℝ 2 F) (p : ℕ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ((genMomentPt d N F p M : ℝ) : ℂ)
      = (2⁻¹ : ℝ) • ∑ q ∈ usedCoord d N,
          (gvar d (crd d N q) : ℝ) • coordD2 d N (momentFun F p) M q := by
  simp only [genMomentPt, Complex.ofReal_mul, Complex.ofReal_sum, Complex.real_smul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coordD2_momentFun_re_ofReal hF p M q]

/-- `∑_α S_α Re(F̄ ∂_α²F) = 2 Re(F̄ 𝓛F)`. -/
theorem sum_gvar_re_coordD2 (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ q ∈ usedCoord d N,
        (gvar d (crd d N q) : ℝ) * ((starRingEnd ℂ) (F M) * coordD2 d N F M q).re
      = 2 * ((starRingEnd ℂ) (F M) * genD d N F M).re := by
  have h1 : (starRingEnd ℂ) (F M) * genD d N F M
      = (2⁻¹ : ℝ) • ∑ q ∈ usedCoord d N,
          (gvar d (crd d N q) : ℝ) • ((starRingEnd ℂ) (F M) * coordD2 d N F M q) := by
    simp only [genD, mul_smul_comm, Finset.mul_sum]
  rw [h1]
  simp only [Complex.smul_re, Complex.re_sum, smul_eq_mul]
  ring

/-- **The Grönwall-ready bound.**

`𝓛(|F|^{2p}) ≤ 2p ‖F‖^{2p-1} ‖𝓛F‖ + p(2p-1) ‖F‖^{2p-2} · ∑_α S_α‖∂_αF‖²`.

The two constants are exactly the ones of the ticket; the second one, `p(2p-1)`, comes from
`2p(p-1) + p`, the `2p(p-1)` being the price of bounding `Re(F̄ ∂_αF)²` by `‖F‖²‖∂_αF‖²`.
By `secondOrder_eq_quadVar` the factor multiplying `p(2p-1)‖F‖^{2p-2}` is the quadratic
variation of (5.25). -/
theorem genMomentPt_le (hF : ContDiff ℝ 2 F) {p : ℕ} (hp : 1 ≤ p)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    genMomentPt d N F p M
      ≤ 2 * p * ‖F M‖ ^ (2 * p - 1) * ‖genD d N F M‖
        + p * (2 * p - 1) * ‖F M‖ ^ (2 * p - 2) * quadVar d N F M := by
  set a : ℝ := ‖F M‖ ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  -- the pointwise bound `(p-1) a^{p-2} Re(F̄ ∂F)² ≤ (p-1) a^{p-1} ‖∂F‖²`
  have hkey : ∀ q : d.Idx N × d.Idx N × Bool,
      (((p - 1 : ℕ)) : ℝ) * a ^ (p - 2) * ((starRingEnd ℂ) (F M) * coordD1 d N F M q).re ^ 2
        ≤ (((p - 1 : ℕ)) : ℝ) * a ^ (p - 1) * ‖coordD1 d N F M q‖ ^ 2 := by
    intro q
    rcases Nat.lt_or_ge p 2 with hlt | hge
    · have : p - 1 = 0 := by omega
      rw [this]
      simp
    · have hsq : ((starRingEnd ℂ) (F M) * coordD1 d N F M q).re ^ 2
          ≤ a * ‖coordD1 d N F M q‖ ^ 2 := by
        have h1 : |((starRingEnd ℂ) (F M) * coordD1 d N F M q).re|
            ≤ ‖(starRingEnd ℂ) (F M) * coordD1 d N F M q‖ :=
          Complex.abs_re_le_norm _
        have h2 : ‖(starRingEnd ℂ) (F M) * coordD1 d N F M q‖ = ‖F M‖ * ‖coordD1 d N F M q‖ := by
          rw [norm_mul, RCLike.norm_conj]
        rw [h2] at h1
        have h3 : ((starRingEnd ℂ) (F M) * coordD1 d N F M q).re ^ 2
            ≤ (‖F M‖ * ‖coordD1 d N F M q‖) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        calc ((starRingEnd ℂ) (F M) * coordD1 d N F M q).re ^ 2
            ≤ (‖F M‖ * ‖coordD1 d N F M q‖) ^ 2 := h3
          _ = a * ‖coordD1 d N F M q‖ ^ 2 := by rw [ha]; ring
      have hpow : a ^ (p - 2) * a = a ^ (p - 1) := by
        rw [← pow_succ]
        congr 1
        omega
      have hc : (0 : ℝ) ≤ (((p - 1 : ℕ)) : ℝ) * a ^ (p - 2) := by positivity
      calc (((p - 1 : ℕ)) : ℝ) * a ^ (p - 2)
              * ((starRingEnd ℂ) (F M) * coordD1 d N F M q).re ^ 2
          ≤ (((p - 1 : ℕ)) : ℝ) * a ^ (p - 2) * (a * ‖coordD1 d N F M q‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsq hc
        _ = (((p - 1 : ℕ)) : ℝ) * a ^ (p - 1) * ‖coordD1 d N F M q‖ ^ 2 := by
            rw [← hpow]; ring
  -- step 1: replace `a^{p-2} Re(F̄ ∂F)²` by `a^{p-1} ‖∂F‖²` inside the sum
  have hstep : genMomentPt d N F p M
      ≤ (2⁻¹ : ℝ) * ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) *
          ((p : ℝ) * ((((p - 1 : ℕ)) : ℝ) * a ^ (p - 1)
              * (4 * ‖coordD1 d N F M q‖ ^ 2)
            + a ^ (p - 1) * (2 * ‖coordD1 d N F M q‖ ^ 2
              + 2 * ((starRingEnd ℂ) (F M) * coordD2 d N F M q).re))) := by
    rw [genMomentPt]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => ?_) (by norm_num)
    refine mul_le_mul_of_nonneg_left ?_ (gvar d (crd d N q)).2
    rw [coordD2_momentFun_ofReal hF p M q, Complex.ofReal_re, ← ha]
    have h4 := hkey q
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    nlinarith [h4, hp0]
  refine le_trans hstep ?_
  -- step 2: evaluate the resulting sum
  have hsum : ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) *
      ((p : ℝ) * ((((p - 1 : ℕ)) : ℝ) * a ^ (p - 1) * (4 * ‖coordD1 d N F M q‖ ^ 2)
        + a ^ (p - 1) * (2 * ‖coordD1 d N F M q‖ ^ 2
          + 2 * ((starRingEnd ℂ) (F M) * coordD2 d N F M q).re)))
      = (p : ℝ) * a ^ (p - 1) * (4 * (((p - 1 : ℕ)) : ℝ) + 2) * quadVar d N F M
        + (p : ℝ) * a ^ (p - 1) * 2 * (2 * ((starRingEnd ℂ) (F M) * genD d N F M).re) := by
    rw [← sum_gvar_re_coordD2 (F := F) M]
    simp only [quadVar, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hsum]
  -- step 3: `Re(F̄ 𝓛F) ≤ ‖F‖ ‖𝓛F‖` and the exponent bookkeeping
  have hre : ((starRingEnd ℂ) (F M) * genD d N F M).re ≤ ‖F M‖ * ‖genD d N F M‖ := by
    calc ((starRingEnd ℂ) (F M) * genD d N F M).re
        ≤ |((starRingEnd ℂ) (F M) * genD d N F M).re| := le_abs_self _
      _ ≤ ‖(starRingEnd ℂ) (F M) * genD d N F M‖ := Complex.abs_re_le_norm _
      _ = ‖F M‖ * ‖genD d N F M‖ := by rw [norm_mul, RCLike.norm_conj]
  have hp1 : a ^ (p - 1) = ‖F M‖ ^ (2 * p - 2) := by
    rw [ha, ← pow_mul]
    congr 1
    omega
  have hp2 : a ^ (p - 1) * ‖F M‖ = ‖F M‖ ^ (2 * p - 1) := by
    rw [ha, ← pow_mul, ← pow_succ]
    congr 1
    omega
  have hcast : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp, Nat.cast_one]
  have hQ : 0 ≤ quadVar d N F M := quadVar_nonneg F M
  have hap : 0 ≤ a ^ (p - 1) := by positivity
  have hkey2 : (p : ℝ) * a ^ (p - 1) * 2 * (2 * ((starRingEnd ℂ) (F M) * genD d N F M).re)
      ≤ 4 * (p : ℝ) * ‖F M‖ ^ (2 * p - 1) * ‖genD d N F M‖ := by
    have h4 : (0 : ℝ) ≤ 4 * (p : ℝ) * a ^ (p - 1) := by positivity
    calc (p : ℝ) * a ^ (p - 1) * 2 * (2 * ((starRingEnd ℂ) (F M) * genD d N F M).re)
        = 4 * (p : ℝ) * a ^ (p - 1) * ((starRingEnd ℂ) (F M) * genD d N F M).re := by ring
      _ ≤ 4 * (p : ℝ) * a ^ (p - 1) * (‖F M‖ * ‖genD d N F M‖) :=
          mul_le_mul_of_nonneg_left hre h4
      _ = 4 * (p : ℝ) * ‖F M‖ ^ (2 * p - 1) * ‖genD d N F M‖ := by rw [← hp2]; ring
  have hkey3 : (p : ℝ) * a ^ (p - 1) * (4 * (((p - 1 : ℕ)) : ℝ) + 2) * quadVar d N F M
      = 2 * ((p : ℝ) * (2 * p - 1) * ‖F M‖ ^ (2 * p - 2) * quadVar d N F M) := by
    rw [hcast, hp1]
    ring
  linarith [hkey2, hkey3]

/-! #### Numerical self-checks of the constants

The expansions above are *derived* (`HasDerivAt.unique`), so they cannot be mis-transcribed;
these two lines check instead that the constants `4`, `2` and `p(2p-1)` fit together, on the
scalar model `F = id`, where `∂F = 1`, `∂²F = 0` and `|F|^{2p} = x^{2p}` has second derivative
`2p(2p-1)x^{2p-2}`. -/

example : ((3 : ℝ) * (((3 - 1 : ℕ) : ℝ) * (((2 : ℝ) ^ 2) ^ (3 - 2)) * (4 * (2 : ℝ) ^ 2)
      + (((2 : ℝ) ^ 2) ^ (3 - 1)) * 2))
    = 2 * 3 * (2 * 3 - 1) * (2 : ℝ) ^ (2 * 3 - 2) := by norm_num

example : ((1 : ℝ) * (((1 - 1 : ℕ) : ℝ) * (((5 : ℝ) ^ 2) ^ (1 - 2)) * (4 * (5 : ℝ) ^ 2)
      + (((5 : ℝ) ^ 2) ^ (1 - 1)) * 2))
    = 2 * 1 * (2 * 1 - 1) * (5 : ℝ) ^ (2 * 1 - 2) := by norm_num

/-- **`genMomentPt_le` with the paper's quadratic variation on the right.**  This is
`genMomentPt_le` rewritten through the fulcrum `secondOrder_eq_quadVar`: the coefficient of
`p(2p-1)‖F‖^{2p-2}` in the derivative of the `2p`-th moment is `∑_α |E^{(M)}(α)|²`, the
integrand of (5.25). -/
theorem genMomentPt_le_quadVarPairs (hF : ContDiff ℝ 2 F) {p : ℕ} (hp : 1 ≤ p)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    genMomentPt d N F p M
      ≤ 2 * p * ‖F M‖ ^ (2 * p - 1) * ‖genD d N F M‖
        + p * (2 * p - 1) * ‖F M‖ ^ (2 * p - 2) * quadVarPairs d N F M := by
  rw [← secondOrder_eq_quadVar F M]
  exact genMomentPt_le hF hp M

end MomentSecondOrder

/-! ### The moment derivative -/

section MomentGenerator

variable {d : Dims} {N : ℕ} {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {p : ℕ}

/-- `E|F(H_u)|^{2p}`, the quantity the moment route runs Grönwall on. -/
noncomputable def momentIntegral (d : Dims) (N : ℕ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (p : ℕ) (u : ℝ) : ℝ :=
  ∫ ω, ‖F (Hflow d N u ω)‖ ^ (2 * p) ∂(P d)

theorem integrable_genMomentPt (h : TestFun d N (momentFun F p))
    (u : ℝ) : Integrable (fun ω => genMomentPt d N F p (Hflow d N u ω)) (P d) := by
  refine Integrable.const_mul (integrable_finsetSum _ fun q _ => ?_) _
  exact ((integrable_coordD2 h u q).re).const_mul _

/-- **The generator identity for `Φ = |F|^{2p}`.**

`d/du E|F(H_u)|^{2p} = E[𝓛(|F|^{2p})(H_u)]`, a real-valued statement. -/
theorem hasDerivAt_momentIntegral (hst : MatrixStein d) (hF : ContDiff ℝ 2 F)
    (h : TestFun d N (momentFun F p)) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (momentIntegral d N F p)
      (∫ ω, genMomentPt d N F p (Hflow d N u ω) ∂(P d)) u := by
  have hgen := hasDerivAt_integral_Phi hst h hu
  have hA : (fun s : ℝ => ∫ ω, momentFun F p (Hflow d N s ω) ∂(P d))
      = fun s : ℝ => ((momentIntegral d N F p s : ℝ) : ℂ) := by
    funext s
    simp only [momentFun_eq, momentIntegral]
    exact integral_complex_ofReal
  have hB : ((∫ ω, genMomentPt d N F p (Hflow d N u ω) ∂(P d) : ℝ) : ℂ)
      = (1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
          ∫ ω, coordD2 d N (momentFun F p) (Hflow d N u ω) q ∂(P d) := by
    rw [← integral_complex_ofReal]
    have hpt : (fun ω => ((genMomentPt d N F p (Hflow d N u ω) : ℝ) : ℂ))
        = fun ω => (2⁻¹ : ℝ) • ∑ q ∈ usedCoord d N,
            (gvar d (crd d N q) : ℝ) • coordD2 d N (momentFun F p) (Hflow d N u ω) q :=
      funext fun ω => ofReal_genMomentPt hF p _
    have hint : ∀ q ∈ usedCoord d N, Integrable
        (fun ω : Ω d => (gvar d (crd d N q) : ℝ)
          • coordD2 d N (momentFun F p) (Hflow d N u ω) q) (P d) := by
      intro q _
      exact (integrable_coordD2 h u q).smul ((gvar d (crd d N q) : ℝ))
    rw [hpt, integral_smul, integral_finsetSum _ hint]
    simp only [integral_smul, one_div]
  rw [hA, ← hB] at hgen
  have hre := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt u hgen
  simpa [Function.comp_def] using hre

/-- **The derivative bound, integrated.**  Combining `genMomentPt_le` with `integral_mono`. -/
theorem integral_genMomentPt_le (hF : ContDiff ℝ 2 F)
    (h : TestFun d N (momentFun F p)) (hp : 1 ≤ p) {u : ℝ}
    {G : Ω d → ℝ} (hG : Integrable G (P d))
    (hGle : ∀ ω, 2 * p * ‖F (Hflow d N u ω)‖ ^ (2 * p - 1) * ‖genD d N F (Hflow d N u ω)‖
        + p * (2 * p - 1) * ‖F (Hflow d N u ω)‖ ^ (2 * p - 2)
          * quadVar d N F (Hflow d N u ω) ≤ G ω) :
    ∫ ω, genMomentPt d N F p (Hflow d N u ω) ∂(P d) ≤ ∫ ω, G ω ∂(P d) :=
  integral_mono (integrable_genMomentPt h u) hG fun ω =>
    le_trans (genMomentPt_le hF hp _) (hGle ω)

end MomentGenerator

/-! ### Grönwall -/

section Gronwall

/-- **Grönwall for a real function with a one-sided derivative bound.**  From
`φ' ≤ K φ + ε` on `[a, b)` and `φ a ≤ δ` we get `φ x ≤ gronwallBound δ K ε (x - a)` on
`[a, b]`.  (Mathlib's `le_gronwallBound_of_liminf_deriv_right_le` is stated with a `liminf`
of slopes; `HasDerivWithinAt.liminf_right_slope_le` supplies it.) -/
theorem le_gronwallBound_of_hasDerivWithinAt_le {φ φ' : ℝ → ℝ} {δ K ε a b : ℝ}
    (hcont : ContinuousOn φ (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt φ (φ' x) (Set.Ici x) x)
    (hδ : φ a ≤ δ) (hbound : ∀ x ∈ Set.Ico a b, φ' x ≤ K * φ x + ε) :
    ∀ x ∈ Set.Icc a b, φ x ≤ gronwallBound δ K ε (x - a) := by
  refine le_gronwallBound_of_liminf_deriv_right_le hcont (fun x hx r hr => ?_) hδ hbound
  have := (hderiv x hx).liminf_right_slope_le hr
  simpa [slope_def_field, div_eq_inv_mul] using this

variable {d : Dims} {N : ℕ} {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {p : ℕ}

/-- **The moment route's Grönwall step.**

If on `[a, b)` (with `a > 0`) the second-order term of the generator identity is bounded by
`K · E|F|^{2p} + ε`, then `E|F(H_u)|^{2p} ≤ gronwallBound δ K ε (u - a)` on `[a, b]`.  With
`ε = 0` this is `δ e^{K(u-a)}` (`gronwallBound_ε0`). -/
theorem momentIntegral_le_gronwallBound (hst : MatrixStein d) (hF : ContDiff ℝ 2 F)
    (h : TestFun d N (momentFun F p)) {a b δ K ε : ℝ} (ha : 0 < a)
    (hδ : momentIntegral d N F p a ≤ δ)
    (hbd : ∀ u ∈ Set.Ico a b, (∫ ω, genMomentPt d N F p (Hflow d N u ω) ∂(P d))
        ≤ K * momentIntegral d N F p u + ε) :
    ∀ u ∈ Set.Icc a b, momentIntegral d N F p u ≤ gronwallBound δ K ε (u - a) := by
  have hd : ∀ u : ℝ, a ≤ u → HasDerivAt (momentIntegral d N F p)
      (∫ ω, genMomentPt d N F p (Hflow d N u ω) ∂(P d)) u := fun u hu =>
    hasDerivAt_momentIntegral hst hF h (lt_of_lt_of_le ha hu)
  refine le_gronwallBound_of_hasDerivWithinAt_le
    (φ' := fun u => ∫ ω, genMomentPt d N F p (Hflow d N u ω) ∂(P d))
    (fun u hu => ((hd u hu.1).continuousAt).continuousWithinAt)
    (fun u hu => (hd u hu.1).hasDerivWithinAt) hδ hbd

end Gronwall

/-! ### Building a `TestFun` for `Φ = |F|^{2p}` -/

section TestFunBuild

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **What `TestFun` asks of the inner function `F`**: `C²` with globally bounded value, first
and second derivative.  This is `RBM.Gauss.TestFun` transported to `F`; the point of the
section is that it is *inherited* by `|F|^{2p}` (`TestFun.of_bddC2`), and that the resolvent
observables of the moment route satisfy it (`bddC2_greenObs`), thanks to the global bound
`‖G‖ ≤ η⁻¹` of T71. -/
structure BddC2 (F : E → ℂ) : Prop where
  /-- `F` is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 F
  /-- `F` is globally bounded. -/
  bdd₀ : ∃ C : ℝ, ∀ M, ‖F M‖ ≤ C
  /-- `DF` is globally bounded. -/
  bdd₁ : ∃ C : ℝ, ∀ M, ‖fderiv ℝ F M‖ ≤ C
  /-- `D²F` is globally bounded. -/
  bdd₂ : ∃ C : ℝ, ∀ M, ‖fderiv ℝ (fderiv ℝ F) M‖ ≤ C

/-- `BddC2` is inherited by `|F|^{2p}`. -/
theorem bddC2_momentFun {F : E → ℂ} (h : BddC2 F) (p : ℕ) : BddC2 (momentFun F p) := by
  obtain ⟨hcd, ⟨C0, hC0⟩, ⟨C1, hC1⟩, ⟨C2, hC2⟩⟩ := h
  have hC0' : (0 : ℝ) ≤ C0 := le_trans (norm_nonneg (F 0)) (hC0 0)
  have hC1' : (0 : ℝ) ≤ C1 := le_trans (norm_nonneg (fderiv ℝ F 0)) (hC1 0)
  have hC2' : (0 : ℝ) ≤ C2 := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ F) 0)) (hC2 0)
  have hF1 : ContDiff ℝ 1 F := hcd.of_le (by norm_num)
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hp1 : (0 : ℝ) ≤ (((p - 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
  -- `‖R^k‖ ≤ (C0²)^k`
  have hnormR : ∀ (M : E) (k : ℕ), ‖(F M * (starRingEnd ℂ) (F M)) ^ k‖ ≤ (C0 ^ 2) ^ k := by
    intro M k
    rw [norm_pow, mul_conj_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖F M‖ ^ 2)]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [hC0 M, norm_nonneg (F M)]) k
  have hnormDF : ∀ (M A : E), ‖fderiv ℝ F M A‖ ≤ C1 * ‖A‖ := fun M A =>
    le_trans ((fderiv ℝ F M).le_opNorm A) (mul_le_mul_of_nonneg_right (hC1 M) (norm_nonneg _))
  have hnormD2F : ∀ (M A B : E), ‖fderiv ℝ (fderiv ℝ F) M B A‖ ≤ C2 * ‖B‖ * ‖A‖ := by
    intro M A B
    refine le_trans ((fderiv ℝ (fderiv ℝ F) M B).le_opNorm A) ?_
    exact mul_le_mul_of_nonneg_right
      (le_trans ((fderiv ℝ (fderiv ℝ F) M).le_opNorm B)
        (mul_le_mul_of_nonneg_right (hC2 M) (norm_nonneg _))) (norm_nonneg _)
  -- `‖R'_A‖ ≤ 2 C0 C1 ‖A‖`
  have hnormS : ∀ (M A : E), ‖fderiv ℝ F M A * (starRingEnd ℂ) (F M)
      + F M * (starRingEnd ℂ) (fderiv ℝ F M A)‖ ≤ 2 * C0 * C1 * ‖A‖ := by
    intro M A
    have h1 : ‖fderiv ℝ F M A * (starRingEnd ℂ) (F M)‖ = ‖fderiv ℝ F M A‖ * ‖F M‖ := by
      rw [norm_mul, RCLike.norm_conj]
    have h2 : ‖F M * (starRingEnd ℂ) (fderiv ℝ F M A)‖ = ‖F M‖ * ‖fderiv ℝ F M A‖ := by
      rw [norm_mul, RCLike.norm_conj]
    calc ‖fderiv ℝ F M A * (starRingEnd ℂ) (F M)
            + F M * (starRingEnd ℂ) (fderiv ℝ F M A)‖
        ≤ ‖fderiv ℝ F M A * (starRingEnd ℂ) (F M)‖
            + ‖F M * (starRingEnd ℂ) (fderiv ℝ F M A)‖ := norm_add_le _ _
      _ = 2 * (‖F M‖ * ‖fderiv ℝ F M A‖) := by rw [h1, h2]; ring
      _ ≤ 2 * (C0 * (C1 * ‖A‖)) := by
          have := mul_le_mul (hC0 M) (hnormDF M A) (norm_nonneg _) hC0'
          linarith
      _ = 2 * C0 * C1 * ‖A‖ := by ring
  refine ⟨contDiff_momentFun hcd p, ⟨C0 ^ (2 * p), fun M => ?_⟩,
    ⟨(p : ℝ) * (C0 ^ 2) ^ (p - 1) * (2 * C0 * C1), fun M => ?_⟩,
    ⟨(p : ℝ) * ((((p - 1 : ℕ)) : ℝ) * (C0 ^ 2) ^ (p - 2) * ((2 * C0 * C1) * (2 * C0 * C1))
      + (C0 ^ 2) ^ (p - 1) * (2 * (C0 * C2) + 2 * (C1 * C1))), fun M => ?_⟩⟩
  · rw [momentFun_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖F M‖ ^ (2 * p))]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC0 M) _
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
    rw [fderiv_momentFun hF1 p M A]
    calc ‖(p : ℂ) * (F M * (starRingEnd ℂ) (F M)) ^ (p - 1)
            * (fderiv ℝ F M A * (starRingEnd ℂ) (F M)
              + F M * (starRingEnd ℂ) (fderiv ℝ F M A))‖
        = (p : ℝ) * ‖(F M * (starRingEnd ℂ) (F M)) ^ (p - 1)‖
            * ‖fderiv ℝ F M A * (starRingEnd ℂ) (F M)
              + F M * (starRingEnd ℂ) (fderiv ℝ F M A)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_natCast]
      _ ≤ (p : ℝ) * (C0 ^ 2) ^ (p - 1) * (2 * C0 * C1 * ‖A‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hnormR M (p - 1)) hp0) (hnormS M A)
            (norm_nonneg _) (by positivity)
      _ = (p : ℝ) * (C0 ^ 2) ^ (p - 1) * (2 * C0 * C1) * ‖A‖ := by ring
  · have hcst : (0 : ℝ) ≤ (p : ℝ) * ((((p - 1 : ℕ)) : ℝ) * (C0 ^ 2) ^ (p - 2)
        * ((2 * C0 * C1) * (2 * C0 * C1)) + (C0 ^ 2) ^ (p - 1)
          * (2 * (C0 * C2) + 2 * (C1 * C1))) := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hcst fun B => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
    rw [fderiv2_momentFun' hcd p M A B]
    -- the two summands
    have hX : ‖(((p - 1 : ℕ)) : ℂ) * (F M * (starRingEnd ℂ) (F M)) ^ (p - 2)
        * ((fderiv ℝ F M A * (starRingEnd ℂ) (F M)
            + F M * (starRingEnd ℂ) (fderiv ℝ F M A))
          * (fderiv ℝ F M B * (starRingEnd ℂ) (F M)
            + F M * (starRingEnd ℂ) (fderiv ℝ F M B)))‖
        ≤ (((p - 1 : ℕ)) : ℝ) * (C0 ^ 2) ^ (p - 2)
            * ((2 * C0 * C1 * ‖A‖) * (2 * C0 * C1 * ‖B‖)) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
      refine mul_le_mul (mul_le_mul_of_nonneg_left (hnormR M (p - 2)) hp1)
        (mul_le_mul (hnormS M A) (hnormS M B) (norm_nonneg _) (by positivity))
        (by positivity) (by positivity)
    have hT : ‖fderiv ℝ (fderiv ℝ F) M B A * (starRingEnd ℂ) (F M)
          + fderiv ℝ F M A * (starRingEnd ℂ) (fderiv ℝ F M B)
          + fderiv ℝ F M B * (starRingEnd ℂ) (fderiv ℝ F M A)
          + F M * (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ F) M B A)‖
        ≤ (2 * (C0 * C2) + 2 * (C1 * C1)) * (‖B‖ * ‖A‖) := by
      have e1 : ‖fderiv ℝ (fderiv ℝ F) M B A * (starRingEnd ℂ) (F M)‖
          ≤ (C2 * ‖B‖ * ‖A‖) * C0 := by
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (hnormD2F M A B) (hC0 M) (norm_nonneg _) (by positivity)
      have e2 : ‖fderiv ℝ F M A * (starRingEnd ℂ) (fderiv ℝ F M B)‖
          ≤ (C1 * ‖A‖) * (C1 * ‖B‖) := by
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (hnormDF M A) (hnormDF M B) (norm_nonneg _) (by positivity)
      have e3 : ‖fderiv ℝ F M B * (starRingEnd ℂ) (fderiv ℝ F M A)‖
          ≤ (C1 * ‖B‖) * (C1 * ‖A‖) := by
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (hnormDF M B) (hnormDF M A) (norm_nonneg _) (by positivity)
      have e4 : ‖F M * (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ F) M B A)‖
          ≤ C0 * (C2 * ‖B‖ * ‖A‖) := by
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (hC0 M) (hnormD2F M A B) (norm_nonneg _) hC0'
      calc ‖fderiv ℝ (fderiv ℝ F) M B A * (starRingEnd ℂ) (F M)
              + fderiv ℝ F M A * (starRingEnd ℂ) (fderiv ℝ F M B)
              + fderiv ℝ F M B * (starRingEnd ℂ) (fderiv ℝ F M A)
              + F M * (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ F) M B A)‖
          ≤ ‖fderiv ℝ (fderiv ℝ F) M B A * (starRingEnd ℂ) (F M)
              + fderiv ℝ F M A * (starRingEnd ℂ) (fderiv ℝ F M B)
              + fderiv ℝ F M B * (starRingEnd ℂ) (fderiv ℝ F M A)‖
            + ‖F M * (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ F) M B A)‖ := norm_add_le _ _
        _ ≤ (‖fderiv ℝ (fderiv ℝ F) M B A * (starRingEnd ℂ) (F M)
              + fderiv ℝ F M A * (starRingEnd ℂ) (fderiv ℝ F M B)‖
            + ‖fderiv ℝ F M B * (starRingEnd ℂ) (fderiv ℝ F M A)‖)
            + ‖F M * (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ F) M B A)‖ := by
              gcongr; exact norm_add_le _ _
        _ ≤ ((‖fderiv ℝ (fderiv ℝ F) M B A * (starRingEnd ℂ) (F M)‖
              + ‖fderiv ℝ F M A * (starRingEnd ℂ) (fderiv ℝ F M B)‖)
            + ‖fderiv ℝ F M B * (starRingEnd ℂ) (fderiv ℝ F M A)‖)
            + ‖F M * (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ F) M B A)‖ := by
              gcongr; exact norm_add_le _ _
        _ ≤ (((C2 * ‖B‖ * ‖A‖) * C0 + (C1 * ‖A‖) * (C1 * ‖B‖)) + (C1 * ‖B‖) * (C1 * ‖A‖))
            + C0 * (C2 * ‖B‖ * ‖A‖) := by gcongr
        _ = (2 * (C0 * C2) + 2 * (C1 * C1)) * (‖B‖ * ‖A‖) := by ring
    have hY : ‖(F M * (starRingEnd ℂ) (F M)) ^ (p - 1)
        * (fderiv ℝ (fderiv ℝ F) M B A * (starRingEnd ℂ) (F M)
          + fderiv ℝ F M A * (starRingEnd ℂ) (fderiv ℝ F M B)
          + fderiv ℝ F M B * (starRingEnd ℂ) (fderiv ℝ F M A)
          + F M * (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ F) M B A))‖
        ≤ (C0 ^ 2) ^ (p - 1) * ((2 * (C0 * C2) + 2 * (C1 * C1)) * (‖B‖ * ‖A‖)) := by
      rw [norm_mul]
      exact mul_le_mul (hnormR M (p - 1)) hT (norm_nonneg _) (by positivity)
    rw [norm_mul, Complex.norm_natCast]
    refine le_trans (mul_le_mul_of_nonneg_left (le_trans (norm_add_le _ _)
      (add_le_add hX hY)) hp0) ?_
    have hAB : ‖A‖ * ‖B‖ = ‖B‖ * ‖A‖ := mul_comm _ _
    nlinarith [hp0, norm_nonneg A, norm_nonneg B,
      mul_nonneg (mul_nonneg hp1 (by positivity : (0:ℝ) ≤ (C0 ^ 2) ^ (p - 2)))
        (by positivity : (0:ℝ) ≤ (2 * C0 * C1) * (2 * C0 * C1))]

/-- The `TestFun` of `RBM1D/Gauss/Generator.lean` for `Φ = |F|^{2p}`. -/
theorem TestFun.of_bddC2 {d : Dims} {N : ℕ} {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (h : BddC2 F) (p : ℕ) : TestFun d N (momentFun F p) :=
  let h' := bddC2_momentFun h p
  ⟨h'.contDiff, h'.bdd₀, h'.bdd₁, h'.bdd₂⟩

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

/-- **The observable**: a fixed continuous `ℝ`-linear functional of the resolvent, e.g. an
entry `G_ij` or an average `⟨G E_a⟩`.  This is the `F` of the moment route at loop length one;
`φ` is deterministic, so composing with the deterministic linear operator `U_{u,t,σ}` of
(5.25) stays inside this class. -/
noncomputable def greenObs (z : ℂ) (φ : Matrix n n ℂ →L[ℝ] ℂ) : Matrix n n ℂ → ℂ :=
  fun M => φ (resH z M)

theorem fderiv_greenObs {z : ℂ} (hz : z.im ≠ 0) (φ : Matrix n n ℂ →L[ℝ] ℂ)
    (M : Matrix n n ℂ) : fderiv ℝ (greenObs z φ) M = φ.comp (fderiv ℝ (resH z) M) :=
  (φ.hasFDerivAt.comp M (hasFDerivAt_resH hz M)).fderiv.trans (by
    rw [(hasFDerivAt_resH hz M).fderiv])

theorem fderiv2_greenObs_apply {z : ℂ} (hz : z.im ≠ 0) (φ : Matrix n n ℂ →L[ℝ] ℂ)
    (M A B : Matrix n n ℂ) :
    fderiv ℝ (fderiv ℝ (greenObs z φ)) M B A = φ (fderiv ℝ (fderiv ℝ (resH z)) M B A) := by
  have hcd : ContDiff ℝ 2 (greenObs (n := n) z φ) := φ.contDiff.comp (contDiff_resH hz)
  have hlhs : HasDerivAt (fun t : ℝ => fderiv ℝ (greenObs z φ) (M + t • B) A)
      (fderiv ℝ (fderiv ℝ (greenObs z φ)) M B A) 0 := hasDerivAt_dir2' hcd M A B
  have hinner : HasDerivAt (fun t : ℝ => fderiv ℝ (resH z) (M + t • B) A)
      (fderiv ℝ (fderiv ℝ (resH z)) M B A) 0 := hasDerivAt_dir2' (contDiff_resH hz) M A B
  have hfun : (fun t : ℝ => fderiv ℝ (greenObs z φ) (M + t • B) A)
      = fun t : ℝ => φ (fderiv ℝ (resH z) (M + t • B) A) := by
    funext t
    rw [fderiv_greenObs hz φ (M + t • B)]
    rfl
  rw [hfun] at hlhs
  have hrhs := (φ.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hinner
  exact hlhs.unique (by simpa [Function.comp_def] using hrhs)

/-- **`BddC2` for the resolvent observables**: everything `TestFun.of_bddC2` needs, with the
constants `‖φ‖η⁻¹`, `‖φ‖η⁻²`, `2‖φ‖η⁻³` — global, by `norm_green_le`. -/
theorem bddC2_greenObs {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    (φ : Matrix n n ℂ →L[ℝ] ℂ) : BddC2 (greenObs (n := n) z φ) := by
  refine ⟨φ.contDiff.comp (contDiff_resH hz), ⟨‖φ‖ * η⁻¹, fun M => ?_⟩,
    ⟨‖φ‖ * (η⁻¹ * η⁻¹), fun M => ?_⟩, ⟨‖φ‖ * (2 * (η⁻¹ * η⁻¹ * η⁻¹)), fun M => ?_⟩⟩
  · exact le_trans (φ.le_opNorm _)
      (mul_le_mul_of_nonneg_left (norm_resH_le hη hzη M) (norm_nonneg _))
  · rw [fderiv_greenObs hz φ M]
    exact le_trans (φ.opNorm_comp_le _)
      (mul_le_mul_of_nonneg_left (norm_fderiv_resH_le hz hη hzη M) (norm_nonneg _))
  · have h0 : (0 : ℝ) ≤ η⁻¹ := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun B => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
    rw [fderiv2_greenObs_apply hz φ M A B]
    have h1 : ‖fderiv ℝ (fderiv ℝ (resH z)) M B A‖
        ≤ 2 * (η⁻¹ * η⁻¹ * η⁻¹) * ‖B‖ * ‖A‖ := by
      refine le_trans ((fderiv ℝ (fderiv ℝ (resH z)) M B).le_opNorm A) ?_
      exact mul_le_mul_of_nonneg_right
        (le_trans ((fderiv ℝ (fderiv ℝ (resH z)) M).le_opNorm B)
          (mul_le_mul_of_nonneg_right (norm_fderiv2_resH_le hz hη hzη M) (norm_nonneg _)))
        (norm_nonneg _)
    calc ‖φ (fderiv ℝ (fderiv ℝ (resH z)) M B A)‖
        ≤ ‖φ‖ * ‖fderiv ℝ (fderiv ℝ (resH z)) M B A‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ * (2 * (η⁻¹ * η⁻¹ * η⁻¹) * ‖B‖ * ‖A‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖φ‖ * (2 * (η⁻¹ * η⁻¹ * η⁻¹)) * ‖B‖ * ‖A‖ := by ring

/-- **The `TestFun` instance the ticket asks for**: `Φ = |φ(G_z)|^{2p}` with `G_z` the
resolvent pre-composed with the Hermitian projection.  This is what feeds the generator
identity of T71 and `hasDerivAt_momentIntegral`. -/
theorem testFun_momentFun_greenObs {d : Dims} {N : ℕ} {z : ℂ} {η : ℝ} (hz : z.im ≠ 0)
    (hη : 0 < η) (hzη : η ≤ |z.im|) (φ : Matrix (d.Idx N) (d.Idx N) ℂ →L[ℝ] ℂ) (p : ℕ) :
    TestFun d N (momentFun (greenObs z φ) p) :=
  TestFun.of_bddC2 (bddC2_greenObs hz hη hzη φ) p


/-- **End-to-end**: for the concrete `F = φ(G_z)`, the moment `u ↦ E|F(H_u)|^{2p}` is
differentiable at every `u > 0`, with derivative `E[𝓛(|F|^{2p})(H_u)]`.  Every hypothesis of
`hasDerivAt_momentIntegral` is discharged here except `MatrixStein` (T70's). -/
theorem hasDerivAt_momentIntegral_greenObs {d : Dims} {N : ℕ} {z : ℂ} {η : ℝ}
    (hst : MatrixStein d) (hz : z.im ≠ 0) (hη : 0 < η) (hzη : η ≤ |z.im|)
    (φ : Matrix (d.Idx N) (d.Idx N) ℂ →L[ℝ] ℂ) (p : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (momentIntegral d N (greenObs z φ) p)
      (∫ ω, genMomentPt d N (greenObs z φ) p (Hflow d N u ω) ∂(P d)) u :=
  hasDerivAt_momentIntegral hst (bddC2_greenObs hz hη hzη φ).contDiff
    (testFun_momentFun_greenObs hz hη hzη φ p) hu

end ResolventC2

end RBM.Gauss

