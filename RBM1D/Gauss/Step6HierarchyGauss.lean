/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step6
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Hierarchy.DriftDef

/-!
# T152: the Step 6 hierarchy (5.129)–(5.131) from a pointwise drift identity

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8.  `RBM.Step6.sharpExpect_step6` (T56) has four hypotheses that quantify over
the two drift tensors and had no producer anywhere in the tree: `hH` (`RBM.Step6.Hierarchy`),
`hFD` (`RBM.Step6.FastDecayHyp`), `h5133` and `hG`.  This file supplies the *analytic* half of
`hH` and settles the fiat status of all four.

## Main results

* `RBM.Uker_ThetaOp_eq` — **`U_{v,t} ∘ Θ_v` is the `v`-derivative of `U_{v,t}`, up to sign.**
  The only algebraic input is `edgeKer_mul_Theta_mul_SB` below, i.e. `(1 - vξS)Θ_{vξ} = 1`:
  one edge factor of (5.17) composed with one slot of (5.16) is
  `(1 - vξS)Θ_{uξ} · ξΘ_{vξ}S = ξ S Θ_{uξ}`.
* `RBM.hasDerivAt_Uker_thetaOp` — **`∂_v U_{v,t} = - U_{v,t} ∘ Θ_v`**, the variation-of-constants
  identity, from `RBM.hasDerivAt_Uker_apply` (T132a) and the previous item.
* `RBM.hasDerivAt_Uker_path` — the product rule `∂_v (U_{v,t} ∘ Y_v) = U_{v,t}(Y'_v - Θ_v Y_v)`
  for a moving tensor.
* `RBM.Uker_duhamel` — **the Duhamel formula for `RBM.Uker`**:
  `Y_u = U_{s,u} Y_s + ∫_s^u U_{v,u} D_v dv` whenever `Y' = Θ_v Y + D` on `[s, u]` and the
  integrand is interval-integrable.  This is the piece nothing in the tree had: T132a's
  `RBM.hasDerivAt_Uker_apply` differentiates `U` with the *tensor frozen*, which is not enough
  to integrate the hierarchy.
* `RBM.Uker_duhamel_Ioo` — the same with the drift identity required only on the **open**
  interval and continuity on the closed one.  This variant is not cosmetic: the Gaussian flow
  `H_u = √u X` is not differentiable at `u = 0` (`RBM.Gauss.hasDerivAt_Psi_Hflow` assumes
  `0 < u`), while `RBM.Step6` admits `s N = 0`, so the closed-interval form of the hypothesis
  is *unsatisfiable* on the Gaussian model whenever the window starts at the origin.
* `RBM.Step6.hierarchy_of_hasDerivAt`, `RBM.Step6.hierarchy_of_hasDerivAt_Ioo` —
  **`RBM.Step6.Hierarchy` from the pointwise-in-time drift identity**
  `∂_v E(L-K)_v = Θ_v (E(L-K)_v) + (DLK_v + DG_v)`, plus interval integrability of the two
  propagated drifts.  These are the first producers of `RBM.Step6.Hierarchy` in the tree.
* `RBM.integral_ThetaOp` — `Θ_v` commutes with expectations (it is a finite `ℂ`-linear
  combination of tensor entries).  This is the step that turns the *pathwise* drift identity
  (5.15) — `RBM.MomentDuhamel.Hyp.drift` — into the *expectation* identity that
  `hierarchy_of_hasDerivAt` consumes.
* `RBM.Step6.hG_zero_right`, `RBM.Step6.sharpExpect_step6_single` — **the fiat audit of `hG`,
  made into a theorem.**  `hG` is satisfied by `DG = 0` with `Cg = 0`; so is the `DG` half of
  `FastDecayHyp`.  Hence Step 6 never needs the paper's split of the drift: a *single* tensor
  `D` carrying the whole non-`Θ` drift discharges `hH`, `hFD`, `h5133` and `hG` at once, and
  nothing is lost, because `RBM.Step6.driftBound_of_5133` and `RBM.Step6.driftBound_of_5134`
  produce the *same* bound `η_v^{-1} (W ℓ_v η_v)^{-3}`.

## The fiat audit (T152)

`RBM.Step6.Hierarchy` and `RBM.Step6.FastDecayHyp` are `Prop`s, not structures; the only data
are the two tensors `DLK DG : RBM.Step6.DriftTensor B`, which `RBM.Step6.sharpExpect_step6`
quantifies over existentially from the caller's point of view.  Field by field:

* `Hierarchy` **alone is fiat-satisfiable**, in exactly the sense of the warning at
  `RBM1D/Gauss/DischargeBDG.lean:70ff`.  Take `DG = 0` and `DLK_v := (∂_v - Θ_v)(E(L-K)_v)`:
  whenever `v ↦ E(L-K)_v` is `C¹` on the window, `Uker_duhamel` below makes the identity true
  by construction, for *no* mathematical content.  So `hH` is not where the content of Step 6
  lives, and a "producer of `hH`" that does not also produce `h5133` is worth nothing.  What
  `hierarchy_of_hasDerivAt` contributes is the converse direction: it lets one *choose* the
  tensors to be the paper's `E E^{((L-K)×(L-K))}` and `E E^{(G)}` and still get the identity,
  which is what makes the size bounds provable rather than merely assumed.
* `hG` **is vacuous as stated for `DG = 0`** (`hG_zero_right`, proved below: `Cg = 0`).  It
  constrains `DG` only once `DG` has been *fixed* to the paper's `E E^{(G)}`; it cannot be used
  to pin `DG` down.  Consequently the four-hypothesis presentation of Step 6 is equivalent to
  a three-hypothesis one (`sharpExpect_step6_single`).
* `h5133` and the `DLK` half of `FastDecayHyp` are the **only** binding constraints on the
  data.  Both are genuine size statements about a tensor that the hierarchy identity has
  already pinned down (the drift of a `C¹` path is unique), so together with `hH` they are not
  fiat.  Neither is produced here; see "What this file does not do".

## What this file does *not* do

The *Gaussian* input to `hierarchy_of_hasDerivAt` — the expectation drift identity
`∂_v E(L-K)_v = Θ_v(E(L-K)_v) + E[F_v]` — is **not** proved here, and it is not a matter of
assembly.  Along the Gaussian flow the pathwise identity (5.15) is
`RBM.Gauss.hasDerivAt_sub_prim_thetaGen` (T140) and the differentiation under the integral sign
is `RBM.Gauss.hasDerivAt_sample_ELval_hierarchy_gauss` (T140, modulo `RBM.Gauss.MatrixStein`
(T70) and the joint differentiability of T141); but `RBM.primRhs` is *quadratic* in the loop
values, so `E[primRhs(L_v)] ≠ primRhs(E L_v)` and the passage to expectations genuinely
produces the term `E[primBil(L-K, L-K)]` — the paper's `E E^{((L-K)×(L-K))}` — rather than
merely commuting.  `integral_ThetaOp` below is the one half of that passage which *is* pure
linearity.  The other half, and the size bounds `h5133`/`hFD`, remain open.

A second obstruction found while writing this file, and recorded here because it decides the
shape of the remaining work: **the Gaussian drift identity cannot hold at `v = 0`.**  Every
route to it goes through the chain rule along `H_v = √v X`, which needs `0 < v`
(`RBM.Gauss.hasDerivAt_Psi_Hflow`, `RBM.Gauss.hasDerivAt_integral_Psi`,
`RBM.Gauss.hasDerivAt_sample_ELval_hierarchy_gauss` all carry `hu : 0 < u`), whereas
`RBM.Step6.sharpExpect_step6` is the one step of Theorem 2.21 that admits `0 ≤ s`.  Hence the
closed-interval hypothesis of `hierarchy_of_hasDerivAt` is unsatisfiable at `s N = 0` and the
`Ioo` variant is the one to use; it costs a continuity hypothesis at the left endpoint in
exchange.  This is the same `0 ≤ s` versus `0 < s` seam that `docs/STATUS.md` records for the
assembly of Theorem 2.21, arriving here from the analytic side.

## Update (T173)

The section `T173: the drift tensor of Step 6, pinned` at the end of this file closes the
first of the two gaps just described.  `RBM.driftE` is the drift tensor, **as a definition**
`D_v = E[F_v]` with `F = RBM.DriftDef.driftF` (T58/T118(iii)); `RBM.hasDerivAt_lkT_thetaOp_driftE`
is the expectation drift identity, the quadratic half included; `RBM.hierarchy_driftE` produces
`RBM.Step6.Hierarchy X E s t (driftE X E) 0` through the `Ioo` variant above; and
`RBM.sharpExpect_step6_driftE` is `sharpExpect_step6_single` with no tensor variable left.
The size obligations `h5133` and the `DLK` half of `hFD` are reduced to pathwise statements
about `driftF` (`RBM.fastDecay_driftE`, `RBM.norm_driftE_le_integral`) but are **not** proved.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM

open MeasureTheory

/-! ### The variation-of-constants calculus for `RBM.Uker` -/

section UkerCalculus

variable (L : ℕ) [NeZero L]

/-- Reindexing a double sum over `(b, c)` by the involution `(b, c) ↦ (b^{(k → c)}, b k)`.
This is the combinatorial content of `Uker_ThetaOp_eq`: one slot of `RBM.ThetaOp` replaces the
`k`-th external index, and the replaced index becomes the summation variable of the `k`-th
edge factor of `RBM.Uker`. -/
theorem sum_update_reindex {n : ℕ} (k : Fin n) (f : LoopArg L n → ZMod L → ℂ) :
    ∑ b : LoopArg L n, ∑ c : ZMod L, f b c
      = ∑ d : LoopArg L n, ∑ e : ZMod L, f (Function.update d k e) (d k) := by
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun p => (Function.update p.1 k p.2, p.1 k))
    (j := fun q => (Function.update q.1 k q.2, q.1 k)) ?_ ?_ ?_ ?_ ?_
  · intro p _
    exact Finset.mem_univ _
  · intro q _
    exact Finset.mem_univ _
  · intro p _
    ext
    · simp
    · simp
  · intro q _
    ext
    · simp
    · simp
  · intro p _
    simp

/-- **One edge of (5.17) composed with one slot of (5.16)**:
`edgeKer_{v,u} · (Θ_{vξ} S) = S Θ_{uξ}`.  The whole computation is
`(1 - vξS) Θ_{uξ} Θ_{vξ} S = Θ_{uξ} (1 - vξS) Θ_{vξ} S = Θ_{uξ} S`, using that the propagators
commute (`RBM.Theta_commute`) and `RBM.mul_Theta`. -/
theorem edgeKer_mul_Theta_mul_SB (hL : 3 ≤ L) {ξ v u : ℂ} (hv : ‖v * ξ‖ < 1)
    (hu : ‖u * ξ‖ < 1) :
    edgeKer L ξ v u * (Theta L (v * ξ) * SB L) = SB L * Theta L (u * ξ) := by
  have hc : Theta L (u * ξ) * Theta L (v * ξ) = Theta L (v * ξ) * Theta L (u * ξ) :=
    (Theta_commute L hL hu hv).eq
  have hcs : Theta L (u * ξ) * SB L = SB L * Theta L (u * ξ) :=
    (Theta_commute_SB L hL hu).eq
  calc edgeKer L ξ v u * (Theta L (v * ξ) * SB L)
      = (1 - (v * ξ) • SB L) * (Theta L (u * ξ) * Theta L (v * ξ)) * SB L := by
        simp only [edgeKer]; noncomm_ring
    _ = ((1 - (v * ξ) • SB L) * Theta L (v * ξ)) * (Theta L (u * ξ) * SB L) := by
        rw [hc]; noncomm_ring
    _ = SB L * Theta L (u * ξ) := by rw [mul_Theta L hL hv, one_mul, hcs]

/-- **`U_{v,u} ∘ Θ_v` in closed form.**  The right-hand side is, up to a sign, exactly the
derivative produced by `RBM.hasDerivAt_Uker_apply`; `hasDerivAt_Uker_thetaOp` below makes that
comparison. -/
theorem Uker_ThetaOp_eq (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} {v u : ℂ}
    (hv : ∀ i, ‖v * ξ i‖ < 1) (hu : ∀ i, ‖u * ξ i‖ < 1)
    (A : LoopArg L n → ℂ) (a : LoopArg L n) :
    Uker L ξ v u (ThetaOp L ξ v A) a
      = ∑ b : LoopArg L n, (∑ i : Fin n,
          (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) v u (a j) (b j))
            * (ξ i * (SB L * Theta L (u * ξ i)) (a i) (b i))) * A b := by
  classical
  have step1 : Uker L ξ v u (ThetaOp L ξ v A) a
      = ∑ k : Fin n, ∑ b : LoopArg L n, ∑ c : ZMod L,
          (∏ i, edgeKer L (ξ i) v u (a i) (b i))
            * ((ξ k * (Theta L (v * ξ k) * SB L) (b k) c) * A (Function.update b k c)) := by
    rw [Uker_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [ThetaOp, Finset.mul_sum]
  have step2 : ∀ k : Fin n,
      (∑ b : LoopArg L n, ∑ c : ZMod L,
          (∏ i, edgeKer L (ξ i) v u (a i) (b i))
            * ((ξ k * (Theta L (v * ξ k) * SB L) (b k) c) * A (Function.update b k c)))
        = ∑ d : LoopArg L n,
            ((∏ j ∈ Finset.univ.erase k, edgeKer L (ξ j) v u (a j) (d j))
              * (ξ k * (SB L * Theta L (u * ξ k)) (a k) (d k))) * A d := by
    intro k
    rw [sum_update_reindex L k (fun b c => (∏ i, edgeKer L (ξ i) v u (a i) (b i))
      * ((ξ k * (Theta L (v * ξ k) * SB L) (b k) c) * A (Function.update b k c)))]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hkey : ∀ e : ZMod L,
        (∏ i, edgeKer L (ξ i) v u (a i) (Function.update d k e i))
          * ((ξ k * (Theta L (v * ξ k) * SB L) (Function.update d k e k) (d k))
              * A (Function.update (Function.update d k e) k (d k)))
        = ((∏ j ∈ Finset.univ.erase k, edgeKer L (ξ j) v u (a j) (d j)) * (ξ k * A d))
            * (edgeKer L (ξ k) v u (a k) e * (Theta L (v * ξ k) * SB L) e (d k)) := by
      intro e
      have hprod : (∏ i, edgeKer L (ξ i) v u (a i) (Function.update d k e i))
          = edgeKer L (ξ k) v u (a k) e
            * ∏ j ∈ Finset.univ.erase k, edgeKer L (ξ j) v u (a j) (d j) := by
        rw [← Finset.mul_prod_erase Finset.univ
          (fun i => edgeKer L (ξ i) v u (a i) (Function.update d k e i)) (Finset.mem_univ k)]
        congr 1
        · rw [Function.update_self]
        · exact Finset.prod_congr rfl fun j hj => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      have hup : Function.update (Function.update d k e) k (d k) = d := by
        rw [Function.update_idem, Function.update_eq_self]
      rw [hprod, hup, Function.update_self]
      ring
    simp_rw [hkey]
    rw [← Finset.mul_sum]
    have hmul : ∑ e : ZMod L,
        edgeKer L (ξ k) v u (a k) e * (Theta L (v * ξ k) * SB L) e (d k)
        = (edgeKer L (ξ k) v u * (Theta L (v * ξ k) * SB L)) (a k) (d k) :=
      (Matrix.mul_apply).symm
    rw [hmul, edgeKer_mul_Theta_mul_SB L hL (hv k) (hu k)]
    ring
  rw [step1]
  simp_rw [step2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_mul]

/-- The Leibniz rule over the `n` edges of (5.17), from `RBM.hasDerivAt_edgeKer`. -/
theorem hasDerivAt_prod_edgeKer {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ) (a b : LoopArg L n) (v : ℝ) :
    HasDerivAt (fun r : ℝ => ∏ i, edgeKer L (ξ i) (r : ℂ) t (a i) (b i))
      (∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (v : ℂ) t (a j) (b j))
        * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))) v := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun (i : Fin n) (r : ℝ) => edgeKer L (ξ i) (r : ℂ) t (a i) (b i))
    (f' := fun i => -(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hasDerivAt_edgeKer L (ξ i) t (a i) (b i) v)
  simpa only [smul_eq_mul] using h

/-- **`∂_v U_{v,t} = - U_{v,t} ∘ Θ_v`**: the variation-of-constants identity for the evolution
kernel (5.17) and the generator (5.16). -/
theorem hasDerivAt_Uker_thetaOp (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} {t : ℂ} {v : ℝ}
    (hv : ∀ i, ‖((v : ℝ) : ℂ) * ξ i‖ < 1) (ht : ∀ i, ‖t * ξ i‖ < 1)
    (A : LoopArg L n → ℂ) (a : LoopArg L n) :
    HasDerivAt (fun r : ℝ => Uker L ξ (r : ℂ) t A a)
      (-Uker L ξ ((v : ℝ) : ℂ) t (ThetaOp L ξ ((v : ℝ) : ℂ) A) a) v := by
  refine (hasDerivAt_Uker_apply L ξ t A a v).congr_deriv ?_
  rw [Uker_ThetaOp_eq L hL hv ht A a, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← neg_mul, ← Finset.sum_neg_distrib]
  exact congrArg (· * A b) (Finset.sum_congr rfl fun i _ => mul_neg _ _)

/-- **The product rule along a moving tensor**: `∂_v (U_{v,t} ∘ Y_v) = U_{v,t}(Y'_v - Θ_v Y_v)`.
`RBM.hasDerivAt_Uker_apply` (T132a) only differentiates `U` with `Y` frozen; this is the form
the hierarchy needs. -/
theorem hasDerivAt_Uker_path (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} {t : ℂ} {v : ℝ}
    (hv : ∀ i, ‖((v : ℝ) : ℂ) * ξ i‖ < 1) (ht : ∀ i, ‖t * ξ i‖ < 1)
    {Y : ℝ → LoopArg L n → ℂ} {Y' : LoopArg L n → ℂ}
    (hY : ∀ b, HasDerivAt (fun r : ℝ => Y r b) (Y' b) v) (a : LoopArg L n) :
    HasDerivAt (fun r : ℝ => Uker L ξ (r : ℂ) t (Y r) a)
      (Uker L ξ ((v : ℝ) : ℂ) t Y' a
        - Uker L ξ ((v : ℝ) : ℂ) t (ThetaOp L ξ ((v : ℝ) : ℂ) (Y v)) a) v := by
  have hterm : ∀ b : LoopArg L n,
      HasDerivAt (fun r : ℝ => (∏ i, edgeKer L (ξ i) (r : ℂ) t (a i) (b i)) * Y r b)
        ((∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (v : ℂ) t (a j) (b j))
            * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))) * Y v b
          + (∏ i, edgeKer L (ξ i) ((v : ℝ) : ℂ) t (a i) (b i)) * Y' b) v :=
    fun b => (hasDerivAt_prod_edgeKer L ξ t a b v).mul (hY b)
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (LoopArg L n)))
    (fun b (_ : b ∈ (Finset.univ : Finset (LoopArg L n))) => hterm b)
  refine hsum.congr_deriv ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ b : LoopArg L n,
      (∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, edgeKer L (ξ j) (v : ℂ) t (a j) (b j))
        * (-(ξ i * (SB L * Theta L (t * ξ i)) (a i) (b i)))) * Y v b
      = -Uker L ξ ((v : ℝ) : ℂ) t (ThetaOp L ξ ((v : ℝ) : ℂ) (Y v)) a := by
    rw [Uker_ThetaOp_eq L hL hv ht (Y v) a, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← neg_mul, ← Finset.sum_neg_distrib]
    exact congrArg (· * Y v b) (Finset.sum_congr rfl fun i _ => mul_neg _ _)
  rw [h1]
  rw [show (∑ b : LoopArg L n, (∏ i, edgeKer L (ξ i) ((v : ℝ) : ℂ) t (a i) (b i)) * Y' b)
      = Uker L ξ ((v : ℝ) : ℂ) t Y' a from rfl]
  ring

/-- **The Duhamel (variation-of-constants) formula for the evolution kernel (5.17).**

If `∂_v Y_v = Θ_v Y_v + D_v` on `[s, u]` then `Y_u = U_{s,u} Y_s + ∫_s^u U_{v,u} D_v dv`.
This is the integrated form of the hierarchy, and the piece the tree did not have:
`RBM.hasDerivAt_Uker_apply` differentiates `U` with the tensor frozen. -/
theorem Uker_duhamel (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} {s u : ℝ}
    (hξs : ∀ r ∈ Set.uIcc s u, ∀ i, ‖((r : ℝ) : ℂ) * ξ i‖ < 1)
    (hξu : ∀ i, ‖((u : ℝ) : ℂ) * ξ i‖ < 1)
    {Y D : ℝ → LoopArg L n → ℂ}
    (hY : ∀ r ∈ Set.uIcc s u, ∀ b, HasDerivAt (fun q : ℝ => Y q b)
      (ThetaOp L ξ ((r : ℝ) : ℂ) (Y r) b + D r b) r)
    (a : LoopArg L n)
    (hint : IntervalIntegrable
      (fun r : ℝ => Uker L ξ ((r : ℝ) : ℂ) ((u : ℝ) : ℂ) (D r) a) volume s u) :
    Y u a = Uker L ξ ((s : ℝ) : ℂ) ((u : ℝ) : ℂ) (Y s) a
      + ∫ r in s..u, Uker L ξ ((r : ℝ) : ℂ) ((u : ℝ) : ℂ) (D r) a := by
  have hderiv : ∀ r ∈ Set.uIcc s u,
      HasDerivAt (fun q : ℝ => Uker L ξ ((q : ℝ) : ℂ) ((u : ℝ) : ℂ) (Y q) a)
        (Uker L ξ ((r : ℝ) : ℂ) ((u : ℝ) : ℂ) (D r) a) r := by
    intro r hr
    refine (hasDerivAt_Uker_path L hL (hξs r hr) hξu
      (Y := Y) (Y' := ThetaOp L ξ ((r : ℝ) : ℂ) (Y r) + D r) (fun b => hY r hr b) a).congr_deriv ?_
    rw [Uker_add, Pi.add_apply, add_sub_cancel_left]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hself : Uker L ξ ((u : ℝ) : ℂ) ((u : ℝ) : ℂ) (Y u) a = Y u a :=
    congrFun (Uker_self L hL hξu (Y u)) a
  rw [hself] at hftc
  rw [hftc]
  ring

theorem continuous_edgeKer_fst (ξ t : ℂ) (x y : ZMod L) :
    Continuous fun r : ℝ => edgeKer L ξ (r : ℂ) t x y :=
  Differentiable.continuous (𝕜 := ℝ)
    fun r : ℝ => (hasDerivAt_edgeKer L ξ t x y r).differentiableAt

theorem continuousOn_Uker_path {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ) {Y : ℝ → LoopArg L n → ℂ}
    {S : Set ℝ} (hY : ∀ b, ContinuousOn (fun q : ℝ => Y q b) S) (a : LoopArg L n) :
    ContinuousOn (fun r : ℝ => Uker L ξ (r : ℂ) t (Y r) a) S := by
  refine continuousOn_finsetSum _ fun b _ => ?_
  exact ((continuous_finsetProd _ fun i _ =>
    continuous_edgeKer_fst L (ξ i) t (a i) (b i)).continuousOn).mul (hY b)

/-- **The Duhamel formula with the derivative only on the open interval.**

The Gaussian flow `H_u = √u X` is *not* differentiable at `u = 0`
(`RBM.Gauss.hasDerivAt_Psi_Hflow` needs `0 < u`), while `RBM.Step6` admits `s N = 0`.  This
variant asks for the drift identity on `(s, u)` and mere continuity on `[s, u]`, which is what
the Gaussian model can actually supply when the window starts at the origin. -/
theorem Uker_duhamel_Ioo (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} {s u : ℝ} (hsu : s ≤ u)
    (hξs : ∀ r ∈ Set.Ioo s u, ∀ i, ‖((r : ℝ) : ℂ) * ξ i‖ < 1)
    (hξu : ∀ i, ‖((u : ℝ) : ℂ) * ξ i‖ < 1)
    {Y D : ℝ → LoopArg L n → ℂ}
    (hcont : ∀ b, ContinuousOn (fun q : ℝ => Y q b) (Set.Icc s u))
    (hY : ∀ r ∈ Set.Ioo s u, ∀ b, HasDerivAt (fun q : ℝ => Y q b)
      (ThetaOp L ξ ((r : ℝ) : ℂ) (Y r) b + D r b) r)
    (a : LoopArg L n)
    (hint : IntervalIntegrable
      (fun r : ℝ => Uker L ξ ((r : ℝ) : ℂ) ((u : ℝ) : ℂ) (D r) a) volume s u) :
    Y u a = Uker L ξ ((s : ℝ) : ℂ) ((u : ℝ) : ℂ) (Y s) a
      + ∫ r in s..u, Uker L ξ ((r : ℝ) : ℂ) ((u : ℝ) : ℂ) (D r) a := by
  have hcontf : ContinuousOn
      (fun q : ℝ => Uker L ξ ((q : ℝ) : ℂ) ((u : ℝ) : ℂ) (Y q) a) (Set.Icc s u) :=
    continuousOn_Uker_path L ξ _ hcont a
  have hderiv : ∀ r ∈ Set.Ioo s u,
      HasDerivWithinAt (fun q : ℝ => Uker L ξ ((q : ℝ) : ℂ) ((u : ℝ) : ℂ) (Y q) a)
        (Uker L ξ ((r : ℝ) : ℂ) ((u : ℝ) : ℂ) (D r) a) (Set.Ioi r) r := by
    intro r hr
    refine HasDerivAt.hasDerivWithinAt ?_
    refine (hasDerivAt_Uker_path L hL (hξs r hr) hξu
      (Y := Y) (Y' := ThetaOp L ξ ((r : ℝ) : ℂ) (Y r) + D r) (fun b => hY r hr b) a).congr_deriv ?_
    rw [Uker_add, Pi.add_apply, add_sub_cancel_left]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hsu hcontf hderiv hint
  have hself : Uker L ξ ((u : ℝ) : ℂ) ((u : ℝ) : ℂ) (Y u) a = Y u a :=
    congrFun (Uker_self L hL hξu (Y u)) a
  rw [hself] at hftc
  rw [hftc]
  ring

/-- **The generator (5.16) commutes with expectations.**  `RBM.ThetaOp` is a finite `ℂ`-linear
combination of entries of its argument, so no hypothesis beyond entrywise integrability is
needed.  This is the linear half of the passage from the *pathwise* drift identity (5.15)
(`RBM.MomentDuhamel.Hyp.drift`) to the *expectation* identity consumed by
`RBM.Step6.hierarchy_of_hasDerivAt`; the nonlinear half is the quadratic term `RBM.primBil`,
which is where the paper's `E E^{((L-K)×(L-K))}` comes from. -/
theorem integral_ThetaOp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (ξ : Fin n → ℂ) (v : ℂ) (Y : Ω → LoopArg L n → ℂ)
    (hY : ∀ b, Integrable (fun ω => Y ω b) P) (a : LoopArg L n) :
    ∫ ω, ThetaOp L ξ v (Y ω) a ∂P = ThetaOp L ξ v (fun b => ∫ ω, Y ω b ∂P) a := by
  classical
  simp only [ThetaOp]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ fun c _ => (hY (Function.update a i c)).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun c _ => (hY (Function.update a i c)).const_mul _)]
  exact Finset.sum_congr rfl fun c _ => integral_const_mul _ _

end UkerCalculus

/-! ### `RBM.Step6.Hierarchy` from the drift identity -/

namespace Step6

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- On the window `0 ≤ v < 1` every edge parameter of a `2`-loop satisfies `‖v ξ_i‖ < 1`, since
`‖ξ_i‖ = ‖m(σ_i) m(σ_{i+1})‖ ≤ 1` (`RBM.Step6.norm_xiOf_mSigma_le`). -/
theorem norm_time_mul_xiOf_lt_one {E : ℝ} (hE : |E| ≤ 2) (σ : Fin 2 → Bool) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (i : Fin 2) : ‖((r : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  calc r * ‖xiOf (mSigma E) σ i‖ ≤ r * 1 :=
        mul_le_mul_of_nonneg_left (norm_xiOf_mSigma_le hE σ i) hr0
    _ = r := mul_one r
    _ < 1 := hr1

/-- **(5.129)–(5.131) from the pointwise-in-time drift identity.**

`RBM.Step6.Hierarchy` is the *integrated* form of (5.20) at loop length `2`, in expectation.
Its differential form is the hypothesis `hderiv` here:
`∂_v E(L-K)_{v,σ,b} = (Θ_{v,σ} ∘ E(L-K)_v)_b + (DLK_{v,σ,b} + DG_{v,σ,b})` for `v ∈ [s_N, u]`.
The passage between the two is `RBM.Uker_duhamel`, plus the linearity of `RBM.Uker` to split
the single integral into the paper's two.

`hderiv`'s generator is written with `RBM.ThetaOp`, which is definitionally
`RBM.SumZeroDyn.genS` (see `RBM.Gauss.thetaGenOp_eq_ThetaOp`), so a `hderiv` phrased with
either operator is accepted.

**This does not by itself make Step 6 true.**  Taking `DG = 0` and `DLK` to be the residual
`(∂_v - Θ_v) E(L-K)_v` satisfies `hderiv` by construction whenever the path is `C¹`; the
content of Step 6 is `h5133` and the fast decay of the *chosen* tensors.  See the fiat audit
in the module docstring. -/
theorem hierarchy_of_hasDerivAt (X : Sample B) {E : ℝ} (hE : |E| ≤ 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {DLK DG : DriftTensor B}
    (hderiv : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool), ∀ v ∈ Set.Icc (s N) ((u : ℝ)),
      ∀ b : LoopArg (B.L N) 2, HasDerivAt (fun q : ℝ => lkT X E N q σ b)
        (ThetaOp (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) (lkT X E N v σ) b
          + (DLK N v σ b + DG N v σ b)) v)
    (hintLK : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (DLK N v σ) a) volume (s N) (u : ℝ))
    (hintG : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (DG N v σ) a) volume (s N) (u : ℝ)) :
    Hierarchy X E s t DLK DG := by
  intro N u σ a
  have hL := B.three_le_L N
  have hsu : s N ≤ (u : ℝ) := u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have huIcc : Set.uIcc (s N) ((u : ℝ)) = Set.Icc (s N) ((u : ℝ)) := Set.uIcc_of_le hsu
  have hbound : ∀ r ∈ Set.uIcc (s N) ((u : ℝ)), ∀ i,
      ‖((r : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
    intro r hr i
    rw [huIcc] at hr
    exact norm_time_mul_xiOf_lt_one hE σ ((hs0 N).trans hr.1) (lt_of_le_of_lt hr.2 hu1) i
  have hξu : ∀ i, ‖(((u : ℝ)) : ℂ) * xiOf (mSigma E) σ i‖ < 1 :=
    norm_time_mul_xiOf_lt_one hE σ ((hs0 N).trans hsu) hu1
  have hduh := Uker_duhamel (B.L N) hL (ξ := xiOf (mSigma E) σ) (s := s N) (u := (u : ℝ))
    hbound hξu (Y := fun v => lkT X E N v σ) (D := fun v => DLK N v σ + DG N v σ)
    (fun r hr b => by
      have := hderiv N u σ r (huIcc ▸ hr) b
      simpa using this) a
    (by
      refine ((hintLK N u σ a).add (hintG N u σ a)).congr ?_
      intro r _
      simp only [Uker_add, Pi.add_apply])
  rw [hduh, add_assoc]
  congr 1
  rw [← intervalIntegral.integral_add (hintLK N u σ a) (hintG N u σ a)]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [Uker_add, Pi.add_apply]

/-- **(5.129)–(5.131) with the drift identity asked for only on the open time interval.**

Same as `hierarchy_of_hasDerivAt`, but with the derivative required only on `(s_N, u)` and
continuity on `[s_N, u]`.  This is the form the Gaussian model can supply at `s_N = 0`, where
the flow `H_u = √u X` is not differentiable. -/
theorem hierarchy_of_hasDerivAt_Ioo (X : Sample B) {E : ℝ} (hE : |E| ≤ 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {DLK DG : DriftTensor B}
    (hcont : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      ContinuousOn (fun q : ℝ => lkT X E N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hderiv : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool), ∀ v ∈ Set.Ioo (s N) ((u : ℝ)),
      ∀ b : LoopArg (B.L N) 2, HasDerivAt (fun q : ℝ => lkT X E N q σ b)
        (ThetaOp (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) (lkT X E N v σ) b
          + (DLK N v σ b + DG N v σ b)) v)
    (hintLK : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (DLK N v σ) a) volume (s N) (u : ℝ))
    (hintG : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (DG N v σ) a) volume (s N) (u : ℝ)) :
    Hierarchy X E s t DLK DG := by
  intro N u σ a
  have hL := B.three_le_L N
  have hsu : s N ≤ (u : ℝ) := u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hbound : ∀ r ∈ Set.Ioo (s N) ((u : ℝ)), ∀ i,
      ‖((r : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 := fun r hr i =>
    norm_time_mul_xiOf_lt_one hE σ ((hs0 N).trans hr.1.le) (hr.2.trans hu1) i
  have hξu : ∀ i, ‖(((u : ℝ)) : ℂ) * xiOf (mSigma E) σ i‖ < 1 :=
    norm_time_mul_xiOf_lt_one hE σ ((hs0 N).trans hsu) hu1
  have hduh := Uker_duhamel_Ioo (B.L N) hL hsu (ξ := xiOf (mSigma E) σ)
    hbound hξu (Y := fun v => lkT X E N v σ) (D := fun v => DLK N v σ + DG N v σ)
    (fun b => hcont N u σ b)
    (fun r hr b => by simpa using hderiv N u σ r hr b) a
    (by
      refine ((hintLK N u σ a).add (hintG N u σ a)).congr ?_
      intro r _
      simp only [Uker_add, Pi.add_apply])
  rw [hduh, add_assoc]
  congr 1
  rw [← intervalIntegral.integral_add (hintLK N u σ a) (hintG N u σ a)]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [Uker_add, Pi.add_apply]

/-! ### The fiat audit of `hG` and of the `DG` half of `FastDecayHyp` -/

/-- The zero tensor is `(ℓ, δ)`-fast-decaying for every non-negative `δ`. -/
theorem fastDecay_zero (L : ℕ) [NeZero L] {n : ℕ} {ℓ δ : ℝ} (hδ : 0 ≤ δ) :
    FastDecay L (n := n) ℓ δ 0 := fun _ _ => by simpa using hδ

/-- **`hG` of `RBM.Step6.sharpExpect_step6` is vacuous at `DG = 0`.**  It bounds `E E^{(G)}`
by `W ℓ_v max |E[⟨(G-m)E_{a₁}⟩ L_{3}]|`; with `Cg = 0` and the zero tensor there is nothing to
prove.  So `hG` cannot be used to pin `DG` down — the constraint only bites once `DG` has been
*fixed* to the paper's `E E^{(G)}`.  This is the negative half of T152's fiat audit. -/
theorem hG_zero_right (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ N (v : TimeIcc s t N) (σ : Fin 2 → Bool)
      (a : LoopArg (B.L N) 2) (Λ : ℝ),
      (∀ a₁ (w : LoopData (B.L N) 3), ‖mix13 X E N v a₁ w‖ ≤ Λ) →
        ‖(0 : DriftTensor B) N v σ a‖ ≤ Cg * ((B.W N : ℝ) * B.ell N v * Λ) :=
  ⟨0, le_rfl, fun _ _ _ _ _ _ => by simp⟩

/-- **Step 6 with a single drift tensor.**

`RBM.Step6.sharpExpect_step6` splits the drift of (5.15) into the paper's
`E E^{((L-K)×(L-K))}` and `E E^{(G)}` and asks for a separate bound on each — but the two
bounds, (5.133) and (5.135), have the *same* size `η_v^{-1}(W ℓ_v η_v)^{-3}`
(`RBM.Step6.driftBound_of_5133`, `RBM.Step6.driftBound_of_5134`).  Together with
`hG_zero_right` and `fastDecay_zero` this means the split costs nothing: one tensor `D`
carrying the whole non-`Θ` drift discharges `hH`, `hFD`, `h5133` and `hG` at once.

For T152 this is the operative reduction: the four open hypotheses of Step 6 are **three**
obligations on a single tensor — the hierarchy identity (`hierarchy_of_hasDerivAt`), the
fast decay of `E(L-K)_s` and of `D`, and the bound (5.133) on `D`. -/
theorem sharpExpect_step6_single (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {D : DriftTensor B}
    (hH : Hierarchy X E s t D 0)
    (hFD : ∀ τ > (0 : ℝ), ∀ Dd > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-Dd))
          (lkT X E N (s N) σ) ∧
        ∀ v ∈ Set.Icc (s N) (t N),
          FastDecay (B.L N) (B.ell N v * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-Dd)) (D N v σ))
    (h5132 : UnifDetDom (fun N (u : LoopData (B.L N) 2) => X.expErr E N (s N) u.idx)
      (fun N _ => (B.scale E N (s N))⁻¹ ^ 3))
    (h5133 : UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) =>
      ‖D N p.1 p.2.1 p.2.2‖)
      (fun N p => (B.W N : ℝ) * B.ell N p.1 * (B.scale E N p.1)⁻¹ ^ 4))
    (h527 : Eq527 X E s t)
    (hq11 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖quad11 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hint1 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N v ω (Step6.oneLoop a₁)) B.P)
    (hint2 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)) (w : LoopData (B.L N) 3),
      Integrable (fun ω => (X.Lval E N v ω (Step6.oneLoop a₁) - B.Kval E N v (Step6.oneLoop a₁)) *
        (X.Lval E N v ω w.idx - B.Kval E N v w.idx)) B.P)
    (hq13 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × LoopData (B.L N) 3)) =>
      ‖quad13 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 4)) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr E N p.1 p.2.idx)
      (fun N _ => (B.scale E N (t N))⁻¹ ^ 3) := by
  refine sharpExpect_step6 X hκ0 hκ1 hEκ hs0 hst ht1 hc hH ?_ h5132 h5133 h527 hq11
    (hG_zero_right X E s t) hint1 hint2 hq13
  intro τ hτ Dd hDd
  filter_upwards [hFD τ hτ Dd hDd] with N hN σ
  have hδ : (0 : ℝ) ≤ (B.W N : ℝ) ^ (-Dd) := by
    have : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
    positivity
  exact ⟨(hN σ).1, fun v hv => ⟨(hN σ).2 v hv, fastDecay_zero (B.L N) hδ⟩⟩

end Step6

/-! ### T173: the drift tensor of Step 6, pinned to `RBM.DriftDef.driftF`

The reduction `sharpExpect_step6_single` leaves three obligations on a *single* tensor.  They
are obligations about *some* tensor only as long as the tensor is free, so the first thing to
do is to remove that freedom: `RBM.driftE` below is a **definition**,
`D_{v,σ,a} = E[F_{v,σ,a}]` with `F` the drift `RBM.DriftDef.driftF` that T58/T118(iii) proved
`RBM.MomentDuhamel.Hyp.F` to be.  Nothing in it can be chosen. -/

section DriftE

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(5.15) with the time derivative removed**, i.e. the purely algebraic content of
`RBM.DriftDef.drift_split_gen`:

`Ẽ + (primRhs(L) - primRhs(K)) = Θ_u (L - K) + F_u`.

`RBM.DriftDef.drift_split_gen` states this with `∂_u(L-K)` and `𝓛(L-K)` in place of the two
left-hand summands and therefore needs `M` Hermitian and `Im z_u ≠ 0`; the algebra behind it
needs neither, and it is the algebra that survives the passage to expectations.  The three
inputs are `RBM.primRhs_sub` (5.12)/(5.13), `RBM.Decay.sum_couplingLen` (5.14) truncated by
`RBM.DriftDef.sum_couplingLen_erase_two`, and (5.19)
(`RBM.Gauss.couplingLen_two_eq_thetaGenLoop`), which identifies the `l_K = 2` grade of the
coupling with the generator. -/
theorem eGterm_add_primRhs_sub_eq (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (B.L N) (n + 2))
    (hm : ∀ b b' : Bool, ‖(u : ℂ) * (mSigma E b * mSigma E b')‖ < 1) :
    Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) (LoopData.idx (σ, a))
        + (primRhs (B.L N) (B.W N) (gloop (B.L N) (B.W N) M (zt E u)) (LoopData.idx (σ, a))
          - primRhs (B.L N) (B.W N) (B.Kval E N u) (LoopData.idx (σ, a)))
      = ThetaOp (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
          (MomentDuhamel.lkFun B E N u M σ) a
        + DriftDef.driftF B E N u M σ a := by
  set I : LoopIdx (ZMod (B.L N)) := LoopData.idx (σ, a) with hI
  have hwf : I.WF := LoopData.idx_wf _
  have hlen : I.length = n + 2 := LoopData.idx_length _
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  set D : LoopIdx (ZMod (B.L N)) → ℂ :=
    gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u with hD
  have hgen : ThetaOp (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
      (MomentDuhamel.lkFun B E N u M σ) a
      = SumZeroDyn.genS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
          (MomentDuhamel.lkFun B E N u M σ) a := rfl
  rw [hgen, DriftDef.genS_eq_thetaGenLoop_gen B E N u σ a, DriftDef.driftF]
  have hK : ∀ σ₁ σ₂ a₁ a₂, B.Kval E N u ⟨[σ₁, σ₂], [a₁, a₂]⟩
      = kTwo (B.L N) (B.W N) (mSigma E) u σ₁ σ₂ a₁ a₂ := by
    intro σ₁ σ₂ a₁ a₂; rw [Band.Kval, Kgen_two]
  have hξ : ‖(u : ℂ) * Gauss.xiLoop (mSigma E) I (I.length - 1)‖ < 1 := by
    rw [Gauss.xiLoop]; exact hm _ _
  have hcoup := Gauss.couplingLen_two_eq_thetaGenLoop (L := B.L N) (B.W N) (mSigma E) u
    (B.Kval E N u) D hL3 hK I hwf (by omega) hξ
  have hsum : Decay.couplingLen (B.L N) (B.W N) 2 (B.Kval E N u) D I
        + ∑ lK ∈ Finset.Icc 3 (n + 2), Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D I
      = primBil (B.L N) (B.W N) (B.Kval E N u) D I
        + primBil (B.L N) (B.W N) D (B.Kval E N u) I := by
    have hN : I.length + 2 ≤ n + 4 := by omega
    have h2mem : (2 : ℕ) ∈ Finset.range (n + 4) := Finset.mem_range.mpr (by omega)
    have hstep := Finset.add_sum_erase (Finset.range (n + 4))
      (fun lK => Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D I) h2mem
    rw [← hlen, ← DriftDef.sum_couplingLen_erase_two (B.L N) (B.W N) (B.Kval E N u) D I hN,
      hstep, Decay.sum_couplingLen (B.L N) (B.W N) (B.Kval E N u) D I hN]
  have hps := primRhs_sub (B.L N) (B.W N) (gloop (B.L N) (B.W N) M (zt E u)) (B.Kval E N u) I
  rw [← hD] at hps
  linear_combination hps - hsum + hcoup

/-- **The drift tensor of Step 6, as a definition**: `D_{v,σ,a} = E[F_{v,σ,a}]`.

`F` is `RBM.DriftDef.driftF`, which T58/T118(iii) proved to be the drift of (5.15)
(`RBM.DriftDef.F_eq_driftF`, via `RBM.MomentDuhamel.Hyp.F_unique`) — every summand of it is a
definition in the Green function of the matrix.  So `driftE` has **no free data at all**, and
`RBM.Step6.sharpExpect_step6_single` applied to it (`sharpExpect_step6_driftE` below)
quantifies over no tensor.  `driftE_eq_integral_Fpath` records that it is literally
`E[H.Fpath]` for any `RBM.MomentDuhamel.Hyp`. -/
noncomputable def driftE (X : Sample B) (E : ℝ) : Step6.DriftTensor B :=
  fun N v σ a => ∫ ω, DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ a ∂B.P

/-- **`driftE` is `E[F]` for the `F` of the moment interface**, on the window and for
`|E| < 2`, `0 ≤ v < 1`.  `RBM.MomentDuhamel.Hyp.Fpath` is pinned by `Hyp.drift`, so this is a
statement about a determined object, not about a choice. -/
theorem driftE_eq_integral_Fpath {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}
    (H : MomentDuhamel.Hyp X E s t 0) {N : ℕ} {v : ℝ} (hE : |E| < 2) (hv0 : 0 ≤ v)
    (hv1 : v < 1) (hsv : s N ≤ v) (hvt : v ≤ t N) (σ : Fin 2 → Bool)
    (a : LoopArg (B.L N) 2) :
    driftE X E N v σ a = ∫ ω, H.Fpath N v ω σ a ∂B.P := by
  refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).symm
  exact DriftDef.Fpath_eq_driftF_of_lt_one H hE hv0 hv1 hsv hvt ω σ a

/-! #### The expectation-form drift identity -/

theorem integrable_lkFun (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) {m : ℕ}
    (σ : Fin m → Bool) (b : LoopArg (B.L N) m)
    (h : Integrable (fun ω => X.Lval E N v ω (LoopData.idx (σ, b))) B.P) :
    Integrable (fun ω => MomentDuhamel.lkFun B E N v (X.H N v ω) σ b) B.P := by
  have := B.isProbabilityMeasure
  exact h.sub (integrable_const _)

theorem integral_lkFun (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) {m : ℕ}
    (σ : Fin m → Bool) (b : LoopArg (B.L N) m)
    (h : Integrable (fun ω => X.Lval E N v ω (LoopData.idx (σ, b))) B.P) :
    ∫ ω, MomentDuhamel.lkFun B E N v (X.H N v ω) σ b ∂B.P
      = X.ELval E N v (LoopData.idx (σ, b)) - B.Kval E N v (LoopData.idx (σ, b)) := by
  have := B.isProbabilityMeasure
  rw [show (fun ω => MomentDuhamel.lkFun B E N v (X.H N v ω) σ b)
      = (fun ω => X.Lval E N v ω (LoopData.idx (σ, b))
          - B.Kval E N v (LoopData.idx (σ, b))) from rfl,
    integral_sub h (integrable_const _), integral_const]
  simp [Sample.ELval]

/-- `RBM.ThetaOp` of an integrable family is integrable: it is a finite `ℂ`-linear combination
of entries.  The companion of `RBM.integral_ThetaOp`. -/
theorem integrable_ThetaOp (L : ℕ) [NeZero L] {P : Measure Ω} {n : ℕ}
    (ξ : Fin n → ℂ) (t : ℂ) (Y : Ω → LoopArg L n → ℂ)
    (hY : ∀ b, Integrable (fun ω => Y ω b) P) (a : LoopArg L n) :
    Integrable (fun ω => ThetaOp L ξ t (Y ω) a) P := by
  classical
  simp only [ThetaOp]
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun c _ => (hY (Function.update a i c)).const_mul _

/-- **The expectation-form drift identity**
`∂_v E(L-K)_{v,σ,a} = (Θ_v ∘ E(L-K)_v)_a + D_{v,σ,a}`, with `D = RBM.driftE`.

This is the input `RBM.Step6.hierarchy_of_hasDerivAt_Ioo` consumes, and it is the step T152
left open.  Two things happen in it.  The *linear* half is `RBM.integral_ThetaOp`: `Θ_v`
commutes with `E`.  The *quadratic* half does not commute — `RBM.primRhs` is quadratic in the
loop values, so `E[primRhs(L_v)] ≠ primRhs(E L_v)` — and what survives is exactly the
`RBM.primBil (L-K) (L-K)` summand of `RBM.DriftDef.driftF`, i.e. the paper's
`E E^{((L-K)×(L-K))}`.  That summand is inside `D`, where the paper puts it.

`hEL` is the conclusion of `RBM.Gauss.hasDerivAt_sample_ELval_hierarchy_gauss` (T140) read on
an abstract `RBM.Sample`; it is the only analytic input, and it carries `0 < v` there, which
is why the hierarchy can only be produced on the **open** interval. -/
theorem hasDerivAt_lkT_thetaOp_driftE (X : Sample B) (E : ℝ) {N : ℕ} {v : ℝ}
    (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2)
    (hm : ∀ b b' : Bool, ‖(v : ℂ) * (mSigma E b * mSigma E b')‖ < 1)
    (hintL : ∀ b : LoopArg (B.L N) 2,
      Integrable (fun ω => X.Lval E N v ω (LoopData.idx (σ, b))) B.P)
    (hintF : Integrable (fun ω => DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ a) B.P)
    (hEL : HasDerivAt (fun q : ℝ => X.ELval E N q (LoopData.idx (σ, a)))
      (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma E) (X.H N v ω) (zt E v) (LoopData.idx (σ, a))
        + primRhs (B.L N) (B.W N) (X.Lval E N v ω) (LoopData.idx (σ, a))) ∂B.P) v) :
    HasDerivAt (fun q : ℝ => Step6.lkT X E N q σ a)
      (ThetaOp (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) (Step6.lkT X E N v σ) a
        + driftE X E N v σ a) v := by
  have hP := B.isProbabilityMeasure
  have hL3 := B.three_le_L N
  have hK : HasDerivAt (fun q : ℝ => B.Kval E N q (LoopData.idx (σ, a)))
      (primRhs (B.L N) (B.W N) (B.Kval E N v) (LoopData.idx (σ, a))) v :=
    hasDerivAt_Kgen_all (L := B.L N) (B.W N) (mSigma E) hL3 hm _ (LoopData.idx_wf _) (by simp)
  refine (hEL.sub hK).congr_deriv ?_
  have hptw : ∀ ω : Ω,
      Gauss.eGterm (B.L N) (B.W N) (mSigma E) (X.H N v ω) (zt E v) (LoopData.idx (σ, a))
        + primRhs (B.L N) (B.W N) (X.Lval E N v ω) (LoopData.idx (σ, a))
      = (ThetaOp (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
            (MomentDuhamel.lkFun B E N v (X.H N v ω) σ) a
          + DriftDef.driftF B E N v (X.H N v ω) σ a)
        + primRhs (B.L N) (B.W N) (B.Kval E N v) (LoopData.idx (σ, a)) := by
    intro ω
    have h := eGterm_add_primRhs_sub_eq B E N v (X.H N v ω) (n := 0) σ a hm
    have hLv : X.Lval E N v ω = gloop (B.L N) (B.W N) (X.H N v ω) (zt E v) := rfl
    rw [hLv]
    linear_combination h
  have hintTh : Integrable (fun ω =>
      ThetaOp (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (MomentDuhamel.lkFun B E N v (X.H N v ω) σ) a) B.P :=
    integrable_ThetaOp (B.L N) _ _ _ (fun b => integrable_lkFun X E N v σ b (hintL b)) a
  have hintSum : Integrable (fun ω : Ω =>
      ThetaOp (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
          (MomentDuhamel.lkFun B E N v (X.H N v ω) σ) a
        + DriftDef.driftF B E N v (X.H N v ω) σ a) B.P := hintTh.add hintF
  calc (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma E) (X.H N v ω) (zt E v)
            (LoopData.idx (σ, a))
          + primRhs (B.L N) (B.W N) (X.Lval E N v ω) (LoopData.idx (σ, a))) ∂B.P)
        - primRhs (B.L N) (B.W N) (B.Kval E N v) (LoopData.idx (σ, a))
      = ((∫ ω, (ThetaOp (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
              (MomentDuhamel.lkFun B E N v (X.H N v ω) σ) a
            + DriftDef.driftF B E N v (X.H N v ω) σ a) ∂B.P)
          + primRhs (B.L N) (B.W N) (B.Kval E N v) (LoopData.idx (σ, a)))
        - primRhs (B.L N) (B.W N) (B.Kval E N v) (LoopData.idx (σ, a)) := by
        congr 1
        rw [show (fun ω : Ω => Gauss.eGterm (B.L N) (B.W N) (mSigma E) (X.H N v ω) (zt E v)
              (LoopData.idx (σ, a))
            + primRhs (B.L N) (B.W N) (X.Lval E N v ω) (LoopData.idx (σ, a)))
          = (fun ω : Ω => (ThetaOp (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
                (MomentDuhamel.lkFun B E N v (X.H N v ω) σ) a
              + DriftDef.driftF B E N v (X.H N v ω) σ a)
            + primRhs (B.L N) (B.W N) (B.Kval E N v) (LoopData.idx (σ, a)))
          from funext hptw,
          integral_add hintSum (integrable_const _), integral_const]
        simp
    _ = (∫ ω, ThetaOp (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
            (MomentDuhamel.lkFun B E N v (X.H N v ω) σ) a ∂B.P)
          + driftE X E N v σ a := by
        rw [integral_add hintTh hintF,
          show driftE X E N v σ a
            = ∫ ω, DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ a ∂B.P from rfl]
        ring
    _ = ThetaOp (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) (Step6.lkT X E N v σ) a
          + driftE X E N v σ a := by
        congr 1
        rw [integral_ThetaOp (B.L N) (P := B.P) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
          (fun ω b => MomentDuhamel.lkFun B E N v (X.H N v ω) σ b)
          (fun b => integrable_lkFun X E N v σ b (hintL b)) a]
        congr 1
        funext b
        exact integral_lkFun X E N v σ b (hintL b)

/-! #### `RBM.Step6.Hierarchy` for the single tensor -/

theorem Uker_zero (L : ℕ) [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ)
    (a : LoopArg L n) : Uker L ξ s t (0 : LoopArg L n → ℂ) a = 0 := by
  rw [Uker_apply]
  exact Finset.sum_eq_zero fun b _ => by simp

theorem norm_time_mul_mSigma_lt_one {E : ℝ} (hE : |E| ≤ 2) {v : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v < 1) (b b' : Bool) : ‖(v : ℂ) * (mSigma E b * mSigma E b')‖ < 1 := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0,
    norm_mSigma hE, norm_mSigma hE, mul_one, mul_one]
  exact hv1

/-- **(5.129)-(5.131) with the single tensor `RBM.driftE`.**

The second drift is `0`, which is legitimate by `RBM.Step6.hG_zero_right` and
`RBM.Step6.fastDecay_zero` (T152): the paper's split of the drift buys nothing in Lean.  The
derivative is required only on the **open** interval, and that is forced, not convenient:
every route to `hEL` factors through the chain rule along `H_v = √v X`, which carries `0 < v`,
while `RBM.Step6.sharpExpect_step6` admits `s N = 0`.

This is the first producer of `RBM.Step6.Hierarchy` in the tree whose tensor is a definition
rather than a bound variable. -/
theorem hierarchy_driftE (X : Sample B) {E : ℝ} (hE : |E| ≤ 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hcont : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT X E N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintL : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => X.Lval E N v ω (LoopData.idx (σ, b))) B.P)
    (hintF : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ b) B.P)
    (hEL : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      HasDerivAt (fun q : ℝ => X.ELval E N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma E) (X.H N v ω) (zt E v)
            (LoopData.idx (σ, b))
          + primRhs (B.L N) (B.W N) (X.Lval E N v ω) (LoopData.idx (σ, b))) ∂B.P) v)
    (hintU : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftE X E N v σ) a) volume (s N) (u : ℝ)) :
    Step6.Hierarchy X E s t (driftE X E) 0 := by
  refine Step6.hierarchy_of_hasDerivAt_Ioo X hE hs0 ht1 hcont ?_ hintU ?_
  · intro N u σ v hv b
    have hv0 : 0 < v := lt_of_le_of_lt (hs0 N) hv.1
    have hv1 : v < 1 := hv.2.trans (u.2.2.trans_lt (ht1 N))
    have hm := norm_time_mul_mSigma_lt_one hE hv0.le hv1
    refine (hasDerivAt_lkT_thetaOp_driftE X E σ b hm (hintL N v hv0 hv1 σ)
      (hintF N v hv0 hv1 σ b) (hEL N v hv0 hv1 σ b)).congr_deriv ?_
    simp
  · intro N u σ a
    have h0 : ∀ r : ℝ, Uker (B.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) (((u : ℝ)) : ℂ)
        ((0 : Step6.DriftTensor B) N r σ) a = 0 := fun _ => Uker_zero (B.L N) _ _ _ a
    simp only [h0]
    exact intervalIntegrable_const

/-! #### The size obligations on `RBM.driftE`

Both remaining obligations of `RBM.Step6.sharpExpect_step6_single` are bounds on `D`, and
taking the expectation is *not* what makes them hard: an expectation of a uniformly
fast-decaying family is fast-decaying (`fastDecay_driftE`), and the norm of an expectation is
at most the first moment of the norm (`norm_driftE_le_integral`).  What is left after these
two reductions is the pathwise estimate of Lemma 5.10 for `RBM.DriftDef.driftF`
(`RBM.DriftDef.fastDecay_driftF` already gives the decay half from Lemma 5.9's inputs), and
for (5.133) the first-moment version of it.  See `docs/STATUS.md`. -/

theorem fastDecay_integral {L : ℕ} [NeZero L] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    {ℓ δ : ℝ} {A : Ω → LoopArg L n → ℂ} (h : ∀ ω, FastDecay L ℓ δ (A ω)) :
    FastDecay L ℓ δ (fun b => ∫ ω, A ω b ∂P) := by
  intro b hb
  have := norm_integral_le_of_norm_le_const (μ := P) (C := δ) (f := fun ω => A ω b)
    (Filter.Eventually.of_forall fun ω => h ω b hb)
  simpa using this

/-- **The `DLK` half of `RBM.Step6.FastDecayHyp` for `RBM.driftE`, reduced to the pathwise
statement.**  With `RBM.DriftDef.fastDecay_driftF` this makes the fast decay of the drift a
consequence of Lemma 5.9, with no stochastic step. -/
theorem fastDecay_driftE (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool)
    {ℓ δ : ℝ}
    (h : ∀ ω, FastDecay (B.L N) ℓ δ
      (fun b : LoopArg (B.L N) 2 => DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ b)) :
    FastDecay (B.L N) ℓ δ (driftE X E N v σ) := by
  have := B.isProbabilityMeasure
  exact fastDecay_integral (P := B.P) h

/-- **(5.133) for `RBM.driftE` is a first-moment bound on `F`.**  Note that it is *not* a
pathwise deterministic bound: `‖F‖` is only controlled with high probability, so the route to
`h5133` is a bound on `E‖F‖`, not on `sup_ω ‖F‖`. -/
theorem norm_driftE_le_integral (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool)
    (a : LoopArg (B.L N) 2) :
    ‖driftE X E N v σ a‖
      ≤ ∫ ω, ‖DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ a‖ ∂B.P :=
  norm_integral_le_integral_norm _

/-- **`RBM.Step6.sharpExpect_step6_single` with the drift tensor pinned**: the probe call the
ticket asks for.  There is no tensor variable left anywhere in the statement — the `D` of
`sharpExpect_step6_single` is `RBM.driftE`, a definition — so `hH`, `hFD` and `h5133` are
statements about a determined object and none of them can be satisfied by choosing `D`. -/
theorem sharpExpect_step6_driftE (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hH : Step6.Hierarchy X E s t (driftE X E) 0)
    (hFD : ∀ τ > (0 : ℝ), ∀ Dd > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-Dd))
          (Step6.lkT X E N (s N) σ) ∧
        ∀ v ∈ Set.Icc (s N) (t N),
          FastDecay (B.L N) (B.ell N v * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-Dd))
            (driftE X E N v σ))
    (h5132 : UnifDetDom (fun N (u : LoopData (B.L N) 2) => X.expErr E N (s N) u.idx)
      (fun N _ => (B.scale E N (s N))⁻¹ ^ 3))
    (h5133 : UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) =>
      ‖driftE X E N p.1 p.2.1 p.2.2‖)
      (fun N p => (B.W N : ℝ) * B.ell N p.1 * (B.scale E N p.1)⁻¹ ^ 4))
    (h527 : Step6.Eq527 X E s t)
    (hq11 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖Step6.quad11 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hint1 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N v ω (Step6.oneLoop a₁)) B.P)
    (hint2 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)) (w : LoopData (B.L N) 3),
      Integrable (fun ω => (X.Lval E N v ω (Step6.oneLoop a₁) - B.Kval E N v (Step6.oneLoop a₁)) *
        (X.Lval E N v ω w.idx - B.Kval E N v w.idx)) B.P)
    (hq13 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × LoopData (B.L N) 3)) =>
      ‖Step6.quad13 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 4)) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr E N p.1 p.2.idx)
      (fun N _ => (B.scale E N (t N))⁻¹ ^ 3) :=
  Step6.sharpExpect_step6_single X hκ0 hκ1 hEκ hs0 hst ht1 hc hH hFD h5132 h5133 h527 hq11
    hint1 hint2 hq13

end DriftE

end RBM
