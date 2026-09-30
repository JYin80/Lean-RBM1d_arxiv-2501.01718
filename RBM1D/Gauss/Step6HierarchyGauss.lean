/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step6
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Hierarchy.DriftDef

/-!
# The Step 6 hierarchy (5.129)–(5.131) from a pointwise drift identity

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8.  The hierarchy `RBM.Step6.Hierarchy` of Step 6 quantifies over two drift
tensors.  This file supplies its *analytic* half: the Duhamel formula for the propagator
`RBM.Uker`, and the passage from a pointwise-in-time drift identity to the hierarchy.

## Main results

* `RBM.Uker_ThetaOp_eq` — **`U_{v,t} ∘ Θ_v` is the `v`-derivative of `U_{v,t}`, up to sign.**
  The only algebraic input is `edgeKer_mul_Theta_mul_SB` below, i.e. `(1 - vξS)Θ_{vξ} = 1`:
  one edge factor of (5.17) composed with one slot of (5.16) is
  `(1 - vξS)Θ_{uξ} · ξΘ_{vξ}S = ξ S Θ_{uξ}`.
* `RBM.hasDerivAt_Uker_path` — the product rule `∂_v (U_{v,t} ∘ Y_v) = U_{v,t}(Y'_v - Θ_v Y_v)`
  for a moving tensor; at a frozen tensor it is the variation-of-constants identity
  `∂_v U_{v,t} = - U_{v,t} ∘ Θ_v`.
* `RBM.Uker_duhamel_Ioo` — **the Duhamel formula for `RBM.Uker`**:
  `Y_u = U_{s,u} Y_s + ∫_s^u U_{v,u} D_v dv` whenever `Y' = Θ_v Y + D` on the **open**
  interval `(s, u)`, `Y` is continuous on `[s, u]`, and the integrand is interval-integrable.
  The open interval is not cosmetic: the Gaussian flow `H_u = √u X` is not differentiable at
  `u = 0`, while Step 6 admits `s N = 0`, so a closed-interval form of the hypothesis would be
  *unsatisfiable* on the Gaussian model whenever the window starts at the origin.
* `RBM.Step6.hierarchy_of_hasDerivAt_Ioo` — **`RBM.Step6.Hierarchy` from the pointwise-in-time
  drift identity** `∂_v E(L-K)_v = Θ_v (E(L-K)_v) + (DLK_v + DG_v)` on the open interval, plus
  interval integrability of the two propagated drifts.
* `RBM.integral_ThetaOp` — `Θ_v` commutes with expectations (it is a finite `ℂ`-linear
  combination of tensor entries).  This is the step that turns the *pathwise* drift identity
  (5.15) into the *expectation* identity that `hierarchy_of_hasDerivAt_Ioo` consumes.

## Fiat-satisfiability

`RBM.Step6.Hierarchy` is a `Prop`, not a structure; the only data are the two tensors
`DLK DG : RBM.Step6.DriftTensor B`.  The hierarchy **alone is fiat-satisfiable**, in exactly the
sense of the warning at `RBM1D/Gauss/DischargeBDG.lean`.  Take `DG = 0` and
`DLK_v := (∂_v - Θ_v)(E(L-K)_v)`: whenever `v ↦ E(L-K)_v` is `C¹` on the window, the Duhamel
formula makes the identity true by construction, for *no* mathematical content.  So the
hierarchy is not where the content of Step 6 lives.  What `hierarchy_of_hasDerivAt_Ioo`
contributes is the converse direction: it lets one *choose* the tensors to be the paper's
`E E^{((L-K)×(L-K))}` and `E E^{(G)}` and still get the identity, which is what makes the size
bounds (5.133)–(5.135) provable rather than merely assumed.  Those size bounds are not proved
here.

## The drift tensor, pinned

The section "The drift tensor of Step 6, pinned to `RBM.DriftDef.driftF`" at the end of this
file removes the freedom in the tensor.  `RBM.driftE` is the drift tensor, **as a definition**
`D_v = E[F_v]` with `F = RBM.DriftDef.driftF`; `RBM.hasDerivAt_lkT_thetaOp_driftE` is the
expectation drift identity, the quadratic half included: `RBM.primRhs` is *quadratic* in the
loop values, so `E[primRhs(L_v)] ≠ primRhs(E L_v)` and the passage to expectations genuinely
produces the term `E[primBil(L-K, L-K)]` — the paper's `E E^{((L-K)×(L-K))}` — rather than
merely commuting.  `integral_ThetaOp` is the one half of that passage which *is* pure linearity.

**The Gaussian drift identity cannot hold at `v = 0`.**  Every route to it goes through the
chain rule along `H_v = √v X`, which needs `0 < v`, whereas Step 6 is the one step of
Theorem 2.21 that admits `0 ≤ s`.  Hence the `Ioo` variant is the one to use; it costs a
continuity hypothesis at the left endpoint in exchange.  This is the same `0 ≤ s` versus
`0 < s` seam as in the assembly of Theorem 2.21, arriving here from the analytic side.

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
derivative of `U_{v,u}` in `v` with the tensor frozen. -/
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

/-- **The product rule along a moving tensor**: `∂_v (U_{v,t} ∘ Y_v) = U_{v,t}(Y'_v - Θ_v Y_v)`.
Differentiating `U` with `Y` frozen is not enough; this is the form the hierarchy needs. -/
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

The Gaussian flow `H_u = √u X` is *not* differentiable at `u = 0`, while Step 6 admits `s N = 0`.
This variant asks for the drift identity on `(s, u)` and mere continuity on `[s, u]`, which is what
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
to the *expectation* identity consumed by `RBM.Step6.hierarchy_of_hasDerivAt_Ioo`; the
nonlinear half is the quadratic term `RBM.primBil`,
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

/-- **(5.129)–(5.131) with the drift identity asked for only on the open time interval.**

The derivative is required only on `(s_N, u)`, and continuity on `[s_N, u]`.  This is the form the
Gaussian model can supply at `s_N = 0`, where the flow `H_u = √u X` is not differentiable. -/
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

end Step6

/-! ### The drift tensor of Step 6, pinned to `RBM.DriftDef.driftF`

Obligations on a drift tensor are obligations about *some* tensor only as long as the tensor
is free, so the first thing to do is to remove that freedom: `RBM.driftE` below is a
**definition**, `D_{v,σ,a} = E[F_{v,σ,a}]` with `F` the drift `RBM.DriftDef.driftF`.  Nothing
in it can be chosen. -/

section DriftE

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(5.15) with the time derivative removed**, i.e. the purely algebraic content of the drift
identity (5.15):

`Ẽ + (primRhs(L) - primRhs(K)) = Θ_u (L - K) + F_u`.

With `∂_u(L-K)` and `𝓛(L-K)` in place of the two left-hand summands the identity needs `M`
Hermitian and `Im z_u ≠ 0`; the algebra behind it
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

`F` is `RBM.DriftDef.driftF`, the drift of (5.15) — every summand of it is a definition in the
Green function of the matrix.  So `driftE` has **no free data at all**. -/
noncomputable def driftE (X : Sample B) (E : ℝ) : Step6.DriftTensor B :=
  fun N v σ a => ∫ ω, DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ a ∂B.P

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

This is the input `RBM.Step6.hierarchy_of_hasDerivAt_Ioo` consumes.  Two things happen in it.  The
*linear* half is `RBM.integral_ThetaOp`: `Θ_v` commutes with `E`.  The *quadratic* half does not
commute — `RBM.primRhs` is quadratic in the loop values, so `E[primRhs(L_v)] ≠ primRhs(E L_v)` — and
what survives is exactly the `RBM.primBil (L-K) (L-K)` summand of `RBM.DriftDef.driftF`, i.e. the
paper's `E E^{((L-K)×(L-K))}`.  That summand is inside `D`, where the paper puts it.

`hEL` is the conclusion of `RBM.Gauss.hasDerivAt_sample_ELval_hierarchy_gauss` read on
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

theorem norm_time_mul_mSigma_lt_one {E : ℝ} (hE : |E| ≤ 2) {v : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v < 1) (b b' : Bool) : ‖(v : ℂ) * (mSigma E b * mSigma E b')‖ < 1 := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0,
    norm_mSigma hE, norm_mSigma hE, mul_one, mul_one]
  exact hv1

end DriftE

end RBM
