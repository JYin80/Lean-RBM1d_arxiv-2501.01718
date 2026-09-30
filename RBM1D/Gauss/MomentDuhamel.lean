/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.EEBridge
import RBM1D.Gauss.MomentDuhamelEEFunCore

/-!
# The moment Duhamel: the deterministic objects, the propagator's time derivative

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2: the deterministic objects of **(5.20) and (5.24) in moment form**.  The moment
route has no martingale at all, and the drift is pinned down by a **pointwise identity in
`(u, M)`**.

## Main definitions

* `RBM.MomentDuhamel.lkFun` — `(L - K)_{u,σ,a}` as a *deterministic* function of the time `u`
  and the matrix `M`, with no `ω` anywhere; along a flow it is `RBM.SumZeroDyn.lkT`, by `rfl`.
* `RBM.MomentDuhamel.eeFun` — the `E ⊗ E` of Definition 5.4 as a *deterministic* function of
  `(u, M)`.  It is a definition, not an interface field.
* `RBM.MomentDuhamel.EEpath` — `E ⊗ E` read along a flow.

## Main results

* `RBM.hasDerivAt_edgeKer` — **`∂_u U_{u,v}` is elementary.**  The running time `u` occurs in
  (5.17) only through `1 - (u ξ) S^{(B)}` (`RBM.edgeKer`), which is *affine* in `u`; so
  `u ↦ U_{u,v}` is a product of affine factors and its derivative needs no propagator ODE, no
  `RBM1D/Propagator/Deriv.lean`, and no hypothesis at all (not even `‖v ξ‖ < 1`).

## What this file does *not* do

Nothing here assumes `RBM.Gauss.MatrixStein`.  Nothing here is an `axiom` and nothing here is
`sorry`.
-/

namespace RBM

open MeasureTheory Filter Real

/-! ### `∂_u U_{u,v}`: the propagator's time derivative is elementary -/

section Propagator

variable (L : ℕ) [NeZero L]

/-- **`∂_s edgeKer L ξ s t = -ξ (S^{(B)} Θ(tξ))`**, with *no* hypotheses whatsoever — in
particular without `‖t ξ‖ < 1`.

The point is (5.17)'s shape: `edgeKer L ξ s t = (1 - (s ξ) • S^{(B)}) * Θ(t ξ)` has the
running time `s` only in the *affine* first factor. -/
theorem hasDerivAt_edgeKer (ξ t : ℂ) (x y : ZMod L) (s : ℝ) :
    HasDerivAt (fun r : ℝ => edgeKer L ξ (r : ℂ) t x y)
      (-(ξ * (SB L * Theta L (t * ξ)) x y)) s := by
  have h : ∀ r : ℝ, edgeKer L ξ (r : ℂ) t x y
      = (Theta L (t * ξ)) x y - (r : ℂ) * (ξ * (SB L * Theta L (t * ξ)) x y) := by
    intro r
    simp only [edgeKer, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_mul,
      Matrix.smul_apply, smul_eq_mul]
    ring
  simp only [h]
  have hc : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
  have h2 : HasDerivAt
      (fun r : ℝ => (Theta L (t * ξ)) x y - (r : ℂ) * (ξ * (SB L * Theta L (t * ξ)) x y))
      (0 - 1 * (ξ * (SB L * Theta L (t * ξ)) x y)) s :=
    (hasDerivAt_const s _).sub (hc.mul_const _)
  convert h2 using 1
  ring

end Propagator

/-! ### `(L - K)` as a deterministic function of `(u, M)` -/

namespace MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`(L - K)_{u,σ,a}` as a function of the time and the matrix**, with no `ω`.

This is the object the pointwise drift identity of (5.15) is about; `RBM.SumZeroDyn.lkT` is
its value along a flow (by `rfl`). -/
noncomputable def lkFun (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) : ℂ :=
  gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (σ, a))
    - B.Kval E N u (LoopData.idx (σ, a))

/-! ### The primed interface -/

namespace Hyp

variable {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

end Hyp

/-- **`E ⊗ E` read along the flow.**  It is a *definition*, not an interface field. -/
noncomputable def EEpath (X : Sample B) (E : ℝ) (n : ℕ) :
    ∀ N, ℝ → Ω → (Fin (n + 2) → Bool) → LoopArg (B.L N) ((n + 2) + (n + 2)) → ℂ :=
  fun N u ω σ c => eeFun B E N u (X.H N u ω) σ c

/-! ### From `‖·‖_{2p}` bounds to `≺` -/

end MomentDuhamel

end RBM
