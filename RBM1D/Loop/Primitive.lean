/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Index
import RBM1D.Propagator.Deriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The primitive equation

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 2.12 and
Example 2.15.

The primitive loop `K_{t,σ,a}` solves (2.48):
`d/dt K_{t,σ,a} = W ∑_{1≤k<l≤n} ∑_{a,b} (G^{(a),L}_{k,l} ∘ K_{t,σ,a}) S^(B)_{ab} (G^{(b),R}_{k,l} ∘ K_{t,σ,a})`,
where `G ∘ K_{t,σ,a} = K_{t, G(σ,a)}` (2.49).

## Main results

* `RBM.primRhs`       : the right-hand side of (2.48) for a given `K : LoopIdx (ZMod L) → ℂ`
* `RBM.primRhs_two`   : at `n = 2` it is (2.55); this is the index check between
  `RBM.LoopIdx.cutGlueL`/`cutGlueR` and the paper's own expansion
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

/-- The right-hand side of (2.48):
`W ∑_{1≤k<l≤n} ∑_{a,b} K(G^{(a),L}_{k,l}(σ,a)) S^(B)_{ab} K(G^{(b),R}_{k,l}(σ,a))`. -/
noncomputable def primRhs (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) : ℂ :=
  (W : ℂ) * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
    K (I.cutGlueL k l a) * SB L a b * K (I.cutGlueR k l b)

/-- **Index check.** At `n = 2` the general right-hand side of (2.48), built from
`cutGlueL`/`cutGlueR`, is exactly (2.55):
`W ∑_{a,b} K_{σ,(a₁,a)} S^(B)_{ab} K_{σ,(b,a₂)}`.

The operators produce `∑_{a,b} K_{σ,(a,a₂)} S_{ab} K_{σ,(a₁,b)}`; the two agree after
swapping the dummy indices `a ↔ b`, using the symmetry of `S^(B)`. -/
theorem primRhs_two (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (σ₁ σ₂ : Bool) (a₁ a₂ : ZMod L) :
    primRhs L W K ⟨[σ₁, σ₂], [a₁, a₂]⟩
      = (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
          K ⟨[σ₁, σ₂], [a₁, a]⟩ * SB L a b * K ⟨[σ₁, σ₂], [b, a₂]⟩ := by
  have h12 : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have h1 : Ioc 1 2 = ({2} : Finset ℕ) := by decide
  have h2 : Ioc 2 2 = (∅ : Finset ℕ) := by decide
  have hlen : (LoopIdx.mk [σ₁, σ₂] [a₁, a₂]).length = 2 := rfl
  rw [primRhs, hlen, h12, Finset.sum_pair (by norm_num), h1, h2, Finset.sum_singleton,
    Finset.sum_empty, add_zero]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hS : SB L b a = SB L a b := congrFun (congrFun (SB_transpose L) a) b
  change K ⟨[σ₁, σ₂], [b, a₂]⟩ * SB L b a * K ⟨[σ₁, σ₂], [a₁, a]⟩ = _
  rw [hS]
  ring

end RBM
