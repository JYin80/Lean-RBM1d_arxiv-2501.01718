/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Index
import RBM1D.Defs.Semicircle
import RBM1D.Propagator.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

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
* `RBM.primInit`, `RBM.IsPrimitive` : the initial value and Definition 2.12 as a predicate;
  `m : Bool → ℂ` (the paper's `m(σ)` of (2.42)) is a parameter
* `RBM.kTwo`, `RBM.hasDerivAt_kTwo`, `RBM.kTwo_zero` : **Example 2.15**, (2.57) solves (2.55)
  with the initial value of Definition 2.12
* `RBM.hasDerivAt_kTwoLoop` : the same in the general form (2.48) at `n = 2`
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

/-- The initial value in Definition 2.12: `K_{0,σ,a} = W^{-n+1} ∏_k m(σ_k) 1(a₁ = ⋯ = aₙ)`. -/
noncomputable def primInit (W : ℕ) (m : Bool → ℂ) (I : LoopIdx (ZMod L)) : ℂ :=
  (W : ℂ)⁻¹ ^ (I.length - 1) * (I.σ.map m).prod *
    (if ∀ x ∈ I.a, ∀ y ∈ I.a, x = y then 1 else 0)

/-- **Definition 2.12.**  `K` solves the primitive equation (2.48) at the times `T`, with
the initial value `primInit` at `t = 0`, and `K_{t,±,a} = m(±)` for loops of length `1`.
The case `n = 1` is imposed separately: for `n = 1` the sum in (2.48) is empty. -/
def IsPrimitive (W : ℕ) (m : Bool → ℂ) (T : Set ℝ) (K : ℝ → LoopIdx (ZMod L) → ℂ) : Prop :=
  (∀ t ∈ T, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length →
      HasDerivAt (fun s => K s I) (primRhs L W (K t) I) t) ∧
  (∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length → K 0 I = primInit L W m I) ∧
  (∀ t ∈ T, ∀ (s : Bool) (a : ZMod L), K t ⟨[s], [a]⟩ = m s)

section Example215

/-- (2.57): `K_{t,σ,(a₁,a₂)} = W⁻¹ m₁ m₂ (Θ^{(B)}_{t m₁ m₂})_{a₁ a₂}`, `mᵢ = m(σᵢ)`. -/
noncomputable def kTwo (W : ℕ) (m : Bool → ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a₁ a₂ : ZMod L) : ℂ :=
  (W : ℂ)⁻¹ * (m σ₁ * m σ₂) * Theta L (t * (m σ₁ * m σ₂)) a₁ a₂

theorem Theta_zero : Theta L 0 = 1 := by
  simp [Theta]

/-- **Example 2.15**: (2.57) solves (2.55) wherever `‖t m₁ m₂‖ < 1`. -/
theorem hasDerivAt_kTwo (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ) {t : ℝ}
    (σ₁ σ₂ : Bool) (ht : ‖(t : ℂ) * (m σ₁ * m σ₂)‖ < 1) (a₁ a₂ : ZMod L) :
    HasDerivAt (fun s => kTwo L W m s σ₁ σ₂ a₁ a₂)
      ((W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
        kTwo L W m t σ₁ σ₂ a₁ a * SB L a b * kTwo L W m t σ₁ σ₂ b a₂) t := by
  set μ := m σ₁ * m σ₂ with hμ
  have h1 := hasDerivAt_Theta_apply L hL ht a₁ a₂
  have h2 : HasDerivAt (fun ζ : ℂ => ζ * μ) μ (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).mul_const μ
  have h3 := ((h1.comp (t : ℂ) h2).comp_ofReal).const_mul ((W : ℂ)⁻¹ * μ)
  refine h3.congr_deriv ?_
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  simp only [kTwo, ← hμ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  field_simp

/-- Example 2.15 with the paper's `m(σ)` at energy `|E| ≤ 2` (`RBM.mSigma`): since
`|m^{(E)}| = 1`, the hypothesis `‖t m₁ m₂‖ < 1` is just `0 ≤ t < 1`. -/
theorem hasDerivAt_kTwo_mSigma (hL : 3 ≤ L) (W : ℕ) [NeZero W] {E t : ℝ} (hE : |E| ≤ 2)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (σ₁ σ₂ : Bool) (a₁ a₂ : ZMod L) :
    HasDerivAt (fun s => kTwo L W (mSigma E) s σ₁ σ₂ a₁ a₂)
      ((W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
        kTwo L W (mSigma E) t σ₁ σ₂ a₁ a * SB L a b * kTwo L W (mSigma E) t σ₁ σ₂ b a₂) t :=
  hasDerivAt_kTwo L hL W (mSigma E) σ₁ σ₂ (norm_mul_mSigma_lt_one hE ht0 ht1 σ₁ σ₂) a₁ a₂

/-- At `t = 0`, (2.57) is the initial value of Definition 2.12 for `n = 2`. -/
theorem kTwo_zero (W : ℕ) (m : Bool → ℂ) (σ₁ σ₂ : Bool) (a₁ a₂ : ZMod L) :
    kTwo L W m 0 σ₁ σ₂ a₁ a₂ = primInit L W m ⟨[σ₁, σ₂], [a₁, a₂]⟩ := by
  have hall : (∀ x ∈ [a₁, a₂], ∀ y ∈ [a₁, a₂], x = y) ↔ a₁ = a₂ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨-, h⟩, -⟩
      exact h
    · rintro rfl
      simp
  simp only [kTwo, primInit, Complex.ofReal_zero, zero_mul, Theta_zero, Matrix.one_apply,
    LoopIdx.length, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, hall]
  split_ifs <;> ring

/-- (2.57) as a function of the loop index, zero off loops of length `2`. -/
noncomputable def kTwoLoop (W : ℕ) (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (ZMod L)) : ℂ :=
  match I.σ, I.a with
  | [σ₁, σ₂], [a₁, a₂] => kTwo L W m t σ₁ σ₂ a₁ a₂
  | _, _ => 0

/-- **Example 2.15, general form**: (2.57) satisfies (2.48) at `n = 2`, with the right-hand
side built from the cut-and-glue operators. -/
theorem hasDerivAt_kTwoLoop (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ) {t : ℝ}
    (σ₁ σ₂ : Bool) (ht : ‖(t : ℂ) * (m σ₁ * m σ₂)‖ < 1) (a₁ a₂ : ZMod L) :
    HasDerivAt (fun s => kTwoLoop L W m s ⟨[σ₁, σ₂], [a₁, a₂]⟩)
      (primRhs L W (kTwoLoop L W m t) ⟨[σ₁, σ₂], [a₁, a₂]⟩) t := by
  rw [primRhs_two]
  exact hasDerivAt_kTwo L hL W m σ₁ σ₂ ht a₁ a₂

/-- (2.58), `σ = (+,-)`: `K_{t,σ,(a,b)} = W⁻¹ |m|² ((1 - t|m|² S^(B))⁻¹)_{ab}`. -/
example (W : ℕ) (m₀ : ℂ) (t : ℝ) (a b : ZMod L) :
    kTwo L W (fun s => if s then m₀ else (starRingEnd ℂ) m₀) t true false a b
      = (W : ℂ)⁻¹ * (Complex.normSq m₀ : ℂ)
        * Ring.inverse (1 - ((t : ℂ) * (Complex.normSq m₀ : ℂ)) • SB L) a b := by
  simp [kTwo, Theta, Complex.mul_conj]

/-- (2.58), `σ = (+,+)`: `K_{t,σ,(a,b)} = W⁻¹ m² ((1 - t m² S^(B))⁻¹)_{ab}`. -/
example (W : ℕ) (m₀ : ℂ) (t : ℝ) (a b : ZMod L) :
    kTwo L W (fun s => if s then m₀ else (starRingEnd ℂ) m₀) t true true a b
      = (W : ℂ)⁻¹ * m₀ ^ 2 * Ring.inverse (1 - ((t : ℂ) * m₀ ^ 2) • SB L) a b := by
  simp [kTwo, Theta, sq]

end Example215

end RBM
