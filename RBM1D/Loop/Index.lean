/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.ZMod.Defs

/-!
# Index data of `G`-loops and the cut-and-glue operators

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definitions 2.9 and 2.10,
at the level of index data only (no Green's functions).

An `n`-`G` loop `L_{t,σ,a} = ⟨∏_{i=1}^n G_t(σ_i) E_{a_i}⟩` (2.41) is determined by the
charges `σ = (σ_1, …, σ_n)`, `σ_i ∈ {+, -}`, and the block labels `a = (a_1, …, a_n)`.
We store them as two lists, with `true` for `+`; `RBM.LoopIdx.WF` says they have the
same length.  Labels live in an arbitrary type `α`; the paper uses `α = ZMod L`.

The operators of Definition 2.10 take the paper's `1`-based indices `k`, `l`:

* `cutGlue k b`     : `G^{(b)}_k`, replace `G(σ_k)` by `G(σ_k) E_b G(σ_k)`
* `cutGlueL k l b`  : `G^{(b),L}_{k,l}`, keep the chain through `E_{a_n}`, glue with `E_b`
* `cutGlueR k l b`  : `G^{(b),R}_{k,l}`, keep the other chain, glue with `E_b`

## Main results

* `length_cutGlue`, `length_cutGlueL`, `length_cutGlueR` : the lengths `n + 1`,
  `k + n - l + 1`, `l - k + 1`
* `length_cutGlueL_add_length_cutGlueR` : the two chains have total length `n + 2`,
  which is why (2.48) is quadratic
* `length_cutGlueL_le`, `length_cutGlueR_le` : both are at most `n`; equality for the
  right loop at `k = 1, l = n`
* `WF` is preserved by all three operators
* the examples of Figures 1–3
-/

namespace RBM

/-- Index data `(σ, a)` of a `G`-loop: charges (`true` for `+`) and block labels. -/
@[ext]
structure LoopIdx (α : Type*) where
  σ : List Bool
  a : List α
  deriving DecidableEq

namespace LoopIdx

variable {α : Type*}

/-- Well-formedness: as many charges as labels. -/
def WF (x : LoopIdx α) : Prop := x.σ.length = x.a.length

/-- The number of `G` edges `n`. -/
def length (x : LoopIdx α) : ℕ := x.a.length

/-- `G^{(b)}_k` (Definition 2.10 (1)), `1 ≤ k ≤ n`: cut the `k`-th `G` edge and glue
the two new ends with `E_b`.  `σ' = (σ_1, …, σ_k, σ_k, …, σ_n)`,
`a' = (a_1, …, a_{k-1}, b, a_k, …, a_n)`. -/
def cutGlue (k : ℕ) (b : α) (x : LoopIdx α) : LoopIdx α where
  σ := x.σ.take k ++ x.σ.drop (k - 1)
  a := x.a.take (k - 1) ++ b :: x.a.drop (k - 1)

/-- `G^{(b),L}_{k,l}` (Definition 2.10 (2)), `1 ≤ k < l ≤ n`: cut the `k`-th and `l`-th
`G` edges and close up the chain containing `E_{a_n}`, inserting `E_b`.
`σ' = (σ_1, …, σ_k, σ_l, …, σ_n)`, `a' = (a_1, …, a_{k-1}, b, a_l, …, a_n)`. -/
def cutGlueL (k l : ℕ) (b : α) (x : LoopIdx α) : LoopIdx α where
  σ := x.σ.take k ++ x.σ.drop (l - 1)
  a := x.a.take (k - 1) ++ b :: x.a.drop (l - 1)

/-- `G^{(b),R}_{k,l}` (Definition 2.10 (3)), `1 ≤ k < l ≤ n`: close up the chain not
containing `E_{a_n}`, inserting `E_b`.  `σ' = (σ_k, …, σ_l)`, `a' = (a_k, …, a_{l-1}, b)`. -/
def cutGlueR (k l : ℕ) (b : α) (x : LoopIdx α) : LoopIdx α where
  σ := (x.σ.drop (k - 1)).take (l - k + 1)
  a := (x.a.drop (k - 1)).take (l - k) ++ [b]

section Length

variable (x : LoopIdx α) (b : α) {k l : ℕ}

theorem length_cutGlue (hk : k ≤ x.length) : (x.cutGlue k b).length = x.length + 1 := by
  simp only [length, cutGlue, List.length_append, List.length_take, List.length_cons,
    List.length_drop] at hk ⊢
  omega

theorem length_cutGlueL (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueL k l b).length = k + x.length - l + 1 := by
  simp only [length, cutGlueL, List.length_append, List.length_take, List.length_cons,
    List.length_drop] at hl ⊢
  omega

theorem length_cutGlueR (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueR k l b).length = l - k + 1 := by
  simp only [length, cutGlueR, List.length_append, List.length_take, List.length_drop,
    List.length_singleton] at hl ⊢
  omega

/-- The two loops produced by cutting at `k < l` have total length `n + 2`. -/
theorem length_cutGlueL_add_length_cutGlueR (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueL k l b).length + (x.cutGlueR k l b).length = x.length + 2 := by
  rw [length_cutGlueL x b hk hkl hl, length_cutGlueR x b hk hkl hl]
  omega

/-- The left loop is no longer than the original. -/
theorem length_cutGlueL_le (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueL k l b).length ≤ x.length := by
  rw [length_cutGlueL x b hk hkl hl]
  omega

/-- The right loop is no longer than the original. -/
theorem length_cutGlueR_le (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueR k l b).length ≤ x.length := by
  rw [length_cutGlueR x b hk hkl hl]
  omega

/-- The bound `length_cutGlueR_le` is attained: at `k = 1, l = n` the right loop has
the full length `n`, so an induction on `K` cannot simply use the length. -/
theorem length_cutGlueR_one (hn : 2 ≤ x.length) :
    (x.cutGlueR 1 x.length b).length = x.length := by
  rw [length_cutGlueR x b le_rfl (by omega) le_rfl]
  omega

/-- Both loops have length at least `2`. -/
theorem two_le_length_cutGlueL (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    2 ≤ (x.cutGlueL k l b).length := by
  rw [length_cutGlueL x b hk hkl hl]
  omega

theorem two_le_length_cutGlueR (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    2 ≤ (x.cutGlueR k l b).length := by
  rw [length_cutGlueR x b hk hkl hl]
  omega

end Length

section WF

variable {x : LoopIdx α} (b : α) {k l : ℕ}

theorem WF.cutGlue (hx : x.WF) (hk1 : 1 ≤ k) (hk : k ≤ x.length) : (x.cutGlue k b).WF := by
  simp only [WF, length, LoopIdx.cutGlue, List.length_append, List.length_take,
    List.length_cons, List.length_drop] at hx hk ⊢
  omega

theorem WF.cutGlueL (hx : x.WF) (hk1 : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueL k l b).WF := by
  simp only [WF, length, LoopIdx.cutGlueL, List.length_append, List.length_take,
    List.length_cons, List.length_drop] at hx hl ⊢
  omega

theorem WF.cutGlueR (hx : x.WF) (hk1 : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueR k l b).WF := by
  simp only [WF, length, LoopIdx.cutGlueR, List.length_append, List.length_take,
    List.length_drop, List.length_singleton] at hx hl ⊢
  omega

end WF

section Labels

variable (x : LoopIdx α) (b : α) {k l : ℕ}

/-- The left loop always contains `E_{a_n}`: its last label is `a_n`. -/
theorem getLast?_cutGlueL (hkl : k < l) (hl : l ≤ x.length) :
    (x.cutGlueL k l b).a.getLast? = x.a.getLast? := by
  have hne : x.a.drop (l - 1) ≠ [] := by
    simp only [length] at hl
    simp only [ne_eq, List.drop_eq_nil_iff, not_le]
    omega
  simp only [cutGlueL]
  rw [show x.a.take (k - 1) ++ b :: x.a.drop (l - 1)
      = (x.a.take (k - 1) ++ [b]) ++ x.a.drop (l - 1) by simp]
  conv_rhs => rw [← List.take_append_drop (l - 1) x.a]
  simp only [List.getLast?_append, List.getLast?_eq_some_getLast hne, Option.some_or]

/-- For `k ≥ 2` the left loop also starts with `E_{a_1}`. -/
theorem head?_cutGlueL_of_two_le (hk : 2 ≤ k) (hkn : k ≤ x.length) :
    (x.cutGlueL k l b).a.head? = x.a.head? := by
  obtain ⟨σ, a⟩ := x
  cases a with
  | nil => simp [length] at hkn; omega
  | cons h t =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    simp [cutGlueL]

/-- For `k = 1` the left loop starts with the new label `b`, not with `a_1`: the chain
through `E_{a_n}` is `E_{a_l}, …, E_{a_n}` and does not reach `E_{a_1}`.
(The remark after Definition 2.10 that `a_1` always stays in the left loop needs `k ≥ 2`;
see `docs/paper-deltas.md`.) -/
theorem head?_cutGlueL_one : (x.cutGlueL 1 l b).a.head? = some b := by
  simp [cutGlueL]

end Labels

section Examples

variable {L : ℕ} (σ₁ σ₂ σ₃ σ₄ σ₅ : Bool) (a a₁ a₂ a₃ a₄ a₅ : ZMod L)

/-- Figure 1: `G^{(a)}_2` on a loop of length `4`. -/
example : (LoopIdx.mk [σ₁, σ₂, σ₃, σ₄] [a₁, a₂, a₃, a₄]).cutGlue 2 a
    = ⟨[σ₁, σ₂, σ₂, σ₃, σ₄], [a₁, a, a₂, a₃, a₄]⟩ := rfl

/-- Figure 2: `G^{(a),L}_{3,5}` on a loop of length `5`. -/
example : (LoopIdx.mk [σ₁, σ₂, σ₃, σ₄, σ₅] [a₁, a₂, a₃, a₄, a₅]).cutGlueL 3 5 a
    = ⟨[σ₁, σ₂, σ₃, σ₅], [a₁, a₂, a, a₅]⟩ := rfl

/-- Figure 3: `G^{(a),R}_{3,5}` on a loop of length `5`. -/
example : (LoopIdx.mk [σ₁, σ₂, σ₃, σ₄, σ₅] [a₁, a₂, a₃, a₄, a₅]).cutGlueR 3 5 a
    = ⟨[σ₃, σ₄, σ₅], [a₃, a₄, a]⟩ := rfl

end Examples

end LoopIdx

end RBM
