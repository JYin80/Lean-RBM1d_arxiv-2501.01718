/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Lemma57
import RBM1D.Gauss.MomentDuhamel

/-!
# (5.36) applied to the pinned `E ⊗ E`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (5.22) and (5.36).

(5.36) is a pointwise inequality about a real number `EE` that is tied to the `b`-sum of
(5.22) through

`EE ≤ W * ∑ b, L^{(1)}(b)`.

This file proves that inequality for the concrete `E ⊗ E`: `RBM.MomentDuhamel.EEpath` is a
**definition**, and (5.22) is the theorem `RBM.EEBridge.eeEdge_eq_sum_gloop`; `L^{(1)}` is
defined too.  It then proves the estimates (5.65), (5.66) and (5.72) for the two glued
`6`-loops of Figure 14 on which the proof of (5.36) runs.  The assembled bound, (5.36) for
`‖RBM.MomentDuhamel.EEpath …‖`, is `RBM.EEDef.ee_le_EEpath_sym'` in
`RBM1D/Gauss/NearFieldRemainder.lean`, through `RBM.Lemma57.ee_le_sym'`.

## Main results

* `RBM.EEDef.glueSum` — `L^{(1)}(b)` of (5.22), **defined**: `∑_k ∑_{b'} |S^{(B)}_{bb'}|
  ‖L_{glue(I,I',k,b,b')}‖`, the `(2n+2)`-loop of (5.23) summed over the cut edge `k` and the
  second glue label `b'`.
* `RBM.EEDef.norm_eeTens_le_W_sum` — **(5.22) as a `b`-sum**:
  `‖(E⊗E)_{σ,a,a'}‖ ≤ W ∑_b L^{(1)}(b)`, via `eeEdge_eq_sum_SB` and `glueLoop_loopCut`.
* `RBM.EEDef.eeL6`, `RBM.EEDef.norm_eeFun_le_W_sum`, `RBM.EEDef.norm_EEpath_le_W_sum` — the
  same for the pinned `E ⊗ E` along the flow.
* `RBM.EEDef.eeL6k`, `RBM.EEDef.eeL6_two_eq`, `RBM.EEDef.glueIdx_two_zero`,
  `RBM.EEDef.glueIdx_two_one` — the `k`-sum of (5.22) at `n = 0` and the two explicit
  glued `6`-loops of Figure 14.
* `RBM.EEDef.eeL6k_two_one_le`, `RBM.EEDef.eeL6k_two_zero_le` — **(5.65) + (5.66)** for each
  summand of (5.22), with the loop cut at the glue label `b`.
* `RBM.EEDef.eeL6k_two_one_le_glue`, `RBM.EEDef.eeL6k_two_zero_le_glue` — **(5.65) +
  (5.72)** for each summand, with the glued factor bounded entrywise.
* `RBM.EEDef.eeL6k_two_one'_le`, `RBM.EEDef.eeL6k_two_zero'_le` — **(5.66)** for each summand,
  with the loop cut at the second glue label `b'`.
* `RBM.EEDef.eeL6_two_le_near₁`, `RBM.EEDef.eeL6_two_le_near₂`, `RBM.EEDef.eeL6_two_le_far` —
  the three cases of the `b`-sum in the proof of (5.36) (`b` near `a₁`, near `a₂`, far from
  both), for both terms of (5.22).

## Every term is a definition

Every quantity on the left of these bounds is a definition: `RBM.MomentDuhamel.EEpath` is
`RBM.EEBridge.eeArg`, that is `RBM.Gauss.eeTens` of Definition 5.4, evaluated at the flow's own
matrix `X.H N u ω` and spectral parameter `z_u`.  The `b`-sum on the right is `eeL6`, again a
definition, and the inequality between them is a theorem, not an assumption.
-/

namespace RBM
namespace EEDef

open Matrix Finset Gauss EEBridge MomentDuhamel

/-! ### (5.22) as the `b`-sum that (5.36) consumes -/

section Generic

variable {d : Dims} {N : ℕ} {z : ℂ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}

/-- **`L^{(1)}(b)` of (5.22)**: the glued `(2n+2)`-loop of (5.23), summed over the cut edge `k`
and over the second glue label `b'` against the weight `S^{(B)}_{bb'}`.

The factor `W` of (5.22) is *not* included; it sits in front of the `b`-sum, where
(5.36) expects it. -/
noncomputable def glueSum (d : Dims) (N : ℕ) (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I I' : LoopIdx (ZMod (d.L N))) (m : ℕ) (b : ZMod (d.L N)) : ℝ :=
  ∑ k ∈ Finset.range m, ∑ b' : ZMod (d.L N),
    ‖SB (d.L N) b b'‖ * ‖gloop (d.L N) (d.W N) M z (glueIdx I I' k b b')‖

/-- **(5.22) in the shape (5.36) consumes it**:
`‖(E⊗E)_{σ,a,a'}‖ ≤ W ∑_b L^{(1)}(b)`.

`RBM.Gauss.eeTens` is the `k`-sum of `RBM.Gauss.eeEdge` over the `n` edges of the loop, and
each edge is `W ∑_{b,b'} S^{(B)}_{bb'} · L_{glue}` by `eeEdge_eq_sum_SB` read through
the gluing identity (`RBM.EEBridge.eeEdge_eq_sum_gloop`).  Taking norms and exchanging the
`k`- and `b`-sums is all that happens here. -/
theorem norm_eeTens_le_W_sum (hM : M.IsHermitian) (I I' : LoopIdx (ZMod (d.L N))) {m : ℕ}
    (hm : I.length = m) :
    ‖eeTens d N z M I I'‖
      ≤ (d.W N : ℝ) * ∑ b : ZMod (d.L N), glueSum d N z M I I' m b := by
  classical
  subst hm
  have hsum : eeTens d N z M I I'
      = ∑ k ∈ Finset.range I.length, eeEdge d N z M I I' k := rfl
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hstep : ∀ k ∈ Finset.range I.length,
      ‖eeEdge d N z M I I' k‖
        ≤ (d.W N : ℝ) * ∑ b : ZMod (d.L N), ∑ b' : ZMod (d.L N),
            ‖SB (d.L N) b b'‖ * ‖gloop (d.L N) (d.W N) M z (glueIdx I I' k b b')‖ := by
    intro k _
    rw [eeEdge_eq_sum_gloop hM I I' k, norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => le_of_eq (norm_mul _ _))
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
  unfold glueSum
  rw [Finset.sum_comm]

end Generic

/-! ### The same for the pinned `E ⊗ E` along the flow -/

section Path

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`L^{(1)}(b)` of (5.22) for the `E ⊗ E` of the flow**, `RBM.EEDef.glueSum` at the matrix
`H_u` and the spectral parameter `z_u`, with the two loops the two halves of the doubled
argument `c`. -/
noncomputable def eeL6 (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) (b : ZMod (B.L N)) : ℝ :=
  ∑ k ∈ Finset.range m, ∑ b' : ZMod (B.L N),
    ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) k b b')‖

theorem eeL6_eq_glueSum (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) (b : ZMod (B.L N)) :
    eeL6 X E N u ω σ c b
      = glueSum B.toDims N (zt E u) (X.H N u ω)
          (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) m b := rfl

/-- **(5.22) for `RBM.MomentDuhamel.eeFun`.** -/
theorem norm_eeFun_le_W_sum (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) :
    ‖eeFun B E N u (X.H N u ω) σ c‖
      ≤ (B.W N : ℝ) * ∑ b : ZMod (B.L N), eeL6 X E N u ω σ c b := by
  have h := norm_eeTens_le_W_sum (d := B.toDims) (N := N) (z := zt E u)
      (M := X.H N u ω) (X.hermitian N u ω)
      (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) (m := m) (toIdx_length _ _)
  simp only [eeL6_eq_glueSum]
  exact h

/-- **(5.22) for the pinned `E ⊗ E`, `RBM.MomentDuhamel.EEpath`.**  This is the inequality
`EE ≤ W ∑_b L^{(1)}(b)` from which (5.36) starts. -/
theorem norm_EEpath_le_W_sum (X : Sample B) (E : ℝ) {n N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (n + 2) → Bool) (c : LoopArg (B.L N) ((n + 2) + (n + 2))) :
    ‖MomentDuhamel.EEpath X E n N u ω σ c‖
      ≤ (B.W N : ℝ) * ∑ b : ZMod (B.L N), eeL6 X E N u ω σ c b :=
  norm_eeFun_le_W_sum X E N u ω σ c

theorem one_le_W (B : Band Ω) (N : ℕ) : 1 ≤ (B.W N : ℝ) := by
  exact_mod_cast B.W_pos N

end Path

/-! ### (5.36) for the pinned `E ⊗ E` -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The first label of the `2`-loop carried by a doubled loop argument. -/
def lab₁ {L : ℕ} (c : LoopArg L (2 + 2)) : ZMod L := leftArg c 0

/-- The second label of the `2`-loop carried by a doubled loop argument. -/
def lab₂ {L : ℕ} (c : LoopArg L (2 + 2)) : ZMod L := leftArg c 1

/-! ### The surviving hypotheses are consistent

A theorem whose hypotheses cannot all hold at once is vacuous; this section checks that the
surviving hypotheses can.

The witness is uniform in everything: `ℓ_u = ℓ_s = 1`, `D = 0`, `η_u = (W(1+S))^{-1}` with
`S = ∑_b L^{(1)}(b)` — so that `A_u = W ℓ_u η_u = (1+S)^{-1}` and the (2.73) budget
`A_u^{-5} = (1+S)^5` is above `S` — and `Gsq` taken to saturate (4.2).  It is *not* the regime
of the paper (there `A_u → ∞`); it only certifies that the six hypotheses are jointly
satisfiable for the **concrete** `eeL6`, which is what could have broken when `L^{(1)}` stopped
being a parameter. -/

end Main


/-! ### (5.65)-(5.66) and (5.72) for the glued `6`-loop

`RBM.EEDef.eeL6` is by *definition* the sum over `k ∈ range m` of (5.22).  At `m = 2` — the
`2`-loop that (5.36) is about — that sum has the two terms of Figure 14, and
`RBM.EEDef.glueIdx_two_zero` / `glueIdx_two_one` compute them: the glued `(2n+2)`-loop of
(5.23) is the explicit `6`-loop

`k = 1 :  ⟨[σ₂, σ₁, σ₂, -σ₂, -σ₁, -σ₂], [a₂, a₁, b, a₁', a₂', b']⟩`
`k = 0 :  ⟨[σ₁, σ₂, σ₁, -σ₁, -σ₂, -σ₁], [a₁, a₂, b, a₂', a₁', b']⟩`

with `a₁ = leftArg c 0`, `a₂ = leftArg c 1`, `aᵢ' = rightArg c (i-1)`.  Feeding these to
`RBM.Lemma57.norm_gloop_six_le_schwarz` (= (5.65) + (5.66)) and
`RBM.Lemma57.norm_gloop_six_le_glue` (= (5.65) + (5.72)) gives the four estimates below.
-/

section Six

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The `k`-th summand of `RBM.EEDef.eeL6`, i.e. the `k`-th term of the `k`-sum of (5.22). -/
noncomputable def eeL6k (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) (k : ℕ) (b : ZMod (B.L N)) : ℝ :=
  ∑ b' : ZMod (B.L N),
    ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) k b b')‖

theorem eeL6_eq_sum_eeL6k (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) (b : ZMod (B.L N)) :
    eeL6 X E N u ω σ c b = ∑ k ∈ Finset.range m, eeL6k X E N u ω σ c k b := rfl

/-- At `m = 2` — the `2`-loop of (5.36) — the `k`-sum of (5.22) has exactly the two terms of
Figure 14. -/
theorem eeL6_two_eq (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2)) (b : ZMod (B.L N)) :
    eeL6 X E N u ω σ c b = eeL6k X E N u ω σ c 0 b + eeL6k X E N u ω σ c 1 b := by
  rw [eeL6_eq_sum_eeL6k, Finset.sum_range_succ, Finset.sum_range_one]

/-! ### (5.23) at `n = 0`: the two glued `6`-loops of Figure 14 -/

/-- **Figure 14, right (`k = 0`)**: cutting the first edge of the `2`-loop. -/
theorem glueIdx_two_zero {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2))
    (b b' : ZMod L) :
    glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 0 b b'
      = ⟨[σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)],
         [leftArg c 0, leftArg c 1, b, rightArg c 1, rightArg c 0, b']⟩ := by
  simp [glueIdx, cutPairs, pairs, pairAt, ofPairs, LoopData.idx, List.ofFn_succ]

/-- **Figure 14, left (`k = 1`)**: cutting the second edge of the `2`-loop. -/
theorem glueIdx_two_one {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2))
    (b b' : ZMod L) :
    glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 1 b b'
      = ⟨[σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)],
         [leftArg c 1, leftArg c 0, b, rightArg c 0, rightArg c 1, b']⟩ := by
  simp [glueIdx, cutPairs, pairs, pairAt, ofPairs, LoopData.idx, List.ofFn_succ]


/-! ### (5.65) + (5.66) for the two glued `6`-loops -/

variable (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)

/-- **(5.65) + (5.66) for the `k = 1` term of (5.22)** (Figure 14, left).

The four `G`-edges of (5.65) are `(a₁', a₂')`, `(a₂', b')`, `(b', a₂)`, `(a₂, a₁)`, so the two
edges that touch the glue label `b'` are attached to `a₂`; `S` bounds the `4`-loop
`L_{(σ₂,-σ₂,σ₂,-σ₂),(b,a₁',b,a₁)}` of (5.66), which is what (2.73) at `n = 4` estimates. -/
theorem norm_gloop_glue_two_one_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b b' : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[σ 1, !(σ 1), σ 1, !(σ 1)], [b, rightArg c 0, b, leftArg c 0]⟩).re ≤ S) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 1 b b')‖
      ≤ Gm (rightArg c 0) (rightArg c 1) * Gm (rightArg c 1) b'
        * Gm b' (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0) * √S := by
  rw [glueIdx_two_one]
  exact Lemma57.norm_gloop_six_le_schwarz (B.L N) (B.W N) (X.hermitian N u ω)
    (σ 1) (σ 0) (σ 1) (!(σ 0)) (!(σ 1))
    (leftArg c 1) (leftArg c 0) b (rightArg c 0) (rightArg c 1) b'
    (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _)
    (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
    (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp) hS

/-- **(5.65) + (5.66) for the `k = 0` term of (5.22)** (Figure 14, right).

Identical to `norm_gloop_glue_two_one_le` except that the two `G`-edges that touch the glue
label `b'` are attached to `a₁`, not `a₂`, and the `4`-loop of (5.66) is the one with
`a₂'`, `a₂` in place of `a₁'`, `a₁`.  This swap is the whole content of the `k = 1`/`k = 2`
symmetry of Figure 14. -/
theorem norm_gloop_glue_two_zero_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b b' : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[σ 0, !(σ 0), σ 0, !(σ 0)], [b, rightArg c 1, b, leftArg c 1]⟩).re ≤ S) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 0 b b')‖
      ≤ Gm (rightArg c 1) (rightArg c 0) * Gm (rightArg c 0) b'
        * Gm b' (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1) * √S := by
  rw [glueIdx_two_zero]
  exact Lemma57.norm_gloop_six_le_schwarz (B.L N) (B.W N) (X.hermitian N u ω)
    (σ 0) (σ 1) (σ 0) (!(σ 1)) (!(σ 0))
    (leftArg c 0) (leftArg c 1) b (rightArg c 1) (rightArg c 0) b'
    (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _)
    (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
    (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp) hS


/-! ### The `b'`-sum: (5.66) for the two summands of `eeL6` -/

/-- **(5.66) for the `k = 1` summand of `RBM.EEDef.eeL6`.**

The `b'`-sum is against `‖S^{(B)}_{bb'}‖`, whose row sums are `1`, so a bound `Kb` on the
product of the two `b'`-edges, valid on the (three-point) support of that row, passes through
unchanged.  `Kb` is the paper's `T_{u,D}(‖b - a₂‖)`-carrying factor of (5.67). -/
theorem eeL6k_two_one_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Kb S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hb' : ∀ b' : ZMod (B.L N), SB (B.L N) b b' ≠ 0 →
      Gm (rightArg c 1) b' * Gm b' (leftArg c 1) ≤ Kb)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[σ 1, !(σ 1), σ 1, !(σ 1)], [b, rightArg c 0, b, leftArg c 0]⟩).re ≤ S) :
    eeL6k X E N u ω σ c 1 b
      ≤ Gm (rightArg c 0) (rightArg c 1) * Kb * Gm (leftArg c 1) (leftArg c 0) * √S := by
  classical
  set C : ℝ := Gm (rightArg c 0) (rightArg c 1) * Kb * Gm (leftArg c 1) (leftArg c 0) * √S
    with hC
  have hstep : ∀ b' ∈ (Finset.univ : Finset (ZMod (B.L N))),
      ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
          (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 1 b b')‖
        ≤ ‖SB (B.L N) b b'‖ * C := by
    intro b' _
    by_cases h0 : SB (B.L N) b b' = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_gloop_glue_two_one_le X E N u ω σ c b b' hGm0 hGm hS).trans ?_
      rw [hC]
      have h1 := hb' b' h0
      have h2 : (0 : ℝ) ≤ √S := Real.sqrt_nonneg S
      have h3 := hGm0 (rightArg c 0) (rightArg c 1)
      have h4 := hGm0 (leftArg c 1) (leftArg c 0)
      have hexp : Gm (rightArg c 0) (rightArg c 1) * Gm (rightArg c 1) b'
          * Gm b' (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0) * √S
          = Gm (rightArg c 0) (rightArg c 1) * (Gm (rightArg c 1) b' * Gm b' (leftArg c 1))
            * Gm (leftArg c 1) (leftArg c 0) * √S := by ring
      rw [hexp]
      gcongr
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]

/-- **(5.66) for the `k = 0` summand of `RBM.EEDef.eeL6`** — the mirror image, with the two
`b'`-edges attached to `a₁`. -/
theorem eeL6k_two_zero_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Kb S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hb' : ∀ b' : ZMod (B.L N), SB (B.L N) b b' ≠ 0 →
      Gm (rightArg c 0) b' * Gm b' (leftArg c 0) ≤ Kb)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[σ 0, !(σ 0), σ 0, !(σ 0)], [b, rightArg c 1, b, leftArg c 1]⟩).re ≤ S) :
    eeL6k X E N u ω σ c 0 b
      ≤ Gm (rightArg c 1) (rightArg c 0) * Kb * Gm (leftArg c 0) (leftArg c 1) * √S := by
  classical
  set C : ℝ := Gm (rightArg c 1) (rightArg c 0) * Kb * Gm (leftArg c 0) (leftArg c 1) * √S
    with hC
  have hstep : ∀ b' ∈ (Finset.univ : Finset (ZMod (B.L N))),
      ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
          (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 0 b b')‖
        ≤ ‖SB (B.L N) b b'‖ * C := by
    intro b' _
    by_cases h0 : SB (B.L N) b b' = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_gloop_glue_two_zero_le X E N u ω σ c b b' hGm0 hGm hS).trans ?_
      rw [hC]
      have h1 := hb' b' h0
      have h2 : (0 : ℝ) ≤ √S := Real.sqrt_nonneg S
      have h3 := hGm0 (rightArg c 1) (rightArg c 0)
      have h4 := hGm0 (leftArg c 0) (leftArg c 1)
      have hexp : Gm (rightArg c 1) (rightArg c 0) * Gm (rightArg c 0) b'
          * Gm b' (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1) * √S
          = Gm (rightArg c 1) (rightArg c 0) * (Gm (rightArg c 0) b' * Gm b' (leftArg c 0))
            * Gm (leftArg c 0) (leftArg c 1) * √S := by ring
      rw [hexp]
      gcongr
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]


/-! ### (5.65) + (5.72): the Case-2(1b) route, with `G†E_bG` bounded entrywise -/

/-- **(5.72) for the `k = 1` summand of `RBM.EEDef.eeL6`.**

`K` bounds the glued factor `(G(σ₂)E_bG(-σ₂))_{x₁x₁'}` entrywise, via
`RBM.Lemma57.norm_mul_Eblk_mul_apply_le` — that is the paper's
`(G†E_bG)_{x₁x₁'} ≤ max_{y∈I_b}|G_{x₁y}||G_{x₁'y}|` followed by (4.2)+(5.31).  At `k = 1`
the free ends of that factor lie in the blocks `a₁`, `a₁'`, so `K` is the paper's
`J*_{u,D} T_{u,D}(‖b - a₁‖)`. -/
theorem eeL6k_two_one_le_glue (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Kb K : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y) (hK : 0 ≤ K)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hb' : ∀ b' : ZMod (B.L N), SB (B.L N) b b' ≠ 0 →
      Gm (rightArg c 1) b' * Gm b' (leftArg c 1) ≤ Kb)
    (hglue : ∀ p q y : ZMod (B.L N) × Fin (B.W N),
      p.1 = leftArg c 0 → q.1 = rightArg c 0 → y.1 = b →
      ‖Gsig (X.H N u ω) (zt E u) (σ 1) p y‖
        * ‖Gsig (X.H N u ω) (zt E u) (!(σ 1)) y q‖ ≤ K) :
    eeL6k X E N u ω σ c 1 b
      ≤ Gm (rightArg c 0) (rightArg c 1) * Kb * Gm (leftArg c 1) (leftArg c 0) * K := by
  classical
  set C : ℝ := Gm (rightArg c 0) (rightArg c 1) * Kb * Gm (leftArg c 1) (leftArg c 0) * K
    with hC
  have hstep : ∀ b' ∈ (Finset.univ : Finset (ZMod (B.L N))),
      ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
          (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 1 b b')‖
        ≤ ‖SB (B.L N) b b'‖ * C := by
    intro b' _
    by_cases h0 : SB (B.L N) b b' = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [glueIdx_two_one]
      refine (Lemma57.norm_gloop_six_le_glue (B.L N) (B.W N)
        (σ 1) (σ 0) (σ 1) (!(σ 1)) (!(σ 0)) (!(σ 1))
        (leftArg c 1) (leftArg c 0) b (rightArg c 0) (rightArg c 1) b'
        (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) hK
        (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
        (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp)
        (fun p q y hp hq hy => hglue p q y hp hq hy)).trans ?_
      rw [hC]
      have h1 := hb' b' h0
      have hexp : Gm (rightArg c 0) (rightArg c 1) * Gm (rightArg c 1) b'
          * Gm b' (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0) * K
          = Gm (rightArg c 0) (rightArg c 1) * (Gm (rightArg c 1) b' * Gm b' (leftArg c 1))
            * Gm (leftArg c 1) (leftArg c 0) * K := by ring
      rw [hexp]
      gcongr <;> exact hGm0 _ _
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]

/-- **(5.72) for the `k = 0` summand of `RBM.EEDef.eeL6`** — the mirror image: the free ends
of the glued factor lie in the blocks `a₂`, `a₂'`, so `K` is `J*_{u,D} T_{u,D}(‖b - a₂‖)`
while the `b'`-edges carry `‖b - a₁‖`.  The *product* of the two is the same as at `k = 1`,
so both summands of (5.22) satisfy a bound of the same shape. -/
theorem eeL6k_two_zero_le_glue (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Kb K : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y) (hK : 0 ≤ K)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hb' : ∀ b' : ZMod (B.L N), SB (B.L N) b b' ≠ 0 →
      Gm (rightArg c 0) b' * Gm b' (leftArg c 0) ≤ Kb)
    (hglue : ∀ p q y : ZMod (B.L N) × Fin (B.W N),
      p.1 = leftArg c 1 → q.1 = rightArg c 1 → y.1 = b →
      ‖Gsig (X.H N u ω) (zt E u) (σ 0) p y‖
        * ‖Gsig (X.H N u ω) (zt E u) (!(σ 0)) y q‖ ≤ K) :
    eeL6k X E N u ω σ c 0 b
      ≤ Gm (rightArg c 1) (rightArg c 0) * Kb * Gm (leftArg c 0) (leftArg c 1) * K := by
  classical
  set C : ℝ := Gm (rightArg c 1) (rightArg c 0) * Kb * Gm (leftArg c 0) (leftArg c 1) * K
    with hC
  have hstep : ∀ b' ∈ (Finset.univ : Finset (ZMod (B.L N))),
      ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
          (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 0 b b')‖
        ≤ ‖SB (B.L N) b b'‖ * C := by
    intro b' _
    by_cases h0 : SB (B.L N) b b' = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [glueIdx_two_zero]
      refine (Lemma57.norm_gloop_six_le_glue (B.L N) (B.W N)
        (σ 0) (σ 1) (σ 0) (!(σ 0)) (!(σ 1)) (!(σ 0))
        (leftArg c 0) (leftArg c 1) b (rightArg c 1) (rightArg c 0) b'
        (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) hK
        (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
        (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp)
        (fun p q y hp hq hy => hglue p q y hp hq hy)).trans ?_
      rw [hC]
      have h1 := hb' b' h0
      have hexp : Gm (rightArg c 1) (rightArg c 0) * Gm (rightArg c 0) b'
          * Gm b' (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1) * K
          = Gm (rightArg c 1) (rightArg c 0) * (Gm (rightArg c 0) b' * Gm b' (leftArg c 0))
            * Gm (leftArg c 0) (leftArg c 1) * K := by ring
      rw [hexp]
      gcongr <;> exact hGm0 _ _
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]


/-! ### The two summands together -/

end Six

/-! ### The second cut

The `6`-loop of (5.23) has **two** glue labels, `b` and `b'`.  The section above opens it at
`b`; `RBM.Lemma57.norm_gloop_six_le_schwarz'` opens it at `b'`, and the two openings leave
*different* four-edge products behind:

| term | cut | the four surviving edges | glued pair |
|---|---|---|---|
| `k = 1` | `b`  | `a₁'–a₂'`, `a₂'–b'`, `b'–a₂`, `a₂–a₁` | `a₁–b–a₁'` |
| `k = 1` | `b'` | `a₂–a₁`, `a₁–b`, `b–a₁'`, `a₁'–a₂'` | `a₂'–b'–a₂` |
| `k = 0` | `b`  | `a₂'–a₁'`, `a₁'–b'`, `b'–a₁`, `a₁–a₂` | `a₂–b–a₂'` |
| `k = 0` | `b'` | `a₁–a₂`, `a₂–b`, `b–a₂'`, `a₂'–a₁'` | `a₁'–b'–a₁` |

In the `k = 1` loop the label `b` meets only `a₁`-blocks and `b'` only `a₂`-blocks; in the
`k = 0` loop it is the other way round.  That is the exact content of the `k=1`/`k=2`
symmetry of Figure 14:

* for `b` near `a₁` (so far from `a₂`) the pair of `G`-edges that decays is the one joining
  the glue label to `a₂`, which is the `b'`-pair at `k = 1` (cut at `b`) and the `b`-pair at
  `k = 0` (**cut at `b'`**);
* for `b` near `a₂` the mirror image: cut `k = 0` at `b` and `k = 1` at `b'`.

Both halves therefore land on the *same* shape `Gsq(a₁,a₂)·Gsq(b,aᵢ)·μ`, with `i = 2` on the
first half and `i = 1` on the second — the two near-field hypotheses of
`RBM.Lemma57.ee_le_sym'`.  For `b` far from both labels either cut works and the product of
the four edges with the glued pair is symmetric, as observed for (5.72) above.

**The outcome is symmetric in the two labels**, as expected: nothing is short.  The argument
needs one further hypothesis, `hrow` below — the paper's "we can treat `b = b'` for all
practical purposes" — because in each loop one of the two glue labels is reached only through
`b'`; `hrow` makes this identification an explicit hypothesis.
-/

section SixSym

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
variable (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)

/-- **(5.65) + (5.66) for the `k = 1` term of (5.22), cut at the second glue label `b'`**
(Figure 14, left, opened at the other side).  The four surviving `G`-edges are
`a₂–a₁`, `a₁–b`, `b–a₁'`, `a₁'–a₂'`, and the `4`-loop of (5.66) is the one on `b'` and the
`a₂`-blocks.  Compare `norm_gloop_glue_two_one_le`, which cuts at `b`. -/
theorem norm_gloop_glue_two_one'_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b b' : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[!(σ 1), σ 1, !(σ 1), σ 1], [b', leftArg c 1, b', rightArg c 1]⟩).re ≤ S) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 1 b b')‖
      ≤ Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) b
        * Gm b (rightArg c 0) * Gm (rightArg c 0) (rightArg c 1) * √S := by
  rw [glueIdx_two_one]
  exact Lemma57.norm_gloop_six_le_schwarz' (B.L N) (B.W N) (X.hermitian N u ω)
    (σ 1) (σ 0) (σ 1) (!(σ 1)) (!(σ 0))
    (leftArg c 1) (leftArg c 0) b (rightArg c 0) (rightArg c 1) b'
    (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _)
    (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
    (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp) hS

/-- **(5.65) + (5.66) for the `k = 0` term of (5.22), cut at the second glue label `b'`**
(Figure 14, right, opened at the other side).  The four surviving `G`-edges are
`a₁–a₂`, `a₂–b`, `b–a₂'`, `a₂'–a₁'`: they carry the pair `b–a₂` *directly*, with no `b'` in
it, which is what the half `‖b-a₁‖ ≤ ‖b-a₂‖` of the `b`-sum needs. -/
theorem norm_gloop_glue_two_zero'_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b b' : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[!(σ 0), σ 0, !(σ 0), σ 0], [b', leftArg c 0, b', rightArg c 0]⟩).re ≤ S) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 0 b b')‖
      ≤ Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) b
        * Gm b (rightArg c 1) * Gm (rightArg c 1) (rightArg c 0) * √S := by
  rw [glueIdx_two_zero]
  exact Lemma57.norm_gloop_six_le_schwarz' (B.L N) (B.W N) (X.hermitian N u ω)
    (σ 0) (σ 1) (σ 0) (!(σ 0)) (!(σ 1))
    (leftArg c 0) (leftArg c 1) b (rightArg c 1) (rightArg c 0) b'
    (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _)
    (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
    (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp) hS

/-! ### The `b'`-sum for the second cut

When the loop is cut at `b'` the four surviving `G`-edges do **not** involve `b'` at all, so
the `b'`-sum against `‖S^{(B)}_{bb'}‖` only has to absorb the `4`-loop of (5.66); a bound `S`
uniform in `b'` passes straight through the row sum `∑_{b'} ‖S^{(B)}_{bb'}‖ = 1`. -/

/-- **(5.66) for the `k = 1` summand of `RBM.EEDef.eeL6`, cut at `b'`.** -/
theorem eeL6k_two_one'_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : ∀ b' : ZMod (B.L N), (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[!(σ 1), σ 1, !(σ 1), σ 1], [b', leftArg c 1, b', rightArg c 1]⟩).re ≤ S) :
    eeL6k X E N u ω σ c 1 b
      ≤ Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) b
        * Gm b (rightArg c 0) * Gm (rightArg c 0) (rightArg c 1) * √S := by
  classical
  refine (Finset.sum_le_sum (fun b' _ => mul_le_mul_of_nonneg_left
    (norm_gloop_glue_two_one'_le X E N u ω σ c b b' hGm0 hGm (hS b'))
    (norm_nonneg (SB (B.L N) b b')))).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]

/-- **(5.66) for the `k = 0` summand of `RBM.EEDef.eeL6`, cut at `b'`.** -/
theorem eeL6k_two_zero'_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : ∀ b' : ZMod (B.L N), (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[!(σ 0), σ 0, !(σ 0), σ 0], [b', leftArg c 0, b', rightArg c 0]⟩).re ≤ S) :
    eeL6k X E N u ω σ c 0 b
      ≤ Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) b
        * Gm b (rightArg c 1) * Gm (rightArg c 1) (rightArg c 0) * √S := by
  classical
  refine (Finset.sum_le_sum (fun b' _ => mul_le_mul_of_nonneg_left
    (norm_gloop_glue_two_zero'_le X E N u ω σ c b b' hGm0 hGm (hS b'))
    (norm_nonneg (SB (B.L N) b b')))).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]

/-! ### The two halves of the `b`-sum, on `RBM.EEDef.eeL6` itself

`hrow` below is the paper's `b = b'`: in each of the two loops of Figure 14 one of the glue
labels is reached only through `b'`, so the pair of `G`-edges meeting it is
`Gm x b' · Gm b' x`, and the estimate needs it controlled by the `b`-indexed quantity the
`b`-sum is about.  `hSmax` is (2.73) at `n = 4`, uniform over the four `4`-loops that the two
cuts produce. -/

/-- **Case 2(1a) for `b` near `a₁`**, for *both* terms of (5.22): `k = 1` cut at `b`,
`k = 0` cut at `b'`.  This is the near-field hypothesis of `RBM.Lemma57.ee_le_sym'` for `b`
near `a₁`, summand by summand, with the `k = 0` summand taken apart at the *other* glue
label. -/
theorem eeL6_two_le_near₁ (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax : ℝ}
    (hc0 : rightArg c 0 = leftArg c 0) (hc1 : rightArg c 1 = leftArg c 1)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax) :
    eeL6 X E N u ω σ c b
      ≤ Gsq (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1) * (2 * √Smax) := by
  classical
  have hs0 : (0 : ℝ) ≤ √Smax := Real.sqrt_nonneg _
  have h1 : eeL6k X E N u ω σ c 1 b
      ≤ Gm (rightArg c 0) (rightArg c 1) * Gsq b (leftArg c 1)
        * Gm (leftArg c 1) (leftArg c 0) * √Smax :=
    eeL6k_two_one_le X E N u ω σ c b hGm0 hGm
      (fun b' h0 => by rw [hc1]; exact hrow (leftArg c 1) b b' h0)
      (hSmax (σ 1) b (rightArg c 0) (leftArg c 0))
  have h0 : eeL6k X E N u ω σ c 0 b
      ≤ Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) b
        * Gm b (rightArg c 1) * Gm (rightArg c 1) (rightArg c 0) * √Smax :=
    eeL6k_two_zero'_le X E N u ω σ c b hGm0 hGm
      (fun b' => by simpa using hSmax (!(σ 0)) b' (leftArg c 0) (rightArg c 0))
  have hA : Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0)
      ≤ Gsq (leftArg c 0) (leftArg c 1) := hGsq2 _ _
  have hB : Gm (leftArg c 1) b * Gm b (leftArg c 1) ≤ Gsq b (leftArg c 1) := by
    calc Gm (leftArg c 1) b * Gm b (leftArg c 1)
        = Gm b (leftArg c 1) * Gm (leftArg c 1) b := mul_comm _ _
      _ ≤ Gsq b (leftArg c 1) := hGsq2 b (leftArg c 1)
  have s1 : eeL6k X E N u ω σ c 1 b
      ≤ Gsq (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1) * √Smax := by
    refine h1.trans ?_
    rw [hc0, hc1]
    have hstep : (Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0))
        * (Gsq b (leftArg c 1) * √Smax)
        ≤ Gsq (leftArg c 0) (leftArg c 1) * (Gsq b (leftArg c 1) * √Smax) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg (hGsq0 _ _) hs0)
    calc Gm (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1)
          * Gm (leftArg c 1) (leftArg c 0) * √Smax
        = (Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0))
            * (Gsq b (leftArg c 1) * √Smax) := by ring
      _ ≤ Gsq (leftArg c 0) (leftArg c 1) * (Gsq b (leftArg c 1) * √Smax) := hstep
      _ = Gsq (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1) * √Smax := by ring
  have s0 : eeL6k X E N u ω σ c 0 b
      ≤ Gsq (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1) * √Smax := by
    refine h0.trans ?_
    rw [hc1, hc0]
    have hstep : (Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0))
        * ((Gm (leftArg c 1) b * Gm b (leftArg c 1)) * √Smax)
        ≤ Gsq (leftArg c 0) (leftArg c 1) * (Gsq b (leftArg c 1) * √Smax) :=
      mul_le_mul hA (mul_le_mul_of_nonneg_right hB hs0)
        (mul_nonneg (mul_nonneg (hGm0 _ _) (hGm0 _ _)) hs0) (hGsq0 _ _)
    calc Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) b * Gm b (leftArg c 1)
          * Gm (leftArg c 1) (leftArg c 0) * √Smax
        = (Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0))
            * ((Gm (leftArg c 1) b * Gm b (leftArg c 1)) * √Smax) := by ring
      _ ≤ Gsq (leftArg c 0) (leftArg c 1) * (Gsq b (leftArg c 1) * √Smax) := hstep
      _ = Gsq (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1) * √Smax := by ring
  rw [eeL6_two_eq]
  exact (add_le_add s0 s1).trans (le_of_eq (by ring))

/-- **Case 2(1a) for `b` near `a₂`** — the mirror: `k = 0` cut at `b`, `k = 1` cut at `b'`.
This is the near-field hypothesis of `RBM.Lemma57.ee_le_sym'` for `b` near `a₂`, i.e. the half
the paper treats by symmetry (exchanging `a₁ ↔ a₂` and cutting the loop at `b'` instead of
`b`). -/
theorem eeL6_two_le_near₂ (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax : ℝ}
    (hc0 : rightArg c 0 = leftArg c 0) (hc1 : rightArg c 1 = leftArg c 1)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax) :
    eeL6 X E N u ω σ c b
      ≤ Gsq (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0) * (2 * √Smax) := by
  classical
  have hs0 : (0 : ℝ) ≤ √Smax := Real.sqrt_nonneg _
  have h0 : eeL6k X E N u ω σ c 0 b
      ≤ Gm (rightArg c 1) (rightArg c 0) * Gsq b (leftArg c 0)
        * Gm (leftArg c 0) (leftArg c 1) * √Smax :=
    eeL6k_two_zero_le X E N u ω σ c b hGm0 hGm
      (fun b' hz => by rw [hc0]; exact hrow (leftArg c 0) b b' hz)
      (hSmax (σ 0) b (rightArg c 1) (leftArg c 1))
  have h1 : eeL6k X E N u ω σ c 1 b
      ≤ Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) b
        * Gm b (rightArg c 0) * Gm (rightArg c 0) (rightArg c 1) * √Smax :=
    eeL6k_two_one'_le X E N u ω σ c b hGm0 hGm
      (fun b' => by simpa using hSmax (!(σ 1)) b' (leftArg c 1) (rightArg c 1))
  have hA : Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1)
      ≤ Gsq (leftArg c 1) (leftArg c 0) := hGsq2 _ _
  have hB : Gm (leftArg c 0) b * Gm b (leftArg c 0) ≤ Gsq b (leftArg c 0) := by
    calc Gm (leftArg c 0) b * Gm b (leftArg c 0)
        = Gm b (leftArg c 0) * Gm (leftArg c 0) b := mul_comm _ _
      _ ≤ Gsq b (leftArg c 0) := hGsq2 b (leftArg c 0)
  have s0 : eeL6k X E N u ω σ c 0 b
      ≤ Gsq (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0) * √Smax := by
    refine h0.trans ?_
    rw [hc1, hc0]
    have hstep : (Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1))
        * (Gsq b (leftArg c 0) * √Smax)
        ≤ Gsq (leftArg c 1) (leftArg c 0) * (Gsq b (leftArg c 0) * √Smax) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg (hGsq0 _ _) hs0)
    calc Gm (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0)
          * Gm (leftArg c 0) (leftArg c 1) * √Smax
        = (Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1))
            * (Gsq b (leftArg c 0) * √Smax) := by ring
      _ ≤ Gsq (leftArg c 1) (leftArg c 0) * (Gsq b (leftArg c 0) * √Smax) := hstep
      _ = Gsq (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0) * √Smax := by ring
  have s1 : eeL6k X E N u ω σ c 1 b
      ≤ Gsq (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0) * √Smax := by
    refine h1.trans ?_
    rw [hc0, hc1]
    have hstep : (Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1))
        * ((Gm (leftArg c 0) b * Gm b (leftArg c 0)) * √Smax)
        ≤ Gsq (leftArg c 1) (leftArg c 0) * (Gsq b (leftArg c 0) * √Smax) :=
      mul_le_mul hA (mul_le_mul_of_nonneg_right hB hs0)
        (mul_nonneg (mul_nonneg (hGm0 _ _) (hGm0 _ _)) hs0) (hGsq0 _ _)
    calc Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) b * Gm b (leftArg c 0)
          * Gm (leftArg c 0) (leftArg c 1) * √Smax
        = (Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1))
            * ((Gm (leftArg c 0) b * Gm b (leftArg c 0)) * √Smax) := by ring
      _ ≤ Gsq (leftArg c 1) (leftArg c 0) * (Gsq b (leftArg c 0) * √Smax) := hstep
      _ = Gsq (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0) * √Smax := by ring
  rw [eeL6_two_eq]
  exact (add_le_add s0 s1).trans (le_of_eq (by ring))

/-- **Case 2(1b) for `b` far from both labels**, for *both* terms of (5.22).  Here either cut
does; `eeL6k_two_one_le_glue` and `eeL6k_two_zero_le_glue` (the cut at `b`) are used for
both, because the product of the four edges with the glued pair is the same
`T_{u,D}(‖a₁-a₂‖) T_{u,D}(‖a₁-b‖) T_{u,D}(‖a₂-b‖)` either way: the bound is symmetric in
`k`.  The two summands cost a factor `2`, absorbed into
`(2J)³`. -/
theorem eeL6_two_le_far (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {ℓu ηu D J : ℝ}
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ}
    (hℓu : 0 < ℓu) (hJ : 1 ≤ J)
    (hc0 : rightArg c 0 = leftArg c 0) (hc1 : rightArg c 1 = leftArg c 1)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)))
    (hfar : 4 * ellStar (B.W N : ℝ) ℓu
      ≤ (zdist (B.L N) (leftArg c 0 - leftArg c 1) : ℝ))
    (hb1 : ellStar (B.W N : ℝ) ℓu < (zdist (B.L N) (leftArg c 0 - b) : ℝ))
    (hb2 : ellStar (B.W N : ℝ) ℓu < (zdist (B.L N) (leftArg c 1 - b) : ℝ)) :
    eeL6 X E N u ω σ c b
      ≤ (2 * J) ^ 3
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
          * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
            * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) := by
  classical
  have hW : (1 : ℝ) ≤ (B.W N : ℝ) := one_le_W B N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hstar : (0 : ℝ) ≤ ellStar (B.W N : ℝ) ℓu := by
    unfold ellStar; have := Real.log_nonneg hW; positivity
  have hT12 : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D
      (zdist (B.L N) (leftArg c 0 - leftArg c 1)) := tailT_nonneg hW0.le _
  have hT1b : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D
      (zdist (B.L N) (leftArg c 0 - b)) := tailT_nonneg hW0.le _
  have hT2b : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D
      (zdist (B.L N) (leftArg c 1 - b)) := tailT_nonneg hW0.le _
  have hA12 : Gsq (leftArg c 0) (leftArg c 1)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1)) :=
    h42sq _ _ (by linarith)
  have hA21 : Gsq (leftArg c 1) (leftArg c 0)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1)) := by
    have h := h42sq (leftArg c 1) (leftArg c 0)
      (by rw [Lemma57.zdist_sub_comm]; linarith)
    rwa [Lemma57.zdist_sub_comm] at h
  have hB1 : Gsq b (leftArg c 0)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b)) := by
    have h := h42sq b (leftArg c 0) (by rw [Lemma57.zdist_sub_comm]; linarith)
    rwa [Lemma57.zdist_sub_comm] at h
  have hB2 : Gsq b (leftArg c 1)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b)) := by
    have h := h42sq b (leftArg c 1) (by rw [Lemma57.zdist_sub_comm]; linarith)
    rwa [Lemma57.zdist_sub_comm] at h
  have hG1 : Gm (leftArg c 0) b * Gm b (leftArg c 0)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b)) :=
    (hGsq2 _ _).trans (h42sq (leftArg c 0) b (by linarith))
  have hG2 : Gm (leftArg c 1) b * Gm b (leftArg c 1)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b)) :=
    (hGsq2 _ _).trans (h42sq (leftArg c 1) b (by linarith))
  have h1 : eeL6k X E N u ω σ c 1 b
      ≤ Gm (rightArg c 0) (rightArg c 1) * Gsq b (leftArg c 1)
        * Gm (leftArg c 1) (leftArg c 0)
        * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))) :=
    eeL6k_two_one_le_glue X E N u ω σ c b hGm0 (mul_nonneg hJ0 hT1b) hGm
      (fun b' hz => by rw [hc1]; exact hrow (leftArg c 1) b b' hz)
      (fun p q y hp hq hy => by
        rw [hc0] at hq
        exact (mul_le_mul (hGm (σ 1) (leftArg c 0) b p y hp hy)
          (hGm (!(σ 1)) b (leftArg c 0) y q hy hq) (norm_nonneg _) (hGm0 _ _)).trans hG1)
  have h0 : eeL6k X E N u ω σ c 0 b
      ≤ Gm (rightArg c 1) (rightArg c 0) * Gsq b (leftArg c 0)
        * Gm (leftArg c 0) (leftArg c 1)
        * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) :=
    eeL6k_two_zero_le_glue X E N u ω σ c b hGm0 (mul_nonneg hJ0 hT2b) hGm
      (fun b' hz => by rw [hc0]; exact hrow (leftArg c 0) b b' hz)
      (fun p q y hp hq hy => by
        rw [hc1] at hq
        exact (mul_le_mul (hGm (σ 0) (leftArg c 1) b p y hp hy)
          (hGm (!(σ 0)) b (leftArg c 1) y q hy hq) (norm_nonneg _) (hGm0 _ _)).trans hG2)
  have s1 : eeL6k X E N u ω σ c 1 b
      ≤ J ^ 3 * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
        * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) := by
    refine h1.trans ?_
    rw [hc0, hc1]
    have p1 : Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0)
        ≤ J * tailT (B.W N : ℝ) ℓu ηu D
            (zdist (B.L N) (leftArg c 0 - leftArg c 1)) := (hGsq2 _ _).trans hA12
    have q1 := mul_le_mul p1 hB2 (hGsq0 _ _) (mul_nonneg hJ0 hT12)
    have q2 := mul_le_mul_of_nonneg_right q1 (mul_nonneg hJ0 hT1b)
    calc Gm (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1)
            * Gm (leftArg c 1) (leftArg c 0)
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b)))
        = (Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0)
            * Gsq b (leftArg c 1))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))) := by ring
      _ ≤ (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))) := q2
      _ = _ := by ring
  have s0 : eeL6k X E N u ω σ c 0 b
      ≤ J ^ 3 * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
        * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) := by
    refine h0.trans ?_
    rw [hc1, hc0]
    have p1 : Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1)
        ≤ J * tailT (B.W N : ℝ) ℓu ηu D
            (zdist (B.L N) (leftArg c 0 - leftArg c 1)) := (hGsq2 _ _).trans hA21
    have q1 := mul_le_mul p1 hB1 (hGsq0 _ _) (mul_nonneg hJ0 hT12)
    have q2 := mul_le_mul_of_nonneg_right q1 (mul_nonneg hJ0 hT2b)
    calc Gm (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0)
            * Gm (leftArg c 0) (leftArg c 1)
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b)))
        = (Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1)
            * Gsq b (leftArg c 0))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) := by ring
      _ ≤ (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) := q2
      _ = _ := by ring
  have hP : (0 : ℝ) ≤ J ^ 3
      * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
      * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) :=
    mul_nonneg (mul_nonneg (pow_nonneg hJ0 3) hT12) (mul_nonneg hT1b hT2b)
  rw [eeL6_two_eq]
  have hsum := add_le_add s0 s1
  refine hsum.trans ?_
  have hexp : (2 * J) ^ 3
      * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
      * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b)))
      = 8 * (J ^ 3
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
        * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b)))) := by ring
  rw [hexp]
  linarith [hP]

end SixSym

end EEDef
end RBM
