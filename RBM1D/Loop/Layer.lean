/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.TreeRepGeneral

/-!
# Definitions 3.8 and 3.9: layers by long edges, `K^(π)` and `Σ^(π)`

Paper pp.38–40.

**Definition 3.8.**  For a tree `Γ_a ∈ T_SP(P_a)` (for us a crossing-free set `F` of diagonals,
Lemma 3.2 taken as the definition, paper-deltas #8) the *long internal edges* are
`F_long(Γ_a, σ) = {{i,j} ∈ F(Γ_a) : {σ_i, σ_j} = {+, −}}`, i.e. `σ_i ≠ σ_j` (`Flong`).  For
`π ⊆ Z_n^off` (our `diagonals n`), `T_SP(P_a, σ, π)` is the set of trees whose long edges are
exactly `π` (`TSPlong`).  These sets partition `T_SP(P_a)` (`sum_TSPlong`).

**Definition 3.9.**
* (3.40) `K^(π)_{t,σ,a} = ∑_{Γ_a ∈ T_SP(P_a,σ,π)} Γ_a(t,σ)` (`Kpi`), independent of `W`;
* (3.41) `K_{t,σ,a} = W^{-n+1} m_σ ∑_π K^(π)_{t,σ,a}` (`Kn_eq_sum_Kpi`, and `K_eq_sum_Kpi`
  for any solution of Definition 2.12, via Lemma 3.4);
* (3.42) the self-energy `Σ^(π)(t,σ,d)`: remove the boundary edges.  `d_i` is the endpoint of
  the boundary edge at `a_i`; boundary edges ending at the same internal vertex force their
  `d`'s to coincide (a Kronecker delta), and the remaining internal vertices are summed.  In the
  pivot-free encoding of `Loop/TreeRepGeneral.lean` this is `selfW`: the labelling `b` of all
  internal vertices is summed, with the constraint `d_v = b(leafPar v)` for every leaf `v`
  (`selfE`, `SigmaPi`; for the star it is `δ_{d_1⋯d_n}`, `selfW_empty`).  Then
  `K^(π)_{t,σ,a} = ∑_d Σ^(π)(t,σ,d) ∏_i (Θ_{t m_i m_{i+1}})_{a_i d_i}` (`Kpi_eq_sum_SigmaPi`).

As in Lemma 3.4, the tree of the `2`-gon is a single edge, not the star (paper-deltas #9), so
(3.41) is stated for `n ≥ 3` (paper-deltas #19).
-/

namespace RBM

open Finset

section Def38

variable {n : ℕ}

/-- **Definition 3.8 I**: the long internal edges of `F`, those joining regions of opposite
charge. -/
def Flong (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) : Finset (Fin n × Fin n) :=
  F.filter fun d => σ d.1 ≠ σ d.2

theorem mem_Flong {F : Finset (Fin n × Fin n)} {σ : Fin n → Bool} {d : Fin n × Fin n} :
    d ∈ Flong F σ ↔ d ∈ F ∧ σ d.1 ≠ σ d.2 := mem_filter

theorem Flong_subset (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) : Flong F σ ⊆ F :=
  filter_subset _ _

/-- `F_long(Γ_a, σ) ⊂ F(Γ_a) ⊂ Z_n^off`. -/
theorem Flong_subset_diagonals {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    (σ : Fin n → Bool) : Flong F σ ⊆ diagonals n :=
  (Flong_subset F σ).trans (mem_TSP.1 hF).1

/-- **Definition 3.8 II**: `T_SP(P_a, σ, π)`, the trees whose long internal edges are exactly
`π`. -/
def TSPlong (n : ℕ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) :=
  (TSP n).filter fun F => Flong F σ = π

theorem mem_TSPlong {σ : Fin n → Bool} {π F : Finset (Fin n × Fin n)} :
    F ∈ TSPlong n σ π ↔ F ∈ TSP n ∧ Flong F σ = π := mem_filter

theorem TSPlong_subset (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    TSPlong n σ π ⊆ TSP n := filter_subset _ _

/-- Only `π ⊆ Z_n^off` can occur. -/
theorem TSPlong_eq_empty {σ : Fin n → Bool} {π : Finset (Fin n × Fin n)}
    (h : ¬π ⊆ diagonals n) : TSPlong n σ π = ∅ := by
  by_contra hne
  obtain ⟨F, hF⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨hF, hπ⟩ := mem_TSPlong.1 hF
  exact h (hπ ▸ Flong_subset_diagonals hF σ)

/-- Different `π` give disjoint layers. -/
theorem disjoint_TSPlong (σ : Fin n → Bool) {π π' : Finset (Fin n × Fin n)} (h : π ≠ π') :
    Disjoint (TSPlong n σ π) (TSPlong n σ π') := by
  rw [disjoint_left]
  intro _ h1 h2
  exact h ((mem_TSPlong.1 h1).2.symm.trans (mem_TSPlong.1 h2).2)

/-- The layers cover `T_SP(P_a)`. -/
theorem biUnion_TSPlong (σ : Fin n → Bool) :
    (diagonals n).powerset.biUnion (TSPlong n σ) = TSP n := by
  ext F
  simp only [mem_biUnion, mem_powerset]
  refine ⟨fun ⟨π, _, hF⟩ => TSPlong_subset σ π hF, fun hF => ?_⟩
  exact ⟨Flong F σ, Flong_subset_diagonals hF σ, mem_TSPlong.2 ⟨hF, rfl⟩⟩

/-- **The layers partition `T_SP(P_a)`**: summing over the layers is summing over all trees. -/
theorem sum_TSPlong {M : Type*} [AddCommMonoid M] (σ : Fin n → Bool)
    (f : Finset (Fin n × Fin n) → M) :
    ∑ π ∈ (diagonals n).powerset, ∑ F ∈ TSPlong n σ π, f F = ∑ F ∈ TSP n, f F :=
  sum_fiberwise_of_maps_to (fun _ hF => mem_powerset.2 (Flong_subset_diagonals hF σ)) f

end Def38

section Def39

variable (L : ℕ) [NeZero L] {n : ℕ} [NeZero n]

/-- **Definition 3.9 I**, (3.40): `K^(π)_{t,σ,a}`, the sum of the trees whose long edges are
`π`.  It does not contain `W`. -/
noncomputable def Kpi (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → ZMod L)
    (π : Finset (Fin n × Fin n)) : ℂ :=
  ∑ F ∈ TSPlong n σ π, treeValG L m t σ a F

/-- (3.41) for the tree representation: `K = W^{-n+1} m_σ ∑_π K^(π)`. -/
theorem Kn_eq_sum_Kpi (W : ℕ) (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → ZMod L) :
    Kn L W m t n σ a =
      (∏ i, m (σ i)) * (W : ℂ)⁻¹ ^ (n - 1) *
        ∑ π ∈ (diagonals n).powerset, Kpi L m t σ a π := by
  simp only [Kn, Kpi]
  rw [sum_TSPlong]

/-- The self-energy of one tree, for general edge weights `E`: the boundary edges are removed,
`d_v` is the endpoint of the boundary edge at `a_v`, and all internal vertices are summed
subject to `d_v = b(leafPar v)` (a Kronecker delta for each leaf). -/
noncomputable def selfW (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ)
    (d : Fin n → ZMod L) : ℂ :=
  ∑ b : ↥(nodes F) → ZMod L,
    (∏ v : Fin n, if d v = b ⟨leafPar F v, leafPar_mem F v⟩ then (1 : ℂ) else 0) *
      ∏ e : ↥F, E e (b ⟨e.1, mem_nodes_of_mem e.2⟩) (b ⟨nodePar F e, nodePar_mem F e⟩)

variable {L} in
/-- Re-attaching the boundary edges to the self-energy gives back the tree value. -/
theorem treeValW_eq_sum_selfW (F : Finset (Fin n × Fin n)) (a : Fin n → ZMod L)
    (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) :
    treeValW L F a M E = ∑ d : Fin n → ZMod L, selfW L F E d * ∏ v, M v (a v) (d v) := by
  simp only [selfW, sum_mul]
  rw [sum_comm, treeValW]
  refine sum_congr rfl fun b _ => ?_
  have h : ∀ d : Fin n → ZMod L,
      (∏ v : Fin n, if d v = b ⟨leafPar F v, leafPar_mem F v⟩ then (1 : ℂ) else 0) *
          (∏ e : ↥F, E e (b ⟨e.1, mem_nodes_of_mem e.2⟩) (b ⟨nodePar F e, nodePar_mem F e⟩)) *
        ∏ v, M v (a v) (d v) =
      (∏ e : ↥F, E e (b ⟨e.1, mem_nodes_of_mem e.2⟩) (b ⟨nodePar F e, nodePar_mem F e⟩)) *
        ∏ v, (if d v = b ⟨leafPar F v, leafPar_mem F v⟩ then M v (a v) (d v) else 0) := by
    intro d
    rw [mul_comm (∏ v : Fin n, _), mul_assoc, ← prod_mul_distrib]
    congr 2
    funext v
    split_ifs <;> simp
  simp_rw [h, ← mul_sum]
  rw [mul_comm]
  congr 1
  have := (prod_univ_sum (fun _ : Fin n => (univ : Finset (ZMod L)))
    (fun v x => if x = b ⟨leafPar F v, leafPar_mem F v⟩ then M v (a v) x else 0)).symm
  rw [Fintype.piFinset_univ] at this
  rw [this]
  refine prod_congr rfl fun v _ => ?_
  rw [Fintype.sum_ite_eq']

variable {L} in
/-- The star (`F = ∅`, a single molecule with no internal edge): all boundary edges end at the
root, so the self-energy is the Kronecker delta `δ_{d_1 ⋯ d_n}` (the first term of the paper's
`n = 4` example after (3.42)). -/
theorem selfW_empty (E : ↥(∅ : Finset (Fin n × Fin n)) → Matrix (ZMod L) (ZMod L) ℂ)
    (d : Fin n → ZMod L) :
    selfW L ∅ E d = ∑ x : ZMod L, ∏ v, if d v = x then (1 : ℂ) else 0 := by
  have hmem : ∀ y (hy : y ∈ nodes (∅ : Finset (Fin n × Fin n))), y = wholeP n := by
    intro y hy; simpa [nodes] using hy
  have : Unique ↥(nodes (∅ : Finset (Fin n × Fin n))) :=
    { default := ⟨wholeP n, wholeP_mem_nodes _⟩
      uniq := fun ⟨y, hy⟩ => Subtype.ext (hmem y hy) }
  unfold selfW
  rw [← (Equiv.funUnique ↥(nodes (∅ : Finset (Fin n × Fin n))) (ZMod L)).symm.sum_comp]
  refine sum_congr rfl fun x _ => ?_
  simp [Equiv.funUnique]

/-- The self-energy of one tree (Definition 3.9 II): boundary edges removed, internal edges
`Θ_{t m_i m_j} - 1`. -/
noncomputable def selfE (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (F : Finset (Fin n × Fin n))
    (d : Fin n → ZMod L) : ℂ :=
  selfW L F (fun e => thetaEdge L m t (σ e.1.1) (σ e.1.2) - 1) d

/-- **Definition 3.9 II**: the self-energy `Σ^(π)(t,σ,d)` of `K^(π)`. -/
noncomputable def SigmaPi (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) (d : Fin n → ZMod L) : ℂ :=
  ∑ F ∈ TSPlong n σ π, selfE L m t σ F d

/-- One tree: `Γ_a(t,σ) = ∑_d Σ_Γ(d) ∏_i (Θ_{t m_i m_{i+1}})_{a_i d_i}`. -/
theorem treeValG_eq_sum_selfE (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → ZMod L)
    (F : Finset (Fin n × Fin n)) :
    treeValG L m t σ a F =
      ∑ d : Fin n → ZMod L,
        selfE L m t σ F d * ∏ v, thetaEdge L m t (σ v) (σ (v + 1)) (a v) (d v) :=
  treeValW_eq_sum_selfW F a _ _

/-- **(3.42)**: `K^(π)_{t,σ,a} = ∑_d Σ^(π)(t,σ,d) ∏_i (Θ_{t m_i m_{i+1}})_{a_i d_i}`. -/
theorem Kpi_eq_sum_SigmaPi (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → ZMod L)
    (π : Finset (Fin n × Fin n)) :
    Kpi L m t σ a π =
      ∑ d : Fin n → ZMod L,
        SigmaPi L m t σ π d * ∏ v, thetaEdge L m t (σ v) (σ (v + 1)) (a v) (d v) := by
  simp only [Kpi, SigmaPi, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun F _ => treeValG_eq_sum_selfE L m t σ a F

end Def39

section Main

variable {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ)
  (hm1 : ∀ s, ‖m s‖ ≤ 1) {T₀ : ℝ} (hT₀ : T₀ < 1)
include hL hm1 hT₀

/-- **(3.41)** for a solution of Definition 2.12 (via Lemma 3.4), `n ≥ 3`:
`K_{t,σ,a} = W^{-n+1} m_σ ∑_π K^(π)_{t,σ,a}`. -/
theorem K_eq_sum_Kpi {T : Set ℝ} {K : ℝ → LoopIdx (ZMod L) → ℂ}
    (hK : IsPrimitive L W m T K) (hT : Set.Icc 0 T₀ ⊆ T) {R : ℝ}
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T₀) (I : LoopIdx (ZMod L)) (hI : I.WF) (h3 : 3 ≤ I.length) :
    haveI : NeZero I.length := ⟨by omega⟩
    K t I = (I.σ.map m).prod * (W : ℂ)⁻¹ ^ (I.length - 1) *
      ∑ π ∈ (diagonals I.length).powerset,
        Kpi L m t (fun i => I.σ.getD i false) (fun i => I.a.getD i 0) π := by
  rw [treeRep_general hL W m hm1 hT₀ hK hT hR ht I hI h3]
  simp only [Kpi]
  rw [sum_TSPlong]

end Main

end RBM
