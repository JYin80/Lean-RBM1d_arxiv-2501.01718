/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.CanonicalPartition
import RBM1D.Loop.TreeRepGeneral

/-!
# Lemma 3.2 (2) and (3): realization and uniqueness

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 3.2 (pp. 27–28).

`RBM1D/Loop/CanonicalPartition.lean` builds the map `Γ ↦ F (Γ)` and proves it lands in
`RBM.TSP n` (Lemma 3.2 (1)).  This file completes Lemma 3.2:

* **realization** — for every crossing-free family `F` of diagonals there is a canonical tree
  `canonGraph F` with `F (canonGraph F) = F`, so the image of `Γ ↦ F (Γ)` is *all* of
  `RBM.TSP n`;
* **uniqueness** — two canonical trees with the same pair set are isomorphic by an
  isomorphism matching the leaf labels.

Together these say that `Γ ↦ F (Γ)` is a bijection from canonical trees of the `n`-gon, up to
leaf-label preserving isomorphism, onto `RBM.TSP n`.

## The construction

The realization is the laminar family already used for Lemma 3.4 in
`RBM1D/Loop/TreeRepGeneral.lean`: a diagonal `d = (i, j)` is read as the arc
`{v | i ≤ v < j}` of polygon vertices, crossing-freeness is laminarity, and the internal
vertices of the tree are the nodes `F ∪ {whole}`, `whole = (0, n - 1)`.  Each leaf `v` hangs
on the smallest node containing it (`RBM.leafPar`) and each node other than `whole` hangs on
the smallest node strictly containing it (`RBM.nodePar`); the root leaf `n - 1` hangs on
`whole`.

The uniqueness proof runs the same picture inside an abstract canonical tree `Γ`.  Rooting
`Γ` at the leaf `a_{n-1}` (`RBM.rootIdx`), every other vertex `v` has a unique neighbour
`RBM.upNb` towards the root; the two regions through the edge `v — upNb v` form a pair
`RBM.edgePair`, and the leaves below that edge are exactly the arc of that pair
(`RBM.leafSide_eq_inArc`).  The content of the proof is that this dictionary turns the tree
structure of `Γ` into `leafPar` and `nodePar`:

* `RBM.upPair_leafNb` : the up-edge of a leaf's neighbour carries `leafPar F m`;
* `RBM.nodePar_upPair` : going up one internal edge is `nodePar F`.

## Main definitions

* `RBM.CanonV F`, `RBM.canonGraph F` : the vertex type `Fin n ⊕ nodes F` and the tree
* `RBM.rootIdx`, `RBM.upNb`, `RBM.leafNb`, `RBM.edgePair` : the rooted picture in an
  abstract canonical tree
* `RBM.ndVertex`, `RBM.canonEmb`, `RBM.canonIso` : the comparison map `canonGraph F ≃g Γ`

## Main results

* `RBM.canonGraph_isTree`, `RBM.isCanonicalTree_canonGraph` : `canonGraph F` satisfies
  Definition 3.1 (`RBM.IsCanonicalTree`)
* `RBM.FGamma_canonGraph` : `F (canonGraph F) = F` — **Lemma 3.2 (2)**
* `RBM.exists_isCanonicalTree_of_mem_TSP`, `RBM.mem_TSP_iff_exists_isCanonicalTree` : the
  image of `Γ ↦ F (Γ)` is exactly `RBM.TSP n`
* `RBM.canonIso` : every canonical tree with pair set `F` is isomorphic to `canonGraph F`
* `RBM.exists_iso_of_FGamma_eq` : **Lemma 3.2 (3)** — `F (Γ) = F (Γ')` forces `Γ ≅ Γ'` by a
  leaf-label preserving isomorphism

## The hypothesis `3 ≤ n`

Definition 3.1 partitions a polygon, so `n ≥ 3`.  For `n = 2` the model degenerates: the tree
on `2` leaves is a single edge, whereas the construction here would make `whole` an internal
vertex of degree `2`, which `IsCanonicalTree.internal_degree` forbids.  See
`docs/paper-deltas.md`.
-/

namespace RBM

open SimpleGraph

section Realize

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)}

/-- The vertices of the canonical tree of `F`: the `n` polygon vertices (the leaves) and the
nodes `F ∪ {whole}` (the internal vertices). -/
abbrev CanonV {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n)) : Type :=
  Fin n ⊕ {d : Fin n × Fin n // d ∈ nodes F}

/-- Adjacency in the canonical tree: a leaf is joined to its `leafPar`, and a node other than
`whole` is joined to its `nodePar`. -/
def canonAdj (F : Finset (Fin n × Fin n)) : CanonV F → CanonV F → Prop
  | Sum.inl _, Sum.inl _ => False
  | Sum.inl v, Sum.inr d => leafPar F v = d.1
  | Sum.inr d, Sum.inl v => leafPar F v = d.1
  | Sum.inr d, Sum.inr e =>
      d.1 ≠ e.1 ∧ ((d.1 ≠ wholeP n ∧ nodePar F d.1 = e.1) ∨ (e.1 ≠ wholeP n ∧ nodePar F e.1 = d.1))

@[simp] theorem canonAdj_inl_inl (v w : Fin n) :
    canonAdj F (Sum.inl v) (Sum.inl w) ↔ False := Iff.rfl

@[simp] theorem canonAdj_inl_inr (v : Fin n) (d : {d : Fin n × Fin n // d ∈ nodes F}) :
    canonAdj F (Sum.inl v) (Sum.inr d) ↔ leafPar F v = d.1 := Iff.rfl

@[simp] theorem canonAdj_inr_inl (v : Fin n) (d : {d : Fin n × Fin n // d ∈ nodes F}) :
    canonAdj F (Sum.inr d) (Sum.inl v) ↔ leafPar F v = d.1 := Iff.rfl

@[simp] theorem canonAdj_inr_inr (d e : {d : Fin n × Fin n // d ∈ nodes F}) :
    canonAdj F (Sum.inr d) (Sum.inr e) ↔
      d.1 ≠ e.1 ∧ ((d.1 ≠ wholeP n ∧ nodePar F d.1 = e.1) ∨
        (e.1 ≠ wholeP n ∧ nodePar F e.1 = d.1)) := Iff.rfl

theorem canonAdj_symm (u v : CanonV F) (h : canonAdj F u v) : canonAdj F v u := by
  cases u with
  | inl v' => cases v with
    | inl w => exact h
    | inr e => exact h
  | inr d => cases v with
    | inl w => exact h
    | inr e => exact ⟨(h.1).symm, h.2.symm⟩

/-- The canonical tree of a crossing-free family `F`. -/
def canonGraph (F : Finset (Fin n × Fin n)) : SimpleGraph (CanonV F) where
  Adj := canonAdj F
  symm := ⟨canonAdj_symm⟩
  loopless := ⟨by
    rintro (v | d) h
    · exact h
    · exact h.1 rfl⟩

@[simp] theorem canonGraph_adj (u v : CanonV F) : (canonGraph F).Adj u v ↔ canonAdj F u v :=
  Iff.rfl

/-- The internal vertex attached to the leaf `v`. -/
noncomputable def canonPar (F : Finset (Fin n × Fin n)) (v : Fin n) : CanonV F :=
  Sum.inr ⟨leafPar F v, leafPar_mem F v⟩

theorem canonGraph_adj_canonPar (v : Fin n) :
    (canonGraph F).Adj (Sum.inl v) (canonPar F v) := rfl

/-- The only neighbour of the leaf `v` is `canonPar F v`. -/
theorem canonGraph_adj_inl_iff {v : Fin n} {u : CanonV F} :
    (canonGraph F).Adj (Sum.inl v) u ↔ u = canonPar F v := by
  cases u with
  | inl w => simp [canonGraph, canonPar]
  | inr e =>
    constructor
    · intro h
      have h' : leafPar F v = e.1 := h
      exact congrArg Sum.inr (Subtype.ext h'.symm)
    · intro h
      have : e = ⟨leafPar F v, leafPar_mem F v⟩ := by
        simpa [canonPar] using h
      show leafPar F v = e.1
      rw [this]

theorem mem_F_of_mem_nodes {d : Fin n × Fin n} (hd : d ∈ nodes F) (hne : d ≠ wholeP n) :
    d ∈ F := by
  simp only [nodes, Finset.mem_insert] at hd
  exact hd.resolve_left hne

/-- The leaf `v` hangs below the node `d ∈ F` exactly when it lies in the arc of `d`.  (The
root leaf `n - 1` lies in no arc and hangs on `whole`.) -/
theorem arcLe_leafPar_iff_inArc (hF : IsTSP F) {d : Fin n × Fin n} (hd : d ∈ F) (v : Fin n) :
    ArcLe (leafPar F v) d ↔ InArc d v := by
  constructor
  · intro h
    by_cases hv : v.val < n - 1
    · exact ((leafPar_spec hF hv).1).mono h
    · have hroot : v.val = n - 1 := by have := v.isLt; omega
      rw [leafPar_root F hroot] at h
      exact absurd h (not_arcLe_wholeP hF hd)
  · intro h
    exact (leafPar_spec hF (lt_of_inArc h)).2 d (mem_nodes_of_mem hd) h

/-- The internal vertex above the node `d`. -/
noncomputable def canonUp (F : Finset (Fin n × Fin n)) (d : Fin n × Fin n) : CanonV F :=
  Sum.inr ⟨nodePar F d, nodePar_mem F d⟩

/-- The internal vertex of the node `d`. -/
def canonNd {d : Fin n × Fin n} (hd : d ∈ nodes F) : CanonV F := Sum.inr ⟨d, hd⟩

theorem canonGraph_adj_up (hF : IsTSP F) (hn : 2 ≤ n) {d : Fin n × Fin n} (hd : d ∈ F) :
    (canonGraph F).Adj (canonNd (mem_nodes_of_mem hd)) (canonUp F d) := by
  obtain ⟨-, -, hne, -⟩ := nodePar_spec hF hn (mem_nodes_of_mem hd) (ne_wholeP hF hd)
  exact ⟨fun hc => hne hc.symm, Or.inl ⟨ne_wholeP hF hd, rfl⟩⟩

/-! ### The two cut certificates -/

/-- The cut certificate for the edge above the node `d`: the vertices lying below `d`. -/
noncomputable def belowB (F : Finset (Fin n × Fin n)) (d : Fin n × Fin n) : CanonV F → Bool :=
  Sum.elim (fun v => decide (ArcLe (leafPar F v) d)) (fun e => decide (ArcLe e.1 d))

/-- The cut certificate for the leaf edge at `v`: the single vertex `v`. -/
def leafB (F : Finset (Fin n × Fin n)) (v : Fin n) : CanonV F → Bool :=
  Sum.elim (fun w => decide (w = v)) (fun _ => false)

theorem belowB_const (hF : IsTSP F) (hn : 2 ≤ n) {d : Fin n × Fin n} (hd : d ∈ F)
    (u w : CanonV F) (huw : (canonGraph F).Adj u w)
    (hne : s(u, w) ≠ s(canonNd (mem_nodes_of_mem hd), canonUp F d)) :
    belowB F d u = belowB F d w := by
  -- the one-step transfer along a node edge
  have key : ∀ c : Fin n × Fin n, c ∈ F → c ≠ d → (ArcLe c d ↔ ArcLe (nodePar F c) d) := by
    intro c hc hcd
    refine ⟨fun h => nodePar_arcLe hF hn hd hc h hcd, fun h => ?_⟩
    exact ((nodePar_spec hF hn (mem_nodes_of_mem hc) (ne_wholeP hF hc)).2.1).trans h
  cases u with
  | inl v =>
    cases w with
    | inl w' => exact absurd huw id
    | inr e =>
      have h : leafPar F v = e.1 := huw
      simp only [belowB, Sum.elim_inl, Sum.elim_inr, h]
  | inr e =>
    cases w with
    | inl v =>
      have h : leafPar F v = e.1 := huw
      simp only [belowB, Sum.elim_inl, Sum.elim_inr, h]
    | inr e' =>
      obtain ⟨hne', hcase⟩ := huw
      simp only [belowB, Sum.elim_inr, decide_eq_decide]
      -- the transfer, in whichever direction the parent relation goes
      have main : ∀ f f' : {d : Fin n × Fin n // d ∈ nodes F}, f.1 ≠ wholeP n →
          nodePar F f.1 = f'.1 →
          s(Sum.inr f, Sum.inr f') ≠ (s(canonNd (mem_nodes_of_mem hd), canonUp F d) :
            Sym2 (CanonV F)) → (ArcLe f.1 d ↔ ArcLe f'.1 d) := by
        intro f f' hfw hff' hfe
        have hfF : f.1 ∈ F := mem_F_of_mem_nodes f.2 hfw
        have hfd : f.1 ≠ d := by
          rintro rfl
          refine hfe ?_
          have : f' = ⟨nodePar F f.1, nodePar_mem F f.1⟩ := Subtype.ext hff'.symm
          rw [this]
          rfl
        rw [← hff']
        exact key f.1 hfF hfd
      rcases hcase with ⟨hfw, hff'⟩ | ⟨hfw, hff'⟩
      · exact main e e' hfw hff' hne
      · exact (main e' e hfw hff' (by rwa [Sym2.eq_swap])).symm

theorem leafB_const (v : Fin n) (u w : CanonV F) (huw : (canonGraph F).Adj u w)
    (hne : s(u, w) ≠ s(Sum.inl v, canonPar F v)) : leafB F v u = leafB F v w := by
  have key : ∀ (w' : Fin n) (e : {d : Fin n × Fin n // d ∈ nodes F}), leafPar F w' = e.1 →
      s(Sum.inl w', Sum.inr e) ≠ (s(Sum.inl v, canonPar F v) : Sym2 (CanonV F)) → w' ≠ v := by
    rintro w' e he hee rfl
    refine hee ?_
    have : e = ⟨leafPar F w', leafPar_mem F w'⟩ := Subtype.ext he.symm
    rw [this]
    rfl
  cases u with
  | inl v' =>
    cases w with
    | inl w' => exact absurd huw id
    | inr e =>
      have h : leafPar F v' = e.1 := huw
      simp only [leafB, Sum.elim_inl, Sum.elim_inr, decide_eq_false_iff_not]
      exact key v' e h hne
  | inr e =>
    cases w with
    | inl v' =>
      have h : leafPar F v' = e.1 := huw
      simp only [leafB, Sum.elim_inl, Sum.elim_inr, decide_eq_false_iff_not, eq_comm (a := false)]
      exact key v' e h (by rwa [Sym2.eq_swap] at hne)
    | inr e' => rfl

/-! ### `canonGraph F` is a tree -/

theorem sep_node_edge (hF : IsTSP F) (hn : 2 ≤ n) {d : Fin n × Fin n} (hd : d ∈ F) :
    Sep (canonGraph F) s(canonNd (mem_nodes_of_mem hd), canonUp F d)
      (canonNd (mem_nodes_of_mem hd)) (canonUp F d) := by
  refine sep_of_cut (belowB F d) (fun u w => belowB_const hF hn hd u w) ?_
  have h1 : ArcLe d d := ⟨le_refl _, le_refl _⟩
  have h2 : ¬ ArcLe (nodePar F d) d := not_arcLe_nodePar_self hF hn hd
  simp [belowB, canonNd, canonUp, h1, h2]

theorem sep_leaf_edge (v : Fin n) :
    Sep (canonGraph F) s(Sum.inl v, canonPar F v) (Sum.inl v) (canonPar F v) := by
  refine sep_of_cut (leafB F v) (fun u w => leafB_const v u w) ?_
  simp [leafB, canonPar]

/-- Every edge of `canonGraph F` is a leaf edge or a node edge, and either way a bridge. -/
theorem sep_of_adj_canon (hF : IsTSP F) (hn : 2 ≤ n) {x y : CanonV F}
    (hxy : (canonGraph F).Adj x y) : Sep (canonGraph F) s(x, y) x y := by
  cases x with
  | inl v =>
    cases y with
    | inl w => exact absurd hxy id
    | inr e =>
      have h : leafPar F v = e.1 := hxy
      have hy : (Sum.inr e : CanonV F) = canonPar F v := congrArg Sum.inr (Subtype.ext h.symm)
      rw [hy]
      exact sep_leaf_edge v
  | inr e =>
    cases y with
    | inl v =>
      have h : leafPar F v = e.1 := hxy
      have hx : (Sum.inr e : CanonV F) = canonPar F v := congrArg Sum.inr (Subtype.ext h.symm)
      rw [hx, Sym2.eq_swap, sep_comm]
      exact sep_leaf_edge v
    | inr e' =>
      obtain ⟨-, hcase⟩ := hxy
      have main : ∀ f f' : {d : Fin n × Fin n // d ∈ nodes F}, f.1 ≠ wholeP n →
          nodePar F f.1 = f'.1 →
          Sep (canonGraph F) s(Sum.inr f, Sum.inr f') (Sum.inr f) (Sum.inr f') := by
        intro f f' hfw hff'
        have hfF : f.1 ∈ F := mem_F_of_mem_nodes f.2 hfw
        have hx : canonNd (mem_nodes_of_mem hfF) = (Sum.inr f : CanonV F) := rfl
        have hy : canonUp F f.1 = (Sum.inr f' : CanonV F) := congrArg Sum.inr (Subtype.ext hff')
        have := sep_node_edge hF hn hfF
        rwa [hx, hy] at this
      rcases hcase with ⟨hfw, hff'⟩ | ⟨hfw, hff'⟩
      · exact main e e' hfw hff'
      · rw [Sym2.eq_swap, sep_comm]
        exact main e' e hfw hff'

theorem canonGraph_isAcyclic (hF : IsTSP F) (hn : 2 ≤ n) : (canonGraph F).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro x y hxy
  rw [isBridge_iff_forall_walk_mem_edges]
  exact sep_iff_forall_walk.mp (sep_of_adj_canon hF hn hxy)

theorem arcWidth_lt_nodePar (hF : IsTSP F) (hn : 2 ≤ n) {d : Fin n × Fin n} (hd : d ∈ nodes F)
    (hdw : d ≠ wholeP n) : arcWidth d < arcWidth (nodePar F d) := by
  obtain ⟨-, hle, hne, -⟩ := nodePar_spec hF hn hd hdw
  have h1 := arcWidth_le_of_arcLe hle
  rcases Nat.lt_or_ge (arcWidth d) (arcWidth (nodePar F d)) with h | h
  · exact h
  · exact absurd (eq_of_arcLe_of_width (le_of_lt (lt_of_mem_nodes hF hn hd)) hle h).symm hne

theorem reachable_node_whole (hF : IsTSP F) (hn : 2 ≤ n) :
    ∀ (k : ℕ) (d : Fin n × Fin n) (hd : d ∈ nodes F),
      arcWidth (wholeP n) - arcWidth d ≤ k →
      (canonGraph F).Reachable (canonNd hd) (canonNd (wholeP_mem_nodes F)) := by
  intro k
  induction k with
  | zero =>
    intro d hd hk
    have hle : arcWidth d ≤ arcWidth (wholeP n) := arcWidth_le_of_arcLe (arcLe_wholeP d)
    have heq : d = wholeP n :=
      eq_of_arcLe_of_width (le_of_lt (lt_of_mem_nodes hF hn hd)) (arcLe_wholeP d) (by omega)
    subst heq
    exact Reachable.refl _
  | succ k ih =>
    intro d hd hk
    by_cases hdw : d = wholeP n
    · subst hdw; exact Reachable.refl _
    · have hdF : d ∈ F := mem_F_of_mem_nodes hd hdw
      have hlt := arcWidth_lt_nodePar hF hn hd hdw
      have hle : arcWidth (nodePar F d) ≤ arcWidth (wholeP n) :=
        arcWidth_le_of_arcLe (arcLe_wholeP _)
      have hadj : (canonGraph F).Adj (canonNd hd) (canonUp F d) := canonGraph_adj_up hF hn hdF
      refine Reachable.trans hadj.reachable ?_
      exact ih (nodePar F d) (nodePar_mem F d) (by omega)

theorem reachable_whole (hF : IsTSP F) (hn : 2 ≤ n) (u : CanonV F) :
    (canonGraph F).Reachable u (canonNd (wholeP_mem_nodes F)) := by
  cases u with
  | inl v =>
    exact Reachable.trans (canonGraph_adj_canonPar v).reachable
      (reachable_node_whole hF hn _ (leafPar F v) (leafPar_mem F v) le_rfl)
  | inr e => exact reachable_node_whole hF hn _ e.1 e.2 le_rfl

theorem canonGraph_connected (hF : IsTSP F) (hn : 2 ≤ n) : (canonGraph F).Connected := by
  rw [connected_iff]
  exact ⟨fun u v => (reachable_whole hF hn u).trans (reachable_whole hF hn v).symm,
    ⟨canonNd (wholeP_mem_nodes F)⟩⟩

theorem canonGraph_isTree (hF : IsTSP F) (hn : 2 ≤ n) : (canonGraph F).IsTree :=
  ⟨canonGraph_connected hF hn, canonGraph_isAcyclic hF hn⟩

/-! ### Degrees -/

theorem neighborSet_inl (v : Fin n) :
    (canonGraph F).neighborSet (Sum.inl v) = {canonPar F v} := by
  ext u
  rw [mem_neighborSet, Set.mem_singleton_iff]
  exact canonGraph_adj_inl_iff

theorem ncard_neighborSet_inl (v : Fin n) :
    ((canonGraph F).neighborSet (Sum.inl v)).ncard = 1 := by
  rw [neighborSet_inl, Set.ncard_singleton]

/-- A neighbour of the node `d` lying on the far side from the root leaf `n - 1`. -/
def IsChild (F : Finset (Fin n × Fin n)) (d : Fin n × Fin n) : CanonV F → Prop :=
  Sum.elim (fun v => InArc d v) (fun c => ArcLe c.1 d ∧ c.1 ≠ d)

/-- Every leaf in the arc of a node `d` is reached from `d` through a neighbour of `d`: the
leaf itself, or the largest node strictly below `d` whose arc contains it. -/
theorem exists_child (hF : IsTSP F) (hn : 2 ≤ n) {d : Fin n × Fin n} (hd : d ∈ nodes F)
    {v : Fin n} (hv : InArc d v) :
    ∃ u : CanonV F, (canonGraph F).Adj (canonNd hd) u ∧
      (u = Sum.inl v ∨ ∃ c : {c : Fin n × Fin n // c ∈ nodes F},
        u = Sum.inr c ∧ InArc c.1 v ∧ ArcLe c.1 d ∧ c.1 ≠ d) := by
  by_cases hlp : leafPar F v = d
  · exact ⟨Sum.inl v, hlp, Or.inl rfl⟩
  · have hvr : v.val < n - 1 := lt_of_inArc hv
    have hlpS : leafPar F v ∈ (nodes F).filter (fun c => InArc c v ∧ ArcLe c d ∧ c ≠ d) :=
      Finset.mem_filter.2 ⟨leafPar_mem F v, (leafPar_spec hF hvr).1,
        (leafPar_spec hF hvr).2 d hd hv, hlp⟩
    obtain ⟨c, hcS, hcmax⟩ :=
      ((nodes F).filter (fun c => InArc c v ∧ ArcLe c d ∧ c ≠ d)).exists_max_image arcWidth
        ⟨_, hlpS⟩
    obtain ⟨hcn, hcv, hcd, hcne⟩ := Finset.mem_filter.1 hcS
    have hcw : c ≠ wholeP n := by
      rintro rfl
      exact hcne (ArcLe.antisymm (arcLe_wholeP d) hcd).symm
    have hpar : nodePar F c = d := by
      by_contra hne
      obtain ⟨hmem, hle, -, hmin⟩ := nodePar_spec hF hn hcn hcw
      have h1 : ArcLe (nodePar F c) d := hmin d hd hcd (Ne.symm hcne)
      have h2 : InArc (nodePar F c) v := hcv.mono hle
      have h3 := hcmax _ (Finset.mem_filter.2 ⟨hmem, h2, h1, hne⟩)
      have h4 := arcWidth_lt_nodePar hF hn hcn hcw
      omega
    exact ⟨Sum.inr ⟨c, hcn⟩, ⟨Ne.symm hcne, Or.inr ⟨hcw, hpar⟩⟩,
      Or.inr ⟨⟨c, hcn⟩, rfl, hcv, hcd, hcne⟩⟩

theorem exists_two_children (hF : IsTSP F) (hn : 2 ≤ n) {d : Fin n × Fin n} (hd : d ∈ nodes F)
    (hw : 2 ≤ arcWidth d) :
    ∃ u₁ u₂ : CanonV F, (canonGraph F).Adj (canonNd hd) u₁ ∧
      (canonGraph F).Adj (canonNd hd) u₂ ∧ u₁ ≠ u₂ ∧ IsChild F d u₁ ∧ IsChild F d u₂ := by
  have hd12 : d.1.val < d.2.val := by
    have := lt_of_mem_nodes hF hn hd; rwa [Fin.lt_def] at this
  have hd2 := d.2.isLt
  have harc : arcWidth d = d.2.val - d.1.val := rfl
  set v₂ : Fin n := ⟨d.2.val - 1, by omega⟩ with hv₂
  have h₁ : InArc d d.1 := ⟨le_refl _, by rw [Fin.lt_def]; omega⟩
  have h₂ : InArc d v₂ := by
    refine ⟨?_, ?_⟩ <;> simp only [hv₂, Fin.le_def, Fin.lt_def] <;> omega
  obtain ⟨u₁, ha₁, hcov₁⟩ := exists_child hF hn hd h₁
  obtain ⟨u₂, ha₂, hcov₂⟩ := exists_child hF hn hd h₂
  have hvne : d.1 ≠ v₂ := by
    intro hc
    have := congrArg Fin.val hc
    simp only [hv₂] at this
    omega
  refine ⟨u₁, u₂, ha₁, ha₂, ?_, ?_, ?_⟩
  · rcases hcov₁ with rfl | ⟨c, rfl, hc₁, hc₂, hc₃⟩
    · rcases hcov₂ with rfl | ⟨c', rfl, -, -, -⟩
      · exact fun hc => hvne (Sum.inl_injective hc)
      · exact fun hc => by simp at hc
    · rcases hcov₂ with rfl | ⟨c', rfl, hc₁', -, -⟩
      · exact fun hc => by simp at hc
      · intro hc
        have hcc : c = c' := Sum.inr_injective hc
        subst hcc
        refine hc₃ ?_
        have e1 : c.1.1.val = d.1.val := by
          have := hc₁.1; have := hc₂.1
          simp only [Fin.le_def] at *; omega
        have e2 : c.1.2.val = d.2.val := by
          have := hc₁'.2; have := hc₂.2
          simp only [Fin.lt_def, Fin.le_def, hv₂] at *; omega
        exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  · rcases hcov₁ with rfl | ⟨c, rfl, -, hc₂, hc₃⟩
    · exact h₁
    · exact ⟨hc₂, hc₃⟩
  · rcases hcov₂ with rfl | ⟨c, rfl, -, hc₂, hc₃⟩
    · exact h₂
    · exact ⟨hc₂, hc₃⟩

theorem arcWidth_wholeP : arcWidth (wholeP n) = n - 1 := by
  simp only [arcWidth, wholeP, Fin.val_zero, Nat.sub_zero]

theorem three_le_ncard_neighborSet_node (hF : IsTSP F) (hn : 3 ≤ n) {d : Fin n × Fin n}
    (hd : d ∈ nodes F) : 3 ≤ ((canonGraph F).neighborSet (canonNd hd)).ncard := by
  have hn2 : 2 ≤ n := by omega
  have hw : 2 ≤ arcWidth d := by
    by_cases hdw : d = wholeP n
    · subst hdw
      rw [arcWidth_wholeP]
      omega
    · obtain ⟨h1, h2, -⟩ := hF.1 d (mem_F_of_mem_nodes hd hdw)
      rw [Fin.lt_def] at h1
      simp only [arcWidth]
      omega
  obtain ⟨u₁, u₂, ha₁, ha₂, hne, hc₁, hc₂⟩ := exists_two_children hF hn2 hd hw
  obtain ⟨u₃, ha₃, hnot₃⟩ : ∃ u₃, (canonGraph F).Adj (canonNd hd) u₃ ∧ ¬ IsChild F d u₃ := by
    by_cases hdw : d = wholeP n
    · subst hdw
      refine ⟨Sum.inl ⟨n - 1, by omega⟩, leafPar_root F rfl, ?_⟩
      intro h
      have := lt_of_inArc (d := wholeP n) h
      simp only at this
      omega
    · have hdF := mem_F_of_mem_nodes hd hdw
      exact ⟨canonUp F d, canonGraph_adj_up hF hn2 hdF,
        fun h => (not_arcLe_nodePar_self hF hn2 hdF) h.1⟩
  have hsub : ({u₁, u₂, u₃} : Set (CanonV F)) ⊆ (canonGraph F).neighborSet (canonNd hd) := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    simp only [mem_neighborSet]
    rcases hu with rfl | rfl | rfl
    · exact ha₁
    · exact ha₂
    · exact ha₃
  have h3 : ({u₁, u₂, u₃} : Set (CanonV F)).ncard = 3 := by
    refine Set.ncard_eq_three.2 ⟨u₁, u₂, u₃, hne, ?_, ?_, rfl⟩
    · rintro rfl; exact hnot₃ hc₁
    · rintro rfl; exact hnot₃ hc₂
  rw [← h3]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-! ### The two region paths through each edge -/

theorem add_one_ne_self (hn : 2 ≤ n) (v : Fin n) : v + 1 ≠ v := by
  intro h
  have h2 : v = v - 1 := by
    conv_lhs => rw [← add_sub_cancel_right v 1]
    rw [h]
  have h3 := congrArg Fin.val h2
  rw [fin_val_sub_one] at h3
  have hv := v.isLt
  split_ifs at h3 <;> omega

/-- The indicator of the arc of a diagonal `d` changes exactly at `d.1` and at `d.2`. -/
theorem inArc_cycChange {d : Fin n × Fin n} (hdiag : IsDiag n d.1 d.2) (i : Fin n) :
    ¬ (InArc d (i - 1) ↔ InArc d i) ↔ (i = d.1 ∨ i = d.2) := by
  obtain ⟨h1, h2, h3⟩ := hdiag
  rw [Fin.lt_def] at h1
  have hi := i.isLt
  have hd2 := d.2.isLt
  have hpos := NeZero.pos n
  have hsub := fin_val_sub_one i
  have key1 : (i = d.1) ↔ (i.val = d.1.val) := ⟨fun h => by rw [h], fun h => Fin.ext h⟩
  have key2 : (i = d.2) ↔ (i.val = d.2.val) := ⟨fun h => by rw [h], fun h => Fin.ext h⟩
  simp only [InArc, Fin.le_def, Fin.lt_def, key1, key2, hsub]
  split_ifs with hi0 <;> omega

theorem sep_inl_node (hF : IsTSP F) (hn : 2 ≤ n) {d : Fin n × Fin n} (hd : d ∈ F) (v : Fin n) :
    Sep (canonGraph F) s(canonNd (mem_nodes_of_mem hd), canonUp F d)
      (Sum.inl v) (canonNd (mem_nodes_of_mem hd)) ↔ ¬ InArc d v := by
  constructor
  · intro hsep hv
    have hb : belowB F d (Sum.inl v) = true := by
      simp only [belowB, Sum.elim_inl, decide_eq_true_eq]
      exact (arcLe_leafPar_iff_inArc hF hd v).2 hv
    have hb2 : belowB F d (canonUp F d) = false := by
      simp only [belowB, canonUp, Sum.elim_inr, decide_eq_false_iff_not]
      exact not_arcLe_nodePar_self hF hn hd
    have h1 : Sep (canonGraph F) s(canonNd (mem_nodes_of_mem hd), canonUp F d)
        (Sum.inl v) (canonUp F d) :=
      sep_of_cut (belowB F d) (fun u w => belowB_const hF hn hd u w) (by rw [hb, hb2]; simp)
    exact ((sep_right_iff (canonGraph_isTree hF hn) (canonGraph_adj_up hF hn hd) _).1 h1) hsep
  · intro hv
    have hb : belowB F d (Sum.inl v) = false := by
      simp only [belowB, Sum.elim_inl, decide_eq_false_iff_not]
      exact fun h => hv ((arcLe_leafPar_iff_inArc hF hd v).1 h)
    have hb2 : belowB F d (canonNd (mem_nodes_of_mem hd)) = true := by
      simp only [belowB, canonNd, Sum.elim_inr, decide_eq_true_eq]
      exact ⟨le_refl _, le_refl _⟩
    exact sep_of_cut (belowB F d) (fun u w => belowB_const hF hn hd u w) (by rw [hb, hb2]; simp)

/-- The region paths through the edge above the node `d` are exactly `P_{d.1}` and `P_{d.2}`. -/
theorem onRegion_node (hF : IsTSP F) (hn : 2 ≤ n) {d : Fin n × Fin n} (hd : d ∈ F) (i : Fin n) :
    OnRegion (canonGraph F) (Sum.inl : Fin n → CanonV F) i
      s(canonNd (mem_nodes_of_mem hd), canonUp F d) ↔ (i = d.1 ∨ i = d.2) := by
  rw [OnRegion, sep_iff_not_iff (canonGraph_isTree hF hn) (canonGraph_adj_up hF hn hd),
    sep_inl_node hF hn hd, sep_inl_node hF hn hd, ← inArc_cycChange (hF.1 d hd) i]
  tauto

theorem sep_leaf_inl (v w : Fin n) :
    Sep (canonGraph F) s(Sum.inl v, canonPar F v) (Sum.inl w) (Sum.inl v) ↔ w ≠ v := by
  constructor
  · rintro h rfl
    exact not_sep_self _ _ _ h
  · intro hw
    refine sep_of_cut (leafB F v) (fun u w' => leafB_const v u w') ?_
    simp [leafB, hw]

/-- The region paths through the leaf edge at `v` are exactly `P_v` and `P_{v+1}`. -/
theorem onRegion_leaf (hF : IsTSP F) (hn : 2 ≤ n) (v : Fin n) (i : Fin n) :
    OnRegion (canonGraph F) (Sum.inl : Fin n → CanonV F) i s(Sum.inl v, canonPar F v) ↔
      (i = v ∨ i = v + 1) := by
  have hsub : (i - 1 = v) ↔ (i = v + 1) := sub_eq_iff_eq_add
  have hvv : v + 1 ≠ v := add_one_ne_self hn v
  rw [OnRegion, sep_iff_not_iff (canonGraph_isTree hF hn) (canonGraph_adj_canonPar v),
    sep_leaf_inl, sep_leaf_inl]
  simp only [ne_eq, hsub]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h ⟨fun _ => hc.1, fun _ => hc.2⟩
  · rintro (rfl | rfl) hiff
    · exact hiff.1 (Ne.symm hvv) rfl
    · exact hiff.2 hvv rfl

/-- Every edge of `canonGraph F` is a leaf edge or the edge above a node of `F`. -/
theorem canon_edge_cases {e : Sym2 (CanonV F)}
    (he : e ∈ (canonGraph F).edgeSet) :
    (∃ v : Fin n, e = s(Sum.inl v, canonPar F v)) ∨
      (∃ d : Fin n × Fin n, ∃ hd : d ∈ F,
        e = s(canonNd (mem_nodes_of_mem hd), canonUp F d)) := by
  induction e using Sym2.ind with
  | _ x y =>
  rw [mem_edgeSet] at he
  cases x with
  | inl v =>
    cases y with
    | inl w => exact absurd he id
    | inr c =>
      have h : leafPar F v = c.1 := he
      have hc : (Sum.inr c : CanonV F) = canonPar F v := congrArg Sum.inr (Subtype.ext h.symm)
      exact Or.inl ⟨v, by rw [hc]⟩
  | inr c =>
    cases y with
    | inl v =>
      have h : leafPar F v = c.1 := he
      have hc : (Sum.inr c : CanonV F) = canonPar F v := congrArg Sum.inr (Subtype.ext h.symm)
      exact Or.inl ⟨v, by rw [hc, Sym2.eq_swap]⟩
    | inr c' =>
      obtain ⟨-, hcase⟩ := he
      rcases hcase with ⟨hcw, hcc⟩ | ⟨hcw, hcc⟩
      · have hcF : c.1 ∈ F := mem_F_of_mem_nodes c.2 hcw
        refine Or.inr ⟨c.1, hcF, ?_⟩
        have h2 : canonUp F c.1 = (Sum.inr c' : CanonV F) := congrArg Sum.inr (Subtype.ext hcc)
        rw [h2]
        rfl
      · have hcF : c'.1 ∈ F := mem_F_of_mem_nodes c'.2 hcw
        refine Or.inr ⟨c'.1, hcF, ?_⟩
        have h2 : canonUp F c'.1 = (Sum.inr c : CanonV F) := congrArg Sum.inr (Subtype.ext hcc)
        rw [h2, Sym2.eq_swap]
        rfl

theorem canon_planar (hF : IsTSP F) (hn : 2 ≤ n) (e : Sym2 (CanonV F))
    (he : e ∈ (canonGraph F).edgeSet) :
    {i : Fin n | Sep (canonGraph F) e (Sum.inl (i - 1)) (Sum.inl i)}.ncard = 2 := by
  rcases canon_edge_cases he with ⟨v, rfl⟩ | ⟨d, hd, rfl⟩
  · have hset : {i : Fin n | Sep (canonGraph F) s(Sum.inl v, canonPar F v)
        (Sum.inl (i - 1)) (Sum.inl i)} = {v, v + 1} := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact onRegion_leaf hF hn v i
    rw [hset, Set.ncard_pair (Ne.symm (add_one_ne_self hn v))]
  · have hset : {i : Fin n | Sep (canonGraph F) s(canonNd (mem_nodes_of_mem hd), canonUp F d)
        (Sum.inl (i - 1)) (Sum.inl i)} = {d.1, d.2} := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact onRegion_node hF hn hd i
    rw [hset, Set.ncard_pair (ne_of_lt (hF.1 d hd).1)]

/-! ### `canonGraph F` is a canonical tree, and its pair set is `F` -/

theorem isCanonicalTree_canonGraph (hF : IsTSP F) (hn : 3 ≤ n) :
    IsCanonicalTree n (canonGraph F) (Sum.inl : Fin n → CanonV F) where
  tree := canonGraph_isTree hF (by omega)
  inj := Sum.inl_injective
  leaf_degree := ncard_neighborSet_inl
  internal_degree := by
    rintro (v | c) hv
    · exact absurd (Set.mem_range_self v) hv
    · exact three_le_ncard_neighborSet_node hF hn c.2
  planar := canon_planar hF (by omega)

/-- A leaf edge carries two *adjacent* region indices, so it is never a diagonal. -/
theorem not_adjacent_pair (hn : 2 ≤ n) {d : Fin n × Fin n} (hdiag : IsDiag n d.1 d.2)
    (v : Fin n) (h1 : d.1 = v ∨ d.1 = v + 1) (h2 : d.2 = v ∨ d.2 = v + 1) : False := by
  obtain ⟨hlt, h2', h3'⟩ := hdiag
  rw [Fin.lt_def] at hlt
  have hv1 := d.1.isLt
  have hv2 := d.2.isLt
  rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2
  · rw [e1, e2] at hlt; omega
  · have hs : d.2 - 1 = d.1 := by rw [e1, e2, add_sub_cancel_right]
    have hv := congrArg Fin.val hs
    rw [fin_val_sub_one] at hv
    split_ifs at hv <;> omega
  · have hs : d.1 - 1 = d.2 := by rw [e1, e2, add_sub_cancel_right]
    have hv := congrArg Fin.val hs
    rw [fin_val_sub_one] at hv
    split_ifs at hv <;> omega
  · rw [e1, e2] at hlt; omega

/-- **Lemma 3.2 (2).**  The pair set of the canonical tree built from `F` is `F` itself. -/
theorem FGamma_canonGraph (hF : IsTSP F) (hn : 2 ≤ n) :
    FGamma (canonGraph F) (Sum.inl : Fin n → CanonV F) = ↑F := by
  ext d
  constructor
  · rintro ⟨hdiag, e, he, h1, h2⟩
    rcases canon_edge_cases he with ⟨v, rfl⟩ | ⟨c, hc, rfl⟩
    · rw [onRegion_leaf hF hn] at h1 h2
      exact absurd (not_adjacent_pair hn hdiag v h1 h2) not_false
    · rw [onRegion_node hF hn hc] at h1 h2
      have hd12 : d.1.val < d.2.val := by rw [← Fin.lt_def]; exact hdiag.1
      have hc12 : c.1.val < c.2.val := by rw [← Fin.lt_def]; exact (hF.1 c hc).1
      have v1 : d.1.val = c.1.val ∨ d.1.val = c.2.val := by
        rcases h1 with h | h
        · exact Or.inl (congrArg Fin.val h)
        · exact Or.inr (congrArg Fin.val h)
      have v2 : d.2.val = c.1.val ∨ d.2.val = c.2.val := by
        rcases h2 with h | h
        · exact Or.inl (congrArg Fin.val h)
        · exact Or.inr (congrArg Fin.val h)
      have hdc : d = c := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
      rw [hdc]
      exact Finset.mem_coe.2 hc
  · intro hd
    rw [Finset.mem_coe] at hd
    exact ⟨hF.1 d hd, s(canonNd (mem_nodes_of_mem hd), canonUp F d),
      (mem_edgeSet _).2 (canonGraph_adj_up hF hn hd),
      (onRegion_node hF hn hd d.1).2 (Or.inl rfl),
      (onRegion_node hF hn hd d.2).2 (Or.inr rfl)⟩

/-- **Lemma 3.2, realization.**  Every crossing-free set of diagonals of the `n`-gon is
`F (Γ)` for some canonical tree `Γ`. -/
theorem exists_isCanonicalTree_of_mem_TSP (hn : 3 ≤ n) (hF : F ∈ TSP n) :
    ∃ (V : Type) (_ : Finite V) (Γ : SimpleGraph V) (a : Fin n → V),
      IsCanonicalTree n Γ a ∧ (Set.toFinite (FGamma Γ a)).toFinset = F := by
  refine ⟨CanonV F, inferInstance, canonGraph F, Sum.inl,
    isCanonicalTree_canonGraph (isTSP_of_mem_TSP hF) hn, ?_⟩
  apply Finset.coe_injective
  rw [Set.Finite.coe_toFinset]
  exact FGamma_canonGraph (isTSP_of_mem_TSP hF) (by omega)

/-- **Lemma 3.2: the image of `Γ ↦ F (Γ)` is exactly `T_SP (P_a) = RBM.TSP n`.**  The
inclusion `⊆` is `RBM.FGamma_mem_TSP` (Lemma 3.2 (1)); the inclusion `⊇` is the realization
above. -/
theorem mem_TSP_iff_exists_isCanonicalTree (hn : 3 ≤ n) (F : Finset (Fin n × Fin n)) :
    F ∈ TSP n ↔ ∃ (V : Type) (_ : Finite V) (Γ : SimpleGraph V) (a : Fin n → V),
      IsCanonicalTree n Γ a ∧ (Set.toFinite (FGamma Γ a)).toFinset = F := by
  refine ⟨exists_isCanonicalTree_of_mem_TSP hn, ?_⟩
  rintro ⟨V, hV, Γ, a, hcan, rfl⟩
  have := hV
  exact FGamma_mem_TSP hcan

end Realize

section Unique

variable {V : Type*} {Γ : SimpleGraph V} {n : ℕ} [NeZero n] {a : Fin n → V}

/-- The root leaf index `n - 1`: the tree of `F` is rooted at the leaf `a_{n-1}`. -/
def rootIdx (n : ℕ) [NeZero n] : Fin n := ⟨n - 1, by have := NeZero.pos n; omega⟩

theorem fin_val_add_one (v : Fin n) :
    (v + 1).val = if v.val = n - 1 then 0 else v.val + 1 := by
  have hsub := fin_val_sub_one (v + 1)
  rw [add_sub_cancel_right] at hsub
  have hb := (v + 1).isLt
  have hv := v.isLt
  have hpos := NeZero.pos n
  revert hsub hb
  generalize (v + 1).val = t
  intro hsub hb
  split_ifs at hsub ⊢ <;> omega

theorem rootIdx_add_one : rootIdx n + 1 = 0 := by
  refine Fin.ext ?_
  rw [fin_val_add_one]
  simp [rootIdx]

/-! ### The neighbour towards the root -/

theorem exists_up (hΓ : Γ.IsTree) {v r₀ : V} (hv : v ≠ r₀) :
    ∃ r, Γ.Adj v r ∧ Sep Γ s(v, r) v r₀ := by
  classical
  obtain ⟨u, hadj, q, hq⟩ := Walk.not_nil_iff.1 (Walk.not_nil_of_ne (p := treePath hΓ v r₀) hv)
  refine ⟨u, hadj, ?_⟩
  rw [sep_iff_mem_edges_treePath hΓ, hq, Walk.edges_cons]
  simp

open Classical in
/-- The neighbour of `v` lying on the side of the root leaf `a_{n-1}`. -/
noncomputable def upNb (Γ : SimpleGraph V) (a : Fin n → V) (v : V) : V :=
  if hv : ∃ r, Γ.Adj v r ∧ Sep Γ s(v, r) v (a (rootIdx n)) then hv.choose else v

theorem upNb_spec (hΓ : Γ.IsTree) {v : V} (hv : v ≠ a (rootIdx n)) :
    Γ.Adj v (upNb Γ a v) ∧ Sep Γ s(v, upNb Γ a v) v (a (rootIdx n)) := by
  classical
  have hex := exists_up hΓ hv
  have heq : upNb Γ a v = hex.choose := dite_eq_left hex
  rw [heq]
  exact hex.choose_spec

theorem upNb_unique (hΓ : Γ.IsTree) {v r : V} (hv : v ≠ a (rootIdx n)) (hadj : Γ.Adj v r)
    (hsep : Sep Γ s(v, r) v (a (rootIdx n))) : r = upNb Γ a v := by
  obtain ⟨hadj', hsep'⟩ := upNb_spec hΓ hv
  by_contra hne
  refine (sep_unique_neighbor hΓ hadj hadj' hne ((sep_comm _ _ _ _).mp hsep)) ?_
  exact (sep_comm _ _ _ _).mp hsep'

/-! ### The pendant edge at a leaf -/

open Classical in
/-- The unique neighbour of the leaf `a m`. -/
noncomputable def leafNb (Γ : SimpleGraph V) (a : Fin n → V) (m : Fin n) : V :=
  if hm : ∃ r, Γ.neighborSet (a m) = {r} then hm.choose else a m

theorem neighborSet_leaf (h : IsCanonicalTree n Γ a) (m : Fin n) :
    Γ.neighborSet (a m) = {leafNb Γ a m} := by
  classical
  have hex : ∃ r, Γ.neighborSet (a m) = {r} := Set.ncard_eq_one.1 (h.leaf_degree m)
  have heq : leafNb Γ a m = hex.choose := dite_eq_left hex
  rw [heq]
  exact hex.choose_spec

theorem adj_leafNb (h : IsCanonicalTree n Γ a) (m : Fin n) : Γ.Adj (a m) (leafNb Γ a m) := by
  have hm : leafNb Γ a m ∈ Γ.neighborSet (a m) := by
    rw [neighborSet_leaf h]; rfl
  exact hm

theorem eq_leafNb_of_adj (h : IsCanonicalTree n Γ a) {m : Fin n} {r : V} (hr : Γ.Adj (a m) r) :
    r = leafNb Γ a m := by
  have hm : r ∈ Γ.neighborSet (a m) := hr
  rw [neighborSet_leaf h, Set.mem_singleton_iff] at hm
  exact hm

/-- Deleting the pendant edge at `a m` isolates `a m`. -/
theorem sep_pendant (h : IsCanonicalTree n Γ a) (m : Fin n) (u : V) :
    Sep Γ s(a m, leafNb Γ a m) u (a m) ↔ u ≠ a m := by
  classical
  constructor
  · rintro hs rfl
    exact not_sep_self _ _ _ hs
  · intro hu
    refine sep_of_cut (fun t => decide (t = a m)) ?_ (by simp [hu])
    intro x y hxy hne
    by_cases hx : x = a m
    · subst hx
      exact absurd (congrArg (fun t => s(a m, t)) (eq_leafNb_of_adj h hxy)) hne
    · by_cases hy : y = a m
      · subst hy
        refine absurd ?_ hne
        rw [eq_leafNb_of_adj h hxy.symm, Sym2.eq_swap]
      · simp [hx, hy]

theorem onRegion_pendant (h : IsCanonicalTree n Γ a) (hn : 2 ≤ n) (m i : Fin n) :
    OnRegion Γ a i s(a m, leafNb Γ a m) ↔ (i = m ∨ i = m + 1) := by
  have hsub : (i - 1 = m) ↔ (i = m + 1) := sub_eq_iff_eq_add
  have hvv : m + 1 ≠ m := add_one_ne_self hn m
  have e1 : (a (i - 1) = a m) ↔ (i - 1 = m) := ⟨fun hh => h.inj hh, fun hh => by rw [hh]⟩
  have e2 : (a i = a m) ↔ (i = m) := ⟨fun hh => h.inj hh, fun hh => by rw [hh]⟩
  rw [OnRegion, sep_iff_not_iff h.tree (adj_leafNb h m), sep_pendant h, sep_pendant h]
  simp only [ne_eq, e1, e2, hsub]
  constructor
  · intro hh
    by_contra hc
    push Not at hc
    exact hh ⟨fun _ => hc.1, fun _ => hc.2⟩
  · rintro (rfl | rfl) hiff
    · exact hiff.1 (Ne.symm hvv) rfl
    · exact hiff.2 hvv rfl

/-! ### The pair of region indices carried by an edge -/

open Classical in
/-- The two region indices through the edge `e`, ordered. -/
noncomputable def edgePair (Γ : SimpleGraph V) (a : Fin n → V) (e : Sym2 V) : Fin n × Fin n :=
  if he : ∃ pq : Fin n × Fin n, pq.1.val < pq.2.val ∧
      ∀ i, OnRegion Γ a i e ↔ (i = pq.1 ∨ i = pq.2) then he.choose else (0, 0)

theorem edgePair_spec (h : IsCanonicalTree n Γ a) {e : Sym2 V} (he : e ∈ Γ.edgeSet) :
    (edgePair Γ a e).1.val < (edgePair Γ a e).2.val ∧
      ∀ i, OnRegion Γ a i e ↔ (i = (edgePair Γ a e).1 ∨ i = (edgePair Γ a e).2) := by
  classical
  have hex : ∃ pq : Fin n × Fin n, pq.1.val < pq.2.val ∧
      ∀ i, OnRegion Γ a i e ↔ (i = pq.1 ∨ i = pq.2) := by
    obtain ⟨p, q, hpq, hset⟩ := Set.ncard_eq_two.1 (h.planar e he)
    have key : ∀ i : Fin n, OnRegion Γ a i e ↔ (i = p ∨ i = q) := by
      intro i
      constructor
      · intro hi
        have hm : i ∈ ({p, q} : Set (Fin n)) := hset ▸ hi
        simpa using hm
      · intro hi
        have hm : i ∈ ({p, q} : Set (Fin n)) := by simpa using hi
        rw [← hset] at hm
        exact hm
    rcases lt_trichotomy p.val q.val with hlt | heq | hgt
    · exact ⟨(p, q), hlt, key⟩
    · exact absurd (Fin.ext heq) hpq
    · exact ⟨(q, p), hgt, fun i => (key i).trans (by tauto)⟩
  have heq : edgePair Γ a e = hex.choose := dite_eq_left hex
  rw [heq]
  exact hex.choose_spec

theorem edgePair_eq (h : IsCanonicalTree n Γ a) {e : Sym2 V} (he : e ∈ Γ.edgeSet) {p q : Fin n}
    (hpq : p.val < q.val) (hreg : ∀ i, OnRegion Γ a i e ↔ (i = p ∨ i = q)) :
    edgePair Γ a e = (p, q) := by
  obtain ⟨hlt, hspec⟩ := edgePair_spec h he
  have h1 : p.val = (edgePair Γ a e).1.val ∨ p.val = (edgePair Γ a e).2.val := by
    rcases (hspec p).1 ((hreg p).2 (Or.inl rfl)) with hh | hh
    · exact Or.inl (congrArg Fin.val hh)
    · exact Or.inr (congrArg Fin.val hh)
  have h2 : q.val = (edgePair Γ a e).1.val ∨ q.val = (edgePair Γ a e).2.val := by
    rcases (hspec q).1 ((hreg q).2 (Or.inr rfl)) with hh | hh
    · exact Or.inl (congrArg Fin.val hh)
    · exact Or.inr (congrArg Fin.val hh)
  have h3 : (edgePair Γ a e).1.val = p.val ∨ (edgePair Γ a e).1.val = q.val := by
    rcases (hreg _).1 ((hspec _).2 (Or.inl rfl)) with hh | hh
    · exact Or.inl (congrArg Fin.val hh)
    · exact Or.inr (congrArg Fin.val hh)
  have h4 : (edgePair Γ a e).2.val = p.val ∨ (edgePair Γ a e).2.val = q.val := by
    rcases (hreg _).1 ((hspec _).2 (Or.inr rfl)) with hh | hh
    · exact Or.inl (congrArg Fin.val hh)
    · exact Or.inr (congrArg Fin.val hh)
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · show (edgePair Γ a e).1.val = p.val
    omega
  · show (edgePair Γ a e).2.val = q.val
    omega

/-! ### Two leaves on the far side of an internal vertex -/

theorem exists_two_leaves_of_internal [Finite V] (h : IsCanonicalTree n Γ a) {x y : V} (hxy : Γ.Adj x y)
    (hx : x ∉ Set.range a) :
    ∃ m₁ m₂ : Fin n, m₁ ≠ m₂ ∧ ¬ Sep Γ s(x, y) (a m₁) x ∧ ¬ Sep Γ s(x, y) (a m₂) x := by
  have hdeg := h.internal_degree x hx
  have hy : y ∈ Γ.neighborSet x := hxy
  have hcard : 2 ≤ (Γ.neighborSet x \ {y}).ncard := by
    have := Set.ncard_sdiff_singleton_add_one hy (Set.toFinite _)
    omega
  obtain ⟨r₁, hr₁mem, -⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := Γ.neighborSet x \ {y}) (by omega) y
  obtain ⟨r₂, hr₂mem, hr₂ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := Γ.neighborSet x \ {y}) (by omega) r₁
  have hadj₁ : Γ.Adj x r₁ := hr₁mem.1
  have hadj₂ : Γ.Adj x r₂ := hr₂mem.1
  have hne₁ : r₁ ≠ y := fun hc => hr₁mem.2 (by simp [hc])
  have hne₂ : r₂ ≠ y := fun hc => hr₂mem.2 (by simp [hc])
  have hstep : ∀ r : V, Γ.Adj x r → r ≠ y → ¬ Sep Γ s(x, y) r x := by
    intro r hr hry
    refine not_sep_of_adj hr.symm ?_
    rw [Ne, Sym2.eq_iff]
    rintro (⟨hc, _⟩ | ⟨hc, _⟩)
    · exact hr.ne hc.symm
    · exact hry hc
  obtain ⟨m₁, hm₁⟩ := exists_leaf_sep h hadj₁
  obtain ⟨m₂, hm₂⟩ := exists_leaf_sep h hadj₂
  refine ⟨m₁, m₂, ?_, ?_, ?_⟩
  · intro hc
    subst hc
    exact (sep_unique_neighbor h.tree hadj₁ hadj₂ (Ne.symm hr₂ne) hm₁) hm₂
  · exact not_sep_of_sep_branch h.tree hadj₁ hxy (not_sep_self Γ _ x) (hstep r₁ hadj₁ hne₁) hm₁
  · exact not_sep_of_sep_branch h.tree hadj₂ hxy (not_sep_self Γ _ x) (hstep r₂ hadj₂ hne₂) hm₂

/-- An edge with a single leaf on one side is the pendant edge at that leaf. -/
theorem eq_leaf_of_single_leafside [Finite V] (h : IsCanonicalTree n Γ a) {x y : V} (hxy : Γ.Adj x y)
    {m₀ : Fin n} (hs : ∀ m : Fin n, ¬ Sep Γ s(x, y) (a m) x → m = m₀) : x = a m₀ := by
  by_cases hx : x ∈ Set.range a
  · obtain ⟨j, rfl⟩ := hx
    rw [hs j (not_sep_self _ _ _)]
  · obtain ⟨m₁, m₂, hne, h1, h2⟩ := exists_two_leaves_of_internal h hxy hx
    exact absurd ((hs m₁ h1).trans (hs m₂ h2).symm) hne

/-! ### The pair of an edge: a node of `F`, or a leaf pair -/

theorem wholeP_eq : wholeP n = (0, rootIdx n) := rfl

theorem edgePair_pendant_of_ne (h : IsCanonicalTree n Γ a) (hn : 2 ≤ n) {m : Fin n}
    (hm : m ≠ rootIdx n) : edgePair Γ a s(a m, leafNb Γ a m) = (m, m + 1) := by
  refine edgePair_eq h ((mem_edgeSet _).2 (adj_leafNb h m)) ?_ (onRegion_pendant h hn m)
  show m.val < (m + 1).val
  rw [fin_val_add_one]
  split_ifs with hc
  · exact absurd (Fin.ext hc : m = rootIdx n) hm
  · omega

theorem edgePair_pendant_root (h : IsCanonicalTree n Γ a) (hn : 2 ≤ n) :
    edgePair Γ a s(a (rootIdx n), leafNb Γ a (rootIdx n)) = (0, rootIdx n) := by
  refine edgePair_eq h ((mem_edgeSet _).2 (adj_leafNb h _)) ?_ ?_
  · show (0 : Fin n).val < (rootIdx n).val
    show 0 < n - 1
    omega
  · intro i
    rw [onRegion_pendant h hn, rootIdx_add_one]
    tauto

/-- The leaves on the side of `x` are exactly the arc of the edge's pair, provided the root
leaf lies on the other side. -/
theorem leafSide_eq_inArc (h : IsCanonicalTree n Γ a) {x y : V} (hxy : Γ.Adj x y)
    (hroot : Sep Γ s(x, y) x (a (rootIdx n))) (m : Fin n) :
    (¬ Sep Γ s(x, y) (a m) x) ↔ InArc (edgePair Γ a s(x, y)) m := by
  obtain ⟨hlt, hspec⟩ := edgePair_spec h ((mem_edgeSet _).2 hxy)
  have hI := leafSide_eq_Ico h hxy hlt hspec
  have hr : Sep Γ s(x, y) (a (rootIdx n)) x := (sep_comm _ _ _ _).mp hroot
  have hpx : ¬ Sep Γ s(x, y) (a (edgePair Γ a s(x, y)).1) x := by
    intro hp
    have hmem := (hI (rootIdx n)).1 (iff_of_true hr hp)
    have hq := (edgePair Γ a s(x, y)).2.isLt
    have hpos := NeZero.pos n
    have hrv : (rootIdx n).val = n - 1 := rfl
    omega
  simp only [InArc, Fin.le_def, Fin.lt_def]
  rw [← hI m]
  exact ⟨fun hm => iff_of_false hm hpx, fun hm hc => hpx (hm.mp hc)⟩

/-- An edge whose two regions are cyclically adjacent is a pendant edge. -/
theorem pendant_of_width_one [Finite V] (h : IsCanonicalTree n Γ a) {x y : V} (hxy : Γ.Adj x y)
    {p q : Fin n} (hpq : p.val < q.val) (hq : q.val = p.val + 1)
    (hspec : ∀ i, OnRegion Γ a i s(x, y) ↔ (i = p ∨ i = q)) :
    s(x, y) = s(a p, leafNb Γ a p) := by
  have hI := leafSide_eq_Ico h hxy hpq hspec
  by_cases hp : Sep Γ s(x, y) (a p) x
  · have hspec' : ∀ i, OnRegion Γ a i s(y, x) ↔ (i = p ∨ i = q) := by
      intro i; rw [Sym2.eq_swap]; exact hspec i
    have hI' := leafSide_eq_Ico h hxy.symm hpq hspec'
    have hpy : ¬ Sep Γ s(y, x) (a p) y := by
      rw [Sym2.eq_swap]
      exact fun hc => ((sep_right_iff h.tree hxy (a p)).1 hc) hp
    have hy : y = a p := by
      refine eq_leaf_of_single_leafside h hxy.symm ?_
      intro m hm
      have := (hI' m).1 (iff_of_false hm hpy)
      exact Fin.ext (by omega)
    have hx : x = leafNb Γ a p := eq_leafNb_of_adj h (by rw [← hy]; exact hxy.symm)
    rw [hx, hy, Sym2.eq_swap]
  · have hx : x = a p := by
      refine eq_leaf_of_single_leafside h hxy ?_
      intro m hm
      have := (hI m).1 (iff_of_false hm hp)
      exact Fin.ext (by omega)
    have hy : y = leafNb Γ a p := eq_leafNb_of_adj h (by rw [← hx]; exact hxy)
    rw [hx, hy]

theorem isTSP_of_FGamma (h : IsCanonicalTree n Γ a) {F : Finset (Fin n × Fin n)}
    (hFG : FGamma Γ a = ↑F) : IsTSP F := by
  refine ⟨fun d hd => ?_, fun d hd d' hd' => ?_⟩
  · have hm : d ∈ FGamma Γ a := by rw [hFG]; exact Finset.mem_coe.2 hd
    exact hm.1
  · have h1 : d ∈ FGamma Γ a := by rw [hFG]; exact Finset.mem_coe.2 hd
    have h2 : d' ∈ FGamma Γ a := by rw [hFG]; exact Finset.mem_coe.2 hd'
    exact crossingFree_FGamma h d h1 d' h2

/-- Every edge either carries a node of `F` or is the pendant edge at a non-root leaf. -/
theorem edgePair_mem_nodes_or_pendant [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) {x y : V} (hxy : Γ.Adj x y) :
    edgePair Γ a s(x, y) ∈ nodes F ∨
      ∃ m : Fin n, m ≠ rootIdx n ∧ s(x, y) = s(a m, leafNb Γ a m) := by
  obtain ⟨hlt, hspec⟩ := edgePair_spec h ((mem_edgeSet _).2 hxy)
  set p := (edgePair Γ a s(x, y)).1 with hpdef
  set q := (edgePair Γ a s(x, y)).2 with hqdef
  have hq := q.isLt
  by_cases hdiag : IsDiag n p q
  · refine Or.inl (mem_nodes_of_mem ?_)
    have hmem : (p, q) ∈ FGamma Γ a :=
      ⟨hdiag, s(x, y), (mem_edgeSet _).2 hxy, (hspec p).2 (Or.inl rfl), (hspec q).2 (Or.inr rfl)⟩
    rw [hFG] at hmem
    have : edgePair Γ a s(x, y) = (p, q) := rfl
    rw [this]
    exact Finset.mem_coe.1 hmem
  · simp only [IsDiag, not_and_or, not_not, not_lt] at hdiag
    have hplt : p < q := Fin.lt_def.2 hlt
    rcases hdiag with hc | hc | hc
    · exact absurd (Fin.le_def.1 hc) (by omega)
    · -- q = p + 1 as naturals: a pendant edge
      refine Or.inr ⟨p, ?_, pendant_of_width_one h hxy hlt (by omega) hspec⟩
      intro hcc
      have : p.val = n - 1 := congrArg Fin.val hcc
      omega
    · -- p = 0 and q = n - 1: the root node
      refine Or.inl ?_
      have hz : ((0 : Fin n) : ℕ) = 0 := by simp
      have hp0 : p = 0 := Fin.ext (by omega)
      have hqr : q = rootIdx n := Fin.ext (by
        have : (rootIdx n).val = n - 1 := rfl
        omega)
      have : edgePair Γ a s(x, y) = wholeP n := by
        rw [wholeP_eq]
        exact Prod.ext hp0 hqr
      rw [this]
      exact wholeP_mem_nodes F

/-! ### Monotonicity of arcs along the tree -/

/-- If `v` lies below the up-edge of `w`, then everything above the up-edge of `w` is above
the up-edge of `v`. -/
theorem sep_up_of_sep_up (h : IsCanonicalTree n Γ a) {v w : V} (hv : v ≠ a (rootIdx n))
    (hw : w ≠ a (rootIdx n)) (hvw : ¬ Sep Γ s(w, upNb Γ a w) v w) {t : V}
    (ht : Sep Γ s(w, upNb Γ a w) t w) : Sep Γ s(v, upNb Γ a v) t v := by
  obtain ⟨hadjv, hsepv⟩ := upNb_spec h.tree hv
  obtain ⟨hadjw, hsepw⟩ := upNb_spec h.tree hw
  have hρw : Sep Γ s(w, upNb Γ a w) (a (rootIdx n)) w := (sep_comm _ _ _ _).mp hsepw
  have h1 : ¬ Sep Γ s(v, upNb Γ a v) (a (rootIdx n)) (upNb Γ a w) :=
    not_sep_of_sep h.tree hadjw hadjv hvw hρw
  have h2 : ¬ Sep Γ s(v, upNb Γ a v) t (upNb Γ a w) :=
    not_sep_of_sep h.tree hadjw hadjv hvw ht
  have hρv : Sep Γ s(v, upNb Γ a v) (a (rootIdx n)) v := (sep_comm _ _ _ _).mp hsepv
  have h3 : Sep Γ s(v, upNb Γ a v) (upNb Γ a w) v := by
    by_contra hc
    exact (not_sep_trans h1 hc) hρv
  by_contra hc
  have h2' : ¬ Sep Γ s(v, upNb Γ a v) (upNb Γ a w) t :=
    fun hcc => h2 ((sep_comm _ _ _ _).mp hcc)
  exact (not_sep_trans h2' hc) h3

theorem inArc_mono_up (h : IsCanonicalTree n Γ a) {v w : V} (hv : v ≠ a (rootIdx n))
    (hw : w ≠ a (rootIdx n)) (hvw : ¬ Sep Γ s(w, upNb Γ a w) v w) {m : Fin n}
    (hm : InArc (edgePair Γ a s(v, upNb Γ a v)) m) :
    InArc (edgePair Γ a s(w, upNb Γ a w)) m := by
  obtain ⟨hadjv, hsepv⟩ := upNb_spec h.tree hv
  obtain ⟨hadjw, hsepw⟩ := upNb_spec h.tree hw
  rw [← leafSide_eq_inArc h hadjw hsepw]
  rw [← leafSide_eq_inArc h hadjv hsepv] at hm
  exact fun hc => hm (sep_up_of_sep_up h hv hw hvw hc)

omit [NeZero n] in
theorem arcLe_of_inArc_subset {c d : Fin n × Fin n} (hc : c.1.val < c.2.val)
    (hsub : ∀ m, InArc c m → InArc d m) : ArcLe c d := by
  have hc2 := c.2.isLt
  have h1 : InArc c c.1 := ⟨le_refl _, Fin.lt_def.2 hc⟩
  have hmid : InArc c ⟨c.2.val - 1, by omega⟩ := by
    constructor <;> simp only [Fin.le_def, Fin.lt_def] <;> omega
  have k1 := hsub _ h1
  have k2 := hsub _ hmid
  simp only [InArc, Fin.le_def, Fin.lt_def] at k1 k2
  exact ⟨Fin.le_def.2 (by omega), Fin.le_def.2 (by omega)⟩

/-! ### Leaves, their neighbours, and the root -/

theorem leafNb_not_mem_range [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n) (m : Fin n) :
    leafNb Γ a m ∉ Set.range a := by
  rintro ⟨j, hj⟩
  have hadj : Γ.Adj (a m) (a j) := hj ▸ adj_leafNb h m
  have hjm : j ≠ m := fun hc => hadj.ne (by rw [hc])
  obtain ⟨k, hkm, hkj⟩ : ∃ k : Fin n, k ≠ m ∧ k ≠ j := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {m, j} := by
      intro k _
      by_cases hk : k = m
      · simp [hk]
      · simp [hcon k hk]
    have hcard := Finset.card_le_card hsub
    have h2 : ({m, j} : Finset (Fin n)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have hs1 : Sep Γ s(a m, a j) (a k) (a m) := by
    have hp := (sep_pendant h m (a k)).2 (fun hc => hkm (h.inj hc))
    rwa [← hj] at hp
  have hs2 : Sep Γ s(a m, a j) (a k) (a j) := by
    have hjj : leafNb Γ a j = a m := (eq_leafNb_of_adj h hadj.symm).symm
    have := (sep_pendant h j (a k)).2 (fun hc => hkj (h.inj hc))
    rw [hjj, Sym2.eq_swap] at this
    exact this
  rcases not_sep_or_not_sep h.tree.connected hadj (a k) with hc | hc
  · exact hc hs1
  · exact hc hs2

theorem upNb_leaf (h : IsCanonicalTree n Γ a) {m : Fin n} (hm : m ≠ rootIdx n) :
    upNb Γ a (a m) = leafNb Γ a m :=
  eq_leafNb_of_adj h (upNb_spec h.tree (fun hc => hm (h.inj hc))).1

theorem upNb_leafNb_root [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n) :
    upNb Γ a (leafNb Γ a (rootIdx n)) = a (rootIdx n) := by
  have hne : leafNb Γ a (rootIdx n) ≠ a (rootIdx n) := by
    intro hc
    exact leafNb_not_mem_range h hn (rootIdx n) ⟨rootIdx n, hc.symm⟩
  refine (upNb_unique h.tree hne (adj_leafNb h (rootIdx n)).symm ?_).symm
  rw [Sym2.eq_swap]
  exact (sep_comm _ _ _ _).mp (sep_adj h.tree.isAcyclic (adj_leafNb h (rootIdx n)))

/-- The pendant pair at a non-root leaf is never a node of `F`. -/
theorem pendant_pair_not_mem_nodes (hn : 3 ≤ n) (hF : IsTSP F) {m : Fin n} (hm : m ≠ rootIdx n) :
    (m, m + 1) ∉ nodes F := by
  have hmv : m.val ≠ n - 1 := fun hc => hm (Fin.ext hc)
  have hval : (m + 1).val = m.val + 1 := by
    rw [fin_val_add_one]
    split_ifs with hc
    · exact absurd hc hmv
    · rfl
  have hb := m.isLt
  intro hmem
  by_cases hw : (m, m + 1) = wholeP n
  · have h1 : m.val = ((0 : Fin n) : ℕ) := congrArg (fun d => (Fin.val d.1)) hw
    have h2 : (m + 1).val = n - 1 := congrArg (fun d => (Fin.val d.2)) hw
    have hz : ((0 : Fin n) : ℕ) = 0 := by simp
    omega
  · obtain ⟨-, h2, -⟩ := hF.1 _ (mem_F_of_mem_nodes hmem hw)
    exact h2 hval

/-! ### The up-edge of a vertex carries a node of `F` -/

theorem upPair_mem_nodes [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) {v : V} (hv : v ∉ Set.range a) :
    edgePair Γ a s(v, upNb Γ a v) ∈ nodes F := by
  have hvr : v ≠ a (rootIdx n) := fun hc => hv ⟨rootIdx n, hc.symm⟩
  obtain ⟨hadj, hsep⟩ := upNb_spec h.tree hvr
  rcases edgePair_mem_nodes_or_pendant h hn hFG hadj with hc | ⟨m, hm, he⟩
  · exact hc
  · exfalso
    rw [Sym2.eq_iff] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hv ⟨m, h1.symm⟩
    · subst h1
      have hsep' : Sep Γ s(a m, leafNb Γ a m) (a (rootIdx n)) (leafNb Γ a m) := by
        have hh := (sep_comm _ _ _ _).mp hsep
        rw [h2, Sym2.eq_swap] at hh
        exact hh
      have hsep2 : Sep Γ s(a m, leafNb Γ a m) (a (rootIdx n)) (a m) :=
        (sep_pendant h m (a (rootIdx n))).2 (fun hc => hm (h.inj hc).symm)
      rcases not_sep_or_not_sep h.tree.connected (adj_leafNb h m) (a (rootIdx n)) with hc | hc
      · exact hc hsep2
      · exact hc hsep'

/-- Each edge is the up-edge of exactly one of its endpoints. -/
theorem exists_lower_of_edge (h : IsCanonicalTree n Γ a) {x y : V} (hxy : Γ.Adj x y) :
    ∃ z : V, z ≠ a (rootIdx n) ∧ s(z, upNb Γ a z) = s(x, y) := by
  rcases not_sep_or_not_sep h.tree.connected hxy (a (rootIdx n)) with hc | hc
  · have hy : Sep Γ s(x, y) (a (rootIdx n)) y := (sep_right_iff h.tree hxy _).2 hc
    have hyne : y ≠ a (rootIdx n) := fun hcc => not_sep_self _ _ _ (hcc ▸ hy)
    refine ⟨y, hyne, ?_⟩
    have hsy : Sep Γ s(y, x) y (a (rootIdx n)) := by
      rw [Sym2.eq_swap]
      exact (sep_comm _ _ _ _).mp hy
    have heq := upNb_unique h.tree hyne hxy.symm hsy
    rw [← heq, Sym2.eq_swap]
  · have hx : Sep Γ s(x, y) (a (rootIdx n)) x := by
      by_contra hcc
      exact hc ((sep_right_iff h.tree hxy _).2 hcc)
    have hxne : x ≠ a (rootIdx n) := fun hcc => not_sep_self _ _ _ (hcc ▸ hx)
    refine ⟨x, hxne, ?_⟩
    have heq := upNb_unique h.tree hxne hxy ((sep_comm _ _ _ _).mp hx)
    rw [← heq]

/-- Every node of `F` is carried by the up-edge of some vertex. -/
theorem exists_lower_of_node [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) {c : Fin n × Fin n} (hc : c ∈ nodes F) :
    ∃ z : V, z ≠ a (rootIdx n) ∧ edgePair Γ a s(z, upNb Γ a z) = c := by
  obtain ⟨x, y, hxy, hpair⟩ : ∃ x y : V, Γ.Adj x y ∧ edgePair Γ a s(x, y) = c := by
    by_cases hw : c = wholeP n
    · subst hw
      refine ⟨a (rootIdx n), leafNb Γ a (rootIdx n), adj_leafNb h _, ?_⟩
      rw [edgePair_pendant_root h (by omega), wholeP_eq]
    · have hcF : c ∈ F := mem_F_of_mem_nodes hc hw
      have hmem : c ∈ FGamma Γ a := by rw [hFG]; exact Finset.mem_coe.2 hcF
      obtain ⟨hdiag, e, he, h1, h2⟩ := hmem
      have hne : c.1 ≠ c.2 := ne_of_lt hdiag.1
      induction e using Sym2.ind with
      | _ x y =>
      rw [mem_edgeSet] at he
      refine ⟨x, y, he, ?_⟩
      have hreg := onRegion_iff_of_pair h ((mem_edgeSet _).2 he) hne h1 h2
      rw [edgePair_eq h ((mem_edgeSet _).2 he) (Fin.lt_def.1 hdiag.1) hreg]
  obtain ⟨z, hz, hzeq⟩ := exists_lower_of_edge h hxy
  exact ⟨z, hz, by rw [hzeq, hpair]⟩

theorem upNb_not_mem_range [Finite V] (h : IsCanonicalTree n Γ a) {v : V}
    (hv : v ≠ a (rootIdx n)) (hvr : upNb Γ a v ≠ a (rootIdx n)) :
    upNb Γ a v ∉ Set.range a := by
  rintro ⟨j, hj⟩
  obtain ⟨hadj, hsep⟩ := upNb_spec h.tree hv
  have hadj' : Γ.Adj (a j) v := by rw [hj]; exact hadj.symm
  have hvj : v = leafNb Γ a j := eq_leafNb_of_adj h hadj'
  have hs2 : Sep Γ s(a j, leafNb Γ a j) (a (rootIdx n)) (leafNb Γ a j) := by
    have hh := (sep_comm _ _ _ _).mp hsep
    rw [← hj, hvj, Sym2.eq_swap] at hh
    exact hh
  rcases not_sep_or_not_sep h.tree.connected (adj_leafNb h j) (a (rootIdx n)) with hc | hc
  · have hr : a (rootIdx n) = a j := by
      by_contra hcc
      exact hc ((sep_pendant h j (a (rootIdx n))).2 hcc)
    exact hvr (by rw [← hj, ← hr])
  · exact hc hs2

/-! ### The up-edge of a leaf's neighbour carries `leafPar` -/

theorem upPair_leafNb_root [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n) :
    edgePair Γ a s(leafNb Γ a (rootIdx n), upNb Γ a (leafNb Γ a (rootIdx n))) = wholeP n := by
  rw [upNb_leafNb_root h hn, Sym2.eq_swap, edgePair_pendant_root h (by omega), wholeP_eq]

theorem upPair_leafNb_of_ne [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) {m : Fin n} (hm : m ≠ rootIdx n) :
    edgePair Γ a s(leafNb Γ a m, upNb Γ a (leafNb Γ a m)) = leafPar F m := by
  have hF : IsTSP F := isTSP_of_FGamma h hFG
  have hwr : leafNb Γ a m ∉ Set.range a := leafNb_not_mem_range h hn m
  have hwne : leafNb Γ a m ≠ a (rootIdx n) := fun hc => hwr ⟨rootIdx n, hc.symm⟩
  have hdnodes : edgePair Γ a s(leafNb Γ a m, upNb Γ a (leafNb Γ a m)) ∈ nodes F :=
    upPair_mem_nodes h hn hFG hwr
  obtain ⟨hadjw, hsepw⟩ := upNb_spec h.tree hwne
  have hnotpend : s(a m, leafNb Γ a m) ≠ s(leafNb Γ a m, upNb Γ a (leafNb Γ a m)) := by
    intro hc
    have heq : edgePair Γ a s(leafNb Γ a m, upNb Γ a (leafNb Γ a m)) = (m, m + 1) := by
      rw [← hc, edgePair_pendant_of_ne h (by omega) hm]
    rw [heq] at hdnodes
    exact pendant_pair_not_mem_nodes hn hF hm hdnodes
  have hbelow : ¬ Sep Γ s(leafNb Γ a m, upNb Γ a (leafNb Γ a m)) (a m) (leafNb Γ a m) :=
    not_sep_of_adj (adj_leafNb h m) hnotpend
  have hinarc : InArc (edgePair Γ a s(leafNb Γ a m, upNb Γ a (leafNb Γ a m))) m :=
    (leafSide_eq_inArc h hadjw hsepw m).1 hbelow
  refine (leafPar_eq hdnodes hinarc ?_).symm
  intro c hcn hcm
  obtain ⟨z, hz, hzeq⟩ := exists_lower_of_node h hn hFG hcn
  obtain ⟨hadjz, hsepz⟩ := upNb_spec h.tree hz
  have hmz : ¬ Sep Γ s(z, upNb Γ a z) (a m) z := by
    rw [leafSide_eq_inArc h hadjz hsepz, hzeq]
    exact hcm
  have hwz : ¬ Sep Γ s(z, upNb Γ a z) (leafNb Γ a m) z := by
    have hne : s(a m, leafNb Γ a m) ≠ s(z, upNb Γ a z) := by
      intro hcc
      have heq : edgePair Γ a s(z, upNb Γ a z) = (m, m + 1) := by
        rw [← hcc, edgePair_pendant_of_ne h (by omega) hm]
      rw [hzeq] at heq
      rw [heq] at hcn
      exact pendant_pair_not_mem_nodes hn hF hm hcn
    have h1 : ¬ Sep Γ s(z, upNb Γ a z) (a m) (leafNb Γ a m) :=
      not_sep_of_adj (adj_leafNb h m) hne
    exact not_sep_trans (fun hcc => h1 ((sep_comm _ _ _ _).mp hcc)) hmz
  rw [← hzeq]
  refine arcLe_of_inArc_subset (edgePair_spec h ((mem_edgeSet _).2 hadjw)).1 ?_
  intro m' hm'
  exact inArc_mono_up h hwne hz hwz hm'

/-! ### Going up one internal edge is `nodePar` -/

theorem nodePar_upPair [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) {v : V} (hvint : v ∉ Set.range a)
    (hvr : upNb Γ a v ≠ a (rootIdx n)) :
    nodePar F (edgePair Γ a s(v, upNb Γ a v))
      = edgePair Γ a s(upNb Γ a v, upNb Γ a (upNb Γ a v)) := by
  have hF : IsTSP F := isTSP_of_FGamma h hFG
  have hv : v ≠ a (rootIdx n) := fun hc => hvint ⟨rootIdx n, hc.symm⟩
  have hwint : upNb Γ a v ∉ Set.range a := upNb_not_mem_range h hv hvr
  obtain ⟨hadjv, hsepv⟩ := upNb_spec h.tree hv
  obtain ⟨hadjw, hsepw⟩ := upNb_spec h.tree hvr
  have hdw : edgePair Γ a s(upNb Γ a v, upNb Γ a (upNb Γ a v)) ∈ nodes F :=
    upPair_mem_nodes h hn hFG hwint
  have hedgene : s(v, upNb Γ a v) ≠ s(upNb Γ a v, upNb Γ a (upNb Γ a v)) := by
    intro hc
    rw [Sym2.eq_iff] at hc
    rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hadjv.ne h1
    · have hedge : s(upNb Γ a v, upNb Γ a (upNb Γ a v)) = s(v, upNb Γ a v) := by
        rw [← h1, Sym2.eq_swap]
      have k1 : Sep Γ s(v, upNb Γ a v) (upNb Γ a v) (a (rootIdx n)) := by
        rw [← hedge]; exact hsepw
      rcases not_sep_or_not_sep h.tree.connected hadjv (a (rootIdx n)) with hcc | hcc
      · exact hcc ((sep_comm _ _ _ _).mp hsepv)
      · exact hcc ((sep_comm _ _ _ _).mp k1)
  have hvbelow : ¬ Sep Γ s(upNb Γ a v, upNb Γ a (upNb Γ a v)) v (upNb Γ a v) :=
    not_sep_of_adj hadjv hedgene
  have hle : ArcLe (edgePair Γ a s(v, upNb Γ a v))
      (edgePair Γ a s(upNb Γ a v, upNb Γ a (upNb Γ a v))) := by
    refine arcLe_of_inArc_subset (edgePair_spec h ((mem_edgeSet _).2 hadjv)).1 ?_
    intro m' hm'
    exact inArc_mono_up h hv hvr hvbelow hm'
  have hvarc : ∀ m : Fin n, InArc (edgePair Γ a s(v, upNb Γ a v)) m ↔
      ¬ Sep Γ s(v, upNb Γ a v) (a m) v := fun m => (leafSide_eq_inArc h hadjv hsepv m).symm
  have hnev : edgePair Γ a s(upNb Γ a v, upNb Γ a (upNb Γ a v))
      ≠ edgePair Γ a s(v, upNb Γ a v) := by
    intro hc
    obtain ⟨hlt, hspec⟩ := edgePair_spec h ((mem_edgeSet _).2 hadjv)
    obtain ⟨-, hspec'⟩ := edgePair_spec h ((mem_edgeSet _).2 hadjw)
    refine hedgene (edge_unique_of_paired h (i := (edgePair Γ a s(v, upNb Γ a v)).1)
      (j := (edgePair Γ a s(v, upNb Γ a v)).2) (fun hcc => by
        rw [Fin.ext_iff] at hcc; omega)
      ((mem_edgeSet _).2 hadjv) ((mem_edgeSet _).2 hadjw)
      ((hspec _).2 (Or.inl rfl)) ((hspec _).2 (Or.inr rfl)) ?_ ?_)
    · exact (hspec' _).2 (Or.inl (by rw [hc]))
    · exact (hspec' _).2 (Or.inr (by rw [hc]))
  refine nodePar_eq ?_ hdw hle hnev ?_
  · exact le_of_lt (Fin.lt_def.2 (edgePair_spec h ((mem_edgeSet _).2 hadjv)).1)
  intro c hcn hcle hcne
  obtain ⟨z, hz, hzeq⟩ := exists_lower_of_node h hn hFG hcn
  obtain ⟨hadjz, hsepz⟩ := upNb_spec h.tree hz
  have hcarc : ∀ m : Fin n, InArc c m ↔ ¬ Sep Γ s(z, upNb Γ a z) (a m) z := by
    intro m
    rw [← hzeq]
    exact (leafSide_eq_inArc h hadjz hsepz m).symm
  have hcsep : ∀ m : Fin n, InArc c m → Sep Γ s(z, upNb Γ a z) (a m) (upNb Γ a z) :=
    fun m hm => (sep_right_iff h.tree hadjz (a m)).2 ((hcarc m).1 hm)
  have hwz : ¬ Sep Γ s(z, upNb Γ a z) (upNb Γ a v) z := by
    intro hsepwz
    refine hcne (ArcLe.antisymm hcle ?_).symm
    have hzlt : c.1.val < c.2.val := by
      have := lt_of_mem_nodes hF (by omega) hcn
      rwa [Fin.lt_def] at this
    have hkey : ∀ t : V, Sep Γ s(z, upNb Γ a z) t (upNb Γ a z) →
        ¬ Sep Γ s(v, upNb Γ a v) t z := by
      intro t ht
      have hzx : ¬ Sep Γ s(upNb Γ a z, z) (upNb Γ a v) (upNb Γ a z) := by
        rw [Sym2.eq_swap]
        intro hcc
        exact ((sep_right_iff h.tree hadjz (upNb Γ a v)).1 hcc) hsepwz
      have ht' : Sep Γ s(upNb Γ a z, z) t (upNb Γ a z) := by rwa [Sym2.eq_swap]
      have hres := not_sep_of_sep h.tree hadjz.symm hadjv.symm hzx ht'
      rwa [Sym2.eq_swap] at hres
    refine arcLe_of_inArc_subset hzlt ?_
    have hm0 : InArc (edgePair Γ a s(v, upNb Γ a v)) (edgePair Γ a s(v, upNb Γ a v)).1 :=
      ⟨le_refl _, Fin.lt_def.2 (edgePair_spec h ((mem_edgeSet _).2 hadjv)).1⟩
    have hA : ¬ Sep Γ s(v, upNb Γ a v) (a (edgePair Γ a s(v, upNb Γ a v)).1) z :=
      hkey _ (hcsep _ (hm0.mono hcle))
    have hB : ¬ Sep Γ s(v, upNb Γ a v) (a (edgePair Γ a s(v, upNb Γ a v)).1) v :=
      (hvarc _).1 hm0
    have hzv : ¬ Sep Γ s(v, upNb Γ a v) z v :=
      not_sep_trans (fun hcc => hA ((sep_comm _ _ _ _).mp hcc)) hB
    intro m hm
    exact (hvarc m).2 (not_sep_trans (hkey (a m) (hcsep m hm)) hzv)
  rw [← hzeq]
  refine arcLe_of_inArc_subset (edgePair_spec h ((mem_edgeSet _).2 hadjw)).1 ?_
  intro m' hm'
  exact inArc_mono_up h hvr hz hwz hm'

/-! ### The vertex carrying a node, and the isomorphism -/

theorem upPair_leafNb [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) (m : Fin n) :
    edgePair Γ a s(leafNb Γ a m, upNb Γ a (leafNb Γ a m)) = leafPar F m := by
  by_cases hm : m = rootIdx n
  · subst hm
    rw [upPair_leafNb_root h hn, leafPar_root F rfl]
  · exact upPair_leafNb_of_ne h hn hFG hm

theorem lower_unique [Finite V] (h : IsCanonicalTree n Γ a) {z z' : V}
    (hz : z ≠ a (rootIdx n)) (hz' : z' ≠ a (rootIdx n))
    (heq : edgePair Γ a s(z, upNb Γ a z) = edgePair Γ a s(z', upNb Γ a z')) : z = z' := by
  obtain ⟨hadj, hsep⟩ := upNb_spec h.tree hz
  obtain ⟨hadj', hsep'⟩ := upNb_spec h.tree hz'
  obtain ⟨hlt, hspec⟩ := edgePair_spec h ((mem_edgeSet _).2 hadj)
  obtain ⟨-, hspec'⟩ := edgePair_spec h ((mem_edgeSet _).2 hadj')
  have hij : (edgePair Γ a s(z, upNb Γ a z)).1 ≠ (edgePair Γ a s(z, upNb Γ a z)).2 := by
    intro hcc
    rw [Fin.ext_iff] at hcc
    omega
  have hedge : s(z, upNb Γ a z) = s(z', upNb Γ a z') :=
    edge_unique_of_paired h hij ((mem_edgeSet _).2 hadj) ((mem_edgeSet _).2 hadj')
      ((hspec _).2 (Or.inl rfl)) ((hspec _).2 (Or.inr rfl))
      ((hspec' _).2 (Or.inl (by rw [heq]))) ((hspec' _).2 (Or.inr (by rw [heq])))
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have hadjzz : Γ.Adj z z' := by rw [← h2]; exact hadj
    have k1 : Sep Γ s(z, z') (a (rootIdx n)) z := by
      have hh := (sep_comm _ _ _ _).mp hsep
      rwa [h2] at hh
    have k2 : Sep Γ s(z, z') (a (rootIdx n)) z' := by
      have hh := (sep_comm _ _ _ _).mp hsep'
      rw [← h1] at hh
      rwa [Sym2.eq_swap] at hh
    rcases not_sep_or_not_sep h.tree.connected hadjzz (a (rootIdx n)) with hc | hc
    · exact hc k1
    · exact hc k2

open Classical in
/-- The vertex of `Γ` whose up-edge carries the node `c`. -/
noncomputable def ndVertex (Γ : SimpleGraph V) (a : Fin n → V) (c : Fin n × Fin n) : V :=
  if hc : ∃ z : V, z ≠ a (rootIdx n) ∧ edgePair Γ a s(z, upNb Γ a z) = c then hc.choose
  else a (rootIdx n)

theorem ndVertex_spec [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) {c : Fin n × Fin n} (hc : c ∈ nodes F) :
    ndVertex Γ a c ≠ a (rootIdx n) ∧
      edgePair Γ a s(ndVertex Γ a c, upNb Γ a (ndVertex Γ a c)) = c := by
  classical
  have hex := exists_lower_of_node h hn hFG hc
  have heq : ndVertex Γ a c = hex.choose := dite_eq_left hex
  rw [heq]
  exact hex.choose_spec

theorem ndVertex_eq [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) {c : Fin n × Fin n} (hc : c ∈ nodes F)
    {z : V} (hz : z ≠ a (rootIdx n)) (heq : edgePair Γ a s(z, upNb Γ a z) = c) :
    z = ndVertex Γ a c := by
  obtain ⟨h1, h2⟩ := ndVertex_spec h hn hFG hc
  exact lower_unique h hz h1 (by rw [heq, h2])

theorem ndVertex_not_mem_range [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) {c : Fin n × Fin n} (hc : c ∈ nodes F) :
    ndVertex Γ a c ∉ Set.range a := by
  obtain ⟨h1, h2⟩ := ndVertex_spec h hn hFG hc
  rintro ⟨j, hj⟩
  have hjr : j ≠ rootIdx n := by
    intro hcc
    exact h1 (by rw [← hj, hcc])
  rw [← hj, upNb_leaf h hjr, edgePair_pendant_of_ne h (by omega) hjr] at h2
  rw [← h2] at hc
  exact pendant_pair_not_mem_nodes hn (isTSP_of_FGamma h hFG) hjr hc

theorem upPair_ne_wholeP [Finite V] (h : IsCanonicalTree n Γ a) {v : V}
    (hvint : v ∉ Set.range a) (hvr : upNb Γ a v ≠ a (rootIdx n)) :
    edgePair Γ a s(v, upNb Γ a v) ≠ wholeP n := by
  intro hw
  have hv : v ≠ a (rootIdx n) := fun hc => hvint ⟨rootIdx n, hc.symm⟩
  obtain ⟨hadjv, hsepv⟩ := upNb_spec h.tree hv
  have hwint : upNb Γ a v ∉ Set.range a := upNb_not_mem_range h hv hvr
  obtain ⟨m₁, m₂, hne, k1, k2⟩ := exists_two_leaves_of_internal h hadjv.symm hwint
  have key : ∀ m : Fin n, ¬ Sep Γ s(upNb Γ a v, v) (a m) (upNb Γ a v) → m = rootIdx n := by
    intro m hm
    rw [Sym2.eq_swap] at hm
    have hsm : Sep Γ s(v, upNb Γ a v) (a m) v := by
      by_contra hcc
      exact hm ((sep_right_iff h.tree hadjv (a m)).2 hcc)
    have hnot : ¬ InArc (edgePair Γ a s(v, upNb Γ a v)) m := by
      rw [← leafSide_eq_inArc h hadjv hsepv m]
      exact fun hcc => hcc hsm
    rw [hw] at hnot
    refine Fin.ext ?_
    have hmv := m.isLt
    have hpos := NeZero.pos n
    have hz : ((0 : Fin n) : ℕ) = 0 := by simp
    have hrv : (rootIdx n).val = n - 1 := rfl
    simp only [InArc, wholeP, Fin.le_def, Fin.lt_def, not_and, not_lt] at hnot
    omega
  exact hne ((key m₁ k1).trans (key m₂ k2).symm)

/-- The comparison map from the concrete model to an abstract canonical tree. -/
noncomputable def canonEmb (Γ : SimpleGraph V) (a : Fin n → V) (F : Finset (Fin n × Fin n)) :
    CanonV F → V := Sum.elim a (fun c => ndVertex Γ a c.1)

theorem canonEmb_bijective [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) :
    Function.Bijective (canonEmb Γ a F) := by
  constructor
  · rintro (m | c) (m' | c') heq
    · exact congrArg Sum.inl (h.inj heq)
    · exact absurd ⟨m, heq⟩ (ndVertex_not_mem_range h hn hFG c'.2)
    · exact absurd ⟨m', heq.symm⟩ (ndVertex_not_mem_range h hn hFG c.2)
    · refine congrArg Sum.inr (Subtype.ext ?_)
      obtain ⟨-, k1⟩ := ndVertex_spec h hn hFG c.2
      obtain ⟨-, k2⟩ := ndVertex_spec h hn hFG c'.2
      rw [← k1, ← k2]
      exact congrArg (fun z => edgePair Γ a s(z, upNb Γ a z)) heq
  · intro v
    by_cases hv : v ∈ Set.range a
    · obtain ⟨m, rfl⟩ := hv
      exact ⟨Sum.inl m, rfl⟩
    · have hvr : v ≠ a (rootIdx n) := fun hc => hv ⟨rootIdx n, hc.symm⟩
      have hmem : edgePair Γ a s(v, upNb Γ a v) ∈ nodes F := upPair_mem_nodes h hn hFG hv
      exact ⟨Sum.inr ⟨_, hmem⟩, (ndVertex_eq h hn hFG hmem hvr rfl).symm⟩

theorem canonEmb_adj_iff [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) (u u' : CanonV F) :
    Γ.Adj (canonEmb Γ a F u) (canonEmb Γ a F u') ↔ (canonGraph F).Adj u u' := by
  have hleaf : ∀ m : Fin n, leafNb Γ a m = ndVertex Γ a (leafPar F m) := by
    intro m
    refine ndVertex_eq h hn hFG (leafPar_mem F m) ?_ (upPair_leafNb h hn hFG m)
    exact fun hc => leafNb_not_mem_range h hn m ⟨rootIdx n, hc.symm⟩
  cases u with
  | inl m =>
    cases u' with
    | inl m' =>
      constructor
      · intro hadj
        have hadj' : Γ.Adj (a m) (a m') := hadj
        exact absurd ⟨m', eq_leafNb_of_adj h hadj'⟩ (leafNb_not_mem_range h hn m)
      · intro hc
        exact absurd hc id
    | inr c =>
      obtain ⟨-, k⟩ := ndVertex_spec h hn hFG c.2
      constructor
      · intro hadj
        have hadj' : Γ.Adj (a m) (ndVertex Γ a c.1) := hadj
        have hq : leafNb Γ a m = ndVertex Γ a c.1 := (eq_leafNb_of_adj h hadj').symm
        show leafPar F m = c.1
        rw [← k, ← hq, upPair_leafNb h hn hFG m]
      · intro hc
        have hc' : leafPar F m = c.1 := hc
        show Γ.Adj (a m) (ndVertex Γ a c.1)
        rw [← hc', ← hleaf m]
        exact adj_leafNb h m
  | inr c =>
    obtain ⟨hz, hk⟩ := ndVertex_spec h hn hFG c.2
    have hint : ndVertex Γ a c.1 ∉ Set.range a := ndVertex_not_mem_range h hn hFG c.2
    cases u' with
    | inl m =>
      constructor
      · intro hadj
        have hadj' : Γ.Adj (ndVertex Γ a c.1) (a m) := hadj
        have hq : leafNb Γ a m = ndVertex Γ a c.1 := (eq_leafNb_of_adj h hadj'.symm).symm
        show leafPar F m = c.1
        rw [← hk, ← hq, upPair_leafNb h hn hFG m]
      · intro hc
        have hc' : leafPar F m = c.1 := hc
        show Γ.Adj (ndVertex Γ a c.1) (a m)
        rw [← hc', ← hleaf m]
        exact (adj_leafNb h m).symm
    | inr c' =>
      obtain ⟨hz', hk'⟩ := ndVertex_spec h hn hFG c'.2
      have hint' : ndVertex Γ a c'.1 ∉ Set.range a := ndVertex_not_mem_range h hn hFG c'.2
      constructor
      · intro hadj
        have hadj' : Γ.Adj (ndVertex Γ a c.1) (ndVertex Γ a c'.1) := hadj
        have hcc : c.1 ≠ c'.1 := fun hcon => hadj'.ne (by rw [hcon])
        obtain ⟨z, hzr, hzeq⟩ := exists_lower_of_edge h hadj'
        refine ⟨hcc, ?_⟩
        rw [Sym2.eq_iff] at hzeq
        rcases hzeq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · subst e1
          have hup : upNb Γ a (ndVertex Γ a c.1) ≠ a (rootIdx n) := by rw [e2]; exact hz'
          have hnp := nodePar_upPair h hn hFG hint hup
          rw [hk, e2, hk'] at hnp
          have hne1 : c.1 ≠ wholeP n := by
            rw [← hk]
            exact upPair_ne_wholeP h hint hup
          exact Or.inl ⟨hne1, hnp⟩
        · subst e1
          have hup : upNb Γ a (ndVertex Γ a c'.1) ≠ a (rootIdx n) := by rw [e2]; exact hz
          have hnp := nodePar_upPair h hn hFG hint' hup
          rw [hk', e2, hk] at hnp
          have hne1 : c'.1 ≠ wholeP n := by
            rw [← hk']
            exact upPair_ne_wholeP h hint' hup
          exact Or.inr ⟨hne1, hnp⟩
      · rintro ⟨hcc, hcase⟩
        show Γ.Adj (ndVertex Γ a c.1) (ndVertex Γ a c'.1)
        rcases hcase with ⟨hw, hpar⟩ | ⟨hw, hpar⟩
        · have hup : upNb Γ a (ndVertex Γ a c.1) ≠ a (rootIdx n) := by
            intro hcon
            refine hw ?_
            rw [← hk, hcon]
            have hvj : ndVertex Γ a c.1 = leafNb Γ a (rootIdx n) :=
              eq_leafNb_of_adj h (hcon ▸ (upNb_spec h.tree hz).1).symm
            rw [hvj, Sym2.eq_swap, edgePair_pendant_root h (by omega), wholeP_eq]
          have hnp := nodePar_upPair h hn hFG hint hup
          rw [hk, hpar] at hnp
          have heq2 : upNb Γ a (ndVertex Γ a c.1) = ndVertex Γ a c'.1 :=
            ndVertex_eq h hn hFG c'.2 hup hnp.symm
          rw [← heq2]
          exact (upNb_spec h.tree hz).1
        · have hup : upNb Γ a (ndVertex Γ a c'.1) ≠ a (rootIdx n) := by
            intro hcon
            refine hw ?_
            rw [← hk', hcon]
            have hvj : ndVertex Γ a c'.1 = leafNb Γ a (rootIdx n) :=
              eq_leafNb_of_adj h (hcon ▸ (upNb_spec h.tree hz').1).symm
            rw [hvj, Sym2.eq_swap, edgePair_pendant_root h (by omega), wholeP_eq]
          have hnp := nodePar_upPair h hn hFG hint' hup
          rw [hk', hpar] at hnp
          have heq2 : upNb Γ a (ndVertex Γ a c'.1) = ndVertex Γ a c.1 :=
            ndVertex_eq h hn hFG c.2 hup hnp.symm
          rw [← heq2]
          exact ((upNb_spec h.tree hz').1).symm

/-- **The canonical tree of `F` is the only one.**  Any canonical tree with pair set `F` is
isomorphic to `canonGraph F` by a leaf-label preserving isomorphism. -/
noncomputable def canonIso [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) : canonGraph F ≃g Γ where
  toEquiv := Equiv.ofBijective (canonEmb Γ a F) (canonEmb_bijective h hn hFG)
  map_rel_iff' := canonEmb_adj_iff h hn hFG _ _

theorem canonIso_inl [Finite V] (h : IsCanonicalTree n Γ a) (hn : 3 ≤ n)
    {F : Finset (Fin n × Fin n)} (hFG : FGamma Γ a = ↑F) (m : Fin n) :
    canonIso h hn hFG (Sum.inl m) = a m := rfl

/-- **Lemma 3.2 (3): uniqueness.**  Two canonical trees of the same polygon with the same
pair set `F (Γ)` are isomorphic by an isomorphism matching the leaf labels. -/
theorem exists_iso_of_FGamma_eq [Finite V] {V' : Type*} [Finite V'] {Γ' : SimpleGraph V'}
    {a' : Fin n → V'} (h : IsCanonicalTree n Γ a) (h' : IsCanonicalTree n Γ' a') (hn : 3 ≤ n)
    (hFF : FGamma Γ a = FGamma Γ' a') : ∃ φ : Γ ≃g Γ', ∀ m, φ (a m) = a' m := by
  have hFG : FGamma Γ a = ↑(Set.toFinite (FGamma Γ a)).toFinset :=
    (Set.Finite.coe_toFinset _).symm
  have hFG' : FGamma Γ' a' = ↑(Set.toFinite (FGamma Γ a)).toFinset := by rw [← hFF]; exact hFG
  refine ⟨(canonIso h hn hFG).symm.trans (canonIso h' hn hFG'), fun m => ?_⟩
  have hinv : (canonIso h hn hFG).symm (a m) = Sum.inl m := by
    rw [← canonIso_inl h hn hFG m]
    simp
  show (canonIso h' hn hFG') ((canonIso h hn hFG).symm (a m)) = a' m
  rw [hinv]
  exact canonIso_inl h' hn hFG' m

/-! ### Anchors: the two halves of Lemma 3.2, instantiated at Figure 4 -/

/-- The tree of Figure 4 exists: `F = {{1,4},{4,6}}` (`0`-based `{(0,3),(3,5)}`) is realized
by a canonical partition of the hexagon. -/
example : ∃ (W : Type) (_ : Finite W) (G : SimpleGraph W) (b : Fin 6 → W),
    IsCanonicalTree 6 G b ∧
      (Set.toFinite (FGamma G b)).toFinset = ({(0, 3), (3, 5)} : Finset (Fin 6 × Fin 6)) :=
  exists_isCanonicalTree_of_mem_TSP (by norm_num) figure_four

/-- ... and it is the only one. -/
example {W W' : Type} [Finite W] [Finite W'] {G : SimpleGraph W} {G' : SimpleGraph W'}
    {b : Fin 6 → W} {b' : Fin 6 → W'} (hG : IsCanonicalTree 6 G b)
    (hG' : IsCanonicalTree 6 G' b') (hF : FGamma G b = FGamma G' b') :
    ∃ φ : G ≃g G', ∀ m, φ (b m) = b' m :=
  exists_iso_of_FGamma_eq hG hG' (by norm_num) hF

end Unique

end RBM
