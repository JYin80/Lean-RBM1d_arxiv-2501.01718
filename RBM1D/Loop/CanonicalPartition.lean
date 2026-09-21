/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import RBM1D.Loop.Crossing

/-!
# Lemma 3.2: canonical partitions of a polygon, via their trees

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 3.1 and Lemma 3.2
(pp. 27–28).

## The modelling step

Definition 3.1 describes a *plane* object: a partition of an oriented `n`-gon `P_a` into
subregions `R_1, …, R_n`, one per boundary edge `e_k = a_{k-1}a_k`, with each vertex `a_i`
lying in exactly two regions.  Part III of Definition 3.1 passes from the partition to its
**tree** `Γ`, obtained by deleting the boundary edges of the polygon; Lemma 3.2 and
Definition 3.3 only ever use `Γ`.  We take that step as the definition:

> **A canonical partition of `P_a` is its tree `Γ`: a finite leaf-labelled tree whose
> leaves are exactly `a_0, …, a_{n-1}`, whose internal vertices have degree `≥ 3`, and
> in which every edge lies on exactly two of the `n` region paths.**

Unpacking the three clauses (`RBM.IsCanonicalTree`):

* *leaf-labelled tree*: `Γ : SimpleGraph V` with `Γ.IsTree`, and an injection `a : Fin n → V`
  whose image is exactly the set of degree-`1` vertices;
* *internal degree `≥ 3`*: this is the normal form of the equivalence II of Definition 3.1 —
  an internal vertex of degree `2` merely subdivides an edge and changes no adjacency
  relation `R_i ∩ R_j`, so each equivalence class has exactly one representative with no
  degree-`2` internal vertex;
* *planarity*: region `R_i` has tree boundary the unique path `P_i` from `a_{i-1}` to `a_i`
  (the `i`-th polygon edge `e_i` closes it up into a polygon), and the condition "every edge
  of `Γ` lies on exactly two of the paths `P_i`" is what makes the `n` regions fit together
  into a plane partition of the polygon: it says precisely that, for every edge, the leaves
  on one side of it form a *cyclic interval* of `Fin n` (`RBM.leafSide_eq_Ico`).
  The clause of Definition 3.1 that "each `a_i` belongs to exactly two regions, `R_i` and
  `R_{i+1}`" is automatic for a leaf (`RBM.mem_support_regionPath_self`,
  `RBM.mem_support_regionPath_succ`).

Indices are `0`-based throughout: the paper's vertex `a_i` (`1 ≤ i ≤ n`) is our `a (i-1)`,
and the paper's region `R_i` is our region `i - 1`.  The index type is `Fin n`, which for
`n > 0` is the type `ZMod n` of the paper's cyclic labels; we spell it `Fin n` so that the
pair set `F (Γ)` lands literally in the index type of `RBM.Crossing` and `RBM.TSP`
(`RBM1D/Loop/Crossing.lean`).

## Main definitions

* `RBM.Sep Γ e u v` : deleting the edge `e` disconnects `u` from `v`
* `RBM.IsCanonicalTree n Γ a` : Definition 3.1 I–III in the tree model above
* `RBM.treePath`, `RBM.regionPath` : the unique path in a tree, and the tree boundary `P_i`
* `RBM.OnRegion` : the edge `e` lies on `P_i`
* `RBM.Paired`, `RBM.FGamma` : "`R_i ∩ R_j ∈ E (Γ)`" and the set `F (Γ)` of (3.1)

## Main results

* `RBM.sep_iff_mem_edges_treePath`, `RBM.onRegion_iff_mem_edges_regionPath` : `P_i` passes
  through `e` iff `e` separates `a_{i-1}` from `a_i`
* `RBM.not_sep_of_sep`, `RBM.quadrant_empty` : two distinct edges of a tree have compatible
  splits (one of the four quadrants is empty) — the tree-theoretic input to Lemma 3.2
* `RBM.interval_of_two_cycChange`, `RBM.leafSide_eq_Ico` : the planarity clause says exactly
  that the leaves on one side of an edge form a cyclic interval
* `RBM.exists_leaf_sep` : every branch of the tree reaches a polygon vertex
* `RBM.edge_unique_of_paired` : **Lemma 3.2, step 0** — two region paths share at most one
  edge, so `R_i ∩ R_j` really is a single element of `E (Γ)`
* `RBM.crossingFree_FGamma`, `RBM.FGamma_mem_TSP` : **Lemma 3.2 (1)** — `F (Γ)` has no
  crossing pairs, hence `F (Γ) ∈ RBM.TSP n`

## What is *not* proved here

Lemma 3.2 also asserts (2) that every crossing-free `F*` is realized by some `Γ`, and (3)
that `F (Γ) = F (Γ')` forces `Γ = Γ'`; together with the equivalence II of Definition 3.1
these make `Γ ↦ F (Γ)` a bijection `T_SP (P_a) ≃ RBM.TSP n`.  Only the forward map and its
crossing-freeness are formalized here, so `RBM.TSP` (`RBM1D/Loop/Crossing.lean`) is still
*defined* as the set of crossing-free diagonal sets, as recorded in `docs/paper-deltas.md`.

The model was checked against the paper's data by exhaustive enumeration outside Lean (all
leaf-labelled trees with internal degree `≥ 3` and `n` leaves, filtered by the planarity
clause): the number of such `Γ` up to leaf-preserving isomorphism is `1, 3, 11, 45, 197`
for `n = 3, …, 7`, matching `RBM.TSP_three`, `RBM.TSP_four`, `RBM.card_TSP_five`,
`RBM.card_TSP_six`, and `Γ ↦ F (Γ)` is a bijection onto `RBM.TSP n` in each case; the tree
of Figure 4 gives `F = {{1,4},{4,6}}` as the paper states (see `RBM.figure_four` below).
-/

namespace RBM

open SimpleGraph

section Sep

variable {V : Type*} {Γ : SimpleGraph V}

/-- `Sep Γ e u v`: deleting the edge `e` from `Γ` disconnects `u` from `v`.
For a tree this says exactly that the (unique) path from `u` to `v` runs through `e`. -/
def Sep (Γ : SimpleGraph V) (e : Sym2 V) (u v : V) : Prop :=
  ¬ (Γ.deleteEdges {e}).Reachable u v

theorem sep_comm (Γ : SimpleGraph V) (e : Sym2 V) (u v : V) : Sep Γ e u v ↔ Sep Γ e v u := by
  unfold Sep
  exact not_congr ⟨Reachable.symm, Reachable.symm⟩

theorem not_sep_self (Γ : SimpleGraph V) (e : Sym2 V) (u : V) : ¬ Sep Γ e u u :=
  fun h => h (Reachable.refl u)

/-- `e` separates `u` from `v` iff *every* walk from `u` to `v` uses `e`. -/
theorem sep_iff_forall_walk {e : Sym2 V} {u v : V} :
    Sep Γ e u v ↔ ∀ p : Γ.Walk u v, e ∈ p.edges := by
  induction e with
  | h x y =>
    unfold Sep
    rw [reachable_deleteEdges_iff_exists_walk]
    push Not
    rfl

/-- A cut certificate: a `Bool`-valued function constant across every edge except `e`
separates any two vertices it distinguishes. -/
theorem sep_of_cut {e : Sym2 V} (c : V → Bool)
    (hc : ∀ u v : V, Γ.Adj u v → s(u, v) ≠ e → c u = c v) {u v : V} (huv : c u ≠ c v) :
    Sep Γ e u v := by
  intro ⟨p⟩
  refine huv ?_
  clear huv
  induction p with
  | nil => rfl
  | cons h _ ih =>
    rw [deleteEdges_adj] at h
    exact (hc _ _ h.1 (by simpa using h.2)).trans ih

/-- Deleting an edge of a connected graph leaves at most two pieces: every vertex stays
attached to one of the two endpoints. -/
theorem reachable_deleteEdges_or {x y : V} (hadj : Γ.Adj x y) {u w : V} (p : Γ.Walk u w) :
    (Γ.deleteEdges {s(x, y)}).Reachable u w ∨
      ((Γ.deleteEdges {s(x, y)}).Reachable u x ∧ (Γ.deleteEdges {s(x, y)}).Reachable w y) ∨
      ((Γ.deleteEdges {s(x, y)}).Reachable u y ∧ (Γ.deleteEdges {s(x, y)}).Reachable w x) := by
  induction p with
  | nil => exact Or.inl (Reachable.refl _)
  | @cons u z w h q ih =>
    by_cases hne : s(u, z) = s(x, y)
    · rw [Sym2.eq_iff] at hne
      rcases hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨Reachable.refl _, h1.symm⟩)
        · exact Or.inr (Or.inl ⟨Reachable.refl _, h2⟩)
        · exact Or.inl h2.symm
      · rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr ⟨Reachable.refl _, h1.symm⟩)
        · exact Or.inl h2.symm
        · exact Or.inr (Or.inr ⟨Reachable.refl _, h2⟩)
    · have hR : (Γ.deleteEdges {s(x, y)}).Reachable u z :=
        (deleteEdges_adj.mpr ⟨h, by simpa using hne⟩).reachable
      rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (hR.trans h1)
      · exact Or.inr (Or.inl ⟨hR.trans h1, h2⟩)
      · exact Or.inr (Or.inr ⟨hR.trans h1, h2⟩)

/-- The two sides of an edge cover everything: no vertex is cut off from both endpoints. -/
theorem not_sep_or_not_sep (hc : Γ.Connected) {x y : V} (hadj : Γ.Adj x y) (v : V) :
    ¬ Sep Γ s(x, y) v x ∨ ¬ Sep Γ s(x, y) v y := by
  obtain ⟨p⟩ := hc v x
  rcases reachable_deleteEdges_or hadj p with h | ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact Or.inl (fun hs => hs h)
  · exact Or.inl (fun hs => hs h1)
  · exact Or.inr (fun hs => hs h1)

/-- Adjacent vertices are not separated by any *other* edge. -/
theorem not_sep_of_adj {u v : V} {e : Sym2 V} (huv : Γ.Adj u v) (hne : s(u, v) ≠ e) :
    ¬ Sep Γ e u v :=
  fun hc => hc (deleteEdges_adj.mpr ⟨huv, by simpa using hne⟩).reachable

/-- "Same side of `e`" is transitive. -/
theorem not_sep_trans {e : Sym2 V} {u v w : V} (h1 : ¬ Sep Γ e u v) (h2 : ¬ Sep Γ e v w) :
    ¬ Sep Γ e u w :=
  fun hc => hc ((not_not.mp h1).trans (not_not.mp h2))

/-- Every edge of an acyclic graph separates its own endpoints. -/
theorem sep_adj (hΓ : Γ.IsAcyclic) {x y : V} (hxy : Γ.Adj x y) : Sep Γ s(x, y) x y :=
  isAcyclic_iff_forall_adj_isBridge.mp hΓ hxy

/-- **Split compatibility**, the tree-theoretic input to Lemma 3.2.  If the edge `zw` lies
on the `x`-side of the edge `xy`, then *everything* on the `y`-side of `xy` lies on the
same side of `zw` as `y` does.  Equivalently: of the four sets cut out by two distinct
edges of a tree, one is empty. -/
theorem not_sep_of_sep (hΓ : Γ.IsTree) {x y z w : V} (hxy : Γ.Adj x y) (_hzw : Γ.Adj z w)
    (hzx : ¬ Sep Γ s(x, y) z x) {v : V} (hv : Sep Γ s(x, y) v x) :
    ¬ Sep Γ s(z, w) v y := by
  classical
  intro hf
  have hvy : ¬ Sep Γ s(x, y) v y := by
    rcases not_sep_or_not_sep hΓ.connected hxy v with h | h
    · exact absurd h (not_not_intro hv)
    · exact h
  obtain ⟨p⟩ := not_not.mp hvy
  have hfmem : s(z, w) ∈ (p.mapLe (Γ.deleteEdges_le _)).edges :=
    sep_iff_forall_walk.mp hf _
  have hz : z ∈ p.support := by
    have := (p.mapLe (Γ.deleteEdges_le _)).fst_mem_support_of_mem_edges hfmem
    rwa [Walk.support_mapLe_eq_support] at this
  have hvz : (Γ.deleteEdges {s(x, y)}).Reachable v z := (p.takeUntil z hz).reachable
  exact sep_adj hΓ.isAcyclic hxy (((hvz.symm.trans p.reachable).symm).trans (not_not.mp hzx)).symm

/-- Exactly one of the two endpoints of an edge is cut off from a given vertex. -/
theorem sep_right_iff (hΓ : Γ.IsTree) {x y : V} (hxy : Γ.Adj x y) (v : V) :
    Sep Γ s(x, y) v y ↔ ¬ Sep Γ s(x, y) v x := by
  constructor
  · intro h hx
    rcases not_sep_or_not_sep hΓ.connected hxy v with h' | h'
    · exact h' hx
    · exact h' h
  · intro h hr
    exact sep_adj hΓ.isAcyclic hxy ((not_not.mp h).symm.trans hr)

/-- `e` separates `u` from `v` exactly when `u` and `v` lie on opposite sides of `e`. -/
theorem sep_iff_not_iff (hΓ : Γ.IsTree) {x y : V} (hxy : Γ.Adj x y) (u v : V) :
    Sep Γ s(x, y) u v ↔ ¬ (Sep Γ s(x, y) u x ↔ Sep Γ s(x, y) v x) := by
  constructor
  · intro h hiff
    by_cases hux : Sep Γ s(x, y) u x
    · have hvx : Sep Γ s(x, y) v x := hiff.mp hux
      have hu : ¬ Sep Γ s(x, y) u y := fun hs => ((sep_right_iff hΓ hxy u).mp hs) hux
      have hv : ¬ Sep Γ s(x, y) v y := fun hs => ((sep_right_iff hΓ hxy v).mp hs) hvx
      exact h ((not_not.mp hu).trans (not_not.mp hv).symm)
    · have hvx : ¬ Sep Γ s(x, y) v x := fun hv => hux (hiff.mpr hv)
      exact h ((not_not.mp hux).trans (not_not.mp hvx).symm)
  · intro h hr
    exact h ⟨fun hu hv => hu (hr.trans hv), fun hv hu => hv (hr.symm.trans hu)⟩

/-- **Split compatibility**, in the form used below: of the four sets cut out by two
distinct edges `xy` and `zw` of a tree, one is empty. -/
theorem quadrant_empty (hΓ : Γ.IsTree) {x y z w : V} (hxy : Γ.Adj x y) (hzw : Γ.Adj z w)
    (_hef : s(x, y) ≠ s(z, w)) :
    (∀ v, ¬ (Sep Γ s(x, y) v x ∧ Sep Γ s(z, w) v z)) ∨
      (∀ v, ¬ (Sep Γ s(x, y) v x ∧ ¬ Sep Γ s(z, w) v z)) ∨
      (∀ v, ¬ (¬ Sep Γ s(x, y) v x ∧ Sep Γ s(z, w) v z)) ∨
      (∀ v, ¬ (¬ Sep Γ s(x, y) v x ∧ ¬ Sep Γ s(z, w) v z)) := by
  -- `z` lies on one of the two sides of `xy`; say the `x`-side (the other case is symmetric).
  have key : ∀ x' y' : V, Γ.Adj x' y' → s(x', y') = s(x, y) → ¬ Sep Γ s(x, y) z x' →
      (∀ v, ¬ (Sep Γ s(x, y) v x' ∧ Sep Γ s(z, w) v z)) ∨
      (∀ v, ¬ (Sep Γ s(x, y) v x' ∧ ¬ Sep Γ s(z, w) v z)) := by
    intro x' y' hxy' hs hzx
    have hstep : ∀ v, Sep Γ s(x, y) v x' → ¬ Sep Γ s(z, w) v y' := by
      intro v hv
      refine not_sep_of_sep hΓ hxy' hzw ?_ ?_
      · rwa [hs]
      · rwa [hs]
    by_cases hy : Sep Γ s(z, w) y' z
    · refine Or.inr (fun v hv => ?_)
      exact hv.2 (fun hr => hstep v hv.1 (fun hr' => hy (hr'.symm.trans hr)))
    · refine Or.inl (fun v hv => ?_)
      exact hv.2 ((not_not.mp (hstep v hv.1)).trans (not_not.mp hy))
  rcases not_sep_or_not_sep hΓ.connected hxy z with h | h
  · rcases key x y hxy rfl h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · have hyx : ∀ v, Sep Γ s(x, y) v y ↔ ¬ Sep Γ s(x, y) v x := sep_right_iff hΓ hxy
    rcases key y x hxy.symm (Sym2.eq_swap) h with h' | h'
    · exact Or.inr (Or.inr (Or.inl (fun v hv => h' v ⟨(hyx v).mpr hv.1, hv.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (fun v hv => h' v ⟨(hyx v).mpr hv.1, hv.2⟩)))

/-- At most one edge at `x` leads to `z`: the "first step from `x` towards `z`" is unique. -/
theorem sep_unique_neighbor (hΓ : Γ.IsTree) {x r₁ r₂ z : V} (h1 : Γ.Adj x r₁) (h2 : Γ.Adj x r₂)
    (hne : r₁ ≠ r₂) (hz1 : Sep Γ s(x, r₁) z x) : ¬ Sep Γ s(x, r₂) z x := by
  intro hz2
  have key : ¬ Sep Γ s(x, r₁) z r₂ := not_sep_of_sep hΓ h2 h1 (not_sep_self Γ _ x) hz2
  have hr2 : ¬ Sep Γ s(x, r₁) r₂ x := by
    refine not_sep_of_adj h2.symm ?_
    rw [Ne, Sym2.eq_iff]
    rintro (⟨_, hc⟩ | ⟨hc, _⟩)
    · exact h1.ne hc
    · exact hne hc.symm
  exact (not_sep_trans key hr2) hz1

/-- The branch of `x` through `r` stays on one side of any other edge `zw` whose `z` end is
on the `x`-side of `xr`. -/
theorem not_sep_of_sep_branch (hΓ : Γ.IsTree) {x r z w : V} (hxr : Γ.Adj x r) (hzw : Γ.Adj z w)
    (hzx : ¬ Sep Γ s(x, r) z x) (hrz : ¬ Sep Γ s(z, w) r z) {v : V} (hv : Sep Γ s(x, r) v x) :
    ¬ Sep Γ s(z, w) v z :=
  not_sep_trans (not_sep_of_sep hΓ hxr hzw hzx hv) hrz

end Sep

section Cyclic

variable {n : ℕ} [NeZero n]

/-- The cyclic predecessor in `Fin n` (the paper's `i - 1`, with `a_0 = a_n`). -/
theorem fin_val_sub_one (i : Fin n) :
    (i - 1).val = if i.val = 0 then n - 1 else i.val - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := Nat.pos_of_neZero n; omega⟩
  rw [Fin.coe_sub_one]
  have h : (i = 0) ↔ (i.val = 0) :=
    ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
  simp only [h, Nat.add_sub_cancel]

/-- `s` changes value between `i - 1` and `i`.  For the side of an edge of the tree, this is
exactly the statement that the region path `P_i` runs through that edge. -/
def CycChange (s : Fin n → Prop) (i : Fin n) : Prop := ¬ (s (i - 1) ↔ s i)

/-- If `s` does not change anywhere on `(u, v]` then it is constant on `[u, v]`. -/
theorem iff_of_no_cycChange (s : Fin n → Prop) (u : ℕ) (hu : u < n) :
    ∀ v : ℕ, u ≤ v → ∀ hv : v < n,
      (∀ k, ∀ hk : k < n, u < k → k ≤ v → ¬ CycChange s ⟨k, hk⟩) →
      (s ⟨u, hu⟩ ↔ s ⟨v, hv⟩) := by
  intro v huv
  induction v, huv using Nat.le_induction with
  | base => intro _ _; exact Iff.rfl
  | succ v hv' ih =>
    intro hv h
    have hvn : v < n := by omega
    have h1 : s ⟨u, hu⟩ ↔ s ⟨v, hvn⟩ :=
      ih hvn fun k hk h1 h2 => h k hk h1 (by omega)
    have h2 : ¬ CycChange s ⟨v + 1, hv⟩ := h (v + 1) hv (by omega) le_rfl
    have hpred : (⟨v + 1, hv⟩ : Fin n) - 1 = ⟨v, hvn⟩ := by
      refine Fin.ext ?_
      have hval : ((⟨v + 1, hv⟩ : Fin n)).val = v + 1 := rfl
      rw [fin_val_sub_one, hval]
      simp
    rw [CycChange, hpred] at h2
    exact h1.trans (not_not.mp h2)

/-- **The cyclic interval lemma.**  A predicate on `Fin n` that changes value at exactly two
places `p` and `q` (with `p < q`) is constant on the cyclic interval `[p, q)` and constant,
with the opposite value, on its complement. -/
theorem interval_of_two_cycChange (s : Fin n → Prop) {p q : Fin n} (hpq : p.val < q.val)
    (hC : ∀ m : Fin n, CycChange s m ↔ (m = p ∨ m = q)) (m : Fin n) :
    (s m ↔ s p) ↔ (p.val ≤ m.val ∧ m.val < q.val) := by
  have hqn : q.val < n := q.isLt
  have hpn : p.val < n := p.isLt
  -- `s` is constant on `[p, q)`.
  have hin : ∀ r : Fin n, p.val ≤ r.val → r.val < q.val → (s r ↔ s p) := by
    intro r h1 h2
    have := iff_of_no_cycChange s p.val hpn r.val h1 r.isLt ?_
    · rw [Fin.eta, Fin.eta] at this
      exact this.symm
    · intro k hk hk1 hk2 hch
      rcases (hC ⟨k, hk⟩).mp hch with h | h
      · have h' : k = p.val := congrArg Fin.val h
        omega
      · have h' : k = q.val := congrArg Fin.val h
        omega
  -- The change at `q` flips the value.
  have hflip : ¬ (s p ↔ s q) := by
    have hch : CycChange s q := (hC q).mpr (Or.inr rfl)
    have hq1 : (q - 1).val = q.val - 1 := by rw [fin_val_sub_one, ite_eq_right (by omega)]
    have : s (q - 1) ↔ s p := hin (q - 1) (by omega) (by omega)
    exact fun h => hch (this.trans h)
  -- `s` is constant on `[q, n)`.
  have htail : ∀ r : Fin n, q.val ≤ r.val → (s r ↔ s q) := by
    intro r h1
    have := iff_of_no_cycChange s q.val hqn r.val h1 r.isLt ?_
    · rw [Fin.eta, Fin.eta] at this
      exact this.symm
    · intro k hk hk1 hk2 hch
      rcases (hC ⟨k, hk⟩).mp hch with h | h
      · have h' : k = p.val := congrArg Fin.val h
        omega
      · have h' : k = q.val := congrArg Fin.val h
        omega
  -- `s` is constant on `[0, p)`, with the same value as on `[q, n)`.
  have hhead : ∀ r : Fin n, r.val < p.val → (s r ↔ s q) := by
    intro r h1
    have hp0 : 0 < p.val := by omega
    have hn0 : (0 : ℕ) < n := by omega
    have hz : s ⟨0, hn0⟩ ↔ s r := by
      have := iff_of_no_cycChange s 0 hn0 r.val (Nat.zero_le _) r.isLt ?_
      · rwa [Fin.eta] at this
      · intro k hk hk1 hk2 hch
        rcases (hC ⟨k, hk⟩).mp hch with h | h
        · have h' : k = p.val := congrArg Fin.val h
          omega
        · have h' : k = q.val := congrArg Fin.val h
          omega
    have hz0 : ¬ CycChange s ⟨0, hn0⟩ := by
      intro hch
      rcases (hC ⟨0, hn0⟩).mp hch with h | h
      · have h' : (0 : ℕ) = p.val := congrArg Fin.val h
        omega
      · have h' : (0 : ℕ) = q.val := congrArg Fin.val h
        omega
    have hlast : (⟨0, hn0⟩ : Fin n) - 1 = ⟨n - 1, by omega⟩ := by
      refine Fin.ext ?_
      rw [fin_val_sub_one]
      simp
    rw [CycChange, hlast, not_not] at hz0
    have hlt : s ⟨n - 1, by omega⟩ ↔ s q := htail ⟨n - 1, by omega⟩ (by show q.val ≤ n - 1; omega)
    exact ((hz.symm.trans hz0.symm).trans hlt)
  rcases lt_trichotomy m.val p.val with h | h | h
  · constructor
    · intro hm
      exact absurd (hm.symm.trans (hhead m h)) hflip
    · intro hm; omega
  · have hmem : p.val ≤ m.val ∧ m.val < q.val := ⟨le_of_eq h.symm, by omega⟩
    exact iff_of_true (hin m hmem.1 hmem.2) hmem
  · by_cases hq : m.val < q.val
    · exact iff_of_true (hin m (by omega) hq) ⟨by omega, hq⟩
    · constructor
      · intro hm
        exact absurd (hm.symm.trans (htail m (by omega))) hflip
      · intro hm; omega

end Cyclic

section Canonical

variable {V : Type*} {Γ : SimpleGraph V} {n : ℕ} [NeZero n] {a : Fin n → V}

/-- The unique path between two vertices of a tree. -/
noncomputable def treePath (hΓ : Γ.IsTree) (u v : V) : Γ.Walk u v :=
  (hΓ.existsUnique_path u v).choose

theorem treePath_isPath (hΓ : Γ.IsTree) (u v : V) : (treePath hΓ u v).IsPath :=
  (hΓ.existsUnique_path u v).choose_spec.1

/-- In a tree, `e` separates `u` from `v` exactly when the path from `u` to `v` uses `e`. -/
theorem sep_iff_mem_edges_treePath (hΓ : Γ.IsTree) {e : Sym2 V} (u v : V) :
    Sep Γ e u v ↔ e ∈ (treePath hΓ u v).edges := by
  classical
  refine ⟨fun h => sep_iff_forall_walk.mp h _, fun he => sep_iff_forall_walk.mpr fun p => ?_⟩
  have hb : p.bypass = treePath hΓ u v :=
    (hΓ.existsUnique_path u v).choose_spec.2 p.bypass p.bypass_isPath
  exact p.edges_bypass_subset_edges (hb ▸ he)

/-- **Definition 3.1 (I–III) in the tree model.**  The canonical partition of the oriented
`n`-gon `P_a` is presented by its tree `Γ`: the leaves are the polygon vertices `a_i`, the
internal vertices have degree `≥ 3` (the normal form of the equivalence II), and each edge
lies on exactly two of the `n` region paths (planarity). -/
structure IsCanonicalTree (n : ℕ) [NeZero n] (Γ : SimpleGraph V) (a : Fin n → V) : Prop where
  /-- `Γ` is a tree. -/
  tree : Γ.IsTree
  /-- The polygon vertices are distinct. -/
  inj : Function.Injective a
  /-- Each `a_i` is a leaf. -/
  leaf_degree : ∀ i : Fin n, (Γ.neighborSet (a i)).ncard = 1
  /-- Every other vertex is internal, of degree at least `3`. -/
  internal_degree : ∀ v : V, v ∉ Set.range a → 3 ≤ (Γ.neighborSet v).ncard
  /-- Planarity: each edge of `Γ` lies on exactly two region paths. -/
  planar : ∀ e ∈ Γ.edgeSet, {i : Fin n | Sep Γ e (a (i - 1)) (a i)}.ncard = 2

/-- The tree boundary `P_i` of the region `R_i`: the unique path from `a_{i-1}` to `a_i`.
The `i`-th polygon edge `e_i = a_{i-1}a_i` closes it up into the polygon `R_i`. -/
noncomputable def regionPath (hΓ : Γ.IsTree) (a : Fin n → V) (i : Fin n) :
    Γ.Walk (a (i - 1)) (a i) :=
  treePath hΓ _ _

/-- The edge `e` lies on the region path `P_i`. -/
def OnRegion (Γ : SimpleGraph V) (a : Fin n → V) (i : Fin n) (e : Sym2 V) : Prop :=
  Sep Γ e (a (i - 1)) (a i)

/-- `OnRegion` is what the planarity clause of `IsCanonicalTree` counts, and it really is
membership in the region path. -/
theorem onRegion_iff_mem_edges_regionPath (hΓ : Γ.IsTree) (a : Fin n → V) (e : Sym2 V)
    (i : Fin n) : OnRegion Γ a i e ↔ e ∈ (regionPath hΓ a i).edges :=
  sep_iff_mem_edges_treePath hΓ _ _

/-- Definition 3.1: `R_i` and `R_j` are *paired* when their tree boundaries share an edge,
i.e. `R_i ∩ R_j ∈ E (Γ)`. -/
def Paired (Γ : SimpleGraph V) (a : Fin n → V) (i j : Fin n) : Prop :=
  ∃ e ∈ Γ.edgeSet, OnRegion Γ a i e ∧ OnRegion Γ a j e

/-- `F (Γ)` of (3.1): the set of non-adjacent paired region indices, written as ordered
pairs `(i, j)` with `i < j`, exactly as `RBM.diagonals` does. -/
def FGamma (Γ : SimpleGraph V) (a : Fin n → V) : Set (Fin n × Fin n) :=
  {d | IsDiag n d.1 d.2 ∧ Paired Γ a d.1 d.2}

/-- Planarity pins down the two regions through an edge: if `P_i` and `P_j` both use `e`
with `i ≠ j`, then those are the *only* region paths through `e`. -/
theorem onRegion_iff_of_pair (h : IsCanonicalTree n Γ a) {e : Sym2 V} (he : e ∈ Γ.edgeSet)
    {i j : Fin n} (hij : i ≠ j) (hi : OnRegion Γ a i e) (hj : OnRegion Γ a j e) (m : Fin n) :
    OnRegion Γ a m e ↔ (m = i ∨ m = j) := by
  have hsub : ({i, j} : Set (Fin n)) ⊆ {m : Fin n | Sep Γ e (a (m - 1)) (a m)} := by
    rintro m (rfl | rfl)
    · exact hi
    · exact hj
  have hle : {m : Fin n | Sep Γ e (a (m - 1)) (a m)}.ncard ≤ ({i, j} : Set (Fin n)).ncard := by
    rw [h.planar e he, Set.ncard_pair hij]
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  constructor
  · intro hm
    have hmem : m ∈ {m : Fin n | Sep Γ e (a (m - 1)) (a m)} := hm
    rw [← heq] at hmem
    simpa using hmem
  · intro hm
    have hmem : m ∈ ({i, j} : Set (Fin n)) := by simpa using hm
    rw [heq] at hmem
    exact hmem

/-- **The leaves on one side of an edge form a cyclic interval.**  This is exactly what the
planarity clause buys: if the two region paths through the edge `xy` are `P_p` and `P_q`
with `p < q`, then `a_m` lies on the same side of `xy` as `a_p` iff `p ≤ m < q`. -/
theorem leafSide_eq_Ico (h : IsCanonicalTree n Γ a) {x y : V} (hxy : Γ.Adj x y)
    {p q : Fin n} (hpq : p.val < q.val)
    (hpair : ∀ i : Fin n, OnRegion Γ a i s(x, y) ↔ (i = p ∨ i = q)) (m : Fin n) :
    (Sep Γ s(x, y) (a m) x ↔ Sep Γ s(x, y) (a p) x) ↔ (p.val ≤ m.val ∧ m.val < q.val) := by
  refine interval_of_two_cycChange (fun i => Sep Γ s(x, y) (a i) x) hpq (fun i => ?_) m
  rw [← hpair i]
  exact (sep_iff_not_iff h.tree hxy (a (i - 1)) (a i)).symm

/-- Two propositions that are never equivalent are negations of each other. -/
theorem eq_not_of_not_iff {A B : Prop} (h : ¬ (A ↔ B)) : A = ¬ B :=
  propext ⟨fun ha hb => h ⟨fun _ => hb, fun _ => ha⟩,
    fun hnb => not_not.mp fun hna => h ⟨fun ha => absurd ha hna, fun hb => absurd hb hnb⟩⟩

/-- The purely propositional core of Lemma 3.2 (1): if the four leaves `a_i, a_k, a_j, a_l`
realize all four combinations of the two sides, no quadrant can be empty. -/
theorem no_empty_quadrant {Pi Pk Pj Pl Qi Qk Qj Ql : Prop}
    (hq1 : ¬ (Qi ↔ Qk)) (hq2 : Pk ↔ Pi) (hq3 : ¬ (Pj ↔ Pi)) (hq4 : Qj ↔ Qk)
    (hq5 : ¬ (Pl ↔ Pi)) (hq6 : ¬ (Ql ↔ Qk)) :
    ¬ ((¬ (Pi ∧ Qi) ∧ ¬ (Pk ∧ Qk) ∧ ¬ (Pj ∧ Qj) ∧ ¬ (Pl ∧ Ql)) ∨
       (¬ (Pi ∧ ¬ Qi) ∧ ¬ (Pk ∧ ¬ Qk) ∧ ¬ (Pj ∧ ¬ Qj) ∧ ¬ (Pl ∧ ¬ Ql)) ∨
       (¬ (¬ Pi ∧ Qi) ∧ ¬ (¬ Pk ∧ Qk) ∧ ¬ (¬ Pj ∧ Qj) ∧ ¬ (¬ Pl ∧ Ql)) ∨
       (¬ (¬ Pi ∧ ¬ Qi) ∧ ¬ (¬ Pk ∧ ¬ Qk) ∧ ¬ (¬ Pj ∧ ¬ Qj) ∧ ¬ (¬ Pl ∧ ¬ Ql))) := by
  have e1 : Qi = ¬ Qk := eq_not_of_not_iff hq1
  have e2 : Pk = Pi := propext hq2
  have e3 : Pj = ¬ Pi := eq_not_of_not_iff hq3
  have e4 : Qj = Qk := propext hq4
  have e5 : Pl = ¬ Pi := eq_not_of_not_iff hq5
  have e6 : Ql = ¬ Qk := eq_not_of_not_iff hq6
  rw [e1, e2, e3, e4, e5, e6]
  clear hq1 hq2 hq3 hq4 hq5 hq6 e1 e2 e3 e4 e5 e6
  tauto

/-- The crossing-free property, in the asymmetric form `i < k < j < l`. -/
theorem not_crossing_aux (h : IsCanonicalTree n Γ a) {i j k l : Fin n}
    (hij : (i, j) ∈ FGamma Γ a) (hkl : (k, l) ∈ FGamma Γ a)
    (c1 : i.val < k.val) (c2 : k.val < j.val) (c3 : j.val < l.val) : False := by
  obtain ⟨hdij, e, he, hei, hej⟩ := hij
  obtain ⟨hdkl, f, hf, hfk, hfl⟩ := hkl
  have hijne : i ≠ j := fun hc => by rw [hc] at c1; omega
  have hklne : k ≠ l := fun hc => by rw [hc] at c2; omega
  have hPe := onRegion_iff_of_pair h he hijne hei hej
  have hPf := onRegion_iff_of_pair h hf hklne hfk hfl
  -- the two edges are distinct, since `i` is a region of `e` but not of `f`
  have hef : e ≠ f := by
    rintro rfl
    rcases (hPf i).mp hei with hc | hc <;> rw [hc] at c1 <;> omega
  -- unpack the two edges
  induction e using Sym2.ind with
  | _ x y =>
  induction f using Sym2.ind with
  | _ z w =>
  rw [mem_edgeSet] at he hf
  have hIe := leafSide_eq_Ico h he (by omega) hPe
  have hIf := leafSide_eq_Ico h hf (by omega) hPf
  have hq1 : ¬ (Sep Γ s(z, w) (a i) z ↔ Sep Γ s(z, w) (a k) z) := by
    intro hc; have := (hIf i).mp hc; omega
  have hq2 : Sep Γ s(x, y) (a k) x ↔ Sep Γ s(x, y) (a i) x := (hIe k).mpr ⟨by omega, by omega⟩
  have hq3 : ¬ (Sep Γ s(x, y) (a j) x ↔ Sep Γ s(x, y) (a i) x) := by
    intro hc; have := (hIe j).mp hc; omega
  have hq4 : Sep Γ s(z, w) (a j) z ↔ Sep Γ s(z, w) (a k) z := (hIf j).mpr ⟨by omega, by omega⟩
  have hq5 : ¬ (Sep Γ s(x, y) (a l) x ↔ Sep Γ s(x, y) (a i) x) := by
    intro hc; have := (hIe l).mp hc; omega
  have hq6 : ¬ (Sep Γ s(z, w) (a l) z ↔ Sep Γ s(z, w) (a k) z) := by
    intro hc; have := (hIf l).mp hc; omega
  refine no_empty_quadrant hq1 hq2 hq3 hq4 hq5 hq6 ?_
  rcases quadrant_empty h.tree he hf hef with hQ | hQ | hQ | hQ
  · exact Or.inl ⟨hQ (a i), hQ (a k), hQ (a j), hQ (a l)⟩
  · exact Or.inr (Or.inl ⟨hQ (a i), hQ (a k), hQ (a j), hQ (a l)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hQ (a i), hQ (a k), hQ (a j), hQ (a l)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hQ (a i), hQ (a k), hQ (a j), hQ (a l)⟩))

/-- **Lemma 3.2 (1).**  `F (Γ)` contains no crossing pairs. -/
theorem crossingFree_FGamma (h : IsCanonicalTree n Γ a) :
    ∀ d ∈ FGamma Γ a, ∀ d' ∈ FGamma Γ a, ¬ Crossing d d' := by
  rintro ⟨i, j⟩ hd ⟨k, l⟩ hd' (⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩)
  · exact not_crossing_aux h hd hd' c1 c2 c3
  · exact not_crossing_aux h hd' hd c1 c2 c3

/-- `F (Γ)` consists of diagonals. -/
theorem FGamma_subset_diagonals :
    (Set.toFinite (FGamma Γ a)).toFinset ⊆ diagonals n := by
  intro d hd
  rw [Set.Finite.mem_toFinset] at hd
  simpa [diagonals] using hd.1

/-- **Lemma 3.2 (1), packaged.**  `F (Γ)` is one of the crossing-free sets of diagonals that
`RBM.TSP` collects: the map `Γ ↦ F (Γ)` lands in `RBM.TSP n`. -/
theorem FGamma_mem_TSP (h : IsCanonicalTree n Γ a) :
    (Set.toFinite (FGamma Γ a)).toFinset ∈ TSP n := by
  rw [mem_TSP]
  refine ⟨FGamma_subset_diagonals, fun d hd d' hd' => ?_⟩
  rw [Set.Finite.mem_toFinset] at hd hd'
  exact crossingFree_FGamma h d hd d' hd'

/-- The leaves of `Γ` are exactly the polygon vertices: a vertex of degree `1` is some
`a i`.  (This is the "leaves are exactly `a_0, …, a_{n-1}`" half of the model.) -/
theorem mem_range_of_ncard_neighborSet_eq_one (h : IsCanonicalTree n Γ a) {v : V}
    (hv : (Γ.neighborSet v).ncard = 1) : v ∈ Set.range a := by
  by_contra hc
  have := h.internal_degree v hc
  omega

/-- **Every branch of the tree reaches a polygon vertex.**  For every edge `vr` of `Γ` some
`a m` lies on the `r`-side.  Finiteness of `V` is essential here. -/
theorem exists_leaf_sep [Finite V] (h : IsCanonicalTree n Γ a) {v r : V} (hvr : Γ.Adj v r) :
    ∃ m : Fin n, Sep Γ s(v, r) (a m) v := by
  suffices H : ∀ N : ℕ, ∀ v r : V, Γ.Adj v r → {u | Sep Γ s(v, r) u v}.ncard ≤ N →
      ∃ m : Fin n, Sep Γ s(v, r) (a m) v from H _ v r hvr le_rfl
  intro N
  induction N with
  | zero =>
    intro v r hvr hle
    have hr : r ∈ {u | Sep Γ s(v, r) u v} := (sep_comm Γ _ _ _).mp (sep_adj h.tree.isAcyclic hvr)
    have := (Set.ncard_pos (Set.toFinite _)).mpr ⟨r, hr⟩
    omega
  | succ N ih =>
    intro v r hvr hle
    have hrv : Sep Γ s(v, r) r v := (sep_comm Γ _ _ _).mp (sep_adj h.tree.isAcyclic hvr)
    by_cases hdeg : (Γ.neighborSet r).ncard = 1
    · obtain ⟨m, hm⟩ := mem_range_of_ncard_neighborSet_eq_one h hdeg
      exact ⟨m, by rw [hm]; exact hrv⟩
    · have h2 : 1 < (Γ.neighborSet r).ncard := by
        have hv : v ∈ Γ.neighborSet r := hvr.symm
        have := (Set.ncard_pos (Set.toFinite _)).mpr ⟨v, hv⟩
        omega
      obtain ⟨r', hr', hne⟩ := Set.exists_ne_of_one_lt_ncard h2 v
      have hrr' : Γ.Adj r r' := hr'
      have hsub : {u | Sep Γ s(r, r') u r} ⊆ {u | Sep Γ s(v, r) u v} := by
        intro u hu
        have key : ¬ Sep Γ s(r, v) u r' :=
          not_sep_of_sep h.tree hrr' hvr.symm (not_sep_self Γ _ r) hu
        have hr'r : ¬ Sep Γ s(r, v) r' r := by
          intro hc
          exact hc (deleteEdges_adj.mpr ⟨hrr'.symm, by
            simp only [Set.mem_singleton_iff]
            intro hcc
            rw [Sym2.eq_iff] at hcc
            rcases hcc with ⟨hc1, _⟩ | ⟨hc1, _⟩
            · exact hrr'.ne hc1.symm
            · exact hne hc1⟩).reachable
        have hur : ¬ Sep Γ s(r, v) u r := fun hc => hc ((not_not.mp key).trans (not_not.mp hr'r))
        rw [Sym2.eq_swap] at hur
        show Sep Γ s(v, r) u v
        exact not_not.mp ((sep_right_iff h.tree hvr u).not.mp hur)
      have hstrict : {u | Sep Γ s(r, r') u r} ⊂ {u | Sep Γ s(v, r) u v} :=
        ⟨hsub, fun hc => not_sep_self Γ _ r (hc hrv)⟩
      have := Set.ncard_lt_ncard hstrict (Set.toFinite _)
      obtain ⟨m, hm⟩ := ih r r' hrr' (by omega)
      exact ⟨m, hsub hm⟩

/-- Definition 3.1: the polygon vertex `a i` lies on the boundary of `R_i` and of `R_{i+1}`. -/
theorem mem_support_regionPath_self (hΓ : Γ.IsTree) (a : Fin n → V) (i : Fin n) :
    a i ∈ (regionPath hΓ a i).support :=
  Walk.end_mem_support _

theorem mem_support_regionPath_succ (hΓ : Γ.IsTree) (a : Fin n → V) (i : Fin n) :
    a i ∈ (regionPath hΓ a (i + 1)).support := by
  have h : a i = a (i + 1 - 1) := by rw [add_sub_cancel_right]
  rw [h]
  exact Walk.start_mem_support _

/-- The core of "`R_i ∩ R_j ∈ E (Γ)`" (Lemma 3.2), with both edges oriented: `z` on the
`x`-side of `xy`, and `x` on the `z`-side of `zw`. -/
theorem edge_unique_aux [Finite V] (h : IsCanonicalTree n Γ a) {i j : Fin n} (hij : i.val < j.val)
    {x y z w : V} (hxy : Γ.Adj x y) (hzw : Γ.Adj z w) (hef : s(x, y) ≠ s(z, w))
    (hPe : ∀ m : Fin n, OnRegion Γ a m s(x, y) ↔ (m = i ∨ m = j))
    (hPf : ∀ m : Fin n, OnRegion Γ a m s(z, w) ↔ (m = i ∨ m = j))
    (hzx : ¬ Sep Γ s(x, y) z x) (hxz : ¬ Sep Γ s(z, w) x z) : False := by
  have hIe := leafSide_eq_Ico h hxy hij hPe
  have hIf := leafSide_eq_Ico h hzw hij hPf
  -- the `y`-side of `xy` and the `w`-side of `zw` are disjoint
  have hyz : ¬ Sep Γ s(z, w) y z :=
    not_sep_trans (not_sep_of_adj hxy.symm (by rw [Sym2.eq_swap]; exact hef)) hxz
  have hdisj : ∀ v : V, Sep Γ s(x, y) v x → ¬ Sep Γ s(z, w) v z := fun v hv =>
    not_sep_trans (not_sep_of_sep h.tree hxy hzw hzx hv) hyz
  -- so the two sides between them carry *all* the polygon vertices
  have hbase : Sep Γ s(z, w) (a i) z ↔ ¬ Sep Γ s(x, y) (a i) x := by
    refine ⟨fun hfi hei => hdisj _ hei hfi, fun hei => ?_⟩
    by_contra hfi
    have k1 : ¬ ((Sep Γ s(x, y) (a j) x) ↔ (Sep Γ s(x, y) (a i) x)) := by
      intro hc; have := (hIe j).mp hc; omega
    have k2 : ¬ ((Sep Γ s(z, w) (a j) z) ↔ (Sep Γ s(z, w) (a i) z)) := by
      intro hc; have := (hIf j).mp hc; omega
    exact hdisj (a j) (by tauto) (by tauto)
  -- hence no polygon vertex lies in the middle region
  have hmid : ∀ m : Fin n, ¬ Sep Γ s(x, y) (a m) x → Sep Γ s(z, w) (a m) z := by
    intro m hm
    have k := (hIe m).trans (hIf m).symm
    tauto
  -- but `x` itself lies in the middle region, so `x` is internal
  have hxdeg : 3 ≤ (Γ.neighborSet x).ncard := by
    by_cases hx : x ∈ Set.range a
    · obtain ⟨m, hm⟩ := hx
      refine absurd (hmid m ?_) ?_
      · rw [hm]; exact not_sep_self Γ _ x
      · rw [hm]; exact hxz
    · exact h.internal_degree x hx
  have hxw : x ≠ w := by
    intro hc
    refine hxz ?_
    rw [hc]
    exact (sep_comm Γ _ _ _).mp (sep_adj h.tree.isAcyclic hzw)
  -- `x` has a neighbour `r` leading neither to `y`, nor to `z`, nor along `zw`
  obtain ⟨r, hrmem, hry, hrz, hrf⟩ :
      ∃ r, Γ.Adj x r ∧ r ≠ y ∧ ¬ Sep Γ s(x, r) z x ∧ s(x, r) ≠ s(z, w) := by
    by_contra hcon
    push Not at hcon
    have hbad : ∀ r, Γ.Adj x r → r ≠ y → (Sep Γ s(x, r) z x ∨ s(x, r) = s(z, w)) := by
      intro r hr hry
      by_cases hs : Sep Γ s(x, r) z x
      · exact Or.inl hs
      · exact Or.inr (hcon r hr hry hs)
    have hfeq : ∀ r, s(x, r) = s(z, w) → (x = z ∧ r = w) := by
      intro r hr
      rw [Sym2.eq_iff] at hr
      rcases hr with ⟨h1, h2⟩ | ⟨h1, _⟩
      · exact ⟨h1, h2⟩
      · exact absurd h1 hxw
    have huniq : ∀ r₁ r₂, Γ.Adj x r₁ → Γ.Adj x r₂ → r₁ ≠ y → r₂ ≠ y → r₁ = r₂ := by
      intro r₁ r₂ h1 h2 hy1 hy2
      by_contra hne
      rcases hbad r₁ h1 hy1 with s1 | s1 <;> rcases hbad r₂ h2 hy2 with s2 | s2
      · exact sep_unique_neighbor h.tree h1 h2 hne s1 s2
      · obtain ⟨hxz', _⟩ := hfeq r₂ s2
        rw [← hxz'] at s1
        exact not_sep_self Γ _ x s1
      · obtain ⟨hxz', _⟩ := hfeq r₁ s1
        rw [← hxz'] at s2
        exact not_sep_self Γ _ x s2
      · obtain ⟨_, hr1⟩ := hfeq r₁ s1
        obtain ⟨_, hr2⟩ := hfeq r₂ s2
        exact hne (hr1.trans hr2.symm)
    by_cases hex : ∃ b, Γ.Adj x b ∧ b ≠ y
    · obtain ⟨b, hbm, hby⟩ := hex
      have hsub : Γ.neighborSet x ⊆ {y, b} := by
        intro r hr
        by_cases hry : r = y
        · exact Or.inl hry
        · exact Or.inr (huniq r b hr hbm hry hby)
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : ({y, b} : Set V).ncard ≤ 2 := by
        refine le_trans (Set.ncard_insert_le _ _) ?_
        simp
      omega
    · push Not at hex
      have hsub : Γ.neighborSet x ⊆ {y} := fun r hr => hex r hr
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_singleton] at hle
      omega
  -- the branch of `x` through `r` lies entirely in the middle region, but it has a leaf
  have hrx : ¬ Sep Γ s(x, y) r x := by
    refine not_sep_of_adj hrmem.symm ?_
    rw [Ne, Sym2.eq_iff]
    rintro (⟨hc, _⟩ | ⟨hc, _⟩)
    · exact hrmem.ne hc.symm
    · exact hry hc
  have hrz' : ¬ Sep Γ s(z, w) r z := by
    refine not_sep_trans (not_sep_of_adj hrmem.symm ?_) hxz
    rw [Sym2.eq_swap]
    exact hrf
  obtain ⟨m, hm⟩ := exists_leaf_sep h hrmem
  have h1 : ¬ Sep Γ s(x, y) (a m) x :=
    not_sep_of_sep_branch h.tree hrmem hxy (not_sep_self Γ _ x) hrx hm
  have h2 : ¬ Sep Γ s(z, w) (a m) z :=
    not_sep_of_sep_branch h.tree hrmem hzw hrz hrz' hm
  exact h2 (hmid m h1)

/-- `R_i ∩ R_j ∈ E (Γ)`, in the form `i < j`. -/
theorem edge_unique_of_paired' [Finite V] (h : IsCanonicalTree n Γ a) {i j : Fin n}
    (hij : i.val < j.val) {e f : Sym2 V} (he : e ∈ Γ.edgeSet) (hf : f ∈ Γ.edgeSet)
    (hei : OnRegion Γ a i e) (hej : OnRegion Γ a j e)
    (hfi : OnRegion Γ a i f) (hfj : OnRegion Γ a j f) : e = f := by
  by_contra hef
  have hijne : i ≠ j := fun hc => by rw [hc] at hij; omega
  have hPe := onRegion_iff_of_pair h he hijne hei hej
  have hPf := onRegion_iff_of_pair h hf hijne hfi hfj
  induction e using Sym2.ind with
  | _ x y =>
  induction f using Sym2.ind with
  | _ z w =>
  rw [mem_edgeSet] at he hf
  have key : ∀ x' y' : V, Γ.Adj x' y' → s(x', y') = s(x, y) →
      ∀ z' w' : V, Γ.Adj z' w' → s(z', w') = s(z, w) →
      ¬ Sep Γ s(x', y') z' x' → ¬ Sep Γ s(z', w') x' z' → False := by
    intro x' y' hxy' hs1 z' w' hzw' hs2 hzx' hxz'
    refine edge_unique_aux h hij hxy' hzw' (by rw [hs1, hs2]; exact hef) ?_ ?_ hzx' hxz'
    · intro m; rw [hs1]; exact hPe m
    · intro m; rw [hs2]; exact hPf m
  have hswz : ¬ Sep Γ s(x, y) w z :=
    not_sep_of_adj hf.symm (by rw [Sym2.eq_swap]; exact fun hc => hef hc.symm)
  rcases not_sep_or_not_sep h.tree.connected he z with hz1 | hz1
  · rcases not_sep_or_not_sep h.tree.connected hf x with hx1 | hx1
    · exact key x y he rfl z w hf rfl hz1 hx1
    · exact key x y he rfl w z hf.symm Sym2.eq_swap (not_sep_trans hswz hz1)
        (by rw [Sym2.eq_swap]; exact hx1)
  · rcases not_sep_or_not_sep h.tree.connected hf y with hx1 | hx1
    · exact key y x he.symm Sym2.eq_swap z w hf rfl (by rw [Sym2.eq_swap]; exact hz1) hx1
    · exact key y x he.symm Sym2.eq_swap w z hf.symm Sym2.eq_swap
        (by rw [Sym2.eq_swap]; exact not_sep_trans hswz hz1)
        (by rw [Sym2.eq_swap]; exact hx1)

/-- **Lemma 3.2, step 0: `R_i ∩ R_j ∈ E (Γ)`.**  Two distinct region paths share at most one
edge, so the intersection of two regions, when non-empty, is a single edge of `Γ`.  This is
where the requirement that internal vertices have degree `≥ 3` is used. -/
theorem edge_unique_of_paired [Finite V] (h : IsCanonicalTree n Γ a) {i j : Fin n} (hij : i ≠ j)
    {e f : Sym2 V} (he : e ∈ Γ.edgeSet) (hf : f ∈ Γ.edgeSet)
    (hei : OnRegion Γ a i e) (hej : OnRegion Γ a j e)
    (hfi : OnRegion Γ a i f) (hfj : OnRegion Γ a j f) : e = f := by
  rcases lt_or_gt_of_ne (fun hc : i.val = j.val => hij (Fin.ext hc)) with hlt | hlt
  · exact edge_unique_of_paired' h hlt he hf hei hej hfi hfj
  · exact edge_unique_of_paired' h hlt he hf hej hei hfj hfi

/-- **Figure 4.**  The tree drawn on p. 27 has leaves `a_1, …, a_6`, internal vertices
`b_1, b_2, b_3`, and internal edges `{b_1,b_2}`, `{b_2,b_3}`.  Deleting `{b_1,b_2}` leaves
`{a_1,a_2,a_3}` on one side, so the two region paths through it are `P_1` and `P_4`;
deleting `{b_2,b_3}` leaves `{a_4,a_5}`, so its region paths are `P_4` and `P_6`.  Hence
`F (Γ) = {{1,4},{4,6}}`, which is what the paper records under (3.1).  In our `0`-based
labels that is `{(0,3),(3,5)}`, and it is indeed a member of `RBM.TSP 6`. -/
theorem figure_four : ({(0, 3), (3, 5)} : Finset (Fin 6 × Fin 6)) ∈ TSP 6 := by decide

end Canonical

end RBM
