/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.TreeRep
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.List.GetD

/-!
# Lemma 3.4 for general `n`: a pivot-free tree value

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 3.3 and Lemma 3.4.

The tree `Γ ∈ T_SP(P_a)` attached to a crossing-free set `F` of diagonals is encoded as a
**laminar family of vertex intervals**, rooted at the last vertex `n - 1`:

* the region pair `d = (i, j)` (a diagonal, `RBM.IsDiag`) is the arc of vertices `i ≤ v < j`;
  crossing-free (`RBM.CrossingFree`) is exactly "pairwise nested or disjoint";
* the internal vertices of `Γ` are the nodes `F ∪ {whole}`, `whole = (0, n - 1)` being the arc
  of all non-root vertices; the parent of a node or of a leaf is the smallest node strictly
  containing it (`RBM.nodePar`, `RBM.leafPar`), and the root leaf `n - 1` hangs on `whole`;
* the leaf edge at `v` carries `Θ_{t m(σ_v) m(σ_{v+1})}` and the internal edge of `d = (i, j)`
  carries `Θ_{t m(σ_i) m(σ_j)} - 1` (Definition 3.3).

The value `RBM.treeValG` is a sum over labels of **all** internal vertices at once, with no
choice of a pivot diagonal.  Factorizing it along any edge is therefore a Fubini argument,
which is what the derivative in (2.48) needs (see `docs/STATUS.md`, T25b).

This file contains the definitions, the star case, and the edge-by-edge derivative.
-/

namespace RBM

open Finset

section Laminar

variable {n : ℕ} [NeZero n]

/-- The root node: the region pair `(0, n - 1)`, whose arc is every non-root vertex. -/
def wholeP (n : ℕ) [NeZero n] : Fin n × Fin n :=
  (0, ⟨n - 1, by have := NeZero.pos n; omega⟩)

/-- Vertex `v` lies in the arc of `d = (i, j)`: `i ≤ v < j`. -/
def InArc (d : Fin n × Fin n) (v : Fin n) : Prop := d.1 ≤ v ∧ v < d.2

instance (d : Fin n × Fin n) (v : Fin n) : Decidable (InArc d v) := by
  unfold InArc; infer_instance

/-- The arc of `d` is contained in the arc of `e`. -/
def ArcLe (d e : Fin n × Fin n) : Prop := e.1 ≤ d.1 ∧ d.2 ≤ e.2

instance (d e : Fin n × Fin n) : Decidable (ArcLe d e) := by
  unfold ArcLe; infer_instance

/-- The width `j - i` of the arc of `(i, j)`. -/
def arcWidth (d : Fin n × Fin n) : ℕ := d.2.val - d.1.val

/-- The internal vertices of the tree: `F ∪ {whole}`. -/
def nodes (F : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n) := insert (wholeP n) F

theorem wholeP_mem_nodes (F : Finset (Fin n × Fin n)) : wholeP n ∈ nodes F :=
  mem_insert_self _ _

theorem mem_nodes_of_mem {F : Finset (Fin n × Fin n)} {d : Fin n × Fin n} (h : d ∈ F) :
    d ∈ nodes F := mem_insert_of_mem h

/-- The smallest node containing a given set of candidates, or `whole` if there is none. -/
noncomputable def minNode (s : Finset (Fin n × Fin n)) : Fin n × Fin n :=
  if h : s.Nonempty then Classical.choose (s.exists_min_image arcWidth h) else wholeP n

theorem minNode_mem_or {s : Finset (Fin n × Fin n)} :
    minNode s ∈ s ∨ minNode s = wholeP n := by
  unfold minNode
  split_ifs with h
  · exact Or.inl (Classical.choose_spec (s.exists_min_image arcWidth h)).1
  · exact Or.inr rfl

theorem minNode_le {s : Finset (Fin n × Fin n)} {e : Fin n × Fin n} (he : e ∈ s) :
    minNode s ∈ s ∧ arcWidth (minNode s) ≤ arcWidth e := by
  have h : s.Nonempty := ⟨e, he⟩
  unfold minNode
  split_ifs
  exact ⟨(Classical.choose_spec (s.exists_min_image arcWidth h)).1,
    (Classical.choose_spec (s.exists_min_image arcWidth h)).2 e he⟩

/-- The parent of the leaf `v`: the smallest node whose arc contains `v`.  No node contains
the root vertex `n - 1`, which therefore hangs on `whole`. -/
noncomputable def leafPar (F : Finset (Fin n × Fin n)) (v : Fin n) : Fin n × Fin n :=
  minNode ((nodes F).filter fun e => InArc e v)

/-- The parent of the node `d`: the smallest other node whose arc contains the arc of `d`. -/
noncomputable def nodePar (F : Finset (Fin n × Fin n)) (d : Fin n × Fin n) : Fin n × Fin n :=
  minNode ((nodes F).filter fun e => ArcLe d e ∧ e ≠ d)

theorem leafPar_mem (F : Finset (Fin n × Fin n)) (v : Fin n) : leafPar F v ∈ nodes F := by
  rcases minNode_mem_or (s := (nodes F).filter fun e => InArc e v) with h | h
  · exact (mem_filter.1 h).1
  · rw [leafPar, h]; exact wholeP_mem_nodes F

theorem nodePar_mem (F : Finset (Fin n × Fin n)) (d : Fin n × Fin n) : nodePar F d ∈ nodes F := by
  rcases minNode_mem_or (s := (nodes F).filter fun e => ArcLe d e ∧ e ≠ d) with h | h
  · exact (mem_filter.1 h).1
  · rw [nodePar, h]; exact wholeP_mem_nodes F

/-- Over the empty family every leaf hangs on `whole`: the star. -/
theorem leafPar_empty (v : Fin n) : leafPar (∅ : Finset (Fin n × Fin n)) v = wholeP n := by
  rcases minNode_mem_or (s := (nodes (∅ : Finset (Fin n × Fin n))).filter fun e => InArc e v)
    with h | h
  · have h1 := (mem_filter.1 h).1
    have h2 : (nodes (∅ : Finset (Fin n × Fin n))) = {wholeP n} := by simp [nodes]
    rw [h2, mem_singleton] at h1
    exact h1
  · exact h

/-! ### Laminarity -/

/-- `F` is a family of diagonals with no crossing pair: an element of `T_SP(n)`. -/
def IsTSP (F : Finset (Fin n × Fin n)) : Prop :=
  (∀ d ∈ F, IsDiag n d.1 d.2) ∧ CrossingFree F

omit [NeZero n] in
theorem isTSP_of_mem_TSP {F : Finset (Fin n × Fin n)} (h : F ∈ TSP n) : IsTSP F := by
  rw [mem_TSP] at h
  refine ⟨fun d hd => ?_, h.2⟩
  have := h.1 hd
  simp only [diagonals, mem_filter, mem_univ, true_and] at this
  exact this

theorem arcLe_wholeP (d : Fin n × Fin n) : ArcLe d (wholeP n) := by
  refine ⟨Fin.zero_le _, ?_⟩
  simp only [wholeP, Fin.le_def]
  have := d.2.isLt
  omega

theorem lt_of_mem_nodes {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
    {d : Fin n × Fin n} (hd : d ∈ nodes F) : d.1 < d.2 := by
  rcases mem_insert.1 hd with rfl | hd
  · simp only [wholeP, Fin.lt_def, Fin.val_zero]; omega
  · exact (hF.1 d hd).1

/-- **Laminarity**: two nodes are nested or have disjoint arcs. -/
theorem nodes_laminar {F : Finset (Fin n × Fin n)} (hF : IsTSP F) {d e : Fin n × Fin n}
    (hd : d ∈ nodes F) (he : e ∈ nodes F) :
    ArcLe d e ∨ ArcLe e d ∨ d.2 ≤ e.1 ∨ e.2 ≤ d.1 := by
  rcases mem_insert.1 he with rfl | he'
  · exact Or.inl (arcLe_wholeP d)
  rcases mem_insert.1 hd with rfl | hd'
  · exact Or.inr (Or.inl (arcLe_wholeP e))
  have h1 := hF.2 d hd' e he'
  have hd2 := (hF.1 d hd').1
  have he2 := (hF.1 e he').1
  simp only [Crossing, not_or, not_and, not_lt] at h1
  simp only [ArcLe, Fin.le_def, Fin.lt_def] at h1 hd2 he2 ⊢
  omega

omit [NeZero n] in
theorem InArc.mono {d e : Fin n × Fin n} {v : Fin n} (h : InArc d v) (hde : ArcLe d e) :
    InArc e v := by
  simp only [InArc, ArcLe, Fin.le_def, Fin.lt_def] at *
  omega

omit [NeZero n] in
theorem ArcLe.trans {d e f : Fin n × Fin n} (h1 : ArcLe d e) (h2 : ArcLe e f) : ArcLe d f := by
  simp only [ArcLe, Fin.le_def] at *
  omega

omit [NeZero n] in
theorem ArcLe.antisymm {d e : Fin n × Fin n} (h1 : ArcLe d e) (h2 : ArcLe e d) : d = e := by
  simp only [ArcLe, Fin.le_def] at *
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

omit [NeZero n] in
theorem arcWidth_le_of_arcLe {d e : Fin n × Fin n} (h : ArcLe d e) :
    arcWidth d ≤ arcWidth e := by
  simp only [ArcLe, arcWidth, Fin.le_def] at *
  omega

omit [NeZero n] in
theorem eq_of_arcLe_of_width {d e : Fin n × Fin n} (hd : d.1 ≤ d.2) (h : ArcLe d e)
    (hw : arcWidth e ≤ arcWidth d) : d = e := by
  simp only [ArcLe, arcWidth, Fin.le_def] at *
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- The containers of a vertex are totally ordered by inclusion. -/
theorem arcLe_total_of_inArc {F : Finset (Fin n × Fin n)} (hF : IsTSP F) {d e : Fin n × Fin n}
    (hd : d ∈ nodes F) (he : e ∈ nodes F) {v : Fin n} (hdv : InArc d v) (hev : InArc e v) :
    ArcLe d e ∨ ArcLe e d := by
  rcases nodes_laminar hF hd he with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp only [InArc, Fin.le_def, Fin.lt_def] at hdv hev h; omega
  · simp only [InArc, Fin.le_def, Fin.lt_def] at hdv hev h; omega

/-- **Characterization of `leafPar`**: the node that contains `v` and is contained in every
node containing `v`. -/
theorem leafPar_eq {F : Finset (Fin n × Fin n)} {v : Fin n} {e : Fin n × Fin n}
    (he : e ∈ nodes F) (hev : InArc e v)
    (hmin : ∀ e' ∈ nodes F, InArc e' v → ArcLe e e') : leafPar F v = e := by
  have hmem : e ∈ (nodes F).filter fun e => InArc e v := mem_filter.2 ⟨he, hev⟩
  obtain ⟨h1, h2⟩ := minNode_le hmem
  have h3 := mem_filter.1 h1
  exact (eq_of_arcLe_of_width (le_of_lt (lt_of_le_of_lt hev.1 hev.2)) (hmin _ h3.1 h3.2) h2).symm

/-- The root vertex `n - 1` hangs on `whole`. -/
theorem leafPar_root (F : Finset (Fin n × Fin n)) {v : Fin n} (hv : v.val = n - 1) :
    leafPar F v = wholeP n := by
  rcases minNode_mem_or (s := (nodes F).filter fun e => InArc e v) with h | h
  · exfalso
    have := (mem_filter.1 h).2
    simp only [InArc, Fin.lt_def] at this
    have := (minNode ((nodes F).filter fun e => InArc e v)).2.isLt
    omega
  · exact h

/-- **Characterization of `nodePar`**: the node strictly above `d` contained in every node
strictly above `d`. -/
theorem nodePar_eq {F : Finset (Fin n × Fin n)} {d e : Fin n × Fin n} (hd : d.1 ≤ d.2)
    (he : e ∈ nodes F) (hde : ArcLe d e) (hne : e ≠ d)
    (hmin : ∀ e' ∈ nodes F, ArcLe d e' → e' ≠ d → ArcLe e e') : nodePar F d = e := by
  have hmem : e ∈ (nodes F).filter fun e => ArcLe d e ∧ e ≠ d := mem_filter.2 ⟨he, hde, hne⟩
  obtain ⟨h1, h2⟩ := minNode_le hmem
  have h3 := mem_filter.1 h1
  have he12 : e.1 ≤ e.2 := le_trans hde.1 (le_trans hd hde.2)
  exact (eq_of_arcLe_of_width he12 (hmin _ h3.1 h3.2.1 h3.2.2) h2).symm

/-- The strict containers of a node are totally ordered by inclusion. -/
theorem arcLe_total_of_arcLe {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
    {d e e' : Fin n × Fin n} (hd : d ∈ nodes F) (he : e ∈ nodes F) (he' : e' ∈ nodes F)
    (h1 : ArcLe d e) (h2 : ArcLe d e') : ArcLe e e' ∨ ArcLe e' e := by
  have hlt := lt_of_mem_nodes hF hn hd
  rcases nodes_laminar hF he he' with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp only [ArcLe, Fin.le_def, Fin.lt_def] at h1 h2 h hlt; omega
  · simp only [ArcLe, Fin.le_def, Fin.lt_def] at h1 h2 h hlt; omega

/-- `leafPar` is the smallest container of a non-root vertex. -/
theorem leafPar_spec {F : Finset (Fin n × Fin n)} (hF : IsTSP F) {v : Fin n}
    (hv : v.val < n - 1) :
    InArc (leafPar F v) v ∧ ∀ e ∈ nodes F, InArc e v → ArcLe (leafPar F v) e := by
  have hW : wholeP n ∈ (nodes F).filter fun e => InArc e v := by
    refine mem_filter.2 ⟨wholeP_mem_nodes F, Fin.zero_le _, ?_⟩
    simp only [wholeP, Fin.lt_def]; exact hv
  obtain ⟨h1, h2⟩ := minNode_le hW
  have hm := mem_filter.1 h1
  refine ⟨hm.2, fun e he hev => ?_⟩
  rcases arcLe_total_of_inArc hF hm.1 he hm.2 hev with h | h
  · exact h
  · have hemem : e ∈ (nodes F).filter fun e => InArc e v := mem_filter.2 ⟨he, hev⟩
    have := (minNode_le hemem).2
    rw [eq_of_arcLe_of_width (le_of_lt (lt_of_le_of_lt hev.1 hev.2)) h this]
    exact ⟨le_refl _, le_refl _⟩

/-- `nodePar` is the smallest strict container of a node other than `whole`. -/
theorem nodePar_spec {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
    {d : Fin n × Fin n} (hd : d ∈ nodes F) (hdw : d ≠ wholeP n) :
    nodePar F d ∈ nodes F ∧ ArcLe d (nodePar F d) ∧ nodePar F d ≠ d ∧
      ∀ e ∈ nodes F, ArcLe d e → e ≠ d → ArcLe (nodePar F d) e := by
  have hW : wholeP n ∈ (nodes F).filter fun e => ArcLe d e ∧ e ≠ d :=
    mem_filter.2 ⟨wholeP_mem_nodes F, arcLe_wholeP d, fun h => hdw h.symm⟩
  obtain ⟨h1, h2⟩ := minNode_le hW
  have hm := mem_filter.1 h1
  have hlt := lt_of_mem_nodes hF hn hd
  refine ⟨hm.1, hm.2.1, hm.2.2, fun e he hde hne => ?_⟩
  rcases arcLe_total_of_arcLe hF hn hd hm.1 he hm.2.1 hde with h | h
  · exact h
  · have hemem : e ∈ (nodes F).filter fun e => ArcLe d e ∧ e ≠ d := mem_filter.2 ⟨he, hde, hne⟩
    have := (minNode_le hemem).2
    have he12 : e.1 ≤ e.2 := le_trans hde.1 (le_trans (le_of_lt hlt) hde.2)
    rw [eq_of_arcLe_of_width he12 h this]
    exact ⟨le_refl _, le_refl _⟩

theorem wholeP_not_mem {F : Finset (Fin n × Fin n)} (hF : IsTSP F) : wholeP n ∉ F := by
  intro h
  have := (hF.1 _ h).2.2
  simp [wholeP] at this

/-- A vertex in some arc is not the root. -/
theorem lt_of_inArc {d : Fin n × Fin n} {v : Fin n} (hv : InArc d v) : v.val < n - 1 := by
  have := (arcLe_wholeP d).2
  simp only [InArc, wholeP, Fin.le_def, Fin.lt_def] at hv this
  omega

/-! ### Which side of a cut `J` the parents lie on -/

section Side

variable {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) {J : Fin n × Fin n}
  (hJ : J ∈ F)
include hF hJ

theorem not_arcLe_wholeP : ¬ArcLe (wholeP n) J := by
  intro h
  have hJd := (hF.1 J hJ)
  obtain ⟨-, -, hw⟩ := hJd
  simp only [ArcLe, wholeP, Fin.le_def] at h
  apply hw
  have := J.2.isLt
  constructor <;> simp only [Fin.val_zero] at h ⊢ <;> omega

theorem ne_wholeP : J ≠ wholeP n := fun h => wholeP_not_mem hF (h ▸ hJ)

theorem leafPar_arcLe_of_inArc {v : Fin n} (hv : InArc J v) : ArcLe (leafPar F v) J :=
  (leafPar_spec hF (lt_of_inArc hv)).2 J (mem_nodes_of_mem hJ) hv

theorem not_arcLe_leafPar {v : Fin n} (hv : ¬InArc J v) : ¬ArcLe (leafPar F v) J := by
  intro h
  by_cases hr : v.val < n - 1
  · exact hv ((leafPar_spec hF hr).1.mono h)
  · have hroot : v.val = n - 1 := by have := v.isLt; omega
    rw [leafPar_root F hroot] at h
    exact not_arcLe_wholeP hF hJ h

include hn in
theorem nodePar_arcLe {d : Fin n × Fin n} (hd : d ∈ F) (hdJ : ArcLe d J) (hne : d ≠ J) :
    ArcLe (nodePar F d) J :=
  (nodePar_spec hF hn (mem_nodes_of_mem hd) (ne_wholeP hF hd)).2.2.2 J (mem_nodes_of_mem hJ) hdJ
    (Ne.symm hne)

include hn in
omit hJ in
theorem not_arcLe_nodePar {d : Fin n × Fin n} (hd : d ∈ F) (hdJ : ¬ArcLe d J) :
    ¬ArcLe (nodePar F d) J := fun h =>
  hdJ ((nodePar_spec hF hn (mem_nodes_of_mem hd) (ne_wholeP hF hd)).2.1.trans h)

include hn in
theorem not_arcLe_nodePar_self : ¬ArcLe (nodePar F J) J := by
  obtain ⟨-, h1, h2, -⟩ := nodePar_spec hF hn (mem_nodes_of_mem hJ) (ne_wholeP hF hJ)
  exact fun h => h2 (h.antisymm h1)

end Side

end Laminar

section Generic

variable (L : ℕ) [NeZero L]

/-- The value of a weighted tree with internal nodes `Nd`, leaves `Lf` and internal edges
`Ed`: the leaf `ℓ` has label `a ℓ`, weight `M ℓ` and hangs on `p ℓ`; the edge `e` has weight
`E e` from `c e` to `q e`.  `∑_b ∏_ℓ (M_ℓ)_{a_ℓ, b(p ℓ)} ∏_e (E_e)_{b(c e), b(q e)}`. -/
noncomputable def gval {Nd Lf Ed : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Lf] [Fintype Ed]
    (a : Lf → ZMod L) (M : Lf → Matrix (ZMod L) (ZMod L) ℂ) (p : Lf → Nd)
    (E : Ed → Matrix (ZMod L) (ZMod L) ℂ) (c q : Ed → Nd) : ℂ :=
  ∑ b : Nd → ZMod L, (∏ ℓ, M ℓ (a ℓ) (b (p ℓ))) * ∏ e, E e (b (c e)) (b (q e))

variable {L}

/-- **Transport**: the value only depends on the tree up to isomorphism. -/
theorem gval_congr {Nd Lf Ed Nd' Lf' Ed' : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Lf]
    [Fintype Ed] [Fintype Nd'] [DecidableEq Nd'] [Fintype Lf'] [Fintype Ed']
    (eN : Nd ≃ Nd') (eL : Lf ≃ Lf') (eE : Ed ≃ Ed')
    {a : Lf → ZMod L} {M : Lf → Matrix (ZMod L) (ZMod L) ℂ} {p : Lf → Nd}
    {E : Ed → Matrix (ZMod L) (ZMod L) ℂ} {c q : Ed → Nd}
    {a' : Lf' → ZMod L} {M' : Lf' → Matrix (ZMod L) (ZMod L) ℂ} {p' : Lf' → Nd'}
    {E' : Ed' → Matrix (ZMod L) (ZMod L) ℂ} {c' q' : Ed' → Nd'}
    (ha : ∀ ℓ, a' (eL ℓ) = a ℓ) (hM : ∀ ℓ, M' (eL ℓ) = M ℓ) (hp : ∀ ℓ, p' (eL ℓ) = eN (p ℓ))
    (hE : ∀ e, E' (eE e) = E e) (hc : ∀ e, c' (eE e) = eN (c e))
    (hq : ∀ e, q' (eE e) = eN (q e)) :
    gval L a M p E c q = gval L a' M' p' E' c' q' := by
  unfold gval
  rw [← (eN.arrowCongr (Equiv.refl (ZMod L))).sum_comp]
  refine Fintype.sum_congr _ _ fun b => ?_
  congr 1
  · rw [← eL.prod_comp]
    refine Fintype.prod_congr _ _ fun ℓ => ?_
    simp [Equiv.arrowCongr_apply, ha, hM, hp]
  · rw [← eE.prod_comp]
    refine Fintype.prod_congr _ _ fun e => ?_
    simp [Equiv.arrowCongr_apply, hE, hc, hq]

/-- Reordering a fourfold sum: `(a, b, c, d) ↦ (d, c, a, b)`. -/
theorem sum_perm4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ c, ∑ a, ∑ b, f a b c d :=
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ c, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Reordering a fourfold sum with two `Finset` ranges: `(a, b, c, d) ↦ (d, c, a, b)`. -/
theorem sum_perm4' {α β γ δ : Type*} [Fintype γ] [Fintype δ] (s : Finset α) (t : Finset β)
    (f : α → β → γ → δ → ℂ) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c, ∑ d, f a b c d = ∑ d, ∑ c, ∑ a ∈ s, ∑ b ∈ t, f a b c d :=
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c, ∑ d, f a b c d = ∑ a ∈ s, ∑ b ∈ t, ∑ d, ∑ c, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a ∈ s, ∑ d, ∑ b ∈ t, ∑ c, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ a ∈ s, ∑ b ∈ t, ∑ c, f a b c d := Finset.sum_comm
    _ = ∑ d, ∑ a ∈ s, ∑ c, ∑ b ∈ t, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ a ∈ s, ∑ b ∈ t, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **Splitting along an edge.**  A tree made of two parts `N₁`, `N₂` joined by one edge
`c₀ — q₀` of weight `P S Q` is `∑_{u,w} part₂(u) S_{uw} part₁(w)`, where each part gets the
cut edge back as an extra leaf: `(u, Pᵀ)` on `c₀ ∈ N₂` and `(w, Q)` on `q₀ ∈ N₁`. -/
theorem gval_split {N₁ N₂ Lf₁ Lf₂ Ed₁ Ed₂ : Type*} [Fintype N₁] [DecidableEq N₁] [Fintype N₂]
    [DecidableEq N₂] [Fintype Lf₁] [Fintype Lf₂] [Fintype Ed₁] [Fintype Ed₂]
    (a₁ : Lf₁ → ZMod L) (M₁ : Lf₁ → Matrix (ZMod L) (ZMod L) ℂ) (p₁ : Lf₁ → N₁)
    (E₁ : Ed₁ → Matrix (ZMod L) (ZMod L) ℂ) (c₁ q₁ : Ed₁ → N₁)
    (a₂ : Lf₂ → ZMod L) (M₂ : Lf₂ → Matrix (ZMod L) (ZMod L) ℂ) (p₂ : Lf₂ → N₂)
    (E₂ : Ed₂ → Matrix (ZMod L) (ZMod L) ℂ) (c₂ q₂ : Ed₂ → N₂)
    (P S Q : Matrix (ZMod L) (ZMod L) ℂ) (c₀ : N₂) (q₀ : N₁) :
    gval L (Sum.elim a₁ a₂) (Sum.elim M₁ M₂) (Sum.elim (Sum.inl ∘ p₁) (Sum.inr ∘ p₂))
        (fun o : Option (Ed₁ ⊕ Ed₂) => o.elim (P * S * Q) (Sum.elim E₁ E₂))
        (fun o => o.elim (Sum.inr c₀) (Sum.elim (Sum.inl ∘ c₁) (Sum.inr ∘ c₂)))
        (fun o => o.elim (Sum.inl q₀) (Sum.elim (Sum.inl ∘ q₁) (Sum.inr ∘ q₂)))
      = ∑ u : ZMod L, ∑ w : ZMod L,
          gval L (fun o : Option Lf₂ => o.elim u a₂) (fun o => o.elim P.transpose M₂)
              (fun o => o.elim c₀ p₂) E₂ c₂ q₂
            * S u w *
          gval L (fun o : Option Lf₁ => o.elim w a₁) (fun o => o.elim Q M₁)
              (fun o => o.elim q₀ p₁) E₁ c₁ q₁ := by
  unfold gval
  rw [← (Equiv.sumArrowEquivProdArrow N₁ N₂ (ZMod L)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.prod_sum_type, Fintype.prod_option, Option.elim, Sum.elim_inl,
    Sum.elim_inr, Function.comp_apply, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [sum_perm4]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ =>
    Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  ring

end Generic

section Value

variable (L : ℕ) [NeZero L] {n : ℕ} [NeZero n]

/-- The tree value with abstract leaf weights `M v` and internal edge weights `E d`:
`∑_b ∏_v (M_v)_{a_v, b(par v)} ∏_{d ∈ F} (E_d)_{b(d), b(par d)}`, the sum running over labels
`b` of all internal vertices. -/
noncomputable def treeValW (F : Finset (Fin n × Fin n)) (a : Fin n → ZMod L)
    (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) : ℂ :=
  ∑ b : ↥(nodes F) → ZMod L,
    (∏ v : Fin n, M v (a v) (b ⟨leafPar F v, leafPar_mem F v⟩)) *
      ∏ d : ↥F, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)

/-- **Definition 3.3**, pivot-free: the value of the tree of `F`, with leaf edges
`Θ_{t m(σ_v) m(σ_{v+1})}` and internal edges `Θ_{t m(σ_i) m(σ_j)} - 1`. -/
noncomputable def treeValG (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → ZMod L)
    (F : Finset (Fin n × Fin n)) : ℂ :=
  treeValW L F a (fun v => thetaEdge L m t (σ v) (σ (v + 1)))
    (fun d => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1)

theorem treeValW_eq_gval (F : Finset (Fin n × Fin n)) (a : Fin n → ZMod L)
    (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) :
    treeValW L F a M E
      = gval L a M (fun v => (⟨leafPar F v, leafPar_mem F v⟩ : ↥(nodes F))) E
          (fun d => (⟨d.1, mem_nodes_of_mem d.2⟩ : ↥(nodes F)))
          (fun d => (⟨nodePar F d, nodePar_mem F d⟩ : ↥(nodes F))) :=
  rfl

/-- The empty family is the star `∑_b ∏_v (M_v)_{a_v b}`. -/
theorem treeValW_empty (a : Fin n → ZMod L) (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    (E : ↥(∅ : Finset (Fin n × Fin n)) → Matrix (ZMod L) (ZMod L) ℂ) :
    treeValW L ∅ a M E = ∑ b : ZMod L, ∏ v : Fin n, M v (a v) b := by
  have hn : nodes (∅ : Finset (Fin n × Fin n)) = {wholeP n} := by simp [nodes]
  have : Unique ↥(nodes (∅ : Finset (Fin n × Fin n))) :=
    { default := ⟨wholeP n, wholeP_mem_nodes _⟩
      uniq := fun x => Subtype.ext (by
        have hx : (x : Fin n × Fin n) ∈ ({wholeP n} : Finset (Fin n × Fin n)) := by
          simpa [nodes] using x.2
        exact mem_singleton.1 hx) }
  rw [treeValW, ← (Equiv.funUnique ↥(nodes (∅ : Finset (Fin n × Fin n))) (ZMod L)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun c => ?_
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, leafPar_empty]
  rfl

/-! ### The derivative: one term per edge -/

variable {F : Finset (Fin n × Fin n)} {a : Fin n → ZMod L}
  {M : ℝ → Fin n → Matrix (ZMod L) (ZMod L) ℂ} {E : ℝ → ↥F → Matrix (ZMod L) (ZMod L) ℂ}
  {M' : Fin n → Matrix (ZMod L) (ZMod L) ℂ} {E' : ↥F → Matrix (ZMod L) (ZMod L) ℂ} {t : ℝ}

theorem prod_update_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) (g : ι → ℂ) (v : ι)
    (hg : ∀ w, w ≠ v → g w = f w) :
    ∏ w, g w = g v * ∏ w ∈ Finset.univ.erase v, f w := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  congr 1
  exact Finset.prod_congr rfl fun w hw => hg w (Finset.ne_of_mem_erase hw)

/-- The derivative of the tree value is the sum over its edges of the value with that edge
differentiated. -/
theorem hasDerivAt_treeValW (hM : ∀ v i j, HasDerivAt (fun r => M r v i j) (M' v i j) t)
    (hE : ∀ d i j, HasDerivAt (fun r => E r d i j) (E' d i j) t) :
    HasDerivAt (fun r => treeValW L F a (M r) (E r))
      (∑ v : Fin n, treeValW L F a (Function.update (M t) v (M' v)) (E t)
        + ∑ d : ↥F, treeValW L F a (M t) (Function.update (E t) d (E' d))) t := by
  classical
  simp only [treeValW]
  refine (HasDerivAt.fun_sum fun b _ =>
    (HasDerivAt.fun_finsetProd fun v _ => hM v _ _).mul
      (HasDerivAt.fun_finsetProd fun d _ => hE d _ _)).congr_deriv ?_
  conv_rhs => arg 1; rw [Finset.sum_comm]
  conv_rhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [prod_update_eq (fun w => M t w (a w) (b ⟨leafPar F w, leafPar_mem F w⟩)) _ v
      (fun w hw => by rw [Function.update_of_ne hw]), Function.update_self, smul_eq_mul]
    ring
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [prod_update_eq (fun e => E t e (b ⟨e.1, mem_nodes_of_mem e.2⟩)
      (b ⟨nodePar F e, nodePar_mem F e⟩)) _ d (fun e he => by rw [Function.update_of_ne he]),
      Function.update_self, smul_eq_mul]
    ring

end Value

section Cut

variable (L : ℕ) [NeZero L] {n : ℕ} [NeZero n]

/-- Nodes, leaves and internal edges inside / outside the arc of a cut `J`. -/
abbrev NIn (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) := {x : ↥(nodes F) // ArcLe x.1 J}
abbrev NOut (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) := {x : ↥(nodes F) // ¬ArcLe x.1 J}
abbrev LIn (J : Fin n × Fin n) := {v : Fin n // InArc J v}
abbrev LOut (J : Fin n × Fin n) := {v : Fin n // ¬InArc J v}
abbrev EIn (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) := {d : ↥F // ArcLe d.1 J ∧ d.1 ≠ J}
abbrev EOut (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) := {d : ↥F // ¬ArcLe d.1 J}

variable {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) {J : Fin n × Fin n}
  (hJ : J ∈ F)

/-- The parent of an inside leaf, as an inside node. -/
noncomputable def inLeafPar (v : LIn J) : NIn F J :=
  ⟨⟨leafPar F v, leafPar_mem F v⟩, leafPar_arcLe_of_inArc hF hJ v.2⟩

/-- The parent of an outside leaf, as an outside node. -/
noncomputable def outLeafPar (v : LOut J) : NOut F J :=
  ⟨⟨leafPar F v, leafPar_mem F v⟩, not_arcLe_leafPar hF hJ v.2⟩

/-- The child and parent ends of an inside edge. -/
def inChild (d : EIn F J) : NIn F J := ⟨⟨d.1.1, mem_nodes_of_mem d.1.2⟩, d.2.1⟩

noncomputable def inPar (d : EIn F J) : NIn F J :=
  ⟨⟨nodePar F d.1.1, nodePar_mem F _⟩, nodePar_arcLe hF hn hJ d.1.2 d.2.1 d.2.2⟩

/-- The child and parent ends of an outside edge. -/
def outChild (d : EOut F J) : NOut F J := ⟨⟨d.1.1, mem_nodes_of_mem d.1.2⟩, d.2⟩

noncomputable def outPar (d : EOut F J) : NOut F J :=
  ⟨⟨nodePar F d.1.1, nodePar_mem F _⟩, not_arcLe_nodePar hF hn d.1.2 d.2⟩

/-- The two ends of the cut edge `J`. -/
def cutIn : NIn F J := ⟨⟨J, mem_nodes_of_mem hJ⟩, ⟨le_refl _, le_refl _⟩⟩

noncomputable def cutOut : NOut F J :=
  ⟨⟨nodePar F J, nodePar_mem F J⟩, not_arcLe_nodePar_self hF hn hJ⟩

/-- The edges of `F`: the cut `J`, the outside edges and the inside edges. -/
def edgeEquiv : ↥F ≃ Option (EOut F J ⊕ EIn F J) where
  toFun d := if h1 : d.1 = J then none else
    if h2 : ArcLe d.1 J then some (Sum.inr ⟨d, h2, h1⟩) else some (Sum.inl ⟨d, h2⟩)
  invFun o := o.elim ⟨J, hJ⟩ (Sum.elim (fun x => x.1) (fun x => x.1))
  left_inv d := by
    by_cases h1 : d.1 = J
    · simp only [h1, dite_true, Option.elim]; exact Subtype.ext h1.symm
    · by_cases h2 : ArcLe d.1 J <;> simp [h1, h2]
  right_inv o := by
    rcases o with _ | x | x
    · simp
    · have h2 := x.2
      have h1 : x.1.1 ≠ J := fun h => h2 (by rw [h]; exact ⟨le_refl _, le_refl _⟩)
      simp [h1, h2]
    · have h1 := x.2.2
      have h2 := x.2.1
      simp [h1, h2]

/-- **Cutting a tree at the internal edge `J`.**  If the edge `J` carries `P S Q`, the tree
value is `∑_{u,w} (inside tree + root leaf (u, Pᵀ)) S_{uw} (outside tree + leaf (w, Q))`. -/
theorem treeValW_cut (a : Fin n → ZMod L) (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) (P S Q : Matrix (ZMod L) (ZMod L) ℂ) :
    treeValW L F a M (Function.update E ⟨J, hJ⟩ (P * S * Q))
      = ∑ u : ZMod L, ∑ w : ZMod L,
          gval L (fun o : Option (LIn J) => o.elim u (fun v => a v.1))
              (fun o => o.elim P.transpose (fun v => M v.1))
              (fun o => o.elim (cutIn hJ) (inLeafPar hF hJ)) (fun d : EIn F J => E d.1)
              inChild (inPar hF hn hJ)
            * S u w *
          gval L (fun o : Option (LOut J) => o.elim w (fun v => a v.1))
              (fun o => o.elim Q (fun v => M v.1))
              (fun o => o.elim (cutOut hF hn hJ) (outLeafPar hF hJ)) (fun d : EOut F J => E d.1)
              outChild (outPar hF hn) := by
  rw [treeValW_eq_gval, ← gval_split]
  refine gval_congr
    ((Equiv.sumCompl (fun x : ↥(nodes F) => ArcLe x.1 J)).symm.trans (Equiv.sumComm _ _))
    ((Equiv.sumCompl (fun v : Fin n => InArc J v)).symm.trans (Equiv.sumComm _ _))
    (edgeEquiv hJ) ?_ ?_ ?_ ?_ ?_ ?_
  · intro v
    by_cases h : InArc J v
    · simp [Equiv.sumCompl_symm_apply_of_pos h]
    · simp [Equiv.sumCompl_symm_apply_of_neg h]
  · intro v
    by_cases h : InArc J v
    · simp [Equiv.sumCompl_symm_apply_of_pos h]
    · simp [Equiv.sumCompl_symm_apply_of_neg h]
  · intro v
    by_cases h : InArc J v
    · have h' : ArcLe (leafPar F v) J := leafPar_arcLe_of_inArc hF hJ h
      simp [Equiv.sumCompl_symm_apply_of_pos h, Equiv.sumCompl_symm_apply_of_pos
        (p := fun x : ↥(nodes F) => ArcLe x.1 J) (a := ⟨leafPar F v, leafPar_mem F v⟩) h',
        inLeafPar]
    · have h' : ¬ArcLe (leafPar F v) J := not_arcLe_leafPar hF hJ h
      simp [Equiv.sumCompl_symm_apply_of_neg h, Equiv.sumCompl_symm_apply_of_neg
        (p := fun x : ↥(nodes F) => ArcLe x.1 J) (a := ⟨leafPar F v, leafPar_mem F v⟩) h',
        outLeafPar]
  · intro d
    by_cases h1 : d.1 = J
    · have hd : d = ⟨J, hJ⟩ := Subtype.ext h1
      subst hd
      simp [edgeEquiv]
    · have hne : d ≠ ⟨J, hJ⟩ := fun h => h1 (congrArg Subtype.val h)
      by_cases h2 : ArcLe d.1 J <;> simp [edgeEquiv, h1, h2, Function.update_of_ne hne]
  · intro d
    by_cases h1 : d.1 = J
    · have hd : d = ⟨J, hJ⟩ := Subtype.ext h1
      subst hd
      simp [edgeEquiv, Equiv.sumCompl_symm_apply_of_pos
        (p := fun x : ↥(nodes F) => ArcLe x.1 J) (a := ⟨J, mem_nodes_of_mem hJ⟩)
        (⟨le_refl _, le_refl _⟩ : ArcLe J J), cutIn]
    · by_cases h2 : ArcLe d.1 J
      · simp [edgeEquiv, h1, h2, Equiv.sumCompl_symm_apply_of_pos
          (p := fun x : ↥(nodes F) => ArcLe x.1 J) (a := ⟨d.1, mem_nodes_of_mem d.2⟩) h2,
          inChild]
      · simp [edgeEquiv, h1, h2, Equiv.sumCompl_symm_apply_of_neg
          (p := fun x : ↥(nodes F) => ArcLe x.1 J) (a := ⟨d.1, mem_nodes_of_mem d.2⟩) h2,
          outChild]
  · intro d
    by_cases h1 : d.1 = J
    · have hd : d = ⟨J, hJ⟩ := Subtype.ext h1
      subst hd
      simp [edgeEquiv, Equiv.sumCompl_symm_apply_of_neg
        (p := fun x : ↥(nodes F) => ArcLe x.1 J) (a := ⟨nodePar F J, nodePar_mem F J⟩)
        (not_arcLe_nodePar_self hF hn hJ), cutOut]
    · by_cases h2 : ArcLe d.1 J
      · simp [edgeEquiv, h1, h2, Equiv.sumCompl_symm_apply_of_pos
          (p := fun x : ↥(nodes F) => ArcLe x.1 J) (a := ⟨nodePar F d.1, nodePar_mem F _⟩)
          (nodePar_arcLe hF hn hJ d.2 h2 h1), inPar]
      · simp [edgeEquiv, h1, h2, Equiv.sumCompl_symm_apply_of_neg
          (p := fun x : ↥(nodes F) => ArcLe x.1 J) (a := ⟨nodePar F d.1, nodePar_mem F _⟩)
          (not_arcLe_nodePar hF hn d.2 h2), outPar]

end Cut

section CutIn

variable {n : ℕ} [NeZero n]

/-- The width `j - i` of the cut `J = (i, j)`: the inside polygon has `wIn J + 1` vertices. -/
def wIn (J : Fin n × Fin n) : ℕ := J.2.val - J.1.val

/-- Shift a region pair inside `J` to the inside polygon: `(x₁, x₂) ↦ (x₁ - i, x₂ - i)`. -/
def shiftIn (J : Fin n × Fin n) (d : Fin n × Fin n) : Fin (wIn J + 1) × Fin (wIn J + 1) :=
  (⟨min (d.1.val - J.1.val) (wIn J), by omega⟩, ⟨min (d.2.val - J.1.val) (wIn J), by omega⟩)

/-- The family of the inside polygon: the edges strictly inside `J`, shifted. -/
def FIn (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) :
    Finset (Fin (wIn J + 1) × Fin (wIn J + 1)) :=
  (F.filter fun d => ArcLe d J ∧ d ≠ J).image (shiftIn J)

/-- The inside vertex `v ∈ J` in the inside polygon: `v - i`. -/
def inV (J : Fin n × Fin n) (v : Fin n) : Fin (wIn J + 1) :=
  ⟨min (v.val - J.1.val) (wIn J), by omega⟩

variable {J : Fin n × Fin n}

omit [NeZero n] in
theorem shiftIn_val {d : Fin n × Fin n} (h : ArcLe d J) (h12 : d.1 ≤ d.2) :
    (shiftIn J d).1.val = d.1.val - J.1.val ∧ (shiftIn J d).2.val = d.2.val - J.1.val := by
  simp only [ArcLe, Fin.le_def] at h h12
  simp only [shiftIn, wIn]
  constructor <;> omega

omit [NeZero n] in
theorem inV_val {v : Fin n} (h : InArc J v) : (inV J v).val = v.val - J.1.val := by
  simp only [InArc, Fin.le_def, Fin.lt_def] at h
  simp only [inV, wIn]
  omega

omit [NeZero n] in
theorem shiftIn_self : shiftIn J J = wholeP (wIn J + 1) := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp [shiftIn, wholeP, wIn]

omit [NeZero n] in
theorem shiftIn_injOn {d e : Fin n × Fin n} (hd : ArcLe d J) (hd12 : d.1 ≤ d.2)
    (he : ArcLe e J) (he12 : e.1 ≤ e.2) (h : shiftIn J d = shiftIn J e) : d = e := by
  have h1 := shiftIn_val hd hd12
  have h2 := shiftIn_val he he12
  have h3 := congrArg (fun x => x.1.val) h
  have h4 := congrArg (fun x => x.2.val) h
  simp only [ArcLe, Fin.le_def] at hd he hd12 he12
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

omit [NeZero n] in
theorem arcLe_shiftIn_iff {d e : Fin n × Fin n} (hd : ArcLe d J) (hd12 : d.1 ≤ d.2)
    (he : ArcLe e J) (he12 : e.1 ≤ e.2) :
    ArcLe (shiftIn J d) (shiftIn J e) ↔ ArcLe d e := by
  have h1 := shiftIn_val hd hd12
  have h2 := shiftIn_val he he12
  simp only [ArcLe, Fin.le_def] at hd he hd12 he12 ⊢
  omega

omit [NeZero n] in
theorem inArc_shiftIn_iff {d : Fin n × Fin n} (hd : ArcLe d J) (hd12 : d.1 ≤ d.2) {v : Fin n}
    (hv : InArc J v) : InArc (shiftIn J d) (inV J v) ↔ InArc d v := by
  have h1 := shiftIn_val hd hd12
  have h2 := inV_val hv
  simp only [ArcLe, InArc, Fin.le_def, Fin.lt_def] at hd hv hd12 ⊢
  omega

variable {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
include hF hJ

theorem shiftIn_mem_nodes {x : Fin n × Fin n} (hx : x ∈ nodes F) (hxJ : ArcLe x J) :
    shiftIn J x ∈ nodes (FIn F J) := by
  by_cases h : x = J
  · subst h
    rw [shiftIn_self]
    exact wholeP_mem_nodes _
  · have hxF : x ∈ F := by
      rcases mem_insert.1 hx with rfl | hx
      · exact absurd hxJ (not_arcLe_wholeP hF hJ)
      · exact hx
    exact mem_nodes_of_mem (mem_image_of_mem _ (mem_filter.2 ⟨hxF, hxJ, h⟩))

omit hF in
theorem exists_of_mem_nodes_FIn {y : Fin (wIn J + 1) × Fin (wIn J + 1)}
    (hy : y ∈ nodes (FIn F J)) : ∃ x ∈ nodes F, ArcLe x J ∧ shiftIn J x = y := by
  rcases mem_insert.1 hy with rfl | hy
  · exact ⟨J, mem_nodes_of_mem hJ, ⟨le_refl _, le_refl _⟩, shiftIn_self⟩
  · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    have hx' := mem_filter.1 hx
    exact ⟨x, mem_nodes_of_mem hx'.1, hx'.2.1, rfl⟩

include hn

/-- **The inside part of a cut is a tree value on the inside polygon** `Fin (wIn J + 1)`:
`J` becomes the root node, the inside leaves are shifted by `-i`, and the cut leaf becomes the
root vertex `wIn J`. -/
theorem gval_in_eq (L : ℕ) [NeZero L] (a : Fin n → ZMod L) (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) (u : ZMod L) (R : Matrix (ZMod L) (ZMod L) ℂ)
    (a' : Fin (wIn J + 1) → ZMod L) (M' : Fin (wIn J + 1) → Matrix (ZMod L) (ZMod L) ℂ)
    (E' : ↥(FIn F J) → Matrix (ZMod L) (ZMod L) ℂ)
    (ha0 : a' (Fin.last _) = u) (ha1 : ∀ v : LIn J, a' (inV J v) = a v)
    (hM0 : M' (Fin.last _) = R) (hM1 : ∀ v : LIn J, M' (inV J v) = M v)
    (hE : ∀ d : EIn F J,
      E' ⟨shiftIn J d.1.1, mem_image_of_mem _ (mem_filter.2 ⟨d.1.2, d.2⟩)⟩ = E d.1) :
    gval L (fun o : Option (LIn J) => o.elim u (fun v => a v.1))
        (fun o => o.elim R (fun v => M v.1))
        (fun o => o.elim (cutIn hJ) (inLeafPar hF hJ)) (fun d : EIn F J => E d.1)
        inChild (inPar hF hn hJ)
      = treeValW L (FIn F J) a' M' E' := by
  have h12 : ∀ x ∈ nodes F, x.1 ≤ x.2 := fun x hx => le_of_lt (lt_of_mem_nodes hF hn hx)
  -- the three bijections
  let fN : NIn F J → ↥(nodes (FIn F J)) := fun x =>
    ⟨shiftIn J x.1.1, shiftIn_mem_nodes hF hJ x.1.2 x.2⟩
  have hfN : Function.Bijective fN := by
    constructor
    · intro x y h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (shiftIn_injOn x.2 (h12 _ x.1.2) y.2 (h12 _ y.1.2) this))
    · intro y
      obtain ⟨x, hx, hxJ, hxy⟩ := exists_of_mem_nodes_FIn hJ y.2
      exact ⟨⟨⟨x, hx⟩, hxJ⟩, Subtype.ext hxy⟩
  let fL : Option (LIn J) → Fin (wIn J + 1) := fun o => o.elim (Fin.last _) (fun v => inV J v.1)
  have hlt : ∀ v : LIn J, (inV J v.1).val < wIn J := by
    intro v
    have h1 := inV_val v.2
    have h2 := v.2
    simp only [InArc, Fin.le_def, Fin.lt_def] at h2
    simp only [wIn]; omega
  have hfL : Function.Bijective fL := by
    constructor
    · rintro (_ | v) (_ | v') h
      · rfl
      · have := hlt v'; simp only [fL, Option.elim, Fin.ext_iff, Fin.val_last] at h; omega
      · have := hlt v; simp only [fL, Option.elim, Fin.ext_iff, Fin.val_last] at h; omega
      · simp only [fL, Option.elim, Fin.ext_iff] at h
        have h1 := inV_val v.2
        have h2 := inV_val v'.2
        have h3 := v.2
        have h4 := v'.2
        simp only [InArc, Fin.le_def] at h3 h4
        exact congrArg some (Subtype.ext (Fin.ext (by omega)))
    · intro i
      by_cases hi : i.val = wIn J
      · exact ⟨none, Fin.ext (by simp [fL, hi])⟩
      · have hi' : i.val < wIn J := by have := i.isLt; omega
        have hv : i.val + J.1.val < n := by
          have := J.2.isLt; simp only [wIn] at hi'; omega
        have hin : InArc J ⟨i.val + J.1.val, hv⟩ := by
          simp only [InArc, Fin.le_def, Fin.lt_def]; simp only [wIn] at hi'; omega
        refine ⟨some ⟨⟨i.val + J.1.val, hv⟩, hin⟩, Fin.ext ?_⟩
        simp only [fL, Option.elim]
        rw [inV_val hin]; simp
  let fE : EIn F J → ↥(FIn F J) := fun d =>
    ⟨shiftIn J d.1.1, mem_image_of_mem _ (mem_filter.2 ⟨d.1.2, d.2⟩)⟩
  have hfE : Function.Bijective fE := by
    constructor
    · intro d e h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (shiftIn_injOn d.2.1 (h12 _ (mem_nodes_of_mem d.1.2))
        e.2.1 (h12 _ (mem_nodes_of_mem e.1.2)) this))
    · intro y
      obtain ⟨x, hx, hxy⟩ := mem_image.1 y.2
      have hx' := mem_filter.1 hx
      exact ⟨⟨⟨x, hx'.1⟩, hx'.2⟩, Subtype.ext hxy⟩
  rw [treeValW_eq_gval]
  refine gval_congr (Equiv.ofBijective fN hfN) (Equiv.ofBijective fL hfL)
    (Equiv.ofBijective fE hfE) ?_ ?_ ?_ ?_ ?_ ?_
  · rintro (_ | v)
    · simpa [fL] using ha0
    · simpa [fL] using ha1 v
  · rintro (_ | v)
    · simpa [fL] using hM0
    · simpa [fL] using hM1 v
  · rintro (_ | v)
    · refine Subtype.ext ?_
      simp only [Equiv.ofBijective_apply, fL, fN, Option.elim, cutIn]
      rw [leafPar_root _ (by simp), shiftIn_self]
    · refine Subtype.ext ?_
      simp only [Equiv.ofBijective_apply, fL, fN, Option.elim, inLeafPar]
      have hr := lt_of_inArc v.2
      have hspec := leafPar_spec hF hr
      have hin := leafPar_arcLe_of_inArc hF hJ v.2
      have hmem := leafPar_mem F v.1
      refine leafPar_eq (shiftIn_mem_nodes hF hJ hmem hin)
        ((inArc_shiftIn_iff hin (h12 _ hmem) v.2).2 hspec.1) ?_
      intro e' he' hev'
      obtain ⟨x, hx, hxJ, rfl⟩ := exists_of_mem_nodes_FIn hJ he'
      have hxv := (inArc_shiftIn_iff hxJ (h12 _ hx) v.2).1 hev'
      exact (arcLe_shiftIn_iff hin (h12 _ hmem) hxJ (h12 _ hx)).2 (hspec.2 x hx hxv)
  · intro d
    simpa [fE] using hE d
  · intro d
    rfl
  · intro d
    refine Subtype.ext ?_
    simp only [Equiv.ofBijective_apply, fE, fN, inPar]
    have hd := mem_nodes_of_mem d.1.2
    have hspec := nodePar_spec hF hn hd (ne_wholeP hF d.1.2)
    have hin := nodePar_arcLe hF hn hJ d.1.2 d.2.1 d.2.2
    have hpm := nodePar_mem F d.1.1
    have hdd := shiftIn_val d.2.1 (h12 _ hd)
    have hlt' := lt_of_mem_nodes hF hn hd
    refine nodePar_eq ?_ (shiftIn_mem_nodes hF hJ hpm hin)
      ((arcLe_shiftIn_iff d.2.1 (h12 _ hd) hin (h12 _ hpm)).2 hspec.2.1) ?_ ?_
    · rw [Fin.le_def, hdd.1, hdd.2]; rw [Fin.lt_def] at hlt'; omega
    · intro h
      exact hspec.2.2.1 (shiftIn_injOn hin (h12 _ hpm) d.2.1 (h12 _ hd) h)
    · intro e' he' hde' hne'
      obtain ⟨x, hx, hxJ, rfl⟩ := exists_of_mem_nodes_FIn hJ he'
      have hdx := (arcLe_shiftIn_iff d.2.1 (h12 _ hd) hxJ (h12 _ hx)).1 hde'
      have hxd : x ≠ d.1.1 := fun h => hne' (by rw [h])
      exact (arcLe_shiftIn_iff hin (h12 _ hpm) hxJ (h12 _ hx)).2 (hspec.2.2.2 x hx hdx hxd)

end CutIn

section CutOut

variable {n : ℕ} [NeZero n]

/-- Collapse the arc of `J = (i, j)` to the single point `i`: `r ↦ r` for `r ≤ i`,
`r ↦ r - (j - i - 1)` beyond. -/
def col (J : Fin n × Fin n) (r : ℕ) : ℕ := if r ≤ J.1.val then r else r - (wIn J - 1)

/-- The outside polygon has `n - wIn J + 1` vertices. -/
def shiftOut (J : Fin n × Fin n) (d : Fin n × Fin n) :
    Fin (n - wIn J + 1) × Fin (n - wIn J + 1) :=
  (⟨min (col J d.1.val) (n - wIn J), by omega⟩, ⟨min (col J d.2.val) (n - wIn J), by omega⟩)

/-- The family of the outside polygon: the edges not inside `J`, collapsed. -/
def FOut (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) :
    Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1)) :=
  (F.filter fun d => ¬ArcLe d J).image (shiftOut J)

/-- An outside vertex in the outside polygon. -/
def outV (J : Fin n × Fin n) (v : Fin n) : Fin (n - wIn J + 1) :=
  ⟨min (col J v.val) (n - wIn J), by omega⟩

/-- The glue vertex of the outside polygon: `J` collapsed to the point `i`. -/
def glueV (J : Fin n × Fin n) : Fin (n - wIn J + 1) := ⟨min J.1.val (n - wIn J), by omega⟩

variable {J : Fin n × Fin n}

/-- The endpoint condition of an outside node: no endpoint strictly inside `J`. -/
def OutEnds (J : Fin n × Fin n) (x : Fin n × Fin n) : Prop :=
  (x.1.val ≤ J.1.val ∨ J.2.val ≤ x.1.val) ∧ (x.2.val ≤ J.1.val ∨ J.2.val ≤ x.2.val) ∧
    x.1.val < x.2.val

omit [NeZero n] in
theorem col_of_le {r : ℕ} (h : r ≤ J.1.val) : col J r = r := by simp [col, h]

omit [NeZero n] in
theorem col_of_gt {r : ℕ} (h : J.1.val < r) : col J r = r - (wIn J - 1) := by
  simp [col, not_le.2 h]

omit [NeZero n] in
theorem col_val {r : ℕ} (hr' : r < n) (hJ2 : J.1.val < J.2.val) :
    min (col J r) (n - wIn J) = col J r := by
  have := J.2.isLt
  simp only [col, wIn] at *
  split_ifs <;> omega

omit [NeZero n] in
theorem shiftOut_val (x : Fin n × Fin n) (hJ2 : J.1.val < J.2.val) :
    (shiftOut J x).1.val = col J x.1.val ∧ (shiftOut J x).2.val = col J x.2.val :=
  ⟨col_val x.1.isLt hJ2, col_val x.2.isLt hJ2⟩

omit [NeZero n] in
theorem outV_val (v : Fin n) (hJ2 : J.1.val < J.2.val) :
    (outV J v).val = col J v.val := by
  exact col_val v.isLt hJ2

omit [NeZero n] in
/-- `col` is strictly monotone on points outside the open arc of `J`. -/
theorem col_le_iff {r s : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r) (hs : s ≤ J.1.val ∨ J.2.val ≤ s)
    (hJ : J.1.val + 2 ≤ J.2.val) : col J r ≤ col J s ↔ r ≤ s := by
  simp only [col, wIn]
  split_ifs <;> omega

omit [NeZero n] in
theorem col_lt_of_vertex {r v : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r)
    (hv : v < J.1.val ∨ J.2.val ≤ v) (hJ : J.1.val + 2 ≤ J.2.val) :
    (col J v < col J r ↔ v < r) ∧ (col J r ≤ col J v ↔ r ≤ v) := by
  simp only [col, wIn]
  constructor <;> split_ifs <;> omega

omit [NeZero n] in
theorem shiftOut_injOn {d e : Fin n × Fin n} (hd : OutEnds J d) (he : OutEnds J e)
    (hJ : J.1.val + 2 ≤ J.2.val) (h : shiftOut J d = shiftOut J e) : d = e := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := shiftOut_val d hJ2
  have h2 := shiftOut_val e hJ2
  have h3 := congrArg (fun x => x.1.val) h
  have h4 := congrArg (fun x => x.2.val) h
  have a1 := (col_le_iff hd.1 he.1 hJ).1 (by omega)
  have a2 := (col_le_iff he.1 hd.1 hJ).1 (by omega)
  have a3 := (col_le_iff hd.2.1 he.2.1 hJ).1 (by omega)
  have a4 := (col_le_iff he.2.1 hd.2.1 hJ).1 (by omega)
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

omit [NeZero n] in
theorem arcLe_shiftOut_iff {d e : Fin n × Fin n} (hd : OutEnds J d) (he : OutEnds J e)
    (hJ : J.1.val + 2 ≤ J.2.val) : ArcLe (shiftOut J d) (shiftOut J e) ↔ ArcLe d e := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := shiftOut_val d hJ2
  have h2 := shiftOut_val e hJ2
  simp only [ArcLe, Fin.le_def, h1, h2, col_le_iff he.1 hd.1 hJ, col_le_iff hd.2.1 he.2.1 hJ]

omit [NeZero n] in
theorem inArc_shiftOut_iff {d : Fin n × Fin n} (hd : OutEnds J d) {v : Fin n}
    (hv : ¬InArc J v) (hJ : J.1.val + 2 ≤ J.2.val) :
    InArc (shiftOut J d) (outV J v) ↔ InArc d v := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := shiftOut_val d hJ2
  have h2 := outV_val v hJ2
  have hv' : v.val < J.1.val ∨ J.2.val ≤ v.val := by
    simp only [InArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv; omega
  simp only [InArc, Fin.le_def, Fin.lt_def, h1, h2, (col_lt_of_vertex hd.1 hv' hJ).2,
    (col_lt_of_vertex hd.2.1 hv' hJ).1]

omit [NeZero n] in
/-- An outside node contains the glue vertex iff it contains `J`. -/
theorem inArc_glue_iff {d : Fin n × Fin n} (hd : OutEnds J d) (hJ : J.1.val + 2 ≤ J.2.val) :
    InArc (shiftOut J d) (glueV J) ↔ ArcLe J d := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := shiftOut_val d hJ2
  have hg : (glueV J).val = J.1.val := by
    have := J.2.isLt; simp only [glueV, wIn]; omega
  obtain ⟨e1, e2, e3⟩ := hd
  simp only [InArc, ArcLe, Fin.le_def, Fin.lt_def, h1, hg]
  simp only [col, wIn]
  split_ifs <;> omega

variable {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
include hF hJ

omit [NeZero n] in
theorem diag_width : J.1.val + 2 ≤ J.2.val := by
  obtain ⟨h1, h2, -⟩ := hF.1 J hJ
  rw [Fin.lt_def] at h1
  omega

include hn in
theorem outEnds_of {x : Fin n × Fin n} (hx : x ∈ nodes F) (hxJ : ¬ArcLe x J) : OutEnds J x := by
  have hlt := lt_of_mem_nodes hF hn hx
  have hJw := diag_width hF hJ
  rcases nodes_laminar hF hx (mem_nodes_of_mem hJ) with h | h | h | h
  · exact absurd h hxJ
  all_goals simp only [ArcLe, Fin.le_def, Fin.lt_def] at h hlt ⊢
  all_goals exact ⟨by omega, by omega, hlt⟩

theorem shiftOut_whole : shiftOut J (wholeP n) = wholeP (n - wIn J + 1) := by
  have hJw := diag_width hF hJ
  have := J.2.isLt
  have hc : col J (n - 1) = n - wIn J := by
    rw [col_of_gt (by omega)]; simp only [wIn]; omega
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · simp [shiftOut, wholeP, col]
  · simp only [shiftOut, wholeP, hc]; simp

theorem shiftOut_mem_nodes {x : Fin n × Fin n} (hx : x ∈ nodes F) (hxJ : ¬ArcLe x J) :
    shiftOut J x ∈ nodes (FOut F J) := by
  rcases mem_insert.1 hx with rfl | hx
  · rw [shiftOut_whole hF hJ]; exact wholeP_mem_nodes _
  · exact mem_nodes_of_mem (mem_image_of_mem _ (mem_filter.2 ⟨hx, hxJ⟩))

theorem exists_of_mem_nodes_FOut {y : Fin (n - wIn J + 1) × Fin (n - wIn J + 1)}
    (hy : y ∈ nodes (FOut F J)) : ∃ x ∈ nodes F, ¬ArcLe x J ∧ shiftOut J x = y := by
  rcases mem_insert.1 hy with rfl | hy
  · exact ⟨wholeP n, wholeP_mem_nodes F, not_arcLe_wholeP hF hJ, shiftOut_whole hF hJ⟩
  · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    have hx' := mem_filter.1 hx
    exact ⟨x, mem_nodes_of_mem hx'.1, hx'.2, rfl⟩

include hn

/-- **The outside part of a cut is a tree value on the outside polygon**
`Fin (n - wIn J + 1)`: `J` collapses to the glue vertex, which hangs on the parent of `J`. -/
theorem gval_out_eq (L : ℕ) [NeZero L] (a : Fin n → ZMod L)
    (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) (x : ZMod L)
    (Q : Matrix (ZMod L) (ZMod L) ℂ) (a' : Fin (n - wIn J + 1) → ZMod L)
    (M' : Fin (n - wIn J + 1) → Matrix (ZMod L) (ZMod L) ℂ)
    (E' : ↥(FOut F J) → Matrix (ZMod L) (ZMod L) ℂ)
    (ha0 : a' (glueV J) = x) (ha1 : ∀ v : LOut J, a' (outV J v) = a v)
    (hM0 : M' (glueV J) = Q) (hM1 : ∀ v : LOut J, M' (outV J v) = M v)
    (hE : ∀ d : EOut F J, E' ⟨shiftOut J d.1.1, mem_image_of_mem _ (mem_filter.2 ⟨d.1.2, d.2⟩)⟩
      = E d.1) :
    gval L (fun o : Option (LOut J) => o.elim x (fun v => a v.1))
        (fun o => o.elim Q (fun v => M v.1))
        (fun o => o.elim (cutOut hF hn hJ) (outLeafPar hF hJ)) (fun d : EOut F J => E d.1)
        outChild (outPar hF hn)
      = treeValW L (FOut F J) a' M' E' := by
  have hJw := diag_width hF hJ
  have hJ2 : J.1.val < J.2.val := by omega
  have hends : ∀ y ∈ nodes F, ¬ArcLe y J → OutEnds J y := fun y hy hyJ => outEnds_of hF hn hJ hy hyJ
  have hg : (glueV J).val = J.1.val := by
    have := J.2.isLt; simp only [glueV, wIn]; omega
  have hvside : ∀ v : LOut J, v.1.val < J.1.val ∨ J.2.val ≤ v.1.val := by
    intro v; have := v.2; simp only [InArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this; omega
  -- nodes
  let fN : NOut F J → ↥(nodes (FOut F J)) := fun y =>
    ⟨shiftOut J y.1.1, shiftOut_mem_nodes hF hJ y.1.2 y.2⟩
  have hfN : Function.Bijective fN := by
    constructor
    · intro y z h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (shiftOut_injOn (hends _ y.1.2 y.2) (hends _ z.1.2 z.2) hJw this))
    · intro y
      obtain ⟨z, hz, hzJ, hzy⟩ := exists_of_mem_nodes_FOut hF hJ y.2
      exact ⟨⟨⟨z, hz⟩, hzJ⟩, Subtype.ext hzy⟩
  -- leaves
  let fL : Option (LOut J) → Fin (n - wIn J + 1) := fun o => o.elim (glueV J) (fun v => outV J v.1)
  have hfL : Function.Bijective fL := by
    constructor
    · have hcol : ∀ v : LOut J, (col J v.1.val < J.1.val ∧ col J v.1.val = v.1.val) ∨
          (J.1.val < col J v.1.val ∧ col J v.1.val = v.1.val - (wIn J - 1)) := by
        intro v
        rcases hvside v with h | h
        · exact Or.inl (by rw [col_of_le (le_of_lt h)]; exact ⟨h, rfl⟩)
        · refine Or.inr ?_
          rw [col_of_gt (lt_of_lt_of_le hJ2 h)]
          refine ⟨?_, rfl⟩
          simp only [wIn]; omega
      rintro (_ | v) (_ | v') h
      · rfl
      · have h1 := outV_val v'.1 hJ2
        simp only [fL, Option.elim, Fin.ext_iff, hg, h1] at h
        rcases hcol v' with h2 | h2 <;> omega
      · have h1 := outV_val v.1 hJ2
        simp only [fL, Option.elim, Fin.ext_iff, hg, h1] at h
        rcases hcol v with h2 | h2 <;> omega
      · have h1 := outV_val v.1 hJ2; have h2 := outV_val v'.1 hJ2
        simp only [fL, Option.elim, Fin.ext_iff, h1, h2] at h
        refine congrArg some (Subtype.ext (Fin.ext ?_))
        have h3 := hvside v; have h4 := hvside v'
        rcases hcol v with h5 | h5 <;> rcases hcol v' with h6 | h6 <;> simp only [wIn] at * <;>
          omega
    · intro i
      have hi := i.isLt
      have := J.2.isLt
      by_cases h1 : i.val = J.1.val
      · exact ⟨none, Fin.ext (by simp [fL, hg, h1])⟩
      by_cases h2 : i.val < J.1.val
      · have hv : ¬InArc J ⟨i.val, by omega⟩ := by
          simp only [InArc, Fin.le_def, Fin.lt_def, not_and, not_lt]; omega
        refine ⟨some ⟨⟨i.val, by omega⟩, hv⟩, Fin.ext ?_⟩
        simp only [fL, Option.elim, outV_val _ hJ2]
        rw [col_of_le (by omega)]
      · have hin : i.val + (wIn J - 1) < n := by simp only [wIn] at hi ⊢; omega
        have hv : ¬InArc J ⟨i.val + (wIn J - 1), hin⟩ := by
          simp only [InArc, Fin.le_def, Fin.lt_def, not_and, not_lt, wIn]; omega
        refine ⟨some ⟨⟨i.val + (wIn J - 1), hin⟩, hv⟩, Fin.ext ?_⟩
        simp only [fL, Option.elim, outV_val _ hJ2]
        rw [col_of_gt (by simp only [wIn]; omega)]
        simp only [wIn]; omega
  -- edges
  let fE : EOut F J → ↥(FOut F J) := fun d =>
    ⟨shiftOut J d.1.1, mem_image_of_mem _ (mem_filter.2 ⟨d.1.2, d.2⟩)⟩
  have hfE : Function.Bijective fE := by
    constructor
    · intro d e h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (shiftOut_injOn (hends _ (mem_nodes_of_mem d.1.2) d.2)
        (hends _ (mem_nodes_of_mem e.1.2) e.2) hJw this))
    · intro y
      obtain ⟨z, hz, hzy⟩ := mem_image.1 y.2
      have hz' := mem_filter.1 hz
      exact ⟨⟨⟨z, hz'.1⟩, hz'.2⟩, Subtype.ext hzy⟩
  rw [treeValW_eq_gval]
  refine gval_congr (Equiv.ofBijective fN hfN) (Equiv.ofBijective fL hfL)
    (Equiv.ofBijective fE hfE) ?_ ?_ ?_ ?_ ?_ ?_
  · rintro (_ | v)
    · simpa [fL] using ha0
    · simpa [fL] using ha1 v
  · rintro (_ | v)
    · simpa [fL] using hM0
    · simpa [fL] using hM1 v
  · rintro (_ | v)
    · -- the glue leaf hangs on the parent of `J`
      refine Subtype.ext ?_
      simp only [Equiv.ofBijective_apply, fL, fN, Option.elim, cutOut]
      have hJn := mem_nodes_of_mem hJ
      have hspec := nodePar_spec hF hn hJn (ne_wholeP hF hJ)
      have hout := not_arcLe_nodePar_self hF hn hJ
      have hpm := nodePar_mem F J
      refine leafPar_eq (shiftOut_mem_nodes hF hJ hpm hout)
        ((inArc_glue_iff (hends _ hpm hout) hJw).2 hspec.2.1) ?_
      intro e' he' hge'
      obtain ⟨z, hz, hzJ, rfl⟩ := exists_of_mem_nodes_FOut hF hJ he'
      have hJz := (inArc_glue_iff (hends _ hz hzJ) hJw).1 hge'
      have hzne : z ≠ J := fun h => hzJ (h ▸ ⟨le_refl _, le_refl _⟩)
      exact (arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2
        (hspec.2.2.2 z hz hJz hzne)
    · refine Subtype.ext ?_
      simp only [Equiv.ofBijective_apply, fL, fN, Option.elim, outLeafPar]
      by_cases hr : v.1.val < n - 1
      · have hspec := leafPar_spec hF hr
        have hout := not_arcLe_leafPar hF hJ v.2
        have hpm := leafPar_mem F v.1
        refine leafPar_eq (shiftOut_mem_nodes hF hJ hpm hout)
          ((inArc_shiftOut_iff (hends _ hpm hout) v.2 hJw).2 hspec.1) ?_
        intro e' he' hve'
        obtain ⟨z, hz, hzJ, rfl⟩ := exists_of_mem_nodes_FOut hF hJ he'
        have hzv := (inArc_shiftOut_iff (hends _ hz hzJ) v.2 hJw).1 hve'
        exact (arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2 (hspec.2 z hz hzv)
      · have hroot : v.1.val = n - 1 := by have := v.1.isLt; omega
        rw [leafPar_root F hroot, shiftOut_whole hF hJ, leafPar_root]
        rw [outV_val _ hJ2, hroot]
        have := J.2.isLt
        rw [col_of_gt (by omega)]
        simp only [wIn]; omega
  · intro d
    simpa [fE] using hE d
  · intro d
    rfl
  · intro d
    refine Subtype.ext ?_
    simp only [Equiv.ofBijective_apply, fE, fN, outPar]
    have hd := mem_nodes_of_mem d.1.2
    have hspec := nodePar_spec hF hn hd (ne_wholeP hF d.1.2)
    have hout := not_arcLe_nodePar hF hn d.1.2 d.2
    have hpm := nodePar_mem F d.1.1
    have hdE := hends _ hd d.2
    have hdd := shiftOut_val d.1.1 hJ2
    have hlt' := lt_of_mem_nodes hF hn hd
    refine nodePar_eq ?_ (shiftOut_mem_nodes hF hJ hpm hout)
      ((arcLe_shiftOut_iff hdE (hends _ hpm hout) hJw).2 hspec.2.1) ?_ ?_
    · rw [Fin.le_def, hdd.1, hdd.2]
      exact (col_le_iff hdE.1 hdE.2.1 hJw).2 (le_of_lt hdE.2.2)
    · intro h
      exact hspec.2.2.1 (shiftOut_injOn (hends _ hpm hout) hdE hJw h)
    · intro e' he' hde' hne'
      obtain ⟨z, hz, hzJ, rfl⟩ := exists_of_mem_nodes_FOut hF hJ he'
      have hdz := (arcLe_shiftOut_iff hdE (hends _ hz hzJ) hJw).1 hde'
      have hzd : z ≠ d.1.1 := fun h => hne' (by rw [h])
      exact (arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2
        (hspec.2.2.2 z hz hdz hzd)

end CutOut

section CutBij

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- Lift a region pair of the inside polygon back: `(i', j') ↦ (i' + J.1, j' + J.1)`. -/
def unShift (J : Fin n × Fin n) (h : Fin (wIn J + 1) × Fin (wIn J + 1)) : Fin n × Fin n :=
  (⟨min (h.1.val + J.1.val) (n - 1), by have := NeZero.pos n; omega⟩,
    ⟨min (h.2.val + J.1.val) (n - 1), by have := NeZero.pos n; omega⟩)

/-- Undo the collapse: `r ↦ r` for `r ≤ i`, `r ↦ r + (w - 1)` beyond. -/
def unCol (J : Fin n × Fin n) (r : ℕ) : ℕ := if r ≤ J.1.val then r else r + (wIn J - 1)

/-- Lift a region pair of the outside polygon back. -/
def unColP (J : Fin n × Fin n) (g : Fin (n - wIn J + 1) × Fin (n - wIn J + 1)) :
    Fin n × Fin n :=
  (⟨min (unCol J g.1.val) (n - 1), by have := NeZero.pos n; omega⟩,
    ⟨min (unCol J g.2.val) (n - 1), by have := NeZero.pos n; omega⟩)

theorem unShift_val (h : Fin (wIn J + 1) × Fin (wIn J + 1)) :
    (unShift J h).1.val = h.1.val + J.1.val ∧ (unShift J h).2.val = h.2.val + J.1.val := by
  have h1 := h.1.isLt; have h2 := h.2.isLt; have := J.2.isLt
  simp only [unShift, wIn] at *
  constructor <;> omega

omit [NeZero n] in
theorem unCol_lt {r : ℕ} (hr : r < n - wIn J + 1) (hJ : J.1.val < J.2.val) : unCol J r < n := by
  have := J.2.isLt
  simp only [unCol, wIn] at *
  split_ifs <;> omega

theorem unColP_val (g : Fin (n - wIn J + 1) × Fin (n - wIn J + 1)) (hJ : J.1.val < J.2.val) :
    (unColP J g).1.val = unCol J g.1.val ∧ (unColP J g).2.val = unCol J g.2.val := by
  have h1 := unCol_lt g.1.isLt hJ; have h2 := unCol_lt g.2.isLt hJ
  simp only [unColP]
  constructor <;> omega

omit [NeZero n] in
theorem unCol_of_le {r : ℕ} (h : r ≤ J.1.val) : unCol J r = r := by simp [unCol, h]

omit [NeZero n] in
theorem unCol_of_gt {r : ℕ} (h : J.1.val < r) : unCol J r = r + (wIn J - 1) := by
  simp [unCol, not_le.2 h]

omit [NeZero n] in
theorem col_unCol {r : ℕ} : col J (unCol J r) = r := by
  simp only [col, unCol, wIn]
  split_ifs <;> omega

omit [NeZero n] in
theorem unCol_col {r : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r) (hJ : J.1.val + 2 ≤ J.2.val) :
    unCol J (col J r) = r := by
  simp only [col, unCol, wIn]
  split_ifs <;> omega

omit [NeZero n] in
theorem unCol_ends {r : ℕ} (hJ : J.1.val + 2 ≤ J.2.val) :
    unCol J r ≤ J.1.val ∨ J.2.val ≤ unCol J r := by
  simp only [unCol, wIn]
  split_ifs <;> omega

theorem shiftIn_unShift (h : Fin (wIn J + 1) × Fin (wIn J + 1)) : shiftIn J (unShift J h) = h := by
  have hv := unShift_val h
  have h1 := h.1.isLt; have h2 := h.2.isLt
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp only [shiftIn, hv] <;> omega

theorem unShift_shiftIn {d : Fin n × Fin n} (hd : ArcLe d J) (h12 : d.1 ≤ d.2) :
    unShift J (shiftIn J d) = d := by
  have hv := shiftIn_val hd h12
  simp only [ArcLe, Fin.le_def] at hd h12
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp only [unShift, hv] <;>
    have := d.2.isLt <;> omega

theorem shiftOut_unColP (g : Fin (n - wIn J + 1) × Fin (n - wIn J + 1))
    (hJ : J.1.val + 2 ≤ J.2.val) : shiftOut J (unColP J g) = g := by
  have hJ2 : J.1.val < J.2.val := by omega
  have hv := unColP_val g hJ2
  have h1 := shiftOut_val (unColP J g) hJ2
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · rw [h1.1, hv.1, col_unCol]
  · rw [h1.2, hv.2, col_unCol]

theorem unColP_shiftOut {d : Fin n × Fin n} (hd : OutEnds J d) (hJ : J.1.val + 2 ≤ J.2.val) :
    unColP J (shiftOut J d) = d := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := shiftOut_val d hJ2
  have hv := unColP_val (shiftOut J d) hJ2
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · rw [hv.1, h1.1, unCol_col hd.1 hJ]
  · rw [hv.2, h1.2, unCol_col hd.2.1 hJ]

/-- A lifted outside pair has no endpoint strictly inside `J`. -/
theorem outEnds_unColP (g : Fin (n - wIn J + 1) × Fin (n - wIn J + 1)) (hg : g.1 < g.2)
    (hJ : J.1.val + 2 ≤ J.2.val) : OutEnds J (unColP J g) := by
  have hJ2 : J.1.val < J.2.val := by omega
  have hv := unColP_val g hJ2
  rw [Fin.lt_def] at hg
  refine ⟨hv.1 ▸ unCol_ends hJ, hv.2 ▸ unCol_ends hJ, ?_⟩
  rw [hv.1, hv.2]
  simp only [unCol, wIn]; split_ifs <;> omega

/-- Glue an outside and an inside family back along `J`. -/
def glueF (J : Fin n × Fin n) (G : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1)))
    (H : Finset (Fin (wIn J + 1) × Fin (wIn J + 1))) : Finset (Fin n × Fin n) :=
  insert J (G.image (unColP J) ∪ H.image (unShift J))

theorem mem_diagonals_iff {m : ℕ} {d : Fin m × Fin m} : d ∈ diagonals m ↔ IsDiag m d.1 d.2 := by
  simp [diagonals]

variable (hJd : IsDiag n J.1 J.2)
include hJd

omit [NeZero n] in
theorem width_of_isDiag : J.1.val + 2 ≤ J.2.val := by
  obtain ⟨h1, h2, -⟩ := hJd; rw [Fin.lt_def] at h1; omega

omit [NeZero n] hJd in
/-- The inside family is a crossing-free family of diagonals. -/
theorem FIn_mem_TSP {F : Finset (Fin n × Fin n)} (hF : IsTSP F) : FIn F J ∈ TSP (wIn J + 1) := by
  rw [mem_TSP]
  constructor
  · intro y hy
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨hdF, hdJ, hne⟩ := mem_filter.1 hd
    obtain ⟨d1, d2, d3⟩ := hF.1 d hdF
    have hv := shiftIn_val hdJ (le_of_lt d1)
    rw [mem_diagonals_iff]
    have hJ' := hdJ
    simp only [ArcLe, Fin.le_def] at hJ'
    have hne' : ¬(d.1.val = J.1.val ∧ d.2.val = J.2.val) := fun h =>
      hne (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
    rw [Fin.lt_def] at d1
    refine ⟨by rw [Fin.lt_def, hv.1, hv.2]; omega, by rw [hv.1, hv.2]; omega, ?_⟩
    rw [hv.1, hv.2]; simp only [wIn]; omega
  · intro y hy z hz hc
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨e, he, rfl⟩ := mem_image.1 hz
    obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
    obtain ⟨heF, heJ, -⟩ := mem_filter.1 he
    have hd1 := (hF.1 d hdF).1
    have he1 := (hF.1 e heF).1
    have hv := shiftIn_val hdJ (le_of_lt hd1)
    have hw := shiftIn_val heJ (le_of_lt he1)
    apply hF.2 d hdF e heF
    simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2] at hc ⊢
    simp only [ArcLe, Fin.le_def] at hdJ heJ
    omega

/-- The outside family is a crossing-free family of diagonals. -/
theorem FOut_mem_TSP {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    FOut F J ∈ TSP (n - wIn J + 1) := by
  have hJw := width_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  rw [mem_TSP]
  constructor
  · intro y hy
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
    have hE := outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ
    obtain ⟨d1, d2, d3⟩ := hF.1 d hdF
    have hv := shiftOut_val d hJ2
    have hne : ¬(d.1.val = J.1.val ∧ d.2.val = J.2.val) := fun h =>
      hdJ (by simp only [ArcLe, Fin.le_def]; omega)
    have hn2 := J.2.isLt
    have hd2 := d.2.isLt
    rw [mem_diagonals_iff]
    obtain ⟨e1, e2, e3⟩ := hE
    refine ⟨?_, ?_, ?_⟩
    · rw [Fin.lt_def, hv.1, hv.2]; simp only [col, wIn]; split_ifs <;> omega
    · rw [hv.1, hv.2]; simp only [col, wIn]; split_ifs <;> omega
    · rw [hv.1, hv.2]; simp only [col, wIn]; split_ifs <;> omega
  · intro y hy z hz hc
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
    obtain ⟨e, he, rfl⟩ := mem_image.1 hz
    obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
    obtain ⟨heF, heJ⟩ := mem_filter.1 he
    have hdE := outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ
    have heE := outEnds_of hF hn hJ (mem_nodes_of_mem heF) heJ
    have hv := shiftOut_val d hJ2
    have hw := shiftOut_val e hJ2
    apply hF.2 d hdF e heF
    obtain ⟨a1, a2, a3⟩ := hdE
    obtain ⟨b1, b2, b3⟩ := heE
    simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2] at hc ⊢
    simp only [col, wIn] at hc
    split_ifs at hc <;> omega

theorem arcLe_unShift (h : Fin (wIn J + 1) × Fin (wIn J + 1)) : ArcLe (unShift J h) J := by
  have hv := unShift_val h
  have hJw := width_of_isDiag hJd
  have h2 := h.2.isLt
  have hw : wIn J = J.2.val - J.1.val := rfl
  constructor
  · rw [Fin.le_def, hv.1]; omega
  · rw [Fin.le_def, hv.2]; omega

omit hJd in
theorem unShift_ne {h : Fin (wIn J + 1) × Fin (wIn J + 1)} (hh : IsDiag (wIn J + 1) h.1 h.2) :
    unShift J h ≠ J := by
  intro he
  have hv := unShift_val h
  obtain ⟨-, -, h3⟩ := hh
  apply h3
  have e1 := congrArg (fun x => x.1.val) he
  have e2 := congrArg (fun x => x.2.val) he
  simp only [hv.1, hv.2] at e1 e2
  simp only [wIn]; omega

theorem not_arcLe_unColP {g : Fin (n - wIn J + 1) × Fin (n - wIn J + 1)}
    (hg : IsDiag (n - wIn J + 1) g.1 g.2) : ¬ArcLe (unColP J g) J := by
  have hJw := width_of_isDiag hJd
  have hv := unColP_val g (by omega)
  obtain ⟨g1, g2, -⟩ := hg
  rw [Fin.lt_def] at g1
  simp only [ArcLe, Fin.le_def, hv.1, hv.2, unCol, wIn]
  split_ifs <;> omega

/-- The glued family is a crossing-free family of diagonals. -/
theorem glueF_mem_TSP {G : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1))}
    {H : Finset (Fin (wIn J + 1) × Fin (wIn J + 1))} (hG : G ∈ TSP (n - wIn J + 1))
    (hH : H ∈ TSP (wIn J + 1)) : glueF J G H ∈ TSP n := by
  have hJw := width_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  rw [mem_TSP] at hG hH ⊢
  have hGd : ∀ g ∈ G, IsDiag _ g.1 g.2 := fun g hg => mem_diagonals_iff.1 (hG.1 hg)
  have hHd : ∀ h ∈ H, IsDiag _ h.1 h.2 := fun h hh => mem_diagonals_iff.1 (hH.1 hh)
  have hn2 := J.2.isLt
  -- the three kinds of elements
  have kinds : ∀ x ∈ glueF J G H, x = J ∨ (∃ g ∈ G, unColP J g = x) ∨
      (∃ h ∈ H, unShift J h = x) := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact Or.inl rfl
    rcases mem_union.1 hx with hx | hx
    · exact Or.inr (Or.inl (mem_image.1 hx))
    · exact Or.inr (Or.inr (mem_image.1 hx))
  constructor
  · intro x hx
    rw [mem_diagonals_iff]
    rcases kinds x hx with rfl | ⟨g, hg, rfl⟩ | ⟨h, hh, rfl⟩
    · exact hJd
    · have hv := unColP_val g hJ2
      obtain ⟨g1, g2, g3⟩ := hGd g hg
      rw [Fin.lt_def] at g1
      refine ⟨?_, ?_, ?_⟩
      · rw [Fin.lt_def, hv.1, hv.2]; simp only [unCol, wIn]; split_ifs <;> omega
      · rw [hv.1, hv.2]; simp only [unCol, wIn]; split_ifs <;> omega
      · rw [hv.1, hv.2]; simp only [unCol, wIn] at g3 ⊢; split_ifs <;> omega
    · have hv := unShift_val h
      obtain ⟨h1, h2, h3⟩ := hHd h hh
      rw [Fin.lt_def] at h1
      have hb := h.2.isLt
      refine ⟨by rw [Fin.lt_def, hv.1, hv.2]; omega, by rw [hv.1, hv.2]; omega, ?_⟩
      rw [hv.1, hv.2]; simp only [wIn] at h3 hb ⊢; omega
  · -- crossing-freeness
    have outE : ∀ g ∈ G, OutEnds J (unColP J g) := fun g hg =>
      outEnds_unColP g (hGd g hg).1 hJw
    have crossJ : ∀ x, OutEnds J x → ¬Crossing J x ∧ ¬Crossing x J := by
      intro x ⟨a1, a2, a3⟩
      simp only [Crossing, Fin.lt_def]; constructor <;> omega
    have crossIn : ∀ h, ¬Crossing J (unShift J h) ∧ ¬Crossing (unShift J h) J := by
      intro h
      have := arcLe_unShift hJd h
      simp only [ArcLe, Fin.le_def] at this
      simp only [Crossing, Fin.lt_def]; constructor <;> omega
    have crossGH : ∀ g h, OutEnds J (unColP J g) →
        ¬Crossing (unColP J g) (unShift J h) ∧ ¬Crossing (unShift J h) (unColP J g) := by
      intro g h ⟨a1, a2, a3⟩
      have := arcLe_unShift hJd h
      simp only [ArcLe, Fin.le_def] at this
      simp only [Crossing, Fin.lt_def]; constructor <;> omega
    have crossGG : ∀ g ∈ G, ∀ g' ∈ G, ¬Crossing (unColP J g) (unColP J g') := by
      intro g hg g' hg' hc
      apply hG.2 g hg g' hg'
      have hv := unColP_val g hJ2
      have hw := unColP_val g' hJ2
      simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2, unCol, wIn] at hc ⊢
      split_ifs at hc <;> omega
    have crossHH : ∀ h ∈ H, ∀ h' ∈ H, ¬Crossing (unShift J h) (unShift J h') := by
      intro h hh h' hh' hc
      apply hH.2 h hh h' hh'
      have hv := unShift_val h
      have hw := unShift_val h'
      simp only [Crossing, Fin.lt_def, hv.1, hv.2, hw.1, hw.2] at hc ⊢
      omega
    intro x hx y hy
    rcases kinds x hx with rfl | ⟨g, hg, rfl⟩ | ⟨h, hh, rfl⟩ <;>
      rcases kinds y hy with rfl | ⟨g', hg', rfl⟩ | ⟨h', hh', rfl⟩
    · exact not_crossing_self _
    · exact (crossJ _ (outE g' hg')).1
    · exact (crossIn h').1
    · exact (crossJ _ (outE g hg)).2
    · exact crossGG g hg g' hg'
    · exact (crossGH g h' (outE g hg)).1
    · exact (crossIn h).2
    · exact (crossGH g' h (outE g' hg')).2
    · exact crossHH h hh h' hh'

theorem FIn_glueF {G : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1))}
    {H : Finset (Fin (wIn J + 1) × Fin (wIn J + 1))} (hG : G ∈ TSP (n - wIn J + 1))
    (hH : H ∈ TSP (wIn J + 1)) : FIn (glueF J G H) J = H := by
  rw [mem_TSP] at hG hH
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    obtain ⟨hxg, hxJ, hne⟩ := mem_filter.1 hx
    rcases mem_insert.1 hxg with rfl | hxg
    · exact absurd rfl hne
    rcases mem_union.1 hxg with hxg | hxg
    · obtain ⟨g, hg, rfl⟩ := mem_image.1 hxg
      exact absurd hxJ (not_arcLe_unColP hJd (mem_diagonals_iff.1 (hG.1 hg)))
    · obtain ⟨h, hh, rfl⟩ := mem_image.1 hxg
      rw [shiftIn_unShift]; exact hh
  · intro hy
    refine mem_image.2 ⟨unShift J y, mem_filter.2 ⟨?_, arcLe_unShift hJd y,
      unShift_ne (mem_diagonals_iff.1 (hH.1 hy))⟩, shiftIn_unShift y⟩
    exact mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ hy))

theorem FOut_glueF {G : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1))}
    {H : Finset (Fin (wIn J + 1) × Fin (wIn J + 1))} (hG : G ∈ TSP (n - wIn J + 1)) :
    FOut (glueF J G H) J = G := by
  have hJw := width_of_isDiag hJd
  rw [mem_TSP] at hG
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    obtain ⟨hxg, hxJ⟩ := mem_filter.1 hx
    rcases mem_insert.1 hxg with rfl | hxg
    · exact absurd ⟨le_refl _, le_refl _⟩ hxJ
    rcases mem_union.1 hxg with hxg | hxg
    · obtain ⟨g, hg, rfl⟩ := mem_image.1 hxg
      rw [shiftOut_unColP g hJw]; exact hg
    · obtain ⟨h, -, rfl⟩ := mem_image.1 hxg
      exact absurd (arcLe_unShift hJd h) hxJ
  · intro hy
    refine mem_image.2 ⟨unColP J y, mem_filter.2 ⟨?_,
      not_arcLe_unColP hJd (mem_diagonals_iff.1 (hG.1 hy))⟩, shiftOut_unColP y hJw⟩
    exact mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ hy))

theorem glueF_cut {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    glueF J (FOut F J) (FIn F J) = F := by
  have hJw := width_of_isDiag hJd
  ext x
  constructor
  · intro hx
    rcases mem_insert.1 hx with rfl | hx
    · exact hJ
    rcases mem_union.1 hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
      obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
      rw [unColP_shiftOut (outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ) hJw]
      exact hdF
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      obtain ⟨d, hd, rfl⟩ := mem_image.1 hy
      obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
      rw [unShift_shiftIn hdJ (le_of_lt (hF.1 d hdF).1)]
      exact hdF
  · intro hx
    by_cases h1 : x = J
    · rw [h1]; exact mem_insert_self _ _
    refine mem_insert_of_mem ?_
    by_cases h2 : ArcLe x J
    · refine mem_union_right _ (mem_image.2 ⟨shiftIn J x, mem_image_of_mem _
        (mem_filter.2 ⟨hx, h2, h1⟩), unShift_shiftIn h2 (le_of_lt (hF.1 x hx).1)⟩)
    · refine mem_union_left _ (mem_image.2 ⟨shiftOut J x, mem_image_of_mem _
        (mem_filter.2 ⟨hx, h2⟩), unColP_shiftOut
          (outEnds_of hF hn hJ (mem_nodes_of_mem hx) h2) hJw⟩)

/-- **The cut bijection**: `{F ∈ T_SP(n) : J ∈ F} ≃ T_SP(outside) × T_SP(inside)`. -/
theorem sum_cut (hn : 2 ≤ n)
    (f : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1)) →
      Finset (Fin (wIn J + 1) × Fin (wIn J + 1)) → ℂ) :
    ∑ F ∈ (TSP n).filter (fun F => J ∈ F), f (FOut F J) (FIn F J)
      = ∑ G ∈ TSP (n - wIn J + 1), ∑ H ∈ TSP (wIn J + 1), f G H := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun F => (FOut F J, FIn F J)) (fun p => glueF J p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    have hF' := isTSP_of_mem_TSP hFT
    exact mem_product.2 ⟨FOut_mem_TSP hJd hF' hn hJF, FIn_mem_TSP hF'⟩
  · intro p hp
    obtain ⟨hG, hH⟩ := mem_product.1 hp
    exact mem_filter.2 ⟨glueF_mem_TSP hJd hG hH, mem_insert_self _ _⟩
  · intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    exact glueF_cut hJd (isTSP_of_mem_TSP hFT) hn hJF
  · intro p hp
    obtain ⟨hG, hH⟩ := mem_product.1 hp
    exact Prod.ext (FOut_glueF hJd hG) (FIn_glueF hJd hG hH)
  · intro F _
    rfl

end CutBij

section Assembly

variable (L : ℕ) [NeZero L] {n : ℕ} [NeZero n]

/-- **Linearity in one leaf**: `M_v = A B` gives `∑_z A_{a_v z}` times the tree with the leaf
relabelled `z` and weight `B`. -/
theorem treeValW_leaf_mul (F : Finset (Fin n × Fin n)) (a : Fin n → ZMod L)
    (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) (v : Fin n)
    (A B : Matrix (ZMod L) (ZMod L) ℂ) :
    treeValW L F a (Function.update M v (A * B)) E
      = ∑ z : ZMod L, A (a v) z * treeValW L F (Function.update a v z) (Function.update M v B) E := by
  simp only [treeValW, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [prod_update_eq (fun w => M w (a w) (b ⟨leafPar F w, leafPar_mem F w⟩)) _ v
    (fun w hw => by rw [Function.update_of_ne hw]), Function.update_self, Matrix.mul_apply,
    Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [prod_update_eq (fun w => M w (a w) (b ⟨leafPar F w, leafPar_mem F w⟩)) _ v
    (fun w hw => by rw [Function.update_of_ne hw, Function.update_of_ne hw]),
    Function.update_self, Function.update_self]
  ring

variable {L}
variable (hL : 3 ≤ L) {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
  {J : Fin n × Fin n} (hJ : J ∈ F)
  (m : Bool → ℂ) (t : ℝ) (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hL hF hn hJ hm

/-- **The internal edge `J`, differentiated, is a product of two smaller trees.**  With leaf
weights `Θ_{t m(σ_v) m(σ_{v+1})}` and internal weights `Θ - 1`, putting `Θ_J S Θ_J` on the edge
`J` gives `∑_{u,w} (inside polygon, root label u) S_{uw} (outside polygon, glue label w)`.
The small polygons enter only through their charges `σi`, `σo` (read off `σ`) and labels. -/
theorem treeValW_internal_cut (σ : Fin n → Bool) (a : Fin n → ZMod L)
    (σi : Fin (wIn J + 1) → Bool) (ai : ZMod L → Fin (wIn J + 1) → ZMod L)
    (σo : Fin (n - wIn J + 1) → Bool) (ao : ZMod L → Fin (n - wIn J + 1) → ZMod L)
    (hσi : ∀ i : Fin (wIn J + 1), σi i = σ (unShift J (i, i)).1)
    (hσo : ∀ i : Fin (n - wIn J + 1), σo i = σ (unColP J (i, i)).1)
    (hai0 : ∀ u, ai u (Fin.last _) = u) (hai1 : ∀ u, ∀ v : LIn J, ai u (inV J v) = a v)
    (hao0 : ∀ w, ao w (glueV J) = w) (hao1 : ∀ w, ∀ v : LOut J, ao w (outV J v) = a v) :
    treeValW L F a (fun v => thetaEdge L m t (σ v) (σ (v + 1)))
        (Function.update (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1) ⟨J, hJ⟩
          (thetaEdge L m t (σ J.1) (σ J.2) * SB L * thetaEdge L m t (σ J.1) (σ J.2)))
      = ∑ u : ZMod L, ∑ w : ZMod L,
          treeValG L m t σi (ai u) (FIn F J) * SB L u w * treeValG L m t σo (ao w) (FOut F J) := by
  have hJd := hF.1 J hJ
  have hJw := width_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  have hJn := J.2.isLt
  have hw : wIn J = J.2.val - J.1.val := rfl
  -- vertex / region bookkeeping
  have si : ∀ i : Fin (wIn J + 1), (unShift J (i, i)).1.val = i.val + J.1.val := fun i =>
    (unShift_val (i, i)).1
  have so : ∀ i : Fin (n - wIn J + 1), (unColP J (i, i)).1.val = unCol J i.val := fun i =>
    (unColP_val (i, i) hJ2).1
  have hΘT : (thetaEdge L m t (σ J.1) (σ J.2)).transpose = thetaEdge L m t (σ J.2) (σ J.1) := by
    rw [thetaEdge_comm L m t (σ J.2)]
    exact Theta_transpose L hL (hm _ _)
  have hσi' : ∀ (i : Fin (wIn J + 1)) (v : Fin n), v.val = i.val + J.1.val → σi i = σ v := by
    intro i v hv; rw [hσi i]; congr 1; exact Fin.ext (by rw [si i, hv])
  have hσo' : ∀ (i : Fin (n - wIn J + 1)) (v : Fin n), v.val = unCol J i.val → σo i = σ v := by
    intro i v hv; rw [hσo i]; congr 1; exact Fin.ext (by rw [so i, hv])
  have hone : (1 : Fin n).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hsucc : ∀ v : Fin n, v.val < n - 1 → (v + 1 : Fin n).val = v.val + 1 := by
    intro v hv; rw [Fin.val_add, hone, Nat.mod_eq_of_lt (by omega)]
  -- inside side conditions
  have hM0i : thetaEdge L m t (σi (Fin.last _)) (σi (Fin.last _ + 1))
      = (thetaEdge L m t (σ J.1) (σ J.2)).transpose := by
    rw [hΘT, Fin.last_add_one, hσi' _ J.2 (by simp only [Fin.val_last, wIn]; omega),
      hσi' 0 J.1 (by simp)]
  have hM1i : ∀ v : LIn J, thetaEdge L m t (σi (inV J v)) (σi (inV J v + 1))
      = thetaEdge L m t (σ v.1) (σ (v.1 + 1)) := by
    intro v
    have hv := v.2
    simp only [InArc, Fin.le_def, Fin.lt_def] at hv
    have h1 := inV_val v.2
    have hlt : (inV J v.1).val < wIn J := by rw [h1]; simp only [wIn]; omega
    have hvn : v.1.val < n - 1 := by omega
    rw [hσi' _ v.1 (by rw [h1]; omega), hσi' _ (v.1 + 1) (by
      rw [hsucc v.1 hvn, Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; exact hlt), h1]
      omega)]
  have hEi : ∀ d : EIn F J, thetaEdge L m t (σi (shiftIn J d.1.1).1) (σi (shiftIn J d.1.1).2) - 1
      = thetaEdge L m t (σ d.1.1.1) (σ d.1.1.2) - 1 := by
    intro d
    have hlt := (hF.1 d.1.1 d.1.2).1
    have hv := shiftIn_val d.2.1 (le_of_lt hlt)
    have hdJ := d.2.1
    simp only [ArcLe, Fin.le_def] at hdJ
    rw [hσi' _ d.1.1.1 (by rw [hv.1]; omega),
      hσi' _ d.1.1.2 (by rw [hv.2]; omega)]
  -- outside side conditions
  have hg : (glueV J).val = J.1.val := by simp only [glueV, wIn]; omega
  have hM0o : thetaEdge L m t (σo (glueV J)) (σo (glueV J + 1))
      = thetaEdge L m t (σ J.1) (σ J.2) := by
    have hg1 : (glueV J + 1).val = J.1.val + 1 := by
      rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last, hg]; simp only [wIn]; omega), hg]
    rw [hσo' _ J.1 (by rw [hg, unCol_of_le le_rfl]), hσo' _ J.2 (by
      rw [hg1, unCol_of_gt (by omega)]; simp only [wIn]; omega)]
  have hM1o : ∀ v : LOut J, thetaEdge L m t (σo (outV J v)) (σo (outV J v + 1))
      = thetaEdge L m t (σ v.1) (σ (v.1 + 1)) := by
    intro v
    have hvs : v.1.val < J.1.val ∨ J.2.val ≤ v.1.val := by
      have := v.2; simp only [InArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this; omega
    have h1 := outV_val v.1 hJ2
    rw [hσo' _ v.1 (by rw [h1, unCol_col (by omega) hJw])]
    congr 1
    by_cases hr : v.1.val = n - 1
    · have hlast : outV J v.1 = Fin.last _ := by
        refine Fin.ext ?_
        rw [h1, Fin.val_last, col_of_gt (by omega), hr]; simp only [wIn]; omega
      have hv1 : v.1 + 1 = 0 := by
        refine Fin.ext ?_
        rw [Fin.val_add, hone, hr, Nat.sub_add_cancel (by omega), Nat.mod_self]; rfl
      rw [hlast, Fin.last_add_one, hv1]
      exact hσo' 0 0 (by simp [unCol])
    · have hvn : v.1.val < n - 1 := by have := v.1.isLt; omega
      have hlt : (outV J v.1).val < n - wIn J := by
        rw [h1]; rcases hvs with h | h
        · rw [col_of_le (by omega)]; simp only [wIn]; omega
        · rw [col_of_gt (by omega)]; simp only [wIn]; omega
      refine hσo' _ _ ?_
      rw [hsucc v.1 hvn, Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; exact hlt), h1]
      rcases hvs with h | h
      · rw [col_of_le (by omega)]
        by_cases h' : v.1.val + 1 ≤ J.1.val
        · rw [unCol_of_le h']
        · have : v.1.val + 1 = J.1.val := by omega
          rw [this, unCol_of_le le_rfl]
      · rw [col_of_gt (by omega), unCol_of_gt (by simp only [wIn]; omega)]
        simp only [wIn]; omega
  have hEo : ∀ d : EOut F J, thetaEdge L m t (σo (shiftOut J d.1.1).1) (σo (shiftOut J d.1.1).2) - 1
      = thetaEdge L m t (σ d.1.1.1) (σ d.1.1.2) - 1 := by
    intro d
    have hE := outEnds_of hF hn hJ (mem_nodes_of_mem d.1.2) d.2
    have hv := shiftOut_val d.1.1 hJ2
    rw [hσo' _ d.1.1.1 (by rw [hv.1, unCol_col hE.1 hJw]),
      hσo' _ d.1.1.2 (by rw [hv.2, unCol_col hE.2.1 hJw])]
  rw [treeValW_cut L hF hn hJ a _ _ (thetaEdge L m t (σ J.1) (σ J.2)) (SB L)
    (thetaEdge L m t (σ J.1) (σ J.2))]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  rw [gval_in_eq hF hn hJ L a (fun v => thetaEdge L m t (σ v) (σ (v + 1)))
      (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1) u _ (ai u) (fun v => thetaEdge L m t (σi v) (σi (v + 1)))
      (fun d => thetaEdge L m t (σi d.1.1) (σi d.1.2) - 1) (hai0 u) (hai1 u) hM0i hM1i hEi,
    gval_out_eq hF hn hJ L a (fun v => thetaEdge L m t (σ v) (σ (v + 1)))
      (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1) w _ (ao w) (fun v => thetaEdge L m t (σo v) (σo (v + 1)))
      (fun d => thetaEdge L m t (σo d.1.1) (σo d.1.2) - 1) (hao0 w) (hao1 w) hM0o hM1o hEo]
  rfl

end Assembly

section KN

variable (L : ℕ) [NeZero L]

/-- **(3.5) on an `n`-gon given by functions**: `m_σ W^{-(n-1)} ∑_{F ∈ T_SP(n)} Γ_F`. -/
noncomputable def Kn (W : ℕ) (m : Bool → ℂ) (t : ℝ) (n : ℕ) [NeZero n] (σ : Fin n → Bool)
    (a : Fin n → ZMod L) : ℂ :=
  (∏ i, m (σ i)) * (W : ℂ)⁻¹ ^ (n - 1) * ∑ F ∈ TSP n, treeValG L m t σ a F

variable {L}

/-- Linearity in one internal edge weight. -/
theorem treeValW_edge_smul {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n)) (a : Fin n → ZMod L)
    (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) (d : ↥F)
    (c : ℂ) (X : Matrix (ZMod L) (ZMod L) ℂ) :
    treeValW L F a M (Function.update E d (c • X))
      = c * treeValW L F a M (Function.update E d X) := by
  simp only [treeValW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [prod_update_eq (fun e => E e (b ⟨e.1, mem_nodes_of_mem e.2⟩)
      (b ⟨nodePar F e, nodePar_mem F e⟩)) _ d (fun e he => by rw [Function.update_of_ne he]),
    prod_update_eq (fun e => E e (b ⟨e.1, mem_nodes_of_mem e.2⟩)
      (b ⟨nodePar F e, nodePar_mem F e⟩)) _ d (fun e he => by rw [Function.update_of_ne he]),
    Function.update_self, Function.update_self, Matrix.smul_apply, smul_eq_mul]
  ring

variable (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ) {t : ℝ}
  (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hL hm

/-- The derivative of an edge weight: `μ Θ S Θ`, written as `(μ • (Θ S)) Θ`. -/
noncomputable abbrev dTheta (m : Bool → ℂ) (t : ℝ) (s s' : Bool) : Matrix (ZMod L) (ZMod L) ℂ :=
  ((m s * m s') • (thetaEdge L m t s s' * SB L)) * thetaEdge L m t s s'

omit hL hm in
theorem dTheta_eq (s s' : Bool) :
    dTheta m t s s' = (m s * m s') • (thetaEdge L m t s s' * SB L * thetaEdge L m t s s') := by
  rw [dTheta, Matrix.smul_mul]

omit [NeZero W] in
/-- **The derivative of `Kn`**: one term per leaf and one per internal edge of every tree. -/
theorem hasDerivAt_Kn {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → ZMod L) :
    HasDerivAt (fun r => Kn L W m r n σ a)
      ((∏ i, m (σ i)) * (W : ℂ)⁻¹ ^ (n - 1) * ∑ F ∈ TSP n,
        (∑ v : Fin n, treeValW L F a (Function.update
            (fun v => thetaEdge L m t (σ v) (σ (v + 1))) v (dTheta m t (σ v) (σ (v + 1))))
            (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1)
          + ∑ d : ↥F, treeValW L F a (fun v => thetaEdge L m t (σ v) (σ (v + 1)))
            (Function.update (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1) d
              (dTheta m t (σ d.1.1) (σ d.1.2))))) t := by
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun F _ => ?_)
  refine hasDerivAt_treeValW L (fun v i j => ?_) (fun d i j => ?_)
  · exact hasDerivAt_thetaEdge' hL m _ _ (hm _ _) i j
  · have := (hasDerivAt_thetaEdge' hL m (σ d.1.1) (σ d.1.2) (hm _ _) i j).sub_const
      ((1 : Matrix (ZMod L) (ZMod L) ℂ) i j)
    simpa using this

omit hL hm [NeZero W] in
/-- **A leaf term**: differentiating the leaf `v` in every tree gives
`∑_x (μ Θ S)_{a_v x} K(a with a_v := x)`. -/
theorem leaf_term {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → ZMod L) (v : Fin n) :
    (∏ i, m (σ i)) * (W : ℂ)⁻¹ ^ (n - 1) * ∑ F ∈ TSP n,
        treeValW L F a (Function.update
            (fun v => thetaEdge L m t (σ v) (σ (v + 1))) v (dTheta m t (σ v) (σ (v + 1))))
          (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1)
      = ∑ x : ZMod L, ((m (σ v) * m (σ (v + 1))) • (thetaEdge L m t (σ v) (σ (v + 1)) * SB L))
          (a v) x * Kn L W m t n σ (Function.update a v x) := by
  have hM : Function.update (fun v => thetaEdge L m t (σ v) (σ (v + 1))) v
      (thetaEdge L m t (σ v) (σ (v + 1))) = fun v => thetaEdge L m t (σ v) (σ (v + 1)) :=
    Function.update_eq_self _ _
  simp only [dTheta, treeValW_leaf_mul, hM, Kn, treeValG, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun F _ => by ring

omit hL hm [NeZero W] in
/-- Exchanging `∑_F ∑_{J ∈ F}` for `∑_J ∑_{F ∋ J}`. -/
theorem sum_edges_swap {n : ℕ} [NeZero n] (g : (F : Finset (Fin n × Fin n)) → ↥F → ℂ) :
    ∑ F ∈ TSP n, ∑ d : ↥F, g F d
      = ∑ J ∈ diagonals n, ∑ F ∈ (TSP n).filter (fun F => J ∈ F),
          (if h : J ∈ F then g F ⟨J, h⟩ else 0) := by
  have h1 : ∀ F ∈ TSP n, ∑ d : ↥F, g F d
      = ∑ J ∈ diagonals n, (if h : J ∈ F then g F ⟨J, h⟩ else 0) := by
    intro F hF
    have e1 : ∑ d : ↥F, g F d = ∑ d : ↥F, (if h : d.1 ∈ F then g F ⟨d.1, h⟩ else 0) :=
      Finset.sum_congr rfl fun d _ => by rw [dite_eq_left d.2]
    rw [e1, Finset.sum_coe_sort F (fun J => if h : J ∈ F then g F ⟨J, h⟩ else 0)]
    refine Finset.sum_subset (mem_TSP.1 hF).1 fun J _ hJ => ?_
    rw [dite_eq_right hJ]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun F _ => by split_ifs <;> rfl

end KN

section KNInternal

variable {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ) {t : ℝ}
  (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hL hm

/-- **An internal-edge term**: differentiating the edge `J` in every tree containing it gives
`W ∑_{x,y} K(outside, glue x) S_{xy} K(inside, root y)`, the cut-and-glue term of `J`. -/
theorem internal_term {n : ℕ} [NeZero n] (hn : 2 ≤ n) {J : Fin n × Fin n}
    (hJd : IsDiag n J.1 J.2) (σ : Fin n → Bool) (a : Fin n → ZMod L)
    (σi : Fin (wIn J + 1) → Bool) (ai : ZMod L → Fin (wIn J + 1) → ZMod L)
    (σo : Fin (n - wIn J + 1) → Bool) (ao : ZMod L → Fin (n - wIn J + 1) → ZMod L)
    (hσi : ∀ i : Fin (wIn J + 1), σi i = σ (unShift J (i, i)).1)
    (hσo : ∀ i : Fin (n - wIn J + 1), σo i = σ (unColP J (i, i)).1)
    (hai0 : ∀ u, ai u (Fin.last _) = u) (hai1 : ∀ u, ∀ v : LIn J, ai u (inV J v) = a v)
    (hao0 : ∀ w, ao w (glueV J) = w) (hao1 : ∀ w, ∀ v : LOut J, ao w (outV J v) = a v)
    (hprod : (∏ i, m (σi i)) * ∏ i, m (σo i) = (∏ i, m (σ i)) * (m (σ J.1) * m (σ J.2))) :
    (∏ i, m (σ i)) * (W : ℂ)⁻¹ ^ (n - 1) * ∑ F ∈ (TSP n).filter (fun F => J ∈ F),
        (if h : J ∈ F then treeValW L F a (fun v => thetaEdge L m t (σ v) (σ (v + 1)))
          (Function.update (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1) ⟨J, h⟩
            (dTheta m t (σ J.1) (σ J.2))) else 0)
      = (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L,
          Kn L W m t (n - wIn J + 1) σo (ao x) * SB L x y * Kn L W m t (wIn J + 1) σi (ai y) := by
  have hJw := width_of_isDiag hJd
  have hJn := J.2.isLt
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  -- each tree containing `J`
  have hterm : ∀ F ∈ (TSP n).filter (fun F => J ∈ F),
      (if h : J ∈ F then treeValW L F a (fun v => thetaEdge L m t (σ v) (σ (v + 1)))
          (Function.update (fun d : ↥F => thetaEdge L m t (σ d.1.1) (σ d.1.2) - 1) ⟨J, h⟩
            (dTheta m t (σ J.1) (σ J.2))) else 0)
        = (m (σ J.1) * m (σ J.2)) * ∑ u : ZMod L, ∑ w : ZMod L,
            treeValG L m t σi (ai u) (FIn F J) * SB L u w * treeValG L m t σo (ao w) (FOut F J) := by
    intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    rw [dite_eq_left hJF, dTheta_eq, treeValW_edge_smul,
      treeValW_internal_cut hL (isTSP_of_mem_TSP hFT) hn hJF m t hm σ a σi ai σo ao hσi hσo
        hai0 hai1 hao0 hao1]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  -- the cut bijection
  have hbij := sum_cut hJd hn (fun G H => ∑ u : ZMod L, ∑ w : ZMod L,
    treeValG L m t σi (ai u) H * SB L u w * treeValG L m t σo (ao w) G)
  rw [hbij]
  -- regroup into the two `Kn`
  have hwn : wIn J ≤ n := by simp only [wIn]; omega
  have hconst : (∏ i, m (σ i)) * (W : ℂ)⁻¹ ^ (n - 1) * (m (σ J.1) * m (σ J.2))
      = (W : ℂ) * ((∏ i, m (σo i)) * (W : ℂ)⁻¹ ^ (n - wIn J + 1 - 1))
          * ((∏ i, m (σi i)) * (W : ℂ)⁻¹ ^ (wIn J + 1 - 1)) := by
    have hpow : (W : ℂ) * (W : ℂ)⁻¹ ^ (n - wIn J + 1 - 1) * (W : ℂ)⁻¹ ^ (wIn J + 1 - 1)
        = (W : ℂ)⁻¹ ^ (n - 1) := by
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel, mul_assoc, ← pow_add, Nat.sub_add_cancel hwn]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, Nat.add_sub_cancel, ← mul_assoc, mul_comm (W : ℂ), mul_assoc,
        mul_inv_cancel₀ hW, mul_one]
    calc (∏ i, m (σ i)) * (W : ℂ)⁻¹ ^ (n - 1) * (m (σ J.1) * m (σ J.2))
        = ((∏ i, m (σi i)) * ∏ i, m (σo i)) * (W : ℂ)⁻¹ ^ (n - 1) := by rw [hprod]; ring
      _ = _ := by rw [← hpow]; ring
  calc (∏ i, m (σ i)) * (W : ℂ)⁻¹ ^ (n - 1) * ((m (σ J.1) * m (σ J.2)) *
        ∑ G ∈ TSP (n - wIn J + 1), ∑ H ∈ TSP (wIn J + 1), ∑ u : ZMod L, ∑ w : ZMod L,
          treeValG L m t σi (ai u) H * SB L u w * treeValG L m t σo (ao w) G)
      = ∑ x : ZMod L, ∑ y : ZMod L, ∑ G ∈ TSP (n - wIn J + 1), ∑ H ∈ TSP (wIn J + 1),
          ((∏ i, m (σ i)) * (W : ℂ)⁻¹ ^ (n - 1) * (m (σ J.1) * m (σ J.2))) *
            (treeValG L m t σo (ao x) G * SB L x y * treeValG L m t σi (ai y) H) := by
        rw [← mul_assoc, Finset.mul_sum]
        simp only [Finset.mul_sum]
        rw [sum_perm4' (TSP (n - wIn J + 1)) (TSP (wIn J + 1)) (fun G H u w =>
          (∏ i, m (σ i)) * (W : ℂ)⁻¹ ^ (n - 1) * (m (σ J.1) * m (σ J.2)) *
            (treeValG L m t σi (ai u) H * SB L u w * treeValG L m t σo (ao w) G))]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun H _ => by
            rw [SB_apply_comm L y x]; ring
    _ = (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L,
          Kn L W m t (n - wIn J + 1) σo (ao x) * SB L x y * Kn L W m t (wIn J + 1) σi (ai y) := by
        rw [hconst]
        simp only [Kn, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm (s := TSP (wIn J + 1))]
        exact Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun H _ => by ring

end KNInternal


section Lists

variable (L : ℕ) [NeZero L]

/-- **The tree representation on loop indices**: `m(σ)` for `n = 1`, Example 2.15 for `n = 2`,
and `m_σ W^{-(n-1)} ∑_{Γ ∈ T_SP(n)} Γ` for `n ≥ 3`. -/
noncomputable def Kgen (W : ℕ) (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (ZMod L)) : ℂ :=
  if I.length = 1 then m (I.σ.getD 0 false)
  else if I.length = 2 then
    kTwo L W m t (I.σ.getD 0 false) (I.σ.getD 1 false) (I.a.getD 0 0) (I.a.getD 1 0)
  else if h : 3 ≤ I.length then
    haveI : NeZero I.length := ⟨by omega⟩
    Kn L W m t I.length (fun i => I.σ.getD i false) (fun i => I.a.getD i 0)
  else 0

variable {L}

/-- `Kgen` on a loop of known length `n ≥ 3` is `Kn`. -/
theorem Kgen_eq (W : ℕ) (m : Bool → ℂ) (t : ℝ) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (I : LoopIdx (ZMod L)) (h : I.length = n) :
    Kgen L W m t I = Kn L W m t n (fun i => I.σ.getD i false) (fun i => I.a.getD i 0) := by
  subst h
  have h1 : I.length ≠ 1 := by omega
  have h2 : I.length ≠ 2 := by omega
  simp only [Kgen, h1, h2, ite_false, dite_eq_left hn]

theorem Kgen_two (W : ℕ) (m : Bool → ℂ) (t : ℝ) (s₁ s₂ : Bool) (x y : ZMod L) :
    Kgen L W m t ⟨[s₁, s₂], [x, y]⟩ = kTwo L W m t s₁ s₂ x y := by
  simp [Kgen, LoopIdx.length]

theorem Kgen_one (W : ℕ) (m : Bool → ℂ) (t : ℝ) (s : Bool) (x : ZMod L) :
    Kgen L W m t ⟨[s], [x]⟩ = m s := by
  simp [Kgen, LoopIdx.length]

/-! ### Splitting the pairs `(k, l)` of (2.48) -/

/-- The pair `(k, l)` of the leaf edge at `v`: `(v+1, v+2)`, or `(1, n)` for the root. -/
def leafPair {n : ℕ} (v : Fin n) : ℕ × ℕ := if v.val + 1 < n then (v.val + 1, v.val + 2) else (1, n)

theorem sum_pairs {n : ℕ} [NeZero n] (hn : 3 ≤ n) (f : ℕ → ℕ → ℂ) :
    ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, f k l
      = ∑ v : Fin n, f (leafPair v).1 (leafPair v).2
        + ∑ J ∈ diagonals n, f (J.1.val + 1) (J.2.val + 1) := by
  -- the pairs as a finset of `ℕ × ℕ`
  set P : Finset (ℕ × ℕ) := (Finset.Icc 1 n).sigma (fun k => Finset.Ioc k n) |>.map
    ⟨fun p => (p.1, p.2), fun p q h => by
      simp only [Prod.mk.injEq] at h; exact Sigma.ext h.1 (heq_of_eq h.2)⟩ with hP
  have hLHS : ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, f k l = ∑ p ∈ P, f p.1 p.2 := by
    rw [hP, Finset.sum_map, Finset.sum_sigma]
    rfl
  have hmem : ∀ p : ℕ × ℕ, p ∈ P ↔ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ n := by
    intro p
    simp only [hP, Finset.mem_map, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨k, l⟩, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩; exact ⟨h1, h3, h4⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨p.1, p.2⟩, ⟨⟨h1, le_of_lt (lt_of_lt_of_le h2 h3)⟩, h2, h3⟩, rfl⟩
  have hinjL : Set.InjOn (fun v : Fin n => leafPair v) (Finset.univ : Finset (Fin n)) := by
    intro v _ w _ h
    simp only [leafPair] at h
    refine Fin.ext ?_
    have := v.isLt; have := w.isLt
    split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hinjD : Set.InjOn (fun J : Fin n × Fin n => (J.1.val + 1, J.2.val + 1))
      (diagonals n : Set (Fin n × Fin n)) := by
    intro J _ K _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have hsplit : P = (Finset.univ.image fun v : Fin n => leafPair v) ∪
      ((diagonals n).image fun J : Fin n × Fin n => (J.1.val + 1, J.2.val + 1)) := by
    ext p
    rw [hmem, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hl : p.2 = p.1 + 1
      · refine Or.inl ⟨⟨p.1 - 1, by omega⟩, Finset.mem_univ _, ?_⟩
        simp only [leafPair]
        split_ifs with hc <;> ext <;> simp <;> omega
      by_cases hr : p.1 = 1 ∧ p.2 = n
      · refine Or.inl ⟨⟨n - 1, by omega⟩, Finset.mem_univ _, ?_⟩
        simp only [leafPair]
        split_ifs with hc <;> ext <;> simp <;> omega
      · refine Or.inr ⟨(⟨p.1 - 1, by omega⟩, ⟨p.2 - 1, by omega⟩), ?_, ?_⟩
        · rw [mem_diagonals_iff]
          refine ⟨by rw [Fin.lt_def]; simp; omega, by simp; omega, by simp; omega⟩
        · ext <;> simp <;> omega
    · rintro (⟨v, -, rfl⟩ | ⟨J, hJ, rfl⟩)
      · simp only [leafPair]; have := v.isLt
        split_ifs <;> simp <;> omega
      · obtain ⟨h1, h2, h3⟩ := mem_diagonals_iff.1 hJ
        rw [Fin.lt_def] at h1
        have := J.2.isLt
        simp; omega
  have hdisj : Disjoint (Finset.univ.image fun v : Fin n => leafPair v)
      ((diagonals n).image fun J : Fin n × Fin n => (J.1.val + 1, J.2.val + 1)) := by
    rw [Finset.disjoint_left]
    rintro p hp hq
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨J, hJ, hJv⟩ := Finset.mem_image.1 hq
    obtain ⟨h1, h2, h3⟩ := mem_diagonals_iff.1 hJ
    rw [Fin.lt_def] at h1
    have := J.2.isLt
    simp only [leafPair] at hJv
    split_ifs at hJv <;> simp only [Prod.mk.injEq] at hJv <;> omega
  rw [hLHS, hsplit, Finset.sum_union hdisj, Finset.sum_image hinjL, Finset.sum_image hinjD]

/-! ### Reading entries of the cut-and-glue lists -/

section ListGetD

variable {α : Type*} {l l' : List α} {d : α}

theorem getD_take_append_of_lt {k i : ℕ} (hi : i < k) (hk : k ≤ l.length) :
    (l.take k ++ l').getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take]
  simp [hi]

theorem getD_take_append_of_ge {k i : ℕ} (hi : k ≤ i) (hk : k ≤ l.length) :
    (l.take k ++ l').getD i d = l'.getD (i - k) d := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega), List.length_take, min_eq_left hk]

theorem getD_drop' {k i : ℕ} : (l.drop k).getD i d = l.getD (k + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_drop_take {k j i : ℕ} (hi : i < j) :
    ((l.drop k).take j).getD i d = l.getD (k + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hi]

theorem getD_cons_succ' {x : α} {i : ℕ} : (x :: l).getD (i + 1) d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD]

end ListGetD

variable {L : ℕ} [NeZero L]

theorem Kgen_of_length_two (W : ℕ) (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (ZMod L))
    (h : I.length = 2) :
    Kgen L W m t I = kTwo L W m t (I.σ.getD 0 false) (I.σ.getD 1 false) (I.a.getD 0 0)
      (I.a.getD 1 0) := by
  simp [Kgen, h]

variable (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ) {t : ℝ}
  (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)

/-- **A leaf pair** `(v+1, v+2)` of (2.48) is the leaf term of `v`. -/
theorem leaf_pair_term {n : ℕ} [NeZero n] (hn : 3 ≤ n) (I : LoopIdx (ZMod L)) (hI : I.WF)
    (hlen : I.length = n) (v : Fin n) (hv : v.val + 1 < n) :
    (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L,
        Kgen L W m t (I.cutGlueL (v.val + 1) (v.val + 2) x) * SB L x y *
          Kgen L W m t (I.cutGlueR (v.val + 1) (v.val + 2) y)
      = ∑ x : ZMod L, ((m (I.σ.getD v false) * m (I.σ.getD (v + 1 : Fin n) false)) •
          (thetaEdge L m t (I.σ.getD v false) (I.σ.getD (v + 1 : Fin n) false) * SB L))
          (I.a.getD v 0) x *
          Kn L W m t n (fun i => I.σ.getD i false)
            (Function.update (fun i : Fin n => I.a.getD i 0) v x) := by
  have hσl : I.σ.length = n := by rw [hI]; exact hlen
  have hal : I.a.length = n := hlen
  have hv1 : ((v + 1 : Fin n) : ℕ) = v.val + 1 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt hv]
  -- the left chain: the same polygon with `a_v := x`
  have hL' : ∀ x, Kgen L W m t (I.cutGlueL (v.val + 1) (v.val + 2) x)
      = Kn L W m t n (fun i => I.σ.getD i false)
          (Function.update (fun i : Fin n => I.a.getD i 0) v x) := by
    intro x
    have hlenL : (I.cutGlueL (v.val + 1) (v.val + 2) x).length = n := by
      rw [LoopIdx.length_cutGlueL I x (by omega) (by omega) (by omega)]; omega
    rw [Kgen_eq W m t hn _ hlenL]
    congr 1
    · funext i
      simp only [LoopIdx.cutGlueL, show v.val + 2 - 1 = v.val + 1 by omega, List.take_append_drop]
    · funext i
      simp only [LoopIdx.cutGlueL, show v.val + 2 - 1 = v.val + 1 by omega,
        show v.val + 1 - 1 = v.val by omega]
      by_cases hiv : i = v
      · subst hiv
        rw [Function.update_self, getD_take_append_of_ge le_rfl (by omega), Nat.sub_self]
        rfl
      · rw [Function.update_of_ne hiv]
        have hiv' : i.val ≠ v.val := fun h => hiv (Fin.ext h)
        rcases Nat.lt_or_gt_of_ne hiv' with h | h
        · rw [getD_take_append_of_lt h (by omega)]
        · rw [getD_take_append_of_ge (by omega) (by omega),
            show i.val - v.val = (i.val - v.val - 1) + 1 by omega, getD_cons_succ', getD_drop']
          congr 1; omega
  -- the right chain: the `2`-loop `(σ_v, σ_{v+1}), (a_v, y)`
  have hR' : ∀ y, Kgen L W m t (I.cutGlueR (v.val + 1) (v.val + 2) y)
      = kTwo L W m t (I.σ.getD v false) (I.σ.getD (v + 1 : Fin n) false) (I.a.getD v 0) y := by
    intro y
    have hlenR : (I.cutGlueR (v.val + 1) (v.val + 2) y).length = 2 := by
      rw [LoopIdx.length_cutGlueR I y (by omega) (by omega) (by omega)]; omega
    rw [Kgen_of_length_two W m t _ hlenR]
    simp only [LoopIdx.cutGlueR, show v.val + 1 - 1 = v.val by omega,
      show v.val + 2 - (v.val + 1) = 1 by omega]
    have e1 : (List.take 1 (List.drop v.val I.a) ++ [y]).getD 0 0 = I.a.getD v 0 := by
      rw [getD_take_append_of_lt (by omega) (by simp; omega), getD_drop', Nat.add_zero]
    have e2 : (List.take 1 (List.drop v.val I.a) ++ [y]).getD 1 0 = y := by
      rw [getD_take_append_of_ge (by omega) (by simp; omega)]
      simp
    rw [getD_drop_take (by omega), getD_drop_take (by omega), hv1, e1, e2]
    simp
  simp_rw [hL', hR']
  exact rhs_kTwo_left W m t _ _ _ _

include hL hm in
/-- **The root pair** `(1, n)` of (2.48) is the leaf term of the root `v = n - 1` (the left
chain is the `2`-loop `(σ₀, σ_{n-1})`, the right chain the polygon with `a_{n-1} := y`). -/
theorem root_pair_term {n : ℕ} [NeZero n] (hn : 3 ≤ n) (I : LoopIdx (ZMod L)) (hI : I.WF)
    (hlen : I.length = n) (v : Fin n) (hv : v.val = n - 1) :
    (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L,
        Kgen L W m t (I.cutGlueL 1 n x) * SB L x y * Kgen L W m t (I.cutGlueR 1 n y)
      = ∑ x : ZMod L, ((m (I.σ.getD v false) * m (I.σ.getD (v + 1 : Fin n) false)) •
          (thetaEdge L m t (I.σ.getD v false) (I.σ.getD (v + 1 : Fin n) false) * SB L))
          (I.a.getD v 0) x *
          Kn L W m t n (fun i => I.σ.getD i false)
            (Function.update (fun i : Fin n => I.a.getD i 0) v x) := by
  have hσl : I.σ.length = n := by rw [hI]; exact hlen
  have hal : I.a.length = n := hlen
  have hv1 : ((v + 1 : Fin n) : ℕ) = 0 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n), hv,
      Nat.sub_add_cancel (by omega), Nat.mod_self]
  -- the left chain: the `2`-loop `(σ₀, σ_{n-1}), (x, a_{n-1})`
  have hL' : ∀ x, Kgen L W m t (I.cutGlueL 1 n x)
      = kTwo L W m t (I.σ.getD 0 false) (I.σ.getD v false) x (I.a.getD v 0) := by
    intro x
    have hlenL : (I.cutGlueL 1 n x).length = 2 := by
      rw [LoopIdx.length_cutGlueL I x le_rfl (by omega) (by omega)]; omega
    rw [Kgen_of_length_two W m t _ hlenL]
    simp only [LoopIdx.cutGlueL, Nat.sub_self, List.take_zero, List.nil_append]
    have e1 : (List.take 1 I.σ ++ List.drop (n - 1) I.σ).getD 0 false = I.σ.getD 0 false :=
      getD_take_append_of_lt (by omega) (by omega)
    have e2 : (List.take 1 I.σ ++ List.drop (n - 1) I.σ).getD 1 false = I.σ.getD v false := by
      rw [getD_take_append_of_ge le_rfl (by omega), Nat.sub_self, getD_drop', hv, Nat.add_zero]
    have e3 : (x :: List.drop (n - 1) I.a).getD 1 0 = I.a.getD v 0 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, getD_cons_succ', getD_drop', hv, Nat.add_zero]
    rw [e1, e2, e3]
    rfl
  -- the right chain: the polygon with `a_{n-1} := y`
  have hR' : ∀ y, Kgen L W m t (I.cutGlueR 1 n y)
      = Kn L W m t n (fun i => I.σ.getD i false)
          (Function.update (fun i : Fin n => I.a.getD i 0) v y) := by
    intro y
    have hlenR : (I.cutGlueR 1 n y).length = n := by
      rw [LoopIdx.length_cutGlueR I y le_rfl (by omega) (by omega)]; omega
    rw [Kgen_eq W m t hn _ hlenR]
    congr 1
    · funext i
      simp only [LoopIdx.cutGlueR, Nat.sub_self, List.drop_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
        ← List.getD_eq_getElem?_getD]
    · funext i
      simp only [LoopIdx.cutGlueR, Nat.sub_self, List.drop_zero, show n - 1 + 1 = n by omega]
      by_cases hiv : i = v
      · subst hiv
        rw [Function.update_self, getD_take_append_of_ge (by omega) (by omega), hv, Nat.sub_self]
        rfl
      · rw [Function.update_of_ne hiv]
        have hi : i.val < n - 1 := by
          have := i.isLt; have : i.val ≠ v.val := fun h => hiv (Fin.ext h); omega
        rw [getD_take_append_of_lt hi (by omega)]
  simp_rw [hL', hR']
  rw [rhs_kTwo_right W m t hL _ _ (hm _ _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h0 : (v + 1 : Fin n) = 0 := Fin.ext (by rw [hv1]; rfl)
  rw [h0, mul_comm (m (I.σ.getD 0 false))]
  rfl

omit [NeZero L] in
/-- The charges of the two chains: the inside chain has `σ_p, …, σ_q`, the outside chain
`σ_0, …, σ_p, σ_q, …, σ_{n-1}`, so together they have every charge once and `σ_p, σ_q` twice. -/
theorem prod_chains (g : ℕ → ℂ) {n p q : ℕ} (hpq : p + 2 ≤ q) (hq : q < n) :
    (∏ i ∈ Finset.range (q - p + 1), g (p + i)) *
        ∏ i ∈ Finset.range (n - (q - p) + 1), g (if i ≤ p then i else i + (q - p - 1))
      = (∏ i ∈ Finset.range n, g i) * (g p * g q) := by
  have h1 : ∏ i ∈ Finset.range (q - p + 1), g (p + i) = ∏ i ∈ Finset.Ico p (q + 1), g i := by
    rw [Finset.prod_Ico_eq_prod_range, show q + 1 - p = q - p + 1 by omega]
  have h2 : ∏ i ∈ Finset.range (n - (q - p) + 1), g (if i ≤ p then i else i + (q - p - 1))
      = (∏ i ∈ Finset.range (p + 1), g i) * ∏ i ∈ Finset.Ico q n, g i := by
    rw [← Finset.prod_range_mul_prod_Ico _ (show p + 1 ≤ n - (q - p) + 1 by omega)]
    have e1 : ∀ i ∈ Finset.range (p + 1), g (if i ≤ p then i else i + (q - p - 1)) = g i := by
      intro i hi; rw [Finset.mem_range] at hi; rw [ite_eq_left (by omega)]
    have e2 : ∀ i ∈ Finset.Ico (p + 1) (n - (q - p) + 1),
        g (if i ≤ p then i else i + (q - p - 1)) = g (i + (q - p - 1)) := by
      intro i hi; rw [Finset.mem_Ico] at hi; rw [ite_eq_right (by omega)]
    rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2,
      Finset.prod_Ico_add' g (p + 1) (n - (q - p) + 1) (q - p - 1),
      show p + 1 + (q - p - 1) = q by omega, show n - (q - p) + 1 + (q - p - 1) = n by omega]
  rw [h1, h2]
  -- split everything at `p`, `p + 1`, `q`, `q + 1`
  rw [← Finset.prod_range_mul_prod_Ico g (show p + 1 ≤ n by omega),
    Finset.prod_eq_prod_Ico_succ_bot (show p < q + 1 by omega),
    ← Finset.prod_Ico_consecutive g (show p + 1 ≤ q + 1 by omega) (show q + 1 ≤ n by omega),
    Finset.prod_eq_prod_Ico_succ_bot (show q < n by omega)]
  rw [← Finset.prod_Ico_consecutive g (show p + 1 ≤ q by omega) (show q ≤ q + 1 by omega)]
  simp only [Nat.Ico_succ_singleton, Finset.prod_singleton]
  ring

include hL hm in
/-- **A diagonal pair** `(J.1+1, J.2+1)` of (2.48) is the internal-edge term of `J`. -/
theorem diag_pair_term {n : ℕ} [NeZero n] (hn : 3 ≤ n) (I : LoopIdx (ZMod L)) (hI : I.WF)
    (hlen : I.length = n) {J : Fin n × Fin n} (hJd : IsDiag n J.1 J.2) :
    (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L,
        Kgen L W m t (I.cutGlueL (J.1.val + 1) (J.2.val + 1) x) * SB L x y *
          Kgen L W m t (I.cutGlueR (J.1.val + 1) (J.2.val + 1) y)
      = (∏ i, m (I.σ.getD (i : Fin n) false)) * (W : ℂ)⁻¹ ^ (n - 1) *
          ∑ F ∈ (TSP n).filter (fun F => J ∈ F),
            (if h : J ∈ F then treeValW L F (fun i : Fin n => I.a.getD i 0)
              (fun v => thetaEdge L m t (I.σ.getD (v : Fin n) false) (I.σ.getD (v + 1 : Fin n) false))
              (Function.update (fun d : ↥F => thetaEdge L m t (I.σ.getD d.1.1 false)
                (I.σ.getD d.1.2 false) - 1) ⟨J, h⟩
                (dTheta m t (I.σ.getD J.1 false) (I.σ.getD J.2 false))) else 0) := by
  have hσl : I.σ.length = n := by rw [hI]; exact hlen
  have hal : I.a.length = n := hlen
  have hJw := width_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  have hJn := J.2.isLt
  have hw : wIn J = J.2.val - J.1.val := rfl
  have hwn : wIn J + 2 ≤ n := by
    obtain ⟨-, -, h3⟩ := hJd
    simp only [wIn]; by_contra h; apply h3; omega
  -- the chains
  let σi : Fin (wIn J + 1) → Bool := fun i => ((I.σ.drop J.1.val).take (wIn J + 1)).getD i false
  let ai : ZMod L → Fin (wIn J + 1) → ZMod L := fun y i =>
    ((I.a.drop J.1.val).take (wIn J) ++ [y]).getD i 0
  let σo : Fin (n - wIn J + 1) → Bool := fun i =>
    (I.σ.take (J.1.val + 1) ++ I.σ.drop J.2.val).getD i false
  let ao : ZMod L → Fin (n - wIn J + 1) → ZMod L := fun x i =>
    (I.a.take J.1.val ++ x :: I.a.drop J.2.val).getD i 0
  have hKR : ∀ y, Kgen L W m t (I.cutGlueR (J.1.val + 1) (J.2.val + 1) y)
      = Kn L W m t (wIn J + 1) σi (ai y) := by
    intro y
    have hlenR : (I.cutGlueR (J.1.val + 1) (J.2.val + 1) y).length = wIn J + 1 := by
      rw [LoopIdx.length_cutGlueR I y (by omega) (by omega) (by omega)]; simp only [wIn]; omega
    rw [Kgen_eq W m t (by omega) _ hlenR]
    simp only [LoopIdx.cutGlueR, show J.1.val + 1 - 1 = J.1.val by omega,
      show J.2.val + 1 - (J.1.val + 1) = wIn J by simp only [wIn]; omega]
    rfl
  have hKL : ∀ x, Kgen L W m t (I.cutGlueL (J.1.val + 1) (J.2.val + 1) x)
      = Kn L W m t (n - wIn J + 1) σo (ao x) := by
    intro x
    have hlenL : (I.cutGlueL (J.1.val + 1) (J.2.val + 1) x).length = n - wIn J + 1 := by
      rw [LoopIdx.length_cutGlueL I x (by omega) (by omega) (by omega)]; simp only [wIn]; omega
    rw [Kgen_eq W m t (by omega) _ hlenL]
    simp only [LoopIdx.cutGlueL, show J.1.val + 1 - 1 = J.1.val by omega,
      show J.2.val + 1 - 1 = J.2.val by omega]
    rfl
  -- the hypotheses of `internal_term`
  have hσi : ∀ i : Fin (wIn J + 1), σi i = I.σ.getD ((unShift J (i, i)).1 : Fin n) false := by
    intro i
    simp only [σi]
    rw [getD_drop_take i.isLt, (unShift_val (i, i)).1, add_comm]
  have hσo : ∀ i : Fin (n - wIn J + 1), σo i = I.σ.getD ((unColP J (i, i)).1 : Fin n) false := by
    intro i
    simp only [σo]
    rw [(unColP_val (i, i) hJ2).1]
    dsimp only
    have hi := i.isLt
    by_cases h : i.val ≤ J.1.val
    · rw [getD_take_append_of_lt (by omega) (by omega), unCol_of_le h]
    · rw [getD_take_append_of_ge (by omega) (by omega), getD_drop', unCol_of_gt (by omega)]
      congr 1; simp only [wIn]; omega
  have hai0 : ∀ u, ai u (Fin.last _) = u := by
    intro u
    simp only [ai, Fin.val_last]
    rw [getD_take_append_of_ge le_rfl (by simp; omega), Nat.sub_self]
    rfl
  have hai1 : ∀ u, ∀ v : LIn J, ai u (inV J v) = I.a.getD (v.1 : Fin n) 0 := by
    intro u v
    have hv := v.2
    simp only [InArc, Fin.le_def, Fin.lt_def] at hv
    have h1 := inV_val v.2
    simp only [ai]
    rw [h1, getD_take_append_of_lt (by simp only [wIn]; omega) (by simp; omega), getD_drop']
    congr 1; omega
  have hg : (glueV J).val = J.1.val := by simp only [glueV, wIn]; omega
  have hao0 : ∀ x, ao x (glueV J) = x := by
    intro x
    simp only [ao]
    rw [hg, getD_take_append_of_ge le_rfl (by omega), Nat.sub_self]
    rfl
  have hao1 : ∀ x, ∀ v : LOut J, ao x (outV J v) = I.a.getD (v.1 : Fin n) 0 := by
    intro x v
    have hvs : v.1.val < J.1.val ∨ J.2.val ≤ v.1.val := by
      have := v.2; simp only [InArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this; omega
    simp only [ao]
    rw [outV_val v.1 hJ2]
    rcases hvs with h | h
    · rw [col_of_le (by omega), getD_take_append_of_lt h (by omega)]
    · rw [col_of_gt (by omega), getD_take_append_of_ge (by simp only [wIn]; omega) (by omega),
        show v.1.val - (wIn J - 1) - J.1.val = (v.1.val - J.2.val) + 1 by simp only [wIn]; omega,
        getD_cons_succ', getD_drop']
      congr 1; omega
  have hprod : (∏ i, m (σi i)) * ∏ i, m (σo i)
      = (∏ i, m (I.σ.getD (i : Fin n) false)) * (m (I.σ.getD J.1 false) * m (I.σ.getD J.2 false)) := by
    set g : ℕ → ℂ := fun j => m (I.σ.getD j false) with hgdef
    have e1 : ∏ i, m (σi i) = ∏ i ∈ Finset.range (J.2.val - J.1.val + 1), g (J.1.val + i) := by
      rw [← Fin.prod_univ_eq_prod_range (fun j => g (J.1.val + j))]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [σi, g]; rw [getD_drop_take i.isLt]
    have e2 : ∏ i, m (σo i) = ∏ i ∈ Finset.range (n - (J.2.val - J.1.val) + 1),
        g (if i ≤ J.1.val then i else i + (J.2.val - J.1.val - 1)) := by
      rw [← Fin.prod_univ_eq_prod_range
        (fun j => g (if j ≤ J.1.val then j else j + (J.2.val - J.1.val - 1)))]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hσo i, (unColP_val (i, i) hJ2).1]
      simp only [g, unCol, wIn]
    have e3 : ∏ i, m (I.σ.getD (i : Fin n) false) = ∏ i ∈ Finset.range n, g i :=
      Fin.prod_univ_eq_prod_range g n
    rw [e1, e2, e3, prod_chains g hJw hJn]
  rw [internal_term hL W m hm (by omega) hJd _ _ σi ai σo ao hσi hσo hai0 hai1 hao0 hao1 hprod]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hKL, hKR]

include hL hm in
/-- **Lemma 3.4, the ODE**: for every loop of length `n ≥ 3` the tree representation `Kgen`
satisfies the primitive equation (2.48). -/
theorem hasDerivAt_Kgen (I : LoopIdx (ZMod L)) (hI : I.WF) (h3 : 3 ≤ I.length) :
    HasDerivAt (fun r => Kgen L W m r I) (primRhs L W (Kgen L W m t) I) t := by
  set n := I.length with hn
  have : NeZero n := ⟨by omega⟩
  set σF : Fin n → Bool := fun i => I.σ.getD i false with hσF
  set aF : Fin n → ZMod L := fun i => I.a.getD i 0 with haF
  have hfun : (fun r => Kgen L W m r I) = fun r => Kn L W m r n σF aF :=
    funext fun r => Kgen_eq W m r h3 I rfl
  rw [hfun]
  refine (hasDerivAt_Kn hL W m hm σF aF).congr_deriv ?_
  -- the derivative: leaf terms and edge terms
  rw [Finset.sum_add_distrib, mul_add, Finset.sum_comm, Finset.mul_sum,
    sum_edges_swap (fun F d => treeValW L F aF (fun v => thetaEdge L m t (σF v) (σF (v + 1)))
      (Function.update (fun d : ↥F => thetaEdge L m t (σF d.1.1) (σF d.1.2) - 1) d
        (dTheta m t (σF d.1.1) (σF d.1.2)))), Finset.mul_sum]
  -- (2.48): leaf pairs, the root pair and the diagonals
  rw [primRhs, ← hn, sum_pairs h3 (fun k l => ∑ x : ZMod L, ∑ y : ZMod L,
      Kgen L W m t (I.cutGlueL k l x) * SB L x y * Kgen L W m t (I.cutGlueR k l y)),
    mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [leaf_term W m σF aF v]
    simp only [leafPair]
    split_ifs with hv
    · exact (leaf_pair_term W m (t := t) h3 I hI rfl v hv).symm
    · exact (root_pair_term hL W m hm h3 I hI rfl v (by have := v.isLt; omega)).symm
  · refine Finset.sum_congr rfl fun J hJ => ?_
    exact (diag_pair_term hL W m hm h3 I hI rfl (mem_diagonals_iff.1 hJ)).symm

end Lists

section Final

variable {L : ℕ} [NeZero L]

theorem prod_getD_eq {α : Type*} (l : List α) (f : α → ℂ) (d : α) {n : ℕ} (h : l.length = n) :
    ∏ i : Fin n, f (l.getD i d) = (l.map f).prod := by
  subst h
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem allEq_iff {α : Type*} (l : List α) (d : α) {n : ℕ} (h : l.length = n) (hn : 0 < n) :
    (∀ x ∈ l, ∀ y ∈ l, x = y) ↔ ∀ i : Fin n, l.getD i d = l.getD 0 d := by
  subst h
  constructor
  · intro H i
    rw [List.getD_eq_getElem _ _ i.isLt, List.getD_eq_getElem _ _ hn]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · intro H x hx y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
    have h1 := H ⟨i, hi⟩
    have h2 := H ⟨j, hj⟩
    rw [List.getD_eq_getElem _ _ hi] at h1
    rw [List.getD_eq_getElem _ _ hj] at h2
    rw [h1, h2]

/-- The star with identity matrices: `∑_b ∏_v δ_{a_v b} = 1(all a_v equal)`. -/
theorem star_one {n : ℕ} [NeZero n] (a : Fin n → ZMod L) :
    ∑ b : ZMod L, ∏ v : Fin n, (1 : Matrix (ZMod L) (ZMod L) ℂ) (a v) b
      = if ∀ v, a v = a 0 then 1 else 0 := by
  simp only [Matrix.one_apply, Finset.prod_boole, Finset.mem_univ, true_imp_iff]
  rw [Finset.sum_eq_single (a 0)]
  · intro b _ hb
    exact ite_eq_right (fun h => hb (h 0).symm)
  · intro h; exact absurd (Finset.mem_univ _) h

variable (W : ℕ) [NeZero W] (m : Bool → ℂ)

theorem thetaEdge_zero (s s' : Bool) : thetaEdge L m 0 s s' = 1 := by
  simp [thetaEdge, Theta_zero]

omit [NeZero W] in
/-- **The initial value** of the tree representation: at `t = 0` all internal edges vanish,
only the star survives, and it is `1(a₁ = ⋯ = aₙ)`. -/
theorem Kn_zero {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → ZMod L) :
    Kn L W m 0 n σ a = (∏ i, m (σ i)) * (W : ℂ)⁻¹ ^ (n - 1) *
      (if ∀ v, a v = a 0 then 1 else 0) := by
  rw [Kn]
  congr 1
  rw [Finset.sum_eq_single ∅]
  · rw [treeValG, treeValW_empty]
    simp only [thetaEdge_zero]
    exact star_one a
  · intro F _ hF
    obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.2 hF
    rw [treeValG, treeValW]
    refine Finset.sum_eq_zero fun b _ => ?_
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ (⟨d, hd⟩ : ↥F)) ?_)
    simp [thetaEdge_zero]
  · intro h; exact absurd (empty_mem_TSP n) h

omit [NeZero W] in
theorem Kgen_zero (I : LoopIdx (ZMod L)) (hI : I.WF) (h2 : 2 ≤ I.length) :
    Kgen L W m 0 I = primInit L W m I := by
  rcases Nat.lt_or_ge I.length 3 with h | h
  · -- `n = 2`
    have hlen : I.length = 2 := by omega
    obtain ⟨σ, a⟩ := I
    have ha : a.length = 2 := hlen
    have hσ : σ.length = 2 := hI.trans ha
    obtain ⟨x₁, x₂, rfl⟩ := List.length_eq_two.1 ha
    obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.1 hσ
    rw [Kgen_two]
    exact kTwo_zero L W m s₁ s₂ x₁ x₂
  · -- `n ≥ 3`
    have : NeZero I.length := ⟨by omega⟩
    have hσl : I.σ.length = I.length := hI
    have hall : (∀ v : Fin I.length, I.a.getD v 0 = I.a.getD ((0 : Fin I.length) : ℕ) 0)
        ↔ ∀ x ∈ I.a, ∀ y ∈ I.a, x = y := by
      rw [Fin.val_zero]
      exact (allEq_iff I.a 0 (n := I.length) rfl (by omega)).symm
    rw [Kgen_eq W m 0 h I rfl, Kn_zero, primInit, prod_getD_eq I.σ m false hσl]
    simp only [hall]
    ring

variable (hL : 3 ≤ L) {t : ℝ} (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hL hm

/-- `n = 2`: the tree representation is Example 2.15. -/
theorem hasDerivAt_Kgen_two (I : LoopIdx (ZMod L)) (hI : I.WF) (h2 : I.length = 2) :
    HasDerivAt (fun r => Kgen L W m r I) (primRhs L W (Kgen L W m t) I) t := by
  obtain ⟨σ, a⟩ := I
  have ha : a.length = 2 := h2
  have hσ : σ.length = 2 := hI.trans ha
  obtain ⟨x₁, x₂, rfl⟩ := List.length_eq_two.1 ha
  obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.1 hσ
  have hfun : (fun r => Kgen L W m r ⟨[s₁, s₂], [x₁, x₂]⟩)
      = fun r => kTwo L W m r s₁ s₂ x₁ x₂ := funext fun r => Kgen_two W m r _ _ _ _
  rw [hfun, primRhs_two]
  simp only [Kgen_two]
  exact hasDerivAt_kTwo L hL W m s₁ s₂ (hm _ _) x₁ x₂

/-- **(2.48) for the tree representation, every `n ≥ 2`.** -/
theorem hasDerivAt_Kgen_all (I : LoopIdx (ZMod L)) (hI : I.WF) (h2 : 2 ≤ I.length) :
    HasDerivAt (fun r => Kgen L W m r I) (primRhs L W (Kgen L W m t) I) t := by
  rcases Nat.lt_or_ge I.length 3 with h | h
  · exact hasDerivAt_Kgen_two W m hL hm I hI (by omega)
  · exact hasDerivAt_Kgen hL W m hm I hI h

end Final

section Lemma34

variable {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ)
  (hm1 : ∀ s, ‖m s‖ ≤ 1) {T₀ : ℝ} (hT₀ : T₀ < 1)
include hL hm1 hT₀

/-- **The tree representation solves Definition 2.12** on `[0, T₀]`, `T₀ < 1`, `|m| ≤ 1`. -/
theorem isPrimitive_Kgen : IsPrimitive L W m (Set.Icc 0 T₀) (fun t => Kgen L W m t) := by
  refine ⟨fun t ht I hI h2 => ?_, fun I hI h2 => Kgen_zero W m I hI h2,
    fun t _ s a => Kgen_one W m t s a⟩
  exact hasDerivAt_Kgen_all W m hL
    (fun s s' => (norm_mul_le_of_mem_Icc m hm1 ht s s').trans_lt hT₀) I hI h2

omit [NeZero W] in
theorem norm_Kgen_two_le {t : ℝ} (ht : t ∈ Set.Icc 0 T₀) (I : LoopIdx (ZMod L)) (hI : I.WF)
    (h2 : I.length = 2) : ‖Kgen L W m t I‖ ≤ (W : ℝ)⁻¹ * (1 - T₀)⁻¹ := by
  obtain ⟨σ, a⟩ := I
  have ha : a.length = 2 := h2
  have hσ : σ.length = 2 := hI.trans ha
  obtain ⟨x₁, x₂, rfl⟩ := List.length_eq_two.1 ha
  obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.1 hσ
  rw [Kgen_two]
  exact norm_kLoop4_two_le W m hL hm1 ht hT₀ (I := ⟨[s₁, s₂], [x₁, x₂]⟩) rfl rfl

/-- **Lemma 3.4 (tree representation), every `n`.**  If `K` solves the primitive equation of
Definition 2.12 on `[0, T₀]` (`T₀ < 1`, `|m| ≤ 1`) with bounded `2`-loops, then on every loop of
length `n ≥ 2` it is the tree representation `Kgen`. -/
theorem eq_Kgen_of_isPrimitive {T : Set ℝ} {K : ℝ → LoopIdx (ZMod L) → ℂ}
    (hK : IsPrimitive L W m T K) (hT : Set.Icc 0 T₀ ⊆ T) {R : ℝ}
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length →
      K t I = Kgen L W m t I := by
  have hK' : IsPrimitive L W m (Set.Icc 0 T₀) K :=
    ⟨fun t ht => hK.1 t (hT ht), hK.2.1, fun t ht => hK.2.2 t (hT ht)⟩
  have hpos : 0 < 1 - T₀ := by linarith
  have hR0 : 0 ≤ max R ((W : ℝ)⁻¹ * (1 - T₀)⁻¹) := le_trans (by positivity) (le_max_right _ _)
  exact isPrimitive_unique L hL W m hK' (isPrimitive_Kgen hL W m hm1 hT₀) subset_rfl hR0
    (fun t ht I hI h2 => ⟨(hR t ht I hI h2).trans (le_max_left _ _),
      (norm_Kgen_two_le hL W m hm1 hT₀ ht I hI h2).trans (le_max_right _ _)⟩)

/-- **Lemma 3.4, (3.5), in the paper's form** for `n ≥ 3`:
`K_{t,σ,a} = m_σ W^{-n+1} ∑_{Γ ∈ T_SP(P_a)} Γ_a(t, σ)`. -/
theorem treeRep_general {T : Set ℝ} {K : ℝ → LoopIdx (ZMod L) → ℂ}
    (hK : IsPrimitive L W m T K) (hT : Set.Icc 0 T₀ ⊆ T) {R : ℝ}
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T₀) (I : LoopIdx (ZMod L)) (hI : I.WF) (h3 : 3 ≤ I.length) :
    haveI : NeZero I.length := ⟨by omega⟩
    K t I = (I.σ.map m).prod * (W : ℂ)⁻¹ ^ (I.length - 1) *
      ∑ F ∈ TSP I.length, treeValG L m t (fun i => I.σ.getD i false) (fun i => I.a.getD i 0) F := by
  have : NeZero I.length := ⟨by omega⟩
  rw [eq_Kgen_of_isPrimitive hL W m hm1 hT₀ hK hT hR t ht I hI (by omega),
    Kgen_eq W m t h3 I rfl, Kn]
  congr 2
  exact prod_getD_eq I.σ m false (n := I.length) hI

end Lemma34

end RBM
