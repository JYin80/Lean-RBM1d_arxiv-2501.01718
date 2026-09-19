/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.TreeRep
import Mathlib.Analysis.Calculus.Deriv.Mul

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

end RBM
