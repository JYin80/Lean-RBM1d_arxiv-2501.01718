/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Layer

/-!
# Lemma 3.10: symmetry and the sum-zero property of the self-energy

Paper p.40–45.

**Lemma 3.10 (1)** says `Σ^(∅)(t, σ^(alt), d)` is translation invariant and symmetric,
`Σ(d) = Σ(-d)`.  The paper calls this a "simple consequence of the explicit expression"; here
it is proved for **every** `σ` and every layer `π` (`SigmaPi_add_const`, `SigmaPi_neg`), from
the corresponding properties of each edge weight (`selfW_add_const`, `selfW_neg`).

**(3.47)–(3.48)**: summing `K^(π)` over all boundary labels `a` turns every boundary edge into
its row sum `(1 - t m_i m_{i+1})^{-1}` (`S^(B) 1 = 1`), so
`∑_a K^(π)(t,σ,a) = ∏_i (1 - t m_i m_{i+1})^{-1} · ∑_d Σ^(π)(t,σ,d)` (`sum_Kpi_eq`), an exact
identity.
-/

namespace RBM

open Finset

section Symmetry

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- If every edge weight is translation invariant, so is the self-energy. -/
theorem selfW_add_const (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ)
    (hE : ∀ e x y c, E e (x + c) (y + c) = E e x y) (d : Fin n → ZMod L) (c : ZMod L) :
    selfW L F E (fun v => d v + c) = selfW L F E d := by
  unfold selfW
  rw [← Equiv.sum_comp (Equiv.addRight (fun _ : ↥(nodes F) => c))]
  refine sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_addRight, Pi.add_apply, add_left_inj, hE]

/-- If every edge weight satisfies `E(-x,-y) = E(x,y)`, the self-energy is even. -/
theorem selfW_neg (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ)
    (hE : ∀ e x y, E e (-x) (-y) = E e x y) (d : Fin n → ZMod L) :
    selfW L F E (fun v => -d v) = selfW L F E d := by
  unfold selfW
  rw [← Equiv.sum_comp (Equiv.neg (↥(nodes F) → ZMod L))]
  refine sum_congr rfl fun b _ => ?_
  simp only [Equiv.neg_apply, Pi.neg_apply, neg_inj, hE]

omit [NeZero n] in
theorem Theta_sub_one_add_const (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (x y c : ZMod L) :
    (Theta L ξ - 1) (x + c) (y + c) = (Theta L ξ - 1) x y := by
  simp only [Matrix.sub_apply, Matrix.one_apply, add_left_inj, Theta_apply_add_right L hL hξ]

omit [NeZero n] in
theorem Theta_sub_one_neg (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (x y : ZMod L) :
    (Theta L ξ - 1) (-x) (-y) = (Theta L ξ - 1) x y := by
  have h1 : Theta L ξ (-x) (-y) = Theta L ξ x y := by
    have := Theta_apply_add_right L hL hξ (-x) (-y) (x + y)
    rw [show -x + (x + y) = y by ring, show -y + (x + y) = x by ring] at this
    rw [← this]
    exact congrFun (congrFun (Theta_transpose L hL hξ) x) y
  simp only [Matrix.sub_apply, Matrix.one_apply, neg_inj, h1]

variable (m : Bool → ℂ) {t : ℝ} (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hm

/-- **Lemma 3.10 (1), translation invariance**, for every `σ` and `π`:
`Σ^(π)(t,σ,d + c) = Σ^(π)(t,σ,d)`. -/
theorem SigmaPi_add_const (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n))
    (d : Fin n → ZMod L) (c : ZMod L) :
    SigmaPi L m t σ π (fun v => d v + c) = SigmaPi L m t σ π d := by
  unfold SigmaPi selfE
  refine sum_congr rfl fun F _ => selfW_add_const F _ (fun e x y c => ?_) d c
  exact Theta_sub_one_add_const hL (hm _ _) x y c

/-- **Lemma 3.10 (1), symmetry**, for every `σ` and `π`: `Σ^(π)(t,σ,-d) = Σ^(π)(t,σ,d)`. -/
theorem SigmaPi_neg (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n))
    (d : Fin n → ZMod L) :
    SigmaPi L m t σ π (fun v => -d v) = SigmaPi L m t σ π d := by
  unfold SigmaPi selfE
  refine sum_congr rfl fun F _ => selfW_neg F _ (fun e x y => ?_) d
  exact Theta_sub_one_neg hL (hm _ _) x y

end Symmetry

section RowSums

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Column sums of `Θ_ξ`: `∑_x (Θ_ξ)_{xy} = (1 - ξ)^{-1}`. -/
theorem sum_Theta_col (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (y : ZMod L) :
    ∑ x : ZMod L, Theta L ξ x y = (1 - ξ)⁻¹ := by
  rw [← sum_Theta_row L hL hξ y]
  refine sum_congr rfl fun x _ => ?_
  exact congrFun (congrFun (Theta_transpose L hL hξ) y) x

variable (m : Bool → ℂ) {t : ℝ} (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hm

/-- **(3.47)–(3.48)**: `∑_a K^(π)(t,σ,a) = ∏_i (1 - t m_i m_{i+1})^{-1} ∑_d Σ^(π)(t,σ,d)`. -/
theorem sum_Kpi_eq (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    ∑ a : Fin n → ZMod L, Kpi L m t σ a π =
      (∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹) *
        ∑ d : Fin n → ZMod L, SigmaPi L m t σ π d := by
  simp_rw [Kpi_eq_sum_SigmaPi]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun d _ => ?_
  rw [← mul_sum, mul_comm]
  congr 1
  have h := (prod_univ_sum (fun _ : Fin n => (univ : Finset (ZMod L)))
    (fun v x => thetaEdge L m t (σ v) (σ (v + 1)) x (d v))).symm
  rw [Fintype.piFinset_univ] at h
  rw [h]
  refine prod_congr rfl fun v _ => ?_
  exact sum_Theta_col hL (hm _ _) (d v)

end RowSums

section SumOut

/-- **Summing out one coordinate.**  If `f` does not depend on the coordinate `i`, and `G y b`
does not depend on it either and has `∑_y G y b = r`, then
`|Z| ∑_b f(b) G(b_i, b) = r ∑_b f(b)`. -/
theorem sum_out {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z] (i : ι)
    (f : (ι → Z) → ℂ) (G : Z → (ι → Z) → ℂ) (r : ℂ)
    (hf : ∀ b x, f (Function.update b i x) = f b)
    (hG : ∀ b x y, G y (Function.update b i x) = G y b)
    (hr : ∀ b, ∑ x, G x b = r) :
    (Fintype.card Z : ℂ) * ∑ b, f b * G (b i) b = r * ∑ b, f b := by
  classical
  rcases isEmpty_or_nonempty Z with hZ | ⟨⟨x0⟩⟩
  · have : IsEmpty (ι → Z) := ⟨fun b => isEmptyElim (b i)⟩
    simp
  set e := Equiv.piSplitAt i (fun _ : ι => Z)
  have hs : ∀ x b', e.symm (x, b') = Function.update (e.symm (x0, b')) i x := by
    intro x b'
    funext j
    by_cases hj : j = i
    · subst hj; simp [e, Equiv.piSplitAt]
    · simp [e, Equiv.piSplitAt, hj]
  have hsi : ∀ x b', e.symm (x, b') i = x := by
    intro x b'; rw [hs, Function.update_self]
  have h1 : ∀ x b', f (e.symm (x, b')) = f (e.symm (x0, b')) := by
    intro x b'; rw [hs, hf]
  have h2 : ∀ x y b', G y (e.symm (x, b')) = G y (e.symm (x0, b')) := by
    intro x y b'; rw [hs, hG]
  rw [← Equiv.sum_comp e.symm, ← Equiv.sum_comp e.symm (fun b => f b),
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hl : ∀ x, ∑ b' : {j // j ≠ i} → Z, f (e.symm (x, b')) * G (e.symm (x, b') i) (e.symm (x, b'))
      = ∑ b' : {j // j ≠ i} → Z, f (e.symm (x0, b')) * G x (e.symm (x0, b')) := by
    intro x
    refine sum_congr rfl fun b' _ => ?_
    rw [h1, hsi, h2]
  have hr' : ∀ x, ∑ b' : {j // j ≠ i} → Z, f (e.symm (x, b'))
      = ∑ b' : {j // j ≠ i} → Z, f (e.symm (x0, b')) := fun x => sum_congr rfl fun b' _ => h1 x b'
  simp only [hl, hr']
  rw [sum_comm, sum_const, card_univ, nsmul_eq_mul]
  simp only [← mul_sum, hr]
  rw [← sum_mul]
  ring

end SumOut

section TreeSum

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- A tree without boundary edges, all labels summed: `∑_b ∏_e E_e(b_e, b_{par e})`. -/
noncomputable def treeZ (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) : ℂ :=
  ∑ b : ↥(nodes F) → ZMod L,
    ∏ d : ↥F, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)

omit [NeZero n] in
theorem arcWidth_lt {d e : Fin n × Fin n} (hde : ArcLe d e) (hne : d ≠ e) (hd : d.1 ≤ d.2) :
    arcWidth d < arcWidth e := by
  obtain ⟨h1, h2⟩ := hde
  have h : d.1.val ≠ e.1.val ∨ d.2.val ≠ e.2.val := by
    by_contra h
    exact hne (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  simp only [arcWidth]
  rw [Fin.le_def] at h1 h2 hd
  omega

/-- **Peeling.**  If every edge weight has constant column sums `r_e`, then for every set `G`
of edges, `L^{|G|} ∑_b ∏_{e ∈ G} E_e(b_e, b_{par e}) = ∏_{e ∈ G} r_e · ∑_b 1`.  An edge of `G`
of smallest arc is childless in `G`, so its lower label can be summed out (`sum_out`). -/
theorem treeZ_peel {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
    (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) (r : ↥F → ℂ) (hr : ∀ d y, ∑ x, E d x y = r d) :
    ∀ G : Finset ↥F, (L : ℂ) ^ G.card * ∑ b : ↥(nodes F) → ZMod L,
        ∏ d ∈ G, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩) =
      (∏ d ∈ G, r d) * ∑ _b : ↥(nodes F) → ZMod L, (1 : ℂ) := by
  intro G
  induction G using Finset.strongInduction with
  | H G ih =>
  rcases G.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨e, he, hmin⟩ := G.exists_min_image (fun d : ↥F => arcWidth d.1) hne
  set i : ↥(nodes F) := ⟨e.1, mem_nodes_of_mem e.2⟩
  have hpe := nodePar_spec hF hn (mem_nodes_of_mem e.2) (ne_wholeP hF e.2)
  -- the parents of the other edges of `G` are not `e`
  have hpar : ∀ d ∈ G.erase e, nodePar F d.1 ≠ e.1 := by
    intro d hd heq
    obtain ⟨hdne, hdG⟩ := mem_erase.1 hd
    obtain ⟨-, hdp, hpd, -⟩ := nodePar_spec hF hn (mem_nodes_of_mem d.2) (ne_wholeP hF d.2)
    rw [heq] at hdp hpd
    have hdd : d.1.1 ≤ d.1.2 := le_of_lt (hF.1 _ d.2).1
    have := arcWidth_lt hdp (Ne.symm hpd) hdd
    exact absurd (hmin d hdG) (not_le.2 this)
  have hself : ∀ d ∈ G.erase e, (⟨d.1, mem_nodes_of_mem d.2⟩ : ↥(nodes F)) ≠ i := by
    intro d hd h
    have h' : d.1 = e.1 := by simpa [i] using congrArg Subtype.val h
    exact (mem_erase.1 hd).1 (Subtype.ext h')
  set f : (↥(nodes F) → ZMod L) → ℂ := fun b =>
    ∏ d ∈ G.erase e, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)
  set Gf : ZMod L → (↥(nodes F) → ZMod L) → ℂ := fun y b =>
    E e y (b ⟨nodePar F e, nodePar_mem F e⟩)
  have hsplit : ∀ b : ↥(nodes F) → ZMod L,
      ∏ d ∈ G, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)
        = f b * Gf (b i) b := by
    intro b
    rw [← mul_prod_erase G _ he, mul_comm]
  have hf : ∀ b x, f (Function.update b i x) = f b := by
    intro b x
    refine prod_congr rfl fun d hd => ?_
    have h1 : (⟨nodePar F d, nodePar_mem F d⟩ : ↥(nodes F)) ≠ i := by
      intro h; exact hpar d hd (congrArg Subtype.val h)
    rw [Function.update_of_ne (hself d hd), Function.update_of_ne h1]
  have hG : ∀ b x y, Gf y (Function.update b i x) = Gf y b := by
    intro b x y
    have h1 : (⟨nodePar F e, nodePar_mem F e⟩ : ↥(nodes F)) ≠ i := by
      intro h; exact hpe.2.2.1 (congrArg Subtype.val h)
    simp only [Gf, Function.update_of_ne h1]
  have hsum := sum_out i f Gf (r e) hf hG (fun b => hr e _)
  rw [ZMod.card] at hsum
  have hcard : G.card = (G.erase e).card + 1 := (card_erase_add_one he).symm
  have hlt : G.erase e ⊂ G := erase_ssubset he
  have hih := ih _ hlt
  simp only [hsplit]
  rw [hcard, pow_succ, mul_assoc, hsum, ← mul_prod_erase G _ he]
  rw [mul_left_comm, hih]
  ring

/-- **The closed form of a fully summed tree**: `∑_b ∏_e E_e(b_e, b_{par e}) = L ∏_e r_e`. -/
theorem treeZ_eq {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
    (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) (r : ↥F → ℂ) (hr : ∀ d y, ∑ x, E d x y = r d) :
    treeZ F E = L * ∏ d, r d := by
  have h := treeZ_peel hF hn E r hr univ
  have hc : Fintype.card ↥(nodes F) = F.card + 1 := by
    rw [Fintype.card_coe, nodes, card_insert_of_notMem (wholeP_not_mem hF)]
  simp only [sum_const, card_univ, Fintype.card_pi, prod_const, Fintype.card_coe, hc,
    ZMod.card, nsmul_eq_mul, mul_one] at h
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  have hpow : (L : ℂ) ^ F.card ≠ 0 := pow_ne_zero _ hL0
  unfold treeZ
  apply mul_left_cancel₀ hpow
  rw [h]
  push_cast
  ring

/-- Summing the self-energy over `d` removes the Kronecker deltas. -/
theorem sum_selfW (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) :
    ∑ d : Fin n → ZMod L, selfW L F E d = treeZ F E := by
  unfold selfW treeZ
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_mul]
  have h := (prod_univ_sum (fun _ : Fin n => (univ : Finset (ZMod L)))
    (fun v x => if x = b ⟨leafPar F v, leafPar_mem F v⟩ then (1 : ℂ) else 0)).symm
  rw [Fintype.piFinset_univ] at h
  rw [h]
  simp

end TreeSum

section Closed

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- The column sum of an internal edge `Θ_ξ - 1`, `ξ = t m(s) m(s')`: `(1 - ξ)^{-1} - 1`. -/
noncomputable def edgeR (m : Bool → ℂ) (t : ℝ) (s s' : Bool) : ℂ :=
  (1 - (t : ℂ) * (m s * m s'))⁻¹ - 1

/-- `Q(σ,π) = ∑_{F ∈ T_SP(σ,π)} ∏_{e ∈ F} ((1 - ξ_e)^{-1} - 1)`. -/
noncomputable def Qlayer (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) : ℂ :=
  ∑ F ∈ TSPlong n σ π, ∏ e ∈ F, edgeR m t (σ e.1) (σ e.2)

/-- `A(σ,π) = L^{-1} ∑_a K^(π)(t,σ,a) = ∏_v (1 - ξ_v)^{-1} · Q(σ,π)` (`sum_Kpi_closed`); it
depends neither on `L` nor on `W`. -/
noncomputable def Alayer (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) : ℂ :=
  (∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹) * Qlayer m t σ π

omit [NeZero n] in
theorem sum_Theta_sub_one_col (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (y : ZMod L) :
    ∑ x : ZMod L, (Theta L ξ - 1) x y = (1 - ξ)⁻¹ - 1 := by
  simp only [Matrix.sub_apply, sum_sub_distrib, sum_Theta_col hL hξ, Matrix.one_apply]
  simp

variable (m : Bool → ℂ) {t : ℝ} (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hm

/-- `∑_d Σ^(π)(t,σ,d) = L · Q(σ,π)`. -/
theorem sum_SigmaPi (hL : 3 ≤ L) (hn : 2 ≤ n) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    ∑ d : Fin n → ZMod L, SigmaPi L m t σ π d = L * Qlayer m t σ π := by
  unfold SigmaPi Qlayer
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun F hF => ?_
  have hT : IsTSP F := isTSP_of_mem_TSP (TSPlong_subset σ π hF)
  unfold selfE
  rw [sum_selfW, treeZ_eq hT hn (fun e => thetaEdge L m t (σ e.1.1) (σ e.1.2) - 1)
    (fun e => edgeR m t (σ e.1.1) (σ e.1.2))
    (fun e y => sum_Theta_sub_one_col hL (hm _ _) y)]
  rw [prod_coe_sort F (fun e => edgeR m t (σ e.1) (σ e.2))]

/-- **The closed form of (3.48)**: `∑_a K^(π)(t,σ,a) = L · A(σ,π)`. -/
theorem sum_Kpi_closed (hL : 3 ≤ L) (hn : 2 ≤ n) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) :
    ∑ a : Fin n → ZMod L, Kpi L m t σ a π = L * Alayer m t σ π := by
  rw [sum_Kpi_eq m hm hL, sum_SigmaPi m hm hL hn, Alayer]
  ring

end Closed

section Molecule

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- The charges of the inside polygon of the cut at `J`: its region `k` is region `J.1 + k`
(`k = wIn J` is region `J.2`). -/
def sigmaIn (σ : Fin n → Bool) (J : Fin n × Fin n) : Fin (wIn J + 1) → Bool :=
  fun k => σ ⟨min (J.1.val + k.val) (n - 1), by have := NeZero.pos n; omega⟩

/-- The charges of the outside polygon of the cut at `J`: its region `k` is region
`unCol J k` (the regions strictly between `J.1` and `J.2` are removed). -/
def sigmaOut (σ : Fin n → Bool) (J : Fin n × Fin n) : Fin (n - wIn J + 1) → Bool :=
  fun k => σ ⟨min (unCol J k.val) (n - 1), by have := NeZero.pos n; omega⟩

omit [NeZero n] in
theorem arcLe_le {d : Fin n × Fin n} (h : ArcLe d J) (h12 : d.1 ≤ d.2) :
    J.1.val ≤ d.1.val ∧ d.2.val ≤ J.2.val ∧ d.1.val ≤ d.2.val := by
  simp only [ArcLe, Fin.le_def] at h h12
  exact ⟨h.1, h.2, h12⟩

theorem sigmaIn_shiftIn (σ : Fin n → Bool) {d : Fin n × Fin n} (hd : ArcLe d J)
    (h12 : d.1 ≤ d.2) :
    sigmaIn σ J (shiftIn J d).1 = σ d.1 ∧ sigmaIn σ J (shiftIn J d).2 = σ d.2 := by
  obtain ⟨h1, h2⟩ := shiftIn_val hd h12
  obtain ⟨a1, a2, a3⟩ := arcLe_le hd h12
  have hd1 := d.1.isLt
  have hd2 := d.2.isLt
  constructor <;> (unfold sigmaIn; congr 1; ext; simp only [h1, h2]; omega)

theorem sigmaOut_shiftOut (σ : Fin n → Bool) {d : Fin n × Fin n} (hd : OutEnds J d)
    (hJ : J.1.val + 2 ≤ J.2.val) :
    sigmaOut σ J (shiftOut J d).1 = σ d.1 ∧ sigmaOut σ J (shiftOut J d).2 = σ d.2 := by
  obtain ⟨h1, h2⟩ := shiftOut_val d (by omega : J.1.val < J.2.val)
  have hd1 := d.1.isLt
  have hd2 := d.2.isLt
  have e1 := unCol_col hd.1 hJ
  have e2 := unCol_col hd.2.1 hJ
  constructor <;> (unfold sigmaOut; congr 1; ext; simp only [h1, h2, e1, e2]; omega)

variable {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
include hF hn hJ

/-- **A product over the edges of `F ∋ J` splits over the cut**: the edge `J`, the outside
family and the inside family, each with its own charges. -/
theorem prod_cut (σ : Fin n → Bool) (w : Bool → Bool → ℂ) :
    ∏ e ∈ F, w (σ e.1) (σ e.2) =
      w (σ J.1) (σ J.2) * (∏ g ∈ FOut F J, w (sigmaOut σ J g.1) (sigmaOut σ J g.2)) *
        ∏ h ∈ FIn F J, w (sigmaIn σ J h.1) (sigmaIn σ J h.2) := by
  have hJw := diag_width hF hJ
  have h12 : ∀ d ∈ F, d.1 ≤ d.2 := fun d hd => le_of_lt (hF.1 d hd).1
  rw [← mul_prod_erase F _ hJ, mul_assoc]
  congr 1
  rw [← prod_filter_mul_prod_filter_not (F.erase J) (fun d => ArcLe d J), mul_comm]
  have hout : (F.erase J).filter (fun d => ¬ArcLe d J) = F.filter (fun d => ¬ArcLe d J) := by
    ext d
    simp only [mem_filter, mem_erase]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · exact fun h => ⟨⟨fun hdJ => h.2 (hdJ ▸ ⟨le_rfl, le_rfl⟩), h.1⟩, h.2⟩
  have hin : (F.erase J).filter (fun d => ArcLe d J) = F.filter (fun d => ArcLe d J ∧ d ≠ J) := by
    ext d
    simp only [mem_filter, mem_erase]
    tauto
  rw [hout, hin]
  congr 1
  · unfold FOut
    rw [prod_image]
    · refine prod_congr rfl fun d hd => ?_
      obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
      obtain ⟨e1, e2⟩ := sigmaOut_shiftOut σ (outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ) hJw
      rw [e1, e2]
    · intro d hd e he h
      obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
      obtain ⟨heF, heJ⟩ := mem_filter.1 he
      exact shiftOut_injOn (outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ)
        (outEnds_of hF hn hJ (mem_nodes_of_mem heF) heJ) hJw h
  · unfold FIn
    rw [prod_image]
    · refine prod_congr rfl fun d hd => ?_
      obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
      obtain ⟨e1, e2⟩ := sigmaIn_shiftIn σ hdJ (h12 d hdF)
      rw [e1, e2]
    · intro d hd e he h
      obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
      obtain ⟨heF, heJ, -⟩ := mem_filter.1 he
      exact shiftIn_injOn hdJ (h12 d hdF) heJ (h12 e heF) h

/-- The long edges of the outside family are the outside long edges of `F`. -/
theorem Flong_FOut (σ : Fin n → Bool) :
    Flong (FOut F J) (sigmaOut σ J) =
      ((Flong F σ).filter fun d => ¬ArcLe d J).image (shiftOut J) := by
  have hJw := diag_width hF hJ
  unfold Flong FOut
  rw [filter_image]
  congr 1
  ext d
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hdF, hdJ⟩, hl⟩
    obtain ⟨e1, e2⟩ := sigmaOut_shiftOut σ (outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ) hJw
    exact ⟨⟨hdF, by rwa [e1, e2] at hl⟩, hdJ⟩
  · rintro ⟨⟨hdF, hl⟩, hdJ⟩
    obtain ⟨e1, e2⟩ := sigmaOut_shiftOut σ (outEnds_of hF hn hJ (mem_nodes_of_mem hdF) hdJ) hJw
    exact ⟨⟨hdF, hdJ⟩, by rwa [e1, e2]⟩

omit hn hJ in
/-- The long edges of the inside family are the long edges of `F` strictly inside `J`. -/
theorem Flong_FIn (σ : Fin n → Bool) :
    Flong (FIn F J) (sigmaIn σ J) =
      ((Flong F σ).filter fun d => ArcLe d J ∧ d ≠ J).image (shiftIn J) := by
  have h12 : ∀ d ∈ F, d.1 ≤ d.2 := fun d hd => le_of_lt (hF.1 d hd).1
  unfold Flong FIn
  rw [filter_image]
  congr 1
  ext d
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hdF, hdJ, hne⟩, hl⟩
    obtain ⟨e1, e2⟩ := sigmaIn_shiftIn σ hdJ (h12 d hdF)
    exact ⟨⟨hdF, by rwa [e1, e2] at hl⟩, hdJ, hne⟩
  · rintro ⟨⟨hdF, hl⟩, hdJ, hne⟩
    obtain ⟨e1, e2⟩ := sigmaIn_shiftIn σ hdJ (h12 d hdF)
    exact ⟨⟨hdF, hdJ, hne⟩, by rwa [e1, e2]⟩

/-- **The layer condition across the cut.**  Let `π = F_long(F₀, σ)` for some tree `F₀` and let
`J ∈ π` be innermost (no other long edge of `π` inside `J`).  Then a tree `F ∋ J` lies in the
layer `π` iff its inside family has no long edges and the long edges of its outside family are
`π ∖ {J}`, collapsed. -/
theorem Flong_eq_iff_cut (σ : Fin n → Bool) {F₀ : Finset (Fin n × Fin n)} (hF₀ : IsTSP F₀)
    {π : Finset (Fin n × Fin n)} (hπ : Flong F₀ σ = π) (hJπ : J ∈ π)
    (hinner : ∀ e ∈ π, ArcLe e J → e = J) :
    Flong F σ = π ↔ Flong (FOut F J) (sigmaOut σ J) = (π.erase J).image (shiftOut J) ∧
      Flong (FIn F J) (sigmaIn σ J) = ∅ := by
  have hJw := diag_width hF hJ
  have hJF₀ : J ∈ F₀ := Flong_subset F₀ σ (hπ ▸ hJπ)
  have hJlong : σ J.1 ≠ σ J.2 := (mem_Flong.1 (hπ ▸ hJπ)).2
  have hπout : ∀ e ∈ π.erase J, OutEnds J e ∧ ¬ArcLe e J := by
    intro e he
    obtain ⟨hne, heπ⟩ := mem_erase.1 he
    have hnot : ¬ArcLe e J := fun h => hne (hinner e heπ h)
    exact ⟨outEnds_of hF₀ hn hJF₀ (mem_nodes_of_mem (Flong_subset F₀ σ (hπ ▸ heπ))) hnot, hnot⟩
  have hπerase : π.filter (fun d => ¬ArcLe d J) = π.erase J := by
    ext e
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨heπ, hnot⟩
      exact ⟨fun h => hnot (h ▸ ⟨le_rfl, le_rfl⟩), heπ⟩
    · rintro ⟨hne, heπ⟩
      exact ⟨heπ, fun h => hne (hinner e heπ h)⟩
  have hπin : π.filter (fun d => ArcLe d J ∧ d ≠ J) = ∅ := by
    refine filter_eq_empty_iff.2 fun e heπ h => h.2 (hinner e heπ h.1)
  rw [Flong_FOut hF hn hJ, Flong_FIn hF σ]
  constructor
  · intro h
    rw [h, hπerase, hπin, image_empty]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hout, hin⟩
    have hin' : (Flong F σ).filter (fun d => ArcLe d J ∧ d ≠ J) = ∅ := image_eq_empty.1 hin
    have hout' : (Flong F σ).filter (fun d => ¬ArcLe d J) = π.erase J := by
      ext e
      constructor
      · intro he
        obtain ⟨heF, heJ⟩ := mem_filter.1 he
        have heO := outEnds_of hF hn hJ (mem_nodes_of_mem (Flong_subset F σ heF)) heJ
        have : shiftOut J e ∈ (π.erase J).image (shiftOut J) := hout ▸ mem_image_of_mem _ he
        obtain ⟨e', he', hee'⟩ := mem_image.1 this
        rwa [← shiftOut_injOn (hπout e' he').1 heO hJw hee']
      · intro he
        have : shiftOut J e ∈ ((Flong F σ).filter fun d => ¬ArcLe d J).image (shiftOut J) :=
          hout ▸ mem_image_of_mem _ he
        obtain ⟨e', he', hee'⟩ := mem_image.1 this
        obtain ⟨he'F, he'J⟩ := mem_filter.1 he'
        have he'O := outEnds_of hF hn hJ (mem_nodes_of_mem (Flong_subset F σ he'F)) he'J
        rwa [← shiftOut_injOn he'O (hπout e he).1 hJw hee']
    ext e
    constructor
    · intro he
      by_cases heJ : e = J
      · exact heJ ▸ hJπ
      by_cases hin : ArcLe e J
      · have : e ∈ (Flong F σ).filter (fun d => ArcLe d J ∧ d ≠ J) := mem_filter.2 ⟨he, hin, heJ⟩
        rw [hin'] at this
        exact absurd this (notMem_empty e)
      · have : e ∈ (Flong F σ).filter (fun d => ¬ArcLe d J) := mem_filter.2 ⟨he, hin⟩
        rw [hout'] at this
        exact (mem_erase.1 this).2
    · intro he
      by_cases heJ : e = J
      · exact heJ ▸ mem_Flong.2 ⟨hJ, hJlong⟩
      · have : e ∈ π.erase J := mem_erase.2 ⟨heJ, he⟩
        rw [← hout'] at this
        exact (mem_filter.1 this).1

end Molecule

section MoleculeSum

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **The molecule factorization (3.53)–(3.58), closed form.**  If `J` is an innermost long edge
of the layer `π = F_long(F₀, σ)`, then
`Q(σ, π) = r_J · Q(σ_out, π ∖ {J}) · Q(σ_in, ∅)`: the inside of `J` is a single molecule. -/
theorem Qlayer_cut (hn : 2 ≤ n) (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)}
    (hπ : Flong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, ArcLe e J → e = J) :
    Qlayer m t σ π = edgeR m t (σ J.1) (σ J.2) *
      Qlayer m t (sigmaOut σ J) ((π.erase J).image (shiftOut J)) *
        Qlayer m t (sigmaIn σ J) ∅ := by
  have hF₀' := isTSP_of_mem_TSP hF₀
  have hJF₀ : J ∈ F₀ := Flong_subset F₀ σ (hπ ▸ hJπ)
  have hJd : IsDiag n J.1 J.2 := hF₀'.1 J hJF₀
  set π' := (π.erase J).image (shiftOut J)
  set f : Finset (Fin (n - wIn J + 1) × Fin (n - wIn J + 1)) →
      Finset (Fin (wIn J + 1) × Fin (wIn J + 1)) → ℂ := fun G H =>
    (if Flong G (sigmaOut σ J) = π' then
      ∏ g ∈ G, edgeR m t (sigmaOut σ J g.1) (sigmaOut σ J g.2) else 0) *
    (if Flong H (sigmaIn σ J) = ∅ then
      ∏ h ∈ H, edgeR m t (sigmaIn σ J h.1) (sigmaIn σ J h.2) else 0)
  have hlayer : TSPlong n σ π = ((TSP n).filter fun F => J ∈ F).filter fun F => Flong F σ = π := by
    ext F
    simp only [TSPlong, mem_filter]
    constructor
    · rintro ⟨hF, h⟩
      exact ⟨⟨hF, Flong_subset F σ (h ▸ hJπ)⟩, h⟩
    · rintro ⟨⟨hF, -⟩, h⟩
      exact ⟨hF, h⟩
  have hpt : ∀ F ∈ (TSP n).filter (fun F => J ∈ F),
      (if Flong F σ = π then ∏ e ∈ F, edgeR m t (σ e.1) (σ e.2) else 0)
        = edgeR m t (σ J.1) (σ J.2) * f (FOut F J) (FIn F J) := by
    intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    have hF' := isTSP_of_mem_TSP hFT
    have hiff := Flong_eq_iff_cut hF' hn hJF σ hF₀' hπ hJπ hinner
    by_cases h : Flong F σ = π
    · obtain ⟨h1, h2⟩ := hiff.1 h
      have h1' : Flong (FOut F J) (sigmaOut σ J) = π' := h1
      simp only [f, h, h1', h2, ↓reduceIte, prod_cut hF' hn hJF σ]
      ring
    · simp only [f, h, ↓reduceIte]
      by_cases h1 : Flong (FOut F J) (sigmaOut σ J) = π'
      · have h2 : ¬Flong (FIn F J) (sigmaIn σ J) = ∅ := fun h2 => h (hiff.2 ⟨h1, h2⟩)
        simp [h2]
      · simp [h1]
  unfold Qlayer
  rw [hlayer, sum_filter, sum_congr rfl hpt, ← mul_sum, sum_cut hJd hn f]
  simp only [f, ← sum_mul_sum, ← sum_filter]
  rw [mul_assoc]
  rfl

end MoleculeSum

section Leaves

theorem fin_congr {N : ℕ} {α : Type*} (σ : Fin N → α) {a b : ℕ} (ha : a < N) (hb : b < N)
    (h : a = b) : σ ⟨a, ha⟩ = σ ⟨b, hb⟩ := by
  subst h; rfl

/-- A cyclic product over consecutive pairs, written over `range`. -/
theorem prod_cyc {k : ℕ} (τ : Fin (k + 1) → Bool) (g : Bool → Bool → ℂ) :
    ∏ v : Fin (k + 1), g (τ v) (τ (v + 1)) =
      (∏ v ∈ range k, g (τ ⟨min v k, by omega⟩) (τ ⟨min (v + 1) k, by omega⟩)) *
        g (τ (Fin.last k)) (τ 0) := by
  rw [Fin.prod_univ_castSucc, Fin.last_add_one]
  refine congrArg₂ (· * ·) ?_ rfl
  rw [← Fin.prod_univ_eq_prod_range
    (fun v => g (τ ⟨min v k, by omega⟩) (τ ⟨min (v + 1) k, by omega⟩)) k]
  refine prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  have h1 : Fin.castSucc i = ⟨min i k, by omega⟩ :=
    Fin.ext (by rw [Fin.val_castSucc]; exact (min_eq_left hi.le).symm)
  have h2 : Fin.castSucc i + 1 = ⟨min (i + 1) k, by omega⟩ := by
    ext
    rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i), Fin.val_castSucc]
    exact (min_eq_left hi).symm
  rw [h2, h1]

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **The boundary edges across the cut.**  Every boundary edge of the `n`-gon is a boundary
edge of exactly one of the two smaller polygons, and each of them has one more boundary edge,
the cut edge `J` (read from each side):
`∏_v g(σ_v, σ_{v+1}) · g(σ_j, σ_i) g(σ_i, σ_j) = ∏_{in} · ∏_{out}`. -/
theorem prod_leaves_cut (hJd : IsDiag n J.1 J.2) (σ : Fin n → Bool) (g : Bool → Bool → ℂ) :
    (∏ v : Fin n, g (σ v) (σ (v + 1))) * (g (σ J.2) (σ J.1) * g (σ J.1) (σ J.2)) =
      (∏ k : Fin (wIn J + 1), g (sigmaIn σ J k) (sigmaIn σ J (k + 1))) *
        ∏ k : Fin (n - wIn J + 1), g (sigmaOut σ J k) (sigmaOut σ J (k + 1)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  obtain ⟨hlt, hne1, hnot⟩ := hJd
  rw [Fin.lt_def] at hlt
  have hjn : J.2.val ≤ n' := by have := J.2.isLt; omega
  have hw : wIn J = J.2.val - J.1.val := rfl
  have hunc : ∀ v, v ≤ J.1.val → unCol J v = v := fun v hv => unCol_of_le hv
  have hunc' : ∀ v, J.1.val < v → unCol J v = v + (wIn J - 1) := fun v hv => unCol_of_gt hv
  -- the extended charges
  set σ' : ℕ → Bool := fun r => σ ⟨min r n', by omega⟩ with hσ'
  set G : ℕ → ℂ := fun r => g (σ' r) (σ' (r + 1)) with hG
  have hJ1 : σ J.1 = σ' J.1.val := fin_congr σ J.1.isLt (by omega) (by omega)
  have hJ2 : σ J.2 = σ' J.2.val := fin_congr σ J.2.isLt (by omega) (by omega)
  have horig : ∏ v : Fin (n' + 1), g (σ v) (σ (v + 1)) =
      (∏ v ∈ range n', G v) * g (σ' n') (σ' 0) := by
    rw [prod_cyc σ g]
    refine congrArg₂ (· * ·) rfl (congrArg₂ g ?_ ?_) <;>
      exact fin_congr σ _ _ (by simp)
  have hin : ∏ k : Fin (wIn J + 1), g (sigmaIn σ J k) (sigmaIn σ J (k + 1)) =
      (∏ v ∈ Ico J.1.val J.2.val, G v) * g (σ' J.2.val) (σ' J.1.val) := by
    rw [prod_cyc (sigmaIn σ J) g, prod_Ico_eq_prod_range]
    refine congrArg₂ (· * ·) (prod_congr rfl fun v hv => ?_) (congrArg₂ g ?_ ?_)
    · rw [mem_range] at hv
      exact congrArg₂ g (fin_congr σ _ _ (by simp; omega)) (fin_congr σ _ _ (by simp; omega))
    · exact fin_congr σ _ _ (by simp; omega)
    · exact fin_congr σ _ _ (by simp)
  have hout : ∏ k : Fin (n' + 1 - wIn J + 1), g (sigmaOut σ J k) (sigmaOut σ J (k + 1)) =
      (∏ v ∈ range J.1.val, G v) * g (σ' J.1.val) (σ' J.2.val) *
        (∏ v ∈ Ico J.2.val n', G v) * g (σ' n') (σ' 0) := by
    rw [prod_cyc (sigmaOut σ J) g]
    refine congrArg₂ (· * ·) ?_ (congrArg₂ g ?_ ?_)
    · rw [← prod_range_mul_prod_Ico _ (show J.1.val ≤ n' + 1 - wIn J by omega),
        prod_eq_prod_Ico_succ_bot (show J.1.val < n' + 1 - wIn J by omega), ← mul_assoc]
      refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_congr rfl fun v hv => ?_) ?_) ?_
      · rw [mem_range] at hv
        refine congrArg₂ g (fin_congr σ _ _ ?_) (fin_congr σ _ _ ?_)
        · simp only [min_eq_left (show v ≤ n' + 1 - wIn J by omega)]
          rw [hunc _ (by omega)]; omega
        · simp only [min_eq_left (show v + 1 ≤ n' + 1 - wIn J by omega)]
          rw [hunc _ (by omega)]; omega
      · refine congrArg₂ g (fin_congr σ _ _ ?_) (fin_congr σ _ _ ?_)
        · simp only [min_eq_left (show J.1.val ≤ n' + 1 - wIn J by omega)]
          rw [hunc _ le_rfl]; omega
        · simp only [min_eq_left (show J.1.val + 1 ≤ n' + 1 - wIn J by omega)]
          rw [hunc' _ (by omega)]; omega
      · rw [prod_Ico_eq_prod_range, prod_Ico_eq_prod_range,
          show n' + 1 - wIn J - (J.1.val + 1) = n' - J.2.val by omega]
        refine prod_congr rfl fun v hv => ?_
        rw [mem_range] at hv
        refine congrArg₂ g (fin_congr σ _ _ ?_) (fin_congr σ _ _ ?_)
        · simp only [min_eq_left (show J.1.val + 1 + v ≤ n' + 1 - wIn J by omega)]
          rw [hunc' _ (by omega)]; omega
        · simp only [min_eq_left (show J.1.val + 1 + v + 1 ≤ n' + 1 - wIn J by omega)]
          rw [hunc' _ (by omega)]; omega
    · refine fin_congr σ _ _ ?_
      simp only [Fin.val_last, min_self]
      rw [hunc' _ (by omega)]; omega
    · refine fin_congr σ _ _ ?_
      simp only [Fin.val_zero, Nat.zero_min]
      rw [hunc _ (Nat.zero_le _)]; omega
  rw [horig, hin, hout, hJ1, hJ2]
  rw [← prod_range_mul_prod_Ico G (show J.1.val ≤ n' by omega),
    ← prod_Ico_consecutive G (show J.1.val ≤ J.2.val by omega) hjn]
  ring

end Leaves

section MoleculeA

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **(3.60)–(3.64) in closed form.**  At an innermost long edge `J` of the layer `π`,
`A(σ, π) = ξ_J (1 - ξ_J) · A(σ_in, ∅) · A(σ_out, π ∖ {J})`; for a long edge `ξ_J = t|m|²`. -/
theorem Alayer_cut (hn : 2 ≤ n) (m : Bool → ℂ) {t : ℝ}
    (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)}
    (hπ : Flong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, ArcLe e J → e = J) :
    Alayer m t σ π = (t * (m (σ J.1) * m (σ J.2))) * (1 - t * (m (σ J.1) * m (σ J.2))) *
      Alayer m t (sigmaIn σ J) ∅ * Alayer m t (sigmaOut σ J) ((π.erase J).image (shiftOut J)) := by
  have hJd : IsDiag n J.1 J.2 :=
    (isTSP_of_mem_TSP hF₀).1 J (Flong_subset F₀ σ (hπ ▸ hJπ))
  set g : Bool → Bool → ℂ := fun s s' => (1 - (t : ℂ) * (m s * m s'))⁻¹ with hg
  have hP := prod_leaves_cut hJd σ g
  set ξ : ℂ := (t : ℂ) * (m (σ J.1) * m (σ J.2)) with hξ
  have hx : 1 - ξ ≠ 0 := by
    intro h
    have : ‖ξ‖ = 1 := by rw [show ξ = 1 by linear_combination -h, norm_one]
    exact absurd (hm (σ J.1) (σ J.2)) (by rw [this]; exact lt_irrefl 1)
  have hgJ : g (σ J.2) (σ J.1) = (1 - ξ)⁻¹ := by simp only [g, ξ, mul_comm (m (σ J.2))]
  have hgJ' : g (σ J.1) (σ J.2) = (1 - ξ)⁻¹ := rfl
  rw [hgJ, hgJ'] at hP
  unfold Alayer
  rw [Qlayer_cut hn m t σ hF₀ hπ hJπ hinner]
  unfold edgeR
  simp only [g] at hP
  rw [← hξ]
  have hP' : ∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹ =
      (∏ k : Fin (wIn J + 1), (1 - (t : ℂ) * (m (sigmaIn σ J k) * m (sigmaIn σ J (k + 1))))⁻¹) *
        (∏ k : Fin (n - wIn J + 1),
          (1 - (t : ℂ) * (m (sigmaOut σ J k) * m (sigmaOut σ J (k + 1))))⁻¹) * (1 - ξ) ^ 2 := by
    rw [← hP]
    field_simp
  rw [hP']
  field_simp
  ring

end MoleculeA

end RBM
