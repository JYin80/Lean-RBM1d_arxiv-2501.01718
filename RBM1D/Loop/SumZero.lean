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

end RBM
