/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.TreeRepGeneral
import RBM1D.Propagator.DecayComplex
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Corollary 3.5: the pure loop decays

Paper p.30, **Corollary 3.5 (Pure loop `K`)**: for `σ = (+, …, +)`,

  `|K_{t,σ,a}| ≤ C_n exp(-c_n max_{ij} ‖a_i - a_j‖)`.                              (3.6)

The proof follows the paper.  By Lemma 3.4 (`treeRep_general`) `K` is a sum of tree values.
When every charge is `+`, every edge of every tree is `Θ_ξ` or `Θ_ξ - 1` with the *same*
complex `ξ = t m(+)²`, and the complex form of (2.52) (`norm_Theta_apply_le_complex`) bounds
every entry by `B e^{-κ ‖x - y‖}` (`norm_thetaEdge_le`).  A tree whose edges all decay
exponentially decays in the distance between any two leaves (`norm_treeValW_le`).

## The gap hypothesis

(2.52) is uniform in `L` but carries `1/|1-ξ|` and `ℓ̂ = min(|1-ξ|^{-1/2}, L)`.  The paper's
constants are uniform because in the bulk `|1 - t m²|` is bounded below.  We make this an
explicit hypothesis `δ ≤ ‖1 - t m(+)²‖` (for `t ≤ T₀ < 1` it holds with `δ = 1 - T₀`,
`gap_of_le`), and the constants `cor35Const n δ`, `cor35Rate δ` depend on `n` and `δ` only
(paper-deltas #17).

## Main statements

* `RBM.Cor35.sum_pow_zdist_le` : `∑_u r^{‖u‖} ≤ 2/(1-r)` on the cycle, uniformly in `L`
* `RBM.Cor35.chain` : in the tree of `F`, the distance from a node to the root is at most
  the total length of the internal edges
* `RBM.Cor35.norm_treeValW_le` : a tree with exponentially decaying edges decays in the
  distance between any two leaves
* `RBM.Cor35.norm_thetaEdge_le` : the entries of `Θ_{t m(+)²}` and `Θ_{t m(+)²} - 1` decay
* `RBM.cor35` : **Corollary 3.5** for `n ≥ 3`; `RBM.cor35_two` : the case `n = 2`
-/

namespace RBM

open Finset Real

namespace Cor35

section Sum

variable (L : ℕ) [NeZero L]

theorem zdist_neg (u : ZMod L) : zdist L (-u) = zdist L u := by
  have hu := ZMod.val_lt u
  rw [zdist, zdist, ZMod.neg_val]
  split_ifs with h
  · subst h; simp
  · omega

theorem sum_pow_val_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ u : ZMod L, r ^ u.val ≤ 1 / (1 - r) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by have := NeZero.pos L; omega⟩
  have h : ∑ u : ZMod (k + 1), r ^ u.val = ∑ i ∈ range (k + 1), r ^ i := by
    rw [← Fin.sum_univ_eq_sum_range]; rfl
  rw [h, range_eq_Ico]
  simpa using geom_sum_Ico_le_of_lt_one hr0 hr1 (m := 0) (n := k + 1)

/-- `∑_u r^{‖u‖} ≤ 2/(1-r)` on the cycle `ZMod L`, uniformly in `L`. -/
theorem sum_pow_zdist_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ u : ZMod L, r ^ zdist L u ≤ 2 / (1 - r) := by
  have h1 : ∀ u : ZMod L, r ^ zdist L u ≤ r ^ u.val + r ^ (-u).val := by
    intro u
    by_cases hu : u = 0
    · subst hu; simp [zdist]
    · simp only [ZMod.neg_val, hu, ↓reduceIte, zdist]
      rcases min_choice u.val (L - u.val) with h | h <;> rw [h]
      · linarith [pow_nonneg hr0 (L - u.val)]
      · linarith [pow_nonneg hr0 u.val]
  have h2 : ∑ u : ZMod L, r ^ (-u).val = ∑ u : ZMod L, r ^ u.val :=
    Equiv.sum_comp (Equiv.neg (ZMod L)) (fun u => r ^ u.val)
  calc ∑ u : ZMod L, r ^ zdist L u ≤ ∑ u : ZMod L, (r ^ u.val + r ^ (-u).val) :=
        sum_le_sum fun u _ => h1 u
    _ = 2 * ∑ u : ZMod L, r ^ u.val := by rw [sum_add_distrib, h2]; ring
    _ ≤ 2 * (1 / (1 - r)) := by gcongr; exact sum_pow_val_le L hr0 hr1
    _ = 2 / (1 - r) := by ring

/-- `∑_x e^{-λ‖x - c‖} ≤ 2/(1 - e^{-λ})`, uniformly in `L` and `c`. -/
theorem sum_exp_zdist_le {lam : ℝ} (hlam : 0 < lam) (c : ZMod L) :
    ∑ x : ZMod L, exp (-(lam * zdist L (x - c))) ≤ 2 / (1 - exp (-lam)) := by
  have hr1 : exp (-lam) < 1 := exp_lt_one_iff.2 (by linarith)
  have e : ∀ x : ZMod L, exp (-(lam * zdist L (x - c))) = exp (-lam) ^ zdist L (x - c) := by
    intro x; rw [← exp_nat_mul]; congr 1; ring
  simp_rw [e]
  have h := (Equiv.subRight c).sum_comp (fun u => exp (-lam) ^ zdist L u)
  simp only [Equiv.subRight_apply] at h
  rw [h]
  exact sum_pow_zdist_le L (exp_pos _).le hr1

theorem one_le_two_div {lam : ℝ} (hlam : 0 < lam) : 1 ≤ 2 / (1 - exp (-lam)) := by
  have h1 : exp (-lam) < 1 := exp_lt_one_iff.2 (by linarith)
  have h0 : 0 < exp (-lam) := exp_pos _
  rw [le_div_iff₀ (by linarith)]
  linarith

end Sum

section Chain

variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]

theorem zdist_sub_le (x y z : ZMod L) :
    zdist L (x - z) ≤ zdist L (x - y) + zdist L (y - z) := by
  have := zdist_add_le L (x - y) (y - z)
  rwa [sub_add_sub_cancel] at this

/-- **Paths to the root.**  In the tree of `F` (rooted at `whole`), the distance from any
node `d` to the root is at most the total length of the internal edges above `d`. -/
theorem chain {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
    (β : Fin n × Fin n → ZMod L) : ∀ k : ℕ, ∀ d ∈ nodes F, (F.filter (ArcLe d)).card ≤ k →
      zdist L (β d - β (wholeP n)) ≤
        ∑ e ∈ F.filter (ArcLe d), zdist L (β e - β (nodePar F e)) := by
  intro k
  induction k with
  | zero =>
    intro d hd hk
    by_cases hw : d = wholeP n
    · subst hw; simp
    · have hdF : d ∈ F := (mem_insert.1 hd).resolve_left hw
      have hmem : d ∈ F.filter (ArcLe d) := mem_filter.2 ⟨hdF, le_rfl, le_rfl⟩
      have := card_pos.2 ⟨d, hmem⟩
      omega
  | succ k ih =>
    intro d hd hk
    by_cases hw : d = wholeP n
    · subst hw; simp
    · have hdF : d ∈ F := (mem_insert.1 hd).resolve_left hw
      obtain ⟨hp, hdp, hpd, -⟩ := nodePar_spec hF hn hd hw
      have hsub : F.filter (ArcLe (nodePar F d)) ⊆ (F.filter (ArcLe d)).erase d := by
        intro e he
        obtain ⟨heF, hpe⟩ := mem_filter.1 he
        refine mem_erase.2 ⟨?_, mem_filter.2 ⟨heF, hdp.trans hpe⟩⟩
        rintro rfl
        exact hpd (hpe.antisymm hdp)
      have hdmem : d ∈ F.filter (ArcLe d) := mem_filter.2 ⟨hdF, le_rfl, le_rfl⟩
      have hcard : (F.filter (ArcLe (nodePar F d))).card ≤ k := by
        have h1 := card_le_card hsub
        rw [card_erase_of_mem hdmem] at h1
        omega
      have hih := ih (nodePar F d) hp hcard
      have htri := zdist_sub_le (β d) (β (nodePar F d)) (β (wholeP n))
      have hs := sum_le_sum_of_subset hsub (f := fun e => zdist L (β e - β (nodePar F e)))
      rw [← add_sum_erase _ _ hdmem]
      omega

theorem chain' {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
    (β : Fin n × Fin n → ZMod L) {d : Fin n × Fin n} (hd : d ∈ nodes F) :
    zdist L (β d - β (wholeP n)) ≤ ∑ e ∈ F, zdist L (β e - β (nodePar F e)) :=
  (chain hF hn β _ d hd le_rfl).trans (sum_le_sum_of_subset (filter_subset _ _))

end Chain

section TreeBound

variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]

/-- The root is the leaf parent of the last vertex. -/
def lastV (n : ℕ) [NeZero n] : Fin n := ⟨n - 1, by have := NeZero.pos n; omega⟩

/-- **Pointwise part of the tree bound.**  Write `D` for the total edge length of a
labelling `β` of the tree of `F`.  Every leaf-to-leaf distance is at most `2D`, and every
node is within `D` of the last leaf. -/
theorem dist_bounds {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
    (a : Fin n → ZMod L) (β : Fin n × Fin n → ZMod L) :
    (∀ i j : Fin n, zdist L (a i - a j) ≤
      2 * (∑ v, zdist L (a v - β (leafPar F v)) + ∑ e ∈ F, zdist L (β e - β (nodePar F e)))) ∧
    (∀ d ∈ nodes F, zdist L (β d - a (lastV n)) ≤
      ∑ v, zdist L (a v - β (leafPar F v)) + ∑ e ∈ F, zdist L (β e - β (nodePar F e))) := by
  set Ls := ∑ v, zdist L (a v - β (leafPar F v))
  set Es := ∑ e ∈ F, zdist L (β e - β (nodePar F e))
  have hleaf : ∀ v, zdist L (a v - β (wholeP n)) ≤ Ls + Es := by
    intro v
    have h1 := zdist_sub_le (a v) (β (leafPar F v)) (β (wholeP n))
    have h2 := chain' hF hn β (leafPar_mem F v)
    have h3 : zdist L (a v - β (leafPar F v)) ≤ Ls :=
      single_le_sum (f := fun v => zdist L (a v - β (leafPar F v))) (fun _ _ => Nat.zero_le _)
        (mem_univ v)
    omega
  have hlast : zdist L (a (lastV n) - β (wholeP n)) ≤ Ls := by
    have h := single_le_sum (f := fun v => zdist L (a v - β (leafPar F v)))
      (fun _ _ => Nat.zero_le _) (mem_univ (lastV n))
    simpa [leafPar_root F (v := lastV n) rfl] using h
  refine ⟨fun i j => ?_, fun d hd => ?_⟩
  · have h1 := zdist_sub_le (a i) (β (wholeP n)) (a j)
    have h2 : zdist L (β (wholeP n) - a j) = zdist L (a j - β (wholeP n)) := by
      rw [← zdist_neg L, neg_sub]
    have := hleaf i
    have := hleaf j
    omega
  · have h1 := zdist_sub_le (β d) (β (wholeP n)) (a (lastV n))
    have h2 : zdist L (β (wholeP n) - a (lastV n)) = zdist L (a (lastV n) - β (wholeP n)) := by
      rw [← zdist_neg L, neg_sub]
    have := chain' hF hn β hd
    omega

/-- **Trees with exponentially decaying edges decay.**  If every edge weight of the tree of
`F` satisfies `|M_{xy}| ≤ B e^{-κ‖x-y‖}`, the tree value is at most
`B^{n+n²} (2/(1-e^{-κ/(2n²)}))^{n²} e^{-κ‖a_i - a_j‖/4}` for every pair of leaves, uniformly
in `L`. -/
theorem norm_treeValW_le {F : Finset (Fin n × Fin n)} (hF : IsTSP F) (hn : 2 ≤ n)
    (a : Fin n → ZMod L) (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ) {B κ : ℝ} (hB : 1 ≤ B) (hκ : 0 < κ)
    (hM : ∀ v x y, ‖M v x y‖ ≤ B * exp (-(κ * zdist L (x - y))))
    (hE : ∀ d x y, ‖E d x y‖ ≤ B * exp (-(κ * zdist L (x - y)))) (i j : Fin n) :
    ‖treeValW L F a M E‖ ≤ B ^ (n + n * n) *
      (2 / (1 - exp (-(κ / (2 * ((n * n : ℕ) : ℝ)))))) ^ (n * n) *
        exp (-(κ / 4 * zdist L (a i - a j))) := by
  have hnn : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by
    have := NeZero.pos n; exact_mod_cast Nat.mul_pos this this
  set lam := κ / (2 * ((n * n : ℕ) : ℝ)) with hlam_def
  have hlam : 0 < lam := by positivity
  set S := 2 / (1 - exp (-lam)) with hS
  have hS1 : 1 ≤ S := one_le_two_div hlam
  set N := (nodes F).card
  have hN : N ≤ n * n := by
    have := card_le_univ (nodes F)
    simpa using this
  have hFN : F.card ≤ N := card_le_card (subset_insert _ _)
  set g : ZMod L → ℝ := fun x => exp (-(lam * zdist L (x - a (lastV n))))
  set C0 := B ^ (n + F.card) * exp (-(κ / 4 * zdist L (a i - a j)))
  have hB0 : 0 ≤ B := by linarith
  -- the pointwise bound
  have hpt : ∀ b : ↥(nodes F) → ZMod L,
      ‖(∏ v : Fin n, M v (a v) (b ⟨leafPar F v, leafPar_mem F v⟩)) *
        ∏ d : ↥F, E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)‖
        ≤ C0 * ∏ ν : ↥(nodes F), g (b ν) := by
    intro b
    obtain ⟨β, hβ⟩ : ∃ β : Fin n × Fin n → ZMod L, ∀ d (h : d ∈ nodes F), b ⟨d, h⟩ = β d :=
      ⟨fun d => if h : d ∈ nodes F then b ⟨d, h⟩ else 0, fun d h => by simp [h]⟩
    have hβ' : ∀ ν : ↥(nodes F), b ν = β ν.1 := fun ν => hβ ν.1 ν.2
    set Ls := ∑ v, zdist L (a v - β (leafPar F v))
    set Es := ∑ e ∈ F, zdist L (β e - β (nodePar F e))
    obtain ⟨hij, hnode⟩ := dist_bounds hF hn a β
    have hL : ∏ v : Fin n, ‖M v (a v) (b ⟨leafPar F v, leafPar_mem F v⟩)‖
        ≤ B ^ n * exp (-(κ * (Ls : ℝ))) := by
      calc ∏ v : Fin n, ‖M v (a v) (b ⟨leafPar F v, leafPar_mem F v⟩)‖
          ≤ ∏ v : Fin n, (B * exp (-(κ * zdist L (a v - β (leafPar F v))))) := by
            refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
            rw [hβ]; exact hM _ _ _
        _ = B ^ n * exp (-(κ * (Ls : ℝ))) := by
            rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← exp_sum]
            congr 2
            simp only [Ls, Nat.cast_sum, mul_sum, sum_neg_distrib]
    have hE' : ∏ d : ↥F, ‖E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)‖
        ≤ B ^ F.card * exp (-(κ * (Es : ℝ))) := by
      calc ∏ d : ↥F, ‖E d (b ⟨d.1, mem_nodes_of_mem d.2⟩) (b ⟨nodePar F d, nodePar_mem F d⟩)‖
          ≤ ∏ d : ↥F, (B * exp (-(κ * zdist L (β d.1 - β (nodePar F d.1))))) := by
            refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun d _ => ?_
            rw [hβ, hβ]; exact hE _ _ _
        _ = B ^ F.card * exp (-(κ * (Es : ℝ))) := by
            rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_coe, ← exp_sum]
            congr 2
            rw [sum_coe_sort F (fun e => -(κ * (zdist L (β e - β (nodePar F e)) : ℝ)))]
            simp only [Es, Nat.cast_sum, mul_sum, sum_neg_distrib]
    -- the exponent
    have hexp : exp (-(κ * (Ls : ℝ))) * exp (-(κ * (Es : ℝ)))
        ≤ exp (-(κ / 4 * zdist L (a i - a j))) * ∏ ν : ↥(nodes F), g (b ν) := by
      simp only [g, ← exp_sum, ← exp_add]
      apply exp_le_exp.2
      have h1 : (zdist L (a i - a j) : ℝ) ≤ 2 * ((Ls : ℝ) + Es) := by exact_mod_cast hij i j
      have h2 : ∑ ν : ↥(nodes F), (zdist L (b ν - a (lastV n)) : ℝ) ≤ N * ((Ls : ℝ) + Es) := by
        have : ∀ ν : ↥(nodes F), (zdist L (b ν - a (lastV n)) : ℝ) ≤ (Ls : ℝ) + Es := by
          intro ν; rw [hβ']; exact_mod_cast hnode ν.1 ν.2
        calc _ ≤ ∑ _ν : ↥(nodes F), ((Ls : ℝ) + Es) := sum_le_sum fun ν _ => this ν
          _ = N * ((Ls : ℝ) + Es) := by rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      have h3 : (N : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hN
      have hD : (0 : ℝ) ≤ (Ls : ℝ) + Es := by positivity
      have h4 : lam * ∑ ν : ↥(nodes F), (zdist L (b ν - a (lastV n)) : ℝ)
          ≤ κ / 2 * ((Ls : ℝ) + Es) := by
        calc _ ≤ lam * (((n * n : ℕ) : ℝ) * ((Ls : ℝ) + Es)) := by
              gcongr; exact h2.trans (by gcongr)
          _ = κ / 2 * ((Ls : ℝ) + Es) := by rw [hlam_def]; field_simp
      have h5 : κ / 4 * (zdist L (a i - a j) : ℝ) ≤ κ / 2 * ((Ls : ℝ) + Es) := by
        nlinarith
      have h6 : ∑ ν : ↥(nodes F), -(lam * (zdist L (b ν - a (lastV n)) : ℝ))
          = -(lam * ∑ ν : ↥(nodes F), (zdist L (b ν - a (lastV n)) : ℝ)) := by
        rw [mul_sum, sum_neg_distrib]
      rw [h6]
      nlinarith
    rw [norm_mul, norm_prod, norm_prod]
    calc _ ≤ (B ^ n * exp (-(κ * (Ls : ℝ)))) * (B ^ F.card * exp (-(κ * (Es : ℝ)))) :=
          mul_le_mul hL hE' (prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
      _ = B ^ (n + F.card) * (exp (-(κ * (Ls : ℝ))) * exp (-(κ * (Es : ℝ)))) := by ring
      _ ≤ B ^ (n + F.card) * (exp (-(κ / 4 * zdist L (a i - a j))) * ∏ ν : ↥(nodes F), g (b ν)) :=
          by gcongr
      _ = C0 * ∏ ν : ↥(nodes F), g (b ν) := by ring
  -- sum over the labels
  have hsum : ∑ b : ↥(nodes F) → ZMod L, ∏ ν : ↥(nodes F), g (b ν) = (∑ x, g x) ^ N := by
    have h := Finset.prod_univ_sum (fun _ : ↥(nodes F) => (univ : Finset (ZMod L)))
      (fun _ x => g x)
    rw [Fintype.piFinset_univ] at h
    rw [← h, prod_const, card_univ, Fintype.card_coe]
  have hg : ∑ x, g x ≤ S := sum_exp_zdist_le L hlam _
  have hg0 : 0 ≤ ∑ x, g x := sum_nonneg fun _ _ => (exp_pos _).le
  have hC0 : 0 ≤ C0 := by positivity
  rw [treeValW]
  calc _ ≤ ∑ b : ↥(nodes F) → ZMod L, C0 * ∏ ν : ↥(nodes F), g (b ν) :=
        (norm_sum_le _ _).trans (sum_le_sum fun b _ => hpt b)
    _ = C0 * (∑ x, g x) ^ N := by rw [← mul_sum, hsum]
    _ ≤ C0 * S ^ (n * n) := by
        gcongr
        exact (pow_le_pow_left₀ hg0 hg N).trans (pow_le_pow_right₀ hS1 hN)
    _ ≤ B ^ (n + n * n) * S ^ (n * n) * exp (-(κ / 4 * zdist L (a i - a j))) := by
        have : B ^ (n + F.card) ≤ B ^ (n + n * n) := pow_le_pow_right₀ hB (by omega)
        have hS0 : 0 ≤ S ^ (n * n) := by positivity
        calc C0 * S ^ (n * n) = B ^ (n + F.card) * S ^ (n * n) *
              exp (-(κ / 4 * zdist L (a i - a j))) := by ring
          _ ≤ _ := by gcongr

end TreeBound

section Entries

variable {L : ℕ} [NeZero L]

omit [NeZero L] in
theorem half_le_ellHat (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) : 1 / 2 ≤ ellHat L ξ := by
  have h0 : 0 < ‖1 - ξ‖ := by
    have := norm_sub_norm_le (1 : ℂ) ξ; rw [norm_one] at this; linarith
  have h4 : ‖1 - ξ‖ ≤ 4 := by
    have := norm_sub_le (1 : ℂ) ξ; rw [norm_one] at this; linarith
  unfold ellHat
  refine le_min ?_ ?_
  · have hs : Real.sqrt ‖1 - ξ‖ ≤ 2 :=
      (Real.sqrt_le_sqrt h4).trans_eq
        (by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 h0) hs
  · have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    linarith

omit [NeZero L] in
theorem ellHat_le_of_gap {ξ : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδξ : δ ≤ ‖1 - ξ‖) :
    ellHat L ξ ≤ 1 / Real.sqrt δ :=
  (min_le_left _ _).trans (one_div_le_one_div_of_le (Real.sqrt_pos.2 hδ) (Real.sqrt_le_sqrt hδξ))

/-- **(2.52) with a gap**: if `δ ≤ |1 - ξ|`, the entries of `Θ_ξ` are bounded by
`(2C/δ) e^{-c √δ ‖x - y‖}`, uniformly in `L`. -/
theorem norm_Theta_apply_le_of_gap (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {δ : ℝ} (hδ : 0 < δ)
    (hδξ : δ ≤ ‖1 - ξ‖) (x y : ZMod L) :
    ‖Theta L ξ x y‖ ≤ 2 * cTwo52 / δ * exp (-(cZero * Real.sqrt δ * zdist L (x - y))) := by
  have h := norm_Theta_apply_le_complex hL hξ x y
  have hℓ := half_le_ellHat hL hξ
  have hℓ' := ellHat_le_of_gap (L := L) hδ hδξ
  have hℓ0 : 0 < ellHat L ξ := by linarith
  have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hz : (0 : ℝ) ≤ zdist L (x - y) := Nat.cast_nonneg _
  have hinv : Real.sqrt δ ≤ 1 / ellHat L ξ := by
    rw [le_div_iff₀ hℓ0]
    rw [le_div_iff₀ hsq] at hℓ'
    linarith
  have hexp : exp (-(cZero * zdist L (x - y) / ellHat L ξ))
      ≤ exp (-(cZero * Real.sqrt δ * zdist L (x - y))) := by
    apply exp_le_exp.2
    have h1 := mul_le_mul_of_nonneg_left hinv (by have := cZero_pos; positivity :
      0 ≤ cZero * (zdist L (x - y) : ℝ))
    have e1 : cZero * (zdist L (x - y) : ℝ) / ellHat L ξ
        = cZero * zdist L (x - y) * (1 / ellHat L ξ) := by ring
    have e2 : cZero * Real.sqrt δ * (zdist L (x - y) : ℝ)
        = cZero * zdist L (x - y) * Real.sqrt δ := by ring
    linarith
  have hden : δ * (1 / 2) ≤ ‖1 - ξ‖ * ellHat L ξ :=
    mul_le_mul hδξ hℓ (by norm_num) (norm_nonneg _)
  have hc := cTwo52_pos
  calc ‖Theta L ξ x y‖ ≤ _ := h
    _ ≤ cTwo52 * exp (-(cZero * Real.sqrt δ * zdist L (x - y))) / (δ * (1 / 2)) :=
        div_le_div₀ (by positivity) (by gcongr) (by positivity) hden
    _ = 2 * cTwo52 / δ * exp (-(cZero * Real.sqrt δ * zdist L (x - y))) := by
        field_simp

omit [NeZero L] in
theorem norm_one_apply_le (κ : ℝ) (x y : ZMod L) :
    ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) x y‖ ≤ exp (-(κ * zdist L (x - y))) := by
  by_cases h : x = y
  · subst h; simp
  · rw [Matrix.one_apply_ne h, norm_zero]; exact (exp_pos _).le

/-- For `t ∈ [0, T₀]`, `T₀ < 1`, the gap holds with `δ = 1 - T₀`. -/
theorem gap_of_le {m : Bool → ℂ} (hm1 : ∀ s, ‖m s‖ ≤ 1) {t T₀ : ℝ} (ht : t ∈ Set.Icc 0 T₀) :
    1 - T₀ ≤ ‖1 - (t : ℂ) * (m true * m true)‖ := by
  have hξ : ‖(t : ℂ) * (m true * m true)‖ ≤ t := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    have := mul_le_mul (hm1 true) (hm1 true) (norm_nonneg _) zero_le_one
    nlinarith [ht.1]
  have := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * (m true * m true))
  rw [norm_one] at this
  linarith [ht.2]

/-- **The edges of a pure loop decay.**  Every entry of `Θ_{t m(+)²}` and of
`Θ_{t m(+)²} - 1` is at most `(2C/δ + 1) e^{-c √δ ‖x - y‖}`. -/
theorem norm_thetaEdge_le (hL : 3 ≤ L) {m : Bool → ℂ} (hm1 : ∀ s, ‖m s‖ ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) {δ : ℝ} (hδ : 0 < δ)
    (hgap : δ ≤ ‖1 - (t : ℂ) * (m true * m true)‖) (x y : ZMod L) :
    ‖thetaEdge L m t true true x y‖ ≤
        (2 * cTwo52 / δ + 1) * exp (-(cZero * Real.sqrt δ * zdist L (x - y))) ∧
      ‖(thetaEdge L m t true true - 1) x y‖ ≤
        (2 * cTwo52 / δ + 1) * exp (-(cZero * Real.sqrt δ * zdist L (x - y))) := by
  have hξ : ‖(t : ℂ) * (m true * m true)‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    have := mul_le_mul (hm1 true) (hm1 true) (norm_nonneg _) zero_le_one
    nlinarith
  have h := norm_Theta_apply_le_of_gap hL hξ hδ hgap x y
  have h1 := norm_one_apply_le (L := L) (cZero * Real.sqrt δ) x y
  have he : 0 ≤ exp (-(cZero * Real.sqrt δ * zdist L (x - y))) := (exp_pos _).le
  unfold thetaEdge
  refine ⟨by linarith, ?_⟩
  rw [Matrix.sub_apply]
  calc _ ≤ ‖Theta L (t * (m true * m true)) x y‖ + ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) x y‖ :=
        norm_sub_le _ _
    _ ≤ _ := by linarith

end Entries

end Cor35

open Cor35

/-- The rate `c_n` of Corollary 3.5 (it does not depend on `n`). -/
noncomputable def cor35Rate (δ : ℝ) : ℝ := cZero * Real.sqrt δ / 4

/-- The constant `C_n` of Corollary 3.5: it depends on `n` and the gap `δ` only. -/
noncomputable def cor35Const (n : ℕ) (δ : ℝ) : ℝ :=
  (TSP n).card * ((2 * cTwo52 / δ + 1) ^ (n + n * n) *
    (2 / (1 - exp (-(cZero * Real.sqrt δ / (2 * ((n * n : ℕ) : ℝ)))))) ^ (n * n))

section Main

variable {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ)
  (hm1 : ∀ s, ‖m s‖ ≤ 1) {T₀ : ℝ} (hT₀ : T₀ < 1)
include hL hm1 hT₀

/-- **Corollary 3.5 (Pure loop `K`)**, (3.6): for `σ = (+, …, +)` and `n ≥ 3`,
`|K_{t,σ,a}| ≤ C_n e^{-c ‖a_i - a_j‖}` for every pair `i, j`, i.e.
`≤ C_n e^{-c max_{ij} ‖a_i - a_j‖}`.  The constants depend only on `n` and the gap `δ`
(`δ ≤ |1 - t m(+)²|`), not on `L`, `W`, `t` or `a`. -/
theorem cor35 {T : Set ℝ} {K : ℝ → LoopIdx (ZMod L) → ℂ}
    (hK : IsPrimitive L W m T K) (hT : Set.Icc 0 T₀ ⊆ T) {R : ℝ}
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ t ∈ Set.Icc 0 T₀, δ ≤ ‖1 - (t : ℂ) * (m true * m true)‖)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T₀) (I : LoopIdx (ZMod L)) (hI : I.WF) {n : ℕ} (hn : 3 ≤ n)
    (hlen : I.length = n) (hσ : I.σ = List.replicate n true) {i j : ℕ} (hi : i < n)
    (hj : j < n) :
    ‖K t I‖ ≤ cor35Const n δ * exp (-(cor35Rate δ * zdist L (I.a.getD i 0 - I.a.getD j 0))) := by
  have h3 : 3 ≤ I.length := hlen ▸ hn
  have hrep := treeRep_general hL W m hm1 hT₀ hK hT hR ht I hI h3
  have : NeZero I.length := ⟨by omega⟩
  rw [hrep]
  have hκ : 0 < cZero * Real.sqrt δ := mul_pos cZero_pos (Real.sqrt_pos.2 hδ)
  have hB : 1 ≤ 2 * cTwo52 / δ + 1 := by
    have := cTwo52_pos
    have : 0 ≤ 2 * cTwo52 / δ := by positivity
    linarith
  have hσ' : ∀ k : Fin I.length, I.σ.getD k false = true := fun k => by
    rw [hσ]; exact List.getD_replicate (x := true) (by have := k.isLt; omega)
  have hedge := norm_thetaEdge_le hL hm1 ht.1 (lt_of_le_of_lt ht.2 hT₀) hδ (hgap t ht)
  set X := (2 * cTwo52 / δ + 1) ^ (I.length + I.length * I.length) *
    (2 / (1 - exp (-(cZero * Real.sqrt δ / (2 * ((I.length * I.length : ℕ) : ℝ)))))) ^
      (I.length * I.length) *
    exp (-(cZero * Real.sqrt δ / 4 * zdist L (I.a.getD i 0 - I.a.getD j 0)))
  have htree : ∀ F ∈ TSP I.length,
      ‖treeValG L m t (fun k => I.σ.getD k false) (fun k => I.a.getD k 0) F‖ ≤ X := by
    intro F hF
    refine norm_treeValW_le (isTSP_of_mem_TSP hF) (by omega) _ _ _ hB hκ
      (fun v x y => ?_) (fun d x y => ?_) ⟨i, by omega⟩ ⟨j, by omega⟩
    · simp only [hσ']; exact (hedge x y).1
    · simp only [hσ']; exact (hedge x y).2
  have hprod : ‖(I.σ.map m).prod‖ ≤ 1 := by
    rw [hσ, List.map_replicate, List.prod_replicate, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hm1 true)
  have hW : ‖(W : ℂ)⁻¹ ^ (I.length - 1)‖ ≤ 1 := by
    rw [norm_pow, norm_inv, Complex.norm_natCast]
    have : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ this)
  have hX : 0 ≤ X := by
    have := one_le_two_div (lam := cZero * Real.sqrt δ / (2 * ((I.length * I.length : ℕ) : ℝ)))
      (by have : (0 : ℝ) < ((I.length * I.length : ℕ) : ℝ) := by positivity
          positivity)
    positivity
  have hsum : ‖∑ F ∈ TSP I.length,
      treeValG L m t (fun k => I.σ.getD k false) (fun k => I.a.getD k 0) F‖
      ≤ (TSP I.length).card * X := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum htree).trans ?_
    rw [sum_const, nsmul_eq_mul]
  rw [norm_mul, norm_mul]
  calc _ ≤ 1 * 1 * ((TSP I.length).card * X) := by
        gcongr
    _ = cor35Const n δ * exp (-(cor35Rate δ * zdist L (I.a.getD i 0 - I.a.getD j 0))) := by
        simp only [X, cor35Const, cor35Rate]
        rw [hlen]
        ring

/-- **Corollary 3.5 at `n = 2`**: here `K = W⁻¹ m(+)² (Θ_{t m(+)²})_{a₁a₂}` (Example 2.15),
and (3.6) is (2.52) with the gap. -/
theorem cor35_two {T : Set ℝ} {K : ℝ → LoopIdx (ZMod L) → ℂ}
    (hK : IsPrimitive L W m T K) (hT : Set.Icc 0 T₀ ⊆ T) {R : ℝ}
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ t ∈ Set.Icc 0 T₀, δ ≤ ‖1 - (t : ℂ) * (m true * m true)‖)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T₀) (I : LoopIdx (ZMod L)) (hI : I.WF) (hlen : I.length = 2)
    (hσ : I.σ = [true, true]) :
    ‖K t I‖ ≤ 2 * cTwo52 / δ *
      exp (-(cZero * Real.sqrt δ * zdist L (I.a.getD 0 0 - I.a.getD 1 0))) := by
  rw [eq_Kgen_of_isPrimitive hL W m hm1 hT₀ hK hT hR t ht I hI (by omega)]
  simp only [Kgen, hlen, hσ, (by decide : ¬(2 : ℕ) = 1), ↓reduceIte, List.getD_cons_zero,
    List.getD_cons_succ]
  have hξ : ‖(t : ℂ) * (m true * m true)‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    have := mul_le_mul (hm1 true) (hm1 true) (norm_nonneg _) zero_le_one
    nlinarith [ht.1, ht.2, hT₀]
  have hΘ := norm_Theta_apply_le_of_gap hL hξ hδ (hgap t ht) (I.a.getD 0 0) (I.a.getD 1 0)
  have hW : ‖(W : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W))
  have hmm : ‖m true * m true‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hm1 true) (hm1 true) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  unfold kTwo
  rw [norm_mul, norm_mul]
  calc _ ≤ 1 * 1 * ‖Theta L (t * (m true * m true)) (I.a.getD 0 0) (I.a.getD 1 0)‖ := by
        gcongr
    _ ≤ _ := by rw [one_mul, one_mul]; exact hΘ

end Main

end RBM
