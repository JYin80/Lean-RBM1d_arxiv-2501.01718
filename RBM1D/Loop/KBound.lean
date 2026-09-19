/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.SumZero
import RBM1D.Propagator.LongDiff

/-!
# Lemma 3.11: the bound on `K^(π)`

Paper pp.41, 45–48.

**(3.43)**, the short-range property of the single-molecule self-energy: for `π = ∅` every
internal edge joins equal charges, so it is a short edge `Θ_{t m²} - 1`, which decays
exponentially on the scale of the bulk gap `|1 - t m²| ≥ √k`.  The self-energy is the tree value
with *identity* boundary edges (`selfW_eq_treeValW_one`), so the tree bound of Corollary 3.5
applies verbatim (`norm_SigmaPi_empty_le`).
-/

namespace RBM

open Finset Cor35

section SelfDecay

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- The self-energy is the tree value with identity boundary edges. -/
theorem selfW_eq_treeValW_one (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ)
    (d : Fin n → ZMod L) :
    selfW L F E d = treeValW L F d (fun _ => 1) E := by
  simp only [selfW, treeValW, Matrix.one_apply]

variable (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2)
include hL hE

/-- The internal edges of a single-molecule tree (`π = ∅`) are short: both ends carry the same
charge, and the edge `Θ_{t m(s)²} - 1` decays on the scale of the bulk gap. -/
theorem norm_selfEdge_le {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (s : Bool) (x y : ZMod L) :
    ‖(thetaEdge L (mSigma E) t s s - 1) x y‖ ≤
      (2 * cTwo52 / Real.sqrt k + 1) *
        Real.exp (-(cZero * Real.sqrt (Real.sqrt k) * zdist L (x - y))) := by
  have hm1 := norm_mSigma_le_one hE
  let m' : Bool → ℂ := fun b => mSigma E (if b then s else !s)
  have hm1' : ∀ b, ‖m' b‖ ≤ 1 := fun b => hm1 _
  have hgap' : Real.sqrt k ≤ ‖1 - (t : ℂ) * (m' true * m' true)‖ := by
    simp only [m', ite_true]
    exact gap_mSigma hk0 hk1 hEk ht0 ht1.le s
  have h := (norm_thetaEdge_le hL hm1' ht0 ht1 (Real.sqrt_pos.2 hk0) hgap' x y).2
  have e : thetaEdge L (mSigma E) t s s = thetaEdge L m' t true true := by
    simp only [thetaEdge, m', ite_true]
  rw [e]
  exact h

/-- **(3.43)**: the single-molecule self-energy is short-ranged,
`|Σ^(∅)(t,σ,d)| ≤ C e^{-c ‖d_i - d_j‖}` for every pair `i, j`, with `C, c` depending only on `n`
and the bulk parameter `k` (`|E| ≤ 2 - k`), uniformly in `L` and `0 ≤ t < 1`. -/
theorem norm_SigmaPi_empty_le {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (σ : Fin n → Bool) (hn : 2 ≤ n) (d : Fin n → ZMod L)
    (i j : Fin n) :
    ‖SigmaPi L (mSigma E) t σ ∅ d‖ ≤
      cor35Const n (Real.sqrt k) *
        Real.exp (-(cor35Rate (Real.sqrt k) * zdist L (d i - d j))) := by
  set δ := Real.sqrt k with hδdef
  have hδ : 0 < δ := Real.sqrt_pos.2 hk0
  have hκ : 0 < cZero * Real.sqrt δ := mul_pos cZero_pos (Real.sqrt_pos.2 hδ)
  have hB : 1 ≤ 2 * cTwo52 / δ + 1 := by
    have := cTwo52_pos
    have : 0 ≤ 2 * cTwo52 / δ := by positivity
    linarith
  set X := (2 * cTwo52 / δ + 1) ^ (n + n * n) *
    (2 / (1 - Real.exp (-(cZero * Real.sqrt δ / (2 * ((n * n : ℕ) : ℝ)))))) ^ (n * n) *
    Real.exp (-(cZero * Real.sqrt δ / 4 * zdist L (d i - d j)))
  have hF : ∀ F ∈ TSPlong n σ ∅, ‖selfE L (mSigma E) t σ F d‖ ≤ X := by
    intro F hF
    obtain ⟨hFT, hFl⟩ := mem_TSPlong.1 hF
    rw [selfE, selfW_eq_treeValW_one]
    refine norm_treeValW_le (isTSP_of_mem_TSP hFT) hn d _ _ hB hκ (fun v x y => ?_)
      (fun e x y => ?_) i j
    · exact (norm_one_apply_le _ x y).trans (le_mul_of_one_le_left (Real.exp_pos _).le hB)
    · have hs : σ e.1.1 = σ e.1.2 := by
        by_contra hne
        have : e.1 ∈ Flong F σ := mem_Flong.2 ⟨e.2, hne⟩
        rw [hFl] at this
        simp at this
      rw [← hs]
      exact norm_selfEdge_le hL hE hk0 hk1 hEk ht0 ht1 _ x y
  have hX : 0 ≤ X := by
    have := one_le_two_div (lam := cZero * Real.sqrt δ / (2 * ((n * n : ℕ) : ℝ)))
      (by have : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by
            have := NeZero.pos n; exact_mod_cast Nat.mul_pos this this
          have := cZero_pos
          positivity)
    positivity
  have hcard : ((TSPlong n σ ∅).card : ℝ) ≤ (TSP n).card := by
    exact_mod_cast card_le_card (TSPlong_subset σ ∅)
  calc ‖SigmaPi L (mSigma E) t σ ∅ d‖
      ≤ ∑ F ∈ TSPlong n σ ∅, ‖selfE L (mSigma E) t σ F d‖ := norm_sum_le _ _
    _ ≤ ∑ _F ∈ TSPlong n σ ∅, X := sum_le_sum hF
    _ = (TSPlong n σ ∅).card * X := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (TSP n).card * X := by gcongr
    _ = _ := by simp only [X, cor35Const, cor35Rate]; ring

end SelfDecay

end RBM
