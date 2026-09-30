/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma41FlowGauss

/-!
# The loop hypothesis of Lemma 4.1 along the flow, at an `N`-dependent energy

The predicate `RBM.Gauss.LoopHypFlowN` (a bound `Φ` on `Lre` on the event `Step1.goodEv`) and
three consequences at an `N`-dependent energy `E : ℕ → ℝ`: its restatement through the
`(+,-)` 2-loops (`RBM.Gauss.loopHypFlow_iffN`), the bound on `Lmax`
(`RBM.Gauss.stochDom_indicator_Lmax_flowN`) and the bound on the entry control
(`RBM.Gauss.stochDom_indicator_entryControl_flowN`).

None of them fixes an energy-dependent constant: none of the theorems takes a bound on `E` at all
(the argument is purely combinatorial, at a fixed `(N, ω)`), and the definition of
`LoopHypFlowN` carries no fixed constant either.
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset

variable {d : Dims} {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-! ### The predicate `LoopHypFlowN` -/

variable {Φ : ∀ N, RBM.TimeIcc s t N → ℝ}

/-- **The loop hypothesis along the flow**: `1_{goodEv} Lre(G_u)_{ab} ≺ Φ_u`, uniformly in
`u ∈ [s, t]` and `a, b`. No energy-dependent constant is fixed here (only the events
`Step1.goodEv`/`Lre` are threaded through). -/
abbrev LoopHypFlowN (d : Dims) (E : ℕ → ℝ) (s t : ℕ → ℝ) (Φ : ∀ N, RBM.TimeIcc s t N → ℝ) : Prop :=
  StochDom (P d)
    (fun N (p : RBM.TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) ω =>
      (Step1.goodEv (sample d) (E N) N (p.1 : ℝ)).indicator
        (fun ω => Lre (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) p.2.1 p.2.2) ω)
    (fun N p _ => Φ N p.1)

/-- **`LoopHypFlowN` in terms of the `(+,-)` 2-loops**: equivalently,
`1_{goodEv} |L_{u,(+,-),(a,b)}| ≺ Φ_u`. -/
theorem loopHypFlow_iffN :
    LoopHypFlowN d E s t Φ ↔ StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) ω =>
        (Step1.goodEv (sample d) (E N) N (p.1 : ℝ)).indicator
          (fun ω => ‖(sample d).Lval (E N) N (p.1 : ℝ) ω (pmLoop p.2.1 p.2.2)‖) ω)
      (fun N p _ => Φ N p.1) := by
  have h : ∀ (N : ℕ) (u : ℝ) (ab : ZMod (d.L N) × ZMod (d.L N)) (ω : Ω d),
      ‖(sample d).Lval (E N) N u ω (pmLoop ab.1 ab.2)‖
        = Lre (Hflow d N u ω) (zt (E N) u) ab.1 ab.2 := fun N u ab ω =>
    sample_Lval_pm (E N) N u ω ab.1 ab.2
  constructor <;> intro hh <;> simpa only [h] using hh

/-- **`1_{goodEv} Lmax ≺ Φ`** from `LoopHypFlowN`. -/
theorem stochDom_indicator_Lmax_flowN {V : ℕ → Type*} (hΦ0 : ∀ N u, 0 ≤ Φ N u)
    (hΦ : LoopHypFlowN d E s t Φ) :
    StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × V N) ω =>
        (Step1.goodEv (sample d) (E N) N (p.1 : ℝ)).indicator
          (fun ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ))) ω)
      (fun N p _ => Φ N p.1) := by
  refine StochDom.of_subset_union hΦ hΦ fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards with N
  intro ω hω
  refine Set.mem_union_left _ ?_
  simp only [badSet, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨p, hlt⟩ := hω
  by_cases hmem : ω ∈ Step1.goodEv (sample d) (E N) N (p.1 : ℝ)
  · rw [Set.indicator_of_mem hmem] at hlt
    obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty)
      (fun q : ZMod (d.L N) × ZMod (d.L N) =>
        Lre (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) q.1 q.2)
    unfold Lmax at hlt
    rw [hq] at hlt
    exact ⟨(p.1, q), by rw [Set.indicator_of_mem hmem]; exact hlt⟩
  · rw [Set.indicator_of_notMem hmem] at hlt
    exact absurd hlt (not_lt.2
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) τ) (hΦ0 N p.1)))

/-- **The entry control is at most `Φ + W⁻¹` on `goodEv`**: the sum of `Lre` over the
`S`-neighbourhoods of the two blocks, plus `W⁻¹` when the blocks are `S`-adjacent, is dominated
by `Φ + W⁻¹`, from `LoopHypFlowN`. -/
theorem stochDom_indicator_entryControl_flowN (hΦ0 : ∀ N u, 0 ≤ Φ N u)
    (hΦ : LoopHypFlowN d E s t Φ) :
    StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
        (Step1.goodEv (sample d) (E N) N (p.1 : ℝ)).indicator
          (fun ω => (∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
              Lre (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) (p.2.1.2.1 + b) (p.2.1.1.1 + a))
            + if p.2.1.1.1 - p.2.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) := by
  refine StochDom.of_subset_union hΦ hΦ fun τ hτ => ⟨τ / 2, by linarith, ?_⟩
  filter_upwards [eventually_le_rpow 9 (show (0:ℝ) < τ / 2 by linarith),
    Filter.eventually_ge_atTop 1] with N h9 hN1
  intro ω hω
  refine Set.mem_union_left _ ?_
  simp only [badSet, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨p, hlt⟩ := hω
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hW : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  have hτ1 : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1' hτ.le
  have hτ2 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' (by linarith)
  by_cases hmem : ω ∈ Step1.goodEv (sample d) (E N) N (p.1 : ℝ)
  · rw [Set.indicator_of_mem hmem] at hlt
    have hite : (if p.2.1.1.1 - p.2.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        ≤ (N : ℝ) ^ τ * ((d.W N : ℕ) : ℝ)⁻¹ := by
      split_ifs
      · nlinarith [hW, hτ1]
      · positivity
    have hsum : (N : ℝ) ^ τ * Φ N p.1
        < ∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
            Lre (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) (p.2.1.2.1 + b) (p.2.1.1.1 + a) := by
      nlinarith [hlt, hite]
    have h9M := sum_sum_Lre_le d N (E N) (p.1 : ℝ) ω p.2.1.1.1 p.2.1.2.1
    have hM : 0 ≤ Lmax (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) :=
      Lmax_nonneg (Hflow_isHermitian d N (p.1 : ℝ) ω)
    have hkey : (N : ℝ) ^ (τ / 2) * Φ N p.1
        < Lmax (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) := by
      have hsplit : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
        rw [← Real.rpow_add hN0]; congr 1; ring
      nlinarith [hsum, h9M, h9, hΦ0 N p.1, hτ2]
    obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty)
      (fun q : ZMod (d.L N) × ZMod (d.L N) =>
        Lre (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) q.1 q.2)
    unfold Lmax at hkey
    rw [hq] at hkey
    exact ⟨(p.1, q), by rw [Set.indicator_of_mem hmem]; exact hkey⟩
  · rw [Set.indicator_of_notMem hmem] at hlt
    exfalso
    have : (0 : ℝ) ≤ (N : ℝ) ^ τ * (Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) := by
      have h1 : (0 : ℝ) ≤ Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹ := by linarith [hΦ0 N p.1]
      positivity
    linarith [hlt]

end RBM.Gauss
