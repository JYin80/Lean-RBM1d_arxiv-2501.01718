/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Green.EntryBoundFloor

/-!
# Lemma 4.1, (4.3), with a floor and the time inside the index set, at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 4.1, (4.3).

`RBM.diag_bound_stochDom_floor_idxN`: the diagonal bound (4.3) of Lemma 4.1, with an additive
floor and the time inside the index set, at an energy `E : ℕ → ℝ` with
`hE : ∀ N, |E N| ≤ 2 - κ`. The margin `κ` is explicit, so no energy-dependent constant is fixed
before `N`.
-/

namespace RBM

open Filter MeasureTheory Finset

section RandomModelFloorN

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
variable {L W : ℕ → ℕ} [∀ N, NeZero (L N)] [∀ N, NeZero (W N)]

/-- **Lemma 4.1, (4.3), with an additive floor, the time inside the index set, and an
`N`-dependent energy.** -/
theorem diag_bound_stochDom_floor_idxN {U : ℕ → Type*} (hL : ∀ N, 3 ≤ L N)
    (Hf : ∀ N, ℝ → Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ)
    (uf : ∀ N, U N → ℝ) (hH : ∀ N u ω, (Hf N u ω).IsHermitian)
    {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : ∀ N, |E N| ≤ 2 - κ)
    (ht0 : ∀ N q, 0 ≤ uf N q) (ht1 : ∀ N q, uf N q < 1)
    {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) {fl : ℕ → ℝ} (hfl0 : ∀ N, 0 ≤ fl N)
    (hLrow : StochDom P
      (fun N (q : U N × OffPair L W N) ω =>
        ldeRowLHS (Hf N (uf N q.1) ω) (green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1)))
          q.2.1.1 q.2.1.2)
      (fun N q ω =>
        ldeRowRHS (Sblk (L N) (W N)) (green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1)))
          q.2.1.1 q.2.1.2 + fl N))
    (hLcol : StochDom P
      (fun N (q : U N × OffPair L W N) ω =>
        ldeColLHS (Hf N (uf N q.1) ω) (green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1)))
          q.2.1.1 q.2.1.2)
      (fun N q ω =>
        ldeColRHS (Sblk (L N) (W N)) (green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1)))
          q.2.1.1 q.2.1.2 + fl N))
    (hLquad : StochDom P
      (fun N (q : U N × BIdx L W N) ω =>
        ldeQuadLHS (Hf N (uf N q.1) ω) (green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1)))
          (Sblk (L N) (W N)) (uf N q.1) q.2)
      (fun N q ω =>
        ldeQuadRHS (Sblk (L N) (W N)) (green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1))) q.2
          + fl N))
    (hLdiag : StochDom P
      (fun N (q : U N × BIdx L W N) ω => ‖Hf N (uf N q.1) ω q.2 q.2‖ ^ 2)
      (fun N (q : U N × BIdx L W N) _ => Sblk (L N) (W N) q.2 q.2)) :
    StochDom P
      (fun N (q : U N × BIdx L W N) ω =>
        Set.indicator
          {ω | GoodEvent (green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1))) (mE (E N)) (δ N)}
          (fun ω => ‖green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1)) q.2 q.2 - mE (E N)‖ ^ 2) ω)
      (fun N q ω => Lmax (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1)) + fl N) := by
  have hK1 : 1 ≤ Kstab κ := one_le_Kstab
  have hK0 : 0 < Kstab κ := by linarith
  have hε₀ : (0 : ℝ) < 1 / (2 * Kstab κ) := by positivity
  refine StochDom.of_det (((hLrow.sumElim hLcol).sumElim hLquad).sumElim hLdiag)
    (fun N q ω => by
      have := Lmax_nonneg (z := zt (E N) (uf N q.1)) (hH N (uf N q.1) ω)
      have := hfl0 N
      linarith)
    hδ0 hc₀ hδ hε₀ (8280 * Kstab κ ^ 2) 2 ?_
  intro N ω Φ hΦ1 hΦδ hδε hAB q
  have hL0 := Lmax_nonneg (z := zt (E N) (uf N q.1)) (hH N (uf N q.1) ω)
  have hflN := hfl0 N
  by_cases hω : ω ∈
      {ω | GoodEvent (green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1))) (mE (E N)) (δ N)}
  · rw [Set.indicator_of_mem hω]
    have hδ12 : δ N ≤ 1 / 2 := by
      refine hδε.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hKδ : Kstab κ * δ N ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hδε hK0.le
      rwa [show Kstab κ * (1 / (2 * Kstab κ)) = 1 / 2 by field_simp] at this
    have hLr : LDERowFloor (Hf N (uf N q.1) ω)
        (green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1))) (Sblk (L N) (W N)) Φ (fl N) :=
      fun i j hij => hAB (Sum.inl (Sum.inl (Sum.inl (q.1, ⟨(i, j), hij⟩))))
    have hLc : LDEColFloor (Hf N (uf N q.1) ω)
        (green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1))) (Sblk (L N) (W N)) Φ (fl N) :=
      fun k j hkj => hAB (Sum.inl (Sum.inl (Sum.inr (q.1, ⟨(k, j), hkj⟩))))
    have hLq : LDEQuadFloor (Hf N (uf N q.1) ω)
        (green (Hf N (uf N q.1) ω) (zt (E N) (uf N q.1))) (Sblk (L N) (W N))
        (uf N q.1) Φ (fl N) :=
      fun i => hAB (Sum.inl (Sum.inr (q.1, i)))
    have hLd : ∀ i, ‖Hf N (uf N q.1) ω i i‖ ^ 2 ≤ Φ * Sblk (L N) (W N) i i :=
      fun i => hAB (Sum.inr (q.1, i))
    exact norm_sq_green_diag_sub_le_blk_floor (L N) (hL N) (hH N (uf N q.1) ω) hκ0 hκ1 (hE N)
      (ht0 N q.1) (ht1 N q.1) hω hδ12 hΦ1 hΦδ hKδ hflN hLr hLc hLq hLd q.2
  · rw [Set.indicator_of_notMem hω]
    have hΦ0 : 0 ≤ Φ := by linarith
    positivity

end RandomModelFloorN

end RBM
