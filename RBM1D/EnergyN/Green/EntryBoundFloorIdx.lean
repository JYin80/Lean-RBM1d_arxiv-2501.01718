/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Green.EntryBoundFloor

/-!
# Lemma 4.1, (4.2), with a floor and the time inside the index set, `N`-dependent parameters

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 4.1, (4.2).

`RBM.entry_bound_stochDom_floor_idxN`: the entry bound (4.2) of Lemma 4.1, with an additive floor
and the time inside the index set, where the spectral-parameter map `zf : ℕ → ℝ → ℂ` and the
reference value `m : ℕ → ℂ` (`hm : ∀ N, ‖m N‖ = 1`) depend on `N`. They enter only through the
deterministic kernel `RBM.norm_sq_green_le_blk_floor`, applied after `N` is bound, and every
constant of the proof (`1/2`, `81`, `2`) is absolute.
-/

namespace RBM

open Filter MeasureTheory Finset

section RandomModelFloorIdxN

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
variable {L W : ℕ → ℕ} [∀ N, NeZero (L N)] [∀ N, NeZero (W N)]

/-- **Lemma 4.1, (4.2), with an additive floor, the time inside the index set, and an
`N`-dependent spectral parameter and reference value.** -/
theorem entry_bound_stochDom_floor_idxN {U : ℕ → Type*} (hL : ∀ N, 3 ≤ L N)
    (Hf : ∀ N, ℝ → Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ)
    (uf : ∀ N, U N → ℝ) (zf : ℕ → ℝ → ℂ) (hH : ∀ N u ω, (Hf N u ω).IsHermitian)
    (hz : ∀ N (q : U N), (zf N (uf N q)).im ≠ 0) {m : ℕ → ℂ} (hm : ∀ N, ‖m N‖ = 1)
    {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) {fl : ℕ → ℝ} (hfl0 : ∀ N, 0 ≤ fl N)
    (hLrow : StochDom P
      (fun N (q : U N × OffPair L W N) ω =>
        ldeRowLHS (Hf N (uf N q.1) ω) (green (Hf N (uf N q.1) ω) (zf N (uf N q.1)))
          q.2.1.1 q.2.1.2)
      (fun N q ω =>
        ldeRowRHS (Sblk (L N) (W N)) (green (Hf N (uf N q.1) ω) (zf N (uf N q.1)))
          q.2.1.1 q.2.1.2 + fl N))
    (hLcol : StochDom P
      (fun N (q : U N × OffPair L W N) ω =>
        ldeColLHS (Hf N (uf N q.1) ω) (green (Hf N (uf N q.1) ω) (zf N (uf N q.1)))
          q.2.1.1 q.2.1.2)
      (fun N q ω =>
        ldeColRHS (Sblk (L N) (W N)) (green (Hf N (uf N q.1) ω) (zf N (uf N q.1)))
          q.2.1.1 q.2.1.2 + fl N)) :
    StochDom P
      (fun N (q : U N × OffPair L W N) ω =>
        Set.indicator {ω | GoodEvent (green (Hf N (uf N q.1) ω) (zf N (uf N q.1))) (m N) (δ N)}
          (fun ω => ‖green (Hf N (uf N q.1) ω) (zf N (uf N q.1)) q.2.1.1 q.2.1.2‖ ^ 2) ω)
      (fun N q ω =>
        (∑ a ∈ sbSupport (L N), ∑ b ∈ sbSupport (L N),
            Lre (Hf N (uf N q.1) ω) (zf N (uf N q.1)) (q.2.1.2.1 + b) (q.2.1.1.1 + a))
          + (if q.2.1.1.1 - q.2.1.2.1 ∈ sbSupport (L N) then ((W N : ℕ) : ℝ)⁻¹ else 0)
          + 2 * fl N) := by
  refine StochDom.of_det (hLrow.sumElim hLcol) ?_ hδ0 hc₀ hδ
    (by norm_num : (0 : ℝ) < 1 / 2) 81 2 ?_
  · intro N q ω
    have h1 : 0 ≤ ∑ a ∈ sbSupport (L N), ∑ b ∈ sbSupport (L N),
        Lre (Hf N (uf N q.1) ω) (zf N (uf N q.1)) (q.2.1.2.1 + b) (q.2.1.1.1 + a) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Lre_nonneg (hH N (uf N q.1) ω) _ _
    have h2 : (0 : ℝ) ≤
        if q.2.1.1.1 - q.2.1.2.1 ∈ sbSupport (L N) then ((W N : ℕ) : ℝ)⁻¹ else 0 := by
      split_ifs <;> positivity
    have h3 := hfl0 N
    linarith
  · intro N ω Φ hΦ1 hΦδ hδε hAB q
    have hflN := hfl0 N
    by_cases hω : ω ∈ {ω | GoodEvent (green (Hf N (uf N q.1) ω) (zf N (uf N q.1))) (m N) (δ N)}
    · rw [Set.indicator_of_mem hω]
      have hLr : LDERowFloor (Hf N (uf N q.1) ω)
          (green (Hf N (uf N q.1) ω) (zf N (uf N q.1))) (Sblk (L N) (W N)) Φ (fl N) :=
        fun i j hij => hAB (Sum.inl (q.1, ⟨(i, j), hij⟩))
      have hLc : LDEColFloor (Hf N (uf N q.1) ω)
          (green (Hf N (uf N q.1) ω) (zf N (uf N q.1))) (Sblk (L N) (W N)) Φ (fl N) :=
        fun k j hkj => hAB (Sum.inr (q.1, ⟨(k, j), hkj⟩))
      exact norm_sq_green_le_blk_floor (L N) (hL N) (hH N (uf N q.1) ω) (hz N q.1) (hm N) hω
        hδε hΦ1 hΦδ hflN hLr hLc q.2.2
    · rw [Set.indicator_of_notMem hω]
      have h1 : 0 ≤ ∑ a ∈ sbSupport (L N), ∑ b ∈ sbSupport (L N),
          Lre (Hf N (uf N q.1) ω) (zf N (uf N q.1)) (q.2.1.2.1 + b) (q.2.1.1.1 + a) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          Lre_nonneg (hH N (uf N q.1) ω) _ _
      have h2 : (0 : ℝ) ≤
          if q.2.1.1.1 - q.2.1.2.1 ∈ sbSupport (L N) then ((W N : ℕ) : ℝ)⁻¹ else 0 := by
        split_ifs <;> positivity
      have hΦ0 : 0 ≤ Φ := by linarith
      positivity

end RandomModelFloorIdxN

end RBM
