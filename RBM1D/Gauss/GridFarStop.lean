/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Plain

/-!
# The far stopping index `gridTauFar`

`thrFar` and `gridTauFar` are the far-field stopping level `N^{δ'}(η_s/η_u)^{13/4}` (the level of
the stopping time `T'` of the second pass after (5.48)) and the grid stopping time built from
it (the `gridTau` shape of `GridGoodEvent.lean`, with `Step2.thr → thrFar`).  `thrFar_le_thr'`
compares the far level with `Step2.thr`, and `gridTauFar_le_gridTau` compares the two stopping
indices.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## `thrFar`, `gridTauFar` and their stopping-time facts -/

/-- **A1**: the second-pass level `N^{δ′}(η_s/η_u)^{13/4}` — not (5.43)'s `N^δ(η_s/η_u)^4`. -/
noncomputable def thrFar (E : ℝ) (s : ℕ → ℝ) (δ' : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ δ' * (etaT E (s N) / etaT E u) ^ ((13 : ℝ) / 4)

variable (d : Dims)

/-- **A1**: `T′ = min{u_j : J*_{u_j,D} ≥ N^{δ′} r_{u_j}^{13/4}}` on the grid (∧ goodSet failure,
exactly as `gridTau`, `GridGoodEvent.lean`, with `Step2.thr` replaced by `thrFar`). -/
noncomputable def gridTauFar (E D δ' τ₁ ε ζCtr τ3 τ57 : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (ω : Ωg d) : ℕ :=
  min (firstHit (fun j (ω : Ωg d) => jSMat d E D N (time s u K N j) (H d s u K N j ω)
      - thrFar E s δ' N (time s u K N j)) 0 (K N) ω)
    (firstHit (fun j (ω : Ωg d) =>
      (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D)ᶜ.indicator
        (fun _ => (1 : ℝ)) (H d s u K N j ω)) (1 / 2) (K N) ω)

variable {d}

/-- `{j < gridTauFar}` is `filt d j`-measurable, from `lt_min_firstHit_grid_measurableSet`
(`GridStopFilt.lean`) with `measurable_jSMat` and the `goodSet` measurability. -/
theorem lt_gridTauFar_measurableSet {E : ℝ} (hE : |E| < 2) (D δ' τ₁ ε ζCtr τ3 τ57 : ℝ)
    (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (j : ℕ) :
    MeasurableSet[filt d j] {ω | j < gridTauFar d E D δ' τ₁ ε ζCtr τ3 τ57 s u K N ω} :=
  lt_min_firstHit_grid_measurableSet d s u K N
    (F := fun j M => jSMat d E D N (time s u K N j) M - thrFar E s δ' N (time s u K N j))
    (F' := fun j M => (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57
      D)ᶜ.indicator (fun _ => (1 : ℝ)) M)
    (fun _ => (measurable_jSMat d E D N _).sub measurable_const)
    (fun _ => measurable_const.indicator
      (measurableSet_goodSet d E N _ _ τ₁ ε ζCtr τ3 τ57 D hE).compl)
    0 (1 / 2) (K N) j

/-- `gridTauFar ≤ K N`. -/
theorem gridTauFar_le (E D δ' τ₁ ε ζCtr τ3 τ57 : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (ω : Ωg d) : gridTauFar d E D δ' τ₁ ε ζCtr τ3 τ57 s u K N ω ≤ K N :=
  (min_le_left _ _).trans (firstHit_le _ _ _ ω)

/-- Strictly before `gridTauFar`, `J*` is below the far threshold and the grid state is in the
good set. -/
theorem lt_gridTauFar_imp {E D δ' τ₁ ε ζCtr τ3 τ57 : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ}
    {ω : Ωg d} (h : j < gridTauFar d E D δ' τ₁ ε ζCtr τ3 τ57 s u K N ω) :
    jSMat d E D N (time s u K N j) (H d s u K N j ω) < thrFar E s δ' N (time s u K N j) ∧
      H d s u K N j ω ∈
        goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D := by
  obtain ⟨h1, h2⟩ := lt_min_firstHit_imp _ _ _ _ _ h
  refine ⟨by linarith, ?_⟩
  by_contra hmem
  have h2' : (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D)ᶜ.indicator
      (fun _ => (1 : ℝ)) (H d s u K N j ω) < 1 / 2 := h2
  rw [Set.indicator_of_mem (Set.mem_compl hmem)] at h2'
  norm_num at h2'

/-! ## A generic monotonicity fact for `firstHit` -/

/-- If `J ≤ J'` pointwise on `[0, K]`, the (pointwise larger) process `J'` reaches any threshold
`θ` no later than `J` does. Reuses Mathlib's `hittingBtwn_mem_set_of_hittingBtwn_lt` and
`hittingBtwn_le_of_mem`. -/
theorem firstHit_le_of_le {Ω' : Type*} {J J' : ℕ → Ω' → ℝ} {θ : ℝ} {K : ℕ} {ω : Ω'}
    (h : ∀ j ≤ K, J j ω ≤ J' j ω) : firstHit J' θ K ω ≤ firstHit J θ K ω := by
  by_cases hK : firstHit J θ K ω = K
  · rw [hK]; exact firstHit_le J' θ K ω
  · have hlt : firstHit J θ K ω < K := lt_of_le_of_ne (firstHit_le J θ K ω) hK
    have hmem : J (firstHit J θ K ω) ω ∈ Set.Ici θ :=
      MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt (u := J) (s := Set.Ici θ) (n := 0) hlt
    have hmem' : J' (firstHit J θ K ω) ω ∈ Set.Ici θ := by
      rw [Set.mem_Ici] at hmem ⊢
      exact hmem.trans (h _ (firstHit_le J θ K ω))
    exact MeasureTheory.hittingBtwn_le_of_mem (u := J') (s := Set.Ici θ) (n := 0)
      (Nat.zero_le _) (firstHit_le J θ K ω) hmem'

/-! ## Comparison with the near-field stopping time -/

/-- `thrFar ≤ Step2.thr`: `13/4 ≤ 4` and the ratio `η_s/η_u ≥ 1` for `s ≤ u < 1`. -/
theorem thrFar_le_thr' {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ} {δ : ℝ} {N : ℕ} {u : ℝ}
    (hsu : s N ≤ u) (hu1 : u < 1) : thrFar E s δ N u ≤ Step2.thr E s δ N u := by
  have hr : (1 : ℝ) ≤ etaT E (s N) / etaT E u := by
    rw [Step2.etaT_ratio hE]
    have h1u : (0 : ℝ) < 1 - u := by linarith
    rw [le_div_iff₀ h1u]; linarith
  have hpow : (etaT E (s N) / etaT E u) ^ ((13 : ℝ) / 4) ≤ (etaT E (s N) / etaT E u) ^ (4 : ℕ) := by
    have h1 : (etaT E (s N) / etaT E u) ^ ((13 : ℝ) / 4) ≤ (etaT E (s N) / etaT E u) ^ (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
    rwa [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ δ := Real.rpow_nonneg (Nat.cast_nonneg _) δ
  unfold thrFar Step2.thr
  exact mul_le_mul_of_nonneg_left hpow hN0

/-- `gridTauFar ≤ gridTau`: applying `thrFar_le_thr'` at every `u_j`, `j ≤ K N`, and
`firstHit_le_of_le` to the `J*` component; the `goodSet` component is literally unchanged. -/
theorem gridTauFar_le_gridTau {E : ℝ} (hE : |E| < 2) {D δ τ₁ ε ζCtr τ3 τ57 : ℝ} {s u : ℕ → ℝ}
    {K : ℕ → ℕ} {N : ℕ} (hsu : s N ≤ u N) (hu1 : u N < 1) (ω : Ωg d) :
    gridTauFar d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω ≤ gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω := by
  have hJ : ∀ j ≤ K N,
      jSMat d E D N (time s u K N j) (H d s u K N j ω) - Step2.thr E s δ N (time s u K N j) ≤
      jSMat d E D N (time s u K N j) (H d s u K N j ω) - thrFar E s δ N (time s u K N j) := by
    intro j hj
    have hsuj : s N ≤ time s u K N j := by
      have h0 := time_mono_of_le (K := K) hsu (Nat.zero_le j)
      rwa [time_zero] at h0
    have hv1 : time s u K N j < 1 := by
      rcases Nat.eq_zero_or_pos (K N) with hK0 | hK0
      · have hj0 : j = 0 := by omega
        rw [hj0, time_zero]; linarith
      · have hK0' : K N ≠ 0 := hK0.ne'
        have hle : time s u K N j ≤ time s u K N (K N) := time_mono_of_le (K := K) hsu hj
        rw [time_last s u K N hK0'] at hle
        linarith
    linarith [thrFar_le_thr' (δ := δ) hE hsuj hv1]
  unfold gridTauFar gridTau
  exact min_le_min (firstHit_le_of_le hJ) (le_refl _)

end RBM.Gauss.Grid

end
