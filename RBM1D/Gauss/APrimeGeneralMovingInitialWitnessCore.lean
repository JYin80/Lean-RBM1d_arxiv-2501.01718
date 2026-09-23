/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Iteration
import RBM1D.Gauss.DimsExample

/-!
# Clean positive-length initial-window witness

The first gained grid step for the concrete growing Gaussian band model has left endpoint
exactly zero and right endpoint exactly `1/2` eventually.  The exact zero-time identities
therefore supply `BoundsCore` on the same nondegenerate window.
-/

namespace RBM.APrimeGeneralMovingInitialHinit

open Filter MeasureTheory Set Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private theorem eventual_cap :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-1 + (1 : ℝ) / 2) ≤ 1 - (1 / 2 : ℝ) := by
  filter_upwards [eventually_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop 1] with N hNpow hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hEq : (N : ℝ) ^ (-1 + (1 : ℝ) / 2) =
      ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [show -1 + (1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hN0]
  rw [hEq]
  have hInv : ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ (2 : ℝ)⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hNpow)
  norm_num at hInv ⊢
  exact hInv

/-- The first gained grid cell has exact zero-time initial bounds and terminal time `1/2`
eventually, on one and the same concrete Gaussian band model. -/
theorem positive_length_hinit_witness' :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧
      let s := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0
      let t := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (sample d) 0 s ∧ (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      (∀ᶠ N : ℕ in atTop, t N = 1 / 2) := by
  obtain ⟨τ', hτ', c, hc, _n₀, hgrid⟩ :=
    B.eventually_flow_grid' (κ := 1) (τ := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)
  have hgrid0 := hgrid 0 (by norm_num)
    (fun _ => (1 / 2 : ℝ)) (fun _ => by norm_num) eventual_cap
  let s : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0
  let t : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1
  have hsEq : ∀ N, s N = 0 := by
    intro N
    change gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0 = 0
    exact gridT_zero (by norm_num)
  have hs0 : ∀ N, 0 ≤ s N := fun N => (hsEq N).ge
  have hst : ∀ N, s N ≤ t N := by
    intro N
    exact gridT_mono (B.one_le_W N) hτ'.le (1 / 2 : ℝ) (by omega)
  have ht1 : ∀ N, t N < 1 := by
    intro N
    exact (min_le_left _ _).trans_lt
      (gridS_lt_one (by linarith [B.one_le_W N]) _)
  have hcond : Cond272' B 0 s t c := by
    filter_upwards [hgrid0] with N hN
    rw [etaT_div_etaT (by norm_num : |(0 : ℝ)| < 2)]
    exact hN.2.2.2 0
  have hreg : Cond272Reg B 0 s t c := by
    refine ⟨hcond.toCond272 (by norm_num) hst ht1 hc.le, ?_⟩
    filter_upwards [hcond] with N hN
    rw [etaT_div_etaT (by norm_num : |(0 : ℝ)| < 2)] at hN
    have h1t : 0 < 1 - t N := by linarith [ht1 N]
    have h1s : 0 < 1 - s N := by linarith [hst N]
    have hR1 : (1 : ℝ) ≤ (1 - s N) / (1 - t N) := by
      rw [le_div_iff₀ h1t]
      linarith [hst N]
    have hRp : (1 : ℝ) ≤ ((1 - s N) / (1 - t N)) ^ 30 := one_le_pow₀ hR1
    nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)) c]
  have hB : BoundsCore (sample d) 0 s := by
    have hsFun : s = fun _ => 0 := funext hsEq
    rw [hsFun]
    exact (Bounds_zero (sample d) (by norm_num : |(0 : ℝ)| ≤ 2)).toBoundsCore
  have hWt : Tendsto (fun N : ℕ => ((d.W N : ℝ)) ^ (-τ')) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hτ').comp (Gauss.tendsto_W d)
  have htEq : ∀ᶠ N : ℕ in atTop, t N = 1 / 2 := by
    filter_upwards [hWt.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with N hW
    change gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1 = 1 / 2
    apply gridT_of_le
    rw [gridS]
    norm_num
    have hW' : ((Dims.growW N : ℝ)) ^ (-τ') < 1 / 2 := by
      simpa only [d, Dims.exampleGrow_W] using hW
    linarith
  have hpos : ∀ᶠ N : ℕ in atTop, s N < t N := by
    filter_upwards [htEq] with N ht
    rw [hsEq N, ht]
    norm_num
  exact ⟨τ', hτ', c, hc, hsEq, hs0, hst, ht1, hreg, hB, hpos, htEq⟩

/-- Compatibility projection with the frozen public signature. -/
theorem positive_length_hinit_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧
      let s := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0
      let t := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (sample d) 0 s ∧ (∀ᶠ N : ℕ in atTop, s N < t N) := by
  rcases positive_length_hinit_witness' with
    ⟨τ', hτ', c, hc, hsEq, hs0, hst, ht1, hreg, hB, hpos, _htEq⟩
  exact ⟨τ', hτ', c, hc, hsEq, hs0, hst, ht1, hreg, hB, hpos⟩

#print axioms positive_length_hinit_witness'
#print axioms positive_length_hinit_witness

end
end RBM.APrimeGeneralMovingInitialHinit
