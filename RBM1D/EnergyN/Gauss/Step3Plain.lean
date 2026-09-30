/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step3Charges
import RBM1D.Gauss.Step2Plain

/-!
# `(η_s/η_u)^4 ≤ (W ℓ_u η_u)^{1/4}` from the plain pair, at an `N`-dependent energy

`RBM.StepGlue.eventually_R4_le_rpow_quarter_plainN`: eventually
`(η_s/η_u)^4 ≤ (W ℓ_u η_u)^{1/4}` for all `u ∈ [s, t]`, at an `N`-dependent energy `E : ℕ → ℝ`.

## The external `κ`

No energy-dependent constant is fixed here: no fixed constant crosses `∀ᶠ N`. The proof only
extracts the plain fact `r^{30} ≤ scale(t)` from `hreg0` pointwise, via the generic (`E`-free)
helper `Step2.etaT_ratio`.
-/

noncomputable section

namespace RBM

open MeasureTheory Filter

namespace StepGlue

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **`(η_s/η_u)^4 ≤ (W ℓ_u η_u)^{1/4}` eventually**, for all `u ∈ [s, t]`, from the plain pair. -/
theorem eventually_R4_le_rpow_quarter_plainN (hE : ∀ N, |E N| < 2) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ B.scale (E N) N (t N)) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT (E N) (s N) / etaT (E N) u) ^ 4 ≤ B.scale (E N) N u ^ ((1 : ℝ) / 4) := by
  filter_upwards [hreg0] with N hN u
  have hW0 : (0 : ℝ) ≤ B.W N := by positivity
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hrt : etaT (E N) (s N) / etaT (E N) (t N) = (1 - s N) / (1 - t N) :=
    Step2.etaT_ratio (hE N) _ _
  have hru : etaT (E N) (s N) / etaT (E N) u = (1 - s N) / (1 - (u : ℝ)) :=
    Step2.etaT_ratio (hE N) _ _
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have h1s : 0 < 1 - s N := by linarith [(hst N).trans (ht1 N).le]
  set r : ℝ := (1 - s N) / (1 - t N) with hrdef
  set ρ : ℝ := (1 - s N) / (1 - (u : ℝ)) with hρdef
  have hρ0 : 0 ≤ ρ := le_of_lt (div_pos h1s h1u)
  have hρr : ρ ≤ r := by
    refine div_le_div_of_nonneg_left h1s.le h1t ?_
    linarith [u.2.2]
  have hr1 : (1 : ℝ) ≤ r := (one_le_div h1t).2 (by linarith [u.2.1, (hst N)])
  have hAt : r ^ 30 ≤ B.scale (E N) N (t N) := by rw [hrt] at hN; exact hN
  have hAv : B.scale (E N) N (t N) ≤ B.scale (E N) N u := flowScale_antitoneOn hW0 (B.L N) (E N)
    (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 (ht1 N).le) u.2.2
  have h16 : (ρ ^ 4) ^ 4 ≤ B.scale (E N) N u := by
    have hp : ρ ^ 16 ≤ r ^ 16 := pow_le_pow_left₀ hρ0 hρr 16
    have hr16 : r ^ 16 ≤ r ^ 30 := pow_le_pow_right₀ hr1 (by norm_num)
    calc (ρ ^ 4) ^ 4 = ρ ^ 16 := by ring
      _ ≤ r ^ 16 := hp
      _ ≤ r ^ 30 := hr16
      _ ≤ B.scale (E N) N (t N) := hAt
      _ ≤ B.scale (E N) N u := hAv
  have hkey := Real.rpow_le_rpow (by positivity) h16 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [hru]
  have he : ((ρ ^ 4) ^ 4 : ℝ) ^ ((1 : ℝ) / 4) = ρ ^ 4 := by
    rw [← Real.rpow_natCast (ρ ^ 4) 4, ← Real.rpow_mul (by positivity)]
    norm_num
  rwa [he] at hkey

end StepGlue

end RBM
