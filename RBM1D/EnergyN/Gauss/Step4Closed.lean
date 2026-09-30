/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step4Base
import RBM1D.Gauss.Lemma514NonAltTwo
import RBM1D.Gauss.OneLoopTimeIcc
import RBM1D.Gauss.Lemma514AltEnd
import RBM1D.Gauss.SigmaExhaust
import RBM1D.EnergyN.Gauss.Step4Gauss
import RBM1D.EnergyN.Gauss.Lemma514All
import RBM1D.EnergyN.Gauss.Lemma514AltEnd

/-!
# Step 4 for the Gaussian flow, closed form, at an `N`-dependent energy

`RBM.Gauss.step4_gauss_plainN`: (2.78) for the Gaussian flow at an `N`-dependent energy
`E : ℕ → ℝ`, with `hEκ : ∀ N, |E N| ≤ 2 - κ` and `hB : BoundsCoreN`. No energy-dependent
constant is fixed in this file. The proof uses `step4_gauss_of_plainN`,
`Grid.endpoint_alt_two_hEndAlt_plainN` and `h514_all_plainN`.
-/

noncomputable section

namespace RBM

open MeasureTheory Filter

namespace Gauss

variable (d : Dims)

/-- **(2.78) for the Gaussian flow** at an `N`-dependent energy: `|L - K| ≺ (W ℓ_u η_u)^{-n}`
for loops of every length `n ≥ 1`, uniformly in `u ∈ [s, t]`, from (2.68)–(2.70) at `s` and the
plain pair. -/
theorem step4_gauss_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ n : ℕ, 1 ≤ n → StochDom (band d).P
      (fun N (p : TimeIcc s t N × LoopData ((band d).L N) n) ω =>
        (sample d).lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => ((band d).scale (E N) N p.1)⁻¹ ^ n) :=
  step4_gauss_of_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
    (Grid.endpoint_alt_two_hEndAlt_plainN d hκ0 hκ1 hEκ hB hs0 ht1 hc0 hreg0 hAc)
    (h514_all_plainN d (traceMomentBound_gauss d) hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc)

end Gauss

end RBM

end

