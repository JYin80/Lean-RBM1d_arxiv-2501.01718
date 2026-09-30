/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Step1BandNorm
import RBM1D.Flow.Step1GUETranslation

/-!
# Theorem 2.6 Step 1 assembly and Theorem 2.6 against the GUE matrix model

`step1Target_of`: Step 1, (2.21), for the band model at bulk energy against the GUE matrix
`H_∞` (`Step1Target`), obtained as the difference of two limits against the common reference
`gue0Ref'`: `step1_band'` gives `ouPairing(t_*) - gue0Ref' → 0`, and
`gue_translation'` gives `gueMatPairing - gue0Ref' → 0`; subtracting and
cancelling the common reference gives `ouPairing(t_*) - gueMatPairing → 0`.

`theorem2_6_mat`: Theorem 2.6 (2.18) against the GUE matrix model, from Step 1 (`step1Target_of`)
and Step 2's output (2.24) (`h2 : Step2Output d κ`), via `theorem2_6_mat_of_steps`
(`DBMInput.lean`; the final combination in the proof of Theorem 2.6).

The only external input in the closure of both theorems is `h51 : LSY22' d`, the corrected
(unit-density) reading of [51, Theorem 2.2] (`docs/PAPER-VS-LEAN.md` §4).
-/

open MeasureTheory Filter Topology

namespace RBM.Gauss

/-- **Step 1 (2.21) against the GUE matrix `H_∞`**. For bulk
`|E| ≤ 2 - κ`, `τ_* ∈ (0,1)`, `t_* = M^{-1+τ_*}`, every `k` and test function `O`, the OU
marginal's pairing at `t_*` is asymptotically the GUE matrix's pairing, both at `E`. Proof:
`(ouPairing - gue0Ref') - (gueMatPairing - gue0Ref') = ouPairing - gueMatPairing`, and the two
terms on the left tend to `0` by `step1_band'` and `gue_translation'` respectively. -/
theorem step1Target_of (d : Dims) (h51 : LSY22' d) {κ : ℝ} (hκ : 0 < κ)
    (hLL : BandTracialLocalLaw d (κ / 2)) (hG : GUELocalLaw d) : Step1Target d κ := by
  intro τs h0 h1 E hE k O hO
  have hband := step1_band' d h51 hκ hLL hG h0 h1 hE k hO
  have hgue := gue_translation' d h51 hG hκ hE k hO
  have h := hband.sub hgue
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  ring

/-- **Theorem 2.6 against the GUE matrix model**: (2.18), from
Step 1 (`step1Target_of`) and Step 2's output (2.24) (`h2`), via `theorem2_6_mat_of_steps`
. -/
theorem theorem2_6_mat (d : Dims) (h51 : LSY22' d) {κ : ℝ} (hκ : 0 < κ)
    (hLL : BandTracialLocalLaw d (κ / 2)) (hG : GUELocalLaw d) (h2 : Step2Output d κ) :
    BulkUniversalityMat d κ :=
  theorem2_6_mat_of_steps d κ (step1Target_of d h51 hκ hLL hG) h2

end RBM.Gauss
