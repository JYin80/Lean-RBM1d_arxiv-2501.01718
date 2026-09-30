/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2FarInputs
import RBM1D.Gauss.CutoffBounds

/-!
# The far index set of (5.48) along the flow

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.29), (5.48).

The far half of (5.48) is the bound `|(L-K)_{u,a}| ≺ T_{u,D}(‖a₁-a₂‖)`, with no prefactor, on the
far index set `‖a₁ - a₂‖ > 6ℓ*_u`.  Since `ℓ*_u = (log W)^{3/2} ℓ̂_u` grows with `u`, the far
index set *shrinks* with `u`: an argument that is far at a later time was far at every earlier
time.  So the `J*` of (5.29) restricted to the far index set jumps downwards whenever `6ℓ*_u`
crosses an achieved distance, and it has no two-sided modulus of continuity in `u`.

## Main results

* `RBM.Step2FarMart.ellStar_mono_time` — `ℓ*_u` is non-decreasing in `u`.
* `RBM.Step2FarMart.far_mono_time` — the far index set shrinks with time.
* `RBM.Step2FarMart.tT_mono` — the tail function `T_{u,D}` is non-increasing in `D`.
-/

namespace RBM
namespace Step2FarMart

open Real Filter MeasureTheory

/-! ### 1. The far-restricted `J*` of (5.29) -/

section FarJ

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

variable (X : Sample B) {E D : ℝ} {N : ℕ} {u : ℝ} {ω : Ω}

end FarJ

/-! ### 2. The far half of (5.48) -/

section Far548

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Far548

/-! ### 3. The far index set shrinks with time

`6ℓ*_u` grows with `u`, so the far index set shrinks and the far-restricted `J*` has downward
jumps: it has no two-sided modulus of continuity in `u`. -/

section FarCut

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- `ℓ*_u = (log W)^{3/2} ℓ̂_u` is non-decreasing in `u`, because `ℓ̂` is
(`RBM.Step3.ellHat_mono`). -/
theorem ellStar_mono_time {N : ℕ} (hW1 : (1 : ℝ) ≤ (B.W N : ℝ)) {w v : ℝ} (hwv : w ≤ v)
    (hv1 : v < 1) :
    ellStar (B.W N : ℝ) (B.ell N w) ≤ ellStar (B.W N : ℝ) (B.ell N v) := by
  have hlogW : 0 ≤ log (B.W N : ℝ) := Real.log_nonneg hW1
  have hp : (0 : ℝ) ≤ log (B.W N : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlogW _
  have h : B.ell N w ≤ B.ell N v := Step3.ellHat_mono (L := B.L N) hwv hv1
  unfold ellStar
  nlinarith

/-- **The far index set shrinks with time.**  `6ℓ*_u` grows, so an argument that is far at a
later time was far at every earlier time — never the other way round. -/
theorem far_mono_time {N : ℕ} (hW1 : (1 : ℝ) ≤ (B.W N : ℝ)) {w v : ℝ} (hwv : w ≤ v)
    (hv1 : v < 1) {d : ℝ} (h : ¬ (d ≤ 6 * ellStar (B.W N : ℝ) (B.ell N v))) :
    ¬ (d ≤ 6 * ellStar (B.W N : ℝ) (B.ell N w)) := by
  have hmono := ellStar_mono_time (B := B) hW1 hwv hv1
  intro hc
  exact h (by linarith)

end FarCut

/-! ### 4. The Duhamel defect -/

section Defect

open Step2FarInputs

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s : ℕ → ℝ}

/-- The tail function is non-increasing in the decay exponent. -/
theorem tT_mono {N : ℕ} {D D' v ℓ : ℝ} (hW : (1 : ℝ) ≤ (B.W N : ℝ)) (hDD : D ≤ D') :
    Step2.tT B E N D' v ℓ ≤ Step2.tT B E N D v ℓ := by
  have hDW : (B.W N : ℝ) ^ (-D') ≤ (B.W N : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  unfold Step2.tT tailT
  have : (0 : ℝ) ≤ (((B.W N : ℝ) * B.ell N v * etaT E v) ^ 2)⁻¹
      * exp (-√(ℓ / B.ell N v)) := by positivity
  linarith

end Defect

/-! ### 5. The martingale term of (5.21) in the far field -/

section Supply

open Step2FarInputs

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Supply

/-! ### 6. The sharp bound in the far field -/

section Sharp

open Step2FarInputs

variable {Ω : Type*} [MeasurableSpace Ω]

end Sharp

/-! ### 7. The smoothed threshold -/

section SmoothThreshold

open Cutoff

end SmoothThreshold

/-! ### 8. The smoothed far functional -/

section SmoothFar

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

variable (X : Sample B) {E D : ℝ} {N : ℕ} {u : ℝ} {ω : Ω}

end SmoothFar

/-! ### 9. (5.48) with the smoothed threshold -/

section Produce548

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Produce548

/-! ### 10. The smoothed far functional is continuous in time -/

section SmoothCut

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E D : ℝ}

end SmoothCut

/-! ### 11. The bootstrap for the smoothed far functional -/

section Hookup

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Hookup

/-! ### 12. Satisfiability of the smoothed route -/

section Satisfiable

variable {Ω : Type*} [MeasurableSpace Ω]

end Satisfiable

/-! ### 13. The bootstrap hypotheses, assembled from the entries -/

section Assemble

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E D : ℝ} {s t : ℕ → ℝ}

end Assemble

end Step2FarMart
end RBM
