/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.CutoffBounds
import RBM1D.Hierarchy.Step2Moment
import RBM1D.Hierarchy.Step2MomentStep

/-!
# The sharp bound `J*_{u,D} ≺ (η_s/η_u)²` (the remark after (5.47)): the drift near field

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.41), (5.44)–(5.48).

The near half of (5.48),

`|(L-K)_{u,(+,-),a}| ≺ (η_s/η_u)² · T_{u,D}(‖a₁-a₂‖)`,

is the stronger bound `J*_{τ,D} ≺ (η_s/η_t)²` of the remark after (5.47), whereas the stopping
time (5.43), `T = min{u : J*_{u,D} ≥ N^δ (η_s/η_t)⁴}`, works at the level `(η_s/η_u)⁴`.

**Where the two powers are.**  They are not lost in an estimate.  In the one-step arithmetic of
(5.39)–(5.47) exactly one summand is genuinely at the level `(η_s/η_u)⁴`: the near-field term
of (5.41), when its two `u`-dependent factors `(η_u/η_t)²` and `(ℓ_u/ℓ_s)³` are bounded
**separately**, each at its own supremum.  Done jointly ("multiply first, then integrate"), that
term is at the level `(η_s/η_u)²`, like every other summand.  Sup × length is not enough here:
the genuine antiderivative of `(1-u)^{-1/2}` is what buys the last half power.

## Main results

* `RBM.Step2Near47.driftNearInt`, `RBM.Step2Near47.driftNearInt_eq` — the near-field integrand
  of the drift term of (5.41), `η_u^{-1}(η_u/η_v)²(η_s/η_u)^{3/2}`, is a constant times
  `(1-u)^{-1/2}`.

## Deviations from the paper

* The near-field coefficient of (5.41) is `(ℓ_u/ℓ_s)³` here, not the paper's `(ℓ_u/ℓ_s)²`: this
  is the (2.73)-reduced shape of (5.35).  Integrating `(ℓ_u/ℓ_s)³` jointly still lands on the
  level `(η_s/η_u)²`.
-/

namespace RBM

namespace Step2Near47

open Real Filter MeasureTheory intervalIntegral

/-! ### 1. (5.41)'s near field, integrated jointly -/

section Near

variable {E : ℝ}

/-- The near-field integrand of the **drift** term of (5.41), with the loop-length ratio
`ℓ_u/ℓ_s` already replaced by its bound `√(η_s/η_u)` (`RBM.Step3.ellHat_le_sqrt_mul`) and the
reduced shape's cube in place of the paper's square:

`η_u^{-1} (η_u/η_v)² (η_s/η_u)^{3/2}`.

The same object for the **quadratic variation** of (5.44) has the exponents `4` and `5/2`
instead of `2` and `3/2`. -/
noncomputable def driftNearInt (E s v u : ℝ) : ℝ :=
  (etaT E u)⁻¹ * (etaT E u / etaT E v) ^ 2 * √(etaT E s / etaT E u) ^ 3

/-- The integrand collapses to `η_s^{3/2} η_v^{-2} η_u^{-1/2}`, i.e. a constant times
`(1-u)^{-1/2}`.  Note the sign of the exponent: unlike the quadratic-variation integrand of
(5.44), which is *increasing* in `η_u` and is therefore handled by "sup × length", this one is
*decreasing*, so sup × length overshoots and a genuine antiderivative is needed. -/
theorem driftNearInt_eq (hE : |E| < 2) {s v u : ℝ} (hs1 : s < 1) (hu1 : u < 1) (hv1 : v < 1) :
    driftNearInt E s v u
      = √(etaT E s) ^ 3 * (etaT E v ^ 2 * √((mE E).im))⁻¹ * (√(1 - u))⁻¹ := by
  have hm := mE_im_pos hE
  have ha : 0 < etaT E s := Step2.etaT_pos' hE hs1
  have hb : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hc : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have hp0 : 0 < √(1 - u) := Real.sqrt_pos.2 h1u
  have hq0 : 0 < √((mE E).im) := Real.sqrt_pos.2 hm
  have hsu : √(etaT E u) = √(1 - u) * √((mE E).im) := by
    rw [Step2.etaT_eq, Real.sqrt_mul h1u.le]
  have hbu : etaT E u = √(1 - u) ^ 2 * √((mE E).im) ^ 2 := by
    rw [Real.sq_sqrt h1u.le, Real.sq_sqrt hm.le, Step2.etaT_eq]
  have hdiv : √(etaT E s / etaT E u) = √(etaT E s) / √(etaT E u) := Real.sqrt_div ha.le _
  rw [driftNearInt, hdiv, hsu, div_pow, div_pow]
  rw [hbu]
  have hne1 : √(1 - u) ≠ 0 := hp0.ne'
  have hne2 : √((mE E).im) ≠ 0 := hq0.ne'
  have hne3 : etaT E v ≠ 0 := hc.ne'
  field_simp

end Near

/-! ### 2. The one-step arithmetic at the sharp threshold -/

section Arith

end Arith

/-! ### 2″. The second pass costs nothing in the exponent budget -/

section SecondPassExponents

variable {x R r A : ℝ}

end SecondPassExponents

/-! ### 2′. The exponent table does not move -/

section Exponents

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s : ℕ → ℝ}

end Exponents

/-! ### 3. The sharp bound: `J*_{u,D} ≺ (η_s/η_u)²` -/

section Sharp

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

variable (X : Sample B) {D : ℝ}

end Sharp

/-! ### 4. The near half of (5.48) -/

section Hnear

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

end Hnear

/-! ### 5. Satisfiability witnesses (compiled) -/

section Sat

end Sat

end Step2Near47

end RBM

