/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

module

public import RBM1D.MainDefs
public import RBM1D.Gauss.Model
public import RBM1D.Flow.Consequences
public import RBM1D.Loop.ContinuityAssembly

@[expose] public section

/-!
# The identities in law (2.39), (2.66), (6.1) for the Gaussian model

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 2.8 ((2.39), (2.66)) and (6.1).

In the paper these three statements are justified by *equality in distribution up to a
deterministic scaling*.  In the moment route of `RBM1D/Gauss/Model.lean` the flow is
`H_u = √u • X` with **one fixed** Gaussian band matrix `X`, so the two sides of each of the
three statements are deterministic scalings of **the same** sample point `ω`: no distributional
argument is needed at all, and the identities become algebraic identities of resolvents.

## The algebraic core

`RBM.green (c • H) (c z) = c⁻¹ • RBM.green H z` for `c ≠ 0` (`RBM.Gauss.green_smul_mul`), hence
for real `c` the same for `RBM.Gsig` and, taking `n` factors and a trace,
`RBM.gloop (c • H) (c z) I = c⁻ⁿ · RBM.gloop H z I` (`RBM.Gauss.gloop_smul_mul`).

* **(2.39)/(2.66)**: with `E = lemE z`, `t = lemT z` and `z_t^{(E)} = t^{1/2} z` (2.37,
  `RBM.eq_inv_sqrt_mul_zt`), `H_t = t^{1/2} X`, so
  `G_t^{(E)}(ω) = t^{-1/2} (X(ω) - z)⁻¹`, i.e. `t^{1/2} G_t^{(E)} = G(z)` with `H := X`,
  **pointwise in `ω`** (`RBM.Gauss.green_Hflow_lemT_eq`).  The `n`-loop version gives
  `t^{n/2} L_{t,σ,a} = ` the `n`-loop of `G(z)` (`RBM.Gauss.gloop_Hflow_lemT_eq`), which is
  (2.66) for `n = 2` and the 1-loop identity used for (2.4) for `n = 1`.
* **(6.1)**: `H_{t₂} = (t₂/t₁)^{1/2} H_{t₁}` and `z̃_{t₁} = (t₂/t₁)^{1/2} z_{t₁}`, so the loops
  of `G̃_{t₁}` are `(t₁/t₂)^{n/2} L_{t₁,σ,a}` pointwise, and `(t₁/t₂)^{n/2} ≤ 1`
  (`RBM.Gauss.gloop_Hflow_ztTilde_eq`).

## Main results

* `RBM.Gauss.transfer_gauss` : the `RBM.Transfer` of `RBM.Gauss.sample`, with `Hband = X`.
* `RBM.Gauss.transferLoop1_gauss` : the `RBM.TransferLoop1` of `RBM.Gauss.transfer_gauss`.
* `RBM.Gauss.gloop_Hflow_ztTilde_eq` : the loop scaling (6.1) of the flow, pointwise in `ω`,
  for `0 < t₁ ≤ t₂`.

## Deviations from the paper

* `RBM.Gauss.gloop_Hflow_ztTilde_eq` carries the hypotheses `0 < t₁` and `t₁ ≤ t₂`.  The
  paper uses (6.1) only for `1/2 ≤ t₁ ≤ t₂ < 1` (§6), where both hold.  They are needed because
  `(t₂/t₁)^{1/2}` is meaningless otherwise.
* Nothing here proves that the flow of the moment route is a matrix Brownian motion; it is not.
  This is the deviation already recorded for `RBM1D/Gauss/Model.lean`.
-/

namespace RBM.Gauss

open MeasureTheory Filter Matrix
open scoped NNReal ENNReal

/-! ### Scaling of the resolvent -/

section Algebra

variable {n : Type*} [Fintype n] [DecidableEq n]

end Algebra

section LoopAlgebra

variable {L W : ℕ} [NeZero L] [NeZero W]

end LoopAlgebra

/-! ### (2.37) in multiplicative form -/

/-! ### (2.39) and (2.66) for the Gaussian model

`H_t = t^{1/2} X` and `z_t^{(E)} = t^{1/2} z`, so `t^{1/2} G_t^{(E)} = (X - z)⁻¹` pointwise. -/

variable (d : Dims)

/-- **(2.39) for the 1-`G` loop**, pointwise: `Tr G(z) E_a = t^{1/2} L_{t,+,a}`. -/
theorem gloop_one_Hflow_lemT_eq (N : ℕ) {z : ℂ} (hz : 0 < z.im) (ω : Ω d)
    (a : ZMod (d.L N)) :
    RBM.gloop (d.L N) (d.W N) (Xmat d N ω) z ⟨[true], [a]⟩
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) *
        RBM.gloop (d.L N) (d.W N) (Hflow d N (RBM.lemT z) ω)
          (RBM.zt (RBM.lemE z) (RBM.lemT z)) ⟨[true], [a]⟩ := by
  have hlen : (([true] : List Bool).zip [a]).length = 1 := rfl
  rw [gloop_Hflow_lemT_eq d N hz ω [true] [a], hlen, pow_one]

/-! ### The `RBM.Transfer` of the Gaussian model -/

/-- **(2.39) for the 1-`G` loop** for the moment route: again an equality of random variables. -/
theorem transferLoop1_gauss : RBM.TransferLoop1 (transfer_gauss d) where
  loop1 := by
    intro z hz c ζ h
    refine RBM.StochDom.of_le_left (fun N a ω => le_of_eq ?_) h
    congr 2
    exact gloop_one_Hflow_lemT_eq d N (hz N) ω a

/-! ### (6.1) for the Gaussian model -/

/-- **(6.1) pointwise**: the `n`-loop of `G̃_{t₁} = (H_{t₂} - z̃_{t₁})⁻¹` is
`(t₁/t₂)^{n/2} L_{t₁,σ,a}`, an equality of random variables. -/
theorem gloop_Hflow_ztTilde_eq (N : ℕ) {E t₁ t₂ : ℝ} (h₁ : 0 < t₁) (h₁₂ : t₁ ≤ t₂) (ω : Ω d)
    (I : RBM.LoopIdx (ZMod (d.L N))) :
    RBM.gloop (d.L N) (d.W N) (Hflow d N t₂ ω) (RBM.ztTilde E t₁ t₂) I
      = ((Real.sqrt (t₂ / t₁) : ℝ) : ℂ)⁻¹ ^ (I.σ.zip I.a).length *
        RBM.gloop (d.L N) (d.W N) (Hflow d N t₁ ω) (RBM.zt E t₁) I := by
  set r : ℝ := Real.sqrt (t₂ / t₁) with hr_def
  have hr0 : 0 < r := Real.sqrt_pos.2 (div_pos (lt_of_lt_of_le h₁ h₁₂) h₁)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hmul : r * Real.sqrt t₁ = Real.sqrt t₂ := by
    have hdiv : (0 : ℝ) ≤ t₂ / t₁ := le_of_lt (div_pos (lt_of_lt_of_le h₁ h₁₂) h₁)
    rw [hr_def, ← Real.sqrt_mul hdiv t₁, div_mul_cancel₀ _ h₁.ne']
  have hH : Hflow d N t₂ ω = (r : ℂ) • Hflow d N t₁ ω := by
    show ((Real.sqrt t₂ : ℝ) : ℂ) • Xmat d N ω
      = (r : ℂ) • (((Real.sqrt t₁ : ℝ) : ℂ) • Xmat d N ω)
    rw [smul_smul, ← Complex.ofReal_mul, hmul]
  rw [hH, RBM.ztTilde, gloop_smul_mul hrC]

end RBM.Gauss

