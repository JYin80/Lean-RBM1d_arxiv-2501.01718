/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2FarInputs

/-!
# T1496: absorbing the `≺` loss into the reduced (5.35) shape (inventory target M3)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.35).

`docs/reports/T1488-prove.md` §3, target **M3**: `RBM.Step2FarInputs.eGpm_le_rhs535_of_jS`
takes its hypotheses `h273`/`h557C`/`h557R` with constant `1`, while (Step 1's) `Step1.apriori`
and the (2.73)-reduced (5.57) only give them up to a loss `N^τ`.  Since `ℓs` is a free parameter
of `RBM.Step2FarInputs.rhs535` (only `0 < ℓs` and `1 ≤ ℓu/ℓs` are ever required by its
consumers), the loss can be absorbed by shrinking `ℓs` to `ℓs / c` with `c := N^{2τ}`, at the
cost of multiplying the whole right side by `c ^ 3`.  This file proves exactly that scaling
step (T1 of the ticket).

**T2 of the ticket (`eGpm_le_rhs535_of_jS_scaled`) is not proved here.**  Per the ticket's
Step 0, `h560` — the hypothesis `docs/reports/T1488-prove.md` "Open issues" #2 flags as
suspected unsatisfiable — is among the hypotheses of
`RBM.Step2FarInputs.eGpm_le_rhs535_of_jS` (and of `RBM.Step2FarInputs.h535_of_jS`), and `h560`
does not mention `ℓs` at all, so the `ℓs`-rescaling of T1 neither introduces nor removes this
difficulty.  The ticket instructs: "Do not use (T2) with an unverified hypothesis." See the
prove report for the precise account.
-/

namespace RBM

open Real

/-- **(T1).**  `RBM.Step2FarInputs.rhs535` shrinks `ℓs` to `ℓs / c` at the cost of a factor
`c ^ 3`, for `c ≥ 1` and nonnegative data.  The degree of `rhs535` in `r = ℓu / ℓs` is `3`
(from the near-field term `cNear · r ^ 3`); the far-field terms have degree `3/2` and `1`, both
`≤ 3`, so a single factor `c ^ 3` dominates every term. -/
theorem rhs535_div_le {Wr Lr ℓu ℓs ηu D J ρ d c : ℝ}
    (hc : 1 ≤ c) (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu)
    (hJ0 : 0 ≤ J) (hρ0 : 0 ≤ ρ) (hLr0 : 0 ≤ Lr) (_hd0 : 0 ≤ d) :
    Step2FarInputs.rhs535 Wr Lr ℓu (ℓs / c) ηu D J ρ d
      ≤ c ^ 3 * Step2FarInputs.rhs535 Wr Lr ℓu ℓs ηu D J ρ d := by
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hWpos : (0 : ℝ) < Wr := lt_of_lt_of_le one_pos hW
  have hA0 : (0 : ℝ) < Wr * ℓu * ηu := by positivity
  have hr0 : (0 : ℝ) ≤ ℓu / ℓs := div_nonneg hℓu.le hℓs.le
  have hcN : 0 ≤ Lemma57.cNear Wr ℓu := Lemma57.cNear_nonneg hW hℓu
  have hcF : 0 ≤ Lemma57.cFar Wr ℓu := Lemma57.cFar_nonneg hW hℓu
  have htail : 0 ≤ tailT Wr ℓu ηu D d := tailT_nonneg hWpos.le d
  have hηi : (0 : ℝ) ≤ ηu⁻¹ := by positivity
  have hAiInv : (0 : ℝ) ≤ (√(Wr * ℓu * ηu))⁻¹ := by positivity
  have hAinv : (0 : ℝ) ≤ (Wr * ℓu * ηu)⁻¹ := by positivity
  -- `√c ≤ c`, hence `c * √c ≤ c ^ 3` and `c ≤ c ^ 3` (both from `c ≥ 1`).
  have hsqrtc : √c ≤ c := (Real.sqrt_le_left hcpos.le).mpr (by nlinarith)
  have hc1 : c ≤ c ^ 3 := by nlinarith [sq_nonneg (c - 1), hcpos.le]
  have hc32 : c * √c ≤ c ^ 3 := by
    have h1 : c * √c ≤ c * c := by nlinarith [Real.sqrt_nonneg c]
    nlinarith [h1, hc1]
  have hrdiv : ℓu / (ℓs / c) = c * (ℓu / ℓs) := by
    have hℓs' : ℓs ≠ 0 := hℓs.ne'
    have hc' : c ≠ 0 := hcpos.ne'
    field_simp
  rw [Step2FarInputs.rhs535, Step2FarInputs.rhs535, hrdiv]
  set r : ℝ := ℓu / ℓs with hrdef
  set A : ℝ := Wr * ℓu * ηu with hAdef
  set ind : ℝ := (if d ≤ ellStar Wr ℓu then (1 : ℝ) else 0) with hinddef
  rw [Real.sqrt_mul hcpos.le r]
  -- Term-wise bounds, in the additive (not distributed) shape.
  have e1 : Lemma57.cNear Wr ℓu * (c * r) ^ 3 * ind
      = c ^ 3 * (Lemma57.cNear Wr ℓu * r ^ 3 * ind) := by ring
  have e2 : Lemma57.cFar Wr ℓu * (c * r * (√c * √r) * (√A)⁻¹ * J)
      ≤ c ^ 3 * (Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * J)) := by
    have hfac : (0 : ℝ) ≤ Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * J) :=
      mul_nonneg hcF
        (mul_nonneg (mul_nonneg (mul_nonneg hr0 (Real.sqrt_nonneg r)) hAiInv) hJ0)
    have hcomm : Lemma57.cFar Wr ℓu * (c * r * (√c * √r) * (√A)⁻¹ * J)
        = (c * √c) * (Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * J)) := by ring
    rw [hcomm]
    exact mul_le_mul_of_nonneg_right hc32 hfac
  have e3 : 169 * (c * r * A⁻¹ * (J * √J))
      ≤ c ^ 3 * (169 * (r * A⁻¹ * (J * √J))) := by
    have hfac : (0 : ℝ) ≤ 169 * (r * A⁻¹ * (J * √J)) :=
      mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg hr0 hAinv) (mul_nonneg hJ0 (Real.sqrt_nonneg J)))
    have hcomm : 169 * (c * r * A⁻¹ * (J * √J)) = c * (169 * (r * A⁻¹ * (J * √J))) := by ring
    rw [hcomm]
    exact mul_le_mul_of_nonneg_right hc1 hfac
  have e4 : c * r * (ℓu * ηu)⁻¹ * Lr * ρ
      ≤ c ^ 3 * (r * (ℓu * ηu)⁻¹ * Lr * ρ) := by
    have hℓηinv : (0 : ℝ) ≤ (ℓu * ηu)⁻¹ := by positivity
    have hfac : (0 : ℝ) ≤ r * (ℓu * ηu)⁻¹ * Lr * ρ :=
      mul_nonneg (mul_nonneg (mul_nonneg hr0 hℓηinv) hLr0) hρ0
    have hcomm : c * r * (ℓu * ηu)⁻¹ * Lr * ρ = c * (r * (ℓu * ηu)⁻¹ * Lr * ρ) := by ring
    rw [hcomm]
    exact mul_le_mul_of_nonneg_right hc1 hfac
  -- Combine the three tailT-weighted terms additively (not distributed over `c ^ 3` yet).
  have hsum : Lemma57.cNear Wr ℓu * (c * r) ^ 3 * ind
        + Lemma57.cFar Wr ℓu * (c * r * (√c * √r) * (√A)⁻¹ * J)
        + 169 * (c * r * A⁻¹ * (J * √J))
      ≤ c ^ 3 * (Lemma57.cNear Wr ℓu * r ^ 3 * ind)
          + c ^ 3 * (Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * J))
          + c ^ 3 * (169 * (r * A⁻¹ * (J * √J))) := by
    linarith [e1, e2, e3]
  have hmul : ηu⁻¹ * (Lemma57.cNear Wr ℓu * (c * r) ^ 3 * ind
          + Lemma57.cFar Wr ℓu * (c * r * (√c * √r) * (√A)⁻¹ * J)
          + 169 * (c * r * A⁻¹ * (J * √J))) * tailT Wr ℓu ηu D d
      ≤ ηu⁻¹ * (c ^ 3 * (Lemma57.cNear Wr ℓu * r ^ 3 * ind)
          + c ^ 3 * (Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * J))
          + c ^ 3 * (169 * (r * A⁻¹ * (J * √J)))) * tailT Wr ℓu ηu D d :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hηi) htail
  have hcomb :=
    add_le_add hmul e4
  refine hcomb.trans_eq ?_
  ring

end RBM
