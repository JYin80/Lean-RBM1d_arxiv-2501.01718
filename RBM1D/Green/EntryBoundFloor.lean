/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Green.EntryBound

/-!
# Lemma 4.1 with an additive floor in the large deviation estimates

T148 (`RBM1D/Gauss/LDENetClose.lean`) proved that the time-uniform forms of the large deviation
estimates (4.2) and (4.7) are **not available in their literal form** along the Gaussian flow:
after the deterministic modulus, each is equivalent to a polynomial lower bound on its own
control, and those controls are exponentially small in the band distance.  What is available
unconditionally is the same domination with an **additive floor**,

  `ldeRowLHS(u) ≺ ldeRowRHS(u) + N^{-B}`  for every `B ≥ 0`,

and likewise for the column estimate (T148) and the quadratic estimate (4.7) (T166).

This file is the deterministic half of the corresponding chain: every kernel of
`RBM1D/Green/EntryBound.lean` that consumes `RBM.LDERow`, `RBM.LDECol` or `RBM.LDEQuad`, restated
with the floor.  Nothing in `RBM1D/Green/EntryBound.lean` changes; every declaration here is new.

## Why the floor is harmless

The floor enters (4.10)/(4.11) exactly the way the (2.76) error does — additively, inside the
same bracket.  Downstream of (4.11) every constant `Λ` that bounds `∑_{k,l} S_{ik}|G_{kl}|²S_{lj}`
and `S_{ij}` may simply be asked to bound the floor as well (`hflΛ : fl ≤ Λ`), which costs
nothing because the block instance takes `Λ = 2 L^max + fl`.  So the floored statements have the
*same shape* as the unfloored ones, with larger absolute constants:

| unfloored | floored | constant |
|---|---|---|
| `RBM.norm_sq_green_offdiag_le` | `RBM.norm_sq_green_offdiag_le_floor` | `162 → 324` |
| `RBM.ldeQuadRHS_le` | `RBM.ldeQuadRHS_le_floor` | `38 → 74` |
| `RBM.norm_sq_selfEnergy_err_le` | `RBM.norm_sq_selfEnergy_err_le_floor` | `240 → 460` |
| `RBM.norm_sq_green_diag_sub_le` | `RBM.norm_sq_green_diag_sub_le_floor` | `2160 → 4140` |
| `RBM.norm_sq_green_diag_sub_le_blk` | `RBM.norm_sq_green_diag_sub_le_blk_floor` | `4320 → 8280` |

The constants are not optimised.

## Relation to `RBM1D/Hierarchy/LKDecayQuant.lean`

T160 proved the (4.2) half of this chain — `LDERowFloor`, `LDEColFloor`,
`norm_sq_green_le_row_floor`, `norm_sq_green_le_col_floor`, `norm_sq_green_le_two_sided_floor`,
`norm_sq_green_le_blk_floor` — inside `RBM.LKDecayQuant`, and recommended sinking them here,
since they are pure matrix lemmas with nothing to do with the hierarchy.  They are reproved here
(in the `RBM` namespace, so there is no clash with the `RBM.LKDecayQuant` copies); the copies in
`RBM1D/Hierarchy/LKDecayQuant.lean` can be deleted and re-routed here by whoever owns that file.
-/

namespace RBM

open Finset Matrix

section EntryFloor

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {H G : Matrix n n ℂ} {z m : ℂ} {δ Φ fl : ℝ} {S : n → n → ℝ}

/-- **The row large deviation bound (4.2) with an additive floor `fl` in the control.** -/
def LDERowFloor (H G : Matrix n n ℂ) (S : n → n → ℝ) (Φ fl : ℝ) : Prop :=
  ∀ i j, i ≠ j → ldeRowLHS H G i j ≤ Φ * (ldeRowRHS S G i j + fl)

/-- **The column large deviation bound (4.2) with an additive floor `fl` in the control.** -/
def LDEColFloor (H G : Matrix n n ℂ) (S : n → n → ℝ) (Φ fl : ℝ) : Prop :=
  ∀ k j, k ≠ j → ldeColLHS H G k j ≤ Φ * (ldeColRHS S G k j + fl)

/-- **The quadratic large deviation bound (4.7) with an additive floor `fl` in the control.**
This is `RBM.LDEQuad` with `ldeQuadRHS` replaced by `ldeQuadRHS + fl`; it is what
`RBM.Gauss.stochDom_ldeQuad_flow_floor` (T166) produces at `fl = N^{-B}`. -/
def LDEQuadFloor (H G : Matrix n n ℂ) (S : n → n → ℝ) (t Φ fl : ℝ) : Prop :=
  ∀ i, ldeQuadLHS H G S t i ≤ Φ * (ldeQuadRHS S G i + fl)

/-- The floor is a weakening: `RBM.LDERow` implies `RBM.LDERowFloor`. -/
theorem LDERowFloor.of_lderow (hΦ : 0 ≤ Φ) (hfl : 0 ≤ fl) (h : LDERow H G S Φ) :
    LDERowFloor H G S Φ fl := fun i j hij =>
  (h i j hij).trans (mul_le_mul_of_nonneg_left (by linarith) hΦ)

/-- The floor is a weakening: `RBM.LDECol` implies `RBM.LDEColFloor`. -/
theorem LDEColFloor.of_ldecol (hΦ : 0 ≤ Φ) (hfl : 0 ≤ fl) (h : LDECol H G S Φ) :
    LDEColFloor H G S Φ fl := fun k j hkj =>
  (h k j hkj).trans (mul_le_mul_of_nonneg_left (by linarith) hΦ)

/-- The floor is a weakening: `RBM.LDEQuad` implies `RBM.LDEQuadFloor`. -/
theorem LDEQuadFloor.of_ldequad {t : ℝ} (hΦ : 0 ≤ Φ) (hfl : 0 ≤ fl) (h : LDEQuad H G S t Φ) :
    LDEQuadFloor H G S t Φ fl := fun i =>
  (h i).trans (mul_le_mul_of_nonneg_left (by linarith) hΦ)

/-- **(4.10) with a floor**: `|G_{ij}|² ≤ 9 Φ (∑_k S_{ik} |G_{kj}|² + fl)` for `i ≠ j`. -/
theorem norm_sq_green_le_row_floor (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ i, ∑ k, S i k ≤ 1) (hΦ : 0 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hfl : 0 ≤ fl)
    (hLDE : LDERowFloor H G S Φ fl) {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 9 * Φ * (∑ k, S i k * ‖G k j‖ ^ 2 + fl) := by
  have hGii := hΩ.diag_ne_zero hm hδ i
  have h48 := green_eq_neg_mul_sum_row hMG hGii hij
  rw [sum_erase_sub_smul_row] at h48
  have hnorm := congrArg norm h48
  rw [norm_mul, norm_neg] at hnorm
  have hsq : ‖G i j‖ ^ 2 ≤ 9 / 4 * ldeRowLHS H G i j := by
    rw [hnorm, ldeRowLHS, mul_pow]
    exact mul_le_mul_of_nonneg_right (hΩ.norm_sq_diag_le hm hδ i) (sq_nonneg _)
  have hrhs : ldeRowRHS S G i j ≤ 2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 2 * (2 * δ * ‖G i j‖) ^ 2 := by
    refine sum_mul_sq_le_of_le_add _ (hS0 i) (hS1 i) (fun _ => norm_nonneg _) ?_
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k j
    have h2 := hΩ.norm_offdiag_le hki
    have h3 : ‖greenMinor G i k j‖ ≤ ‖G k j‖ + ‖greenMinor G i k j - G k j‖ := by
      calc ‖greenMinor G i k j‖ = ‖G k j + (greenMinor G i k j - G k j)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k i‖ * ‖G i j‖ ≤ δ * ‖G i j‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    linarith
  have hlde := hLDE i j hij
  have key : ‖G i j‖ ^ 2 ≤ 9 * Φ * (∑ k, S i k * ‖G k j‖ ^ 2 + fl / 2) := by
    refine absorb_le (sq_nonneg _) hΦδ ?_
    calc ‖G i j‖ ^ 2 ≤ 9 / 4 * ldeRowLHS H G i j := hsq
      _ ≤ 9 / 4 * (Φ * (ldeRowRHS S G i j + fl)) := by linarith
      _ ≤ 9 / 4 * (Φ * ((2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 2 * (2 * δ * ‖G i j‖) ^ 2) + fl)) := by
          gcongr
      _ = 9 / 4 * (Φ * (2 * (∑ k, S i k * ‖G k j‖ ^ 2 + fl / 2)
            + 8 * δ ^ 2 * ‖G i j‖ ^ 2)) := by ring
  nlinarith [mul_nonneg hΦ hfl]

/-- **(4.10), column form, with a floor.** -/
theorem norm_sq_green_le_col_floor (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ j, ∑ l, S l j ≤ 1) (hΦ : 0 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hfl : 0 ≤ fl)
    (hLDE : LDEColFloor H G S Φ fl) {k j : n} (hkj : k ≠ j) :
    ‖G k j‖ ^ 2 ≤ 9 * Φ * (∑ l, S l j * ‖G k l‖ ^ 2 + fl) := by
  have hGjj := hΩ.diag_ne_zero hm hδ j
  have h48 := green_eq_neg_mul_sum_col hGM hGjj hkj
  rw [sum_erase_sub_smul_col] at h48
  have hnorm := congrArg norm h48
  rw [norm_mul, norm_neg] at hnorm
  have hsq : ‖G k j‖ ^ 2 ≤ 9 / 4 * ldeColLHS H G k j := by
    rw [hnorm, ldeColLHS, mul_pow]
    exact mul_le_mul_of_nonneg_right (hΩ.norm_sq_diag_le hm hδ j) (sq_nonneg _)
  have hrhs : ldeColRHS S G k j ≤ 2 * ∑ l, S l j * ‖G k l‖ ^ 2 + 2 * (2 * δ * ‖G k j‖) ^ 2 := by
    have hre : ldeColRHS S G k j = ∑ l ∈ univ.erase j, S l j * ‖greenMinor G j k l‖ ^ 2 := by
      rw [ldeColRHS]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hre]
    refine sum_mul_sq_le_of_le_add _ (fun l => hS0 l j) (hS1 j) (fun _ => norm_nonneg _) ?_
    intro l hl
    have hlj : l ≠ j := Finset.ne_of_mem_erase hl
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ j k l
    have h2 := hΩ.norm_offdiag_le hlj.symm
    have h3 : ‖greenMinor G j k l‖ ≤ ‖G k l‖ + ‖greenMinor G j k l - G k l‖ := by
      calc ‖greenMinor G j k l‖ = ‖G k l + (greenMinor G j k l - G k l)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k j‖ * ‖G j l‖ ≤ ‖G k j‖ * δ :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    linarith
  have hlde := hLDE k j hkj
  have key : ‖G k j‖ ^ 2 ≤ 9 * Φ * (∑ l, S l j * ‖G k l‖ ^ 2 + fl / 2) := by
    refine absorb_le (sq_nonneg _) hΦδ ?_
    calc ‖G k j‖ ^ 2 ≤ 9 / 4 * ldeColLHS H G k j := hsq
      _ ≤ 9 / 4 * (Φ * (ldeColRHS S G k j + fl)) := by linarith
      _ ≤ 9 / 4 * (Φ * ((2 * ∑ l, S l j * ‖G k l‖ ^ 2 + 2 * (2 * δ * ‖G k j‖) ^ 2) + fl)) := by
          gcongr
      _ = 9 / 4 * (Φ * (2 * (∑ l, S l j * ‖G k l‖ ^ 2 + fl / 2)
            + 8 * δ ^ 2 * ‖G k j‖ ^ 2)) := by ring
  nlinarith [mul_nonneg hΦ hfl]

/-- **(4.11) with a floor**: the floor survives the two iterations as `2 fl` inside the same
bracket, `|G_{ij}|² ≤ 81 Φ² (∑_{k,l} S_{ik}|G_{kl}|²S_{lj} + S_{ij} + 2 fl)`. -/
theorem norm_sq_green_le_two_sided_floor (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hfl : 0 ≤ fl) (hLrow : LDERowFloor H G S Φ fl)
    (hLcol : LDEColFloor H G S Φ fl) {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 81 * Φ ^ 2 * ((∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + S i j + 2 * fl) := by
  have hΦ : 0 ≤ Φ := by linarith
  have h1 := norm_sq_green_le_row_floor hMG hm hΩ hδ hS0 hSrow hΦ hΦδ hfl hLrow hij
  have hk : ∀ k, ‖G k j‖ ^ 2
      ≤ 9 * Φ * ((∑ l, S l j * ‖G k l‖ ^ 2) + fl) + (if k = j then 9 / 4 else 0) := by
    intro k
    by_cases hkj : k = j
    · subst hkj
      rw [ite_eq_left rfl]
      have h2 := hΩ.norm_sq_diag_le hm hδ k
      have h3 : 0 ≤ 9 * Φ * ((∑ l, S l k * ‖G k l‖ ^ 2) + fl) :=
        mul_nonneg (by linarith) (by
          have : 0 ≤ ∑ l, S l k * ‖G k l‖ ^ 2 :=
            Finset.sum_nonneg fun l _ => mul_nonneg (hS0 l k) (sq_nonneg _)
          linarith)
      linarith
    · rw [ite_eq_right hkj, add_zero]
      exact norm_sq_green_le_col_floor hGM hm hΩ hδ hS0 hScol hΦ hΦδ hfl hLcol hkj
  have e1 : ∀ k : n, S i k * (9 * Φ * ((∑ l, S l j * ‖G k l‖ ^ 2) + fl)
        + (if k = j then 9 / 4 else 0))
      = 9 * Φ * (∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 * Φ * fl * S i k
        + S i k * (if k = j then 9 / 4 else 0) := by
    intro k
    have hterm : ∑ l, S i k * ‖G k l‖ ^ 2 * S l j = S i k * ∑ l, S l j * ‖G k l‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hterm]; ring
  have hs : ∑ k, S i k * (if k = j then 9 / 4 else 0) = 9 / 4 * S i j := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hsum : ∑ k, S i k * ‖G k j‖ ^ 2
      ≤ 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 * Φ * fl + 9 / 4 * S i j := by
    have hrow := hSrow i
    have hrow0 : 0 ≤ ∑ k, S i k := Finset.sum_nonneg fun k _ => hS0 i k
    have hfl9 : 0 ≤ 9 * Φ * fl := by positivity
    calc ∑ k, S i k * ‖G k j‖ ^ 2
        ≤ ∑ k, S i k * (9 * Φ * ((∑ l, S l j * ‖G k l‖ ^ 2) + fl)
            + (if k = j then 9 / 4 else 0)) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (hS0 i k)
      _ = ∑ k, (9 * Φ * (∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 * Φ * fl * S i k
            + S i k * (if k = j then 9 / 4 else 0)) := Finset.sum_congr rfl fun k _ => e1 k
      _ = 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j)
            + 9 * Φ * fl * (∑ k, S i k) + ∑ k, S i k * (if k = j then 9 / 4 else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 * Φ * fl + 9 / 4 * S i j := by
          rw [hs]
          nlinarith
  have hX : 0 ≤ ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_nonneg (hS0 i k) (sq_nonneg _)) (hS0 l j)
  have hSij := hS0 i j
  have hΦ2 : Φ ≤ Φ ^ 2 := by nlinarith
  have hstep : ‖G i j‖ ^ 2
      ≤ 9 * Φ * ((9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 * Φ * fl
          + 9 / 4 * S i j) + fl) := by
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hΦ2 hSij, mul_le_mul_of_nonneg_right hΦ2 hfl,
    mul_nonneg hΦ hfl, sq_nonneg Φ]

/-- **(4.11) with a floor, in the form used below**: with `Λ` bounding the two terms on the right
*and the floor*, `|G_{ij}|² ≤ 324 Φ² Λ` for `i ≠ j`.  The floor costs a factor `2` against
`RBM.norm_sq_green_offdiag_le`. -/
theorem norm_sq_green_offdiag_le_floor (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hfl : 0 ≤ fl) (hLrow : LDERowFloor H G S Φ fl)
    (hLcol : LDEColFloor H G S Φ fl) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    (hflΛ : fl ≤ Λ) {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 324 * Φ ^ 2 * Λ := by
  have h := norm_sq_green_le_two_sided_floor hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hfl
    hLrow hLcol hij
  have h2 : (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + S i j + 2 * fl ≤ 4 * Λ := by
    linarith [hΛ1 i j, hΛ2 i j]
  have hΦ2 : 0 ≤ 81 * Φ ^ 2 := by positivity
  calc ‖G i j‖ ^ 2
      ≤ 81 * Φ ^ 2 * ((∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + S i j + 2 * fl) := h
    _ ≤ 81 * Φ ^ 2 * (4 * Λ) := mul_le_mul_of_nonneg_left h2 hΦ2
    _ = 324 * Φ ^ 2 * Λ := by ring

/-- The right-hand side of the quadratic LDE, after removing the `(i)` superscript with (4.9) and
using the floored (4.11): `∑_{k,l≠i} S_{ik} |G^(i)_{kl}|² S_{li} ≤ 74 Φ Λ`. -/
theorem ldeQuadRHS_le_floor (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hfl : 0 ≤ fl) (hLrow : LDERowFloor H G S Φ fl)
    (hLcol : LDEColFloor H G S Φ fl) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    (hflΛ : fl ≤ Λ) (i : n) :
    ldeQuadRHS S G i ≤ 74 * Φ * Λ := by
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i i) (hΛ2 i i)
  have hpt : ∀ k ∈ univ.erase i, ∀ l ∈ univ.erase i,
      S i k * ‖greenMinor G i k l‖ ^ 2 * S l i
        ≤ S i k * (2 * ‖G k l‖ ^ 2 + 72 * Φ * Λ) * S l i := by
    intro k hk l hl
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have hli : l ≠ i := Finset.ne_of_mem_erase hl
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k l
    have h2 := hΩ.norm_offdiag_le hli.symm
    have h3 : ‖greenMinor G i k l‖ ≤ ‖G k l‖ + ‖greenMinor G i k l - G k l‖ := by
      calc ‖greenMinor G i k l‖ = ‖G k l + (greenMinor G i k l - G k l)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k i‖ * ‖G i l‖ ≤ ‖G k i‖ * δ :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have h5 : ‖greenMinor G i k l‖ ≤ ‖G k l‖ + 2 * δ * ‖G k i‖ := by linarith
    have h6 := norm_sq_green_offdiag_le_floor hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hfl
      hLrow hLcol hΛ1 hΛ2 hflΛ hki
    have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i i)
    have h7 : ‖greenMinor G i k l‖ ^ 2 ≤ 2 * ‖G k l‖ ^ 2 + 8 * δ ^ 2 * ‖G k i‖ ^ 2 := by
      have := norm_nonneg (greenMinor G i k l)
      nlinarith [sq_nonneg (‖G k l‖ - 2 * δ * ‖G k i‖), norm_nonneg (G k i),
        norm_nonneg (G k l)]
    have h8 : 8 * δ ^ 2 * ‖G k i‖ ^ 2 ≤ 72 * Φ * Λ := by
      have h9 : 8 * δ ^ 2 * ‖G k i‖ ^ 2 ≤ 8 * δ ^ 2 * (324 * Φ ^ 2 * Λ) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      have h10 : 8 * δ ^ 2 * (324 * Φ ^ 2 * Λ) = 72 * (36 * Φ * δ ^ 2) * (Φ * Λ) := by ring
      have h11 : 72 * (36 * Φ * δ ^ 2) * (Φ * Λ) ≤ 72 * 1 * (Φ * Λ) := by
        have : 0 ≤ Φ * Λ := mul_nonneg (by linarith) hΛ0
        nlinarith
      linarith
    have h12 : ‖greenMinor G i k l‖ ^ 2 ≤ 2 * ‖G k l‖ ^ 2 + 72 * Φ * Λ := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h12 (hS0 i k)) (hS0 l i)
  have hnn : ∀ k l, 0 ≤ S i k * (2 * ‖G k l‖ ^ 2 + 72 * Φ * Λ) * S l i := by
    intro k l
    have : 0 ≤ 72 * Φ * Λ := mul_nonneg (by linarith) hΛ0
    exact mul_nonneg (mul_nonneg (hS0 i k) (by positivity)) (hS0 l i)
  calc ldeQuadRHS S G i
      ≤ ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i,
          S i k * (2 * ‖G k l‖ ^ 2 + 72 * Φ * Λ) * S l i :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hpt k hk l hl
    _ ≤ ∑ k, ∑ l, S i k * (2 * ‖G k l‖ ^ 2 + 72 * Φ * Λ) * S l i :=
        sum_sum_le_sum_sum _ hnn
    _ = 2 * ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l i
          + 72 * Φ * Λ * ((∑ k, S i k) * ∑ l, S l i) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ 2 * Λ + 72 * Φ * Λ * (1 * 1) := by
        have h1 := hΛ1 i i
        have h2 : (∑ k, S i k) * ∑ l, S l i ≤ 1 * 1 :=
          mul_le_mul (hSrow i) (hScol i) (Finset.sum_nonneg fun l _ => hS0 l i) zero_le_one
        have h3 : 0 ≤ 72 * Φ * Λ := mul_nonneg (by linarith) hΛ0
        nlinarith
    _ ≤ 74 * Φ * Λ := by nlinarith

/-- **The self-consistent equation behind (4.3), with a floor.**
`G_{ii}⁻¹ = -z - t ∑_k S_{ik} G_{kk} + e_i` with `|e_i|² ≤ 460 Φ² Λ`. -/
theorem norm_sq_selfEnergy_err_le_floor (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hfl : 0 ≤ fl) (hLrow : LDERowFloor H G S Φ fl)
    (hLcol : LDEColFloor H G S Φ fl) (hLquad : LDEQuadFloor H G S t Φ fl)
    (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    (hflΛ : fl ≤ Λ) (i : n) :
    ‖(G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k‖ ^ 2 ≤ 460 * Φ ^ 2 * Λ := by
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i i) (hΛ2 i i)
  have hΦ : 0 ≤ Φ := by linarith
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i i)
  have hGii := hΩ.diag_ne_zero hm hδ i
  have hinv := inv_green_diag_eq hGM hMG hGii
  rw [sum_erase_sub_smul_quad, sub_smul_one_apply_self] at hinv
  set Q := ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, H i k * greenMinor G i k l * H l i with hQ
  set A2 := Q - (t : ℂ) * ∑ k ∈ univ.erase i, (S i k : ℂ) * greenMinor G i k k with hA2
  set A3 := (t : ℂ) * ((S i i : ℂ) * G i i) with hA3
  set A4 := (t : ℂ) * ∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k) with hA4
  have hsplit : ∑ k, (S i k : ℂ) * G k k
      = (S i i : ℂ) * G i i + ∑ k ∈ univ.erase i, (S i k : ℂ) * greenMinor G i k k
        + ∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have heq : (G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k = H i i - A2 + A3 + A4 := by
    rw [hinv, hsplit, hA2, hA3, hA4]
    ring
  rw [heq]
  have hb1 : ‖H i i‖ ^ 2 ≤ Φ * Λ :=
    (hLdiag i).trans (mul_le_mul_of_nonneg_left (hΛ2 i i) hΦ)
  have hb2 : ‖A2‖ ^ 2 ≤ 75 * Φ ^ 2 * Λ := by
    have h1 := hLquad i
    have h2 := ldeQuadRHS_le_floor hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hfl hLrow hLcol
      hΛ1 hΛ2 hflΛ i
    have h3 : ‖A2‖ ^ 2 = ldeQuadLHS H G S t i := rfl
    have h4 : Λ ≤ Φ * Λ := by nlinarith
    calc ‖A2‖ ^ 2 ≤ Φ * (ldeQuadRHS S G i + fl) := h3 ▸ h1
      _ ≤ Φ * (74 * Φ * Λ + Λ) := by
          refine mul_le_mul_of_nonneg_left ?_ hΦ
          linarith
      _ ≤ Φ * (74 * Φ * Λ + Φ * Λ) := by
          refine mul_le_mul_of_nonneg_left ?_ hΦ
          linarith
      _ = 75 * Φ ^ 2 * Λ := by ring
  have hSii1 : S i i ≤ 1 :=
    le_trans (Finset.single_le_sum (fun k _ => hS0 i k) (Finset.mem_univ i)) (hSrow i)
  have hb3 : ‖A3‖ ^ 2 ≤ 9 / 4 * Λ := by
    have hn : ‖A3‖ = t * (S i i * ‖G i i‖) := by
      rw [hA3, norm_mul, norm_mul, Complex.norm_of_nonneg ht0, Complex.norm_of_nonneg (hS0 i i)]
    have h1 := hΩ.norm_sq_diag_le hm hδ i
    have h2 : ‖A3‖ ^ 2 ≤ S i i ^ 2 * ‖G i i‖ ^ 2 := by
      have h0 : 0 ≤ S i i * ‖G i i‖ := mul_nonneg (hS0 i i) (norm_nonneg _)
      have h5 : t * (S i i * ‖G i i‖) ≤ S i i * ‖G i i‖ := by nlinarith
      calc ‖A3‖ ^ 2 = (t * (S i i * ‖G i i‖)) ^ 2 := by rw [hn]
        _ ≤ (S i i * ‖G i i‖) ^ 2 := pow_le_pow_left₀ (mul_nonneg ht0 h0) h5 2
        _ = S i i ^ 2 * ‖G i i‖ ^ 2 := by ring
    have h3 : S i i ^ 2 ≤ Λ := by nlinarith [hS0 i i, hΛ2 i i]
    have h4 : S i i ^ 2 * ‖G i i‖ ^ 2 ≤ Λ * (9 / 4) :=
      mul_le_mul h3 h1 (sq_nonneg _) hΛ0
    linarith
  have hb4 : ‖A4‖ ^ 2 ≤ 36 * Φ * Λ := by
    have hpt : ∀ k ∈ univ.erase i,
        ‖(S i k : ℂ) * (G k k - greenMinor G i k k)‖ ≤ S i k * (2 * δ * ‖G i k‖) := by
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      rw [norm_mul, Complex.norm_of_nonneg (hS0 i k), norm_sub_rev]
      refine mul_le_mul_of_nonneg_left ?_ (hS0 i k)
      have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k k
      have h2 := hΩ.norm_offdiag_le hki
      have h3 : ‖G k i‖ * ‖G i k‖ ≤ δ * ‖G i k‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      linarith
    have hA4le : ‖A4‖ ≤ ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) := by
      rw [hA4, norm_mul, Complex.norm_of_nonneg ht0]
      calc t * ‖∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k)‖
          ≤ 1 * ‖∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k)‖ :=
            mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ ≤ ∑ k ∈ univ.erase i, ‖(S i k : ℂ) * (G k k - greenMinor G i k k)‖ := by
            rw [one_mul]; exact norm_sum_le _ _
        _ ≤ _ := Finset.sum_le_sum hpt
    have hCS : (∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖)) ^ 2
        ≤ (∑ k ∈ univ.erase i, S i k) * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun k _ => hS0 i k)
        (fun k _ => mul_nonneg (hS0 i k) (sq_nonneg _)) fun k _ => le_of_eq (by ring)
    have hE1 : ∑ k ∈ univ.erase i, S i k ≤ 1 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i univ)
        fun k _ _ => hS0 i k) (hSrow i)
    have hE2 : ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2
        ≤ ∑ k ∈ univ.erase i, S i k * (4 * δ ^ 2 * (324 * Φ ^ 2 * Λ)) := by
      refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (hS0 i k)
      have hki : i ≠ k := (Finset.ne_of_mem_erase hk).symm
      have h1 := norm_sq_green_offdiag_le_floor hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hfl
        hLrow hLcol hΛ1 hΛ2 hflΛ hki
      calc (2 * δ * ‖G i k‖) ^ 2 = 4 * δ ^ 2 * ‖G i k‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hE3 : ∑ k ∈ univ.erase i, S i k * (4 * δ ^ 2 * (324 * Φ ^ 2 * Λ))
        ≤ 4 * δ ^ 2 * (324 * Φ ^ 2 * Λ) := by
      rw [← Finset.sum_mul]
      have : 0 ≤ 4 * δ ^ 2 * (324 * Φ ^ 2 * Λ) := by positivity
      nlinarith
    have hE4 : 4 * δ ^ 2 * (324 * Φ ^ 2 * Λ) ≤ 36 * Φ * Λ := by
      have h1 : 4 * δ ^ 2 * (324 * Φ ^ 2 * Λ) = 36 * (36 * Φ * δ ^ 2) * (Φ * Λ) := by ring
      have h2 : 0 ≤ Φ * Λ := mul_nonneg hΦ hΛ0
      nlinarith
    have hS : 0 ≤ ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hS0 i k) (sq_nonneg _)
    have hA4sq : ‖A4‖ ^ 2 ≤ (∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hA4le 2
    have hE5 : (∑ k ∈ univ.erase i, S i k) * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2
        ≤ 1 * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 :=
      mul_le_mul_of_nonneg_right hE1 hS
    linarith
  -- assemble
  have htri : ‖H i i - A2 + A3 + A4‖ ≤ ‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖ := by
    calc ‖H i i - A2 + A3 + A4‖ ≤ ‖H i i - A2 + A3‖ + ‖A4‖ := norm_add_le _ _
      _ ≤ ‖H i i - A2‖ + ‖A3‖ + ‖A4‖ := by linarith [norm_add_le (H i i - A2) A3]
      _ ≤ ‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖ := by linarith [norm_sub_le (H i i) A2]
  have hsq : ‖H i i - A2 + A3 + A4‖ ^ 2
      ≤ 4 * (‖H i i‖ ^ 2 + ‖A2‖ ^ 2 + ‖A3‖ ^ 2 + ‖A4‖ ^ 2) := by
    have h0 := norm_nonneg (H i i - A2 + A3 + A4)
    have h1 : ‖H i i - A2 + A3 + A4‖ ^ 2 ≤ (‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖) ^ 2 :=
      pow_le_pow_left₀ h0 htri 2
    nlinarith [sq_nonneg (‖H i i‖ - ‖A2‖), sq_nonneg (‖H i i‖ - ‖A3‖),
      sq_nonneg (‖H i i‖ - ‖A4‖), sq_nonneg (‖A2‖ - ‖A3‖), sq_nonneg (‖A2‖ - ‖A4‖),
      sq_nonneg (‖A3‖ - ‖A4‖)]
  have hΦΛ : Φ * Λ ≤ Φ ^ 2 * Λ := by
    have : Φ ≤ Φ ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hΛ0
  have hΛΦ : Λ ≤ Φ ^ 2 * Λ := by
    have : 1 ≤ Φ ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-- **(4.3), deterministic form, with a floor.**  `|G_{ii} - m|² ≤ 4140 K² Φ² Λ`, where `Λ`
bounds `∑_{k,l} S_{ik}|G_{kl}|²S_{lj}`, `S_{ij}` **and the floor**. -/
theorem norm_sq_green_diag_sub_le_floor [Nonempty n]
    (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1) {t : ℝ}
    (hmz : m * ((t : ℂ) * m + z) = -1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hΩ : GoodEvent G m δ)
    (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k) (hSrow : ∀ i, ∑ k, S i k = 1)
    (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hfl : 0 ≤ fl)
    (hLrow : LDERowFloor H G S Φ fl) (hLcol : LDEColFloor H G S Φ fl)
    (hLquad : LDEQuadFloor H G S t Φ fl)
    (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    (hflΛ : fl ≤ Λ) {K : ℝ} (hKδ : K * δ ≤ 1 / 2) (hStab : Stable S ((t : ℂ) * m ^ 2) K)
    (i : n) :
    ‖G i i - m‖ ^ 2 ≤ 4140 * K ^ 2 * Φ ^ 2 * Λ := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i₀ i₀) (hΛ2 i₀ i₀)
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i₀ i₀)
  have hSrow' : ∀ i, ∑ k, S i k ≤ 1 := fun i => (hSrow i).le
  have hm0 : m ≠ 0 := by
    intro h; rw [h, norm_zero] at hm; exact zero_ne_one hm
  set ε := Real.sqrt (460 * Φ ^ 2 * Λ) with hε
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  set e : n → ℂ := fun i => (G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k with he
  have heb : ∀ i, ‖e i‖ ≤ ε := by
    intro i
    rw [hε, Real.le_sqrt (norm_nonneg _) (by positivity)]
    exact norm_sq_selfEnergy_err_le_floor hGM hMG hm ht0 ht1 hΩ hδ hS0 hSrow' hScol hΦ1 hΦδ
      hfl hLrow hLcol hLquad hLdiag hΛ1 hΛ2 hflΛ i
  set v : n → ℂ := fun k => G k k - m with hv
  have hvδ : ∀ k, ‖v k‖ ≤ δ := fun k => hΩ.norm_diag_sub_le k
  obtain ⟨k₀, hk₀⟩ := Finite.exists_max fun k => ‖v k‖
  set V := ‖v k₀‖ with hV
  have hident : ∀ i, v i - (t : ℂ) * m ^ 2 * ∑ k, (S i k : ℂ) * v k
      = -(m ^ 2 * e i) + m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i) := by
    intro i
    have hGii := hΩ.diag_ne_zero hm hδ i
    have hSv : ∑ k, (S i k : ℂ) * G k k = ∑ k, (S i k : ℂ) * v k + m := by
      have h1 : ∑ k, (S i k : ℂ) * v k = ∑ k, (S i k : ℂ) * G k k - m := by
        have h2 : ∑ k, (S i k : ℂ) = 1 := by exact_mod_cast hSrow i
        rw [hv]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h2, one_mul]
      rw [h1]; ring
    have hinv : (G i i)⁻¹ = m⁻¹ - ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i) := by
      have hz : z = -m⁻¹ - (t : ℂ) * m := by
        field_simp
        linear_combination hmz
      simp only [he, hSv, hz]
      ring
    have h1 : G i i * (m⁻¹ - ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)) = 1 := by
      rw [← hinv]; exact mul_inv_cancel₀ hGii
    have hmm : m * m⁻¹ = 1 := mul_inv_cancel₀ hm0
    simp only [hv]
    linear_combination m * h1 - G i i * hmm
  have hSvb : ∀ i, ‖∑ k, (S i k : ℂ) * v k‖ ≤ V := by
    intro i
    calc ‖∑ k, (S i k : ℂ) * v k‖ ≤ ∑ k, ‖(S i k : ℂ) * v k‖ := norm_sum_le _ _
      _ ≤ ∑ k, S i k * V := Finset.sum_le_sum fun k _ => by
          rw [norm_mul, Complex.norm_of_nonneg (hS0 i k)]
          exact mul_le_mul_of_nonneg_left (hk₀ k) (hS0 i k)
      _ = V := by rw [← Finset.sum_mul, hSrow i, one_mul]
  have hBi : ∀ i, ‖v i - (t : ℂ) * m ^ 2 * ∑ k, (S i k : ℂ) * v k‖ ≤ 3 / 2 * ε + δ * V := by
    intro i
    rw [hident i]
    have hx : ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖ ≤ V + ε := by
      calc ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖
          ≤ ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k‖ + ‖e i‖ := norm_sub_le _ _
        _ ≤ V + ε := by
          rw [norm_mul, Complex.norm_of_nonneg ht0]
          have h1 := hSvb i
          have h2 : t * ‖∑ k, (S i k : ℂ) * v k‖ ≤ 1 * V :=
            mul_le_mul ht1 h1 (norm_nonneg _) zero_le_one
          linarith [heb i]
    have hV0 : 0 ≤ V := norm_nonneg _
    calc ‖-(m ^ 2 * e i) + m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)‖
        ≤ ‖-(m ^ 2 * e i)‖ + ‖m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)‖ :=
          norm_add_le _ _
      _ = ‖e i‖ + ‖v i‖ * ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖ := by
          rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_pow, hm]; ring
      _ ≤ ε + δ * (V + ε) := by
          have := mul_le_mul (hvδ i) hx (norm_nonneg _) hδ0
          linarith [heb i]
      _ ≤ 3 / 2 * ε + δ * V := by nlinarith
  have hst := hStab v (3 / 2 * ε + δ * V) hBi
  have hVb : V ≤ 3 * K * ε := by
    have h1 := hst k₀
    have h2 : K * (δ * V) ≤ 1 / 2 * V := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hKδ (norm_nonneg _)
    rw [← hV] at h1
    nlinarith
  have hvi : ‖v i‖ ≤ 3 * K * ε := (hk₀ i).trans hVb
  have hsq : ‖v i‖ ^ 2 ≤ (3 * K * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvi 2
  have hε2 : ε ^ 2 = 460 * Φ ^ 2 * Λ := Real.sq_sqrt (by positivity)
  calc ‖G i i - m‖ ^ 2 = ‖v i‖ ^ 2 := rfl
    _ ≤ (3 * K * ε) ^ 2 := hsq
    _ = 9 * K ^ 2 * ε ^ 2 := by ring
    _ = 4140 * K ^ 2 * Φ ^ 2 * Λ := by rw [hε2]; ring

end EntryFloor

section BlkFloor

open Finset

variable (L : ℕ) [NeZero L] {W : ℕ} [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

/-- **(4.2) in the block model, with a floor** — `RBM.norm_sq_green_le_blk` with `2 fl`
added inside the bracket. -/
theorem norm_sq_green_le_blk_floor (hL : 3 ≤ L) (hH : H.IsHermitian) (hz : z.im ≠ 0) {m : ℂ}
    (hm : ‖m‖ = 1) {δ : ℝ} (hΩ : GoodEvent (green H z) m δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ}
    (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) {fl : ℝ} (hfl : 0 ≤ fl)
    (hLrow : LDERowFloor H (green H z) (Sblk L W) Φ fl)
    (hLcol : LDEColFloor H (green H z) (Sblk L W) Φ fl)
    {i j : ZMod L × Fin W} (hij : i ≠ j) :
    ‖green H z i j‖ ^ 2 ≤ 81 * Φ ^ 2 * ((∑ u ∈ sbSupport L, ∑ v ∈ sbSupport L,
        Lre H z (j.1 + v) (i.1 + u))
      + (if i.1 - j.1 ∈ sbSupport L then (W : ℝ)⁻¹ else 0) + 2 * fl) := by
  have h := norm_sq_green_le_two_sided_floor (green_mul_sub_of_im hH hz)
    (sub_mul_green_of_im hH hz) hm hΩ hδ Sblk_nonneg (fun i => (sum_Sblk_row hL i).le)
    (fun j => (sum_Sblk_col hL j).le) hΦ1 hΦδ hfl hLrow hLcol hij
  rw [sum_sum_Sblk_eq_nbr hH] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h1 : 0 ≤ ∑ u ∈ sbSupport L, ∑ v ∈ sbSupport L, Lre H z (j.1 + v) (i.1 + u) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Lre_nonneg hH _ _
  have h2 := Sblk_le (L := L) (W := W) i j
  linarith

/-- **(4.3) in the block model, with a floor** — `RBM.norm_sq_green_diag_sub_le_blk` with the
floor riding additively next to `L^max`:
`|G_{ii} - m|² ≤ 8280 K_κ² Φ² (max_{a,b} L_{(+,-),(a,b)} + fl)`.

This is the (4.3) kernel that T166's `RBM.Gauss.stochDom_ldeQuad_flow_floor` and T148's
`RBM.Gauss.stochDom_ldeRow_flow_floor`/`_ldeCol_flow_floor` feed, and it is what
`RBM.Gauss.DiagBoundFlow` needs in order to be produced along the flow. -/
theorem norm_sq_green_diag_sub_le_blk_floor (hL : 3 ≤ L) (hH : H.IsHermitian) {E κ t : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) {δ : ℝ}
    (hΩ : GoodEvent (green H (zt E t)) (mE E) δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ} (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hKδ : Kstab κ * δ ≤ 1 / 2) {fl : ℝ} (hfl : 0 ≤ fl)
    (hLrow : LDERowFloor H (green H (zt E t)) (Sblk L W) Φ fl)
    (hLcol : LDEColFloor H (green H (zt E t)) (Sblk L W) Φ fl)
    (hLquad : LDEQuadFloor H (green H (zt E t)) (Sblk L W) t Φ fl)
    (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * Sblk L W i i) (i : ZMod L × Fin W) :
    ‖green H (zt E t) i i - mE E‖ ^ 2
      ≤ 8280 * Kstab κ ^ 2 * Φ ^ 2 * (Lmax H (zt E t) + fl) := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hz := zt_im_ne_zero hκ0 hE ht1
  have hm := norm_mE hE2
  have hL0 := Lmax_nonneg (z := zt E t) hH
  have hK0 : 0 ≤ Kstab κ := Kstab_nonneg
  have h := norm_sq_green_diag_sub_le_floor (green_mul_sub_of_im hH hz)
    (sub_mul_green_of_im hH hz) hm (mE_mul_add_zt hE2 t) ht0 ht1.le hΩ hδ Sblk_nonneg
    (sum_Sblk_row hL) (fun j => (sum_Sblk_col hL j).le) hΦ1 hΦδ hfl hLrow hLcol hLquad hLdiag
    (Λ := 2 * Lmax H (zt E t) + fl)
    (fun i j => by linarith [sum_sum_Sblk_le_Lmax hL hH (z := zt E t) i j])
    (fun i j => by linarith [Sblk_le_Lmax hH hm hΩ hδ i j])
    (by linarith) hKδ (stable_Sblk_short_edge hL hκ0 hκ1 hE ht0 ht1) i
  have hKsq : 0 ≤ Kstab κ ^ 2 := sq_nonneg _
  have hΦsq : 0 ≤ Φ ^ 2 := sq_nonneg _
  nlinarith [h, mul_nonneg (mul_nonneg hKsq hΦsq) hL0,
    mul_nonneg (mul_nonneg hKsq hΦsq) hfl]

end BlkFloor

section RandomModelFloor

open Filter MeasureTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
variable {L W : ℕ → ℕ} [∀ N, NeZero (L N)] [∀ N, NeZero (W N)]

/-- **Lemma 4.1, (4.3), with an additive floor in the large deviation inputs.**

Word for word `RBM.diag_bound_stochDom`, except that the three large deviation hypotheses carry
the additive floor `fl N` in their controls and the conclusion carries it next to `L^max`.  This
is the slot that `RBM.Gauss.stochDom_ldeRow_flow_floor`, `RBM.Gauss.stochDom_ldeCol_flow_floor`
(T148) and `RBM.Gauss.stochDom_ldeQuad_flow_floor` (T166) fill.  `hLdiag` is **not** floored:
its producer `RBM.Gauss.stochDom_normSq_Hflow_diag` is unconditional. -/
theorem diag_bound_stochDom_floor (hL : ∀ N, 3 ≤ L N)
    (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ) (hH : ∀ N ω, (H N ω).IsHermitian)
    {E κ t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) {fl : ℕ → ℝ} (hfl0 : ∀ N, 0 ≤ fl N)
    (hLrow : StochDom P
      (fun N (u : OffPair L W N) ω =>
        ldeRowLHS (H N ω) (green (H N ω) (zt E t)) u.1.1 u.1.2)
      (fun N u ω =>
        ldeRowRHS (Sblk (L N) (W N)) (green (H N ω) (zt E t)) u.1.1 u.1.2 + fl N))
    (hLcol : StochDom P
      (fun N (u : OffPair L W N) ω =>
        ldeColLHS (H N ω) (green (H N ω) (zt E t)) u.1.1 u.1.2)
      (fun N u ω =>
        ldeColRHS (Sblk (L N) (W N)) (green (H N ω) (zt E t)) u.1.1 u.1.2 + fl N))
    (hLquad : StochDom P
      (fun N (i : BIdx L W N) ω =>
        ldeQuadLHS (H N ω) (green (H N ω) (zt E t)) (Sblk (L N) (W N)) t i)
      (fun N i ω => ldeQuadRHS (Sblk (L N) (W N)) (green (H N ω) (zt E t)) i + fl N))
    (hLdiag : StochDom P (fun N (i : BIdx L W N) ω => ‖H N ω i i‖ ^ 2)
      (fun N i _ => Sblk (L N) (W N) i i)) :
    StochDom P
      (fun N (i : BIdx L W N) ω =>
        (goodSet H (zt E t) (mE E) δ N).indicator
          (fun ω => ‖green (H N ω) (zt E t) i i - mE E‖ ^ 2) ω)
      (fun N _ ω => Lmax (H N ω) (zt E t) + fl N) := by
  have hK1 : 1 ≤ Kstab κ := one_le_Kstab
  have hK0 : 0 < Kstab κ := by linarith
  have hε₀ : (0 : ℝ) < 1 / (2 * Kstab κ) := by positivity
  refine StochDom.of_det (((hLrow.sumElim hLcol).sumElim hLquad).sumElim hLdiag)
    (fun N _ ω => by
      have := Lmax_nonneg (z := zt E t) (hH N ω)
      have := hfl0 N
      linarith)
    hδ0 hc₀ hδ hε₀ (8280 * Kstab κ ^ 2) 2 ?_
  intro N ω Φ hΦ1 hΦδ hδε hAB i
  have hL0 := Lmax_nonneg (z := zt E t) (hH N ω)
  have hflN := hfl0 N
  by_cases hω : ω ∈ goodSet H (zt E t) (mE E) δ N
  · rw [Set.indicator_of_mem hω]
    have hδ12 : δ N ≤ 1 / 2 := by
      refine hδε.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hKδ : Kstab κ * δ N ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hδε hK0.le
      rwa [show Kstab κ * (1 / (2 * Kstab κ)) = 1 / 2 by field_simp] at this
    have hLr : LDERowFloor (H N ω) (green (H N ω) (zt E t)) (Sblk (L N) (W N)) Φ (fl N) :=
      fun i j hij => hAB (Sum.inl (Sum.inl (Sum.inl ⟨(i, j), hij⟩)))
    have hLc : LDEColFloor (H N ω) (green (H N ω) (zt E t)) (Sblk (L N) (W N)) Φ (fl N) :=
      fun k j hkj => hAB (Sum.inl (Sum.inl (Sum.inr ⟨(k, j), hkj⟩)))
    have hLq : LDEQuadFloor (H N ω) (green (H N ω) (zt E t)) (Sblk (L N) (W N)) t Φ (fl N) :=
      fun i => hAB (Sum.inl (Sum.inr i))
    have hLd : ∀ i, ‖H N ω i i‖ ^ 2 ≤ Φ * Sblk (L N) (W N) i i :=
      fun i => hAB (Sum.inr i)
    exact norm_sq_green_diag_sub_le_blk_floor (L N) (hL N) (hH N ω) hκ0 hκ1 hE ht0 ht1
      hω hδ12 hΦ1 hΦδ hKδ hflN hLr hLc hLq hLd i
  · rw [Set.indicator_of_notMem hω]
    have hΦ0 : 0 ≤ Φ := by linarith
    positivity

/-- **Lemma 4.1, (4.3), with an additive floor *and* the time inside the index set.**

`RBM.diag_bound_stochDom` fixes the matrix `H` and the spectral parameter `z_t`.  Along a flow
they both move with the index, so the index type is `U N × BIdx L W N` and the matrix is a
family `Hf N u ω` at a time `uf N q` read off the index.  Nothing else changes:
`RBM.StochDom.of_det` takes arbitrary index types, and the deterministic kernel
`RBM.norm_sq_green_diag_sub_le_blk_floor` is applied at the index's own time.

This is the shape `RBM.Gauss.DiagBoundFlow` needs.  Its four inputs along the Gaussian flow are
`RBM.Gauss.stochDom_ldeRow_flow_floor`, `RBM.Gauss.stochDom_ldeCol_flow_floor` (T148),
`RBM.Gauss.stochDom_ldeQuad_flow_floor` (T166), and a time-indexed form of
`RBM.Gauss.stochDom_normSq_Hflow_diag`. -/
theorem diag_bound_stochDom_floor_idx {U : ℕ → Type*} (hL : ∀ N, 3 ≤ L N)
    (Hf : ∀ N, ℝ → Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ)
    (uf : ∀ N, U N → ℝ) (hH : ∀ N u ω, (Hf N u ω).IsHermitian)
    {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    (ht0 : ∀ N q, 0 ≤ uf N q) (ht1 : ∀ N q, uf N q < 1)
    {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) {fl : ℕ → ℝ} (hfl0 : ∀ N, 0 ≤ fl N)
    (hLrow : StochDom P
      (fun N (q : U N × OffPair L W N) ω =>
        ldeRowLHS (Hf N (uf N q.1) ω) (green (Hf N (uf N q.1) ω) (zt E (uf N q.1)))
          q.2.1.1 q.2.1.2)
      (fun N q ω =>
        ldeRowRHS (Sblk (L N) (W N)) (green (Hf N (uf N q.1) ω) (zt E (uf N q.1)))
          q.2.1.1 q.2.1.2 + fl N))
    (hLcol : StochDom P
      (fun N (q : U N × OffPair L W N) ω =>
        ldeColLHS (Hf N (uf N q.1) ω) (green (Hf N (uf N q.1) ω) (zt E (uf N q.1)))
          q.2.1.1 q.2.1.2)
      (fun N q ω =>
        ldeColRHS (Sblk (L N) (W N)) (green (Hf N (uf N q.1) ω) (zt E (uf N q.1)))
          q.2.1.1 q.2.1.2 + fl N))
    (hLquad : StochDom P
      (fun N (q : U N × BIdx L W N) ω =>
        ldeQuadLHS (Hf N (uf N q.1) ω) (green (Hf N (uf N q.1) ω) (zt E (uf N q.1)))
          (Sblk (L N) (W N)) (uf N q.1) q.2)
      (fun N q ω =>
        ldeQuadRHS (Sblk (L N) (W N)) (green (Hf N (uf N q.1) ω) (zt E (uf N q.1))) q.2
          + fl N))
    (hLdiag : StochDom P
      (fun N (q : U N × BIdx L W N) ω => ‖Hf N (uf N q.1) ω q.2 q.2‖ ^ 2)
      (fun N (q : U N × BIdx L W N) _ => Sblk (L N) (W N) q.2 q.2)) :
    StochDom P
      (fun N (q : U N × BIdx L W N) ω =>
        Set.indicator
          {ω | GoodEvent (green (Hf N (uf N q.1) ω) (zt E (uf N q.1))) (mE E) (δ N)}
          (fun ω => ‖green (Hf N (uf N q.1) ω) (zt E (uf N q.1)) q.2 q.2 - mE E‖ ^ 2) ω)
      (fun N q ω => Lmax (Hf N (uf N q.1) ω) (zt E (uf N q.1)) + fl N) := by
  have hK1 : 1 ≤ Kstab κ := one_le_Kstab
  have hK0 : 0 < Kstab κ := by linarith
  have hε₀ : (0 : ℝ) < 1 / (2 * Kstab κ) := by positivity
  refine StochDom.of_det (((hLrow.sumElim hLcol).sumElim hLquad).sumElim hLdiag)
    (fun N q ω => by
      have := Lmax_nonneg (z := zt E (uf N q.1)) (hH N (uf N q.1) ω)
      have := hfl0 N
      linarith)
    hδ0 hc₀ hδ hε₀ (8280 * Kstab κ ^ 2) 2 ?_
  intro N ω Φ hΦ1 hΦδ hδε hAB q
  have hL0 := Lmax_nonneg (z := zt E (uf N q.1)) (hH N (uf N q.1) ω)
  have hflN := hfl0 N
  by_cases hω : ω ∈ {ω | GoodEvent (green (Hf N (uf N q.1) ω) (zt E (uf N q.1))) (mE E) (δ N)}
  · rw [Set.indicator_of_mem hω]
    have hδ12 : δ N ≤ 1 / 2 := by
      refine hδε.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hKδ : Kstab κ * δ N ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hδε hK0.le
      rwa [show Kstab κ * (1 / (2 * Kstab κ)) = 1 / 2 by field_simp] at this
    have hLr : LDERowFloor (Hf N (uf N q.1) ω)
        (green (Hf N (uf N q.1) ω) (zt E (uf N q.1))) (Sblk (L N) (W N)) Φ (fl N) :=
      fun i j hij => hAB (Sum.inl (Sum.inl (Sum.inl (q.1, ⟨(i, j), hij⟩))))
    have hLc : LDEColFloor (Hf N (uf N q.1) ω)
        (green (Hf N (uf N q.1) ω) (zt E (uf N q.1))) (Sblk (L N) (W N)) Φ (fl N) :=
      fun k j hkj => hAB (Sum.inl (Sum.inl (Sum.inr (q.1, ⟨(k, j), hkj⟩))))
    have hLq : LDEQuadFloor (Hf N (uf N q.1) ω)
        (green (Hf N (uf N q.1) ω) (zt E (uf N q.1))) (Sblk (L N) (W N))
        (uf N q.1) Φ (fl N) :=
      fun i => hAB (Sum.inl (Sum.inr (q.1, i)))
    have hLd : ∀ i, ‖Hf N (uf N q.1) ω i i‖ ^ 2 ≤ Φ * Sblk (L N) (W N) i i :=
      fun i => hAB (Sum.inr (q.1, i))
    exact norm_sq_green_diag_sub_le_blk_floor (L N) (hL N) (hH N (uf N q.1) ω) hκ0 hκ1 hE
      (ht0 N q.1) (ht1 N q.1) hω hδ12 hΦ1 hΦδ hKδ hflN hLr hLc hLq hLd q.2
  · rw [Set.indicator_of_notMem hω]
    have hΦ0 : 0 ≤ Φ := by linarith
    positivity

end RandomModelFloor

end RBM
