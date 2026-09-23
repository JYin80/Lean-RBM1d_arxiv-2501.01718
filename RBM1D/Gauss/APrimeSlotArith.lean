/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSlotDriftCore
import RBM1D.Gauss.APrimeModel

/-!
# T276 — the slot arithmetic: `hfit` and `hbudget` become theorems

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.39)–(5.48), along the repaired route (A′) of the V548 referee report, §5.

T271 (`RBM1D/Gauss/APrimeModel.lean`) left exactly two arithmetic obligations open — its
"remaining item 4":

* `hfit` — the hypothesis of `RBM.APrimeModel.drift_bound_first_cell`, an inequality between
  T268's explicit first-cell output and the `drift` slot of `RBM.StepSideAPrime.stepRhs''`;
* `hbudget` — the hypothesis of `RBM.APrimeModel.qv_bound_model`, an inequality between T269's
  explicit envelope `Q^{bd}` and the square of the `tail` slot.

Both are inequalities between two **deterministic** numbers (no `ω`, no `∃ C`), so they are
checkable; this file checks them, at the *concrete* slot values of T263's factor-2 margin
witness `RBM.StepSideAPrime.sat_StepSide''_half`.

## The `p`-dependent constants

The quantifier order of route (A′) is `∀ δ, ∀ p, ∀ᶠ N in atTop` — `N` is chosen **after** `p`.
Consequently any constant `c_p` that depends on `p` alone (`√(2p−1)` of the weighted
Burkholder–Davis–Gundy step, `c_MD`, `‖χ′‖·p`, …) satisfies `c_p ≤ N^{η}` eventually, for
*every* `η > 0` (`eventually_const_mul_rpow_le`).  Taking the `≺`-parameter of each envelope
below `δ/16` makes `c_p·N^{η}` fall inside the factor `x = N^{δ/8}` that `stepRhs''` already
carries — which is what that `x` is there for.  **This is the main route; the primed
`WeightedMoment'` fallback of the ticket is not needed.**

The exponent account, once:

* the `tail` slot contributes `x⁴ = N^{δ/2}` (through `κ = x/2` and one `x·R²`), so the
  `hbudget` inequality has room for any envelope exponent `η < δ/2`;
* the `drift` slot contributes `x² = N^{δ/4}` (through `Ξ = x/2` and `q = R²/2`), so `hfit`
  has room for any envelope exponent `η < δ/4`.

`η < δ/16` therefore covers both at once (`eventually_slot_arith`).

## Satisfiability

The project's dominant defect is a compiled, axiom-clean theorem whose hypotheses cannot be
met.  `sat_slot_arith` is a **compiled witness**: explicit `δ, η, ε_s, m, E`, a window ratio
`R = 2 > 1` (so the window is genuinely non-collapsed), a **strictly positive** envelope
`G ≡ 1` and a **strictly positive** first-cell left-hand side, with all hypotheses of
`eventually_slot_arith` discharged and the conclusion non-vacuous
(`sat_slot_arith_nondegenerate`).

## Main results

* `eventually_const_mul_rpow_le` — the absorption step (`c_p·N^η ≤ N^θ` eventually, `η < θ`).
* `driftTerm_slot_ge`, `sq_tailTerm_slot_ge` — the two slot lower bounds, pure algebra.
* `eventually_hfit`, `eventually_hbudget` — the two obligations, as theorems, in the shape
  `∀ p, ∀ᶠ N in atTop`.
* `eventually_slot_arith` — both, together with T263's `StepSide''` bundle.
* `sat_slot_arith`, `sat_slot_arith_nondegenerate` — the compiled satisfiability witness.
* `drift_bound_first_cell_slot`, `qv_bound_model_slot` — the wiring check: the two shapes
  land in T271's consumers verbatim.
* `eventually_slot_arith_of_detDom` — the same, driven by `≺`-envelopes, with no exponent
  left for the caller to choose.
-/

namespace RBM

namespace APrimeSlotArith

open Filter Real MeasureTheory
open StepSideAPrime APrimeOneStep APrimePrior APrimeModel

/-! ### 1. The eight slot values of T263's margin witness, named -/

/-- The cross-term slot `κ` of `RBM.StepSideAPrime.sat_StepSide''_half`. -/
noncomputable def slotKappa (x : ℝ) : ℝ := x / 2

/-- T263's side-condition bundle, read at the eight slot values above. -/
def SlotSide (x R : ℝ) : Prop :=
  StepSide'' x R (slotXi x) (slotA x R) (slotEps x R) (slotQ R) (slotBeta x R)
    (slotGamma x R) (slotKappa x) (slotJv x R)

/-- The `tail` slot of `RBM.APrimeOneStep.stepRhs''_div_of_slots`, at the eight values: this
is the `c` that `RBM.APrimeModel.qv_bound_model` must beat. -/
noncomputable def slotTail (x R : ℝ) : ℝ := tailTerm x R (slotKappa x) / R ^ 4

/-- **The slot values do satisfy T263's bundle**, with the factor-2 margin of
`RBM.StepSideAPrime.sat_StepSide''_half` in every constraint that has a direction. -/
theorem slotSide {x R : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) : SlotSide x R :=
  sat_StepSide''_half hx hR

theorem slotTail_nonneg {x R : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) : 0 ≤ slotTail x R := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  unfold slotTail tailTerm slotKappa
  positivity

/-! ### 2. The tail-slot lower bound — pure algebra -/

/-- **The tail slot is at least its `κ`-term.**  The three constant terms
`x·R² + x + 1` of `RBM.APrimeOneStep.tailTerm` only help. -/
theorem tailTerm_ge_kappa {x R κ : ℝ} (hx : 0 ≤ x) :
    x * R ^ 2 * κ ≤ tailTerm x R κ := by
  have h : (0 : ℝ) ≤ x * (R ^ 2 + 1) :=
    mul_nonneg hx (by positivity)
  unfold tailTerm
  linarith

/-- **⭐ The tail slot, squared, at T263's witness value `κ = x/2`.**  The one-step budget
of `RBM.APrimeModel.qv_bound_model` is a bound on `c²`, and `c² ≥ x⁴/(4R⁴)`: the factor `x⁴`
is `N^{δ/2}`, which is where the `p`-dependent constants go. -/
theorem sq_tailTerm_slot_ge {x R : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) :
    x ^ 4 / (4 * R ^ 4) ≤ (slotTail x R) ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hlow : x ^ 2 / (2 * R ^ 2) ≤ slotTail x R := by
    have h := tailTerm_ge_kappa (x := x) (R := R) (κ := slotKappa x) hx0.le
    have hk : x * R ^ 2 * slotKappa x = x ^ 2 * R ^ 2 / 2 := by unfold slotKappa; ring
    rw [hk] at h
    unfold slotTail
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < R ^ 4), div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < 2 * R ^ 2)]
    nlinarith [h, (by positivity : (0 : ℝ) < R ^ 2)]
  have h0 : (0 : ℝ) ≤ x ^ 2 / (2 * R ^ 2) := by positivity
  have hsq : x ^ 4 / (4 * R ^ 4) = (x ^ 2 / (2 * R ^ 2)) ^ 2 := by
    field_simp
    ring
  rw [hsq]
  exact pow_le_pow_left₀ h0 hlow 2

/-! ### 3. Absorbing the `p`-dependent constants

`N` is chosen **after** `p`, so a constant depending on `p` alone costs an arbitrarily small
power of `N`.  This is the whole content of the "`p`-bottleneck" that T260 flagged. -/

/-- **⭐ The absorption step.**  For `0 ≤ η < θ` and any constant `c` — in particular any
`c_p` depending on `p` alone — one has `c·N^{η} ≤ N^{θ}` for all large `N`.

⚠ The statement is `∀ᶠ N in atTop` with `c` fixed **beforehand**: written as `∀ c N, …` it
would be unsatisfiable (let `c → ∞` at fixed `N`).  This is T188's quantifier discipline. -/
theorem eventually_const_mul_rpow_le {c η θ : ℝ} (hη : η < θ) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ η ≤ (N : ℝ) ^ θ := by
  filter_upwards [eventually_le_rpow c (sub_pos.2 hη), Filter.eventually_ge_atTop 1]
    with N hc hN1
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hpow : (0 : ℝ) ≤ (N : ℝ) ^ η := Real.rpow_nonneg (by linarith) η
  calc c * (N : ℝ) ^ η ≤ (N : ℝ) ^ (θ - η) * (N : ℝ) ^ η :=
        mul_le_mul_of_nonneg_right hc hpow
    _ = (N : ℝ) ^ θ := by
        rw [← Real.rpow_add (by linarith : (0 : ℝ) < (N : ℝ))]
        congr 1
        ring

/-- `(N^{δ/8})² = N^{δ/4}`: the drift slot's room. -/
theorem rpow_div_eight_sq {δ : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    ((N : ℝ) ^ (δ / 8)) ^ (2 : ℕ) = (N : ℝ) ^ (δ / 4) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  rw [← Real.rpow_natCast ((N : ℝ) ^ (δ / 8)) 2, ← Real.rpow_mul hN0]
  congr 1
  push_cast
  ring

/-- `(N^{δ/8})⁴ = N^{δ/2}`: the tail slot's room. -/
theorem rpow_div_eight_pow_four {δ : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    ((N : ℝ) ^ (δ / 8)) ^ (4 : ℕ) = (N : ℝ) ^ (δ / 2) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  rw [← Real.rpow_natCast ((N : ℝ) ^ (δ / 8)) 4, ← Real.rpow_mul hN0]
  congr 1
  push_cast
  ring

/-! ### 4. `hbudget` -/

/-- **⭐⭐ `hbudget` as a theorem.**

The hypothesis of `RBM.APrimeModel.qv_bound_model` with `c := slotTail x R`,
`x = N^{δ/8}`: the weighted quadratic-variation envelope `G N` — in the model layer
`(b−a)·Q^{bd}` of T269 — times the Burkholder factor `2p−1` sits below the square of the tail
slot, as soon as `G` obeys a `≺`-bound with exponent `η < δ/2`.

The `p`-dependence is carried entirely by the constant `2p−1` and is absorbed by
`eventually_const_mul_rpow_le`; the quantifier order is `p` first, `N` after. -/
theorem eventually_hbudget {δ η cq : ℝ} (hη0 : 0 ≤ η) (hη : η < δ / 2)
    {p : ℕ} (hp : 1 ≤ p) {Rn G : ℕ → ℝ} (hRn : ∀ N, 1 ≤ Rn N)
    (hG0 : ∀ᶠ N : ℕ in atTop, 0 ≤ G N)
    (hGbd : ∀ᶠ N : ℕ in atTop, 4 * (Rn N) ^ 4 * G N ≤ cq * (N : ℝ) ^ η) :
    ∀ᶠ N : ℕ in atTop,
      (2 * (p : ℝ) - 1) * G N ≤ (slotTail ((N : ℝ) ^ (δ / 8)) (Rn N)) ^ 2 := by
  have hδ0 : 0 ≤ δ := by linarith
  have hpp : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  filter_upwards [hG0, hGbd,
    eventually_const_mul_rpow_le (c := (2 * (p : ℝ) - 1) * cq) hη,
    Filter.eventually_ge_atTop 1] with N hG0N hGbdN habs hN1
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hN0 (by linarith)
  have hR1 : (1 : ℝ) ≤ Rn N := hRn N
  have hR4 : (0 : ℝ) < (Rn N) ^ 4 := by positivity
  -- the slot's room
  have hroom := sq_tailTerm_slot_ge (x := (N : ℝ) ^ (δ / 8)) (R := Rn N) hx1 hR1
  rw [rpow_div_eight_pow_four (δ := δ) hN1] at hroom
  refine le_trans ?_ hroom
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (Rn N) ^ 4)]
  calc (2 * (p : ℝ) - 1) * G N * (4 * (Rn N) ^ 4)
      = (2 * (p : ℝ) - 1) * (4 * (Rn N) ^ 4 * G N) := by ring
    _ ≤ (2 * (p : ℝ) - 1) * (cq * (N : ℝ) ^ η) :=
        mul_le_mul_of_nonneg_left hGbdN hpp
    _ = (2 * (p : ℝ) - 1) * cq * (N : ℝ) ^ η := by ring
    _ ≤ (N : ℝ) ^ (δ / 2) := habs

/-! ### 5. `hfit` -/

/-- The left-hand side of `hfit`, verbatim from `RBM.APrimeModel.drift_bound_first_cell`:
T268's `s = 0` budget (**no `log`**) against the constant drift envelope. -/
noncomputable def fitLhs (E Nr tc Qb Qm εs δ : ℝ) : ℝ :=
  2 * (tc * Qb + 4 * Nr ^ (εs - 2 * δ) * (etaT E tc / etaT E 0) ^ 2
      * √(2 * Qm * (mE E).im⁻¹))

theorem fitLhs_nonneg {E Nr tc Qb Qm εs δ : ℝ} (hNr : 0 ≤ Nr) (h : 0 ≤ tc * Qb) :
    0 ≤ fitLhs E Nr tc Qb Qm εs δ := by
  have h1 : (0 : ℝ) ≤ Nr ^ (εs - 2 * δ) := Real.rpow_nonneg hNr _
  have h2 : (0 : ℝ) ≤ √(2 * Qm * (mE E).im⁻¹) := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) ≤ 4 * Nr ^ (εs - 2 * δ) * (etaT E tc / etaT E 0) ^ 2
      * √(2 * Qm * (mE E).im⁻¹) :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) h2
  unfold fitLhs
  linarith

/-- At `ε_s = 2δ` the `N`-power of the first-cell budget is `N⁰ = 1`, so the left-hand side
does not depend on `N` at all.  (Used only by the satisfiability witness.) -/
theorem fitLhs_of_exp_zero {E Nr Nr' tc Qb Qm εs δ : ℝ} (h : εs - 2 * δ = 0) :
    fitLhs E Nr tc Qb Qm εs δ = fitLhs E Nr' tc Qb Qm εs δ := by
  unfold fitLhs
  rw [h, Real.rpow_zero, Real.rpow_zero]

/-- **⭐⭐ `hfit` as a theorem.**

The hypothesis of `RBM.APrimeModel.drift_bound_first_cell` with
`Dbd := slotDrift m (N^{δ/8}) (Rn N)`: T268's first-cell output sits below the drift slot as
soon as it obeys a `≺`-bound with a constant `c_p` (depending on `p` alone, through `c_MD`,
`‖χ′‖·p`, …) and exponent `η < δ/4`.

Again the order is `p` first, `N` after; the absorption is `eventually_const_mul_rpow_le`. -/
theorem eventually_hfit {E : ℝ} {δ η εs cp m : ℝ} (hη0 : 0 ≤ η) (hη : η < δ / 4)
    (hm : 0 < m) {Rn tc Qb Qm : ℕ → ℝ} (hRn : ∀ N, 1 ≤ Rn N)
    (hLbd : ∀ᶠ N : ℕ in atTop,
      fitLhs E (N : ℝ) (tc N) (Qb N) (Qm N) εs δ ≤ cp * (N : ℝ) ^ η) :
    ∀ᶠ N : ℕ in atTop,
      fitLhs E (N : ℝ) (tc N) (Qb N) (Qm N) εs δ ≤ slotDrift m ((N : ℝ) ^ (δ / 8)) (Rn N) := by
  have hδ0 : 0 ≤ δ := by linarith
  filter_upwards [hLbd, eventually_const_mul_rpow_le (c := 4 * m * cp) hη,
    Filter.eventually_ge_atTop 1] with N hLN habs hN1
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hN0 (by linarith)
  have hR1 : (1 : ℝ) ≤ Rn N := hRn N
  have hroom := driftTerm_slot_ge (m := m) (x := (N : ℝ) ^ (δ / 8)) (R := Rn N) hm hx1 hR1
  rw [rpow_div_eight_sq (δ := δ) hN1] at hroom
  refine le_trans ?_ hroom
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4), ← sub_nonneg]
  have hstep : 4 * m * fitLhs E (N : ℝ) (tc N) (Qb N) (Qm N) εs δ ≤ (N : ℝ) ^ (δ / 4) := by
    calc 4 * m * fitLhs E (N : ℝ) (tc N) (Qb N) (Qm N) εs δ
        ≤ 4 * m * (cp * (N : ℝ) ^ η) :=
          mul_le_mul_of_nonneg_left hLN (by positivity)
      _ = 4 * m * cp * (N : ℝ) ^ η := by ring
      _ ≤ (N : ℝ) ^ (δ / 4) := habs
  have hm4 : (0 : ℝ) < 4 * m := by linarith
  have : fitLhs E (N : ℝ) (tc N) (Qb N) (Qm N) εs δ * 4 ≤ (N : ℝ) ^ (δ / 4) * m⁻¹ := by
    rw [le_mul_inv_iff₀ hm]
    nlinarith [hstep]
  linarith

/-! ### 6. Both slots at once -/

/-- **⭐⭐⭐ The slot arithmetic, packaged.**

For every `p` (fixed first) and all large `N` (chosen after): T263's side-condition bundle
holds at the eight slot values, the first-cell `hfit` holds, and the quadratic-variation
`hbudget` holds.  A single envelope exponent `η < δ/16` serves both slots — this is exactly
the ticket's route: the `≺`-parameters of the envelopes go below `δ/16`, and the resulting
`c_p·N^{η}` disappears into the `x = N^{δ/8}` that `RBM.StepSideAPrime.stepRhs''` already
carries.  **No primed `WeightedMoment'` fallback is needed.**

The envelopes `tc`, `Qb`, `Qm`, `G` and the constants `cp`, `cq` are indexed by `p` as well
as `N`, since the drift and quadratic-variation envelopes genuinely depend on `p`. -/
theorem eventually_slot_arith {E : ℝ} {δ η εs m : ℝ} (hη0 : 0 ≤ η) (hη : η < δ / 16)
    (hm : 0 < m) {cp cq : ℕ → ℝ}
    {Rn : ℕ → ℝ} (hRn : ∀ N, 1 ≤ Rn N) {tc Qb Qm G : ℕ → ℕ → ℝ}
    (hG0 : ∀ p, ∀ᶠ N : ℕ in atTop, 0 ≤ G p N)
    (hGbd : ∀ p, ∀ᶠ N : ℕ in atTop, 4 * (Rn N) ^ 4 * G p N ≤ cq p * (N : ℝ) ^ η)
    (hLbd : ∀ p, ∀ᶠ N : ℕ in atTop,
      fitLhs E (N : ℝ) (tc p N) (Qb p N) (Qm p N) εs δ ≤ cp p * (N : ℝ) ^ η) :
    ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      SlotSide ((N : ℝ) ^ (δ / 8)) (Rn N) ∧
        fitLhs E (N : ℝ) (tc p N) (Qb p N) (Qm p N) εs δ
          ≤ slotDrift m ((N : ℝ) ^ (δ / 8)) (Rn N) ∧
        (2 * (p : ℝ) - 1) * G p N ≤ (slotTail ((N : ℝ) ^ (δ / 8)) (Rn N)) ^ 2 := by
  intro p hp
  have h4 : η < δ / 4 := by linarith
  have h2 : η < δ / 2 := by linarith
  filter_upwards [eventually_hfit (E := E) (δ := δ) (η := η) (εs := εs) (cp := cp p)
      (m := m) hη0 h4 hm hRn (hLbd p),
    eventually_hbudget (δ := δ) (η := η) (cq := cq p) hη0 h2 hp hRn (hG0 p) (hGbd p),
    Filter.eventually_ge_atTop 1] with N hfit hbudget hN1
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hN0 (by linarith)
  exact ⟨slotSide hx1 (hRn N), hfit, hbudget⟩

/-! ### 7. Satisfiability: a compiled witness on a non-collapsed window

The project's dominant defect is a compiled, axiom-clean theorem whose hypotheses are not
jointly satisfiable.  The witness below fixes every parameter explicitly, on a window with
`R = 2 > 1`, with a **strictly positive** quadratic-variation envelope and a **strictly
positive** first-cell left-hand side, so neither slot is met by collapsing something to `0`.

`δ = 1/2`, `η = 1/64 < δ/16 = 1/32`, `ε_s = 1 = 2δ`, `m = 1`, `E = 0`, `R ≡ 2`,
`t_c ≡ 1/4`, `Q^{bd} ≡ 1`, `Q_m ≡ 1`, `G ≡ 1`. -/

/-- The witness' first-cell left-hand side; it is a constant, because `ε_s = 2δ`. -/
noncomputable def satFit : ℝ := fitLhs 0 1 (1 / 4) 1 1 1 (1 / 2)

theorem satFit_pos : 0 < satFit := by
  have h1 : (0 : ℝ) ≤ (1 : ℝ) ^ ((1 : ℝ) - 2 * (1 / 2)) := Real.rpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤ √(2 * 1 * (mE 0).im⁻¹) := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) ≤ 4 * (1 : ℝ) ^ ((1 : ℝ) - 2 * (1 / 2))
      * (etaT 0 (1 / 4) / etaT 0 0) ^ 2 * √(2 * 1 * (mE 0).im⁻¹) :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) h2
  unfold satFit fitLhs
  norm_num
  positivity

/-- **⭐ The slot arithmetic is satisfiable**, at explicit parameters, on a window with
`R = 2 > 1` and with both envelopes strictly positive. -/
theorem sat_slot_arith :
    ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      SlotSide ((N : ℝ) ^ ((1 : ℝ) / 2 / 8)) 2 ∧
        fitLhs 0 (N : ℝ) (1 / 4) 1 1 1 (1 / 2)
          ≤ slotDrift 1 ((N : ℝ) ^ ((1 : ℝ) / 2 / 8)) 2 ∧
        (2 * (p : ℝ) - 1) * 1 ≤ (slotTail ((N : ℝ) ^ ((1 : ℝ) / 2 / 8)) 2) ^ 2 := by
  refine eventually_slot_arith (E := 0) (δ := 1 / 2) (η := 1 / 64) (εs := 1) (m := 1)
    (cp := fun _ => satFit) (cq := fun _ => 64) (Rn := fun _ => 2)
    (tc := fun _ _ => 1 / 4) (Qb := fun _ _ => 1) (Qm := fun _ _ => 1) (G := fun _ _ => 1)
    (by norm_num) (by norm_num) (by norm_num) (fun _ => by norm_num)
    (fun _ => Eventually.of_forall fun _ => by norm_num) ?_ ?_
  · intro p
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
    have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have h : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 64) := Real.one_le_rpow hN0 (by norm_num)
    nlinarith
  · intro p
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
    have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have h : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 64) := Real.one_le_rpow hN0 (by norm_num)
    have heq : fitLhs 0 (N : ℝ) (1 / 4) 1 1 1 (1 / 2) = satFit :=
      fitLhs_of_exp_zero (by norm_num)
    rw [heq]
    nlinarith [satFit_pos]

/-- **The witness is non-degenerate**: the window ratio is `> 1`, the quadratic-variation
envelope is `> 0`, and the first-cell left-hand side is `> 0` — so neither slot of
`sat_slot_arith` is satisfied by a collapsed quantity. -/
theorem sat_slot_arith_nondegenerate :
    (1 : ℝ) < 2 ∧ (0 : ℝ) < 1 ∧ 0 < satFit ∧
      ∀ᶠ N : ℕ in atTop, 0 < slotTail ((N : ℝ) ^ ((1 : ℝ) / 2 / 8)) 2 := by
  refine ⟨by norm_num, by norm_num, satFit_pos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx1 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 / 8) := Real.one_le_rpow hN0 (by norm_num)
  have hx0 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 2 / 8) := by linarith
  unfold slotTail tailTerm slotKappa
  positivity

/-! ### 8. The wiring check: the two obligations land in T271's consumers verbatim

Neither theorem below has any content of its own — each is T271's lemma with `hfit` / `hbudget`
replaced by the shapes §4–§6 produce.  They compile, so the shapes match **literally**: the
`Dbd` of `RBM.APrimeModel.drift_bound_first_cell` is `slotDrift`, the `c` of
`RBM.APrimeModel.qv_bound_model` is `slotTail`, and `hc : 0 ≤ c` is discharged here rather
than asked for. -/

/-- **⭐ `hfit`, wired.**  `RBM.APrimeModel.drift_bound_first_cell` with the drift slot of this
file as its `Dbd` and `fitLhs` as its left-hand side. -/
theorem drift_bound_first_cell_slot {E : ℝ} (hE : |E| < 2) {tc κh Qm Nr εs δ m x R : ℝ}
    {Adr Bcr Qh : ℝ → ℝ} {Qb : ℝ}
    (ht0 : 0 ≤ tc) (ht : tc ≤ 1 / 2) (hN : 1 ≤ Nr) (hε : 0 ≤ εs) (hκ0 : 0 ≤ κh)
    (hκ : κh ≤ Nr ^ (εs - 4 * δ) * (etaT E 0)⁻¹) (hQm : 0 ≤ Qm)
    (hQle : ∀ u ∈ Set.Icc (0 : ℝ) tc, Qh u ≤ Qm)
    (hcint : IntervalIntegrable (crossInt κh Qh) volume 0 tc)
    (hABint : IntervalIntegrable (fun r => Adr r + Bcr r) volume 0 tc)
    (hAbd : ∀ u ∈ Set.Icc (0 : ℝ) tc, Adr u ≤ Qb)
    (hBbd : ∀ u ∈ Set.Icc (0 : ℝ) tc, Bcr u ≤ crossInt κh Qh u)
    (hfit : fitLhs E Nr tc Qb Qm εs δ ≤ slotDrift m x R) :
    2 * (∫ r in (0 : ℝ)..tc, (Adr r + Bcr r)) ≤ slotDrift m x R :=
  drift_bound_first_cell hE ht0 ht hN hε hκ0 hκ hQm hQle hcint hABint hAbd hBbd hfit

/-- **⭐ `hbudget`, wired.**  `RBM.APrimeModel.qv_bound_model` with the tail slot of this file
as its `c`; `hc : 0 ≤ c` is `slotTail_nonneg`, so the producer no longer has to argue it. -/
theorem qv_bound_model_slot {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : Band Ω} {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω)
    (hW1 : ∀ ω, W ω ≤ 1) {p : ℕ} (hp : 1 ≤ p) (X : Sample B) (E : ℝ) (N : ℕ) {mm : ℕ}
    (σ : Fin mm → Bool) (a : LoopArg (B.L N) mm) {Good : ℕ → Set Ω} {a' b' : ℝ}
    (hab : a' ≤ b') {Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn x R : ℝ} {Jst : ℝ → Ω → ℝ}
    (hx : 1 ≤ x) (hR : 1 ≤ R)
    (hWr : 1 ≤ Wr) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hLr : 0 ≤ Lr)
    (hnorm : 0 < (Tt * Rn ^ 4) ^ 2)
    (hJ0 : ∀ u ∈ Set.Icc a' b', ∀ ω ∈ Good N, 0 ≤ Jst u ω)
    (hJ : ∀ u ∈ Set.Icc a' b', ∀ ω ∈ Good N, Jst u ω ≤ cWt * Λ)
    (hQ : ∀ u ∈ Set.Icc a' b', ∀ ω ∈ Good N, qvRate X E N σ a u ω
      ≤ qvShape Wr ℓu ℓs ηu D (Jst u ω) Smax ρfar Lr Tval)
    (hQBd : 0 ≤ QBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn)
    (hgint : IntervalIntegrable (gModel P W p X E N σ a Good Tt Rn) volume a' b')
    (hbudget : (2 * (p : ℝ) - 1)
      * ((b' - a') * QBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn) ≤ (slotTail x R) ^ 2) :
    √((2 * (p : ℝ) - 1) * ∫ r in a'..b', gModel P W p X E N σ a Good Tt Rn r)
      ≤ slotTail x R :=
  qv_bound_model hW0 hW1 hp X E N σ a hab hWr hℓu hηu hLr hnorm hJ0 hJ hQ hQBd
    (slotTail_nonneg hx hR) hgint hbudget

/-! ### 9. The `≺` form: no exponent bookkeeping left to the caller

T268/T269 deliver their envelopes as `≺`-statements, and `RBM.detDom_iff` says that `f ≺ 1`
is exactly "`f N ≤ N^{τ}` eventually, for **every** `τ > 0`".  Feeding that in at `τ = δ/32`
discharges both `hGbd` and `hLbd` with room to spare, so the caller never has to choose an
exponent. -/

/-- `f ≺ 1` gives the budget hypothesis at every positive exponent. -/
theorem eventually_le_rpow_of_detDom {f : ℕ → ℝ} (h : f ≺ fun _ => 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, f N ≤ 1 * (N : ℝ) ^ η := by
  filter_upwards [detDom_iff.1 h η hη] with N hN
  rw [one_mul]
  simpa using hN

/-- **⭐⭐⭐ The slot arithmetic from `≺`-envelopes.**  Both obligations of T271 hold, for
every `p` and all large `N`, as soon as the normalized quadratic-variation envelope and the
first-cell drift output are `≺ 1` — the shape T268/T269 produce.  No exponent has to be
chosen by the caller: `δ/32` is taken here. -/
theorem eventually_slot_arith_of_detDom {E : ℝ} {δ εs m : ℝ} (hδ : 0 < δ) (hm : 0 < m)
    {Rn : ℕ → ℝ} (hRn : ∀ N, 1 ≤ Rn N) {tc Qb Qm G : ℕ → ℕ → ℝ}
    (hG0 : ∀ p, ∀ᶠ N : ℕ in atTop, 0 ≤ G p N)
    (hGdom : ∀ p, (fun N => 4 * (Rn N) ^ 4 * G p N) ≺ fun _ => 1)
    (hLdom : ∀ p,
      (fun N => fitLhs E (N : ℝ) (tc p N) (Qb p N) (Qm p N) εs δ) ≺ fun _ => 1) :
    ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      SlotSide ((N : ℝ) ^ (δ / 8)) (Rn N) ∧
        fitLhs E (N : ℝ) (tc p N) (Qb p N) (Qm p N) εs δ
          ≤ slotDrift m ((N : ℝ) ^ (δ / 8)) (Rn N) ∧
        (2 * (p : ℝ) - 1) * G p N ≤ (slotTail ((N : ℝ) ^ (δ / 8)) (Rn N)) ^ 2 :=
  eventually_slot_arith (η := δ / 32) (cp := fun _ => 1) (cq := fun _ => 1)
    (by linarith) (by linarith) hm hRn hG0
    (fun p => eventually_le_rpow_of_detDom (hGdom p) (by linarith))
    (fun p => eventually_le_rpow_of_detDom (hLdom p) (by linarith))

/-- **⭐ The `≺` interface is satisfiable too**, at the same explicit parameters as
`sat_slot_arith` — with a **strictly positive** envelope (`G ≡ 1`) and a strictly positive
first-cell output (`satFit_pos`), on the non-collapsed window `R = 2`. -/
theorem sat_slot_arith_detDom :
    ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      SlotSide ((N : ℝ) ^ ((1 : ℝ) / 2 / 8)) 2 ∧
        fitLhs 0 (N : ℝ) (1 / 4) 1 1 1 (1 / 2)
          ≤ slotDrift 1 ((N : ℝ) ^ ((1 : ℝ) / 2 / 8)) 2 ∧
        (2 * (p : ℝ) - 1) * 1 ≤ (slotTail ((N : ℝ) ^ ((1 : ℝ) / 2 / 8)) 2) ^ 2 := by
  refine eventually_slot_arith_of_detDom (E := 0) (δ := 1 / 2) (εs := 1) (m := 1)
    (Rn := fun _ => 2) (tc := fun _ _ => 1 / 4) (Qb := fun _ _ => 1) (Qm := fun _ _ => 1)
    (G := fun _ _ => 1) (by norm_num) (by norm_num) (fun _ => by norm_num)
    (fun _ => Eventually.of_forall fun _ => by norm_num) (fun _ => ?_) (fun _ => ?_)
  · exact DetDom.of_eventually_le_const_mul (fun _ => zero_le_one) 64
      (Eventually.of_forall fun _ => by norm_num)
  · refine DetDom.of_eventually_le_const_mul (fun _ => zero_le_one) satFit
      (Eventually.of_forall fun N => ?_)
    rw [mul_one]
    exact le_of_eq (fitLhs_of_exp_zero (by norm_num))

end APrimeSlotArith

end RBM
