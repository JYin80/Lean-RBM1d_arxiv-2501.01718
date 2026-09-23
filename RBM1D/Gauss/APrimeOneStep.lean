/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Bootstrap
import RBM1D.Gauss.StepSideAPrime
import RBM1D.Gauss.APrimeOneStepTerms
import RBM1D.Gauss.APrimeGronwall
import RBM1D.Gauss.APrimeDuhamel

/-!
# The one-step moment bound of route (A′): the assembly skeleton (T270)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.39)–(5.48), assembled along the repaired route (A′) of the V548 referee
report, §5.

## What this file is

`RBM.Step2Bootstrap.weightedMoment_of_stepBound` reduces the moment field
`RBM.Step2Bootstrap.WeightedMoment` to **one** statement at one net point: produce a
`StepSide` bundle and the weighted moment bound

`∫ W·|cutTrunc(N^{2δ}·lev) J|^{2p} ≤ (stepRhs / R⁴)^{2p}`.

This file chains that statement, end to end, to the two analytic bricks route (A′) actually
uses — the weighted generator identity `RBM.Gauss.hasDerivAt_integral_weighted` (S1) and the
weighted Minkowski closure `RBM.MomentDuhamel.weightedMinkowski_of_deriv_le` (G) — and to the
rescaled arithmetic `RBM.StepSideAPrime.phi_arith''` (S7).  The estimates that are still being
built elsewhere enter as **named hypotheses**, one per slot of `stepRhs''`, each with its
supplier recorded in the docstring.  Replacing a hypothesis by the theorem that proves it is
then a mechanical edit at one call site.

## The input table

Slot of `stepRhs''` → hypothesis here → supplier:

* `x·R²·Ξ` → `hinit` of `momNormW_le_stepRhs''_div` → **hypothesis**: (5.39), the initial
  datum, i.e. (2.69) at the first cell and the bootstrap level carried by the weight after
  that; deterministic envelope from T269 (`RBM1D/Gauss/APrimePrior.lean`).
* drift + QV → `hdrift` → **hypothesis**: (5.40)–(5.42); T268
  (`RBM1D/Gauss/APrimeTimeInt.lean`) for the (S6) time integrals, T269 for the envelopes
  `Q^{bd}` and `κ̂^{bd}`.
* `x·R²·κ` and `x(R²+1)+1` → `hqv` → **hypothesis**: (S5), the cross term, from T265
  (`RBM1D/Gauss/APrimeDuhamel.lean`); (S3), the early-time quadratic-variation rate, from
  T267 (`RBM1D/Gauss/EarlyQVRateEv.lean`); the bad event from §2 below.
* the (G) regularity block → forwarded verbatim → **theorem**, T264
  (`RBM.MomentDuhamel.weightedMinkowski_of_deriv_le`).
* the arithmetic → `RBM.StepSideAPrime.stepRhs''_div_le` → **theorem**, T263.
* `p = 0` → discharged internally → **theorem**, T260
  (`RBM.Gauss.integral_weight_pow_zero_le`).

## Contents

* §1 `momNormW_pow`, `integral_le_of_momNormW_le`, `integral_cutTrunc_le_of_momNormW_le` —
  the passage from the weighted moment **norm**, which is what (G) bounds, to the weighted
  moment **integral**, which is what `WeightedMoment` asks for.
* §2 `integral_le_good_add_bad` — the bad event is paid for by the polynomial envelope
  `|cutTrunc Θ ·| ≤ 2Θ` (`RBM.MomentDuhamelCut.abs_cutTrunc_le`), so no event complement ever
  has to be estimated inside the moment.
* §3 `initTerm`/`driftTerm`/`tailTerm`, `stepRhs''_eq_split`, `stepRhs''_div_of_slots` and
  `momNormW_le_stepRhs''_div` — the chain: (G) plus three named slot bounds gives the
  normalized one-step bound `momNormW ≤ stepRhs''/R⁴`.  `drift_bound_of_envelopes` and
  `qv_bound_of_envelope` resolve two of those slots into one hypothesis per supplying ticket.
* §4 `oneStep_integral_le` — §3 composed with §1.
* §5 `weightedMoment_bound_of_oneStep''`, `weightedMoment_of_stepBound''` — the `''`
  counterparts of `RBM.Step2Bootstrap.weightedMoment_bound_of_oneStep` and
  `RBM.Step2Bootstrap.weightedMoment_of_stepBound`, with the honest constant
  `(cStep' m + 1)^{2p}` of `phi_arith''`.
* §6 `weightedMoment_of_stepBoundPos''` — **the `p = 0` branch**, discharged by
  `RBM.Gauss.integral_weight_pow_zero_le`, so a producer only ever has to argue for `1 ≤ p`.
* §7 satisfiability: `sat_stepRhs''_div_of_slots` runs the skeleton on a **non-degenerate**
  instance — T264's sharp witness for (G), where the moment and the quadratic-variation slot
  are both nonzero and (G) is attained with equality, against T263's margin witness for the
  side conditions — and `sat_oneStep_chain` carries it through the arithmetic.
-/

namespace RBM

namespace APrimeOneStep

open MeasureTheory Filter Set Real
open MomentDuhamel MomentDuhamelCut CutHypTheta StepSideAPrime

/-! ### 1. From the weighted moment norm to the weighted moment integral

(G) bounds `RBM.MomentDuhamel.momNormW P W p Y = (E[W|Y|^{2p}])^{1/(2p)}`;
`RBM.Step2Bootstrap.WeightedMoment` asks for `E[W|Y|^{2p}]`.  The two are the same object up
to the `2p`-th power, but only for `1 ≤ p` — at `p = 0` the exponent `1/(2p)` is `1/0` and
`momNormW` silently degenerates, which is why §6 takes that branch separately. -/

section ToIntegral

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `momNormW^{2p} = E[W|Y|^{2p}]`, for `1 ≤ p`. -/
theorem momNormW_pow {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) {p : ℕ} (hp : 1 ≤ p) (Y : Ω → ℝ) :
    momNormW P W p Y ^ (2 * p) = ∫ ω, W ω * |Y ω| ^ (2 * p) ∂P := by
  have h0 : (0 : ℝ) ≤ ∫ ω, W ω * |Y ω| ^ (2 * p) ∂P :=
    integral_nonneg fun ω => mul_nonneg (hW0 ω) (pow_nonneg (abs_nonneg _) _)
  have hne : 2 * p ≠ 0 := by omega
  have hexp : (1 : ℝ) / (2 * (p : ℝ)) = (((2 * p : ℕ) : ℝ))⁻¹ := by
    push_cast
    rw [one_div]
  rw [momNormW, hexp]
  exact Real.rpow_inv_natCast_pow h0 hne

/-- The weighted moment integral from the weighted moment norm. -/
theorem integral_le_of_momNormW_le {W Y : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) {p : ℕ} (hp : 1 ≤ p)
    {c : ℝ} (h : momNormW P W p Y ≤ c) :
    ∫ ω, W ω * |Y ω| ^ (2 * p) ∂P ≤ c ^ (2 * p) := by
  rw [← momNormW_pow hW0 hp Y]
  exact pow_le_pow_left₀ (momNormW_nonneg P hW0 p Y) h _

/-- **The shape `WeightedMoment` asks for.**  `Y` is the (normalized) functional the Duhamel
runs on; `cutTrunc θ (Jf ·)` is the truncated functional the interface names, and it is
dominated by `Y` pointwise.  `hYint` is integrability of the majorant, which the producer has
from `RBM.Step2Bootstrap.integrable_weight_mul` whenever `Y` is itself a truncation.

⚠ `hdom` is quantified over **all** `ω` and no good event restricts it — which is admissible
here, and only here, because **both sides are random**: it compares the interface functional
with the Duhamel's own functional, not with a deterministic size.  It is satisfiable with
nothing to prove at `Y = cutTrunc θ ∘ Jf`, where it is an equality; that case is
`integral_cutTrunc_le_of_momNormW_le_self` below, which needs no integrability hypothesis
either.  A hypothesis of the form `|cutTrunc θ (J ω)| ≤ (deterministic constant)` for all `ω`
would be a different matter and must not be written. -/
theorem integral_cutTrunc_le_of_momNormW_le {W Y Jf : Ω → ℝ} {θ c : ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω) {p : ℕ} (hp : 1 ≤ p)
    (hYint : Integrable (fun ω => W ω * |Y ω| ^ (2 * p)) P)
    (hdom : ∀ ω, |cutTrunc θ (Jf ω)| ≤ |Y ω|)
    (h : momNormW P W p Y ≤ c) :
    ∫ ω, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P ≤ c ^ (2 * p) := by
  refine le_trans (integral_mono_of_nonneg ?_ hYint ?_) (integral_le_of_momNormW_le hW0 hp h)
  · exact Eventually.of_forall fun ω => mul_nonneg (hW0 ω) (by positivity)
  · exact Eventually.of_forall fun ω =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hdom ω) _) (hW0 ω)

/-- The principal instantiation of `integral_cutTrunc_le_of_momNormW_le`: the Duhamel is run
on the interface functional itself, so `hdom` is `le_rfl` and no integrability hypothesis is
needed.  This is a **compiled witness that the `hdom`/`hYint` pair is satisfiable**. -/
theorem integral_cutTrunc_le_of_momNormW_le_self {W Jf : Ω → ℝ} {θ c : ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω) {p : ℕ} (hp : 1 ≤ p)
    (h : momNormW P W p (fun ω => cutTrunc θ (Jf ω)) ≤ c) :
    ∫ ω, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P ≤ c ^ (2 * p) :=
  integral_le_of_momNormW_le hW0 hp h

end ToIntegral

/-! ### 2. The bad event, paid for by the polynomial envelope

On the complement of the `≺`-event of Step 1 nothing is known about the flow, but the
**interface** functional is already truncated at `θ`, so `RBM.MomentDuhamelCut.abs_cutTrunc_le`
gives `|cutTrunc θ J| ≤ 2θ` there with no input at all.  With `θ = N^{2δ}·lev` and
`P(Eᶜ) ≤ N^{-D'}` this costs `(2θ)^{2p}N^{-D'} ≤ 1`, which is the constant slot `+1` of
`RBM.StepSideAPrime.stepRhs''`.  No complement of any event is ever estimated inside the
Duhamel itself — that is the whole point of route (A′). -/

section BadEvent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- Split the weighted moment at a measurable event and bound the complement by the
deterministic truncation envelope. -/
theorem integral_le_good_add_bad {W Jf : Ω → ℝ} {θ : ℝ} (hθ : 0 < θ) {p : ℕ}
    (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1) (hWm : AEStronglyMeasurable W P)
    (hJ0 : ∀ ω, 0 ≤ Jf ω) (hJm : AEStronglyMeasurable Jf P)
    {E : Set Ω} (hE : MeasurableSet E) :
    ∫ ω, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P
      ≤ (∫ ω in E, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P)
        + (2 * θ) ^ (2 * p) * (P Eᶜ).toReal := by
  have hint : Integrable (fun ω => W ω * |cutTrunc θ (Jf ω)| ^ (2 * p)) P :=
    Step2Bootstrap.integrable_weight_mul hθ hW0 hW1 hWm hJ0 hJm (2 * p)
  have hsplit : ∫ ω, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P
      = (∫ ω in E, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P)
        + ∫ ω in Eᶜ, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P :=
    (integral_add_compl hE hint).symm
  have hcompl : ∫ ω in Eᶜ, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P
      ≤ (2 * θ) ^ (2 * p) * (P Eᶜ).toReal := by
    have hpt : ∀ ω ∈ Eᶜ, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ≤ (2 * θ) ^ (2 * p) := by
      intro ω _
      have hb : |cutTrunc θ (Jf ω)| ^ (2 * p) ≤ (2 * θ) ^ (2 * p) :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_cutTrunc_le hθ (hJ0 ω)) _
      calc W ω * |cutTrunc θ (Jf ω)| ^ (2 * p)
          ≤ 1 * |cutTrunc θ (Jf ω)| ^ (2 * p) :=
            mul_le_mul_of_nonneg_right (hW1 ω) (by positivity)
        _ = |cutTrunc θ (Jf ω)| ^ (2 * p) := one_mul _
        _ ≤ (2 * θ) ^ (2 * p) := hb
    refine le_trans (setIntegral_mono_on hint.integrableOn integrableOn_const hE.compl hpt) ?_
    rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
  rw [hsplit]
  exact add_le_add le_rfl hcompl

end BadEvent

/-! ### 3. The chain: (G) plus three slot bounds

`RBM.StepSideAPrime.stepRhs''` splits, by `ring`, into exactly the three groups the weighted
Minkowski closure produces:

* `initTerm` — the initial datum `‖Y_a‖_{W,2p}`, i.e. (5.39);
* `driftTerm` — the drift integral `2∫(A + B)`, i.e. the far field (5.40) and the near field
  (5.41) of the paper;
* `tailTerm` — the quadratic-variation term `√((2p−1)∫g)`, i.e. (5.42), **plus** the new
  cross-term slot `κ` of the fixed-`ω` generator identity and the constant slot that pays for
  the bad event and for the `max_a` union.
-/

section Chain

open StepSideAPrime

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The three slot groups add up to `RBM.StepSideAPrime.stepRhs''` **exactly**: the split is an
identity, not an estimate, so nothing is lost in the bookkeeping. -/
theorem stepRhs''_eq_split (m x R Ξ A ε q β γ κ Jv : ℝ) :
    stepRhs'' m x R Ξ A ε q β γ κ Jv
      = initTerm x R Ξ + driftTerm m x R Ξ A ε q β γ Jv + tailTerm x R κ := by
  unfold stepRhs'' initTerm driftTerm tailTerm
  ring

/-- **⭐⭐ The one-step chain: the three slot bounds close `stepRhs''`.**

`hG` is the conclusion of the weighted Minkowski closure (G),
`RBM.MomentDuhamel.weightedMinkowski_of_deriv_le` — **already a theorem** (T264).  There,
`Adr` is the weighted drift norm `‖U_{u,v}F_u/T‖_{W,2p}`, `Bcr` the cross term `‖D̃_u‖_{2p}`
of the weighted generator identity `RBM.Gauss.hasDerivAt_integral_weighted` (also already a
theorem, T264), and `g` the weighted quadratic-variation rate `‖Q_u‖_{W,p}`.

The three named inputs are the slot bounds:

* `hinit` — **(5.39)**, the initial datum at the left endpoint of the cell.  *Supplier*: the
  previous cell's conclusion, i.e. (2.69) at `k = 0` and the bootstrap hypothesis carried by
  the weight for `k ≥ 1`; the deterministic envelope is T269 (`RBM1D/Gauss/APrimePrior.lean`).
* `hdrift` — **(5.40)+(5.41)+(5.42)**, the time integral of the drift and the cross term.
  *Suppliers*: T268 (`RBM1D/Gauss/APrimeTimeInt.lean`) for the (S6) time Cauchy–Schwarz
  `∫u^{-1/2}√Q^{bd} ≤ (log(t/s))^{1/2}(∫Q^{bd})^{1/2}` and for `integral_nearInt_le`; T269 for
  the envelopes `Q^{bd}` and `κ̂^{bd}`.
* `hqv` — **(5.42)** plus the cross-term slot.  *Suppliers*: T265
  (`RBM1D/Gauss/APrimeDuhamel.lean`, `RBM.Gauss.sum_gvar_crossTerm_le`) for the (S5) pointwise
  cross-term bound, T267 (`RBM1D/Gauss/EarlyQVRateEv.lean`) for the (S3) probabilistic
  early-time quadratic-variation rate, and §2 above for the bad event.

**The left endpoint may be `0`** (Cowork's ruling D17): (G)'s derivative hypothesis lives on
`Set.Ioo a b` only, so nothing here forces `0 < a`. -/
theorem stepRhs''_div_of_slots {m x R Ξ A ε q β γ κ Jv : ℝ} {a b : ℝ} {p : ℕ}
    {W : Ω → ℝ} {Y : ℝ → Ω → ℝ} {Adr Bcr g : ℝ → ℝ}
    (hG : momNormW P W p (Y b)
      ≤ momNormW P W p (Y a) + 2 * (∫ r in a..b, (Adr r + Bcr r))
        + √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r))
    (hinit : momNormW P W p (Y a) ≤ initTerm x R Ξ / R ^ 4)
    (hdrift : 2 * (∫ r in a..b, (Adr r + Bcr r))
      ≤ driftTerm m x R Ξ A ε q β γ Jv / R ^ 4)
    (hqv : √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r) ≤ tailTerm x R κ / R ^ 4) :
    momNormW P W p (Y b) ≤ stepRhs'' m x R Ξ A ε q β γ κ Jv / R ^ 4 := by
  refine hG.trans ?_
  rw [stepRhs''_eq_split, add_div, add_div]
  exact add_le_add (add_le_add hinit hdrift) hqv

/-- **⭐⭐ The one-step chain, in normalized units `J*/R⁴`, with (G) wired in.**

`stepRhs''_div_of_slots` composed with `RBM.MomentDuhamel.weightedMinkowski_of_deriv_le`; see
that lemma's docstring for the input table. -/
theorem momNormW_le_stepRhs''_div {m x R Ξ A ε q β γ κ Jv : ℝ}
    {a b : ℝ} (hab : a ≤ b) {p : ℕ} (hp : 1 ≤ p) {W : Ω → ℝ} {Y : ℝ → Ω → ℝ}
    {φ' Adr Bcr g : ℝ → ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω)
    (hcont : ContinuousOn (fun u => ∫ ω, W ω * |Y u ω| ^ (2 * p) ∂P) (Icc a b))
    (hderiv : ∀ u ∈ Ioo a b,
      HasDerivAt (fun r => ∫ ω, W ω * |Y r ω| ^ (2 * p) ∂P) (φ' u) u)
    (hφ'int : IntervalIntegrable φ' volume a b)
    (hA0 : ∀ u ∈ Icc a b, 0 ≤ Adr u) (hB0 : ∀ u ∈ Icc a b, 0 ≤ Bcr u)
    (hg0 : ∀ u ∈ Icc a b, 0 ≤ g u)
    (hABint : IntervalIntegrable (fun r => Adr r + Bcr r) volume a b)
    (hgint : IntervalIntegrable g volume a b)
    (hintψf : ∀ u ∈ Icc a b,
      IntervalIntegrable (fun r => momNormW P W p (Y r) * (Adr r + Bcr r)) volume a u)
    (hbound : ∀ u ∈ Ioo a b, φ' u
      ≤ 2 * (p : ℝ) * (∫ ω, W ω * |Y u ω| ^ (2 * p) ∂P)
            ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) * (Adr u + Bcr u)
        + (p : ℝ) * (2 * (p : ℝ) - 1)
            * (∫ ω, W ω * |Y u ω| ^ (2 * p) ∂P) ^ (((p : ℝ) - 1) / (p : ℝ)) * g u)
    (hinit : momNormW P W p (Y a) ≤ initTerm x R Ξ / R ^ 4)
    (hdrift : 2 * (∫ r in a..b, (Adr r + Bcr r))
      ≤ driftTerm m x R Ξ A ε q β γ Jv / R ^ 4)
    (hqv : √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r) ≤ tailTerm x R κ / R ^ 4) :
    momNormW P W p (Y b) ≤ stepRhs'' m x R Ξ A ε q β γ κ Jv / R ^ 4 :=
  stepRhs''_div_of_slots (weightedMinkowski_of_deriv_le hab hp hW0 hcont hderiv hφ'int
    hA0 hB0 hg0 hABint hgint hintψf hbound) hinit hdrift hqv

/-! #### The two composite slots, resolved into their individual suppliers

`hdrift` and `hqv` above are each the *sum* of several estimates that are being built in
different tickets.  The two lemmas below split them, so that landing one ticket replaces one
named hypothesis and nothing else has to move. -/

/-- **`hdrift` from its three suppliers.**

* `hAbd` — the weighted drift norm `‖U_{u,v}F_u/T‖_{W,2p}` is below its deterministic
  envelope.  *Supplier*: T269, `RBM1D/Gauss/APrimePrior.lean` (the `Q^{bd}` envelope of
  (5.40)–(5.41) with the weight-support level `J* ≤ cWt·Λ` substituted).
* `hBbd` — the cross term `‖D̃_u‖_{2p}` of the weighted generator identity is below its
  envelope.  *Suppliers*: T265, `RBM1D/Gauss/APrimeDuhamel.lean`
  (`RBM.Gauss.sum_gvar_crossTerm_le`, the (S5) pointwise bound) together with T267,
  `RBM1D/Gauss/EarlyQVRateEv.lean` (the (S3) early-time rate `κ̂^{bd}`).
* `htime` — the time integral of the two envelopes.  *Supplier*: T268,
  `RBM1D/Gauss/APrimeTimeInt.lean` ((S6): `∫u^{-1/2}√Q^{bd} ≤ (log(t/s))^{1/2}(∫Q^{bd})^{1/2}`
  and `integral_nearInt_le`). -/
theorem drift_bound_of_envelopes {a b : ℝ} (hab : a ≤ b) {Adr Bcr Qbd Cbd : ℝ → ℝ} {D : ℝ}
    (hABint : IntervalIntegrable (fun r => Adr r + Bcr r) volume a b)
    (hEint : IntervalIntegrable (fun r => Qbd r + Cbd r) volume a b)
    (hAbd : ∀ u ∈ Icc a b, Adr u ≤ Qbd u) (hBbd : ∀ u ∈ Icc a b, Bcr u ≤ Cbd u)
    (htime : 2 * (∫ r in a..b, (Qbd r + Cbd r)) ≤ D) :
    2 * (∫ r in a..b, (Adr r + Bcr r)) ≤ D := by
  refine le_trans ?_ htime
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact intervalIntegral.integral_mono_on hab hABint hEint
    fun u hu => add_le_add (hAbd u hu) (hBbd u hu)

/-- **`hqv` from its two suppliers.**

* `hgbd` — the weighted quadratic-variation rate `‖Q_u‖_{W,p}` is below its envelope.
  *Suppliers*: T267, `RBM1D/Gauss/EarlyQVRateEv.lean` ((S3), the probabilistic early-time
  rate) and T269, `RBM1D/Gauss/APrimePrior.lean` (the `Q^{bd}` envelope).
* `htime` — the time integral of the envelope, squared against the slot.  *Supplier*: T268,
  `RBM1D/Gauss/APrimeTimeInt.lean` ((S6)). -/
theorem qv_bound_of_envelope {a b : ℝ} (hab : a ≤ b) {g gbd : ℝ → ℝ} {p : ℕ} {c : ℝ}
    (hp : 1 ≤ p) (hc : 0 ≤ c)
    (hgint : IntervalIntegrable g volume a b)
    (hgbdint : IntervalIntegrable gbd volume a b)
    (hgbd : ∀ u ∈ Icc a b, g u ≤ gbd u)
    (htime : (2 * (p : ℝ) - 1) * (∫ r in a..b, gbd r) ≤ c ^ 2) :
    √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r) ≤ c := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hmono : (∫ r in a..b, g r) ≤ ∫ r in a..b, gbd r :=
    intervalIntegral.integral_mono_on hab hgint hgbdint hgbd
  have hstep : (2 * (p : ℝ) - 1) * (∫ r in a..b, g r) ≤ c ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hmono (by linarith)) htime
  have := Real.sqrt_le_sqrt hstep
  rwa [Real.sqrt_sq hc] at this

end Chain

/-! ### 4. The one-step moment bound `WeightedMoment` consumes -/

section OneStep

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The one-step moment bound, in the form `RBM.Step2Bootstrap.weightedMoment_of_stepBound`
consumes it** (with `''` for the rescaled arithmetic of T263).

`hdom` says the interface functional `cutTrunc θ (Jf ·)` is dominated by the normalized
Duhamel functional `Y b`; `hYint` is integrability of the majorant. -/
theorem oneStep_integral_le {m x R Ξ A ε q β γ κ Jv : ℝ}
    {p : ℕ} (hp : 1 ≤ p) {W Jf : Ω → ℝ} {Y : Ω → ℝ} {θ : ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω)
    (hYint : Integrable (fun ω => W ω * |Y ω| ^ (2 * p)) P)
    (hdom : ∀ ω, |cutTrunc θ (Jf ω)| ≤ |Y ω|)
    (hmom : momNormW P W p Y ≤ stepRhs'' m x R Ξ A ε q β γ κ Jv / R ^ 4) :
    ∫ ω, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P
      ≤ (stepRhs'' m x R Ξ A ε q β γ κ Jv / R ^ 4) ^ (2 * p) :=
  integral_cutTrunc_le_of_momNormW_le hW0 hp hYint hdom hmom

/-- The same, with the arithmetic of `RBM.StepSideAPrime.phi_arith''` read off: the one-step
output is `((cStep' m + 1)·x²)^{2p}`, which is exactly the per-`p` clause
`RBM.Step2Bootstrap.weightedMoment_bound_of_sq` consumes with `x = N^{δ/8}`. -/
theorem oneStep_integral_le_sq {m x R Ξ A ε q β γ κ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (hside : StepSide'' x R Ξ A ε q β γ κ Jv)
    {p : ℕ} (hp : 1 ≤ p) {W Jf : Ω → ℝ} {Y : Ω → ℝ} {θ : ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω)
    (hYint : Integrable (fun ω => W ω * |Y ω| ^ (2 * p)) P)
    (hdom : ∀ ω, |cutTrunc θ (Jf ω)| ≤ |Y ω|)
    (hmom : momNormW P W p Y ≤ stepRhs'' m x R Ξ A ε q β γ κ Jv / R ^ 4) :
    ∫ ω, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P
      ≤ ((Step2MomentStep.cStep' m + 1) * x ^ 2) ^ (2 * p) := by
  have hR4 : (0 : ℝ) < R ^ 4 := by
    have : (0 : ℝ) < R := by linarith [hside.R_ge]
    positivity
  have h0 : (0 : ℝ) ≤ stepRhs'' m x R Ξ A ε q β γ κ Jv / R ^ 4 :=
    div_nonneg (le_trans zero_le_one (one_le_stepRhs'' hx hm hside)) hR4.le
  exact (oneStep_integral_le hp hW0 hYint hdom hmom).trans
    (pow_le_pow_left₀ h0 (stepRhs''_div_le hx hm hside) _)

end OneStep

/-! ### 5. `WeightedMoment` from the rescaled arithmetic

The `''` counterparts of `RBM.Step2Bootstrap.weightedMoment_bound_of_oneStep` and
`RBM.Step2Bootstrap.weightedMoment_of_stepBound`.  The constant is
`(RBM.Step2MomentStep.cStep' m + 1)^{2p}`, which is what `RBM.StepSideAPrime.phi_arith''`
actually outputs; nothing else changes. -/

section Bridge

open MomentDuhamelCut CutHypTheta MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ}
  {s t mesh : ℕ → ℝ} {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ} {W : ℝ → ℕ → ℕ → Ω → ℝ}

/-- `RBM.Step2Bootstrap.weightedMoment_bound_of_oneStep` for `RBM.StepSideAPrime.StepSide''`. -/
theorem weightedMoment_bound_of_oneStep'' {δ m : ℝ} (hδ0 : 0 ≤ δ) (hm : 0 < m)
    (hΘ : ∀ N, Θ N = 1) (p : ℕ)
    (h : ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N, ∃ R Ξ A ε q β γ κ Jv : ℝ,
      StepSide'' ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv ∧
        ∫ ω, W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
            (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
          ≤ (stepRhs'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv / R ^ 4) ^ (2 * p)) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
      ∫ ω, W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
          (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
        ≤ C * ((N : ℝ) ^ (δ / 2 * p) * Θ N ^ (2 * p)) := by
  have hc₀ : (0 : ℝ) < Step2MomentStep.cStep' m + 1 := by
    linarith [Step2MomentStep.cStep'_pos hm]
  refine Step2Bootstrap.weightedMoment_bound_of_sq hc₀ hΘ p ?_
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1 k hk
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hNR (by linarith)
  obtain ⟨R, Ξ, A, ε, q, β, γ, κ, Jv, hside, hmom⟩ := hN k hk
  have hR4 : (0 : ℝ) < R ^ 4 := by
    have : (0 : ℝ) < R := by linarith [hside.R_ge]
    positivity
  have h0 : (0 : ℝ) ≤ stepRhs'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv / R ^ 4 :=
    div_nonneg (le_trans zero_le_one (one_le_stepRhs'' hx hm hside)) hR4.le
  exact hmom.trans (pow_le_pow_left₀ h0 (stepRhs''_div_le hx hm hside) _)

/-- `RBM.Step2Bootstrap.weightedMoment_of_stepBound` for `RBM.StepSideAPrime.StepSide''`. -/
theorem weightedMoment_of_stepBound'' {δ₀ m : ℝ} (hm : 0 < m) (hΘ : ∀ N, Θ N = 1)
    (H : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t mesh N, ∃ R Ξ A ε q β γ κ Jv : ℝ,
        StepSide'' ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv ∧
          ∫ ω, W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
              (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
            ≤ (stepRhs'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv / R ^ 4) ^ (2 * p)) :
    Step2Bootstrap.WeightedMoment P J s t mesh lev Θ δ₀ W :=
  fun δ hδ0 hδ p => weightedMoment_bound_of_oneStep'' hδ0.le hm hΘ p (H δ hδ0 hδ p)

end Bridge

/-! ### 6. ⚠ The `p = 0` branch

`momNormW` is `(E[W|Y|^{2p}])^{1/(2p)}`, so at `p = 0` its exponent is `1/0` and the
statement degenerates; (G) excludes `p = 0` by `1 ≤ p`, and the pointwise domination that
route (A′) uses becomes `1 ≤ 1` and carries no information (T230's trap).

The branch is not a gap: at `p = 0` the integrand **is** the weight, and `0 ≤ W ≤ 1` on a
probability space already gives `≤ 1 = (anything)^0`.  That is
`RBM.Gauss.integral_weight_pow_zero_le` (T260), and it is discharged here once and for all, so
a producer of the moment field only ever has to argue for `1 ≤ p`. -/

section PZero

open MomentDuhamelCut CutHypTheta MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {J : ℕ → ℝ → Ω → ℝ} {s t mesh : ℕ → ℝ} {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}
  {W : ℝ → ℕ → ℕ → Ω → ℝ}

/-- The `p = 0` clause of the one-step hypothesis, as a theorem. -/
theorem oneStep_pzero {m δ : ℝ} (hδ0 : 0 < δ) (N k : ℕ) (hN1 : 1 ≤ N)
    (hW0 : ∀ ω, 0 ≤ W δ N k ω) (hW1 : ∀ ω, W δ N k ω ≤ 1)
    (hWm : AEStronglyMeasurable (fun ω => W δ N k ω) P) :
    ∃ R Ξ A ε q β γ κ Jv : ℝ,
      StepSide'' ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv ∧
        ∫ ω, W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
            (J N (cutNetPt s mesh N k) ω)| ^ (2 * 0) ∂P
          ≤ (stepRhs'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv / R ^ 4) ^ (2 * 0) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hNR (by linarith)
  refine ⟨1, _, _, _, _, _, _, _, _, sat_StepSide''_half hx le_rfl, ?_⟩
  have hzero := Gauss.integral_weight_pow_zero_le (P := P) (W := W δ N k)
    (J := fun ω => J N (cutNetPt s mesh N k) ω)
    (θ := (N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k)) hW0 hW1 hWm
  refine hzero.trans ?_
  simp

/-- **`WeightedMoment` with the `p = 0` branch discharged**: the producer supplies the one-step
bound only for `1 ≤ p`. -/
theorem weightedMoment_of_stepBoundPos'' {δ₀ m : ℝ} (hm : 0 < m) (hΘ : ∀ N, Θ N = 1)
    (hW0 : ∀ δ N k ω, 0 ≤ W δ N k ω) (hW1 : ∀ δ N k ω, W δ N k ω ≤ 1)
    (hWm : ∀ (δ : ℝ) (N k : ℕ), AEStronglyMeasurable (fun ω => W δ N k ω) P)
    (H : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t mesh N, ∃ R Ξ A ε q β γ κ Jv : ℝ,
        StepSide'' ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv ∧
          ∫ ω, W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
              (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
            ≤ (stepRhs'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv / R ^ 4) ^ (2 * p)) :
    Step2Bootstrap.WeightedMoment P J s t mesh lev Θ δ₀ W := by
  refine weightedMoment_of_stepBound'' hm hΘ ?_
  intro δ hδ0 hδ p
  match p with
  | 0 =>
    filter_upwards [eventually_ge_atTop 1] with N hN1 k _
    exact oneStep_pzero (lev := lev) (J := J) (s := s) (mesh := mesh) hδ0 N k hN1
      (hW0 δ N k) (hW1 δ N k) (hWm δ N k)
  | (n + 1) => exact H δ hδ0 hδ (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

end PZero

/-! ### 7. Satisfiability: the skeleton is not self-contradictory

The danger a skeleton runs is that one of its named inputs is, read literally, unsatisfiable —
then every theorem downstream is vacuously true and the compiler says nothing.  The witness
below is **non-degenerate**: it is T264's sharp witness for (G) (`p = 1`, `W ≡ 1`,
`Y_u ≡ √u`, `g ≡ 1` on `[0,1]`), in which the moment `E[|Y_1|²] = 1`, its derivative and the
quadratic-variation term are all nonzero and (G) is attained with equality, run against
T263's margin witness `RBM.StepSideAPrime.sat_StepSide''_half` for the side conditions.
So `momNormW_le_stepRhs''_div` fires on an instance where nothing has collapsed to `0`. -/

section Sat

open StepSideAPrime

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The drift slot of T263's margin witness is nonnegative, which is all the degenerate drift
of the (G) witness below needs. -/
theorem sat_driftTerm_nonneg :
    0 ≤ driftTerm 1 1 1 ((1 : ℝ) / 2) (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))
      (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))⁻¹ ((1 : ℝ) ^ 2 / 2)
      (2 * (cWt * 1 ^ 16 * 1 ^ 2))⁻¹ (2 * (cWt * √cWt * 1 ^ 24 * 1 ^ 4))⁻¹
      (cWt * 1 ^ 16 * 1 ^ 4 / 2) / (1 : ℝ) ^ 4 := by
  have hc0 : (0 : ℝ) < cWt := cWt_pos
  have hsc : (0 : ℝ) < √cWt := Real.sqrt_pos.2 hc0
  have he : (0 : ℝ) < exp 1 := exp_pos 1
  unfold driftTerm
  have hJ : (0 : ℝ) ≤ cWt * 1 ^ 16 * 1 ^ 4 / 2 := by positivity
  have hsJ : (0 : ℝ) ≤ √(cWt * 1 ^ 16 * 1 ^ 4 / 2) := Real.sqrt_nonneg _
  positivity

/-- **⭐ The satisfiability witness for the whole skeleton.**

`stepRhs''_div_of_slots` is instantiated at

* T264's **non-degenerate** witness for (G), `RBM.MomentDuhamel.sat_weightedMinkowski_sharp`:
  `p = 1`, `W ≡ 1`, `Y_u ≡ √u` on `[0, 1]`, drift `≡ 0`, quadratic-variation rate `≡ 1`.  There
  `E[W|Y_1|²] = 1` and `√((2p−1)∫g) = 1`: **the moment and the quadratic-variation slot are
  both nonzero**, and (G) is attained with equality.
* T263's **margin** witness for the side conditions, `RBM.StepSideAPrime.sat_StepSide''_half`
  at `x = R = 1`, which meets all eight constraints with a factor `2` to spare.

So the three named slot hypotheses `hinit`, `hdrift`, `hqv` hold **simultaneously** on an
instance where nothing has collapsed to `0` — the skeleton is not self-contradictory, and it
is not closing on a vacuous bundle.  Note the left endpoint of the window is **exactly `0`**
(D17). -/
theorem sat_stepRhs''_div_of_slots :
    momNormW P (fun _ => (1 : ℝ)) 1 (fun _ => √(1 : ℝ))
      ≤ stepRhs'' 1 1 1 ((1 : ℝ) / 2) (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))
          (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))⁻¹ ((1 : ℝ) ^ 2 / 2)
          (2 * (cWt * 1 ^ 16 * 1 ^ 2))⁻¹ (2 * (cWt * √cWt * 1 ^ 24 * 1 ^ 4))⁻¹ ((1 : ℝ) / 2)
          (cWt * 1 ^ 16 * 1 ^ 4 / 2) / (1 : ℝ) ^ 4 := by
  refine stepRhs''_div_of_slots (a := 0) (b := 1) (p := 1) (Y := fun u _ => √u)
    (Adr := fun _ => 0) (Bcr := fun _ => 0) (g := fun _ => 1)
    (sat_weightedMinkowski_sharp P) ?_ ?_ ?_
  · simp [momNormW, initTerm]
  · simpa using sat_driftTerm_nonneg
  · norm_num [tailTerm]

/-- The witness carried all the way through the rescaled arithmetic of T263: the one-step
output of the skeleton is below `(cStep' 1 + 1)·x²` at `x = 1`, i.e. the constant
`RBM.StepSideAPrime.phi_arith''` advertises.  The left-hand side is `1`, not `0`. -/
theorem sat_oneStep_chain :
    momNormW P (fun _ => (1 : ℝ)) 1 (fun _ => √(1 : ℝ))
      ≤ (Step2MomentStep.cStep' 1 + 1) * (1 : ℝ) ^ 2 :=
  (sat_stepRhs''_div_of_slots (P := P)).trans
    (sat_stepRhs''_div_half one_pos le_rfl le_rfl)

/-- The side conditions of the same witness, for the record: `oneStep_integral_le_sq` is
applicable to it. -/
theorem sat_stepSide'' :
    StepSide'' 1 1 ((1 : ℝ) / 2) (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))
      (2 * (cWt ^ 2 * 1 ^ 33 * 1 ^ 10))⁻¹ ((1 : ℝ) ^ 2 / 2)
      (2 * (cWt * 1 ^ 16 * 1 ^ 2))⁻¹ (2 * (cWt * √cWt * 1 ^ 24 * 1 ^ 4))⁻¹ ((1 : ℝ) / 2)
      (cWt * 1 ^ 16 * 1 ^ 4 / 2) :=
  sat_StepSide''_half le_rfl le_rfl

end Sat

end APrimeOneStep

end RBM

/-!
## Deviations from the paper

**T270a** (§5.3, (5.39)–(5.48)).

1. *A constant slot pays for the bad event.*  The paper's (5.39)–(5.44) have no additive
   constant: the stopping time of (5.43) makes the complement of the good event invisible to
   the estimate.  Route (A′) replaces the stopping time by a weight, so the complement is a
   genuine set of positive measure and has to be paid for.  It is paid for **without any
   input**, by the deterministic envelope `|cutTrunc Θ ·| ≤ 2Θ`
   (`RBM.MomentDuhamelCut.abs_cutTrunc_le`, §2 here) against a polynomially small probability;
   the price is the constant slot `x(R²+1)+1` of `RBM.StepSideAPrime.stepRhs''`, which
   `tailTerm` carries.  This is the accounting consequence of the deviation already recorded
   as `T230a`, not a new change to any statement of the paper.
2. *The interface functional is dominated, not identified.*  `RBM.Step2Bootstrap.WeightedMoment`
   names `cutTrunc θ (J_u ω)`, whereas the Duhamel runs on the normalized functional `Y`.  The
   skeleton therefore carries an explicit pointwise hypothesis `|cutTrunc θ (J ω)| ≤ |Y ω|`
   (`hdom` of `integral_cutTrunc_le_of_momNormW_le`) rather than an equality.  The paper has no
   counterpart because it never truncates; the truncation is the repository's device from
   `T230a`.

Nothing else here departs from the paper: `stepRhs''_eq_split` is an identity proved by `ring`,
and the constants are T263's (`T263a`) and T264's (`T264a`).
-/
