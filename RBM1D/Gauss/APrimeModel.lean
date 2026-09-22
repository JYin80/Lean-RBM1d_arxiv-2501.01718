/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeOneStep
import RBM1D.Gauss.APrimePrior
import RBM1D.Gauss.APrimeTimeInt
import RBM1D.Gauss.EarlyQVRateEv
import RBM1D.Flow.Step345Producer

/-!
# Route (A′) at the model layer: the slots of the one-step bound, filled (T271)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.39)–(5.48), along the repaired route (A′) of the V548 referee report, §5.
-/

namespace RBM

namespace APrimeModel

open MeasureTheory Filter Set Real
open MomentDuhamel MomentDuhamelCut CutHypTheta StepSideAPrime APrimeOneStep APrimePrior

/-! ### 1. Weighted envelopes: a pointwise bound **on an event** becomes a norm bound -/

section Envelope

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The weighted moment norm below a deterministic envelope, on an event.**

⚠ The hypothesis is *not* `∀ ω, |Y ω| ≤ c`: that shape is unsatisfiable for the functionals
of route (A′) (V548 §6).  It is `|Y ω| ≤ c` **for `ω ∈ G`** together with `Y ω = 0` off `G`,
which is exactly what the event-restricted functional `RBM.Step2Bootstrap.onEvent J Good` of
T249 satisfies: there `Y` is literally `0` off the good event. -/
theorem momNormW_le_of_le_on {W Y : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1)
    {p : ℕ} (hp : 1 ≤ p) {c : ℝ} (hc : 0 ≤ c) {G : Set Ω}
    (hin : ∀ ω ∈ G, |Y ω| ≤ c) (hout : ∀ ω ∉ G, Y ω = 0) :
    momNormW P W p Y ≤ c := by
  have hpt : ∀ ω, W ω * |Y ω| ^ (2 * p) ≤ c ^ (2 * p) := by
    intro ω
    by_cases h : ω ∈ G
    · calc W ω * |Y ω| ^ (2 * p) ≤ 1 * |Y ω| ^ (2 * p) :=
            mul_le_mul_of_nonneg_right (hW1 ω) (by positivity)
        _ = |Y ω| ^ (2 * p) := one_mul _
        _ ≤ c ^ (2 * p) := pow_le_pow_left₀ (abs_nonneg _) (hin ω h) _
    · rw [hout ω h, abs_zero, zero_pow (by omega : 2 * p ≠ 0), mul_zero]
      positivity
  have hint : (∫ ω, W ω * |Y ω| ^ (2 * p) ∂P) ≤ c ^ (2 * p) := by
    have := integral_mono_of_nonneg
      (Eventually.of_forall fun ω => mul_nonneg (hW0 ω) (by positivity))
      (integrable_const (μ := P) (c ^ (2 * p))) (Eventually.of_forall hpt)
    simpa using this
  have h0 : (0 : ℝ) ≤ ∫ ω, W ω * |Y ω| ^ (2 * p) ∂P :=
    integral_nonneg fun ω => mul_nonneg (hW0 ω) (by positivity)
  have hne : 2 * p ≠ 0 := by omega
  have hexp : (1 : ℝ) / (2 * (p : ℝ)) = (((2 * p : ℕ) : ℝ))⁻¹ := by push_cast; rw [one_div]
  rw [momNormW, hexp]
  calc (∫ ω, W ω * |Y ω| ^ (2 * p) ∂P) ^ (((2 * p : ℕ) : ℝ))⁻¹
      ≤ (c ^ (2 * p)) ^ (((2 * p : ℕ) : ℝ))⁻¹ := Real.rpow_le_rpow h0 hint (by positivity)
    _ = c := Real.pow_rpow_inv_natCast hc hne

/-- **The weighted `L^p` norm of a nonnegative rate** — the shape `g` of (G), whose dimension
is that of `Y²`, not of `Y`. -/
noncomputable def rateNormW (P : Measure Ω) (W : Ω → ℝ) (p : ℕ) (Q : Ω → ℝ) : ℝ :=
  (∫ ω, W ω * |Q ω| ^ p ∂P) ^ ((1 : ℝ) / (p : ℝ))

omit [IsProbabilityMeasure P] in
theorem rateNormW_nonneg {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) (p : ℕ) (Q : Ω → ℝ) :
    0 ≤ rateNormW P W p Q :=
  Real.rpow_nonneg (integral_nonneg fun ω => mul_nonneg (hW0 ω) (by positivity)) _

/-- The same envelope statement for the rate norm. -/
theorem rateNormW_le_of_le_on {W Q : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1)
    {p : ℕ} (hp : 1 ≤ p) {c : ℝ} (hc : 0 ≤ c) {G : Set Ω}
    (hin : ∀ ω ∈ G, |Q ω| ≤ c) (hout : ∀ ω ∉ G, Q ω = 0) :
    rateNormW P W p Q ≤ c := by
  have hpt : ∀ ω, W ω * |Q ω| ^ p ≤ c ^ p := by
    intro ω
    by_cases h : ω ∈ G
    · calc W ω * |Q ω| ^ p ≤ 1 * |Q ω| ^ p :=
            mul_le_mul_of_nonneg_right (hW1 ω) (by positivity)
        _ = |Q ω| ^ p := one_mul _
        _ ≤ c ^ p := pow_le_pow_left₀ (abs_nonneg _) (hin ω h) _
    · rw [hout ω h, abs_zero, zero_pow (by omega : p ≠ 0), mul_zero]
      positivity
  have hint : (∫ ω, W ω * |Q ω| ^ p ∂P) ≤ c ^ p := by
    have := integral_mono_of_nonneg
      (Eventually.of_forall fun ω => mul_nonneg (hW0 ω) (by positivity))
      (integrable_const (μ := P) (c ^ p)) (Eventually.of_forall hpt)
    simpa using this
  have h0 : (0 : ℝ) ≤ ∫ ω, W ω * |Q ω| ^ p ∂P :=
    integral_nonneg fun ω => mul_nonneg (hW0 ω) (by positivity)
  have hne : p ≠ 0 := by omega
  have hexp : (1 : ℝ) / (p : ℝ) = ((p : ℝ))⁻¹ := one_div _
  rw [rateNormW, hexp]
  calc (∫ ω, W ω * |Q ω| ^ p ∂P) ^ ((p : ℝ))⁻¹
      ≤ (c ^ p) ^ ((p : ℝ))⁻¹ := Real.rpow_le_rpow h0 hint (by positivity)
    _ = c := Real.pow_rpow_inv_natCast hc hne

end Envelope


/-! ### 2. The model-layer objects

`RBM.MomentDuhamel.lkFun` is `(L−K)_{u,σ,a}` as a function of `(u, M)`; along the flow it is
`RBM.SumZeroDyn.lkT` by `rfl`.  The rate of (5.42) is its `RBM.Gauss.quadVar` at the running
matrix, and the functional of (5.29) is its normalization by the tail `T_{u,D}`.

Every object below carries the good event **in its definition** (`RBM.Step2Bootstrap.onEvent`
is the same device at the level of the state functional, T249): off `Good N` it is `0`.  That
is what makes the deterministic envelopes of §3 satisfiable — a size bound quantified over
*all* `ω` would be false, since `‖X(ω)‖` is unbounded (V548 §6, `RBM.t249_witness_norm_gt`).
-/

section Model

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The quadratic-variation rate of (5.42) at one sample point**, for the loop functional
`(L−K)_{u,σ,a}`.  This is the object T262/T269 estimate. -/
noncomputable def qvRate (X : Sample B) (E : ℝ) (N : ℕ) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) (u : ℝ) (ω : Ω) : ℝ :=
  Gauss.quadVar B.toDims N (fun M => MomentDuhamel.lkFun B E N u M σ a) (X.H N u ω)

theorem qvRate_nonneg (X : Sample B) (E : ℝ) (N : ℕ) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) (u : ℝ) (ω : Ω) : 0 ≤ qvRate X E N σ a u ω :=
  Gauss.quadVar_nonneg _ _

/-- **The rate, restricted to the good event.**  Off `Good N` it is `0`, so the envelopes of
§3 are statements about a quantity that is *identically zero* where nothing is known. -/
noncomputable def qvRateOn (X : Sample B) (E : ℝ) (N : ℕ) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) (Good : ℕ → Set Ω) (u : ℝ) (ω : Ω) : ℝ :=
  Set.indicator (Good N) (qvRate X E N σ a u) ω

theorem qvRateOn_of_mem {X : Sample B} {E : ℝ} {N : ℕ} {m : ℕ} {σ : Fin m → Bool}
    {a : LoopArg (B.L N) m} {Good : ℕ → Set Ω} {u : ℝ} {ω : Ω} (h : ω ∈ Good N) :
    qvRateOn X E N σ a Good u ω = qvRate X E N σ a u ω := Set.indicator_of_mem h _

theorem qvRateOn_of_notMem {X : Sample B} {E : ℝ} {N : ℕ} {m : ℕ} {σ : Fin m → Bool}
    {a : LoopArg (B.L N) m} {Good : ℕ → Set Ω} {u : ℝ} {ω : Ω} (h : ω ∉ Good N) :
    qvRateOn X E N σ a Good u ω = 0 := Set.indicator_of_notMem h _

theorem qvRateOn_nonneg (X : Sample B) (E : ℝ) (N : ℕ) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) (Good : ℕ → Set Ω) (u : ℝ) (ω : Ω) :
    0 ≤ qvRateOn X E N σ a Good u ω := by
  by_cases h : ω ∈ Good N
  · rw [qvRateOn_of_mem h]; exact qvRate_nonneg _ _ _ _ _ _ _
  · rw [qvRateOn_of_notMem h]

/-- **The endpoint-normalized rate of (5.42)**, `Q_u/(T_t R⁴)²`, on the good event.  This is
the `Q̂` of the referee's (S6): the division by `(T_t R⁴)²` is the hat-normalization that
T268's time integrals consume. -/
noncomputable def qvHat (X : Sample B) (E : ℝ) (N : ℕ) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) (Good : ℕ → Set Ω) (Tt Rn : ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  qvRateOn X E N σ a Good u ω / (Tt * Rn ^ 4) ^ 2

/-- **The weighted quadratic-variation rate `g` of (G)**, at the model functional. -/
noncomputable def gModel (P : Measure Ω) (W : Ω → ℝ) (p : ℕ) (X : Sample B) (E : ℝ) (N : ℕ)
    {m : ℕ} (σ : Fin m → Bool) (a : LoopArg (B.L N) m) (Good : ℕ → Set Ω) (Tt Rn : ℝ)
    (u : ℝ) : ℝ :=
  rateNormW P W p (qvHat X E N σ a Good Tt Rn u)

end Model

/-! ### 3. `hgbd` and the `κ` slot, from T269's closed-form envelopes

`RBM.APrimePrior.div_le_QBd_of_le_qvShape` and `RBM.APrimePrior.le_kappaBd_of_le_qvBd` turn a
(5.42)-shaped pointwise bound at the **running** level `J*` into the explicit, `J*`-free
envelopes `Q^{bd}` and `κ̂^{bd}`.  The substitution `J* ≤ cWt·Λ` is legitimate exactly on
`{W ≠ 0} ∩ Good`, which is what `RBM.APrimePrior.eventually_le_cWt_mul_priorLevel` proves;
here that is packaged as the hypothesis `hJ`, quantified over `ω ∈ Good N` only. -/

section Slots

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : Band Ω}

/-- **⭐ `hgbd` as a theorem.**  The weighted rate `g` is below the deterministic `Q^{bd}` of
T269, given the (5.42)-shaped pointwise bound at the running level and the a priori level on
the good event. -/
theorem gModel_le_QBd {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1)
    {p : ℕ} (hp : 1 ≤ p) (X : Sample B) (E : ℝ) (N : ℕ) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) {Good : ℕ → Set Ω} {u : ℝ}
    {Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn : ℝ} {Jst : Ω → ℝ}
    (hWr : 1 ≤ Wr) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hLr : 0 ≤ Lr)
    (hnorm : 0 < (Tt * Rn ^ 4) ^ 2)
    (hJ0 : ∀ ω ∈ Good N, 0 ≤ Jst ω) (hJ : ∀ ω ∈ Good N, Jst ω ≤ cWt * Λ)
    (hQ : ∀ ω ∈ Good N, qvRate X E N σ a u ω
      ≤ qvShape Wr ℓu ℓs ηu D (Jst ω) Smax ρfar Lr Tval)
    (hQBd : 0 ≤ QBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn) :
    gModel P W p X E N σ a Good Tt Rn u ≤ QBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn := by
  refine rateNormW_le_of_le_on hW0 hW1 hp hQBd (G := Good N) (fun ω hω => ?_) (fun ω hω => ?_)
  · rw [abs_of_nonneg (by
      have : 0 ≤ qvRateOn X E N σ a Good u ω := qvRateOn_nonneg _ _ _ _ _ _ _ _
      unfold qvHat; positivity)]
    unfold qvHat
    rw [qvRateOn_of_mem hω]
    exact div_le_QBd_of_le_qvShape hWr hℓu hηu hLr (hJ0 ω hω) (hJ ω hω) hnorm (hQ ω hω)
  · unfold qvHat
    rw [qvRateOn_of_notMem hω, zero_div]

/-- **⭐ The `κ̂^{bd}` envelope at the model layer**: the same pointwise input, read through
`RBM.APrimePrior.le_kappaBd_of_le_qvBd`, gives the hat-normalized cross-term rate that feeds
the `κ` slot of `RBM.StepSideAPrime.stepRhs''`. -/
theorem qvRate_le_kappaBd {X : Sample B} {E : ℝ} {N : ℕ} {m : ℕ} {σ : Fin m → Bool}
    {a : LoopArg (B.L N) m} {Good : ℕ → Set Ω} {u : ℝ}
    {Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval : ℝ} {Jst : Ω → ℝ}
    (hWr : 1 ≤ Wr) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hLr : 0 ≤ Lr)
    (hT : Tval ≠ 0) (hΛ : Λ ≠ 0)
    (hJ0 : ∀ ω ∈ Good N, 0 ≤ Jst ω) (hJ : ∀ ω ∈ Good N, Jst ω ≤ cWt * Λ)
    (hQ : ∀ ω ∈ Good N, qvRate X E N σ a u ω
      ≤ qvShape Wr ℓu ℓs ηu D (Jst ω) Smax ρfar Lr Tval) :
    ∀ ω ∈ Good N, qvRate X E N σ a u ω
      ≤ (Tval * Λ) ^ 2 * kappaBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval := by
  intro ω hω
  exact le_kappaBd_of_le_qvBd hT hΛ
    (le_qvBd_of_le_qvShape hWr hℓu hηu hLr (hJ0 ω hω) (hJ ω hω) (hQ ω hω))

end Slots


/-! ### 4. The two caller obligations of T265 (S5), and the first cell's time integral

T265 proved the (S5) cross-term bound **pointwise in the matrix variable** and left two
normalizations to the caller: the Duhamel rescaling `M ↦ √(u_j/u)·M` and the prefactor
`(2√u)⁻¹` of the fixed-`ω` generator identity.  Both are discharged here, in the direction
the referee's audit prescribes: `√u_j ≤ 1` is absorbed into `κ̂_j`, and the surviving
`u^{-1/2}` is exactly the integrand weight of T268's (S6).

⚠ **The first cell must use the `s = 0` branch of (S6)**, `integral_early_le_budget`, which
carries **no `log (t/s)`**: at `s = 0` that logarithm is `+∞`.  D17 says the cell `[0, u₁]` is
on the main route, so this is not an optional branch. -/

section Rescale

/-- **Caller obligation 1 of T265 (S5)**: the Duhamel rescaling factor is at most `u^{-1/2}`
once `u_j ≤ 1`, the surplus `√u_j ≤ 1` being absorbed into the rate `κ̂_j`. -/
theorem sqrt_div_le_sqrt_inv {u uj : ℝ} (hu : 0 < u) (huj : uj ≤ 1) :
    √(uj / u) ≤ √u⁻¹ := by
  rw [Real.sqrt_le_sqrt_iff (by positivity)]
  rw [div_le_iff₀ hu, inv_mul_cancel₀ hu.ne']
  exact huj

/-- **Caller obligation 2 of T265 (S5)**: the prefactor `(2√u)⁻¹` of the fixed-`ω` generator
identity is at most `u^{-1/2}`, so it costs nothing beyond the (S6) weight. -/
theorem inv_two_sqrt_le_sqrt_inv {u : ℝ} (hu : 0 < u) : (2 * √u)⁻¹ ≤ √u⁻¹ := by
  have hs : 0 < √u := Real.sqrt_pos.2 hu
  rw [Real.sqrt_inv]
  rw [mul_inv, inv_eq_one_div (2 : ℝ)]
  nlinarith [inv_pos.2 hs]

/-- **The (S6) integrand at the model layer**: the `u^{-1/2}` weight of the two obligations
above against the (S5) product of two same-time quadratic-variation rates. -/
noncomputable def crossInt (κh : ℝ) (Qh : ℝ → ℝ) (u : ℝ) : ℝ := √u⁻¹ * √(κh * Qh u)

theorem crossInt_nonneg (κh : ℝ) (Qh : ℝ → ℝ) (u : ℝ) : 0 ≤ crossInt κh Qh u :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **⭐ The first cell's `htime`, from T268's `s = 0` branch.**  No `log (t/s)` appears; the
gain is the `N^{ε-2δ}` of the (S6) budget. -/
theorem integral_crossInt_first_cell_le {E : ℝ} (hE : |E| < 2) {t κh Qm Nr ε δ : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hN : 1 ≤ Nr) (hε : 0 ≤ ε) (hκ0 : 0 ≤ κh)
    (hκ : κh ≤ Nr ^ (ε - 4 * δ) * (etaT E 0)⁻¹) (hQm : 0 ≤ Qm) {Qh : ℝ → ℝ}
    (hQle : ∀ u ∈ Icc (0 : ℝ) t, Qh u ≤ Qm)
    (hint : IntervalIntegrable (crossInt κh Qh) volume 0 t) :
    (∫ u in (0 : ℝ)..t, crossInt κh Qh u)
      ≤ 4 * Nr ^ (ε - 2 * δ) * (etaT E t / etaT E 0) ^ 2 * √(2 * Qm * (mE E).im⁻¹) :=
  APrimeTimeInt.integral_early_le_budget hE ht0 ht hN hε hκ0 hκ hQm hQle hint

end Rescale

/-! ### 5. The two composite slots, at the model layer

`RBM.APrimeOneStep.drift_bound_of_envelopes` and `RBM.APrimeOneStep.qv_bound_of_envelope` are
the skeleton's two splitters.  Here each is closed against a **constant** envelope — which is
what T269 produces, `Q^{bd}` and `κ̂^{bd}` being explicit functions of the model parameters
alone — so the time integral is elementary and the only real content is the budget
inequality, supplied by T268. -/

section Composite

/-- **⭐ `hqv` against a constant envelope.**  `RBM.APrimeOneStep.qv_bound_of_envelope` with
`gbd ≡ Q^{bd}`: the time integral is `(b−a)·Q^{bd}` and the budget is the explicit
inequality `(2p−1)(b−a)Q^{bd} ≤ c²`. -/
theorem qv_bound_of_const {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ} {p : ℕ} {c Qb : ℝ}
    (hp : 1 ≤ p) (hc : 0 ≤ c) (hgint : IntervalIntegrable g volume a b)
    (hgbd : ∀ u ∈ Icc a b, g u ≤ Qb)
    (hbudget : (2 * (p : ℝ) - 1) * ((b - a) * Qb) ≤ c ^ 2) :
    √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r) ≤ c := by
  refine qv_bound_of_envelope hab hp hc hgint (gbd := fun _ => Qb)
    (intervalIntegrable_const) hgbd ?_
  rwa [intervalIntegral.integral_const, smul_eq_mul]

/-- **⭐ `hdrift` against constant envelopes.**  `RBM.APrimeOneStep.drift_bound_of_envelopes`
with both envelopes constant. -/
theorem drift_bound_of_const {a b : ℝ} (hab : a ≤ b) {Adr Bcr : ℝ → ℝ} {Qb Cb D : ℝ}
    (hABint : IntervalIntegrable (fun r => Adr r + Bcr r) volume a b)
    (hAbd : ∀ u ∈ Icc a b, Adr u ≤ Qb) (hBbd : ∀ u ∈ Icc a b, Bcr u ≤ Cb)
    (htime : 2 * ((b - a) * (Qb + Cb)) ≤ D) :
    2 * (∫ r in a..b, (Adr r + Bcr r)) ≤ D := by
  refine drift_bound_of_envelopes hab hABint (Qbd := fun _ => Qb) (Cbd := fun _ => Cb)
    intervalIntegrable_const hAbd hBbd ?_
  rwa [intervalIntegral.integral_const, smul_eq_mul]

/-- **⭐ The `hqv` slot, model-layer, end to end**: §3's envelope for the weighted
quadratic-variation rate composed with the budget of `qv_bound_of_const`.  `hgint` is the
integrability of `u ↦ ‖Q_u‖_{W,p}` in time, which the Duhamel supplies. -/
theorem qv_bound_model {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : Band Ω} {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω)
    (hW1 : ∀ ω, W ω ≤ 1) {p : ℕ} (hp : 1 ≤ p) (X : Sample B) (E : ℝ) (N : ℕ) {m : ℕ}
    (σ : Fin m → Bool) (a : LoopArg (B.L N) m) {Good : ℕ → Set Ω} {a' b' : ℝ} (hab : a' ≤ b')
    {Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn c : ℝ} {Jst : ℝ → Ω → ℝ}
    (hWr : 1 ≤ Wr) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hLr : 0 ≤ Lr)
    (hnorm : 0 < (Tt * Rn ^ 4) ^ 2)
    (hJ0 : ∀ u ∈ Icc a' b', ∀ ω ∈ Good N, 0 ≤ Jst u ω)
    (hJ : ∀ u ∈ Icc a' b', ∀ ω ∈ Good N, Jst u ω ≤ cWt * Λ)
    (hQ : ∀ u ∈ Icc a' b', ∀ ω ∈ Good N, qvRate X E N σ a u ω
      ≤ qvShape Wr ℓu ℓs ηu D (Jst u ω) Smax ρfar Lr Tval)
    (hQBd : 0 ≤ QBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn) (hc : 0 ≤ c)
    (hgint : IntervalIntegrable (gModel P W p X E N σ a Good Tt Rn) volume a' b')
    (hbudget : (2 * (p : ℝ) - 1)
      * ((b' - a') * QBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn) ≤ c ^ 2) :
    √((2 * (p : ℝ) - 1) * ∫ r in a'..b', gModel P W p X E N σ a Good Tt Rn r) ≤ c :=
  qv_bound_of_const hab hp hc hgint
    (fun u hu => gModel_le_QBd hW0 hW1 hp X E N σ a hWr hℓu hηu hLr hnorm (hJ0 u hu)
      (hJ u hu) (hQ u hu) hQBd) hbudget

/-- **⭐ The `hdrift` slot on the first cell**, with the cross term integrated by T268's
`s = 0` branch (**no `log`**) and the drift by its constant envelope.  `hfit` is the arithmetic
of the slot choice: an inequality between two explicit deterministic numbers. -/
theorem drift_bound_first_cell {E : ℝ} (hE : |E| < 2) {tc κh Qm Nr ε δ : ℝ}
    {Adr Bcr Qh : ℝ → ℝ} {Qb Dbd : ℝ}
    (ht0 : 0 ≤ tc) (ht : tc ≤ 1 / 2) (hN : 1 ≤ Nr) (hε : 0 ≤ ε) (hκ0 : 0 ≤ κh)
    (hκ : κh ≤ Nr ^ (ε - 4 * δ) * (etaT E 0)⁻¹) (hQm : 0 ≤ Qm)
    (hQle : ∀ u ∈ Icc (0 : ℝ) tc, Qh u ≤ Qm)
    (hcint : IntervalIntegrable (crossInt κh Qh) volume 0 tc)
    (hABint : IntervalIntegrable (fun r => Adr r + Bcr r) volume 0 tc)
    (hAbd : ∀ u ∈ Icc (0 : ℝ) tc, Adr u ≤ Qb)
    (hBbd : ∀ u ∈ Icc (0 : ℝ) tc, Bcr u ≤ crossInt κh Qh u)
    (hfit : 2 * (tc * Qb + 4 * Nr ^ (ε - 2 * δ) * (etaT E tc / etaT E 0) ^ 2
      * √(2 * Qm * (mE E).im⁻¹)) ≤ Dbd) :
    2 * (∫ r in (0 : ℝ)..tc, (Adr r + Bcr r)) ≤ Dbd := by
  have hsum : (∫ r in (0 : ℝ)..tc, (Adr r + Bcr r))
      ≤ ∫ r in (0 : ℝ)..tc, (Qb + crossInt κh Qh r) :=
    intervalIntegral.integral_mono_on ht0 hABint (intervalIntegrable_const.add hcint)
      fun u hu => add_le_add (hAbd u hu) (hBbd u hu)
  have hsplit : (∫ r in (0 : ℝ)..tc, (Qb + crossInt κh Qh r))
      = tc * Qb + ∫ r in (0 : ℝ)..tc, crossInt κh Qh r := by
    rw [intervalIntegral.integral_add intervalIntegrable_const hcint,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm tc Qb, mul_comm Qb tc]
  have htime := integral_crossInt_first_cell_le hE ht0 ht hN hε hκ0 hκ hQm hQle hcint
  refine le_trans (mul_le_mul_of_nonneg_left (hsum.trans (le_of_eq hsplit)) (by norm_num)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl htime) (by norm_num)) hfit

end Composite


/-! ### 6. The chain: one-step bound → `APrimeHyp` → the `cut` field of the first pass

`RBM.Step2Bootstrap.aprimeHyp_of_stepBound` closes the chain against T197's *unprimed*
`RBM.CutHypTheta.StepSide`.  Route (A′) runs on T263's rescaled `RBM.StepSideAPrime.StepSide''`
(the level is `cWt·x^{16}R⁴` and the slot `κ` of the fixed-`ω` generator identity is new), so
the primed counterpart is built here from `RBM.APrimeOneStep.weightedMoment_of_stepBoundPos''`
— which has the `p = 0` branch already discharged, so a producer only argues for `1 ≤ p`. -/

section Chain

open MomentDuhamelCut CutHypTheta MeasureTheory Step2Bootstrap

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ}
  {s t : ℕ → ℝ} {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}

/-- **⭐ The one-step moment bound at one net point, from the three slot bounds.**

`hG` is the conclusion of the weighted Minkowski closure (G)
(`RBM.MomentDuhamel.weightedMinkowski_of_deriv_le`, a theorem since T264); `hinit`, `hdrift`,
`hqv` are the slots §3–§5 fill.  The output is the shape
`RBM.APrimeOneStep.weightedMoment_of_stepBound''` consumes. -/
theorem oneStep_of_slots {m x R Ξ A ε q β γ κ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (hside : StepSide'' x R Ξ A ε q β γ κ Jv) {a b : ℝ} {p : ℕ} (hp : 1 ≤ p)
    {W Jf : Ω → ℝ} {Y : ℝ → Ω → ℝ} {Adr Bcr g : ℝ → ℝ} {θ : ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω)
    (hYint : Integrable (fun ω => W ω * |Y b ω| ^ (2 * p)) P)
    (hdom : ∀ ω, |cutTrunc θ (Jf ω)| ≤ |Y b ω|)
    (hG : momNormW P W p (Y b)
      ≤ momNormW P W p (Y a) + 2 * (∫ r in a..b, (Adr r + Bcr r))
        + √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r))
    (hinit : momNormW P W p (Y a) ≤ initTerm x R Ξ / R ^ 4)
    (hdrift : 2 * (∫ r in a..b, (Adr r + Bcr r))
      ≤ driftTerm m x R Ξ A ε q β γ Jv / R ^ 4)
    (hqv : √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r) ≤ tailTerm x R κ / R ^ 4) :
    ∫ ω, W ω * |cutTrunc θ (Jf ω)| ^ (2 * p) ∂P
      ≤ ((Step2MomentStep.cStep' m + 1) * x ^ 2) ^ (2 * p) :=
  oneStep_integral_le_sq hx hm hside hp hW0 hYint hdom
    (stepRhs''_div_of_slots hG hinit hdrift hqv)

/-- **⭐⭐ `RBM.Step2Bootstrap.aprimeHyp_of_stepBound` for T263's rescaled side conditions.**

Identical in role to the unprimed version: every field of `APrimeHyp` but the last comes from
`H`, and the last is the one-step bound at one net point — here stated with
`RBM.StepSideAPrime.StepSide''` and `RBM.StepSideAPrime.stepRhs''`, and asked **only for
`1 ≤ p`** (the `p = 0` clause is a theorem, `RBM.APrimeOneStep.oneStep_pzero`). -/
noncomputable def aprimeHyp_of_stepBound'' [IsProbabilityMeasure P] {m : ℝ} (hm : 0 < m)
    (hΘ : ∀ N, Θ N = 1) (H : APrimeHyp P J s t lev Θ)
    (Hstep : ∀ δ, 0 < δ → δ ≤ H.δ₀ → ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t H.mesh N, ∃ R Ξ A ε q β γ κ Jv : ℝ,
        StepSide'' ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv ∧
          ∫ ω, H.W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s H.mesh N k))
              (J N (cutNetPt s H.mesh N k) ω)| ^ (2 * p) ∂P
            ≤ (stepRhs'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv / R ^ 4) ^ (2 * p)) :
    APrimeHyp P J s t lev Θ :=
  { H with
    weightedMoment := weightedMoment_of_stepBoundPos'' hm hΘ
      (fun δ N k ω => H.W_nonneg δ N k ω) (fun δ N k ω => H.W_le_one δ N k ω)
      (fun δ N k => H.W_meas δ N k) Hstep }

variable {B : Band Ω} {E : ℝ}

/-- **⭐⭐⭐ The `cut` field of the first pass, from the rescaled one-step bound.**

`RBM.Step2Bootstrap.momentHypCutEv_of_aprime` composed with `aprimeHyp_of_stepBound''`: the
moment field of route (A′) is no longer a field of the input, it is the one-step bound the
Duhamel produces at one net point, in T263's rescaled arithmetic.

⚠ This is the **unrestricted** interface, whose `modulus` field is quantified over every `ω`;
for `J = jSnorm` that reading is false (T249).  It is recorded here because it is the exact
`''` counterpart of the existing `RBM.Step2Bootstrap.momentHypCutEv_of_aprime`, and because it
is the right statement on windows where the `‖X‖`-free modulus of T257 is available.  **The
route the assembly uses is §8's**, which takes the event-restricted `APrimeHypOn` instead. -/
noncomputable def momentHypCutEv_of_stepBound'' {X : Sample B} {D : ℝ} {m : ℝ} (hm : 0 < m)
    (H : APrimeHyp B.P (fun N u ω => Step2Moment.jSnorm X E D s N u ω) s t
      (fun _ _ => (1 : ℝ)) (fun _ => 1))
    (Hstep : ∀ δ, 0 < δ → δ ≤ H.δ₀ → ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t H.mesh N, ∃ R Ξ A ε q β γ κ Jv : ℝ,
        StepSide'' ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv ∧
          ∫ ω, H.W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * (1 : ℝ))
              (Step2Moment.jSnorm X E D s N (cutNetPt s H.mesh N k) ω)| ^ (2 * p) ∂B.P
            ≤ (stepRhs'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv / R ^ 4) ^ (2 * p))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    MomentDuhamelCut.MomentHypCutEv X E s t D :=
  letI := B.isProbabilityMeasure
  momentHypCutEv_of_aprime (aprimeHyp_of_stepBound'' hm (fun _ => rfl) H Hstep) hinit

end Chain


/-! ### 7. Slot 2 of the merged assembly, asked in the shape route (A′) can produce

The merged assembly's second slot is `∀ D ≥ 60, RBM.MomentDuhamelCut.MomentHypCut X E s t D`,
whose `cut` field is the **`∀ N`** bundle `RBM.MomentDuhamelCut.CutHyp`.  T232 proved that
reading unsatisfiable for a genuinely time-dependent functional
(`RBM.CutHypTheta.sat_no_cutHypCond`), and route (A′) accordingly produces the `∀ᶠ N` bundle
`RBM.MomentDuhamelCut.MomentHypCutEv`.

The gap is **purely one of shape**: reading `RBM.MomentDuhamelCut.step2_cut_of_reg`, the slot-2
input is consumed at exactly one place, `RBM.MomentDuhamelCut.jS_stochDom_cut`, and that
statement has a verbatim `Ev` counterpart, `RBM.MomentDuhamelCut.jS_stochDom_cutEv`, with the
same conclusion.  So the whole chain below `boundsCore_step_of_inputs_reg_W` goes through with
`MomentHypCutEv` in place of `MomentHypCut`, and the table that results is **strictly harder to
satisfy** — `RBM.MomentDuhamelCut.MomentHypCutEv.of_momentHypCut` is the compiled certificate
of that direction (`mergedOnAllEv_slot2_weaker` below).

Nothing above is changed: every statement here is new. -/

section MergedEv

open MomentDuhamelCut MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **(2.76) from the `∀ᶠ N` slot.**  `RBM.MomentDuhamelCut.aprioriDecay_cut_of_cond272` with
`RBM.MomentDuhamelCut.jS_stochDom_cutEv` in place of `jS_stochDom_cut`. -/
theorem aprioriDecay_cutEv_of_cond272 (X : Sample B)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentHypCutEv X E s t D) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272 B E s t) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) :=
  StepGlue.aprioriDecay_of_jS_of_cond272 X hE hs0 hst ht1 hcond
    fun D hD => jS_stochDom_cutEv (Hy D hD) hE hst ht1

/-- **Step 2 from the `∀ᶠ N` slot.**  `RBM.MomentDuhamelCut.step2_cut_of_reg`, verbatim. -/
theorem step2_cutEv_of_reg (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (Hy : ∀ D : ℝ, 60 ≤ D → MomentHypCutEv X E s t D)
    (h1 : Step1.Hyp X E s t) (hB : BoundsCore X E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hcond : Cond272 B E s t)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) := by
  have hE : |E| < 2 := by linarith
  have h276 := aprioriDecay_cutEv_of_cond272 X Hy hE hs0 hst ht1 hcond
  have hfacts := StepGlue.eventually_R4_le_scale_of_cond272 hE hs0 hst ht1 hcond hreg
  have h274 := Step1.weakLaw X hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg h1
  exact ⟨StepGlue.localLaw_of_scale_facts X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hfacts h276 h274
      h1.lemma41, h276⟩

/-- **One step of the p. 24 grid, with slot 2 in the `∀ᶠ N` shape.**  Verbatim
`RBM.boundsCore_step_of_inputs_reg_W`. -/
theorem boundsCore_step_of_inputs_reg_W_ev (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c) (hB : BoundsCore X E s)
    (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentHypCutEv X E s t D)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45 : StepGlue.Eq45Flow X E s t) (h548 : FlowEq548Sm X E s t) :
    BoundsCore X E t :=
  boundsCore_step_of_flow_reg_W X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg
    (Step1.step1 X hκ0 hEκ hB hs0 hst ht1 hreg.1 hc0 hreg.2 h1).1
    (step2_cutEv_of_reg X hκ0 hκ1 hEκ Hy h1 hB hs0 hst ht1 hc0 hreg.1 hreg.2).1 hΘ h514
    h45 h548

/-- The same at T249's repaired slots 3 and 6.  Verbatim
`RBM.boundsCore_step_of_inputs_mergedOn`. -/
theorem boundsCore_step_of_inputs_mergedOn_ev (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore X E s) (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentHypCutEv X E s t D)
    (hcut : CutHypEvOnSlot X E s t)
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45i : Eq45FlowInputs X E s t) (H : Eq548EntryDataEvOn' X E s t) :
    BoundsCore X E t :=
  boundsCore_step_of_inputs_reg_W_ev X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1 Hy
    (flow_hTheta_of_cutHypEvOn X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1 hreg.1 hB hcut)
    h514 (eq45Flow_of_eq45FlowInputs X hκ0 hκ1 hEκ hs0 ht1 h45i)
    (flowEq548Sm_of_entryDataEvOn X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1
      hreg.toCond272 hB H)

/-- **⭐⭐ The merged assembly of `RBM.thm221NoEL_of_inputs_mergedOnAll`, with slot 2 in the
`∀ᶠ N` shape route (A′) produces.**  The conclusion is still `RBM.Thm221NoEL X κ`, the first
cell of p. 24's grid included (D17). -/
theorem thm221NoEL_of_inputs_mergedOnAll_ev (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentHypCutEv X E s t D)
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      BoundsCore X E s → CutHypEvOnSlot X E s t)
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45i : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Eq45FlowInputs X E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      Eq548EntryDataEvOn' X E s t) :
    Thm221NoEL X κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_mergedOn_ev X hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (h1 E hE s t hs0 hst ht1 c hc0 hreg) (Hy E hE s t hs0 hst ht1 c hc0 hreg)
      (hcut E hE s t hs0 hst ht1 c hc0 hreg hB) (h514 E hE s t hs0 hst ht1 c hc0 hreg)
      (h45i E hE s t hs0 hst ht1 c hc0 hreg) (h548e E hE s t hs0 hst ht1 c hc0 hreg)

/-- **The new slot 2 is implied by the old one**, so the table above is nowhere easier to
satisfy than `RBM.thm221NoEL_of_inputs_mergedOnAll`'s: this is a genuine weakening of the
hypothesis, not a relabelling. -/
noncomputable def mergedOnAllEv_slot2_weaker (X : Sample B) {D : ℝ} :
    MomentHypCut X E s t D → MomentHypCutEv X E s t D :=
  fun Hy => MomentHypCutEv.of_momentHypCut Hy

end MergedEv


/-! ### 8. ⭐⭐⭐ Slot 2 **produced**, from route (A′)'s event-restricted interface

Reading `RBM.MomentDuhamelCut.jS_stochDom_cutEv`, slot 2 is used for exactly one statement:

`J*_{u,D}/R⁴ ≺ 1` uniformly on the window — `jsNormDom` below.

That statement is what `RBM.Step2Bootstrap.stochDom_of_aprimeOn` **proves**, from
`RBM.Step2Bootstrap.APrimeHypOn` (T249's interface, whose `modulus` field is asked only on a
high-probability event, so it is not the shape T249 refuted), a `RBM.HighProb` for the event,
and (2.69).  The moment field of that interface is in turn the one-step bound of T263's
rescaled arithmetic, by `aprimeHypOn_of_stepBound''`.

⚠ **Why `APrimeHypOn` and not `APrimeHyp`.**  `APrimeHyp.modulus` is quantified over *every*
`ω`, and for `J = jSnorm` that reading is false: the Hölder constant of `u ↦ G_u` is `O(‖X‖)`
and `‖X‖` is unbounded (`RBM.t249_witness_norm_gt`).  Filling slot 2 with an `APrimeHyp` for
`jSnorm` would therefore be filling it with an unsatisfiable hypothesis — the exact defect the
satisfiability discipline exists to catch.  `APrimeHypOn` carries the event, and D17 says the
event route reaches the first cell `[0, u₁]` as well. -/

section Slot2

open MomentDuhamelCut CutHypTheta MeasureTheory Step2Bootstrap StepSideAPrime

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ}
  {s t : ℕ → ℝ} {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ} {Good : ℕ → Set Ω}

/-- `aprimeHyp_of_stepBound''` for the event-restricted interface. -/
noncomputable def aprimeHypOn_of_stepBound'' [IsProbabilityMeasure P] {m : ℝ} (hm : 0 < m)
    (hΘ : ∀ N, Θ N = 1) (H : APrimeHypOn P J s t lev Θ Good)
    (Hstep : ∀ δ, 0 < δ → δ ≤ H.δ₀ → ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t H.mesh N, ∃ R Ξ A ε q β γ κ Jv : ℝ,
        StepSide'' ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv ∧
          ∫ ω, H.W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s H.mesh N k))
              (J N (cutNetPt s H.mesh N k) ω)| ^ (2 * p) ∂P
            ≤ (stepRhs'' m ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv / R ^ 4) ^ (2 * p)) :
    APrimeHypOn P J s t lev Θ Good :=
  { H with
    weightedMoment := weightedMoment_of_stepBoundPos'' hm hΘ
      (fun δ N k ω => H.W_nonneg δ N k ω) (fun δ N k ω => H.W_le_one δ N k ω)
      (fun δ N k => H.W_meas δ N k) Hstep }

variable {B : Band Ω} {E : ℝ}

/-- **Slot 2, reduced to the statement it is used for**: `(5.47)` in normalized form. -/
def JSNormDom (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D : ℝ) : Prop :=
  StochDom B.P
    (fun N (u : TimeIcc s t N) ω => Step2Moment.jSnorm X E D s N (u : ℝ) ω)
    (fun _ _ _ => (1 : ℝ))

/-- **⭐⭐ Slot 2 from route (A′).**  `RBM.Step2Bootstrap.stochDom_of_aprimeOn` at
`Θ ≡ 1`, `lev ≡ 1`, for the functional `J*_{u,D}/R⁴` the interface names. -/
theorem jsNormDom_of_aprimeOn {X : Sample B} {D : ℝ}
    (H : APrimeHypOn B.P (fun N u ω => Step2Moment.jSnorm X E D s N u ω) s t
      (fun _ _ => (1 : ℝ)) (fun _ => 1) Good)
    (hgood : HighProb B.P Good)
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    JSNormDom X E s t D :=
  letI := B.isProbabilityMeasure
  stochDom_of_aprimeOn H hgood (Filter.Eventually.of_forall fun _ => le_rfl) hinit

/-- **(5.47)** from `JSNormDom`: `RBM.MomentDuhamelCut.jS_stochDom_cutEv`, whose proof uses
`Hy` only through `stochDom_jSnorm_cutEv`. -/
theorem jS_stochDom_of_jsNormDom {X : Sample B} {D : ℝ} (Hy : JSNormDom X E s t D)
    (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 4) := by
  refine StochDom.of_subset Hy fun τ hτ => ⟨τ, hτ, ?_⟩
  refine Filter.Eventually.of_forall fun N ω hω => ?_
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hR : 0 < Step2Moment.ratR E s N (u : ℝ) ^ 4 :=
    pow_pos (Step2Moment.ratR_pos hE hs1 (u.2.2.trans_lt (ht1 N))) 4
  change (N : ℝ) ^ τ * 1 < Step2.jS X E D N (u : ℝ) ω / Step2Moment.ratR E s N (u : ℝ) ^ 4
  rw [mul_one, lt_div_iff₀ hR]
  exact hu

/-- **The new slot 2 is implied by the old one**, so §9's table is nowhere easier to satisfy
than `RBM.thm221NoEL_of_inputs_mergedOnAll`'s: `RBM.MomentDuhamelCut.stochDom_jSnorm_cut`. -/
theorem jsNormDom_of_momentHypCut {X : Sample B} {D : ℝ} (Hy : MomentHypCut X E s t D) :
    JSNormDom X E s t D :=
  stochDom_jSnorm_cut Hy

/-- The same from the `∀ᶠ N` slot of §7. -/
theorem jsNormDom_of_momentHypCutEv {X : Sample B} {D : ℝ} (Hy : MomentHypCutEv X E s t D) :
    JSNormDom X E s t D :=
  stochDom_jSnorm_cutEv Hy

/-- (2.76) from `JSNormDom`. -/
theorem aprioriDecay_of_jsNormDom (X : Sample B)
    (Hy : ∀ D : ℝ, 60 ≤ D → JSNormDom X E s t D) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272 B E s t) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) :=
  StepGlue.aprioriDecay_of_jS_of_cond272 X hE hs0 hst ht1 hcond
    fun D hD => jS_stochDom_of_jsNormDom (Hy D hD) hE hst ht1

/-- Step 2 from `JSNormDom`. -/
theorem step2_of_jsNormDom (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (Hy : ∀ D : ℝ, 60 ≤ D → JSNormDom X E s t D)
    (h1 : Step1.Hyp X E s t) (hB : BoundsCore X E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hcond : Cond272 B E s t)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) := by
  have hE : |E| < 2 := by linarith
  have h276 := aprioriDecay_of_jsNormDom X Hy hE hs0 hst ht1 hcond
  have hfacts := StepGlue.eventually_R4_le_scale_of_cond272 hE hs0 hst ht1 hcond hreg
  have h274 := Step1.weakLaw X hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg h1
  exact ⟨StepGlue.localLaw_of_scale_facts X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hfacts h276 h274
      h1.lemma41, h276⟩

/-- One step of the p. 24 grid, with slot 2 replaced by `JSNormDom`. -/
theorem boundsCore_step_of_inputs_mergedOn_aprime (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore X E s) (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → JSNormDom X E s t D)
    (hcut : CutHypEvOnSlot X E s t)
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45i : Eq45FlowInputs X E s t) (H : Eq548EntryDataEvOn' X E s t) :
    BoundsCore X E t :=
  boundsCore_step_of_flow_reg_W X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg
    (Step1.step1 X hκ0 hEκ hB hs0 hst ht1 hreg.1 hc0 hreg.2 h1).1
    (step2_of_jsNormDom X hκ0 hκ1 hEκ Hy h1 hB hs0 hst ht1 hc0 hreg.1 hreg.2).1
    (flow_hTheta_of_cutHypEvOn X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1 hreg.1 hB hcut)
    h514 (eq45Flow_of_eq45FlowInputs X hκ0 hκ1 hEκ hs0 ht1 h45i)
    (flowEq548Sm_of_entryDataEvOn X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1
      hreg.toCond272 hB H)

end Slot2


/-! ### 9. The merged assembly with slot 2 gone

`RBM.thm221NoEL_of_inputs_mergedOnAll`'s table is

`RBM.Step1.Hyp` · **`RBM.MomentDuhamelCut.MomentHypCut`** · `RBM.CutHypEvOnSlot` ·
`RBM.Step3.Lemma514` · `RBM.Eq45FlowInputs` · `RBM.Eq548EntryDataEvOn'`.

Below, the starred slot is replaced by `APrimeSlot` — route (A′)'s event-restricted interface,
its high-probability event and (2.69) — and the conclusion is still `RBM.Thm221NoEL X κ`.
`APrimeSlot`'s only non-deterministic field is `RBM.Step2Bootstrap.APrimeHypOn.weightedMoment`,
and `aprimeHypOn_of_stepBound''` (§8) produces *that* from the one-step bound of T263's
rescaled arithmetic, whose three slots §§3–5 fill. -/

section MergedAPrime

open MomentDuhamelCut CutHypTheta MeasureTheory Step2Bootstrap StepSideAPrime

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **Route (A′)'s slot-2 package.**  The `modulus` field lives on `Good`, which is what makes
it satisfiable (T249/D17); the moment field is the one-step bound, via
`aprimeHypOn_of_stepBound''`; `init` is (2.69), literally
`RBM.MomentDuhamelCut.MomentHypCut.init`, unchanged. -/
structure APrimeSlot (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D : ℝ) where
  /-- The high-probability event carrying the time modulus (in the application `{‖X‖ ≤ N}`). -/
  Good : ℕ → Set Ω
  /-- T249's event-restricted interface of route (A′). -/
  hyp : APrimeHypOn B.P (fun N u ω => Step2Moment.jSnorm X E D s N u ω) s t
    (fun _ _ => (1 : ℝ)) (fun _ => 1) Good
  /-- The event is of high probability. -/
  good : HighProb B.P Good
  /-- **(2.69)**, unchanged from `RBM.MomentDuhamelCut.MomentHypCut.init`. -/
  init : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
    (fun _ _ _ => (1 : ℝ))

/-- **⭐⭐⭐ Slot 2, produced.** -/
theorem jsNormDom_of_aprimeSlot {X : Sample B} {D : ℝ} (S : APrimeSlot X E s t D) :
    JSNormDom X E s t D :=
  jsNormDom_of_aprimeOn S.hyp S.good S.init

/-- **⭐⭐⭐ The merged assembly with slot 2 replaced by route (A′)'s interface.**

The table is `RBM.Step1.Hyp` · **`APrimeSlot`** · `RBM.CutHypEvOnSlot` ·
`RBM.Step3.Lemma514` · `RBM.Eq45FlowInputs` · `RBM.Eq548EntryDataEvOn'`, on **every** window
`0 ≤ s ≤ t < 1` (the first cell of p. 24's grid included, D17), and the conclusion is
`RBM.Thm221NoEL X κ`.  `RBM.MomentDuhamelCut.MomentHypCut` does not occur. -/
theorem thm221NoEL_of_inputs_mergedOnAll_aprime (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 60 ≤ D → APrimeSlot X E s t D)
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      BoundsCore X E s → CutHypEvOnSlot X E s t)
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45i : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Eq45FlowInputs X E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      Eq548EntryDataEvOn' X E s t) :
    Thm221NoEL X κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_mergedOn_aprime X hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (h1 E hE s t hs0 hst ht1 c hc0 hreg)
      (fun D hD => jsNormDom_of_aprimeSlot (Hy E hE s t hs0 hst ht1 c hc0 hreg D hD))
      (hcut E hE s t hs0 hst ht1 c hc0 hreg hB) (h514 E hE s t hs0 hst ht1 c hc0 hreg)
      (h45i E hE s t hs0 hst ht1 c hc0 hreg) (h548e E hE s t hs0 hst ht1 c hc0 hreg)

end MergedAPrime


/-! ### 10. Satisfiability

Three things are checked, in the order `CLAUDE.md`'s discipline lists them.

1. **The one-step hypothesis of `aprimeHypOn_of_stepBound''` is inhabited**, and inhabited on
   a *non-degenerate* instance: `sat_aprimeHypOn_of_stepBound''` runs it on T230's compiled
   interface `RBM.Step2Bootstrap.satAPrimeHypOn`, whose functional `J_u = 2u⁺` is genuinely
   time-dependent (T232's counterexample applies to it, which is why the interface is the
   `∀ᶠ N` one) and whose window is `[0, 1]` — **left endpoint exactly `0`**, D17.  The weight
   is the soft-max weight, not the constant `1`.
2. **The slot bounds of §§3–5 are not vacuous**: `sat_qv_bound_of_const` and
   `sat_crossInt_first_cell` fire with every quantity **strictly positive** — no `Q ≡ 0`, no
   `s = t`, no `κ̂ = 0` — on the first cell, whose left endpoint is `0`.
3. **The new slot 2 is not weaker by accident**: `mergedOnAllEv_slot2_weaker` (§7) compiles the
   direction `MomentHypCut → MomentHypCutEv`, and §8's route replaces the slot by a statement
   (`JSNormDom`) that the old slot *implies* (`jsNormDom_of_momentHypCut`), so §9's table is
   nowhere easier to satisfy than `RBM.thm221NoEL_of_inputs_mergedOnAll`'s. -/

section Sat

open MomentDuhamelCut CutHypTheta MeasureTheory Step2Bootstrap StepSideAPrime

/-- The one-step right-hand side is at least `3` once `1 ≤ x`: the constant slot alone is
`x(R²+1)+1 ≥ 3`.  (`RBM.StepSideAPrime.one_le_stepRhs''` only extracts the `+1`.) -/
theorem three_le_stepRhs'' {m x R Ξ A ε q β γ κ Jv : ℝ} (hx : 1 ≤ x) (hm : 0 < m)
    (H : StepSide'' x R Ξ A ε q β γ κ Jv) : 3 ≤ stepRhs'' m x R Ξ A ε q β γ κ Jv := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR1 : (1 : ℝ) ≤ R := H.R_ge
  have hR0 : (0 : ℝ) < R := by linarith
  have hAthr : (0 : ℝ) < cWt ^ 2 * x ^ 33 * R ^ 10 :=
    mul_pos (mul_pos (pow_pos cWt_pos 2) (pow_pos hx0 33)) (pow_pos hR0 10)
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le hAthr H.A_ge
  have hmi : (0 : ℝ) < m⁻¹ := inv_pos.2 hm
  have hJ0 := H.Jv_nonneg
  have hsJ : (0 : ℝ) ≤ √Jv := Real.sqrt_nonneg _
  have h1 : (0 : ℝ) ≤ x * R ^ 2 * Ξ :=
    mul_nonneg (mul_nonneg hx0.le (by positivity)) H.Ξ_nonneg
  have h2 : (0 : ℝ) ≤ x * R ^ 2 * κ :=
    mul_nonneg (mul_nonneg hx0.le (by positivity)) H.κ_nonneg
  have h3 : (0 : ℝ) ≤ Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2
      * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + x * m⁻¹ * R ^ 2 * (q + β * Jv + γ * (Jv * √Jv))) := by
    have hi : (0 : ℝ) ≤ A⁻¹ := (inv_pos.2 hA0).le
    have hbJ : (0 : ℝ) ≤ β * Jv := mul_nonneg H.β_nonneg hJ0
    have hgJ : (0 : ℝ) ≤ γ * (Jv * √Jv) := mul_nonneg H.γ_nonneg (mul_nonneg hJ0 hsJ)
    have hbr1 : (0 : ℝ) ≤ 36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε :=
      add_nonneg (mul_nonneg (mul_nonneg (by linarith) (by positivity)) hi)
        (mul_nonneg (by positivity) H.ε_nonneg)
    have hc : (0 : ℝ) ≤ exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2
        * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε) :=
      mul_nonneg (mul_nonneg (exp_pos 1).le (sq_nonneg _)) hbr1
    have hsum : (0 : ℝ) ≤ q + β * Jv + γ * (Jv * √Jv) := by
      have := H.q_nonneg; linarith
    have hd : (0 : ℝ) ≤ x * m⁻¹ * R ^ 2 * (q + β * Jv + γ * (Jv * √Jv)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hx0.le hmi.le) (by positivity)) hsum
    exact mul_nonneg H.Ξ_nonneg (by linarith)
  have hR2 : (1 : ℝ) ≤ R ^ 2 := one_le_pow₀ hR1
  have h4 : (2 : ℝ) ≤ x * (R ^ 2 + 1) := by nlinarith
  unfold stepRhs''
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **⭐ The one-step hypothesis of `aprimeHypOn_of_stepBound''` is inhabited**, on T230's
compiled interface: the soft-max weight, the genuinely time-dependent functional `J_u = 2u⁺`,
and the window `[0, 1]` whose **left endpoint is `0`**. -/
noncomputable def sat_aprimeHypOn_of_stepBound'' (P : Measure Ω) [IsProbabilityMeasure P] :
    APrimeHypOn P (fun _ u (_ : Ω) => 2 * max u 0) (fun _ => 0) (fun _ => 1)
      (fun _ _ => (1 : ℝ)) (fun _ => 1) (fun _ => Set.univ) := by
  refine aprimeHypOn_of_stepBound'' (m := 1) one_pos (fun _ => rfl) (satAPrimeHypOn P) ?_
  intro δ hδ0 _ p hp
  filter_upwards [eventually_ge_atTop 1] with N hN1 k hk
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hNR (by linarith)
  refine ⟨1, _, _, _, _, _, _, _, _, sat_StepSide''_half hx le_rfl, ?_⟩
  set H := satAPrimeHypOn P with hHdef
  set w : ℝ := cutNetPt (fun _ => (0 : ℝ)) H.mesh N k with hw
  have hmem : w ∈ Set.Icc (0 : ℝ) 1 :=
    netFinset_subset_Icc (H.window N) (H.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hJle : ∀ ω : Ω,
      |cutTrunc ((N : ℝ) ^ (2 * δ) * (1 : ℝ)) (2 * max w 0)| ≤ 2 := by
    intro _
    have h0 : (0 : ℝ) ≤ 2 * max w 0 := by positivity
    have hle : 2 * max w 0 ≤ 2 := by
      have : max w 0 ≤ 1 := max_le hmem.2 (by norm_num)
      linarith
    rw [abs_of_nonneg (cutTrunc_nonneg h0)]
    exact (cutTrunc_le_self h0).trans hle
  have hbound : ∀ ω : Ω, H.W δ N k ω *
      |cutTrunc ((N : ℝ) ^ (2 * δ) * (1 : ℝ)) (2 * max w 0)| ^ (2 * p) ≤ 2 ^ (2 * p) := by
    intro ω
    calc H.W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * (1 : ℝ)) (2 * max w 0)| ^ (2 * p)
        ≤ 1 * |cutTrunc ((N : ℝ) ^ (2 * δ) * (1 : ℝ)) (2 * max w 0)| ^ (2 * p) :=
          mul_le_mul_of_nonneg_right (H.W_le_one δ N k ω) (by positivity)
      _ = |cutTrunc ((N : ℝ) ^ (2 * δ) * (1 : ℝ)) (2 * max w 0)| ^ (2 * p) := one_mul _
      _ ≤ 2 ^ (2 * p) := pow_le_pow_left₀ (abs_nonneg _) (hJle ω) _
  have hint : (∫ ω, H.W δ N k ω *
      |cutTrunc ((N : ℝ) ^ (2 * δ) * (1 : ℝ)) (2 * max w 0)| ^ (2 * p) ∂P)
      ≤ 2 ^ (2 * p) := by
    have := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ω =>
        mul_nonneg (H.W_nonneg δ N k ω) (by positivity : (0:ℝ) ≤ _ ^ (2 * p)))
      (integrable_const (μ := P) ((2 : ℝ) ^ (2 * p)))
      (Filter.Eventually.of_forall hbound)
    simpa using this
  refine hint.trans (pow_le_pow_left₀ (by norm_num) ?_ _)
  have h3 := three_le_stepRhs'' (m := 1) hx one_pos (sat_StepSide''_half hx (le_rfl : (1:ℝ) ≤ 1))
  simp only [one_pow, div_one] at h3 ⊢
  linarith

/-- **⭐ The `hqv` slot is met with room to spare on the first cell**, at strictly positive
data: `p = 1`, the cell `[0, 1/2]` (**left endpoint `0`**), a rate `g ≡ 1` that does **not**
vanish, envelope `Q^{bd} = 1` and budget `c = 1`. -/
theorem sat_qv_bound_of_const :
    √((2 * ((1 : ℕ) : ℝ) - 1) * ∫ _r in (0 : ℝ)..(1 / 2), (1 : ℝ)) ≤ 1 := by
  refine qv_bound_of_const (by norm_num) (p := 1) le_rfl zero_le_one
    intervalIntegrable_const (fun _ _ => le_rfl) ?_
  norm_num

/-- **⭐ The first cell's (S6) integral fires at strictly positive data**, with **no `log`**:
`t = 1/2`, `κ̂ > 0`, `Q ≡ Q_m > 0`, `ε = 0`, `δ = 0`, `N = 1`.  Nothing has collapsed. -/
theorem sat_crossInt_first_cell {E : ℝ} (hE : |E| < 2) :
    (∫ u in (0 : ℝ)..(1 / 2), crossInt (etaT E 0)⁻¹ (fun _ => 1) u)
      ≤ 4 * (1 : ℝ) ^ ((0 : ℝ) - 2 * 0) * (etaT E (1 / 2) / etaT E 0) ^ 2
          * √(2 * 1 * (mE E).im⁻¹) := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  have he0 : (0 : ℝ) < etaT E 0 := by
    have : etaT E 0 = (mE E).im := by rw [etaT]; ring
    rw [this]; exact hm
  refine integral_crossInt_first_cell_le hE (by norm_num) le_rfl le_rfl le_rfl
    (le_of_lt (inv_pos.2 he0)) ?_ zero_le_one (fun _ _ => le_rfl) ?_
  · rw [Real.one_rpow, one_mul]
  · exact (APrimeTimeInt.intervalIntegrable_sqrt_inv (by norm_num)).mul_const _

end Sat

end APrimeModel

end RBM

/-!
## Deviations from the paper

**T271a** (§5.3, (5.39)–(5.48); the merged assembly of Theorem 2.21).

1. *Slot 2 of the assembly is reduced to the statement it is used for.*  The repository's
   merged assembly asks for the bundle `RBM.MomentDuhamelCut.MomentHypCut`, whose `cut` field
   is the `∀ N` reading T232 refuted.  Reading `RBM.MomentDuhamelCut.step2_cut_of_reg`, that
   bundle is consumed at exactly one place, `RBM.MomentDuhamelCut.jS_stochDom_cut`, so §8
   replaces it by the single conclusion `JSNormDom` — `J*_{u,D}/R⁴ ≺ 1` on the window, which
   is (5.47) in normalized form and *is* a statement of the paper.  `jsNormDom_of_momentHypCut`
   compiles the direction that makes the new table no easier to satisfy.  This is bookkeeping
   internal to the formalization (the consequence of `T230a`), not a change to any statement of
   the paper.
2. *The `u^{-1/2}` weight of the cross term is displayed.*  The paper's (5.41) does not carry
   the factors `√(u_j/u)` (the Duhamel rescaling) and `(2√u)⁻¹` (the prefactor of the fixed-`ω`
   generator identity); they are the referee's (S5), left by T265 as a caller obligation and
   discharged in §4 here as `sqrt_div_le_sqrt_inv` and `inv_two_sqrt_le_sqrt_inv`.  Their
   product is majorized by `u^{-1/2}`, which is the integrand weight of (S6).  Recorded already
   as `T265a`-3; nothing new is assumed.
3. *A weighted `L^p` rate norm.*  `rateNormW` is the weight-carrying version of the norm in
   which (5.42) is read.  The paper states (5.42) pointwise; the weight is the device of
   `T230a` that replaces the stopping time of (5.43), so this is the same deviation, applied to
   the quadratic-variation slot.
4. *The rates are defined with the good event built in.*  `qvRateOn` is `0` off `Good N`.
   This is T249's `RBM.Step2Bootstrap.onEvent` at the level of the rate, and it is what makes
   the deterministic envelopes of §3 satisfiable: the `∀ ω` reading of a size bound on these
   functionals is false, not merely unproved (`RBM.t249_witness_norm_gt`).  Same deviation as
   `T249a`; no statement of the paper is altered.

Nothing else here departs from the paper: §§7–9 reprove existing repository statements verbatim
with one hypothesis weakened, and the constants are T263's (`T263a`), T268's (`T268a`, `T268b`)
and T269's (`T269a`, `T269b`).
-/
