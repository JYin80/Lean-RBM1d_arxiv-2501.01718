/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.EarlyQVRate
import RBM1D.Gauss.Step2Bootstrap
import RBM1D.Gauss.StepSideAPrime
import RBM1D.Flow.FirstCell

/-!
# T269: propagation of the a priori bound, and the two deterministic rate envelopes

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2–§5.3, (5.36), (5.42), (5.46), Lemma 5.7.

This file supplies the three items that `docs/reports/V548-referee.md` §2c/§5 leaves between
the weight support and the one-step arithmetic.  Everything here is **pointwise in `ω`** and
every size statement is guarded by the two events `supp W` (the weight does not vanish) and
`Good` (the modulus event); there is no `∀ ω` size hypothesis anywhere.

## (a) Propagation of the a priori bound from the net to the whole window

`RBM.Step2Bootstrap.abs_le_two_mul_of_softW_ne_zero` says: where the soft-max weight
`softW r S ρ Θ'` does not vanish, **every** member of the family obeys `|ρ i| ≤ 2Θ'`, with no
cardinality loss.  Taking the family to be indexed by the net of (5.46) and `ρ` to be the
functional itself, this is an a priori bound at every net point.  The time modulus then
carries it to every `v` in the window, through `RBM.MomentDuhamelCut.hclose_of_modulus`:

* `RBM.APrimePrior.le_of_softW_ne_zero_of_modulus` — the raw form, `Y v ≤ 2Θ' + Θ`;
* `RBM.APrimePrior.le_cWt_mul_priorLevel` — calibrated: with the widened weight of the
  referee's patch 2, `Θ' = 2·e·Λ_N` and `Λ_N = N^{2δ}Θ_N`, the conclusion is
  `Y v ≤ cWt·Λ_N` with `cWt = 4e + 2` — exactly the level `Jv ≤ cWt·x^{16}R^4` that
  `RBM.StepSideAPrime.StepSide''` consumes (`x = N^{δ/8}`, `Θ_N = R^4`);
* `RBM.APrimePrior.eventually_le_cWt_mul_priorLevel` — the same read off a
  `RBM.MomentDuhamelCut.CutHypEvOn` bundle, i.e. with the modulus taken **only on `Good N`**.

Which of the two available moduli is used is the caller's choice; the statement takes the
modulus as a hypothesis in the exact shape both of them produce.  See the module note below.

## (b), (c) The two deterministic envelopes

`RBM.APrimePrior.qvShape` is the right-hand side of `RBM.EarlyQVRate.quadVar_lkFun_le_ee_sym`
— (5.36) at `t = u`, `a = a' = b`, with the **sharp** far field of (5.71)/(5.72) — written as
a function of the running level `J*`, with the near-field indicator dropped.  It is monotone
in `J*` (`qvShape_mono`), so substituting the a priori bound of (a) produces a `J*`-free
envelope `RBM.APrimePrior.qvBd`.  The two normalizations of §2c then give

* `RBM.APrimePrior.kappaBd` — `κ̂^{bd}`, the early-time rate normalized by `(T_{u_j,D}(b)·Λ_j)²`;
* `RBM.APrimePrior.QBd` — `Q^{bd}_u`, the current-time rate normalized by `(T_{t,D}(a)·R^4)²`.

Both are *explicit closed-form functions* of `(W, ℓ_u, ℓ_s, η_u, D, Λ, S_max, ρ, L, T)` — no
`∃ C`, no dependence on the estimated quantity, and finite (`qvBd_nonneg`,
`kappaBd_eq`, `QBd_eq`).

**On the referee's `W^{-1}`.**  §2c.4/§6 (S3) of the report state the sharp far field with an
extra `W^{-1}`.  That is a slip: (5.71)/(5.72) bound the `b`-sum, and (5.22) puts a factor `W`
in front of it, which cancels it.  T262 checked this against p. 62–63 and the repository's
`RBM.Lemma57.ee_le` already has the correct form; nothing here chases a `W^{-1}`.  The real
sharpening is `(J*)²` in place of the `(J*)³` of the *statement* (5.36), and it is visible in
`qvShape` as the `(2J)²` coefficient of `cFar2`.

Nothing here is an `axiom` and nothing is `sorry`.
-/

namespace RBM

namespace APrimePrior

open Real Finset Filter MeasureTheory
open Step2Bootstrap MomentDuhamelCut StepSideAPrime
open scoped Matrix.Norms.L2Operator

/-! ### 1. The a priori level and the widened cut level -/

/-- The a priori level `Λ_N = N^{2δ}·Θ_N` of `prefNet` (`RBM.Step2Bootstrap.prefNet`): the
level the weight of route (A′) is calibrated at. -/
noncomputable def priorLevel (δ : ℝ) (Θ : ℕ → ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (2 * δ) * Θ N

/-- The cut level inside the **widened** weight of the referee's patch 2,
`W_p = χ(J̃/(2Θ′))^{2p}` with `Θ′ = e·Λ_N`: so the level is `2Θ′ = 2e·Λ_N`, and the support
statement gives `4e·Λ_N`. -/
noncomputable def priorThr (δ : ℝ) (Θ : ℕ → ℝ) (N : ℕ) : ℝ := 2 * (exp 1 * priorLevel δ Θ N)

theorem priorLevel_pos {δ : ℝ} {Θ : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) (hΘ : 0 < Θ N) :
    0 < priorLevel δ Θ N := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hN0 _
  unfold priorLevel; positivity

theorem priorThr_pos {δ : ℝ} {Θ : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) (hΘ : 0 < Θ N) :
    0 < priorThr δ Θ N := by
  have := priorLevel_pos (δ := δ) (Θ := Θ) (N := N) hN hΘ
  have he : (0 : ℝ) < exp 1 := exp_pos 1
  unfold priorThr; positivity

/-- `Θ_N ≤ Λ_N` as soon as `1 ≤ N` and `0 ≤ δ`: the level is at least the threshold. -/
theorem le_priorLevel {δ : ℝ} {Θ : ℕ → ℝ} {N : ℕ} (hδ : 0 ≤ δ) (hN : 1 ≤ N) (hΘ : 0 ≤ Θ N) :
    Θ N ≤ priorLevel δ Θ N := by
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
  unfold priorLevel; nlinarith

/-! ### 2. (a) — from the support of the weight to the whole window -/

section Propagation

variable {ι : Type*}

/-- **The a priori bound propagates from the net to every time of the window.**

Two inputs, both event-restricted by construction: the weight is non-zero at this `ω`
(`hne` — this is the event `supp W`), and the modulus holds at this `ω` (`hmod` — this is the
event `Good`, once the caller reads it off `CutHypEvOn.modulus`).  `hidx` says only that each
net point's value is dominated by some member of the family the weight is built from; when the
family *is* the net (the case below) it is `le_abs_self`.

No cardinality factor enters: `RBM.Step2Bootstrap.abs_le_two_mul_of_softW_ne_zero` bounds
*every* member, not their soft maximum. -/
theorem le_of_softW_ne_zero_of_modulus {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} {ρ : ι → ℝ}
    {Θ' : ℝ} (hΘ' : 0 < Θ') (hne : softW r S ρ Θ' ≠ 0)
    {s t mesh : ℕ → ℝ} {Kmod γ Θ : ℝ} (hγ : 0 < γ) {N : ℕ} (hmesh : 0 < mesh N)
    {Y : ℝ → ℝ}
    (hmod : ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      |Y v - Y w| ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ)
    (hfine : (N : ℝ) ^ Kmod * (1 / mesh N) ^ γ ≤ Θ)
    (hidx : ∀ ws ∈ netFinset s t mesh N, ∃ i ∈ S, Y ws ≤ |ρ i|) :
    ∀ v ∈ Set.Icc (s N) (t N), Y v ≤ 2 * Θ' + Θ := by
  intro v hv
  obtain ⟨ws, hwsF, _, hle⟩ :=
    hclose_of_modulus (s := s) (t := t) (mesh := mesh) (Θ := Θ) hγ hmesh hmod hfine v hv
  obtain ⟨i, hiS, hi⟩ := hidx ws (Finset.mem_coe.1 hwsF)
  have hbd : |ρ i| ≤ 2 * Θ' := abs_le_two_mul_of_softW_ne_zero hr hΘ' hne hiS
  linarith

/-- The same with the family **indexed by the net itself**, `ρ = Y`: this is the shape route
(A′) actually uses, and `hidx` disappears. -/
theorem le_of_softW_ne_zero_of_modulus_self {r : ℕ} (hr : 1 ≤ r)
    {Θ' : ℝ} (hΘ' : 0 < Θ') {s t mesh : ℕ → ℝ} {Kmod γ Θ : ℝ} (hγ : 0 < γ) {N : ℕ}
    (hmesh : 0 < mesh N) {Y : ℝ → ℝ}
    (hne : softW r (netFinset s t mesh N) Y Θ' ≠ 0)
    (hmod : ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      |Y v - Y w| ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ)
    (hfine : (N : ℝ) ^ Kmod * (1 / mesh N) ^ γ ≤ Θ) :
    ∀ v ∈ Set.Icc (s N) (t N), Y v ≤ 2 * Θ' + Θ :=
  le_of_softW_ne_zero_of_modulus hr hΘ' hne hγ hmesh hmod hfine
    (fun ws hws => ⟨ws, hws, le_abs_self _⟩)

/-- **⭐ (a), calibrated.**  With the widened weight at `2Θ′ = 2e·Λ_N` the propagated bound is

`Y v ≤ cWt · Λ_N`,  `cWt = 4e + 2`,  `Λ_N = N^{2δ}Θ_N`,

for **every** `v` in the window — which is `RBM.StepSideAPrime.StepSide''`'s field `Jv_le` at
`x = N^{δ/8}`, `Θ_N = R^4`.  The `4e` is the weight support, the `+1` is the modulus, and the
remaining `+1` is the genuine margin of `RBM.StepSideAPrime.prior_lt_level`. -/
theorem le_cWt_mul_priorLevel {r : ℕ} (hr : 1 ≤ r) {δ : ℝ} (hδ : 0 ≤ δ)
    {s t mesh Θ : ℕ → ℝ} {Kmod γ : ℝ} (hγ : 0 < γ) {N : ℕ} (hN : 1 ≤ N)
    (hΘ : 0 < Θ N) (hmesh : 0 < mesh N) {Y : ℝ → ℝ}
    (hne : softW r (netFinset s t mesh N) Y (priorThr δ Θ N) ≠ 0)
    (hmod : ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      |Y v - Y w| ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ)
    (hfine : (N : ℝ) ^ Kmod * (1 / mesh N) ^ γ ≤ Θ N) :
    ∀ v ∈ Set.Icc (s N) (t N), Y v ≤ cWt * priorLevel δ Θ N := by
  intro v hv
  have hraw := le_of_softW_ne_zero_of_modulus_self hr (priorThr_pos (δ := δ) (Θ := Θ) hN hΘ)
    hγ hmesh hne hmod hfine v hv
  have hΛ : Θ N ≤ priorLevel δ Θ N := le_priorLevel hδ hN hΘ.le
  have hstep : 2 * priorThr δ Θ N + Θ N ≤ cWt * priorLevel δ Θ N := by
    unfold priorThr cWt
    nlinarith [hΛ, priorLevel_pos (δ := δ) (Θ := Θ) (N := N) hN hΘ]
  linarith

end Propagation

/-! ### 2b. (a) read off a `CutHypEvOn` bundle -/

section OnEvent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **⭐ (a) on the event.**  The same propagation with the modulus taken from a
`RBM.MomentDuhamelCut.CutHypEvOn` bundle, so that it is asserted **only on `Good N`** — the
two available moduli, `RBM.abs_jSfarSm_sub_le_lip` (`γ = 1`, needs `0 < s`) and
`RBM.abs_jSfarSm_sub_le_event` (`γ = 1/2`, allows `v = w = 0`), both land in a bundle of this
shape, and `RBM.cutHypEvOn_jSfarSm_event` is the packaged instance of the second.

The conclusion is a size bound guarded by *both* events: `ω ∈ Good N` and `softW ≠ 0`. -/
theorem eventually_le_cWt_mul_priorLevel {J : ℕ → ℝ → Ω → ℝ} {s t Θ : ℕ → ℝ}
    {Good : ℕ → Set Ω} (H : CutHypEvOn P J s t Θ Good) {r : ℕ} (hr : 1 ≤ r) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Good N,
      softW r (netFinset s t H.mesh N) (fun ws => J N ws ω) (priorThr δ Θ N) ≠ 0 →
      ∀ v ∈ Set.Icc (s N) (t N), J N v ω ≤ cWt * priorLevel δ Θ N := by
  filter_upwards [H.modulus, H.mesh_fine, eventually_ge_atTop 1] with N hmod hfine hN1 ω hω hne
  exact le_cWt_mul_priorLevel hr hδ H.γ_pos hN1 (H.Θ_pos N) (H.mesh_pos N) hne
    (hmod ω hω) hfine

end OnEvent

/-! ### 3. The deterministic envelopes: the (5.36)/(5.42) shape and its two normalizations -/

section Envelopes

/-- **The (5.36)-at-`t = u` shape, as a function of the running level `Jst`.**

This is the right-hand side of `RBM.EarlyQVRate.quadVar_lkFun_le_ee_sym` with the near-field
indicator replaced by `1`.  The far field is the sharp one of (5.71)+(5.72) *times the factor
`W` of (5.22)*: `(Jst)²` against `cFar2`, `(Jst)³` against `72 A_u^{-1}`, and **no** `W^{-1}`
(see the module docstring). -/
noncomputable def qvShape (Wr ℓu ℓs ηu D Jst Smax ρfar Lr Tval : ℝ) : ℝ :=
  2 * (ηu⁻¹ * (Lemma57.cNear2 Wr ℓu * (ℓu / ℓs) ^ 5
          + Lemma57.cFar2 Wr ℓu * ((2 * Jst) ^ 2 * (Wr * ℓu * ηu * (2 * Real.sqrt Smax)))
          + 72 * (2 * Jst) ^ 3 * (Wr * ℓu * ηu)⁻¹) * Tval ^ 2
      + (Wr * Lr * ρfar + 2 * Wr * Lr * Wr ^ (-D) * (2 * Jst) ^ 3 * Tval ^ 2))

/-- **The shape is monotone in the running level.**  This is what makes "substitute the a
priori bound" legitimate. -/
theorem qvShape_mono {Wr ℓu ℓs ηu D Smax ρfar Lr Tval : ℝ} {Jst Jst' : ℝ}
    (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hLr : 0 ≤ Lr)
    (hJ0 : 0 ≤ Jst) (hJ : Jst ≤ Jst') :
    qvShape Wr ℓu ℓs ηu D Jst Smax ρfar Lr Tval
      ≤ qvShape Wr ℓu ℓs ηu D Jst' Smax ρfar Lr Tval := by
  have hW0 : (0 : ℝ) < Wr := by linarith
  have hcN : 0 ≤ Lemma57.cNear2 Wr ℓu := Lemma57.cNear2_nonneg hW hℓu
  have hcF : 0 ≤ Lemma57.cFar2 Wr ℓu := Lemma57.cFar2_nonneg hW hℓu
  have hWD : (0 : ℝ) < Wr ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hS : 0 ≤ Real.sqrt Smax := Real.sqrt_nonneg _
  have hA : (0 : ℝ) < Wr * ℓu * ηu := by positivity
  have h2 : (0 : ℝ) ≤ 2 * Jst := by linarith
  unfold qvShape
  gcongr

/-- **`Q^{bd}`/`κ̂^{bd}` before normalization**: `qvShape` with the a priori level `cWt·Λ` of
(a) substituted for the running level.  Explicit, finite, and independent of `ω`. -/
noncomputable def qvBd (Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval : ℝ) : ℝ :=
  qvShape Wr ℓu ℓs ηu D (cWt * Λ) Smax ρfar Lr Tval

/-- **⭐ Substituting (a) into the (5.36)/(5.42) bound.**  Any quantity dominated by the shape
at the running level is dominated by the `J*`-free envelope. -/
theorem le_qvBd_of_le_qvShape {Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Jst Qval : ℝ}
    (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hLr : 0 ≤ Lr)
    (hJ0 : 0 ≤ Jst) (hJ : Jst ≤ cWt * Λ)
    (hQ : Qval ≤ qvShape Wr ℓu ℓs ηu D Jst Smax ρfar Lr Tval) :
    Qval ≤ qvBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval :=
  hQ.trans (qvShape_mono hW hℓu hηu hLr hJ0 hJ)

/-- **⭐ `κ̂^{bd}`, in closed form.**  The early-time rate of §2c, normalized by
`(T_{u_j,D}(b)·Λ_j)²`.  Read off `qvBd`/`(T·Λ)²` (see `kappaBd_eq_div`):

* the near field decays like `Λ^{-2}` — this is the `N^{-4δ}η_s^{-1}` of §2c.4;
* the two far-field terms are `O(1)` and `O(Λ)` — the `(J*)²`/`(J*)³` of (5.71)/(5.72);
* the `W^{-D}` tail is `O(Λ)` and the `ρ` tail is `O(Λ^{-2}T^{-2})`.

No `∃ C`, no `ω`, and nothing on the right depends on the quantity being estimated. -/
noncomputable def kappaBd (Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval : ℝ) : ℝ :=
  2 * (ηu⁻¹ * (Lemma57.cNear2 Wr ℓu * (ℓu / ℓs) ^ 5 / Λ ^ 2
          + Lemma57.cFar2 Wr ℓu
              * (4 * cWt ^ 2 * (Wr * ℓu * ηu * (2 * Real.sqrt Smax)))
          + 576 * cWt ^ 3 * Λ * (Wr * ℓu * ηu)⁻¹)
      + (Wr * Lr * ρfar / (Tval ^ 2 * Λ ^ 2)
          + 16 * Wr * Lr * Wr ^ (-D) * cWt ^ 3 * Λ))

/-- The envelope is finite and non-negative — in particular it is not `∞`, and nothing on
the right depends on the quantity being estimated. -/
theorem qvShape_nonneg {Wr ℓu ℓs ηu D Jst Smax ρfar Lr Tval : ℝ}
    (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hLr : 0 ≤ Lr)
    (hρ : 0 ≤ ρfar) (hJ0 : 0 ≤ Jst) :
    0 ≤ qvShape Wr ℓu ℓs ηu D Jst Smax ρfar Lr Tval := by
  have hW0 : (0 : ℝ) < Wr := by linarith
  have hcN : 0 ≤ Lemma57.cNear2 Wr ℓu := Lemma57.cNear2_nonneg hW hℓu
  have hcF : 0 ≤ Lemma57.cFar2 Wr ℓu := Lemma57.cFar2_nonneg hW hℓu
  have hWD : (0 : ℝ) < Wr ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hS : 0 ≤ Real.sqrt Smax := Real.sqrt_nonneg _
  have h2J : (0 : ℝ) ≤ 2 * Jst := by linarith
  have a1 : (0 : ℝ) ≤ Lemma57.cNear2 Wr ℓu * (ℓu / ℓs) ^ 5 := by positivity
  have a2 : (0 : ℝ) ≤ Lemma57.cFar2 Wr ℓu
      * ((2 * Jst) ^ 2 * (Wr * ℓu * ηu * (2 * Real.sqrt Smax))) :=
    mul_nonneg hcF (mul_nonneg (pow_nonneg h2J 2) (by positivity))
  have a3 : (0 : ℝ) ≤ 72 * (2 * Jst) ^ 3 * (Wr * ℓu * ηu)⁻¹ :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h2J 3)) (by positivity)
  have e1 : (0 : ℝ) ≤ ηu⁻¹ := by positivity
  have e3 : (0 : ℝ) ≤ Tval ^ 2 := sq_nonneg _
  have eX : (0 : ℝ) ≤ ηu⁻¹ * (Lemma57.cNear2 Wr ℓu * (ℓu / ℓs) ^ 5
        + Lemma57.cFar2 Wr ℓu * ((2 * Jst) ^ 2 * (Wr * ℓu * ηu * (2 * Real.sqrt Smax)))
        + 72 * (2 * Jst) ^ 3 * (Wr * ℓu * ηu)⁻¹) * Tval ^ 2 :=
    mul_nonneg (mul_nonneg e1 (by linarith)) e3
  have eY : (0 : ℝ) ≤ Wr * Lr * ρfar := by positivity
  have eZ : (0 : ℝ) ≤ 2 * Wr * Lr * Wr ^ (-D) * (2 * Jst) ^ 3 * Tval ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg h2J 3)) (sq_nonneg _)
  unfold qvShape
  linarith

theorem qvBd_nonneg {Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval : ℝ}
    (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hLr : 0 ≤ Lr)
    (hρ : 0 ≤ ρfar) (hΛ : 0 ≤ Λ) :
    0 ≤ qvBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval :=
  qvShape_nonneg hW hℓu hℓs hηu hLr hρ (mul_nonneg cWt_pos.le hΛ)

/-- `κ̂^{bd}` **is** `qvBd/(T·Λ)²`: the closed form above is the normalization, not a new
estimate. -/
theorem kappaBd_eq_div {Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval : ℝ}
    (hT : Tval ≠ 0) (hΛ : Λ ≠ 0) :
    kappaBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval
      = qvBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval / (Tval * Λ) ^ 2 := by
  unfold kappaBd qvBd qvShape
  field_simp
  ring

/-- **⭐ `Q^{bd}`, in closed form.**  The current-time rate of §2c, normalized by
`(T_{t,D}(a)·R^4)²`: the same envelope with the endpoint normalization of `Ψ_u`.  `Tt` is
`T_{t,D}(|a₁−a₂|)` and `Rn` is `R = η_s/η_t`. -/
noncomputable def QBd (Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn : ℝ) : ℝ :=
  2 * (ηu⁻¹ * (Lemma57.cNear2 Wr ℓu * (ℓu / ℓs) ^ 5
          + Lemma57.cFar2 Wr ℓu
              * (4 * cWt ^ 2 * Λ ^ 2 * (Wr * ℓu * ηu * (2 * Real.sqrt Smax)))
          + 576 * cWt ^ 3 * Λ ^ 3 * (Wr * ℓu * ηu)⁻¹) * Tval ^ 2
      + (Wr * Lr * ρfar
          + 16 * Wr * Lr * Wr ^ (-D) * cWt ^ 3 * Λ ^ 3 * Tval ^ 2)) / (Tt * Rn ^ 4) ^ 2

/-- `Q^{bd}` **is** `qvBd/(T_t·R^4)²`. -/
theorem QBd_eq_div {Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn : ℝ} :
    QBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn
      = qvBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval / (Tt * Rn ^ 4) ^ 2 := by
  unfold QBd qvBd qvShape
  ring_nf

/-- The normalization identity in product form: `(T·Λ)²·κ̂^{bd} = qvBd`. -/
theorem mul_kappaBd_eq {Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval : ℝ} (hT : Tval ≠ 0) (hΛ : Λ ≠ 0) :
    (Tval * Λ) ^ 2 * kappaBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval
      = qvBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval := by
  rw [kappaBd_eq_div hT hΛ]
  field_simp

/-- **(c), normalized.**  Anything dominated by `qvBd` is dominated by `(T·Λ)²·κ̂^{bd}`. -/
theorem le_kappaBd_of_le_qvBd {Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Qval : ℝ}
    (hT : Tval ≠ 0) (hΛ : Λ ≠ 0)
    (h : Qval ≤ qvBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval) :
    Qval ≤ (Tval * Λ) ^ 2 * kappaBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval := by
  rw [mul_kappaBd_eq hT hΛ]; exact h

/-- **(b).**  A current-time quadratic-variation rate dominated by the (5.42) shape at the
running level is, after the endpoint normalization, dominated by the explicit `Q^{bd}`. -/
theorem div_le_QBd_of_le_qvShape {Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn Jst Qval : ℝ}
    (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hLr : 0 ≤ Lr)
    (hJ0 : 0 ≤ Jst) (hJ : Jst ≤ cWt * Λ) (hnorm : 0 < (Tt * Rn ^ 4) ^ 2)
    (hQ : Qval ≤ qvShape Wr ℓu ℓs ηu D Jst Smax ρfar Lr Tval) :
    Qval / (Tt * Rn ^ 4) ^ 2 ≤ QBd Wr ℓu ℓs ηu D Λ Smax ρfar Lr Tval Tt Rn := by
  rw [QBd_eq_div]
  have h := le_qvBd_of_le_qvShape (Λ := Λ) hW hℓu hηu hLr hJ0 hJ hQ
  gcongr

end Envelopes

/-! ### 4. The bridge: T262's (5.36)-at-`t = u` lands in the shape, and (a) closes it -/

section Bridge

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **T262 in the `qvShape` normal form.**  `RBM.EarlyQVRate.quadVar_lkFun_le_ee_sym` with the
near-field indicator relaxed to `1`.  Nothing is quantified over `ω`: the three Step-1 inputs
`h273`, `h564`, `h42sq` and the structural witnesses `Gm`, `Gsq`, `Smax` are supplied at the
single sample point at hand, which is where the caller has the event `Good`. -/
theorem quadVar_lkFun_le_qvShape (X : Sample B) {E : ℝ} (hE : |E| < 2) {N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (a : LoopArg (B.L N) (0 + 2))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hW : 1 ≤ (B.W N : ℝ))
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax ρ : ℝ} (hρ : 0 ≤ ρ)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax)
    (h273 : ∀ b, EEDef.eeL6 X E N u ω σ (Fin.append a a) b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
      < (zdist (B.L N) (a 0 - b) : ℝ) → EEDef.eeL6 X E N u ω σ (Fin.append a a) b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) :
    Gauss.quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) (X.H N u ω)
      ≤ qvShape (B.W N : ℝ) ℓu ℓs ηu D J Smax ρ (B.L N : ℝ)
          (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1))) := by
  refine (EarlyQVRate.quadVar_lkFun_le_ee_sym X hE hu0 hu1 ω σ a hℓu hℓs hηu hJ hρ hGm0 hGm
    hGsq0 hGsq2 hrow hSmax h273 h564 h42sq).trans ?_
  have hcN : 0 ≤ Lemma57.cNear2 (B.W N : ℝ) ℓu :=
    Lemma57.cNear2_nonneg hW (by linarith)
  have hr5 : (0 : ℝ) ≤ (ℓu / ℓs) ^ 5 := by positivity
  have hind : Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
      (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu then 1 else 0)
      ≤ Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 := by
    split_ifs with h
    · simp
    · rw [mul_zero]; positivity
  unfold qvShape
  gcongr

/-- **⭐ (c).**  (a) substituted into T262: the early-time quadratic-variation rate has the
explicit, `ω`-free envelope `qvBd` — and hence, normalized by `(T·Λ)²`, the rate `κ̂^{bd}`.

`hJle` is exactly the conclusion of `RBM.APrimePrior.le_cWt_mul_priorLevel`, i.e. it holds on
`supp W ∩ Good` and nowhere is it asserted for all `ω`. -/
theorem quadVar_lkFun_le_qvBd (X : Sample B) {E : ℝ} (hE : |E| < 2) {N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (a : LoopArg (B.L N) (0 + 2))
    {ℓu ℓs ηu D J Λ : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hJle : J ≤ cWt * Λ) (hW : 1 ≤ (B.W N : ℝ)) (hL : (0 : ℝ) ≤ (B.L N : ℝ))
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax ρ : ℝ} (hρ : 0 ≤ ρ)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax)
    (h273 : ∀ b, EEDef.eeL6 X E N u ω σ (Fin.append a a) b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
      < (zdist (B.L N) (a 0 - b) : ℝ) → EEDef.eeL6 X E N u ω σ (Fin.append a a) b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) :
    Gauss.quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) (X.H N u ω)
      ≤ qvBd (B.W N : ℝ) ℓu ℓs ηu D Λ Smax ρ (B.L N : ℝ)
          (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1))) :=
  le_qvBd_of_le_qvShape hW (by linarith) hηu hL (by linarith) hJle
    (quadVar_lkFun_le_qvShape X hE hu0 hu1 ω σ a hℓu hℓs hηu hJ hW hρ hGm0 hGm hGsq0 hGsq2
      hrow hSmax h273 h564 h42sq)

end Bridge

/-! ### 5. Satisfiability

Three things have to be checked, in the order the discipline of `CLAUDE.md` lists them.

1. **The envelopes are not `∞` and do not depend on the estimated quantity**:
   `qvShape_nonneg`, `qvBd_nonneg`, and the closed forms `kappaBd`, `QBd` themselves, whose
   arguments are `(W, ℓ_u, ℓ_s, η_u, D, Λ, S_max, ρ, L, T)` and nothing else.
2. **`supp W` does not degenerate to the empty set**:
   `RBM.APrimePrior.softW_ne_zero_at` exhibits a positive threshold at which the weight is
   `1` at *any* sample point, and `softW_priorThr_ne_zero` shows the *calibrated* threshold
   `2Θ′ = 2e·Λ_N` is already reached as soon as the net values obey the a priori level — so
   `RBM.Step2Bootstrap.softW_eq_zero` notwithstanding, the support is a genuine event.
3. **`supp W ∩ Good ≠ ∅` at a concrete model**:
   `sat_supp_inter_good_nonempty_exampleGrow`, at `d = exampleGrow` and the sample point
   `ω = 0`, which lies in the event `{‖X_N‖ ≤ N}` of `RBM.cutHypEvOn_jSfarSm_event`.
   `sat_propagation_exampleGrow` then runs (a) end to end on that model, on the cell
   `[0, 1/2]` the grid of p. 24 starts with — **left endpoint `0`**, so the modulus used is
   T257/T266's event route (`γ = 1/2`), not T257's `‖X‖`-free route (`γ = 1`, which needs
   `0 < s`). -/

section Sat

variable {ι : Type*}

/-- **The weight is `1` at an explicit positive threshold, at every sample point.**  So the
support of the weight is never empty for trivial reasons. -/
theorem softW_ne_zero_at (r : ℕ) (S : Finset ι) (ρ : ι → ℝ) :
    softW r S ρ (softMax r S ρ + 1) ≠ 0 := by
  have hm := softMax_nonneg r S ρ
  have hpos : (0 : ℝ) < softMax r S ρ + 1 := by linarith
  have hle : softMax r S ρ / (softMax r S ρ + 1) ≤ 1 := (div_le_one hpos).2 (by linarith)
  rw [softW, Cutoff.cutChi_eq_one hle]
  norm_num

/-- The calibration `card^{1/q} ≤ 2e` of `priorThr` is the one of
`RBM.Step2Bootstrap.rpow_card_le_exp_one`, with room to spare. -/
theorem card_calib_two_exp {A c q : ℝ} (hc0 : 0 < c) {N : ℕ} (hN : 2 ≤ N)
    (hcard : c ≤ (N : ℝ) ^ A) (hA : 0 < A) (hq : A * Real.log N ≤ q) :
    c ^ ((1 : ℝ) / q) ≤ 2 * exp 1 := by
  have h1 := rpow_card_le_exp_one hc0 hN hcard hA hq
  have h2 : (0 : ℝ) < exp 1 := exp_pos 1
  linarith

/-- **The calibrated support is reached.**  If every member of the family obeys the a priori
level `Λ_N`, the widened weight at `2Θ′ = 2e·Λ_N` equals `1`; so the hypothesis `softW ≠ 0`
of (a) is not vacuous. -/
theorem softW_priorThr_ne_zero {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} {ρ : ι → ℝ} {δ : ℝ}
    {Θ : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) (hΘ : 0 < Θ N)
    (hcard : ((S.card : ℝ)) ^ ((1 : ℝ) / (2 * (r : ℝ))) ≤ 2 * exp 1)
    (h : ∀ i ∈ S, |ρ i| ≤ priorLevel δ Θ N) :
    softW r S ρ (priorThr δ Θ N) ≠ 0 := by
  have hΛ := priorLevel_pos (δ := δ) (Θ := Θ) (N := N) hN hΘ
  have he : (0 : ℝ) < 2 * exp 1 := by have := exp_pos 1; linarith
  have hkey := one_le_softW hr hΛ he hcard h
  have heq : priorThr δ Θ N = 2 * exp 1 * priorLevel δ Θ N := by unfold priorThr; ring
  rw [heq]
  linarith

/-- **`supp W ∩ Good ≠ ∅` at `RBM.Gauss.Dims.exampleGrow`.**  The sample point `ω = 0` lies in
the modulus event `{‖X_N‖ ≤ N}` of `RBM.cutHypEvOn_jSfarSm_event` (`RBM.Gauss.Xmat_zero`), and
the weight built on the net of that bundle is `1` there at an explicit positive threshold. -/
theorem sat_supp_inter_good_nonempty_exampleGrow (N r : ℕ) (mesh : ℕ → ℝ) :
    ∃ ω : Gauss.Ω Gauss.Dims.exampleGrow,
      ω ∈ {ω : Gauss.Ω Gauss.Dims.exampleGrow |
          ‖Gauss.Xmat Gauss.Dims.exampleGrow N ω‖ ≤ (N : ℝ)} ∧
        ∃ Θ' : ℝ, 0 < Θ' ∧
          softW r (netFinset (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) mesh N)
            (fun ws => Step2FarMart.jSfarSm (Gauss.sample Gauss.Dims.exampleGrow) 0 1 N ws ω)
            Θ' ≠ 0 := by
  classical
  set S := netFinset (fun _ : ℕ => (0 : ℝ)) (fun _ : ℕ => (1 / 2 : ℝ)) mesh N with hS
  set ρ : ℝ → ℝ := fun ws =>
    Step2FarMart.jSfarSm (Gauss.sample Gauss.Dims.exampleGrow) 0 1 N ws 0 with hρ
  refine ⟨0, ?_, softMax r S ρ + 1, ?_, softW_ne_zero_at r S ρ⟩
  · have hx : Gauss.Xmat Gauss.Dims.exampleGrow N (0 : Gauss.Ω Gauss.Dims.exampleGrow) = 0 := by
      ext i j
      simp [Gauss.Xmat, Gauss.Xentry]
    change ‖Gauss.Xmat Gauss.Dims.exampleGrow N (0 : Gauss.Ω Gauss.Dims.exampleGrow)‖ ≤ (N : ℝ)
    rw [hx, norm_zero]
    exact Nat.cast_nonneg N
  · have := softMax_nonneg r S ρ; linarith

/-- The propagated level is completely explicit: `cWt·Λ_N = (4e + 2)·N^{2δ}` at `Θ ≡ 1`. -/
theorem cWt_priorLevel_one (δ : ℝ) (N : ℕ) :
    cWt * priorLevel δ (fun _ => (1 : ℝ)) N = (4 * exp 1 + 2) * (N : ℝ) ^ (2 * δ) := by
  unfold priorLevel cWt; ring

/-- **⭐ (a) end to end on a compiled model.**  `d = exampleGrow`, `E = 0`, `D = 1`, the cell
`[0, 1/2]` of the grid of p. 24 (**left endpoint `0`**), `Θ ≡ 1`, `Kmod = 4`, `γ = 1/2`,
`mesh = RBM.meshK 4 (1/2) = (N+1)^8`.  On the event `{‖X_N‖ ≤ N}` (the `Good` of
`RBM.cutHypEvOn_jSfarSm_event`) intersected with the support of the widened weight, the
functional obeys the a priori level `(4e + 2)·N^{2δ}` at **every** time of the cell, not just
at the net points.

The modulus used is the event route `RBM.abs_jSfarSm_sub_le_event` (`γ = 1/2`), packaged as
`RBM.modulus_event_exampleGrow_zero`; T257's `‖X‖`-free route (`γ = 1`) is not usable here
because it needs `0 < s` and this cell starts at `0`. -/
theorem sat_propagation_exampleGrow {δ : ℝ} (hδ : 0 ≤ δ) {r : ℕ} (hr : 1 ≤ r) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ {ω : Gauss.Ω Gauss.Dims.exampleGrow |
          ‖Gauss.Xmat Gauss.Dims.exampleGrow N ω‖ ≤ (N : ℝ)},
        softW r (netFinset (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ))
            (meshK (2 + 2 * (1 : ℝ)) (1 / 2)) N)
          (fun ws => Step2FarMart.jSfarSm (Gauss.sample Gauss.Dims.exampleGrow) 0 1 N ws ω)
          (priorThr δ (fun _ => (1 : ℝ)) N) ≠ 0 →
        ∀ v ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ),
          Step2FarMart.jSfarSm (Gauss.sample Gauss.Dims.exampleGrow) 0 1 N v ω
            ≤ (4 * exp 1 + 2) * (N : ℝ) ^ (2 * δ) := by
  have hfine := (sat_mesh_pair_event (D := 1) (s := fun _ : ℕ => (0 : ℝ))
    (t := fun _ : ℕ => (1 / 2 : ℝ)) le_rfl (fun _ => le_rfl) (fun _ => by norm_num)).2.1
  filter_upwards [modulus_event_exampleGrow_zero, hfine, eventually_ge_atTop 1]
    with N hmod hfineN hN1 ω hω hne v hv
  have := le_cWt_mul_priorLevel (r := r) (δ := δ) (s := fun _ : ℕ => (0 : ℝ))
    (t := fun _ : ℕ => (1 / 2 : ℝ)) (mesh := meshK (2 + 2 * (1 : ℝ)) (1 / 2))
    (Θ := fun _ : ℕ => (1 : ℝ)) (Kmod := 2 + 2 * (1 : ℝ)) (γ := (1 : ℝ) / 2) hr hδ
    (by norm_num) hN1 (by norm_num) (meshK_pos _ _ N) hne (hmod ω hω) hfineN v hv
  rwa [cWt_priorLevel_one] at this

end Sat

/-! ### Deviations

**T269a** (not a deviation from the paper; a correction to `docs/reports/V548-referee.md`).
§2c.4, §2c.6 and §6 (S3) of that report write the sharp far field of (5.36)-at-`t = u` with an
extra factor `W^{-1}`.  T262 already recorded (as `T262a`) that this is a slip — (5.71)/(5.72)
bound the `b`-sum and (5.22) carries a factor `W` in front of it, which cancels it — and this
file follows T262: `qvShape` has no `W^{-1}`, and the sharpening relative to the *statement*
(5.36) is `(J*)²` in place of `(J*)³`.  Consequences for the arithmetic: none, because
`RBM.StepSideAPrime.StepSide''`'s far-field slots `β`, `γ` are fed by
`RBM.Lemma57.ee_le`'s coefficients, not by the report's.  0 lines of the paper affected.

**T269b** (a deviation of the formalization from the report, not from the paper).  §5 step 2
of the report writes the propagated a priori bound as `∀ v ∈ [s,t] : J*_v ≤ c₀Λ_v` with a
*time-dependent* level `Λ_v = N^{2δ}(η_s/η_v)^4`.  `RBM.MomentDuhamelCut.CutHypEvOn` carries a
single level `Θ : ℕ → ℝ` per `N`, so `RBM.APrimePrior.le_cWt_mul_priorLevel` propagates to the
*constant* level `Λ_N = N^{2δ}Θ_N`, which at `Θ_N = R^4 = (η_{s_N}/η_{t_N})^4` is the value of
`Λ_v` at the right endpoint — the weakest point of the window, so the constant version implies
nothing the time-dependent one does not.  This is the same convention
`RBM.StepSideAPrime.StepSide''` already uses (`Jv ≤ cWt·x^{16}R^4`, one `R`), so no interface
changes.  Nothing in the paper is affected; the sharper time-dependent form, when it is
needed, is the same statement with `Θ` replaced by `v ↦ (η_s/η_v)^4` and the modulus asserted
against that level. -/

end APrimePrior

end RBM

