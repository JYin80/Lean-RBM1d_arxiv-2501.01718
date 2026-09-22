/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Q716
import RBM1D.Hierarchy.DriftDef
import RBM1D.Hierarchy.LKDecayQuant

/-!
# T220: the (7.13) premise of the five `momentDuhamelQ` terms, along the flow

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.5 (pp. 67–69), (7.13) and Lemma 7.3 (7.16).

T201 landed the five kernel estimates `RBM.Gauss.momNorm_Uker_Qop_le`,
`…_commS_le`, `…_PsumVarthetaDot_le`, `…_QQ_le` — (7.16) Case 2 in moment form, one for each
term of `RBM.MomentDuhamel.Hyp.momentDuhamelQ`.  In each of them the sum-zero premise (7.15)
is a *theorem*; the one premise left open is `hGd`, the **fast decay (7.13) of the projected
tensor**, which is the only premise that is a statement about the *model* rather than about
the kernel.  T214 recorded that this is why the five estimates still have no consumer.

This file produces `hGd`.

## The five tensors and where their decay comes from

| term of `momentDuhamelQ` | tensor in the `hGd` slot | decay from |
|---|---|---|
| datum (5.91) | `Q_{s_N} ∘ (L-K)_{s_N,σ}` | (5.75) `RBM.SumZeroDyn.LKDecay` + Lemma 5.13 |
| drift (5.91) | `Q_u ∘ F_u` | `RBM.DriftDef.fastDecay_driftF` + Lemma 5.13 |
| commutator (5.99) | `[Q_u,Θ_{u,σ}] ∘ (L-K)_u` | (5.96) Ward + `fastDecay_commS` (5.99) |
| `ϑ̇` term (5.100) | `(P ∘ (L-K)_u)_{b₀} ϑ̇_{u,b}` | (5.96) Ward + `fastDecay_varthetaDot` |
| `E ⊗ E` (5.103) | `(Q_u ⊗ Q_u) ∘ (E ⊗ E)_u` | `RBM.Decay.norm_eTens_le_of_far` + (5.104) |

**Correction to the T220 ticket's guess.**  The ticket expected all five to come from the
(2.75)/(2.76) decay and from (5.35)/(5.36).  Two of them do not, and the difference matters:

* terms 3 and 4 carry **no (7.13) hypothesis on the tensor at all**.  Their decay is
  `ϑ_u`'s and `ϑ̇_u`'s own — `RBM.SumZeroDyn.fastDecay_commS` and `fastDecay_varthetaDot` —
  and the only thing asked of `L - K` is the **Ward bound (5.96)** on its *slot sums*
  `P ∘ (L-K)`, i.e. `RBM.SumZeroDyn.norm_Psum_lkT_le`.  (5.75) still enters, but one loop
  length lower (`n+1`, inside Ward), not as (7.13) of the `(n+2)`-tensor;
* term 5 does **not** go through (5.35)/(5.36) either.  Its decay is Definition 5.8 of the
  flow's *`G`-loops of the glued length `2m+2`*, which is
  `RBM.LKDecayQuant.GLoopDecayEvent` (definitionally `RBM.EEBridge.eeDecayEvent`), produced
  with high probability by `RBM.LKDecayQuant.highProb_gLoopDecay_of_flowInputs`.  Getting
  from there to (7.13) of `E ⊗ E` needs the gluing of (5.23) to preserve labels, which is
  §5 below and is the only new mathematics in this file.

So terms 1 and 2 rest on (5.75) — which `RBM.LKDecayQuant.lkDecay_of_inputs` derives from
**(2.76)** — terms 3 and 4 on (5.96), and term 5 on the `G`-loop decay at the doubled
length.  The drift tensor itself needs *no* stochastic input beyond those:
`RBM.DriftDef.fastDecay_driftF` is a deterministic, pathwise theorem; its `hKd` slot (the
decay of `K` at loop length `n+2`) is a named input throughout the repository — the only
producer, `RBM.exists_loopDecay_Kval`, is at length `3`.

## The event discipline

(7.13) holds **with high probability**, never for every `ω`: at `ω` with `H = 0` the
resolvent is the constant `-z⁻¹`, `L - K` does not decay at the flow's radius, and a
pointwise-in-`ω` (7.13) is simply false.  The `hGd` slot, however, is quantified over all
`ω`.  The bridge is `RBM.FastDecayFlow.fastDecay_of_mem_of_zero`: the tensor fed to the
kernel estimate is the **indicator** `Set.indicator Ξ A`, which is `A ω` on the good event and
`0` off it, and every one of the four operators `Q_u`, `[Q_u,Θ]`, `(P·)ϑ̇`, `Q_u ⊗ Q_u`
annihilates `0`.  Off the event the estimate is then a statement about `0`, and the loss is
paid for by T201's `RBM.Gauss.momNorm_le_affine_on_event`
(`RBM.FastDecayFlow.Uker_indicator` identifies the two sides).

**Why this is not a way of making the slot vacuously satisfiable.**  Truncating to `Ξ` would
be worthless if `Ξ` could be empty — the `hGd` would then be a statement about the zero
tensor.  §8 therefore *produces* the event: `RBM.FastDecayFlow.highProb_lkGood` derives
`RBM.HighProb` of it from (5.75), and `RBM.FastDecayFlow.nonempty_lkGood` turns that into
`∀ᶠ N, (lkGood … N).Nonempty` — so the event is provably non-empty, not assumed so.  §11
adds the positive witness: a non-zero tensor for which every premise holds with `δ = 0` and
which `Q_u` fixes.

## Main results

* `RBM.FastDecayFlow.fastDecay_of_mem_of_zero`, `RBM.FastDecayFlow.Uker_indicator` — the
  event/`∀ ω` bridge (§1).
* `RBM.FastDecayFlow.Qop_zero`, `commS_zero`, `dotMap_zero`, `QQ_zero` — the four operators
  kill `0` (§2).
* `RBM.FastDecayFlow.hGd_Qop`, `hGd_commS`, `hGd_dot`, `hGd_QQ` — (7.13) in the exact shape
  of the `hGd` slot (`∀ ω`), for a tensor controlled only on `Ξ` (§4, §6).
* `RBM.FastDecayFlow.fastDecay_eeArg`, `fastDecay_eeFun` — (7.13) for `E ⊗ E` of
  Definition 5.4 from Definition 5.8 of the glued `G`-loops (§5, §7).
* `RBM.FastDecayFlow.nonempty_of_highProb`, `lkGood`, `highProb_lkGood`, `nonempty_lkGood`,
  `fastDecay_lkT_of_mem_lkGood`, `fastDecay_eeFun_of_mem_gLoopDecay` — the good events and
  their high probability (§8).
* `RBM.FastDecayFlow.hGd_Qop_lkT`, `hGd_Qop_driftF`, `hGd_commS_lkT`, `hGd_dot_lkT`,
  `hGd_QQ_eeFun` — the `hGd` slot at the **five tensors of `momentDuhamelQ` themselves** (§9).
* `RBM.FastDecayFlow.momNorm_Uker_Qop_event_le`, `…_commS_event_le`, `…_dot_event_le`,
  `…_QQ_event_le` — T201's five estimates with `hGd` **discharged by a theorem** (§10; terms
  1 and 2 of `momentDuhamelQ` share the first shape).
* `RBM.FastDecayFlow.hGd_witness` — the satisfiability witness (§11).
* `RBM.FastDecayFlow.momNorm_Uker_Qop_lkT_le` — the whole chain composed at the model, for
  term 1: no decay hypothesis is left in it (§12).

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM.FastDecayFlow

open Filter MeasureTheory Real
open RBM.SumZeroDyn

/-! ### §1  The event/`∀ ω` bridge

(7.13) is a high-probability statement; the `hGd` slot is `∀ ω`.  The tensor that enters the
kernel estimate is therefore the indicator of the good event, and what has to be checked is
that the operator in front of it kills `0`. -/

section Bridge

variable {Ω : Type*} {L : ℕ}

/-- **The bridge.**  If an operator `T` annihilates the zero tensor and `T (A ω)` is
`(R, δ)`-fast-decaying for every `ω` in the good event `Ξ`, then `T (1_Ξ A)` is
`(R, δ)`-fast-decaying for **every** `ω` — which is the shape of the `hGd` slot of T201's
kernel estimates.

This is the only legitimate way to feed a statement about the model into a slot quantified
over all sample points: the estimate off `Ξ` is a statement about `0`, and the loss is
accounted for by `RBM.Gauss.momNorm_le_affine_on_event`. -/
theorem fastDecay_of_mem_of_zero {m m' : ℕ} {R δ : ℝ} (hδ : 0 ≤ δ)
    {T : (LoopArg L m → ℂ) → LoopArg L m' → ℂ} (hT0 : T 0 = 0)
    {Ξ : Set Ω} {A : Ω → LoopArg L m → ℂ}
    (h : ∀ ω ∈ Ξ, FastDecay L R δ (T (A ω))) (ω : Ω) :
    FastDecay L R δ (T (Set.indicator Ξ A ω)) := by
  classical
  by_cases hω : ω ∈ Ξ
  · rw [Set.indicator_of_mem hω]; exact h ω hω
  · rw [Set.indicator_of_notMem hω, hT0]
    intro a _
    simpa using hδ

/-- The same for the size envelope of the `hGM` slot. -/
theorem norm_of_mem_of_zero {m m' : ℕ} {M : ℝ} (hM : 0 ≤ M)
    {T : (LoopArg L m → ℂ) → LoopArg L m' → ℂ} (hT0 : T 0 = 0)
    {Ξ : Set Ω} {A : Ω → LoopArg L m → ℂ}
    (h : ∀ ω ∈ Ξ, ∀ b, ‖T (A ω) b‖ ≤ M) (ω : Ω) (b : LoopArg L m') :
    ‖T (Set.indicator Ξ A ω) b‖ ≤ M := by
  classical
  by_cases hω : ω ∈ Ξ
  · rw [Set.indicator_of_mem hω]; exact h ω hω b
  · rw [Set.indicator_of_notMem hω, hT0]
    simpa using hM

variable [NeZero L]

/-- The evolution kernel kills the zero tensor (`RBM.Uker_smul` at `c = 0`). -/
theorem Uker_zero {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ) :
    Uker L ξ s t (0 : LoopArg L n → ℂ) = 0 := by
  have h := Uker_smul L ξ s t 0 (0 : LoopArg L n → ℂ)
  simpa using h

/-- **The identification used by `RBM.Gauss.momNorm_le_affine_on_event`**: applying the kernel
to the truncated tensor is the same as truncating the value.  So a bound on
`‖U ∘ (1_Ξ A)‖` *is* a bound on `1_Ξ ‖U ∘ A‖`, and the tail is the only thing left to pay
for. -/
theorem Uker_indicator {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ) {Ξ : Set Ω}
    (A : Ω → LoopArg L n → ℂ) (ω : Ω) (a : LoopArg L n) :
    Uker L ξ s t (Set.indicator Ξ A ω) a
      = Set.indicator Ξ (fun ω => Uker L ξ s t (A ω) a) ω := by
  classical
  by_cases hω : ω ∈ Ξ
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Uker_zero]
    rfl

end Bridge

/-! ### §2  The four operators annihilate `0`

`Q_t`, `[Q_t, Θ_{t,σ}]`, `A ↦ (P ∘ A)_{b₀} ϑ̇_{t,b}` and `Q_t ⊗ Q_t` are all linear, so this
is immediate; it is stated because `RBM.FastDecayFlow.fastDecay_of_mem_of_zero` needs it
literally. -/

section Zero

variable (L : ℕ) [NeZero L]

theorem Psum_zero {n : ℕ} (x : ZMod L) : Psum L (0 : LoopArg L (n + 1) → ℂ) x = 0 := by
  simp [Psum]

theorem Qop_zero {n : ℕ} (t : ℂ) : Qop L t (0 : LoopArg L (n + 1) → ℂ) = 0 := by
  funext b
  change (0 : LoopArg L (n + 1) → ℂ) b - Psum L (0 : LoopArg L (n + 1) → ℂ) (b 0)
      * vartheta L t b = 0
  rw [Psum_zero]
  simp

theorem genOp_zero {n : ℕ} (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ) :
    genOp L M (0 : LoopArg L n → ℂ) = 0 := by
  funext a
  simp [genOp]

theorem commS_zero {n : ℕ} (ξ : Fin (n + 1) → ℂ) (t : ℂ) :
    commS L ξ t (0 : LoopArg L (n + 1) → ℂ) = 0 := by
  rw [commS, commOp, genOp_zero, Qop_zero, genOp_zero]
  simp

/-- The `ϑ̇` term of (5.100) as an operator on the tensor. -/
noncomputable def dotMap {n : ℕ} (u : ℝ) (A : LoopArg L (n + 1) → ℂ) :
    LoopArg L (n + 1) → ℂ :=
  fun b => Psum L A (b 0) * varthetaDot L (n := n) u b

theorem dotMap_zero {n : ℕ} (u : ℝ) : dotMap L (n := n) u 0 = 0 := by
  funext b
  rw [dotMap, Psum_zero]
  simp

theorem Q1_zero {k m' : ℕ} (t : ℂ) :
    Q1 L (k := k) (m' := m') t (0 : LoopArg L ((k + 1) + m') → ℂ) = 0 := by
  funext c
  change Qop L t (fun a' => (0 : LoopArg L ((k + 1) + m') → ℂ) (Fin.append a' (spl2 L c)))
      (spl1 L c) = 0
  have h : (fun a' => (0 : LoopArg L ((k + 1) + m') → ℂ) (Fin.append a' (spl2 L c)))
      = (0 : LoopArg L (k + 1) → ℂ) := rfl
  rw [h, Qop_zero]
  rfl

theorem Q2_zero {m k : ℕ} (t : ℂ) :
    Q2 L (m := m) (k := k) t (0 : LoopArg L (m + (k + 1)) → ℂ) = 0 := by
  funext c
  change Qop L t (fun b' => (0 : LoopArg L (m + (k + 1)) → ℂ) (Fin.append (spl1 L c) b'))
      (spl2 L c) = 0
  have h : (fun b' => (0 : LoopArg L (m + (k + 1)) → ℂ) (Fin.append (spl1 L c) b'))
      = (0 : LoopArg L (k + 1) → ℂ) := rfl
  rw [h, Qop_zero]
  rfl

theorem QQ_zero {k : ℕ} (t : ℂ) : QQ L (n := k) t (0 : LoopArg L ((k + 1) + (k + 1)) → ℂ) = 0 := by
  rw [QQ_eq, Q2_zero, Q1_zero]

end Zero

/-! ### §3  The decay budgets

The error `δ` in each `hGd` below is the paper's `O(W^{-D})` made explicit.  Each is of the
shape "input error + (polynomial in the size) · `e^{-c₀K}`": the budget of Lemma 5.13 (5.87)
for `Q_u`, and of (5.99)/(5.100) for the commutator and the `ϑ̇` term.  They are named so that
the statements below stay readable; `ℓr` is `ℓ_u`. -/

section Budgets

/-- **(5.87)**: the decay budget after one `Q_u` projection, read at the radius `ℓ_u (4K)`. -/
noncomputable def qopErr (L n : ℕ) (K M δ : ℝ) : ℝ :=
  δ + ((6 * exp 1 * cTwo52 * (4 * K)) ^ (n + 1) * M
      + (2 * cTwo52) ^ (n + 1) * (L : ℝ) ^ (n + 1) * δ) * exp (-(cZero * (4 * K) / 2))

/-- **(5.87)** again, read at a general radius `ℓ_u K` rather than at `ℓ_u (4K)`.
`RBM.SumZeroDyn.fastDecay_Qop_le` does **not** widen the radius, so this is the form in which
the `Q_u` terms cost nothing at all; `qopErr` is its value at `4K`. -/
noncomputable def qopErr1 (L n : ℕ) (K M δ : ℝ) : ℝ :=
  δ + ((6 * exp 1 * cTwo52 * K) ^ (n + 1) * M
      + (2 * cTwo52) ^ (n + 1) * (L : ℝ) ^ (n + 1) * δ) * exp (-(cZero * K / 2))

theorem qopErr_eq (L n : ℕ) (K M δ : ℝ) : qopErr L n K M δ = qopErr1 L n (4 * K) M δ := rfl

theorem qopErr1_nonneg (L n : ℕ) {K M δ : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ) :
    0 ≤ qopErr1 L n K M δ := by
  have := cTwo52_pos
  unfold qopErr1
  positivity

/-- **(5.99)**: the decay budget of the commutator `[Q_u, Θ_{u,σ}]`. -/
noncomputable def commErr (L n : ℕ) (ℓr u K Pb : ℝ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) + 1) * ((1 - u)⁻¹ * (Pb * ((cTwo52 / ℓr) ^ (n + 1)
        * exp (-(cZero * ((ℓr * K) / 2) / ℓr))))
      + L * (cTwo52 / ((1 - u) * ℓr) * exp (-(cZero * (ℓr * K) / ℓr))
        * (Pb * (cTwo52 / ℓr) ^ (n + 1))))
    + (1 + ((n + 1 : ℕ) : ℝ)) * (1 - u)⁻¹ * Pb
        * ((cTwo52 / ℓr) ^ (n + 1) * exp (-(cZero * ((2 * (ℓr * K) + 1) / 2) / ℓr)))

/-- **(5.100)**: the decay budget of the `ϑ̇` term, which is `ϑ̇`'s own. -/
noncomputable def dotErr (n : ℕ) (ℓr u K Pb : ℝ) : ℝ :=
  Pb * (3 * ((n + 1 : ℕ) : ℝ) * (cTwo52 / ℓr) ^ (n + 1) * (1 - u)⁻¹
    * exp (-(cZero * ((ℓr * (4 * K)) / 4 - 1 / 2) / ℓr)))

/-- One `Q_u` block on one half of a doubled tensor: the error of (5.87) again, in the form
`RBM.SumZeroDyn.fastDecay_Q1` / `fastDecay_Q2` produce it. -/
noncomputable def qBlockErr (L k : ℕ) (ℓr R e δ : ℝ) : ℝ :=
  δ + ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ) * (cTwo52 / ℓr) ^ k
      * exp (-(cZero * R / ℓr)) + (L : ℝ) ^ k * δ * (cTwo52 / ℓr) ^ k

/-- The size after one `Q_u` block (`RBM.SumZeroDyn.norm_Q1_le` / `norm_Q2_le`). -/
noncomputable def qBlockSize (L k : ℕ) (ℓr R e δ : ℝ) : ℝ :=
  e + ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ) * (cTwo52 / ℓr) ^ k

/-- **(5.103)**: the decay budget after `Q_u ⊗ Q_u`, i.e. two nested blocks. -/
noncomputable def qqErr (L k : ℕ) (ℓr K e δ : ℝ) : ℝ :=
  qBlockErr L k ℓr (2 * (ℓr * K)) (qBlockSize L k ℓr (ℓr * K) e δ)
    (qBlockErr L k ℓr (ℓr * K) e δ)

theorem qopErr_nonneg (L n : ℕ) {K M δ : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ) :
    0 ≤ qopErr L n K M δ := by
  have := cTwo52_pos
  unfold qopErr
  positivity

theorem commErr_nonneg (L n : ℕ) {ℓr u K Pb : ℝ} (hℓ : 0 < ℓr) (hu : u < 1) (_hK : 0 ≤ K)
    (hP : 0 ≤ Pb) : 0 ≤ commErr L n ℓr u K Pb := by
  have := cTwo52_pos
  have h1u : (0 : ℝ) < 1 - u := by linarith
  unfold commErr
  positivity

theorem dotErr_nonneg (n : ℕ) {ℓr u K Pb : ℝ} (hℓ : 0 < ℓr) (hu : u < 1) (hP : 0 ≤ Pb) :
    0 ≤ dotErr n ℓr u K Pb := by
  have := cTwo52_pos
  have h1u : (0 : ℝ) < 1 - u := by linarith
  unfold dotErr
  positivity

theorem qBlockErr_nonneg (L k : ℕ) {ℓr R e δ : ℝ} (hℓ : 0 < ℓr) (hR : 0 ≤ R) (he : 0 ≤ e)
    (hδ : 0 ≤ δ) : 0 ≤ qBlockErr L k ℓr R e δ := by
  have := cTwo52_pos
  unfold qBlockErr
  positivity

theorem qBlockSize_nonneg (L k : ℕ) {ℓr R e δ : ℝ} (hℓ : 0 < ℓr) (hR : 0 ≤ R) (he : 0 ≤ e)
    (hδ : 0 ≤ δ) : 0 ≤ qBlockSize L k ℓr R e δ := by
  have := cTwo52_pos
  unfold qBlockSize
  positivity

theorem qqErr_nonneg (L k : ℕ) {ℓr K e δ : ℝ} (hℓ : 0 < ℓr) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hδ : 0 ≤ δ) : 0 ≤ qqErr L k ℓr K e δ :=
  qBlockErr_nonneg L k hℓ (by positivity)
    (qBlockSize_nonneg L k hℓ (by positivity) he hδ) (qBlockErr_nonneg L k hℓ (by positivity) he hδ)

end Budgets

/-! ### §4  The `hGd` slot for the first four terms

Each theorem here has exactly the shape T201's kernel estimates want: `∀ ω, FastDecay L
(ℓ_u (4K)) δ (T (1_Ξ A ω))`, with the hypotheses on `A` asked only **on the good event** `Ξ`.
The common radius `ℓ_u (4K)` is forced by the commutator (one application of the generator
widens by `2ℓ+1`) and by `E ⊗ E` (two `Q_u`'s); reading the two plain `Q_u` terms there as
well costs nothing. -/

section HGd

variable {Ω : Type*}

/-- **`hGd` for terms 1 and 2 of `momentDuhamelQ`** (the initial datum `Q_{s_N} ∘ (L-K)_{s_N}`
and the drift `Q_u ∘ F_u`): Lemma 5.13's decay half (`RBM.SumZeroDyn.fastDecay_Qop_le`,
(5.87)) applied on the good event.  The only inputs are the size and the (7.13) decay of the
*unprojected* tensor `A` on `Ξ`. -/
theorem hGd_Qop (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {K M δ : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    {Ξ : Set Ω} {A : Ω → LoopArg L (n + 2) → ℂ}
    (hAM : ∀ ω ∈ Ξ, ∀ b, ‖A ω b‖ ≤ M)
    (hAd : ∀ ω ∈ Ξ, FastDecay L (ellHat L ((u : ℝ) : ℂ) * K) δ (A ω)) (ω : Ω) :
    FastDecay L (ellHat L ((u : ℝ) : ℂ) * (4 * K)) (qopErr L n K M δ)
      (Qop L ((u : ℝ) : ℂ) (Set.indicator Ξ A ω)) := by
  have hℓ := half_le_ellHat_real L hL hu0 hu1
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hwide : ellHat L ((u : ℝ) : ℂ) * K ≤ ellHat L ((u : ℝ) : ℂ) * (4 * K) := by nlinarith
  refine fastDecay_of_mem_of_zero (qopErr_nonneg L n hK0 hM hδ) (Qop_zero L (n := n + 1) _)
    (fun ω hω => ?_) ω
  exact fastDecay_Qop_le L (n := n + 1) hL hu0 hu1 (by linarith : (1 : ℝ) ≤ 4 * K) hM hδ
    (hAM ω hω) (SumZeroDyn.FastDecay.mono L (hAd ω hω) hwide le_rfl)

/-- **`hGd` for terms 1 and 2, sharp radius.**  `RBM.SumZeroDyn.fastDecay_Qop_le` returns the
*same* `ℓ` it is given, so when the tensor's own (7.13) radius is already `ℓ_u K` — which is
what `RBM.FastDecayFlow.lkGood` delivers — the `Q_u` projection costs no radius at all, and
`RBM.FastDecayFlow.hGd_Qop`'s widening to `ℓ_u (4K)` (needed only to share a radius with the
commutator) can be dispensed with. -/
theorem hGd_Qop_sharp (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) {K M δ : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    {Ξ : Set Ω} {A : Ω → LoopArg L (n + 2) → ℂ}
    (hAM : ∀ ω ∈ Ξ, ∀ b, ‖A ω b‖ ≤ M)
    (hAd : ∀ ω ∈ Ξ, FastDecay L (ellHat L ((u : ℝ) : ℂ) * K) δ (A ω)) (ω : Ω) :
    FastDecay L (ellHat L ((u : ℝ) : ℂ) * K) (qopErr1 L n K M δ)
      (Qop L ((u : ℝ) : ℂ) (Set.indicator Ξ A ω)) := by
  refine fastDecay_of_mem_of_zero (qopErr1_nonneg L n (by linarith) hM hδ)
    (Qop_zero L (n := n + 1) _) (fun ω hω => ?_) ω
  exact fastDecay_Qop_le L (n := n + 1) hL hu0 hu1 hK hM hδ (hAM ω hω) (hAd ω hω)

/-- **`hGd` for term 3**, the commutator `[Q_u, Θ_{u,σ}] ∘ (L-K)_u` of (5.99).

Note what the input is: `RBM.SumZeroDyn.fastDecay_commS` needs **no** decay of `A` itself,
only the Ward bound (5.96) on its slot sums `P ∘ A` (`RBM.SumZeroDyn.norm_Psum_lkT_le` for
`A = L - K`).  That is the content of (5.99): the decay comes from `ϑ_u`, not from `A`. -/
theorem hGd_commS (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {ξ : Fin (n + 2) → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1) {K Pb : ℝ} (hK : 1 ≤ K) (hP0 : 0 ≤ Pb)
    {Ξ : Set Ω} {A : Ω → LoopArg L (n + 2) → ℂ}
    (hAP : ∀ ω ∈ Ξ, ∀ x, ‖Psum L (A ω) x‖ ≤ Pb) (ω : Ω) :
    FastDecay L (ellHat L ((u : ℝ) : ℂ) * (4 * K))
      (commErr L n (ellHat L ((u : ℝ) : ℂ)) u K Pb)
      (commS L ξ ((u : ℝ) : ℂ) (Set.indicator Ξ A ω)) := by
  have hℓ := half_le_ellHat_real L hL hu0 hu1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by linarith
  have hR : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) * K := by nlinarith
  have hrad : 2 * (ellHat L ((u : ℝ) : ℂ) * K) + 1
      ≤ ellHat L ((u : ℝ) : ℂ) * (4 * K) := by nlinarith
  refine fastDecay_of_mem_of_zero (commErr_nonneg L n hℓ0 hu1 (by linarith) hP0)
    (commS_zero L (n := n + 1) ξ _) (fun ω hω => ?_) ω
  exact SumZeroDyn.FastDecay.mono L
    (fastDecay_commS L (n := n + 1) hL hu0 hu1 hξ hR hP0 (hAP ω hω)) hrad le_rfl

/-- **`hGd` for term 4**, the `ϑ̇` term of (5.100).  The decay is entirely `ϑ̇`'s
(`RBM.SumZeroDyn.fastDecay_varthetaDot`); the tensor only has to have bounded slot sums.  The
side condition `2 ≤ ℓ_u (4K)` of that lemma is automatic here, because `ℓ_u ≥ 1/2` and
`K ≥ 1`. -/
theorem hGd_dot (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {K Pb : ℝ} (hK : 1 ≤ K) (hP0 : 0 ≤ Pb)
    {Ξ : Set Ω} {A : Ω → LoopArg L (n + 2) → ℂ}
    (hAP : ∀ ω ∈ Ξ, ∀ x, ‖Psum L (A ω) x‖ ≤ Pb) (ω : Ω) :
    FastDecay L (ellHat L ((u : ℝ) : ℂ) * (4 * K))
      (dotErr n (ellHat L ((u : ℝ) : ℂ)) u K Pb)
      (dotMap L (n := n + 1) u (Set.indicator Ξ A ω)) := by
  have hℓ := half_le_ellHat_real L hL hu0 hu1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by linarith
  have hR : (2 : ℝ) ≤ ellHat L ((u : ℝ) : ℂ) * (4 * K) := by nlinarith
  refine fastDecay_of_mem_of_zero (dotErr_nonneg n hℓ0 hu1 hP0)
    (dotMap_zero L (n := n + 1) u) (fun ω hω => ?_) ω
  exact fastDecay_Psum_mul L (fastDecay_varthetaDot L hL hu0 hu1 (n := n + 1) hR) hP0
    (hAP ω hω)

end HGd

/-! ### §4b  The decay of the unprojected tensors along the flow

`hGd_Qop` asks for (7.13) of `A` itself.  For the initial datum and for the commutator/`ϑ̇`
terms `A` is `L - K`, whose decay **is** (5.75) = `RBM.SumZeroDyn.LKDecay` — the object Step 2
delivers through (2.76) (`RBM.LKDecayQuant.lkDecay_of_inputs`).  For the drift `A = F_u` is
the pinned `RBM.DriftDef.driftF`, whose decay is a *deterministic* theorem. -/

section Underlying

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ}

/-- **(5.75) in the shape `hGd_Qop` reads it at.**  `RBM.SumZeroDyn.LKDecay` is stated through
`RBM.Sample.lkErr` weighted by `RBM.SumZeroDyn.farInd`; that pointwise inequality is exactly
(7.13) of the tensor `RBM.SumZeroDyn.lkT` (`RBM.SumZeroDyn.fastDecay_of_farInd` and
`RBM.SumZeroDyn.norm_lkT`). -/
theorem fastDecay_lkT_of_farInd {N : ℕ} {u : ℝ} {ω : Ω} {m : ℕ} (σ : Fin m → Bool) {R δ : ℝ}
    (h : ∀ b : LoopArg (B.L N) m,
      X.lkErr E N u ω (LoopData.idx (σ, b)) * farInd (B.L N) R b ≤ δ) :
    FastDecay (B.L N) R δ (lkT X E N u ω σ) :=
  fastDecay_of_farInd fun b => by rw [norm_lkT]; exact h b

/-- **(7.13) for the pinned drift `F_u`**, at the radius the kernel estimate reads it at.

`RBM.DriftDef.fastDecay_driftF` is deterministic and pathwise: Lemma 5.9's decay of `K`, of
`L` and of `L - K`, with their sup bounds, is its whole input, and no `ω` is quantified over.
It produces the radius `2ℓ + 1`; at `ℓ = ℓ_u K` that is below `ℓ_u (4K)` because `ℓ_u ≥ 1/2`
and `K ≥ 1`, which is the same regrading `RBM.SumZeroDyn.hgood_commDot` performs. -/
theorem fastDecay_driftF_window (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ) (hL : 3 ≤ B.L N)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (Mx : Matrix (B.Idx N) (B.Idx N) ℂ) {n : ℕ}
    (σ : Fin (n + 2) → Bool) {K δ MK MD δF : ℝ} (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hMK : 0 ≤ MK) (hMD : 0 ≤ MD)
    (hKd : Decay.LoopDecay (B.L N) (n + 2) (ellHat (B.L N) ((u : ℝ) : ℂ) * K) δ
      (B.Kval E N u))
    (hDd : Decay.LoopDecay (B.L N) (n + 2) (ellHat (B.L N) ((u : ℝ) : ℂ) * K) δ
      (gloop (B.L N) (B.W N) Mx (zt E u) - B.Kval E N u))
    (hLd : Decay.LoopDecay (B.L N) (n + 3) (ellHat (B.L N) ((u : ℝ) : ℂ) * K) δ
      (gloop (B.L N) (B.W N) Mx (zt E u)))
    (hKb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length ≤ n + 2 → ‖B.Kval E N u J‖ ≤ MK)
    (hDb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length ≤ n + 2 →
      ‖(gloop (B.L N) (B.W N) Mx (zt E u) - B.Kval E N u) J‖ ≤ MD)
    (hδF : (B.W N : ℝ) * ((n : ℝ) + 2) * ((B.L N : ℝ) * (MD * δ))
        + (n : ℝ) * (2 * (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * (B.L N : ℝ) * δ * (MK + MD))
        + 2 * (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * (B.L N : ℝ) * δ * MD ≤ δF) :
    FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * (4 * K)) δF
      (DriftDef.driftF B E N u Mx σ) := by
  have hℓ := half_le_ellHat_real (B.L N) hL hu0 hu1
  have hℓ0 : (0 : ℝ) ≤ ellHat (B.L N) ((u : ℝ) : ℂ) := by linarith
  have hrad : 2 * (ellHat (B.L N) ((u : ℝ) : ℂ) * K) + 1
      ≤ ellHat (B.L N) ((u : ℝ) : ℂ) * (4 * K) := by nlinarith
  refine SumZeroDyn.FastDecay.mono (B.L N)
    (DriftDef.fastDecay_driftF B E N u Mx σ (by positivity) hδ hMK hMD hKd hDd hLd hKb hDb
      hδF) hrad le_rfl

end Underlying

/-! ### §5  (7.13) for `E ⊗ E`

The fifth tensor is the only one whose decay is not already packaged somewhere in the
repository.  `RBM.Decay.norm_eTens_le_of_far` bounds (5.22) by `W n L δ` **provided every
glued loop `J k b b'` of (5.23) carries two labels at distance `≥ ℓ`**, and that hypothesis is
what has to be checked: the gluing cuts one `G` edge of each factor, so one has to know that
cutting does not lose a label.

It does not.  `RBM.EEBridge.cutPairs` is `RBM.EEBridge.pairs` *rotated* to begin at the cut
edge — the cut edge's own pair is put back as the head — and `RBM.EEBridge.rflip` reverses a
chain, keeping every label and adding the closing one.  So the glued `(2m+2)`-loop contains
every label of `a` and of `a'`, and a far pair among the `2m` arguments of the doubled tensor
survives it. -/

section EEDecay

open EEBridge

variable {L : ℕ}

/-- Rotating a list to begin at its `k`-th entry keeps every element. -/
theorem mem_rot_cons {α : Type*} (l : List α) {k : ℕ} (hk : k < l.length) {x : α} (hx : x ∈ l) :
    x ∈ l[k] :: (l.drop (k + 1) ++ l.take k) := by
  have hx' : x ∈ l.take k ++ l.drop k := by rw [List.take_append_drop]; exact hx
  rcases List.mem_append.1 hx' with h | h
  · exact List.mem_cons_of_mem _ (List.mem_append.2 (Or.inr h))
  · rw [List.drop_eq_getElem_cons hk] at h
    rcases List.mem_cons.1 h with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append.2 (Or.inl h))

/-- **Cutting a `G` edge keeps every label.**  `RBM.EEBridge.cutPairs` puts the cut pair back
as the head, so it is `RBM.EEBridge.pairs` rotated; this is what makes the decay of the
`G`-loops survive the gluing of (5.23). -/
theorem mem_cutPairs_of_mem {I : LoopIdx (ZMod L)} (hI : I.WF) {k : ℕ} (hk : k < I.length)
    {x : ZMod L} (hx : x ∈ I.a) : x ∈ (cutPairs I k).map Prod.snd := by
  have hlen : I.σ.length = I.a.length := hI
  have hps : (pairs I).map Prod.snd = I.a := List.map_snd_zip (le_of_eq hlen.symm)
  have hpl : (pairs I).length = I.length := pairs_length hI
  have hk' : k < (pairs I).length := by rw [hpl]; exact hk
  rw [← hps] at hx
  obtain ⟨p, hp, hpx⟩ := List.mem_map.1 hx
  have hpa : pairAt I k = (pairs I)[k] := List.getD_eq_getElem _ _ hk'
  rw [cutPairs, hpa]
  exact List.mem_map.2 ⟨p, mem_rot_cons (pairs I) hk' hp, hpx⟩

/-- **Reversing and flipping a chain keeps its labels**, and adds the closing label `c`. -/
theorem mem_rflip {t : Bool} : ∀ (l : List (Bool × ZMod L)) (c : ZMod L) {x : ZMod L},
    (x ∈ l.map Prod.snd ∨ x = c) → x ∈ (rflip t l c).map Prod.snd := by
  intro l
  induction l with
  | nil =>
      intro c x hx
      rcases hx with hx | hx
      · simp at hx
      · simp [hx]
  | cons p l ih =>
      intro c x hx
      rw [rflip_cons, List.map_append]
      rcases hx with hx | hx
      · refine List.mem_append.2 (Or.inl (ih p.2 ?_))
        rcases List.mem_cons.1 (by simpa using hx : x ∈ p.2 :: l.map Prod.snd) with h | h
        · exact Or.inr h
        · exact Or.inl h
      · exact List.mem_append.2 (Or.inr (by simp [hx]))

/-- **Every label of either factor occurs in the glued loop of (5.23).** -/
theorem mem_glueIdx_of_mem {I I' : LoopIdx (ZMod L)} (hI : I.WF) (hI' : I'.WF) {k : ℕ}
    (hk : k < I.length) (hk' : k < I'.length) (b b' : ZMod L) {x : ZMod L}
    (hx : x ∈ I.a ∨ x ∈ I'.a) : x ∈ (glueIdx I I' k b b').a := by
  rw [glueIdx, ofPairs_a, List.map_append]
  rcases hx with hx | hx
  · exact List.mem_append.2 (Or.inl (mem_cutPairs_of_mem hI hk hx))
  · refine List.mem_append.2 (Or.inr ?_)
    rw [List.map_cons]
    exact List.mem_cons_of_mem _ (mem_rflip _ _ (Or.inl (mem_cutPairs_of_mem hI' hk' hx)))

variable {d : Gauss.Dims} {N : ℕ} {z : ℂ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}

/-- **(7.13) for `E ⊗ E` of Definition 5.4**: if the `G`-loops of length `2m + 2` have the
`(ℓ, δ)` decay of Definition 5.8 (Lemma 5.9), then the doubled tensor `RBM.EEBridge.eeArg` is
`(ℓ, W m L δ)`-fast-decaying in its `2m` arguments.

This is `RBM.Decay.norm_eTens_le_of_far` with its "every glued loop carries a far pair"
hypothesis discharged by `RBM.FastDecayFlow.mem_glueIdx_of_mem`. -/
theorem fastDecay_eeArg (hM : M.IsHermitian) {m : ℕ} (σ : Fin m → Bool) {ℓ δ : ℝ}
    (hYd : Decay.LoopDecay (d.L N) (2 * m + 2) ℓ δ (gloop (d.L N) (d.W N) M z)) :
    FastDecay (d.L N) ℓ ((d.W N : ℝ) * m * ((d.L N : ℝ) * δ))
      (fun c : LoopArg (d.L N) (m + m) => eeArg d N z M σ c) := by
  intro c hc
  obtain ⟨i, j, hij⟩ := hc
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; exact absurd i.isLt (by omega)
    · exact h
  have hIwf : (Gauss.toIdx σ (leftArg c)).WF := Gauss.toIdx_wf _ _
  have hI'wf : (Gauss.toIdx σ (rightArg c)).WF := Gauss.toIdx_wf _ _
  have hIl : (Gauss.toIdx σ (leftArg c)).length = m := Gauss.toIdx_length _ _
  have hI'l : (Gauss.toIdx σ (rightArg c)).length = m := Gauss.toIdx_length _ _
  have hIa : (Gauss.toIdx σ (leftArg c)).a = List.ofFn (leftArg c) := rfl
  have hI'a : (Gauss.toIdx σ (rightArg c)).a = List.ofFn (rightArg c) := rfl
  have hclamp : ∀ k : ℕ, min (k - 1) (m - 1) < m := fun k => by
    have : min (k - 1) (m - 1) ≤ m - 1 := min_le_right _ _
    omega
  have hmemI : ∀ p : Fin (m + m),
      c p ∈ (Gauss.toIdx σ (leftArg c)).a ∨ c p ∈ (Gauss.toIdx σ (rightArg c)).a := by
    intro p
    refine Fin.addCases (motive := fun p => c p ∈ (Gauss.toIdx σ (leftArg c)).a
      ∨ c p ∈ (Gauss.toIdx σ (rightArg c)).a) (fun p₁ => ?_) (fun p₂ => ?_) p
    · refine Or.inl ?_
      rw [hIa]
      exact List.mem_ofFn.2 ⟨p₁, rfl⟩
    · refine Or.inr ?_
      rw [hI'a]
      exact List.mem_ofFn.2 ⟨p₂, rfl⟩
  have hfar : ∀ (k : ℕ) (b b' : ZMod (d.L N)),
      ∃ x ∈ (glueJ (Gauss.toIdx σ (leftArg c)) (Gauss.toIdx σ (rightArg c)) m k b b').a,
        ∃ y ∈ (glueJ (Gauss.toIdx σ (leftArg c)) (Gauss.toIdx σ (rightArg c)) m k b b').a,
          ℓ ≤ (zdist (d.L N) (x - y) : ℝ) := by
    intro k b b'
    have hkI : min (k - 1) (m - 1) < (Gauss.toIdx σ (leftArg c)).length := by
      rw [hIl]; exact hclamp k
    have hkI' : min (k - 1) (m - 1) < (Gauss.toIdx σ (rightArg c)).length := by
      rw [hI'l]; exact hclamp k
    exact ⟨c i, by rw [glueJ]; exact mem_glueIdx_of_mem hIwf hI'wf hkI hkI' b b' (hmemI i),
      c j, by rw [glueJ]; exact mem_glueIdx_of_mem hIwf hI'wf hkI hkI' b b' (hmemI j), hij⟩
  have hJ : ∀ (k : ℕ) (b b' : ZMod (d.L N)),
      (glueJ (Gauss.toIdx σ (leftArg c)) (Gauss.toIdx σ (rightArg c)) m k b b').WF
      ∧ (glueJ (Gauss.toIdx σ (leftArg c)) (Gauss.toIdx σ (rightArg c)) m k b b').length
          = 2 * m + 2 :=
    fun k b b' => ⟨glueIdx_wf _ _ _ _ _, glueIdx_length hIwf hI'wf hIl hI'l (hclamp k) b b'⟩
  have key := Decay.norm_eTens_le_of_far (d.L N) (d.three_le_L N) (d.W N) m hJ hYd hfar
  change ‖eeArg d N z M σ c‖ ≤ _
  rw [show eeArg d N z M σ c
      = Gauss.eeTens d N z M (Gauss.toIdx σ (leftArg c)) (Gauss.toIdx σ (rightArg c)) from rfl,
    eeTens_eq_eTens hM, hIl]
  exact key

end EEDecay

/-! ### §6  `hGd` for term 5: `(Q_u ⊗ Q_u) ∘ (E ⊗ E)_u`

(5.103) with the two blocks projected.  The decay survives both projections by Lemma 5.13
applied once per block (`RBM.SumZeroDyn.fastDecay_Q2`, then `fastDecay_Q1`), each doubling the
radius — so the common radius `ℓ_u (4K)` is exactly what two blocks produce. -/

section QQDecay

variable {Ω : Type*}

/-- **(7.13) survives `Q_u ⊗ Q_u`.** -/
theorem fastDecay_QQ (L : ℕ) [NeZero L] (hL : 3 ≤ L) {k : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) {K e δ : ℝ} (hK : 1 ≤ K) (he : 0 ≤ e) (hδ : 0 ≤ δ)
    {Bc : LoopArg L ((k + 1) + (k + 1)) → ℂ} (hBe : ∀ c, ‖Bc c‖ ≤ e)
    (hB : FastDecay L (ellHat L ((u : ℝ) : ℂ) * K) δ Bc) :
    FastDecay L (ellHat L ((u : ℝ) : ℂ) * (4 * K))
      (qqErr L k (ellHat L ((u : ℝ) : ℂ)) K e δ) (QQ L ((u : ℝ) : ℂ) Bc) := by
  have hℓ := half_le_ellHat_real L hL hu0 hu1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by linarith
  have hR : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) * K := by nlinarith
  have h2max : ∀ c, ‖Q2 L ((u : ℝ) : ℂ) Bc c‖
      ≤ qBlockSize L k (ellHat L ((u : ℝ) : ℂ)) (ellHat L ((u : ℝ) : ℂ) * K) e δ :=
    norm_Q2_le L hL hu0 hu1 hR he hδ hBe hB
  have h2dec : FastDecay L (2 * (ellHat L ((u : ℝ) : ℂ) * K))
      (qBlockErr L k (ellHat L ((u : ℝ) : ℂ)) (ellHat L ((u : ℝ) : ℂ) * K) e δ)
      (Q2 L ((u : ℝ) : ℂ) Bc) :=
    fastDecay_Q2 L hL hu0 hu1 hR he hδ hBe hB
  have h3dec := fastDecay_Q1 L hL hu0 hu1
    (by linarith : (0 : ℝ) < 2 * (ellHat L ((u : ℝ) : ℂ) * K))
    (qBlockSize_nonneg L k hℓ0 hR.le he hδ) (qBlockErr_nonneg L k hℓ0 hR.le he hδ) h2max h2dec
  rw [QQ_eq]
  exact SumZeroDyn.FastDecay.mono L h3dec (le_of_eq (by ring)) le_rfl

/-- **`hGd` for term 5 of `momentDuhamelQ`**, the `E ⊗ E` term of (5.103). -/
theorem hGd_QQ (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {K e δ : ℝ} (hK : 1 ≤ K) (he : 0 ≤ e) (hδ : 0 ≤ δ)
    {Ξ : Set Ω} {A : Ω → LoopArg L ((n + 2) + (n + 2)) → ℂ}
    (hAe : ∀ ω ∈ Ξ, ∀ c, ‖A ω c‖ ≤ e)
    (hAd : ∀ ω ∈ Ξ, FastDecay L (ellHat L ((u : ℝ) : ℂ) * K) δ (A ω)) (ω : Ω) :
    FastDecay L (ellHat L ((u : ℝ) : ℂ) * (4 * K))
      (qqErr L (n + 1) (ellHat L ((u : ℝ) : ℂ)) K e δ)
      (QQ L ((u : ℝ) : ℂ) (Set.indicator Ξ A ω)) := by
  have hℓ := half_le_ellHat_real L hL hu0 hu1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by linarith
  refine fastDecay_of_mem_of_zero (qqErr_nonneg L (n + 1) hℓ0 (by linarith) he hδ)
    (QQ_zero L (k := n + 1) _) (fun ω hω => ?_) ω
  exact fastDecay_QQ L hL hu0 hu1 hK he hδ (hAe ω hω) (hAd ω hω)

end QQDecay

/-! ### §7  `E ⊗ E` along the flow

`RBM.MomentDuhamel.eeFun` is `RBM.EEBridge.eeArg` by definition, so §5 applies to it verbatim
at the flow's (Hermitian) matrix. -/

section EEFlow

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(7.13) for the pinned `E ⊗ E` of Definition 5.4**, evaluated at any Hermitian matrix —
in particular at the flow `H_u` (`RBM.Sample.hermitian`).  The input is Lemma 5.9's decay of
the `G`-loops of length `2m + 2`, the same object `RBM.EEBridge.eeDecayEvent` names. -/
theorem fastDecay_eeFun (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    {Mx : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : Mx.IsHermitian) {m : ℕ} (σ : Fin m → Bool)
    {ℓ δ : ℝ}
    (hYd : Decay.LoopDecay (B.L N) (2 * m + 2) ℓ δ (gloop (B.L N) (B.W N) Mx (zt E u))) :
    FastDecay (B.L N) ℓ ((B.W N : ℝ) * m * ((B.L N : ℝ) * δ))
      (MomentDuhamel.eeFun B E N u Mx σ) :=
  fastDecay_eeArg (d := B.toDims) (N := N) (z := zt E u) (M := Mx) hM σ hYd

end EEFlow

/-! ### §8  The good events, and their high probability

This is the section that keeps §1's truncation honest.  `RBM.FastDecayFlow.hGd_Qop` and its
three siblings are statements about `1_Ξ A`; if `Ξ` could be taken empty they would be
statements about the zero tensor, and the whole file would be content-free in exactly the way
T164/T169 warn about.  So `Ξ` is not assumed here — it is **produced** from (5.75), with its
`RBM.HighProb` and (hence) its non-emptiness proved. -/

section GoodEvents

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A high-probability family of events is eventually non-empty.**

No measurability is needed: if `Ξ N` were empty then `(Ξ N)ᶜ = univ` has measure `1`, while
`RBM.HighProb` at `D = 1` puts it below `N^{-1} < 1`. -/
theorem nonempty_of_highProb {P : Measure Ω} [IsProbabilityMeasure P] {Ξ : ℕ → Set Ω}
    (h : HighProb P Ξ) : ∀ᶠ N : ℕ in atTop, (Ξ N).Nonempty := by
  filter_upwards [h 1 one_pos, eventually_ge_atTop 2] with N hN hN2
  rw [Set.nonempty_iff_ne_empty]
  intro hemp
  rw [hemp, Set.compl_empty, measure_univ] at hN
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hrw : (N : ℝ) ^ (-(1 : ℝ)) = ((N : ℝ))⁻¹ := by
    rw [Real.rpow_neg (by linarith), Real.rpow_one]
  have hlt : (N : ℝ) ^ (-(1 : ℝ)) < 1 := by
    rw [hrw, inv_lt_one_iff₀]
    right; linarith
  exact absurd hN (not_le.2 (ENNReal.ofReal_lt_one.2 hlt))

variable {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **The good event of (5.75)** at loop length `m`, radius exponent `τ`, Markov exponent `τ₁`
and order `D`: at every time of the window and every charge, `RBM.Sample.lkErr` is below
`N^{τ₁} N^{-D}` as soon as two labels are `ℓ_u N^τ` apart.

This is literally the set `RBM.SumZeroDyn.good_of_stochDom` produces from
`RBM.SumZeroDyn.LKDecay`, which is why `RBM.FastDecayFlow.highProb_lkGood` is one `exact`. -/
def lkGood (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (m : ℕ) (τ τ₁ D : ℝ) (N : ℕ) : Set Ω :=
  {ω | ∀ p : TimeIcc s t N × LoopData (B.L N) m,
      X.lkErr E N (p.1 : ℝ) ω p.2.idx
          * farInd (B.L N) (B.ell N (p.1 : ℝ) * (N : ℝ) ^ τ) p.2.2
        ≤ (N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)}

/-- **(5.75) ⇒ the good event holds with high probability.**  The stochastic input is
(2.76): `RBM.LKDecayQuant.lkDecay_of_inputs` produces `LKDecay` from it. -/
theorem highProb_lkGood (hdec : LKDecay X E s t) {m : ℕ} (hm : 1 ≤ m) {τ τ₁ D : ℝ}
    (hτ : 0 < τ) (hτ₁ : 0 < τ₁) (hD : 0 < D) :
    HighProb B.P (lkGood X E s t m τ τ₁ D) :=
  good_of_stochDom (hdec m hm τ hτ D hD) hτ₁

/-- **The good event is eventually non-empty** — the anti-vacuity statement for the whole
file. -/
theorem nonempty_lkGood (hdec : LKDecay X E s t) {m : ℕ} (hm : 1 ≤ m) {τ τ₁ D : ℝ}
    (hτ : 0 < τ) (hτ₁ : 0 < τ₁) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, (lkGood X E s t m τ τ₁ D N).Nonempty := by
  have := B.isProbabilityMeasure
  exact nonempty_of_highProb (highProb_lkGood hdec hm hτ hτ₁ hD)

/-- **(7.13) for `L - K` on the good event**, at the radius `ℓ_u N^τ` the kernel estimates
read it at.  This is (5.75) unwrapped through `RBM.SumZeroDyn.fastDecay_of_farInd`. -/
theorem fastDecay_lkT_of_mem_lkGood {m N : ℕ} {τ τ₁ D u : ℝ} (hsu : s N ≤ u) (hut : u ≤ t N)
    {ω : Ω} (hω : ω ∈ lkGood X E s t m τ τ₁ D N) (σ : Fin m → Bool) :
    FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * (N : ℝ) ^ τ)
      ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)) (lkT X E N u ω σ) :=
  fastDecay_of_farInd fun b => by
    rw [norm_lkT]; exact hω (⟨u, hsu, hut⟩, (σ, b))

/-- **(7.13) for `E ⊗ E` on the `G`-loop decay event**, i.e. §5 read along the flow.

The event is `RBM.LKDecayQuant.GLoopDecayEvent` at the glued length `2(n+2)+2`, which is
definitionally `RBM.EEBridge.eeDecayEvent` and which
`RBM.LKDecayQuant.highProb_gLoopDecay_of_flowInputs` produces with high probability. -/
theorem fastDecay_eeFun_of_mem_gLoopDecay {n N : ℕ} {τ D u : ℝ} (hsu : s N ≤ u) (hut : u ≤ t N)
    {ω : Ω} (hω : ω ∈ LKDecayQuant.GLoopDecayEvent X E s t (2 * (n + 2) + 2) τ D N)
    (σ : Fin (n + 2) → Bool) :
    FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * (N : ℝ) ^ τ)
      ((B.W N : ℝ) * ((n + 2 : ℕ) : ℝ) * ((B.L N : ℝ) * (N : ℝ) ^ (-D)))
      (MomentDuhamel.eeFun B E N u (X.H N u ω) σ) :=
  fastDecay_eeFun B E N u (X.hermitian N u ω) σ (hω ⟨u, hsu, hut⟩)

/-- **(5.96) on the good event**: the Ward bound on the slot sums of `L - K`, which is the
*only* thing terms 3 and 4 of `momentDuhamelQ` ask of the tensor.

`RBM.SumZeroDyn.norm_Psum_lkT_le` with its decay slot filled by `lkGood` **at loop length
`n+1`** — one length below the tensor, because Ward's identity trades a label for a factor
`κ_u = (2iWη_u)^{-1}`. -/
theorem norm_Psum_lkT_le_of_mem_lkGood (hE : |E| < 2) {n : ℕ} (hW : WardP X E n) {N : ℕ}
    {u : ℝ} (hsu : s N ≤ u) (hut : u ≤ t N) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hA0 : 0 < B.scale E N u) {σ : Fin (n + 2) → Bool} (hq : QGood σ)
    {τ τ₁ D φ : ℝ} (hN1 : 1 ≤ N) (hφ : 0 ≤ φ)
    {ω : Ω} (hω : ω ∈ lkGood X E s t (n + 1) τ τ₁ D N)
    (hX : X.xiLK E N u ω (n + 1) ≤ (N : ℝ) ^ τ * φ) (x : ZMod (B.L N)) :
    ‖Psum (B.L N) (lkT X E N u ω σ) x‖
      ≤ (2 * (B.W N : ℝ) * etaT E u)⁻¹
          * (2 * ((2 * exp 1 * (B.ell N u * (N : ℝ) ^ τ + 1)) ^ n
            * ((N : ℝ) ^ τ * φ * (B.scale E N u)⁻¹ ^ (n + 1))
          + (B.L N : ℝ) ^ n * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)))) := by
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hK0 : (0 : ℝ) < (N : ℝ) ^ τ := Real.rpow_pos_of_pos (by linarith) _
  refine norm_Psum_lkT_le X hE hW hu0 hu1 hA0 hq hK0 hφ
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hX (fun ρ b => ?_) x
  exact hω (⟨u, hsu, hut⟩, (ρ, b))

end GoodEvents

/-! ### §9  The `hGd` slot at the five tensors of `momentDuhamelQ` themselves

§4 and §6 discharge `hGd` for an abstract tensor controlled on `Ξ`; here `Ξ` and the tensor
are the model's.  These five are what T219's assembly plugs in. -/

section FiveTensors

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **Term 1 of `momentDuhamelQ`**, the initial datum `Q_{s_N} ∘ (L-K)_{s_N,σ}` of (5.91),
read at a general window time `u` (the field uses `u = s_N`).

The radius is *not* given away: `RBM.SumZeroDyn.fastDecay_Qop_le` returns the same `ℓ`, so
`ℓ_u N^τ` — the radius `lkGood` provides — is also the radius the kernel estimate is read
at. -/
theorem hGd_Qop_lkT {n N : ℕ} {τ τ₁ D u M : ℝ} (hsu : s N ≤ u) (hut : u ≤ t N)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hτK : 1 ≤ (N : ℝ) ^ τ) (hM : 0 ≤ M)
    (σ : Fin (n + 2) → Bool) {Ξ : Set Ω} (hΞ : Ξ ⊆ lkGood X E s t (n + 2) τ τ₁ D N)
    (hAM : ∀ ω ∈ Ξ, ∀ b, ‖lkT X E N u ω σ b‖ ≤ M) (ω : Ω) :
    FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * (N : ℝ) ^ τ)
      (qopErr1 (B.L N) n ((N : ℝ) ^ τ) M ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)))
      (Qop (B.L N) ((u : ℝ) : ℂ) (Set.indicator Ξ (fun ω => lkT X E N u ω σ) ω)) :=
  hGd_Qop_sharp (B.L N) (B.three_le_L N) hu0 hu1 hτK hM (by positivity) hAM
    (fun ω hω => fastDecay_lkT_of_mem_lkGood hsu hut (hΞ hω) σ) ω

/-- **Term 2 of `momentDuhamelQ`**, the drift `Q_u ∘ F_u` of (5.91) with `F` pinned to
`RBM.DriftDef.driftF` (T58/T206).

Note where the stochastic input is and is not: `RBM.DriftDef.fastDecay_driftF` is pathwise and
deterministic, so the event only has to deliver *its* inputs — Lemma 5.9's decay of `K`, of
`L` and of `L - K` at the flow's matrix, and their sup bounds.  Those are taken here as
hypotheses on `Ξ`, exactly as `RBM.DriftBound` takes them; the `K` half has no producer above
loop length `3` anywhere in the repository (`RBM.exists_loopDecay_Kval`). -/
theorem hGd_Qop_driftF {n N : ℕ} {u K δ MK MD δF M : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hK : 1 ≤ K) (hδ : 0 ≤ δ) (hMK : 0 ≤ MK) (hMD : 0 ≤ MD) (hM : 0 ≤ M) (hδF : 0 ≤ δF)
    (σ : Fin (n + 2) → Bool) {Ξ : Set Ω}
    (hAM : ∀ ω ∈ Ξ, ∀ b, ‖DriftDef.driftF B E N u (X.H N u ω) σ b‖ ≤ M)
    (hKd : ∀ ω ∈ Ξ, Decay.LoopDecay (B.L N) (n + 2)
      (ellHat (B.L N) ((u : ℝ) : ℂ) * K) δ (B.Kval E N u))
    (hDd : ∀ ω ∈ Ξ, Decay.LoopDecay (B.L N) (n + 2)
      (ellHat (B.L N) ((u : ℝ) : ℂ) * K) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u))
    (hLd : ∀ ω ∈ Ξ, Decay.LoopDecay (B.L N) (n + 3)
      (ellHat (B.L N) ((u : ℝ) : ℂ) * K) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)))
    (hKb : ∀ ω ∈ Ξ, ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length ≤ n + 2 →
      ‖B.Kval E N u J‖ ≤ MK)
    (hDb : ∀ ω ∈ Ξ, ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length ≤ n + 2 →
      ‖(gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u) J‖ ≤ MD)
    (hbudget : (B.W N : ℝ) * ((n : ℝ) + 2) * ((B.L N : ℝ) * (MD * δ))
        + (n : ℝ) * (2 * (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * (B.L N : ℝ) * δ * (MK + MD))
        + 2 * (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * (B.L N : ℝ) * δ * MD ≤ δF) (ω : Ω) :
    FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * (4 * K))
      (qopErr1 (B.L N) n (4 * K) M δF)
      (Qop (B.L N) ((u : ℝ) : ℂ)
        (Set.indicator Ξ (fun ω => DriftDef.driftF B E N u (X.H N u ω) σ) ω)) :=
  hGd_Qop_sharp (B.L N) (B.three_le_L N) hu0 hu1 (by linarith) hM hδF hAM
    (fun ω hω => fastDecay_driftF_window B E N u (B.three_le_L N) hu0 hu1 (X.H N u ω) σ hK hδ
      hMK hMD (hKd ω hω) (hDd ω hω) (hLd ω hω) (hKb ω hω) (hDb ω hω) hbudget) ω

/-- **Term 3 of `momentDuhamelQ`**, the commutator `[Q_u, Θ_{u,σ}] ∘ (L-K)_u` of (5.99).

The tensor's own (7.13) is **not** used: the decay is `ϑ_u`'s, and all that is asked of
`L - K` is the Ward bound (5.96) on its slot sums
(`RBM.FastDecayFlow.norm_Psum_lkT_le_of_mem_lkGood`). -/
theorem hGd_commS_lkT {n N : ℕ} {u K Pb : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hE : |E| ≤ 2)
    (hK : 1 ≤ K) (hP0 : 0 ≤ Pb) (σ : Fin (n + 2) → Bool) {Ξ : Set Ω}
    (hAP : ∀ ω ∈ Ξ, ∀ x, ‖Psum (B.L N) (lkT X E N u ω σ) x‖ ≤ Pb) (ω : Ω) :
    FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * (4 * K))
      (commErr (B.L N) n (ellHat (B.L N) ((u : ℝ) : ℂ)) u K Pb)
      (commS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
        (Set.indicator Ξ (fun ω => lkT X E N u ω σ) ω)) :=
  hGd_commS (B.L N) (B.three_le_L N) hu0 hu1
    (fun i => (norm_xiOf_mSigma hE σ i).le) hK hP0 hAP ω

/-- **Term 4 of `momentDuhamelQ`**, the `ϑ̇` term of (5.100).  Same input as term 3: (5.96)
only. -/
theorem hGd_dot_lkT {n N : ℕ} {u K Pb : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hK : 1 ≤ K) (hP0 : 0 ≤ Pb) (σ : Fin (n + 2) → Bool) {Ξ : Set Ω}
    (hAP : ∀ ω ∈ Ξ, ∀ x, ‖Psum (B.L N) (lkT X E N u ω σ) x‖ ≤ Pb) (ω : Ω) :
    FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * (4 * K))
      (dotErr n (ellHat (B.L N) ((u : ℝ) : ℂ)) u K Pb)
      (dotMap (B.L N) (n := n + 1) u (Set.indicator Ξ (fun ω => lkT X E N u ω σ) ω)) :=
  hGd_dot (B.L N) (B.three_le_L N) hu0 hu1 hK hP0 hAP ω

/-- **Term 5 of `momentDuhamelQ`**, the `E ⊗ E` term `(Q_u ⊗ Q_u) ∘ (E ⊗ E)_u` of (5.103),
with `E ⊗ E` the pinned `RBM.MomentDuhamel.eeFun` of Definition 5.4.

The decay input is the one of §5/§8: Definition 5.8 for the flow's `G`-loops at the glued
length `2(n+2)+2`. -/
theorem hGd_QQ_eeFun {n N : ℕ} {τ D u e : ℝ} (hsu : s N ≤ u) (hut : u ≤ t N)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hτK : 1 ≤ (N : ℝ) ^ τ) (he : 0 ≤ e)
    (σ : Fin (n + 2) → Bool) {Ξ : Set Ω}
    (hΞ : Ξ ⊆ LKDecayQuant.GLoopDecayEvent X E s t (2 * (n + 2) + 2) τ D N)
    (hAe : ∀ ω ∈ Ξ, ∀ c, ‖MomentDuhamel.eeFun B E N u (X.H N u ω) σ c‖ ≤ e) (ω : Ω) :
    FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * (4 * (N : ℝ) ^ τ))
      (qqErr (B.L N) (n + 1) (ellHat (B.L N) ((u : ℝ) : ℂ)) ((N : ℝ) ^ τ) e
        ((B.W N : ℝ) * ((n + 2 : ℕ) : ℝ) * ((B.L N : ℝ) * (N : ℝ) ^ (-D))))
      (QQ (B.L N) ((u : ℝ) : ℂ)
        (Set.indicator Ξ (fun ω => MomentDuhamel.eeFun B E N u (X.H N u ω) σ) ω)) :=
  hGd_QQ (B.L N) (B.three_le_L N) hu0 hu1 hτK he (by positivity) hAe
    (fun ω hω => fastDecay_eeFun_of_mem_gLoopDecay hsu hut (hΞ hω) σ) ω

end FiveTensors

/-! ### §10  T201's five kernel estimates with `hGd` discharged

These are `RBM.Gauss.momNorm_Uker_Qop_le`, `…_commS_le`, `…_PsumVarthetaDot_le`, `…_QQ_le`
with their **last open premise supplied by a theorem** rather than by a hypothesis.  Terms 1
and 2 of `RBM.MomentDuhamel.Hyp.momentDuhamelQ` share the first shape (the tensor under `Q_u`
is `(L-K)_{s_N}` for the datum and `F_u` for the drift), so four statements cover the five
terms; §9 supplies the tensor in each case.

What is *not* discharged here, and is not this ticket's: the size envelope `hGM`, the
integrability `hint`, and the passage from the truncated tensor `1_Ξ A` back to `A` (that is
`RBM.Gauss.momNorm_le_affine_on_event`, i.e. T218/T219). -/

section Discharged

open RBM.MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Terms 1 and 2 of `momentDuhamelQ`, with `hGd` discharged.**  The decay premise is gone:
all that is left about the tensor is that on the good event it is bounded by `M` and
`(ℓ_u K, δ)`-fast-decaying — which §8 produces from (5.75). -/
theorem momNorm_Uker_Qop_event_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K M ζ δ : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {Ξ : Set Ω} {A : Ω → LoopArg L (n + 2) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖Qop L ((u : ℝ) : ℂ) (Set.indicator Ξ A ω) b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hAM : ∀ ω ∈ Ξ, ∀ b, ‖A ω b‖ ≤ M)
    (hAd : ∀ ω ∈ Ξ, FastDecay L (ellHat L ((u : ℝ) : ℂ) * K) δ (A ω))
    (a : LoopArg L (n + 2)) :
    momNorm P q (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop L ((u : ℝ) : ℂ) (Set.indicator Ξ A ω)) a‖)
      ≤ cKerSumZero (n + 2) * K ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * momNorm P q ψ
        + (cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2)
              * qopErr1 L n K M δ) :=
  Gauss.momNorm_Uker_Qop_le L hL hq hE σ hs0 hsu huv hv0 hv1 hκA hK hζ
    (qopErr1_nonneg L n (by linarith) hM hδ) hψ0 hint hGM
    (hGd_Qop_sharp L hL (hs0.trans hsu) (huv.trans_lt hv1) hK hM hδ hAM hAd) a

/-- **Term 3 of `momentDuhamelQ` (5.99), with `hGd` discharged.**  Note that no (7.13) of the
tensor is left either — only the Ward bound (5.96) on its slot sums. -/
theorem momNorm_Uker_commS_event_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K Pb ζ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hP0 : 0 ≤ Pb)
    {Ξ : Set Ω} {A : Ω → LoopArg L (n + 2) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (Set.indicator Ξ A ω) b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hAP : ∀ ω ∈ Ξ, ∀ x, ‖Psum L (A ω) x‖ ≤ Pb)
    (a : LoopArg L (n + 2)) :
    momNorm P q (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (Set.indicator Ξ A ω)) a‖)
      ≤ cKerSumZero (n + 2) * (4 * K) ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * momNorm P q ψ
        + (cKerSumZero (n + 2) * (4 * K) ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2)
              * commErr L n (ellHat L ((u : ℝ) : ℂ)) u K Pb) := by
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by
    have := half_le_ellHat_real L hL hu0 hu1; linarith
  exact Gauss.momNorm_Uker_commS_le L hL hq hE σ hs0 hsu huv hv0 hv1 hκA (by linarith) hζ
    (commErr_nonneg L n hℓ0 hu1 (by linarith : (0 : ℝ) ≤ K) hP0) hψ0 hint hGM
    (hGd_commS L hL hu0 hu1 (fun i => (norm_xiOf_mSigma hE σ i).le) hK hP0 hAP) a

/-- **Term 4 of `momentDuhamelQ` (5.100), with `hGd` discharged.** -/
theorem momNorm_Uker_dot_event_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K Pb ζ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hP0 : 0 ≤ Pb)
    {Ξ : Set Ω} {A : Ω → LoopArg L (n + 2) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ (ω : Ω) (b : LoopArg L (n + 2)),
      ‖Psum L (Set.indicator Ξ A ω) (b 0) * varthetaDot L (n := n + 1) u b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hAP : ∀ ω ∈ Ξ, ∀ x, ‖Psum L (A ω) x‖ ≤ Pb)
    (a : LoopArg L (n + 2)) :
    momNorm P q (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b : LoopArg L (n + 2) =>
          Psum L (Set.indicator Ξ A ω) (b 0) * varthetaDot L (n := n + 1) u b) a‖)
      ≤ cKerSumZero (n + 2) * (4 * K) ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * momNorm P q ψ
        + (cKerSumZero (n + 2) * (4 * K) ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2)
              * dotErr n (ellHat L ((u : ℝ) : ℂ)) u K Pb) := by
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by
    have := half_le_ellHat_real L hL hu0 hu1; linarith
  exact Gauss.momNorm_Uker_PsumVarthetaDot_le L hL hq hE σ hs0 hsu huv hv0 hv1 hκA
    (by linarith) hζ (dotErr_nonneg n hℓ0 hu1 hP0) hψ0 hint hGM
    (hGd_dot L hL hu0 hu1 hK hP0 hAP) a

/-- **Term 5 of `momentDuhamelQ` (5.103), with `hGd` discharged.** -/
theorem momNorm_Uker_QQ_event_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| < 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K e ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (he : 0 ≤ e) (hδ : 0 ≤ δ)
    {Ξ : Set Ω} {A : Ω → LoopArg L ((n + 2) + (n + 2)) → ℂ} {ψ : Ω → ℝ}
    (hψ0 : ∀ ω, 0 ≤ ψ ω) (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖QQ L ((u : ℝ) : ℂ) (Set.indicator Ξ A ω) b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ ((n + 2) + (n + 2)) * ψ ω + ζ)
    (hAe : ∀ ω ∈ Ξ, ∀ c, ‖A ω c‖ ≤ e)
    (hAd : ∀ ω ∈ Ξ, FastDecay L (ellHat L ((u : ℝ) : ℂ) * K) δ (A ω))
    (a : LoopArg L ((n + 2) + (n + 2))) :
    momNorm P q (fun ω => ‖Uker L (xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (QQ L ((u : ℝ) : ℂ) (Set.indicator Ξ A ω)) a‖)
      ≤ cKerSumZero ((n + 2) + (n + 2)) * (4 * K) ^ (2 * ((n + 2) + (n + 2)))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ ((n + 2) + (n + 2)) * momNorm P q ψ
        + (cKerSumZero ((n + 2) + (n + 2)) * (4 * K) ^ (2 * ((n + 2) + (n + 2)))
              * ((1 - s) / (1 - v)) ^ ((n + 2) + (n + 2)) * ζ
          + cKerSumZeroErr ((n + 2) + (n + 2)) * (L : ℝ) ^ ((n + 2) + (n + 2))
              * ((1 - s) / (1 - v)) ^ ((n + 2) + (n + 2))
              * qqErr L (n + 1) (ellHat L ((u : ℝ) : ℂ)) K e δ) := by
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by
    have := half_le_ellHat_real L hL hu0 hu1; linarith
  exact Gauss.momNorm_Uker_QQ_le L hL hq hE σ hs0 hsu huv hv0 hv1 hκA (by linarith) hζ
    (qqErr_nonneg L (n + 1) hℓ0 (by linarith : (0 : ℝ) ≤ K) he hδ) hψ0 hint hGM
    (hGd_QQ L hL hu0 hu1 hK he hδ hAe hAd) a

end Discharged

/-! ### §11  Satisfiability

Two statements, in the two directions the project's discipline asks for.

* `RBM.FastDecayFlow.nonempty_lkGood` (§8) rules out the **empty good event**: the truncation
  of §1 is not what makes the `hGd` slots true, because the event is provably non-empty.
* `RBM.FastDecayFlow.hGd_witness` is the **positive witness**: an explicit non-zero tensor,
  at the critical scaling `1 - u = L^{-1}` where the decay length `ℓ̂_u = √L` is genuinely
  long (neither `0` nor saturated at `L`), meeting every premise of
  `RBM.FastDecayFlow.hGd_Qop_sharp` with error `δ = 0` and with `Ξ = univ`, and which `Q_u`
  fixes rather than annihilates. -/

section Witness

/-- **The decay length is genuinely long at the critical scaling.**  At `1 - u = L^{-1}`,
`ℓ̂_u = min(|1-u|^{-1/2}, L) = √L`: the minimum is *not* attained at the saturating branch
`L`, so the witness below is read at a non-degenerate radius. -/
theorem ellHat_critical (L : ℕ) (hL : 3 ≤ L) :
    ellHat L ((1 - (L : ℝ)⁻¹ : ℝ) : ℂ) = Real.sqrt L := by
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < (L : ℝ) := by linarith
  have hinv : (0 : ℝ) < (L : ℝ)⁻¹ := by positivity
  rw [ellHat_ofReal L (by linarith), show (1 : ℝ) - (1 - (L : ℝ)⁻¹) = (L : ℝ)⁻¹ by ring,
    Real.sqrt_inv, one_div, inv_inv]
  exact min_eq_left (Real.sqrt_le_self_iff.2 (Or.inr (by linarith)))

variable {Ω : Type*}

/-- **The satisfiability witness for the `hGd` slot.**

All four clauses hold simultaneously, with `Ξ = Set.univ`, input error `0`, and data
`(M, δ) = (‖κ‖, 0)` that do not depend on `N`:

1. the radius is read at the critical scaling, where `ℓ̂_u = √L` is genuinely long;
2. the tensor is **not** the zero tensor;
3. `Q_u` does not annihilate it — it fixes it, so the `hGd` below is not a statement about
   `0`;
4. `RBM.FastDecayFlow.hGd_Qop_sharp`'s conclusion holds for it.

Clause 3 is the one that matters: a version of §1 in which `Q_u ∘ 1_Ξ A` happened to be `0`
would satisfy every `hGd` slot and be worthless. -/
theorem hGd_witness (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {K : ℝ} (hK : 2 ≤ K) {κ : ℂ}
    (hκ : κ ≠ 0) (ω : Ω) :
    ellHat L ((1 - (L : ℝ)⁻¹ : ℝ) : ℂ) = Real.sqrt L
    ∧ Gauss.witTensor L n κ ≠ 0
    ∧ Qop L (((1 - (L : ℝ)⁻¹ : ℝ) : ℝ) : ℂ) (Gauss.witTensor L n κ) = Gauss.witTensor L n κ
    ∧ FastDecay L (ellHat L ((1 - (L : ℝ)⁻¹ : ℝ) : ℂ) * K) (qopErr1 L n K ‖κ‖ 0)
        (Qop L (((1 - (L : ℝ)⁻¹ : ℝ) : ℝ) : ℂ)
          (Set.indicator (Set.univ : Set Ω) (fun _ => Gauss.witTensor L n κ) ω)) := by
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < (L : ℝ) := by linarith
  have hinv1 : (L : ℝ)⁻¹ ≤ 1 / 3 := by
    rw [inv_le_comm₀ hL0 (by norm_num)]; linarith
  have hinv0 : (0 : ℝ) < (L : ℝ)⁻¹ := by positivity
  have hu0 : (0 : ℝ) ≤ 1 - (L : ℝ)⁻¹ := by linarith
  have hu1 : (1 - (L : ℝ)⁻¹ : ℝ) < 1 := by linarith
  have hell : ellHat L ((1 - (L : ℝ)⁻¹ : ℝ) : ℂ) = Real.sqrt L := ellHat_critical L hL
  have hsq1 : (1 : ℝ) ≤ Real.sqrt L := Real.one_le_sqrt.2 (by linarith)
  have hrad : (1 : ℝ) < ellHat L ((1 - (L : ℝ)⁻¹ : ℝ) : ℂ) * K := by
    rw [hell]; nlinarith
  refine ⟨hell, Gauss.witTensor_ne_zero L hL hκ, Gauss.Qop_witTensor L hL κ _, ?_⟩
  exact hGd_Qop_sharp L hL hu0 hu1 (by linarith : (1 : ℝ) ≤ K) (norm_nonneg κ) le_rfl
    (fun _ _ b => Gauss.norm_witTensor_le L b)
    (fun _ _ => Gauss.fastDecay_witTensor L hL κ hrad) ω

end Witness

/-! ### §12  End to end, for term 1 of `momentDuhamelQ`

The point of this section is that the chain really closes: §8's good event, §9's `hGd` at the
model tensor and §10's discharged estimate compose into one statement in which **nothing
about the decay is a hypothesis any more** — the only inputs left are the size envelope
`hGM`/`hAM`, the integrability, and the inclusion `Ξ ⊆ lkGood`, whose right-hand side §8
proves to hold with high probability from (5.75).

The other four terms compose the same way, with `hGd_Qop_driftF`, `hGd_commS_lkT`,
`hGd_dot_lkT`, `hGd_QQ_eeFun` in place of `fastDecay_lkT_of_mem_lkGood`; term 1 is spelled
out because it is the one T219's assembly reaches first. -/

section EndToEnd

open RBM.MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **(7.16) in moment form for `Q_u ∘ (L-K)_u`, with (7.13) discharged from (5.75).**

This is `RBM.Gauss.momNorm_Uker_Qop_le` — term 1 (and, at `u` in the interior, term 2's
shape) of `RBM.MomentDuhamel.Hyp.momentDuhamelQ` — with its `hGd` slot filled by a theorem.
The decay radius is `ℓ_u N^τ` and the decay error `N^{τ₁-D}`, i.e. exactly what
`RBM.FastDecayFlow.lkGood` delivers: `RBM.SumZeroDyn.fastDecay_Qop_le` gives away no radius,
so the `K` of the kernel estimate *is* `N^τ`. -/
theorem momNorm_Uker_Qop_lkT_le (hE : |E| ≤ 2) {q n N : ℕ} (hq : q ≠ 0)
    (σ : Fin (n + 2) → Bool) {u v : ℝ} (hs0 : 0 ≤ s N) (hsu : s N ≤ u) (hut : u ≤ t N)
    (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {τ τ₁ D M ζ : ℝ} (hτK : 1 ≤ (N : ℝ) ^ τ) (hM : 0 ≤ M)
    (hζ : 0 ≤ ζ) {Ξ : Set Ω} (hΞ : Ξ ⊆ lkGood X E s t (n + 2) τ τ₁ D N)
    {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω) (hint : Integrable (fun ω => ψ ω ^ q) B.P)
    (hGM : ∀ ω b, ‖Qop (B.L N) ((u : ℝ) : ℂ)
        (Set.indicator Ξ (fun ω => lkT X E N u ω σ) ω) b‖
      ≤ (κA * ((1 - u) * ellHat (B.L N) (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hAM : ∀ ω ∈ Ξ, ∀ b, ‖lkT X E N u ω σ b‖ ≤ M)
    (a : LoopArg (B.L N) (n + 2)) :
    momNorm B.P q (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (B.L N) ((u : ℝ) : ℂ) (Set.indicator Ξ (fun ω => lkT X E N u ω σ) ω)) a‖)
      ≤ cKerSumZero (n + 2) * ((N : ℝ) ^ τ) ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat (B.L N) (v : ℂ)))⁻¹ ^ (n + 2) * momNorm B.P q ψ
        + (cKerSumZero (n + 2) * ((N : ℝ) ^ τ) ^ (2 * (n + 2))
              * ((1 - s N) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2)
              * ((1 - s N) / (1 - v)) ^ (n + 2)
              * qopErr1 (B.L N) n ((N : ℝ) ^ τ) M ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D))) := by
  have := B.isProbabilityMeasure
  exact momNorm_Uker_Qop_event_le (B.L N) (B.three_le_L N) hq hE σ hs0 hsu huv hv0 hv1 hκA
    hτK hM hζ (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hψ0 hint hGM hAM
    (fun ω hω => fastDecay_lkT_of_mem_lkGood hsu hut (hΞ hω) σ) a

end EndToEnd

end RBM.FastDecayFlow
