/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Q716
import RBM1D.Hierarchy.DriftDef

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
  show (0 : LoopArg L (n + 1) → ℂ) b - Psum L (0 : LoopArg L (n + 1) → ℂ) (b 0)
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
  show Qop L t (fun a' => (0 : LoopArg L ((k + 1) + m') → ℂ) (Fin.append a' (spl2 L c)))
      (spl1 L c) = 0
  have h : (fun a' => (0 : LoopArg L ((k + 1) + m') → ℂ) (Fin.append a' (spl2 L c)))
      = (0 : LoopArg L (k + 1) → ℂ) := rfl
  rw [h, Qop_zero]
  rfl

theorem Q2_zero {m k : ℕ} (t : ℂ) :
    Q2 L (m := m) (k := k) t (0 : LoopArg L (m + (k + 1)) → ℂ) = 0 := by
  funext c
  show Qop L t (fun b' => (0 : LoopArg L (m + (k + 1)) → ℂ) (Fin.append (spl1 L c) b'))
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

/-! ### §4  The decay of the unprojected tensors along the flow

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
  show ‖eeArg d N z M σ c‖ ≤ _
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

end RBM.FastDecayFlow
