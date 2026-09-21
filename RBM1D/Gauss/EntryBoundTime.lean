/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDENetClose
import RBM1D.Green.EntryBoundFloor

/-!
# (4.2) and (4.3) with the time inside the index set — T107, T183

`RBM1D/Gauss/Lemma41FlowGauss.lean` (T108) carries **(4.2) along the flow** as the hypothesis
`RBM.Gauss.EntryBoundFlow`: `RBM.entry_bound_stochDom` with `RBM.TimeIcc s t N` added to the
index set, so that the matrix `H_u` and the spectral parameter `z_u` follow the index.  This
file discharges it.

## What is actually true

The literal `RBM.Gauss.EntryBoundFlow` is **not** what the time-uniform large deviation
estimates produce.  T148 (`RBM1D/Gauss/LDENetClose.lean`) proved that their unfloored,
time-uniform forms are equivalent to a polynomial lower bound on their own controls, and those
controls are exponentially small in the band distance.  What is available unconditionally is the
same domination with an **additive floor** `N^{-B}`, for every `B ≥ 0`
(`RBM.Gauss.stochDom_ldeRow_flow_floor`, `RBM.Gauss.stochDom_ldeCol_flow_floor`).

So the deliverable here is `RBM.Gauss.EntryBoundFlow'`, which is `RBM.Gauss.EntryBoundFlow` with
`+ fl N` in the control, and `RBM.Gauss.entryBoundFlow_floor`, which proves it with
`fl N = 2 N^{-B}` and **no large deviation hypothesis at all**.  The deterministic kernel is
T166's `RBM.norm_sq_green_le_blk_floor` (`RBM1D/Green/EntryBoundFloor.lean`); the index widening
that T166 wrote for (4.3) — `RBM.diag_bound_stochDom_floor_idx` — had no (4.2) counterpart
there, so `RBM.Gauss.entry_bound_stochDom_floor_idx` was written here.  **T184 sank it** into
`RBM1D/Green/EntryBoundFloor.lean` beside its diagonal twin, where it belongs; the name
`RBM.Gauss.entry_bound_stochDom_floor_idx` survives as an `export` of the very same constant.

## Why the floor costs nothing

`RBM.Gauss.EntryBoundFlow`'s only consumer, `RBM.Gauss.stochDom_indicator_offdiag_flow`,
immediately composes it with `RBM.Gauss.stochDom_indicator_entryControl_flow`, whose control
`Φ(N,u) + W⁻¹` carries an **unconditional** `W⁻¹`.  Since `3 W ≤ W L ≤ N` (`RBM.Dims.dim` and
`3 ≤ L`), the floor at `B = 1` already satisfies `2 N⁻¹ ≤ W⁻¹`, and
`RBM.Gauss.stochDom_indicator_add_const` absorbs it.  Consequently the four downstream
statements are reproved **verbatim**, only with the hypothesis weakened:

| unprimed (hypothesis `EntryBoundFlow`) | primed (hypothesis `EntryBoundFlow'`) |
| --- | --- |
| `RBM.Gauss.stochDom_indicator_offdiag_flow` | `RBM.Gauss.stochDom_indicator_offdiag_flow'` |
| `RBM.Gauss.stochDom_indicator_llMax_sq_flow` | `RBM.Gauss.stochDom_indicator_llMax_sq_flow'` |
| `RBM.Gauss.lemma41Flow` | `RBM.Gauss.lemma41Flow'` |
| `RBM.Gauss.step1Hyp_gauss_of_scale` | `RBM.Gauss.step1Hyp_gauss_of_scale'` |

Nothing in `RBM1D/Gauss/Lemma41FlowGauss.lean`, `RBM1D/Gauss/Step1Hyp.lean`,
`RBM1D/Green/EntryBound.lean` or `RBM1D/Green/EntryBoundFloor.lean` is changed; every
declaration here is new.

## Main results

* `RBM.Gauss.entry_bound_stochDom_floor_idx` — (4.2) floored, with the time in the index set;
  since T184 an `export` of `RBM.entry_bound_stochDom_floor_idx`.
* `RBM.Gauss.entryBoundFlow_floor` — **(4.2) along the flow**, the T107 deliverable.
* `RBM.Gauss.lemma41Flow_of_diagBoundFlow` — `RBM.Step1.Lemma41Flow` with (4.2) discharged.
* `RBM.Gauss.step1Hyp_gauss_of_scale'` — `RBM.Step1.Hyp` with (4.2) discharged; its two extra
  regime inputs (`N^{-1} ≤ η_{t_N}` and `δ_N ≤ N^{-c/6}`) are both consequences of
  `RBM.Step1.step1`'s own `N^c ≤ W ℓ_t η_t`, so nothing is added to the hypothesis list.

## (4.3) — T183

The second half of the file does the same for `RBM.Gauss.DiagBoundFlow`, which is what T107 left
behind.  T166 had already written the floored, time-indexed deterministic chain
`RBM.diag_bound_stochDom_floor_idx` (`RBM1D/Green/EntryBoundFloor.lean`) and the third large
deviation input `RBM.Gauss.stochDom_ldeQuad_flow_floor`, so only the wiring was missing:

* the fourth input `hLdiag` existed only at a fixed time (`RBM.Gauss.stochDom_normSq_Hflow_diag`,
  T92).  Widening its index set is free — `‖H_{u,ii}‖² = u ‖X_{ii}‖²` is monotone in `u` and the
  control `S_{ii}` does not depend on `u` — and is done by
  `RBM.Gauss.stochDom_normSq_Hflow_diag_idx`;
* the floor is absorbed at `B = 1` by the same `RBM.Gauss.stochDom_indicator_add_const` that
  T107 wrote for (4.2), against the **unconditional** `W⁻¹` in
  `RBM.Gauss.stochDom_indicator_Lmax_flow`'s control;
* `hδ` was already required by `RBM.entry_bound_stochDom`, so it is not a new burden.

| unprimed (hypothesis `DiagBoundFlow`) | primed (hypothesis `DiagBoundFlow'`) |
| --- | --- |
| `RBM.Gauss.stochDom_indicator_diag_flow` | `RBM.Gauss.stochDom_indicator_diag_flow'` |
| `RBM.Gauss.lemma41Flow` | `RBM.Gauss.lemma41Flow''` |
| `RBM.Gauss.lemma41Flow_of_diagBoundFlow` | `RBM.Gauss.lemma41Flow_gauss` |
| `RBM.Gauss.step1Hyp_gauss_of_scale'` | `RBM.Gauss.step1Hyp_gauss_of_scale''` |

* `RBM.Gauss.DiagBoundFlow'` — (4.3) along the flow with an additive floor.
* `RBM.Gauss.diagBoundFlow_floor` — **(4.3) along the flow**, the T183 deliverable.
* `RBM.Gauss.lemma41Flow_gauss` — `RBM.Step1.Lemma41Flow` with (4.2) *and* (4.3) discharged.
* `RBM.Gauss.step1Hyp_gauss_of_scale''` — `RBM.Step1.Hyp` under word for word the hypotheses of
  `RBM.Gauss.step1Hyp_gauss_of_scale`, minus both `RBM.Gauss.EntryBoundFlow` and
  `RBM.Gauss.DiagBoundFlow`.  (4.3)'s kernel wants the spectral gap as `|E| ≤ 2 - κ` with
  `0 < κ ≤ 1`; `κ` is capped at `1` internally, which only weakens the hypothesis, so nothing is
  added to the list.
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset

/-! ### The (4.2) kernel with the time in the index set — sunk by T184

`RBM.Gauss.entry_bound_stochDom_floor_idx` was written here (T107) because T166's index widening
for (4.3), `RBM.diag_bound_stochDom_floor_idx`, had no (4.2) counterpart in
`RBM1D/Green/EntryBoundFloor.lean`.  It is a pure `RBM.StochDom.of_det` call on the
deterministic kernel `RBM.norm_sq_green_le_blk_floor`, with nothing in it that belongs to the
Gaussian flow, so T184 sank it beside its diagonal twin as
`RBM.entry_bound_stochDom_floor_idx`.

The old name is kept as a re-export, so it denotes the **same constant**: every use site, here
and downstream, is unaffected. -/

export _root_.RBM (entry_bound_stochDom_floor_idx)

section Flow

variable {d : Dims} {E : ℝ} {s t : ℕ → ℝ}

/-- **`RBM.Gauss.EntryBoundFlow` with an additive floor `fl N` in the control.**

The literal `RBM.Gauss.EntryBoundFlow` is not what the time-uniform large deviation estimates
produce: T148 proved that their unfloored forms are equivalent to a polynomial lower bound on
their own controls, which fails in the band-distance tails.  What is available unconditionally
is the same statement with an additive floor, and that is this definition. -/
def EntryBoundFlow' (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (fl : ℕ → ℝ) : Prop :=
  StochDom (P d)
    (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ))
          (mE E) (flowDelta d E t) N).indicator
        (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2.1.1 p.2.1.2‖ ^ 2) ω)
    (fun N p ω =>
      (∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
          Lre (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) (p.2.1.2.1 + b) (p.2.1.1.1 + a))
        + (if p.2.1.1.1 - p.2.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        + fl N)

/-- `RBM.Gauss.EntryBoundFlow` is the floor-free case of `RBM.Gauss.EntryBoundFlow'`. -/
theorem EntryBoundFlow'.of_entryBoundFlow (h : EntryBoundFlow d E s t) {fl : ℕ → ℝ}
    (hfl0 : ∀ N, 0 ≤ fl N) : EntryBoundFlow' d E s t fl := by
  refine StochDom.control_mono h fun N p ω => ?_
  have := hfl0 N
  linarith

/-- **(4.2) along the flow, with a floor — T107.**

`RBM.Gauss.EntryBoundFlow'` holds for the Gaussian flow with **no large deviation hypothesis**:
the two inputs are T148/T160's floored, time-uniform row and column estimates
`RBM.Gauss.stochDom_ldeRow_flow_floor` and `RBM.Gauss.stochDom_ldeCol_flow_floor`, and the
deterministic kernel is T166's `RBM.norm_sq_green_le_blk_floor`.

The remaining hypotheses are the regime: `|E| < 2`, `0 ≤ s_N ≤ t_N < 1`, the polynomial lower
bound `N^{-K} ≤ η_{t_N}` on the spectral window, and the polynomial decay of the threshold
`δ_N = RBM.Gauss.flowDelta d E t N` of (4.1). -/
theorem entryBoundFlow_floor (d : Dims) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (t N)) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, flowDelta d E t N ≤ (N : ℝ) ^ (-c₀)) {B : ℝ} (hB : 0 ≤ B) :
    EntryBoundFlow' d E s t (fun N => 2 * (N : ℝ) ^ (-B)) := by
  have hδ0 : ∀ N, 0 ≤ flowDelta d E t N := by
    intro N
    have ht0 : (0 : ℝ) ≤ t N := le_trans (hs0 N) (hst N)
    have hpos : 0 < (band d).scale E N (t N) := (band d).scale_pos' hE N ht0 (ht1 N)
    exact Real.rpow_nonneg (by positivity) _
  exact entry_bound_stochDom_floor_idx (P d) (L := d.L) (W := d.W)
    (U := fun N => RBM.TimeIcc s t N) d.three_le_L
    (fun N u ω => Hflow d N u ω) (fun N u => (u : ℝ)) (zt E)
    (fun N u ω => Hflow_isHermitian d N u ω)
    (fun N u => zt_im_ne_zero_of_lt_one hE (lt_of_le_of_lt u.2.2 (ht1 N)))
    (norm_mE (le_of_lt hE)) hδ0 hc₀ hδ
    (fun N => Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (stochDom_ldeRow_flow_floor d hE hs0 hst ht1 hK hη hB)
    (stochDom_ldeCol_flow_floor d hE hs0 hst ht1 hK hη hB)

/-! ### Absorbing the floor at the consumer -/

section Absorb

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {U : ℕ → Type*}

/-- **A constant added inside an indicator is absorbed by a control that dominates it.**

If `1_A f ≺ ζ` and the constant `c_N` is eventually at most `ζ` itself, then
`1_A (f + c_N) ≺ ζ`: the factor `N^τ` in the definition of `≺` has room to spare. -/
theorem stochDom_indicator_add_const {A : ∀ N, U N → Set Ω} {f ζ : ∀ N, U N → Ω → ℝ}
    {c : ℕ → ℝ} (h : StochDom P (fun N u ω => (A N u).indicator (f N u) ω) ζ)
    (hζ0 : ∀ N u ω, 0 ≤ ζ N u ω)
    (hc : ∀ᶠ N : ℕ in atTop, ∀ u ω, c N ≤ ζ N u ω) :
    StochDom P (fun N u ω => (A N u).indicator (fun ω => f N u ω + c N) ω) ζ := by
  refine StochDom.of_subset h fun τ hτ => ⟨τ / 2, by linarith, ?_⟩
  filter_upwards [hc, eventually_le_rpow 2 (show (0 : ℝ) < τ / 2 by linarith),
    Filter.eventually_ge_atTop 1] with N hcN h2 hN1
  rintro ω ⟨u, hu⟩
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hsplit : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hζ := hζ0 N u ω
  have hcu := hcN u ω
  refine ⟨u, ?_⟩
  show (N : ℝ) ^ (τ / 2) * ζ N u ω < (A N u).indicator (f N u) ω
  replace hu : (N : ℝ) ^ τ * ζ N u ω < (A N u).indicator (fun ω => f N u ω + c N) ω := hu
  by_cases hmem : ω ∈ A N u
  · rw [Set.indicator_of_mem hmem] at hu ⊢
    rw [hsplit] at hu
    set x : ℝ := (N : ℝ) ^ (τ / 2) with hx
    have hpos : (0 : ℝ) ≤ x * x - x - 1 := by nlinarith
    nlinarith [mul_nonneg hζ hpos]
  · rw [Set.indicator_of_notMem hmem] at hu
    exact absurd hu (not_lt.2
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) τ) hζ))

end Absorb

section Consumer

variable {d : Dims} {E : ℝ} {s t : ℕ → ℝ} {Φ : ∀ N, RBM.TimeIcc s t N → ℝ}

/-- `2 N⁻¹ ≤ W⁻¹` eventually: `3 W ≤ W L ≤ N` by `RBM.Dims.dim` and `3 ≤ L`. -/
theorem eventually_two_rpow_neg_one_le_W_inv (d : Dims) :
    ∀ᶠ N : ℕ in atTop, 2 * (N : ℝ) ^ (-(1 : ℝ)) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by
  filter_upwards [d.dim] with N hdim
  have hW : 0 < d.W N := d.W_pos N
  have hL : 3 ≤ d.L N := d.three_le_L N
  have hWN : 3 * d.W N ≤ N := by
    have h3 : 3 * d.W N ≤ d.L N * d.W N := Nat.mul_le_mul hL (le_refl (d.W N))
    have hcm : d.L N * d.W N = d.W N * d.L N := Nat.mul_comm _ _
    have hd := hdim.1
    omega
  have hW' : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast hW
  have hN' : (0 : ℝ) < (N : ℝ) := by
    have : 0 < 3 * d.W N := by omega
    have : 0 < N := by omega
    exact_mod_cast this
  have hWN' : 3 * (d.W N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hWN
  have he : (N : ℝ) ^ (-(1 : ℝ)) = (N : ℝ)⁻¹ := by
    rw [Real.rpow_neg hN'.le, Real.rpow_one]
  rw [he, inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hN' hW']
  linarith

/-- **The off-diagonal half of Lemma 4.1 along the flow, from the *floored* (4.2).**

The conclusion is word for word `RBM.Gauss.stochDom_indicator_offdiag_flow`'s; only the
hypothesis is weakened, from `RBM.Gauss.EntryBoundFlow` to `RBM.Gauss.EntryBoundFlow'`.  The
floor costs nothing because the control on the right already carries an **unconditional** `W⁻¹`
summand, while the floor may be taken as small as one likes. -/
theorem stochDom_indicator_offdiag_flow' (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) {fl : ℕ → ℝ}
    (hflW : ∀ᶠ N : ℕ in atTop, fl N ≤ ((d.W N : ℕ) : ℝ)⁻¹)
    (hEntry : EntryBoundFlow' d E s t fl) (hΦ0 : ∀ N u, 0 ≤ Φ N u)
    (hΦ : LoopHypFlow d E s t Φ) :
    StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2.1.1 p.2.1.2‖ ^ 2) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) := by
  have h1 : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2.1.1 p.2.1.2‖ ^ 2) ω)
      (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
        ((∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
            Lre (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) (p.2.1.2.1 + b) (p.2.1.1.1 + a))
          + if p.2.1.1.1 - p.2.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
          + fl N) :=
    stochDom_mono_left hEntry fun N p ω =>
      Set.indicator_le_indicator_of_subset (goodEv_subset_goodSet_flow hE hs0 ht1 N p.1)
        (fun _ => by positivity) ω
  have h2 := stochDom_indicator_add_const
    (A := fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) =>
      Step1.goodEv (sample d) E N (p.1 : ℝ))
    (c := fl) (stochDom_indicator_entryControl_flow hΦ0 hΦ)
    (fun N p _ => by
      have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
      linarith [hΦ0 N p.1])
    (by
      filter_upwards [hflW] with N hN p _
      linarith [hΦ0 N p.1])
  refine stochDom_trans_indicator_idx h1 h2 (fun N p _ => ?_)
  have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  linarith [hΦ0 N p.1]

/-- **`RBM.Gauss.stochDom_indicator_llMax_sq_flow`, with its two inputs abstracted.**

The proof of `RBM.Gauss.stochDom_indicator_llMax_sq_flow` only ever uses (4.2) and (4.3) along
the flow through their conclusions, so it applies verbatim to the primed off-diagonal bound
`RBM.Gauss.stochDom_indicator_offdiag_flow'` as well. -/
theorem stochDom_indicator_llMax_sq_flow_of (hΦ0 : ∀ N u, 0 ≤ Φ N u)
    (hoff : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2.1.1 p.2.1.2‖ ^ 2) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹))
    (hdg : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2 p.2 - mE E‖ ^ 2) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹)) :
    StochDom (P d)
      (fun N (u : RBM.TimeIcc s t N) ω =>
        (Step1.goodEv (sample d) E N (u : ℝ)).indicator
          (fun ω => Step1.llMax (sample d) E N (u : ℝ) ω ^ 2) ω)
      (fun N u _ => Φ N u + ((d.W N : ℕ) : ℝ)⁻¹) := by
  refine StochDom.of_subset_union hoff hdg fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards with N
  intro ω hω
  simp only [badSet, Set.mem_ofPred_eq] at hω
  obtain ⟨u, hlt⟩ := hω
  have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  have hC : (0 : ℝ) ≤ (N : ℝ) ^ τ * (Φ N u + ((d.W N : ℕ) : ℝ)⁻¹) := by
    have h1 : (0 : ℝ) ≤ Φ N u + ((d.W N : ℕ) : ℝ)⁻¹ := by linarith [hΦ0 N u]
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) τ
    positivity
  by_cases hmem : ω ∈ Step1.goodEv (sample d) E N (u : ℝ)
  · rw [Set.indicator_of_mem hmem] at hlt
    set c : ℝ := (N : ℝ) ^ τ * (Φ N u + ((d.W N : ℕ) : ℝ)⁻¹) with hc
    set r : ℝ := Real.sqrt c with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg c
    have hr2 : r ^ 2 = c := Real.sq_sqrt hC
    have hex : ∃ ij : (band d).Idx N × (band d).Idx N,
        r < (sample d).llErr E N (u : ℝ) ω ij := by
      by_contra hcon
      push Not at hcon
      have : Step1.llMax (sample d) E N (u : ℝ) ω ≤ r := Step1.llMax_le _ hcon
      have hm0 : 0 ≤ Step1.llMax (sample d) E N (u : ℝ) ω :=
        Step1.llMax_nonneg _ N (u : ℝ) ω
      nlinarith [hlt, hr2, this, hm0]
    obtain ⟨ij, hij⟩ := hex
    have hij0 : 0 ≤ (sample d).llErr E N (u : ℝ) ω ij := norm_nonneg _
    have hsq : c < (sample d).llErr E N (u : ℝ) ω ij ^ 2 := by nlinarith [hij, hr0, hr2, hij0]
    rw [(sample d).llErr_eq N (u : ℝ) ω ij] at hsq
    by_cases hne : ij.1 = ij.2
    · refine Set.mem_union_right _ ⟨(u, ij.2), ?_⟩
      show c < (Step1.goodEv (sample d) E N (u : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) ij.2 ij.2 - mE E‖ ^ 2) ω
      rw [Set.indicator_of_mem hmem]
      rw [hne] at hsq
      simp only [↓reduceIte] at hsq
      exact hsq
    · refine Set.mem_union_left _ ⟨(u, ⟨(ij.1, ij.2), hne⟩), ?_⟩
      show c < (Step1.goodEv (sample d) E N (u : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) ij.1 ij.2‖ ^ 2) ω
      rw [Set.indicator_of_mem hmem]
      simp only [hne, ↓reduceIte, sub_zero] at hsq
      exact hsq
  · rw [Set.indicator_of_notMem hmem] at hlt
    exact absurd hlt (not_lt.2 hC)

/-- **Lemma 4.1 along the flow, from the *floored* (4.2)** — the conclusion is word for word
`RBM.Gauss.stochDom_indicator_llMax_sq_flow`'s. -/
theorem stochDom_indicator_llMax_sq_flow' (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) {fl : ℕ → ℝ}
    (hflW : ∀ᶠ N : ℕ in atTop, fl N ≤ ((d.W N : ℕ) : ℝ)⁻¹)
    (hEntry : EntryBoundFlow' d E s t fl) (hDiag : DiagBoundFlow d E s t)
    (hΦ0 : ∀ N u, 0 ≤ Φ N u) (hΦ : LoopHypFlow d E s t Φ) :
    StochDom (P d)
      (fun N (u : RBM.TimeIcc s t N) ω =>
        (Step1.goodEv (sample d) E N (u : ℝ)).indicator
          (fun ω => Step1.llMax (sample d) E N (u : ℝ) ω ^ 2) ω)
      (fun N u _ => Φ N u + ((d.W N : ℕ) : ℝ)⁻¹) :=
  stochDom_indicator_llMax_sq_flow_of hΦ0
    (stochDom_indicator_offdiag_flow' hE hs0 ht1 hflW hEntry hΦ0 hΦ)
    (stochDom_indicator_diag_flow hE hs0 ht1 hDiag hΦ0 hΦ)

/-- **`RBM.Step1.Lemma41Flow` from the *floored* (4.2)** — the conclusion is word for word
`RBM.Gauss.lemma41Flow`'s. -/
theorem lemma41Flow' (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {fl : ℕ → ℝ}
    (hflW : ∀ᶠ N : ℕ in atTop, fl N ≤ ((d.W N : ℕ) : ℝ)⁻¹)
    (hEntry : EntryBoundFlow' d E s t fl) (hDiag : DiagBoundFlow d E s t) :
    Step1.Lemma41Flow (sample d) E s t := by
  intro Ψ hΨ0 hloop
  exact stochDom_indicator_llMax_sq_flow' hE hs0 ht1 hflW hEntry hDiag hΨ0
    (loopHypFlow_iff.2 hloop)

/-- **`RBM.Step1.Lemma41Flow` with (4.2) discharged — the deliverable of T107.**

`RBM.Gauss.lemma41Flow` carried two hypotheses, `RBM.Gauss.EntryBoundFlow` and
`RBM.Gauss.DiagBoundFlow`.  The first is now a theorem (in its floored form, which is all the
consumer needs): the only remaining hypotheses besides `RBM.Gauss.DiagBoundFlow` are the
regime. -/
theorem lemma41Flow_of_diagBoundFlow (d : Dims) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (t N)) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, flowDelta d E t N ≤ (N : ℝ) ^ (-c₀))
    (hDiag : DiagBoundFlow d E s t) :
    Step1.Lemma41Flow (sample d) E s t :=
  lemma41Flow' hE hs0 ht1 (eventually_two_rpow_neg_one_le_W_inv d)
    (entryBoundFlow_floor d hE hs0 hst ht1 hK hη hc₀ hδ zero_le_one) hDiag

/-! ### The regime inputs from `RBM.Step1.step1`'s own `N^c ≤ W ℓ_t η_t` -/

/-- **`N^{-1} ≤ η_{t_N}`** from `N^c ≤ W ℓ_{t_N} η_{t_N}`: the first half of
`RBM.Gauss.rpow_neg_one_le_one_sub_of_scale_ge`, stopped one step earlier. -/
theorem rpow_neg_one_le_etaT_of_scale_ge (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N)) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E (t N) := by
  filter_upwards [hreg, (band d).dim, Filter.eventually_ge_atTop 1] with N hregN hdim hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hW : (0 : ℝ) < (band d).W N := by exact_mod_cast (band d).W_pos N
  have hη : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
  have hℓL : (band d).ell N (t N) ≤ (((band d).L N : ℕ) : ℝ) := min_le_right _ _
  have hWL : (((band d).W N : ℕ) : ℝ) * (((band d).L N : ℕ) : ℝ) ≤ N := by exact_mod_cast hdim.1
  have hscale : (band d).scale E N (t N) ≤ (N : ℝ) * etaT E (t N) := by
    rw [Band.scale]
    calc (((band d).W N : ℕ) : ℝ) * (band d).ell N (t N) * etaT E (t N)
        ≤ (((band d).W N : ℕ) : ℝ) * (((band d).L N : ℕ) : ℝ) * etaT E (t N) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓL hW.le) hη.le
      _ ≤ (N : ℝ) * etaT E (t N) := mul_le_mul_of_nonneg_right hWL hη.le
  have hkey : (N : ℝ) ^ (c - 1) ≤ etaT E (t N) := by
    have h1 := hregN.trans hscale
    have he : (N : ℝ) ^ (c - 1) = (N : ℝ) ^ c / (N : ℝ) := by
      rw [show c - 1 = c + -(1 : ℝ) by ring, Real.rpow_add hN0, Real.rpow_neg_one,
        div_eq_mul_inv]
    rw [he, div_le_iff₀ hN0]
    linarith
  exact le_trans (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)) hkey

/-- **The threshold `δ_N` of (4.1) decays polynomially** as soon as `N^c ≤ W ℓ_{t_N} η_{t_N}`:
`δ_N = (W ℓ_{t_N} η_{t_N})^{-1/6} ≤ N^{-c/6}`. -/
theorem flowDelta_le_rpow_neg (d : Dims) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N)) :
    ∀ᶠ N : ℕ in atTop, flowDelta d E t N ≤ (N : ℝ) ^ (-(c / 6)) := by
  filter_upwards [hreg, Filter.eventually_ge_atTop 1] with N hregN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNc : (0 : ℝ) < (N : ℝ) ^ c := Real.rpow_pos_of_pos hN0 c
  have hinv : ((band d).scale E N (t N))⁻¹ ≤ ((N : ℝ) ^ c)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hNc hregN
  have hlast : (((N : ℝ) ^ c)⁻¹) ^ ((1 : ℝ) / 6) = (N : ℝ) ^ (-(c / 6)) := by
    rw [← Real.rpow_neg hN0.le, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  have hsc : 0 < (band d).scale E N (t N) := lt_of_lt_of_le hNc hregN
  show ((band d).scale E N (t N))⁻¹ ^ ((1 : ℝ) / 6) ≤ (N : ℝ) ^ (-(c / 6))
  rw [← hlast]
  exact Real.rpow_le_rpow (le_of_lt (inv_pos.2 hsc)) hinv (by norm_num)

/-- **`RBM.Step1.Hyp` for the Gaussian model with (4.2) discharged.**

Word for word the conclusion of `RBM.Gauss.step1Hyp_gauss_of_scale`, under word for word its
hypotheses **minus `RBM.Gauss.EntryBoundFlow`**: the floored (4.2) of
`RBM.Gauss.entryBoundFlow_floor` replaces it, and its two regime inputs — `N^{-1} ≤ η_{t_N}`
and `δ_N ≤ N^{-c/6}` — are both consequences of `RBM.Step1.step1`'s own `N^c ≤ W ℓ_t η_t`.  So
the floor costs no hypothesis at all here. -/
theorem step1Hyp_gauss_of_scale' (d : Dims) {κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N))
    (hDiag : DiagBoundFlow d E s t) :
    Step1.Hyp (sample d) E s t := by
  have hE2 : |E| < 2 := by linarith
  have hS : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
      LoopScaling (sample d) E t₁ t₂ := fun t₁ t₂ h1 h12 _ =>
    loopScaling_gauss (d := d) (fun N => lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (h1 N)) h12
  exact
    { scaling := hS
      lift := fun n hn => netLift_gauss d hE2 hs0 hst ht1 one_pos
        (rpow_neg_one_le_one_sub_of_scale_ge (band d) hE2 ht1 hc0 hreg) hn
        (fun u => eq58_seq_thr (sample d) hκ hE (C₀ := 3) (by norm_num) hB hs0 hst ht1 hcond
          hS u hn)
      lemma41 := lemma41Flow' hE2 hs0 ht1 (eventually_two_rpow_neg_one_le_W_inv d)
        (entryBoundFlow_floor d hE2 hs0 hst ht1 zero_le_one
          (rpow_neg_one_le_etaT_of_scale_ge d hE2 ht1 hc0 hreg)
          (by linarith : (0 : ℝ) < c / 6) (flowDelta_le_rpow_neg d hreg) zero_le_one)
        hDiag
      cont := cont_gauss d hE2 (fun N => (hs0 N)) ht1 }

/-! ### (4.3) along the flow: `RBM.Gauss.DiagBoundFlow'` — T183 -/

/-- **`RBM.Gauss.DiagBoundFlow` with an additive floor `fl N` in the control.**

Exactly as for (4.2): the literal `RBM.Gauss.DiagBoundFlow` is not what the time-uniform large
deviation estimates produce (T148 showed their unfloored forms are equivalent to a polynomial
lower bound on their own controls), while the floored form is unconditional.  This is the (4.3)
analogue of `RBM.Gauss.EntryBoundFlow'`. -/
def DiagBoundFlow' (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (fl : ℕ → ℝ) : Prop :=
  StochDom (P d)
    (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ))
          (mE E) (flowDelta d E t) N).indicator
        (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2 p.2 - mE E‖ ^ 2) ω)
    (fun N p ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) + fl N)

/-- `RBM.Gauss.DiagBoundFlow` is the floor-free case of `RBM.Gauss.DiagBoundFlow'`. -/
theorem DiagBoundFlow'.of_diagBoundFlow (h : DiagBoundFlow d E s t) {fl : ℕ → ℝ}
    (hfl0 : ∀ N, 0 ≤ fl N) : DiagBoundFlow' d E s t fl := by
  refine StochDom.control_mono h fun N p ω => ?_
  have := hfl0 N
  linarith

/-- **`hLdiag` with the time inside the index set.**

`RBM.Gauss.stochDom_normSq_Hflow_diag` (T92) fixes the time `u`.  Widening the index set costs
nothing: `‖H_{u,ii}‖² = u ‖X_{ii}‖²` is monotone in `u`, so for `u ≤ 1` the failure event at any
time is contained in the failure event at `u = 1`, and the control `S_{ii}` does not depend on
the time at all. -/
theorem stochDom_normSq_Hflow_diag_idx {U : ℕ → Type*} (uf : ∀ N, U N → ℝ)
    (hu0 : ∀ N q, 0 ≤ uf N q) (hu1 : ∀ N q, uf N q ≤ 1) :
    StochDom (P d)
      (fun N (q : U N × BIdx d.L d.W N) ω => ‖Hflow d N (uf N q.1) ω q.2 q.2‖ ^ 2)
      (fun N (q : U N × BIdx d.L d.W N) _ => Sblk (d.L N) (d.W N) q.2 q.2) := by
  have h := stochDom_normSq_Hflow_diag (d := d) (u := 1) zero_le_one
  refine StochDom.of_subset_union h h fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards with N
  rintro ω ⟨q, hq⟩
  refine Set.mem_union_left _ ⟨q.2, ?_⟩
  have e1 : ‖Hflow d N (uf N q.1) ω q.2 q.2‖ ^ 2
      = uf N q.1 * (ω ⟨N, q.2, q.2, true⟩) ^ 2 := normSq_Hflow_diag (hu0 N q.1) ω q.2
  have e2 : ‖Hflow d N 1 ω q.2 q.2‖ ^ 2
      = 1 * (ω ⟨N, q.2, q.2, true⟩) ^ 2 := normSq_Hflow_diag zero_le_one ω q.2
  have hsq : (0 : ℝ) ≤ (ω ⟨N, q.2, q.2, true⟩) ^ 2 := sq_nonneg _
  have hmono : uf N q.1 * (ω ⟨N, q.2, q.2, true⟩) ^ 2 ≤ 1 * (ω ⟨N, q.2, q.2, true⟩) ^ 2 :=
    mul_le_mul_of_nonneg_right (hu1 N q.1) hsq
  show (N : ℝ) ^ τ * Sblk (d.L N) (d.W N) q.2 q.2 < ‖Hflow d N 1 ω q.2 q.2‖ ^ 2
  rw [e2]
  have hq' : (N : ℝ) ^ τ * Sblk (d.L N) (d.W N) q.2 q.2
      < ‖Hflow d N (uf N q.1) ω q.2 q.2‖ ^ 2 := hq
  rw [e1] at hq'
  linarith

/-- **(4.3) along the flow, with a floor — T183.**

`RBM.Gauss.DiagBoundFlow'` holds for the Gaussian flow with **no large deviation hypothesis**:
the three floored, time-uniform large deviation inputs are
`RBM.Gauss.stochDom_ldeRow_flow_floor`, `RBM.Gauss.stochDom_ldeCol_flow_floor` (T148) and
`RBM.Gauss.stochDom_ldeQuad_flow_floor` (T166), `hLdiag` is
`RBM.Gauss.stochDom_normSq_Hflow_diag_idx`, and the deterministic kernel is T166's
`RBM.norm_sq_green_diag_sub_le_blk_floor` through `RBM.diag_bound_stochDom_floor_idx`.

The remaining hypotheses are the regime, and they are the same batch as for (4.2) except that
(4.3)'s kernel needs the spectral gap in the form `|E| ≤ 2 - κ` with `0 < κ ≤ 1`. -/
theorem diagBoundFlow_floor (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (t N)) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, flowDelta d E t N ≤ (N : ℝ) ^ (-c₀)) {B : ℝ} (hB : 0 ≤ B) :
    DiagBoundFlow' d E s t (fun N => (N : ℝ) ^ (-B)) := by
  have hE2 : |E| < 2 := by linarith
  have hδ0 : ∀ N, 0 ≤ flowDelta d E t N := by
    intro N
    have ht0 : (0 : ℝ) ≤ t N := le_trans (hs0 N) (hst N)
    have hpos : 0 < (band d).scale E N (t N) := (band d).scale_pos' hE2 N ht0 (ht1 N)
    exact Real.rpow_nonneg (by positivity) _
  exact diag_bound_stochDom_floor_idx (P d) (L := d.L) (W := d.W)
    (U := fun N => RBM.TimeIcc s t N) d.three_le_L
    (fun N u ω => Hflow d N u ω) (fun N u => (u : ℝ))
    (fun N u ω => Hflow_isHermitian d N u ω) hκ0 hκ1 hE
    (fun N u => le_trans (hs0 N) u.2.1)
    (fun N u => lt_of_le_of_lt u.2.2 (ht1 N))
    hδ0 hc₀ hδ (fun N => Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (stochDom_ldeRow_flow_floor d hE2 hs0 hst ht1 hK hη hB)
    (stochDom_ldeCol_flow_floor d hE2 hs0 hst ht1 hK hη hB)
    (stochDom_ldeQuad_flow_floor d hE2 hs0 hst ht1 hK hη hB)
    (stochDom_normSq_Hflow_diag_idx (d := d) (fun N (u : RBM.TimeIcc s t N) => (u : ℝ))
      (fun N u => le_trans (hs0 N) u.2.1)
      (fun N u => le_of_lt (lt_of_le_of_lt u.2.2 (ht1 N))))

/-! ### Absorbing the (4.3) floor at the consumer -/

/-- `N⁻¹ ≤ W⁻¹` eventually — the `B = 1` floor of `RBM.Gauss.diagBoundFlow_floor`, which carries
no factor `2`, is a fortiori below `RBM.Gauss.eventually_two_rpow_neg_one_le_W_inv`'s bound. -/
theorem eventually_rpow_neg_one_le_W_inv (d : Dims) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by
  filter_upwards [eventually_two_rpow_neg_one_le_W_inv d] with N hN
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  linarith

/-- **The diagonal half of Lemma 4.1 along the flow, from the *floored* (4.3).**

The conclusion is word for word `RBM.Gauss.stochDom_indicator_diag_flow`'s; only the hypothesis
is weakened, from `RBM.Gauss.DiagBoundFlow` to `RBM.Gauss.DiagBoundFlow'`.  The floor costs
nothing because the control on the right already carries an **unconditional** `W⁻¹` summand,
while the floor may be taken as small as one likes. -/
theorem stochDom_indicator_diag_flow' (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {fl : ℕ → ℝ} (hflW : ∀ᶠ N : ℕ in atTop, fl N ≤ ((d.W N : ℕ) : ℝ)⁻¹)
    (hDiag : DiagBoundFlow' d E s t fl) (hΦ0 : ∀ N u, 0 ≤ Φ N u)
    (hΦ : LoopHypFlow d E s t Φ) :
    StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2 p.2 - mE E‖ ^ 2) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) := by
  have h1 : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2 p.2 - mE E‖ ^ 2) ω)
      (fun N p ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) + fl N) :=
    stochDom_mono_left hDiag fun N p ω =>
      Set.indicator_le_indicator_of_subset (goodEv_subset_goodSet_flow hE hs0 ht1 N p.1)
        (fun _ => by positivity) ω
  have hLmax : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ))) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) :=
    StochDom.control_mono
      (stochDom_indicator_Lmax_flow (V := fun N => BIdx d.L d.W N) hΦ0 hΦ)
      (fun N p _ => by
        have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
        linarith)
  have h2 := stochDom_indicator_add_const
    (A := fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) =>
      Step1.goodEv (sample d) E N (p.1 : ℝ))
    (c := fl) hLmax
    (fun N p _ => by
      have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
      linarith [hΦ0 N p.1])
    (by
      filter_upwards [hflW] with N hN p _
      linarith [hΦ0 N p.1])
  refine stochDom_trans_indicator_idx h1 h2 (fun N p _ => ?_)
  have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  linarith [hΦ0 N p.1]

/-- **`RBM.Step1.Lemma41Flow` from the *floored* (4.2) and (4.3)** — the conclusion is word for
word `RBM.Gauss.lemma41Flow`'s, with both hypotheses weakened to their floored forms. -/
theorem lemma41Flow'' (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {flE flD : ℕ → ℝ}
    (hflE : ∀ᶠ N : ℕ in atTop, flE N ≤ ((d.W N : ℕ) : ℝ)⁻¹)
    (hflD : ∀ᶠ N : ℕ in atTop, flD N ≤ ((d.W N : ℕ) : ℝ)⁻¹)
    (hEntry : EntryBoundFlow' d E s t flE) (hDiag : DiagBoundFlow' d E s t flD) :
    Step1.Lemma41Flow (sample d) E s t := by
  intro Ψ hΨ0 hloop
  exact stochDom_indicator_llMax_sq_flow_of hΨ0
    (stochDom_indicator_offdiag_flow' hE hs0 ht1 hflE hEntry hΨ0 (loopHypFlow_iff.2 hloop))
    (stochDom_indicator_diag_flow' hE hs0 ht1 hflD hDiag hΨ0 (loopHypFlow_iff.2 hloop))

/-- **`RBM.Step1.Lemma41Flow` with both (4.2) and (4.3) discharged — the deliverable of T183.**

`RBM.Gauss.lemma41Flow` carried `RBM.Gauss.EntryBoundFlow` and `RBM.Gauss.DiagBoundFlow`;
`RBM.Gauss.lemma41Flow_of_diagBoundFlow` (T107) removed the first.  Both are now theorems in
their floored forms, which is all the consumer needs, so nothing is left but the regime. -/
theorem lemma41Flow_gauss (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (t N)) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, flowDelta d E t N ≤ (N : ℝ) ^ (-c₀)) :
    Step1.Lemma41Flow (sample d) E s t := by
  have hE2 : |E| < 2 := by linarith
  exact lemma41Flow'' hE2 hs0 ht1 (eventually_two_rpow_neg_one_le_W_inv d)
    (eventually_rpow_neg_one_le_W_inv d)
    (entryBoundFlow_floor d hE2 hs0 hst ht1 hK hη hc₀ hδ zero_le_one)
    (diagBoundFlow_floor d hκ0 hκ1 hE hs0 hst ht1 hK hη hc₀ hδ zero_le_one)

/-- **`RBM.Step1.Hyp` for the Gaussian model with both (4.2) and (4.3) discharged.**

Word for word the conclusion of `RBM.Gauss.step1Hyp_gauss_of_scale`, under word for word its
hypotheses **minus `RBM.Gauss.EntryBoundFlow` and `RBM.Gauss.DiagBoundFlow`**: the floored forms
`RBM.Gauss.entryBoundFlow_floor` and `RBM.Gauss.diagBoundFlow_floor` replace them, and their
regime inputs — `N^{-1} ≤ η_{t_N}` and `δ_N ≤ N^{-c/6}` — are both consequences of
`RBM.Step1.step1`'s own `N^c ≤ W ℓ_t η_t`.  (4.3)'s kernel wants `0 < κ ≤ 1`; `κ` is capped at
`1`, which only weakens `|E| ≤ 2 - κ`.  So the floors cost no hypothesis at all here. -/
theorem step1Hyp_gauss_of_scale'' (d : Dims) {κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N)) :
    Step1.Hyp (sample d) E s t := by
  have hE2 : |E| < 2 := by linarith
  have hκ0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ1 : min κ 1 ≤ 1 := min_le_right _ _
  have hEκ : |E| ≤ 2 - min κ 1 := by
    have hmin : min κ 1 ≤ κ := min_le_left _ _
    linarith
  have hS : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
      LoopScaling (sample d) E t₁ t₂ := fun t₁ t₂ h1 h12 _ =>
    loopScaling_gauss (d := d) (fun N => lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (h1 N)) h12
  exact
    { scaling := hS
      lift := fun n hn => netLift_gauss d hE2 hs0 hst ht1 one_pos
        (rpow_neg_one_le_one_sub_of_scale_ge (band d) hE2 ht1 hc0 hreg) hn
        (fun u => eq58_seq_thr (sample d) hκ hE (C₀ := 3) (by norm_num) hB hs0 hst ht1 hcond
          hS u hn)
      lemma41 := lemma41Flow_gauss d hκ0 hκ1 hEκ hs0 hst ht1 zero_le_one
        (rpow_neg_one_le_etaT_of_scale_ge d hE2 ht1 hc0 hreg)
        (by linarith : (0 : ℝ) < c / 6) (flowDelta_le_rpow_neg d hreg)
      cont := cont_gauss d hE2 (fun N => (hs0 N)) ht1 }

end Consumer

end Flow

end RBM.Gauss
