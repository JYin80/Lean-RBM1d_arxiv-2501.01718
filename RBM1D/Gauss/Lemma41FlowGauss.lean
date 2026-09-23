/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma41Glue
import RBM1D.Gauss.APrimeGeneralMovingCarrierCore

/-!
# `RBM.Step1.Lemma41Flow` for the Gaussian model — T108

`RBM1D/Gauss/Lemma41Glue.lean` (T102) proves Lemma 4.1 in the language of
`RBM.Step1.Lemma41Flow` **at one fixed time** `u`.  `RBM.Step1.Lemma41Flow` itself asks for the
same bound with the time `u ∈ [s_N, t_N]` **inside** the index set of `≺`.  This file closes
that gap.

## The structure of the argument

`RBM.Step1.Lemma41Flow` is a *bound transfer*: it takes a domination

```
1_{Ω_u} ‖L_{(+,-),(a,b)}(u)‖ ≺ Φ(N,u)     uniformly in (u, a, b)
```

and returns

```
1_{Ω_u} ‖G_u − m‖²_max ≺ Φ(N,u) + W⁻¹     uniformly in u.
```

Both sides are already *time-uniform* dominations.  Consequently **no time net is needed
here**: every step of T102's chain (the sup over block pairs, the nine-term control of (4.2),
the passage from the entries to `‖·‖_max`) is an argument about the failure event at a single
`N` and a single `ω`, with an existential over the index set, and is therefore insensitive to
what the index set is.  Carrying the time inside the index set all the way through is enough.

This is why the slow-variation difficulty recorded in `docs/STATUS.md` ("obstacle two": the
time nets of `RBM1D/Gauss/DominationHolder.lean` take a control `Φ : ℕ → ℝ`, while
`Lemma41Flow`'s control `Φ N u` depends on the time) does **not** arise: the net would be
needed only if one started from the *fixed-time* (4.2)/(4.3) and tried to make them uniform in
`u` afterwards.  The uniformity in `u` is instead imported, once, from the time-indexed forms
of (4.2) and (4.3) — the ticket T107 interface, carried here as the two explicit hypotheses
`RBM.Gauss.EntryBoundFlow` and `RBM.Gauss.DiagBoundFlow`.

## The hypotheses

* `RBM.Gauss.EntryBoundFlow d E s t` — **(4.2) along the flow**, i.e.
  `RBM.Gauss.entry_bound_gauss` with `TimeIcc s t N` added to the index set and the spectral
  parameter `z = z_u` following the index.  **To be discharged by T107**
  (`RBM1D/Gauss/EntryBoundTime.lean`); it is not proved here and nothing in this file touches
  `RBM1D/Green/EntryBound.lean`.
* `RBM.Gauss.DiagBoundFlow d E s t` — **(4.3) along the flow**, likewise.

Both are stated with the *time-independent* threshold
`δ_N = (W ℓ_{t_N} η_{t_N})^{-1/6} = RBM.Gauss.flowDelta d E t N`, exactly as prescribed in
`docs/STATUS.md`: `RBM.flowScale` is antitone in the time, so the `u`-dependent threshold
`(W ℓ_u η_u)^{-1/6}` of `RBM.Step1.goodEv` is at most `δ_N` for every `u ≤ t_N`, and the event
of `Lemma41Flow` is contained in the event of the hypotheses
(`RBM.Gauss.goodEv_subset_goodSet_flow`).  The indicator therefore only decreases, which is the
direction needed.

The operator-norm bound `‖X‖ ≺ 1` of T100 (`RBM.Gauss.OpNormBound`) is **not** used here: it is
an input to the time-uniform large deviation estimates behind T107, not to the bound transfer.

## Main definitions

* `RBM.Gauss.flowDelta` — the threshold `δ_N = (W ℓ_{t_N} η_{t_N})^{-1/6}`.
* `RBM.Gauss.EntryBoundFlow`, `RBM.Gauss.DiagBoundFlow` — the T107 interface.
* `RBM.Gauss.LoopHypFlow` — the hypothesis of `RBM.Step1.Lemma41Flow`, restated with `RBM.Lre`.

## Main results

* `RBM.Gauss.lemma41Flow` — `RBM.Step1.Lemma41Flow (sample d) E s t`, for **every**
  nonnegative control `Φ N u`, given `EntryBoundFlow` and `DiagBoundFlow`.
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset

variable {d : Dims} {E : ℝ} {s t : ℕ → ℝ}

/-! ### Generic monotonicity of `≺` in the dominated quantity -/

section Mono

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- `≺` is monotone in the dominated quantity: the failure event only shrinks. -/
theorem stochDom_mono_left {ξ ξ' ζ : ∀ N, U N → Ω → ℝ} (h : StochDom P ξ' ζ)
    (hle : ∀ N u ω, ξ N u ω ≤ ξ' N u ω) : StochDom P ξ ζ := by
  refine StochDom.of_subset h fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards with N
  rintro ω ⟨u, hu⟩
  exact ⟨u, hu.trans_le (hle N u ω)⟩

/-- **Transitivity through an index-dependent indicator.**  `RBM.StochDom.trans_indicator`
(T102) with the event allowed to depend on the index — here, on the time. -/
theorem stochDom_trans_indicator_idx {A : ∀ N, U N → Set Ω} {f g h : ∀ N, U N → Ω → ℝ}
    (h₁ : StochDom P (fun N u ω => (A N u).indicator (f N u) ω) g)
    (h₂ : StochDom P (fun N u ω => (A N u).indicator (g N u) ω) h)
    (hh : ∀ N u ω, 0 ≤ h N u ω) :
    StochDom P (fun N u ω => (A N u).indicator (f N u) ω) h := by
  refine StochDom.of_subset_union h₁ h₂ fun τ hτ => ⟨τ / 2, by linarith, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
  intro ω hω
  obtain ⟨u, hu0'⟩ := hω
  have hu : (N : ℝ) ^ τ * h N u ω < (A N u).indicator (f N u) ω := hu0'
  by_contra hcon
  rw [Set.mem_union] at hcon
  push Not at hcon
  obtain ⟨hb1, hb2⟩ := hcon
  simp only [badSet, Set.mem_ofPred_eq, not_exists, not_lt] at hb1 hb2
  replace hb1 : ∀ v, (A N v).indicator (f N v) ω ≤ (N : ℝ) ^ (τ / 2) * g N v ω := hb1
  replace hb2 : ∀ v, (A N v).indicator (g N v) ω ≤ (N : ℝ) ^ (τ / 2) * h N v ω := hb2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hp : (0 : ℝ) < (N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hN0 _
  have hmem : ω ∈ A N u := by
    by_contra hnot
    rw [Set.indicator_of_notMem hnot] at hu
    exact absurd hu (not_lt.2
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) τ) (hh N u ω)))
  have e1 : (A N u).indicator (f N u) ω ≤ (N : ℝ) ^ (τ / 2) * g N u ω := hb1 u
  have e2 : g N u ω ≤ (N : ℝ) ^ (τ / 2) * h N u ω := by
    have := hb2 u
    rwa [Set.indicator_of_mem hmem] at this
  have hchain : (A N u).indicator (f N u) ω
      ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * h N u ω) :=
    e1.trans (mul_le_mul_of_nonneg_left e2 hp.le)
  have hpow : (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * h N u ω)
      = (N : ℝ) ^ τ * h N u ω := by
    rw [← mul_assoc, ← Real.rpow_add hN0]
    congr 2
    ring
  rw [hpow] at hchain
  exact absurd hu (not_lt.2 hchain)

end Mono

/-! ### The threshold `δ_N` and the good events -/


/-- The `u`-threshold of `RBM.Step1.goodEv` is at most `δ_N`, for `u ∈ [s_N, t_N]`. -/
theorem scale_rpow_le_flowDelta (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (N : ℕ) (u : RBM.TimeIcc s t N) :
    ((band d).scale E N (u : ℝ))⁻¹ ^ ((1 : ℝ) / 6) ≤ flowDelta d E t N := by
  have hW : (0 : ℝ) ≤ ((band d).W N : ℝ) := Nat.cast_nonneg _
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hanti : (band d).scale E N (t N) ≤ (band d).scale E N (u : ℝ) :=
    flowScale_antitoneOn hW ((band d).L N) E (Set.mem_Iic.2 hu1.le)
      (Set.mem_Iic.2 (ht1 N).le) u.2.2
  have ht0 : (0 : ℝ) ≤ t N := (hs0 N).trans (u.2.1.trans u.2.2)
  have htpos : 0 < (band d).scale E N (t N) := (band d).scale_pos' hE N ht0 (ht1 N)
  have hupos : 0 < (band d).scale E N (u : ℝ) := htpos.trans_le hanti
  have hinv : ((band d).scale E N (u : ℝ))⁻¹ ≤ ((band d).scale E N (t N))⁻¹ := by
    have h := one_div_le_one_div_of_le htpos hanti
    rwa [one_div, one_div] at h
  exact Real.rpow_le_rpow (by positivity) hinv (by norm_num)

/-- **The good event of `RBM.Step1.Lemma41Flow` sits inside the good event of (4.1) at the
uniform threshold `δ_N`.**  Both are `{‖G_u − m‖_max ≤ ·}`; only the threshold differs, and
`RBM.flowScale` is antitone in the time. -/
theorem goodEv_subset_goodSet_flow (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (N : ℕ) (u : RBM.TimeIcc s t N) :
    Step1.goodEv (sample d) E N (u : ℝ) ⊆
      goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) (mE E)
        (flowDelta d E t) N := by
  rw [goodEv_eq_goodSet E N (u : ℝ)]
  intro ω hω x y
  exact (hω x y).trans (scale_rpow_le_flowDelta hE hs0 ht1 N u)

/-! ### The T107 interface: (4.2) and (4.3) with the time inside the index set -/

/-- **(4.2) along the flow** — the time-indexed form of `RBM.Gauss.entry_bound_gauss`.

This is the conclusion of ticket T107 (`RBM1D/Gauss/EntryBoundTime.lean`): the deterministic
kernel `RBM.norm_sq_green_le_blk` of `RBM1D/Green/EntryBound.lean` together with
`RBM.StochDom.of_det`, whose index types `U`, `V` are arbitrary, applied with `TimeIcc s t N`
in the index set so that the spectral parameter `z_u` follows the index.  It is carried here as
a hypothesis and is **not** proved in this file. -/
def EntryBoundFlow (d : Dims) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  StochDom (P d)
    (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ))
          (mE E) (flowDelta d E t) N).indicator
        (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2.1.1 p.2.1.2‖ ^ 2) ω)
    (fun N p ω =>
      (∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
          Lre (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) (p.2.1.2.1 + b) (p.2.1.1.1 + a))
        + if p.2.1.1.1 - p.2.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)

/-- **(4.3) along the flow** — the time-indexed form of `RBM.Gauss.diag_bound_gauss`.  The
conclusion of ticket T107; carried here as a hypothesis. -/
def DiagBoundFlow (d : Dims) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  StochDom (P d)
    (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ))
          (mE E) (flowDelta d E t) N).indicator
        (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2 p.2 - mE E‖ ^ 2) ω)
    (fun N p ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)))

/-! ### The hypothesis of `RBM.Step1.Lemma41Flow`, restated with `RBM.Lre` -/

variable {Φ : ∀ N, RBM.TimeIcc s t N → ℝ}

/-- The hypothesis of `RBM.Step1.Lemma41Flow`, with the two-loop written as `RBM.Lre`. -/
abbrev LoopHypFlow (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (Φ : ∀ N, RBM.TimeIcc s t N → ℝ) : Prop :=
  StochDom (P d)
    (fun N (p : RBM.TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) ω =>
      (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
        (fun ω => Lre (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2.1 p.2.2) ω)
    (fun N p _ => Φ N p.1)

/-- `RBM.Gauss.LoopHypFlow` is exactly the hypothesis of `RBM.Step1.Lemma41Flow`. -/
theorem loopHypFlow_iff :
    LoopHypFlow d E s t Φ ↔ StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => ‖(sample d).Lval E N (p.1 : ℝ) ω (pmLoop p.2.1 p.2.2)‖) ω)
      (fun N p _ => Φ N p.1) := by
  have h : ∀ (N : ℕ) (u : ℝ) (ab : ZMod (d.L N) × ZMod (d.L N)) (ω : Ω d),
      ‖(sample d).Lval E N u ω (pmLoop ab.1 ab.2)‖
        = Lre (Hflow d N u ω) (zt E u) ab.1 ab.2 := fun N u ab ω =>
    sample_Lval_pm E N u ω ab.1 ab.2
  constructor <;> intro hh <;> simpa only [h] using hh

/-! ### The chain of T102, with the time carried inside the index set -/

/-- **`1_Ω L^max_u ≺ Φ(N,u)`**, uniformly in `u`: the maximum over the (finitely many) block
pairs is attained. -/
theorem stochDom_indicator_Lmax_flow {V : ℕ → Type*} (hΦ0 : ∀ N u, 0 ≤ Φ N u)
    (hΦ : LoopHypFlow d E s t Φ) :
    StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × V N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ))) ω)
      (fun N p _ => Φ N p.1) := by
  refine StochDom.of_subset_union hΦ hΦ fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards with N
  intro ω hω
  refine Set.mem_union_left _ ?_
  simp only [badSet, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨p, hlt⟩ := hω
  by_cases hmem : ω ∈ Step1.goodEv (sample d) E N (p.1 : ℝ)
  · rw [Set.indicator_of_mem hmem] at hlt
    obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty)
      (fun q : ZMod (d.L N) × ZMod (d.L N) =>
        Lre (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) q.1 q.2)
    unfold Lmax at hlt
    rw [hq] at hlt
    exact ⟨(p.1, q), by rw [Set.indicator_of_mem hmem]; exact hlt⟩
  · rw [Set.indicator_of_notMem hmem] at hlt
    exact absurd hlt (not_lt.2
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) τ) (hΦ0 N p.1)))

/-- **The control of (4.2) is `≺ Φ(N,u) + W⁻¹`**, uniformly in `u`. -/
theorem stochDom_indicator_entryControl_flow (hΦ0 : ∀ N u, 0 ≤ Φ N u)
    (hΦ : LoopHypFlow d E s t Φ) :
    StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => (∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
              Lre (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) (p.2.1.2.1 + b) (p.2.1.1.1 + a))
            + if p.2.1.1.1 - p.2.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) := by
  refine StochDom.of_subset_union hΦ hΦ fun τ hτ => ⟨τ / 2, by linarith, ?_⟩
  filter_upwards [eventually_le_rpow 9 (show (0:ℝ) < τ / 2 by linarith),
    Filter.eventually_ge_atTop 1] with N h9 hN1
  intro ω hω
  refine Set.mem_union_left _ ?_
  simp only [badSet, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨p, hlt⟩ := hω
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hW : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  have hτ1 : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1' hτ.le
  have hτ2 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' (by linarith)
  by_cases hmem : ω ∈ Step1.goodEv (sample d) E N (p.1 : ℝ)
  · rw [Set.indicator_of_mem hmem] at hlt
    have hite : (if p.2.1.1.1 - p.2.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        ≤ (N : ℝ) ^ τ * ((d.W N : ℕ) : ℝ)⁻¹ := by
      split_ifs
      · nlinarith [hW, hτ1]
      · positivity
    have hsum : (N : ℝ) ^ τ * Φ N p.1
        < ∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
            Lre (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) (p.2.1.2.1 + b) (p.2.1.1.1 + a) := by
      nlinarith [hlt, hite]
    have h9M := sum_sum_Lre_le d N E (p.1 : ℝ) ω p.2.1.1.1 p.2.1.2.1
    have hM : 0 ≤ Lmax (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) :=
      Lmax_nonneg (Hflow_isHermitian d N (p.1 : ℝ) ω)
    have hkey : (N : ℝ) ^ (τ / 2) * Φ N p.1
        < Lmax (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) := by
      have hsplit : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
        rw [← Real.rpow_add hN0]; congr 1; ring
      nlinarith [hsum, h9M, h9, hΦ0 N p.1, hτ2]
    obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty)
      (fun q : ZMod (d.L N) × ZMod (d.L N) =>
        Lre (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) q.1 q.2)
    unfold Lmax at hkey
    rw [hq] at hkey
    exact ⟨(p.1, q), by rw [Set.indicator_of_mem hmem]; exact hkey⟩
  · rw [Set.indicator_of_notMem hmem] at hlt
    exfalso
    have : (0 : ℝ) ≤ (N : ℝ) ^ τ * (Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) := by
      have h1 : (0 : ℝ) ≤ Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹ := by linarith [hΦ0 N p.1]
      positivity
    linarith [hlt]

/-- **The diagonal half of Lemma 4.1 along the flow**: `1_{Ω_u}|G_u,ii − m|² ≺ Φ(N,u) + W⁻¹`,
uniformly in `u ∈ [s_N, t_N]` and `i`. -/
theorem stochDom_indicator_diag_flow (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hDiag : DiagBoundFlow d E s t) (hΦ0 : ∀ N u, 0 ≤ Φ N u) (hΦ : LoopHypFlow d E s t Φ) :
    StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2 p.2 - mE E‖ ^ 2) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) := by
  have h1 : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2 p.2 - mE E‖ ^ 2) ω)
      (fun N p ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ))) :=
    stochDom_mono_left hDiag fun N p ω =>
      Set.indicator_le_indicator_of_subset (goodEv_subset_goodSet_flow hE hs0 ht1 N p.1)
        (fun _ => by positivity) ω
  have h2 : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N (p.1 : ℝ)).indicator
          (fun ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ))) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) :=
    StochDom.control_mono
      (stochDom_indicator_Lmax_flow (V := fun N => BIdx d.L d.W N) hΦ0 hΦ)
      (fun N _ _ => by
        have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
        linarith)
  refine stochDom_trans_indicator_idx h1 h2 (fun N p _ => ?_)
  have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  linarith [hΦ0 N p.1]

/-- **The off-diagonal half of Lemma 4.1 along the flow**: `1_{Ω_u}|G_u,ij|² ≺ Φ(N,u) + W⁻¹`,
uniformly in `u ∈ [s_N, t_N]` and `i ≠ j`. -/
theorem stochDom_indicator_offdiag_flow (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) (hEntry : EntryBoundFlow d E s t) (hΦ0 : ∀ N u, 0 ≤ Φ N u)
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
        (∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
            Lre (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) (p.2.1.2.1 + b) (p.2.1.1.1 + a))
          + if p.2.1.1.1 - p.2.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0) :=
    stochDom_mono_left hEntry fun N p ω =>
      Set.indicator_le_indicator_of_subset (goodEv_subset_goodSet_flow hE hs0 ht1 N p.1)
        (fun _ => by positivity) ω
  refine stochDom_trans_indicator_idx h1 (stochDom_indicator_entryControl_flow hΦ0 hΦ)
    (fun N p _ => ?_)
  have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  linarith [hΦ0 N p.1]

/-- **Lemma 4.1 along the flow, in the language of `RBM.Step1.Lemma41Flow`**:
`1_{Ω_u} ‖G_u − m‖²_max ≺ Φ(N,u) + W⁻¹`, uniformly in `u ∈ [s_N, t_N]`. -/
theorem stochDom_indicator_llMax_sq_flow (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) (hEntry : EntryBoundFlow d E s t) (hDiag : DiagBoundFlow d E s t)
    (hΦ0 : ∀ N u, 0 ≤ Φ N u) (hΦ : LoopHypFlow d E s t Φ) :
    StochDom (P d)
      (fun N (u : RBM.TimeIcc s t N) ω =>
        (Step1.goodEv (sample d) E N (u : ℝ)).indicator
          (fun ω => Step1.llMax (sample d) E N (u : ℝ) ω ^ 2) ω)
      (fun N u _ => Φ N u + ((d.W N : ℕ) : ℝ)⁻¹) := by
  refine StochDom.of_subset_union
    (stochDom_indicator_offdiag_flow hE hs0 ht1 hEntry hΦ0 hΦ)
    (stochDom_indicator_diag_flow hE hs0 ht1 hDiag hΦ0 hΦ)
    fun τ hτ => ⟨τ, hτ, ?_⟩
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

/-! ### The assembly -/

/-- **Lemma 4.1 along the flow, uniformly in the time** — `RBM.Step1.Lemma41Flow` for the
Gaussian model, for **every** nonnegative control `Φ N u`.

The two hypotheses are the time-indexed forms of (4.2) and (4.3), the deliverables of T107.
No slow-variation assumption on `Φ` and no time net are needed: `Lemma41Flow` is a transfer
between two dominations that are *both* already uniform in the time, and every step of the
transfer is an argument about the failure event at a single `N` and a single `ω`. -/
theorem lemma41Flow (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hEntry : EntryBoundFlow d E s t) (hDiag : DiagBoundFlow d E s t) :
    Step1.Lemma41Flow (sample d) E s t := by
  intro Φ hΦ0 hloop
  exact stochDom_indicator_llMax_sq_flow hE hs0 ht1 hEntry hDiag hΦ0
    (loopHypFlow_iff.2 hloop)

/-! ### The slow-variation hypothesis for the control that Step 1 actually uses

Even though this file needs no time net, the slow-variation hypothesis of
`RBM.Gauss.stochDom_timeIcc_of_holder_slow_hp` and
`RBM.Gauss.stochDom_timeIcc_of_holder_slow_dom` is worth discharging for the control that
`RBM1D/Hierarchy/Step1.lean` supplies,
```
Φ(N,u) = (ℓ_u / ℓ_{s_N}) · (W ℓ_u η_u)⁻¹,
```
because it shows what the hypothesis costs.  The answer is: almost nothing.  The factors `ℓ_u`
cancel,
```
Φ(N,u) = (ℓ_{s_N} · W · η_u)⁻¹,   η_u = (1-u) Im m^{(E)},
```
so `Φ(N,v)/Φ(N,u) = (1-u)/(1-v)`, and `|u - v| ≤ δ_N ≤ 1 - t_N ≤ 1 - v` already gives
`1 - u ≤ 2(1 - v)`, i.e. a factor `2 ≤ N^ε`.  The only input is that the net spacing is below
the distance of the interval from the singularity at `u = 1`. -/

section SlowStep1

variable {Ωb : Type*} [MeasurableSpace Ωb]

/-- `Φ(N,u) = (ℓ_u/ℓ_{s_N})(W ℓ_u η_u)⁻¹ = (ℓ_{s_N} W η_u)⁻¹`: the factors `ℓ_u` cancel. -/
theorem step1Phi_eq (B : RBM.Band Ωb) {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ} (N : ℕ) {u : ℝ}
    (hu1 : u < 1) (hs1 : s N < 1) :
    B.ell N u / B.ell N (s N) * (B.scale E N u)⁻¹
      = (B.ell N (s N) * (B.W N : ℝ) * etaT E u)⁻¹ := by
  have hL : 1 ≤ B.L N := le_trans (by norm_num) (B.three_le_L N)
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL hs1
  have hℓu : 0 < B.ell N u := Step3.ellHat_pos_of_lt_one hL hu1
  have hη : 0 < etaT E u := etaT_pos hE hu1
  show B.ell N u / B.ell N (s N) * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ = _
  field_simp

/-- **The slow-variation hypothesis of `RBM.Gauss.stochDom_timeIcc_of_holder_slow_hp` for
Step 1's control**, at every `ε > 0`: it suffices that the net scale `δ_N` stays below
`1 - t_N`. -/
theorem slow_step1Phi (B : RBM.Band Ωb) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {δ : ℕ → ℝ}
    (hδt : ∀ᶠ N : ℕ in Filter.atTop, δ N ≤ 1 - t N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
      |u - v| ≤ δ N →
        B.ell N v / B.ell N (s N) * (B.scale E N v)⁻¹
          ≤ (N : ℝ) ^ ε * (B.ell N u / B.ell N (s N) * (B.scale E N u)⁻¹) := by
  filter_upwards [hδt, eventually_le_rpow 2 hε] with N hδN hN2 u hu v hv huv
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hu1 : u < 1 := hu.2.trans_lt (ht1 N)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hL : 1 ≤ B.L N := le_trans (by norm_num) (B.three_le_L N)
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL hs1
  have hηu : 0 < etaT E u := etaT_pos hE hu1
  have hηv : 0 < etaT E v := etaT_pos hE hv1
  rw [step1Phi_eq B hE N hu1 hs1, step1Phi_eq B hE N hv1 hs1]
  -- `η_u ≤ N^ε η_v`, because `1 - u ≤ 2(1 - v)`
  have hηle : etaT E u ≤ (N : ℝ) ^ ε * etaT E v := by
    have him : 0 ≤ (mE E).im := mE_im_nonneg E
    have h1 : v - u ≤ δ N := (neg_le_abs (u - v)).trans huv |>.trans_eq' (by ring)
    have h2 : 1 - u ≤ 2 * (1 - v) := by linarith [hv.2]
    have heu : etaT E u = (1 - u) * (mE E).im := rfl
    have hev : etaT E v = (1 - v) * (mE E).im := rfl
    rw [heu, hev]
    nlinarith [him, hN2, hηv, hev]
  have hdu : (0 : ℝ) < B.ell N (s N) * (B.W N : ℝ) * etaT E u := by positivity
  have hdv : (0 : ℝ) < B.ell N (s N) * (B.W N : ℝ) * etaT E v := by positivity
  have ha : (0 : ℝ) < B.ell N (s N) * (B.W N : ℝ) := by positivity
  rw [show (N : ℝ) ^ ε * (B.ell N (s N) * (B.W N : ℝ) * etaT E u)⁻¹
      = (N : ℝ) ^ ε / (B.ell N (s N) * (B.W N : ℝ) * etaT E u) by rw [div_eq_mul_inv],
    ← one_div, div_le_div_iff₀ hdv hdu]
  nlinarith [mul_le_mul_of_nonneg_left hηle ha.le]

end SlowStep1

end RBM.Gauss


