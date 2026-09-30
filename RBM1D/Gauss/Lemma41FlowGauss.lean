/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma41Glue
import RBM1D.Gauss.GoodSetFlowCore

/-!
# Lemma 4.1 along the flow: the good events at a time-independent threshold

`RBM1D/Gauss/Lemma41Glue.lean` proves Lemma 4.1 **at one fixed time** `u`.  Along the flow the
same bound is needed with the time `u ∈ [s_N, t_N]` **inside** the index set of `≺`.

## The structure of the argument

Lemma 4.1 along the flow is a *bound transfer*: it takes a domination

```
1_{Ω_u} ‖L_{(+,-),(a,b)}(u)‖ ≺ Φ(N,u)     uniformly in (u, a, b)
```

and returns

```
1_{Ω_u} ‖G_u − m‖²_max ≺ Φ(N,u) + W⁻¹     uniformly in u.
```

Both sides are already *time-uniform* dominations.  Consequently **no time net is needed**:
every step of the chain (the sup over block pairs, the nine-term control of (4.2), the passage
from the entries to `‖·‖_max`) is an argument about the failure event at a single `N` and a
single `ω`, with an existential over the index set, and is therefore insensitive to what the
index set is.  Carrying the time inside the index set all the way through is enough.

This is why the slow-variation difficulty (the time nets of `RBM1D/Gauss/DominationHolder.lean`
take a control `Φ : ℕ → ℝ`, while the control `Φ N u` here depends on the time) does **not**
arise: the net would be needed only if one started from the *fixed-time* (4.2)/(4.3) and tried
to make them uniform in `u` afterwards.  The uniformity in `u` is instead imported, once, from
the time-indexed forms of (4.2) and (4.3).

## The threshold

(4.2) and (4.3) along the flow are stated with the *time-independent* threshold
`δ_N = (W ℓ_{t_N} η_{t_N})^{-1/6} = RBM.Gauss.flowDelta d E t N`: `RBM.flowScale` is antitone in
the time, so the `u`-dependent threshold `(W ℓ_u η_u)^{-1/6}` of `RBM.Step1.goodEv` is at most
`δ_N` for every `u ≤ t_N` (`RBM.Gauss.scale_rpow_le_flowDelta`), and the good event at `u` is
contained in the good event of (4.1) at `δ_N` (`RBM.Gauss.goodEv_subset_goodSet_flow`).  The
indicator therefore only decreases, which is the direction needed.

The operator-norm bound `‖X‖ ≺ 1` is **not** used here: it is an input to the time-uniform
large deviation estimates of `RBM1D/Gauss/EntryBoundTime.lean`, not to the bound transfer.

## Main definitions

* `RBM.Gauss.flowDelta` — the threshold `δ_N = (W ℓ_{t_N} η_{t_N})^{-1/6}`.

## Main results

* `RBM.Gauss.stochDom_mono_left`, `RBM.Gauss.stochDom_trans_indicator_idx` — monotonicity of `≺`
  in the dominated quantity, and transitivity through an index-dependent indicator.
* `RBM.Gauss.scale_rpow_le_flowDelta`, `RBM.Gauss.goodEv_subset_goodSet_flow` — the threshold
  comparison.
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

/-- **Transitivity through an index-dependent indicator**: transitivity of `≺` through an
indicator, with the event allowed to depend on the index — here, on the time. -/
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

/-- **The good event `RBM.Step1.goodEv` sits inside the good event of (4.1) at the
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

/-! ### (4.2) and (4.3) with the time inside the index set -/

variable {Φ : ∀ N, RBM.TimeIcc s t N → ℝ}

/-! ### The chain, with the time carried inside the index set -/

/-! ### The assembly -/

section SlowStep1

variable {Ωb : Type*} [MeasurableSpace Ωb]

end SlowStep1

end RBM.Gauss


