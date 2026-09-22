/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6Sample
import RBM1D.Hierarchy.LKDecayQuant

/-!
# T227: Step 6's envelope hypotheses, quantified over the window

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8, (5.126)–(5.136), and §2.7, (2.71), (2.80).

T205 (`RBM1D/Gauss/Step6Sample.lean`) compiled `RBM.Gauss.not_exists_env_eG`: the family
`henvG` of `RBM.sharpExpect_step6_driftEG`, which asks for a single real number `Env N`
dominating `‖E^{(G)}(L-K, L)_{v,σ,a}(ω)‖` for **every** `v : ℝ`, has no producer at all — at
`E = 0`, `ω = 0`, `v = 1 - w` the value is `2(w⁻¹-1)w^{-3}/W`, unbounded as `w ↓ 0`.  Since
Theorems 2.4/2.5 quantify over every `|E| ≤ 2 - κ`, this blocked the whole (2.71) induction.

The defect is a quantifier, not a gap: the proofs of `RBM.unifDetDom_driftELK`,
`RBM.fastDecayHyp_driftSplit` and `RBM.unifDetDom_driftEG` use those hypotheses **only at
window times** `v ∈ [s_N, t_N]`.  This file carries the three theorems over to
`∀ v : RBM.TimeIcc s t N`, assembles the primed (2.80), and then *produces* the primed
hypotheses for the Gaussian model, so that the family is no longer vacuous.

## What is here

* §1 — two crude counting bounds, `RBM.norm_eG_le_crude` and `RBM.norm_primBil_le_crude`:
  `|E^{(G)}| ≤ W n L M_X M_Y` and `|primBil| ≤ W n² L M M'`.  Both are the trivial triangle
  inequality with `∑_b ‖S^{(B)}_{ab}‖ = 1` (`RBM.sum_norm_SB_apply_row`); they are the shape in
  which the window envelope is checked.
* §2 — the primed theorems `RBM.unifDetDom_driftELK'`, `RBM.fastDecayHyp_driftSplit'`,
  `RBM.unifDetDom_driftEG'`, `RBM.driftBound_driftEG'`, `RBM.sharpExpect_step6_driftEG'` and
  `RBM.sharpExpect_step6_driftSplit'` (the sixth affected declaration, which T205's list
  missed).
  The statements are the frozen ones with `∀ (v : ℝ)` replaced by `∀ (v : RBM.TimeIcc s t N)`
  in `henvQ`/`henvG`/`henvLK`, `hmeasQ`/`hmeasG`/`hmeasLK` and `hintL1`; every other hypothesis
  and the conclusion are unchanged (the proofs are T182/T189's, with the hypotheses read at the
  window point that was already in scope).
* §3 — **the envelope exists on the window**: `RBM.exists_env_window` builds it explicitly, for
  an arbitrary `RBM.Sample`, out of `RBM.envFloor E t N = max(1, η_{t_N}^{-1})`, the
  deterministic loop bound `RBM.norm_gloop_flow_le_envFloor` and (2.59)
  (`RBM.exists_norm_Kval_le_envFloor`).  The only side condition is
  `hη : ∀ᶠ N, N^{-c} ≤ η_{t_N}`, the same one `RBM.Gauss.quad11_unifDetDom_gauss` already takes,
  and it is used **only** for the polynomial bound `Env N ≤ N^{Kenv}`, not for the envelope
  itself.
* §4 — **the positive witness** `RBM.exists_env_window_grid`, on the window
  `[1 - 1/(N+2), 1 - 1/(N+3)]` at the energy `E = 0`: `s_N > 0`, `s_N < t_N`, `t_N < 1`, and
  `1 - t_N ≍ N^{-1}` is the hardest end of the range of Theorem 2.21, so this is not a
  collapsed scale.  §4b instantiates §3 at a single interior time.
* §5 — the (2.71) half of the induction step, `RBM.bounds_step_of_step6_window`: `BoundsCore` at
  `t` (what `RBM.Thm221NoEL` delivers) plus `RBM.Bounds` at `s` plus the Step 6 data give
  `RBM.Bounds X E t`, through T205's `RBM.bounds_of_boundsCore_of_sharpExpect`.
* §6 — the Gaussian producers for the window slots: `RBM.Gauss.hmeasQ_window`,
  `RBM.Gauss.hmeasG_window`, `RBM.Gauss.hmeasLK_window`, `RBM.Gauss.hintL1_window`, and (from
  §4b) `RBM.Gauss.hintQ_gauss`, `RBM.Gauss.hintG_gauss`.
* §7 — `RBM.Gauss.env_window_vs_not_exists_env_eG`, the two directions side by side: at `E = 0`
  the envelope exists on the window and provably does not exist on `ℝ`.
* §8 — `RBM.Gauss.bounds_step_gauss_window`: §5 applied to the Gaussian model with **every slot
  that has a producer plugged in**, so the residual hypothesis list is the gap as the
  elaborator sees it, not as a comment claims it.  `RBM.Gauss.eventually_rpow_le_etaT_window`
  and `RBM.Gauss.bounds_step_gauss_side_conditions_grid` check that its side conditions are
  jointly satisfiable on the same non-degenerate window as §4.

## What is **not** here

`RBM.Bounds` still has **no inhabitant at `s > 0`**, so the acceptance criterion of T227 is only
half met.  What §8 leaves open, and nothing else:

* `hin59`, `hinQ`, `hinG` — the `HighProb` producers of `RBM.FDInputs`, `RBM.QuadInputs`,
  `RBM.EGInputs` (T205's list, item 2; explicitly out of T227's scope).
  **⚠ CORRECTED by T234, §10:** these are produced there, from
  `RBM.LKDecayQuant.FlowInputs` (Steps 1–2) plus `Ξ^{(L-K)} ≺ 1` (Steps 3–5), plus a
  deterministic bound for `RBM.FDInputs`' third clause.
* `hlk`, `hKd` — the quantitative half of Lemma 5.9: `RBM.exists_loopDecay_Kval` gives the decay
  of `K` at every radius, but with `δ = C(1-v) e^{-c(1-v) ℓ}`, and turning that into `N^{-D}` at
  radius `ℓ_v N^τ` needs `c(1-v) ℓ_v N^τ ≳ D log N`, which is the `RBM.DriftBound.DriftInputs`
  estimate — genuinely missing mathematics, not a quantifier.
  **⚠⚠ WRONG, CORRECTED by T234, §9 and §11.**  The rate of Corollary 3.5 is
  `RBM.cor35Rate δ = c₀ √δ / 4`, *square-root* in the gap, so the decay length of `K` is
  `(1-v)^{-1/2} = ℓ̂_v` and the exponent at the radius `ℓ_v N^τ` is `c₀ N^τ / 4`
  (`RBM.cor35Rate_mul_ell_mul`), with nothing to beat.  `RBM.loopDecay_Kval_quant` proves `hKd`
  **unconditionally, at every loop length**, and `RBM.Gauss.hlk_gauss` proves `hlk`.
* `hcont`, `hintU1`, `hintU2` — continuity in the time of `E L - K`, and interval integrability
  of `U` against the two drift tensors.  **Still open** (T205's item 4).
* `hlmk` — (2.68) uniformly on the window, which Steps 1–5 produce.  **Still open.**

**T234's net effect** (§9–§13, appended at the end of this file): the residual list of
`RBM.Gauss.bounds_step_gauss_window` drops from ten items to seven in
`RBM.Gauss.bounds_step_gauss_window'`.  `RBM.Bounds` at `s > 0` is **still not inhabited** —
what remains is `hcont`/`hintU1`/`hintU2`, `hlmk`, and the induction data `hc`/`hη`/`hBC`/`hB`.

So the (2.71) step theorem exists, and is not vacuous, but it is a *step theorem with named
hypotheses* rather than a discharge.  No hypothesis of this file is known to be unsatisfiable —
in particular none is an `ω`-quantified pointwise inequality, and all decay hypotheses are in
the paper's `∀ τ, ∀ D, ∀ᶠ N` order — and the one that *was* unsatisfiable, the envelope, is
discharged here.
-/

open MeasureTheory Filter

namespace RBM

/-! ### §1  Crude counting bounds for the two drift tensors

These are the `O(1)`-free versions of `RBM.Decay.norm_eG_le` and
`RBM.Decay.norm_primBil_sub_le`: no decay, no scale, just the triangle inequality and the fact
that each row of `S^{(B)}` has total mass `1`.  They are what turns a *pointwise* loop envelope
into an envelope for the drift tensors. -/

section Crude

open Finset

variable {L : ℕ} [NeZero L]

/-- **A crude bound for `E^{(G)}`**: `|E^{(G)}_{σ,a}| ≤ W n L M_X M_Y`, where `M_X` bounds the
`1`-loops of the left argument and `M_Y` the `(n+1)`-loops of the right one.  The `L` is the
`a`-sum; the `b`-sum is free because `∑_b ‖S^{(B)}_{ab}‖ = 1`. -/
theorem norm_eG_le_crude (hL : 3 ≤ L) (W : ℕ) {X Y : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {MX MY : ℝ} (hMX0 : 0 ≤ MX)
    (hX : ∀ (b : Bool) (a : ZMod L), ‖X ⟨[b], [a]⟩‖ ≤ MX)
    (hY : ∀ J : LoopIdx (ZMod L), J.WF → J.length = I.length + 1 → ‖Y J‖ ≤ MY) :
    ‖Decay.eG L W X Y I‖ ≤ (W : ℝ) * I.length * ((L : ℝ) * (MX * MY)) := by
  rw [Decay.eG]
  refine Decay.norm_W_sum_le' W I.length _ fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  have hYk : ∀ b : ZMod L, ‖Y (I.cutGlue k b)‖ ≤ MY := fun b =>
    hY _ (hI.cutGlue b hk.1 hk.2) (LoopIdx.length_cutGlue I b hk.2)
  calc ‖∑ a : ZMod L, ∑ b : ZMod L,
        X ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b * Y (I.cutGlue k b)‖
      ≤ ∑ a : ZMod L, ∑ b : ZMod L,
        ‖X ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b * Y (I.cutGlue k b)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a : ZMod L, ∑ b : ZMod L, MX * MY * ‖SB L _a b‖ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_mul]
        calc ‖X ⟨[I.σ.getD (k - 1) true], [a]⟩‖ * ‖SB L a b‖ * ‖Y (I.cutGlue k b)‖
            ≤ MX * ‖SB L a b‖ * MY := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right (hX _ a) (norm_nonneg _))
                (hYk b) (norm_nonneg _) (by positivity)
          _ = MX * MY * ‖SB L a b‖ := by ring
    _ = (L : ℝ) * (MX * MY) := by
        have hrow : ∀ a : ZMod L, (∑ b : ZMod L, MX * MY * ‖SB L a b‖) = MX * MY := by
          intro a
          rw [← Finset.mul_sum, sum_norm_SB_apply_row L hL a, mul_one]
        rw [Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_const, Finset.card_univ,
          ZMod.card, nsmul_eq_mul]

/-- **A crude bound for `primBil`**: `|primBil(K, K')_{σ,a}| ≤ W n² L M M'`, where `M`, `M'`
bound the arguments on well-formed loops of length between `2` and `n`.  Both glued loops have
their length in that range (`RBM.LoopIdx.two_le_length_cutGlueL`,
`RBM.LoopIdx.length_cutGlueL_le` and the right-hand pair). -/
theorem norm_primBil_le_crude (hL : 3 ≤ L) (W : ℕ) {K K' : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {M M' : ℝ} (hM0 : 0 ≤ M) (hM'0 : 0 ≤ M')
    (hK : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K J‖ ≤ M)
    (hK' : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K' J‖ ≤ M') :
    ‖primBil L W K K' I‖ ≤ (W : ℝ) * I.length ^ 2 * ((L : ℝ) * (M * M')) := by
  rw [primBil]
  refine Decay.norm_W_sum_le W I.length _ (by positivity) fun k hk l hl => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have hKL : ∀ a : ZMod L, ‖K (I.cutGlueL k l a)‖ ≤ M := fun a =>
    hK _ (LoopIdx.WF.cutGlueL a hI hk.1 hl.1 hl.2)
      (LoopIdx.two_le_length_cutGlueL I a hk.1 hl.1 hl.2)
      (LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2)
  have hKR : ∀ b : ZMod L, ‖K' (I.cutGlueR k l b)‖ ≤ M' := fun b =>
    hK' _ (LoopIdx.WF.cutGlueR b hI hk.1 hl.1 hl.2)
      (LoopIdx.two_le_length_cutGlueR I b hk.1 hl.1 hl.2)
      (LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2)
  calc ‖∑ a : ZMod L, ∑ b : ZMod L,
        K (I.cutGlueL k l a) * SB L a b * K' (I.cutGlueR k l b)‖
      ≤ ∑ a : ZMod L, ∑ b : ZMod L,
        ‖K (I.cutGlueL k l a) * SB L a b * K' (I.cutGlueR k l b)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a : ZMod L, ∑ b : ZMod L, M * M' * ‖SB L _a b‖ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_mul]
        calc ‖K (I.cutGlueL k l a)‖ * ‖SB L a b‖ * ‖K' (I.cutGlueR k l b)‖
            ≤ M * ‖SB L a b‖ * M' := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right (hKL a) (norm_nonneg _))
                (hKR b) (norm_nonneg _) (by positivity)
          _ = M * M' * ‖SB L a b‖ := by ring
    _ = (L : ℝ) * (M * M') := by
        have hrow : ∀ a : ZMod L, (∑ b : ZMod L, M * M' * ‖SB L a b‖) = M * M' := by
          intro a
          rw [← Finset.mul_sum, sum_norm_SB_apply_row L hL a, mul_one]
        rw [Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_const, Finset.card_univ,
          ZMod.card, nsmul_eq_mul]

end Crude


/-! ### §2  The six Step 6 theorems, with the envelope read on the window

The statements below are `RBM.unifDetDom_driftELK`, `RBM.fastDecayHyp_driftSplit`,
`RBM.unifDetDom_driftEG`, `RBM.driftBound_driftEG`, `RBM.sharpExpect_step6_driftEG` and
`RBM.sharpExpect_step6_driftSplit` with **one change**: the hypotheses
`hmeasQ`/`hmeasG`/`hmeasLK`, `henvQ`/`henvG`/`henvLK` and `hintL1`/`hintL` quantify the time
over `RBM.TimeIcc s t N` instead of over `ℝ`.  Nothing else moves — same conclusion, same
remaining hypotheses, same proofs, which read those hypotheses at the window point that the
proof already had in scope.

A mechanical scan of `Gauss/Step6DriftSplit.lean` and `Gauss/Step6DriftEG.lean` for
`(henv… | hmeas… | hintL…) : ∀ (N : ℕ) (v : ℝ)` returns exactly those **six** declarations;
T205's list named five, missing `RBM.sharpExpect_step6_driftSplit`, which is vacuous for the
same reason and is primed here too.

The unprimed versions are kept (frozen signatures) but have no producer and cannot have one:
`RBM.Gauss.not_exists_env_eG` refutes their `henvG` family outright. -/

section Window

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

open Real in
set_option maxHeartbeats 1000000 in
/-- **Window form of `RBM.unifDetDom_driftELK`.**  Only the quantifier on the time changes; see the
header of this file and `RBM.Gauss.not_exists_env_eG` for why the `ℝ`-quantified form has no
producer. -/
theorem unifDetDom_driftELK' (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {Env : ℕ → ℝ} {Kenv Blow : ℝ}
    (hmeas : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (lkPath X E N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (henv : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N)
    (hKenv : 0 ≤ Kenv) (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hB : 0 ≤ Blow)
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-Blow)
      ≤ (B.W N : ℝ) * B.ell N (u : ℝ) * (B.scale E N (u : ℝ))⁻¹ ^ 4)
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ))) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) =>
        ‖driftELK X E N p.1 p.2.1 p.2.2‖)
      (fun N p => (B.W N : ℝ) * B.ell N p.1 * (B.scale E N p.1)⁻¹ ^ 4) := by
  have hP := B.isProbabilityMeasure
  intro τ hτ
  set τ₁ : ℝ := τ / 8 with hτ₁def
  have hτ₁ : 0 < τ₁ := by rw [hτ₁def]; linarith
  set D₁ : ℝ := Blow + Kenv + τ₁ + 4 with hD₁def
  have hD₁ : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hin τ₁ hτ₁ D₁ hD₁ D₁ hD₁,
    SumZeroDyn.flow_crude hE hs0 hst ht1 hc, hEnvpoly, hlow,
    SumZeroDyn.eventually_const_mul_rpow_le (24 * exp 1)
      (show 3 * τ₁ < τ / 2 by rw [hτ₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 4
      (show 2 + τ₁ - D₁ < -Blow - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 1
      (show Kenv - D₁ < -Blow - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 2 (show τ / 2 < τ by linarith),
    eventually_ge_atTop 2] with N hgood hcr hEnvN hlowN hmainN herr1N herr2N hfinN hN2
  obtain ⟨hLN, hWN, _, hu⟩ := hcr
  rintro ⟨v, q⟩
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set u : ℝ := (v : ℝ) with hudef
  have hu0 : 0 ≤ u := (hs0 N).trans v.2.1
  have hu1 : u < 1 := v.2.2.trans_lt (ht1 N)
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hA : 1 ≤ B.scale E N u := (hu v).1
  have hA0 : (0 : ℝ) < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hell : (1 : ℝ) / 2 ≤ B.ell N u := by
    have := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    rw [Band.ell]; linarith
  set Gt : ℝ := (B.W N : ℝ) * B.ell N u * (B.scale E N u)⁻¹ ^ 4 with hGtdef
  have hGt0 : 0 ≤ Gt := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (B.scale E N u)⁻¹ ^ 4 := by positivity
    have hℓ0 : (0 : ℝ) ≤ B.ell N u := by linarith
    rw [hGtdef]; positivity
  have hGtlow : (N : ℝ) ^ (-Blow) ≤ Gt := hlowN v
  set Krad : ℝ := (N : ℝ) ^ τ₁ with hKraddef
  set δ : ℝ := (N : ℝ) ^ (-D₁) with hδdef
  have hKrad1 : (1 : ℝ) ≤ Krad := Real.one_le_rpow hN1' hτ₁.le
  have hδ0 : (0 : ℝ) ≤ δ := Real.rpow_nonneg hN0.le _
  -- the pointwise bound on the good set
  set c : ℝ := 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt + 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
    with hcdef
  have hc0 : 0 ≤ c := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    have hK0 : (0 : ℝ) ≤ Krad := by linarith
    rw [hcdef]
    have h1 : (0 : ℝ) ≤ 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt := by positivity
    have h2 : (0 : ℝ) ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad := by positivity
    linarith
  have hpt : ∀ ω ∈ QuadInputs X E s t N Krad δ Krad,
      ‖primBil (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω)
        (LoopData.idx (q.1, q.2))‖ ≤ c := by
    intro ω hω
    obtain ⟨hDd, hΨ⟩ := hω v
    have hxi0 : 0 ≤ X.xiLK E N u ω 2 := X.xiLK_nonneg hA0.le
    have hbase := norm_primBil_lkPath_le X N ω q.1 q.2 hE hu1 hA hell hKrad1 hδ0 hDd
    refine hbase.trans ?_
    rw [hcdef, ← hGtdef]
    have h1 : X.xiLK E N u ω 2 ^ 2 ≤ Krad ^ 2 := by
      have : X.xiLK E N u ω 2 ≤ Krad := hΨ
      nlinarith
    have hcoef : (0 : ℝ) ≤ 8 * exp 1 * (Krad + 2) := by
      have : (0 : ℝ) ≤ Krad := by linarith
      positivity
    have hWLd : (0 : ℝ) ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) := by
      have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
      have hL : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
      positivity
    have hA' : 8 * exp 1 * (Krad + 2) * X.xiLK E N u ω 2 ^ 2 * Gt
        ≤ 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt := by
      have := mul_le_mul_of_nonneg_left h1 hcoef
      exact mul_le_mul_of_nonneg_right this hGt0
    have hB' : 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * X.xiLK E N u ω 2
        ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad :=
      mul_le_mul_of_nonneg_left hΨ hWLd
    linarith
  -- the first moment
  have hbad : (B.P (QuadInputs X E s t N Krad δ Krad)ᶜ).toReal ≤ δ :=
    ENNReal.toReal_le_of_le_ofReal hδ0 hgood
  have hstep : ‖driftELK X E N v q.1 q.2‖ ≤ c + Env N * δ := by
    have := norm_integral_le_add_measure_compl (P := B.P)
      (f := fun ω => primBil (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω)
        (LoopData.idx (q.1, q.2)))
      (hmeas N v q.1 q.2) (G := QuadInputs X E s t N Krad δ Krad) hc0 hpt
      (fun ω => henv N v q.1 q.2 ω)
    refine this.trans ?_
    have := mul_le_mul_of_nonneg_left hbad (hEnv0 N)
    linarith
  refine hstep.trans ?_
  -- the `Ξ`-bookkeeping: main term, two errors
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have h2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) * (N : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hW0 : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    rw [h2]; nlinarith
  have hmain : 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt ≤ (N : ℝ) ^ (τ / 2) * Gt := by
    have h3 : Krad + 2 ≤ 3 * Krad := by linarith
    have hK0 : (0 : ℝ) ≤ Krad := by linarith
    have hstep2 : 8 * exp 1 * (Krad + 2) * Krad ^ 2 ≤ 24 * exp 1 * (N : ℝ) ^ (3 * τ₁) := by
      have hk3 : Krad ^ 3 = (N : ℝ) ^ (3 * τ₁) := by
        rw [hKraddef, ← Real.rpow_natCast ((N : ℝ) ^ τ₁) 3, ← Real.rpow_mul hN0.le]
        norm_num [mul_comm]
      have : 8 * exp 1 * (Krad + 2) * Krad ^ 2 ≤ 8 * exp 1 * (3 * Krad) * Krad ^ 2 := by
        have : (0 : ℝ) ≤ 8 * exp 1 * Krad ^ 2 := by positivity
        nlinarith [exp_nonneg (1 : ℝ)]
      calc 8 * exp 1 * (Krad + 2) * Krad ^ 2 ≤ 8 * exp 1 * (3 * Krad) * Krad ^ 2 := this
        _ = 24 * exp 1 * Krad ^ 3 := by ring
        _ = 24 * exp 1 * (N : ℝ) ^ (3 * τ₁) := by rw [hk3]
    exact mul_le_mul_of_nonneg_right (hstep2.trans hmainN) hGt0
  have herr1 : 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad ≤ (N : ℝ) ^ (-Blow - 1) := by
    have he : (N : ℝ) ^ (2 : ℝ) * δ * Krad = (N : ℝ) ^ (2 + τ₁ - D₁) := by
      rw [hδdef, hKraddef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    have hmono : 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
        ≤ 4 * ((N : ℝ) ^ (2 : ℝ) * δ) * Krad := by
      have hK0 : (0 : ℝ) ≤ Krad := by linarith
      have : (B.W N : ℝ) * (B.L N : ℝ) * δ ≤ (N : ℝ) ^ (2 : ℝ) * δ :=
        mul_le_mul_of_nonneg_right hWL hδ0
      nlinarith
    refine hmono.trans ?_
    calc 4 * ((N : ℝ) ^ (2 : ℝ) * δ) * Krad = 4 * ((N : ℝ) ^ (2 : ℝ) * δ * Krad) := by ring
      _ = 4 * (N : ℝ) ^ (2 + τ₁ - D₁) := by rw [he]
      _ ≤ (N : ℝ) ^ (-Blow - 1) := herr1N
  have herr2 : Env N * δ ≤ (N : ℝ) ^ (-Blow - 1) := by
    have h1 : Env N * δ ≤ (N : ℝ) ^ Kenv * δ := mul_le_mul_of_nonneg_right hEnvN hδ0
    have he : (N : ℝ) ^ Kenv * δ = (N : ℝ) ^ (Kenv - D₁) := by
      rw [hδdef, ← Real.rpow_add hN0, sub_eq_add_neg]
    refine h1.trans ?_
    rw [he]
    calc (N : ℝ) ^ (Kenv - D₁) = 1 * (N : ℝ) ^ (Kenv - D₁) := by ring
      _ ≤ (N : ℝ) ^ (-Blow - 1) := herr2N
  have hsumerr : (N : ℝ) ^ (-Blow - 1) + (N : ℝ) ^ (-Blow - 1) ≤ Gt := by
    have hmul : (N : ℝ) ^ (-Blow - 1) * (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ (-Blow) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-Blow - 1) := Real.rpow_nonneg hN0.le _
    have h2 : (N : ℝ) ^ (-Blow - 1) + (N : ℝ) ^ (-Blow - 1) ≤ (N : ℝ) ^ (-Blow) := by
      rw [← hmul, Real.rpow_one]
      nlinarith
    exact h2.trans hGtlow
  have hfin : (N : ℝ) ^ (τ / 2) * Gt + Gt ≤ (N : ℝ) ^ τ * Gt := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' (by linarith)
    have h2 : (N : ℝ) ^ (τ / 2) + 1 ≤ (N : ℝ) ^ τ := by
      have := hfinN
      linarith
    have := mul_le_mul_of_nonneg_right h2 hGt0
    linarith [this]
  rw [hcdef]
  linarith [hmain, herr1, herr2, hsumerr, hfin]


set_option maxHeartbeats 1000000 in
/-- **Window form of `RBM.fastDecayHyp_driftSplit`.**  Only the quantifier on the time changes; see the
header of this file and `RBM.Gauss.not_exists_env_eG` for why the `ℝ`-quantified form has no
producer. -/
theorem fastDecayHyp_driftSplit' (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {Env : ℕ → ℝ} {Kenv KM : ℝ}
    (hmeasQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (lkPath X E N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (hmeasG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ))) (LoopData.idx (σ, a))) B.P)
    (henvQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (henvG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ))) (LoopData.idx (σ, a))‖
        ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv) (hKM : 0 ≤ KM)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X E N (s N) σ))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D)) :
    Step6.FastDecayHyp X E s t (driftELK X E) (driftEG X E) := by
  have hP := B.isProbabilityMeasure
  intro τ hτ D hD
  set τ' : ℝ := τ / 2 with hτ'def
  have hτ' : 0 < τ' := by rw [hτ'def]; linarith
  set D₁ : ℝ := D + KM + Kenv + 4 with hD₁def
  have hD₁ : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hlk τ hτ D hD, hin τ' hτ' D₁ hD₁, hEnvpoly,
    SumZeroDyn.flow_crude hE hs0 hst ht1 hc, B.eventually_le_W_rpow 3 hτ',
    SumZeroDyn.eventually_const_mul_rpow_le 8
      (show 2 + KM - D₁ < -D - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 1
      (show Kenv - D₁ < -D - 1 by rw [hD₁def]; linarith),
    eventually_ge_atTop 2] with N hlkN hinN hEnvN hcr hW3 herr1N herr2N hN2
  obtain ⟨hLN, hWN, _, _⟩ := hcr
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  set δ : ℝ := (N : ℝ) ^ (-D₁) with hδdef
  set M : ℝ := (N : ℝ) ^ KM with hMdef
  have hδ0 : (0 : ℝ) ≤ δ := Real.rpow_nonneg hN0.le _
  have hM0 : (0 : ℝ) ≤ M := Real.rpow_nonneg hN0.le _
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have h2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) * (N : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hW0' : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL0' : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    rw [h2]; nlinarith
  -- `N^{-D} ≤ W^{-D}`
  have hWD : (N : ℝ) ^ (-D) ≤ (B.W N : ℝ) ^ (-D) := by
    have h1 : (0 : ℝ) < (B.W N : ℝ) ^ D := Real.rpow_pos_of_pos hW0 D
    have h2 : (B.W N : ℝ) ^ D ≤ (N : ℝ) ^ D := Real.rpow_le_rpow hW0.le hWN hD.le
    rw [Real.rpow_neg hW0.le, Real.rpow_neg hN0.le, ← one_div, ← one_div]
    exact one_div_le_one_div_of_le h1 h2
  have hsum2 : (N : ℝ) ^ (-D - 1) + (N : ℝ) ^ (-D - 1) ≤ (B.W N : ℝ) ^ (-D) := by
    have hmul : (N : ℝ) ^ (-D - 1) * (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ (-D) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-D - 1) := Real.rpow_nonneg hN0.le _
    have : (N : ℝ) ^ (-D - 1) + (N : ℝ) ^ (-D - 1) ≤ (N : ℝ) ^ (-D) := by
      rw [← hmul, Real.rpow_one]; nlinarith
    exact this.trans hWD
  -- the two error budgets
  have herrEnv : Env N * δ ≤ (N : ℝ) ^ (-D - 1) := by
    have h1 : Env N * δ ≤ (N : ℝ) ^ Kenv * δ := mul_le_mul_of_nonneg_right hEnvN hδ0
    have he : (N : ℝ) ^ Kenv * δ = (N : ℝ) ^ (Kenv - D₁) := by
      rw [hδdef, ← Real.rpow_add hN0, sub_eq_add_neg]
    refine h1.trans ?_
    rw [he]
    calc (N : ℝ) ^ (Kenv - D₁) = 1 * (N : ℝ) ^ (Kenv - D₁) := by ring
      _ ≤ (N : ℝ) ^ (-D - 1) := herr2N
  have hcoefErr : ∀ cc : ℝ, 0 ≤ cc → cc ≤ 8 →
      cc * (B.W N : ℝ) * (B.L N : ℝ) * δ * M ≤ (N : ℝ) ^ (-D - 1) := by
    intro cc hcc0 hcc8
    have he : (N : ℝ) ^ (2 : ℝ) * δ * M = (N : ℝ) ^ (2 + KM - D₁) := by
      rw [hδdef, hMdef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    have hδM : (0 : ℝ) ≤ δ * M := mul_nonneg hδ0 hM0
    have hW0' : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0' : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have hWL0 : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) := mul_nonneg hW0' hL0'
    have hstep : cc * (B.W N : ℝ) * (B.L N : ℝ) * δ * M ≤ 8 * ((N : ℝ) ^ (2 : ℝ) * δ * M) := by
      have hcc : cc * ((B.W N : ℝ) * (B.L N : ℝ)) ≤ 8 * ((B.W N : ℝ) * (B.L N : ℝ)) :=
        mul_le_mul_of_nonneg_right hcc8 hWL0
      calc cc * (B.W N : ℝ) * (B.L N : ℝ) * δ * M
          = cc * ((B.W N : ℝ) * (B.L N : ℝ)) * (δ * M) := by ring
        _ ≤ 8 * ((B.W N : ℝ) * (B.L N : ℝ)) * (δ * M) :=
            mul_le_mul_of_nonneg_right hcc hδM
        _ = 8 * (((B.W N : ℝ) * (B.L N : ℝ)) * (δ * M)) := by ring
        _ ≤ 8 * ((N : ℝ) ^ (2 : ℝ) * (δ * M)) := by
            have := mul_le_mul_of_nonneg_right hWL hδM
            linarith
        _ = 8 * ((N : ℝ) ^ (2 : ℝ) * δ * M) := by ring
    refine hstep.trans ?_
    rw [he]
    exact herr1N
  refine fun σ => ⟨hlkN σ, ?_⟩
  intro v hv
  set vv : TimeIcc s t N := ⟨v, hv⟩ with hvvdef
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hℓ1 : (1 : ℝ) ≤ B.ell N v := by
    have := one_le_ellHat (B.L N) (B.three_le_L N) hv0 hv1
    rw [Band.ell]; exact this
  have hWt1 : (1 : ℝ) ≤ (B.W N : ℝ) ^ τ' := by linarith
  -- the radius arithmetic `2 ℓ_v W^{τ'} + 1 ≤ ℓ_v W^τ`
  have hWW : (B.W N : ℝ) ^ τ' * (B.W N : ℝ) ^ τ' = (B.W N : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; congr 1; rw [hτ'def]; ring
  have hrad : 2 * (B.ell N v * (B.W N : ℝ) ^ τ') + 1 ≤ B.ell N v * (B.W N : ℝ) ^ τ := by
    have h1 : 2 * (B.ell N v * (B.W N : ℝ) ^ τ') + 1
        ≤ B.ell N v * (3 * (B.W N : ℝ) ^ τ') := by nlinarith
    have h2 : B.ell N v * (3 * (B.W N : ℝ) ^ τ')
        ≤ B.ell N v * ((B.W N : ℝ) ^ τ' * (B.W N : ℝ) ^ τ') := by
      have : (3 : ℝ) * (B.W N : ℝ) ^ τ' ≤ (B.W N : ℝ) ^ τ' * (B.W N : ℝ) ^ τ' := by nlinarith
      nlinarith
    rw [← hWW]; linarith
  have hradG : B.ell N v * (B.W N : ℝ) ^ τ' ≤ B.ell N v * (B.W N : ℝ) ^ τ := by
    nlinarith [hrad, hWt1]
  constructor
  · -- the quadratic half
    have hgood : ∀ ω ∈ FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M,
        FastDecay (B.L N) (2 * (B.ell N v * (B.W N : ℝ) ^ τ') + 1)
          (8 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M)
          (fun a : LoopArg (B.L N) 2 => primBil (B.L N) (B.W N) (lkPath X E N v ω)
            (lkPath X E N v ω) (LoopData.idx (σ, a))) := by
      intro ω hω
      obtain ⟨hDd, _, hDb⟩ := hω vv
      exact fastDecay_primBil_lkPath X E N v ω σ hδ0 hM0 hDd hDb
    have hE8 : (0 : ℝ) ≤ 8 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M := by
      have hW0' : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
      have hL0' : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
      positivity
    have hres := fastDecay_integral_of_highProb (P := B.P)
      (G := FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M) hE8 (hmeasQ N vv σ) hgood
      (fun ω a => henvQ N vv σ a ω)
    refine SumZeroDyn.FastDecay.mono (B.L N) hres hrad ?_
    have h1 : 8 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M ≤ (N : ℝ) ^ (-D - 1) :=
      hcoefErr 8 (by norm_num) le_rfl
    have h2 : Env N * (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M)ᶜ).toReal
        ≤ (N : ℝ) ^ (-D - 1) := by
      refine le_trans (mul_le_mul_of_nonneg_left hinN (hEnv0 N)) herrEnv
    linarith [hsum2]
  · -- the `E^{(G)}` half
    have hgood : ∀ ω ∈ FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M,
        FastDecay (B.L N) (B.ell N v * (B.W N : ℝ) ^ τ')
          (2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ)
          (fun a : LoopArg (B.L N) 2 => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
            (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))) := by
      intro ω hω
      obtain ⟨_, hLd, hDb⟩ := hω vv
      exact fastDecay_eG_lkPath X E N v ω σ hLd hDb
    have hE2 : (0 : ℝ) ≤ 2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ := by
      have hW0' : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
      have hL0' : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
      positivity
    have hres := fastDecay_integral_of_highProb (P := B.P)
      (G := FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M) hE2 (hmeasG N vv σ) hgood
      (fun ω a => henvG N vv σ a ω)
    refine SumZeroDyn.FastDecay.mono (B.L N) hres hradG ?_
    have h1 : 2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ ≤ (N : ℝ) ^ (-D - 1) := by
      have := hcoefErr 2 (by norm_num) (by norm_num)
      linarith [this, (by ring : 2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ
        = 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M)]
    have h2 : Env N * (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M)ᶜ).toReal
        ≤ (N : ℝ) ^ (-D - 1) :=
      le_trans (mul_le_mul_of_nonneg_left hinN (hEnv0 N)) herrEnv
    linarith [hsum2]


open Real in
set_option maxHeartbeats 1000000 in
/-- **Window form of `RBM.unifDetDom_driftEG`.**  Only the quantifier on the time changes; see the
header of this file and `RBM.Gauss.not_exists_env_eG` for why the `ℝ`-quantified form has no
producer. -/
theorem unifDetDom_driftEG' (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {Env : ℕ → ℝ} {Kenv : ℝ}
    (hmeasLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (lkPath X E N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (henvLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hintL : ∀ (N : ℕ) (v : TimeIcc s t N) (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N (v : ℝ) ω ⟨[b], [x]⟩) B.P)
    (h526 : UnifDetDom (fun N (p : TimeIcc s t N × ZMod (B.L N)) => ‖Step6.lk1 X E N p.1 p.2‖)
      (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval E N (v : ℝ)))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ))) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) =>
        ‖driftEG X E N p.1 p.2.1 p.2.2‖)
      (fun N p => (B.W N : ℝ) * B.ell N p.1 * (B.scale E N p.1)⁻¹ ^ 4) := by
  have hP := B.isProbabilityMeasure
  have hE : |E| < 2 := by linarith
  obtain ⟨CK, hCK0, hCK⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 3) (by norm_num)
  intro τ hτ
  set τ₁ : ℝ := τ / 8 with hτ₁def
  have hτ₁ : 0 < τ₁ := by rw [hτ₁def]; linarith
  set D₁ : ℝ := 3 + Kenv + τ₁ + 4 with hD₁def
  have hD₁ : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hin τ₁ hτ₁ D₁ hD₁ D₁ hD₁, h526 τ₁ hτ₁, hKd τ₁ hτ₁ D₁ hD₁,
    SumZeroDyn.flow_crude hE hs0 hst ht1 hc, hEnvpoly,
    eventually_rpow_neg_three_le_drift_target B hE hs0 hst ht1 hc,
    SumZeroDyn.eventually_const_mul_rpow_le (12 * exp 1 * (1 + CK))
      (show 3 * τ₁ < τ / 2 by rw [hτ₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 4
      (show 2 + τ₁ - D₁ < -(3 : ℝ) - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 1
      (show Kenv - D₁ < -(3 : ℝ) - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 2 (show τ / 2 < τ by linarith),
    eventually_ge_atTop 2] with
    N hgood h526N hKdN hcr hEnvN hlowN hmainN herr1N herr2N hfinN hN2
  obtain ⟨hLN, hWN, _, hu⟩ := hcr
  rintro ⟨v, q⟩
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set u : ℝ := (v : ℝ) with hudef
  have hu0 : 0 ≤ u := (hs0 N).trans v.2.1
  have hu1 : u < 1 := v.2.2.trans_lt (ht1 N)
  have hA : 1 ≤ B.scale E N u := (hu v).1
  have hA0 : (0 : ℝ) < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hAi1 : (B.scale E N u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  have hAi0 : (0 : ℝ) ≤ (B.scale E N u)⁻¹ := inv_nonneg.2 hA0.le
  have hell : (1 : ℝ) / 2 ≤ B.ell N u := by
    have := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    rw [Band.ell]; linarith
  set Gt : ℝ := (B.W N : ℝ) * B.ell N u * (B.scale E N u)⁻¹ ^ 4 with hGtdef
  have hGt0 : 0 ≤ Gt := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hℓ0 : (0 : ℝ) ≤ B.ell N u := by linarith
    rw [hGtdef]; positivity
  have hGtlow : (N : ℝ) ^ (-(3 : ℝ)) ≤ Gt := hlowN v
  set Krad : ℝ := (N : ℝ) ^ τ₁ with hKraddef
  set δ : ℝ := (N : ℝ) ^ (-D₁) with hδdef
  have hKrad1 : (1 : ℝ) ≤ Krad := Real.one_le_rpow hN1' hτ₁.le
  have hKrad0 : (0 : ℝ) ≤ Krad := by linarith
  have hδ0 : (0 : ℝ) ≤ δ := Real.rpow_nonneg hN0.le _
  have hWLδ0 : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) * δ := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    positivity
  -- the two integrability facts
  have hint1 : ∀ (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => lkPath X E N u ω ⟨[b], [x]⟩) B.P :=
    fun b x => integrable_lkPath_one X E N u b x (hintL N v b x)
  have hintLK : Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N u ω)
      (lkPath X E N u ω) (LoopData.idx (q.1, q.2))) B.P :=
    Integrable.mono' (integrable_const (Env N)) (hmeasLK N v q.1 q.2)
      (Filter.Eventually.of_forall fun ω => henvLK N v q.1 q.2 ω)
  -- the `L - K` half, pathwise on the good set
  set c₁ : ℝ := 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt
    + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad with hc₁def
  have hc₁0 : 0 ≤ c₁ := by
    have h1 : (0 : ℝ) ≤ 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt := by positivity
    have h2 : (0 : ℝ) ≤ 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad := by positivity
    rw [hc₁def]; linarith
  have hptLK : ∀ ω ∈ EGInputs X E s t N Krad δ Krad,
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω)
        (LoopData.idx (q.1, q.2))‖ ≤ c₁ := by
    intro ω hω
    obtain ⟨hDd, hΨ1, hΨ3⟩ := hω v
    have hxi1 : 0 ≤ X.xiLK E N u ω 1 := X.xiLK_nonneg hA0.le
    have hxi3 : 0 ≤ X.xiLK E N u ω 3 := X.xiLK_nonneg hA0.le
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖lkPath X E N u ω ⟨[b], [x]⟩‖ ≤ X.xiLK E N u ω 1 * (B.scale E N u)⁻¹ := by
      intro b x
      have := DriftBound.norm_lk_le X E N u ω hA0.ne' (⟨[b], [x]⟩ : LoopIdx (ZMod (B.L N)))
        rfl (j := 1) rfl
      rwa [pow_one] at this
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length = 3 →
        ‖lkPath X E N u ω J‖ ≤ (X.xiLK E N u ω 3 * (B.scale E N u)⁻¹)
          * (B.scale E N u)⁻¹ ^ 2 := by
      intro J hJ hlen
      have := DriftBound.norm_lk_le X E N u ω hA0.ne' J hJ hlen
      calc ‖lkPath X E N u ω J‖ ≤ X.xiLK E N u ω 3 * (B.scale E N u)⁻¹ ^ 3 := this
        _ = (X.xiLK E N u ω 3 * (B.scale E N u)⁻¹) * (B.scale E N u)⁻¹ ^ 2 := by ring
    have hCΦ : X.xiLK E N u ω 1 * (X.xiLK E N u ω 3 * (B.scale E N u)⁻¹)
        ≤ (Krad * Krad) * (B.scale E N u)⁻¹ := by
      have h1 : X.xiLK E N u ω 1 * X.xiLK E N u ω 3 ≤ Krad * Krad :=
        mul_le_mul hΨ1 hΨ3 hxi3 hKrad0
      calc X.xiLK E N u ω 1 * (X.xiLK E N u ω 3 * (B.scale E N u)⁻¹)
          = (X.xiLK E N u ω 1 * X.xiLK E N u ω 3) * (B.scale E N u)⁻¹ := by ring
        _ ≤ (Krad * Krad) * (B.scale E N u)⁻¹ := mul_le_mul_of_nonneg_right h1 hAi0
    exact norm_eG_two_le N (lkPath X E N u ω) (lkPath X E N u ω) q.1 q.2
      (Ξ := X.xiLK E N u ω 1) (Φ := X.xiLK E N u ω 3 * (B.scale E N u)⁻¹)
      (C := Krad * Krad) (Ξb := Krad)
      hE hu1 hA hell hKrad1 hδ0 hxi1 (by positivity) hX hY hDd hCΦ hΨ1
  have hbad : (B.P (EGInputs X E s t N Krad δ Krad)ᶜ).toReal ≤ δ :=
    ENNReal.toReal_le_of_le_ofReal hδ0 hgood
  have hLKbound : ‖∫ ω, Decay.eG (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω)
      (LoopData.idx (q.1, q.2)) ∂B.P‖ ≤ c₁ + Env N * δ := by
    have := norm_integral_le_add_measure_compl (P := B.P)
      (f := fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω)
        (LoopData.idx (q.1, q.2)))
      (hmeasLK N v q.1 q.2) (G := EGInputs X E s t N Krad δ Krad) hc₁0 hptLK
      (fun ω => henvLK N v q.1 q.2 ω)
    refine this.trans ?_
    have := mul_le_mul_of_nonneg_left hbad (hEnv0 N)
    linarith
  -- the `K` half, deterministic
  set c₂ : ℝ := 4 * exp 1 * (Krad + 2) * (Krad * CK) * Gt
    + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad with hc₂def
  have hKbound : ‖Decay.eG (B.L N) (B.W N) (fun J => ∫ ω, lkPath X E N u ω J ∂B.P)
      (B.Kval E N u) (LoopData.idx (q.1, q.2))‖ ≤ c₂ := by
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖(fun J => ∫ ω, lkPath X E N u ω J ∂B.P) ⟨[b], [x]⟩‖
          ≤ (Krad * (B.scale E N u)⁻¹) * (B.scale E N u)⁻¹ := by
      intro b x
      have heq := norm_integral_lkPath_one X E N u b x (hintL N v true x)
      have hle : ‖Step6.lk1 X E N u x‖ ≤ Krad * (B.scale E N u)⁻¹ ^ 2 := h526N (v, x)
      calc ‖(fun J => ∫ ω, lkPath X E N u ω J ∂B.P) ⟨[b], [x]⟩‖
          = ‖Step6.lk1 X E N u x‖ := heq
        _ ≤ Krad * (B.scale E N u)⁻¹ ^ 2 := hle
        _ = (Krad * (B.scale E N u)⁻¹) * (B.scale E N u)⁻¹ := by ring
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length = 3 →
        ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ 2 := by
      intro J hJ hlen
      have := hCK N u hu0 hu1 J hJ hlen
      simpa using this
    exact norm_eG_two_le N (fun J => ∫ ω, lkPath X E N u ω J ∂B.P) (B.Kval E N u) q.1 q.2
      (Ξ := Krad * (B.scale E N u)⁻¹) (Φ := CK) (C := Krad * CK) (Ξb := Krad)
      hE hu1 hA hell hKrad1 hδ0 (by positivity) (by positivity) hX hY (hKdN v)
      (le_of_eq (by ring)) (mul_le_of_le_one_right hKrad0 hAi1)
  -- assemble
  have hsplit := driftEG_eq_add X E N u q.1 q.2 hint1 hintLK
  have htot : ‖driftEG X E N v q.1 q.2‖ ≤ (c₁ + Env N * δ) + c₂ := by
    rw [show driftEG X E N v q.1 q.2 = driftEG X E N u q.1 q.2 from rfl, hsplit]
    exact (norm_add_le _ _).trans (add_le_add hLKbound hKbound)
  refine htot.trans ?_
  -- the `Ξ`-bookkeeping: one main term, two errors
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have h2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) * (N : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hW0 : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    rw [h2]
    exact mul_le_mul hWN hLN hL0 (hW0.trans hWN)
  have hmain : 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt
      + 4 * exp 1 * (Krad + 2) * (Krad * CK) * Gt ≤ (N : ℝ) ^ (τ / 2) * Gt := by
    have hk3 : Krad ^ 3 = (N : ℝ) ^ (3 * τ₁) := by
      rw [hKraddef, ← Real.rpow_natCast ((N : ℝ) ^ τ₁) 3, ← Real.rpow_mul hN0.le]
      norm_num [mul_comm]
    have hstep : 4 * exp 1 * (Krad + 2) * (Krad * Krad)
        + 4 * exp 1 * (Krad + 2) * (Krad * CK)
        ≤ 12 * exp 1 * (1 + CK) * (N : ℝ) ^ (3 * τ₁) := by
      rw [← hk3]
      have he : (0 : ℝ) ≤ exp 1 := (exp_pos 1).le
      have h1 : Krad + 2 ≤ 3 * Krad := by linarith
      have h2 : Krad + CK ≤ Krad * (1 + CK) := add_le_mul_one_add hKrad1 hCK0
      have hn1 : (0 : ℝ) ≤ Krad * (Krad + CK) := mul_nonneg hKrad0 (by linarith)
      have hinner : (Krad + 2) * (Krad * (Krad + CK))
          ≤ (3 * Krad) * (Krad * (Krad * (1 + CK))) := by
        calc (Krad + 2) * (Krad * (Krad + CK)) ≤ (3 * Krad) * (Krad * (Krad + CK)) :=
              mul_le_mul_of_nonneg_right h1 hn1
          _ ≤ (3 * Krad) * (Krad * (Krad * (1 + CK))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              exact mul_le_mul_of_nonneg_left h2 hKrad0
      calc 4 * exp 1 * (Krad + 2) * (Krad * Krad)
            + 4 * exp 1 * (Krad + 2) * (Krad * CK)
          = (4 * exp 1) * ((Krad + 2) * (Krad * (Krad + CK))) := by ring
        _ ≤ (4 * exp 1) * ((3 * Krad) * (Krad * (Krad * (1 + CK)))) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = 12 * exp 1 * (1 + CK) * Krad ^ 3 := by ring
    calc 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt
          + 4 * exp 1 * (Krad + 2) * (Krad * CK) * Gt
        = (4 * exp 1 * (Krad + 2) * (Krad * Krad)
            + 4 * exp 1 * (Krad + 2) * (Krad * CK)) * Gt := by ring
      _ ≤ (12 * exp 1 * (1 + CK) * (N : ℝ) ^ (3 * τ₁)) * Gt :=
          mul_le_mul_of_nonneg_right hstep hGt0
      _ ≤ (N : ℝ) ^ (τ / 2) * Gt := mul_le_mul_of_nonneg_right hmainN hGt0
  have herr1 : 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
      + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := by
    have he : (N : ℝ) ^ (2 : ℝ) * δ * Krad = (N : ℝ) ^ (2 + τ₁ - D₁) := by
      rw [hδdef, hKraddef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    have hmono : 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
        + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad ≤ 4 * ((N : ℝ) ^ (2 : ℝ) * δ * Krad) := by
      have h1 : (B.W N : ℝ) * (B.L N : ℝ) * δ ≤ (N : ℝ) ^ (2 : ℝ) * δ :=
        mul_le_mul_of_nonneg_right hWL hδ0
      exact two_mul_add_two_mul_le hKrad0 h1
    refine hmono.trans ?_
    rw [he]
    exact herr1N
  have herr2 : Env N * δ ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := by
    have h1 : Env N * δ ≤ (N : ℝ) ^ Kenv * δ := mul_le_mul_of_nonneg_right hEnvN hδ0
    have he : (N : ℝ) ^ Kenv * δ = (N : ℝ) ^ (Kenv - D₁) := by
      rw [hδdef, ← Real.rpow_add hN0, sub_eq_add_neg]
    refine h1.trans ?_
    rw [he]
    calc (N : ℝ) ^ (Kenv - D₁) = 1 * (N : ℝ) ^ (Kenv - D₁) := by ring
      _ ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := herr2N
  have hsumerr : (N : ℝ) ^ (-(3 : ℝ) - 1) + (N : ℝ) ^ (-(3 : ℝ) - 1) ≤ Gt := by
    have hmul : (N : ℝ) ^ (-(3 : ℝ) - 1) * (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := Real.rpow_nonneg hN0.le _
    have h2 : (N : ℝ) ^ (-(3 : ℝ) - 1) + (N : ℝ) ^ (-(3 : ℝ) - 1) ≤ (N : ℝ) ^ (-(3 : ℝ)) := by
      rw [← hmul, Real.rpow_one]
      exact add_self_le_mul_two_le hp hN2'
    exact h2.trans hGtlow
  have hfin : (N : ℝ) ^ (τ / 2) * Gt + Gt ≤ (N : ℝ) ^ τ * Gt := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' (by linarith)
    have h2 : (N : ℝ) ^ (τ / 2) + 1 ≤ (N : ℝ) ^ τ := by linarith [hfinN]
    exact mul_add_le_mul_of_add_one_le h2 hGt0
  rw [hc₁def, hc₂def]
  exact final_arith_eg hmain herr1 herr2 hsumerr hfin


/-- **Window form of `RBM.driftBound_driftEG`.**  Only the quantifier on the time changes; see the
header of this file and `RBM.Gauss.not_exists_env_eG` for why the `ℝ`-quantified form has no
producer. -/
theorem driftBound_driftEG' (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {Env : ℕ → ℝ} {Kenv : ℝ}
    (hmeasLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (lkPath X E N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (henvLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hintL : ∀ (N : ℕ) (v : TimeIcc s t N) (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N (v : ℝ) ω ⟨[b], [x]⟩) B.P)
    (h526 : UnifDetDom (fun N (p : TimeIcc s t N × ZMod (B.L N)) => ‖Step6.lk1 X E N p.1 p.2‖)
      (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval E N (v : ℝ)))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ))) :
    Step6.DriftBound B E s t (driftEG X E) :=
  Step6.driftBound_of_5133 (by linarith : |E| < 2) ht1
    (unifDetDom_driftEG' X hκ0 hκ1 hEκ hs0 hst ht1 hc hmeasLK henvLK hEnv0 hKenv hEnvpoly
      hintL h526 hKd hin)


set_option maxHeartbeats 1000000 in
/-- **Window form of `RBM.sharpExpect_step6_driftEG`.**  Only the quantifier on the time changes; see the
header of this file and `RBM.Gauss.not_exists_env_eG` for why the `ℝ`-quantified form has no
producer.  This is the (2.80) producer
that the (2.71) induction consumes. -/
theorem sharpExpect_step6_driftEG' (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    -- the analytic inputs of the hierarchy (T140/T141/T70)
    (hcont : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT X E N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintL2 : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => X.Lval E N v ω (LoopData.idx (σ, b))) B.P)
    (hintQ : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, b))) B.P)
    (hintG : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, b))) B.P)
    (hEL : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      HasDerivAt (fun q : ℝ => X.ELval E N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma E) (X.H N v ω) (zt E v)
            (LoopData.idx (σ, b))
          + primRhs (B.L N) (B.W N) (X.Lval E N v ω) (LoopData.idx (σ, b))) ∂B.P) v)
    (hintU1 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK X E N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG X E N v σ) a) volume (s N) (u : ℝ))
    -- measurability and the crude envelope
    {Env : ℕ → ℝ} {Kenv KM : ℝ}
    (hmeasQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (lkPath X E N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (hmeasG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ))) (LoopData.idx (σ, a))) B.P)
    (hmeasLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (lkPath X E N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (henvQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (henvG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ))) (LoopData.idx (σ, a))‖
        ≤ Env N)
    (henvLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv) (hKM : 0 ≤ KM)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    -- Lemma 5.9 and the counts (5.76)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X E N (s N) σ))
    (hin59 : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D))
    (hinQ : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hinG : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval E N (v : ℝ)))
    -- (5.132), (5.127), `quad11`, and the `1`-loop integrability
    (h5132 : UnifDetDom (fun N (u : LoopData (B.L N) 2) => X.expErr E N (s N) u.idx)
      (fun N _ => (B.scale E N (s N))⁻¹ ^ 3))
    (h527 : Step6.Eq527 X E s t)
    (hq11 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖Step6.quad11 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hintL1 : ∀ (N : ℕ) (v : TimeIcc s t N) (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N (v : ℝ) ω ⟨[b], [x]⟩) B.P) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr E N p.1 p.2.idx)
      (fun N _ => (B.scale E N (t N))⁻¹ ^ 3) := by
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := by linarith
  exact Step6.sharpExpect_of_hierarchy X hE hs0 hst ht1 hc
    (hierarchy_driftSplit X hE2 hs0 ht1 hcont hintL2 hintQ hintG hEL hintU1 hintU2)
    (fastDecayHyp_driftSplit' X hE hs0 hst ht1 hc hmeasQ hmeasG henvQ henvG hEnv0 hKenv
      hEnvpoly hKM hlk hin59)
    h5132
    (Step6.driftBound_of_5133 hE ht1
      (unifDetDom_driftELK' X hE hs0 hst ht1 hc hmeasQ henvQ hEnv0 hKenv hEnvpoly
        (by norm_num) (eventually_rpow_neg_three_le_drift_target B hE hs0 hst ht1 hc) hinQ))
    (driftBound_driftEG' X hκ0 hκ1 hEκ hs0 hst ht1 hc hmeasLK henvLK hEnv0 hKenv hEnvpoly
      hintL1 (Step6.lemma515 X hκ0 hκ1 hEκ hs0 ht1 h527 hq11) hKd hinG)

set_option maxHeartbeats 1000000 in
/-- **Window form of `RBM.sharpExpect_step6_driftSplit`.**

This is the *sixth* declaration hit by T205's defect, and the one its list missed: the frozen
`RBM.sharpExpect_step6_driftSplit` carries the same `∀ v : ℝ` slots `hmeasQ`/`hmeasG`,
`henvQ`/`henvG`, so `RBM.Gauss.not_exists_env_eG` refutes its `henvG` family too and it is
vacuous exactly as `RBM.sharpExpect_step6_driftEG` was.  Only the quantifier on the time
changes; `hG` — the structural bound (5.134), which `RBM.sharpExpect_step6_driftEG'` discharges
and this one keeps as a hypothesis — is untouched, as is the conclusion. -/
theorem sharpExpect_step6_driftSplit' (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hcont : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT X E N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintL : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => X.Lval E N v ω (LoopData.idx (σ, b))) B.P)
    (hintQ : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, b))) B.P)
    (hintG : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, b))) B.P)
    (hEL : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      HasDerivAt (fun q : ℝ => X.ELval E N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma E) (X.H N v ω) (zt E v)
            (LoopData.idx (σ, b))
          + primRhs (B.L N) (B.W N) (X.Lval E N v ω) (LoopData.idx (σ, b))) ∂B.P) v)
    (hintU1 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK X E N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG X E N v σ) a) volume (s N) (u : ℝ))
    {Env : ℕ → ℝ} {Kenv KM : ℝ}
    (hmeasQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (lkPath X E N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (hmeasG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ))) (LoopData.idx (σ, a))) B.P)
    (henvQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (henvG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ))) (LoopData.idx (σ, a))‖
        ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv) (hKM : 0 ≤ KM)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X E N (s N) σ))
    (hin59 : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D))
    (hinQ : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (h5132 : UnifDetDom (fun N (u : LoopData (B.L N) 2) => X.expErr E N (s N) u.idx)
      (fun N _ => (B.scale E N (s N))⁻¹ ^ 3))
    (h527 : Step6.Eq527 X E s t)
    (hq11 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖Step6.quad11 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hG : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ N (v : TimeIcc s t N) (σ : Fin 2 → Bool)
      (a : LoopArg (B.L N) 2) (Λ : ℝ),
      (∀ a₁ (w : LoopData (B.L N) 3), ‖Step6.mix13 X E N v a₁ w‖ ≤ Λ) →
        ‖driftEG X E N v σ a‖ ≤ Cg * ((B.W N : ℝ) * B.ell N (v : ℝ) * Λ))
    (hint1 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N v ω (Step6.oneLoop a₁)) B.P)
    (hint2 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)) (w : LoopData (B.L N) 3),
      Integrable (fun ω => (X.Lval E N v ω (Step6.oneLoop a₁) - B.Kval E N v (Step6.oneLoop a₁)) *
        (X.Lval E N v ω w.idx - B.Kval E N v w.idx)) B.P)
    (hq13 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × LoopData (B.L N) 3)) =>
      ‖Step6.quad13 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 4)) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr E N p.1 p.2.idx)
      (fun N _ => (B.scale E N (t N))⁻¹ ^ 3) := by
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := by linarith
  exact Step6.sharpExpect_step6 X hκ0 hκ1 hEκ hs0 hst ht1 hc
    (hierarchy_driftSplit X hE2 hs0 ht1 hcont hintL hintQ hintG hEL hintU1 hintU2)
    (fastDecayHyp_driftSplit' X hE hs0 hst ht1 hc hmeasQ hmeasG henvQ henvG hEnv0 hKenv
      hEnvpoly hKM hlk hin59)
    h5132
    (unifDetDom_driftELK' X hE hs0 hst ht1 hc hmeasQ henvQ hEnv0 hKenv hEnvpoly
      (by norm_num) (eventually_rpow_neg_three_le_drift_target B hE hs0 hst ht1 hc) hinQ)
    h527 hq11 hG hint1 hint2 hq13

end Window

/-! ### §3  The window envelope, and that it exists

`R_N = max(1, η_{t_N}^{-1})` is the only scale a loop of length `≤ 3` can reach on the window:
`|L_J| ≤ R_N^{|J|}` for every `ω` (`RBM.Gauss.norm_gloop_le_det`, which is deterministic), and
`|K_J| ≤ C R_N^3` by (2.59).  So `|L - K| ≤ (1+C) R_N^3`, and the two drift tensors, being
`W · (at most 4 cuts) · (an `S^{(B)}`-row, mass `1`) · (two such loops)`, are bounded by
`4 W L ((1+C) R_N^3)^2`.  Off the window this fails — and not by a constant:
`RBM.Gauss.not_exists_env_eG`. -/

section EnvWindow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `η` is antitone in the time: `η_t ≤ η_v` for `v ≤ t`. -/
theorem etaT_le_of_le_window {E : ℝ} (hE : |E| < 2) {u w : ℝ} (huw : u ≤ w) :
    etaT E w ≤ etaT E u := by
  show (1 - w) * (mE E).im ≤ (1 - u) * (mE E).im
  exact mul_le_mul_of_nonneg_right (by linarith) (mE_im_pos hE).le

/-- The window floor `R_N = max(1, η_{t_N}^{-1})`. -/
noncomputable def envFloor (E : ℝ) (t : ℕ → ℝ) (N : ℕ) : ℝ :=
  max 1 (etaT E (t N))⁻¹

theorem one_le_envFloor (E : ℝ) (t : ℕ → ℝ) (N : ℕ) :
    1 ≤ envFloor E t N := le_max_left _ _

theorem envFloor_nonneg (E : ℝ) (t : ℕ → ℝ) (N : ℕ) :
    0 ≤ envFloor E t N := le_trans zero_le_one (one_le_envFloor E t N)

/-- Every loop of length `1 ≤ n ≤ 3` of the flow is bounded by `R_N^3` on the window. -/
theorem norm_gloop_flow_le_envFloor (X : Sample B) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (ht1 : ∀ N, t N < 1) (N : ℕ) (v : TimeIcc s t N) (ω : Ω)
    (J : LoopIdx (ZMod (B.L N))) (hJ : J.WF) (hn : 1 ≤ J.length) (h3 : J.length ≤ 3) :
    ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)) J‖ ≤ envFloor E t N ^ 3 := by
  have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
  have hηt : 0 < etaT E (t N) := etaT_pos hE (ht1 N)
  have hηv : 0 < etaT E (v : ℝ) := etaT_pos hE hv1
  have hmono : etaT E (t N) ≤ etaT E (v : ℝ) := etaT_le_of_le_window hE v.2.2
  have hR : (etaT E (v : ℝ))⁻¹ ≤ envFloor E t N :=
    le_trans (inv_anti₀ hηt hmono) (le_max_right _ _)
  have hR0 : 0 ≤ (etaT E (v : ℝ))⁻¹ := inv_nonneg.2 hηv.le
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hbase := Gauss.norm_gloop_le_det (X.hermitian N (v : ℝ) ω) hE hv1 J hJ hn
  refine hbase.trans ?_
  have hWle : ((B.W N : ℝ))⁻¹ ^ (J.length - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
  have h1 : (etaT E (v : ℝ))⁻¹ ^ J.length ≤ envFloor E t N ^ J.length :=
    pow_le_pow_left₀ hR0 hR _
  have h2 : envFloor E t N ^ J.length ≤ envFloor E t N ^ 3 :=
    pow_le_pow_right₀ (one_le_envFloor E t N) h3
  calc (etaT E (v : ℝ))⁻¹ ^ J.length * ((B.W N : ℝ))⁻¹ ^ (J.length - 1)
      ≤ (etaT E (v : ℝ))⁻¹ ^ J.length * 1 :=
        mul_le_mul_of_nonneg_left hWle (by positivity)
    _ = (etaT E (v : ℝ))⁻¹ ^ J.length := mul_one _
    _ ≤ envFloor E t N ^ 3 := h1.trans h2

/-- `K` at loop lengths `1, 2, 3` is bounded by `C R_N^3` on the window, with one constant. -/
theorem exists_norm_Kval_le_envFloor (B : Band Ω) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (v : TimeIcc s t N) (J : LoopIdx (ZMod (B.L N))),
      J.WF → 1 ≤ J.length → J.length ≤ 3 →
        ‖B.Kval E N (v : ℝ) J‖ ≤ C * envFloor E t N ^ 3 := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  obtain ⟨C1, hC10, hC1⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 1) le_rfl
  obtain ⟨C2, hC20, hC2⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 2) (by norm_num)
  obtain ⟨C3, hC30, hC3⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 3) (by norm_num)
  refine ⟨max C1 (max C2 C3), le_max_of_le_left hC10, fun N v J hJ hn h3 => ?_⟩
  have hv0 : 0 ≤ (v : ℝ) := (hs0 N).trans v.2.1
  have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
  have hηt : 0 < etaT E (t N) := etaT_pos hE (ht1 N)
  have hmono : etaT E (t N) ≤ etaT E (v : ℝ) := etaT_le_of_le_window hE v.2.2
  -- `η_v ≤ W ℓ_v η_v` because `W ≥ 1` and `ℓ_v ≥ 1`
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hell : (1 : ℝ) ≤ B.ell N (v : ℝ) := one_le_ellHat (B.L N) (B.three_le_L N) hv0 hv1
  have hηv : 0 < etaT E (v : ℝ) := etaT_pos hE hv1
  have hWl : (1 : ℝ) ≤ (B.W N : ℝ) * B.ell N (v : ℝ) := by nlinarith
  have hscale : etaT E (v : ℝ) ≤ B.scale E N (v : ℝ) := by
    show etaT E (v : ℝ) ≤ (B.W N : ℝ) * B.ell N (v : ℝ) * etaT E (v : ℝ)
    calc etaT E (v : ℝ) = 1 * etaT E (v : ℝ) := (one_mul _).symm
      _ ≤ ((B.W N : ℝ) * B.ell N (v : ℝ)) * etaT E (v : ℝ) :=
          mul_le_mul_of_nonneg_right hWl hηv.le
  have hscale0 : 0 < B.scale E N (v : ℝ) := lt_of_lt_of_le hηv hscale
  have hinv : (B.scale E N (v : ℝ))⁻¹ ≤ envFloor E t N :=
    le_trans (le_trans (inv_anti₀ hηv hscale) (inv_anti₀ hηt hmono))
      (le_max_right _ _)
  have hinv0 : (0 : ℝ) ≤ (B.scale E N (v : ℝ))⁻¹ := inv_nonneg.2 hscale0.le
  have hpow : ∀ n : ℕ, n ≤ 3 → (B.scale E N (v : ℝ))⁻¹ ^ n ≤ envFloor E t N ^ 3 := by
    intro n hn3
    exact (pow_le_pow_left₀ hinv0 hinv n).trans
      (pow_le_pow_right₀ (one_le_envFloor E t N) hn3)
  have hCmax : ∀ (c : ℝ) (n : ℕ), 0 ≤ c → c ≤ max C1 (max C2 C3) → n ≤ 4 →
      ‖B.Kval E N (v : ℝ) J‖ ≤ c * (B.scale E N (v : ℝ))⁻¹ ^ (n - 1) →
      ‖B.Kval E N (v : ℝ) J‖ ≤ max C1 (max C2 C3) * envFloor E t N ^ 3 := by
    intro c n hc0 hcle hn4 hb
    refine hb.trans ?_
    have h1 : c * (B.scale E N (v : ℝ))⁻¹ ^ (n - 1) ≤ c * envFloor E t N ^ 3 :=
      mul_le_mul_of_nonneg_left (hpow _ (by omega)) hc0
    exact h1.trans (mul_le_mul_of_nonneg_right hcle (pow_nonneg (envFloor_nonneg E t N) 3))
  have hcases : J.length = 1 ∨ J.length = 2 ∨ J.length = 3 := by omega
  rcases hcases with h | h | h
  · exact hCmax C1 1 hC10 (le_max_left _ _) (by norm_num) (hC1 N (v : ℝ) hv0 hv1 J hJ h)
  · exact hCmax C2 2 hC20 (le_max_of_le_right (le_max_left _ _)) (by norm_num)
      (hC2 N (v : ℝ) hv0 hv1 J hJ h)
  · exact hCmax C3 3 hC30 (le_max_of_le_right (le_max_right _ _)) (by norm_num)
      (hC3 N (v : ℝ) hv0 hv1 J hJ h)

theorem exists_env_window (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT E (t N)) :
    ∃ (Env : ℕ → ℝ) (Kenv : ℝ), 0 ≤ Kenv ∧ (∀ N, 0 ≤ Env N) ∧
      (∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv) ∧
      (∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
          (LoopData.idx (σ, a))‖ ≤ Env N) ∧
      (∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
          (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)))
          (LoopData.idx (σ, a))‖ ≤ Env N) ∧
      (∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
          (LoopData.idx (σ, a))‖ ≤ Env N) := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  obtain ⟨C, hC0, hC⟩ := exists_norm_Kval_le_envFloor B hκ0 hκ1 hEκ hs0 ht1
  -- the pointwise loop envelope `M N = (1 + C) R_N^3`
  have hM0 : ∀ N : ℕ, 0 ≤ (1 + C) * envFloor E t N ^ 3 := fun N => by
    have := pow_nonneg (envFloor_nonneg E t N) 3; nlinarith
  have hgl : ∀ (N : ℕ) (v : TimeIcc s t N) (ω : Ω) (J : LoopIdx (ZMod (B.L N))),
      J.WF → 1 ≤ J.length → J.length ≤ 3 →
      ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)) J‖
        ≤ (1 + C) * envFloor E t N ^ 3 := by
    intro N v ω J hJ hn h3
    refine (norm_gloop_flow_le_envFloor X hE ht1 N v ω J hJ hn h3).trans ?_
    have := pow_nonneg (envFloor_nonneg E t N) 3
    nlinarith
  have hlk : ∀ (N : ℕ) (v : TimeIcc s t N) (ω : Ω) (J : LoopIdx (ZMod (B.L N))),
      J.WF → 1 ≤ J.length → J.length ≤ 3 →
      ‖lkPath X E N (v : ℝ) ω J‖ ≤ (1 + C) * envFloor E t N ^ 3 := by
    intro N v ω J hJ hn h3
    have h1 := norm_gloop_flow_le_envFloor X hE ht1 N v ω J hJ hn h3
    have h2 := hC N v J hJ hn h3
    calc ‖lkPath X E N (v : ℝ) ω J‖
        = ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)) J
            - B.Kval E N (v : ℝ) J‖ := rfl
      _ ≤ ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)) J‖
            + ‖B.Kval E N (v : ℝ) J‖ := norm_sub_le _ _
      _ ≤ envFloor E t N ^ 3 + C * envFloor E t N ^ 3 := add_le_add h1 h2
      _ = (1 + C) * envFloor E t N ^ 3 := by ring
  refine ⟨fun N => 4 * (B.W N : ℝ) * (B.L N : ℝ) * ((1 + C) * envFloor E t N ^ 3) ^ 2,
    2 + 6 * c, by linarith, fun N => ?_, ?_, ?_, ?_, ?_⟩
  · have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have := hM0 N
    positivity
  · -- the polynomial bound
    filter_upwards [hη, B.dim, eventually_ge_atTop 1,
      SumZeroDyn.eventually_const_mul_rpow_le (4 * (1 + C) ^ 2)
        (show 1 + 6 * c < 2 + 6 * c by linarith)] with N hηN hdimN hN1 hfinN
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    set A : ℝ := (N : ℝ) ^ c with hAdef
    have hA1 : (1 : ℝ) ≤ A := Real.one_le_rpow hN1' hc0
    have hηt : 0 < etaT E (t N) := etaT_pos hE (ht1 N)
    have hRA : envFloor E t N ≤ A := by
      refine max_le hA1 ?_
      have hpos : (0 : ℝ) < (N : ℝ) ^ (-c) := Real.rpow_pos_of_pos hN0 _
      have := inv_anti₀ hpos hηN
      rwa [Real.rpow_neg hN0.le, inv_inv] at this
    have hR0 : 0 ≤ envFloor E t N := envFloor_nonneg E t N
    have hA0 : (0 : ℝ) ≤ A := by linarith
    have h3 : envFloor E t N ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ hR0 hRA 3
    have hA30 : (0 : ℝ) ≤ A ^ 3 := by positivity
    have hMA : (1 + C) * envFloor E t N ^ 3 ≤ (1 + C) * A ^ 3 := by nlinarith
    have hMsq : ((1 + C) * envFloor E t N ^ 3) ^ 2 ≤ ((1 + C) * A ^ 3) ^ 2 :=
      pow_le_pow_left₀ (hM0 N) hMA 2
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by
      have : ((B.W N * B.L N : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hdimN.1
      push_cast at this; linarith
    have hA6 : A ^ 6 = (N : ℝ) ^ (6 * c) := by
      rw [hAdef, ← Real.rpow_natCast ((N : ℝ) ^ c) 6, ← Real.rpow_mul hN0.le]
      norm_num [mul_comm]
    have hstep : 4 * (B.W N : ℝ) * (B.L N : ℝ) * ((1 + C) * envFloor E t N ^ 3) ^ 2
        ≤ 4 * (1 + C) ^ 2 * ((N : ℝ) * A ^ 6) := by
      have hWL0 : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) :=
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hsq0 : (0 : ℝ) ≤ ((1 + C) * A ^ 3) ^ 2 := by positivity
      calc 4 * (B.W N : ℝ) * (B.L N : ℝ) * ((1 + C) * envFloor E t N ^ 3) ^ 2
          = 4 * ((B.W N : ℝ) * (B.L N : ℝ)) * ((1 + C) * envFloor E t N ^ 3) ^ 2 := by ring
        _ ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ)) * ((1 + C) * A ^ 3) ^ 2 := by nlinarith
        _ ≤ 4 * (N : ℝ) * ((1 + C) * A ^ 3) ^ 2 := by nlinarith
        _ = 4 * (1 + C) ^ 2 * ((N : ℝ) * A ^ 6) := by ring
    refine hstep.trans ?_
    have hprod : (N : ℝ) * A ^ 6 = (N : ℝ) ^ (1 + 6 * c) := by
      rw [hA6, Real.rpow_add hN0, Real.rpow_one]
    rw [hprod]
    exact hfinN
  · -- `henvQ`
    intro N v σ a ω
    have hlen2 : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length = 2 := by
      show (List.ofFn a).length = 2
      rw [List.length_ofFn]
    have hK : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length →
        J.length ≤ (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length →
        ‖lkPath X E N (v : ℝ) ω J‖ ≤ (1 + C) * envFloor E t N ^ 3 := by
      intro J hJ h2 hle
      rw [hlen2] at hle
      exact hlk N v ω J hJ (by omega) (by omega)
    have hbound := norm_primBil_le_crude (B.three_le_L N) (B.W N)
      (I := LoopData.idx (σ, a)) (LoopData.idx_wf _) (hM0 N) (hM0 N) hK hK
    rw [hlen2] at hbound
    refine hbound.trans ?_
    push_cast
    have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have := hM0 N
    nlinarith [mul_nonneg (mul_nonneg hW0 hL0) (mul_nonneg this this)]
  · -- `henvG`
    intro N v σ a ω
    have hlen2 : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length = 2 := by
      show (List.ofFn a).length = 2
      rw [List.length_ofFn]
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖lkPath X E N (v : ℝ) ω ⟨[b], [x]⟩‖ ≤ (1 + C) * envFloor E t N ^ 3 :=
      fun b x => hlk N v ω ⟨[b], [x]⟩ rfl le_rfl (by show (1 : ℕ) ≤ 3; norm_num)
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
        J.length = (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length + 1 →
        ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)) J‖
          ≤ (1 + C) * envFloor E t N ^ 3 := by
      intro J hJ hJlen
      rw [hlen2] at hJlen
      exact hgl N v ω J hJ (by omega) (by omega)
    have hbound := norm_eG_le_crude (B.three_le_L N) (B.W N)
      (I := LoopData.idx (σ, a)) (LoopData.idx_wf _) (hM0 N) hX hY
    rw [hlen2] at hbound
    refine hbound.trans ?_
    push_cast
    have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have := hM0 N
    nlinarith [mul_nonneg (mul_nonneg hW0 hL0) (mul_nonneg this this)]
  · -- `henvLK`
    intro N v σ a ω
    have hlen2 : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length = 2 := by
      show (List.ofFn a).length = 2
      rw [List.length_ofFn]
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖lkPath X E N (v : ℝ) ω ⟨[b], [x]⟩‖ ≤ (1 + C) * envFloor E t N ^ 3 :=
      fun b x => hlk N v ω ⟨[b], [x]⟩ rfl le_rfl (by show (1 : ℕ) ≤ 3; norm_num)
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
        J.length = (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length + 1 →
        ‖lkPath X E N (v : ℝ) ω J‖ ≤ (1 + C) * envFloor E t N ^ 3 := by
      intro J hJ hJlen
      rw [hlen2] at hJlen
      exact hlk N v ω J hJ (by omega) (by omega)
    have hbound := norm_eG_le_crude (B.three_le_L N) (B.W N)
      (I := LoopData.idx (σ, a)) (LoopData.idx_wf _) (hM0 N) hX hY
    rw [hlen2] at hbound
    refine hbound.trans ?_
    push_cast
    have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have := hM0 N
    nlinarith [mul_nonneg (mul_nonneg hW0 hL0) (mul_nonneg this this)]

end EnvWindow

/-! ### §4  The positive witness, on the grid window and at the refuted energy

`RBM.Gauss.not_exists_env_eG` (T205) refutes `henvG` at `E = 0` when the time runs over all of
`ℝ`.  Here is the converse on the window: at the *same* energy, on the window
`[1 - 1/(N+2), 1 - 1/(N+3)]` — which is not degenerate (`s_N > 0`, `s_N < t_N`, and
`1 - t_N ≍ N^{-1}` is the hardest end of the range of Theorem 2.21, not a collapsed scale) —
an envelope exists, explicitly, and is polynomially bounded. -/

section GridWitness

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `s_N = 1 - 1/(N+2)`, the left end of the witness window. -/
noncomputable def envWinS (N : ℕ) : ℝ := 1 - ((N : ℝ) + 2)⁻¹

/-- `t_N = 1 - 1/(N+3)`, the right end of the witness window: `1 - t_N ≍ N^{-1}`. -/
noncomputable def envWinT (N : ℕ) : ℝ := 1 - ((N : ℝ) + 3)⁻¹

theorem envWinS_pos (N : ℕ) : 0 < envWinS N := by
  have h : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have h2 : ((N : ℝ) + 2)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right; linarith [Nat.cast_nonneg (α := ℝ) N]
  rw [envWinS]; linarith

theorem envWinS_lt_envWinT (N : ℕ) : envWinS N < envWinT N := by
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) < (N : ℝ) + 3 := by linarith
  have : ((N : ℝ) + 3)⁻¹ < ((N : ℝ) + 2)⁻¹ := by
    apply inv_strictAnti₀ (by linarith) (by linarith)
  rw [envWinS, envWinT]; linarith

theorem envWinT_lt_one (N : ℕ) : envWinT N < 1 := by
  have h3 : (0 : ℝ) < ((N : ℝ) + 3)⁻¹ := by positivity
  rw [envWinT]; linarith

/-- On the witness window, `η_{t_N} = 1/(N+3)` at the energy `E = 0`, which is not
super-polynomially small: `N^{-2} ≤ η_{t_N}` for `N ≥ 3`. -/
theorem eventually_rpow_le_etaT_envWinT :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT 0 (envWinT N) := by
  filter_upwards [eventually_ge_atTop 3] with N hN3
  have hN3' : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hm : etaT 0 (envWinT N) = ((N : ℝ) + 3)⁻¹ := by
    show (1 - envWinT N) * (mE 0).im = _
    rw [Gauss.mE_zero, envWinT]
    simp
  have hrpow : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hN0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hm, hrpow]
  exact inv_anti₀ (by linarith) (by nlinarith)

/-- **The positive witness for the window envelope**, at `E = 0` and on the non-degenerate grid
window.  Compare `RBM.Gauss.not_exists_env_eG`: with the time running over all of `ℝ` the same
family has no producer at all. -/
theorem exists_env_window_grid (X : Sample B) :
    (∀ N, 0 < envWinS N) ∧ (∀ N, envWinS N < envWinT N) ∧ (∀ N, envWinT N < 1) ∧
    ∃ (Env : ℕ → ℝ) (Kenv : ℝ), 0 ≤ Kenv ∧ (∀ N, 0 ≤ Env N) ∧
      (∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv) ∧
      (∀ (N : ℕ) (v : TimeIcc envWinS envWinT N) (σ : Fin 2 → Bool)
          (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖primBil (B.L N) (B.W N) (lkPath X 0 N (v : ℝ) ω) (lkPath X 0 N (v : ℝ) ω)
          (LoopData.idx (σ, a))‖ ≤ Env N) ∧
      (∀ (N : ℕ) (v : TimeIcc envWinS envWinT N) (σ : Fin 2 → Bool)
          (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X 0 N (v : ℝ) ω)
          (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt 0 (v : ℝ)))
          (LoopData.idx (σ, a))‖ ≤ Env N) ∧
      (∀ (N : ℕ) (v : TimeIcc envWinS envWinT N) (σ : Fin 2 → Bool)
          (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X 0 N (v : ℝ) ω) (lkPath X 0 N (v : ℝ) ω)
          (LoopData.idx (σ, a))‖ ≤ Env N) :=
  ⟨envWinS_pos, envWinS_lt_envWinT, envWinT_lt_one,
    exists_env_window X (κ := 1) one_pos le_rfl (by norm_num)
      (fun N => (envWinS_pos N).le) envWinT_lt_one (c := 2) (by norm_num)
      eventually_rpow_le_etaT_envWinT⟩

end GridWitness


/-! ### §4b  The same envelope at a single interior time

Instantiating §3 at the degenerate window `s = t = v` gives the pointwise bound in the shape the
*integrability* slots `hintQ`, `hintG` of `RBM.sharpExpect_step6_driftEG'` want — those are
quantified over `0 < v < 1`, not over the window, so they were never affected by T205's defect;
what was missing was a bound, and §1 + §3 supply one. -/

section PointTime

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `N^{-1} ≤ η` for large `N`, for any fixed `η > 0`. -/
theorem eventually_rpow_neg_one_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ η := by
  obtain ⟨k, hk⟩ := exists_nat_gt η⁻¹
  filter_upwards [eventually_ge_atTop (max k 1)] with N hN
  have hNk : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_left k 1) hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_right k 1) hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [Real.rpow_neg hN0.le, Real.rpow_one]
  have h1 : η⁻¹ ≤ (N : ℝ) := le_trans hk.le hNk
  have := inv_anti₀ (inv_pos.2 hη) h1
  rwa [inv_inv] at this

/-- **The drift tensors are bounded at a single interior time**, uniformly in `ω`. -/
theorem exists_norm_drift_le_at (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
          (LoopData.idx (σ, a))‖ ≤ M) ∧
      (∀ (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
          (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))‖ ≤ M) ∧
      (∀ (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
          (LoopData.idx (σ, a))‖ ≤ M) := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  obtain ⟨Env, Kenv, -, hEnv0, -, hQ, hG, hLK⟩ :=
    exists_env_window X hκ0 hκ1 hEκ (s := fun _ => v) (t := fun _ => v)
      (fun _ => hv0) (fun _ => hv1) (c := 1) zero_le_one
      (eventually_rpow_neg_one_le (etaT_pos hE hv1))
  refine ⟨Env N, hEnv0 N, fun σ a ω => hQ N ⟨v, le_rfl, le_rfl⟩ σ a ω,
    fun σ a ω => hG N ⟨v, le_rfl, le_rfl⟩ σ a ω, fun σ a ω => hLK N ⟨v, le_rfl, le_rfl⟩ σ a ω⟩

end PointTime

/-! ### §5  The (2.71) half of the induction step -/

section Step

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The (2.71) half of the induction step of p. 24** — the (2.80) producer of §2 fed into
T205's assembly bridge `RBM.bounds_of_boundsCore_of_sharpExpect`.

Given (2.68)–(2.70) at `t` (which `RBM.Thm221NoEL` delivers from (2.68)–(2.70) at `s`), the
bounds `RBM.Bounds X E s` at `s` — whose field `expect` is exactly (5.132), the `h5132` slot of
Step 6 — and the remaining Step 6 data, this returns `RBM.Bounds X E t`, i.e. (2.68)–(2.71) at
`t`.  The envelope hypotheses are the **window** ones of §2; with the `ℝ`-quantified originals
this statement would be vacuous (`RBM.Gauss.not_exists_env_eG`).

Still open, and visible in the hypothesis list: `hcont`, `hintQ`, `hintG`, `hintU1`, `hintU2`,
`hlk`, `hKd` and the four good sets `hin59`, `hinQ`, `hinG` (through `RBM.FDInputs`,
`RBM.QuadInputs`, `RBM.EGInputs`).  None of them is known to be unsatisfiable; none has a
producer yet. -/
theorem bounds_step_of_step6_window (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    -- the analytic inputs of the hierarchy (T140/T141/T70)
    (hcont : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT X E N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintL2 : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => X.Lval E N v ω (LoopData.idx (σ, b))) B.P)
    (hintQ : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, b))) B.P)
    (hintG : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, b))) B.P)
    (hEL : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      HasDerivAt (fun q : ℝ => X.ELval E N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma E) (X.H N v ω) (zt E v)
            (LoopData.idx (σ, b))
          + primRhs (B.L N) (B.W N) (X.Lval E N v ω) (LoopData.idx (σ, b))) ∂B.P) v)
    (hintU1 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK X E N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG X E N v σ) a) volume (s N) (u : ℝ))
    -- measurability and the crude envelope
    {Env : ℕ → ℝ} {Kenv KM : ℝ}
    (hmeasQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (lkPath X E N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (hmeasG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ))) (LoopData.idx (σ, a))) B.P)
    (hmeasLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (lkPath X E N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (henvQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (henvG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ))) (LoopData.idx (σ, a))‖
        ≤ Env N)
    (henvLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv) (hKM : 0 ≤ KM)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    -- Lemma 5.9 and the counts (5.76)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X E N (s N) σ))
    (hin59 : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D))
    (hinQ : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hinG : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval E N (v : ℝ)))
    -- (5.132), (5.127), `quad11`, and the `1`-loop integrability
    (h527 : Step6.Eq527 X E s t)
    (hq11 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖Step6.quad11 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hintL1 : ∀ (N : ℕ) (v : TimeIcc s t N) (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N (v : ℝ) ω ⟨[b], [x]⟩) B.P)
    (hBC : BoundsCore X E t) (hB : Bounds X E s) :
    Bounds X E t :=
  bounds_of_boundsCore_of_sharpExpect hBC
    (sharpExpect_step6_driftEG' X hκ0 hκ1 hEκ hs0 hst ht1 hc hcont hintL2 hintQ hintG hEL
      hintU1 hintU2 hmeasQ hmeasG hmeasLK henvQ henvG henvLK hEnv0 hKenv hKM hEnvpoly
      hlk hin59 hinQ hinG hKd hB.expect h527 hq11 hintL1) hst

end Step

end RBM

/-! ### §6  The Gaussian producers for the window slots -/

namespace RBM.Gauss

open RBM Finset


theorem continuous_lkPath_gauss (d : Dims) (N : ℕ) {E v : ℝ} (hE : |E| < 2) (hv : v < 1)
    (I : LoopIdx (ZMod ((band d).L N))) :
    Continuous fun ω : Ω d => lkPath (sample d) E N v ω I :=
  (continuous_gloop_Hflow d N v (zt_im_ne_zero_of_lt_one hE hv) I).sub continuous_const

theorem continuous_gloop_flow_gauss (d : Dims) (N : ℕ) {E v : ℝ} (hE : |E| < 2) (hv : v < 1)
    (I : LoopIdx (ZMod ((band d).L N))) :
    Continuous fun ω : Ω d =>
      gloop ((band d).L N) ((band d).W N) ((sample d).H N v ω) (zt E v) I :=
  continuous_gloop_Hflow d N v (zt_im_ne_zero_of_lt_one hE hv) I

theorem continuous_primBil_lkPath_gauss (d : Dims) (N : ℕ) {E v : ℝ} (hE : |E| < 2) (hv : v < 1)
    (I : LoopIdx (ZMod ((band d).L N))) :
    Continuous fun ω : Ω d => primBil ((band d).L N) ((band d).W N)
      (lkPath (sample d) E N v ω) (lkPath (sample d) E N v ω) I := by
  refine continuous_const.mul (continuous_finsetSum _ fun k _ => continuous_finsetSum _
    fun l _ => continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_)
  exact ((continuous_lkPath_gauss d N hE hv _).mul continuous_const).mul
    (continuous_lkPath_gauss d N hE hv _)

theorem continuous_eG_lkPath_gloop_gauss (d : Dims) (N : ℕ) {E v : ℝ} (hE : |E| < 2) (hv : v < 1)
    (I : LoopIdx (ZMod ((band d).L N))) :
    Continuous fun ω : Ω d => Decay.eG ((band d).L N) ((band d).W N)
      (lkPath (sample d) E N v ω)
      (gloop ((band d).L N) ((band d).W N) ((sample d).H N v ω) (zt E v)) I := by
  refine continuous_const.mul (continuous_finsetSum _ fun k _ => continuous_finsetSum _
    fun a _ => continuous_finsetSum _ fun b _ => ?_)
  exact ((continuous_lkPath_gauss d N hE hv _).mul continuous_const).mul
    (continuous_gloop_flow_gauss d N hE hv _)

theorem continuous_eG_lkPath_gauss (d : Dims) (N : ℕ) {E v : ℝ} (hE : |E| < 2) (hv : v < 1)
    (I : LoopIdx (ZMod ((band d).L N))) :
    Continuous fun ω : Ω d => Decay.eG ((band d).L N) ((band d).W N)
      (lkPath (sample d) E N v ω) (lkPath (sample d) E N v ω) I := by
  refine continuous_const.mul (continuous_finsetSum _ fun k _ => continuous_finsetSum _
    fun a _ => continuous_finsetSum _ fun b _ => ?_)
  exact ((continuous_lkPath_gauss d N hE hv _).mul continuous_const).mul
    (continuous_lkPath_gauss d N hE hv _)

/-- `hmeasQ` of `RBM.sharpExpect_step6_driftEG'`, for the Gaussian model. -/
theorem hmeasQ_window (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) :
    ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      AEStronglyMeasurable (fun ω => primBil ((band d).L N) ((band d).W N)
        (lkPath (sample d) E N (v : ℝ) ω) (lkPath (sample d) E N (v : ℝ) ω)
        (LoopData.idx (σ, a))) (band d).P :=
  fun N v σ a => (continuous_primBil_lkPath_gauss d N hE (v.2.2.trans_lt (ht1 N))
    (LoopData.idx (σ, a))).aestronglyMeasurable

/-- `hmeasG` of `RBM.sharpExpect_step6_driftEG'`, for the Gaussian model. -/
theorem hmeasG_window (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) :
    ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG ((band d).L N) ((band d).W N)
        (lkPath (sample d) E N (v : ℝ) ω)
        (gloop ((band d).L N) ((band d).W N) ((sample d).H N (v : ℝ) ω) (zt E (v : ℝ)))
        (LoopData.idx (σ, a))) (band d).P :=
  fun N v σ a => (continuous_eG_lkPath_gloop_gauss d N hE (v.2.2.trans_lt (ht1 N))
    (LoopData.idx (σ, a))).aestronglyMeasurable

/-- `hmeasLK` of `RBM.sharpExpect_step6_driftEG'`, for the Gaussian model. -/
theorem hmeasLK_window (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) :
    ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG ((band d).L N) ((band d).W N)
        (lkPath (sample d) E N (v : ℝ) ω) (lkPath (sample d) E N (v : ℝ) ω)
        (LoopData.idx (σ, a))) (band d).P :=
  fun N v σ a => (continuous_eG_lkPath_gauss d N hE (v.2.2.trans_lt (ht1 N))
    (LoopData.idx (σ, a))).aestronglyMeasurable

/-- `hintL1` of `RBM.sharpExpect_step6_driftEG'`, for the Gaussian model: T150's
`RBM.Gauss.int1_gauss` at both charges. -/
theorem hintL1_window (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) :
    ∀ (N : ℕ) (v : TimeIcc s t N) (b : Bool) (x : ZMod ((band d).L N)),
      Integrable (fun ω => (sample d).Lval E N (v : ℝ) ω ⟨[b], [x]⟩) (band d).P := by
  intro N v b x
  have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
  exact integrable_sample_Lval (etaT_pos_of_lt_one hE hv1) (abs_im_zt E hE hv1).ge
    ⟨[b], [x]⟩ rfl le_rfl

/-- **`hintQ` of `RBM.sharpExpect_step6_driftEG'`, for the Gaussian model.**  The integrand is
continuous in `ω` and deterministically bounded at every interior time
(`RBM.exists_norm_drift_le_at`), on a probability space. -/
theorem hintQ_gauss (d : Dims) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) :
    ∀ (N : ℕ) (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      Integrable (fun ω => primBil ((band d).L N) ((band d).W N)
        (lkPath (sample d) E N v ω) (lkPath (sample d) E N v ω) (LoopData.idx (σ, b)))
        (band d).P := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  intro N v hv0 hv1 σ b
  obtain ⟨M, -, hQ, -, -⟩ := exists_norm_drift_le_at (sample d) hκ0 hκ1 hEκ hv0.le hv1 N
  exact integrable_of_continuous_of_bound
    (continuous_primBil_lkPath_gauss d N hE hv1 (LoopData.idx (σ, b))) (fun ω => hQ σ b ω)

/-- **`hintG` of `RBM.sharpExpect_step6_driftEG'`, for the Gaussian model.** -/
theorem hintG_gauss (d : Dims) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) :
    ∀ (N : ℕ) (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      Integrable (fun ω => Decay.eG ((band d).L N) ((band d).W N)
        (lkPath (sample d) E N v ω)
        (gloop ((band d).L N) ((band d).W N) ((sample d).H N v ω) (zt E v))
        (LoopData.idx (σ, b))) (band d).P := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  intro N v hv0 hv1 σ b
  obtain ⟨M, -, -, hG, -⟩ := exists_norm_drift_le_at (sample d) hκ0 hκ1 hEκ hv0.le hv1 N
  exact integrable_of_continuous_of_bound
    (continuous_eG_lkPath_gloop_gauss d N hE hv1 (LoopData.idx (σ, b))) (fun ω => hG σ b ω)

/-! ### §7  The two directions side by side -/

/-- **The envelope exists on the window and does not exist on `ℝ`.**

The second conjunct is T205's `RBM.Gauss.not_exists_env_eG` verbatim; the first is the window
form of the *same* family at the *same* energy `E = 0`, on the non-degenerate grid window
`[1 - 1/(N+2), 1 - 1/(N+3)]`.  Together they say that the obstruction T205 found is exactly the
quantifier on the time, and nothing else. -/
theorem env_window_vs_not_exists_env_eG (d : Dims) :
    (∃ (Env : ℕ → ℝ) (Kenv : ℝ), 0 ≤ Kenv ∧ (∀ N, 0 ≤ Env N) ∧
      (∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv) ∧
      ∀ (N : ℕ) (v : TimeIcc envWinS envWinT N) (σ : Fin 2 → Bool)
          (a : LoopArg ((band d).L N) 2) (ω : Ω d),
        ‖Decay.eG ((band d).L N) ((band d).W N) (lkPath (sample d) 0 N (v : ℝ) ω)
          (gloop ((band d).L N) ((band d).W N) ((sample d).H N (v : ℝ) ω) (zt 0 (v : ℝ)))
          (LoopData.idx (σ, a))‖ ≤ Env N)
    ∧ ∀ N : ℕ, ¬ ∃ Env : ℝ, ∀ (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2)
        (ω : Ω d),
      ‖Decay.eG ((band d).L N) ((band d).W N) (lkPath (sample d) 0 N v ω)
        (gloop ((band d).L N) ((band d).W N) ((sample d).H N v ω) (zt 0 v))
        (LoopData.idx (σ, a))‖ ≤ Env := by
  refine ⟨?_, fun N => not_exists_env_eG d N⟩
  obtain ⟨-, -, -, Env, Kenv, hK0, hE0, hpoly, -, hG, -⟩ := exists_env_window_grid (sample d)
  exact ⟨Env, Kenv, hK0, hE0, hpoly, hG⟩

/-! ### §8  The (2.71) step for the Gaussian model, with every available slot discharged

`RBM.bounds_step_of_step6_window` carries *all* of Step 6's data as named hypotheses, so it
does not by itself say which of them are still missing.  This section applies it to the
Gaussian model with every slot that has a producer actually plugged in, so that the residual
hypothesis list **is** the gap, checked by the elaborator rather than asserted in a comment. -/

/-- On the grid window, `η_u ≥ N^{-2}` for **every** `u` in the window, not just at its right
end: `η` is antitone (`RBM.etaT_le_of_le_window`) and `u ≤ t_N`.  This is the side condition
`hη` of `RBM.Gauss.quad11_unifDetDom_gauss'` and of `RBM.exists_env_window`. -/
theorem eventually_rpow_le_etaT_window :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc envWinS envWinT N,
      (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT 0 u := by
  filter_upwards [eventually_rpow_le_etaT_envWinT] with N hN u
  exact hN.trans (etaT_le_of_le_window (by norm_num) u.2.2)

/-- **The (2.71) half of the induction step for the Gaussian model.**

Every slot of `RBM.bounds_step_of_step6_window` for which the tree has a producer is discharged
here:

* the envelope `henvQ`/`henvG`/`henvLK`, `hEnv0`, `hKenv`, `hEnvpoly` — `RBM.exists_env_window`
  (§3), the hypothesis family that `RBM.Gauss.not_exists_env_eG` refutes in its `∀ v : ℝ` form;
* `hmeasQ`/`hmeasG`/`hmeasLK` — §6, from `RBM.Gauss.continuous_gloop_Hflow`;
* `hintL1` — §6 (T150's `RBM.Gauss.int1_gauss` shape); `hintL2` — T205's
  `RBM.Gauss.hintL2_gauss`; `hintQ`/`hintG` — §6, from §1 + §3;
* `hEL` — T205's `RBM.Gauss.hEL_gauss`; `h527` — `RBM.Gauss.eq527_gauss`;
* `hq11` — `RBM.Gauss.quad11_unifDetDom_gauss'`, whose side condition `hη` is the one already
  present here.

What is left is exactly the mathematics that is still missing, and nothing else:

* `hcont`, `hintU1`, `hintU2` — continuity in the time of `E L - K` and interval integrability
  of `U` against the two drift tensors;
* `hlk`, `hKd` — the *quantitative* half of Lemma 5.9 (`RBM.exists_loopDecay_Kval` gives the
  decay of `K` at every radius, but with `δ = C(1-v) e^{-c(1-v) ℓ}`, not `N^{-D}`).
  **⚠⚠ T234 refutes the reading of this as a gap**: `RBM.cor35Rate δ = c₀ √δ / 4`, so the decay
  length is `ℓ̂_v` and `RBM.loopDecay_Kval_quant` (§9) proves `hKd` with no hypotheses at all;
  `RBM.Gauss.hlk_gauss` (§12) proves `hlk`.  Both are discharged in
  `RBM.Gauss.bounds_step_gauss_window'`.
* `hin59`, `hinQ`, `hinG` — the `HighProb` producers of `RBM.FDInputs`, `RBM.QuadInputs`,
  `RBM.EGInputs`.  **Produced in T234's §10**; discharged in
  `RBM.Gauss.bounds_step_gauss_window'`.
* `hlmk` — (2.68) uniformly on the window (Steps 1–5 output);
* `hc`, `hη` — the window's own regularity, and `hBC`/`hB`, which are the induction data.

None of these is `ω`-quantified pointwise (`hlk`, `hcont`, `hKd` are statements about the
deterministic `E L - K` and `K`; the three good sets are event-restricted), and the decay
hypotheses are in the paper's `∀ τ, ∀ D, ∀ᶠ N` order. -/
theorem bounds_step_gauss_window (d : Dims) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 (band d) E s t)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT E u)
    (hcont : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT (sample d) E N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintU1 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK (sample d) E N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG (sample d) E N v σ) a) volume (s N) (u : ℝ))
    {KM : ℝ} (hKM : 0 ≤ KM)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay ((band d).L N) ((band d).ell N (s N) * ((band d).W N : ℝ) ^ τ)
        (((band d).W N : ℝ) ^ (-D)) (Step6.lkT (sample d) E N (s N) σ))
    (hin59 : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ((band d).P (FDInputs (sample d) E s t N (((band d).W N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        ((N : ℝ) ^ KM))ᶜ).toReal ≤ (N : ℝ) ^ (-D))
    (hinQ : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb (band d).P (fun N =>
      QuadInputs (sample d) E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hinG : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb (band d).P (fun N =>
      EGInputs (sample d) E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay ((band d).L N) 3 ((band d).ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        ((band d).Kval E N (v : ℝ)))
    (hlmk : SharpLmKFlow (sample d) E s t)
    (hBC : BoundsCore (sample d) E t) (hB : Bounds (sample d) E s) :
    Bounds (sample d) E t := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  have hηt : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT E (t N) := by
    filter_upwards [hη] with N hN
    exact hN ⟨t N, hst N, le_rfl⟩
  obtain ⟨Env, Kenv, hKenv, hEnv0, hEnvpoly, henvQ, henvG, henvLK⟩ :=
    exists_env_window (sample d) hκ0 hκ1 hEκ hs0 ht1 hc0 hηt
  exact bounds_step_of_step6_window (sample d) hκ0 hκ1 hEκ hs0 hst ht1 hc
    hcont (hintL2_gauss d hE) (hintQ_gauss d hκ0 hκ1 hEκ) (hintG_gauss d hκ0 hκ1 hEκ)
    (hEL_gauss d hE) hintU1 hintU2
    (hmeasQ_window d hE ht1) (hmeasG_window d hE ht1) (hmeasLK_window d hE ht1)
    henvQ henvG henvLK hEnv0 hKenv hKM hEnvpoly
    hlk hin59 hinQ hinG hKd
    (eq527_gauss d hE hs0 ht1)
    (quad11_unifDetDom_gauss' d hκ0 hκ1 hEκ hs0 ht1 hc0 hη hlmk)
    (hintL1_window d hE ht1) hBC hB

/-- **The side conditions of `RBM.Gauss.bounds_step_gauss_window` are jointly satisfiable on a
non-degenerate window.**  At `E = 0`, `κ = 1`, `c = 2`, on the grid window
`[1 - 1/(N+2), 1 - 1/(N+3)]`: `s_N > 0` (so this is *not* T205's degenerate `s = t = 0`
witness), `s_N < t_N`, `t_N < 1`, and the scale condition `hη` holds throughout the window.

This is the positive half required after a quantifier repair: the family that
`RBM.Gauss.not_exists_env_eG` refutes on `ℝ` is inhabited here (§4, §7), and the step theorem's
own side conditions are consistent with a window on which that happens.  It does **not** claim
the remaining hypotheses (`hcont`, `hintU1`, `hintU2`, `hlk`, `hin59`, `hinQ`, `hinG`, `hKd`,
`hlmk`, `hc`, `hBC`, `hB`) hold — those are the open gap, and `RBM.Bounds` still has no
inhabitant at `s > 0`. -/
theorem bounds_step_gauss_side_conditions_grid :
    (∀ N, 0 < envWinS N) ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ |(0 : ℝ)| ≤ 2 - 1 ∧
      (∀ N, 0 ≤ envWinS N) ∧ (∀ N, envWinS N ≤ envWinT N) ∧ (∀ N, envWinT N < 1) ∧
      (0 : ℝ) ≤ 2 ∧
      (∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc envWinS envWinT N,
        (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT 0 u) :=
  ⟨envWinS_pos, one_pos, le_rfl, by norm_num, fun N => (envWinS_pos N).le,
    fun N => (envWinS_lt_envWinT N).le, envWinT_lt_one, by norm_num,
    eventually_rpow_le_etaT_window⟩

end RBM.Gauss

namespace RBM

open Real

/-! ### §9  T234: the quantitative half of Lemma 5.9 on the `K` side

The residual-hypothesis list of §8 records `hKd` as "genuinely missing mathematics": the only
producer of the decay of `K`, `RBM.exists_loopDecay_Kval`, delivers
`δ = C_m(1-v) e^{-c(1-v) ℓ}`, and turning that into `N^{-D}` at the radius `ℓ_v N^τ` was read as
needing `c(1-v) · ℓ_v N^τ ≳ D log N`, which fails badly when `1 - v ≍ N^{-1}` and
`ℓ_v ≍ N^{1/2}`.

**That reading is wrong, and the correction is a one-line unfolding.**  The rate of
Corollary 3.5 is `RBM.cor35Rate δ = c₀ √δ / 4` (`RBM1D/Loop/Cor35.lean:366`) — it is
*square-root* in the gap, not linear.  So the decay length of `K` is `δ^{-1/2}`, which at
`δ = 1 - v` is exactly `RBM.ellHat`'s first branch `ℓ̂_v = (1-v)^{-1/2}`; this is the same
sharpened decay length as (2.52), whose `1 - |ξ|` versus `|1 - ξ|` distinction Phase 1 already
settled.  Consequently

  `cor35Rate (1-v) · (ℓ_v · N^τ) = (c₀/4) · N^τ`   (`RBM.cor35Rate_mul_ell_mul`)

whenever the cut-off in `ℓ̂` is inactive (`1 ≤ L √(1-v)`), so the exponential is `e^{-cN^τ}`,
super-polynomially small — there is no `log N` threshold to beat.  In the complementary regime
`L √(1-v) < 1` one has `ℓ_v = L`, so the radius `ℓ_v N^τ` already exceeds the diameter `L/2` of
the ring and the decay statement is vacuous (`RBM.LKDecayQuant.loopDecay_of_half_lt`).

`RBM.loopDecay_Kval_quant` is therefore **unconditional** — no good event, no `FlowInputs`, no
side condition on the scale — and holds at **every** loop length `m`, not only at `m = 3`.  That
discharges `hKd` of §8, the `hKd` of `RBM.unifDetDom_driftEG'`, and the first conjunct of
`RBM.DriftBound.DriftInputs` at loop length `n + 2` (the item T220 handed over).

The arithmetic that turns `C_m(δ) e^{-c₀√δ ℓ/4}` into `N^{-D}` is T126's
`RBM.LKDecayQuant.term2_le`, which is reused verbatim; the only new ingredient is the
identity `RBM.cor35Rate_mul_ell_mul` and the case split on the two branches of `ℓ̂`. -/

section KQuant

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The rate of Corollary 3.5 is `c₀/4` per unit of `N^τ` on the radius `ℓ_v N^τ`.**

`cor35Rate δ = c₀ √δ / 4` and `ℓ̂_v √(1-v) = 1` in the regime where the cut-off in `ℓ̂` is
inactive, so `cor35Rate (1-v) * (ℓ̂_v * A) = (c₀/4) A` — the gap cancels exactly.  This is the
statement that `ℓ̂_v`, not `(1-v)^{-1}`, is the decay length of `K`. -/
theorem cor35Rate_mul_ell_mul (L : ℕ) {u : ℝ} (hu1 : u < 1)
    (h : 1 ≤ (L : ℝ) * Real.sqrt (1 - u)) (A : ℝ) :
    cor35Rate (1 - u) * (ellHat L (u : ℂ) * A) = cZero / 4 * A := by
  have he := LKDecayQuant.ellHat_mul_sqrt_eq_one L hu1 h
  have hid : cor35Rate (1 - u) * (ellHat L (u : ℂ) * A)
      = cZero / 4 * A * (ellHat L (u : ℂ) * Real.sqrt (1 - u)) := by
    unfold cor35Rate; ring
  rw [hid, he, mul_one]

/-- **The `(ℓ_v N^τ, N^{-D})` decay of `K`, uniformly on the window, at every loop length.**

This is the quantitative half of Lemma 5.9 on the `K` side, in exactly the shape `hKd` of
`RBM.unifDetDom_driftEG'` and of `RBM.Gauss.bounds_step_gauss_window` asks for, and at the
general loop length `m` that `RBM.DriftBound.DriftInputs` asks for at `m = n + 2`.

It is *deterministic*: `K` is the tree representation `RBM.Kgen`, a function of `(E, N, v)`
only, so no event and no sample enter.  The quantifier order is the paper's,
`∀ τ, ∀ D, ∀ᶠ N`. -/
theorem loopDecay_Kval_quant (B : Band Ω) {E : ℝ} (hE : |E| ≤ 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (m : ℕ) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) m (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval E N (v : ℝ)) := by
  intro τ hτ D hD
  have hc0 := cZero_pos
  have hexp := SumZeroDyn.eventually_exp_small (2 * LKDecayQuant.cKbound m)
    (((2 * LKDecayQuant.cKexp m : ℕ) : ℝ) + D) (cZero / 2) (by linarith)
    (show (0 : ℝ) < τ / 2 by linarith)
  have h2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ :=
    SumZeroDyn.eventually_const_mul_rpow_le 2 (show τ / 2 < τ by linarith)
  filter_upwards [LKDecayQuant.eventually_L_le (B := B), hexp, h2, eventually_ge_atTop 1]
    with N hLN hexpN h2N hN1
  intro v
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  set uu : ℝ := (v : ℝ) with huu
  have hu0 : 0 ≤ uu := (hs0 N).trans v.2.1
  have hu1 : uu < 1 := v.2.2.trans_lt (ht1 N)
  have hv0 : (0 : ℝ) < 1 - uu := by linarith
  have hv1 : (1 : ℝ) - uu ≤ 1 := by linarith
  have hell1 : (1 : ℝ) ≤ B.ell N uu :=
    one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
  have hNt : (1 : ℝ) ≤ (N : ℝ) ^ τ := by
    calc (1 : ℝ) = (N : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (N : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hNr1 hτ.le
  have hrad0 : (0 : ℝ) < B.ell N uu * (N : ℝ) ^ τ := by nlinarith
  by_cases hcut : 1 ≤ (B.L N : ℝ) * Real.sqrt (1 - uu)
  · -- the cut-off in `ℓ̂` is inactive: the rate is `c₀/4` per unit of `N^τ`
    have hsqN : 1 / (N : ℝ) ≤ Real.sqrt (1 - uu) := by
      rw [div_le_iff₀ hN0]
      nlinarith [mul_le_mul_of_nonneg_left hLN (Real.sqrt_nonneg (1 - uu))]
    have hvN : 1 / (1 - uu) ≤ (N : ℝ) ^ 2 := by
      have hsq : Real.sqrt (1 - uu) * Real.sqrt (1 - uu) = 1 - uu :=
        Real.mul_self_sqrt (by linarith)
      have hm2 : 1 / (N : ℝ) * (1 / (N : ℝ)) ≤ 1 - uu := by
        rw [← hsq]
        exact mul_le_mul hsqN hsqN (by positivity) (Real.sqrt_nonneg _)
      rw [div_le_iff₀ hv0]
      calc (1 : ℝ) = (N : ℝ) ^ 2 * (1 / (N : ℝ) * (1 / (N : ℝ))) := by field_simp
        _ ≤ (N : ℝ) ^ 2 * (1 - uu) := mul_le_mul_of_nonneg_left hm2 (by positivity)
    have hm1 : ∀ σ, ‖mSigma E σ‖ ≤ 1 := fun σ => le_of_eq (norm_mSigma hE σ)
    have hgap : ∀ σ σ', 1 - uu ≤ ‖1 - (uu : ℂ) * (mSigma E σ * mSigma E σ')‖ := by
      intro σ σ'
      refine one_sub_le_norm_one_sub_mul hu0 ?_
      rw [norm_mul, norm_mSigma hE, norm_mSigma hE, mul_one]
    have hK := Decay.loopDecay_Kgen (B.L N) (B.three_le_L N) (B.W N) hm1 hu0 hu1 hv0 hgap m
      hrad0
    have hexpo : cZero / 2 * (N : ℝ) ^ (τ / 2)
        ≤ cor35Rate (1 - uu) * (B.ell N uu * (N : ℝ) ^ τ) := by
      rw [show B.ell N uu = ellHat (B.L N) (uu : ℂ) from rfl,
        cor35Rate_mul_ell_mul (B.L N) hu1 hcut]
      nlinarith
    have hterm2 := LKDecayQuant.term2_le (m := m) (D := D) (τ := τ) hN0 hv0 hv1 hvN hexpo hexpN
    have hrp : (0 : ℝ) ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
    exact hK.mono (B.L N) le_rfl le_rfl (by linarith)
  · -- the cut-off is active: `ℓ_v = L`, and the radius already exceeds the diameter `L/2`
    push Not at hcut
    have hellL : B.ell N uu = (B.L N : ℝ) := LKDecayQuant.ellHat_eq_L _ hu1 hcut
    have hhalf : (B.L N : ℝ) / 2 < B.ell N uu * (N : ℝ) ^ τ := by
      have hL0 : (0 : ℝ) < (B.L N : ℝ) := by
        exact_mod_cast (by have := B.three_le_L N; omega : 0 < B.L N)
      rw [hellL]; nlinarith
    exact LKDecayQuant.loopDecay_of_half_lt hhalf _

end KQuant

end RBM

namespace RBM

open Real

/-! ### §10  T234: the `HighProb` producers of the three good sets of §8

§8 lists `hin59`, `hinQ`, `hinG` — the good sets `RBM.FDInputs`, `RBM.QuadInputs`,
`RBM.EGInputs` — as having no producer at all.  Each of them is a conjunction of two kinds of
clause, and T205's analysis of the split is confirmed here:

* the **`RBM.Decay.LoopDecay` clauses** are Lemma 5.9 for `L` and for `L - K`, which is T126's
  `RBM.LKDecayQuant.highProb_loopDecay_pair`.  It is stated in the `RBM.Sample.Lval` vocabulary;
  `RBM.highProb_loopDecay_lkPath` reads it in the `RBM.lkPath`/`RBM.gloop` vocabulary the good
  sets use (the two are definitionally equal — `lkPath = gloop - Kval` and
  `Lval = gloop` — so nothing is reshaped).  Its one hypothesis,
  `RBM.LKDecayQuant.FlowInputs`, is the Lemma 4.1 event together with (2.76), and it has its own
  producer `RBM.LKDecayQuant.flowInputs_of_inputs` out of Steps 1–2's deliverables; it is *not*
  a new axiom-shaped assumption.
* the **`Ξ^{(L-K)}_{u,m} ≤ Ψ` clauses** are (5.76)/(2.78), i.e. `Ξ^{(L-K)}_{u,m} ≺ 1`, which is
  Steps 3–5's output in the shape `StochDom P (RBM.Step3.flowXiLK X E s t m) 1`
  (`RBM.StepGlue.flow_hs1` at `m = 1`, `RBM.StepGlue.flow_xiLK_two_le` /
  `RBM.Gauss.xiLK_two_stochDom_of_cutHyp` at `m = 2`, Step 4's iteration above).  The passage to
  a good set is mechanical: `RBM.highProb_flowXiLK_le` is literally the complement of the
  `RBM.badSet` of that domination at the exponent `τ`.

**Non-vacuity discipline.**  Each producer concludes a `RBM.HighProb` (or, for `hin59`, the
`ENNReal.toReal` form that §8 asks for), never "the inequality holds at the points of some set":
the latter is satisfied by the empty set and would be the T164/T169/T220 defect.  No hypothesis
below is an `ω`-quantified pointwise inequality, and the time quantifier is `RBM.TimeIcc s t N`
throughout, as T205/T227 require.

**The third clause of `RBM.FDInputs`** is deterministic and is discharged outright:
`RBM.exists_norm_lkPath_le_rpow` bounds `|L - K|` at loop lengths `≤ 2` on the window by
`N^{2 + 3c}`.  Loop length `0` has to be treated separately — `RBM.lkPath_nil` computes it
exactly, `(L-K)_∅ = L W` (the trace of the identity, since `RBM.Kgen` vanishes at length `0`),
which is `≤ N` by `RBM.Band.dim` — because the `1 ≤ |J|` hypothesis of
`RBM.norm_gloop_flow_le_envFloor` genuinely excludes it.

**Radius bookkeeping.**  `hinQ`/`hinG` want the radius `ℓ_u N^τ` and get it verbatim;
`hin59` wants `ℓ_u W^τ`, which is *smaller*, hence a stronger demand.  It is met by running
Lemma 5.9 at `τ/4` and using (2.2): `W ≥ N^{1/2 + c}` gives `W^τ ≥ N^{(1/2+c)τ} ≥ N^{τ/4}`. -/

section GoodSets

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

theorem highProb_flowXiLK_le (X : Sample B) {E : ℝ} {s t : ℕ → ℝ} {m : ℕ}
    (h : StochDom B.P (Step3.flowXiLK X E s t m) fun _ _ _ => (1 : ℝ))
    {τ : ℝ} (hτ : 0 < τ) :
    HighProb B.P (fun N =>
      {ω | ∀ u : TimeIcc s t N, X.xiLK E N (u : ℝ) ω m ≤ (N : ℝ) ^ τ}) := by
  intro D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine le_trans (measure_mono ?_) hN
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, by simpa only [Step3.flowXiLK, mul_one] using hu⟩

theorem highProb_loopDecay_lkPath (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hFI : LKDecayQuant.FlowInputs X E s t) {m : ℕ} (hm : 1 ≤ m) {τ D : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) :
    HighProb B.P (fun N => {ω | ∀ u : TimeIcc s t N,
      Decay.LoopDecay (B.L N) m (B.ell N (u : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (lkPath X E N (u : ℝ) ω)
      ∧ Decay.LoopDecay (B.L N) m (B.ell N (u : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (gloop (B.L N) (B.W N) (X.H N (u : ℝ) ω) (zt E (u : ℝ)))}) :=
  (LKDecayQuant.highProb_loopDecay_pair hE hs0 ht1 hFI hm hτ hD).mono
    (Eventually.of_forall fun _ _ hω u => ⟨(hω u).2, (hω u).1⟩)

/-- **`RBM.QuadInputs` holds with high probability.** -/
theorem highProb_quadInputs (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hFI : LKDecayQuant.FlowInputs X E s t)
    (hxi2 : StochDom B.P (Step3.flowXiLK X E s t 2) fun _ _ _ => (1 : ℝ)) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)) := by
  intro τ hτ D hD
  refine ((highProb_loopDecay_lkPath X hE hs0 ht1 hFI (m := 2) (by norm_num) hτ hD).inter
    (highProb_flowXiLK_le X hxi2 hτ)).mono (Eventually.of_forall fun N ω hω u => ?_)
  exact ⟨(hω.1 u).1, hω.2 u⟩

/-- **`RBM.EGInputs` holds with high probability.** -/
theorem highProb_egInputs (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hFI : LKDecayQuant.FlowInputs X E s t)
    (hxi1 : StochDom B.P (Step3.flowXiLK X E s t 1) fun _ _ _ => (1 : ℝ))
    (hxi3 : StochDom B.P (Step3.flowXiLK X E s t 3) fun _ _ _ => (1 : ℝ)) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)) := by
  intro τ hτ D hD
  refine (((highProb_loopDecay_lkPath X hE hs0 ht1 hFI (m := 3) (by norm_num) hτ hD).inter
    (highProb_flowXiLK_le X hxi1 hτ)).inter
    (highProb_flowXiLK_le X hxi3 hτ)).mono (Eventually.of_forall fun N ω hω u => ?_)
  exact ⟨(hω.1.1 u).1, hω.1.2 u, hω.2 u⟩


theorem loopIdx_eq_nil {α : Type*} {J : LoopIdx α} (hJ : J.WF) (h : J.length = 0) :
    J = ⟨[], []⟩ := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.length, LoopIdx.WF] at hJ h
  have ha : a = [] := List.eq_nil_of_length_eq_zero h
  have hs : σ = [] := List.eq_nil_of_length_eq_zero (by rw [hJ, h])
  subst ha; subst hs; rfl

theorem lkPath_nil (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω) :
    lkPath X E N v ω ⟨[], []⟩ = ((B.L N * B.W N : ℕ) : ℂ) := by
  change gloop (B.L N) (B.W N) (X.H N v ω) (zt E v) ⟨[], []⟩ - B.Kval E N v ⟨[], []⟩ = _
  rw [show B.Kval E N v (⟨[], []⟩ : LoopIdx (ZMod (B.L N))) = 0 from rfl]
  change Matrix.trace (gloopProd (B.L N) (B.W N) (X.H N v ω) (zt E v) ⟨[], []⟩) - 0 = _
  rw [gloopProd_nil, Matrix.trace_one, sub_zero]
  simp

theorem exists_norm_lkPath_le_rpow (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT E (t N)) :
    ∃ KM : ℝ, 0 ≤ KM ∧ ∀ᶠ N : ℕ in atTop, ∀ (v : TimeIcc s t N) (ω : Ω)
      (J : LoopIdx (ZMod (B.L N))), J.WF → J.length ≤ 2 →
        ‖lkPath X E N (v : ℝ) ω J‖ ≤ (N : ℝ) ^ KM := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  obtain ⟨C, hC0, hC⟩ := exists_norm_Kval_le_envFloor B hκ0 hκ1 hEκ hs0 ht1
  refine ⟨2 + 3 * c, by linarith, ?_⟩
  filter_upwards [hη, B.dim, eventually_ge_atTop 1,
    SumZeroDyn.eventually_const_mul_rpow_le (2 + C)
      (show 1 + 3 * c < 2 + 3 * c by linarith)] with N hηN hdimN hN1 hfinN
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set A : ℝ := (N : ℝ) ^ c with hAdef
  have hA1 : (1 : ℝ) ≤ A := Real.one_le_rpow hN1' hc0
  have hηt : 0 < etaT E (t N) := etaT_pos hE (ht1 N)
  have hRA : envFloor E t N ≤ A := by
    refine max_le hA1 ?_
    have hpos : (0 : ℝ) < (N : ℝ) ^ (-c) := Real.rpow_pos_of_pos hN0 _
    have := inv_anti₀ hpos hηN
    rwa [Real.rpow_neg hN0.le, inv_inv] at this
  have hR0 : 0 ≤ envFloor E t N := envFloor_nonneg E t N
  -- `R_N^3 ≤ N^{3c} ≤ N^{1 + 3c}`
  have hA3 : A ^ 3 = (N : ℝ) ^ (3 * c) := by
    rw [hAdef, ← Real.rpow_natCast ((N : ℝ) ^ c) 3, ← Real.rpow_mul hN0.le]
    norm_num; ring_nf
  have hcube : envFloor E t N ^ 3 ≤ (N : ℝ) ^ (1 + 3 * c) := by
    refine le_trans (pow_le_pow_left₀ hR0 hRA 3) ?_
    rw [hA3]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  -- `L W ≤ N ≤ N^{1 + 3c}`
  have hLW : ((B.L N * B.W N : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 + 3 * c) := by
    have h1 : ((B.L N * B.W N : ℕ) : ℝ) ≤ (N : ℝ) := by
      have h0 : B.W N * B.L N ≤ N := hdimN.1
      have h1 : B.L N * B.W N ≤ N := by rw [Nat.mul_comm]; exact h0
      exact_mod_cast h1
    refine h1.trans ?_
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (1 + 3 * c) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  intro v ω J hJ h2
  have hbound : ‖lkPath X E N (v : ℝ) ω J‖ ≤ (2 + C) * (N : ℝ) ^ (1 + 3 * c) := by
    rcases Nat.eq_zero_or_pos J.length with h0 | h1
    · rw [loopIdx_eq_nil hJ h0, lkPath_nil]
      rw [Complex.norm_natCast]
      nlinarith [Real.rpow_nonneg hN0.le (1 + 3 * c)]
    · have hg := norm_gloop_flow_le_envFloor X hE ht1 N v ω J hJ h1 (by omega)
      have hk := hC N v J hJ h1 (by omega)
      have hsum : ‖lkPath X E N (v : ℝ) ω J‖ ≤ envFloor E t N ^ 3 + C * envFloor E t N ^ 3 :=
        le_trans (norm_sub_le _ _) (add_le_add hg hk)
      nlinarith [Real.rpow_nonneg hN0.le (1 + 3 * c)]
  exact hbound.trans hfinN

theorem exists_fdInputs_highProb (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT E (t N))
    (hFI : LKDecayQuant.FlowInputs X E s t) :
    ∃ KM : ℝ, 0 ≤ KM ∧ ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D) := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  obtain ⟨KM, hKM0, hM⟩ := exists_norm_lkPath_le_rpow X hκ0 hκ1 hEκ hs0 ht1 hc0 hη
  refine ⟨KM, hKM0, fun τ hτ D hD => ?_⟩
  have hdec := highProb_loopDecay_lkPath X hE hs0 ht1 hFI (m := 3) (by norm_num)
    (show (0 : ℝ) < τ / 4 by linarith) hD D hD
  filter_upwards [hdec, hM, B.bandwidth, eventually_ge_atTop 1] with N hdN hMN hbwN hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
  have hWt : (N : ℝ) ^ (τ / 4) ≤ (B.W N : ℝ) ^ τ := by
    have h1 : (N : ℝ) ^ ((1 / 2 + B.c) * τ) ≤ (B.W N : ℝ) ^ τ := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hbwN hτ.le
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hN1' ?_) h1
    have := B.c_pos
    nlinarith
  refine ENNReal.toReal_le_of_le_ofReal hnn (le_trans (measure_mono ?_) hdN)
  refine Set.compl_subset_compl.2 fun ω hω v => ?_
  have hell0 : (0 : ℝ) ≤ B.ell N (v : ℝ) :=
    le_trans zero_le_one (one_le_ellHat (B.L N) (B.three_le_L N)
      ((hs0 N).trans v.2.1) (v.2.2.trans_lt (ht1 N)))
  have hrad : B.ell N (v : ℝ) * (N : ℝ) ^ (τ / 4)
      ≤ B.ell N (v : ℝ) * (B.W N : ℝ) ^ τ := mul_le_mul_of_nonneg_left hWt hell0
  exact ⟨(hω v).1.mono (B.L N) (by norm_num) hrad le_rfl,
    (hω v).2.mono (B.L N) le_rfl hrad le_rfl,
    fun J hJ h2 => hMN v ω J hJ h2⟩

end GoodSets

end RBM

namespace RBM

open Real

/-! ### §11  T234: `hlk` — Lemma 5.9 for the *expectation* `E(L - K)` at the initial time

`hlk` of §8 is the fast decay (7.13) of the tensor `RBM.Step6.lkT X E N (s N) σ`, i.e. of
`E(L-K)_{s_N,σ,·}` — an expectation, not a pathwise quantity, so Lemma 5.9's high-probability
conclusion has to be integrated.  T173's `RBM.fastDecay_integral_of_highProb` is exactly that
step, and it charges `Env · P(Gᶜ)` for the complement; with the deterministic envelope
`N^{2+3c}` of §10 and the good set of §10 taken at the error exponent `D + KM + 1`, that charge
is `N^{-(D+1)}`, so the total is `2N^{-(D+1)} ≤ N^{-D} ≤ W^{-D}` (the last step because `W ≤ N`
and the exponent is negative — the paper's `W^{-D}` is the *weaker* of the two).

`RBM.integral_lkPath_eq_lkT` is the identification `∫ (L - K) = E L - K`, which needs only the
integrability of `L` (the `K` term is deterministic and `P` is a probability measure). -/

section LkExpect

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

theorem integral_lkPath_eq_lkT (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ)
    (σ : Fin 2 → Bool)
    (hint : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 1 ≤ J.length →
      Integrable (fun ω => X.Lval E N u ω J) B.P) :
    (fun b : LoopArg (B.L N) 2 => ∫ ω, lkPath X E N u ω (LoopData.idx (σ, b)) ∂B.P)
      = Step6.lkT X E N u σ := by
  have hP := B.isProbabilityMeasure
  funext b
  change ∫ ω, (X.Lval E N u ω (LoopData.idx (σ, b)) - B.Kval E N u (LoopData.idx (σ, b))) ∂B.P
      = X.ELval E N u (LoopData.idx (σ, b)) - B.Kval E N u (LoopData.idx (σ, b))
  rw [integral_sub (hint _ (LoopData.idx_wf _) (by simp)) (integrable_const _),
    integral_const, probReal_univ, one_smul]
  rfl

theorem fastDecay_lkT_of_flowInputs (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hFI : LKDecayQuant.FlowInputs X E s t)
    {KM : ℝ} (hKM0 : 0 ≤ KM)
    (hM : ∀ᶠ N : ℕ in atTop, ∀ (v : TimeIcc s t N) (ω : Ω) (J : LoopIdx (ZMod (B.L N))),
      J.WF → J.length ≤ 2 → ‖lkPath X E N (v : ℝ) ω J‖ ≤ (N : ℝ) ^ KM)
    (hmeas : ∀ (N : ℕ) (J : LoopIdx (ZMod (B.L N))),
      AEStronglyMeasurable (fun ω => lkPath X E N (s N) ω J) B.P)
    (hint : ∀ (N : ℕ) (J : LoopIdx (ZMod (B.L N))), J.WF → 1 ≤ J.length →
      Integrable (fun ω => X.Lval E N (s N) ω J) B.P) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X E N (s N) σ) := by
  intro τ hτ D hD
  have hP := B.isProbabilityMeasure
  have hdec := highProb_loopDecay_lkPath X hE hs0 ht1 hFI (m := 2) (by norm_num)
    (show (0 : ℝ) < τ / 4 by linarith) (show (0 : ℝ) < D + 1 by linarith)
  filter_upwards [hdec (D + KM + 1) (by linarith), hM, B.bandwidth, B.dim,
    eventually_ge_atTop 1,
    SumZeroDyn.eventually_const_mul_rpow_le 2 (show -(D + 1) < -D by linarith)] with
    N hpN hMN hbwN hdimN hN1 htwoN
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hWN : (B.W N : ℝ) ≤ (N : ℝ) := by
    have h1 : B.W N ≤ B.W N * B.L N :=
      Nat.le_mul_of_pos_right _ (by have := B.three_le_L N; omega)
    exact_mod_cast h1.trans hdimN.1
  have hWt : (N : ℝ) ^ (τ / 4) ≤ (B.W N : ℝ) ^ τ := by
    have h1 : (N : ℝ) ^ ((1 / 2 + B.c) * τ) ≤ (B.W N : ℝ) ^ τ := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hbwN hτ.le
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hN1' ?_) h1
    have := B.c_pos
    nlinarith
  have hWD : (N : ℝ) ^ (-D) ≤ (B.W N : ℝ) ^ (-D) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) D)
      (Real.rpow_le_rpow (by linarith) hWN hD.le)
  intro σ
  set G : Set Ω := {ω | ∀ u : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 2 (B.ell N (u : ℝ) * (N : ℝ) ^ (τ / 4)) ((N : ℝ) ^ (-(D + 1)))
        (lkPath X E N (u : ℝ) ω)
      ∧ Decay.LoopDecay (B.L N) 2 (B.ell N (u : ℝ) * (N : ℝ) ^ (τ / 4)) ((N : ℝ) ^ (-(D + 1)))
        (gloop (B.L N) (B.W N) (X.H N (u : ℝ) ω) (zt E (u : ℝ)))} with hGdef
  have hgood : ∀ ω ∈ G, FastDecay (B.L N) (B.ell N (s N) * (N : ℝ) ^ (τ / 4))
      ((N : ℝ) ^ (-(D + 1)))
      (fun b : LoopArg (B.L N) 2 => lkPath X E N (s N) ω (LoopData.idx (σ, b))) := by
    intro ω hω
    exact ((hω ⟨s N, le_rfl, hst N⟩).1).fastDecay (B.L N) (List.ofFn σ) (by simp)
  have hFD := fastDecay_integral_of_highProb (P := B.P) (L := B.L N) (n := 2)
    (δ := (N : ℝ) ^ (-(D + 1))) (Env := (N : ℝ) ^ KM)
    (A := fun ω (b : LoopArg (B.L N) 2) => lkPath X E N (s N) ω (LoopData.idx (σ, b)))
    (G := G) (Real.rpow_nonneg hN0.le _)
    (fun b => hmeas N (LoopData.idx (σ, b))) hgood
    (fun ω b => hMN ⟨s N, le_rfl, hst N⟩ ω (LoopData.idx (σ, b)) (LoopData.idx_wf _) (by simp))
  rw [integral_lkPath_eq_lkT X E N (s N) σ (hint N)] at hFD
  refine SumZeroDyn.FastDecay.mono (B.L N) hFD ?_ ?_
  · have hell0 : (0 : ℝ) ≤ B.ell N (s N) :=
      le_trans zero_le_one (one_le_ellHat (B.L N) (B.three_le_L N) (hs0 N)
        ((hst N).trans_lt (ht1 N)))
    exact mul_le_mul_of_nonneg_left hWt hell0
  · have hq : (B.P Gᶜ).toReal ≤ (N : ℝ) ^ (-(D + KM + 1)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hN0.le _) hpN
    have hKM : (0 : ℝ) ≤ (N : ℝ) ^ KM := Real.rpow_nonneg hN0.le _
    have hmul : (N : ℝ) ^ KM * (B.P Gᶜ).toReal ≤ (N : ℝ) ^ (-(D + 1)) := by
      refine le_trans (mul_le_mul_of_nonneg_left hq hKM) (le_of_eq ?_)
      rw [← Real.rpow_add hN0]; congr 1; ring
    linarith [hWD]
end LkExpect

end RBM

namespace RBM

/-! ### §11b  T234: `RBM.DriftBound.DriftInputs`, the three decay clauses

T220 handed over "the `RBM.Decay.LoopDecay` of `K` at loop length `n + 2`", observing that the
only producer in the tree, `RBM.exists_loopDecay_Kval`, is at length `3`.  §9 supplies it at
every length, so all three decay clauses of `RBM.DriftBound.DriftInputs` — the decay of `K`, of
`L - K` at length `n + 2`, and of `L` at length `n + 3` — are available together.

What is **not** produced here are the three counting clauses `Ξ^{rhs}_{u,n+2} ≤ Ψ`,
`Ξ^{sum}_{u,n+2} ≤ Ψ` and `Ξ^{(L-K)}_{u,1} ≤ C₁` at the budget
`Ψ = N^τ (2n+3) Φ_N` that `RBM.DriftBound.stochDom_norm_driftF` uses: those are sums of
`Ξ^{(L-K)}_{u,k}` and `Ξ^{(L)}_{u,n+3}` against a budget carrying the free polynomial `Φ`, and
turning Steps 3–5's `Ξ ≺ 1` into them is bookkeeping this ticket did not do. -/

section DriftDecay

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The three `RBM.Decay.LoopDecay` clauses of `RBM.DriftBound.DriftInputs`, with high
probability, at every `n`.**  The `K` clause is §9 (deterministic, so it enters through
`RBM.HighProb.of_eventually_univ`); the other two are T126's pair at loop length `n + 3`. -/
theorem highProb_driftInputs_decay (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hFI : LKDecayQuant.FlowInputs X E s t) (n : ℕ) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N => {ω | ∀ u : TimeIcc s t N,
        Decay.LoopDecay (B.L N) (n + 2) (B.ell N (u : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
          (B.Kval E N (u : ℝ))
      ∧ Decay.LoopDecay (B.L N) (n + 2) (B.ell N (u : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
          (gloop (B.L N) (B.W N) (X.H N (u : ℝ) ω) (zt E (u : ℝ)) - B.Kval E N (u : ℝ))
      ∧ Decay.LoopDecay (B.L N) (n + 3) (B.ell N (u : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
          (gloop (B.L N) (B.W N) (X.H N (u : ℝ) ω) (zt E (u : ℝ)))}) := by
  intro τ hτ D hD
  refine ((highProb_loopDecay_lkPath X hE hs0 ht1 hFI (m := n + 3) (by omega) hτ hD).inter
    (HighProb.of_eventually_univ (P := B.P)
      (Ξ := fun N => {ω : Ω | ∀ u : TimeIcc s t N,
        Decay.LoopDecay (B.L N) (n + 2) (B.ell N (u : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
          (B.Kval E N (u : ℝ))}) ?_)).mono (Eventually.of_forall fun N ω hω u => ?_)
  · filter_upwards [loopDecay_Kval_quant B hE.le hs0 ht1 (n + 2) τ hτ D hD] with N hN ω
    exact hN
  · exact ⟨hω.2 u, (hω.1 u).1.mono (B.L N) (by omega) le_rfl le_rfl, (hω.1 u).2⟩

/-- **A `RBM.HighProb` event is eventually non-empty.**

The anti-vacuity statement for §10/§11b: the producers there conclude a `RBM.HighProb`, never
"the inequality holds at the points of some set", and this turns that into non-emptiness, so
none of the good sets can be the empty set (the T164/T169/T220 defect).

⚠ T247 carried out T234's recommendation: the proof now lives once, in `RBM.HighProb.nonempty`
(`RBM1D/Defs/StochDom.lean`), and both this and `RBM.FastDecayFlow.nonempty_of_highProb` — which
had it verbatim, on the wrong side of the `Gauss/` import order — are one-line re-exports.  The
signature is unchanged (it is consumed twice in §11b below). -/
theorem highProb_nonempty {P : Measure Ω} [IsProbabilityMeasure P] {Ξ : ℕ → Set Ω}
    (h : HighProb P Ξ) : ∀ᶠ N : ℕ in atTop, (Ξ N).Nonempty :=
  h.nonempty measure_univ

/-- T247 probe: the re-export is the shared lemma, not a second proof. -/
example {P : Measure Ω} [IsProbabilityMeasure P] {Ξ : ℕ → Set Ω} (h : HighProb P Ξ) :
    highProb_nonempty h = h.nonempty measure_univ := rfl

end DriftDecay

end RBM

namespace RBM.Gauss

open RBM

/-! ### §12  T234: the Gaussian producers, and §8 with five more slots discharged

`RBM.Gauss.bounds_step_gauss_window'` is §8's step theorem with `hKd` (§9), `hin59`, `hinQ`,
`hinG` (§10) and `hlk` (§11) plugged in.  What replaces them is **not** new mathematics:

* `RBM.LKDecayQuant.FlowInputs` — the Lemma 4.1 event (4.4) plus the large deviations (4.2)
  plus (2.76), with its own producer `RBM.LKDecayQuant.flowInputs_of_inputs` out of Steps 1–2;
* `StochDom P (RBM.Step3.flowXiLK X E s t m) 1` for `m = 1, 2, 3` — (5.76)/(2.78), Steps 3–5's
  own deliverable (`RBM.StepGlue.flow_hs1`, `RBM.StepGlue.flow_xiLK_two_le`, Step 4's
  iteration).

**What is still open**, and nothing else: `hcont`, `hintU1`, `hintU2` (continuity in the time of
`E L - K`, and interval integrability of `U` against the two drift tensors — T205's item 4,
pure analysis), `hlmk` (2.68 on the window, Steps 1–5), and the induction data `hc`, `hη`,
`hBC`, `hB`.  **`RBM.Bounds` therefore still has no inhabitant at `s > 0`**: this file reduces
the residual list from ten items to seven, it does not close it. -/

section GaussProducers

/-- **`hlk` of §8 for the Gaussian model.**  §11 with the two analytic slots filled by
`RBM.Gauss.continuous_lkPath_gauss` (measurability) and `RBM.Gauss.integrable_sample_Lval`
(integrability of `L` at the initial time), and the envelope by §10. -/
theorem hlk_gauss (d : Dims) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT E (t N))
    (hFI : LKDecayQuant.FlowInputs (sample d) E s t) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay ((band d).L N) ((band d).ell N (s N) * ((band d).W N : ℝ) ^ τ)
        (((band d).W N : ℝ) ^ (-D)) (Step6.lkT (sample d) E N (s N) σ) := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  obtain ⟨KM, hKM0, hM⟩ := exists_norm_lkPath_le_rpow (sample d) hκ0 hκ1 hEκ hs0 ht1 hc0 hη
  refine fastDecay_lkT_of_flowInputs (sample d) hE hs0 hst ht1 hFI hKM0 hM ?_ ?_
  · intro N J
    exact (continuous_lkPath_gauss d N hE ((hst N).trans_lt (ht1 N)) J).aestronglyMeasurable
  · intro N J hJ hn
    exact integrable_sample_Lval (etaT_pos_of_lt_one hE ((hst N).trans_lt (ht1 N)))
      (abs_im_zt E hE ((hst N).trans_lt (ht1 N))).ge J hJ hn

/-- **The (2.71) half of the induction step for the Gaussian model, with `hKd`, `hlk`, `hin59`,
`hinQ` and `hinG` discharged.**

Compare `RBM.Gauss.bounds_step_gauss_window`: five of its residual hypotheses are gone, and the
four that replace them (`hFI`, `hxi1`, `hxi2`, `hxi3`) are Steps 1–5's own outputs.  The
hypothesis list of this theorem **is** the remaining gap, as the elaborator sees it. -/
theorem bounds_step_gauss_window' (d : Dims) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 (band d) E s t)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT E u)
    (hcont : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT (sample d) E N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintU1 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK (sample d) E N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG (sample d) E N v σ) a) volume (s N) (u : ℝ))
    (hFI : LKDecayQuant.FlowInputs (sample d) E s t)
    (hxi1 : StochDom (band d).P (Step3.flowXiLK (sample d) E s t 1) fun _ _ _ => (1 : ℝ))
    (hxi2 : StochDom (band d).P (Step3.flowXiLK (sample d) E s t 2) fun _ _ _ => (1 : ℝ))
    (hxi3 : StochDom (band d).P (Step3.flowXiLK (sample d) E s t 3) fun _ _ _ => (1 : ℝ))
    (hlmk : SharpLmKFlow (sample d) E s t)
    (hBC : BoundsCore (sample d) E t) (hB : Bounds (sample d) E s) :
    Bounds (sample d) E t := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  have hηt : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT E (t N) := by
    filter_upwards [hη] with N hN
    exact hN ⟨t N, hst N, le_rfl⟩
  obtain ⟨KM, hKM0, hin59⟩ :=
    exists_fdInputs_highProb (sample d) hκ0 hκ1 hEκ hs0 ht1 hc0 hηt hFI
  exact bounds_step_gauss_window d hκ0 hκ1 hEκ hs0 hst ht1 hc hc0 hη hcont hintU1 hintU2
    hKM0 (hlk_gauss d hκ0 hκ1 hEκ hs0 hst ht1 hc0 hηt hFI) hin59
    (highProb_quadInputs (sample d) hE hs0 ht1 hFI hxi2)
    (highProb_egInputs (sample d) hE hs0 ht1 hFI hxi1 hxi3)
    (loopDecay_Kval_quant (band d) hE.le hs0 ht1 3) hlmk hBC hB

end GaussProducers

/-! ### §13  T234: the new producers are non-degenerate

Two directions, both on the **non-degenerate** grid window `[1 - 1/(N+2), 1 - 1/(N+3)]` of §4
(`s_N > 0`, `1 - t_N ≍ N^{-1}`, the hardest end of Theorem 2.21's range), at `E = 0` — the very
energy at which `RBM.Gauss.not_exists_env_eG` refutes the `ℝ`-quantified envelope:

* `RBM.Gauss.nonempty_goodSets_grid` — the two good sets produced in §10 are **eventually
  non-empty**, proved (not assumed) from their `RBM.HighProb`;
* `RBM.Gauss.loopDecay_Kval_grid` — `hKd` on that window is a *theorem with no hypotheses at
  all* beyond the window itself, which is the content of §9: at `1 - u ≍ N^{-1}` the decay
  length is `ℓ̂_u ≍ N^{1/2}` and the exponent is `c₀N^τ/4`, not `c₀N^{-1+1/2+τ}`. -/

section Witness

/-- **`hKd` on the grid window is unconditional.**  `s_N = 1 - 1/(N+2) > 0` and
`1 - t_N = 1/(N+3)`, so `ℓ̂_u ≍ N^{1/2}` and the cut-off in `ℓ̂` is inactive; there is no side
condition, no good event and no scale hypothesis. -/
theorem loopDecay_Kval_grid (d : Dims) (m : ℕ) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc envWinS envWinT N,
      Decay.LoopDecay ((band d).L N) m ((band d).ell N (v : ℝ) * (N : ℝ) ^ τ)
        ((N : ℝ) ^ (-D)) ((band d).Kval 0 N (v : ℝ)) :=
  loopDecay_Kval_quant (band d) (by norm_num) (fun N => (envWinS_pos N).le) envWinT_lt_one m

/-- **The good sets of §10 are eventually non-empty**, on the grid window at `E = 0`.  The
non-emptiness is *derived* from the `RBM.HighProb`, not assumed: this is the check that T220's
`Ξ = ∅` defect (and T164/T169's before it) is not being repeated. -/
theorem nonempty_goodSets_grid (d : Dims)
    (hFI : LKDecayQuant.FlowInputs (sample d) 0 envWinS envWinT)
    (hxi1 : StochDom (band d).P (Step3.flowXiLK (sample d) 0 envWinS envWinT 1)
      fun _ _ _ => (1 : ℝ))
    (hxi2 : StochDom (band d).P (Step3.flowXiLK (sample d) 0 envWinS envWinT 2)
      fun _ _ _ => (1 : ℝ))
    (hxi3 : StochDom (band d).P (Step3.flowXiLK (sample d) 0 envWinS envWinT 3)
      fun _ _ _ => (1 : ℝ))
    {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, (QuadInputs (sample d) 0 envWinS envWinT N ((N : ℝ) ^ τ)
        ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)).Nonempty) ∧
      ∀ᶠ N : ℕ in atTop, (EGInputs (sample d) 0 envWinS envWinT N ((N : ℝ) ^ τ)
        ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)).Nonempty := by
  have hP := (band d).isProbabilityMeasure
  have hE : |(0 : ℝ)| < 2 := by norm_num
  have hs0 : ∀ N, (0 : ℝ) ≤ envWinS N := fun N => (envWinS_pos N).le
  exact ⟨highProb_nonempty
      (highProb_quadInputs (sample d) hE hs0 envWinT_lt_one hFI hxi2 τ hτ D hD),
    highProb_nonempty
      (highProb_egInputs (sample d) hE hs0 envWinT_lt_one hFI hxi1 hxi3 τ hτ D hD)⟩

end Witness

end RBM.Gauss

namespace RBM

/-! ### §14  T234: the three `Ξ^{(L-K)} ≺ 1` slots of §10 are Steps 3–4's own output

§10/§12 take `StochDom P (RBM.Step3.flowXiLK X E s t m) 1` for `m = 1, 2, 3` as hypotheses.
This section records — as a compiled fact rather than a claim in a comment — that a producer
for **every** `m ≥ 1` is already in the tree: `RBM.Step45.xiLK_le_one_of_hyp`, Step 4's
iteration, out of Step 3's `RBM.Step3.Hyp`/`RBM.Step3.S`, Lemma 5.14 at `n = 2`, and the two
base cases `Ξ^{(L-K)}_{u,1} ≺ 1` (`RBM.StepGlue.flow_hs1`, from (4.5)) and
`Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}` (`RBM.StepGlue.flow_hs2`, from (2.76) and (2.72)).

So the four hypotheses that replace §8's five discharged slots really are Steps 1–5's
deliverables, and none of them is new mathematics. -/

section Steps34

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`Ξ^{(L-K)}_{u,n} ≺ 1` at every `n ≥ 1` from Step 3's data** — `RBM.Step45.xiLK_le_one_of_hyp`
read at the flow's families, which is the shape §10 consumes. -/
theorem xiLK_le_one_of_steps34 (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (H : Step3.Hyp B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowAs B E s) (Step3.flowR B s t) (Step3.flowA B E s t))
    (h0 : ∀ m, 1 ≤ m → Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s)
      (Step3.flowR B s t) (Step3.flowA B E s t) m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s)
      (Step3.flowR B s t) (Step3.flowA B E s t) m l)
    (h514 : Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) 2)
    (h1 : StochDom B.P (Step3.flowXiLK X E s t 1) fun _ _ _ => (1 : ℝ))
    (h2 : StochDom B.P (Step3.flowXiLK X E s t 2)
      fun N u _ => Step3.flowA B E s t N u ^ ((1 : ℝ) / 4)) :
    ∀ n, 1 ≤ n → StochDom B.P (Step3.flowXiLK X E s t n) fun _ _ _ => (1 : ℝ) :=
  Step45.xiLK_le_one_of_hyp H h0 h12 h514 h1 h2

end Steps34

end RBM

namespace RBM.Gauss

open RBM

/-! ### §15  T234: §12 with the three `Ξ ≺ 1` slots replaced by Step 3–4's data -/

section StepsAssembly

/-- **`RBM.Gauss.bounds_step_gauss_window'` with `hxi1`/`hxi2`/`hxi3` traced back to Steps 3–4.**

Every hypothesis here is either Steps 1–5's own deliverable (`hFI`, `H`, `h0`, `h12`, `h514`,
`h1`, `h2`, `hlmk`), the induction data (`hc`, `hη`, `hBC`, `hB`), or one of the three analytic
slots T234 did not do (`hcont`, `hintU1`, `hintU2`).  In particular **no hypothesis of this
theorem is about Lemma 5.9, about `K`'s decay, or about the four good sets** — that was T234's
target, and this is the check that it was met. -/
theorem bounds_step_gauss_window'' (d : Dims) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 (band d) E s t)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT E u)
    (hcont : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT (sample d) E N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintU1 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK (sample d) E N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG (sample d) E N v σ) a) volume (s N) (u : ℝ))
    (hFI : LKDecayQuant.FlowInputs (sample d) E s t)
    (H : Step3.Hyp (band d).P (Step3.flowXiLK (sample d) E s t)
      (Step3.flowXiL (sample d) E s t) (Step3.flowAs (band d) E s) (Step3.flowR (band d) s t)
      (Step3.flowA (band d) E s t))
    (h0 : ∀ m, 1 ≤ m → Step3.S (band d).P (Step3.flowXiLK (sample d) E s t)
      (Step3.flowAs (band d) E s) (Step3.flowR (band d) s t) (Step3.flowA (band d) E s t) m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → Step3.S (band d).P (Step3.flowXiLK (sample d) E s t)
      (Step3.flowAs (band d) E s) (Step3.flowR (band d) s t) (Step3.flowA (band d) E s t) m l)
    (h514 : Step3.Lemma514 (band d).P (Step3.flowXiLK (sample d) E s t)
      (Step3.flowXiL (sample d) E s t) (Step3.flowA (band d) E s t) 2)
    (h1 : StochDom (band d).P (Step3.flowXiLK (sample d) E s t 1) fun _ _ _ => (1 : ℝ))
    (h2 : StochDom (band d).P (Step3.flowXiLK (sample d) E s t 2)
      fun N u _ => Step3.flowA (band d) E s t N u ^ ((1 : ℝ) / 4))
    (hlmk : SharpLmKFlow (sample d) E s t)
    (hBC : BoundsCore (sample d) E t) (hB : Bounds (sample d) E s) :
    Bounds (sample d) E t := by
  have hxi := xiLK_le_one_of_steps34 (sample d) H h0 h12 h514 h1 h2
  exact bounds_step_gauss_window' d hκ0 hκ1 hEκ hs0 hst ht1 hc hc0 hη hcont hintU1 hintU2 hFI
    (hxi 1 le_rfl) (hxi 2 (by norm_num)) (hxi 3 (by norm_num)) hlmk hBC hB
end StepsAssembly

end RBM.Gauss

namespace RBM.Gauss

open RBM

/-! ### §16  T234: `RBM.FDInputs` too is eventually non-empty

`RBM.exists_fdInputs_highProb` delivers §8's `ENNReal.toReal` shape rather than a
`RBM.HighProb`, so `RBM.highProb_nonempty` does not apply to it directly.  The same argument
does: if the good set were empty its complement would be everything, of measure `1`, while the
bound puts it below `N^{-D} < 1`.  With §13 this covers **all three** good sets of §10. -/

section FdWitness

theorem nonempty_fdInputs_grid (d : Dims)
    (hFI : LKDecayQuant.FlowInputs (sample d) 0 envWinS envWinT) {τ D : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) :
    ∃ KM : ℝ, 0 ≤ KM ∧ ∀ᶠ N : ℕ in atTop,
      (FDInputs (sample d) 0 envWinS envWinT N (((band d).W N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        ((N : ℝ) ^ KM)).Nonempty := by
  have hP := (band d).isProbabilityMeasure
  obtain ⟨KM, hKM0, hin⟩ := exists_fdInputs_highProb (sample d) (κ := 1) one_pos le_rfl
    (by norm_num) (fun N => (envWinS_pos N).le) envWinT_lt_one (c := 2) (by norm_num)
    eventually_rpow_le_etaT_envWinT hFI
  refine ⟨KM, hKM0, ?_⟩
  filter_upwards [hin τ hτ D hD, eventually_ge_atTop 2] with N hN hN2
  rw [Set.nonempty_iff_ne_empty]
  intro hemp
  rw [hemp, Set.compl_empty, measure_univ, ENNReal.toReal_one] at hN
  have hN2' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  exact absurd hN (not_le.2 (Real.rpow_lt_one_of_one_lt_of_neg hN2' (by linarith)))


end FdWitness

end RBM.Gauss
