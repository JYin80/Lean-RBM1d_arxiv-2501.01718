/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.ChargeReduce
import RBM1D.Hierarchy.Step2Moment

/-!
# The constant charge `(+,+)`: Lemma 5.11 at `n = 2` and the bootstrap (T122)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 5.11 (p. 65) at `n = 2`,
(5.83), and the continuity argument that closes its self-quadratic term.

T115 found that `Ξ^{(L-K)}_{u,2}` of (5.76) is a maximum over **all four** charges while (2.76)
is stated only for `σ = (+,-)`; T120 shrank the gap to the single constant charge `(+,+)`
(`RBM.ChargeReduce.AprioriDecayPP`).  Jun's ruling (2026-09-21, route (c)): **(2.76) does not
change**; `(+,+)` satisfies (5.82) (`σ₁ = σ₂`) and is therefore supplied by **Lemma 5.11 at
`n = 2`**, whose evolution kernel contracts directly (case 1 of (7.16)) — no Ward identity, no
sum-zero property, no tail function.  Page 70 merely mis-cites this as (2.76).

**A correction carried out by this file** (in the header of `RBM1D/Hierarchy/StepGlue.lean`):
T115/T120 recorded as a corroborating point that the proof of Lemma 5.14 (p. 68) excludes
constant charges.  That was a misreading — the "non-constant" condition appears only inside the
*alternating* branch of (5.96).

## What is proved

* `stochDom_flowXiL`, `flow_xiL_apriori_le` — **(2.73)** in the form `Ξ^{(L)}_{u,m} ≺ R^{m-1}`,
  `R = ℓ_t/ℓ_s`.  `flow_xiLK_one_le` — **(2.75)** in the form `Ξ^{(L-K)}_{u,1} ≺ (W ℓ_s η_s)^{1/2}`.
* `xiLK_two_improve_of`, `xiLK_two_improve` — **(5.83) at `n = 2`**: `RBM.Step3.Lemma514` at
  `n = 2`, with its three free inputs discharged, so that only the conditional statement
  `Ξ^{(L-K)}_{u,2} ≺ θ  ⟹  Ξ^{(L-K)}_{u,2} ≺ R^{5/2} + (W ℓ_s η_s)^{1/2} + θ²(W ℓ_t η_t)^{-1}
  + R²` remains.  The self-quadratic term is what forces a bootstrap.
* `xiLK_two_init` — the starting point `Ξ^{(L-K)}_{s,2} ≺ 1`, from (2.68) = (5.110).
* `BootPP`, `xiLK_two_le` — **the bootstrap**.  See "where the bootstrap hangs" below.
* `flow_S_two_of`, `flow_S_le_two_of`, `flow_hs2_of` — the primed companions of
  `RBM.StepGlue.flow_S_two`, `flow_S_le_two`, `flow_hs2`, which take `Ξ^{(L-K)}_{u,2} ≺ Θ`
  instead of `RBM.StepGlue.AprioriDecayAll`.  `flow_hs2_of` is the **second pass** through
  (5.83), with `Ξ^{(L-K)}_{u,1} ≺ 1` (`RBM.StepGlue.flow_hs1`) in place of the local law; it
  needs **no second bootstrap**.
* `harith_flowAs` — the arithmetic of the second pass for the concrete target
  `Θ = (W ℓ_s η_s)^{1/2}`, from (2.72) with a gain (`hregS`).
* `flow_sharpLoop_glue_of`, `flow_steps45_glue_of` and their `…_flowAs` specializations —
  (2.77), (2.78), (2.79) in exactly the shapes of the fields `RBM.Steps.sharpLoop`,
  `sharpLmK`, `sharpDecay`, **with `AprioriDecayAll` removed**.

## Where the bootstrap hangs (the ticket's step 0)

Not at the `≺` level by re-instantiating `RBM.Step3.Lemma514` on prefix intervals `[s, v]`, and
not at the moment level either.  It hangs at the **event level, pathwise**, exactly as route A
of Step 2 (`RBM.Step2.jS_highProb`) does for the charge `(+,-)`:

* re-instantiating on prefixes fails because both the hypothesis and the conclusion of
  `Lemma514` are `≺`-statements, i.e. statements about the sequence `N → ∞`, whereas continuous
  induction needs, at each **fixed** `N`, an implication between values of one path;
* the moment route of `RBM.Step2Moment` is not needed, because `u ↦ Ξ^{(L-K)}_{u,2}(ω)` is a
  continuous function of `u` for **every** `ω` (a finite maximum of continuous functions).  So
  `RBM.le_of_bootstrap_prefix` can be run inside the high-probability event on which the
  one-step improvement holds, and the conclusion is transferred back to `≺` by a union bound.

Accordingly the hypothesis `RBM.Step2PP.BootPP.step` is the **event** form of Lemma 5.11 at
`n = 2` — the analogue of `RBM.Step2.Hyp.mart`, which asserts (5.44)–(5.46) *stopped at* the
time (5.43).  `xiLK_two_improve` is its `≺`-level shadow and is proved here, so that what is
being assumed is visible.

## Deviations from the paper

* The bootstrap threshold is `N^{2δ} Θ` with the time-independent `Θ = (W ℓ_s η_s)^{1/2}`,
  not the ticket's `(W ℓ_u η_u)^{3/4}`.  Reason: the control parameter `Φ` of
  `RBM.Step3.Lemma514` is time-independent, and the `1`-loop input `Ξ^{(L-K)}_{u,1} ≺
  (W ℓ_u η_u)^{1/2} ≤ (W ℓ_s η_s)^{1/2}` puts `(W ℓ_s η_s)^{1/2}` into the output anyway.
* **`RBM.ChargeReduce.AprioriDecayPP` is *not* discharged, and cannot be by this route.**  It
  asks for `Ξ^{(L-K)}_{u,2} ≺ (η_s/η_u)^4`, while (5.83) at `n = 2` outputs at least
  `(W ℓ_s η_s)^{1/2} + R^{5/2}`, which is larger than `(η_s/η_u)^4 ≤ ((1-s)/(1-t))^4` for every
  `u` (by (2.72), `((1-s)/(1-t))^{30} ≤ W ℓ_t η_t ≤ W ℓ_s η_s`).  What the consumers of
  `AprioriDecayAll` actually need is weaker, and that is what the primed theorems above
  deliver: `S(2,l)` needs only `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_s η_s)^{1/2}` (since
  `Ψ(2,l) ≥ (W ℓ_s η_s)^{1/2}`), and Step 4's `hs2` is reached by the second pass.
* `RBM.StepGlue.AprioriDecayAll` and `RBM.ChargeReduce.AprioriDecayPP` are left untouched, and
  so are all existing signatures.
-/

namespace RBM

open MeasureTheory Filter

namespace Step2PP

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-! ### From a loopwise bound to `Ξ^{(L)}` -/

/-- **From a loopwise bound to `Ξ^{(L)}`.**  If `|L_{u,σ,a}| ≺ f_u` uniformly in `u ∈ [s,t]`
and in the loop `(σ,a)` of length `m`, then `Ξ^{(L)}_{u,m} ≺ f_u (W ℓ_u η_u)^{m-1}`.  This is
the `Ξ^{(L)}` companion of `RBM.StepGlue.stochDom_flowXiLK`. -/
theorem stochDom_flowXiL (X : Sample B) {m : ℕ} {f : ∀ N, TimeIcc s t N → ℝ}
    (hA : ∀ N (u : TimeIcc s t N), 0 ≤ B.scale E N u)
    (h : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => f N p.1)) :
    StochDom B.P (Step3.flowXiL X E s t m)
      (fun N u _ => f N u * B.scale E N u ^ (m - 1)) := by
  refine StochDom.of_subset_union h h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨u, hu⟩
  by_cases h' : ∃ p : TimeIcc s t N × LoopData (B.L N) m,
      (N : ℝ) ^ τ * f N p.1 < ‖X.Lval E N p.1 ω p.2.idx‖
  · exact Or.inl h'
  · exfalso
    have hall : ∀ v : LoopData (B.L N) m, ‖X.Lval E N u ω v.idx‖ ≤ (N : ℝ) ^ τ * f N u :=
      fun v => not_lt.1 fun hc => h' ⟨(u, v), hc⟩
    have hmax : loopMax (B.L N) (B.W N) (X.H N u ω) (zt E u) m ≤ (N : ℝ) ^ τ * f N u :=
      ciSup_le hall
    have hApow : (0 : ℝ) ≤ B.scale E N u ^ (m - 1) := pow_nonneg (hA N u) _
    have : Step3.flowXiL X E s t m N u ω ≤ (N : ℝ) ^ τ * (f N u * B.scale E N u ^ (m - 1)) := by
      show loopMax (B.L N) (B.W N) (X.H N u ω) (zt E u) m * B.scale E N u ^ (m - 1) ≤ _
      calc loopMax (B.L N) (B.W N) (X.H N u ω) (zt E u) m * B.scale E N u ^ (m - 1)
          ≤ ((N : ℝ) ^ τ * f N u) * B.scale E N u ^ (m - 1) :=
            mul_le_mul_of_nonneg_right hmax hApow
        _ = (N : ℝ) ^ τ * (f N u * B.scale E N u ^ (m - 1)) := by ring
    exact absurd hu (not_lt.2 this)

/-! ### The a priori inputs of (5.83) at `n = 2` -/

/-- **(2.73) in the form `Ξ^{(L)}_{u,m} ≺ (ℓ_t/ℓ_s)^{m-1}`**, for every `m ≥ 1`, uniformly in
`u ∈ [s,t]`.  This is `RBM.Steps.apriori` read through `RBM.Step2PP.stochDom_flowXiL`; note that
(2.73) is a bound on `max_{σ,a}`, so **all** charges are covered. -/
theorem flow_xiL_apriori_le' (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hapriori : AprioriFlow X E s t) {m : ℕ}
    (hm : 1 ≤ m) :
    StochDom B.P (Step3.flowXiL X E s t m)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowR B s t N ^ (m - 1)) := by
  have hL : ∀ N, 1 ≤ B.L N := fun N => by have := B.three_le_L N; omega
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hR0 : ∀ N, (0 : ℝ) ≤ Step3.flowR B s t N := fun N =>
    div_nonneg (Step3.ellHat_pos_of_lt_one (hL N) (ht1 N)).le
      (Step3.ellHat_pos_of_lt_one (hL N) ((hst N).trans_lt (ht1 N))).le
  have hXi := stochDom_flowXiL X (f := fun N (u : TimeIcc s t N) =>
    (B.ell N u / B.ell N (s N)) ^ (m - 1) * (B.scale E N u)⁻¹ ^ (m - 1))
    (fun N u => (hA N u).le) (hapriori m hm)
  refine Step3.stochDom_mono (fun N _ _ => pow_nonneg (hR0 N) _) 1
    (Eventually.of_forall fun N u _ => ?_) hXi
  have hA0 : 0 < B.scale E N u := hA N u
  have hℓs : 0 < B.ell N (s N) :=
    Step3.ellHat_pos_of_lt_one (hL N) ((hst N).trans_lt (ht1 N))
  have hℓu : B.ell N u ≤ B.ell N (t N) := Step3.ellHat_mono u.2.2 (ht1 N)
  have hr0 : (0 : ℝ) ≤ B.ell N u / B.ell N (s N) := by
    have := (Step3.ellHat_pos_of_lt_one (L := B.L N) (hL N) (u.2.2.trans_lt (ht1 N))).le
    positivity
  have hkey : (B.ell N u / B.ell N (s N)) ^ (m - 1) * (B.scale E N u)⁻¹ ^ (m - 1) *
      B.scale E N u ^ (m - 1) = (B.ell N u / B.ell N (s N)) ^ (m - 1) := by
    rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hA0.ne'), mul_one]
  rw [hkey, one_mul]
  exact pow_le_pow_left₀ hr0 (div_le_div_of_nonneg_right hℓu hℓs.le) _

/-- **(2.75) in the form `Ξ^{(L-K)}_{u,1} ≺ (W ℓ_s η_s)^{1/2}`**: the local law gives
`Ξ^{(L-K)}_{u,1} ≺ (W ℓ_u η_u)^{1/2}`, and `W ℓ_u η_u ≤ W ℓ_s η_s` by (2.72).  The bound is
taken at `s` because `RBM.Step3.Lemma514` demands a *time-independent* control parameter. -/
theorem flow_xiLK_one_le' (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hll : LocalLawFlow X E s t) :
    StochDom B.P (Step3.flowXiLK X E s t 1)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) := by
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have sc := Step3.scales_flow (E := E) (s := s) (t := t) hE hs0 hst ht1 hcond
  have hXi := StepGlue.stochDom_flowXiLK X (f := fun N (u : TimeIcc s t N) =>
    (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 2)) (fun N u => (hA N u).le)
    (StepGlue.flow_lkErr_one_le' X hll)
  refine Step3.stochDom_mono (fun N _ _ => Real.rpow_nonneg (sc.As_pos N).le _) 1 ?_ hXi
  filter_upwards [sc.A_le_As] with N hle u _
  have hA0 : 0 < B.scale E N u := hA N u
  have hsq : B.scale E N u ^ ((1 : ℝ) / 2) * B.scale E N u ^ ((1 : ℝ) / 2) = B.scale E N u := by
    rw [← Real.rpow_add hA0]; norm_num
  have hval : (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 2) * B.scale E N u ^ 1
      = B.scale E N u ^ ((1 : ℝ) / 2) := by
    rw [Real.inv_rpow hA0.le, pow_one, inv_mul_eq_iff_eq_mul₀ (Real.rpow_pos_of_pos hA0 _).ne']
    exact hsq.symm
  rw [hval, one_mul]
  exact Real.rpow_le_rpow hA0.le (hle u) (by norm_num)

/-! ### (5.83) at `n = 2`: the conditional improvement -/

/-- `A_t ≤ A_u` for `u ∈ [s,t]`: `W ℓ_u η_u` is non-increasing in `u`. -/
theorem scale_last_le (ht1 : ∀ N, t N < 1) (N : ℕ) (u : TimeIcc s t N) :
    B.scale E N (t N) ≤ B.scale E N u := by
  have hW0 : (0 : ℝ) ≤ B.W N := by positivity
  exact flowScale_antitoneOn hW0 (B.L N) E (Set.mem_Iic.2 (u.2.2.trans_lt (ht1 N)).le)
    (Set.mem_Iic.2 (ht1 N).le) u.2.2

/-- **Lemma 5.11 at `n = 2`, i.e. (5.83) with its self-quadratic term made explicit.**

`RBM.Step3.Lemma514` at `n = 2` reads
`Ξ^{(L-K)}_{u,2} ≺ Λ^{1/2} + Φ` as soon as `Ξ^{(L)}_{u,6} ≺ Λ`, `Ξ^{(L-K)}_{u,1} ≺ Φ`,
`Ξ^{(L-K)}_{u,2} Ξ^{(L-K)}_{u,2} (W ℓ_u η_u)^{-1} ≺ Φ` and `Ξ^{(L)}_{u,3} ≺ Φ`; the middle
hypothesis has **the estimated quantity on both sides**, which is why (5.83) at `n = 2` can only
be used conditionally on an a priori bound `θ`.  Here the three free inputs are discharged from
(2.73) and (2.75), leaving exactly the conditional statement

`Ξ^{(L-K)}_{u,2} ≺ θ  ⟹  Ξ^{(L-K)}_{u,2} ≺ R^{5/2} + (W ℓ_s η_s)^{1/2} + θ² (W ℓ_t η_t)^{-1}
  + R²`.

`(+,+)` is a **non-alternating** charge (`σ₁ = σ₂`, (5.82)), so it is covered by
`RBM.SumZeroDyn.bound_nonAlt` inside `RBM.SumZeroDyn.lemma514_flow`, which produces `h514` for
every `n ≥ 2`; no Ward identity, no sum-zero property and no tail function is needed for it.
(Contrary to a remark recorded in T115/T120, the proof of Lemma 5.14 does *not* exclude constant
charges: the "non-constant" condition of (5.96) occurs only inside its **alternating** branch.) -/
theorem xiLK_two_improve_of' (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hapriori : AprioriFlow X E s t)
    (h514 : Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) 2)
    {θ c₁ : ℕ → ℝ} (hθ0 : ∀ N, 0 ≤ θ N) (hc₁0 : ∀ N, 0 ≤ c₁ N)
    (hone : StochDom B.P (Step3.flowXiLK X E s t 1)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => c₁ N))
    (hθ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => θ N)) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) =>
        (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) +
          (c₁ N + θ N ^ 2 * (B.scale E N (t N))⁻¹ + Step3.flowR B s t N ^ 2)) := by
  have hL : ∀ N, 1 ≤ B.L N := fun N => by have := B.three_le_L N; omega
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hAt : ∀ N, 0 < B.scale E N (t N) := fun N =>
    B.scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)
  have hR0 : ∀ N, (0 : ℝ) ≤ Step3.flowR B s t N := fun N =>
    div_nonneg (Step3.ellHat_pos_of_lt_one (hL N) (ht1 N)).le
      (Step3.ellHat_pos_of_lt_one (hL N) ((hst N).trans_lt (ht1 N))).le
  have sc := Step3.scales_flow (E := E) (s := s) (t := t) hE hs0 hst ht1 hcond
  set Λ : ℕ → ℝ := fun N => Step3.flowR B s t N ^ 5 with hΛdef
  set Φ : ℕ → ℝ := fun N => c₁ N +
    θ N ^ 2 * (B.scale E N (t N))⁻¹ + Step3.flowR B s t N ^ 2 with hΦdef
  have hΛ0 : ∀ N, 0 ≤ Λ N := fun N => pow_nonneg (hR0 N) _
  have hΦ0 : ∀ N, 0 ≤ Φ N := fun N => by
    have h1 : (0 : ℝ) ≤ c₁ N := hc₁0 N
    have h2 : (0 : ℝ) ≤ θ N ^ 2 * (B.scale E N (t N))⁻¹ := by
      have := hθ0 N; have := (hAt N).le; positivity
    have h3 : (0 : ℝ) ≤ Step3.flowR B s t N ^ 2 := pow_nonneg (hR0 N) _
    simp only [hΦdef]; linarith
  have hAsΦ : ∀ N, c₁ N ≤ Φ N := fun N => by
    have h2 : (0 : ℝ) ≤ θ N ^ 2 * (B.scale E N (t N))⁻¹ := by
      have := hθ0 N; have := (hAt N).le; positivity
    have h3 : (0 : ℝ) ≤ Step3.flowR B s t N ^ 2 := pow_nonneg (hR0 N) _
    simp only [hΦdef]; linarith
  have hΛ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Λ N := by
    filter_upwards [sc.one_le_R] with N hN
    exact one_le_pow₀ hN
  -- `Ξ^{(L)}_{u,6} ≺ R^5`
  have hY : StochDom B.P (Step3.flowXiL X E s t (2 * 2 + 2))
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Λ N) := by
    simpa [hΛdef] using flow_xiL_apriori_le' X hE hs0 hst ht1 hapriori (m := 6) (by norm_num)
  -- `Ξ^{(L-K)}_{u,1} ≺ Φ`
  have hX1 : ∀ m, 1 ≤ m → m < 2 → StochDom B.P (Step3.flowXiLK X E s t m)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Φ N) := by
    intro m hm1 hm2
    obtain rfl : m = 1 := by omega
    refine Step3.stochDom_mono (fun N _ _ => hΦ0 N) 1
      (Eventually.of_forall fun N _ _ => by rw [one_mul]; exact hAsΦ N) hone
  -- the self-quadratic term `Ξ_2 Ξ_2 A_u^{-1} ≺ θ² A_t^{-1} ≤ Φ`
  have hX2 : ∀ m, 2 ≤ m → m ≤ 2 → StochDom B.P
      (fun N u ω => Step3.flowXiLK X E s t m N u ω *
        Step3.flowXiLK X E s t (2 - m + 2) N u ω * (Step3.flowA B E s t N u)⁻¹)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Φ N) := by
    intro m hm1 hm2
    obtain rfl : m = 2 := by omega
    simp only [show (2 : ℕ) - 2 + 2 = 2 from rfl]
    have hnn : ∀ N (u : TimeIcc s t N) (ω : Ω), 0 ≤ Step3.flowXiLK X E s t 2 N u ω :=
      fun N u ω => X.xiLK_nonneg (hA N u).le
    have hinv : ∀ N (u : TimeIcc s t N) (_ : Ω), 0 ≤ (Step3.flowA B E s t N u)⁻¹ :=
      fun N u _ => (inv_pos.2 (hA N u)).le
    have hsq := StochDom.mul hnn (fun N _ _ => hθ0 N) hθ hθ
    have hprod := StochDom.mul hinv (fun N _ _ => mul_nonneg (hθ0 N) (hθ0 N)) hsq
      (StochDom.refl hinv)
    have hprod' : StochDom B.P
        (fun N (u : TimeIcc s t N) ω => Step3.flowXiLK X E s t 2 N u ω *
          Step3.flowXiLK X E s t 2 N u ω * (Step3.flowA B E s t N u)⁻¹)
        (fun N (u : TimeIcc s t N) (_ : Ω) => θ N * θ N * (Step3.flowA B E s t N u)⁻¹) := hprod
    refine Step3.stochDom_mono (fun N _ _ => hΦ0 N) 1 (Eventually.of_forall fun N u _ => ?_)
      hprod'
    rw [one_mul]
    have hle : (Step3.flowA B E s t N u)⁻¹ ≤ (B.scale E N (t N))⁻¹ :=
      (inv_le_inv₀ (hA N u) (hAt N)).2 (scale_last_le ht1 N u)
    have h1 : θ N * θ N * (Step3.flowA B E s t N u)⁻¹ ≤ θ N ^ 2 * (B.scale E N (t N))⁻¹ := by
      have := mul_le_mul_of_nonneg_left hle (mul_nonneg (hθ0 N) (hθ0 N))
      nlinarith [hθ0 N]
    have h2 : (0 : ℝ) ≤ c₁ N := hc₁0 N
    have h3 : (0 : ℝ) ≤ Step3.flowR B s t N ^ 2 := pow_nonneg (hR0 N) _
    simp only [hΦdef]
    linarith
  -- `Ξ^{(L)}_{u,3} ≺ R² ≤ Φ`
  have hY1 : StochDom B.P (Step3.flowXiL X E s t (2 + 1))
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Φ N) := by
    have h3 : StochDom B.P (Step3.flowXiL X E s t (2 + 1))
        (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowR B s t N ^ 2) := by
      simpa using flow_xiL_apriori_le' X hE hs0 hst ht1 hapriori (m := 3) (by norm_num)
    refine Step3.stochDom_mono (fun N _ _ => hΦ0 N) 1
      (Eventually.of_forall fun N _ _ => ?_) h3
    have h2 : (0 : ℝ) ≤ c₁ N := hc₁0 N
    have h4 : (0 : ℝ) ≤ θ N ^ 2 * (B.scale E N (t N))⁻¹ := by
      have := hθ0 N; have := (hAt N).le; positivity
    rw [one_mul]
    simp only [hΦdef]
    linarith
  exact h514 Λ Φ hΛ0 hΦ0 hΛ1 hY hX1 hX2 hY1

/-- **(5.83) at `n = 2` with the `1`-loop input taken from the local law (2.75)**: the form of
`RBM.Step2PP.xiLK_two_improve_of` used for the bootstrap itself. -/
theorem xiLK_two_improve' (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (h514 : Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) 2)
    {θ : ℕ → ℝ} (hθ0 : ∀ N, 0 ≤ θ N)
    (hθ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => θ N)) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) =>
        (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) +
          (Step3.flowAs B E s N ^ ((1 : ℝ) / 2) +
            θ N ^ 2 * (B.scale E N (t N))⁻¹ + Step3.flowR B s t N ^ 2)) :=
  xiLK_two_improve_of' X hE hs0 hst ht1 hcond hapriori h514 hθ0
    (fun N => Real.rpow_nonneg
      ((Step3.scales_flow (E := E) (s := s) (t := t) hE hs0 hst ht1 hcond).As_pos N).le _)
    (flow_xiLK_one_le' X hE hs0 hst ht1 hcond hll) hθ

/-! ### The starting point of the bootstrap: `Ξ^{(L-K)}_{s,2} ≺ 1` -/

/-- **(2.68) = (5.110) in the form `Ξ^{(L-K)}_{s,2} ≺ 1`.**  This is `RBM.BoundsCore.LmK` at
`n = 2`, which is a bound on `max_{σ,a}` and therefore covers the constant charge `(+,+)` too;
it is the initial condition of the bootstrap. -/
theorem xiLK_two_init (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hLmK : StochDom B.P
      (fun N (w : LoopData (B.L N) 2) ω => X.lkErr E N (s N) ω w.idx)
      (fun N _ _ => (B.scale E N (s N))⁻¹ ^ 2)) :
    StochDom B.P (fun N (_ : Unit) ω => X.xiLK E N (s N) ω 2) (fun _ _ _ => (1 : ℝ)) := by
  have hAs : ∀ N, 0 < B.scale E N (s N) := fun N =>
    B.scale_pos' hE N (hs0 N) ((hst N).trans_lt (ht1 N))
  refine StochDom.of_subset_union hLmK hLmK fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨_u, hu⟩
  by_cases h' : ∃ w : LoopData (B.L N) 2,
      (N : ℝ) ^ τ * (B.scale E N (s N))⁻¹ ^ 2 < X.lkErr E N (s N) ω w.idx
  · exact Or.inl h'
  · exfalso
    have hall : ∀ w : LoopData (B.L N) 2,
        X.lkErr E N (s N) ω w.idx ≤ (N : ℝ) ^ τ * (B.scale E N (s N))⁻¹ ^ 2 :=
      fun w => not_lt.1 fun hc => h' ⟨w, hc⟩
    have hmax : X.lkMax E N (s N) ω 2 ≤ (N : ℝ) ^ τ * (B.scale E N (s N))⁻¹ ^ 2 :=
      ciSup_le hall
    have hle : X.xiLK E N (s N) ω 2 ≤ (N : ℝ) ^ τ * 1 := by
      show X.lkMax E N (s N) ω 2 * B.scale E N (s N) ^ 2 ≤ _
      calc X.lkMax E N (s N) ω 2 * B.scale E N (s N) ^ 2
          ≤ ((N : ℝ) ^ τ * (B.scale E N (s N))⁻¹ ^ 2) * B.scale E N (s N) ^ 2 :=
            mul_le_mul_of_nonneg_right hmax (by positivity)
        _ = (N : ℝ) ^ τ * 1 := by
            rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (hAs N).ne')]
    exact absurd hu (not_lt.2 hle)

/-! ### The bootstrap -/

/-- **The bootstrap input for the constant charge `(+,+)`: Lemma 5.11 at `n = 2` in the stopped
(event) form in which §5.3 uses it.**

`RBM.Step2PP.xiLK_two_improve` is the `≺`-level shadow of the field `step` below: it says that
`Ξ^{(L-K)}_{u,2} ≺ θ` improves itself to `Ξ^{(L-K)}_{u,2} ≺ R^{5/2} + (W ℓ_s η_s)^{1/2} +
θ² (W ℓ_t η_t)^{-1} + R²`.  A `≺`-implication cannot be bootstrapped in the time: `≺` is a
statement about the sequence `N → ∞`, while continuous induction needs, **at each fixed `N`**,
an implication between the values of one path.  That is why the input is recorded here in the
*event* form — exactly as `RBM.Step2.Hyp.mart` records (5.44)–(5.46) *stopped at* the time
(5.43) for the charge `(+,-)`.  With the event form, the bootstrap itself is the deterministic
`RBM.le_of_bootstrap_prefix`, run **pathwise** on the high-probability event; no stopping time,
no moments.

* `cont` — the paths `u ↦ Ξ^{(L-K)}_{u,2}` are continuous for **every** `ω`.  For the flow
  `H_u = √u X` this is deterministic, as in `RBM.Step2Moment.MomentHyp.cont`.
* `step` — for every margin `δ > 0`, with high probability: if `Ξ^{(L-K)}_{u,2} ≤ N^{2δ} Θ_N`
  for every `u ∈ [s, v]`, then `Ξ^{(L-K)}_{v,2} ≤ N^δ Θ_N`.  The gain `N^δ` against `N^{2δ}` is
  the margin that `≺` must beat; it plays the role of `δ` in `RBM.Step2.jS_highProb`.

`(+,+)` is non-alternating, so the underlying estimate is `RBM.SumZeroDyn.bound_nonAlt`
(Lemma 5.11, (5.84)) — no Ward identity, no sum-zero property, no tail function. -/
structure BootPP (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) where
  /-- The deterministic bound `Θ_N` that the bootstrap propagates. -/
  target : ℕ → ℝ
  target_pos : ∀ N, 0 < target N
  one_le_target : ∀ᶠ N : ℕ in atTop, 1 ≤ target N
  /-- The paths `u ↦ Ξ^{(L-K)}_{u,2}` are continuous on `[s, t]`, for every `ω`. -/
  cont : ∀ (N : ℕ) (ω : Ω), ContinuousOn (fun u => X.xiLK E N u ω 2) (Set.Icc (s N) (t N))
  /-- The range `0 < δ ≤ δ₀` of margins for which the improvement is asserted (as in
  `RBM.Step2.Hyp.δ₀`); the arithmetic of (5.83) closes only for small `δ`. -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  /-- **Lemma 5.11 at `n = 2`, stopped**: the one-step improvement, on a high-probability set. -/
  step : ∀ δ, 0 < δ → δ ≤ δ₀ → HighProb B.P fun N => {ω | ∀ v ∈ Set.Icc (s N) (t N),
    (∀ u ∈ Set.Icc (s N) v, X.xiLK E N u ω 2 ≤ (N : ℝ) ^ (2 * δ) * target N) →
      X.xiLK E N v ω 2 ≤ (N : ℝ) ^ δ * target N}

/-- **The bootstrap.**  Continuous induction on the path `u ↦ Ξ^{(L-K)}_{u,2}(ω)`, run inside
the high-probability event of `RBM.Step2PP.BootPP.step`, propagates the initial bound
`Ξ^{(L-K)}_{s,2} ≺ 1` of (2.68) to `Ξ^{(L-K)}_{u,2} ≺ Θ` on all of `[s, t]`.

Only `RBM.le_of_bootstrap_prefix` is used: for each `ω` in the good event the set of times at
which the improved bound holds is closed (continuity) and its complement is open
(self-improvement), so it is everything.  The paper's stopping time (5.43) is not needed. -/
theorem xiLK_two_le (X : Sample B) (Hy : BootPP X E s t) (hst : ∀ N, s N ≤ t N)
    (hinit : StochDom B.P (fun N (_ : Unit) ω => X.xiLK E N (s N) ω 2)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Hy.target N) := by
  intro τ hτ D hD
  set δ : ℝ := min (τ / 2) Hy.δ₀ with hδdef
  have hδ : (0 : ℝ) < δ := lt_min (half_pos hτ) Hy.δ₀_pos
  have hδτ : δ ≤ τ / 2 := min_le_left _ _
  filter_upwards [Hy.step δ hδ (min_le_right _ _) (D + 1) (by linarith),
    hinit δ hδ (D + 1) (by linarith), Hy.one_le_target, eventually_ge_atTop 2,
    eventually_two_mul_rpow_le D] with N hA hB htgt hN2 hdd
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1 : (1 : ℝ) < (N : ℝ) := by linarith
  have hT0 : 0 < Hy.target N := Hy.target_pos N
  have hhalf : (N : ℝ) ^ δ < (N : ℝ) ^ τ :=
    Real.rpow_lt_rpow_left_iff hN1 |>.2 (by linarith)
  -- the failure event sits inside the two bad events
  have hsub : badSet (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Hy.target N) τ N ⊆
    ({ω | ∀ v ∈ Set.Icc (s N) (t N),
      (∀ u ∈ Set.Icc (s N) v, X.xiLK E N u ω 2 ≤ (N : ℝ) ^ (2 * δ) * Hy.target N) →
        X.xiLK E N v ω 2 ≤ (N : ℝ) ^ δ * Hy.target N})ᶜ ∪
    badSet (fun N (_ : Unit) ω => X.xiLK E N (s N) ω 2) (fun _ _ _ => (1 : ℝ)) δ N := by
    rintro ω ⟨u, hu⟩
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    obtain ⟨hev0, hbad⟩ := hno
    have hev : ω ∈ {ω | ∀ v ∈ Set.Icc (s N) (t N),
        (∀ u ∈ Set.Icc (s N) v, X.xiLK E N u ω 2 ≤ (N : ℝ) ^ (2 * δ) * Hy.target N) →
          X.xiLK E N v ω 2 ≤ (N : ℝ) ^ δ * Hy.target N} := by
      by_contra hc
      exact hev0 hc
    have hs2 : X.xiLK E N (s N) ω 2 ≤ (N : ℝ) ^ δ * 1 := by
      by_contra hc
      exact hbad ⟨(), not_le.1 hc⟩
    have hkey : ∀ v ∈ Set.Icc (s N) (t N),
        X.xiLK E N v ω 2 ≤ (N : ℝ) ^ δ * Hy.target N := by
      refine le_of_bootstrap_prefix (C := (N : ℝ) ^ (2 * δ) * Hy.target N)
        (hst N) (Hy.cont N ω) ?_ ?_ ?_
      · exact mul_lt_mul_of_pos_right
          ((Real.rpow_lt_rpow_left_iff hN1).2 (by linarith)) hT0
      · calc X.xiLK E N (s N) ω 2 ≤ (N : ℝ) ^ δ * 1 := hs2
          _ ≤ (N : ℝ) ^ δ * Hy.target N := by
              have : (0 : ℝ) ≤ (N : ℝ) ^ δ := Real.rpow_nonneg (by linarith) _
              nlinarith
      · exact fun v hv hprefix => hev v hv hprefix
    have hle := hkey (u : ℝ) u.2
    have : (N : ℝ) ^ δ * Hy.target N ≤ (N : ℝ) ^ τ * Hy.target N :=
      mul_le_mul_of_nonneg_right hhalf.le hT0.le
    exact absurd hu (not_lt.2 (hle.trans this))
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  refine le_trans (add_le_add hA hB) ?_
  rw [← ENNReal.ofReal_add hp hp]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### The consumers: `S(2,l)`, `S(m,l)` for `m ≤ 2`, and Step 4's base case `hs2` -/

/-- **`S(2,l)` for every `l`** from `Ξ^{(L-K)}_{u,2} ≺ Θ` with `Θ ≤ (W ℓ_s η_s)^{1/2}`: the
primed companion of `RBM.StepGlue.flow_S_two`, which needs `AprioriDecayAll`.  Since
`Ψ(2,l) ≥ (W ℓ_s η_s)^{1/2}` always (`RBM.StepGlue.rpow_half_le_psi`), this is all `S(2,l)`
asks for. -/
theorem flow_S_two_of (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t) {Θ : ℕ → ℝ}
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N))
    (hΘle : ∀ᶠ N : ℕ in atTop, Θ N ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) (l : ℕ) :
    Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s) (Step3.flowR B s t)
      (Step3.flowA B E s t) 2 l := by
  have sc := Step3.scales_flow (E := E) (s := s) (t := t) hE hs0 hst ht1 hcond
  refine Step3.stochDom_mono (fun N u _ => Step3.psi_nonneg (sc.As_pos N).le (sc.R_nonneg N)
    (sc.A_pos N u).le) 1 ?_ hΘ
  filter_upwards [hΘle] with N hN u _
  rw [one_mul]
  exact hN.trans (StepGlue.rpow_half_le_psi (sc.As_pos N).le (sc.R_nonneg N)
    (sc.A_pos N u).le 2 l)

/-- **`h12`**: `S(m,l)` for every `l` and `m ≤ 2`, in exactly the shape of the hypothesis `h12`
of `RBM.Step3.flow_sharpLoop` and `RBM.Step45.flow_steps45` — the primed companion of
`RBM.StepGlue.flow_S_le_two`. -/
theorem flow_S_le_two_of' (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hll : LocalLawFlow X E s t) {Θ : ℕ → ℝ}
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N))
    (hΘle : ∀ᶠ N : ℕ in atTop, Θ N ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2))
    (m l : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2) :
    Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s) (Step3.flowR B s t)
      (Step3.flowA B E s t) m l := by
  interval_cases m
  · exact StepGlue.flow_S_one' X hE hs0 hst ht1 hcond hll l
  · exact flow_S_two_of X hE hs0 hst ht1 hcond hΘ hΘle l

/-- **Step 4's base case `hs2`, by a second pass through (5.83) at `n = 2`.**

Once the bootstrap has produced `Ξ^{(L-K)}_{u,2} ≺ Θ`, (5.83) is applied once more — this time
with the sharp `1`-loop bound `Ξ^{(L-K)}_{u,1} ≺ 1` of `RBM.StepGlue.flow_hs1` in place of the
local law — and **no second bootstrap is needed**: the self-quadratic term is already
`≺ Θ² (W ℓ_t η_t)^{-1}`, a fixed deterministic quantity.  The arithmetic hypothesis `harith` is
the statement that the resulting bound is below `(W ℓ_t η_t)^{1/4} ≤ (W ℓ_u η_u)^{1/4}`; it is
the analogue of `RBM.StepGlue.eventually_R4_le_rpow_quarter`, and with (2.72)-with-a-gain it
holds for `Θ = (W ℓ_t η_t)^{7/12}`, since then
`Θ² (W ℓ_t η_t)^{-1} = (W ℓ_t η_t)^{1/6}`, `R^{5/2} ≤ ((1-s)/(1-t))^{5/4} ≤ (W ℓ_t η_t)^{1/24}`
and `R² ≤ (W ℓ_t η_t)^{1/30}`. -/
theorem flow_hs2_of' (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t) (hapriori : AprioriFlow X E s t)
    (h514 : Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) 2)
    {Θ : ℕ → ℝ} (hΘ0 : ∀ N, 0 ≤ Θ N)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N))
    (hone : StochDom B.P (Step3.flowXiLK X E s t 1)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => (1 : ℝ)))
    (harith : ∀ᶠ N : ℕ in atTop,
      (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) +
        (1 + Θ N ^ 2 * (B.scale E N (t N))⁻¹ + Step3.flowR B s t N ^ 2) ≤
      B.scale E N (t N) ^ ((1 : ℝ) / 4)) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      fun N u _ => Step3.flowA B E s t N u ^ ((1 : ℝ) / 4) := by
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hAt : ∀ N, 0 < B.scale E N (t N) := fun N =>
    B.scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)
  have h2 := xiLK_two_improve_of' X hE hs0 hst ht1 hcond hapriori h514 hΘ0
    (fun _ => zero_le_one) hone hΘ
  refine Step3.stochDom_mono (fun N u _ => Real.rpow_nonneg (hA N u).le _) 1 ?_ h2
  filter_upwards [harith] with N hN u _
  rw [one_mul]
  exact hN.trans (Real.rpow_le_rpow (hAt N).le (scale_last_le ht1 N u) (by norm_num))

/-! ### The concrete target `Θ = (W ℓ_s η_s)^{1/2}` -/

/-- `ℓ_t/ℓ_s ≤ (1-s)/(1-t)`: `R ≤ ((1-s)/(1-t))^{1/2} ≤ (1-s)/(1-t)`. -/
theorem flowR_le_ratio (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (N : ℕ) :
    Step3.flowR B s t N ≤ (1 - s N) / (1 - t N) := by
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have hQ1 : (1 : ℝ) ≤ (1 - s N) / (1 - t N) := by
    rw [le_div_iff₀ h1t]; linarith [hst N]
  have hQ0 : (0 : ℝ) < (1 - s N) / (1 - t N) := by linarith
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL hs1
  have hsq : Real.sqrt ((1 - s N) / (1 - t N)) ≤ (1 - s N) / (1 - t N) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt ((1 - s N) / (1 - t N)) := Real.one_le_sqrt.2 hQ1
    nlinarith [Real.sq_sqrt hQ0.le]
  have h := Step3.ellHat_le_sqrt_mul (L := B.L N) (s := s N) (t := t N) (hst N) (ht1 N)
  show B.ell N (t N) / B.ell N (s N) ≤ (1 - s N) / (1 - t N)
  rw [div_le_iff₀ hℓs]
  exact h.trans (mul_le_mul_of_nonneg_right hsq hℓs.le)

theorem one_le_flowR (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (N : ℕ) :
    (1 : ℝ) ≤ Step3.flowR B s t N := by
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hℓs : 0 < B.ell N (s N) :=
    Step3.ellHat_pos_of_lt_one hL ((hst N).trans_lt (ht1 N))
  show 1 ≤ B.ell N (t N) / B.ell N (s N)
  rw [le_div_iff₀ hℓs, one_mul]
  exact Step3.ellHat_mono (hst N) (ht1 N)

/-- **The arithmetic side condition of `RBM.Step2PP.flow_hs2_of` for `Θ = (W ℓ_s η_s)^{1/2}`,
from (2.72) with a gain.**  With `Q = (1-s)/(1-t)`, each of the four summands is at most `Q^5`:
`R ≤ Q^{1/2} ≤ Q`, `1 ≤ Q`, and `W ℓ_s η_s ≤ Q · W ℓ_t η_t` (`RBM.Step3.flowScale_le_mul`).
Then `Q^{30} ≤ W ℓ_t η_t` gives `4 Q^5 ≤ 4 (W ℓ_t η_t)^{1/6}`, and the `N^c` of `hregS` supplies
the remaining factor `4 ≤ (W ℓ_t η_t)^{1/12}`. -/
theorem harith_flowAs (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) :
    ∀ᶠ N : ℕ in atTop,
      (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) +
        (1 + (Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) ^ 2 * (B.scale E N (t N))⁻¹ +
          Step3.flowR B s t N ^ 2) ≤ B.scale E N (t N) ^ ((1 : ℝ) / 4) := by
  filter_upwards [hregS, eventually_le_rpow 4 (show (0 : ℝ) < c / 12 by positivity),
    eventually_ge_atTop 1] with N hN h4 hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hW0 : (0 : ℝ) ≤ B.W N := by positivity
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  set Q : ℝ := (1 - s N) / (1 - t N) with hQdef
  have hQ1 : (1 : ℝ) ≤ Q := by rw [hQdef, le_div_iff₀ h1t]; linarith [hst N]
  have hQ0 : (0 : ℝ) < Q := by linarith
  rw [Step2.etaT_ratio hE (s N) (t N), ← hQdef] at hN
  have hAt0 : 0 < B.scale E N (t N) :=
    B.scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)
  have hNc1 : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0.le
  have hQ301 : (1 : ℝ) ≤ Q ^ 30 := one_le_pow₀ hQ1
  have hQ30 : Q ^ 30 ≤ B.scale E N (t N) := by nlinarith
  have hNcAt : (N : ℝ) ^ c ≤ B.scale E N (t N) := by nlinarith
  have hAt1 : (1 : ℝ) ≤ B.scale E N (t N) := le_trans hQ301 hQ30
  -- the four summands are each at most `Q^5`
  have hR1 : (1 : ℝ) ≤ Step3.flowR B s t N := one_le_flowR hst ht1 N
  have hR0 : (0 : ℝ) ≤ Step3.flowR B s t N := by linarith
  have hRQ : Step3.flowR B s t N ≤ Q := flowR_le_ratio hst ht1 N
  have hQQ5 : Q ≤ Q ^ 5 := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ 5 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hQ5 : (1 : ℝ) ≤ Q ^ 5 := one_le_pow₀ hQ1
  have e1 : (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) ≤ Q ^ 5 := by
    have h1 : (1 : ℝ) ≤ Step3.flowR B s t N ^ 5 := one_le_pow₀ hR1
    calc (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2)
        ≤ (Step3.flowR B s t N ^ 5) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = Step3.flowR B s t N ^ 5 := Real.rpow_one _
      _ ≤ Q ^ 5 := pow_le_pow_left₀ hR0 hRQ 5
  have e3 : (Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) ^ 2 * (B.scale E N (t N))⁻¹ ≤ Q ^ 5 := by
    have hAs0 : 0 < Step3.flowAs B E s N := B.scale_pos' hE N (hs0 N) hs1
    have hsq : (Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) ^ 2 = Step3.flowAs B E s N := by
      rw [← Real.rpow_natCast (Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) 2,
        ← Real.rpow_mul hAs0.le]
      norm_num
    rw [hsq]
    have hAsQ : Step3.flowAs B E s N ≤ Q * B.scale E N (t N) :=
      Step3.flowScale_le_mul hW0 (hst N) (ht1 N)
    have : Step3.flowAs B E s N * (B.scale E N (t N))⁻¹ ≤ Q := by
      rw [mul_inv_le_iff₀ hAt0]
      linarith
    linarith
  have e4 : Step3.flowR B s t N ^ 2 ≤ Q ^ 5 := by
    calc Step3.flowR B s t N ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ hR0 hRQ 2
      _ ≤ Q ^ 5 := pow_le_pow_right₀ hQ1 (by norm_num)
  -- `Q^5 ≤ (W ℓ_t η_t)^{1/6}` and `4 ≤ (W ℓ_t η_t)^{1/12}`
  have hE6 : (Q ^ (30 : ℕ)) ^ ((1 : ℝ) / 6) = Q ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast Q 30, ← Real.rpow_mul hQ0.le, ← Real.rpow_natCast Q 5]
    norm_num
  have hQ5At : Q ^ 5 ≤ B.scale E N (t N) ^ ((1 : ℝ) / 6) := by
    have := Real.rpow_le_rpow (by positivity) hQ30 (show (0 : ℝ) ≤ 1 / 6 by norm_num)
    rwa [hE6] at this
  have h12 : (4 : ℝ) ≤ B.scale E N (t N) ^ ((1 : ℝ) / 12) := by
    have hcast : ((N : ℝ) ^ c) ^ ((1 : ℝ) / 12) = (N : ℝ) ^ (c / 12) := by
      rw [← Real.rpow_mul (by positivity)]; ring_nf
    calc (4 : ℝ) ≤ (N : ℝ) ^ (c / 12) := h4
      _ = ((N : ℝ) ^ c) ^ ((1 : ℝ) / 12) := hcast.symm
      _ ≤ B.scale E N (t N) ^ ((1 : ℝ) / 12) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) c) hNcAt (by norm_num)
  have hd : B.scale E N (t N) ^ ((1 : ℝ) / 4)
      = B.scale E N (t N) ^ ((1 : ℝ) / 6) * B.scale E N (t N) ^ ((1 : ℝ) / 12) := by
    rw [← Real.rpow_add hAt0]; norm_num
  have h16 : (0 : ℝ) ≤ B.scale E N (t N) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hAt0.le _
  rw [hd]
  nlinarith

/-! ### The packaged conclusions, without `AprioriDecayAll` -/

/-- **(2.77) with `h0` and `h12` discharged, from the `(+,+)` bootstrap** instead of from
`RBM.StepGlue.AprioriDecayAll`: the primed companion of `RBM.StepGlue.flow_sharpLoop_glue`, in
exactly the shape of the field `RBM.Steps.sharpLoop`. -/
theorem flow_sharpLoop_glue_of' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t) {Θ : ℕ → ℝ}
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N))
    (hΘle : ∀ᶠ N : ℕ in atTop, Θ N ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2))
    (h514 : ∀ n, 3 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) := by
  have hE : |E| < 2 := by linarith
  have hcond : Cond272 B E s t := Step2.cond272_of_strict hE hst ht1 hc0 hregS
  exact Step3.flow_sharpLoop X hκ0 hκ1 hEκ hs0 hst ht1 hcond h514
    (StepGlue.flow_S_zero' X hκ0 hκ1 hEκ hs0 hst ht1 hcond hapriori)
    (fun m l hm1 hm2 =>
      flow_S_le_two_of' X hE hs0 hst ht1 hcond hll hΘ hΘle m l hm1 hm2) hn

/-- **(2.78) and (2.79) with `h0`, `h12`, `h1`, `h2` discharged, from the `(+,+)` bootstrap**
instead of from `RBM.StepGlue.AprioriDecayAll`: the primed companion of
`RBM.StepGlue.flow_steps45_glue`, in exactly the shapes of the fields `RBM.Steps.sharpLmK` and
`RBM.Steps.sharpDecay`. -/
theorem flow_steps45_glue_of' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hsharp : SharpLoopFlow X E s t) (h45 : StepGlue.Eq45Flow X E s t) {Θ : ℕ → ℝ}
    (hΘ0 : ∀ N, 0 ≤ Θ N)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N))
    (hΘle : ∀ᶠ N : ℕ in atTop, Θ N ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2))
    (harith : ∀ᶠ N : ℕ in atTop,
      (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) +
        (1 + Θ N ^ 2 * (B.scale E N (t N))⁻¹ + Step3.flowR B s t N ^ 2) ≤
      B.scale E N (t N) ^ ((1 : ℝ) / 4))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h548 : Step45.FlowEq548 X E s t) :
    (∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)) ∧
    (∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)) := by
  have hE : |E| < 2 := by linarith
  have hcond : Cond272 B E s t := Step2.cond272_of_strict hE hst ht1 hc0 hregS
  have hone := StepGlue.flow_hs1 X hE hs0 ht1 h45 (hsharp 2 (by norm_num))
  exact Step45.flow_steps45 X hκ0 hκ1 hEκ hs0 hst ht1 hcond h514
    (StepGlue.flow_S_zero' X hκ0 hκ1 hEκ hs0 hst ht1 hcond hapriori)
    (fun m l hm1 hm2 => flow_S_le_two_of' X hE hs0 hst ht1 hcond hll hΘ hΘle m l hm1 hm2)
    hone
    (flow_hs2_of' X hE hs0 hst ht1 hcond hapriori (h514 2 le_rfl) hΘ0 hΘ hone harith) h548

/-- **(2.77) from the `(+,+)` bootstrap at the concrete target `Θ = (W ℓ_s η_s)^{1/2}`.** -/
theorem flow_sharpLoop_glue_flowAs' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 3 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) :=
  flow_sharpLoop_glue_of' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hapriori hll hΘ
    (Eventually.of_forall fun _ => le_rfl) h514 hn

/-- **(2.78) and (2.79) from the `(+,+)` bootstrap at the concrete target
`Θ = (W ℓ_s η_s)^{1/2}`**, with both arithmetic side conditions discharged from `hregS`
(`RBM.Step2PP.harith_flowAs`).  This is `RBM.StepGlue.flow_steps45_glue` with
`RBM.StepGlue.AprioriDecayAll` removed. -/
theorem flow_steps45_glue_flowAs' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hsharp : SharpLoopFlow X E s t) (h45 : StepGlue.Eq45Flow X E s t)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h548 : Step45.FlowEq548 X E s t) :
    (∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)) ∧
    (∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)) := by
  have hE : |E| < 2 := by linarith
  exact flow_steps45_glue_of' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hapriori hll hsharp h45
    (fun N => Real.rpow_nonneg (B.scale_pos' hE N (hs0 N) ((hst N).trans_lt (ht1 N))).le _)
    hΘ (Eventually.of_forall fun _ => le_rfl)
    (harith_flowAs hE hs0 hst ht1 hc0 hregS) h514 h548

/-! ### The bundle-shaped corollaries (kept for compatibility)

Each is the primed statement with the individual hypotheses replaced by the projections of a
`RBM.Steps`.  **They must not be used to produce a field of `RBM.Steps`** — that is the
circularity of T147 §0a; use the primed forms in the assembly. -/

theorem flow_xiL_apriori_le (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hSteps : Steps X E s t) {m : ℕ} (hm : 1 ≤ m) :
    StochDom B.P (Step3.flowXiL X E s t m)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowR B s t N ^ (m - 1)) :=
  flow_xiL_apriori_le' X hE hs0 hst ht1 hSteps.apriori hm

theorem flow_xiLK_one_le (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hSteps : Steps X E s t) :
    StochDom B.P (Step3.flowXiLK X E s t 1)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) :=
  flow_xiLK_one_le' X hE hs0 hst ht1 hcond hSteps.localLaw

theorem xiLK_two_improve_of (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hSteps : Steps X E s t)
    (h514 : Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) 2)
    {θ c₁ : ℕ → ℝ} (hθ0 : ∀ N, 0 ≤ θ N) (hc₁0 : ∀ N, 0 ≤ c₁ N)
    (hone : StochDom B.P (Step3.flowXiLK X E s t 1)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => c₁ N))
    (hθ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => θ N)) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) =>
        (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) +
          (c₁ N + θ N ^ 2 * (B.scale E N (t N))⁻¹ + Step3.flowR B s t N ^ 2)) :=
  xiLK_two_improve_of' X hE hs0 hst ht1 hcond hSteps.apriori h514 hθ0 hc₁0 hone hθ

theorem xiLK_two_improve (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hSteps : Steps X E s t)
    (h514 : Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) 2)
    {θ : ℕ → ℝ} (hθ0 : ∀ N, 0 ≤ θ N)
    (hθ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => θ N)) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) =>
        (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) +
          (Step3.flowAs B E s N ^ ((1 : ℝ) / 2) +
            θ N ^ 2 * (B.scale E N (t N))⁻¹ + Step3.flowR B s t N ^ 2)) :=
  xiLK_two_improve' X hE hs0 hst ht1 hcond hSteps.apriori hSteps.localLaw h514 hθ0 hθ

theorem flow_S_le_two_of (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hSteps : Steps X E s t) {Θ : ℕ → ℝ}
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N))
    (hΘle : ∀ᶠ N : ℕ in atTop, Θ N ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2))
    (m l : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2) :
    Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s) (Step3.flowR B s t)
      (Step3.flowA B E s t) m l :=
  flow_S_le_two_of' X hE hs0 hst ht1 hcond hSteps.localLaw hΘ hΘle m l hm1 hm2

theorem flow_hs2_of (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t) (hSteps : Steps X E s t)
    (h514 : Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) 2)
    {Θ : ℕ → ℝ} (hΘ0 : ∀ N, 0 ≤ Θ N)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N))
    (hone : StochDom B.P (Step3.flowXiLK X E s t 1)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => (1 : ℝ)))
    (harith : ∀ᶠ N : ℕ in atTop,
      (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) +
        (1 + Θ N ^ 2 * (B.scale E N (t N))⁻¹ + Step3.flowR B s t N ^ 2) ≤
      B.scale E N (t N) ^ ((1 : ℝ) / 4)) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      fun N u _ => Step3.flowA B E s t N u ^ ((1 : ℝ) / 4) :=
  flow_hs2_of' X hE hs0 hst ht1 hcond hSteps.apriori h514 hΘ0 hΘ hone harith

theorem flow_sharpLoop_glue_of (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hSteps : Steps X E s t) {Θ : ℕ → ℝ}
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N))
    (hΘle : ∀ᶠ N : ℕ in atTop, Θ N ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2))
    (h514 : ∀ n, 3 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) :=
  flow_sharpLoop_glue_of' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hSteps.apriori hSteps.localLaw
    hΘ hΘle h514 hn

theorem flow_steps45_glue_of (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hSteps : Steps X E s t) (h45 : StepGlue.Eq45Flow X E s t) {Θ : ℕ → ℝ}
    (hΘ0 : ∀ N, 0 ≤ Θ N)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N))
    (hΘle : ∀ᶠ N : ℕ in atTop, Θ N ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2))
    (harith : ∀ᶠ N : ℕ in atTop,
      (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) +
        (1 + Θ N ^ 2 * (B.scale E N (t N))⁻¹ + Step3.flowR B s t N ^ 2) ≤
      B.scale E N (t N) ^ ((1 : ℝ) / 4))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h548 : Step45.FlowEq548 X E s t) :
    (∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)) ∧
    (∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)) :=
  flow_steps45_glue_of' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hSteps.apriori hSteps.localLaw
    hSteps.sharpLoop h45 hΘ0 hΘ hΘle harith h514 h548

theorem flow_sharpLoop_glue_flowAs (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hSteps : Steps X E s t)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 3 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) :=
  flow_sharpLoop_glue_flowAs' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hSteps.apriori hSteps.localLaw
    hΘ h514 hn

theorem flow_steps45_glue_flowAs (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hSteps : Steps X E s t) (h45 : StepGlue.Eq45Flow X E s t)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h548 : Step45.FlowEq548 X E s t) :
    (∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)) ∧
    (∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)) :=
  flow_steps45_glue_flowAs' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hSteps.apriori hSteps.localLaw
    hSteps.sharpLoop h45 hΘ h514 h548


/-! ### The same glue from the **bare** (2.72) plus the regime bound (T209)

D13 fixes the step condition of Theorem 2.21 to `RBM.Cond272Reg` — (2.72) exactly as printed
plus `N^c ≤ W ℓ_t η_t` — while the primed glue above consumes `hregS = RBM.Cond272'`, i.e.
(2.72) *with* an `N^c` gain.  T186 showed no bridge exists (`a = 1`, `b = 30` forces `e ≤ 0`
in `RBM.rpow_mul_rpow_le_of_pow_thirty`), so the glue has to be restated.

Where does `hregS` actually go?  In `RBM.Step2PP.flow_sharpLoop_glue_of'` and
`RBM.Step2PP.flow_steps45_glue_of'` it is used **only** through
`RBM.Step2.cond272_of_strict`, i.e. only `RBM.Cond272` was ever needed; the sole genuine
consumer is `RBM.Step2PP.harith_flowAs`, which wants `Q^{30} ≤ W ℓ_t η_t` (the bare (2.72),
inverted) *and* `4 ≤ (W ℓ_t η_t)^{1/12}` (the regime bound).  Both are components of
`RBM.Cond272Reg`, so the bare route costs nothing here.

Since `RBM.Cond272Reg` is defined downstream (`Flow/Thm221Bare.lean`), the statements below
take its two components separately; `Flow/Thm221NoEL.lean` supplies them as `h.1` and `h.2`.
The `RBM.Cond272'` versions above are left untouched. -/

/-- **`RBM.Step2PP.harith_flowAs` from the bare (2.72) plus the regime bound.**  Identical
conclusion, and the proof is the original with its two uses of `hregS` split: `Q^{30} ≤ W ℓ_t
η_t` now comes from `RBM.Cond272` inverted, and `N^c ≤ W ℓ_t η_t` — which supplies the leftover
factor `4 ≤ (W ℓ_t η_t)^{1/12}` — is the regime bound itself. -/
theorem harith_flowAs_of_reg (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c) (hcond : Cond272 B E s t)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N)) :
    ∀ᶠ N : ℕ in atTop,
      (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) +
        (1 + (Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) ^ 2 * (B.scale E N (t N))⁻¹ +
          Step3.flowR B s t N ^ 2) ≤ B.scale E N (t N) ^ ((1 : ℝ) / 4) := by
  filter_upwards [hcond, hreg, eventually_le_rpow 4 (show (0 : ℝ) < c / 12 by positivity),
    eventually_ge_atTop 1] with N hN hNcAt h4 hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hW0 : (0 : ℝ) ≤ B.W N := by positivity
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  set Q : ℝ := (1 - s N) / (1 - t N) with hQdef
  have hQ1 : (1 : ℝ) ≤ Q := by rw [hQdef, le_div_iff₀ h1t]; linarith [hst N]
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hAt0 : 0 < B.scale E N (t N) :=
    B.scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)
  have hQ301 : (1 : ℝ) ≤ Q ^ 30 := one_le_pow₀ hQ1
  have hQ30 : Q ^ 30 ≤ B.scale E N (t N) := by
    have hinv := inv_anti₀ (inv_pos.2 hAt0) hN
    rw [inv_inv] at hinv
    have heq : Q ^ 30 = (((1 - t N) / (1 - s N)) ^ 30)⁻¹ := by
      rw [hQdef, ← inv_pow, inv_div]
    rw [heq]; exact hinv
  have hAt1 : (1 : ℝ) ≤ B.scale E N (t N) := le_trans hQ301 hQ30
  -- the four summands are each at most `Q^5`
  have hR1 : (1 : ℝ) ≤ Step3.flowR B s t N := one_le_flowR hst ht1 N
  have hR0 : (0 : ℝ) ≤ Step3.flowR B s t N := by linarith
  have hRQ : Step3.flowR B s t N ≤ Q := flowR_le_ratio hst ht1 N
  have hQQ5 : Q ≤ Q ^ 5 := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ 5 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hQ5 : (1 : ℝ) ≤ Q ^ 5 := one_le_pow₀ hQ1
  have e1 : (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) ≤ Q ^ 5 := by
    have h1 : (1 : ℝ) ≤ Step3.flowR B s t N ^ 5 := one_le_pow₀ hR1
    calc (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2)
        ≤ (Step3.flowR B s t N ^ 5) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = Step3.flowR B s t N ^ 5 := Real.rpow_one _
      _ ≤ Q ^ 5 := pow_le_pow_left₀ hR0 hRQ 5
  have e3 : (Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) ^ 2 * (B.scale E N (t N))⁻¹ ≤ Q ^ 5 := by
    have hAs0 : 0 < Step3.flowAs B E s N := B.scale_pos' hE N (hs0 N) hs1
    have hsq : (Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) ^ 2 = Step3.flowAs B E s N := by
      rw [← Real.rpow_natCast (Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) 2,
        ← Real.rpow_mul hAs0.le]
      norm_num
    rw [hsq]
    have hAsQ : Step3.flowAs B E s N ≤ Q * B.scale E N (t N) :=
      Step3.flowScale_le_mul hW0 (hst N) (ht1 N)
    have : Step3.flowAs B E s N * (B.scale E N (t N))⁻¹ ≤ Q := by
      rw [mul_inv_le_iff₀ hAt0]
      linarith
    linarith
  have e4 : Step3.flowR B s t N ^ 2 ≤ Q ^ 5 := by
    calc Step3.flowR B s t N ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ hR0 hRQ 2
      _ ≤ Q ^ 5 := pow_le_pow_right₀ hQ1 (by norm_num)
  -- `Q^5 ≤ (W ℓ_t η_t)^{1/6}` and `4 ≤ (W ℓ_t η_t)^{1/12}`
  have hE6 : (Q ^ (30 : ℕ)) ^ ((1 : ℝ) / 6) = Q ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast Q 30, ← Real.rpow_mul hQ0.le, ← Real.rpow_natCast Q 5]
    norm_num
  have hQ5At : Q ^ 5 ≤ B.scale E N (t N) ^ ((1 : ℝ) / 6) := by
    have := Real.rpow_le_rpow (by positivity) hQ30 (show (0 : ℝ) ≤ 1 / 6 by norm_num)
    rwa [hE6] at this
  have h12 : (4 : ℝ) ≤ B.scale E N (t N) ^ ((1 : ℝ) / 12) := by
    have hcast : ((N : ℝ) ^ c) ^ ((1 : ℝ) / 12) = (N : ℝ) ^ (c / 12) := by
      rw [← Real.rpow_mul (by positivity)]; ring_nf
    calc (4 : ℝ) ≤ (N : ℝ) ^ (c / 12) := h4
      _ = ((N : ℝ) ^ c) ^ ((1 : ℝ) / 12) := hcast.symm
      _ ≤ B.scale E N (t N) ^ ((1 : ℝ) / 12) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) c) hNcAt (by norm_num)
  have hd : B.scale E N (t N) ^ ((1 : ℝ) / 4)
      = B.scale E N (t N) ^ ((1 : ℝ) / 6) * B.scale E N (t N) ^ ((1 : ℝ) / 12) := by
    rw [← Real.rpow_add hAt0]; norm_num
  have h16 : (0 : ℝ) ≤ B.scale E N (t N) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hAt0.le _
  rw [hd]
  nlinarith

/-- **(2.77) with `h0`, `h12` discharged, from `RBM.Cond272` alone.**  Verbatim
`RBM.Step2PP.flow_sharpLoop_glue_of'`, whose hypotheses `hc0`/`hregS` are used only to produce
`RBM.Cond272` — so this is the same theorem with that step removed, and is strictly more
general. -/
theorem flow_sharpLoop_glue_of_cond272' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272 B E s t)
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t) {Θ : ℕ → ℝ}
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N))
    (hΘle : ∀ᶠ N : ℕ in atTop, Θ N ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2))
    (h514 : ∀ n, 3 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) := by
  have hE : |E| < 2 := by linarith
  exact Step3.flow_sharpLoop X hκ0 hκ1 hEκ hs0 hst ht1 hcond h514
    (StepGlue.flow_S_zero' X hκ0 hκ1 hEκ hs0 hst ht1 hcond hapriori)
    (fun m l hm1 hm2 =>
      flow_S_le_two_of' X hE hs0 hst ht1 hcond hll hΘ hΘle m l hm1 hm2) hn

/-- **(2.78) and (2.79) with `h0`, `h12`, `h1`, `h2` discharged, from `RBM.Cond272` alone.**
Verbatim `RBM.Step2PP.flow_steps45_glue_of'`; there too `hregS` only ever produced
`RBM.Cond272`, the arithmetic side condition being the separate hypothesis `harith`. -/
theorem flow_steps45_glue_of_cond272' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272 B E s t)
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hsharp : SharpLoopFlow X E s t) (h45 : StepGlue.Eq45Flow X E s t) {Θ : ℕ → ℝ}
    (hΘ0 : ∀ N, 0 ≤ Θ N)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Θ N))
    (hΘle : ∀ᶠ N : ℕ in atTop, Θ N ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2))
    (harith : ∀ᶠ N : ℕ in atTop,
      (Step3.flowR B s t N ^ 5) ^ ((1 : ℝ) / 2) +
        (1 + Θ N ^ 2 * (B.scale E N (t N))⁻¹ + Step3.flowR B s t N ^ 2) ≤
      B.scale E N (t N) ^ ((1 : ℝ) / 4))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h548 : Step45.FlowEq548 X E s t) :
    (∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)) ∧
    (∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)) := by
  have hE : |E| < 2 := by linarith
  have hone := StepGlue.flow_hs1 X hE hs0 ht1 h45 (hsharp 2 (by norm_num))
  exact Step45.flow_steps45 X hκ0 hκ1 hEκ hs0 hst ht1 hcond h514
    (StepGlue.flow_S_zero' X hκ0 hκ1 hEκ hs0 hst ht1 hcond hapriori)
    (fun m l hm1 hm2 => flow_S_le_two_of' X hE hs0 hst ht1 hcond hll hΘ hΘle m l hm1 hm2)
    hone
    (flow_hs2_of' X hE hs0 hst ht1 hcond hapriori (h514 2 le_rfl) hΘ0 hΘ hone harith) h548

/-- **(2.77) at `Θ = (W ℓ_s η_s)^{1/2}`, from `RBM.Cond272` alone.** -/
theorem flow_sharpLoop_glue_flowAs_of_cond272' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272 B E s t)
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 3 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) :=
  flow_sharpLoop_glue_of_cond272' X hκ0 hκ1 hEκ hs0 hst ht1 hcond hapriori hll hΘ
    (Eventually.of_forall fun _ => le_rfl) h514 hn

/-- **(2.78) and (2.79) at `Θ = (W ℓ_s η_s)^{1/2}`, from the bare (2.72) plus the regime
bound** — the D13 shape.  This is `RBM.Step2PP.flow_steps45_glue_flowAs'` with `hregS` replaced
by the two components of `RBM.Cond272Reg`; the arithmetic side condition is discharged by
`RBM.Step2PP.harith_flowAs_of_reg`. -/
theorem flow_steps45_glue_flowAs_of_reg' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c) (hcond : Cond272 B E s t)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N))
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hsharp : SharpLoopFlow X E s t) (h45 : StepGlue.Eq45Flow X E s t)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h548 : Step45.FlowEq548 X E s t) :
    (∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)) ∧
    (∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)) := by
  have hE : |E| < 2 := by linarith
  exact flow_steps45_glue_of_cond272' X hκ0 hκ1 hEκ hs0 hst ht1 hcond hapriori hll hsharp h45
    (fun N => Real.rpow_nonneg (B.scale_pos' hE N (hs0 N) ((hst N).trans_lt (ht1 N))).le _)
    hΘ (Eventually.of_forall fun _ => le_rfl)
    (harith_flowAs_of_reg hE hs0 hst ht1 hc0 hcond hreg) h514 h548


end Step2PP

end RBM

