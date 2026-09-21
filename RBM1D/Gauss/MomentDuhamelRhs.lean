/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.Envelope

/-!
# The right-hand side of the moment Duhamel formula: `hrhs` (T146)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2: the `‖·‖_{2p}` bounds on the three terms of (5.20) + (5.24) in moment form,
i.e. the hypothesis `hrhs` that `RBM.MomentDuhamel.stochDom_of_momentDuhamel` (T132a) reduces
the primed `Lemma 5.14` to.

## The route taken, and the one not taken

T132a's own estimate was that filling `hrhs` means redoing the moment version of the
`stochDom_of_logBound` machinery that `RBM.SumZeroDyn.term1F` / `termI1` / `QV1_stochDom` use.
**That machinery is not rebuilt here.**  Those three theorems bound the *whole* term — kernel,
tensor and time integral at once — on a high-probability event, and the high-probability
argument is what forces the `stochDom_of_logBound` pattern.  The moment route can afford to
split the term:

1. the kernel is deterministic, so it comes *out* of the norm by Minkowski
   (`momNorm_Uker_apply_le`, this file), with the same constant `C^n` as Lemma 7.1;
2. what is left is a `‖·‖_{2p}` bound on the *tensor alone*, which is T77's reverse bridge
   `RBM.Gauss.momentDom_of_stochDom` applied to the `≺` bounds of
   `RBM.SumZeroDyn.Lemma510` — here packaged as `momNormDom_of_stochDom`;
3. the time integral is handled by a pointwise-in-`u` bound
   (`intervalIntegral_le_of_le_const`), which needs no integrability hypothesis at all.

So none of `stochDom_of_logBound`, `term1F`, `termI1`, `QV1_stochDom` is restated or re-proved,
and none of them is used.

## Main results

* `RBM.Gauss.momNorm_le_of_le_weighted_sum` — Minkowski for a finite sum with deterministic
  weights, from Jensen.  The reason it is stated this way rather than as
  `‖∑ᵢ Yᵢ‖_q ≤ ∑ᵢ ‖Yᵢ‖_q` is that `RBM.MomentDuhamel.momNorm` is a raw
  `(∫ |Y|^q)^{1/q}`, not an `eLpNorm`, and the only integrability available is that of each
  `|Yᵢ|^q`.
* `RBM.Gauss.momNorm_Uker_apply_le` — **the `U`-kernel estimate in moment form**, the first of
  the three ingredients.  The supremum over the label `b` stays *outside* the moment; putting
  it inside would cost `(#LoopArg)^{1/(2p)} ≈ N^{Ccard/(2p)}`, which for a *fixed* `p` no
  `N^{ε/2}` can absorb.  This is the single place where the moment route differs structurally
  from the pathwise one, and it is a gain, not a loss.
* `RBM.Gauss.momNormDom_of_stochDom` — `≺` + deterministic envelope ⟹ `‖·‖_{2p}`, on an
  arbitrary index family, in particular one carrying a **time** (T124's net engine is not
  needed *here*; it is needed only afterwards, to make the *conclusion* of
  `stochDom_of_momentDuhamel` uniform in the endpoint `v`).
* `RBM.Gauss.hrhs_of_moment_inputs` — **the discharge of `hrhs`**: all three terms bounded,
  from kernel row-sum bounds, three `‖·‖`-inputs on the tensors, and one numerical closing
  hypothesis.  Verified by probe to fill the `hrhs` slot of
  `RBM.MomentDuhamel.stochDom_of_momentDuhamel` by a bare application.
* `RBM.Gauss.hFmom_of_momNormDom`, `RBM.Gauss.hinit_of_momNormDom` — the currying steps that
  put `momNormDom_of_stochDom`'s output into the shape `hrhs_of_moment_inputs` asks for.
* `RBM.Gauss.hEEmom_of_momNorm_two_mul`, `RBM.Gauss.hEEmom_of_momNormDom` — the same for the
  `E ⊗ E` input, which `hrhs_of_moment_inputs` asks for at the **odd-admissible** exponent
  `p`; these are Lyapunov's inequality (`RBM.MomentDuhamel.momNorm_le_momNorm_of_exponent_le`,
  T154(4)) applied under the quantifiers, and they are what lets an *even*-moment producer —
  every producer in this repository — feed `hEEmom`.

Nothing here touches `RBM.ThetaOp`: the kernel hypotheses are stated at the level of
`RBM.edgeKer` row sums (`RBM.sum_norm_edgeKer_row_le`), so the pending correction to
`ThetaOp`'s kernel (T140, the missing `S^{(B)}`) cannot affect any statement in this file.

## The parenthesisation of (5.24) (T146's defect, repaired by T147)

As first written, `RBM.MomentDuhamel.Hyp.momentDuhamel`, `Hyp.momentDuhamelQ` and the `hrhs`
slot of `stochDom_of_momentDuhamel` read

```
  ... ≤ A + 2 * ∫ u in s..v, T₂ u + (cMD p * ∫ u in s..v, T₃ u) ^ (1/2)
```

and the body of an `∫ … , …` extends to the right, so they *elaborated* as
`A + 2 * ∫ u in s..v, (T₂ u + (cMD p * ∫ T₃)^{1/2})` — the third term of (5.24) sitting
*inside* the time integral (in `momentDuhamelQ`, four integrals nesting four deep).  T146
proved `hrhs` against that reading, and the cost showed up as an extra factor `2 (v_N - s_N)`
on the third summand of `hnum`, exactly the effect of integrating a constant over the window.

Each `2 * ∫ …` is now parenthesised, the sum is a genuine sum of three (resp. five) terms, and
that extra factor is gone: `hnum`'s third summand is the bare
`((v_N - s_N) (Ck2^{2n+4} ΦE))^{1/2}`.  Only the middle summand is a time integral, and only it
carries the window length.

## What is *not* done

* The three `‖·‖`-inputs are hypotheses, not theorems.  Two of them (`hinit`, `hFmom`) are
  reduced to a `≺` with a **deterministic** control by `momNormDom_of_stochDom`;
  `RBM.SumZeroDyn.Lemma510.F_le` has a *random* control (`xiRhs`), so the missing step is the
  same `Ξ ≺ 1` replacement that `RBM.SumZeroDyn.F_stochDom` performs pathwise.
* ~~The `E ⊗ E` input `hEEmom` needs Lyapunov's inequality.~~  **Done (T154(4)).**  `hEEmom`
  is a **`p`-th** moment norm, not a `2p`-th one (that is what (5.24) asks for, and what
  `Hyp.momentDuhamel` writes), while T77's reverse bridge produces only even moments.  The
  missing step, Lyapunov's inequality `‖·‖_p ≤ ‖·‖_{2p}` on a probability space, is now
  `RBM.MomentDuhamel.momNorm_le_momNorm_of_exponent_le`, next to `momNorm`; the currying that
  turns an even bound into `hEEmom` is `RBM.Gauss.hEEmom_of_momNorm_two_mul` (and, from a
  `MomNormDom` on `RBM.Gauss.EEIdx`, `RBM.Gauss.hEEmom_of_momNormDom`) in this file.  What is
  still missing for `hEEmom` is only the *input*: the deterministic envelope that turns
  `RBM.EEBridge.stochDom_norm_eeField` into a `MomentDom`.
* `momentDuhamelQ` (the five-term `Q_t` route) has no consumer yet in
  `RBM1D/Gauss/MomentDuhamel.lean`, so there is nothing to discharge for it.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM.Gauss

open MeasureTheory Filter Real RBM.MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### The moment norm: monotonicity and the weighted triangle inequality -/

/-- Monotonicity of `‖·‖_q` in the pointwise absolute value. -/
theorem momNorm_mono {q : ℕ} {Y Z : Ω → ℝ} (hZ : Integrable (fun ω => |Z ω| ^ q) P)
    (h : ∀ ω, |Y ω| ≤ |Z ω|) : momNorm P q Y ≤ momNorm P q Z := by
  refine Real.rpow_le_rpow (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _) ?_ (by positivity)
  exact integral_mono_of_nonneg (Eventually.of_forall fun _ => pow_nonneg (abs_nonneg _) _) hZ
    (Eventually.of_forall fun ω => pow_le_pow_left₀ (abs_nonneg _) (h ω) q)

/-- **The weighted triangle inequality for `‖·‖_q`, in the form the kernel estimates need.**

If `|Z| ≤ ∑ᵢ cᵢ Yᵢ` pointwise with deterministic non-negative weights `cᵢ` and
`‖Yᵢ‖_q ≤ M` for every `i`, then `‖Z‖_q ≤ (∑ᵢ cᵢ) M`.

This is Minkowski's inequality specialised to a *finite* sum with deterministic weights, and it
is proved from Jensen (`ConvexOn.map_sum_le` for `x ↦ x^q` on `[0,∞)`) rather than from the
`L^q` machinery: the only integrability needed is that of each `Yᵢ^q`, which is exactly what
`RBM.MomentDuhamel.Hyp.integrable` and the deterministic envelope of T77 provide. -/
theorem momNorm_le_of_le_weighted_sum {ι : Type*} [Fintype ι] {q : ℕ} (hq : q ≠ 0)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {Y : ι → Ω → ℝ} (hY0 : ∀ i ω, 0 ≤ Y i ω)
    (hint : ∀ i, Integrable (fun ω => Y i ω ^ q) P)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, momNorm P q (Y i) ≤ M)
    {Z : Ω → ℝ} (hZ : ∀ ω, |Z ω| ≤ ∑ i, c i * Y i ω) :
    momNorm P q Z ≤ (∑ i, c i) * M := by
  have hqR : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hS0 : (0 : ℝ) ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  rcases hS0.eq_or_lt with hS | hS
  · -- all weights vanish, hence `Z = 0`
    have hzero : ∀ i, c i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).1 hS.symm i (Finset.mem_univ i)
      exact this
    have hZ0 : ∀ ω, |Z ω| = 0 := by
      intro ω
      refine le_antisymm ((hZ ω).trans (le_of_eq ?_)) (abs_nonneg _)
      exact Finset.sum_eq_zero fun i _ => by rw [hzero i, zero_mul]
    have : momNorm P q Z = 0 := by
      have : ∀ ω, |Z ω| ^ q = 0 := fun ω => by rw [hZ0 ω]; exact zero_pow hq
      simp only [momNorm, this, integral_zero]
      exact Real.zero_rpow (by positivity)
    rw [this, ← hS, zero_mul]
  · set S : ℝ := ∑ i, c i with hSdef
    set w : ι → ℝ := fun i => c i / S with hwdef
    have hw0 : ∀ i, 0 ≤ w i := fun i => div_nonneg (hc i) hS.le
    have hw1 : ∑ i, w i = 1 := by
      rw [hwdef]
      simp only [← Finset.sum_div, ← hSdef]
      exact div_self hS.ne'
    have hcw : ∀ i, c i = S * w i := fun i => by
      rw [hwdef]; field_simp
    -- Jensen, pointwise
    have hjensen : ∀ ω, (∑ i, w i * Y i ω) ^ q ≤ ∑ i, w i * Y i ω ^ q := by
      intro ω
      have h := (convexOn_pow (𝕜 := ℝ) q).map_sum_le (t := (Finset.univ : Finset ι))
        (w := w) (p := fun i => Y i ω) (fun i _ => hw0 i) (by simpa using hw1)
        (fun i _ => Set.mem_Ici.2 (hY0 i ω))
      simpa only [smul_eq_mul] using h
    -- the pointwise majorant
    have hpt : ∀ ω, |Z ω| ^ q ≤ S ^ q * ∑ i, w i * Y i ω ^ q := by
      intro ω
      have hrw : ∑ i, c i * Y i ω = S * ∑ i, w i * Y i ω := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hcw i]; ring
      have h1 : |Z ω| ^ q ≤ (S * ∑ i, w i * Y i ω) ^ q :=
        pow_le_pow_left₀ (abs_nonneg _) (hrw ▸ hZ ω) q
      refine h1.trans ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (hjensen ω) (pow_nonneg hS.le _)
    have hmajint : Integrable (fun ω => S ^ q * ∑ i, w i * Y i ω ^ q) P :=
      (integrable_finsetSum _ fun i _ => (hint i).const_mul (w i)).const_mul _
    have hle := integral_mono_of_nonneg
      (Eventually.of_forall fun ω => pow_nonneg (abs_nonneg (Z ω)) q) hmajint
      (Eventually.of_forall hpt)
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hint i).const_mul (w i))] at hle
    -- each `∫ Yᵢ^q` is `‖Yᵢ‖_q^q ≤ M^q`
    have hYi : ∀ i, ∫ ω, Y i ω ^ q ∂P ≤ M ^ q := by
      intro i
      have habs : ∀ ω, |Y i ω| ^ q = Y i ω ^ q := fun ω => by rw [abs_of_nonneg (hY0 i ω)]
      have h := momNorm_pow P hq (Y i)
      simp only [habs] at h
      rw [← h]
      exact pow_le_pow_left₀ (momNorm_nonneg P q (Y i)) (hM i) q
    have hsum : ∑ i, ∫ ω, w i * Y i ω ^ q ∂P ≤ M ^ q := by
      have : ∀ i, ∫ ω, w i * Y i ω ^ q ∂P ≤ w i * M ^ q := by
        intro i
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hYi i) (hw0 i)
      refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
      rw [← Finset.sum_mul, hw1, one_mul]
    have hfinal : ∫ ω, |Z ω| ^ q ∂P ≤ S ^ q * M ^ q :=
      hle.trans (mul_le_mul_of_nonneg_left hsum (pow_nonneg hS.le _))
    have hSM : (0 : ℝ) ≤ S * M := mul_nonneg hS.le hM0
    calc momNorm P q Z = (∫ ω, |Z ω| ^ q ∂P) ^ ((1 : ℝ) / q) := rfl
      _ ≤ (S ^ q * M ^ q) ^ ((1 : ℝ) / q) :=
          Real.rpow_le_rpow (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _) hfinal
            (by positivity)
      _ = S * M := by
          rw [← mul_pow, ← Real.rpow_natCast (S * M) q, ← Real.rpow_mul hSM, mul_one_div,
            div_self hqR, Real.rpow_one]

/-! ### The `U`-kernel estimate in moment form -/

/-- **The `l¹` mass of the `U` kernel at the row `a`.**  This is the sum that the proof of
Lemma 7.1 (`RBM.norm_Uker_apply_le`) bounds internally; it is isolated here because the moment
version must keep it *outside* the `‖·‖_q`, where the pathwise version may put it inside. -/
theorem sum_prod_norm_edgeKer_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ}
    {s t : ℂ} (ht : ∀ i, ‖t * ξ i‖ < 1) {C : ℝ}
    (hC : ∀ i, 1 + ‖(s - t) * ξ i‖ * (1 - ‖t * ξ i‖)⁻¹ ≤ C) (a : LoopArg L n) :
    (∑ b : LoopArg L n, ∏ i, ‖edgeKer L (ξ i) s t (a i) (b i)‖) ≤ C ^ n := by
  have hrow : ∀ i : Fin n, ∑ c : ZMod L, ‖edgeKer L (ξ i) s t (a i) c‖ ≤ C :=
    fun i => (sum_norm_edgeKer_row_le L hL (ht i) (a i)).trans (hC i)
  rw [sum_prod_pi L (fun i c => ‖edgeKer L (ξ i) s t (a i) c‖)]
  calc (∏ i : Fin n, ∑ c : ZMod L, ‖edgeKer L (ξ i) s t (a i) c‖)
      ≤ ∏ _i : Fin n, C :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (fun i _ => hrow i)
    _ = C ^ n := by simp

/-- **Lemma 7.1 in moment form**, the first of the three ingredients of `hrhs`.

If every entry of the (random) tensor `A` has `‖A_b‖_q ≤ M` — *uniformly in the label `b`, but
with no supremum over `b` inside the norm* — then `‖(U_{s,t,σ} ∘ A)_a‖_q ≤ C^n M`, with the same
constant `C^n` as the pathwise estimate `RBM.norm_Uker_apply_le`.

Why the supremum must stay outside: the pathwise route would bound `|(U ∘ A)_a|` by
`C^n max_b |A_b|` and then take the `q`-th moment, which costs a factor
`(#LoopArg)^{1/q} ≈ N^{Ccard/q}` — fatal, because in `hrhs` the exponent `q = 2p` is *fixed*
before `ε` is. Keeping the kernel mass outside the norm (Minkowski, i.e.
`momNorm_le_of_le_weighted_sum`) costs nothing at all. -/
theorem momNorm_Uker_apply_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) {q : ℕ} (hq : q ≠ 0)
    {n : ℕ} {ξ : Fin n → ℂ} {s t : ℂ} (ht : ∀ i, ‖t * ξ i‖ < 1) {C : ℝ}
    (hC : ∀ i, 1 + ‖(s - t) * ξ i‖ * (1 - ‖t * ξ i‖)⁻¹ ≤ C)
    {A : Ω → LoopArg L n → ℂ} (hint : ∀ b, Integrable (fun ω => ‖A ω b‖ ^ q) P)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b, momNorm P q (fun ω => ‖A ω b‖) ≤ M) (a : LoopArg L n) :
    momNorm P q (fun ω => ‖Uker L ξ s t (A ω) a‖) ≤ C ^ n * M := by
  set c : LoopArg L n → ℝ := fun b => ∏ i, ‖edgeKer L (ξ i) s t (a i) (b i)‖ with hcdef
  have hc : ∀ b, 0 ≤ c b := fun b => Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hsum := sum_prod_norm_edgeKer_le L hL ht hC a
  have hZ : ∀ ω, |‖Uker L ξ s t (A ω) a‖| ≤ ∑ b, c b * ‖A ω b‖ := by
    intro ω
    rw [abs_of_nonneg (norm_nonneg _)]
    calc ‖Uker L ξ s t (A ω) a‖
        ≤ ∑ b : LoopArg L n, ‖(∏ i, edgeKer L (ξ i) s t (a i) (b i)) * A ω b‖ := norm_sum_le _ _
      _ = ∑ b, c b * ‖A ω b‖ := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [norm_mul, norm_prod]
  refine (momNorm_le_of_le_weighted_sum hq hc (fun b ω => norm_nonneg _) hint hM0 hM hZ).trans ?_
  exact mul_le_mul_of_nonneg_right hsum hM0

/-! ### The time integral -/

/-- `∫_a^b f ≤ (b - a) M` from a pointwise bound on `[a,b]`, **with no integrability
hypothesis**: if `f` is not interval-integrable the Bochner integral is `0` by convention and
the bound is trivial.  This is what lets the three `‖·‖_{2p}`-valued integrands of `hrhs` be
handled without proving that `u ↦ ‖·‖_{2p}` is measurable. -/
theorem intervalIntegral_le_of_le_const {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M) {f : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, f u ≤ M) : ∫ u in a..b, f u ≤ (b - a) * M := by
  by_cases hi : IntervalIntegrable f volume a b
  · have h := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const hf
    simpa [mul_comm] using h
  · rw [intervalIntegral.integral_undef hi]
    have hba : (0 : ℝ) ≤ b - a := by linarith
    positivity

/-! ### `‖·‖_{2p}`-domination -/

/-- **`‖Y‖_{2p} ≤ C N^{ε/2} Φ`, for every `ε > 0` and every `p ≥ 1`, eventually in `N` and
uniformly in the index.**  This is the exact shape of the hypothesis `hrhs` of
`RBM.MomentDuhamel.stochDom_of_momentDuhamel`, and — by
`RBM.MomentDuhamel.momentDom_of_momNorm_le` — it is equivalent to `RBM.Gauss.MomentDom`. -/
def MomNormDom (P : Measure Ω) {U : ℕ → Type*} (Y : ∀ N, U N → Ω → ℝ) (Φ : ∀ N, U N → ℝ) :
    Prop :=
  ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u : U N,
    momNorm P (2 * p) (Y N u) ≤ C * ((N : ℝ) ^ (ε / 2) * Φ N u)

/-- **The `≺ ⟹ ‖·‖_{2p}` bridge, second half.**  T77's `RBM.Gauss.momentDom_of_stochDom` turns
`≺` plus a deterministic envelope into `MomentDom`; this turns `MomentDom` into the moment-norm
form `hrhs` wants.  Nothing here needs a `Fintype` on the index, so the index may carry a *time*
— which is exactly what the drift term of `hrhs` requires and what
`RBM.Gauss.stochDom_of_momentDom` (on the way back) forbids. -/
theorem momNormDom_of_momentDom {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ}
    (hΦ0 : ∀ N u, 0 ≤ Φ N u) (h : MomentDom P Y Φ) : MomNormDom P Y Φ := by
  intro ε hε p hp
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨C, hC0, hN⟩ := h ε hε p
  set r : ℝ := (1 : ℝ) / ((2 * p : ℕ) : ℝ) with hrdef
  have hcast : ((2 * p : ℕ) : ℝ) = 2 * (p : ℝ) := by push_cast; ring
  have hne : ((2 * p : ℕ) : ℝ) ≠ 0 := by rw [hcast]; positivity
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  refine ⟨C ^ r + 1, by positivity, ?_⟩
  filter_upwards [hN, eventually_ge_atTop 1] with N hNu hN1 u
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hΦu := hΦ0 N u
  have hmom : momNorm P (2 * p) (Y N u)
      ≤ (C * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p))) ^ r := by
    rw [momNorm]
    exact Real.rpow_le_rpow (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _) (hNu u) hr0
  have hrw : (C * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p))) ^ r
      = C ^ r * ((N : ℝ) ^ (ε / 2) * Φ N u) := by
    rw [Real.mul_rpow hC0.le (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    congr 2
    · rw [← Real.rpow_mul hN0.le, hrdef, hcast]
      congr 1
      field_simp
    · rw [← Real.rpow_natCast (Φ N u) (2 * p), ← Real.rpow_mul hΦu, hrdef, mul_one_div,
        div_self hne, Real.rpow_one]
  rw [hrw] at hmom
  refine hmom.trans ?_
  have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (ε / 2) * Φ N u := by positivity
  nlinarith [Real.rpow_nonneg hC0.le r]

/-- **The `≺ ⟹ ‖·‖_{2p}` bridge of T146's step 0, in one step.**

T77's `RBM.Gauss.momentDom_of_stochDom` composed with `momNormDom_of_momentDom`: a pointwise
`≺` bound with a *deterministic* control, a deterministic envelope of polynomial size, and a
polynomial lower bound on the control, give the `‖·‖_{2p}` bounds that `hrhs` consumes.

The index family `U` is arbitrary — in particular it may be a product carrying a **time**.
That is the whole point: the `≺` statements of `RBM.SumZeroDyn.Lemma510` are already indexed by
`RBM.TimeIcc`, and nothing on this side of the bridge asks for a `Fintype`. -/
theorem momNormDom_of_stochDom [IsFiniteMeasure P] {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ}
    {Φ : ∀ N, U N → ℝ} {Env : ℕ → ℝ} {Kenv Blow : ℝ}
    (hmeas : ∀ (N : ℕ) (u : U N), Measurable (Y N u))
    (hint : ∀ (r N : ℕ) (u : U N), Integrable (fun ω => |Y N u ω| ^ (2 * r)) P)
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ Blow)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (N : ℝ) ^ (-Blow) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω), |Y N u ω| ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hdom : StochDom P (fun N u ω => |Y N u ω|) (fun N u _ => Φ N u)) :
    MomNormDom P Y Φ :=
  momNormDom_of_momentDom (fun N u => (hΦ N u).le)
    (momentDom_of_stochDom hmeas hint hΦ hB hΦlow hEnv0 hKenv henv hEnvpoly hdom)

/-! ### `hrhs`: the three terms of the moment Duhamel right-hand side -/

section Rhs

variable {B : Band Ω}

/-- The index of the drift input of `hrhs_of_moment_inputs`: a time in the window `[s_N, v_N]`,
a charge/label pair, and the label of the tensor entry. -/
abbrev DriftIdx (B : Band Ω) (s v : ℕ → ℝ) (n N : ℕ) : Type :=
  {u : ℝ // s N ≤ u ∧ u ≤ v N} × LoopData (B.L N) (n + 2) × LoopArg (B.L N) (n + 2)

/-- **The drift input of `hrhs_of_moment_inputs` is a `MomNormDom` on `DriftIdx`**, hence
(by `momNormDom_of_stochDom`) available from a `≺` bound indexed by a time — the shape of
`RBM.SumZeroDyn.Lemma510.F_le`. -/
theorem hFmom_of_momNormDom {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ} (H : Hyp X E s t n)
    (v : ℕ → ℝ) {ΦF : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (h : MomNormDom B.P
      (fun N (i : DriftIdx B s v n N) ω => ‖H.F N (i.1 : ℝ) (X.H N (i.1 : ℝ) ω) i.2.1.1 i.2.2‖)
      (fun N i => ΦF N i.2.1)) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ (q : LoopData (B.L N) (n + 2))
        (b : LoopArg (B.L N) (n + 2)),
        momNorm B.P (2 * p) (fun ω => ‖H.F N u (X.H N u ω) q.1 b‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * ΦF N q) := by
  intro ε hε p hp
  obtain ⟨C, hC0, hN⟩ := h ε hε p hp
  exact ⟨C, hC0, hN.mono fun N hNi u hu1 hu2 q b => hNi (⟨u, hu1, hu2⟩, q, b)⟩

/-- **The initial input of `hrhs_of_moment_inputs` is a `MomNormDom`** on the label index at the
single time `s_N`; this is the moment form of the hypothesis (2.68) that
`RBM.SumZeroDyn.termI1` consumes as `hLmK`. -/
theorem hinit_of_momNormDom {X : Sample B} {E : ℝ} {s : ℕ → ℝ} {n : ℕ}
    {Φ1 : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (h : MomNormDom B.P
      (fun N (i : LoopData (B.L N) (n + 2) × LoopArg (B.L N) (n + 2)) ω =>
        ‖SumZeroDyn.lkT X E N (s N) ω i.1.1 i.2‖)
      (fun N i => Φ1 N i.1)) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (q : LoopData (B.L N) (n + 2)) (b : LoopArg (B.L N) (n + 2)),
        momNorm B.P (2 * p) (fun ω => ‖SumZeroDyn.lkT X E N (s N) ω q.1 b‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * Φ1 N q) := by
  intro ε hε p hp
  obtain ⟨C, hC0, hN⟩ := h ε hε p hp
  exact ⟨C, hC0, hN.mono fun N hNi q b => hNi (q, b)⟩

/-- The index of the `E ⊗ E` input of `hrhs_of_moment_inputs`: a time in the window
`[s_N, v_N]`, a charge/label pair, and the label of the **doubled** tensor entry. -/
abbrev EEIdx (B : Band Ω) (s v : ℕ → ℝ) (n N : ℕ) : Type :=
  {u : ℝ // s N ≤ u ∧ u ≤ v N} × LoopData (B.L N) (n + 2) ×
    LoopArg (B.L N) ((n + 2) + (n + 2))

/-- **`hEEmom` of `hrhs_of_moment_inputs` from the *even* bound, by Lyapunov.**

`hEEmom` asks for the `p`-th moment norm of `E ⊗ E`, whereas every producer in the repository
— T77's `RBM.Gauss.momentDom_of_stochDom`, and hence `momNormDom_of_stochDom` and T135's
`RBM.EEBridge.stochDom_norm_eeField` read through it — delivers **even** moments only.  The
missing step is Lyapunov's inequality `‖·‖_p ≤ ‖·‖_{2p}`, i.e.
`RBM.MomentDuhamel.momNorm_le_momNorm_of_exponent_le`; this lemma is nothing but that
inequality applied under the quantifiers, with the same constant `C` and the same control
`ΦE`.

The integrability hypothesis is the one `hrhs_of_moment_inputs` already takes (`hintEE`), so
this costs the caller nothing. -/
theorem hEEmom_of_momNorm_two_mul [IsProbabilityMeasure (B.P)]
    {X : Sample B} {E : ℝ} {s v : ℕ → ℝ} {n : ℕ}
    {ΦE : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hintEE : ∀ (r N : ℕ) (u : ℝ) (σ : Fin (n + 2) → Bool)
        (c : LoopArg (B.L N) ((n + 2) + (n + 2))),
      Integrable (fun ω => ‖eeFun B E N u (X.H N u ω) σ c‖ ^ r) B.P)
    (h2 : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ (q : LoopData (B.L N) (n + 2))
        (c : LoopArg (B.L N) ((n + 2) + (n + 2))),
        momNorm B.P (2 * p) (fun ω => ‖eeFun B E N u (X.H N u ω) q.1 c‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * ΦE N q)) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ (q : LoopData (B.L N) (n + 2))
        (c : LoopArg (B.L N) ((n + 2) + (n + 2))),
        momNorm B.P p (fun ω => ‖eeFun B E N u (X.H N u ω) q.1 c‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * ΦE N q) := by
  intro ε hε p hp
  obtain ⟨C, hC0, hN⟩ := h2 ε hε p hp
  refine ⟨C, hC0, hN.mono fun N hNi u hu1 hu2 q c => ?_⟩
  refine le_trans ?_ (hNi u hu1 hu2 q c)
  refine momNorm_le_momNorm_of_exponent_le (by omega) (by omega) ?_
  simpa only [abs_norm] using hintEE (2 * p) N u q.1 c

/-- **`hEEmom` from a `MomNormDom` on `EEIdx`**, the shape `momNormDom_of_stochDom` produces
from T135's `RBM.EEBridge.stochDom_norm_eeField` together with a deterministic envelope.
This is `hEEmom_of_momNorm_two_mul` precomposed with the currying of `hFmom_of_momNormDom`. -/
theorem hEEmom_of_momNormDom [IsProbabilityMeasure (B.P)]
    {X : Sample B} {E : ℝ} {s : ℕ → ℝ} {n : ℕ} (v : ℕ → ℝ)
    {ΦE : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hintEE : ∀ (r N : ℕ) (u : ℝ) (σ : Fin (n + 2) → Bool)
        (c : LoopArg (B.L N) ((n + 2) + (n + 2))),
      Integrable (fun ω => ‖eeFun B E N u (X.H N u ω) σ c‖ ^ r) B.P)
    (h : MomNormDom B.P
      (fun N (i : EEIdx B s v n N) ω =>
        ‖eeFun B E N (i.1 : ℝ) (X.H N (i.1 : ℝ) ω) i.2.1.1 i.2.2‖)
      (fun N i => ΦE N i.2.1)) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ (q : LoopData (B.L N) (n + 2))
        (c : LoopArg (B.L N) ((n + 2) + (n + 2))),
        momNorm B.P p (fun ω => ‖eeFun B E N u (X.H N u ω) q.1 c‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * ΦE N q) :=
  hEEmom_of_momNorm_two_mul hintEE fun ε hε p hp => by
    obtain ⟨C, hC0, hN⟩ := h ε hε p hp
    exact ⟨C, hC0, hN.mono fun N hNi u hu1 hu2 q c => hNi (⟨u, hu1, hu2⟩, q, c)⟩

/-- **`hrhs` for `RBM.MomentDuhamel.stochDom_of_momentDuhamel`.**

The three terms of the moment Duhamel right-hand side are bounded by `C N^{ε/2} Φ` as soon as

* the `U` kernel has `l¹` row mass at most `Ck` (resp. `Ck2` for the doubled charge `ξ²`)
  throughout the window `[s_N, v_N]` — the input of Lemma 7.1;
* the three tensors `(L-K)_{s_N}`, `F_u`, `(E ⊗ E)_u` obey `‖·‖_{2p}` (resp. `‖·‖_p`) bounds
  uniformly in the label **and in the time `u ∈ [s_N, v_N]`** — the `≺` statements of
  `RBM.SumZeroDyn.Lemma510` read through T77's reverse bridge, `momNormDom_of_momentDom`;
* the three resulting deterministic controls close numerically against `Φ` (`hnum`).

No martingale, no quadratic variation and no pathwise Duhamel appear.  Note also that the
kernel hypotheses are stated at the level of `RBM.edgeKer` row sums, so this theorem is
independent of `RBM.ThetaOp`.

The uniformity in `u` is what the moment route needs and the `≺` route does not have for free:
it is supplied by `momNormDom_of_momentDom` on an index type carrying the time, which is legal
precisely because `RBM.Gauss.MomentDom` — unlike `RBM.Gauss.stochDom_of_momentDom` — does not
ask for a `Fintype`. -/
theorem hrhs_of_moment_inputs [IsProbabilityMeasure (B.P)]
    {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ} (H : Hyp X E s t n)
    (v : ℕ → ℝ) (hsv : ∀ N, s N ≤ v N) (hvt : ∀ N, v N ≤ t N)
    {Ck Ck2 : ℝ} (hCk0 : 0 ≤ Ck) (hCk20 : 0 ≤ Ck2)
    (hkerlt : ∀ᶠ N : ℕ in atTop, ∀ (σ : Fin (n + 2) → Bool) (i : Fin (n + 2)),
      ‖((v N : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1)
    (hkerC : ∀ᶠ N : ℕ in atTop, ∀ (σ : Fin (n + 2) → Bool) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ i, 1 + ‖(((u : ℝ) : ℂ) - ((v N : ℝ) : ℂ)) * xiOf (mSigma E) σ i‖
        * (1 - ‖((v N : ℝ) : ℂ) * xiOf (mSigma E) σ i‖)⁻¹ ≤ Ck)
    (hker2lt : ∀ᶠ N : ℕ in atTop, ∀ (σ : Fin (n + 2) → Bool) (i : Fin ((n + 2) + (n + 2))),
      ‖((v N : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖ < 1)
    (hker2C : ∀ᶠ N : ℕ in atTop, ∀ (σ : Fin (n + 2) → Bool) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ i, 1 + ‖(((u : ℝ) : ℂ) - ((v N : ℝ) : ℂ)) * SumZeroDyn.xi2 E σ i‖
        * (1 - ‖((v N : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖)⁻¹ ≤ Ck2)
    (hintF : ∀ (r N : ℕ) (u : ℝ) (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) (n + 2)),
      Integrable (fun ω => ‖H.F N u (X.H N u ω) σ b‖ ^ r) B.P)
    (hintEE : ∀ (r N : ℕ) (u : ℝ) (σ : Fin (n + 2) → Bool)
        (c : LoopArg (B.L N) ((n + 2) + (n + 2))),
      Integrable (fun ω => ‖eeFun B E N u (X.H N u ω) σ c‖ ^ r) B.P)
    {Φ1 ΦF ΦE : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hΦ10 : ∀ N q, 0 ≤ Φ1 N q) (hΦF0 : ∀ N q, 0 ≤ ΦF N q) (hΦE0 : ∀ N q, 0 ≤ ΦE N q)
    (hinit : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (q : LoopData (B.L N) (n + 2)) (b : LoopArg (B.L N) (n + 2)),
        momNorm B.P (2 * p) (fun ω => ‖SumZeroDyn.lkT X E N (s N) ω q.1 b‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * Φ1 N q))
    (hFmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ (q : LoopData (B.L N) (n + 2))
        (b : LoopArg (B.L N) (n + 2)),
        momNorm B.P (2 * p) (fun ω => ‖H.F N u (X.H N u ω) q.1 b‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * ΦF N q))
    (hEEmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ (q : LoopData (B.L N) (n + 2))
        (c : LoopArg (B.L N) ((n + 2) + (n + 2))),
        momNorm B.P p (fun ω => ‖eeFun B E N u (X.H N u ω) q.1 c‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * ΦE N q))
    {Φ : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hnum : ∀ᶠ N : ℕ in atTop, ∀ q : LoopData (B.L N) (n + 2),
      Ck ^ (n + 2) * Φ1 N q
        + 2 * ((v N - s N) * (Ck ^ (n + 2) * ΦF N q))
        + ((v N - s N) * (Ck2 ^ ((n + 2) + (n + 2)) * ΦE N q)) ^ ((1 : ℝ) / 2)
      ≤ Φ N q) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (SumZeroDyn.lkT X E N (s N) ω q.1) q.2‖)
          + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
              ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (H.F N u (X.H N u ω) q.1) q.2‖))
          + (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
              ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
                (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
          ≤ C * ((N : ℝ) ^ (ε / 2) * Φ N q) := by
  intro ε hε p hp
  obtain ⟨C1, hC10, hA1⟩ := hinit ε hε p hp
  obtain ⟨C2, hC20, hA2⟩ := hFmom ε hε p hp
  obtain ⟨C3, hC30, hA3⟩ := hEEmom ε hε p hp
  have hcMD := H.cMD_nonneg p
  set Csq : ℝ := (H.cMD p * C3) ^ ((1 : ℝ) / 2) with hCsq
  have hCsq0 : 0 ≤ Csq := Real.rpow_nonneg (by positivity) _
  refine ⟨C1 + C2 + Csq + 1, by positivity, ?_⟩
  filter_upwards [hA1, hA2, hA3, hnum, hkerlt, hkerC, hker2lt, hker2C, eventually_ge_atTop 1]
    with N h1 h2 h3 hnumN hlt hCN hlt2 hCN2 hNge q
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNge
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have h2p : 2 * p ≠ 0 := by omega
  have hp0 : p ≠ 0 := by omega
  set Np : ℝ := (N : ℝ) ^ (ε / 2) with hNp
  have hNp0 : (0 : ℝ) < Np := Real.rpow_pos_of_pos hN0 _
  set K1 : ℝ := Ck ^ (n + 2) * Φ1 N q with hK1def
  set K2 : ℝ := (v N - s N) * (Ck ^ (n + 2) * ΦF N q) with hK2def
  set K3 : ℝ := (v N - s N) * (Ck2 ^ ((n + 2) + (n + 2)) * ΦE N q) with hK3def
  have hvs : 0 ≤ v N - s N := by have := hsv N; linarith
  have hK10 : 0 ≤ K1 := by rw [hK1def]; have := hΦ10 N q; positivity
  have hK20 : 0 ≤ K2 := by rw [hK2def]; have := hΦF0 N q; positivity
  have hK30 : 0 ≤ K3 := by rw [hK3def]; have := hΦE0 N q; positivity
  -- the initial term
  have hT1 : momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N (s N) ω q.1) q.2‖)
      ≤ C1 * (Np * K1) := by
    have hbound := momNorm_Uker_apply_le (P := B.P) (B.L N) hL3 h2p (hlt q.1)
      (hCN q.1 (s N) le_rfl (hsv N))
      (A := fun ω => SumZeroDyn.lkT X E N (s N) ω q.1)
      (fun b => by
        simpa using H.integrable (2 * p) N (s N) le_rfl ((hsv N).trans (hvt N)) q.1 b)
      (M := C1 * (Np * Φ1 N q)) (by have := hΦ10 N q; positivity) (fun b => h1 q b) q.2
    refine hbound.trans (le_of_eq ?_)
    rw [hK1def]; ring
  -- the drift term, pointwise in the time
  have hT2 : ∀ u ∈ Set.Icc (s N) (v N), momNorm B.P (2 * p) (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (H.F N u (X.H N u ω) q.1) q.2‖)
      ≤ Ck ^ (n + 2) * (C2 * (Np * ΦF N q)) := by
    intro u hu
    exact momNorm_Uker_apply_le (P := B.P) (B.L N) hL3 h2p (hlt q.1)
      (hCN q.1 u hu.1 hu.2) (A := fun ω => H.F N u (X.H N u ω) q.1)
      (fun b => hintF (2 * p) N u q.1 b) (by have := hΦF0 N q; positivity)
      (fun b => h2 u hu.1 hu.2 q b) q.2
  -- the `E ⊗ E` term
  have hI3nonneg : 0 ≤ ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
      ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖) :=
    intervalIntegral.integral_nonneg (hsv N) fun u _ => momNorm_nonneg _ _ _
  have hI3 : ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
        ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖)
      ≤ C3 * (Np * K3) := by
    have hconst : ∀ u ∈ Set.Icc (s N) (v N), momNorm B.P p (fun ω =>
        ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖)
        ≤ Ck2 ^ ((n + 2) + (n + 2)) * (C3 * (Np * ΦE N q)) := by
      intro u hu
      exact momNorm_Uker_apply_le (P := B.P) (B.L N) hL3 hp0 (hlt2 q.1)
        (hCN2 q.1 u hu.1 hu.2) (A := fun ω => eeFun B E N u (X.H N u ω) q.1)
        (fun c => hintEE p N u q.1 c) (by have := hΦE0 N q; positivity)
        (fun c => h3 u hu.1 hu.2 q c) (Fin.append q.2 q.2)
    have := intervalIntegral_le_of_le_const (hsv N)
      (by have := hΦE0 N q; positivity :
        (0:ℝ) ≤ Ck2 ^ ((n + 2) + (n + 2)) * (C3 * (Np * ΦE N q))) hconst
    refine this.trans (le_of_eq ?_)
    rw [hK3def]; ring
  have hT3 : (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
        ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
      ≤ Csq * (Np * K3 ^ ((1 : ℝ) / 2)) := by
    have hstep : (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
          ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
            (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
        ≤ ((H.cMD p * C3) * (Np * K3)) ^ ((1 : ℝ) / 2) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      calc H.cMD p * _ ≤ H.cMD p * (C3 * (Np * K3)) :=
            mul_le_mul_of_nonneg_left hI3 hcMD
        _ = (H.cMD p * C3) * (Np * K3) := by ring
    refine hstep.trans ?_
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hNp0.le hK30, ← hCsq]
    have hNp1 : (1 : ℝ) ≤ Np := by
      rw [hNp]; exact Real.one_le_rpow hNge1 (by positivity)
    have hhalf : Np ^ ((1 : ℝ) / 2) ≤ Np := by
      calc Np ^ ((1 : ℝ) / 2) ≤ Np ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hNp1 (by norm_num)
        _ = Np := Real.rpow_one Np
    have hK3s : (0 : ℝ) ≤ K3 ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hK30 _
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hhalf hK3s) hCsq0
  -- assemble: three genuinely separate summands, as in (5.24).  Only the *middle* one is a
  -- time integral, so only it picks up the window length `v_N - s_N`.
  have hK3s : (0 : ℝ) ≤ K3 ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hK30 _
  have hMnn : (0 : ℝ) ≤ Ck ^ (n + 2) * (C2 * (Np * ΦF N q)) := by
    have := hΦF0 N q; positivity
  have hI2 : (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (H.F N u (X.H N u ω) q.1) q.2‖))
      ≤ C2 * (Np * K2) := by
    refine (intervalIntegral_le_of_le_const (hsv N) hMnn hT2).trans (le_of_eq ?_)
    rw [hK2def]; ring
  refine (add_le_add (add_le_add hT1
    (mul_le_mul_of_nonneg_left hI2 (by norm_num : (0 : ℝ) ≤ 2))) hT3).trans ?_
  have hb1 : (0 : ℝ) ≤ Np * K1 := mul_nonneg hNp0.le hK10
  have hb2 : (0 : ℝ) ≤ Np * K2 := mul_nonneg hNp0.le hK20
  have hb3 : (0 : ℝ) ≤ Np * K3 ^ ((1 : ℝ) / 2) := mul_nonneg hNp0.le hK3s
  have hmain : C1 * (Np * K1) + 2 * (C2 * (Np * K2)) + Csq * (Np * K3 ^ ((1 : ℝ) / 2))
      ≤ (C1 + C2 + Csq + 1) * (Np * (K1 + 2 * K2 + K3 ^ ((1 : ℝ) / 2))) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ C2 + Csq + 1 by linarith) hb1,
      mul_nonneg (show (0 : ℝ) ≤ C1 + Csq + 1 by linarith) hb2,
      mul_nonneg (show (0 : ℝ) ≤ C1 + C2 + 1 by linarith) hb3]
  refine hmain.trans ?_
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (hnumN q) hNp0.le) (by linarith)

end Rhs

end RBM.Gauss
