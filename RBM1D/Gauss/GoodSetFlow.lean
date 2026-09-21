/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Eq45FlowInputs
import RBM1D.Gauss.Step1Hyp

/-!
# The good event (4.4) at **every** time of the flow — T130

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 4.1 (4.1)/(4.4).

`RBM1D/Gauss/CondStableInst.lean` (T119) leaves the good event of (4.1) at **one** time as its
last local-law hypothesis `hΩ`, and supplies the bridge
`RBM.Gauss.highProb_goodSet_of_stochDom`: (4.4) at a fixed time follows from the weak local law
`‖G - m‖_max ≺ Ψ` together with a polynomial margin `∀ᶠ N, N^τ Ψ_N ≤ δ_N`.
`RBM1D/Gauss/Eq45FlowInputs.lean` (T124) needs the **`u`-uniform** version of that event —
`RBM.Gauss.goodSetFlow`, the good event at *every* `u ∈ [s_N, t_N]` simultaneously — and lists
it as its remaining input (1).  This file produces it.

## Why this is a net statement, and which pieces do the work

`RBM.Gauss.goodSetFlow` puts an uncountable intersection over `u` inside one event, so its
complement is an uncountable union and no fixed-time statement gives it by itself.  The shape
of the argument is the standard one:

* the **fixed-time weak local law, uniform in the time** — `RBM.Gauss.LocalLawUnifIcc` below,
  which is `RBM.Gauss.UnifDomIcc` (T124) for the entries of `G_u - m`.  This is the input that
  Steps 1/2 ((2.74)/(2.75)) supply and that cannot be proved here, so it is a hypothesis;
* the **deterministic modulus in the time** — `RBM.Gauss.abs_norm_green_flow_entry_sub_le`
  below, which is T106's `RBM.Gauss.norm_green_flow_sub_le` read off one entry, with the
  Hölder-`1/2` constant `η_{t_N}^{-2}(‖X‖+1)`;
* the **union bound over the net**, which is exactly T124's engine
  `RBM.Gauss.stochDom_timeIcc_of_unifDom`; the random Hölder constant is made deterministic on
  `‖X‖ ≤ N`, which has high probability by `‖X‖ ≺ 1` (T109, unconditional).

So no new net machinery is built here: the engine of T124 is instantiated at
`ξ = ‖(G_u - m)_{xy}‖`, `ζ = Ψ_N`, `γ = 1/2`, `T = 1`, `Ξ = {‖X‖ ≤ N}`.

## The `t_N → 1` caveat of T119, again

T119 warns against routing slow variation of the control through `L^max ≍ W^{-1}`, whose upper
half costs `η^{-2}` and stops being a `≺` as `t_N → 1`; T124 therefore used a genuine modulus.
Here the caveat **does not bite at all**, and not by accident: the control of the weak local
law is the *deterministic* `Ψ_N`, constant in `u`, so the engine's `hslow` is the triviality
`Ψ_N ≤ N^ε Ψ_N` and nothing about `L^max` is used.  The only place `η_{t_N}` appears is in the
Hölder constant of `ξ`, through the hypothesis `hKbig`
(`η_{t_N}^{-2}(N+1) ≤ N^K` with `K` free) — a one-sided, purely deterministic requirement that
says `η_{t_N}` is bounded below by a power of `N`, which is the standing regime of §4
(`W ℓ_u η_u ≥ 1`).  In particular no two-sided comparison of random controls is taken.

Likewise there is **no indicator discontinuity** to relax here, so T116's `netLift_of_relaxed`
is not needed: `RBM.GoodEvent` is the *closed* condition `‖G - m‖_max ≤ δ_N`, and the margin
`N^τ Ψ_N ≤ δ_N` absorbs the net error, which the engine hides inside `RBM.StochDom`.

## Main definitions

* `RBM.Gauss.LocalLawUnifIcc` — the weak local law `‖G_u - m‖_max ≺ Ψ` at each fixed
  `u ∈ [s_N, t_N]`, with constants uniform in `u`; the (2.74)/(2.75) input.

## Main results

* `RBM.Gauss.abs_norm_green_flow_entry_sub_le` — the Hölder-`1/2` modulus in the time of one
  entry of `‖G_u - m‖`.
* `RBM.Gauss.stochDom_timeIcc_localLaw` — the weak local law with the time **inside** the
  index set of `≺`, i.e. the union over `u` moved inside the probability.
* `RBM.Gauss.highProb_goodSetFlow_of_localLaw` — **the `u`-uniform `hΩ`**: the good event (4.1)
  holds at every `u ∈ [s_N, t_N]` with high probability.  This fills the `hΩ` slot of
  `RBM.Gauss.eq45Flow_of_unifDom` and of the three producers
  `RBM.Gauss.ibpFlow_of_unifDom` / `flucRowFlow_of_unifDom` / `flucBlkFlow_of_unifDom`.
-/

namespace RBM.Gauss

open MeasureTheory Filter Matrix

open scoped Matrix.Norms.L2Operator

/-! ### The modulus in the time of one entry of `G_u - m` -/

/-- **One entry of `‖G_u - m‖` is Hölder-`1/2` in the time.**  This is T106's
`RBM.Gauss.norm_green_flow_sub_le` (through its `√` form
`RBM.Gauss.norm_green_flow_sub_le_sqrt`) composed with `‖·‖` at a fixed entry: the constant
`η_t^{-2}(‖X‖+1)` is random but pathwise finite, and the event `‖X‖ ≤ N` (high probability by
`‖X‖ ≺ 1`, T109) makes it deterministic. -/
theorem abs_norm_green_flow_entry_sub_le (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {s t : ℝ}
    (hs0 : 0 ≤ s) (ht1 : t < 1) (ω : Ω d) (i j : d.Idx N) {u v : ℝ}
    (hu : u ∈ Set.Icc s t) (hv : v ∈ Set.Icc s t) :
    |‖green (Hflow d N u ω) (zt E u) i j - (if i = j then mE E else 0)‖
        - ‖green (Hflow d N v ω) (zt E v) i j - (if i = j then mE E else 0)‖|
      ≤ ((etaT E t)⁻¹ * (etaT E t)⁻¹ * (‖Xmat d N ω‖ + 1)) * Real.sqrt |u - v| := by
  refine le_trans ?_ (norm_green_flow_sub_le_sqrt d N hE hs0 ht1 ω hu hv)
  calc |‖green (Hflow d N u ω) (zt E u) i j - (if i = j then mE E else 0)‖
          - ‖green (Hflow d N v ω) (zt E v) i j - (if i = j then mE E else 0)‖|
      ≤ ‖(green (Hflow d N u ω) (zt E u) i j - (if i = j then mE E else 0))
          - (green (Hflow d N v ω) (zt E v) i j - (if i = j then mE E else 0))‖ :=
        abs_norm_sub_norm_le _ _
    _ = ‖(green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)) i j‖ := by
        rw [Matrix.sub_apply]; congr 1; ring
    _ ≤ ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N v ω) (zt E v)‖ :=
        norm_apply_le_l2_opNorm _ _ _

/-! ### The weak local law along the flow, and the flow good event -/

/-- **The weak local law at each fixed time of the flow, uniformly in the time.**

`‖(G_u - m)_{xy}‖ ≺ Ψ_N` for every `u ∈ [s_N, t_N]` and every pair of indices, with the
constants of Definition 2.1 (i) **not** depending on `u`.  This is what (2.74)/(2.75) of
Steps 1/2 deliver; the union over `u` is *outside* the probability, which is why the net
argument of `RBM.Gauss.stochDom_timeIcc_localLaw` is needed to reach
`RBM.Gauss.goodSetFlow`. -/
abbrev LocalLawUnifIcc (d : Dims) (E : ℝ) (s t Ψ : ℕ → ℝ) : Prop :=
  UnifDomIcc (P d) s t
    (fun N u (ij : d.Idx N × d.Idx N) ω =>
      ‖green (Hflow d N u ω) (zt E u) ij.1 ij.2 - (if ij.1 = ij.2 then mE E else 0)‖)
    (fun N _ _ _ => Ψ N)

variable {d : Dims} {E : ℝ} {s t δ Ψ : ℕ → ℝ} {K B : ℝ}

/-- **The weak local law with the time inside the index set of `≺`.**

The union over `u ∈ [s_N, t_N]` moves inside the probability.  This is T124's net engine
`RBM.Gauss.stochDom_timeIcc_of_unifDom` at `γ = 1/2` (the Hölder exponent of the flow),
`T = 1` (the flow interval sits in `[0,1]`), `Ξ = {‖X‖ ≤ N}` (T109) and the **deterministic,
time-independent** control `Ψ_N`, so the engine's `hslow` is trivial and nothing is compared
to `L^max`.

`hKbig` is the only regime hypothesis: the Hölder constant `η_{t_N}^{-2}(N+1)` of
`RBM.Gauss.abs_norm_green_flow_entry_sub_le` must be at most `N^K`.  `K` is free, so this only
asks that `η_{t_N}` be polynomially bounded below.  `hΨlow` asks the same of `Ψ_N`. -/
theorem stochDom_timeIcc_localLaw (d : Dims) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hKbig : ∀ᶠ N : ℕ in atTop,
      (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ * ((N : ℝ) + 1) ≤ (N : ℝ) ^ K)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N)
    (hll : LocalLawUnifIcc d E s t Ψ) :
    StochDom (P d) (U := fun N => RBM.TimeIcc s t N × (d.Idx N × d.Idx N))
      (fun N p ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2.1 p.2.2
        - (if p.2.1 = p.2.2 then mE E else 0)‖)
      (fun N _ _ => Ψ N) := by
  refine stochDom_timeIcc_of_unifDom (card_Idx_prod_le d) hst one_pos ?_ hK hB
    (by norm_num : (0:ℝ) < (1:ℝ)/2) (fun N _ _ _ => hΨ0 N)
    (δ := fun N => 1 / (N : ℝ) ^ ((K + B + 1) / ((1 : ℝ) / 2)))
    (Eventually.of_forall fun _ => le_rfl) (highProb_norm_Xmat_le d) ?_ ?_ ?_ hll
  · intro N
    have h1 := hs0 N
    have h2 := (ht1 N).le
    linarith
  · filter_upwards [hKbig] with N hKN ω hω ij u hu v hv
    have hX : ‖Xmat d N ω‖ ≤ (N : ℝ) := hω
    have hmod := abs_norm_green_flow_entry_sub_le d N hE (hs0 N) (ht1 N) ω ij.1 ij.2 hu hv
    have hsq : Real.sqrt |u - v| = |u - v| ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have hsq0 : (0 : ℝ) ≤ |u - v| ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (abs_nonneg _) _
    have hηt : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
    have hη0 : (0 : ℝ) < (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ := by positivity
    have hstep : (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ * (‖Xmat d N ω‖ + 1)
        ≤ (N : ℝ) ^ K := by
      refine le_trans ?_ hKN
      have : ‖Xmat d N ω‖ + 1 ≤ (N : ℝ) + 1 := by linarith
      nlinarith
    rw [hsq] at hmod
    calc |‖green (Hflow d N u ω) (zt E u) ij.1 ij.2 - (if ij.1 = ij.2 then mE E else 0)‖
            - ‖green (Hflow d N v ω) (zt E v) ij.1 ij.2 - (if ij.1 = ij.2 then mE E else 0)‖|
        ≤ ((etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ * (‖Xmat d N ω‖ + 1))
            * |u - v| ^ ((1 : ℝ) / 2) := hmod
      _ ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2) := by gcongr
  · filter_upwards [hΨlow] with N hN _ _ _ _ _
    exact hN
  · intro ε hε
    filter_upwards [eventually_le_rpow 1 hε] with N hN _ _ _ _ _ _ _ _
    nlinarith [hΨ0 N]

/-- **The `u`-uniform `hΩ`: the good event (4.1) at every time of the flow.**

This is T124's remaining input (1) and the `u`-uniform version of the `hΩ` that T119 leaves
open.  The fixed-time bridge is `RBM.Gauss.highProb_goodSet_of_stochDom`; here the same margin
hypothesis `∀ᶠ N, N^τ Ψ_N ≤ δ_N` is applied to `RBM.Gauss.stochDom_timeIcc_localLaw`, whose
index set already carries the time — so the resulting high-probability event controls **every**
`u ∈ [s_N, t_N]` at once.

The weak local law `hll` is the input of Steps 1/2 ((2.74)/(2.75)) and is not proved here. -/
theorem highProb_goodSetFlow_of_localLaw (d : Dims) {τ : ℝ} (hτ : 0 < τ) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hKbig : ∀ᶠ N : ℕ in atTop,
      (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ * ((N : ℝ) + 1) ≤ (N : ℝ) ^ K)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N)
    (hll : LocalLawUnifIcc d E s t Ψ)
    (hmargin : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ τ * Ψ N ≤ δ N) :
    HighProb (P d) (goodSetFlow d E s t δ) := by
  refine ((stochDom_timeIcc_localLaw d hE hs0 ht1 hst hK hB hKbig hΨ0 hΨlow hll).highProb
    hτ).mono ?_
  filter_upwards [hmargin] with N hN ω hω u hu x y
  exact (hω (⟨u, hu⟩, (x, y))).trans hN

end RBM.Gauss
