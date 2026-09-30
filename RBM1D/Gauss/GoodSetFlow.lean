/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Eq45FlowInputs
import RBM1D.Gauss.Step1Hyp

/-!
# The weak local law along the flow: the modulus of one entry, and the fixed-time form

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 4.1 (4.1)/(4.4) and (2.74)/(2.75).

The good event of (4.1) is needed at **every** time `u ∈ [s_N, t_N]` simultaneously.  That puts
an uncountable intersection over `u` inside one event, so its complement is an uncountable union
and no fixed-time statement gives it by itself.  The shape of the argument is the standard one:

* the **fixed-time weak local law `‖G_u - m‖_max ≺ Ψ`, uniform in the time** —
  `RBM.Gauss.UnifDomIcc` for the entries of `G_u - m`, which Steps 1/2 ((2.74)/(2.75)) supply;
* the **deterministic modulus in the time** — `RBM.Gauss.abs_norm_green_flow_entry_sub_le`
  below, which is `RBM.Gauss.norm_green_flow_sub_le` read off one entry, with the
  Hölder-`1/2` constant `η_{t_N}^{-2}(‖X‖+1)`;
* the **union bound over the net**, which is the engine
  `RBM.Gauss.stochDom_timeIcc_of_unifDom` of `RBM1D/Gauss/Eq45FlowInputs.lean`; the random Hölder
  constant is made deterministic on `‖X‖ ≤ N`, which has high probability by `‖X‖ ≺ 1`
  (unconditional).

## The regime `t_N → 1`

Routing slow variation of the control through `L^max ≍ W^{-1}` costs `η^{-2}` in the upper half,
which stops being a `≺` as `t_N → 1`.  Here the issue **does not arise**: the control of the weak
local law is the *deterministic* `Ψ_N`, constant in `u`, so slow variation of the control is the
triviality `Ψ_N ≤ N^ε Ψ_N` and nothing about `L^max` is used.  The only place `η_{t_N}` appears
is in the Hölder constant, through a condition `η_{t_N}^{-2}(N+1) ≤ N^K` with `K` free — a
one-sided, purely deterministic requirement that says `η_{t_N}` is bounded below by a power of
`N`, which is the standing regime of §4 (`W ℓ_u η_u ≥ 1`).

Likewise there is **no indicator discontinuity** to relax here: `RBM.GoodEvent` is the *closed*
condition `‖G - m‖_max ≤ δ_N`, and the margin `N^τ Ψ_N ≤ δ_N` absorbs the net error.

## Main results

* `RBM.Gauss.abs_norm_green_flow_entry_sub_le` — the Hölder-`1/2` modulus in the time of one
  entry of `‖G_u - m‖`.
* `RBM.Gauss.unifDomIcc_of_stochDom_timeIcc` — a `≺` with the time inside the index set gives the
  fixed-time form `RBM.Gauss.UnifDomIcc`.
-/

namespace RBM.Gauss

open MeasureTheory Filter Matrix

open scoped Matrix.Norms.L2Operator

/-! ### The modulus in the time of one entry of `G_u - m` -/

/-- **One entry of `‖G_u - m‖` is Hölder-`1/2` in the time.**  This is
`RBM.Gauss.norm_green_flow_sub_le` (through its `√` form
`RBM.Gauss.norm_green_flow_sub_le_sqrt`) composed with `‖·‖` at a fixed entry: the constant
`η_t^{-2}(‖X‖+1)` is random but pathwise finite, and the event `‖X‖ ≤ N` (high probability by
`‖X‖ ≺ 1`) makes it deterministic. -/
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

variable {d : Dims} {E : ℝ} {s t δ Ψ : ℕ → ℝ} {K B : ℝ}

/-! ### The fixed-time weak local law from Step 2

The *fixed-time* weak local law with constants uniform in `u` has the union over `u` **outside**
the probability.  (2.75) of Step 2 is the **stronger** statement with the union *inside*, so the
implication below is the easy direction — one `MeasureTheory.measure_mono` — and the only other
ingredient is a time-*independent* majorant for the control `(W ℓ_u η_u)^{-1/2}`, which (2.72)
supplies through `RBM.Step3.Scales.le_A`.

This is the sense in which Steps 1/2 ((2.74)/(2.75)) supply the input. -/

/-- **A `≺` with the time inside the index set gives `RBM.Gauss.UnifDomIcc`.**

The failure event at one `u ∈ [s_N, t_N]` and one index `a` is contained in the failure event
of the union over `u` and `a`, so the same probability bound holds; the converse needs a net
(`RBM.Gauss.stochDom_timeIcc_of_unifDom`). -/
theorem unifDomIcc_of_stochDom_timeIcc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {V : ℕ → Type*} {s t : ℕ → ℝ} {ξ ζ : ∀ N, ℝ → V N → Ω → ℝ}
    (h : StochDom P (U := fun N => RBM.TimeIcc s t N × V N)
      (fun N p ω => ξ N (p.1 : ℝ) p.2 ω) (fun N p ω => ζ N (p.1 : ℝ) p.2 ω)) :
    UnifDomIcc P s t ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN u hu a
  refine le_trans (measure_mono ?_) hN
  intro ω hω
  exact ⟨(⟨u, hu⟩, a), hω⟩

end RBM.Gauss
