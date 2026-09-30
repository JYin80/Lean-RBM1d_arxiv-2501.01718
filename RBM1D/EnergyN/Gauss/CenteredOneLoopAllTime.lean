/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CenteredOneLoopAllTime
import RBM1D.EnergyN.Gauss.CenteredOneLoopFixedTime
import RBM1D.EnergyN.Gauss.CenteredTraceModulus

/-!
# The centered one-loop trace on the whole time interval, at an `N`-dependent energy

Seven statements at an `N`-dependent energy `E : ℕ → ℝ` about the time functions `q`, `qExt`,
`control` and the centered block trace `CenteredTraceModulus.centeredTrace` on `[s, t]`. None of
them fixes a constant itself; `centeredTrace_unifDomIccN`,
`centeredTrace_twoCharge_stochDom_timeIccN` and `highProb_centeredEventN` use
`CenteredOneLoopFixedTime.centered_block_trace_stochDomN` and therefore take its external
`κ`/`hκ1`.

`eventually_qExt_short_time_comparableN` uses `Gauss.rpow_neg_one_le_one_sub_of_scale_geN`;
`eventually_inv_le_qN` uses only the generic (`E`-free) `Gauss.W_le_self`;
`eventually_control_lowerN` uses `eventually_inv_le_qN`; `centeredTrace_false_stochDom_of_trueN`
needs no bound on `E` at all (a pure conjugation identity).
`centeredTrace_twoCharge_stochDom_timeIccN` also uses
`CenteredTraceModulus.eventually_centeredTrace_sub_leN` and the generic (`E`-free)
`netNumerics`/`Gauss.stochDom_timeIcc_of_unifDom`. The energy-free helpers (`q_pos`, `q_eq_inv`,
`qExt_eq_q`, `qExt_eq_selectorQ`, `q_le_two_mul_of_abs_sub_le`, `Step1.inv_W_le_inv_scale`,
`Step1.one_le_ell_div`) are deterministic per fixed `(E, N)` and are called at `E N`;
`clampTime`, `q`, `qExt`, `control`, `meshSpacing`, `centeredEvent` are `def`s, used pointwise at
`E N`.
-/

namespace RBM.CenteredOneLoopAllTime

open Filter MeasureTheory Set Gauss

noncomputable section

/-- **`qExt` at nearby times is comparable**: eventually, for `u, v ∈ [s, t]` with
`|u - v| ≤ N^{-16}`, `qExt u ≤ 2 qExt v` and `qExt v ≤ 2 qExt u`. No energy-dependent constant is
fixed here. -/
theorem eventually_qExt_short_time_comparableN {d : Dims} {E : ℕ → ℝ} {c : ℝ}
    {s t : ℕ → ℝ} (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272NReg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N),
      |u - v| ≤ (N : ℝ) ^ (-16 : ℝ) →
      qExt d (E N) s t N u ≤ 2 * qExt d (E N) s t N v ∧
        qExt d (E N) s t N v ≤ 2 * qExt d (E N) s t N u := by
  have hfloor := Gauss.rpow_neg_one_le_one_sub_of_scale_geN (band d) hE ht1 hc hreg.2
  filter_upwards [hfloor, eventually_ge_atTop (1 : ℕ)] with N hfloorN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloorN' : (N : ℝ)⁻¹ ≤ 1 - t N := by
    simpa only [Real.rpow_neg_one] using hfloorN
  have hmesh : (N : ℝ) ^ (-16 : ℝ) ≤ (N : ℝ)⁻¹ := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hN1
      (by norm_num : (-16 : ℝ) ≤ -1)
    simpa only [Real.rpow_neg_one] using hpow
  intro u hu v hv hdist
  have hclose : |u - v| ≤ 1 - t N := hdist.trans (hmesh.trans hfloorN')
  have hforward := q_le_two_mul_of_abs_sub_le (d := d) (hE N) (hs0 N) (hst N) (ht1 N)
    hu hv hclose
  have hback := q_le_two_mul_of_abs_sub_le (d := d) (hE N) (hs0 N) (hst N) (ht1 N)
    hv hu (by simpa only [abs_sub_comm] using hclose)
  simpa only [qExt_eq_q hu, qExt_eq_q hv] using ⟨hforward, hback⟩

/-- **`N⁻¹ ≤ q u`** eventually, for all `u ∈ [s, t]`. No energy-dependent constant is fixed here:
it uses only the generic (`E`-free) `Gauss.W_le_self`. -/
theorem eventually_inv_le_qN {d : Dims} {E : ℕ → ℝ} {s t : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Icc (s N) (t N),
      (N : ℝ)⁻¹ ≤ q d (E N) s N u := by
  filter_upwards [Gauss.W_le_self d] with N hWN u hu
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hN : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (d.W_pos N) hWN)
  have hinv : (N : ℝ)⁻¹ ≤ (d.W N : ℝ)⁻¹ :=
    inv_anti₀ hW (by exact_mod_cast hWN)
  exact hinv.trans (W_inv_le_q (hE N) (hs0 N) (ht1 N) hu)

/-- **`N^{-1} ≤ control u b ω`** eventually, for all `u ∈ [s, t]`, `b` and `ω`. No
energy-dependent constant is fixed here: it uses `eventually_inv_le_qN`. -/
theorem eventually_control_lowerN {d : Dims} {E : ℕ → ℝ} {s t : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Ω d, ∀ b : ZMod (d.L N),
      ∀ u ∈ Icc (s N) (t N),
        (N : ℝ) ^ (-1 : ℝ) ≤ control d (E N) s t N u b ω := by
  filter_upwards [eventually_inv_le_qN hE hs0 ht1] with N hfloor ω b u hu
  rw [Real.rpow_neg_one, control, qExt_eq_q hu]
  have hq0 : 0 ≤ q d (E N) s N u :=
    (q_pos (hE N) (hs0 N) (hst N) (ht1 N) hu).le
  exact (hfloor u hu).trans (by nlinarith)

/-- **`‖centeredTrace u ω true b‖ ≤ 2 qExt u` uniformly on `[s, t]`** (`UnifDomIcc`), from
(2.68)–(2.70) at `s` and the hypotheses of Step 1. It takes the external `κ` of
`CenteredOneLoopFixedTime.centered_block_trace_stochDomN`. -/
theorem centeredTrace_unifDomIccN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s)
    (hStep : Step1.HypN (sample d) E s t) :
    UnifDomIcc (P d) s t
      (fun N u (b : ZMod (d.L N)) ω =>
        ‖CenteredTraceModulus.centeredTrace d (E N) N u ω true b‖)
      (fun N u (_b : ZMod (d.L N)) (_ω : Ω d) =>
        2 * qExt d (E N) s t N u) := by
  refine Gauss.unifDomIcc_of_forall_stochDom hst ?_
  intro u hu
  have hfixed := CenteredOneLoopFixedTime.centered_block_trace_stochDomN d
    hκ0 hκ1 hE hs0 hst ht1 hu hc hreg hB hStep
  have hcontrol : ∀ N,
      2 * SingletonLocalLaw.selectorQ d (E N) s u N =
        2 * qExt d (E N) s t N (u N) := by
    intro N
    rw [qExt_eq_selectorQ hu N]
  simpa only [CenteredTraceModulus.centeredTrace,
    Gsig_true, mSigma_true, hcontrol] using hfixed

/-- **The `false`-charge centered trace has the stochastic bound of the `true`-charge one.** No
energy-dependent constant is fixed here, and there is no bound on `E` at all: a pure conjugation
identity. -/
theorem centeredTrace_false_stochDom_of_trueN (d : Dims) {E : ℕ → ℝ}
    {s t : ℕ → ℝ}
    {control : ∀ N, (TimeIcc s t N × ZMod (d.L N)) → Ω d → ℝ}
    (hplus : StochDom (P d)
      (U := fun N => TimeIcc s t N × ZMod (d.L N))
      (fun N p ω =>
        ‖CenteredTraceModulus.centeredTrace
          d (E N) N (p.1 : ℝ) ω true p.2‖)
      control) :
    StochDom (P d)
      (U := fun N => TimeIcc s t N × ZMod (d.L N))
      (fun N p ω =>
        ‖CenteredTraceModulus.centeredTrace
          d (E N) N (p.1 : ℝ) ω false p.2‖)
      control := by
  exact StochDom.of_le_left
    (fun N p ω => by
      rw [CenteredTraceModulus.centeredTrace_false_eq_conj_true]
      simp)
    hplus

set_option maxHeartbeats 1000000 in
-- The generic fixed-selector, event, and net compositions exceed the default elaboration budget.
/-- **`‖centeredTrace u ω σ b‖ ≺ 2 qExt u` for both charges `σ`**, uniformly in `u ∈ [s, t]`
and `b`. It fixes no energy-dependent constant itself (it takes the external `κ` through
`centeredTrace_unifDomIccN`). -/
theorem centeredTrace_twoCharge_stochDom_timeIccN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ}
    {s t : ℕ → ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s)
    (hStep : Step1.HypN (sample d) E s t) :
    ∀ σ : Bool,
      StochDom (P d) (U := fun N => TimeIcc s t N × ZMod (d.L N))
        (fun N p ω =>
          ‖CenteredTraceModulus.centeredTrace
            d (E N) N (p.1 : ℝ) ω σ p.2‖)
        (fun N p _ω => 2 * qExt d (E N) s t N (p.1 : ℝ)) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  let ξ : ∀ N, ℝ → ZMod (d.L N) → Ω d → ℝ := fun N u b ω =>
    ‖CenteredTraceModulus.centeredTrace d (E N) N u ω true b‖
  let ζ : ∀ N, ℝ → ZMod (d.L N) → Ω d → ℝ := fun N u _b _ω =>
    2 * qExt d (E N) s t N u
  have hζ0 : ∀ N u b ω, 0 ≤ ζ N u b ω := by
    intro N u b ω
    exact mul_nonneg (by norm_num) (qExt_nonneg (hE2 N) hs0 hst ht1 N u)
  have hfix : UnifDomIcc (P d) s t ξ ζ := by
    simpa only [ξ, ζ] using
      centeredTrace_unifDomIccN d hκ0 hκ1 hE hs0 hst ht1 hc hreg hB hStep
  have hmod := CenteredTraceModulus.eventually_centeredTrace_sub_leN
    d hκ0 hE hs0 hst ht1 hc hreg
  have hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈
      CenteredTraceModulus.normGood d N,
        ∀ b : ZMod (d.L N), ∀ u ∈ Icc (s N) (t N),
          ∀ v ∈ Icc (s N) (t N),
            |ξ N u b ω - ξ N v b ω| ≤
              (N : ℝ) ^ (6 : ℝ) * |u - v| ^ ((1 : ℝ) / 2) := by
    filter_upwards [hmod, eventually_ge_atTop (2 : ℕ)] with N hNmod hN
    intro ω hω b u hu v hv
    have hcomplex := hNmod ω hω u hu v hv true b
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hcoef : 2 * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 6 := by
      calc
        2 * (N : ℝ) ^ 5 ≤ (N : ℝ) * (N : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right hNr (by positivity)
        _ = (N : ℝ) ^ 6 := by ring
    calc
      |ξ N u b ω - ξ N v b ω| ≤
          ‖CenteredTraceModulus.centeredTrace d (E N) N u ω true b -
            CenteredTraceModulus.centeredTrace d (E N) N v ω true b‖ :=
              abs_norm_sub_norm_le _ _
      _ ≤ 2 * (N : ℝ) ^ 5 * Real.sqrt |u - v| := hcomplex
      _ ≤ (N : ℝ) ^ 6 * Real.sqrt |u - v| :=
        mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
      _ = (N : ℝ) ^ (6 : ℝ) * |u - v| ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
        congr 1
        exact (Real.rpow_natCast (N : ℝ) 6).symm
  have hlow : ∀ᶠ N : ℕ in atTop, ∀ ω ∈
      CenteredTraceModulus.normGood d N,
        ∀ b : ZMod (d.L N), ∀ u ∈ Icc (s N) (t N),
          (N : ℝ) ^ (-1 : ℝ) ≤ ζ N u b ω := by
    filter_upwards [eventually_control_lowerN hE2 hs0 hst ht1] with N hN
    intro ω hω b u hu
    simpa only [ζ, control] using hN ω b u hu
  have hslow : ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ω ∈
      CenteredTraceModulus.normGood d N,
        ∀ b : ZMod (d.L N), ∀ u ∈ Icc (s N) (t N),
          ∀ v ∈ Icc (s N) (t N),
            |u - v| ≤ meshSpacing N →
              ζ N v b ω ≤ (N : ℝ) ^ ε * ζ N u b ω := by
    intro ε hε
    have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ ε :=
      ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
    filter_upwards [eventually_qExt_short_time_comparableN hE2 hs0 hst ht1 hc hreg,
      hlarge] with N hcomparison hlargeN ω hω b u hu v hv hdist
    have hq := (hcomparison u hu v hv (by simpa only [meshSpacing] using hdist)).2
    have htwo : ζ N v b ω ≤ 2 * ζ N u b ω := by
      dsimp [ζ]
      exact mul_le_mul_of_nonneg_left hq (by norm_num)
    exact htwo.trans
      (mul_le_mul_of_nonneg_right hlargeN (by
        exact mul_nonneg (by norm_num) (qExt_nonneg (hE2 N) hs0 hst ht1 N u)))
  have hnum := netNumerics d hs0 hst ht1
  have hall := Gauss.stochDom_timeIcc_of_unifDom
    (P := P d) (Cv := (1 : ℝ)) (T := (1 : ℝ))
    (K := (6 : ℝ)) (B := (1 : ℝ)) (γ := (1 : ℝ) / 2)
    (ξ := ξ) (ζ := ζ) (δ := meshSpacing)
    hnum.hcard hnum.hst hnum.hT hnum.hlen hnum.hK hnum.hB hnum.hγ hζ0
    (by simpa only [meshSpacing] using hnum.hδ)
    (CenteredTraceModulus.highProb_normGood d)
    hHol hlow hslow hfix
  have hplus : StochDom (P d)
      (U := fun N => TimeIcc s t N × ZMod (d.L N))
      (fun N p ω =>
        ‖CenteredTraceModulus.centeredTrace d (E N) N
            (p.1 : ℝ) ω true p.2‖)
      (fun N p _ω => 2 * qExt d (E N) s t N (p.1 : ℝ)) := by
    simpa only [ξ, ζ] using hall
  intro σ
  cases σ with
  | false => exact centeredTrace_false_stochDom_of_trueN d hplus
  | true => exact hplus

/-- **The event `centeredEvent` holds with high probability.** It takes the external `κ` through
`centeredTrace_twoCharge_stochDom_timeIccN`. -/
theorem highProb_centeredEventN (d : Dims) {E : ℕ → ℝ} {κ c ζ : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : 0 < c) (hζ : 0 < ζ)
    (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s)
    (hStep : Step1.HypN (sample d) E s t) :
    HighProb (P d) (fun N => centeredEvent d (E N) ζ s t N) := by
  have htwo := centeredTrace_twoCharge_stochDom_timeIccN d
    hκ0 hκ1 hE hs0 hst ht1 hc hreg hB hStep
  have hfalse := (htwo false).highProb hζ
  have htrue := (htwo true).highProb hζ
  refine (hfalse.inter htrue).mono ?_
  filter_upwards with N ω homega
  intro p σ
  cases σ with
  | false => exact homega.1 p
  | true => exact homega.2 p

section Compat

end Compat

end
end RBM.CenteredOneLoopAllTime
