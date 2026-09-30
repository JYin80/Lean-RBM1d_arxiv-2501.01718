/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6EnvWindow
import RBM1D.EnergyN.Gauss.Step6EnvWindow
import RBM1D.EnergyN.Unif.Gauss.Step6EnvWindow
import RBM1D.EnergyN.Gauss.Step6Hyp
import RBM1D.EnergyN.Gauss.Step6Sample
import RBM1D.EnergyN.Flow.Hypotheses

/-!
# Step 6, the window theorems, envelope and step, at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8, (5.126)–(5.136), and §2.7, (2.71), (2.80).

Six statements of Step 6 at an `N`-dependent energy `E : ℕ → ℝ`: the envelope on the window
(`RBM.exists_env_windowN`), a polynomial bound on `lkPath` (`RBM.exists_norm_lkPath_le_rpowN`),
the decay of the kernels `K` (`RBM.loopDecay_Kval_quantN`), `Ξ^{(L-K)} ≤ N^τ` with high
probability (`RBM.highProb_flowXiLK_leN`), and the (2.71) half of the induction step
(`RBM.bounds_step_of_step6_windowN`) with its Gaussian-model form
(`RBM.Gauss.bounds_step_gauss_windowN`).

## The external `κ`

`RBM.exists_env_windowN` and `RBM.exists_norm_lkPath_le_rpowN` need a kernel constant `C` (loop
lengths `1, 2, 3`). They take `C` from `RBM.exists_norm_Kval_le_envFloor_unif`
(`∃ C, 0 ≤ C ∧ ∀ E, |E| ≤ 2 - κ → …`, `EnergyN/Unif/Gauss/Step6EnvWindow.lean`), obtained once
before `N` and instantiated at `E N` via `hEκ N` at the one call site each, as
`RBM.unifDetDom_driftEG'N` does.

## The diagonal hypotheses of `bounds_step_of_step6_windowN`/`bounds_step_gauss_windowN`

Both use `RBM.sharpExpect_step6_driftEG'N`, whose hierarchy hypotheses
`hcont`/`hintL2`/`hintQ`/`hintG`/`hEL`/`hintU1`/`hintU2` carry the diagonal shape (an extra outer
`∀ N₀` binder with `E N₀` in place of `E`) of `RBM.hierarchyN_driftSplit`. So the same diagonal
shape is required here: `bounds_step_of_step6_windowN` takes `hcont`/`hintU1`/`hintU2` (the
hypotheses with no producer) as diagonal hypotheses directly, and `bounds_step_gauss_windowN`
lifts the fixed-energy Gaussian producers `hintL2_gauss`/`hintQ_gauss`/`hintG_gauss`/`hEL_gauss`
to the diagonal shape by applying them at each `E N₀`. This shape comes from the diagonal helper;
it is not an added mathematical hypothesis (at a constant energy sequence it is the fixed-`E`
shape).
-/

open MeasureTheory Filter

namespace RBM

section EnvWindowN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **A polynomially bounded envelope on the window**: there are `Env ≥ 0` and `Kenv ≥ 0` with
`Env N ≤ N^{Kenv}` eventually that bound `primBil` of `lkPath` with itself, `Decay.eG` of
`lkPath` and `gloop`, and `Decay.eG` of `lkPath` with itself, at all times of the window. The
kernel constant `C` (loop lengths `1, 2, 3`) is obtained once, uniformly in `κ`, from
`RBM.exists_norm_Kval_le_envFloor_unif` (module docstring). -/
theorem exists_env_windowN (X : Sample B) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT (E N) (t N)) :
    ∃ (Env : ℕ → ℝ) (Kenv : ℝ), 0 ≤ Kenv ∧ (∀ N, 0 ≤ Env N) ∧
      (∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv) ∧
      (∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖primBil (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω) (lkPath X (E N) N (v : ℝ) ω)
          (LoopData.idx (σ, a))‖ ≤ Env N) ∧
      (∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
          (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt (E N) (v : ℝ)))
          (LoopData.idx (σ, a))‖ ≤ Env N) ∧
      (∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω) (lkPath X (E N) N (v : ℝ) ω)
          (LoopData.idx (σ, a))‖ ≤ Env N) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_Kval_le_envFloor_unif B hκ0 hκ1 hs0 ht1
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [abs_nonneg (E N), hEκ N]
  -- the pointwise loop envelope `M N = (1 + C) R_N^3`
  have hM0 : ∀ N : ℕ, 0 ≤ (1 + C) * envFloor (E N) t N ^ 3 := fun N => by
    have := pow_nonneg (envFloor_nonneg (E N) t N) 3; nlinarith
  have hgl : ∀ (N : ℕ) (v : TimeIcc s t N) (ω : Ω) (J : LoopIdx (ZMod (B.L N))),
      J.WF → 1 ≤ J.length → J.length ≤ 3 →
      ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt (E N) (v : ℝ)) J‖
        ≤ (1 + C) * envFloor (E N) t N ^ 3 := by
    intro N v ω J hJ hn h3
    refine (norm_gloop_flow_le_envFloor X (hE N) ht1 N v ω J hJ hn h3).trans ?_
    have := pow_nonneg (envFloor_nonneg (E N) t N) 3
    nlinarith
  have hlk : ∀ (N : ℕ) (v : TimeIcc s t N) (ω : Ω) (J : LoopIdx (ZMod (B.L N))),
      J.WF → 1 ≤ J.length → J.length ≤ 3 →
      ‖lkPath X (E N) N (v : ℝ) ω J‖ ≤ (1 + C) * envFloor (E N) t N ^ 3 := by
    intro N v ω J hJ hn h3
    have h1 := norm_gloop_flow_le_envFloor X (hE N) ht1 N v ω J hJ hn h3
    have h2 := hC (E N) (hEκ N) N v J hJ hn h3
    calc ‖lkPath X (E N) N (v : ℝ) ω J‖
        = ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt (E N) (v : ℝ)) J
            - B.Kval (E N) N (v : ℝ) J‖ := rfl
      _ ≤ ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt (E N) (v : ℝ)) J‖
            + ‖B.Kval (E N) N (v : ℝ) J‖ := norm_sub_le _ _
      _ ≤ envFloor (E N) t N ^ 3 + C * envFloor (E N) t N ^ 3 := add_le_add h1 h2
      _ = (1 + C) * envFloor (E N) t N ^ 3 := by ring
  refine ⟨fun N => 4 * (B.W N : ℝ) * (B.L N : ℝ) * ((1 + C) * envFloor (E N) t N ^ 3) ^ 2,
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
    have hηt : 0 < etaT (E N) (t N) := etaT_pos (hE N) (ht1 N)
    have hRA : envFloor (E N) t N ≤ A := by
      refine max_le hA1 ?_
      have hpos : (0 : ℝ) < (N : ℝ) ^ (-c) := Real.rpow_pos_of_pos hN0 _
      have := inv_anti₀ hpos hηN
      rwa [Real.rpow_neg hN0.le, inv_inv] at this
    have hR0 : 0 ≤ envFloor (E N) t N := envFloor_nonneg (E N) t N
    have hA0 : (0 : ℝ) ≤ A := by linarith
    have h3 : envFloor (E N) t N ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ hR0 hRA 3
    have hA30 : (0 : ℝ) ≤ A ^ 3 := by positivity
    have hMA : (1 + C) * envFloor (E N) t N ^ 3 ≤ (1 + C) * A ^ 3 := by nlinarith
    have hMsq : ((1 + C) * envFloor (E N) t N ^ 3) ^ 2 ≤ ((1 + C) * A ^ 3) ^ 2 :=
      pow_le_pow_left₀ (hM0 N) hMA 2
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by
      have : ((B.W N * B.L N : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hdimN.1
      push_cast at this; linarith
    have hA6 : A ^ 6 = (N : ℝ) ^ (6 * c) := by
      rw [hAdef, ← Real.rpow_natCast ((N : ℝ) ^ c) 6, ← Real.rpow_mul hN0.le]
      norm_num [mul_comm]
    have hstep : 4 * (B.W N : ℝ) * (B.L N : ℝ) * ((1 + C) * envFloor (E N) t N ^ 3) ^ 2
        ≤ 4 * (1 + C) ^ 2 * ((N : ℝ) * A ^ 6) := by
      have hWL0 : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) :=
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hsq0 : (0 : ℝ) ≤ ((1 + C) * A ^ 3) ^ 2 := by positivity
      calc 4 * (B.W N : ℝ) * (B.L N : ℝ) * ((1 + C) * envFloor (E N) t N ^ 3) ^ 2
          = 4 * ((B.W N : ℝ) * (B.L N : ℝ)) * ((1 + C) * envFloor (E N) t N ^ 3) ^ 2 := by ring
        _ ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ)) * ((1 + C) * A ^ 3) ^ 2 := by nlinarith
        _ ≤ 4 * (N : ℝ) * ((1 + C) * A ^ 3) ^ 2 := by nlinarith
        _ = 4 * (1 + C) ^ 2 * ((N : ℝ) * A ^ 6) := by ring
    refine hstep.trans ?_
    have hprod : (N : ℝ) * A ^ 6 = (N : ℝ) ^ (1 + 6 * c) := by
      rw [hA6, Real.rpow_add hN0, Real.rpow_one]
    rw [hprod]
    exact hfinN
  · -- the envelope of `primBil` of `lkPath` with itself
    intro N v σ a ω
    have hlen2 : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length = 2 := by
      show (List.ofFn a).length = 2
      rw [List.length_ofFn]
    have hK : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length →
        J.length ≤ (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length →
        ‖lkPath X (E N) N (v : ℝ) ω J‖ ≤ (1 + C) * envFloor (E N) t N ^ 3 := by
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
  · -- the envelope of `Decay.eG` of `lkPath` and `gloop`
    intro N v σ a ω
    have hlen2 : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length = 2 := by
      show (List.ofFn a).length = 2
      rw [List.length_ofFn]
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖lkPath X (E N) N (v : ℝ) ω ⟨[b], [x]⟩‖ ≤ (1 + C) * envFloor (E N) t N ^ 3 :=
      fun b x => hlk N v ω ⟨[b], [x]⟩ rfl le_rfl (by show (1 : ℕ) ≤ 3; norm_num)
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
        J.length = (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length + 1 →
        ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt (E N) (v : ℝ)) J‖
          ≤ (1 + C) * envFloor (E N) t N ^ 3 := by
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
  · -- the envelope of `Decay.eG` of `lkPath` with itself
    intro N v σ a ω
    have hlen2 : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length = 2 := by
      show (List.ofFn a).length = 2
      rw [List.length_ofFn]
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖lkPath X (E N) N (v : ℝ) ω ⟨[b], [x]⟩‖ ≤ (1 + C) * envFloor (E N) t N ^ 3 :=
      fun b x => hlk N v ω ⟨[b], [x]⟩ rfl le_rfl (by show (1 : ℕ) ≤ 3; norm_num)
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
        J.length = (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length + 1 →
        ‖lkPath X (E N) N (v : ℝ) ω J‖ ≤ (1 + C) * envFloor (E N) t N ^ 3 := by
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

end EnvWindowN

section LkRpowN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`‖lkPath‖ ≤ N^{KM}` eventually**, for some `KM ≥ 0`, at all times of the window and loops of
length at most 2. The kernel constant `C` is obtained once, uniformly in `κ`, from
`RBM.exists_norm_Kval_le_envFloor_unif` (module docstring). -/
theorem exists_norm_lkPath_le_rpowN (X : Sample B) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT (E N) (t N)) :
    ∃ KM : ℝ, 0 ≤ KM ∧ ∀ᶠ N : ℕ in atTop, ∀ (v : TimeIcc s t N) (ω : Ω)
      (J : LoopIdx (ZMod (B.L N))), J.WF → J.length ≤ 2 →
        ‖lkPath X (E N) N (v : ℝ) ω J‖ ≤ (N : ℝ) ^ KM := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [abs_nonneg (E N), hEκ N]
  obtain ⟨C, hC0, hC⟩ := exists_norm_Kval_le_envFloor_unif B hκ0 hκ1 hs0 ht1
  refine ⟨2 + 3 * c, by linarith, ?_⟩
  filter_upwards [hη, B.dim, eventually_ge_atTop 1,
    SumZeroDyn.eventually_const_mul_rpow_le (2 + C)
      (show 1 + 3 * c < 2 + 3 * c by linarith)] with N hηN hdimN hN1 hfinN
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set A : ℝ := (N : ℝ) ^ c with hAdef
  have hA1 : (1 : ℝ) ≤ A := Real.one_le_rpow hN1' hc0
  have hηt : 0 < etaT (E N) (t N) := etaT_pos (hE N) (ht1 N)
  have hRA : envFloor (E N) t N ≤ A := by
    refine max_le hA1 ?_
    have hpos : (0 : ℝ) < (N : ℝ) ^ (-c) := Real.rpow_pos_of_pos hN0 _
    have := inv_anti₀ hpos hηN
    rwa [Real.rpow_neg hN0.le, inv_inv] at this
  have hR0 : 0 ≤ envFloor (E N) t N := envFloor_nonneg (E N) t N
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hA3 : A ^ 3 = (N : ℝ) ^ (3 * c) := by
    rw [hAdef, ← Real.rpow_natCast ((N : ℝ) ^ c) 3, ← Real.rpow_mul hN0.le]
    norm_num; ring_nf
  have hcube : envFloor (E N) t N ^ 3 ≤ (N : ℝ) ^ (1 + 3 * c) := by
    refine le_trans (pow_le_pow_left₀ hR0 hRA 3) ?_
    rw [hA3]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hLW : ((B.L N * B.W N : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 + 3 * c) := by
    have h1 : ((B.L N * B.W N : ℕ) : ℝ) ≤ (N : ℝ) := by
      have h0 : B.W N * B.L N ≤ N := hdimN.1
      have h1 : B.L N * B.W N ≤ N := by rw [Nat.mul_comm]; exact h0
      exact_mod_cast h1
    refine h1.trans ?_
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (1 + 3 * c) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  intro v ω J hJ h2
  have hbound : ‖lkPath X (E N) N (v : ℝ) ω J‖ ≤ (2 + C) * (N : ℝ) ^ (1 + 3 * c) := by
    rcases Nat.eq_zero_or_pos J.length with h0 | h1
    · rw [loopIdx_eq_nil hJ h0, lkPath_nil]
      rw [Complex.norm_natCast]
      nlinarith [Real.rpow_nonneg hN0.le (1 + 3 * c)]
    · have hg := norm_gloop_flow_le_envFloor X (hE N) ht1 N v ω J hJ h1 (by omega)
      have hk := hC (E N) (hEκ N) N v J hJ h1 (by omega)
      have hsum : ‖lkPath X (E N) N (v : ℝ) ω J‖ ≤ envFloor (E N) t N ^ 3
          + C * envFloor (E N) t N ^ 3 :=
        le_trans (norm_sub_le _ _) (add_le_add hg hk)
      nlinarith [Real.rpow_nonneg hN0.le (1 + 3 * c)]
  exact hbound.trans hfinN

end LkRpowN

section KQuantN

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The kernels `K` of length `m` have the decay `LoopDecay` at scale `ℓ_v N^τ` with error
`N^{-D}`**, eventually, at all times of the window. No energy-dependent constant is fixed here:
deterministic and unconditional, at the general loop length `m`. -/
theorem loopDecay_Kval_quantN (B : Band Ω) {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (m : ℕ) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) m (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval (E N) N (v : ℝ)) := by
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
    have hm1 : ∀ σ, ‖mSigma (E N) σ‖ ≤ 1 := fun σ => le_of_eq (norm_mSigma (hE N) σ)
    have hgap : ∀ σ σ', 1 - uu ≤ ‖1 - (uu : ℂ) * (mSigma (E N) σ * mSigma (E N) σ')‖ := by
      intro σ σ'
      refine one_sub_le_norm_one_sub_mul hu0 ?_
      rw [norm_mul, norm_mSigma (hE N), norm_mSigma (hE N), mul_one]
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

end KQuantN

section GoodSetsN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`Ξ^{(L-K)}_m ≺ 1` gives `X.xiLK ≤ N^τ` on the window with high probability.** No
energy-dependent constant is fixed here (with `RBM.Step3.flowXiLK` eta-expanded, as in
`RBM.StepGlue.stochDom_flowXiLKN`). -/
theorem highProb_flowXiLK_leN (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ} {m : ℕ}
    (h : StochDom B.P (fun N u ω => Step3.flowXiLK X (E N) s t m N u ω) fun _ _ _ => (1 : ℝ))
    {τ : ℝ} (hτ : 0 < τ) :
    HighProb B.P (fun N =>
      {ω | ∀ u : TimeIcc s t N, X.xiLK (E N) N (u : ℝ) ω m ≤ (N : ℝ) ^ τ}) := by
  intro D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine le_trans (measure_mono ?_) hN
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, by simpa only [Step3.flowXiLK, mul_one] using hu⟩

end GoodSetsN

section StepN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The (2.71) half of the induction step**: `BoundsN` at `t`. Assembled from
`RBM.sharpExpect_step6_driftEG'N` and `RBM.bounds_of_boundsCore_of_sharpExpectN`. The hierarchy
hypotheses `hcont`, `hintL2`, `hintQ`, `hintG`, `hEL`, `hintU1`, `hintU2` carry the diagonal
binder `∀ N₀` that `RBM.sharpExpect_step6_driftEG'N` requires (module docstring). -/
theorem bounds_step_of_step6_windowN (X : Sample B) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t)
    (hcont : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT X (E N₀) N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintL2 : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => X.Lval (E N₀) N v ω (LoopData.idx (σ, b))) B.P)
    (hintQ : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => primBil (B.L N) (B.W N) (lkPath X (E N₀) N v ω)
        (lkPath X (E N₀) N v ω) (LoopData.idx (σ, b))) B.P)
    (hintG : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N₀) N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt (E N₀) v)) (LoopData.idx (σ, b))) B.P)
    (hEL : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      HasDerivAt (fun q : ℝ => X.ELval (E N₀) N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma (E N₀)) (X.H N v ω) (zt (E N₀) v)
            (LoopData.idx (σ, b))
          + primRhs (B.L N) (B.W N) (X.Lval (E N₀) N v ω) (LoopData.idx (σ, b))) ∂B.P) v)
    (hintU1 : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma (E N₀)) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK X (E N₀) N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma (E N₀)) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG X (E N₀) N v σ) a) volume (s N) (u : ℝ))
    {Env : ℕ → ℝ} {Kenv KM : ℝ}
    (hmeasQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (lkPath X (E N) N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (hmeasG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt (E N) (v : ℝ))) (LoopData.idx (σ, a))) B.P)
    (hmeasLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (lkPath X (E N) N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (henvQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω) (lkPath X (E N) N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (henvG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt (E N) (v : ℝ))) (LoopData.idx (σ, a))‖
        ≤ Env N)
    (henvLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω) (lkPath X (E N) N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv) (hKM : 0 ≤ KM)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X (E N) N (s N) σ))
    (hin59 : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X (E N) s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D))
    (hinQ : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X (E N) s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hinG : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X (E N) s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval (E N) N (v : ℝ)))
    (h527 : Step6.Eq527N X E s t)
    (hq11 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖Step6.quad11 X (E N) N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale (E N) N p.1)⁻¹ ^ 2))
    (hintL1 : ∀ (N : ℕ) (v : TimeIcc s t N) (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => X.Lval (E N) N (v : ℝ) ω ⟨[b], [x]⟩) B.P)
    (hBC : BoundsCoreN X E t) (hB : BoundsN X E s) :
    BoundsN X E t :=
  bounds_of_boundsCore_of_sharpExpectN hBC
    (sharpExpect_step6_driftEG'N X hκ0 hκ1 hEκ hs0 hst ht1 hc hcont hintL2 hintQ hintG hEL
      hintU1 hintU2 hmeasQ hmeasG hmeasLK henvQ henvG henvLK hEnv0 hKenv hKM hEnvpoly
      hlk hin59 hinQ hinG hKd hB.expect h527 hq11 hintL1) hst

end StepN

end RBM

namespace RBM.Gauss

open RBM

/-- **The (2.71) half of the induction step for the Gaussian model.** Every hypothesis of
`RBM.bounds_step_of_step6_windowN` with a Gaussian producer is discharged: `henvQ`/`henvG`/`henvLK`
from `RBM.exists_env_windowN`, `h527` from `RBM.Gauss.eq527N_gauss`, `hq11` from
`RBM.Gauss.quad11_unifDetDom_gauss'N`, and `hintL2`/`hintQ`/`hintG`/`hEL`/`hmeasQ`/`hmeasG`/
`hmeasLK`/`hintL1` from the fixed-energy Gaussian producers, applied at each `E N` (diagonally at
`E N₀` where the hierarchy hypothesis demands it, module docstring). What remains as hypotheses
is `hcont`, `hintU1`, `hintU2`, `hlk`, `hin59`, `hinQ`, `hinG`, `hKd`, `hlmk`, `hc`, `hBC`,
`hB`. -/
theorem bounds_step_gauss_windowN (d : Dims) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272N (band d) E s t)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT (E N) u)
    (hcont : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT (sample d) (E N₀) N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintU1 : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma (E N₀)) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK (sample d) (E N₀) N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma (E N₀)) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG (sample d) (E N₀) N v σ) a) volume (s N) (u : ℝ))
    {KM : ℝ} (hKM : 0 ≤ KM)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay ((band d).L N) ((band d).ell N (s N) * ((band d).W N : ℝ) ^ τ)
        (((band d).W N : ℝ) ^ (-D)) (Step6.lkT (sample d) (E N) N (s N) σ))
    (hin59 : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ((band d).P (FDInputs (sample d) (E N) s t N (((band d).W N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        ((N : ℝ) ^ KM))ᶜ).toReal ≤ (N : ℝ) ^ (-D))
    (hinQ : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb (band d).P (fun N =>
      QuadInputs (sample d) (E N) s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hinG : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb (band d).P (fun N =>
      EGInputs (sample d) (E N) s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay ((band d).L N) 3 ((band d).ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        ((band d).Kval (E N) N (v : ℝ)))
    (hlmk : SharpLmKFlowN (sample d) E s t)
    (hBC : BoundsCoreN (sample d) E t) (hB : BoundsN (sample d) E s) :
    BoundsN (sample d) E t := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [abs_nonneg (E N), hEκ N]
  have hηt : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT (E N) (t N) := by
    filter_upwards [hη] with N hN
    exact hN ⟨t N, hst N, le_rfl⟩
  obtain ⟨Env, Kenv, hKenv, hEnv0, hEnvpoly, henvQ, henvG, henvLK⟩ :=
    exists_env_windowN (sample d) hκ0 hκ1 hEκ hs0 ht1 hc0 hηt
  exact bounds_step_of_step6_windowN (sample d) hκ0 hκ1 hEκ hs0 hst ht1 hc
    hcont (fun N₀ => hintL2_gauss d (hE N₀)) (fun N₀ => hintQ_gauss d hκ0 hκ1 (hEκ N₀))
    (fun N₀ => hintG_gauss d hκ0 hκ1 (hEκ N₀)) (fun N₀ => hEL_gauss d (hE N₀)) hintU1 hintU2
    (fun N v σ a => hmeasQ_window d (hE N) ht1 N v σ a)
    (fun N v σ a => hmeasG_window d (hE N) ht1 N v σ a)
    (fun N v σ a => hmeasLK_window d (hE N) ht1 N v σ a)
    henvQ henvG henvLK hEnv0 hKenv hKM hEnvpoly
    hlk hin59 hinQ hinG hKd
    (eq527N_gauss d hE hs0 ht1)
    (quad11_unifDetDom_gauss'N d hκ0 hκ1 hEκ hs0 ht1 hc0 hη hlmk)
    (fun N v b x => hintL1_window d (hE N) ht1 N v b x) hBC hB

end RBM.Gauss
