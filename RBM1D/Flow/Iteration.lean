/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Hypotheses
import RBM1D.Flow.Initial
import RBM1D.Flow.Scales

/-!
# Ingredients of the proof of Lemmas 2.18, 2.19, 2.20 from Theorem 2.21 (§2.7)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7, "Proof of Lemmas 2.18, 2.19,
and 2.20": starting from (2.67) at `t = 0`, apply Theorem 2.21 along the time grid
`1 - s_k = W^{-kτ'}`, `k = 0, …, n₀ - 1`.

The grid induction itself, at an `N`-dependent energy, is `RBM.boundsGrid_of_fields` of
`Flow/EnergyUniform.lean`.  This file proves the ingredients it uses at a fixed energy `E`.

## Main results

* `RBM.StochDom.congr_eventually`, `RBM.UnifDetDom.congr_eventually` — `≺` only depends on
  large `N`; `RBM.StochDom.of_eq_zero` — a family that vanishes is dominated.
* `RBM.Sample.lkErr_zero`, `RBM.Sample.llErr_zero`, `RBM.Sample.expErr_zero` — **(2.67)**: the
  errors of Lemmas 2.18–2.20 vanish at `t = 0` (`L_0 = K_0`, `G_0 = m`, `E L_0 = K_0`, from
  `Flow/Initial.lean`).
* `RBM.Band.eventually_L_le_W`, `RBM.Band.eventually_le_W`, `RBM.Band.eventually_rpow_WL_le` —
  the inputs of the time grid for the band model (`W ≥ N^{1/2+c}`, `WL ≍ N`).
* `RBM.Band.norm_Kval_le` — the primitive loop in the flow:
  `|K_{t,σ,a}| ≤ C (W ℓ_t η_t)^{-n+1}` for every `n ≥ 1` and `0 ≤ t < 1` ((2.59) for `n ≥ 3`,
  `RBM.Band.norm_Kval_two_le` for `n = 2`, `K = m` for `n = 1`).

## The induction

Since `≺` is a `Prop` (Definition 2.1: "for every `τ > 0`, `D > 0`, for `N ≥ N₀(τ, D)`"), the
"`N^ε` loss per application of Theorem 2.21" of that proof is absorbed in the statement of
Theorem 2.21; the induction over `k = 0, …, n₀` is an induction over a *fixed* natural number
`n₀ = ⌈2/τ'⌉`, `τ' = min(τ, 1)/240`, which does not depend on `N`.  This is exactly the remark
in that proof that only finitely many iterations are needed.

## Deviations from the paper

* The grid is the truncated grid `gridT` of `Flow/Scales.lean` (`τ'`, `n₀` fixed first, grid
  cut at `t`), not the solution of `1 - t = W^{-n₀τ'}`.
* The step condition of `Flow/Scales.lean` is stated with `(WL)^{-1+τ}`; since
  `N/2 ≤ WL ≤ N` (`RBM.Band.dim`), we apply it with `τ₀ = min(τ,1)/2` in place of `τ`.
-/

namespace RBM

open MeasureTheory Filter

/-! ### Generic: `≺` only depends on large `N` -/

section Congr

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem StochDom.congr_eventually {U : ℕ → Type*} {ξ ξ' ζ ζ' : ∀ N, U N → Ω → ℝ}
    (h : StochDom P ξ ζ) (hξ : ∀ᶠ N : ℕ in atTop, ξ N = ξ' N)
    (hζ : ∀ᶠ N : ℕ in atTop, ζ N = ζ' N) : StochDom P ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hξ, hζ] with N hN h1 h2
  simpa only [badSet, h1, h2] using hN

theorem UnifDetDom.congr_eventually {U : ℕ → Type*} {f f' g g' : ∀ N, U N → ℝ}
    (h : UnifDetDom f g) (hf : ∀ᶠ N : ℕ in atTop, f N = f' N)
    (hg : ∀ᶠ N : ℕ in atTop, g N = g' N) : UnifDetDom f' g' := by
  intro τ hτ
  filter_upwards [h τ hτ, hf, hg] with N hN h1 h2
  simpa only [h1, h2] using hN

/-- A family that vanishes is dominated by any non-negative family. -/
theorem StochDom.of_eq_zero {U : ℕ → Type*} {ξ ζ : ∀ N, U N → Ω → ℝ}
    (hξ : ∀ N u ω, ξ N u ω = 0) (hζ : ∀ N u ω, 0 ≤ ζ N u ω) : StochDom P ξ ζ :=
  StochDom.of_le_left (fun N u ω => (hξ N u ω).le.trans (hζ N u ω)) (StochDom.refl hζ)

end Congr

/-! ### The scale -/

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

theorem scale_eq_flowScale (E : ℝ) (N : ℕ) (t : ℝ) :
    B.scale E N t = flowScale (B.W N) (B.L N) E t := rfl

theorem scale_nonneg (E : ℝ) (N : ℕ) {t : ℝ} (ht : t ≤ 1) : 0 ≤ B.scale E N t := by
  rw [scale_eq_flowScale, flowScale_eq _ _ _ ht]
  have h1 : 0 ≤ 1 - t := by linarith
  have := mE_im_nonneg E
  have : 0 ≤ min (Real.sqrt (1 - t)) ((B.L N : ℝ) * (1 - t)) :=
    le_min (Real.sqrt_nonneg _) (by positivity)
  positivity

theorem one_le_W (N : ℕ) : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N

theorem one_le_L (N : ℕ) : 1 ≤ B.L N := by have := B.three_le_L N; omega

end Band

/-! ### (2.67): the bounds at `t = 0` -/

section Initial

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

theorem Sample.Lval_zero_eq_Kval (hE : |E| ≤ 2) (N : ℕ) (ω : Ω) (I : LoopIdx (ZMod (B.L N)))
    (hI : I.WF) (h1 : 1 ≤ I.length) : X.Lval E N 0 ω I = B.Kval E N 0 I := by
  rw [Sample.Lval, X.H_zero, Band.Kval]
  exact gloop_zero_zt_zero_eq_Kgen hE I hI h1

theorem Sample.lkErr_zero (hE : |E| ≤ 2) (N : ℕ) (ω : Ω) (I : LoopIdx (ZMod (B.L N)))
    (hI : I.WF) (h1 : 1 ≤ I.length) : X.lkErr E N 0 ω I = 0 := by
  rw [Sample.lkErr, X.Lval_zero_eq_Kval hE N ω I hI h1, sub_self, norm_zero]

theorem Sample.llErr_zero (hE : |E| ≤ 2) (N : ℕ) (ω : Ω) (ij : B.Idx N × B.Idx N) :
    X.llErr E N 0 ω ij = 0 := by
  have h := Gsig_zero_zt_zero_sub (n := B.Idx N) hE
  rw [Gsig_true] at h
  rw [Sample.llErr, Sample.G, X.H_zero, h, Matrix.zero_apply, norm_zero]

theorem Sample.expErr_zero (hE : |E| ≤ 2) (N : ℕ) (I : LoopIdx (ZMod (B.L N)))
    (hI : I.WF) (h1 : 1 ≤ I.length) : X.expErr E N 0 I = 0 := by
  have := B.isProbabilityMeasure
  have : X.ELval E N 0 I = B.Kval E N 0 I := by
    rw [Sample.ELval]
    simp_rw [X.Lval_zero_eq_Kval hE N _ I hI h1]
    rw [integral_const, probReal_univ, one_smul]
  rw [Sample.expErr, this, sub_self, norm_zero]

theorem pmLoop_wf {L : ℕ} (a b : ZMod L) : (pmLoop a b).WF := by
  simp [pmLoop, LoopIdx.WF]

theorem pmLoop_length {L : ℕ} (a b : ZMod L) : (pmLoop a b).length = 2 := by
  simp [pmLoop, LoopIdx.length]

end Initial

/-! ### The time grid for the band model -/

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

/-- `L ≤ W` for large `N`: from `WL ≤ N` and `W ≥ N^{1/2+c}`. -/
theorem eventually_L_le_W : ∀ᶠ N : ℕ in atTop, (B.L N : ℝ) ≤ B.W N := by
  filter_upwards [B.bandwidth, B.dim, eventually_ge_atTop 1] with N hbw hdim hN1
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hWL : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hsq : (N : ℝ) ≤ ((N : ℝ) ^ ((1 : ℝ) / 2 + B.c)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by push_cast; linarith [B.c_pos])
  have hW2 : (N : ℝ) ≤ (B.W N : ℝ) ^ 2 :=
    hsq.trans (pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hbw 2)
  nlinarith

/-- `W → ∞`: `W ≥ W₀` for large `N`. -/
theorem eventually_le_W (W₀ : ℝ) : ∀ᶠ N : ℕ in atTop, W₀ ≤ B.W N := by
  filter_upwards [B.bandwidth, eventually_le_rpow W₀ (by linarith [B.c_pos] :
    (0 : ℝ) < 1 / 2 + B.c)] with N hbw hW
  exact hW.trans hbw

/-- `N^{-1+τ} ≤ 1 - t` implies `(WL)^{-1+τ₀} ≤ 1 - t` for large `N`, if `0 ≤ τ₀ ≤ min(τ/2, 1)`
(since `N/2 ≤ WL`). -/
theorem eventually_rpow_WL_le {τ τ₀ : ℝ} (hτ : 0 < τ) (hτ₀0 : 0 ≤ τ₀) (hτ₀1 : τ₀ ≤ 1)
    (hτ₀τ : τ₀ ≤ τ / 2) :
    ∀ᶠ N : ℕ in atTop, ((B.W N : ℝ) * B.L N) ^ (-1 + τ₀) ≤ (N : ℝ) ^ (-1 + τ) := by
  filter_upwards [B.dim, eventually_le_rpow 2 (half_pos hτ), eventually_ge_atTop 1]
    with N hdim h2 hN1
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hM : (N : ℝ) ≤ 2 * ((B.W N : ℝ) * B.L N) := by exact_mod_cast hdim.2
  set e := -1 + τ₀ with he
  have he0 : e ≤ 0 := by linarith
  have h2e : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ e := by
    calc (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hNe : 0 ≤ (N : ℝ) ^ e := Real.rpow_nonneg hN0.le _
  calc ((B.W N : ℝ) * B.L N) ^ e ≤ ((N : ℝ) / 2) ^ e :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) he0
    _ = (N : ℝ) ^ e / (2 : ℝ) ^ e := Real.div_rpow hN0.le (by norm_num) e
    _ ≤ (N : ℝ) ^ e / (1 / 2) := div_le_div_of_nonneg_left hNe (by norm_num) h2e
    _ = 2 * (N : ℝ) ^ e := by ring
    _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ e := mul_le_mul_of_nonneg_right h2 hNe
    _ = (N : ℝ) ^ (τ / 2 + e) := (Real.rpow_add hN0 _ _).symm
    _ ≤ (N : ℝ) ^ (-1 + τ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end Band

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

end Main

/-! ### Bounds on the primitive loop `K` -/

section Loop261

theorem norm_primInit_le {L W : ℕ} [NeZero L] {E : ℝ} (hE : |E| ≤ 2) (I : LoopIdx (ZMod L)) :
    ‖primInit L W (mSigma E) I‖ ≤ ((W : ℝ)⁻¹) ^ (I.length - 1) := by
  have hprod : ‖(I.σ.map (mSigma E)).prod‖ = 1 := by
    rw [List.norm_prod, List.map_map]
    have : (norm ∘ mSigma E) = fun _ => (1 : ℝ) := funext fun s => norm_mSigma hE s
    rw [this, List.map_const', List.prod_replicate, one_pow]
  have hite : ‖(if ∀ x ∈ I.a, ∀ y ∈ I.a, x = y then (1 : ℂ) else 0)‖ ≤ 1 := by
    split_ifs <;> simp
  rw [primInit, norm_mul, norm_mul, hprod, mul_one, norm_pow, norm_inv, Complex.norm_natCast]
  exact mul_le_of_le_one_right (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) hite

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

/-- `W ℓ_0 η_0 = W Im m ≤ W`. -/
theorem scale_zero_le (E : ℝ) (hE : |E| ≤ 2) (N : ℕ) : B.scale E N 0 ≤ B.W N := by
  rw [scale_eq_flowScale, flowScale_eq _ _ _ zero_le_one]
  have hL : (1 : ℝ) ≤ B.L N := by exact_mod_cast B.one_le_L N
  have hmin : min (Real.sqrt (1 - 0)) ((B.L N : ℝ) * (1 - 0)) = 1 := by
    rw [sub_zero, Real.sqrt_one, mul_one, min_eq_left hL]
  have him : (mE E).im ≤ 1 := (Complex.im_le_norm _).trans (norm_mE hE).le
  rw [hmin, mul_one]
  exact mul_le_of_le_one_right (by linarith [B.one_le_W N]) him

/-- **The bound on `K` used for (2.61)**: `|K_{t,σ,a}| ≤ C (W ℓ_t η_t)^{-n+1}` for `0 ≤ t < 1`,
for loops of length `n = 1` (`K = m`) or `n ≥ 3` ((2.59), `RBM.norm_Kgen_le`, and `K_0 = primInit`
at `t = 0`). -/
theorem norm_Kval_le_of_ne_two {E k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k) {n : ℕ}
    (hn : n = 1 ∨ 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N (t : ℝ), 0 ≤ t → t < 1 → ∀ I : LoopIdx (ZMod (B.L N)), I.WF →
      I.length = n → ‖B.Kval E N t I‖ ≤ C * (B.scale E N t)⁻¹ ^ (n - 1) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  rcases hn with rfl | hn
  · refine ⟨1, zero_le_one, fun N t _ _ I hI hlen => ?_⟩
    obtain ⟨σ, a⟩ := I
    have ha : a.length = 1 := hlen
    have hσ : σ.length = 1 := hI.trans ha
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 ha
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.1 hσ
    rw [Kval, Kgen_one, norm_mSigma hE2, pow_zero, mul_one]
  · obtain ⟨C, hC0, hC⟩ := norm_Kgen_le hk0 hk1 hEk n
    refine ⟨max C 1, le_max_of_le_right zero_le_one, fun N t ht0 ht1 I hI hlen => ?_⟩
    have hY0 : 0 ≤ (B.scale E N t)⁻¹ := inv_nonneg.2 (B.scale_nonneg E N ht1.le)
    have hYp : 0 ≤ (B.scale E N t)⁻¹ ^ (n - 1) := pow_nonneg hY0 _
    rcases ht0.lt_or_eq with ht0 | rfl
    · have h := hC (B.L N) (B.three_le_L N) (B.W N) t ht0 ht1 I hI (by omega) (by omega)
      have hs : (B.W N : ℝ) * (etaT E t * ellHat (B.L N) (t : ℂ)) = B.scale E N t := by
        rw [scale, ell]; ring
      rw [hs, hlen] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hYp)
    · have h0 : B.Kval E N 0 I = primInit (B.L N) (B.W N) (mSigma E) I := by
        rw [Kval, ← gloop_zero_zt_zero_eq_Kgen hE2 I hI (by omega)]
        exact gloop_zero_zt_zero hE2 I hI (by omega)
      have hpos : 0 < B.scale E N 0 :=
        flowScale_pos (by linarith [B.one_le_W N]) (B.one_le_L N) hE zero_lt_one
      have hWinv : (B.W N : ℝ)⁻¹ ≤ (B.scale E N 0)⁻¹ := inv_anti₀ hpos (B.scale_zero_le E hE2 N)
      rw [h0]
      refine (norm_primInit_le hE2 I).trans ?_
      rw [hlen]
      calc ((B.W N : ℝ)⁻¹) ^ (n - 1) ≤ (B.scale E N 0)⁻¹ ^ (n - 1) :=
            pow_le_pow_left₀ (inv_nonneg.2 (Nat.cast_nonneg _)) hWinv _
        _ = 1 * (B.scale E N 0)⁻¹ ^ (n - 1) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hYp

/-- **The 2-loop**: `K_{t,(s₁,s₂),(x,y)} = W⁻¹ m₁m₂ (Θ_{t m₁m₂})_{xy}`, so
`|K| ≤ C (W ℓ_t η_t)^{-1}`: a long edge is `≤ 8e/(η_t ℓ_t)` by (3.35), a short edge is `O(1)`
and `W⁻¹ ≤ (W ℓ_t η_t)⁻¹` since `η_t ℓ_t ≤ 1`. -/
theorem norm_Kval_two_le {E k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N (t : ℝ), 0 ≤ t → t < 1 → ∀ I : LoopIdx (ZMod (B.L N)), I.WF →
      I.length = 2 → ‖B.Kval E N t I‖ ≤ C * (B.scale E N t)⁻¹ ^ (2 - 1) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  set Bk := 2 * cTwo52 / Real.sqrt k + 1
  have hBk : 1 ≤ Bk := by
    have := cTwo52_pos
    have : 0 ≤ 2 * cTwo52 / Real.sqrt k := by
      have := Real.sqrt_nonneg k; positivity
    simp only [Bk]; linarith
  have he : 0 ≤ 8 * Real.exp 1 := by positivity
  refine ⟨Bk + 8 * Real.exp 1, by linarith, fun N t ht0 ht1 I hI hlen => ?_⟩
  obtain ⟨σ, a⟩ := I
  have ha : a.length = 2 := hlen
  have hσ : σ.length = 2 := hI.trans ha
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 ha
  obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.1 hσ
  have hL := B.three_le_L N
  have hW1 := B.one_le_W N
  -- `W ℓ η ≤ W` and `0 < W ℓ η`
  have hs : (B.W N : ℝ) * (etaT E t * ellHat (B.L N) (t : ℂ)) = B.scale E N t := by
    rw [scale, ell]; ring
  have hη : 0 < etaT E t := etaT_pos hE ht1
  have hℓ1 : 1 ≤ ellHat (B.L N) (t : ℂ) := by
    rw [ellHat_ofReal _ ht1]
    refine le_min ?_ (by exact_mod_cast (show 1 ≤ B.L N by omega))
    rw [le_div_iff₀ (Real.sqrt_pos.2 (by linarith)), one_mul]
    exact Real.sqrt_le_one.2 (by linarith)
  have hηℓ : etaT E t * ellHat (B.L N) (t : ℂ) ≤ 1 := by
    rcases ht0.lt_or_eq with ht0' | rfl
    · exact etaT_mul_ellHat_le hL hE2 ht0'.le ht1
    · have h1 : ellHat (B.L N) ((0 : ℝ) : ℂ) = 1 := by
        rw [ellHat_ofReal _ zero_lt_one, sub_zero, Real.sqrt_one, div_one]
        exact min_eq_left (by exact_mod_cast (show 1 ≤ B.L N by omega))
      rw [h1, mul_one, etaT, sub_zero, one_mul]
      exact mE_im_le_one hE
  have hpos : 0 < B.scale E N t := by rw [← hs]; positivity
  have hWinv : (B.W N : ℝ)⁻¹ ≤ (B.scale E N t)⁻¹ := by
    refine inv_anti₀ hpos ?_
    rw [← hs]; nlinarith
  have hS0 : 0 ≤ (B.scale E N t)⁻¹ := inv_nonneg.2 hpos.le
  rw [Kval, Kgen_two, kTwo, pow_one]
  have hm : ‖mSigma E s₁ * mSigma E s₂‖ = 1 := by
    rw [norm_mul, norm_mSigma hE2, norm_mSigma hE2, one_mul]
  rw [norm_mul, norm_mul, hm, mul_one, norm_inv, Complex.norm_natCast]
  by_cases hss : s₁ = s₂
  · -- a short edge
    subst hss
    have h := norm_thetaEdge_same_le hL hE hk0 hk1 hEk ht0 ht1 s₁ x y
    have h' : ‖Theta (B.L N) ((t : ℂ) * (mSigma E s₁ * mSigma E s₁)) x y‖ ≤ Bk :=
      h.trans (mul_le_of_le_one_right (by linarith) (by
        rw [Real.exp_le_one_iff, neg_nonpos]; have := cZero_pos; positivity))
    calc (B.W N : ℝ)⁻¹ * ‖Theta (B.L N) ((t : ℂ) * (mSigma E s₁ * mSigma E s₁)) x y‖
        ≤ (B.scale E N t)⁻¹ * Bk := mul_le_mul hWinv h' (norm_nonneg _) hS0
      _ ≤ (Bk + 8 * Real.exp 1) * (B.scale E N t)⁻¹ := by nlinarith
  · -- a long edge: `ξ = t`
    rw [mSigma_mul_of_ne hE2 hss, mul_one]
    rcases ht0.lt_or_eq with ht0' | rfl
    · have h := norm_Theta_long_edge_le (B.L N) hL hk0 (by linarith) hEk ht0' ht1 x y
      rw [← etaT_eq_zt_im] at h
      calc (B.W N : ℝ)⁻¹ * ‖Theta (B.L N) (t : ℂ) x y‖
          ≤ (B.W N : ℝ)⁻¹ * (8 * Real.exp 1 / (etaT E t * ellHat (B.L N) (t : ℂ))) := by
            gcongr
        _ = 8 * Real.exp 1 * (B.scale E N t)⁻¹ := by
            rw [← hs]; field_simp
        _ ≤ (Bk + 8 * Real.exp 1) * (B.scale E N t)⁻¹ := by nlinarith
    · have h1 : ‖Theta (B.L N) ((0 : ℝ) : ℂ) x y‖ ≤ 1 := by
        rw [Complex.ofReal_zero, Theta_zero, Matrix.one_apply]
        split_ifs <;> simp
      calc (B.W N : ℝ)⁻¹ * ‖Theta (B.L N) ((0 : ℝ) : ℂ) x y‖ ≤ (B.scale E N 0)⁻¹ * 1 :=
            mul_le_mul hWinv h1 (norm_nonneg _) hS0
        _ ≤ (Bk + 8 * Real.exp 1) * (B.scale E N 0)⁻¹ := by nlinarith

/-- **The primitive loop in the flow**: `|K_{t,σ,a}| ≤ C (W ℓ_t η_t)^{-n+1}` for every `n ≥ 1` and
`0 ≤ t < 1` ((2.59) for `n ≥ 3`, the explicit `n = 1, 2` cases otherwise). -/
theorem norm_Kval_le {E k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k) {n : ℕ}
    (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N (t : ℝ), 0 ≤ t → t < 1 → ∀ I : LoopIdx (ZMod (B.L N)), I.WF →
      I.length = n → ‖B.Kval E N t I‖ ≤ C * (B.scale E N t)⁻¹ ^ (n - 1) := by
  by_cases h2 : n = 2
  · subst h2; exact B.norm_Kval_two_le hk0 hk1 hEk
  · exact B.norm_Kval_le_of_ne_two hk0 hk1 hEk (by omega)

end Band

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

end Loop261

end RBM
