/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Hypotheses
import RBM1D.Flow.Initial
import RBM1D.Flow.Scales

/-!
# Lemmas 2.18, 2.19, 2.20 from Theorem 2.21 (§2.7, p. 24)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7, "Proof of Lemmas 2.18, 2.19,
and 2.20" on p. 24: starting from (2.67) at `t = 0`, apply Theorem 2.21 along the time grid
`1 - s_k = W^{-kτ'}`, `k = 0, …, n₀ - 1`.

Theorem 2.21 is the hypothesis `RBM.Thm221 X κ` of `Flow/Hypotheses.lean` (it needs the random
flow); everything else is proved.

## Main results

* `RBM.Bounds_zero` — **(2.67)**: Lemmas 2.18–2.20 hold at `t = 0` with no error
  (`L_0 = K_0`, `G_0 = m`, `E L_0 = K_0`, from `Flow/Initial.lean`).
* `RBM.Bounds.congr` — the bounds only depend on the time sequence for large `N`.
* `RBM.Band.eventually_flow_grid` — for the band model (`W ≥ N^{1/2+c}`, `WL ≍ N`) and
  `1 - t ≥ N^{-1+τ}`: `τ'` and `n₀` depending on `τ` only, and for large `N` the truncated grid
  `u_k = min(1 - W^{-kτ'}, t)` reaches `t` at `k = n₀`, satisfies (2.72) at every step, and
  `W ℓ_t η_t ≥ 1`.
* `RBM.Bounds_of_Thm221` — **Lemmas 2.18 (2.60), 2.19 (2.62), (2.63), 2.20 (2.64)** for every
  time sequence `0 ≤ t ≤ 1 - N^{-1+τ}`, by `n₀` applications of Theorem 2.21.
* `RBM.stochDom_norm_Lval_of_Thm221` — **(2.61)** `max_{σ,a} |L_{t,σ,a}| ≺ (W ℓ_t η_t)^{-n+1}`
  for `n = 1` and `n ≥ 3`, from (2.60) and (2.59) (`RBM.norm_Kgen_le`).  The intermediate
  `RBM.stochDom_norm_Lval_of_LmK` also covers `t = 0` (where `K_0 = primInit`,
  `RBM.Band.norm_Kval_le`), which `RBM.BoundsCore.stochDom_norm_Lval` excludes.

No hypothesis beyond `RBM.Thm221` is needed: the interface of `Flow/Hypotheses.lean` suffices.

## The induction

Since `≺` is a `Prop` (Definition 2.1: "for every `τ > 0`, `D > 0`, for `N ≥ N₀(τ, D)`"), the
"`N^ε` loss per application of Theorem 2.21" of p. 24 is absorbed in the statement of
`RBM.Thm221`; the induction over `k = 0, …, n₀` is an induction over a *fixed* natural number
`n₀ = ⌈2/τ'⌉`, `τ' = min(τ, 1)/240`, which does not depend on `N`.  This is exactly the remark
on p. 24 that only finitely many iterations are needed.

## Deviations from the paper

* The grid is the truncated grid `gridT` of `Flow/Scales.lean` (`τ'`, `n₀` fixed first, grid
  cut at `t`), not the solution of `1 - t = W^{-n₀τ'}`.
* The step condition of `Flow/Scales.lean` is stated with `(WL)^{-1+τ}`; since
  `N/2 ≤ WL ≤ N` (`RBM.Band.dim`), we apply it with `τ₀ = min(τ,1)/2` in place of `τ`.
* (2.61) is proved for `n = 1` and `n ≥ 3`.  `n = 2` needs `|K_{t,σ,a}| ≤ C (W ℓ_t η_t)^{-1}`
  for 2-loops, which is not (yet) available in the required form (`RBM.norm_Kgen_le` is for
  `n ≥ 3`; `RBM.norm_Kgen_two_le` has `(1 - T₀)^{-1}` in place of `(ℓ_t η_t)^{-1}`).
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

/-- **(2.67)**: Lemmas 2.18, 2.19, 2.20 hold at `t = 0` with no error. -/
theorem Bounds_zero (hE : |E| ≤ 2) : Bounds X E (fun _ => 0) := by
  have hY : ∀ N, 0 ≤ (B.scale E N 0)⁻¹ := fun N => inv_nonneg.2 (B.scale_nonneg E N zero_le_one)
  refine ⟨⟨fun n hn => ?_, fun D hD => ?_, ?_⟩, ?_⟩
  · exact StochDom.of_eq_zero
      (fun N u ω => X.lkErr_zero hE N ω u.idx u.idx_wf (by simpa using hn))
      (fun N _ _ => pow_nonneg (hY N) n)
  · refine StochDom.of_eq_zero
      (fun N a ω => X.lkErr_zero hE N ω _ (pmLoop_wf a.1 a.2) (by simp [pmLoop_length]))
      (fun N a _ => mul_nonneg (pow_nonneg (hY N) 2) ?_)
    unfold Band.decayProf
    positivity
  · exact StochDom.of_eq_zero (fun N ij ω => X.llErr_zero hE N ω ij)
      (fun N _ _ => Real.rpow_nonneg (hY N) _)
  · intro τ hτ
    refine Eventually.of_forall fun N u => ?_
    simp only
    rw [X.expErr_zero hE N u.idx u.idx_wf (by simp)]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) τ) (pow_nonneg (hY N) 3)

/-- The bounds (2.68)–(2.71) at a time sequence only depend on it for large `N`. -/
theorem Bounds.congr {s t : ℕ → ℝ} (h : Bounds X E s) (hst : ∀ᶠ N : ℕ in atTop, s N = t N) :
    Bounds X E t where
  LmK n hn := (h.LmK n hn).congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])
  decay D hD := (h.decay D hD).congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])
  localLaw := h.localLaw.congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])
  expect := h.expect.congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])

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

/-- **The grid of p. 24 for the band model.**  Given `κ, τ > 0` there are `τ' > 0` and `n₀ ∈ ℕ`
(depending on `τ` only) such that for every `|E| ≤ 2 - κ` and every time sequence
`0 ≤ t ≤ 1 - N^{-1+τ}` (the latter for large `N`), for large `N` the truncated grid
`u_k = min(1 - W^{-kτ'}, t)` satisfies `u_{n₀} = t` and (2.72) at every step, and
`W ℓ_t η_t ≥ 1`, `t < 1`. -/
theorem eventually_flow_grid {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ n₀ : ℕ, ∀ E : ℝ, |E| ≤ 2 - κ → ∀ t : ℕ → ℝ, (∀ N, 0 ≤ t N) →
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) →
      ∀ᶠ N : ℕ in atTop, gridT (B.W N) τ' (t N) n₀ = t N ∧ 1 ≤ B.scale E N (t N) ∧
        t N < 1 ∧ ∀ k : ℕ, (B.scale E N (gridT (B.W N) τ' (t N) (k + 1)))⁻¹ ≤
          ((1 - gridT (B.W N) τ' (t N) (k + 1)) / (1 - gridT (B.W N) τ' (t N) k)) ^ 30 := by
  set τ₀ := min τ 1 / 2 with hτ₀
  have hτ₀0 : 0 < τ₀ := by have := lt_min hτ one_pos; rw [hτ₀]; linarith
  have hτ₀1 : τ₀ ≤ 1 := by have := min_le_right τ 1; rw [hτ₀]; linarith
  have hτ₀τ : τ₀ ≤ τ / 2 := by have := min_le_left τ 1; rw [hτ₀]; linarith
  set τ' := τ₀ / 120 with hτ'
  have hτ'0 : 0 < τ' := by rw [hτ']; positivity
  set n₀ := ⌈2 / τ'⌉₊ with hn₀
  have hn : 2 ≤ (n₀ : ℝ) * τ' := (div_le_iff₀ hτ'0).1 (Nat.le_ceil _)
  obtain ⟨W₀, -, hW⟩ := flow_grid_2_72 hκ hτ₀0.le hτ'0 (by rw [hτ']; linarith) hn
  refine ⟨τ', hτ'0, n₀, fun E hE t ht0 ht => ?_⟩
  filter_upwards [B.eventually_le_W W₀, B.eventually_L_le_W,
    B.eventually_rpow_WL_le hτ hτ₀0.le hτ₀1 hτ₀τ, ht, eventually_ge_atTop 1] with N hWN hLW hWL htN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have ht1 : t N < 1 := by have := Real.rpow_pos_of_pos hN0 (-1 + τ); linarith
  obtain ⟨-, hgrid, -, hA, hstep⟩ :=
    hW (B.W N) hWN (B.L N) (B.one_le_L N) hLW E hE (t N) (ht0 N) (hWL.trans htN)
  have hE2 : |E| < 2 := by linarith
  have hpos : 0 < B.scale E N (t N) :=
    flowScale_pos (by linarith [B.one_le_W N]) (B.one_le_L N) hE2 ht1
  have hA1 : (B.scale E N (t N))⁻¹ ≤ 1 :=
    hA.trans (Real.rpow_le_one_of_one_le_of_nonpos (B.one_le_W N) (by linarith))
  exact ⟨hgrid, (inv_le_one₀ hpos).1 hA1, ht1, hstep⟩

end Band

/-! ### Lemmas 2.18, 2.19, 2.20 -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

/-- **Proof of Lemmas 2.18, 2.19 and 2.20 (p. 24), assuming Theorem 2.21.**  For `κ, τ > 0`,
`|E| ≤ 2 - κ` and every time sequence with `0 ≤ t` and `t ≤ 1 - N^{-1+τ}` (for large `N`), the
bounds (2.60) = (2.68), (2.63) = (2.69), (2.64) = (2.70) and (2.62) = (2.71) hold at `t`.

Proof: (2.67) at `u_0 = 0`, then Theorem 2.21 from `u_k` to `u_{k+1}` along the truncated grid
`u_k = min(1 - W^{-kτ'}, t)` for `k = 0, …, n₀ - 1` ((2.72) holds at every step for large `N`),
and `u_{n₀} = t` for large `N`. -/
theorem Bounds_of_Thm221 {κ : ℝ} (hκ : 0 < κ) (hT : Thm221 X κ) (hE : |E| ≤ 2 - κ) {τ : ℝ}
    (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) : Bounds X E t := by
  obtain ⟨τ', hτ', n₀, hgrid⟩ := B.eventually_flow_grid hκ hτ
  have hg := hgrid E hE t ht0 ht
  have hE2 : |E| ≤ 2 := by linarith
  let u : ℕ → ℕ → ℝ := fun k N => gridT (B.W N) τ' (t N) k
  have key : ∀ k, Bounds X E (u k) := by
    intro k
    induction k with
    | zero =>
      have h0 : u 0 = fun _ => 0 := funext fun N => gridT_zero (ht0 N)
      rw [h0]
      exact Bounds_zero X hE2
    | succ k ih =>
      refine hT.step E hE (u k) (u (k + 1)) (fun N => ?_) (fun N => ?_) (fun N => ?_) ?_ ih
      · exact le_min (gridS_nonneg (B.one_le_W N) hτ'.le k) (ht0 N)
      · exact gridT_mono (B.one_le_W N) hτ'.le (t N) (Nat.le_succ k)
      · exact (min_le_left _ _).trans_lt (gridS_lt_one (by linarith [B.one_le_W N]) _)
      · filter_upwards [hg] with N hN
        exact hN.2.2.2 k
  exact (key n₀).congr X (by filter_upwards [hg] with N hN; exact hN.1)

end Main

/-! ### (2.61) -/

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
    · exact etaT_mul_ellHat_le hL hE2 ht0' ht1
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

/-- **(2.61) from (2.60) and (2.59)**, for time sequences with `0 ≤ t < 1` (including `t = 0`,
unlike `RBM.BoundsCore.stochDom_norm_Lval`) and for every `n ≥ 1`. -/
theorem stochDom_norm_Lval_of_LmK {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hEk : |E| ≤ 2 - k)
    {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N) (ht1 : ∀ N, t N < 1)
    (hA : ∀ᶠ N : ℕ in atTop, 1 ≤ B.scale E N (t N)) {n : ℕ} (hn : 1 ≤ n)
    (hLK : StochDom B.P (fun N (u : LoopData (B.L N) n) ω => X.lkErr E N (t N) ω u.idx)
      (fun N _ _ => (B.scale E N (t N))⁻¹ ^ n)) :
    StochDom B.P (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval E N (t N) ω u.idx‖)
      (fun N _ _ => (B.scale E N (t N))⁻¹ ^ (n - 1)) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨C, hC0, hC⟩ := B.norm_Kval_le hk0 hk1 hEk hn
  set Y : ℕ → ℝ := fun N => (B.scale E N (t N))⁻¹ with hYdef
  have hY0 : ∀ N, 0 ≤ Y N := fun N => inv_nonneg.2 (B.scale_nonneg E N (ht1 N).le)
  -- `|L - K| ≺ Y^{n-1}`
  have h1 : StochDom B.P (fun N (u : LoopData (B.L N) n) ω => X.lkErr E N (t N) ω u.idx)
      (fun N _ _ => Y N ^ (n - 1)) := by
    refine hLK.trans ?_
    refine StochDom.of_unifDetDom (f := fun N (_ : LoopData (B.L N) n) => Y N ^ n)
      (g := fun N _ => Y N ^ (n - 1)) ?_
    refine UnifDetDom.of_eventually_le_const_mul (fun N _ => pow_nonneg (hY0 N) _) 1 ?_
    filter_upwards [hA] with N hN u
    have hY1 : Y N ≤ 1 := inv_le_one_of_one_le₀ hN
    have : Y N ^ n = Y N * Y N ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this, one_mul]
    exact mul_le_of_le_one_left (pow_nonneg (hY0 N) _) hY1
  -- `|K| ≺ Y^{n-1}`
  have h2 : StochDom B.P (fun N (u : LoopData (B.L N) n) (_ : Ω) => ‖B.Kval E N (t N) u.idx‖)
      (fun N _ _ => Y N ^ (n - 1)) :=
    StochDom.of_unifDetDom (UnifDetDom.of_eventually_le_const_mul
      (fun N _ => pow_nonneg (hY0 N) _) C (Eventually.of_forall fun N u =>
        hC N (t N) (ht0 N) (ht1 N) u.idx u.idx_wf (by simp)))
  have h3 : StochDom B.P (fun N (_ : LoopData (B.L N) n) (_ : Ω) => Y N ^ (n - 1) + Y N ^ (n - 1))
      (fun N _ _ => Y N ^ (n - 1)) := by
    refine StochDom.of_unifDetDom (f := fun N (_ : LoopData (B.L N) n) => Y N ^ (n - 1) +
      Y N ^ (n - 1)) (g := fun N _ => Y N ^ (n - 1)) ?_
    exact UnifDetDom.of_eventually_le_const_mul (fun N _ => pow_nonneg (hY0 N) _) 2
      (Eventually.of_forall fun N _ => by linarith)
  refine StochDom.of_le_left (fun N u ω => ?_) ((h1.add h2).trans h3)
  have := norm_sub_norm_le (X.Lval E N (t N) ω u.idx) (B.Kval E N (t N) u.idx)
  simp only [Pi.add_apply, Sample.lkErr]
  linarith

/-- **Lemma 2.18, (2.61), assuming Theorem 2.21**: for `κ, τ > 0`, `|E| ≤ 2 - κ` and
`0 ≤ t ≤ 1 - N^{-1+τ}`, `max_{σ,a} |L_{t,σ,a}| ≺ (W ℓ_t η_t)^{-n+1}`, for every `n ≥ 1`. -/
theorem stochDom_norm_Lval_of_Thm221 {κ : ℝ} (hκ : 0 < κ) (hT : Thm221 X κ)
    (hE : |E| ≤ 2 - κ) {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval E N (t N) ω u.idx‖)
      (fun N _ _ => (B.scale E N (t N))⁻¹ ^ (n - 1)) := by
  obtain ⟨τ', -, n₀, hgrid⟩ := B.eventually_flow_grid hκ hτ
  -- replace `t` by a sequence `t'` with `t' < 1` for every `N`, equal to `t` for large `N`
  set t' : ℕ → ℝ := fun N => if t N < 1 then t N else 0 with ht'
  have ht'0 : ∀ N, 0 ≤ t' N := fun N => by
    simp only [ht']; split_ifs
    · exact ht0 N
    · exact le_rfl
  have ht'1 : ∀ N, t' N < 1 := fun N => by
    simp only [ht']; split_ifs with h
    · exact h
    · exact zero_lt_one
  have hg := hgrid E hE t ht0 ht
  have htt' : ∀ᶠ N : ℕ in atTop, t N = t' N := by
    filter_upwards [hg] with N hN
    simp only [ht', ite_eq_left hN.2.2.1]
  have ht'' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t' N := by
    filter_upwards [ht, htt'] with N h1 h2; rwa [← h2]
  have hk0 : 0 < min κ 1 := lt_min hκ one_pos
  have hEk : |E| ≤ 2 - min κ 1 := hE.trans (by linarith [min_le_left κ 1])
  have hA : ∀ᶠ N : ℕ in atTop, 1 ≤ B.scale E N (t' N) := by
    filter_upwards [hg, htt'] with N h1 h2; rw [← h2]; exact h1.2.1
  have hB := Bounds_of_Thm221 X hκ hT hE hτ ht'0 ht''
  have h := stochDom_norm_Lval_of_LmK X hk0 (min_le_right κ 1) hEk ht'0 ht'1 hA hn
    (hB.LmK n (by omega))
  exact h.congr_eventually (by filter_upwards [htt'] with N hN; rw [hN])
    (by filter_upwards [htt'] with N hN; rw [hN])

end Loop261

end RBM
