/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step3
import RBM1D.Hierarchy.KernelDecay
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Step 6 of the proof of Theorem 2.21: the sharp `E(L-K)` bound (2.80)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.8 (pp. 72–73): Lemma 5.15
((5.126)–(5.128)) and the proof of (2.80) ((5.129)–(5.136)), with Lemma 7.3 (7.14) (p. 78).

Given the random inputs as hypotheses, Step 6 is deterministic: the linear algebra of (5.128),
one application of the evolution kernel per term via (7.14), the monotonicity
`ℓ_u² η_u ≤ ℓ_v² η_v` (`v ≤ u`), and the time integral `∫_s^u η_v^{-1} dv`.  Nothing is an
`axiom`; (7.14) is the proved Lemma 7.3 (`RBM.norm_Uker_fastDecay_le`, T51).

## Main results

Deterministic:
* `ellHat_sq_mul_one_sub_anti` — `ℓ_u²(1-u) ≤ ℓ_v²(1-v)` for `v ≤ u < 1` (the last line of p. 73).
* `kernel_ratio_le` — `(ℓ_u/ℓ_v)(ℓ_vη_v/(ℓ_uη_u))² (Wℓ_vη_v)^{-3} ≤ (Wℓ_uη_u)^{-3}`.
* `norm_integral_le_log` — `‖∫_s^u f‖ ≤ α log((1-s)/(1-u)) + β(u-s)` if `‖f v‖ ≤ α/(1-v) + β`.
* `Est714At`, `est714At_cKer` — **(7.14)** in the form used here, proved from T51.
* `kernel_term_le` — one kernel step of (5.136); `core_bound` — **(5.129)–(5.131) ⟹ (5.136)**
  at one final time, with explicit constants.
* `eq_Theta_of_selfConsistent` — **(5.128)**: `x = u m² Sᵀ x + y ⟹ x = Θ^{(B)}_{um²} y`;
  `norm_selfConsistent_le` — with (3.36) (short edge), `max|x| ≤ C_κ max|y|`;
  `norm_quadTerm_le` — the quadratic term of (5.127) is `≤ max |E[(G-m)(G-m)]|`.

For the flow (`RBM.Sample`, `RBM.Band` of `Flow/Hypotheses.lean`):
* `lkT` (the tensor `E(L-K)_{u,σ,·}`), `Hierarchy` (**(5.129)–(5.131)**), `FastDecayHyp`
  (fast decay, p. 73), `DriftBound` (the form of (5.133), (5.135)).
* `sharpExpect_of_hierarchy` — **(5.136) ⟹ (2.80)**, in the shape of `RBM.Steps.sharpExpect`.
* `oneLoop`, `lk1`, `quad11`, `Eq527` (**(5.127)**), `lemma515` — **Lemma 5.15, (5.126)**.
* `driftBound_of_5133` — **(5.133)** rewritten; `mix13`, `quad13`, `mix13_eq` — the splitting
  **(5.134)** `L = K + (L-K)`; `driftBound_of_5134` — **(5.134) ⟹ (5.135)**.
* `sharpExpect_step6` — **(2.80)**, everything assembled.

## Hypotheses (random layer, never axioms)

* `Hierarchy`: (5.20) for `n = 2` after taking expectations, the martingale term vanishing (and
  no `l_K > 2` terms for `n = 2`).  The drift tensors `E E^{((L-K)×(L-K))}` and `E E^{(G)}` are
  not defined in Lean; they enter as arbitrary `DriftTensor`s constrained by the hypotheses.
* `FastDecayHyp`: "all tensors discussed above have fast decay" (p. 73), with `(ℓ W^τ, W^{-D})`.
* (5.132) = (2.71) at `s`; (5.133); (5.127); the structural bound of (5.134).
* The three bounds that come from `≺`-bounds on random variables by taking expectations:
  `E[(L-K)_1 (L-K)_1] ≺ A^{-2}`, `E[(L-K)_1 (L-K)_3] ≺ A^{-4}` (both "(2.78)") and (5.133).  Going
  from `≺` to expectations needs a deterministic a-priori bound on the loops, which is not
  formalized; so these are stated directly for the expectations.
* Integrability of the `1`-loops and of the products in (5.134) (in the paper automatic from
  `‖G_t‖ ≤ η_t^{-1}`).

## Deviations from the paper

* (2.80) is proved uniformly in `u ∈ [s,t]` (as `RBM.Steps.sharpExpect` demands), by running
  (5.136) with final time `u` and then using `(W ℓ_u η_u)^{-3} ≤ (W ℓ_t η_t)^{-3}`.
* The time integral: `∫_s^u η_v^{-1} dv = (Im m)^{-1} log((1-s)/(1-u))` is not `O(1)`; the paper's
  "`≺ 1`" uses `log((1-s)/(1-u)) ≤ 2 log W ≺ 1`, which needs `1 - u ≥ W^{-2}`.  We get this from
  (2.72) (`W ℓ_t η_t ≥ 1`), which is therefore a hypothesis of `sharpExpect_of_hierarchy`.
* (7.14) is used with `η_x = 1 - x` (T51's normalization); the ratios `η_s/η_t` coincide with the
  paper's `η_x = (1-x) Im m`.  The fast-decay window is `ℓ_v W^τ` and the tail `W^{-7}`
  (`D = 7` suffices since `(η_s/η_u)² ≤ W^4` and `(W ℓ_u η_u)^{-3} ≥ W^{-3}`).
* (5.134) is taken as `|E E^{(G)}_{u,σ,a}| ≤ C W ℓ_u Λ` whenever `Λ` bounds all
  `|E[⟨(G-m)E_{a₁}⟩ L_{u,σ',a'}]|` (the maximum written as a bound), with `C` uniform.
* (5.127)/(5.128) use the symmetry `S_{ba} = S_{ab}` to write `(1 - u m² S) x = y`.
-/

namespace RBM

open MeasureTheory Filter Finset

namespace Step6

/-! ### Real inequalities between the scales -/

section Real

/-- `ℓ̂(u)² (1-u) ≤ ℓ̂(v)² (1-v)` for `v ≤ u < 1`: the monotonicity `ℓ_u² η_u ≤ ℓ_v² η_v` used at
the end of (5.136) (`η_x = (1-x) Im m`). -/
theorem ellHat_sq_mul_one_sub_anti (L : ℕ) {v u : ℝ} (hvu : v ≤ u) (hu1 : u < 1) :
    ellHat L (u : ℂ) ^ 2 * (1 - u) ≤ ellHat L (v : ℂ) ^ 2 * (1 - v) := by
  have hv1 : v < 1 := hvu.trans_lt hu1
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hsu : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 h1u
  have hsv : 0 < Real.sqrt (1 - v) := Real.sqrt_pos.2 h1v
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  rw [ellHat_ofReal L hu1, ellHat_ofReal L hv1]
  set ℓ := min (1 / Real.sqrt (1 - u)) (L : ℝ) with hℓ
  have hℓ0 : 0 ≤ ℓ := le_min (by positivity) hL0
  have hℓ1 : ℓ ≤ 1 / Real.sqrt (1 - u) := min_le_left _ _
  have hℓ2 : ℓ ≤ L := min_le_right _ _
  have hsq : ℓ ^ 2 * (1 - u) ≤ 1 := by
    calc ℓ ^ 2 * (1 - u) ≤ (1 / Real.sqrt (1 - u)) ^ 2 * (1 - u) := by gcongr
      _ = 1 := by rw [div_pow, Real.sq_sqrt h1u.le]; field_simp
  have hsqL : ℓ ^ 2 * (1 - u) ≤ (L : ℝ) ^ 2 * (1 - v) := by
    calc ℓ ^ 2 * (1 - u) ≤ (L : ℝ) ^ 2 * (1 - u) := by gcongr
      _ ≤ (L : ℝ) ^ 2 * (1 - v) := by gcongr
  rcases min_choice (1 / Real.sqrt (1 - v)) (L : ℝ) with h | h <;> rw [h]
  · rw [div_pow, Real.sq_sqrt h1v.le]
    have : 1 / (1 - v) * (1 - v) = 1 := by field_simp
    linarith
  · exact hsqL

/-- `ℓ̂(u) (1-u) ≤ √(1-u)`. -/
theorem ellHat_mul_one_sub_le_sqrt (L : ℕ) {u : ℝ} (hu1 : u < 1) :
    ellHat L (u : ℂ) * (1 - u) ≤ Real.sqrt (1 - u) := by
  have h1u : 0 < 1 - u := by linarith
  have hsu : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 h1u
  rw [ellHat_ofReal L hu1]
  calc min (1 / Real.sqrt (1 - u)) (L : ℝ) * (1 - u) ≤ 1 / Real.sqrt (1 - u) * (1 - u) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) h1u.le
    _ = Real.sqrt (1 - u) := by
        rw [← Real.sq_sqrt h1u.le]
        field_simp
        rw [Real.sq_sqrt h1u.le, Real.sq_sqrt h1u.le]

/-- **The kernel ratio of (5.136)**: with `η_x = (1-x) μ` and `ℓ_u² η_u ≤ ℓ_v² η_v`,
`(ℓ_u/ℓ_v) (ℓ_v η_v/(ℓ_u η_u))² (W ℓ_v η_v)^{-3} ≤ (W ℓ_u η_u)^{-3}`.  Here `a = 1-v`,
`b = 1-u`. -/
theorem kernel_ratio_le {W μ ℓv ℓu a b : ℝ} (hW : 0 < W) (hμ : 0 < μ) (hℓv : 0 < ℓv)
    (hℓu : 0 < ℓu) (ha : 0 < a) (hb : 0 < b) (hmono : ℓu ^ 2 * b ≤ ℓv ^ 2 * a) :
    ℓu / ℓv * (a * ℓv / (b * ℓu)) ^ 2 * (W * ℓv * (a * μ))⁻¹ ^ 3
      ≤ (W * ℓu * (b * μ))⁻¹ ^ 3 := by
  have hr : ℓu ^ 2 * b / (ℓv ^ 2 * a) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hmono
  have e : ℓu / ℓv * (a * ℓv / (b * ℓu)) ^ 2 * (W * ℓv * (a * μ))⁻¹ ^ 3
      = (W * ℓu * (b * μ))⁻¹ ^ 3 * (ℓu ^ 2 * b / (ℓv ^ 2 * a)) := by
    field_simp
  rw [e]
  exact mul_le_of_le_one_right (by positivity) hr

/-- **The time integral of (5.136)**: `∫_s^u η_v^{-1} dv` is a logarithm.  If
`‖f v‖ ≤ α (1-v)^{-1} + β` on `(s, u]`, then `‖∫_s^u f‖ ≤ α log((1-s)/(1-u)) + β (u - s)`. -/
theorem norm_integral_le_log {s u : ℝ} (hsu : s ≤ u) (hu1 : u < 1) {α β : ℝ}
    {f : ℝ → ℂ} (hf : ∀ v ∈ Set.Ioc s u, ‖f v‖ ≤ α * (1 - v)⁻¹ + β) :
    ‖∫ v in s..u, f v‖ ≤ α * Real.log ((1 - s) / (1 - u)) + β * (u - s) := by
  have hcont : ContinuousOn (fun v : ℝ => (1 - v)⁻¹) (Set.uIcc s u) := by
    refine ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun v hv => ?_
    rw [Set.uIcc_of_le hsu] at hv
    have := hv.2
    linarith
  have hint : IntervalIntegrable (fun v : ℝ => (1 - v)⁻¹) volume s u := hcont.intervalIntegrable
  have hlog : ∫ v in s..u, (1 - v)⁻¹ = Real.log ((1 - s) / (1 - u)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) 1]
    refine integral_inv fun h0 => ?_
    rw [Set.uIcc_of_le (by linarith)] at h0
    have := h0.1
    linarith
  refine (intervalIntegral.norm_integral_le_of_norm_le hsu
    (Eventually.of_forall fun v hv => hf v hv)
    ((hint.const_mul α).add intervalIntegrable_const)).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add (hint.const_mul α) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hlog, intervalIntegral.integral_const, smul_eq_mul]
  ring

end Real

/-! ### Lemma 7.3, (7.14), as a hypothesis -/

section Est714

/-- **(7.14) with the constant `C`**, for loops of length `n`: for `0 ≤ s ≤ t < 1`, `|ξᵢ| ≤ 1`,
`K ≥ 1` (the paper's `W^τ`) and an `(ℓ_s K, δ)`-fast-decaying tensor ((7.13), `RBM.FastDecay`)
with `‖A‖_max ≤ M`,
`|(U_{s,t,σ} ∘ A)_a| ≤ C K^n (ℓ_t/ℓ_s) (ℓ_s η_s/(ℓ_t η_t))^n M + (η_s/η_t)^n δ`
(with `η_x = 1 - x`; the factor `Im m` cancels in both ratios).  Proved with `C = cKer n` in
`est714At_cKer` (Lemma 7.3, `RBM.norm_Uker_fastDecay_le`). -/
def Est714At (C : ℝ) (n : ℕ) : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
    ∀ ξ : Fin n → ℂ, (∀ i, ‖ξ i‖ ≤ 1) → ∀ K M δ : ℝ, 1 ≤ K → 0 ≤ M → 0 ≤ δ →
    ∀ A : LoopArg L n → ℂ, (∀ b, ‖A b‖ ≤ M) → FastDecay L (ellHat L (s : ℂ) * K) δ A →
    ∀ a, ‖Uker L ξ (s : ℂ) (t : ℂ) A a‖ ≤
      C * K ^ n * (ellHat L (t : ℂ) / ellHat L (s : ℂ))
        * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) ^ n * M
        + ((1 - s) / (1 - t)) ^ n * δ

/-- **Lemma 7.3, (7.14)** (`RBM.norm_Uker_fastDecay_le`, T51) in the form `Est714At`. -/
theorem est714At_cKer {n : ℕ} (hn : 1 ≤ n) : Est714At (cKer n) n :=
  fun L _ hL _ _ hs0 hst ht1 _ hξ _ _ _ hK hM hδ _ hAM hA a =>
    norm_Uker_fastDecay_le L hn hL hs0 hst ht1 hξ hK hM hδ hAM hA a

theorem cKer_nonneg (n : ℕ) : 0 ≤ cKer n := by
  unfold cKer; have := cWin_nonneg; positivity

end Est714

/-! ### One application of the kernel -/

section Kernel

variable {L : ℕ} [NeZero L] {W E : ℝ}

theorem flowScale_eq_mul (W : ℝ) (L : ℕ) (E x : ℝ) :
    flowScale W L E x = W * ellHat L (x : ℂ) * ((1 - x) * (mE E).im) := rfl

/-- **One kernel step of (5.136)**: `U_{v,u}` applied to a fast-decaying tensor of size
`c w (W ℓ_v η_v)^{-3}` gives `C K² c w (W ℓ_u η_u)^{-3}` plus the tail `(η_v/η_u)² δ`.
This combines (7.14) with the monotonicity `ℓ_u² η_u ≤ ℓ_v² η_v`. -/
theorem kernel_term_le (hL : 3 ≤ L) (hW : 0 < W) (hE : |E| < 2) {C : ℝ} (hC0 : 0 ≤ C)
    (h714 : Est714At C 2) {v u : ℝ} (hv0 : 0 ≤ v) (hvu : v ≤ u) (hu1 : u < 1)
    {ξ : Fin 2 → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1) {K c w δ : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c) (hw : 0 ≤ w)
    (hδ : 0 ≤ δ) {T : LoopArg L 2 → ℂ} (hT : ∀ b, ‖T b‖ ≤ c * w * (flowScale W L E v)⁻¹ ^ 3)
    (hTd : FastDecay L (ellHat L (v : ℂ) * K) δ T) (a : LoopArg L 2) :
    ‖Uker L ξ (v : ℂ) (u : ℂ) T a‖ ≤
      C * K ^ 2 * c * w * (flowScale W L E u)⁻¹ ^ 3 + ((1 - v) / (1 - u)) ^ 2 * δ := by
  have hv1 : v < 1 := hvu.trans_lt hu1
  have hL1 : 1 ≤ L := by omega
  have hℓv := Step3.ellHat_pos_of_lt_one (L := L) hL1 hv1
  have hℓu := Step3.ellHat_pos_of_lt_one (L := L) hL1 hu1
  have hμ := mE_im_pos hE
  have hM : 0 ≤ c * w * (flowScale W L E v)⁻¹ ^ 3 := by
    rw [flowScale_eq_mul]
    have : 0 < 1 - v := by linarith
    positivity
  have h := h714 L hL v u hv0 hvu hu1 ξ hξ K _ δ hK hM hδ T hT hTd a
  refine h.trans (add_le_add ?_ le_rfl)
  have hratio := kernel_ratio_le hW hμ hℓv hℓu (a := 1 - v) (b := 1 - u) (by linarith)
    (by linarith) (ellHat_sq_mul_one_sub_anti L hvu hu1)
  have hCK : 0 ≤ C * K ^ 2 * c * w := by
    have : 0 ≤ K := by linarith
    positivity
  calc C * K ^ 2 * (ellHat L (u : ℂ) / ellHat L (v : ℂ))
        * ((1 - v) * ellHat L (v : ℂ) / ((1 - u) * ellHat L (u : ℂ))) ^ 2
        * (c * w * (flowScale W L E v)⁻¹ ^ 3)
      = C * K ^ 2 * c * w * (ellHat L (u : ℂ) / ellHat L (v : ℂ)
        * ((1 - v) * ellHat L (v : ℂ) / ((1 - u) * ellHat L (u : ℂ))) ^ 2
        * (W * ellHat L (v : ℂ) * ((1 - v) * (mE E).im))⁻¹ ^ 3) := by
        rw [flowScale_eq_mul]; ring
    _ ≤ C * K ^ 2 * c * w * (W * ellHat L (u : ℂ) * ((1 - u) * (mE E).im))⁻¹ ^ 3 :=
        mul_le_mul_of_nonneg_left hratio hCK
    _ = C * K ^ 2 * c * w * (flowScale W L E u)⁻¹ ^ 3 := by rw [flowScale_eq_mul]

/-- **(5.129)–(5.131) ⟹ (5.136) at one final time `u`, deterministic form.**  If the three
tensors of the integrated hierarchy are fast-decaying, with
`‖E(L-K)_s‖_max ≤ c (W ℓ_s η_s)^{-3}` (5.132) and `‖D_v‖_max ≤ c η_v^{-1} (W ℓ_v η_v)^{-3}` for the
two drift tensors ((5.133), (5.135)), then the right side of (5.129)–(5.131) is at most
`C K² c (W ℓ_u η_u)^{-3} (1 + 2 (Im m)^{-1} log((1-s)/(1-u))) + 3 (η_s/η_u)² δ`. -/
theorem core_bound (hL : 3 ≤ L) (hW : 0 < W) (hE : |E| < 2) {C : ℝ} (hC0 : 0 ≤ C)
    (h714 : Est714At C 2) {s u : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (hu1 : u < 1)
    {ξ : Fin 2 → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1) {K c δ : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    {T₀ : LoopArg L 2 → ℂ} {D₁ D₂ : ℝ → LoopArg L 2 → ℂ}
    (hT₀ : ∀ b, ‖T₀ b‖ ≤ c * (flowScale W L E s)⁻¹ ^ 3)
    (hT₀d : FastDecay L (ellHat L (s : ℂ) * K) δ T₀)
    (hD₁ : ∀ v ∈ Set.Icc s u, ∀ b, ‖D₁ v b‖ ≤ c * (etaT E v)⁻¹ * (flowScale W L E v)⁻¹ ^ 3)
    (hD₁d : ∀ v ∈ Set.Icc s u, FastDecay L (ellHat L (v : ℂ) * K) δ (D₁ v))
    (hD₂ : ∀ v ∈ Set.Icc s u, ∀ b, ‖D₂ v b‖ ≤ c * (etaT E v)⁻¹ * (flowScale W L E v)⁻¹ ^ 3)
    (hD₂d : ∀ v ∈ Set.Icc s u, FastDecay L (ellHat L (v : ℂ) * K) δ (D₂ v)) (a : LoopArg L 2) :
    ‖Uker L ξ (s : ℂ) (u : ℂ) T₀ a + (∫ v in s..u, Uker L ξ (v : ℂ) (u : ℂ) (D₁ v) a)
        + ∫ v in s..u, Uker L ξ (v : ℂ) (u : ℂ) (D₂ v) a‖ ≤
      C * K ^ 2 * c * (flowScale W L E u)⁻¹ ^ 3
          * (1 + 2 * ((mE E).im)⁻¹ * Real.log ((1 - s) / (1 - u)))
        + 3 * (((1 - s) / (1 - u)) ^ 2 * δ) := by
  have hμ := mE_im_pos hE
  have h1u : 0 < 1 - u := by linarith
  set Au := (flowScale W L E u)⁻¹ ^ 3 with hAu
  set Q := ((1 - s) / (1 - u)) ^ 2 * δ with hQ
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ 1 - s := by linarith
    positivity
  have hAu0 : 0 ≤ Au := by
    rw [hAu, flowScale_eq_mul]
    have := Step3.ellHat_pos_of_lt_one (L := L) (by omega) hu1
    positivity
  -- the initial term (5.129)
  have h1 : ‖Uker L ξ (s : ℂ) (u : ℂ) T₀ a‖ ≤ C * K ^ 2 * c * Au + Q := by
    have := kernel_term_le hL hW hE hC0 h714 hs0 hsu hu1 hξ hK hc zero_le_one hδ
      (T := T₀) (fun b => by rw [mul_one]; exact hT₀ b) hT₀d a
    simpa only [mul_one] using this
  -- the drift terms (5.130), (5.131)
  set α := C * K ^ 2 * c * ((mE E).im)⁻¹ * Au with hα
  have hdrift : ∀ D : ℝ → LoopArg L 2 → ℂ,
      (∀ v ∈ Set.Icc s u, ∀ b, ‖D v b‖ ≤ c * (etaT E v)⁻¹ * (flowScale W L E v)⁻¹ ^ 3) →
      (∀ v ∈ Set.Icc s u, FastDecay L (ellHat L (v : ℂ) * K) δ (D v)) →
      ‖∫ v in s..u, Uker L ξ (v : ℂ) (u : ℂ) (D v) a‖ ≤ α * Real.log ((1 - s) / (1 - u)) + Q := by
    intro D hD hDd
    have hpt : ∀ v ∈ Set.Ioc s u, ‖Uker L ξ (v : ℂ) (u : ℂ) (D v) a‖ ≤ α * (1 - v)⁻¹ + Q := by
      intro v hv
      have hv' : v ∈ Set.Icc s u := ⟨hv.1.le, hv.2⟩
      have hv0 : 0 ≤ v := hs0.trans hv.1.le
      have h1v : 0 < 1 - v := by linarith [hv.2]
      have hw : 0 ≤ (etaT E v)⁻¹ := inv_nonneg.2 (etaT_pos hE (by linarith)).le
      have := kernel_term_le hL hW hE hC0 h714 hv0 hv.2 hu1 hξ hK hc hw hδ (T := D v)
        (hD v hv') (hDd v hv') a
      refine this.trans (add_le_add (le_of_eq ?_) ?_)
      · rw [hα, show etaT E v = (1 - v) * (mE E).im from rfl, mul_inv]; ring
      · rw [hQ]
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ 2) hδ
        exact div_le_div_of_nonneg_right (by linarith [hv.1]) h1u.le
    refine (norm_integral_le_log hsu hu1 hpt).trans (add_le_add le_rfl ?_)
    calc Q * (u - s) ≤ Q * 1 := mul_le_mul_of_nonneg_left (by linarith) hQ0
      _ = Q := mul_one Q
  have h2 := hdrift D₁ hD₁ hD₁d
  have h3 := hdrift D₂ hD₂ hD₂d
  calc _ ≤ ‖Uker L ξ (s : ℂ) (u : ℂ) T₀ a‖ + ‖∫ v in s..u, Uker L ξ (v : ℂ) (u : ℂ) (D₁ v) a‖
        + ‖∫ v in s..u, Uker L ξ (v : ℂ) (u : ℂ) (D₂ v) a‖ := norm_add₃_le
    _ ≤ (C * K ^ 2 * c * Au + Q) + (α * Real.log ((1 - s) / (1 - u)) + Q)
        + (α * Real.log ((1 - s) / (1 - u)) + Q) := add_le_add (add_le_add h1 h2) h3
    _ = _ := by rw [hα]; ring

/-- The arithmetic that turns (5.136) into `≺ 1`: with `x = N^{τ'} ≥ 1`, `K = W^{τ'} ≤ x`,
`log((1-s)/(1-u)) ≤ 2x/τ'` and the tail `Q² δ ≤ (W ℓ_u η_u)^{-3} = a`, the bound of `core_bound` is
at most `(C (1 + 4/(μτ')) + 3) x⁴ a`. -/
theorem final_arith {C μ τ' x a Q δ K : ℝ} (hC : 0 ≤ C) (hμ : 0 < μ) (hτ' : 0 < τ')
    (hx1 : 1 ≤ x) (ha : 0 ≤ a) (hK0 : 0 ≤ K) (hKx : K ≤ x) (hQ1 : 1 ≤ Q)
    (hlog : Real.log Q ≤ 2 * (x / τ')) (hQδ : Q ^ 2 * δ ≤ a) :
    C * K ^ 2 * x * a * (1 + 2 * μ⁻¹ * Real.log Q) + 3 * (Q ^ 2 * δ)
      ≤ (C * (1 + 4 / (μ * τ')) + 3) * x ^ 4 * a := by
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hx0 : 0 ≤ x := by linarith
  have h1 : 1 + 2 * μ⁻¹ * Real.log Q ≤ x * (1 + 4 / (μ * τ')) := by
    have h2 : 2 * μ⁻¹ * Real.log Q ≤ 2 * μ⁻¹ * (2 * (x / τ')) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have e : 2 * μ⁻¹ * (2 * (x / τ')) = x * (4 / (μ * τ')) := by field_simp; ring
    nlinarith
  have hK2 : K ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hK0 hKx 2
  have hmain : C * K ^ 2 * x * a * (1 + 2 * μ⁻¹ * Real.log Q)
      ≤ C * x ^ 2 * x * a * (x * (1 + 4 / (μ * τ'))) := by
    have : 0 ≤ 1 + 2 * μ⁻¹ * Real.log Q := by positivity
    gcongr
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx1
  have herr : 3 * (Q ^ 2 * δ) ≤ 3 * (x ^ 4 * a) := by nlinarith
  calc _ ≤ C * x ^ 2 * x * a * (x * (1 + 4 / (μ * τ'))) + 3 * (x ^ 4 * a) :=
        add_le_add hmain herr
    _ = (C * (1 + 4 / (μ * τ')) + 3) * x ^ 4 * a := by ring

end Kernel

/-! ### Lemma 5.15: the self-consistent equation (5.128) -/

section SelfConsistent

variable (L : ℕ) [NeZero L]

open Matrix in
/-- **(5.128)**: the self-consistent equation `x_a = ξ ∑_b S_{ba} x_b + y_a` (this is (5.127)
after writing `⟨G E_a⟩ = m + ⟨(G-m) E_a⟩`, with `ξ = u m²`) is solved by inverting
`1 - ξ S^{(B)}`: `x_a = ∑_{a'} (Θ^{(B)}_ξ)_{a a'} y_{a'}`. -/
theorem eq_Theta_of_selfConsistent (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {x y : ZMod L → ℂ}
    (h : ∀ a, x a = ξ * ∑ b, SB L b a * x b + y a) (a : ZMod L) :
    x a = ∑ a', Theta L ξ a a' * y a' := by
  have hy : y = (1 - ξ • SB L) *ᵥ x := by
    funext c
    have hc := h c
    have hm : ((1 - ξ • SB L) *ᵥ x) c = x c - ξ * ∑ b, SB L c b * x b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      simp [Matrix.mulVec, dotProduct]
    rw [hm]
    have e : ∑ b, SB L b c * x b = ∑ b, SB L c b * x b :=
      Finset.sum_congr rfl fun b _ => by rw [SB_apply_comm]
    rw [e] at hc
    linear_combination -hc
  have hx : Theta L ξ *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Theta_mul L hL hξ, Matrix.one_mulVec]
  rw [← hx]
  rfl

/-- The constant of the short-edge bound (3.36): `∑_b |(Θ_{u m²})_{ab}| ≤ cShortRow κ`. -/
noncomputable def cShortRow (κ : ℝ) : ℝ := 2 * cTwo52 * (1 / cZero + 2) / Real.sqrt κ

theorem cShortRow_nonneg (κ : ℝ) : 0 ≤ cShortRow κ := by
  unfold cShortRow
  have := cTwo52_pos
  have := cZero_pos
  positivity

/-- **(5.128) ⟹ (5.126), deterministic part**: for the short edge `ξ = u m²` (`|E| ≤ 2 - κ`),
`Θ_{u m²}` is bounded in `ℓ^∞ → ℓ^∞` uniformly in `u` and `L` ((3.36)), so
`max_a |x_a| ≤ C_κ max_a |y_a|`. -/
theorem norm_selfConsistent_le (hL : 3 ≤ L) {E κ u : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) {x y : ZMod L → ℂ}
    (h : ∀ a, x a = (u : ℂ) * mE E ^ 2 * ∑ b, SB L b a * x b + y a) {M : ℝ}
    (hy : ∀ a, ‖y a‖ ≤ M) (a : ZMod L) : ‖x a‖ ≤ cShortRow κ * M := by
  have hE2 : |E| ≤ 2 := hEκ.trans (by linarith)
  have hξ : ‖(u : ℂ) * mE E ^ 2‖ < 1 := by rw [norm_short_edge hE2 hu0]; exact hu1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hy a)
  rw [eq_Theta_of_selfConsistent L hL hξ h a]
  calc ‖∑ a', Theta L ((u : ℂ) * mE E ^ 2) a a' * y a'‖
      ≤ ∑ a', ‖Theta L ((u : ℂ) * mE E ^ 2) a a'‖ * M := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hy a') (norm_nonneg _)
    _ = (∑ a', ‖Theta L ((u : ℂ) * mE E ^ 2) a a'‖) * M := by rw [Finset.sum_mul]
    _ ≤ cShortRow κ * M :=
        mul_le_mul_of_nonneg_right
          (sum_norm_Theta_short_edge_le L hL hκ0 hκ1 hEκ hu0 hu1 a) hM

/-- The quadratic term of (5.127) is bounded by the `(G-m)(G-m)` expectations:
`|u m ∑_b S_{ba} Z_{ba}| ≤ max |Z|` (`S^{(B)}` is doubly stochastic, `|u m| ≤ 1`). -/
theorem norm_quadTerm_le (hL : 3 ≤ L) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {Z : ZMod L → ZMod L → ℂ} {M : ℝ} (hZ : ∀ b a, ‖Z b a‖ ≤ M) (a : ZMod L) :
    ‖(u : ℂ) * mE E * ∑ b, SB L b a * Z b a‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hZ a a)
  have hum : ‖(u : ℂ) * mE E‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    have := norm_mE hE
    rw [this, mul_one]; exact hu1
  have hrow : ∑ b, ‖SB L b a‖ = 1 := by
    rw [← sum_norm_SB_row hL a]
    exact Finset.sum_congr rfl fun b _ => by rw [SB_apply_comm]
  calc ‖(u : ℂ) * mE E * ∑ b, SB L b a * Z b a‖
      = ‖(u : ℂ) * mE E‖ * ‖∑ b, SB L b a * Z b a‖ := norm_mul _ _
    _ ≤ 1 * (∑ b, ‖SB L b a‖ * M) := by
        refine mul_le_mul hum ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_))
          (norm_nonneg _) zero_le_one
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hZ b a) (norm_nonneg _)
    _ = M := by rw [← Finset.sum_mul, hrow, one_mul, one_mul]

end SelfConsistent

/-! ### The flow: (5.129)–(5.136) ⟹ (2.80) -/

section Flow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The tensor `a ↦ E(L-K)_{u,σ,a}` of the `2`-loops with charges `σ` (the unknown of
(5.129)). -/
noncomputable def lkT (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (σ : Fin 2 → Bool) :
    LoopArg (B.L N) 2 → ℂ :=
  fun a => X.ELval E N u (LoopData.idx (σ, a)) - B.Kval E N u (LoopData.idx (σ, a))

theorem norm_lkT (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (σ : Fin 2 → Bool)
    (a : LoopArg (B.L N) 2) : ‖lkT X E N u σ a‖ = X.expErr E N u (LoopData.idx (σ, a)) := rfl

/-- A time-dependent family of `2`-loop tensors, `(N, v, σ) ↦ (a ↦ D_{v,σ,a})`: the type of the
drift tensors `E E^{((L-K)×(L-K))}_{v,σ}` and `E E^{(G)}_{v,σ}` of (5.130), (5.131). -/
abbrev DriftTensor (B : Band Ω) : Type := ∀ N, ℝ → (Fin 2 → Bool) → LoopArg (B.L N) 2 → ℂ

/-- **(5.129)–(5.131)**: the integrated loop hierarchy (5.20) for `n = 2`, after taking
expectations.  The martingale term `∫ U_{v,u} ∘ E^{(M)}` has vanished (its expectation is `0`),
and for `n = 2` there is no `l_K > 2` term.  `DLK N v σ` stands for `E E^{((L-K)×(L-K))}_{v,σ}`,
`DG N v σ` for `E E^{(G)}_{v,σ}`; they are not defined in Lean (the random layer), only bounded.
The final time `u` ranges over `[s, t]`. -/
def Hierarchy (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (DLK DG : DriftTensor B) : Prop :=
  ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
    lkT X E N u σ a =
      Uker (B.L N) (xiOf (mSigma E) σ) (s N : ℂ) ((u : ℝ) : ℂ) (lkT X E N (s N) σ) a
        + (∫ v in s N..(u : ℝ),
            Uker (B.L N) (xiOf (mSigma E) σ) (v : ℂ) ((u : ℝ) : ℂ) (DLK N v σ) a)
        + ∫ v in s N..(u : ℝ),
            Uker (B.L N) (xiOf (mSigma E) σ) (v : ℂ) ((u : ℝ) : ℂ) (DG N v σ) a

/-- **Fast decay of the tensors of (5.129)–(5.131)** (p. 73: "one can easily see that all tensors
discussed above have fast decay"): for all `τ, D > 0` and large `N`, `E(L-K)_s` is
`(ℓ_s W^τ, W^{-D})`-fast-decaying and the drift tensors at `v ∈ [s,t]` are
`(ℓ_v W^τ, W^{-D})`-fast-decaying ((7.13)). -/
def FastDecayHyp (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (DLK DG : DriftTensor B) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
    FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (lkT X E N (s N) σ) ∧
      ∀ v ∈ Set.Icc (s N) (t N),
        FastDecay (B.L N) (B.ell N v * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D)) (DLK N v σ) ∧
        FastDecay (B.L N) (B.ell N v * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D)) (DG N v σ)

/-- The bound `max_{σ,a} |D_{v,σ,a}| ≺ η_v^{-1} (W ℓ_v η_v)^{-3}`, uniformly in `v ∈ [s,t]`:
the form of (5.133) and (5.135). -/
def DriftBound (B : Band Ω) (E : ℝ) (s t : ℕ → ℝ) (D : DriftTensor B) : Prop :=
  UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => ‖D N p.1 p.2.1 p.2.2‖)
    (fun N p => (etaT E p.1)⁻¹ * (B.scale E N p.1)⁻¹ ^ 3)

theorem norm_xiOf_mSigma_le {E : ℝ} (hE : |E| ≤ 2) (σ : Fin 2 → Bool) (i : Fin 2) :
    ‖xiOf (mSigma E) σ i‖ ≤ 1 := by
  rw [xiOf, norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul]

/-- **(5.129)–(5.136) ⟹ (2.80)**: `max_{u ∈ [s,t]} max_{σ,a} |E(L-K)_{u,σ,a}| ≺ (W ℓ_t η_t)^{-3}`,
in exactly the shape of the field `RBM.Steps.sharpExpect`.  (7.14) is the proved Lemma 7.3
(`est714At_cKer`); the hypotheses are the hierarchy (5.129)–(5.131), fast decay, (5.132)
(= (2.71) at `s`), (5.133), (5.135), and (2.72)
(which gives `W ℓ_u η_u ≥ 1`, hence `1 - u ≥ W^{-2}`, so that the time integral
`∫_s^u η_v^{-1} dv ≍ log((1-s)/(1-u)) ≤ 2 log W` is `≺ 1`). -/
theorem sharpExpect_of_hierarchy (X : Sample B) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    {DLK DG : DriftTensor B} (hH : Hierarchy X E s t DLK DG)
    (hFD : FastDecayHyp X E s t DLK DG)
    (h5132 : UnifDetDom (fun N (u : LoopData (B.L N) 2) => X.expErr E N (s N) u.idx)
      (fun N _ => (B.scale E N (s N))⁻¹ ^ 3))
    (h5133 : DriftBound B E s t DLK) (h5135 : DriftBound B E s t DG) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr E N p.1 p.2.idx)
      (fun N _ => (B.scale E N (t N))⁻¹ ^ 3) := by
  set C := cKer 2 with hCdef
  have hC0 : 0 ≤ C := cKer_nonneg 2
  have hC : Est714At C 2 := est714At_cKer (by norm_num)
  have hμ := mE_im_pos hE
  have hμ1 : (mE E).im ≤ 1 := mE_im_le_one hE
  intro τ hτ
  set τ' := τ / 8 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  set K0 := C * (1 + 4 / ((mE E).im * τ')) + 3 with hK0
  filter_upwards [h5132 τ' hτ'0, h5133 τ' hτ'0, h5135 τ' hτ'0, hFD τ' hτ'0 7 (by norm_num), hc,
    B.dim, eventually_le_rpow K0 (half_pos hτ), eventually_ge_atTop 1]
    with N h1 h2 h3 h4 h5 h6 h7 h8
  rintro ⟨u, σ, a⟩
  set n : ℝ := (N : ℝ) with hn
  set W : ℝ := (B.W N : ℝ) with hWdef
  have hL3 := B.three_le_L N
  have hW1 : 1 ≤ W := B.one_le_W N
  have hW0 : 0 < W := by linarith
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast h8
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hWn : W ≤ n := by
    have hWL : B.W N ≤ B.W N * B.L N := Nat.le_mul_of_pos_right _ (by omega)
    rw [hn, hWdef]; exact_mod_cast hWL.trans h6.1
  have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have h1s : 1 - (u : ℝ) ≤ 1 - s N := by linarith [u.2.1]
  -- the scales: `1 ≤ A_t ≤ A_u ≤ W √(1-u)`
  have hAt0 : 0 < B.scale E N (t N) := flowScale_pos hW0 (by omega) hE (ht1 N)
  have hAu0 : 0 < B.scale E N u := flowScale_pos hW0 (by omega) hE hu1
  have hAt1 : 1 ≤ B.scale E N (t N) := by
    have hr : ((1 - t N) / (1 - s N)) ^ 30 ≤ 1 := by
      have h1t : 0 < 1 - t N := by linarith [ht1 N]
      refine pow_le_one₀ (div_nonneg h1t.le (by linarith [hst N])) ?_
      rw [div_le_one (by linarith [hst N])]; linarith [hst N]
    exact (inv_le_one₀ hAt0).1 (h5.trans hr)
  have hAtu : B.scale E N (t N) ≤ B.scale E N u :=
    flowScale_antitoneOn hW0.le (B.L N) E (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 (ht1 N).le) u.2.2
  have hAu1 : 1 ≤ B.scale E N u := hAt1.trans hAtu
  have hAuW : B.scale E N u ≤ W * Real.sqrt (1 - u) := by
    rw [Band.scale_eq_flowScale, flowScale_eq_mul]
    have h := ellHat_mul_one_sub_le_sqrt (B.L N) hu1
    have hℓ := Step3.ellHat_pos_of_lt_one (L := B.L N) (by omega) hu1
    calc W * ellHat (B.L N) ((u : ℝ) : ℂ) * ((1 - u) * (mE E).im)
        = W * (ellHat (B.L N) ((u : ℝ) : ℂ) * (1 - u)) * (mE E).im := by ring
      _ ≤ W * Real.sqrt (1 - u) * 1 := by gcongr
      _ = W * Real.sqrt (1 - u) := mul_one _
  have hsq1 : Real.sqrt (1 - (u : ℝ)) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hAuW' : B.scale E N u ≤ W := hAuW.trans (by nlinarith)
  have hinvu : (1 - (u : ℝ))⁻¹ ≤ W ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ h1u]
    have := hAu1.trans hAuW
    have h2 : (1 : ℝ) ≤ (W * Real.sqrt (1 - u)) ^ 2 := by nlinarith
    rwa [mul_pow, Real.sq_sqrt h1u.le] at h2
  -- the ratio `Q = (1-s)/(1-u) = η_s/η_u`
  set Q := (1 - s N) / (1 - (u : ℝ)) with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ, one_le_div h1u]; exact h1s
  have hQW : Q ≤ W ^ 2 := by
    rw [hQ, div_eq_mul_inv]
    calc (1 - s N) * (1 - (u : ℝ))⁻¹ ≤ 1 * W ^ 2 :=
          mul_le_mul (by linarith [hs0 N]) hinvu (inv_nonneg.2 h1u.le) zero_le_one
      _ = W ^ 2 := one_mul _
  have hlog : Real.log Q ≤ 2 * (n ^ τ' / τ') := by
    have hlogn := Real.log_le_rpow_div hn0 hτ'0
    calc Real.log Q ≤ Real.log (n ^ 2) :=
          Real.log_le_log (by linarith) (hQW.trans (pow_le_pow_left₀ hW0.le hWn 2))
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
      _ ≤ 2 * (n ^ τ' / τ') := by linarith
  -- the tail `Q² W^{-7} ≤ (W ℓ_u η_u)^{-3}`
  have hδ : W ^ (-(7 : ℝ)) = (W ^ 7)⁻¹ := by
    rw [Real.rpow_neg hW0.le, ← Real.rpow_natCast]; norm_num
  have hQδ : Q ^ 2 * W ^ (-(7 : ℝ)) ≤ (B.scale E N u)⁻¹ ^ 3 := by
    rw [hδ, inv_pow]
    calc Q ^ 2 * (W ^ 7)⁻¹ ≤ (W ^ 2) ^ 2 * (W ^ 7)⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hQW 2) (by positivity)
      _ = (W ^ 3)⁻¹ := by field_simp
      _ ≤ (B.scale E N u ^ 3)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hAu0.le hAuW' 3)
  -- `K = W^{τ'} ≤ x = N^{τ'}`, `x⁴ = N^{τ/2}`
  have hKx : W ^ τ' ≤ n ^ τ' := Real.rpow_le_rpow hW0.le hWn hτ'0.le
  have hK1 : 1 ≤ W ^ τ' := Real.one_le_rpow hW1 hτ'0.le
  have hx1 : 1 ≤ n ^ τ' := Real.one_le_rpow hn1 hτ'0.le
  have hx4 : (n ^ τ') ^ 4 = n ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]; congr 1; rw [hτ']; push_cast; ring
  -- the hierarchy and the deterministic bound
  have hξ : ∀ i, ‖xiOf (mSigma E) σ i‖ ≤ 1 := norm_xiOf_mSigma_le hE.le σ
  have hcore := core_bound (L := B.L N) (W := W) (E := E) hL3 hW0 hE hC0 hC (hs0 N) u.2.1 hu1
    hξ (K := W ^ τ') (c := n ^ τ') (δ := W ^ (-(7 : ℝ))) hK1 (by positivity) (by positivity)
    (T₀ := lkT X E N (s N) σ) (D₁ := fun v => DLK N v σ) (D₂ := fun v => DG N v σ)
    (fun b => h1 (σ, b)) (h4 σ).1
    (fun v hv b => (h2 (⟨v, hv.1, hv.2.trans u.2.2⟩, (σ, b))).trans
      (le_of_eq (mul_assoc _ _ _).symm))
    (fun v hv => ((h4 σ).2 v ⟨hv.1, hv.2.trans u.2.2⟩).1)
    (fun v hv b => (h3 (⟨v, hv.1, hv.2.trans u.2.2⟩, (σ, b))).trans
      (le_of_eq (mul_assoc _ _ _).symm))
    (fun v hv => ((h4 σ).2 v ⟨hv.1, hv.2.trans u.2.2⟩).2) a
  have harith := final_arith hC0 hμ hτ'0 hx1 (by positivity) (by positivity) hKx hQ1 hlog hQδ
  show X.expErr E N u (LoopData.idx (σ, a)) ≤ n ^ τ * (B.scale E N (t N))⁻¹ ^ 3
  rw [← norm_lkT, hH N u σ a]
  refine hcore.trans (harith.trans ?_)
  rw [hx4]
  have ha : (B.scale E N u)⁻¹ ^ 3 ≤ (B.scale E N (t N))⁻¹ ^ 3 :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ hAt0 hAtu) 3
  calc K0 * n ^ (τ / 2) * (B.scale E N u)⁻¹ ^ 3
      ≤ n ^ (τ / 2) * n ^ (τ / 2) * (B.scale E N (t N))⁻¹ ^ 3 := by
        gcongr
    _ = n ^ τ * (B.scale E N (t N))⁻¹ ^ 3 := by
        rw [hn, UnifDetDom.rpow_half_mul_rpow_half N hτ]

/-! ### Lemma 5.15 and (5.133)–(5.135) for the flow -/

/-- The `1`-loop with charge `+` at the block `a`: `L_{u,(+),(a)} = ⟨G_u E_a⟩`. -/
def oneLoop {L : ℕ} (a : ZMod L) : LoopIdx (ZMod L) := ⟨[true], [a]⟩

/-- `E(L-K)_{u,(+),(a)} = E⟨(G_u - m) E_a⟩`, the quantity of (5.126). -/
noncomputable def lk1 (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (a : ZMod (B.L N)) : ℂ :=
  X.ELval E N u (oneLoop a) - B.Kval E N u (oneLoop a)

/-- `E[⟨(G_u - m) E_b⟩ ⟨(G_u - m) E_a⟩]`, the quadratic term of (5.127)/(5.128). -/
noncomputable def quad11 (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (b a : ZMod (B.L N)) : ℂ :=
  ∫ ω, (X.Lval E N u ω (oneLoop b) - B.Kval E N u (oneLoop b)) *
    (X.Lval E N u ω (oneLoop a) - B.Kval E N u (oneLoop a)) ∂B.P

/-- `E[⟨(G_u - m) E_{a₁}⟩ L_{u,σ',a'}]` for a `3`-loop `(σ', a')`: the quantity of (5.134). -/
noncomputable def mix13 (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (a₁ : ZMod (B.L N))
    (w : LoopData (B.L N) 3) : ℂ :=
  ∫ ω, (X.Lval E N u ω (oneLoop a₁) - B.Kval E N u (oneLoop a₁)) * X.Lval E N u ω w.idx ∂B.P

/-- `E[(L-K)_{u,(+),(a₁)} (L-K)_{u,σ',a'}]`, the second term of the splitting (5.134). -/
noncomputable def quad13 (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (a₁ : ZMod (B.L N))
    (w : LoopData (B.L N) 3) : ℂ :=
  ∫ ω, (X.Lval E N u ω (oneLoop a₁) - B.Kval E N u (oneLoop a₁)) *
    (X.Lval E N u ω w.idx - B.Kval E N u w.idx) ∂B.P

/-- **(5.127)**, after writing `⟨G E_a⟩ = m + ⟨(G-m) E_a⟩` (Gaussian integration by parts; the
random layer, taken as a hypothesis):
`E⟨(G-m)E_a⟩ = u m² ∑_b S_{ba} E⟨(G-m)E_b⟩ + u m ∑_b S_{ba} E[⟨(G-m)E_b⟩⟨(G-m)E_a⟩]`. -/
def Eq527 (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ N (u : TimeIcc s t N) (a : ZMod (B.L N)),
    lk1 X E N u a = ((u : ℝ) : ℂ) * mE E ^ 2 * ∑ b, SB (B.L N) b a * lk1 X E N u b
      + ((u : ℝ) : ℂ) * mE E * ∑ b, SB (B.L N) b a * quad11 X E N u b a

/-- **Lemma 5.15, (5.126)**: `max_a |E⟨(G_u - m) E_a⟩| ≺ (W ℓ_u η_u)^{-2}`, uniformly in
`u ∈ [s,t]`, from (5.127) and the bound `E[⟨(G-m)E_b⟩⟨(G-m)E_a⟩] ≺ (W ℓ_u η_u)^{-2}` (which is
(2.78) for `n = 1`, twice, in expectation).  The proof is (5.128): invert `1 - u m² S^{(B)}`
(`eq_Theta_of_selfConsistent`) and use that `Θ_{u m²}` is bounded ((3.36), short edge). -/
theorem lemma515 (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (h527 : Eq527 X E s t)
    (hquad : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖quad11 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 2)) :
    UnifDetDom (fun N (p : TimeIcc s t N × ZMod (B.L N)) => ‖lk1 X E N p.1 p.2‖)
      (fun N p => (B.scale E N p.1)⁻¹ ^ 2) := by
  have hE2 : |E| ≤ 2 := hEκ.trans (by linarith)
  intro τ hτ
  filter_upwards [hquad (τ / 2) (half_pos hτ), eventually_le_rpow (cShortRow κ) (half_pos hτ)]
    with N hN hc
  rintro ⟨u, a⟩
  have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  set M := (N : ℝ) ^ (τ / 2) * (B.scale E N u)⁻¹ ^ 2 with hM
  have hy : ∀ a', ‖((u : ℝ) : ℂ) * mE E * ∑ b, SB (B.L N) b a' * quad11 X E N u b a'‖ ≤ M :=
    fun a' => norm_quadTerm_le (B.L N) (B.three_le_L N) hE2 hu0 hu1.le
      (fun b a'' => hN (u, (b, a''))) a'
  have hx := norm_selfConsistent_le (B.L N) (B.three_le_L N) hκ0 hκ1 hEκ hu0 hu1
    (x := lk1 X E N u)
    (y := fun a' => ((u : ℝ) : ℂ) * mE E * ∑ b, SB (B.L N) b a' * quad11 X E N u b a')
    (h527 N u) hy a
  have hM0 : 0 ≤ M := by positivity
  calc ‖lk1 X E N u a‖ ≤ cShortRow κ * M := hx
    _ ≤ (N : ℝ) ^ (τ / 2) * M := mul_le_mul_of_nonneg_right hc hM0
    _ = (N : ℝ) ^ τ * (B.scale E N u)⁻¹ ^ 2 := by
        rw [hM, ← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half N hτ]

/-- `W ℓ_v (W ℓ_v η_v)^{-4} = η_v^{-1} (W ℓ_v η_v)^{-3}`: the rewriting in (5.133), (5.135). -/
theorem W_mul_ell_mul_scale_inv_pow_four {E : ℝ} (hE : |E| < 2) (N : ℕ) {v : ℝ} (hv1 : v < 1) :
    (B.W N : ℝ) * B.ell N v * (B.scale E N v)⁻¹ ^ 4 =
      (etaT E v)⁻¹ * (B.scale E N v)⁻¹ ^ 3 := by
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hℓ : 0 < B.ell N v := Step3.ellHat_pos_of_lt_one (by have := B.three_le_L N; omega) hv1
  have hη : 0 < etaT E v := etaT_pos hE hv1
  simp only [Band.scale]
  field_simp

/-- **(5.133)**: `E E^{((L-K)×(L-K))}_{u,σ} ≺ W ℓ_u (W ℓ_u η_u)^{-4}`, which is
`η_u^{-1} (W ℓ_u η_u)^{-3}`. -/
theorem driftBound_of_5133 {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1)
    {D : DriftTensor B}
    (h : UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => ‖D N p.1 p.2.1 p.2.2‖)
      (fun N p => (B.W N : ℝ) * B.ell N p.1 * (B.scale E N p.1)⁻¹ ^ 4)) :
    DriftBound B E s t D :=
  h.congr_eventually (Eventually.of_forall fun _ => rfl) (Eventually.of_forall fun N =>
    funext fun p => W_mul_ell_mul_scale_inv_pow_four hE N (p.1.2.2.trans_lt (ht1 N)))

/-- **The splitting of (5.134)**: writing `L = K + (L - K)` in the `3`-loop,
`E[⟨(G-m)E_{a₁}⟩ L_{3}] = E⟨(G-m)E_{a₁}⟩ K_3 + E[(L-K)_1 (L-K)_3]` (`K` is deterministic). -/
theorem mix13_eq (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (a₁ : ZMod (B.L N))
    (w : LoopData (B.L N) 3)
    (h1 : Integrable (fun ω => X.Lval E N u ω (oneLoop a₁)) B.P)
    (h2 : Integrable (fun ω => (X.Lval E N u ω (oneLoop a₁) - B.Kval E N u (oneLoop a₁)) *
      (X.Lval E N u ω w.idx - B.Kval E N u w.idx)) B.P) :
    mix13 X E N u a₁ w = lk1 X E N u a₁ * B.Kval E N u w.idx + quad13 X E N u a₁ w := by
  have := B.isProbabilityMeasure
  have hsub : Integrable (fun ω => X.Lval E N u ω (oneLoop a₁) - B.Kval E N u (oneLoop a₁)) B.P :=
    h1.sub (integrable_const _)
  have hpt : (fun ω => (X.Lval E N u ω (oneLoop a₁) - B.Kval E N u (oneLoop a₁)) *
      X.Lval E N u ω w.idx) = fun ω =>
      (X.Lval E N u ω (oneLoop a₁) - B.Kval E N u (oneLoop a₁)) * B.Kval E N u w.idx +
      (X.Lval E N u ω (oneLoop a₁) - B.Kval E N u (oneLoop a₁)) *
        (X.Lval E N u ω w.idx - B.Kval E N u w.idx) := by
    funext ω; ring
  unfold mix13
  rw [hpt, integral_add (hsub.mul_const _) h2, integral_mul_const,
    integral_sub h1 (integrable_const _), integral_const]
  simp [lk1, quad13, Sample.ELval]

/-- **(5.134) ⟹ (5.135)**: `E E^{(G)}_{u,σ} ≺ η_u^{-1} (W ℓ_u η_u)^{-3}`.  Inputs: the structural
bound (5.134) `|E E^{(G)}| ≤ C W ℓ_u max |E[⟨(G-m)E_{a₁}⟩ L_{u,σ',a'}]|` (random layer, as a
hypothesis `hG`), integrability, (5.126) for `E⟨(G-m)E_a⟩`, (2.59) for `K` (proved:
`RBM.Band.norm_Kval_le`), and `E[(L-K)_1 (L-K)_3] ≺ (W ℓ_u η_u)^{-4}` ((2.78) for `n = 1, 3`, in
expectation). -/
theorem driftBound_of_5134 (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {DG : DriftTensor B}
    (hG : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ N (v : TimeIcc s t N) (σ : Fin 2 → Bool)
      (a : LoopArg (B.L N) 2) (Λ : ℝ),
      (∀ a₁ (w : LoopData (B.L N) 3), ‖mix13 X E N v a₁ w‖ ≤ Λ) →
        ‖DG N v σ a‖ ≤ Cg * ((B.W N : ℝ) * B.ell N v * Λ))
    (hint1 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N v ω (oneLoop a₁)) B.P)
    (hint2 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)) (w : LoopData (B.L N) 3),
      Integrable (fun ω => (X.Lval E N v ω (oneLoop a₁) - B.Kval E N v (oneLoop a₁)) *
        (X.Lval E N v ω w.idx - B.Kval E N v w.idx)) B.P)
    (h526 : UnifDetDom (fun N (p : TimeIcc s t N × ZMod (B.L N)) => ‖lk1 X E N p.1 p.2‖)
      (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hq : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × LoopData (B.L N) 3)) =>
      ‖quad13 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 4)) :
    DriftBound B E s t DG := by
  obtain ⟨Cg, hCg0, hG⟩ := hG
  obtain ⟨CK, hCK0, hCK⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 3) (by norm_num)
  have hE : |E| < 2 := by linarith
  intro τ hτ
  filter_upwards [h526 (τ / 2) (half_pos hτ), hq (τ / 2) (half_pos hτ),
    eventually_le_rpow (Cg * (CK + 1)) (half_pos hτ)] with N h1 h2 h3
  rintro ⟨v, σ, a⟩
  have hv0 : 0 ≤ (v : ℝ) := (hs0 N).trans v.2.1
  have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
  set x := (N : ℝ) ^ (τ / 2) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg N) _
  set Ai := (B.scale E N v)⁻¹ with hAi
  have hAi0 : 0 ≤ Ai := inv_nonneg.2 (B.scale_nonneg E N hv1.le)
  set Λ := x * (CK + 1) * Ai ^ 4 with hΛ
  have hmix : ∀ a₁ (w : LoopData (B.L N) 3), ‖mix13 X E N v a₁ w‖ ≤ Λ := by
    intro a₁ w
    rw [mix13_eq X E N v a₁ w (hint1 N v a₁) (hint2 N v a₁ w)]
    have hK : ‖B.Kval E N v w.idx‖ ≤ CK * Ai ^ 2 := by
      have := hCK N v hv0 hv1 w.idx w.idx_wf (by simp)
      rwa [hAi]
    have hl : ‖lk1 X E N v a₁‖ ≤ x * Ai ^ 2 := h1 (v, a₁)
    have hqq : ‖quad13 X E N v a₁ w‖ ≤ x * Ai ^ 4 := h2 (v, (a₁, w))
    calc ‖lk1 X E N v a₁ * B.Kval E N v w.idx + quad13 X E N v a₁ w‖
        ≤ ‖lk1 X E N v a₁‖ * ‖B.Kval E N v w.idx‖ + ‖quad13 X E N v a₁ w‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ x * Ai ^ 2 * (CK * Ai ^ 2) + x * Ai ^ 4 := by
          gcongr
      _ = Λ := by rw [hΛ]; ring
  have hD := hG N v σ a Λ hmix
  have hid := W_mul_ell_mul_scale_inv_pow_four (B := B) hE N hv1
  calc ‖DG N v σ a‖ ≤ Cg * ((B.W N : ℝ) * B.ell N v * Λ) := hD
    _ = Cg * (CK + 1) * x * ((B.W N : ℝ) * B.ell N v * Ai ^ 4) := by rw [hΛ]; ring
    _ = Cg * (CK + 1) * x * ((etaT E v)⁻¹ * Ai ^ 3) := by rw [hAi, hid]
    _ ≤ x * x * ((etaT E v)⁻¹ * Ai ^ 3) := by
        have : 0 ≤ (etaT E v)⁻¹ * Ai ^ 3 :=
          mul_nonneg (inv_nonneg.2 (etaT_pos hE hv1).le) (by positivity)
        gcongr
    _ = (N : ℝ) ^ τ * ((etaT E v)⁻¹ * (B.scale E N v)⁻¹ ^ 3) := by
        rw [hx, UnifDetDom.rpow_half_mul_rpow_half N hτ]

/-- **Step 6 of Theorem 2.21: (2.80)**, all pieces assembled, in exactly the shape of the field
`RBM.Steps.sharpExpect`:
`max_{u ∈ [s,t]} max_{σ ∈ {+,-}², a} |E L_{u,σ,a} - K_{u,σ,a}| ≺ (W ℓ_t η_t)^{-3}`.

Hypotheses (all from the random layer or from Steps 4–5; none is an `axiom`):
* `hH`, `hFD` — (5.129)–(5.131) (expectation of (5.20), martingale term vanishing) and the fast
  decay of the three tensors;
* `h5132` — (5.132) = (2.71) at `s` (the field `RBM.Bounds.expect`);
* `h5133` — (5.133) `E E^{((L-K)×(L-K))} ≺ W ℓ_u (W ℓ_u η_u)^{-4}`;
* `h527`, `hq11` — (5.127) and `E[(L-K)_1 (L-K)_1] ≺ (W ℓ_u η_u)^{-2}`, giving (5.126) by
  Lemma 5.15 (`lemma515`);
* `hG`, `hint1`, `hint2`, `hq13` — the structural bound (5.134), integrability, and
  `E[(L-K)_1 (L-K)_3] ≺ (W ℓ_u η_u)^{-4}`, giving (5.135);
* (2.72) `hc`.
(7.14) is Lemma 7.3 (proved, `est714At_cKer`); (2.59) is `RBM.Band.norm_Kval_le` (proved). -/
theorem sharpExpect_step6 (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {DLK DG : DriftTensor B}
    (hH : Hierarchy X E s t DLK DG) (hFD : FastDecayHyp X E s t DLK DG)
    (h5132 : UnifDetDom (fun N (u : LoopData (B.L N) 2) => X.expErr E N (s N) u.idx)
      (fun N _ => (B.scale E N (s N))⁻¹ ^ 3))
    (h5133 : UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) =>
      ‖DLK N p.1 p.2.1 p.2.2‖) (fun N p => (B.W N : ℝ) * B.ell N p.1 * (B.scale E N p.1)⁻¹ ^ 4))
    (h527 : Eq527 X E s t)
    (hq11 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖quad11 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hG : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ N (v : TimeIcc s t N) (σ : Fin 2 → Bool)
      (a : LoopArg (B.L N) 2) (Λ : ℝ),
      (∀ a₁ (w : LoopData (B.L N) 3), ‖mix13 X E N v a₁ w‖ ≤ Λ) →
        ‖DG N v σ a‖ ≤ Cg * ((B.W N : ℝ) * B.ell N v * Λ))
    (hint1 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N v ω (oneLoop a₁)) B.P)
    (hint2 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)) (w : LoopData (B.L N) 3),
      Integrable (fun ω => (X.Lval E N v ω (oneLoop a₁) - B.Kval E N v (oneLoop a₁)) *
        (X.Lval E N v ω w.idx - B.Kval E N v w.idx)) B.P)
    (hq13 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × LoopData (B.L N) 3)) =>
      ‖quad13 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 4)) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr E N p.1 p.2.idx)
      (fun N _ => (B.scale E N (t N))⁻¹ ^ 3) := by
  have hE : |E| < 2 := by linarith
  have h526 := lemma515 X hκ0 hκ1 hEκ hs0 ht1 h527 hq11
  exact sharpExpect_of_hierarchy X hE hs0 hst ht1 hc hH hFD h5132
    (driftBound_of_5133 hE ht1 h5133)
    (driftBound_of_5134 X hκ0 hκ1 hEκ hs0 ht1 hG hint1 hint2 h526 hq13)

end Flow

end Step6

end RBM
