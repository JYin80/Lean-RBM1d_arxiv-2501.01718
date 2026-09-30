/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.SumZeroDyn
import RBM1D.Hierarchy.Step1
import RBM1D.Gauss.Step2JStar

/-!
# Step 2 of the proof of Theorem 2.21: (2.75) and (2.76)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.3: the tail
functions (5.26)–(5.29), Lemma 5.6, the bound (5.34) of Lemma 5.7, the estimates (5.39)–(5.41)
of the stopped hierarchy, the stopping time (5.43), the conclusion (5.47), and from it (2.76)
`|(L-K)_{u,(+,-),a}| ≺ (η_s/η_u)⁴ (W ℓ_u η_u)^{-2} (e^{-(|a₁-a₂|/ℓ_u)^{1/2}} + W^{-D})` and
(2.75) `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/2}`.

**The logical core is a self-improving inequality, not Grönwall**: if the
bound `J* ≤ Λ` up to time `v` implies the better bound `J*(v) ≤ B(v) < Λ(v)`, and `J*` is
continuous, then `J* ≤ B` on all of `[s, t]`.  The stochastic part only has to supply that
implication on one high-probability event.

## Deterministic results

* `jStar` **(5.29)** (with `RBM.tailT` (5.27) of `Analysis/StretchedExp.lean`);
  `le_jStar_mul`: `f ≤ J* T` (the definitional content of (5.31)); `jStar_le`.
* `eLL`, `norm_eLL_le` — **(5.34)**: `|E^{((L-K)×(L-K))}_a| ≤ e (J*)² (36 η^{-1}(Wℓη)^{-1} +
  W L W^{-D}) T(|a₁ - a₂|)` (via the convolution bound (5.50), `RBM.mul_sum_tailT_mul_tailT_le`).
* `norm_Uker_le_of_tail` — the kernel estimate behind **(5.39)–(5.41)**, from Lemma 7.1
  (`RBM.norm_Uker_apply_le`) and (7.2) (`RBM.norm_Uker_tail_le_ellStar`):
  `|A_b| ≤ M T_u(|b₁-b₂|)` implies `|(U_{u,v} ∘ A)_a| ≤ M (η_u/η_v)² Ξ T_v(|a₁-a₂|)`,
  `Ξ = xiK = W^{o(1)}`.
* `cStep` — the constant of the arithmetic of (5.40)–(5.47).
* `norm_Theta_le_of_ellStar`, `norm_oneSub_mul_Theta_le` — **Lemma 5.6, (5.30)**.
  (5.32) is `RBM.tailT_sub_le`.

## The flow

* `sigPM` (`σ = (+,-)`), `lk` (`(L-K)_{u,σ}`), `tT` (`T_{u,D}`), `jS` (`J*_{u,D}`), defined in
  `RBM1D/Gauss/Step2JStar.lean`; `thr` (the threshold `Λ(u) = N^δ (η_s/η_u)⁴`).
* `decayProf_le_tT`, `tT_le_decayProf` — (2.69) in the tail-function form, and the domination
  of the tail function (5.27) by the right side of (2.76).
* `stochDom_rpow_half_of_sq` — `ξ² ≺ ζ` implies `ξ ≺ ζ^{1/2}`, the step from (2.76) to (2.75).

## Deviations from the paper

* **Threshold and stopping time.**  (5.43) uses the time-dependent threshold
  `Λ(u) = N^δ (η_s/η_u)⁴` (`δ > 0` small, arbitrary) instead of `N^δ (η_s/η_t)⁴`, and
  `T = inf{u : J*_u > Λ(u)}`.  The factor `N^δ` gives the room that `≺` needs to contradict
  `J*_T ≥ Λ(T)`; the dependence on `u` gives (2.76) at every `u ∈ [s,t]` with `(η_s/η_u)⁴`
  directly (no net over final times).
* The bootstrap (5.43)–(5.47) is concluded in the form `J*_{u,D} ≺ (η_s/η_u)⁴` (which is
  exactly what (2.76) needs), not in the form of (5.47); (5.48) is not derived.
* **(5.34)** holds with the explicit constant `e (36 + …)` and `T_{u,D}` on both sides.
* **(5.39)–(5.41)**: the kernel bound loses `Ξ = W^{o(1)}` and uses `(η_u/η_v)²` in place of the
  paper's `(ℓ_t/ℓ_s)² 1(|a₁-a₂| ≤ ℓ*_t) + 1`; the `du`-integral is bounded by length × sup.
* `J*` is defined as `max_a f(a)/T(|a₁-a₂|) + 1` and shown to equal `max_ℓ J(ℓ)`.
* (5.30) for `Θ_s^{-1} Θ_t` is stated for `(1 - s S^{(B)}) Θ_t` (= `Θ_s^{-1} Θ_t`,
  `RBM.mul_Theta`).
* `eLL` is written directly from the proof of (5.34).
* Scales: `η_u = etaT E u = (1 - u) Im m`, `ℓ_u = ℓ̂(u)`.
-/

namespace RBM

namespace Step2

open Finset Real MeasureTheory Filter
open scoped Matrix.Norms.Operator

/-! ### The tail functions (5.26)–(5.29) -/

section Tail

variable (L : ℕ) [NeZero L]

variable {L}
variable {f : LoopArg L 2 → ℝ}

variable {W ℓu ηu D : ℝ}

theorem div_le_jStar_sub_one (a : LoopArg L 2) :
    f a / tailT W ℓu ηu D (zdist L (a 0 - a 1)) ≤ jStar L f W ℓu ηu D - 1 := by
  have := Finset.le_sup' (fun a => f a / tailT W ℓu ηu D (zdist L (a 0 - a 1)))
    (Finset.mem_univ a)
  rw [jStar]; linarith

theorem le_jStar_sub_one_mul (hW : 0 < W) (a : LoopArg L 2) :
    f a ≤ (jStar L f W ℓu ηu D - 1) * tailT W ℓu ηu D (zdist L (a 0 - a 1)) := by
  have hT := tailT_pos (ℓu := ℓu) (ηu := ηu) (D := D) hW (zdist L (a 0 - a 1) : ℝ)
  have := div_le_jStar_sub_one (f := f) (W := W) (ℓu := ℓu) (ηu := ηu) (D := D) a
  rwa [div_le_iff₀ hT] at this

theorem one_le_jStar (hW : 0 < W) (hf : ∀ a, 0 ≤ f a) : 1 ≤ jStar L f W ℓu ηu D := by
  have hT := tailT_pos (ℓu := ℓu) (ηu := ηu) (D := D) hW
  have := div_le_jStar_sub_one (f := f) (W := W) (ℓu := ℓu) (ηu := ηu) (D := D)
    (0 : LoopArg L 2)
  have h0 := div_nonneg (hf (0 : LoopArg L 2)) (hT (zdist L ((0 : LoopArg L 2) 0 -
      (0 : LoopArg L 2) 1) : ℝ)).le
  linarith

/-- **`f ≤ J* T`**, the content of (5.31) for `L - K`. -/
theorem le_jStar_mul (hW : 0 < W) (a : LoopArg L 2) :
    f a ≤ jStar L f W ℓu ηu D * tailT W ℓu ηu D (zdist L (a 0 - a 1)) := by
  have h := le_jStar_sub_one_mul (f := f) (ℓu := ℓu) (ηu := ηu) (D := D) hW a
  have hT := tailT_pos (ℓu := ℓu) (ηu := ηu) (D := D) hW (zdist L (a 0 - a 1) : ℝ)
  nlinarith

/-- A bound `f ≤ c T` gives `J* ≤ c + 1`. -/
theorem jStar_le (hW : 0 < W) {c : ℝ}
    (hc : ∀ a, f a ≤ c * tailT W ℓu ηu D (zdist L (a 0 - a 1))) :
    jStar L f W ℓu ηu D ≤ c + 1 := by
  have : Finset.univ.sup' Finset.univ_nonempty
      (fun a => f a / tailT W ℓu ηu D (zdist L (a 0 - a 1))) ≤ c := by
    refine Finset.sup'_le _ _ fun a _ => ?_
    rw [div_le_iff₀ (tailT_pos hW _)]; exact hc a
  rw [jStar]; linarith

end Tail


/-! ### (5.34): the quadratic term -/

section E534

variable (L : ℕ) [NeZero L]

/-- The quadratic term `E^{((L-K)×(L-K))}` of (5.13) for a `2`-loop, as written in the proof
of (5.34): `(E^{((L-K)×(L-K))})_a = W ∑_{b₁,b₂} A_{(a₁,b₁)} S^{(B)}_{b₁b₂} A_{(b₂,a₂)}`. -/
noncomputable def eLL (W : ℝ) (A : LoopArg L 2 → ℂ) : LoopArg L 2 → ℂ :=
  fun a => (W : ℂ) * ∑ b₁ : ZMod L, ∑ b₂ : ZMod L, A ![a 0, b₁] * SB L b₁ b₂ * A ![b₂, a 1]

variable {L}

/-- Shifting the argument of `T_{u,D}` by one costs at most a factor `e` (for `ℓ_u ≥ 1`). -/
theorem tailT_sub_one_le {W ℓu ηu D : ℝ} (hW : 0 ≤ W) (hℓu : 1 ≤ ℓu) (x : ℝ) :
    tailT W ℓu ηu D (x - 1) ≤ exp 1 * tailT W ℓu ηu D x := by
  have hℓ : 0 < ℓu := by linarith
  have hsplit : x / ℓu = (x - 1) / ℓu + 1 / ℓu := by field_simp; ring
  have h1 : √(x / ℓu) ≤ √((x - 1) / ℓu) + 1 := by
    rw [hsplit]
    refine (sqrt_add_le_add_sqrt _ (by positivity)).trans ?_
    have : √(1 / ℓu) ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one hℓ).2 hℓu)
    linarith
  have hexp : exp (-√((x - 1) / ℓu)) ≤ exp 1 * exp (-√(x / ℓu)) := by
    rw [← exp_add, exp_le_exp]; linarith
  have hA : 0 ≤ ((W * ℓu * ηu) ^ 2)⁻¹ := by positivity
  have hε : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW _
  have he : 1 ≤ exp 1 := Real.one_le_exp (by norm_num)
  unfold tailT
  have := mul_le_mul_of_nonneg_left hexp hA
  nlinarith

/-- **(5.34)**, deterministic form.  If `|A_b| ≤ J* T_{u,D}(‖b₁ - b₂‖)` (the definition of
`J* = J*_{u,D}`), then
`|E^{((L-K)×(L-K))}_a| ≤ e (J*)² (36 η_u^{-1} (W ℓ_u η_u)^{-1} + W L W^{-D}) T_{u,D}(‖a₁ - a₂‖)`.
(The paper divides by `T_{t,D} ≥ T_{u,D}`; the `W L W^{-D}` term is negligible for large `D`.) -/
theorem norm_eLL_le (hL : 3 ≤ L) {W ℓu ηu : ℝ} (hW : 0 < W) (hℓu : 1 ≤ ℓu) (hη : 0 < ηu)
    (D : ℝ) (A : LoopArg L 2 → ℂ) (a : LoopArg L 2) :
    ‖eLL L W A a‖ ≤ exp 1 * jStar L (fun b => ‖A b‖) W ℓu ηu D ^ 2 *
      (36 * (ηu⁻¹ * (W * ℓu * ηu)⁻¹) + W * L * W ^ (-D)) *
      tailT W ℓu ηu D (zdist L (a 0 - a 1)) := by
  set J := jStar L (fun b => ‖A b‖) W ℓu ηu D with hJdef
  set T : ℝ → ℝ := tailT W ℓu ηu D with hTdef
  have hℓ : 0 < ℓu := by linarith
  have hJ1 : 1 ≤ J := one_le_jStar hW (fun b => norm_nonneg _)
  have hA : ∀ b : LoopArg L 2, ‖A b‖ ≤ J * T (zdist L (b 0 - b 1)) :=
    fun b => le_jStar_mul (f := fun b => ‖A b‖) hW b
  have hT0 : ∀ x, 0 ≤ T x := fun x => tailT_nonneg hW.le x
  have he : 0 < exp 1 := exp_pos 1
  -- the right factor, after the `S^{(B)}` sum
  have hright : ∀ b₁ : ZMod L, ∑ b₂ : ZMod L, ‖SB L b₁ b₂‖ * ‖A ![b₂, a 1]‖
      ≤ exp 1 * J * T (zdist L (a 1 - b₁)) := by
    intro b₁
    have hpt : ∀ b₂, ‖SB L b₁ b₂‖ * ‖A ![b₂, a 1]‖ ≤
        ‖SB L b₁ b₂‖ * (exp 1 * J * T (zdist L (a 1 - b₁))) := by
      intro b₂
      by_cases hS : SB L b₁ b₂ = 0
      · simp [hS]
      · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hd : zdist L (b₁ - b₂) ≤ 1 := by
          by_contra h
          push Not at h
          exact hS (SB_apply_eq_zero L hL h)
        have h1 := zdist_add_le L (a 1 - b₂) (b₂ - b₁)
        have e1 : a 1 - b₂ + (b₂ - b₁) = a 1 - b₁ := by ring
        rw [e1] at h1
        have e2 : zdist L (a 1 - b₂) = zdist L (b₂ - a 1) := by
          rw [← zdist_neg L (a 1 - b₂), neg_sub]
        have e3 : zdist L (b₂ - b₁) = zdist L (b₁ - b₂) := by
          rw [← zdist_neg L (b₂ - b₁), neg_sub]
        rw [e2, e3] at h1
        have htri : (zdist L (a 1 - b₁) : ℝ) - 1 ≤ zdist L (b₂ - a 1) := by
          have : zdist L (a 1 - b₁) ≤ zdist L (b₂ - a 1) + 1 := by omega
          have : (zdist L (a 1 - b₁) : ℝ) ≤ zdist L (b₂ - a 1) + 1 := by exact_mod_cast this
          linarith
        have hb : ‖A ![b₂, a 1]‖ ≤ J * T (zdist L (b₂ - a 1)) := by simpa using hA ![b₂, a 1]
        calc ‖A ![b₂, a 1]‖ ≤ J * T (zdist L (b₂ - a 1)) := hb
          _ ≤ J * T (zdist L (a 1 - b₁) - 1) :=
            mul_le_mul_of_nonneg_left (tailT_antitone hℓ htri) (by linarith)
          _ ≤ J * (exp 1 * T (zdist L (a 1 - b₁))) :=
            mul_le_mul_of_nonneg_left (tailT_sub_one_le hW.le hℓu _) (by linarith)
          _ = exp 1 * J * T (zdist L (a 1 - b₁)) := by ring
    calc ∑ b₂ : ZMod L, ‖SB L b₁ b₂‖ * ‖A ![b₂, a 1]‖
        ≤ ∑ b₂ : ZMod L, ‖SB L b₁ b₂‖ * (exp 1 * J * T (zdist L (a 1 - b₁))) :=
          Finset.sum_le_sum fun b₂ _ => hpt b₂
      _ = (∑ b₂ : ZMod L, ‖SB L b₁ b₂‖) * (exp 1 * J * T (zdist L (a 1 - b₁))) := by
          rw [Finset.sum_mul]
      _ ≤ 1 * (exp 1 * J * T (zdist L (a 1 - b₁))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by have := hT0 (zdist L (a 1 - b₁)); positivity)
          exact (sum_norm_row_le L (SB L) b₁).trans (norm_SB L hL).le
      _ = exp 1 * J * T (zdist L (a 1 - b₁)) := one_mul _
  have h1 : ‖∑ b₁ : ZMod L, ∑ b₂ : ZMod L, A ![a 0, b₁] * SB L b₁ b₂ * A ![b₂, a 1]‖ ≤
      ∑ b₁ : ZMod L, ‖A ![a 0, b₁]‖ * ∑ b₂ : ZMod L, ‖SB L b₁ b₂‖ * ‖A ![b₂, a 1]‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₁ _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b₂ _ => le_of_eq ?_
    rw [norm_mul, norm_mul]; ring
  have h2 : ∑ b₁ : ZMod L, ‖A ![a 0, b₁]‖ * ∑ b₂ : ZMod L, ‖SB L b₁ b₂‖ * ‖A ![b₂, a 1]‖ ≤
      ∑ b₁ : ZMod L, (J * T (zdist L (a 0 - b₁))) * (exp 1 * J * T (zdist L (a 1 - b₁))) := by
    refine Finset.sum_le_sum fun b₁ _ => ?_
    have hb : ‖A ![a 0, b₁]‖ ≤ J * T (zdist L (a 0 - b₁)) := by simpa using hA ![a 0, b₁]
    exact mul_le_mul hb (hright b₁) (Finset.sum_nonneg fun _ _ => by positivity)
      (by have := hT0 (zdist L (a 0 - b₁)); positivity)
  have h3 : ∑ b₁ : ZMod L, (J * T (zdist L (a 0 - b₁))) * (exp 1 * J * T (zdist L (a 1 - b₁)))
      = exp 1 * J ^ 2 * ∑ x : ZMod L, T (zdist L (a 0 - x)) * T (zdist L (a 1 - x)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have h4 := mul_sum_tailT_mul_tailT_le L (ηu := ηu) hW hℓu hη D (a 0) (a 1)
  have hnW : ‖(W : ℂ)‖ = W := by rw [Complex.norm_real, Real.norm_of_nonneg hW.le]
  calc ‖eLL L W A a‖
      = W * ‖∑ b₁ : ZMod L, ∑ b₂ : ZMod L, A ![a 0, b₁] * SB L b₁ b₂ * A ![b₂, a 1]‖ := by
        rw [eLL, norm_mul, hnW]
    _ ≤ W * (exp 1 * J ^ 2 * ∑ x : ZMod L, T (zdist L (a 0 - x)) * T (zdist L (a 1 - x))) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left (h1.trans h2) hW.le
    _ = exp 1 * J ^ 2 * (W * ∑ x : ZMod L, T (zdist L (a 0 - x)) * T (zdist L (a 1 - x))) := by
        ring
    _ ≤ exp 1 * J ^ 2 * ((36 * (ηu⁻¹ * (W * ℓu * ηu)⁻¹) + W * L * W ^ (-D)) *
          T (zdist L (a 0 - a 1))) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

end E534

/-! ### The self-improving argument and the stopping time (5.43) -/

section SelfImproving

end SelfImproving

/-! ### Propagating tail bounds through `U_{u,v}`: Lemma 7.1 + (7.2) -/

section Kernel

variable {L : ℕ} [NeZero L]

/-- The factor `Ξ = C (1 + 2L e^{-(log W)^{3/2}/8}) + m^{-2} + e^{(log W)^{3/4}}` of the kernel
bound `norm_Uker_le_of_tail`; it is `≤ W^τ` for every `τ > 0` once `L ≤ W²`
(`RBM.Step2FarInputs.eventually_xiK_le`). -/
noncomputable def xiK (L : ℕ) (W m : ℝ) : ℝ :=
  cTail * (1 + 2 * L * exp (-(log W ^ (3 / 2 : ℝ) / 8))) + (m ^ 2)⁻¹ + exp (log W ^ (3 / 4 : ℝ))

theorem xiK_nonneg (L : ℕ) (W m : ℝ) : 0 ≤ xiK L W m := by
  unfold xiK
  have := cTail_nonneg
  positivity

/-- **The kernel estimate behind (5.39)–(5.41)**, from Lemma 7.1 (`RBM.norm_Uker_apply_le`)
and (7.2) (`RBM.norm_Uker_tail_le_ellStar`).  Let `η_x = (1 - x) m`, `ℓ_x = ℓ̂(x)`, and
`T_x = T_{x,D}` the tail function (5.27) with these scales.  If `|A_b| ≤ M T_u(‖b₁ - b₂‖)` and
`W ℓ_v η_v ≤ W ℓ_u η_u`, then for `σ = (+,-)` (`ξ = (1, 1)`)
`|(U_{u,v} ∘ A)_a| ≤ M (η_u/η_v)² Ξ T_v(‖a₁ - a₂‖)`.
For `‖a₁ - a₂‖ ≥ ℓ*_v` this is (7.2); below `ℓ*_v` it is Lemma 7.1, at the price
`e^{(log W)^{3/4}} = W^{o(1)}` (the paper's `1(|a₁ - a₂| ≤ ℓ*)`-term). -/
theorem norm_Uker_le_of_tail (hL : 3 ≤ L) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) {u v : ℝ}
    (hu0 : 0 ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1) {W D M : ℝ} (hW : exp 1 ≤ W)
    (hM : 0 ≤ M)
    (hAuv : W * ellHat L (v : ℂ) * ((1 - v) * m) ≤ W * ellHat L (u : ℂ) * ((1 - u) * m))
    {A : LoopArg L 2 → ℂ}
    (hA : ∀ b, ‖A b‖ ≤ M * tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (b 0 - b 1)))
    (a : LoopArg L 2) :
    ‖Uker L (fun _ => 1) (u : ℂ) (v : ℂ) A a‖ ≤
      M * ((1 - u) / (1 - v)) ^ 2 * xiK L W m *
        tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D (zdist L (a 0 - a 1)) := by
  have hW0 : 0 < W := lt_of_lt_of_le (exp_pos 1) hW
  have hW1 : 1 ≤ W := le_trans (Real.one_le_exp (by norm_num)) hW
  have hL1 : 1 ≤ L := by omega
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓu : 1 ≤ ellHat L (u : ℂ) := one_le_ellHat_of_nonneg hL1 hu0 hu1
  have hℓv : 1 ≤ ellHat L (v : ℂ) := one_le_ellHat_of_nonneg hL1 hv0 hv1
  set ℓu := ellHat L (u : ℂ) with hℓudef
  set ℓv := ellHat L (v : ℂ) with hℓvdef
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  set r := (1 - u) / (1 - v) with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ h1v]; linarith
  set d : ℝ := (zdist L (a 0 - a 1) : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  set Av := W * ℓv * ((1 - v) * m) with hAv
  set Au := W * ℓu * ((1 - u) * m) with hAudef
  have hAv0 : 0 < Av := by positivity
  have hε : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hX := xiK_nonneg L W m
  have hcT := cTail_nonneg
  set Tv := tailT W ℓv ((1 - v) * m) D d with hTv
  have hTv0 : 0 ≤ Tv := tailT_nonneg hW0.le _
  have hxi1 : cTail * (1 + 2 * L * exp (-(log W ^ (3 / 2 : ℝ) / 8))) ≤ xiK L W m := by
    unfold xiK; have := exp_pos (log W ^ (3 / 4 : ℝ)); have : 0 ≤ (m ^ 2)⁻¹ := by positivity
    linarith
  have hxi2 : (m ^ 2)⁻¹ ≤ xiK L W m := by
    unfold xiK
    have := exp_pos (log W ^ (3 / 4 : ℝ))
    have : 0 ≤ cTail * (1 + 2 * L * exp (-(log W ^ (3 / 2 : ℝ) / 8))) := by positivity
    linarith
  have hxi3 : exp (log W ^ (3 / 4 : ℝ)) ≤ xiK L W m := by
    unfold xiK
    have : 0 ≤ cTail * (1 + 2 * L * exp (-(log W ^ (3 / 2 : ℝ) / 8))) := by positivity
    have : 0 ≤ (m ^ 2)⁻¹ := by positivity
    linarith
  by_cases hfar : ellStar W ℓv ≤ d
  · -- (7.2)
    by_cases hM0 : M = 0
    · have hA0 : A = 0 := by
        funext b
        have := hA b
        rw [hM0, zero_mul] at this
        simpa using norm_le_zero_iff.1 this
      have : Uker L (fun _ => 1) (u : ℂ) (v : ℂ) A a = 0 := by
        simp [Uker_apply, hA0]
      rw [this, norm_zero]
      positivity
    have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    set c : ℝ := M * (m ^ 2)⁻¹ with hc
    have hcpos : 0 < c := by positivity
    set A' : LoopArg L 2 → ℂ := ((c : ℂ)⁻¹) • A with hA'def
    have hAA' : A = (c : ℂ) • A' := by
      rw [hA'def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hcpos.ne'), one_smul]
    have hA' : ∀ b, ‖A' b‖ ≤ tailT W ℓu (1 - u) D (zdist L (b 0 - b 1)) := by
      intro b
      have hb := hA b
      have hnc : ‖((c : ℂ)⁻¹)‖ = c⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
      rw [hA'def, Pi.smul_apply, smul_eq_mul, norm_mul, hnc]
      rw [inv_mul_le_iff₀ hcpos]
      refine hb.trans ?_
      unfold tailT
      set e := exp (-√((zdist L (b 0 - b 1) : ℝ) / ℓu))
      have he0 : 0 ≤ e := (exp_pos _).le
      have hm2 : 0 < m ^ 2 := by positivity
      have hm21 : m ^ 2 ≤ 1 := by nlinarith
      have e1 : ((W * ℓu * ((1 - u) * m)) ^ 2)⁻¹ = (m ^ 2)⁻¹ * ((W * ℓu * (1 - u)) ^ 2)⁻¹ := by
        rw [← mul_inv]; congr 1; ring
      rw [e1, hc]
      have hP : 0 ≤ ((W * ℓu * (1 - u)) ^ 2)⁻¹ := by positivity
      have hmi : 1 ≤ (m ^ 2)⁻¹ := one_le_inv₀ hm2 |>.2 hm21
      nlinarith [mul_le_mul_of_nonneg_left hmi (mul_nonneg hMpos.le hε)]
    have key := norm_Uker_tail_le_ellStar L hL hu0 huv hv0 hv1 hW hA' a hfar
    have hU : Uker L (fun _ => 1) (u : ℂ) (v : ℂ) A a
        = (c : ℂ) * Uker L (fun _ => 1) (u : ℂ) (v : ℂ) A' a := by
      rw [hAA', Uker_smul]; rfl
    rw [hU, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
    set X := cTail * (1 + 2 * L * exp (-(log W ^ (3 / 2 : ℝ) / 8))) with hXdef
    set e := exp (-√(d / ℓv)) with he
    have he0 : 0 ≤ e := (exp_pos _).le
    have hPv : ((W * ℓv * (1 - v)) ^ 2)⁻¹ = m ^ 2 * (Av ^ 2)⁻¹ := by
      rw [hAv]; field_simp
    have hTveq : Tv = (Av ^ 2)⁻¹ * e + W ^ (-D) := rfl
    have hX0 : 0 ≤ X := by positivity
    have hQ : 0 ≤ (Av ^ 2)⁻¹ := by positivity
    have hm2 : 0 < m ^ 2 := by positivity
    calc c * ‖Uker L (fun _ => 1) (u : ℂ) (v : ℂ) A' a‖
        ≤ c * (X * (((W * ℓv * (1 - v)) ^ 2)⁻¹ * e) + ((1 - u) / (1 - v)) ^ 2 * W ^ (-D)) :=
          mul_le_mul_of_nonneg_left key hcpos.le
      _ = M * (X * ((Av ^ 2)⁻¹ * e) + (m ^ 2)⁻¹ * r ^ 2 * W ^ (-D)) := by
          rw [hPv, hc, ← hr]; field_simp
      _ ≤ M * (r ^ 2 * xiK L W m * ((Av ^ 2)⁻¹ * e) + r ^ 2 * xiK L W m * W ^ (-D)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hM
          · have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr1
            have : X ≤ r ^ 2 * xiK L W m := hxi1.trans (le_mul_of_one_le_left hX hr2)
            exact mul_le_mul_of_nonneg_right this (mul_nonneg hQ he0)
          · rw [mul_comm ((m ^ 2)⁻¹) (r ^ 2), mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxi2 hε) (sq_nonneg r)
      _ = M * r ^ 2 * xiK L W m * Tv := by rw [hTveq]; ring
  · -- Lemma 7.1
    push Not at hfar
    set Tu0 := tailT W ℓu ((1 - u) * m) D 0 with hTu0
    have hAb : ∀ b, ‖A b‖ ≤ M * Tu0 := fun b =>
      (hA b).trans (mul_le_mul_of_nonneg_left (tailT_antitone (by linarith) (Nat.cast_nonneg _)) hM)
    have hTu00 : 0 ≤ Tu0 := tailT_nonneg hW0.le _
    have ht : ∀ i : Fin 2, ‖(v : ℂ) * (fun _ => (1 : ℂ)) i‖ < 1 := by
      intro i; simp [Complex.norm_real, abs_of_nonneg hv0, hv1]
    have hC : ∀ i : Fin 2, 1 + ‖((u : ℂ) - (v : ℂ)) * (fun _ => (1 : ℂ)) i‖ *
        (1 - ‖(v : ℂ) * (fun _ => (1 : ℂ)) i‖)⁻¹ ≤ r := by
      intro i
      have e1 : ‖((u : ℂ) - (v : ℂ)) * (fun _ => (1 : ℂ)) i‖ = v - u := by
        simp only [mul_one]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        ring
      have e2 : ‖(v : ℂ) * (fun _ => (1 : ℂ)) i‖ = v := by
        simp [Complex.norm_real, abs_of_nonneg hv0]
      rw [e1, e2, hr]
      apply le_of_eq
      field_simp
      ring
    have key := norm_Uker_apply_le L hL ht (mul_nonneg hM hTu00) hC hAb a
    -- `T_u(0) ≤ e^{(log W)^{3/4}} T_v(d)`
    have hlog : 0 ≤ log W := Real.log_nonneg hW1
    have hsq : √(d / ℓv) ≤ log W ^ (3 / 4 : ℝ) := by
      rw [← sqrt_log_rpow_three_halves hW1]
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ (by linarith)]
      unfold ellStar at hfar
      linarith
    have hexp : exp (-(log W ^ (3 / 4 : ℝ))) ≤ exp (-√(d / ℓv)) := exp_le_exp.2 (by linarith)
    have hAu : Av ≤ Au := hAuv
    have hAuv2 : (Au ^ 2)⁻¹ ≤ (Av ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hAv0.le hAu 2)
    have hTu0' : Tu0 = (Au ^ 2)⁻¹ + W ^ (-D) := by
      rw [hTu0, tailT]
      simp only [zero_div, Real.sqrt_zero, neg_zero, exp_zero, mul_one, hAudef]
    have hE0 : 0 < exp (log W ^ (3 / 4 : ℝ)) := exp_pos _
    have hEE : exp (log W ^ (3 / 4 : ℝ)) * exp (-(log W ^ (3 / 4 : ℝ))) = 1 := by
      rw [← exp_add]; simp
    have hTT : Tu0 ≤ exp (log W ^ (3 / 4 : ℝ)) * Tv := by
      rw [hTu0', hTv]
      unfold tailT
      have hQ : 0 ≤ (Av ^ 2)⁻¹ := by positivity
      have h1 : (Av ^ 2)⁻¹ ≤ exp (log W ^ (3 / 4 : ℝ)) * ((Av ^ 2)⁻¹ * exp (-√(d / ℓv))) := by
        calc (Av ^ 2)⁻¹
            = exp (log W ^ (3 / 4 : ℝ)) * ((Av ^ 2)⁻¹ * exp (-(log W ^ (3 / 4 : ℝ)))) := by
              rw [mul_comm ((Av ^ 2)⁻¹), ← mul_assoc, hEE, one_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hQ) hE0.le
      have h2 : W ^ (-D) ≤ exp (log W ^ (3 / 4 : ℝ)) * W ^ (-D) :=
        le_mul_of_one_le_left hε (Real.one_le_exp (Real.rpow_nonneg hlog _))
      have : ((W * ℓv * ((1 - v) * m)) ^ 2)⁻¹ = (Av ^ 2)⁻¹ := rfl
      rw [this, mul_add]
      linarith
    calc ‖Uker L (fun _ => 1) (u : ℂ) (v : ℂ) A a‖ ≤ r ^ 2 * (M * Tu0) := key
      _ ≤ r ^ 2 * (M * (exp (log W ^ (3 / 4 : ℝ)) * Tv)) := by gcongr
      _ ≤ r ^ 2 * (M * (xiK L W m * Tv)) := by gcongr
      _ = M * r ^ 2 * xiK L W m * Tv := by ring

end Kernel

/-! ### The flow: `L - K` for `σ = (+,-)`, `J*`, the threshold and the stopping time -/

section FlowDefs

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The threshold of the stopping time: `Λ(u) = N^δ (η_s/η_u)^4` (the paper's `(η_s/η_t)^4`,
see *Deviations*). -/
noncomputable def thr (E : ℝ) (s : ℕ → ℝ) (δ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ δ * (etaT E (s N) / etaT E u) ^ 4

theorem sigPM_xi {E : ℝ} (hE : |E| ≤ 2) : xiOf (n := 2) (mSigma E) sigPM = fun _ => 1 :=
  xiOf_mSigma_true_false hE

theorem etaT_eq (E u : ℝ) : etaT E u = (1 - u) * (mE E).im := rfl

theorem etaT_pos' {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu : u < 1) : 0 < etaT E u := by
  rw [etaT_eq]; exact mul_pos (by linarith) (mE_im_pos hE)

theorem etaT_ratio {E : ℝ} (hE : |E| < 2) (a b : ℝ) :
    etaT E a / etaT E b = (1 - a) / (1 - b) := by
  have := mE_im_pos hE
  rw [etaT_eq, etaT_eq]
  field_simp

end FlowDefs

/-! ### (5.39)–(5.41): one step of the stopped hierarchy, pathwise -/

section Step

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Step

/-! ### The arithmetic of (5.47) -/

section Arith

/-- The constant `4 + e + (36e + 2)/Im m` of the arithmetic of (5.47). -/
noncomputable def cStep (m : ℝ) : ℝ := 4 + exp 1 + (36 * exp 1 + 2) * m⁻¹

end Arith

/-! ### Scales of the flow -/

section FlowScales

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- `W(N) → ∞` (from (2.2)). -/
theorem tendsto_W (B : Band Ω) : Tendsto (fun N => (B.W N : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 + B.c)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith [B.c_pos])).comp tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono' atTop B.bandwidth h1

/-- `N ≤ W²` eventually (from (2.2)). -/
theorem eventually_le_W_sq (B : Band Ω) : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≤ (B.W N : ℝ) ^ 2 := by
  filter_upwards [B.bandwidth, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have h1 : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ B.W N :=
    (Real.rpow_le_rpow_of_exponent_le hN0 (by linarith [B.c_pos])).trans hN
  have h2 : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  rw [← h2]
  exact pow_le_pow_left₀ (by positivity) h1 2

/-- `2 W² e^{-(log W)^{3/2}/8} ≤ 1` for `W ≥ e^{400}`. -/
theorem two_mul_sq_mul_exp_le {W : ℝ} (hW : exp 400 ≤ W) :
    2 * W ^ 2 * exp (-(log W ^ (3 / 2 : ℝ) / 8)) ≤ 1 := by
  have hW0 : 0 < W := lt_of_lt_of_le (exp_pos _) hW
  have hy : 400 ≤ log W := by rw [← log_exp 400]; exact log_le_log (exp_pos _) hW
  set y := log W with hydef
  have hy0 : 0 ≤ y := by linarith
  have hsq : 20 ≤ √y := by
    rw [show (20 : ℝ) = √(20 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have h32 : y ^ (3 / 2 : ℝ) = y * √y := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hy0 (by norm_num)]; norm_num
  have hbig : 5 / 2 * y ≤ y ^ (3 / 2 : ℝ) / 8 := by rw [h32]; nlinarith
  have hW2 : W ^ 2 = exp (2 * y) := by
    rw [hydef, ← Real.exp_log hW0]; rw [Real.exp_log hW0, ← Real.exp_log (pow_pos hW0 2),
      Real.log_pow]; push_cast; ring_nf
  rw [hW2, mul_assoc, ← exp_add]
  have : 2 * y + -(y ^ (3 / 2 : ℝ) / 8) ≤ -(y / 2) := by linarith
  calc 2 * exp (2 * y + -(y ^ (3 / 2 : ℝ) / 8)) ≤ 2 * exp (-(y / 2)) := by gcongr
    _ ≤ 2 * exp (-200) := by gcongr; linarith
    _ ≤ 1 := by
      have : exp (-200) ≤ exp (-1) := exp_le_exp.2 (by norm_num)
      have h2 : exp (-1) < 1 / 2 := by
        rw [exp_neg, inv_lt_comm₀ (exp_pos 1) (by norm_num)]
        have := Real.add_one_lt_exp (x := (1 : ℝ)) (by norm_num)
        linarith
      linarith

end FlowScales

section FlowFacts

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

theorem natCast_rpow_pow (N : ℕ) (a : ℝ) (k : ℕ) :
    ((N : ℝ) ^ a) ^ k = (N : ℝ) ^ (a * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]

end FlowFacts

/-! ### The random-layer inputs of Step 2 -/

section Hyp

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

theorem idx_sigPM {L : ℕ} (b : LoopArg L 2) : LoopData.idx (sigPM, b) = pmLoop (b 0) (b 1) := by
  simp [LoopData.idx, pmLoop, sigPM, List.ofFn_succ]

/-- (2.69) in the tail-function form: for `W ℓ_u η_u ≥ 1`,
`(W ℓ_u η_u)^{-2} (e^{-(‖a-b‖/ℓ_u)^{1/2}} + W^{-D}) ≤ T_{u,D}(‖a - b‖)`. -/
theorem decayProf_le_tT {E : ℝ} {N : ℕ} {u D : ℝ} (hA : 1 ≤ B.scale E N u)
    (a b : ZMod (B.L N)) :
    (B.scale E N u)⁻¹ ^ 2 * B.decayProf N u D a b ≤ tT B E N D u (zdist (B.L N) (a - b)) := by
  have hA0 : 0 < B.scale E N u := by linarith
  have hQ : (B.scale E N u)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hA)
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hε : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  unfold tT tailT Band.decayProf
  rw [← Real.sqrt_eq_rpow]
  have e1 : ((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2 = (B.scale E N u) ^ 2 := rfl
  rw [e1, ← inv_pow, mul_add]
  have := mul_le_of_le_one_left hε hQ
  linarith

end Hyp

/-! ### The main argument: (5.47) -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Main

/-! ### (5.47) as a `≺` statement, and (2.76) -/

section Conclusions

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- `T_{u,D} ≤ (W ℓ_u η_u)^{-2} (e^{-(ℓ/ℓ_u)^{1/2}} + W^{-D₀})` for `D ≥ D₀ + 4`, once
`W ℓ_u η_u ≤ W²`: the tail function (5.27) is dominated by the right side of (2.76). -/
theorem tT_le_decayProf {N : ℕ} {u D D₀ : ℝ} (hDD : D₀ + 4 ≤ D) (hA1 : 1 ≤ B.scale E N u)
    (hAW : B.scale E N u ≤ (B.W N : ℝ) ^ 2) (a b : ZMod (B.L N)) :
    tT B E N D u (zdist (B.L N) (a - b)) ≤ (B.scale E N u)⁻¹ ^ 2 * B.decayProf N u D₀ a b := by
  have hA0 : 0 < B.scale E N u := by linarith
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hWD : (B.W N : ℝ) ^ (-D) ≤ (B.scale E N u)⁻¹ ^ 2 * (B.W N : ℝ) ^ (-D₀) := by
    have e : (B.W N : ℝ) ^ (-D) = (B.W N : ℝ) ^ (-D₀) * (B.W N : ℝ) ^ (-(D - D₀)) := by
      rw [← Real.rpow_add hW0]; ring_nf
    rw [e, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hW0.le _)
    calc (B.W N : ℝ) ^ (-(D - D₀)) ≤ (B.W N : ℝ) ^ (-(4 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      _ = (((B.W N : ℝ) ^ 2) ^ 2)⁻¹ := by
          rw [Real.rpow_neg hW0.le, show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]; ring
      _ ≤ ((B.scale E N u) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hA0.le hAW 2)
      _ = (B.scale E N u)⁻¹ ^ 2 := by rw [inv_pow]
  unfold tT tailT Band.decayProf
  rw [← Real.sqrt_eq_rpow]
  have e1 : ((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2 = (B.scale E N u) ^ 2 := rfl
  rw [e1, ← inv_pow, mul_add]
  linarith

end Conclusions

/-! ### (2.75) from (2.76) -/

section LocalLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- `ξ² ≺ ζ` implies `ξ ≺ ζ^{1/2}`. -/
theorem stochDom_rpow_half_of_sq {ξ ζ : ∀ N, U N → Ω → ℝ} (hζ : ∀ N u ω, 0 ≤ ζ N u ω)
    (h : StochDom P (fun N u ω => ξ N u ω ^ 2) ζ) :
    StochDom P ξ (fun N u ω => ζ N u ω ^ ((1 : ℝ) / 2)) := by
  refine StochDom.of_subset h fun τ hτ => ⟨2 * τ, by positivity, Eventually.of_forall
    fun N => ?_⟩
  rintro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hN : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h0 : 0 ≤ (N : ℝ) ^ τ * ζ N u ω ^ ((1 : ℝ) / 2) :=
    mul_nonneg hN (Real.rpow_nonneg (hζ N u ω) _)
  have hsq := pow_lt_pow_left₀ hu h0 (two_ne_zero)
  have e : ((N : ℝ) ^ τ * ζ N u ω ^ ((1 : ℝ) / 2)) ^ 2 = (N : ℝ) ^ (2 * τ) * ζ N u ω := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (hζ N u ω), ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 2
    push_cast; ring
  rw [e] at hsq
  exact hsq

variable {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end LocalLaw

/-! ### Lemma 5.6 -/

section Lemma56

/-- `C e^{-a (log W)^{3/2}} ≤ W^{-D}` for large `W` (`a, C > 0`). -/
theorem eventually_mul_exp_neg_log_rpow_le {a : ℝ} (ha : 0 < a) {C : ℝ} (hC : 0 < C) (D : ℝ) :
    ∀ᶠ W : ℝ in atTop, C * exp (-(a * log W ^ (3 / 2 : ℝ))) ≤ W ^ (-D) := by
  set M := |D| + |log C| + 1 with hM
  filter_upwards [eventually_ge_atTop (exp (max 1 ((M / a) ^ 2)))] with W hW
  have hW0 : 0 < W := lt_of_lt_of_le (exp_pos _) hW
  have hy : max 1 ((M / a) ^ 2) ≤ log W := by
    rw [← log_exp (max 1 ((M / a) ^ 2))]; exact log_le_log (exp_pos _) hW
  set y := log W with hydef
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 ≤ y := by linarith
  have hMa : 0 ≤ M / a := div_nonneg (by positivity) ha.le
  have hsq : M / a ≤ √y := by
    rw [show M / a = √((M / a) ^ 2) by rw [Real.sqrt_sq hMa]]
    exact Real.sqrt_le_sqrt ((le_max_right _ _).trans hy)
  have h32 : y ^ (3 / 2 : ℝ) = y * √y := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hy0 (by norm_num)]; norm_num
  have hkey : M * y ≤ a * y ^ (3 / 2 : ℝ) := by
    rw [h32]
    have : M ≤ a * √y := by rwa [div_le_iff₀' ha] at hsq
    nlinarith
  rw [Real.rpow_def_of_pos hW0, ← hydef, ← exp_log hC, ← exp_add, exp_le_exp]
  have h1 : log C ≤ |log C| := le_abs_self _
  have e1 : M * y = |D| * y + |log C| * y + y := by rw [hM]; ring
  have e2 : |log C| ≤ |log C| * y := le_mul_of_one_le_right (abs_nonneg _) hy1
  have e3 : -(|D| * y) ≤ y * -D := by
    have := mul_le_mul_of_nonneg_left (neg_le_neg (le_abs_self D)) hy0
    linarith
  linarith

variable (L : ℕ) [NeZero L]

/-- **(5.30)**, deterministic form: for `‖x - y‖ ≥ δ ℓ*_t`,
`|(Θ_t)_{xy}| ≤ C (1 - t)^{-1} ℓ_t^{-1} e^{-c δ (log W)^{3/2}}` ((2.52) at distance `δ ℓ*_t`). -/
theorem norm_Theta_le_of_ellStar (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {W δ : ℝ}
    {x y : ZMod L} (h : δ * ellStar W (ellHat L (t : ℂ)) ≤ zdist L (x - y)) :
    ‖Theta L (t : ℂ) x y‖ ≤ cTwo52 / ((1 - t) * ellHat L (t : ℂ)) *
      exp (-(cZero * δ * log W ^ (3 / 2 : ℝ))) := by
  have hℓ := SumZeroDyn.ellHat_real_pos' L hL ht0 ht1
  have h1 := SumZeroDyn.norm_Theta_real_le_of_far L hL ht0 ht1 h
  refine h1.trans (le_of_eq ?_)
  congr 3
  unfold ellStar
  field_simp

/-- **(5.30)** for `Θ_s^{-1} Θ_t = (1 - s S^{(B)}) Θ_t` (`RBM.mul_Theta`): its entries are
bounded by those of `Θ_t` at distance `≥ ‖x - y‖ - 1`. -/
theorem norm_oneSub_mul_Theta_le (hL : 3 ≤ L) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {x y : ZMod L} {M : ℝ} (hM : ∀ z, (zdist L (x - y) : ℝ) - 1 ≤ zdist L (z - y) →
      ‖Theta L (t : ℂ) z y‖ ≤ M) :
    ‖((1 - (s : ℂ) • SB L) * Theta L (t : ℂ)) x y‖ ≤ 2 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (by linarith))
  rw [sub_mul, one_mul, Matrix.sub_apply, smul_mul_assoc, Matrix.smul_apply, Matrix.mul_apply,
    smul_eq_mul]
  have hsum : ‖∑ z : ZMod L, SB L x z * Theta L (t : ℂ) z y‖ ≤ M := by
    calc ‖∑ z : ZMod L, SB L x z * Theta L (t : ℂ) z y‖
        ≤ ∑ z : ZMod L, ‖SB L x z‖ * M := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
          rw [norm_mul]
          by_cases hS : SB L x z = 0
          · simp [hS]
          · refine mul_le_mul_of_nonneg_left (hM z ?_) (norm_nonneg _)
            have hd : zdist L (x - z) ≤ 1 := by
              by_contra h; push Not at h; exact hS (SB_apply_eq_zero L hL h)
            have h1 := zdist_add_le L (x - z) (z - y)
            have e : x - z + (z - y) = x - y := by ring
            rw [e] at h1
            have : (zdist L (x - y) : ℝ) ≤ 1 + zdist L (z - y) := by
              have : zdist L (x - y) ≤ 1 + zdist L (z - y) := by omega
              exact_mod_cast this
            linarith
      _ = (∑ z : ZMod L, ‖SB L x z‖) * M := by rw [Finset.sum_mul]
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right
          ((sum_norm_row_le L (SB L) x).trans (norm_SB L hL).le) hM0
      _ = M := one_mul M
  have hs : ‖(s : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hs0]; exact hs1
  calc ‖Theta L (t : ℂ) x y - (s : ℂ) * ∑ z : ZMod L, SB L x z * Theta L (t : ℂ) z y‖
      ≤ ‖Theta L (t : ℂ) x y‖ + ‖(s : ℂ)‖ * ‖∑ z : ZMod L, SB L x z * Theta L (t : ℂ) z y‖ := by
        rw [← norm_mul]; exact norm_sub_le _ _
    _ ≤ M + 1 * M := by
        gcongr
        · exact hM x (by linarith)
    _ = 2 * M := by ring

variable {L}

section Flow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

end Flow

end Lemma56

section Eq531

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Eq531

/-! ### Step 2 -/

section Step2Main

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Step2Main

end Step2

end RBM
