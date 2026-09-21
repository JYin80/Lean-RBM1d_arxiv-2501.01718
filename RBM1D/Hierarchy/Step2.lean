/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.SumZeroDyn
import RBM1D.Hierarchy.Step1

/-!
# Step 2 of the proof of Theorem 2.21: (2.75) and (2.76)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.3 (pp. 56–63): the tail
functions (5.26)–(5.29), Lemma 5.6, the bound (5.34) of Lemma 5.7, the estimates (5.39)–(5.41)
of the stopped hierarchy, the stopping time (5.43), the conclusion (5.47), and from it (2.76)
`|(L-K)_{u,(+,-),a}| ≺ (η_s/η_u)⁴ (W ℓ_u η_u)^{-2} (e^{-(|a₁-a₂|/ℓ_u)^{1/2}} + W^{-D})` and
(2.75) `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/2}`.

**The logical core is a self-improving inequality, not Grönwall** (`self_improving`): if the
bound `J* ≤ Λ` up to time `v` implies the better bound `J*(v) ≤ B(v) < Λ(v)`, and `J*` is
continuous, then `J* ≤ B` on all of `[s, t]`.  The stochastic part only has to supply that
implication on one high-probability event.

## Deterministic results

* `tailLK` **(5.26)**, `jStar` **(5.29)** (with `RBM.tailT` (5.27) and `RBM.ratioJ` (5.28) of
  `Analysis/StretchedExp.lean`); `tailLK_antitone`; `isGreatest_jStar`: `J* = max_ℓ J(ℓ)`;
  `le_jStar_mul`: `f ≤ J* T` (the definitional content of (5.31)); `jStar_le`.
* `eLL`, `norm_eLL_le` — **(5.34)**: `|E^{((L-K)×(L-K))}_a| ≤ e (J*)² (36 η^{-1}(Wℓη)^{-1} +
  W L W^{-D}) T(|a₁ - a₂|)` (via the convolution bound (5.50), `RBM.mul_sum_tailT_mul_tailT_le`).
* `norm_Uker_le_of_tail` — the kernel estimate behind **(5.39)–(5.41)**, from Lemma 7.1
  (`RBM.norm_Uker_apply_le`) and (7.2) (`RBM.norm_Uker_tail_le_ellStar`):
  `|A_b| ≤ M T_u(|b₁-b₂|)` implies `|(U_{u,v} ∘ A)_a| ≤ M (η_u/η_v)² Ξ T_v(|a₁-a₂|)`,
  `Ξ = xiK = W^{o(1)}`.
* `self_improving`, `stopTime` **(5.43)**, `le_stopTime_iff`, `stopTime_eq_right`.
* `phi_arith` — the arithmetic of (5.40)–(5.47).
* `norm_Theta_le_of_ellStar`, `norm_oneSub_mul_Theta_le`, `eq530` — **Lemma 5.6, (5.30)**;
  `eq531` — **(5.31)** (deterministically, eventually in `N`, for every `ω`).
  (5.32) is `RBM.tailT_sub_le` / `RBM.unifDetDom_tailT_sub` (T43).

## The flow

* `sigPM` (`σ = (+,-)`), `lk` (`(L-K)_{u,σ}`), `tT` (`T_{u,D}`), `jS` (`J*_{u,D}`), `thr`
  (the threshold `Λ(u) = N^δ (η_s/η_u)⁴`), `tau` (the stopping time (5.43)).
* `step_bound` — **(5.21) with (5.39)–(5.41) and (5.45), pathwise**: if `J*_{u,D} ≤ Λ(u)` on
  `[s, v)`, then `|(L-K)_{v,a}| ≤ Φ_v T_{v,D}(|a₁ - a₂|)`.
* `jS_highProb`, `jS_stochDom` — **(5.47)**: `J*_{u,D} ≺ (η_s/η_u)⁴` uniformly in `u ∈ [s,t]`.
* `aprioriDecay` — **(2.76)**, `localLaw` — **(2.75)** (from (2.76), (2.59), Lemma 4.1 and
  (2.74), as on p. 63), in exactly the shapes of the fields `RBM.Steps.aprioriDecay`,
  `RBM.Steps.localLaw`; `step2` — both, with (2.74) supplied by `RBM.Step1.weakLaw`.

## Hypotheses (never axioms)

* `Hyp.H` — (5.20), the integrated hierarchy: the structure `RBM.SumZeroDyn.Hierarchy` of
  `Hierarchy/SumZeroDyn.lean` at loop length `2` (T58/T60 interface; the drift `F` is abstract
  there).
* `Hyp.eG` — (5.35) for `F - E^{((L-K)×(L-K))}` (= `E^{(G)}` plus the `l_K > 2` terms).
* `Hyp.mart` — (5.44)–(5.46): the stopped martingale, for thresholds `N^δ (η_s/η_u)⁴`,
  `0 < δ ≤ δ₀`.
* `Hyp.cont` — continuity of `u ↦ (L-K)_{u,a}` on `[s, t]`, w.h.p.
* `RBM.BoundsCore X E s` ((2.69) is used), (2.72) with a gain `N^c` (`hreg`), and for (2.75)
  the Step-1 inputs `RBM.Step1.Hyp` (Lemma 4.1 along the flow, via (2.74)).

## Deviations from the paper

* **Threshold and stopping time.**  (5.43) uses the time-dependent threshold
  `Λ(u) = N^δ (η_s/η_u)⁴` (`δ > 0` small, arbitrary) instead of `(η_s/η_t)⁴`, and
  `T = inf{u : J*_u > Λ(u)}`.  The factor `N^δ` gives the room that `≺` needs to contradict
  `J*_T ≥ Λ(T)`; the dependence on `u` gives (2.76) at every `u ∈ [s,t]` with `(η_s/η_u)⁴`
  directly (no net over final times).
* **(5.47)** is proved in the form `J*_{u,D} ≺ (η_s/η_u)⁴` (which is exactly what (2.76)
  needs), not `≺ (η_s/η_t)²`; (5.48) is not derived.
* **(2.72) with a gain**: `N^c (η_s/η_t)^{30} ≤ W ℓ_t η_t` (`hreg`).  With (2.72) alone the
  `(J*)³ (Wℓη)^{-1/3}` term of (5.35)/(5.41) is exactly critical at the threshold `(η_s/η_t)⁴`
  (`(η_s/η_t)^{2+12} (Wℓη)^{-1/3} ≤ (η_s/η_t)⁴`), leaving no room for the `≺` losses.
* **(5.35)** is a hypothesis, normalized by `T_{u,D}` (what the paper's proof, (5.55) and (5.63),
  establishes) instead of `T_{t,D} ≥ T_{u,D}`, without the indicator `1(|a₁-a₂| ≤ ℓ*_u)`, and for
  the whole drift minus `E^{((L-K)×(L-K))}`.  (5.36), (5.42), (5.44)–(5.46) enter only through the
  stopped-martingale hypothesis `Hyp.mart` (uniform in the time, without the indicator).
* **(5.34)** holds with the explicit constant `e (36 + …)` and `T_{u,D}` on both sides.
* **(5.39)–(5.41)**: the kernel bound loses `Ξ = W^{o(1)}` and uses `(η_u/η_v)²` in place of the
  paper's `(ℓ_t/ℓ_s)² 1(|a₁-a₂| ≤ ℓ*_t) + 1`; the `du`-integral is bounded by length × sup.
* `J*` is defined as `max_a f(a)/T(|a₁-a₂|) + 1` and shown to equal `max_ℓ J(ℓ)`.
* (5.30) for `Θ_s^{-1} Θ_t` is stated for `(1 - s S^{(B)}) Θ_t` (= `Θ_s^{-1} Θ_t`,
  `RBM.mul_Theta`).
* `eLL` is written directly from the proof of (5.34); its identification with the
  `(L-K)×(L-K)` part of the concrete drift (T58, `RBM.primBil`) is part of `Hyp.eG`.
* Scales: `η_u = etaT E u = (1 - u) Im m`, `ℓ_u = ℓ̂(u)`.
-/

namespace RBM

namespace Step2

open Finset Real MeasureTheory Filter
open scoped Matrix.Norms.Operator

/-! ### The tail functions (5.26)–(5.29) -/

section Tail

variable (L : ℕ) [NeZero L]

/-- **(5.26)** `T^{(L-K)}(ℓ) = max_{‖a₁ - a₂‖ ≥ ℓ} f(a)`, for a function `f ≥ 0` of the pair
`a = (a₁, a₂)` (in the application `f(a) = |(L-K)_{u,(+,-),a}|`).  The maximum over the empty
set is `0`. -/
noncomputable def tailLK (f : LoopArg L 2 → ℝ) (ℓ : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => if ℓ ≤ (zdist L (a 0 - a 1) : ℝ) then f a else 0)

/-- **(5.29)** `J*_{u,D} = max_{a} f(a) / T_{u,D}(‖a₁ - a₂‖) + 1`.  By `isGreatest_jStar` this
is the maximum over `ℓ` of `J_{u,D}(ℓ) = T^{(L-K)}_u(ℓ)/T_{u,D}(ℓ) + 1` (5.28). -/
noncomputable def jStar (f : LoopArg L 2 → ℝ) (W ℓu ηu D : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => f a / tailT W ℓu ηu D (zdist L (a 0 - a 1))) + 1

variable {L}
variable {f : LoopArg L 2 → ℝ}

theorem le_tailLK {ℓ : ℝ} {a : LoopArg L 2} (h : ℓ ≤ (zdist L (a 0 - a 1) : ℝ)) :
    f a ≤ tailLK L f ℓ := by
  unfold tailLK
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ a))
  simp [h]

theorem tailLK_nonneg (hf : ∀ a, 0 ≤ f a) (ℓ : ℝ) : 0 ≤ tailLK L f ℓ := by
  unfold tailLK
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (0 : LoopArg L 2)))
  split_ifs
  · exact hf _
  · exact le_rfl

/-- `T^{(L-K)}` is non-increasing (stated after (5.27)). -/
theorem tailLK_antitone (hf : ∀ a, 0 ≤ f a) : Antitone (tailLK L f) := by
  intro ℓ₁ ℓ₂ h
  refine Finset.sup'_le _ _ fun a _ => ?_
  split_ifs with h2
  · exact le_tailLK (h.trans h2)
  · exact tailLK_nonneg hf ℓ₁

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

/-- `J_{u,D}(ℓ) ≤ J*_{u,D}` for every `ℓ` (one half of (5.29)). -/
theorem ratioJ_le_jStar (hW : 0 < W) (hℓu : 0 < ℓu) (hf : ∀ a, 0 ≤ f a) (ℓ : ℝ) :
    ratioJ (tailLK L f) W ℓu ηu D ℓ ≤ jStar L f W ℓu ηu D := by
  have hJ := one_le_jStar (f := f) (ℓu := ℓu) (ηu := ηu) (D := D) hW hf
  have hTℓ := tailT_pos (ℓu := ℓu) (ηu := ηu) (D := D) hW ℓ
  have key : tailLK L f ℓ ≤ (jStar L f W ℓu ηu D - 1) * tailT W ℓu ηu D ℓ := by
    refine Finset.sup'_le _ _ fun a _ => ?_
    split_ifs with h
    · refine (le_jStar_sub_one_mul (ℓu := ℓu) (ηu := ηu) (D := D) hW a).trans ?_
      exact mul_le_mul_of_nonneg_left (tailT_antitone hℓu h) (by linarith)
    · exact mul_nonneg (by linarith) hTℓ.le
  rw [ratioJ]
  have := (div_le_iff₀ hTℓ).2 key
  linarith

/-- The maximum in (5.29) is attained: `J*_{u,D} ≤ J_{u,D}(ℓ)` at `ℓ = ‖a₁ - a₂‖` for a
maximizing pair `a`. -/
theorem exists_jStar_le_ratioJ (hW : 0 < W) :
    ∃ ℓ : ℝ, jStar L f W ℓu ηu D ≤ ratioJ (tailLK L f) W ℓu ηu D ℓ := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := LoopArg L 2))
    (fun a => f a / tailT W ℓu ηu D (zdist L (a 0 - a 1)))
  refine ⟨zdist L (a 0 - a 1), ?_⟩
  rw [jStar, ha, ratioJ]
  have hT := tailT_pos (ℓu := ℓu) (ηu := ηu) (D := D) hW (zdist L (a 0 - a 1) : ℝ)
  have := le_tailLK (f := f) (a := a) (le_refl (zdist L (a 0 - a 1) : ℝ))
  have := div_le_div_of_nonneg_right this hT.le
  linarith

/-- **(5.29)**: `J*_{u,D} = max_ℓ J_{u,D}(ℓ)`, with `J_{u,D} = ratioJ (tailLK f)` of (5.28). -/
theorem isGreatest_jStar (hW : 0 < W) (hℓu : 0 < ℓu) (hf : ∀ a, 0 ≤ f a) :
    IsGreatest (Set.range fun ℓ => ratioJ (tailLK L f) W ℓu ηu D ℓ) (jStar L f W ℓu ηu D) := by
  obtain ⟨ℓ, hℓ⟩ := exists_jStar_le_ratioJ (f := f) (ℓu := ℓu) (ηu := ηu) (D := D) hW
  refine ⟨⟨ℓ, le_antisymm (ratioJ_le_jStar hW hℓu hf ℓ) hℓ⟩, ?_⟩
  rintro _ ⟨ℓ', rfl⟩
  exact ratioJ_le_jStar hW hℓu hf ℓ'

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

/-- **The self-improving inequality (deterministic core of Step 2).**  Let `J` and the
threshold `Λ` be continuous on `[s, t]`, and let `B < Λ` there.  Suppose that at every time
`v`, the bound `J ≤ Λ` on `[s, v)` implies the improved bound `J(v) ≤ B(v)`.  Then
`J ≤ B` on all of `[s, t]`.

This is the argument of p. 59: if `T = inf{u : J(u) > Λ(u)} ≤ t`, then `J ≤ Λ` on `[s, T)`,
so `J(T) ≤ B(T) < Λ(T)`, while continuity forces `J(T) ≥ Λ(T)`.  No Grönwall inequality is
involved: the gain `B < Λ` is what closes the argument. -/
theorem self_improving {J Λ Bd : ℝ → ℝ} {s t : ℝ} (hJ : ContinuousOn J (Set.Icc s t))
    (hΛ : ContinuousOn Λ (Set.Icc s t)) (hB : ∀ v ∈ Set.Icc s t, Bd v < Λ v)
    (hstep : ∀ v ∈ Set.Icc s t, (∀ u ∈ Set.Ico s v, J u ≤ Λ u) → J v ≤ Bd v) :
    ∀ v ∈ Set.Icc s t, J v ≤ Bd v := by
  have key : ∀ u ∈ Set.Icc s t, J u ≤ Λ u := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw, hJw⟩ := hcon
    set S : Set ℝ := {u | u ∈ Set.Icc s t ∧ Λ u < J u} with hSdef
    have hne : S.Nonempty := ⟨w, hw, hJw⟩
    have hbdd : BddBelow S := ⟨s, fun u hu => hu.1.1⟩
    have hcl := csInf_mem_closure hne hbdd
    have hSsub : S ⊆ Set.Icc s t := fun u hu => hu.1
    have hv₀ : sInf S ∈ Set.Icc s t := closure_minimal hSsub isClosed_Icc hcl
    have hbelow : ∀ u ∈ Set.Ico s (sInf S), J u ≤ Λ u := by
      intro u hu
      by_contra h
      push Not at h
      have : sInf S ≤ u := csInf_le hbdd ⟨⟨hu.1, hu.2.le.trans hv₀.2⟩, h⟩
      linarith [hu.2]
    have h1 := hstep (sInf S) hv₀ hbelow
    have h2 : 0 ≤ J (sInf S) - Λ (sInf S) := by
      have hc : ContinuousWithinAt (fun u => J u - Λ u) S (sInf S) :=
        ((hJ.sub hΛ) (sInf S) hv₀).mono hSsub
      have hmem := hc.mem_closure_image hcl
      have hsub : (fun u => J u - Λ u) '' S ⊆ Set.Ici 0 := by
        rintro _ ⟨u, hu, rfl⟩
        simp only [Set.mem_Ici]
        linarith [hu.2]
      exact closure_minimal hsub isClosed_Ici hmem
    linarith [hB (sInf S) hv₀]
  intro v hv
  exact hstep v hv fun u hu => key u ⟨hu.1, hu.2.le.trans hv.2⟩

/-- **The stopping time (5.43)**: the first time in `[s, t]` at which `J` exceeds the
threshold `Λ` (and `t` if there is none). -/
noncomputable def stopTime (J Λ : ℝ → ℝ) (s t : ℝ) : ℝ :=
  sInf ({u | u ∈ Set.Icc s t ∧ Λ u < J u} ∪ {t})

/-- The stopped interval: `v ≤ T` iff `J ≤ Λ` on `[s, v)`. -/
theorem le_stopTime_iff {J Λ : ℝ → ℝ} {s t v : ℝ} (hv : v ∈ Set.Icc s t) :
    v ≤ stopTime J Λ s t ↔ ∀ u ∈ Set.Ico s v, J u ≤ Λ u := by
  have hbdd : BddBelow ({u | u ∈ Set.Icc s t ∧ Λ u < J u} ∪ {t}) := ⟨s, by
    rintro u (hu | hu)
    · exact hu.1.1
    · rw [Set.mem_singleton_iff.1 hu]; exact hv.1.trans hv.2⟩
  constructor
  · intro h u hu
    by_contra hlt
    push Not at hlt
    have : stopTime J Λ s t ≤ u :=
      csInf_le hbdd (Or.inl ⟨⟨hu.1, hu.2.le.trans hv.2⟩, hlt⟩)
    linarith [hu.2]
  · intro h
    refine le_csInf ⟨t, Or.inr rfl⟩ ?_
    rintro x (hx | hx)
    · by_contra hlt
      push Not at hlt
      have := h x ⟨hx.1.1, hlt⟩
      linarith [hx.2]
    · rw [Set.mem_singleton_iff.1 hx]; exact hv.2

/-- "Hence `P(T ≤ t)` is negligible": if `J ≤ Λ` on `[s, t]` (which `self_improving` gives
on the good event), the stopping time is `t`. -/
theorem stopTime_eq_right {J Λ : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (h : ∀ u ∈ Set.Icc s t, J u ≤ Λ u) : stopTime J Λ s t = t := by
  refine le_antisymm ?_ ?_
  · refine csInf_le ⟨s, ?_⟩ (Or.inr rfl)
    rintro u (hu | hu)
    · exact hu.1.1
    · rw [Set.mem_singleton_iff.1 hu]; exact hst
  · exact (le_stopTime_iff ⟨hst, le_rfl⟩).2 fun u hu => h u ⟨hu.1, hu.2.le⟩

end SelfImproving

/-! ### Propagating tail bounds through `U_{u,v}`: Lemma 7.1 + (7.2) -/

section Kernel

variable {L : ℕ} [NeZero L]

/-- The factor `Ξ = C (1 + 2L e^{-(log W)^{3/2}/8}) + m^{-2} + e^{(log W)^{3/4}}` of the kernel
bound `norm_Uker_le_of_tail`; it is `≤ W^τ` for every `τ > 0` once `L ≤ W²` (`xiK_le`). -/
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

/-- The charges `σ = (+, -)` of Step 2. -/
def sigPM : Fin 2 → Bool := ![true, false]

/-- `(L - K)_{u,(+,-),a}`, `a = (a₁, a₂)`. -/
noncomputable def lk (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) :
    LoopArg (B.L N) 2 → ℂ :=
  SumZeroDyn.lkT X E N u ω sigPM

/-- **(5.27)** along the flow: `T_{u,D}(ℓ) = (W ℓ_u η_u)^{-2} e^{-(ℓ/ℓ_u)^{1/2}} + W^{-D}`. -/
noncomputable def tT (B : Band Ω) (E : ℝ) (N : ℕ) (D u ℓ : ℝ) : ℝ :=
  tailT (B.W N) (B.ell N u) (etaT E u) D ℓ

/-- **(5.29)** along the flow: `J*_{u,D}` for `(L - K)_{u,(+,-)}`. -/
noncomputable def jS (X : Sample B) (E D : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  jStar (B.L N) (fun a => ‖lk X E N u ω a‖) (B.W N) (B.ell N u) (etaT E u) D

/-- The threshold of the stopping time: `Λ(u) = N^δ (η_s/η_u)^4` (the paper's `(η_s/η_t)^4`,
see *Deviations*). -/
noncomputable def thr (E : ℝ) (s : ℕ → ℝ) (δ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ δ * (etaT E (s N) / etaT E u) ^ 4

/-- **The stopping time (5.43)** `T = inf{u ∈ [s,t] : J*_{u,D} > Λ(u)}` (`t` if there is none). -/
noncomputable def tau (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (δ D : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  stopTime (fun u => jS X E D N u ω) (thr E s δ N) (s N) (t N)

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

theorem continuousOn_ell (B : Band Ω) (N : ℕ) {a b : ℝ} (hb : b < 1) :
    ContinuousOn (fun u => B.ell N u) (Set.Icc a b) := by
  simp only [Band.ell, ellHat]
  refine ContinuousOn.inf ?_ continuousOn_const
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun u hu => ?_
  have : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact (Real.sqrt_pos.2 (abs_pos.2 (by linarith [hu.2]))).ne'

/-- `u ↦ J*_{u,D}` is continuous on `[a, b]` if the entries of `L - K` are. -/
theorem continuousOn_jS (X : Sample B) {E : ℝ} (hE : |E| < 2) (D : ℝ) (N : ℕ) (ω : Ω)
    {a b : ℝ} (hb : b < 1)
    (hc : ∀ x : LoopArg (B.L N) 2, ContinuousOn (fun u => lk X E N u ω x) (Set.Icc a b)) :
    ContinuousOn (fun u => jS X E D N u ω) (Set.Icc a b) := by
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  refine ContinuousOn.add ?_ continuousOn_const
  refine ContinuousOn.finset_sup'_apply _ fun x _ => ?_
  have hℓ := continuousOn_ell B N (a := a) hb
  have hℓpos : ∀ u ∈ Set.Icc a b, 0 < B.ell N u := fun u hu =>
    Step3.ellHat_pos_of_lt_one hL1 (hu.2.trans_lt hb)
  have hT : ContinuousOn (fun u => tT B E N D u (zdist (B.L N) (x 0 - x 1))) (Set.Icc a b) := by
    unfold tT tailT
    refine ContinuousOn.add (ContinuousOn.mul ?_ ?_) continuousOn_const
    · refine ContinuousOn.inv₀ ?_ fun u hu => ?_
      · refine ContinuousOn.pow (ContinuousOn.mul (ContinuousOn.mul continuousOn_const hℓ) ?_) 2
        unfold etaT; fun_prop
      · have := hℓpos u hu
        have := etaT_pos' hE (hu.2.trans_lt hb)
        positivity
    · refine ContinuousOn.rexp (ContinuousOn.neg (ContinuousOn.sqrt ?_))
      exact ContinuousOn.div continuousOn_const hℓ fun u hu => (hℓpos u hu).ne'
  refine ContinuousOn.div (ContinuousOn.norm (hc x)) hT fun u _ => (tailT_pos hW _).ne'

end FlowDefs

/-! ### (5.39)–(5.41): one step of the stopped hierarchy, pathwise -/

section Step

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- The kernel estimate `norm_Uker_le_of_tail` for the flow, `σ = (+,-)`:
`|(U_{u,v,σ} ∘ A)_a| ≤ M (η_u/η_v)² Ξ T_{v,D}(‖a₁ - a₂‖)` if `|A_b| ≤ M T_{u,D}(‖b₁ - b₂‖)`. -/
theorem norm_Uker_flow (hE : |E| < 2) {N : ℕ} {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v)
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hW : exp 1 ≤ (B.W N : ℝ)) {D M : ℝ} (hM : 0 ≤ M)
    {A : LoopArg (B.L N) 2 → ℂ}
    (hA : ∀ b, ‖A b‖ ≤ M * tT B E N D u (zdist (B.L N) (b 0 - b 1))) (a : LoopArg (B.L N) 2) :
    ‖Uker (B.L N) (xiOf (mSigma E) sigPM) (u : ℂ) (v : ℂ) A a‖ ≤
      M * (etaT E u / etaT E v) ^ 2 * xiK (B.L N) (B.W N) (mE E).im *
        tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
  rw [sigPM_xi hE.le, etaT_ratio hE]
  have hW0 : (0 : ℝ) ≤ B.W N := by positivity
  have hAuv := flowScale_antitoneOn hW0 (B.L N) E (Set.mem_Iic.2 (huv.trans hv1.le))
    (Set.mem_Iic.2 hv1.le) huv
  exact norm_Uker_le_of_tail (B.three_le_L N) (mE_im_pos hE) (mE_im_le_one hE) hu0 huv hv0 hv1
    hW hM hAuv hA a

/-- The bound `Φ_v` of one step: with `R = η_s/η_v`, `Λ = Λ(v)`, `A = W ℓ_v η_v`,
`q = (ℓ_v/ℓ_s)²`, `ε = W L W^{-D}`, `m = Im m`,
`Φ = M_i R² Ξ + Ξ (e Λ² (36 m⁻¹ R² A⁻¹ + R² ε) + M_g m⁻¹ R² (q + A^{-1/3} Λ³)) + M_m (R² + 1)`.
The three groups are (5.39), (5.40) + (5.41), and the martingale (5.45). -/
noncomputable def phi (B : Band Ω) (E : ℝ) (s : ℕ → ℝ) (δ D Mi Mg Mm : ℝ) (N : ℕ) (v : ℝ) : ℝ :=
  Mi * (etaT E (s N) / etaT E v) ^ 2 * xiK (B.L N) (B.W N) (mE E).im
  + xiK (B.L N) (B.W N) (mE E).im *
    (exp 1 * thr E s δ N v ^ 2 *
        (36 * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (B.scale E N v)⁻¹
          + (etaT E (s N) / etaT E v) ^ 2 * ((B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D)))
      + Mg * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 *
        ((B.ell N v / B.ell N (s N)) ^ 2 + (B.scale E N v)⁻¹ ^ ((1 : ℝ) / 3) * thr E s δ N v ^ 3))
  + Mm * ((etaT E (s N) / etaT E v) ^ 2 + 1)

/-- **(5.39)–(5.41) and (5.21) at a time `v` before the stopping time, pathwise.**  Let the
hierarchy (5.20) hold, let `(L-K)_s ≤ M_i T_s` ((2.69)), let the drift other than
`E^{((L-K)×(L-K))}` obey (5.35) with constant `M_g`, and let the martingale at `v` obey (5.45)
with constant `M_m`.  If `J*_{u,D} ≤ Λ(u)` for `u ∈ [s, v)`, then
`|(L-K)_{v,a}| ≤ Φ_v T_{v,D}(‖a₁ - a₂‖)`. -/
theorem step_bound (H : SumZeroDyn.Hierarchy X E s t 0) (hE : |E| < 2) {N : ℕ} {ω : Ω}
    (hs0 : 0 ≤ s N) (ht1 : t N < 1) (hW : exp 1 ≤ (B.W N : ℝ))
    {D δ Mi Mg Mm : ℝ} (hMi : 0 ≤ Mi) (hMg : 0 ≤ Mg)
    (hinit : ∀ b, ‖lk X E N (s N) ω b‖ ≤ Mi * tT B E N D (s N) (zdist (B.L N) (b 0 - b 1)))
    (heG : ∀ u ∈ Set.Icc (s N) (t N), ∀ b,
      ‖H.F N u ω sigPM b - eLL (B.L N) (B.W N) (lk X E N u ω) b‖ ≤
        Mg * ((etaT E u)⁻¹ * ((B.ell N u / B.ell N (s N)) ^ 2 +
          (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 3) * jS X E D N u ω ^ 3)) *
          tT B E N D u (zdist (B.L N) (b 0 - b 1)))
    {v : ℝ} (hv : v ∈ Set.Icc (s N) (t N))
    (hmart : ∀ a, ‖H.mart N v ω sigPM a‖ ≤
      Mm * ((etaT E (s N) / etaT E v) ^ 2 + 1) * tT B E N D v (zdist (B.L N) (a 0 - a 1)))
    (hbelow : ∀ u ∈ Set.Ico (s N) v, jS X E D N u ω ≤ thr E s δ N u)
    (a : LoopArg (B.L N) 2) :
    ‖lk X E N v ω a‖ ≤ phi B E s δ D Mi Mg Mm N v * tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
  have hL3 := B.three_le_L N
  have hL1 : 1 ≤ B.L N := by omega
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hv0 : 0 ≤ v := hs0.trans hv.1
  have hv1 : v < 1 := hv.2.trans_lt ht1
  have hs1 : s N < 1 := hv.1.trans_lt hv1
  have hm0 := mE_im_pos hE
  have hm1 := mE_im_le_one hE
  set m := (mE E).im with hmdef
  set Ξ := xiK (B.L N) (B.W N) m with hΞ
  have hΞ0 : 0 ≤ Ξ := xiK_nonneg _ _ _
  set Tv := tT B E N D v (zdist (B.L N) (a 0 - a 1)) with hTv
  have hTv0 : 0 ≤ Tv := tailT_nonneg hW0.le _
  set R := etaT E (s N) / etaT E v with hR
  have hRe : R = (1 - s N) / (1 - v) := etaT_ratio hE _ _
  have h1v : 0 < 1 - v := by linarith
  have h1s : 0 < 1 - s N := by linarith
  have hR1 : 1 ≤ R := by rw [hRe, le_div_iff₀ h1v]; linarith [hv.1]
  set Λ := thr E s δ N v with hΛ
  set A := B.scale E N v with hA
  have hApos : 0 < A := B.scale_pos' hE N hv0 hv1
  set ε := (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D) with hε
  have hε0 : 0 ≤ ε := by positivity
  set q := (B.ell N v / B.ell N (s N)) ^ 2 with hq
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
  -- (5.20) at the time `v`
  have hdu := H.duhamel N ω sigPM v hv.1 hv.2 a
  have hlk : lk X E N v ω a = _ := hdu
  -- (5.39): the initial term
  have hI : ‖Uker (B.L N) (xiOf (mSigma E) sigPM) (s N : ℂ) (v : ℂ) (lk X E N (s N) ω) a‖
      ≤ Mi * R ^ 2 * Ξ * Tv :=
    norm_Uker_flow hE hs0 hv.1 hv0 hv1 hW hMi hinit a
  -- (5.40) + (5.41): the drift, pointwise in `u ∈ [s, v)`
  set c := m⁻¹ * ((1 - s N) / (1 - v) ^ 2) with hcdef
  set K : ℝ := exp 1 * Λ ^ 2 * (36 * c * A⁻¹ + R ^ 2 * ε)
      + Mg * c * (q + A⁻¹ ^ ((1 : ℝ) / 3) * Λ ^ 3) with hK
  have hdrift : ∀ u ∈ Set.Ico (s N) v,
      ‖Uker (B.L N) (xiOf (mSigma E) sigPM) (u : ℂ) (v : ℂ) (H.F N u ω sigPM) a‖ ≤ K * Ξ * Tv := by
    intro u hu
    have hu0 : 0 ≤ u := hs0.trans hu.1
    have hu1 : u < 1 := hu.2.trans hv1
    have huv : u ≤ v := hu.2.le
    have h1u : 0 < 1 - u := by linarith
    have huI : u ∈ Set.Icc (s N) (t N) := ⟨hu.1, huv.trans hv.2⟩
    have hℓu1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg hL1 hu0 hu1
    have hηu : 0 < etaT E u := etaT_pos' hE hu1
    have hAu : 0 < B.scale E N u := B.scale_pos' hE N hu0 hu1
    have hAuv : A ≤ B.scale E N u := flowScale_antitoneOn hW0.le (B.L N) E
      (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 hv1.le) huv
    have hJ1 : 1 ≤ jS X E D N u ω := one_le_jStar hW0 (fun b => norm_nonneg _)
    have hJΛ : jS X E D N u ω ≤ Λ := by
      refine (hbelow u hu).trans ?_
      rw [hΛ, thr, thr]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (div_nonneg (etaT_pos' hE hs1).le hηu.le) ?_ 4) (by positivity)
      rw [etaT_ratio hE, etaT_ratio hE]
      exact div_le_div_of_nonneg_left h1s.le h1v (by linarith)
    have hΛ1 : 1 ≤ Λ := hJ1.trans hJΛ
    set J := jS X E D N u ω with hJdef
    set ru := etaT E u / etaT E v with hru
    have hrue : ru = (1 - u) / (1 - v) := etaT_ratio hE _ _
    -- split `F = E^{((L-K)×(L-K))} + (F - E^{((L-K)×(L-K))})`
    have hsplit : H.F N u ω sigPM = eLL (B.L N) (B.W N) (lk X E N u ω) +
        (fun b => H.F N u ω sigPM b - eLL (B.L N) (B.W N) (lk X E N u ω) b) := by
      funext b; simp
    rw [hsplit, Uker_add, Pi.add_apply]
    refine (norm_add_le _ _).trans ?_
    -- (5.34) and the kernel bound
    set M₁ := exp 1 * J ^ 2 * (36 * ((etaT E u)⁻¹ * (B.scale E N u)⁻¹) + ε) with hM₁
    have hM₁0 : 0 ≤ M₁ := by positivity
    have h534 : ∀ b, ‖eLL (B.L N) (B.W N) (lk X E N u ω) b‖ ≤
        M₁ * tT B E N D u (zdist (B.L N) (b 0 - b 1)) := by
      intro b
      have := norm_eLL_le hL3 hW0 hℓu1 hηu D (lk X E N u ω) b
      refine this.trans (le_of_eq ?_)
      rw [hM₁, hε]; rfl
    have hU1 := norm_Uker_flow hE hu0 huv hv0 hv1 hW hM₁0 h534 a
    set M₂ := Mg * ((etaT E u)⁻¹ * ((B.ell N u / B.ell N (s N)) ^ 2 +
          (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 3) * J ^ 3)) with hM₂
    have hM₂0 : 0 ≤ M₂ := by positivity
    have hU2 := norm_Uker_flow hE hu0 huv hv0 hv1 hW hM₂0 (heG u huI) a
    refine (add_le_add hU1 hU2).trans ?_
    -- comparisons
    have hr2 : (etaT E u)⁻¹ * ru ^ 2 ≤ c := by
      rw [hcdef]
      rw [hrue, etaT_eq]
      rw [show ((1 - u) * m)⁻¹ * ((1 - u) / (1 - v)) ^ 2 = m⁻¹ * ((1 - u) / (1 - v) ^ 2) by
        field_simp]
      gcongr
      linarith [hu.1]
    have hru2 : ru ^ 2 ≤ R ^ 2 := by
      rw [hrue, hRe]
      exact pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right (by linarith [hu.1]) h1v.le) 2
    have hAinv : (B.scale E N u)⁻¹ ≤ A⁻¹ := inv_anti₀ hApos hAuv
    have hA13 : (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 3) ≤ A⁻¹ ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hAinv (by norm_num)
    have hq : (B.ell N u / B.ell N (s N)) ^ 2 ≤ q := by
      rw [hq]
      exact pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right (Step3.ellHat_mono huv hv1) hℓs.le) 2
    have hJ2 : J ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (by linarith) hJΛ 2
    have hJ3 : J ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ (by linarith) hJΛ 3
    have hηr : 0 ≤ (etaT E u)⁻¹ * ru ^ 2 := by positivity
    have hkey1 : M₁ * ru ^ 2 ≤ exp 1 * Λ ^ 2 * (36 * c * A⁻¹ + R ^ 2 * ε) := by
      rw [hM₁]
      have e1 : exp 1 * J ^ 2 * (36 * ((etaT E u)⁻¹ * (B.scale E N u)⁻¹) + ε) * ru ^ 2
          = exp 1 * J ^ 2 * (36 * ((etaT E u)⁻¹ * ru ^ 2) * (B.scale E N u)⁻¹ + ru ^ 2 * ε) := by
        ring
      rw [e1]
      gcongr
    have hkey2 : M₂ * ru ^ 2 ≤ Mg * c * (q + A⁻¹ ^ ((1 : ℝ) / 3) * Λ ^ 3) := by
      rw [hM₂]
      have e1 : Mg * ((etaT E u)⁻¹ * ((B.ell N u / B.ell N (s N)) ^ 2 +
          (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 3) * J ^ 3)) * ru ^ 2
          = Mg * ((etaT E u)⁻¹ * ru ^ 2) * ((B.ell N u / B.ell N (s N)) ^ 2 +
          (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 3) * J ^ 3) := by ring
      rw [e1]
      gcongr
    have hsum : M₁ * ru ^ 2 + M₂ * ru ^ 2 ≤ K := by rw [hK]; linarith
    calc M₁ * ru ^ 2 * Ξ * Tv + M₂ * ru ^ 2 * Ξ * Tv = (M₁ * ru ^ 2 + M₂ * ru ^ 2) * Ξ * Tv := by
          ring
      _ ≤ K * Ξ * Tv := by gcongr
  have hint : ‖∫ u in (s N)..v,
      Uker (B.L N) (xiOf (mSigma E) sigPM) (u : ℂ) (v : ℂ) (H.F N u ω sigPM) a‖
      ≤ K * Ξ * Tv * |v - s N| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
    filter_upwards [Measure.ae_ne volume v] with u hne hu
    rw [Set.uIoc_of_le hv.1] at hu
    exact hdrift u ⟨hu.1.le, lt_of_le_of_ne hu.2 hne⟩
  -- (5.45)
  have hM := hmart a
  -- assemble
  have hvs : |v - s N| = v - s N := abs_of_nonneg (by linarith [hv.1])
  rw [hvs] at hint
  have hK1 : K * (v - s N) ≤ exp 1 * Λ ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + Mg * m⁻¹ * R ^ 2 * (q + A⁻¹ ^ ((1 : ℝ) / 3) * Λ ^ 3) := by
    have hvs1 : v - s N ≤ 1 := by linarith
    have hvs0 : 0 ≤ v - s N := by linarith [hv.1]
    have hc : c * (v - s N) ≤ m⁻¹ * R ^ 2 := by
      rw [hcdef, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hRe, div_pow, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    have hΛ0 : 0 ≤ Λ := by rw [hΛ, thr]; positivity
    have hq0 : 0 ≤ q := by positivity
    have hB0 : 0 ≤ q + A⁻¹ ^ ((1 : ℝ) / 3) * Λ ^ 3 := by positivity
    have e1 : K * (v - s N) = exp 1 * Λ ^ 2 * (36 * (c * (v - s N)) * A⁻¹
            + R ^ 2 * ε * (v - s N))
          + Mg * (c * (v - s N)) * (q + A⁻¹ ^ ((1 : ℝ) / 3) * Λ ^ 3) := by
      rw [hK]; ring
    rw [e1]
    have t1 : 36 * (c * (v - s N)) * A⁻¹ ≤ 36 * m⁻¹ * R ^ 2 * A⁻¹ := by
      have := mul_le_mul_of_nonneg_right hc (inv_nonneg.2 hApos.le)
      linarith
    have t2 : R ^ 2 * ε * (v - s N) ≤ R ^ 2 * ε :=
      mul_le_of_le_one_right (by positivity) hvs1
    have t3 : Mg * (c * (v - s N)) * (q + A⁻¹ ^ ((1 : ℝ) / 3) * Λ ^ 3)
        ≤ Mg * m⁻¹ * R ^ 2 * (q + A⁻¹ ^ ((1 : ℝ) / 3) * Λ ^ 3) := by
      rw [mul_assoc Mg (m⁻¹)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hMg) hB0
    have t12 := add_le_add t1 t2
    have := mul_le_mul_of_nonneg_left t12 (by positivity : 0 ≤ exp 1 * Λ ^ 2)
    linarith
  calc ‖lk X E N v ω a‖
      ≤ ‖Uker (B.L N) (xiOf (mSigma E) sigPM) (s N : ℂ) (v : ℂ) (lk X E N (s N) ω) a‖
        + ‖∫ u in (s N)..v,
            Uker (B.L N) (xiOf (mSigma E) sigPM) (u : ℂ) (v : ℂ) (H.F N u ω sigPM) a‖
        + ‖H.mart N v ω sigPM a‖ := by
        rw [hlk]; exact norm_add₃_le
    _ ≤ Mi * R ^ 2 * Ξ * Tv + K * Ξ * Tv * (v - s N)
        + Mm * ((etaT E (s N) / etaT E v) ^ 2 + 1) * Tv := add_le_add (add_le_add hI hint) hM
    _ = Mi * R ^ 2 * Ξ * Tv + Ξ * (K * (v - s N)) * Tv + Mm * (R ^ 2 + 1) * Tv := by
        rw [hR]; ring
    _ ≤ Mi * R ^ 2 * Ξ * Tv + Ξ * (exp 1 * Λ ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
          + Mg * m⁻¹ * R ^ 2 * (q + A⁻¹ ^ ((1 : ℝ) / 3) * Λ ^ 3)) * Tv
        + Mm * (R ^ 2 + 1) * Tv := by gcongr
    _ = phi B E s δ D Mi Mg Mm N v * Tv := by
        rw [phi]; ring

end Step

/-! ### The arithmetic of (5.47) -/

section Arith

/-- The constant `4 + e + (36e + 2)/Im m` of `phi_arith`. -/
noncomputable def cStep (m : ℝ) : ℝ := 4 + exp 1 + (36 * exp 1 + 2) * m⁻¹

/-- **The arithmetic of (5.40)–(5.47).**  With `x = N^{δ/8}` (so `N^δ = x⁸` and the losses
are `N^{τ} = x`), the bound `Φ_v + 1` of one step is `≤ C x² R⁴`, provided
`W ℓ_v η_v ≥ x^{17} R^{10}`, `(W ℓ_v η_v)^{-1/3} x^{24} R^{10} ≤ 1` and
`W L W^{-D} x^{17} R^{10} ≤ 1` — all consequences of (2.72) with an `N^{-c}` gain, `δ ≤ c/24`,
`D ≥ 60`.  Since `C x² < x⁸`, the step improves the threshold `Λ = x⁸ R⁴`. -/
theorem phi_arith {x R Ξ m A ε q α : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) (hΞ : Ξ ≤ x)
    (hm0 : 0 < m) (hA : x ^ 17 * R ^ 10 ≤ A) (hε0 : 0 ≤ ε) (hε : ε * x ^ 17 * R ^ 10 ≤ 1)
    (hq0 : 0 ≤ q) (hq : q ≤ R) (hα0 : 0 ≤ α) (hα : α * (x ^ 24 * R ^ 10) ≤ 1) :
    x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε)
      + x * m⁻¹ * R ^ 2 * (q + α * (x ^ 8 * R ^ 4) ^ 3)) + x * (R ^ 2 + 1) + 1
      ≤ cStep m * x ^ 2 * R ^ 4 := by
  have hx0 : 0 < x := by linarith
  have hR0 : 0 < R := by linarith
  have he : 0 < exp 1 := exp_pos 1
  have hmi : 0 < m⁻¹ := inv_pos.2 hm0
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR24 : R ^ 2 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have hR34 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hP1 : 1 ≤ x ^ 2 * R ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (one_le_pow₀ hR)
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hxA : x ^ 17 * R ^ 10 * A⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hA0]; exact hA
  -- the seven terms
  have t1 : x * R ^ 2 * Ξ ≤ x ^ 2 * R ^ 4 := by
    calc x * R ^ 2 * Ξ ≤ x * R ^ 2 * x := by gcongr
      _ = x ^ 2 * R ^ 2 := by ring
      _ ≤ x ^ 2 * R ^ 4 := by gcongr
  have t2 : Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
      ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 4) := by
    calc Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        = 36 * exp 1 * m⁻¹ * (Ξ * x ^ 16 * R ^ 10 * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * (x * x ^ 16 * R ^ 10 * A⁻¹) := by gcongr
      _ = 36 * exp 1 * m⁻¹ * (x ^ 17 * R ^ 10 * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * 1 := by gcongr
      _ ≤ 36 * exp 1 * m⁻¹ * (x ^ 2 * R ^ 4) := by gcongr
  have t3 : Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε)) ≤ exp 1 * (x ^ 2 * R ^ 4) := by
    calc Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε))
        = exp 1 * (Ξ * x ^ 16 * R ^ 10 * ε) := by ring
      _ ≤ exp 1 * (x * x ^ 16 * R ^ 10 * ε) := by gcongr
      _ = exp 1 * (ε * x ^ 17 * R ^ 10) := by ring
      _ ≤ exp 1 * 1 := by gcongr
      _ ≤ exp 1 * (x ^ 2 * R ^ 4) := by gcongr
  have t4 : Ξ * (x * m⁻¹ * R ^ 2 * q) ≤ m⁻¹ * (x ^ 2 * R ^ 4) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * q) ≤ x * (x * m⁻¹ * R ^ 2 * R) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 3) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 4) := by gcongr
  have t5 : Ξ * (x * m⁻¹ * R ^ 2 * (α * (x ^ 8 * R ^ 4) ^ 3)) ≤ m⁻¹ * (x ^ 2 * R ^ 4) := by
    calc Ξ * (x * m⁻¹ * R ^ 2 * (α * (x ^ 8 * R ^ 4) ^ 3))
        ≤ x * (x * m⁻¹ * R ^ 2 * (α * (x ^ 8 * R ^ 4) ^ 3)) := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) * (α * (x ^ 24 * R ^ 10)) := by ring
      _ ≤ m⁻¹ * (x ^ 2 * R ^ 4) * 1 := by gcongr
      _ = m⁻¹ * (x ^ 2 * R ^ 4) := mul_one _
  have t6 : x * (R ^ 2 + 1) ≤ 2 * (x ^ 2 * R ^ 4) := by nlinarith
  have hsplit : x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 *
        (36 * m⁻¹ * R ^ 2 * A⁻¹ + R ^ 2 * ε) + x * m⁻¹ * R ^ 2 * (q + α * (x ^ 8 * R ^ 4) ^ 3))
        + x * (R ^ 2 + 1) + 1
      = x * R ^ 2 * Ξ + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (36 * m⁻¹ * R ^ 2 * A⁻¹))
        + Ξ * (exp 1 * (x ^ 8 * R ^ 4) ^ 2 * (R ^ 2 * ε)) + Ξ * (x * m⁻¹ * R ^ 2 * q)
        + Ξ * (x * m⁻¹ * R ^ 2 * (α * (x ^ 8 * R ^ 4) ^ 3)) + x * (R ^ 2 + 1) + 1 := by ring
  rw [hsplit, cStep]
  nlinarith

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

/-- **(2.72) with a gain**, `N^c (η_s/η_t)^{30} ≤ W ℓ_t η_t`, implies (2.72). -/
theorem cond272_of_strict (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) : Cond272 B E s t := by
  filter_upwards [hreg, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have ht := ht1 N
  have hs1 : s N < 1 := (hst N).trans_lt ht
  have hR := etaT_ratio hE (s N) (t N)
  have h1t : 0 < 1 - t N := by linarith
  have h1s : 0 < 1 - s N := by linarith
  have hR0 : 0 < (1 - s N) / (1 - t N) := div_pos h1s h1t
  rw [hR] at hN
  have hc : 1 ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0.le
  have h1 : ((1 - s N) / (1 - t N)) ^ 30 ≤ B.scale E N (t N) := by
    have := pow_pos hR0 30
    nlinarith
  have hpos : 0 < ((1 - s N) / (1 - t N)) ^ 30 := pow_pos hR0 30
  calc (B.scale E N (t N))⁻¹ ≤ (((1 - s N) / (1 - t N)) ^ 30)⁻¹ := inv_anti₀ hpos h1
    _ = ((1 - t N) / (1 - s N)) ^ 30 := by rw [← inv_pow, inv_div]

theorem natCast_rpow_pow (N : ℕ) (a : ℝ) (k : ℕ) :
    ((N : ℝ) ^ a) ^ k = (N : ℝ) ^ (a * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]

/-- **The scale facts used by one step**, eventually in `N`, uniformly in `v ∈ [s, t]`, with
`x = N^{δ/8}`: the hypotheses of `phi_arith`, `e ≤ W`, `Ξ ≤ x`, `C < x⁶`, and `W ℓ_s η_s ≥ 1`. -/
theorem eventually_step_facts (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : 24 * δ ≤ c) (hD : 60 ≤ D) :
    ∀ᶠ N : ℕ in atTop, exp 1 ≤ (B.W N : ℝ) ∧ 1 ≤ (N : ℝ) ^ (δ / 8) ∧
      cStep (mE E).im < ((N : ℝ) ^ (δ / 8)) ^ 6 ∧
      xiK (B.L N) (B.W N) (mE E).im ≤ (N : ℝ) ^ (δ / 8) ∧ 1 ≤ B.scale E N (s N) ∧
      ∀ v : TimeIcc s t N,
        ((N : ℝ) ^ (δ / 8)) ^ 17 * (etaT E (s N) / etaT E v) ^ 10 ≤ B.scale E N v ∧
        (B.scale E N v)⁻¹ ^ ((1 : ℝ) / 3) *
          (((N : ℝ) ^ (δ / 8)) ^ 24 * (etaT E (s N) / etaT E v) ^ 10) ≤ 1 ∧
        (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D) * ((N : ℝ) ^ (δ / 8)) ^ 17 *
          (etaT E (s N) / etaT E v) ^ 10 ≤ 1 := by
  have h272 := cond272_of_strict hE hst ht1 hc0 hreg
  have hδ16 : 0 < δ / 16 := by positivity
  filter_upwards [hreg, SumZeroDyn.flow_crude hE hs0 hst ht1 h272, B.dim, eventually_le_W_sq B,
    (tendsto_W B).eventually_ge_atTop (exp 400),
    (tendsto_W B).eventually (eventually_exp_mul_log_rpow_le 1 hδ16),
    eventually_le_rpow (2 * cTail + ((mE E).im ^ 2)⁻¹) hδ16, eventually_le_rpow 2 hδ16,
    eventually_le_rpow (cStep (mE E).im + 1) (by positivity : (0 : ℝ) < 3 * δ / 4),
    eventually_ge_atTop 1] with N hreg' hcr hdim hW2 hWe hWexp hC1 hC2 hC3 hN1
  obtain ⟨hLN, hWN, -, hsc⟩ := hcr
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : ℝ) < B.W N := by linarith
  set x := (N : ℝ) ^ (δ / 8) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow hN (by positivity)
  have hm0 := mE_im_pos hE
  set m := (mE E).im with hm
  refine ⟨le_trans (exp_le_exp.2 (by norm_num)) hWe, hx1, ?_, ?_, (hsc ⟨s N, le_rfl, hst N⟩).1, ?_⟩
  · -- `C < x⁶`
    rw [hx, natCast_rpow_pow]
    have : δ / 8 * ((6 : ℕ) : ℝ) = 3 * δ / 4 := by push_cast; ring
    rw [this]; linarith
  · -- `Ξ ≤ x`
    have hLW : (B.L N : ℝ) ≤ (B.W N : ℝ) ^ 2 := hLN.trans hW2
    have hexpL : 2 * (B.L N : ℝ) * exp (-(log (B.W N) ^ (3 / 2 : ℝ) / 8)) ≤ 1 := by
      have := two_mul_sq_mul_exp_le hWe
      have h0 := exp_pos (-(log (B.W N) ^ (3 / 2 : ℝ) / 8))
      nlinarith
    have hct := cTail_nonneg
    have h1 : cTail * (1 + 2 * B.L N * exp (-(log (B.W N) ^ (3 / 2 : ℝ) / 8))) ≤ 2 * cTail := by
      nlinarith
    have h2 : exp (log (B.W N) ^ (3 / 4 : ℝ)) ≤ (N : ℝ) ^ (δ / 16) := by
      have := hWexp
      rw [one_mul] at this
      exact this.trans (Real.rpow_le_rpow hW0.le hWN hδ16.le)
    have hsplit : (N : ℝ) ^ (δ / 16) * (N : ℝ) ^ (δ / 16) = x := by
      rw [← Real.rpow_add hN0, hx]; ring_nf
    unfold xiK
    have h3 : 0 ≤ (N : ℝ) ^ (δ / 16) := Real.rpow_nonneg hN0.le _
    nlinarith
  · intro v
    have hv0 : (0 : ℝ) ≤ (v : ℝ) := (hs0 N).trans v.2.1
    have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have h1v : 0 < 1 - (v : ℝ) := by linarith
    have h1t : 0 < 1 - t N := by linarith [ht1 N]
    have h1s : 0 < 1 - s N := by linarith
    set R := etaT E (s N) / etaT E v with hR
    have hRe : R = (1 - s N) / (1 - v) := etaT_ratio hE _ _
    have hR1 : 1 ≤ R := by rw [hRe, le_div_iff₀ h1v]; linarith [v.2.1]
    have hRt : R ≤ etaT E (s N) / etaT E (t N) := by
      rw [hRe, etaT_ratio hE]
      exact div_le_div_of_nonneg_left h1s.le h1t (by linarith [v.2.2])
    have hRN : R ≤ N := by
      rw [hRe]
      calc (1 - s N) / (1 - v) ≤ 1 / (1 - v) :=
            div_le_div_of_nonneg_right (by linarith [hs0 N]) h1v.le
        _ = (1 - (v : ℝ))⁻¹ := one_div _
        _ ≤ N := (hsc v).2.2
    have hAv : B.scale E N (t N) ≤ B.scale E N v := flowScale_antitoneOn hW0.le (B.L N) E
      (Set.mem_Iic.2 hv1.le) (Set.mem_Iic.2 (ht1 N).le) v.2.2
    have hx192 : x ^ 192 ≤ (N : ℝ) ^ c := by
      rw [hx, natCast_rpow_pow]
      exact Real.rpow_le_rpow_of_exponent_le hN (by push_cast; linarith)
    have hbig : x ^ 192 * R ^ 30 ≤ B.scale E N v := by
      calc x ^ 192 * R ^ 30 ≤ (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 := by
            gcongr
        _ ≤ _ := hreg'.trans hAv
    have hApos : 0 < B.scale E N v := B.scale_pos' hE N hv0 hv1
    have hR0 : 0 ≤ R := by linarith
    have hx0 : 0 ≤ x := by linarith
    refine ⟨?_, ?_, ?_⟩
    · refine le_trans ?_ hbig
      have : x ^ 17 ≤ x ^ 192 := pow_le_pow_right₀ hx1 (by norm_num)
      have : R ^ 10 ≤ R ^ 30 := pow_le_pow_right₀ hR1 (by norm_num)
      gcongr
    · -- `A^{-1/3} x^{24} R^{10} ≤ 1`
      have hy : (x ^ 64 * R ^ 10) ^ 3 = x ^ 192 * R ^ 30 := by ring
      have hy0 : 0 < x ^ 64 * R ^ 10 := by positivity
      have hA13 : x ^ 64 * R ^ 10 ≤ B.scale E N v ^ ((1 : ℝ) / 3) := by
        have h := Real.rpow_le_rpow (by positivity) (hy ▸ hbig) (by norm_num : (0 : ℝ) ≤ 1 / 3)
        have e : ((x ^ 64 * R ^ 10) ^ 3) ^ ((1 : ℝ) / 3) = x ^ 64 * R ^ 10 := by
          rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast hy0.le (by norm_num)
        rwa [e] at h
      rw [Real.inv_rpow hApos.le, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hApos _), mul_one]
      refine le_trans ?_ hA13
      have : x ^ 24 ≤ x ^ 64 := pow_le_pow_right₀ hx1 (by norm_num)
      gcongr
    · -- `W L W^{-D} x^{17} R^{10} ≤ 1`
      have hWD : (N : ℝ) ^ 30 ≤ (B.W N : ℝ) ^ D := by
        calc (N : ℝ) ^ 30 ≤ ((B.W N : ℝ) ^ 2) ^ 30 := pow_le_pow_left₀ hN0.le hW2 30
          _ = (B.W N : ℝ) ^ ((60 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; ring
          _ ≤ (B.W N : ℝ) ^ D := Real.rpow_le_rpow_of_exponent_le hW1 (by push_cast; linarith)
      have hWLN : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
      have hxN : x ≤ N := by
        rw [hx]
        calc (N : ℝ) ^ (δ / 8) ≤ (N : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hN (by linarith)
          _ = N := Real.rpow_one _
      have hWDpos : 0 < (B.W N : ℝ) ^ D := Real.rpow_pos_of_pos hW0 D
      rw [Real.rpow_neg hW0.le]
      have h1 : (B.W N : ℝ) * B.L N * ((B.W N : ℝ) ^ D)⁻¹ * x ^ 17 * R ^ 10
          ≤ N * ((N : ℝ) ^ 30)⁻¹ * N ^ 17 * N ^ 10 := by
        gcongr
      refine h1.trans ?_
      have e : (N : ℝ) * ((N : ℝ) ^ 30)⁻¹ * N ^ 17 * N ^ 10 = ((N : ℝ) ^ 2)⁻¹ := by
        field_simp
      rw [e]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ hN)

end FlowFacts

/-! ### The random-layer inputs of Step 2 -/

section Hyp

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

theorem idx_sigPM {L : ℕ} (b : LoopArg L 2) : LoopData.idx (sigPM, b) = pmLoop (b 0) (b 1) := by
  simp [LoopData.idx, pmLoop, sigPM, List.ofFn_succ]

theorem norm_lk_eq (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) (b : LoopArg (B.L N) 2) :
    ‖lk X E N u ω b‖ = X.lkErr E N u ω (pmLoop (b 0) (b 1)) := by
  rw [lk, SumZeroDyn.norm_lkT, idx_sigPM]

/-- **The random-layer inputs of Step 2** (CLAUDE.md rule 6: hypotheses, never axioms).

* `H` — **(5.20)**: the integrated loop hierarchy, i.e. `RBM.SumZeroDyn.Hierarchy` at loop
  length `2` (T58/T60 interface; only its fields `F`, `mart`, `duhamel` are used).
* `eG` — **(5.35)**: the drift of (5.15) *other than* `E^{((L-K)×(L-K))}` (that is `E^{(G)}`,
  plus the `l_K > 2` terms, which the paper's (5.21) for `n = 2` does not list) obeys
  `≺ η_u^{-1} ((ℓ_u/ℓ_s)² + (W ℓ_u η_u)^{-1/3} (J*_{u,D})³) T_{u,D}(‖a₁ - a₂‖)`, uniformly in
  `u ∈ [s, t]` and `a`.
* `mart` — **(5.44)–(5.46)**: the stopped martingale term.  For `v ≤ T` (the stopping time
  (5.43) with threshold `Λ(u) = N^δ (η_s/η_u)⁴`, `0 < δ ≤ δ₀`),
  `|∫_s^v U_{u,v} ∘ E^{(M)}_u|_a ≺ ((η_s/η_v)² + 1) T_{v,D}(‖a₁ - a₂‖)`, uniformly in `v`
  and `a` (BDG + the quadratic variation bound (5.44), (5.42) + the net (5.46)).
* `cont` — w.h.p. the entries of `L - K` are continuous in `u ∈ [s, t]` (continuity of the
  flow; implicit in the paper's stopping-time argument). -/
structure Hyp (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) where
  /-- (5.20), the integrated hierarchy. -/
  H : SumZeroDyn.Hierarchy X E s t 0
  /-- (5.35), for the drift minus `E^{((L-K)×(L-K))}`. -/
  eG : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopArg (B.L N) 2) ω =>
      ‖H.F N p.1 ω sigPM p.2 - eLL (B.L N) (B.W N) (lk X E N p.1 ω) p.2‖)
    (fun N p ω => (etaT E p.1)⁻¹ * ((B.ell N p.1 / B.ell N (s N)) ^ 2 +
        (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 3) * jS X E D N p.1 ω ^ 3) *
      tT B E N D p.1 (zdist (B.L N) (p.2 0 - p.2 1)))
  /-- The range `0 < δ ≤ δ₀` of thresholds for which (5.44)–(5.46) is asserted. -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  /-- (5.44)–(5.46), the stopped martingale. -/
  mart : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopArg (B.L N) 2) ω =>
      if (p.1 : ℝ) ≤ tau X E s t δ D N ω then ‖H.mart N p.1 ω sigPM p.2‖ else 0)
    (fun N p _ => ((etaT E (s N) / etaT E p.1) ^ 2 + 1) *
      tT B E N D p.1 (zdist (B.L N) (p.2 0 - p.2 1)))
  /-- Continuity of the paths `u ↦ (L - K)_{u,a}` on `[s, t]`, with high probability. -/
  cont : HighProb B.P (fun N => {ω | ∀ a : LoopArg (B.L N) 2,
    ContinuousOn (fun u => lk X E N u ω a) (Set.Icc (s N) (t N))})

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

theorem continuousOn_thr (hE : |E| < 2) (δ : ℝ) (N : ℕ) {a b : ℝ} (hb : b < 1) :
    ContinuousOn (thr E s δ N) (Set.Icc a b) := by
  unfold thr
  refine ContinuousOn.mul continuousOn_const (ContinuousOn.pow ?_ 4)
  refine ContinuousOn.div continuousOn_const (by unfold etaT; fun_prop) fun u hu => ?_
  exact (etaT_pos' hE (hu.2.trans_lt hb)).ne'

/-- **(5.47)**: with high probability, for all `v ∈ [s, t]`,
`J*_{v,D} ≤ C N^{δ/4} (η_s/η_v)⁴`, for every `0 < δ ≤ min(δ₀, c/24, 1)` and `D ≥ 60`.

Proof: on the intersection of the good events of (2.69), (5.35), (5.44)–(5.46) and path
continuity, `step_bound` and `phi_arith` give the premise of `self_improving` with threshold
`Λ(u) = N^δ (η_s/η_u)⁴` and improved bound `C N^{δ/4} (η_s/η_u)⁴ < Λ(u)`. -/
theorem jS_highProb (Hy : Hyp X E s t) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hB : BoundsCore X E s) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : 24 * δ ≤ c) (hδ₀ : δ ≤ Hy.δ₀) (hD : 60 ≤ D) :
    HighProb B.P (fun N => {ω | ∀ v : TimeIcc s t N,
      jS X E D N v ω ≤ cStep (mE E).im * ((N : ℝ) ^ (δ / 8)) ^ 2 *
        (etaT E (s N) / etaT E v) ^ 4}) := by
  have hτ : 0 < δ / 8 := by positivity
  have hD0 : 0 < D := by linarith
  have G1 := (hB.decay D hD0).highProb hτ
  have G2 := (Hy.eG D hD0).highProb hτ
  have G3 := (Hy.mart δ hδ0 hδ₀ D hD0).highProb hτ
  refine (((G1.inter G2).inter G3).inter Hy.cont).mono ?_
  filter_upwards [eventually_step_facts hE hs0 hst ht1 hc0 hreg hδ0 hδ1 hδc hD] with N hF
  rintro ω ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  obtain ⟨hWe, hx1, hCx, hΞ, hAs, hvF⟩ := hF
  simp only [Set.mem_ofPred_eq] at h1 h2 h3 h4 ⊢
  set x := (N : ℝ) ^ (δ / 8) with hx
  have hx0 : 0 ≤ x := by linarith
  have hm0 := mE_im_pos hE
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hN8 : (N : ℝ) ^ δ = x ^ 8 := by
    rw [hx, natCast_rpow_pow]; congr 1; push_cast; ring
  -- the pathwise inputs of `step_bound`
  have hinit : ∀ b : LoopArg (B.L N) 2,
      ‖lk X E N (s N) ω b‖ ≤ x * tT B E N D (s N) (zdist (B.L N) (b 0 - b 1)) := by
    intro b
    rw [norm_lk_eq]
    exact (h1 (b 0, b 1)).trans (mul_le_mul_of_nonneg_left (decayProf_le_tT hAs _ _) hx0)
  have heG : ∀ u ∈ Set.Icc (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      ‖Hy.H.F N u ω sigPM b - eLL (B.L N) (B.W N) (lk X E N u ω) b‖ ≤
        x * ((etaT E u)⁻¹ * ((B.ell N u / B.ell N (s N)) ^ 2 +
          (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 3) * jS X E D N u ω ^ 3)) *
          tT B E N D u (zdist (B.L N) (b 0 - b 1)) := by
    intro u hu b
    have := h2 (⟨u, hu⟩, b)
    simpa only [mul_assoc] using this
  refine fun v => self_improving (J := fun u => jS X E D N u ω) (Λ := thr E s δ N)
    (Bd := fun v => cStep (mE E).im * x ^ 2 * (etaT E (s N) / etaT E v) ^ 4)
    (continuousOn_jS X hE D N ω (ht1 N) h4) (continuousOn_thr hE δ N (ht1 N))
    ?_ ?_ v v.2
  · -- `C x² R⁴ < x⁸ R⁴`
    intro v hv
    have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
    have hR0 : 0 < etaT E (s N) / etaT E v := div_pos (etaT_pos' hE hs1) (etaT_pos' hE hv1)
    show cStep (mE E).im * x ^ 2 * (etaT E (s N) / etaT E v) ^ 4 < thr E s δ N v
    rw [thr, hN8]
    have hx2 : 0 < x ^ 2 := by positivity
    have : x ^ 8 = x ^ 6 * x ^ 2 := by ring
    rw [this]
    have hR4 : 0 < (etaT E (s N) / etaT E v) ^ 4 := by positivity
    have := mul_lt_mul_of_pos_right hCx hx2
    exact mul_lt_mul_of_pos_right this hR4
  · -- one step
    intro v hv hbelow
    have hv0 : 0 ≤ v := (hs0 N).trans hv.1
    have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
    have hmart : ∀ a : LoopArg (B.L N) 2, ‖Hy.H.mart N v ω sigPM a‖ ≤
        x * ((etaT E (s N) / etaT E v) ^ 2 + 1) * tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
      intro a
      have hle : v ≤ tau X E s t δ D N ω := (le_stopTime_iff hv).2 hbelow
      have := h3 (⟨v, hv⟩, a)
      simp only [hle, ↓reduceIte] at this
      simpa only [mul_assoc] using this
    have hstep := fun a => step_bound X Hy.H hE (hs0 N) (ht1 N) hWe hx0 hx0 hinit heG hv
      hmart hbelow a
    have hJ := jStar_le hW0 hstep
    refine hJ.trans ?_
    -- the arithmetic
    obtain ⟨hvA, hvα, hvε⟩ := hvF ⟨v, hv⟩
    set R := etaT E (s N) / etaT E v with hR
    have hRe : R = (1 - s N) / (1 - v) := etaT_ratio hE _ _
    have h1v : 0 < 1 - v := by linarith
    have hR1 : 1 ≤ R := by rw [hRe, le_div_iff₀ h1v]; linarith [hv.1]
    have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
    have hq : (B.ell N v / B.ell N (s N)) ^ 2 ≤ R := by
      have h := Step3.ellHat_le_sqrt_mul (L := B.L N) hv.1 hv1
      have h' : B.ell N v / B.ell N (s N) ≤ √((1 - s N) / (1 - v)) := by
        rw [div_le_iff₀ hℓs]; exact h
      have h0 : 0 ≤ B.ell N v / B.ell N (s N) := by
        have := Step3.ellHat_pos_of_lt_one (L := B.L N) hL1 hv1
        exact div_nonneg this.le hℓs.le
      calc (B.ell N v / B.ell N (s N)) ^ 2 ≤ (√((1 - s N) / (1 - v))) ^ 2 :=
            pow_le_pow_left₀ h0 h' 2
        _ = R := by rw [Real.sq_sqrt (by positivity), hRe]
    have hthr : thr E s δ N v = x ^ 8 * R ^ 4 := by rw [thr, hN8]
    have key := phi_arith (x := x) (R := R) (Ξ := xiK (B.L N) (B.W N) (mE E).im)
      (m := (mE E).im) (A := B.scale E N v) (ε := (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D))
      (q := (B.ell N v / B.ell N (s N)) ^ 2) (α := (B.scale E N v)⁻¹ ^ ((1 : ℝ) / 3))
      hx1 hR1 hΞ hm0 hvA (by positivity) hvε (by positivity) hq
      (Real.rpow_nonneg (inv_nonneg.2 (B.scale_nonneg E N hv1.le)) _) hvα
    refine le_trans (le_of_eq ?_) key
    rw [phi, hthr]

end Main

/-! ### (5.47) as a `≺` statement, and (2.76) -/

section Conclusions

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **(5.47)** `J*_{u,D} ≺ (η_s/η_u)⁴`, uniformly in `u ∈ [s, t]`, for every `D ≥ 60`.
(In particular `P(T ≤ t)` is negligible for the stopping time (5.43).) -/
theorem jS_stochDom (Hy : Hyp X E s t) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hB : BoundsCore X E s) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    {D : ℝ} (hD : 60 ≤ D) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => jS X E D N u ω)
      (fun N u _ => (etaT E (s N) / etaT E u) ^ 4) := by
  refine SumZeroDyn.stochDom_of_good fun τ hτ => ?_
  set δ := min (min τ Hy.δ₀) (min (c / 24) 1) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hτ Hy.δ₀_pos) (lt_min (by positivity) one_pos)
  have hδτ : δ ≤ τ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₀ : δ ≤ Hy.δ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hδc : 24 * δ ≤ c := by
    have : δ ≤ c / 24 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨_, jS_highProb X Hy hE hs0 hst ht1 hB hc0 hreg hδ0 hδ1 hδc hδ₀ hD, ?_⟩
  filter_upwards [eventually_step_facts (B := B) hE hs0 hst ht1 hc0 hreg hδ0 hδ1 hδc hD,
    eventually_ge_atTop 1] with N hF hN1 ω hω u
  obtain ⟨-, hx1, hCx, -⟩ := hF
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hR0 : 0 ≤ (etaT E (s N) / etaT E u) ^ 4 := by
    have := div_pos (etaT_pos' hE hs1) (etaT_pos' hE hu1); positivity
  refine (hω u).trans ?_
  set x := (N : ℝ) ^ (δ / 8) with hx
  have hN8 : (N : ℝ) ^ δ = x ^ 8 := by
    rw [hx, natCast_rpow_pow]; congr 1; push_cast; ring
  have h1 : cStep (mE E).im * x ^ 2 ≤ (N : ℝ) ^ τ := by
    calc cStep (mE E).im * x ^ 2 ≤ x ^ 6 * x ^ 2 := by
          have : 0 ≤ x ^ 2 := by positivity
          nlinarith
      _ = (N : ℝ) ^ δ := by rw [hN8]; ring
      _ ≤ (N : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hN hδτ
  exact mul_le_mul_of_nonneg_right h1 hR0

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

/-- **(2.76)** (Step 2) in exactly the shape of the field `RBM.Steps.aprioriDecay`: for
`σ = (+,-)` and every `D > 0`,
`|L_{u,σ,a} - K_{u,σ,a}| ≺ (η_s/η_u)⁴ (W ℓ_u η_u)^{-2} (e^{-(|a₁-a₂|/ℓ_u)^{1/2}} + W^{-D})`,
uniformly in `u ∈ [s, t]` and `a`. -/
theorem aprioriDecay (Hy : Hyp X E s t) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hB : BoundsCore X E s) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) := by
  intro D₀ hD₀
  set D := max (D₀ + 4) 60 with hDdef
  have hD : 60 ≤ D := le_max_right _ _
  have hDD : D₀ + 4 ≤ D := le_max_left _ _
  have hJ := (jS_stochDom X Hy hE hs0 hst ht1 hB hc0 hreg hD).precomp_param
    (V := fun N => TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) fun N p => p.1
  have hW0 : ∀ N, (0 : ℝ) < B.W N := fun N => by exact_mod_cast B.W_pos N
  have hT0 : ∀ N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) (_ : Ω),
      0 ≤ tT B E N D p.1 (zdist (B.L N) (p.2.1 - p.2.2)) :=
    fun N p _ => tailT_nonneg (hW0 N).le _
  have hR0 : ∀ N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) (_ : Ω),
      0 ≤ (etaT E (s N) / etaT E p.1) ^ 4 := fun N p _ => by
    have := div_pos (etaT_pos' hE ((hst N).trans_lt (ht1 N)))
      (etaT_pos' hE (p.1.2.2.trans_lt (ht1 N)))
    positivity
  have hmul := StochDom.mul hT0 hR0 hJ (StochDom.refl hT0)
  have h272 := cond272_of_strict hE hst ht1 hc0 hreg
  refine Step3.stochDom_mono (ζ := fun N p ω => (etaT E (s N) / etaT E p.1) ^ 4 *
      tT B E N D p.1 (zdist (B.L N) (p.2.1 - p.2.2))) ?_ 1 ?_ ?_
  · intro N p ω
    have := hR0 N p ω
    have hA := B.scale_nonneg E N (p.1.2.2.trans (ht1 N).le)
    have : 0 ≤ B.decayProf N p.1 D₀ p.2.1 p.2.2 := by unfold Band.decayProf; positivity
    positivity
  · filter_upwards [SumZeroDyn.flow_crude hE hs0 hst ht1 h272,
      eventually_le_W_sq B] with
      N hcr hW2 p ω
    obtain ⟨-, -, -, hsc⟩ := hcr
    rw [one_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hR0 N p ω)
    exact tT_le_decayProf hDD (hsc p.1).1 ((hsc p.1).2.1.trans hW2) _ _
  · refine StochDom.of_le_left (fun N p ω => ?_) hmul
    simp only [Pi.mul_apply]
    have h := le_jStar_mul (f := fun b => ‖lk X E N p.1 ω b‖) (ℓu := B.ell N p.1)
      (ηu := etaT E p.1) (D := D) (hW0 N) ![p.2.1, p.2.2]
    rw [norm_lk_eq] at h
    simpa [jS, tT] using h

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

/-- Under (2.72) with a gain: `(η_s/η_u)⁴ ≤ W ℓ_u η_u` and `N^c ≤ W ℓ_u η_u` for `u ∈ [s, t]`. -/
theorem eventually_R4_le_scale (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT E (s N) / etaT E u) ^ 4 ≤ B.scale E N u ∧ (N : ℝ) ^ c ≤ B.scale E N u := by
  filter_upwards [hreg, eventually_ge_atTop 1] with N hN hN1 u
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hW0 : (0 : ℝ) ≤ B.W N := by positivity
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have h1s : 0 < 1 - s N := by linarith
  have hAv : B.scale E N (t N) ≤ B.scale E N u := flowScale_antitoneOn hW0 (B.L N) E
    (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 (ht1 N).le) u.2.2
  have hR1 : 1 ≤ etaT E (s N) / etaT E u := by
    rw [etaT_ratio hE, le_div_iff₀ h1u]; linarith [u.2.1]
  have hRt : etaT E (s N) / etaT E u ≤ etaT E (s N) / etaT E (t N) := by
    rw [etaT_ratio hE, etaT_ratio hE]
    exact div_le_div_of_nonneg_left h1s.le h1t (by linarith [u.2.2])
  have hc : 1 ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0.le
  have hR30 : 1 ≤ (etaT E (s N) / etaT E (t N)) ^ 30 := one_le_pow₀ (hR1.trans hRt)
  refine ⟨?_, ?_⟩
  · calc (etaT E (s N) / etaT E u) ^ 4 ≤ (etaT E (s N) / etaT E (t N)) ^ 30 := by
          calc (etaT E (s N) / etaT E u) ^ 4 ≤ (etaT E (s N) / etaT E (t N)) ^ 4 :=
                pow_le_pow_left₀ (by linarith) hRt 4
            _ ≤ _ := pow_le_pow_right₀ (hR1.trans hRt) (by norm_num)
      _ ≤ (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 :=
          le_mul_of_one_le_left (by positivity) hc
      _ ≤ _ := hN.trans hAv
  · calc (N : ℝ) ^ c ≤ (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 :=
          le_mul_of_one_le_right (by positivity) hR30
      _ ≤ _ := hN.trans hAv

/-- The `K` bound (2.59) at `n = 2` as a `≺` statement: `|K_{u,(+,-),(a,b)}| ≺ (W ℓ_u η_u)^{-1}`. -/
theorem kval_stochDom {C : ℝ}
    (hC : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) 2),
      ‖B.Kval E N u v.idx‖ ≤ C * (B.scale E N u)⁻¹ ^ (2 - 1))
    (hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) (_ : Ω) =>
        ‖B.Kval E N p.1 (pmLoop p.2.1 p.2.2)‖)
      (fun N p _ => (B.scale E N p.1)⁻¹) := by
  refine Step1.stochDom_of_le_const_mul (fun _ _ _ => norm_nonneg _)
    (fun N p _ => (inv_pos.2 (hA N p.1)).le) C fun N p ω => ?_
  have h := hC N p.1 (sigPM, ![p.2.1, p.2.2])
  rw [idx_sigPM] at h
  simpa using h

/-- **(2.75)** (Step 2) in exactly the shape of the field `RBM.Steps.localLaw`:
`‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/2}`, uniformly in `u ∈ [s, t]`.

Proof (p. 63): (2.76) and the `K` bound (2.59) give (5.73)
`|L_{u,(+,-),(a,b)}| ≺ (W ℓ_u η_u)^{-1}`; Lemma 4.1 ((4.2), (4.3), hypothesis `Lemma41Flow` of
Step 1) turns this into `‖G_u - m‖²_max ≺ (W ℓ_u η_u)^{-1}` on the event
`{‖G_u - m‖_max ≤ (W ℓ_u η_u)^{-1/6}}`, which holds w.h.p. by the weak law (2.74). -/
theorem localLaw {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (h276 : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2))
    (h274 : StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 4)))
    (h41 : Step1.Lemma41Flow X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) := by
  have hE : |E| < 2 := by linarith
  have hu0 : ∀ N (u : TimeIcc s t N), (0 : ℝ) ≤ (u : ℝ) := fun N u => (hs0 N).trans u.2.1
  have hu1 : ∀ N (u : TimeIcc s t N), (u : ℝ) < 1 := fun N u => u.2.2.trans_lt (ht1 N)
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N (hu0 N u) (hu1 N u)
  have hAi : ∀ N (u : TimeIcc s t N), 0 ≤ (B.scale E N u)⁻¹ := fun N u => (inv_pos.2 (hA N u)).le
  have hfacts := eventually_R4_le_scale (B := B) hE hst ht1 hc0 hreg
  -- (5.73): `|L_{u,(+,-)}| ≺ (W ℓ_u η_u)^{-1}`
  obtain ⟨C, -, hC⟩ := Step3.exists_norm_Kval_le (B := B) hκ0 hκ1 hEκ hs0 ht1 (n := 2)
    (by norm_num)
  have hLK : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹) := by
    refine Step3.stochDom_mono (fun N p _ => hAi N p.1) 2 ?_ (h276 1 one_pos)
    filter_upwards [hfacts] with N hN p ω
    obtain ⟨hR4, -⟩ := hN p.1
    have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
    have hdec : B.decayProf N p.1 1 p.2.1 p.2.2 ≤ 2 := by
      unfold Band.decayProf
      have h1 : Real.exp (-(((zdist (B.L N) (p.2.1 - p.2.2) : ℝ) / B.ell N p.1) ^ ((1 : ℝ) / 2)))
          ≤ 1 := Real.exp_le_one_iff.2 (by
            have hℓ : 0 < B.ell N p.1 := Step3.ellHat_pos_of_lt_one (B.one_le_L N) (hu1 N p.1)
            have := Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg (zdist (B.L N)
              (p.2.1 - p.2.2))) hℓ.le) ((1 : ℝ) / 2)
            linarith)
      have h2 : (B.W N : ℝ) ^ (-(1 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
      linarith
    have hApos := hA N p.1
    have hdec0 : 0 ≤ B.decayProf N p.1 1 p.2.1 p.2.2 := by unfold Band.decayProf; positivity
    have hR0 : 0 ≤ (etaT E (s N) / etaT E p.1) ^ 4 := by
      have := div_pos (etaT_pos' hE ((hst N).trans_lt (ht1 N))) (etaT_pos' hE (hu1 N p.1))
      positivity
    calc (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
          B.decayProf N p.1 1 p.2.1 p.2.2
        ≤ B.scale E N p.1 * (B.scale E N p.1)⁻¹ ^ 2 * 2 := by gcongr
      _ = 2 * (B.scale E N p.1)⁻¹ := by field_simp
  have hK := kval_stochDom (B := B) (Ω := Ω) (s := s) (t := t) hC hA
  have hL : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        ‖X.Lval E N p.1 ω (pmLoop p.2.1 p.2.2)‖)
      (fun N p _ => (B.scale E N p.1)⁻¹) := by
    refine Step3.stochDom_mono (fun N p _ => hAi N p.1) 2
      (Eventually.of_forall fun N p ω => ?_) (StochDom.of_le_left (fun N p ω => ?_) (hLK.add hK))
    · simp only [Pi.add_apply]; linarith
    · simp only [Pi.add_apply, Sample.lkErr]
      have := norm_sub_norm_le (X.Lval E N p.1 ω (pmLoop p.2.1 p.2.2))
        (B.Kval E N p.1 (pmLoop p.2.1 p.2.2))
      linarith
  -- Lemma 4.1
  have hLind : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        (Step1.goodEv X E N p.1).indicator
          (fun ω => ‖X.Lval E N p.1 ω (pmLoop p.2.1 p.2.2)‖) ω)
      (fun N p _ => (B.scale E N p.1)⁻¹) := by
    refine StochDom.of_le_left (fun N p ω => ?_) hL
    by_cases hω : ω ∈ Step1.goodEv X E N p.1
    · rw [Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω]; exact norm_nonneg _
  have h41' := h41 (fun N u => (B.scale E N u)⁻¹) hAi hLind
  have hsq : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => (Step1.goodEv X E N u).indicator
        (fun ω => Step1.llMax X E N u ω ^ 2) ω)
      (fun N u _ => (B.scale E N u)⁻¹) := by
    refine Step3.stochDom_mono (fun N u _ => hAi N u) 2 (Eventually.of_forall fun N u ω => ?_) h41'
    have := Step1.inv_W_le_inv_scale (B := B) hE N (hu0 N u) (hu1 N u)
    linarith
  -- the good event of Lemma 4.1 holds for all `u` w.h.p., by (2.74)
  have hΩ : HighProb B.P (fun N => {ω | ∀ u : TimeIcc s t N, ω ∈ Step1.goodEv X E N u}) := by
    refine (h274.highProb (by positivity : (0 : ℝ) < c / 24)).mono ?_
    filter_upwards [hfacts, eventually_ge_atTop 1] with N hN hN1 ω hω u
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    obtain ⟨-, hNc⟩ := hN u
    have hApos := hA N u
    have hA1 : 1 ≤ B.scale E N u := (Real.one_le_rpow hN1' hc0.le).trans hNc
    refine Step1.llMax_le X fun ij => (hω (u, ij)).trans ?_
    -- `N^{c/24} A^{-1/4} ≤ A^{-1/6}`
    have h1 : (N : ℝ) ^ (c / 24) ≤ B.scale E N u ^ ((1 : ℝ) / 12) := by
      have e : (N : ℝ) ^ (c / 24) = ((N : ℝ) ^ c) ^ ((1 : ℝ) / 24) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg N)]; ring_nf
      rw [e]
      calc ((N : ℝ) ^ c) ^ ((1 : ℝ) / 24) ≤ B.scale E N u ^ ((1 : ℝ) / 24) :=
            Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) hNc (by norm_num)
        _ ≤ B.scale E N u ^ ((1 : ℝ) / 12) :=
            Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
    rw [Real.inv_rpow hApos.le, Real.inv_rpow hApos.le]
    have e2 : B.scale E N u ^ ((1 : ℝ) / 4) =
        B.scale E N u ^ ((1 : ℝ) / 12) * B.scale E N u ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_add hApos]; norm_num
    rw [e2, mul_inv, ← mul_assoc]
    have hp : 0 < B.scale E N u ^ ((1 : ℝ) / 12) := Real.rpow_pos_of_pos hApos _
    have hq : 0 < (B.scale E N u ^ ((1 : ℝ) / 6))⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos hApos _)
    have : (N : ℝ) ^ (c / 24) * (B.scale E N u ^ ((1 : ℝ) / 12))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hp]; exact h1
    calc (N : ℝ) ^ (c / 24) * (B.scale E N u ^ ((1 : ℝ) / 12))⁻¹ *
          (B.scale E N u ^ ((1 : ℝ) / 6))⁻¹ ≤ 1 * (B.scale E N u ^ ((1 : ℝ) / 6))⁻¹ := by
          gcongr
      _ = _ := one_mul _
  have hmax := Step1.stochDom_of_indicator
    (Ωs := fun N (u : TimeIcc s t N) => Step1.goodEv X E N u)
    (ξ := fun N (u : TimeIcc s t N) ω => Step1.llMax X E N u ω ^ 2)
    (ζ := fun N u _ => (B.scale E N u)⁻¹) hΩ hsq
  have hhalf := stochDom_rpow_half_of_sq
    (ξ := fun N (u : TimeIcc s t N) ω => Step1.llMax X E N u ω)
    (fun N (u : TimeIcc s t N) _ => hAi N u) hmax
  have hfin := hhalf.precomp_param (V := fun N => TimeIcc s t N × (B.Idx N × B.Idx N))
    fun N p => p.1
  refine StochDom.of_le_left
    (ξ' := fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => Step1.llMax X E N p.1 ω)
    (fun N p ω => Step1.llErr_le_llMax X N p.1 ω p.2) ?_
  exact hfin

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

/-- **Lemma 5.6, (5.30)**: for fixed `δ, D > 0`, eventually in `N`, for all `u ∈ [s, t]` and
`‖x - y‖ ≥ δ ℓ*_u`: `|(Θ_u)_{xy}| ≤ W^{-D}` and `|(Θ_s^{-1} Θ_u)_{xy}| ≤ W^{-D}`, where
`Θ_s^{-1} Θ_u = (1 - s S^{(B)}) Θ_u`. -/
theorem eq530 (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {δ D : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (u : TimeIcc s t N) (x y : ZMod (B.L N)),
      δ * ellStar (B.W N) (B.ell N u) ≤ zdist (B.L N) (x - y) →
        ‖Theta (B.L N) ((u : ℝ) : ℂ) x y‖ ≤ (B.W N : ℝ) ^ (-D) ∧
        ‖((1 - ((s N : ℝ) : ℂ) • SB (B.L N)) * Theta (B.L N) ((u : ℝ) : ℂ)) x y‖ ≤
          (B.W N : ℝ) ^ (-D) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hC : 0 < 2 * cTwo52 := by have := cTwo52_pos; positivity
  have hW := tendsto_W B
  -- `ℓ*_u ≥ (log W)^{3/2}`, so `δ ℓ*_u / 2 ≥ 1` eventually
  have hlog : Tendsto (fun N => log (B.W N : ℝ) ^ (3 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (Real.tendsto_log_atTop.comp hW)
  filter_upwards [SumZeroDyn.flow_crude hE hs0 hst ht1 hc, eventually_le_W_sq B,
    hW.eventually (eventually_mul_exp_neg_log_rpow_le (by have := cZero_pos; positivity :
      0 < cZero * (δ / 2)) hC (D + 3)),
    hW.eventually_ge_atTop 2, hlog.eventually_ge_atTop (2 / δ)] with N hcr hW2 hexp hW2' hl
  obtain ⟨-, -, hN1, hsc⟩ := hcr
  intro u x y hxy
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hW1 : (1 : ℝ) ≤ B.W N := by linarith
  have hL3 := B.three_le_L N
  have hu0 : 0 ≤ (u : ℝ) := ((hs0 N).trans u.2.1)
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hℓ1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have hN : (N : ℝ) ≤ (B.W N : ℝ) ^ 2 := hW2
  have hinv : (1 - (u : ℝ))⁻¹ ≤ N := (hsc u).2.2
  -- the bound on `Θ_u` at distance `≥ (δ/2) ℓ*_u`
  have hfar : ∀ z : ZMod (B.L N), (δ / 2) * ellStar (B.W N) (B.ell N u) ≤ zdist (B.L N) (z - y) →
      ‖Theta (B.L N) ((u : ℝ) : ℂ) z y‖ ≤ (B.W N : ℝ) ^ (-(D + 1)) := by
    intro z hz
    have h1 := norm_Theta_le_of_ellStar (B.L N) hL3 hu0 hu1 hz
    refine h1.trans ?_
    have hpre : cTwo52 / ((1 - (u : ℝ)) * B.ell N u) ≤ cTwo52 * (B.W N : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 ≤ (1 - (u : ℝ)) * (B.W N : ℝ) ^ 2 * B.ell N u := by
        have h2 : 1 ≤ (1 - (u : ℝ)) * N := by
          rw [inv_le_iff_one_le_mul₀' h1u] at hinv; linarith
        have h3 : (1 - (u : ℝ)) * N ≤ (1 - (u : ℝ)) * (B.W N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hN h1u.le
        nlinarith
      have := cTwo52_pos
      nlinarith
    have hexp' : 2 * cTwo52 * exp (-(cZero * (δ / 2) * log (B.W N) ^ (3 / 2 : ℝ))) ≤
        (B.W N : ℝ) ^ (-(D + 3)) := by
      simpa [mul_assoc] using hexp
    have hWsplit : (B.W N : ℝ) ^ (-(D + 3)) * (B.W N : ℝ) ^ 2 = (B.W N : ℝ) ^ (-(D + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hW0]; push_cast; ring_nf
    have he0 := exp_pos (-(cZero * (δ / 2) * log (B.W N) ^ (3 / 2 : ℝ)))
    calc cTwo52 / ((1 - (u : ℝ)) * B.ell N u) * exp (-(cZero * (δ / 2) *
          log (B.W N) ^ (3 / 2 : ℝ)))
        ≤ cTwo52 * (B.W N : ℝ) ^ 2 * exp (-(cZero * (δ / 2) * log (B.W N) ^ (3 / 2 : ℝ))) := by
          gcongr
      _ = (B.W N : ℝ) ^ 2 * (cTwo52 * exp (-(cZero * (δ / 2) * log (B.W N) ^ (3 / 2 : ℝ)))) := by
          ring
      _ ≤ (B.W N : ℝ) ^ 2 * (B.W N : ℝ) ^ (-(D + 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := mul_pos cTwo52_pos he0
          linarith
      _ = _ := by rw [mul_comm]; exact hWsplit
  have hWD : (B.W N : ℝ) ^ (-(D + 1)) ≤ (B.W N : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hstar : 1 ≤ (δ / 2) * ellStar (B.W N) (B.ell N u) := by
    unfold ellStar
    have : 2 / δ ≤ log (B.W N) ^ (3 / 2 : ℝ) * B.ell N u := by
      have hlogpos : 0 ≤ log (B.W N) ^ (3 / 2 : ℝ) := by
        have := (div_pos two_pos hδ).le; linarith
      nlinarith
    rw [div_le_iff₀ hδ] at this
    nlinarith
  refine ⟨(hfar x (by linarith)).trans hWD, ?_⟩
  have hs1 : s N ≤ 1 := ((hst N).trans_lt (ht1 N)).le
  have h2 := norm_oneSub_mul_Theta_le (B.L N) hL3 (hs0 N) hs1 (t := u) (x := x) (y := y)
    (M := (B.W N : ℝ) ^ (-(D + 1))) fun z hz => hfar z (by linarith)
  refine h2.trans ?_
  have : 2 * (B.W N : ℝ) ^ (-(D + 1)) = 2 * (B.W N : ℝ)⁻¹ * (B.W N : ℝ) ^ (-D) := by
    rw [neg_add, Real.rpow_add hW0, Real.rpow_neg_one]; ring
  rw [this]
  have : 2 * (B.W N : ℝ)⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hW0]; linarith
  have hε : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  nlinarith

end Flow

end Lemma56

section Eq531

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- `K_{u,(-,+),(a,b)} = W^{-1} (Θ_u)_{ab}` ((2.57) with `m̄ m = |m|² = 1`). -/
theorem Kval_mp (hE : |E| ≤ 2) (N : ℕ) (u : ℝ) (a b : ZMod (B.L N)) :
    B.Kval E N u ⟨[false, true], [a, b]⟩ = ((B.W N : ℂ))⁻¹ * Theta (B.L N) (u : ℂ) a b := by
  have hm : mSigma E false * mSigma E true = 1 := by
    simp only [mSigma, Bool.false_eq_true, ite_false, ite_true]
    rw [Complex.conj_mul', norm_mE hE]; simp
  rw [Band.Kval, Kgen_two, kTwo, hm, mul_one, mul_one]

/-- **Lemma 5.6, (5.31)**: for fixed `δ, D > 0`, eventually in `N`, for every `ω`,
`u ∈ [s, t]` and `‖a - b‖ ≥ δ ℓ*_u`:
`|L_{u,(-,+),(a,b)}| ≤ J*_{u,D} T_{u,D}(‖a - b‖)` (deterministically, the paper's `≺`). -/
theorem eq531 (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {δ : ℝ} (hδ : 0 < δ) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (ω : Ω) (u : TimeIcc s t N) (a b : ZMod (B.L N)),
      δ * ellStar (B.W N) (B.ell N u) ≤ zdist (B.L N) (a - b) →
        ‖X.Lval E N u ω ⟨[false, true], [a, b]⟩‖ ≤
          jS X E D N u ω * tT B E N D u (zdist (B.L N) (a - b)) := by
  filter_upwards [eq530 (B := B) hE hs0 hst ht1 hc (D := D) hδ] with N h530
  intro ω u a b hab
  have hΘ := (h530 u a b hab).1
  have hu0 : 0 ≤ (u : ℝ) := ((hs0 N).trans u.2.1)
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  -- `L = (L - K) + K`, and `(L - K)_{(-,+),(a,b)} = (L - K)_{(+,-),(b,a)}`
  have hidx : LoopData.idx ((![false, true], ![a, b]) : LoopData (B.L N) 2)
      = (⟨[false, true], [a, b]⟩ : LoopIdx (ZMod (B.L N))) := by
    simp [LoopData.idx, List.ofFn_succ]
  have hswap := SumZeroDyn.lkT_swap2 X hE hu0 hu1 ω ![false, true] ![a, b]
  have e1 : (fun i : Fin 2 => (![false, true] : Fin 2 → Bool) (i + 1)) = sigPM := by
    funext i; fin_cases i <;> rfl
  have e2 : (fun i : Fin 2 => (![a, b] : Fin 2 → ZMod (B.L N)) (i + 1)) = ![b, a] := by
    funext i; fin_cases i <;> rfl
  rw [e1, e2] at hswap
  have hL : X.Lval E N u ω ⟨[false, true], [a, b]⟩
      = lk X E N u ω ![b, a] + B.Kval E N u ⟨[false, true], [a, b]⟩ := by
    rw [lk, ← hswap, SumZeroDyn.lkT, hidx]; ring
  have hlk : ‖lk X E N u ω ![b, a]‖ ≤
      (jS X E D N u ω - 1) * tT B E N D u (zdist (B.L N) (a - b)) := by
    have := le_jStar_sub_one_mul (f := fun c => ‖lk X E N u ω c‖) (ℓu := B.ell N u)
      (ηu := etaT E u) (D := D) hW0 ![b, a]
    have hd : zdist (B.L N) (b - a) = zdist (B.L N) (a - b) := by
      rw [← zdist_neg (B.L N) (b - a), neg_sub]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hd] at this
    exact this
  have hK : ‖B.Kval E N u ⟨[false, true], [a, b]⟩‖ ≤ tT B E N D u (zdist (B.L N) (a - b)) := by
    rw [Kval_mp hE.le, norm_mul, norm_inv, Complex.norm_natCast]
    calc (B.W N : ℝ)⁻¹ * ‖Theta (B.L N) ((u : ℝ) : ℂ) a b‖ ≤ 1 * (B.W N : ℝ) ^ (-D) :=
          mul_le_mul (inv_le_one_of_one_le₀ hW1) hΘ (norm_nonneg _) zero_le_one
      _ = (B.W N : ℝ) ^ (-D) := one_mul _
      _ ≤ _ := rpow_neg_le_tailT _
  rw [hL]
  calc ‖lk X E N u ω ![b, a] + B.Kval E N u ⟨[false, true], [a, b]⟩‖
      ≤ ‖lk X E N u ω ![b, a]‖ + ‖B.Kval E N u ⟨[false, true], [a, b]⟩‖ := norm_add_le _ _
    _ ≤ (jS X E D N u ω - 1) * tT B E N D u (zdist (B.L N) (a - b)) +
        tT B E N D u (zdist (B.L N) (a - b)) := add_le_add hlk hK
    _ = _ := by ring

end Eq531

/-! ### Step 2 -/

section Step2Main

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **Step 2 of Theorem 2.21**: (2.75) and (2.76), in exactly the shapes of the fields
`RBM.Steps.localLaw` and `RBM.Steps.aprioriDecay`.

Inputs: (2.68)–(2.70) at `s` (`RBM.BoundsCore`; Step 2 uses (2.69)), (2.72) with a gain `N^c`
(`hreg`), the random-layer inputs of Step 1 (`RBM.Step1.Hyp`, which give (2.74) and Lemma 4.1
along the flow) and of Step 2 (`Hyp`). -/
theorem step2 {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (Hy : Hyp X E s t)
    (h1 : Step1.Hyp X E s t) (hB : BoundsCore X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) := by
  have hE : |E| < 2 := by linarith
  have h276 := aprioriDecay X Hy hE hs0 hst ht1 hB hc0 hreg
  have hc272 := cond272_of_strict hE hst ht1 hc0 hreg
  have hreg' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N) := by
    filter_upwards [eventually_R4_le_scale (B := B) hE hst ht1 hc0 hreg] with N hN
    exact (hN ⟨t N, hst N, le_rfl⟩).2
  have h274 := Step1.weakLaw X hκ0 hEκ hB hs0 hst ht1 hc272 hc0 hreg' h1
  exact ⟨localLaw X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg h276 h274 h1.lemma41,
    h276⟩

end Step2Main

end Step2

end RBM
