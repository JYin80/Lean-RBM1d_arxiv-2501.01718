/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step3
import RBM1D.Analysis.StretchedExp

/-!
# Steps 4 and 5 of the proof of Theorem 2.21: (2.78) and (2.79)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.7: Step 4, the sharp
`L - K` bound (2.78) via (5.125) and induction on the length `n`; Step 5, the sharp decay bound
(2.79) via the two-part split `|a₁ - a₂| ≤ 6 ℓ*_u` (Step 4) / `> 6 ℓ*_u` ((5.48)).

**Given the random-layer inputs as hypotheses, Steps 4 and 5 are deterministic**: `≺`-calculus
plus real inequalities.  Nothing is an `axiom`.  The setting is the abstract one of
`RBM1D/Hierarchy/Step3.lean` (families `X n N u ω = Ξ^{(L-K)}_{u,n}` over a parameter type
`U N` of times, `A N u = W ℓ_u η_u`; `≺` is `RBM.StochDom`, uniform in the time).

## Step 4

* `RBM.Step45.Eq5125 P X A n` — **(5.125)** at length `n`, in bound-transfer form.
* `RBM.Step45.eq5125_of_lemma514` — (5.125) from Lemma 5.14 (5.92) (`RBM.Step3.Lemma514`) and
  (2.77) for `Ξ^{(L)}_{2n+2}`, `Ξ^{(L)}_{n+1}` ("use (2.77) to bound … in (5.111) and (5.112)").
* `RBM.Step45.xiLK_le_one` — **the induction on `n`**: `Ξ^{(L-K)}_{u,n} ≺ 1` for all `n ≥ 1`
  from `Ξ^{(L-K)}_{u,1} ≺ 1`, `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/2}`, (5.125) for `n ≥ 2` and the
  a priori bound `Ξ^{(L-K)}_{u,n} ≺ W ℓ_u η_u` for `n ≥ 3`.
* `RBM.Step45.xiLK_le_one_of_hyp` — the same on top of Step 3 (`RBM.Step3.Hyp`, `S(m,0)`,
  `S(m,l)` for `m ≤ 2`): (5.125) and the a priori bound are derived, the remaining inputs are
  Lemma 5.14 at `n = 2` and the base cases `Ξ^{(L-K)}_{u,1} ≺ 1` ((4.5)),
  `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}` ((2.76), (2.72)).
* **(2.78)** for the flow, at an `N`-dependent energy, is `RBM.Step45.flow_sharpLmKN` in
  `RBM1D/EnergyN/Hierarchy/Step45.lean`.

## Step 5

* `RBM.Step45.stochDom_min` — `ξ ≺ ζ₁`, `ξ ≺ ζ₂` give `ξ ≺ min(ζ₁, ζ₂)`.
* `RBM.Step45.inv_sq_le_tailT` — near region: `(W ℓ_u η_u)^{-2} ≤ e^{√6 (log W)^{3/4}} T_{u,D}(d)`
  for `d ≤ 6 ℓ*_u` ((5.32) with `C = 6`, `RBM.tailT_sub_le`).
* `RBM.Step45.tailT_add_two_le` — `T_{u,D+2}(d) ≤ (W ℓ_u η_u)^{-2} (e^{-(d/ℓ_u)^{1/2}} + W^{-D})`.
* `RBM.Step45.Eq548` — **(5.48)** (multiplied form).
* `RBM.Step45.decay_of_split` — **Step 5**, abstract: Step 4 at `n = 2` and (5.48) give (2.79).
* **(2.79)** for the flow, at an `N`-dependent energy, is `RBM.Step45.flow_sharpDecayN` in
  `RBM1D/EnergyN/Hierarchy/Step45.lean`.

## Deviations from the paper

* (5.125) is taken in the bound-transfer form of `RBM.Step3.Lemma514`: if the maxima on its right
  side are `≺ Φ` (deterministic) uniformly in `u ∈ [s,t]`, then `Ξ^{(L-K)}_{u,n} ≺ 1 + Φ`,
  uniformly in `u` (the paper writes the left side at the time `t`, for every `t`).  It is
  *derived* from (5.92) + (2.77); this needs Lemma 5.14 also at `n = 2` (Step 3 only uses
  `n ≥ 3`), as in the paper, where the induction starts by improving `Ξ_2`.
* The quadratic terms `k = 2` and `k = n` of (5.125) contain `Ξ^{(L-K)}_{u,n}` itself, so the
  induction on `n` uses an a priori bound `Ξ^{(L-K)}_{u,n} ≺ W ℓ_u η_u` (`n ≥ 3`), as in the
  paper; here it follows from Step 3 (`Ξ^{(L-K)}_{u,n} ≺ (W ℓ_s η_s)^{1/2}` and
  `(W ℓ_s η_s)^{3/4} ≤ W ℓ_u η_u` by (2.72)).
* In the abstract induction the base case `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/2}` suffices; the
  paper's `(W ℓ_u η_u)^{1/4}` is what `xiLK_le_one_of_hyp` assumes.
* Inputs taken as hypotheses (random layer): Lemma 5.14 (5.92) for `n ≥ 2`, the Step 3 inputs
  `S(m,0)` and `S(m,l)` (`m ≤ 2`), the base cases from (4.5) and (2.76), and (5.48).
* (5.48) is used at every time `u ∈ [s,t]`, with `ℓ*_u` in the indicator (the paper states it at
  the final time `t`; "for any `t ≥ s`").  It is stated multiplied by `T_{u,D}` instead of
  divided (equivalent, `T_{u,D} > 0` deterministic).  The prefactor `(η_s/η_u)²` plays no role.
* The near region is `|a₁ - a₂| ≤ 6 ℓ*_u` (paper: "`|a₁ - a₂| = O(ℓ*_t)`"); the loss
  `exp(√6 (log W)^{3/4})` is `≤ W^τ ≤ N^τ`.
* `T_{u,D}` has `W^{-D}` without the factor `(W ℓ_u η_u)^{-2}` of (2.79); since
  `W ℓ_u η_u ≤ W` (`η_u ℓ_u ≤ 1`), (5.48) is used with `D + 2` in place of `D`.
* `|a₁ - a₂|` is the cyclic distance `RBM.zdist`, as in `Flow/Hypotheses.lean`.
-/

namespace RBM

open MeasureTheory Filter

namespace Step45

/-! ### Two generic facts about `≺` -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- Two bounds give the minimum: `ξ ≺ ζ₁` and `ξ ≺ ζ₂` imply `ξ ≺ min(ζ₁, ζ₂)`. -/
theorem stochDom_min {ξ ζ₁ ζ₂ : ∀ N, U N → Ω → ℝ} (h₁ : StochDom P ξ ζ₁)
    (h₂ : StochDom P ξ ζ₂) : StochDom P ξ fun N u ω => min (ζ₁ N u ω) (ζ₂ N u ω) := by
  refine StochDom.of_subset_union h₁ h₂ fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  intro ω ⟨u, hu⟩
  have hpos : 0 ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [mul_min_of_nonneg _ _ hpos, min_lt_iff] at hu
  rcases hu with hu | hu
  · exact Or.inl ⟨u, hu⟩
  · exact Or.inr ⟨u, hu⟩

/-- A product bound: `X_p ≺ f`, `X_q ≺ g` and `f g A⁻¹ ≤ C` (eventually) give
`X_p X_q A⁻¹ ≺ 1`. -/
theorem quad_le_one {ξp ξq : ∀ N, U N → Ω → ℝ} {f g A : ∀ N, U N → ℝ}
    (hA : ∀ N u, 0 < A N u) (hq0 : ∀ N u ω, 0 ≤ ξq N u ω) (hf : ∀ N u, 0 ≤ f N u)
    (hg : ∀ N u, 0 ≤ g N u)
    (hp : StochDom P ξp fun N u _ => f N u) (hq : StochDom P ξq fun N u _ => g N u)
    (C : ℝ) (hle : ∀ᶠ N : ℕ in atTop, ∀ u, f N u * g N u * (A N u)⁻¹ ≤ C) :
    StochDom P (fun N u ω => ξp N u ω * ξq N u ω * (A N u)⁻¹) fun _ _ _ => 1 := by
  have hA' : ∀ N u (_ : Ω), 0 ≤ (A N u)⁻¹ := fun N u _ => (inv_pos.2 (hA N u)).le
  have h12 := StochDom.mul hq0 (fun N u _ => hf N u) hp hq
  have h3 := StochDom.mul hA' (fun N u _ => mul_nonneg (hf N u) (hg N u)) h12
    (StochDom.refl hA')
  exact Step3.stochDom_mono (fun _ _ _ => zero_le_one) C
    (hle.mono fun N hN u _ => by simpa using hN u) h3

end Generic

/-! ### Step 4: (5.125) and the induction on `n` -/

section Step4

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

variable (P) in
/-- **(5.125)** at length `n`, in bound-transfer form: if every term in the maxima on the right of
(5.125) is `≺ Φ` uniformly in the time (`Φ ≥ 0` deterministic), then
`Ξ^{(L-K)}_{u,n} ≺ 1 + Φ`.  Here `X m N u ω = Ξ^{(L-K)}_{u,m}` and `A N u = W ℓ_u η_u`. -/
def Eq5125 (X : ℕ → ∀ N, U N → Ω → ℝ) (A : ∀ N, U N → ℝ) (n : ℕ) : Prop :=
  ∀ Φ : ℕ → ℝ, (∀ N, 0 ≤ Φ N) →
    (∀ m, 1 ≤ m → m < n → StochDom P (X m) fun N _ _ => Φ N) →
    (∀ m, 2 ≤ m → m ≤ n → StochDom P (fun N u ω => X m N u ω * X (n - m + 2) N u ω * (A N u)⁻¹)
      fun N _ _ => Φ N) →
    StochDom P (X n) fun N _ _ => 1 + Φ N

variable {X Y : ℕ → ∀ N, U N → Ω → ℝ} {A : ∀ N, U N → ℝ}

/-- `ξ ≺ Φ` gives `ξ ≺ Φ + 1`. -/
theorem stochDom_add_one {ξ : ∀ N, U N → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (h : StochDom P ξ fun N _ _ => Φ N) : StochDom P ξ fun N _ _ => Φ N + 1 :=
  Step3.stochDom_mono (fun N _ _ => by linarith [hΦ N]) 1
    (Eventually.of_forall fun N _ _ => by linarith) h

/-- **(5.92) + (2.77) ⟹ (5.125)**: Lemma 5.14 at length `n`, with
`Ξ^{(L)}_{u,2n+2} ≺ 1` and `Ξ^{(L)}_{u,n+1} ≺ 1` from (2.77), is (5.125) at length `n`. -/
theorem eq5125_of_lemma514 {n : ℕ} (h : Step3.Lemma514 P X Y A n)
    (hY₁ : StochDom P (Y (2 * n + 2)) fun _ _ _ => 1)
    (hY₂ : StochDom P (Y (n + 1)) fun _ _ _ => 1) : Eq5125 P X A n := by
  intro Φ hΦ hsmall hquad
  have hΦ1 : ∀ N, 0 ≤ Φ N + 1 := fun N => by linarith [hΦ N]
  have key := h (fun _ => 1) (fun N => Φ N + 1) (fun _ => zero_le_one) hΦ1
    (Eventually.of_forall fun _ => le_rfl) hY₁
    (fun m h1 h2 => stochDom_add_one hΦ (hsmall m h1 h2))
    (fun m h1 h2 => stochDom_add_one hΦ (hquad m h1 h2))
    (Step3.stochDom_mono (fun N _ _ => hΦ1 N) 1
      (Eventually.of_forall fun N _ _ => by linarith [hΦ N]) hY₂)
  refine Step3.stochDom_mono (fun N _ _ => by linarith [hΦ N]) 2
    (Eventually.of_forall fun N _ _ => ?_) key
  rw [Real.one_rpow]
  linarith [hΦ N]

/-- **Step 4, the induction on `n`**: from the base cases `Ξ^{(L-K)}_{u,1} ≺ 1`,
`Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/2}`, the a priori bound `Ξ^{(L-K)}_{u,n} ≺ W ℓ_u η_u`
(`n ≥ 3`) and (5.125) for `n ≥ 2`, `Ξ^{(L-K)}_{u,n} ≺ 1` for every `n ≥ 1`, uniformly in the
time. -/
theorem xiLK_le_one (hA : ∀ N u, 0 < A N u) (hA1 : ∀ᶠ N : ℕ in atTop, ∀ u, 1 ≤ A N u)
    (hX0 : ∀ n N u ω, 0 ≤ X n N u ω)
    (h1 : StochDom P (X 1) fun _ _ _ => 1)
    (h2 : StochDom P (X 2) fun N u _ => A N u ^ ((1 : ℝ) / 2))
    (hpri : ∀ n, 3 ≤ n → StochDom P (X n) fun N u _ => A N u)
    (h5125 : ∀ n, 2 ≤ n → Eq5125 P X A n) :
    ∀ n, 1 ≤ n → StochDom P (X n) fun _ _ _ => 1 := by
  have hA0 : ∀ N u, 0 ≤ A N u := fun N u => (hA N u).le
  have hone : ∀ N (_ : U N), (0 : ℝ) ≤ 1 := fun _ _ => zero_le_one
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
    · exact h1
    have key := h5125 n hn2 (fun _ => 1) (fun _ => zero_le_one)
      (fun m h1 h2 => ih m h2 h1) (fun m hm2 hmn => ?_)
    · exact Step3.stochDom_mono (fun _ _ _ => zero_le_one) 2
        (Eventually.of_forall fun _ _ _ => by norm_num) key
    -- the quadratic terms
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · obtain rfl : m = 2 := by omega
      refine quad_le_one hA (hX0 _) (fun N u => Real.rpow_nonneg (hA0 N u) _)
        (fun N u => Real.rpow_nonneg (hA0 N u) _) h2 h2 1 (Eventually.of_forall fun N u => ?_)
      rw [← Real.rpow_add (hA N u)]
      norm_num
      exact (mul_inv_cancel₀ (hA N u).ne').le
    rcases (show m = 2 ∨ m = n ∨ (3 ≤ m ∧ m < n) by omega) with rfl | rfl | ⟨hm3, hmn'⟩
    · have hq : n - 2 + 2 = n := by omega
      rw [hq]
      refine quad_le_one hA (hX0 _) hone hA0 (ih 2 (by omega) (by norm_num)) (hpri n hn3) 1
        (Eventually.of_forall fun N u => ?_)
      rw [one_mul, mul_inv_cancel₀ (hA N u).ne']
    · have hq : m - m + 2 = 2 := by omega
      rw [hq]
      refine quad_le_one hA (hX0 _) hA0 hone (hpri m hn3) (ih 2 (by omega) (by norm_num)) 1
        (Eventually.of_forall fun N u => ?_)
      rw [mul_one, mul_inv_cancel₀ (hA N u).ne']
    · refine quad_le_one hA (hX0 _) hone hone (ih m hmn' (by omega)) (ih (n - m + 2) (by omega)
        (by omega)) 1 (hA1.mono fun N hN u => ?_)
      rw [one_mul, one_mul]
      exact inv_le_one_of_one_le₀ (hN u)

/-- `W ℓ_u η_u ≥ 1` for large `N`, from the scale conditions of Step 3. -/
theorem one_le_A {As R : ℕ → ℝ} (sc : Step3.Scales As R A) :
    ∀ᶠ N : ℕ in atTop, ∀ u, 1 ≤ A N u := by
  filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u
  obtain ⟨_, hv, hRv⟩ := hu u
  obtain ⟨-, -, hb2v, -⟩ := Step3.scale_facts hb hR hv hRv
  nlinarith

/-- **Step 4 on top of Step 3**: under the hypotheses of Step 3 (`RBM.Step3.Hyp`, `S(m,0)`,
`S(m,l)` for `m ≤ 2`), Lemma 5.14 at length `2` and the base cases `Ξ^{(L-K)}_{u,1} ≺ 1` (from
(4.5)), `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}` (from (2.76), (2.72)):
`Ξ^{(L-K)}_{u,n} ≺ 1` for every `n ≥ 1`, uniformly in `u ∈ [s,t]`.

(5.125) is derived from (5.92) and (2.77) (`eq5125_of_lemma514`, `RBM.Step3.xiL_le_one`); the
a priori bound `Ξ^{(L-K)}_{u,n} ≺ W ℓ_u η_u` from `Ξ^{(L-K)}_{u,n} ≺ (W ℓ_s η_s)^{1/2}`
(`RBM.Step3.xiLK_le`) and `(W ℓ_s η_s)^{3/4} ≤ W ℓ_u η_u`. -/
theorem xiLK_le_one_of_hyp {As R : ℕ → ℝ} (h : Step3.Hyp P X Y As R A)
    (h0 : ∀ m, 1 ≤ m → Step3.S P X As R A m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → Step3.S P X As R A m l)
    (h514 : Step3.Lemma514 P X Y A 2)
    (h1 : StochDom P (X 1) fun _ _ _ => 1)
    (h2 : StochDom P (X 2) fun N u _ => A N u ^ ((1 : ℝ) / 4)) :
    ∀ n, 1 ≤ n → StochDom P (X n) fun _ _ _ => 1 := by
  have sc := h.scales
  have hA0 : ∀ N u, 0 ≤ A N u := fun N u => (sc.A_pos N u).le
  refine xiLK_le_one sc.A_pos (one_le_A sc) h.X_nonneg h1 ?_ ?_ ?_
  · refine Step3.stochDom_mono (fun N u _ => Real.rpow_nonneg (hA0 N u) _) 1 ?_ h2
    filter_upwards [one_le_A sc] with N hN u _
    rw [one_mul]
    exact Real.rpow_le_rpow_of_exponent_le (hN u) (by norm_num)
  · intro n hn
    refine Step3.stochDom_mono (fun N u _ => hA0 N u) 1 ?_ (Step3.xiLK_le h h0 h12 (by omega))
    filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u _
    obtain ⟨_, hv, hRv⟩ := hu u
    obtain ⟨-, -, hb2v, -⟩ := Step3.scale_facts hb hR hv hRv
    rw [Step3.rpow_half_eq (sc.As_pos N).le, one_mul]
    exact hb2v
  · intro n hn
    refine eq5125_of_lemma514 ?_ (Step3.xiL_le_one h h0 h12 (by omega))
      (Step3.xiL_le_one h h0 h12 (by omega))
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · exact h514
    · exact h.lemma514 n hn3

end Step4

/-! ### Step 4 for the flow: (2.78) -/

section FlowStep4

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

open Step3

end FlowStep4

/-! ### Step 5: the two-part split, (2.79) -/

section Step5

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}
variable {W : ℕ → ℝ} {ℓ η d : ∀ N, U N → ℝ}

/-- The near region: for `d ≤ 6 ℓ*_u`,
`(W ℓ_u η_u)^{-2} ≤ exp(√6 (log W)^{3/4}) T_{u,D}(d)` ((5.32) with `C = 6`).
The `C = 6` instance of `RBM.inv_sq_le_tailT` (`Analysis/StretchedExp.lean`). -/
theorem inv_sq_le_tailT {W ℓ η D d : ℝ} (hW : 1 ≤ W) (hℓ : 0 < ℓ)
    (hd : d ≤ 6 * ellStar W ℓ) :
    ((W * ℓ * η) ^ 2)⁻¹ ≤ Real.exp (√6 * Real.log W ^ ((3 : ℝ) / 4)) * tailT W ℓ η D d :=
  RBM.inv_sq_le_tailT (ℓu := ℓ) (ηu := η) (D := D) hW hℓ (by norm_num) hd

/-- `T_{u,D+2}(d) ≤ (W ℓ_u η_u)^{-2} (exp(-(d/ℓ_u)^{1/2}) + W^{-D})` when `W ℓ_u η_u ≤ W`. -/
theorem tailT_add_two_le {W ℓ η D d : ℝ} (hW : 0 < W) (hA : 0 < W * ℓ * η)
    (hAW : W * ℓ * η ≤ W) :
    tailT W ℓ η (D + 2) d ≤
      (W * ℓ * η)⁻¹ ^ 2 * (Real.exp (-((d / ℓ) ^ ((1 : ℝ) / 2))) + W ^ (-D)) := by
  have hsplit : W ^ (-(D + 2)) = W ^ (-D) * (W ^ 2)⁻¹ := by
    rw [show -(D + 2) = -D + -2 by ring, Real.rpow_add hW, Real.rpow_neg hW.le]
    norm_cast
  have hW2 : (W ^ 2)⁻¹ ≤ ((W * ℓ * η) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hA.le hAW 2)
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  rw [tailT, hsplit, ← Real.sqrt_eq_rpow, inv_pow, mul_add]
  have := mul_le_mul_of_nonneg_left hW2 hWD
  linarith

variable (P) in
/-- **(5.48)** in multiplied form, for every `D > 0`:
`|(L-K)_{u,σ,a}| ≺ T_{u,D}(d) ((η_s/η_u)² 1(d ≤ 6 ℓ*_u) + 1)`, with the prefactor `(η_s/η_u)²`
abstracted as `pref ≥ 0`.  This is the sharpened form of (5.48): the near-field prefactor of
the remark after (5.47), and the far-field bound `1` of the second pass after (5.48).  `ξ N u ω` is
`|(L-K)_{u,(+,-),(a₁,a₂)}|`, `d N u = |a₁ - a₂|`. -/
def Eq548 (ξ : ∀ N, U N → Ω → ℝ) (W : ℕ → ℝ) (ℓ η d pref : ∀ N, U N → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → StochDom P ξ fun N u _ =>
    tailT (W N) (ℓ N u) (η N u) D (d N u) *
      (pref N u * (if d N u ≤ 6 * ellStar (W N) (ℓ N u) then 1 else 0) + 1)

/-- **Step 5**, abstract form: the bound `|(L-K)_{u,σ,a}| ≺ (W ℓ_u η_u)^{-2}` of Step 4
(used for `|a₁ - a₂| ≤ 6 ℓ*_u`) and (5.48) (used for `|a₁ - a₂| > 6 ℓ*_u`) give
`|(L-K)_{u,σ,a}| ≺ (W ℓ_u η_u)^{-2} (exp(-(|a₁-a₂|/ℓ_u)^{1/2}) + W^{-D})` for every `D > 0`.
`W → ∞` with `W ≤ N`, `W ℓ_u η_u ≤ W`. -/
theorem decay_of_split {ξ : ∀ N, U N → Ω → ℝ} {pref : ∀ N, U N → ℝ}
    (hWt : Tendsto W atTop atTop) (hWN : ∀ᶠ N : ℕ in atTop, W N ≤ N) (hW0 : ∀ N, 0 < W N)
    (hℓ : ∀ N u, 0 < ℓ N u) (hA : ∀ N u, 0 < W N * ℓ N u * η N u)
    (hAW : ∀ᶠ N : ℕ in atTop, ∀ u, W N * ℓ N u * η N u ≤ W N)
    (h4 : StochDom P ξ fun N u _ => (W N * ℓ N u * η N u)⁻¹ ^ 2)
    (h548 : Eq548 P ξ W ℓ η d pref) :
    ∀ D : ℝ, 0 < D → StochDom P ξ fun N u _ =>
      (W N * ℓ N u * η N u)⁻¹ ^ 2 *
        (Real.exp (-((d N u / ℓ N u) ^ ((1 : ℝ) / 2))) + W N ^ (-D)) := by
  intro D hD
  have hmin := stochDom_min h4 (h548 (D + 2) (by linarith))
  refine hmin.trans (StochDom.of_unifDetDom (f := fun N u => min ((W N * ℓ N u * η N u)⁻¹ ^ 2)
    (tailT (W N) (ℓ N u) (η N u) (D + 2) (d N u) *
      (pref N u * (if d N u ≤ 6 * ellStar (W N) (ℓ N u) then 1 else 0) + 1)))
    (g := fun N u => (W N * ℓ N u * η N u)⁻¹ ^ 2 *
        (Real.exp (-((d N u / ℓ N u) ^ ((1 : ℝ) / 2))) + W N ^ (-D))) ?_)
  intro τ hτ
  filter_upwards [hWt.eventually (eventually_exp_mul_log_rpow_le (√6) hτ),
    hWt.eventually_ge_atTop 1, hWN, hAW] with N hexp hW1 hWN hAW u
  set T := tailT (W N) (ℓ N u) (η N u) (D + 2) (d N u) with hT
  have hT0 : 0 ≤ T := tailT_nonneg (hW0 N).le _
  set c := Real.exp (√6 * Real.log (W N) ^ ((3 : ℝ) / 4)) with hc
  have hc1 : 1 ≤ c := Real.one_le_exp (by
    have := Real.log_nonneg hW1
    positivity)
  -- `min ≤ c T`
  have hmin : min ((W N * ℓ N u * η N u)⁻¹ ^ 2)
      (T * (pref N u * (if d N u ≤ 6 * ellStar (W N) (ℓ N u) then 1 else 0) + 1)) ≤ c * T := by
    by_cases hnear : d N u ≤ 6 * ellStar (W N) (ℓ N u)
    · refine (min_le_left _ _).trans ?_
      rw [inv_pow]
      exact inv_sq_le_tailT hW1 (hℓ N u) hnear
    · refine (min_le_right _ _).trans ?_
      rw [ite_eq_right hnear, mul_zero, zero_add, mul_one]
      nlinarith
  -- `c ≤ N^τ`
  have hcN : c ≤ (N : ℝ) ^ τ :=
    hexp.trans (Real.rpow_le_rpow (hW0 N).le hWN hτ.le)
  calc _ ≤ c * T := hmin
    _ ≤ (N : ℝ) ^ τ * T := mul_le_mul_of_nonneg_right hcN hT0
    _ ≤ _ := mul_le_mul_of_nonneg_left (tailT_add_two_le (hW0 N) (hA N u) (hAW u))
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)

end Step5

/-! ### Step 5 for the flow: (2.79) -/

section FlowStep5

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `2`-loop `(σ, a) = ((+,-), (a, b))` as `LoopData`. -/
def pmData {L : ℕ} (a b : ZMod L) : LoopData L 2 := (![true, false], ![a, b])

theorem pmData_idx {L : ℕ} (a b : ZMod L) : (pmData a b).idx = pmLoop a b := rfl

/-- `W ≤ N` for large `N` (from `W L ≤ N`). -/
theorem eventually_W_le (B : Band Ω) : ∀ᶠ N : ℕ in atTop, (B.W N : ℝ) ≤ N := by
  filter_upwards [B.dim] with N hN
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have : B.W N ≤ N := le_trans (Nat.le_mul_of_pos_right _ hL) hN.1
  exact_mod_cast this

variable {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end FlowStep5

/-! ### Step 5 with a smoothed near-field weight -/

section Step5W

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}
variable {W : ℕ → ℝ} {ℓ η d : ∀ N, U N → ℝ}

end Step5W

/-! ### The flow form of the smoothed Step 5 -/

section FlowStep5W

variable {Ω : Type*} [MeasurableSpace Ω]

variable {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end FlowStep5W

end Step45

end RBM
