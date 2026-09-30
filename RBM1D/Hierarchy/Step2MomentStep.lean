/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.ChargeReduce
import RBM1D.Hierarchy.Step45
import RBM1D.Hierarchy.Lemma57

/-!
# Step 2: the near/far split of (5.48), and the far field of a near-diagonal tensor

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.39)–(5.48).

## Main results

* `RBM.Step2MomentStep.eq548_of_near_far` — **(5.48)** from its near and far halves.
* `RBM.Step2MomentStep.sum_far_norm_edgeKer_le`, `RBM.Step2MomentStep.sum_norm_edgeKer_one_row_le`
  — the tail of the row sum of the edge kernel beyond a distance `Δ`, and its row bound at
  `ξ = 1`.
* `RBM.Step2MomentStep.norm_Uker_supp_far_le` — **the support estimate**: a tensor living on the
  diagonal band `‖b₁ - b₂‖ ≤ ρ` cannot produce a far field.  This is the paper's "from the decay
  of `U_{u,t}`, `(U_{u,t,σ} ∘ f₂)_a` is exponentially small", made quantitative, and the
  estimate behind the indicator `1(≤ 3ℓ*)` of (5.41).

The flow form of (5.48) from its two halves, at an `N`-dependent energy, is
`RBM.Step2MomentStep.flowEq548_of_near_farN` in `RBM1D/EnergyN/Hierarchy/Step2MomentStep.lean`.
-/

namespace RBM

namespace Step2MomentStep

open Real Filter MeasureTheory

/-! ### 1. The arithmetic of (5.39)–(5.47) for the (2.73)-reduced shape of (5.35) -/

section Arith

end Arith

/-! ### 2. The three side conditions, i.e. the exponent table -/

section Exponents

variable {x R r A : ℝ}

end Exponents

/-! ### 3. (5.44)'s near-field term: integrate first, then take the supremum -/

section Near

variable {E : ℝ}

end Near

/-! ### 4. Satisfiability: the side conditions hold for the flow -/

section Satisfiable

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

end Satisfiable

/-! ### 5. De-truncation at the probability level: the gap-crossing argument -/

section Crossing

end Crossing

/-! ### 6. The continuum of times reduced to fixed times -/

section BootPPNet

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

open Filter

end BootPPNet

/-! ### 7. Why the `(+,+)` bootstrap cannot be replaced by finitely many `≺`-passes -/

section Necessity

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

end Necessity

/-! ### 8. (5.48): the near/far split -/

section Eq548

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {U : ℕ → Type*}
variable {W : ℕ → ℝ} {ℓ η d pref : ∀ N, U N → ℝ}

/-- **(5.48) from its two halves.**  The paper's (5.48),

`(L-K)_{u,a} / T_{u,D}(d) ≺ (η_s/η_u)² 1(d ≤ 6ℓ*_u) + 1`,

is exactly the conjunction of

* `hnear` — the bound with the prefactor everywhere, i.e. `(L-K)_{u,a} ≺ pref · T_{u,D}(d)`
  (for the flow this is the **sharp** bound `J*_{u,D} ≺ (η_s/η_u)²` of the remark after
  (5.47)), and
* `hfar` — the same bound **without** any prefactor, asserted only where `d > 6ℓ*_u`.

`hfar` does not follow from a bound `J*_{u,D} ≺ (η_s/η_u)^4`, which carries the prefactor
at every distance, whereas `RBM.Step45.Eq548` asks for `1` beyond `6ℓ*_u`.  It comes from
keeping the indicators of (5.39), (5.41) and (5.44) through the one-step bound (the paper's
`1(|a₁-a₂| ≤ ℓ*_t)`, `1(≤ 3ℓ*_t)`, `1(≤ 6ℓ*_t)`). -/
theorem eq548_of_near_far {ξ : ∀ N, U N → Ω → ℝ} (hW : ∀ N, 0 ≤ W N)
    (hpref : ∀ N u, 0 ≤ pref N u)
    (hnear : ∀ D : ℝ, 0 < D → StochDom P ξ
      (fun N u _ => pref N u * tailT (W N) (ℓ N u) (η N u) D (d N u)))
    (hfar : ∀ D : ℝ, 0 < D → StochDom P
      (fun N u ω => if d N u ≤ 6 * ellStar (W N) (ℓ N u) then 0 else ξ N u ω)
      (fun N u _ => tailT (W N) (ℓ N u) (η N u) D (d N u))) :
    Step45.Eq548 P ξ W ℓ η d pref := by
  intro D hD
  refine StochDom.of_subset_union (hnear D hD) (hfar D hD) fun τ hτ => ⟨τ, hτ, ?_⟩
  refine Filter.Eventually.of_forall fun N => ?_
  rintro ω ⟨u, hu⟩
  have hT0 : 0 ≤ tailT (W N) (ℓ N u) (η N u) D (d N u) := tailT_nonneg (hW N) _
  have hτ0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  by_cases hnearcase : d N u ≤ 6 * ellStar (W N) (ℓ N u)
  · refine Or.inl ⟨u, ?_⟩
    have hite : (if d N u ≤ 6 * ellStar (W N) (ℓ N u) then (1 : ℝ) else 0) = 1 := by
      simp [hnearcase]
    simp only [hite] at hu
    have h1 : pref N u * tailT (W N) (ℓ N u) (η N u) D (d N u)
        ≤ tailT (W N) (ℓ N u) (η N u) D (d N u) * (pref N u * 1 + 1) := by
      have := hpref N u
      nlinarith
    calc (N : ℝ) ^ τ * (pref N u * tailT (W N) (ℓ N u) (η N u) D (d N u))
        ≤ (N : ℝ) ^ τ * (tailT (W N) (ℓ N u) (η N u) D (d N u) * (pref N u * 1 + 1)) := by
          exact mul_le_mul_of_nonneg_left h1 hτ0
      _ < ξ N u ω := hu
  · refine Or.inr ⟨u, ?_⟩
    have hite : (if d N u ≤ 6 * ellStar (W N) (ℓ N u) then (1 : ℝ) else 0) = 0 := by
      simp [hnearcase]
    have hite' : (if d N u ≤ 6 * ellStar (W N) (ℓ N u) then (0 : ℝ) else ξ N u ω) = ξ N u ω := by
      simp [hnearcase]
    simp only [hite] at hu
    simp only [hite']
    calc (N : ℝ) ^ τ * tailT (W N) (ℓ N u) (η N u) D (d N u)
        = (N : ℝ) ^ τ * (tailT (W N) (ℓ N u) (η N u) D (d N u) * (pref N u * 0 + 1)) := by ring
      _ < ξ N u ω := hu

end Eq548

/-! ### 9. The target of the one-step improvement -/

section StepAnalysis

open Filter

end StepAnalysis

/-! ### 10. Satisfiability witnesses (compiled) -/

section Sat

end Sat




/-! ### 11. The far field of (5.48): the indicators of (5.39)/(5.41)/(5.44), carried through

The paper's indicators `1(≤ ℓ*_t)`, `1(≤ 3ℓ*_t)`, `1(≤ 6ℓ*_t)` of (5.39), (5.41) and (5.44)
are what makes the far field of (5.48) `O(1)`.  The estimate that does the work is the support
estimate `norm_Uker_supp_far_le`: a tensor living on the diagonal band `‖b₁ - b₂‖ ≤ ρ` cannot
produce a far field.  At `‖a₁ - a₂‖ ≥ ρ + 2Δ` its image under `U_{u,v}` is at most
`128 e³ ((1-u)/(1-v))² e^{-Δ/(2ℓ_v)}` times its sup norm, because the edge kernel `Θ` decays
like `e^{-‖x-c‖/ℓ_v}` and the mass has to move a distance `≥ Δ` at each end.
-/

section Supp

variable (L : ℕ) [NeZero L]

/-- Tail of the row sum of the edge kernel beyond distance `Δ > 0`. -/
theorem sum_far_norm_edgeKer_le (hL : 3 ≤ L) {u v : ℝ} (huv : u ≤ v) (hv0 : 0 ≤ v)
    (hv1 : v < 1) {Δ : ℝ} (hΔ : 0 < Δ) (x : ZMod L) :
    ∑ c : ZMod L, ‖edgeKer L 1 (u : ℂ) (v : ℂ) x c‖ *
        (if Δ ≤ (zdist L (x - c) : ℝ) then 1 else 0)
      ≤ 64 * exp 3 * ((v - u) / (1 - v)) * exp (-(Δ / ellHat L (v : ℂ) / 2)) := by
  have hℓ2 : (1:ℝ)/2 ≤ ellHat L (v : ℂ) := half_le_ellHat_real L hL hv0 hv1
  have hℓ0 : 0 < ellHat L (v : ℂ) := by linarith
  have h1v : 0 < 1 - v := by linarith
  set ℓ := ellHat L (v : ℂ) with hℓdef
  set κ := 8 * exp 3 * (v - u) / ((1 - v) * ℓ) with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have key : ∀ c : ZMod L, ‖edgeKer L 1 (u : ℂ) (v : ℂ) x c‖ *
      (if Δ ≤ (zdist L (x - c) : ℝ) then 1 else 0)
      ≤ κ * exp (-(Δ / ℓ / 2)) * exp (-((zdist L (x - c) : ℝ) / ℓ / 2)) := by
    intro c
    by_cases hc : Δ ≤ (zdist L (x - c) : ℝ)
    · rw [show (if Δ ≤ (zdist L (x - c) : ℝ) then (1:ℝ) else 0) = 1 by simp [hc], mul_one]
      have hone : ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) x c‖ = 0 := by
        have hxc : x ≠ c := by
          rintro rfl; simp [zdist] at hc; linarith
        simp [Matrix.one_apply_ne hxc]
      have he : edgeKer L 1 (u : ℂ) (v : ℂ) x c
          = (1 : Matrix (ZMod L) (ZMod L) ℂ) x c + (edgeKer L 1 (u : ℂ) (v : ℂ) - 1) x c := by
        rw [Matrix.sub_apply]; ring
      rw [he]
      refine (norm_add_le _ _).trans ?_
      rw [hone, zero_add]
      refine (norm_edgeKer_one_sub_one_le L hL huv hv0 hv1 x c).trans ?_
      have e1 : 8 * exp 3 * (v - u) / ((1 - v) * ℓ) = κ := rfl
      rw [e1]
      have hsplit : exp (-((zdist L (x - c) : ℝ) / ℓ))
          = exp (-((zdist L (x - c) : ℝ) / ℓ / 2)) * exp (-((zdist L (x - c) : ℝ) / ℓ / 2)) := by
        rw [← exp_add]; ring_nf
      rw [hsplit, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
      refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) hκ0
      have : Δ / ℓ ≤ (zdist L (x - c) : ℝ) / ℓ := by
        exact div_le_div_of_nonneg_right hc hℓ0.le
      linarith
    · rw [show (if Δ ≤ (zdist L (x - c) : ℝ) then (1:ℝ) else 0) = 0 by simp [hc], mul_zero]
      positivity
  calc ∑ c : ZMod L, ‖edgeKer L 1 (u : ℂ) (v : ℂ) x c‖ *
        (if Δ ≤ (zdist L (x - c) : ℝ) then 1 else 0)
      ≤ ∑ c : ZMod L, κ * exp (-(Δ / ℓ / 2)) * exp (-((zdist L (x - c) : ℝ) / ℓ / 2)) :=
        Finset.sum_le_sum fun c _ => key c
    _ = κ * exp (-(Δ / ℓ / 2)) * ∑ c : ZMod L, exp (-((zdist L (x - c) : ℝ) / ℓ / 2)) := by
        rw [← Finset.mul_sum]
    _ ≤ κ * exp (-(Δ / ℓ / 2)) * (8 * ℓ) := by
        refine mul_le_mul_of_nonneg_left (sum_exp_neg_zdist_half_le L hℓ2 x) (by positivity)
    _ = 64 * exp 3 * ((v - u) / (1 - v)) * exp (-(Δ / ℓ / 2)) := by
        rw [hκ]; field_simp; ring


/-- Row bound of the edge kernel at `ξ = 1`: `∑_c |K_{xc}| ≤ (1-u)/(1-v)`. -/
theorem sum_norm_edgeKer_one_row_le (hL : 3 ≤ L) {u v : ℝ} (huv : u ≤ v) (hv0 : 0 ≤ v)
    (hv1 : v < 1) (x : ZMod L) :
    ∑ c : ZMod L, ‖edgeKer L 1 (u : ℂ) (v : ℂ) x c‖ ≤ (1 - u) / (1 - v) := by
  have hξ : ‖(1 : ℂ)‖ ≤ 1 := by simp
  have h := sum_norm_edgeKer_row_le L hL (ξ := 1) (s := (u : ℂ)) (t := (v : ℂ))
    (norm_ofReal_mul_lt_one hv0 hv1 hξ) x
  have e1 : ‖((u : ℂ) - (v : ℂ)) * 1‖ = v - u := by
    rw [mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]; ring
  have e2 : ‖(v : ℂ) * 1‖ = v := by
    rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]
  rw [e1, e2, one_add_row_eq hv1] at h
  exact h

/-- **The far field of a near-diagonal tensor.**  If `A` is supported on `‖b₁ - b₂‖ ≤ ρ` and
bounded by `M` there, then at distance `‖a₁ - a₂‖ ≥ ρ + 2Δ` the image `U_{u,v} ∘ A` is
exponentially small in `Δ/ℓ_v`.  This is the estimate behind the indicator `1(≤ 3ℓ*)` of
(5.41): a tensor living on the diagonal band cannot produce a far-field contribution. -/
theorem norm_Uker_supp_far_le (hL : 3 ≤ L) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v)
    (hv1 : v < 1) {ρ Δ M : ℝ} (hM : 0 ≤ M) (hΔ : 0 < Δ) {A : LoopArg L 2 → ℂ}
    (hA : ∀ b, ‖A b‖ ≤ M * (if (zdist L (b 0 - b 1) : ℝ) ≤ ρ then 1 else 0))
    (a : LoopArg L 2) (hd : ρ + 2 * Δ ≤ (zdist L (a 0 - a 1) : ℝ)) :
    ‖Uker L (fun _ => (1 : ℂ)) (u : ℂ) (v : ℂ) A a‖
      ≤ 128 * exp 3 * M * ((1 - u) / (1 - v)) ^ 2 *
        exp (-(Δ / ellHat L (v : ℂ) / 2)) := by
  have hv0 : 0 ≤ v := hu0.trans huv
  have h1v : 0 < 1 - v := by linarith
  have h1u : 0 < 1 - u := by linarith
  set K := edgeKer L 1 (u : ℂ) (v : ℂ) with hK
  set R := (1 - u) / (1 - v) with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set g : ZMod L → ℝ := fun x => if Δ ≤ (zdist L (a 0 - x) : ℝ) then 1 else 0 with hg
  set h : ZMod L → ℝ := fun y => if Δ ≤ (zdist L (a 1 - y) : ℝ) then 1 else 0 with hh
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    show (0:ℝ) ≤ if Δ ≤ (zdist L (a 0 - x) : ℝ) then 1 else 0
    split_ifs <;> norm_num
  have hh0 : ∀ y, 0 ≤ h y := fun y => by
    show (0:ℝ) ≤ if Δ ≤ (zdist L (a 1 - y) : ℝ) then 1 else 0
    split_ifs <;> norm_num
  have hgh : ∀ b : LoopArg L 2, ‖A b‖ ≤ M * (g (b 0) + h (b 1)) := by
    intro b
    by_cases hb : (zdist L (b 0 - b 1) : ℝ) ≤ ρ
    · have h3 := zdist_triangle_three L (a 0) (a 1) (b 0) (b 1)
      have hor : Δ ≤ (zdist L (a 0 - b 0) : ℝ) ∨ Δ ≤ (zdist L (a 1 - b 1) : ℝ) := by
        by_contra hno
        push Not at hno
        obtain ⟨h1, h2⟩ := hno
        linarith
      have h1 : (1 : ℝ) ≤ g (b 0) + h (b 1) := by
        rcases hor with hc | hc
        · have : g (b 0) = 1 := by
            show (if Δ ≤ (zdist L (a 0 - b 0) : ℝ) then (1:ℝ) else 0) = 1
            simp [hc]
          linarith [hh0 (b 1)]
        · have : h (b 1) = 1 := by
            show (if Δ ≤ (zdist L (a 1 - b 1) : ℝ) then (1:ℝ) else 0) = 1
            simp [hc]
          linarith [hg0 (b 0)]
      calc ‖A b‖ ≤ M * (if (zdist L (b 0 - b 1) : ℝ) ≤ ρ then 1 else 0) := hA b
        _ = M := by rw [show (if (zdist L (b 0 - b 1) : ℝ) ≤ ρ then (1:ℝ) else 0) = 1 by
              simp [hb], mul_one]
        _ ≤ M * (g (b 0) + h (b 1)) := le_mul_of_one_le_right hM h1
    · have : ‖A b‖ ≤ 0 := by
        have := hA b
        rwa [show (if (zdist L (b 0 - b 1) : ℝ) ≤ ρ then (1:ℝ) else 0) = 0 by simp [hb],
          mul_zero] at this
      have hge : 0 ≤ M * (g (b 0) + h (b 1)) := by
        have := hg0 (b 0); have := hh0 (b 1); positivity
      linarith
  have hstart : ‖Uker L (fun _ => (1 : ℂ)) (u : ℂ) (v : ℂ) A a‖
      ≤ M * (∑ x : ZMod L, ∑ y : ZMod L,
        ‖K (a 0) x‖ * ‖K (a 1) y‖ * (g x + h y)) := by
    rw [Uker_apply]
    refine (norm_sum_le _ _).trans ?_
    rw [← sum_fin_two_fun L (fun x y => ‖K (a 0) x‖ * ‖K (a 1) y‖ * (g x + h y)),
      Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [norm_mul, Fin.prod_univ_two, norm_mul]
    have hkk : 0 ≤ ‖K (a 0) (b 0)‖ * ‖K (a 1) (b 1)‖ := by positivity
    calc ‖K (a 0) (b 0)‖ * ‖K (a 1) (b 1)‖ * ‖A b‖
        ≤ ‖K (a 0) (b 0)‖ * ‖K (a 1) (b 1)‖ * (M * (g (b 0) + h (b 1))) :=
          mul_le_mul_of_nonneg_left (hgh b) hkk
      _ = M * (‖K (a 0) (b 0)‖ * ‖K (a 1) (b 1)‖ * (g (b 0) + h (b 1))) := by ring
  have hexpand : ∑ x : ZMod L, ∑ y : ZMod L, ‖K (a 0) x‖ * ‖K (a 1) y‖ * (g x + h y)
      = (∑ x : ZMod L, ‖K (a 0) x‖ * g x) * (∑ y : ZMod L, ‖K (a 1) y‖)
        + (∑ x : ZMod L, ‖K (a 0) x‖) * (∑ y : ZMod L, ‖K (a 1) y‖ * h y) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  set T := 64 * exp 3 * ((v - u) / (1 - v)) * exp (-(Δ / ellHat L (v : ℂ) / 2)) with hT
  have hT0 : 0 ≤ T := by rw [hT]; have : 0 ≤ v - u := by linarith
                         positivity
  have hS0 := sum_far_norm_edgeKer_le L hL huv hv0 hv1 hΔ (a 0)
  have hS1 := sum_far_norm_edgeKer_le L hL huv hv0 hv1 hΔ (a 1)
  have hR0' := sum_norm_edgeKer_one_row_le L hL huv hv0 hv1 (a 0)
  have hR1' := sum_norm_edgeKer_one_row_le L hL huv hv0 hv1 (a 1)
  have hsum0 : (0:ℝ) ≤ ∑ x : ZMod L, ‖K (a 0) x‖ * g x :=
    Finset.sum_nonneg fun x _ => mul_nonneg (norm_nonneg _) (hg0 x)
  have hsum1 : (0:ℝ) ≤ ∑ y : ZMod L, ‖K (a 1) y‖ * h y :=
    Finset.sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (hh0 y)
  have hrow0 : (0:ℝ) ≤ ∑ x : ZMod L, ‖K (a 0) x‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hrow1 : (0:ℝ) ≤ ∑ y : ZMod L, ‖K (a 1) y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hTR : T ≤ 64 * exp 3 * R * exp (-(Δ / ellHat L (v : ℂ) / 2)) := by
    have hle : (v - u) / (1 - v) ≤ R := by rw [hR]; gcongr
    have hE : (0:ℝ) ≤ exp (-(Δ / ellHat L (v : ℂ) / 2)) := (exp_pos _).le
    have h64 : (0:ℝ) ≤ 64 * exp 3 := by positivity
    rw [hT]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle h64) hE
  have hfin : ∑ x : ZMod L, ∑ y : ZMod L, ‖K (a 0) x‖ * ‖K (a 1) y‖ * (g x + h y)
      ≤ 128 * exp 3 * R ^ 2 * exp (-(Δ / ellHat L (v : ℂ) / 2)) := by
    rw [hexpand]
    have hE0 : (0:ℝ) < exp (-(Δ / ellHat L (v : ℂ) / 2)) := exp_pos _
    have h1 : (∑ x : ZMod L, ‖K (a 0) x‖ * g x) * (∑ y : ZMod L, ‖K (a 1) y‖)
        ≤ (64 * exp 3 * R * exp (-(Δ / ellHat L (v : ℂ) / 2))) * R :=
      mul_le_mul (hS0.trans hTR) hR1' hrow1 (by positivity)
    have h2 : (∑ x : ZMod L, ‖K (a 0) x‖) * (∑ y : ZMod L, ‖K (a 1) y‖ * h y)
        ≤ R * (64 * exp 3 * R * exp (-(Δ / ellHat L (v : ℂ) / 2))) :=
      mul_le_mul hR0' (hS1.trans hTR) hsum1 hR0
    nlinarith
  calc ‖Uker L (fun _ => (1 : ℂ)) (u : ℂ) (v : ℂ) A a‖
      ≤ M * (∑ x : ZMod L, ∑ y : ZMod L, ‖K (a 0) x‖ * ‖K (a 1) y‖ * (g x + h y)) := hstart
    _ ≤ M * (128 * exp 3 * R ^ 2 * exp (-(Δ / ellHat L (v : ℂ) / 2))) :=
        mul_le_mul_of_nonneg_left hfin hM
    _ = 128 * exp 3 * M * R ^ 2 * exp (-(Δ / ellHat L (v : ℂ) / 2)) := by ring


end Supp

section FarStep

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s : ℕ → ℝ}

variable {t : ℕ → ℝ}

/-! ### Satisfiability of the far-field hypotheses -/

section FarSat

end FarSat

end FarStep

end Step2MomentStep

end RBM
