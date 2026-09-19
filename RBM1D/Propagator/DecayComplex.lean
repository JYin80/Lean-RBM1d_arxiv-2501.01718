/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Poisson
import RBM1D.Propagator.Decay
import Mathlib.Analysis.PSeries

/-!
# (2.52) on the torus for complex `ξ`, via the Fourier route

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 2.14 (4), (2.52), following
the proof in Appendix B, p. 90:

  `|(Θ_ξ)_{xy}| ≤ C e^{-c‖x-y‖/ℓ̂(ξ)} / (|1-ξ| ℓ̂(ξ))`,  `ℓ̂(ξ) = min(|1-ξ|^{-1/2}, L)`,

for every `‖ξ‖ < 1`, with `C, c` independent of `L` and `ξ`.  `RBM.norm_Theta_apply_le_of_real`
(`RBM1D.Propagator.Decay`) is the real case via the nearest-neighbour closed form; this file
uses only the general Fourier machinery of Appendix B (T8-T10), so it is the route that
survives for general variance profiles.

With `κ = |1-ξ|^{1/2}`, the paper splits into two regimes.

* `κL ≥ 1` (`ℓ̂ = κ⁻¹`): by the periodization `Θ = ∑_n K_{ξ,∞}(u + nL)` and (B.5),
  `|Θ| ≤ (6π²/κ) ∑_n e^{-c₀κ|u+nL|}`; the terms `n ≥ 0` and `n < 0` are two geometric series
  starting at `e^{-c₀κ‖u‖}` with ratio `e^{-c₀κL} ≤ e^{-c₀}`.
* `κL < 1` (`ℓ̂ = L`): by (B.1) and (B.3), the zero mode gives `1/(κ²L)` and the others
  `(1/L) ∑_{p ≠ 0} 6π²/θ(p)² ≤ (3/2) Z L`, `Z = ∑_{n ≠ 0} n⁻²`; and `L ≤ 1/(κ²L)`.

## Main results

* `RBM.tsum_exp_neg_abs_shift_le` : the geometric bound on the periodized exponential
* `RBM.norm_Theta_apply_le_large` : the regime `κL ≥ 1`
* `RBM.norm_Theta_apply_le_small` : the regime `κL < 1`
* `RBM.norm_Theta_apply_le_complex` : **(2.52) for all `‖ξ‖ < 1`**
-/

namespace RBM

open Real

section Geom

/-- `∑_{n ∈ ℤ} e^{-a|u + nL|} ≤ 2 e^{-ad} / (1 - e^{-aL})` for `0 ≤ u < L`, `d ≤ min(u, L-u)`. -/
theorem tsum_exp_neg_abs_shift_le {a : ℝ} (ha : 0 < a) {L : ℕ} (hL : 0 < L) {u : ℤ}
    (hu0 : 0 ≤ u) (huL : u < L) {d : ℝ} (hd1 : d ≤ u) (hd2 : d ≤ L - u) :
    ∑' n : ℤ, exp (-(a * |(u : ℝ) + n * L|)) ≤ 2 * exp (-(a * d)) / (1 - exp (-(a * L))) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set r := exp (-(a * L)) with hr
  have hr0 : 0 ≤ r := (exp_pos _).le
  have hr1 : r < 1 := exp_lt_one_iff.2 (by nlinarith)
  set f : ℤ → ℝ := fun n => exp (-(a * |(u : ℝ) + n * L|)) with hf
  set g : ℕ → ℝ := fun k => exp (-(a * d)) * r ^ k with hg
  have hgs : Summable g := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hrk : ∀ k : ℕ, exp (-(a * d)) * r ^ k = exp (-(a * (d + k * L))) := by
    intro k
    rw [hr, ← exp_nat_mul, ← exp_add]; ring_nf
  have hpos : ∀ k : ℕ, f k ≤ g k := by
    intro k
    simp only [hf, hg, hrk, Int.cast_natCast]
    apply exp_le_exp.2
    have : (u : ℝ) + k * L ≥ 0 := by positivity
    rw [abs_of_nonneg this]
    have hu : d ≤ (u : ℝ) := hd1
    nlinarith
  have hneg : ∀ k : ℕ, f (-(k + 1 : ℤ)) ≤ g k := by
    intro k
    simp only [hf, hg, hrk]
    apply exp_le_exp.2
    push_cast
    have huL' : (u : ℝ) < L := by exact_mod_cast huL
    have : (u : ℝ) + -((k : ℝ) + 1) * L ≤ 0 := by nlinarith
    rw [abs_of_nonpos this]
    nlinarith
  have hf0 : ∀ n, 0 ≤ f n := fun n => (exp_pos _).le
  have s1 : Summable fun k : ℕ => f k := Summable.of_nonneg_of_le (fun k => hf0 _) hpos hgs
  have s2 : Summable fun k : ℕ => f (-(k + 1 : ℤ)) :=
    Summable.of_nonneg_of_le (fun k => hf0 _) hneg hgs
  have hsum : ∑' k : ℕ, g k = exp (-(a * d)) / (1 - r) := by
    simp only [hg]
    rw [Summable.tsum_mul_left _ (summable_geometric_of_lt_one hr0 hr1),
      tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  calc ∑' n : ℤ, f n = ∑' k : ℕ, f k + ∑' k : ℕ, f (-(k + 1 : ℤ)) :=
        tsum_of_nat_of_neg_add_one s1 s2
    _ ≤ ∑' k : ℕ, g k + ∑' k : ℕ, g k :=
        add_le_add (Summable.tsum_le_tsum hpos s1 hgs) (Summable.tsum_le_tsum hneg s2 hgs)
    _ = 2 * exp (-(a * d)) / (1 - r) := by rw [hsum]; ring

end Geom

variable {L : ℕ} [NeZero L] {ξ : ℂ}

omit [NeZero L] in
theorem zdist_le_val (u : ZMod L) : (zdist L u : ℝ) ≤ u.val := by
  exact_mod_cast min_le_left _ _

theorem zdist_le_sub_val (u : ZMod L) : (zdist L u : ℝ) ≤ L - u.val := by
  have h : zdist L u ≤ L - u.val := min_le_right _ _
  have hv : u.val ≤ L := (ZMod.val_lt u).le
  calc (zdist L u : ℝ) ≤ ((L - u.val : ℕ) : ℝ) := by exact_mod_cast h
    _ = L - u.val := by rw [Nat.cast_sub hv]

theorem zdist_le_half (u : ZMod L) : (zdist L u : ℝ) ≤ L / 2 := by
  have h1 := zdist_le_val u
  have h2 := zdist_le_sub_val u
  linarith

/-- **(2.52), regime `κL ≥ 1`**: `|(Θ_ξ)_{xy}| ≤ (12π²/(1 - e^{-c₀}))/κ · e^{-c₀ κ ‖x - y‖}`. -/
theorem norm_Theta_apply_le_large (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1)
    (hκL : 1 ≤ √‖1 - ξ‖ * L) (x y : ZMod L) :
    ‖Theta L ξ x y‖ ≤ 12 * π ^ 2 / (1 - exp (-cZero)) / √‖1 - ξ‖
      * exp (-(cZero * √‖1 - ξ‖ * zdist L (x - y))) := by
  set κ := √‖1 - ξ‖ with hκdef
  have hκ : 0 < κ := sqrt_norm_one_sub_pos hξ
  set a := cZero * κ with ha_def
  have ha : 0 < a := mul_pos cZero_pos hκ
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  set u : ℤ := ((x - y).val : ℤ) with hu
  have hu0 : 0 ≤ u := Nat.cast_nonneg _
  have huL : u < L := by rw [hu]; exact_mod_cast ZMod.val_lt (x - y)
  set d : ℝ := (zdist L (x - y) : ℝ) with hd
  have hd1 : d ≤ u := by rw [hu]; push_cast; exact zdist_le_val _
  have hd2 : d ≤ L - u := by rw [hu]; push_cast; exact zdist_le_sub_val _
  -- summability of the norms
  have hbound : ∀ n : ℤ, ‖Kinf ξ (u + n * L)‖ ≤ 6 * π ^ 2 / κ * exp (-(a * |(u : ℝ) + n * L|)) := by
    intro n
    have := norm_Kinf_le hξ (u + n * L)
    push_cast at this
    simpa [ha_def, mul_assoc] using this
  have hexp_sum : Summable fun n : ℤ => exp (-(a * |(u : ℝ) + n * L|)) := by
    refine Summable.of_nonneg_of_le (fun _ => (exp_pos _).le) (fun n => ?_)
      ((summable_exp_neg_abs_int ha).mul_left (exp (a * |(u : ℝ)|)))
    rw [← exp_add]
    apply exp_le_exp.2
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL0
    have h1 : |(n : ℝ)| ≤ |(n : ℝ)| * L := le_mul_of_one_le_right (abs_nonneg _) hL1
    have h2 : |(n : ℝ)| * L = |((u : ℝ) + n * L) + -u| := by
      rw [add_neg_cancel_comm, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < L)]
    have h3 := abs_add_le ((u : ℝ) + n * L) (-(u : ℝ))
    rw [abs_neg] at h3
    nlinarith
  have hnorm_sum : Summable fun n : ℤ => ‖Kinf ξ (u + n * L)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hexp_sum.mul_left _)
  -- the geometric bound, and `e^{-aL} ≤ e^{-c₀}`
  have hgeom := tsum_exp_neg_abs_shift_le ha hL0 hu0 huL hd1 hd2
  have haL : exp (-(a * L)) ≤ exp (-cZero) := by
    apply exp_le_exp.2
    have : cZero ≤ cZero * (κ * L) := le_mul_of_one_le_right cZero_pos.le hκL
    simp only [ha_def]; nlinarith
  have hc1 : 0 < 1 - exp (-cZero) := by
    have := exp_lt_one_iff.2 (neg_lt_zero.2 cZero_pos); linarith
  rw [Theta_apply_periodize L hL hξ]
  calc ‖∑' n : ℤ, Kinf ξ (u + n * L)‖
      ≤ ∑' n : ℤ, ‖Kinf ξ (u + n * L)‖ := norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ ∑' n : ℤ, 6 * π ^ 2 / κ * exp (-(a * |(u : ℝ) + n * L|)) :=
        Summable.tsum_le_tsum hbound hnorm_sum (hexp_sum.mul_left _)
    _ = 6 * π ^ 2 / κ * ∑' n : ℤ, exp (-(a * |(u : ℝ) + n * L|)) :=
        Summable.tsum_mul_left _ hexp_sum
    _ ≤ 6 * π ^ 2 / κ * (2 * exp (-(a * d)) / (1 - exp (-(a * L)))) := by gcongr
    _ ≤ 6 * π ^ 2 / κ * (2 * exp (-(a * d)) / (1 - exp (-cZero))) := by
        gcongr
    _ = 12 * π ^ 2 / (1 - exp (-cZero)) / κ * exp (-(cZero * κ * d)) := by
        rw [ha_def]; field_simp; ring

/-- `Z = ∑_{n ∈ ℤ} 1/n²` (the `n = 0` term is `0` in Lean's convention). -/
noncomputable def zetaTwoInt : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2

theorem summable_one_div_int_sq : Summable fun n : ℤ => 1 / (n : ℝ) ^ 2 := by
  have h := Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2)
  refine Summable.of_nat_of_neg ?_ ?_
  · simp only [Int.cast_natCast]; exact h
  · simp only [Int.cast_neg, Int.cast_natCast, neg_sq]; exact h

theorem zetaTwoInt_nonneg : 0 ≤ zetaTwoInt := tsum_nonneg fun n => by positivity

/-- `∑_{p ≠ 0} 1/p̃² ≤ Z` over the nonzero frequencies of `ℤ_L`. -/
theorem sum_one_div_valMinAbs_sq_le :
    ∑ p ∈ Finset.univ.erase (0 : ZMod L), 1 / ((p.valMinAbs : ℤ) : ℝ) ^ 2 ≤ zetaTwoInt := by
  rw [← Finset.sum_image (f := fun n : ℤ => 1 / (n : ℝ) ^ 2)
    (fun a _ b _ h => ZMod.valMinAbs_inj.1 h)]
  exact Summable.sum_le_tsum _ (fun n _ => by positivity) summable_one_div_int_sq

/-- **(2.52), regime `κL < 1`**: `|(Θ_ξ)_{xy}| ≤ (1 + (3/2) Z)/(κ² L)`. -/
theorem norm_Theta_apply_le_small (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1)
    (hκL : √‖1 - ξ‖ * L < 1) (x y : ZMod L) :
    ‖Theta L ξ x y‖ ≤ (1 + 3 / 2 * zetaTwoInt) / (‖1 - ξ‖ * L) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hκ : 0 < √‖1 - ξ‖ := sqrt_norm_one_sub_pos hξ
  have hw : 0 < ‖1 - ξ‖ := by rw [← sq_sqrt_norm_one_sub ξ]; positivity
  have hZ := zetaTwoInt_nonneg
  -- each Fourier mode
  set F : ZMod L → ℝ := fun p => ‖(1 - ξ * Shat L p)⁻¹‖ with hF
  have hterm : ∀ p : ZMod L, ‖ZMod.stdAddChar (p * (x - y)) / (1 - ξ * Shat L p)‖ = F p := by
    intro p
    rw [norm_div, AddChar.norm_apply, one_div, ← norm_inv]
  have hF0 : F 0 = 1 / ‖1 - ξ‖ := by
    have : Shat L 0 = 1 := by simp [Shat]; norm_num
    simp only [hF, this, mul_one, norm_inv, one_div]
  have hFp : ∀ p ∈ Finset.univ.erase (0 : ZMod L),
      F p ≤ 3 / 2 * L ^ 2 * (1 / ((p.valMinAbs : ℤ) : ℝ) ^ 2) := by
    intro p hp
    have hp0 : p ≠ 0 := Finset.ne_of_mem_erase hp
    have hv : ((p.valMinAbs : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast (ZMod.valMinAbs_eq_zero p).not.2 hp0
    have hθ : theta L p ^ 2 = 4 * π ^ 2 * ((p.valMinAbs : ℤ) : ℝ) ^ 2 / L ^ 2 := by
      rw [theta]; field_simp; ring
    have hθpos : 0 < theta L p ^ 2 := by rw [hθ]; positivity
    have hlow := le_norm_one_sub_mul_Shat hξ p
    have hpos : 0 < (‖1 - ξ‖ + theta L p ^ 2) / (6 * π ^ 2) := by positivity
    calc F p = ‖1 - ξ * Shat L p‖⁻¹ := by simp only [hF, norm_inv]
      _ ≤ ((‖1 - ξ‖ + theta L p ^ 2) / (6 * π ^ 2))⁻¹ := inv_anti₀ hpos hlow
      _ ≤ (theta L p ^ 2 / (6 * π ^ 2))⁻¹ := by
          apply inv_anti₀ (by positivity); gcongr; linarith
      _ = 3 / 2 * L ^ 2 * (1 / ((p.valMinAbs : ℤ) : ℝ) ^ 2) := by
          rw [hθ]; field_simp; ring
  have hsum : ∑ p : ZMod L, F p ≤ 1 / ‖1 - ξ‖ + 3 / 2 * L ^ 2 * zetaTwoInt := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod L)), hF0]
    gcongr
    calc ∑ p ∈ Finset.univ.erase (0 : ZMod L), F p
        ≤ ∑ p ∈ Finset.univ.erase (0 : ZMod L), 3 / 2 * L ^ 2 * (1 / ((p.valMinAbs : ℤ) : ℝ) ^ 2) :=
          Finset.sum_le_sum hFp
      _ = 3 / 2 * L ^ 2 * ∑ p ∈ Finset.univ.erase (0 : ZMod L),
            1 / ((p.valMinAbs : ℤ) : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 3 / 2 * L ^ 2 * zetaTwoInt := by gcongr; exact sum_one_div_valMinAbs_sq_le
  -- `L ≤ 1/(κ² L)`
  have hLL : ‖1 - ξ‖ * L ^ 2 ≤ 1 := by
    have h := mul_lt_mul'' hκL hκL (by positivity) (by positivity)
    rw [one_mul] at h
    nlinarith [sq_sqrt_norm_one_sub ξ]
  rw [Theta_apply_fourier L hL hξ, norm_mul, norm_inv, Complex.norm_natCast]
  calc (L : ℝ)⁻¹ * ‖∑ p : ZMod L, ZMod.stdAddChar (p * (x - y)) / (1 - ξ * Shat L p)‖
      ≤ (L : ℝ)⁻¹ * ∑ p : ZMod L, F p := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun p _ => hterm p
    _ ≤ (L : ℝ)⁻¹ * (1 / ‖1 - ξ‖ + 3 / 2 * L ^ 2 * zetaTwoInt) := by gcongr
    _ ≤ (1 + 3 / 2 * zetaTwoInt) / (‖1 - ξ‖ * L) := by
        have e1 : (L : ℝ)⁻¹ * (1 / ‖1 - ξ‖ + 3 / 2 * L ^ 2 * zetaTwoInt)
            = 1 / (‖1 - ξ‖ * L) + 3 / 2 * zetaTwoInt * L := by field_simp
        have e2 : (1 + 3 / 2 * zetaTwoInt) / (‖1 - ξ‖ * L)
            = 1 / (‖1 - ξ‖ * L) + 3 / 2 * zetaTwoInt * (1 / (‖1 - ξ‖ * L)) := by ring
        have hLle : (L : ℝ) ≤ 1 / (‖1 - ξ‖ * L) := by
          rw [le_div_iff₀ (by positivity)]; nlinarith
        rw [e1, e2]
        gcongr

/-- The constant of (2.52) for complex `ξ`. -/
noncomputable def cTwo52 : ℝ :=
  12 * π ^ 2 / (1 - exp (-cZero)) + (1 + 3 / 2 * zetaTwoInt) * exp cZero

theorem cTwo52_pos : 0 < cTwo52 := by
  have hc1 : 0 < 1 - exp (-cZero) := by
    have := exp_lt_one_iff.2 (neg_lt_zero.2 cZero_pos); linarith
  unfold cTwo52
  have := zetaTwoInt_nonneg
  positivity

/-- **(2.52) for all `‖ξ‖ < 1`**:
`|(Θ_ξ)_{xy}| ≤ C e^{-c₀ ‖x - y‖/ℓ̂(ξ)} / (|1 - ξ| ℓ̂(ξ))`. -/
theorem norm_Theta_apply_le_complex (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1) (x y : ZMod L) :
    ‖Theta L ξ x y‖ ≤
      cTwo52 * exp (-(cZero * zdist L (x - y) / ellHat L ξ)) / (‖1 - ξ‖ * ellHat L ξ) := by
  set κ := √‖1 - ξ‖ with hκdef
  have hκ : 0 < κ := sqrt_norm_one_sub_pos hξ
  have hκ2 : κ ^ 2 = ‖1 - ξ‖ := sq_sqrt_norm_one_sub ξ
  have hLr : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 < 1 - exp (-cZero) := by
    have := exp_lt_one_iff.2 (neg_lt_zero.2 cZero_pos); linarith
  have hZ := zetaTwoInt_nonneg
  set d : ℝ := (zdist L (x - y) : ℝ) with hd
  rcases le_or_gt 1 (κ * L) with hbig | hsmall
  · -- `ℓ̂ = 1/κ`
    have hell : ellHat L ξ = 1 / κ := by
      rw [ellHat]; apply min_eq_left
      rw [div_le_iff₀ hκ]; linarith
    have h := norm_Theta_apply_le_large hL hξ hbig x y
    rw [hell]
    have e1 : ‖1 - ξ‖ * (1 / κ) = κ := by rw [← hκ2]; field_simp
    have e2 : cZero * d / (1 / κ) = cZero * κ * d := by field_simp
    rw [e1, e2]
    have hA : 12 * π ^ 2 / (1 - exp (-cZero)) ≤ cTwo52 := by
      unfold cTwo52
      have : 0 ≤ (1 + 3 / 2 * zetaTwoInt) * exp cZero := by positivity
      linarith
    calc ‖Theta L ξ x y‖ ≤ 12 * π ^ 2 / (1 - exp (-cZero)) / κ * exp (-(cZero * κ * d)) := h
      _ ≤ cTwo52 / κ * exp (-(cZero * κ * d)) := by gcongr
      _ = cTwo52 * exp (-(cZero * κ * d)) / κ := by ring
  · -- `ℓ̂ = L`
    have hell : ellHat L ξ = L := by
      rw [ellHat]; apply min_eq_right
      rw [le_div_iff₀ hκ]; linarith
    have h := norm_Theta_apply_le_small hL hξ hsmall x y
    rw [hell]
    refine h.trans ?_
    have hw : 0 < ‖1 - ξ‖ := by rw [← hκ2]; positivity
    rw [div_le_div_iff_of_pos_right (mul_pos hw hLr)]
    -- `e^{-c₀ d/L} ≥ e^{-c₀}` since `d ≤ L/2`
    have hdL : d / L ≤ 1 := by
      rw [div_le_one hLr]; have := zdist_le_half (x - y); linarith
    have hexp : exp (-cZero) ≤ exp (-(cZero * d / L)) := by
      apply exp_le_exp.2
      have : cZero * d / L ≤ cZero := by
        rw [mul_div_assoc]; exact mul_le_of_le_one_right cZero_pos.le hdL
      linarith
    have hkey : (1 + 3 / 2 * zetaTwoInt) ≤ cTwo52 * exp (-cZero) := by
      unfold cTwo52
      have h1 : exp cZero * exp (-cZero) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
      have h2 : 0 ≤ 12 * π ^ 2 / (1 - exp (-cZero)) * exp (-cZero) := by positivity
      nlinarith
    calc 1 + 3 / 2 * zetaTwoInt ≤ cTwo52 * exp (-cZero) := hkey
      _ ≤ cTwo52 * exp (-(cZero * d / L)) := by
          gcongr; exact cTwo52_pos.le

/-- **(2.52)** in the form of the paper: constants independent of `L` and `ξ`. -/
theorem norm_Theta_apply_le_exists :
    ∃ C > 0, ∃ c > 0, ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ x y : ZMod L,
      ‖Theta L ξ x y‖ ≤ C * exp (-(c * zdist L (x - y) / ellHat L ξ)) / (‖1 - ξ‖ * ellHat L ξ) :=
  ⟨cTwo52, cTwo52_pos, cZero, cZero_pos,
    fun _ _ hL _ hξ x y => norm_Theta_apply_le_complex hL hξ x y⟩

end RBM
