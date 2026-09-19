/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Contour

/-!
# Periodization: `Θ_ξ` from the infinite-volume kernel

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Appendix B, p. 89, the line after
(B.2):

  `(Θ^{(B)}_ξ)_{xy} = K_{ξ,L}(u) = ∑_{n ∈ ℤ} K_{ξ,∞}(u + nL)`,  `u = x - y`.

The paper says "by comparing Fourier coefficients (or by the Poisson summation formula)".
We avoid Fourier inversion altogether and use uniqueness of the inverse instead:

1. `K_{ξ,∞}` solves the lattice equation `K - ξ S K = δ₀` on `ℤ` (`RBM.Kinf_sub_SB`), because
   `∫_{-π}^{π} e^{ipw} dp = 2π δ_{w,0}` and `(1 + e^{ip} + e^{-ip})/3 = Ŝ(p)`;
2. by (B.5) the periodization is absolutely summable (`RBM.summable_Kinf_shift`), and it solves
   the same equation on `ℤ_L` (`RBM.perK_sub_SB_mulVec`);
3. so its circulant matrix inverts `1 - ξ S^(B)`, and equals `Θ_ξ` (`RBM.eq_Theta_of_mul`),
   exactly as for the Fourier kernel of (B.1) in `RBM1D.Propagator.Symbol`.

## Main results

* `RBM.integral_exp_int` : `∫_{-π}^{π} e^{ipw} dp = 2π δ_{w,0}`
* `RBM.Kinf_sub_SB` : the lattice equation for `K_{ξ,∞}`
* `RBM.summable_Kinf_shift` : `∑_n |K_{ξ,∞}(v + nL)| < ∞`
* `RBM.perSum`, `RBM.perK` : the periodization
* `RBM.Theta_eq_circulant_perK`, `RBM.Theta_apply_periodize` : **the identity after (B.2)**
-/

namespace RBM

open Real Matrix

section Lattice

variable {ξ : ℂ}

/-- `∫_{-π}^{π} e^{ipw} dp = 2π δ_{w,0}` for `w ∈ ℤ`. -/
theorem integral_exp_int (w : ℤ) :
    ∫ p : ℝ in (-π)..π, Complex.exp (Complex.I * p * w)
      = if w = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
  split_ifs with hw
  · subst hw
    have h1 : ∀ p : ℝ, Complex.exp (Complex.I * p * ((0 : ℤ) : ℂ)) = 1 := by intro p; simp
    simp_rw [h1]
    rw [intervalIntegral.integral_const, Complex.real_smul]
    push_cast; ring
  · have hc : Complex.I * (w : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.2 hw)
    have e : ∀ p : ℝ, Complex.exp (Complex.I * p * w) = Complex.exp (Complex.I * w * p) := by
      intro p; ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp (Complex.I * w * (π : ℝ))
        = Complex.exp (Complex.I * w * ((-π : ℝ) : ℂ)) := by
      have : Complex.I * w * (π : ℝ) = Complex.I * w * ((-π : ℝ) : ℂ) + w * (2 * π * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h2, sub_self, zero_div]

theorem continuousOn_kernelFun (hξ : ‖ξ‖ < 1) (u : ℤ) :
    ContinuousOn (fun p : ℝ => kernelFun ξ u p) (Set.uIcc (-π) π) := by
  intro p hp
  rw [Set.uIcc_of_le (by linarith [pi_pos])] at hp
  have hre : |((p : ℂ)).re| ≤ π := by
    rw [Complex.ofReal_re]; exact abs_le.2 ⟨hp.1, hp.2⟩
  have him : |((p : ℂ)).im| ≤ cZero * √‖1 - ξ‖ := by
    rw [Complex.ofReal_im, abs_zero]
    exact mul_nonneg cZero_pos.le (Real.sqrt_nonneg _)
  exact ((differentiableAt_kernelFun u (Dxi_ne_zero hξ hre him)).continuousAt.comp
    Complex.continuous_ofReal.continuousAt).continuousWithinAt

theorem intervalIntegrable_kernelFun (hξ : ‖ξ‖ < 1) (u : ℤ) :
    IntervalIntegrable (fun p : ℝ => kernelFun ξ u p) MeasureTheory.volume (-π) π :=
  (continuousOn_kernelFun hξ u).intervalIntegrable

/-- The pointwise identity behind the lattice equation: `e^{ipw} (1 - ξ Ŝ(p)) / D_ξ(p) = e^{ipw}`
with `Ŝ(p) = (1 + e^{-ip} + e^{ip})/3`. -/
theorem kernelFun_sub_SB {p : ℝ} (hD : Dxi ξ p ≠ 0) (w : ℤ) :
    kernelFun ξ w p - ξ * ((kernelFun ξ w p + kernelFun ξ (w - 1) p + kernelFun ξ (w + 1) p) / 3)
      = Complex.exp (Complex.I * p * w) := by
  have em : Complex.exp (Complex.I * p * ((w - 1 : ℤ) : ℂ))
      = Complex.exp (Complex.I * p * w) * Complex.exp (-(p * Complex.I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have ep : Complex.exp (Complex.I * p * ((w + 1 : ℤ) : ℂ))
      = Complex.exp (Complex.I * p * w) * Complex.exp (p * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hcos : 2 * Complex.cos p = Complex.exp (p * Complex.I) + Complex.exp (-(p * Complex.I)) := by
    rw [Complex.two_cos, neg_mul]
  unfold kernelFun
  rw [em, ep]
  have hD' : Dxi ξ p = 1 - ξ * ((1 + Complex.exp (p * Complex.I)
      + Complex.exp (-(p * Complex.I))) / 3) := by
    unfold Dxi; linear_combination (-(ξ / 3)) * hcos
  field_simp
  rw [hD']
  ring_nf

/-- **The lattice equation**: `K_{ξ,∞}(w) - ξ (K(w) + K(w-1) + K(w+1))/3 = δ_{w,0}`. -/
theorem Kinf_sub_SB (hξ : ‖ξ‖ < 1) (w : ℤ) :
    Kinf ξ w - ξ * ((Kinf ξ w + Kinf ξ (w - 1) + Kinf ξ (w + 1)) / 3)
      = if w = 0 then 1 else 0 := by
  have i0 := intervalIntegrable_kernelFun hξ w
  have i1 := intervalIntegrable_kernelFun hξ (w - 1)
  have i2 := intervalIntegrable_kernelFun hξ (w + 1)
  have hcomb : Kinf ξ w - ξ * ((Kinf ξ w + Kinf ξ (w - 1) + Kinf ξ (w + 1)) / 3)
      = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ p : ℝ in (-π)..π,
          (kernelFun ξ w p - ξ * ((kernelFun ξ w p + kernelFun ξ (w - 1) p
            + kernelFun ξ (w + 1) p) / 3)) := by
    rw [intervalIntegral.integral_sub i0 (((i0.add i1).add i2).div_const 3 |>.const_mul ξ),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_add (i0.add i1) i2, intervalIntegral.integral_add i0 i1]
    simp only [Kinf]
    ring
  rw [hcomb]
  have hpt : ∀ p ∈ Set.uIcc (-π) π, (kernelFun ξ w p - ξ * ((kernelFun ξ w p
      + kernelFun ξ (w - 1) p + kernelFun ξ (w + 1) p) / 3)) = Complex.exp (Complex.I * p * w) := by
    intro p hp
    rw [Set.uIcc_of_le (by linarith [pi_pos])] at hp
    have hre : |((p : ℂ)).re| ≤ π := by
      rw [Complex.ofReal_re]; exact abs_le.2 ⟨hp.1, hp.2⟩
    have him : |((p : ℂ)).im| ≤ cZero * √‖1 - ξ‖ := by
      rw [Complex.ofReal_im, abs_zero]
      exact mul_nonneg cZero_pos.le (Real.sqrt_nonneg _)
    exact kernelFun_sub_SB (Dxi_ne_zero hξ hre him) w
  rw [intervalIntegral.integral_congr hpt, integral_exp_int]
  have h2π : ((2 * π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  split_ifs
  · exact inv_mul_cancel₀ h2π
  · rw [mul_zero]

end Lattice

section Summable

/-- `∑_{n ∈ ℤ} e^{-a|n|} < ∞` for `a > 0`. -/
theorem summable_exp_neg_abs_int {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => exp (-(a * |(n : ℝ)|))) := by
  have hg : Summable (fun n : ℕ => exp (-a) ^ n) :=
    summable_geometric_of_lt_one (exp_pos _).le (exp_lt_one_iff.2 (by linarith))
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hg.congr fun n => ?_
    simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [← exp_nat_mul]; ring_nf
  · refine hg.congr fun n => ?_
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [← exp_nat_mul]; ring_nf

variable {ξ : ℂ}

/-- By (B.5), the periodization `∑_n K_{ξ,∞}(v + nL)` converges absolutely. -/
theorem summable_Kinf_shift (hξ : ‖ξ‖ < 1) (L : ℕ) [NeZero L] (v : ℤ) :
    Summable (fun n : ℤ => Kinf ξ (v + n * L)) := by
  set κ := √‖1 - ξ‖
  have hκ : 0 < κ := sqrt_norm_one_sub_pos hξ
  set a := cZero * κ
  have ha : 0 < a := mul_pos cZero_pos hκ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  refine Summable.of_norm_bounded
    ((summable_exp_neg_abs_int ha).mul_left (6 * π ^ 2 / κ * exp (a * |(v : ℝ)|))) fun n => ?_
  have hK := norm_Kinf_le hξ ((v : ℤ) + n * L)
  -- `|n| ≤ |v + nL| + |v|`
  have hn : |(n : ℝ)| ≤ |(((v + n * L : ℤ)) : ℝ)| + |(v : ℝ)| := by
    push_cast
    have h1 : |(n : ℝ)| ≤ |(n : ℝ)| * L := le_mul_of_one_le_right (abs_nonneg _) hL1
    have h2 : |(n : ℝ)| * L = |((v : ℝ) + n * L) + -v| := by
      rw [add_neg_cancel_comm, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < L)]
    have h3 := abs_add_le ((v : ℝ) + n * L) (-(v : ℝ))
    rw [abs_neg] at h3
    linarith
  have hexp : exp (-(cZero * κ * |(((v + n * L : ℤ)) : ℝ)|))
      ≤ exp (a * |(v : ℝ)|) * exp (-(a * |(n : ℝ)|)) := by
    rw [← exp_add]
    apply exp_le_exp.2
    have : a * |(n : ℝ)| ≤ a * (|(((v + n * L : ℤ)) : ℝ)| + |(v : ℝ)|) :=
      mul_le_mul_of_nonneg_left hn ha.le
    simp only [a] at this ⊢
    linarith
  calc ‖Kinf ξ (v + n * L)‖
      ≤ 6 * π ^ 2 / κ * exp (-(cZero * κ * |(((v + n * L : ℤ)) : ℝ)|)) := hK
    _ ≤ 6 * π ^ 2 / κ * (exp (a * |(v : ℝ)|) * exp (-(a * |(n : ℝ)|))) := by gcongr
    _ = 6 * π ^ 2 / κ * exp (a * |(v : ℝ)|) * exp (-(a * |(n : ℝ)|)) := by ring

end Summable

section Periodize

variable {ξ : ℂ} (L : ℕ) [NeZero L]

/-- The periodized kernel `∑_{n ∈ ℤ} K_{ξ,∞}(v + nL)`. -/
noncomputable def perSum (ξ : ℂ) (v : ℤ) : ℂ := ∑' n : ℤ, Kinf ξ (v + n * L)

omit [NeZero L] in
theorem perSum_add_mul (ξ : ℂ) (v k : ℤ) : perSum L ξ (v + k * L) = perSum L ξ v := by
  unfold perSum
  rw [← (Equiv.addRight k).tsum_eq (fun n : ℤ => Kinf ξ (v + n * L))]
  congr 1
  funext n
  simp only [Equiv.coe_addRight]
  congr 1
  ring

/-- `∑_n δ_{v + nL, 0} = δ_{v,0}` for `0 ≤ v < L`. -/
theorem tsum_ite_add_mul_eq_zero {v : ℤ} (hv0 : 0 ≤ v) (hvL : v < L) :
    (∑' n : ℤ, if v + n * L = 0 then (1 : ℂ) else 0) = if v = 0 then 1 else 0 := by
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have key : ∀ n : ℤ, v + n * L = 0 ↔ n = 0 ∧ v = 0 := by
    intro n
    constructor
    · intro h
      have hdvd : (L : ℤ) ∣ v := ⟨-n, by linarith⟩
      have hv : v = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt hv0 hvL hdvd
      subst hv
      refine ⟨?_, rfl⟩
      have h' : n = 0 ∨ L = 0 := by simpa using h
      rcases h' with h' | h'
      · exact h'
      · exact absurd h' (NeZero.ne L)
    · rintro ⟨rfl, rfl⟩; simp
  split_ifs with hv
  · subst hv
    simp_rw [key, and_true]
    exact tsum_ite_eq (0 : ℤ) (fun _ => (1 : ℂ))
  · simp_rw [key, hv, and_false, ite_false]
    exact tsum_zero

/-- The periodized kernel solves `P - ξ S P = δ` on `ℤ`, with `δ` supported on `Lℤ`. -/
theorem perSum_sub_SB (hξ : ‖ξ‖ < 1) (v : ℤ) :
    perSum L ξ v - ξ * ((perSum L ξ v + perSum L ξ (v - 1) + perSum L ξ (v + 1)) / 3)
      = ∑' n : ℤ, if v + n * L = 0 then (1 : ℂ) else 0 := by
  have s0 := summable_Kinf_shift hξ L v
  have s1 := summable_Kinf_shift hξ L (v - 1)
  have s2 := summable_Kinf_shift hξ L (v + 1)
  have e : ∀ n : ℤ, (if v + n * L = 0 then (1 : ℂ) else 0)
      = Kinf ξ (v + n * L) - ξ / 3 * (Kinf ξ (v + n * L) + Kinf ξ (v - 1 + n * L)
          + Kinf ξ (v + 1 + n * L)) := by
    intro n
    rw [← Kinf_sub_SB hξ (v + n * L)]
    have a1 : v - 1 + n * L = v + n * L - 1 := by ring
    have a2 : v + 1 + n * L = v + n * L + 1 := by ring
    rw [a1, a2]; ring
  simp_rw [e]
  rw [Summable.tsum_sub s0 (((s0.add s1).add s2).mul_left _), Summable.tsum_mul_left _ ((s0.add s1).add s2),
    Summable.tsum_add (s0.add s1) s2, Summable.tsum_add s0 s1]
  simp only [perSum]
  ring

/-- The periodized kernel on `ℤ_L`. -/
noncomputable def perK (ξ : ℂ) (u : ZMod L) : ℂ := perSum L ξ (u.val : ℤ)

omit [NeZero L] in
theorem intCast_val (x : ZMod L) [NeZero L] : (((x.val : ℕ) : ℤ) : ZMod L) = x := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- `perK` may be evaluated at any integer representative. -/
theorem perK_eq (ξ : ℂ) (x : ZMod L) (v : ℤ) (h : (v : ZMod L) = x) :
    perK L ξ x = perSum L ξ v := by
  have h' : ((x.val : ℤ) : ZMod L) = (v : ZMod L) := by rw [intCast_val, h]
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h'
  have hv : v = (x.val : ℤ) + k * L := by linarith
  rw [perK, hv, perSum_add_mul]

/-- The periodized kernel solves `K - ξ S^(B) K = δ₀` on `ℤ_L`. -/
theorem perK_sub_SB_mulVec (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1) (u : ZMod L) :
    perK L ξ u - ξ * (SB L *ᵥ perK L ξ) u = if u = 0 then 1 else 0 := by
  rw [SB_mulVec_apply L hL]
  have hm : perK L ξ (u - 1) = perSum L ξ ((u.val : ℤ) - 1) :=
    perK_eq L ξ _ _ (by push_cast; rw [ZMod.natCast_zmod_val])
  have hp : perK L ξ (u + 1) = perSum L ξ ((u.val : ℤ) + 1) :=
    perK_eq L ξ _ _ (by push_cast; rw [ZMod.natCast_zmod_val])
  rw [hm, hp, perK, perSum_sub_SB L hξ,
    tsum_ite_add_mul_eq_zero L (Nat.cast_nonneg _) (by exact_mod_cast ZMod.val_lt u)]
  simp only [Nat.cast_eq_zero, ZMod.val_eq_zero]

/-- `Θ_ξ` is the circulant matrix generated by the periodized infinite-volume kernel. -/
theorem Theta_eq_circulant_perK (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1) :
    Theta L ξ = circulant (perK L ξ) := by
  refine (eq_Theta_of_mul L hL hξ ?_).symm
  have hmul : circulant (perK L ξ) * SB L = circulant (SB L *ᵥ perK L ξ) := by
    rw [SB, circulant_mul_comm, circulant_mul]
  rw [mul_sub, mul_one, Matrix.mul_smul, hmul, ← circulant_smul, ← circulant_sub,
    ← circulant_single_one ℂ (ZMod L), circulant_inj]
  funext u
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  exact perK_sub_SB_mulVec L hL hξ u

/-- **The identity after (B.2)**: `(Θ_ξ)_{xy} = ∑_{n ∈ ℤ} K_{ξ,∞}(u + nL)`, `u = x - y`
(any integer representative of `x - y` may be used, by `RBM.perK_eq`). -/
theorem Theta_apply_periodize (hL : 3 ≤ L) (hξ : ‖ξ‖ < 1) (x y : ZMod L) :
    Theta L ξ x y = ∑' n : ℤ, Kinf ξ (((x - y).val : ℤ) + n * L) := by
  rw [Theta_eq_circulant_perK L hL hξ, circulant_apply, perK, perSum]

end Periodize

end RBM
