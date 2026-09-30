/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.SumZero
import RBM1D.Hierarchy.KernelDecay
import RBM1D.Hierarchy.Step3
import RBM1D.Loop.WardKgen
import RBM1D.Loop.SumZero
import RBM1D.Propagator.Deriv
import RBM1D.Loop.Continuity

/-!
# §5.5, the dynamical half: the estimates behind Lemma 5.14 (5.92)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, §5.4–5.5, equations (5.84)–(5.107): the estimates behind the bound (5.92) on
`Ξ^{(L-K)}_{u,n}` along the flow, for every loop length `n ≥ 2`, which Step 3 and Steps 4–5
use in the form `RBM.Step3.Lemma514`.

The static half of §5.5 (the operator `Q_t`, `P`, `ϑ_t`, (5.89)–(5.90)) is
`RBM1D/Hierarchy/SumZero.lean`; the kernel bounds (7.16) for `U_{s,t,σ}` are
`RBM1D/Hierarchy/KernelDecay.lean`.  This file adds the time derivative of `Q_t` and the
dynamical estimates.

## Main results

* `RBM.SumZeroDyn.varthetaDot`, `hasDerivAt_vartheta`, `fastDecay_varthetaDot`:
  `ϑ̇_t` and its decay.
* `RBM.SumZeroDyn.genS`, `commS`, `commOp_eq`: the generator `Θ_{t,σ}` of (5.19) and the
  commutator `[Q_t, Θ_{t,σ}]` of **(5.99)**; `SumZero_commS`: it is sum-zero.
* `RBM.SumZeroDyn.norm_Psum_le_of_ward`: **(5.96)** in abstract form.
* `RBM.SumZeroDyn.sum_gloop_ward_mid`, `sum_gloop_ward_last`, `sum_Kgen_ward_mid`: Ward's
  identity (Lemma 3.6) for the slot sums of `L` and of `K`, the input of (5.96).
* `RBM.SumZeroDyn.fastDecay_Qop`, `norm_Qop_le_of_fastDecay`: **Lemma 5.13 (5.87)** in the
  form used, decay and size.

## Deviations from the paper

* The generator is `ξ Θ_{tξ} S^{(B)}` (`genS`), with the `S^{(B)}` of (5.16) and (5.19).
  `RBM.ThetaOp` carries it too, so `genS L ξ t` and
  `RBM.ThetaOp L ξ t` are definitionally equal; `genS` remains as the instance
  `Mᵢ = ξᵢ Θ^(B)_{tξᵢ} S^(B)` of the general slot-wise generator `genOp`, which is what the
  `Q_t` estimates below are actually stated for.
* Charges `σ` with no `(-,+)` pair away from slot `0` are handled as the paper handles them:
  non-alternating ones via Case 1 of (7.16) ((5.84)); the only remaining one, `σ = (-,+)`,
  by rotating the `2`-loop.
* The maxima on the right of (5.77) are replaced by sums; this is weaker than the
  paper's statement only by a constant factor.
* Scales: `η_u = etaT E u`, `ℓ_u = ellHat`, `Wℓ_uη_u = B.scale E N u`.
* The conclusion is `Λ^{1/2} + Φ` as in `RBM.Step3.Lemma514`; the extra `N^τ (1 + log N)`
  losses are absorbed by `≺`, and a `(1 + Φ)` factor by `Λ ≥ 1`.
* The BDG hypotheses require the integrand bound uniformly in `s ≤ u ≤ v ≤ t` (not only for
  each fixed `v`).
-/

namespace RBM

namespace SumZeroDyn

open Finset Real
open scoped Matrix.Norms.Operator

section Tensor
variable (L : ℕ) [NeZero L]

theorem sum_loopArg_succ {n : ℕ} (f : LoopArg L (n + 1) → ℂ) :
    ∑ b : LoopArg L (n + 1), f b = ∑ x : ZMod L, ∑ r : LoopArg L n, f (Fin.cons x r) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod L)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sumZeroAt_zero_of_sumZero {n : ℕ} {A : LoopArg L (n + 1) → ℂ} (h : SumZero L A) :
    SumZeroAt L 0 A := by
  intro x
  rw [sum_loopArg_succ]
  simp only [Fin.cons_zero]
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [hy]) (by simp)]
  simpa [Psum] using h x

/-- The window-sum bound: a `(R, δ)`-fast-decaying tensor bounded by `M` has slot sums
`|P A| ≤ (2e(R+1))^n M + L^n δ`. -/
theorem norm_Psum_le_of_fastDecay {n : ℕ} {R M δ : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    {A : LoopArg L (n + 1) → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M) (hA : FastDecay L R δ A) (x : ZMod L) :
    ‖Psum L A x‖ ≤ (2 * exp 1 * (R + 1)) ^ n * M + (L : ℝ) ^ n * δ := by
  have hpt : ∀ r : LoopArg L n, ‖A (Fin.cons x r)‖ ≤ M * ∏ i, winInd L R (r i - x) + δ := by
    intro r
    by_cases hall : ∀ i, (zdist L (r i - x) : ℝ) < R
    · have : ∏ i, winInd L R (r i - x) = 1 := by
        refine Finset.prod_eq_one fun i _ => ?_
        simp [winInd, hall i]
      rw [this, mul_one]
      linarith [hAM (Fin.cons x r)]
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      have h1 : ‖A (Fin.cons x r)‖ ≤ δ := hA _ ⟨i.succ, 0, by simpa using hi⟩
      have h2 : 0 ≤ M * ∏ i, winInd L R (r i - x) :=
        mul_nonneg hM (Finset.prod_nonneg fun j _ => winInd_nonneg L R _)
      linarith
  calc ‖Psum L A x‖ ≤ ∑ r : LoopArg L n, ‖A (Fin.cons x r)‖ := norm_sum_le _ _
    _ ≤ ∑ r : LoopArg L n, (M * ∏ i, winInd L R (r i - x) + δ) := Finset.sum_le_sum fun r _ => hpt r
    _ = M * ∑ r : LoopArg L n, ∏ i, winInd L R (r i - x) + (L : ℝ) ^ n * δ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
    _ ≤ M * (2 * exp 1 * (R + 1)) ^ n + (L : ℝ) ^ n * δ := by
        gcongr
        rw [sum_prod_pi L (fun _ c => winInd L R (c - x))]
        calc ∏ _i : Fin n, ∑ c : ZMod L, winInd L R (c - x)
            ≤ ∏ _i : Fin n, 2 * exp 1 * (R + 1) :=
              Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => winInd_nonneg L R _)
                (fun i _ => sum_winInd_le L hR x)
          _ = (2 * exp 1 * (R + 1)) ^ n := by simp
    _ = _ := by ring

end Tensor

section Vartheta
variable (L : ℕ) [NeZero L]

theorem norm_ofReal_lt_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : ‖(t : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1

theorem ellHat_real_pos' (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < ellHat L (t : ℂ) :=
  lt_of_lt_of_le (by norm_num) (half_le_ellHat_real L hL ht0 ht1)

/-- (2.52) at a real time `t ∈ [0,1)`, with the exponential factor. -/
theorem norm_Theta_real_le_exp (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (x y : ZMod L) :
    ‖Theta L (t : ℂ) x y‖ ≤ cTwo52 * exp (-(cZero * zdist L (x - y) / ellHat L (t : ℂ)))
      / ((1 - t) * ellHat L (t : ℂ)) := by
  have h := norm_Theta_apply_le_complex hL (norm_ofReal_lt_one ht0 ht1) x y
  rwa [norm_one_sub_ofReal ht1.le] at h

/-- (2.52) at distance `≥ R`. -/
theorem norm_Theta_real_le_of_far (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {x y : ZMod L} {R : ℝ} (hR : R ≤ zdist L (x - y)) :
    ‖Theta L (t : ℂ) x y‖ ≤ cTwo52 / ((1 - t) * ellHat L (t : ℂ))
      * exp (-(cZero * R / ellHat L (t : ℂ))) := by
  have hℓ := ellHat_real_pos' L hL ht0 ht1
  have h1t : 0 < 1 - t := by linarith
  refine (norm_Theta_real_le_exp L hL ht0 ht1 x y).trans ?_
  rw [div_mul_eq_mul_div, mul_comm (cTwo52 : ℝ) _, mul_comm cTwo52 (exp _)]
  gcongr
  · exact cTwo52_pos.le
  · exact cZero_pos.le

/-- (2.52) at a real time, without the exponential. -/
theorem norm_Theta_real_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (x y : ZMod L) :
    ‖Theta L (t : ℂ) x y‖ ≤ cTwo52 / ((1 - t) * ellHat L (t : ℂ)) := by
  have h := norm_Theta_real_le_of_far L hL ht0 ht1 (x := x) (y := y) (R := 0) (by positivity)
  simpa using h

/-- A pair of indices at distance `≥ R` forces one index at distance `≥ R/2` from `a 0`. -/
theorem exists_far_zero {n : ℕ} {R : ℝ} (hR : 0 < R) {a : LoopArg L (n + 1)}
    (h : ∃ i j, R ≤ (zdist L (a i - a j) : ℝ)) :
    ∃ k : Fin n, R / 2 ≤ (zdist L (a 0 - a k.succ) : ℝ) := by
  obtain ⟨i, j, hij⟩ := h
  have htri : (zdist L (a i - a j) : ℝ) ≤ zdist L (a 0 - a i) + zdist L (a 0 - a j) := by
    have h1 := zdist_add_le L (a i - a 0) (a 0 - a j)
    have e : a i - a 0 + (a 0 - a j) = a i - a j := by ring
    rw [e] at h1
    have h2 : zdist L (a i - a 0) = zdist L (a 0 - a i) := by
      rw [← zdist_neg L (a i - a 0), neg_sub]
    rw [h2] at h1
    exact_mod_cast h1
  have key : ∀ k : Fin (n + 1), R / 2 ≤ (zdist L (a 0 - a k) : ℝ) →
      ∃ k' : Fin n, R / 2 ≤ (zdist L (a 0 - a k'.succ) : ℝ) := by
    intro k hk
    induction k using Fin.cases with
    | zero => simp at hk; linarith
    | succ k' => exact ⟨k', hk⟩
  by_cases hi : R / 2 ≤ (zdist L (a 0 - a i) : ℝ)
  · exact key i hi
  · exact key j (by push Not at hi; linarith)

/-- `|ϑ_{t,a}| ≤ (C/ℓ_t)^n`. -/
theorem norm_vartheta_real_le (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : LoopArg L (n + 1)) :
    ‖vartheta L (t : ℂ) a‖ ≤ (cTwo52 / ellHat L (t : ℂ)) ^ n := by
  have hℓ := ellHat_real_pos' L hL ht0 ht1
  have h1t : 0 < 1 - t := by linarith
  rw [vartheta, norm_mul, norm_pow, norm_one_sub_ofReal ht1.le, norm_prod]
  calc (1 - t) ^ n * ∏ i : Fin n, ‖Theta L (t : ℂ) (a 0) (a i.succ)‖
      ≤ (1 - t) ^ n * ∏ _i : Fin n, cTwo52 / ((1 - t) * ellHat L (t : ℂ)) := by
        gcongr with i
        exact norm_Theta_real_le L hL ht0 ht1 _ _
    _ = (cTwo52 / ellHat L (t : ℂ)) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow]
        congr 1
        field_simp

/-- `ϑ_{t,a}` is small if some index is far from `a 0`. -/
theorem norm_vartheta_real_le_of_far (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {a : LoopArg L (n + 1)} {R : ℝ} (k : Fin n) (hk : R ≤ zdist L (a 0 - a k.succ)) :
    ‖vartheta L (t : ℂ) a‖ ≤ (cTwo52 / ellHat L (t : ℂ)) ^ n
      * exp (-(cZero * R / ellHat L (t : ℂ))) := by
  classical
  have hℓ := ellHat_real_pos' L hL ht0 ht1
  have h1t : 0 < 1 - t := by linarith
  set c := cTwo52 / ((1 - t) * ellHat L (t : ℂ)) with hc
  set e := exp (-(cZero * R / ellHat L (t : ℂ))) with he
  have hc0 : 0 ≤ c := div_nonneg cTwo52_pos.le (by positivity)
  have he0 : 0 ≤ e := (exp_pos _).le
  rw [vartheta, norm_mul, norm_pow, norm_one_sub_ofReal ht1.le, norm_prod]
  have hfac : ∀ i : Fin n, ‖Theta L (t : ℂ) (a 0) (a i.succ)‖ ≤ c * (if i = k then e else 1) := by
    intro i
    split_ifs with hik
    · subst hik; exact norm_Theta_real_le_of_far L hL ht0 ht1 hk
    · rw [mul_one]; exact norm_Theta_real_le L hL ht0 ht1 _ _
  calc (1 - t) ^ n * ∏ i : Fin n, ‖Theta L (t : ℂ) (a 0) (a i.succ)‖
      ≤ (1 - t) ^ n * ∏ i : Fin n, c * (if i = k then e else 1) := by
        gcongr with i
        exact hfac i
    _ = (cTwo52 / ellHat L (t : ℂ)) ^ n * e := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k (fun _ => e)]
        simp only [Finset.mem_univ, ite_true, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        rw [← mul_assoc, ← mul_pow, hc]
        congr 2
        field_simp

/-- `ϑ_t` is fast-decaying: it is `(C/ℓ_t)^n e^{-c₀R/(2ℓ_t)}` as soon as two indices are
`R` apart. -/
theorem fastDecay_vartheta (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {R : ℝ} (hR : 0 < R) :
    FastDecay L R ((cTwo52 / ellHat L (t : ℂ)) ^ n * exp (-(cZero * (R / 2) / ellHat L (t : ℂ))))
      (vartheta L (n := n) (t : ℂ)) := by
  intro a ha
  obtain ⟨k, hk⟩ := exists_far_zero L hR ha
  exact norm_vartheta_real_le_of_far L hL ht0 ht1 k hk

end Vartheta

section VarthetaDot
variable (L : ℕ) [NeZero L]

theorem hasDerivAt_Theta_real (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (x y : ZMod L) :
    HasDerivAt (fun u : ℝ => Theta L (u : ℂ) x y)
      ((Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) x y) t :=
  (hasDerivAt_Theta_apply L hL (norm_ofReal_lt_one ht0 ht1) x y).comp_ofReal

/-- `∂_t ϑ_{t,a}`: the time derivative of the reference tensor of Definition 5.12. -/
noncomputable def varthetaDot {n : ℕ} (t : ℝ) (a : LoopArg L (n + 1)) : ℂ :=
  (-(n : ℂ) * (1 - (t : ℂ)) ^ (n - 1)) * ∏ i : Fin n, Theta L (t : ℂ) (a 0) (a i.succ)
    + (1 - (t : ℂ)) ^ n * ∑ i : Fin n, (∏ j ∈ univ.erase i, Theta L (t : ℂ) (a 0) (a j.succ))
        * (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a i.succ)

theorem hasDerivAt_vartheta (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : LoopArg L (n + 1)) :
    HasDerivAt (fun u : ℝ => vartheta L (u : ℂ) a) (varthetaDot L t a) t := by
  have h1 : HasDerivAt (fun u : ℝ => (1 - (u : ℂ)) ^ n)
      ((n : ℂ) * (1 - (t : ℂ)) ^ (n - 1) * (-1)) t := by
    have hid : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    exact (hid.const_sub 1).pow n |>.congr_deriv (by ring)
  have h2 : HasDerivAt (fun u : ℝ => ∏ i : Fin n, Theta L (u : ℂ) (a 0) (a i.succ))
      (∑ i : Fin n, (∏ j ∈ univ.erase i, Theta L (t : ℂ) (a 0) (a j.succ))
        • (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a i.succ)) t :=
    HasDerivAt.fun_finsetProd fun i _ => hasDerivAt_Theta_real L hL ht0 ht1 _ _
  have h3 := h1.mul h2
  refine h3.congr_deriv ?_
  simp only [varthetaDot, smul_eq_mul]
  ring

/-- `P ∘ ϑ̇_t = 0`: differentiate `P ∘ ϑ_t = 1`. -/
theorem Psum_varthetaDot (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (x : ZMod L) : Psum L (varthetaDot L (n := n) t) x = 0 := by
  have hd : HasDerivAt (fun u : ℝ => Psum L (vartheta L (n := n) (u : ℂ)) x)
      (Psum L (varthetaDot L (n := n) t) x) t := by
    simp only [Psum]
    exact HasDerivAt.fun_sum fun r _ => hasDerivAt_vartheta L hL ht0 ht1 _
  have hev : (fun u : ℝ => Psum L (vartheta L (n := n) (u : ℂ)) x) =ᶠ[nhds t] fun _ => 1 := by
    have hopen : Set.Ioo (-1 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds (by linarith) ht1
    filter_upwards [hopen] with u hu
    have hu' : ‖(u : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; exact ⟨hu.1, hu.2⟩
    exact Psum_vartheta L hL hu' x
  have h2 : HasDerivAt (fun _ : ℝ => (1 : ℂ)) (Psum L (varthetaDot L (n := n) t) x) t :=
    hd.congr_of_eventuallyEq hev.symm
  exact h2.unique (hasDerivAt_const t 1)

theorem sum_norm_ThetaSB_row_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (x : ZMod L) :
    ∑ c : ZMod L, ‖(Theta L (t : ℂ) * SB L) x c‖ ≤ (1 - t)⁻¹ := by
  have hn := norm_ofReal_lt_one ht0 ht1
  refine (sum_norm_row_le L _ x).trans ?_
  calc ‖Theta L (t : ℂ) * SB L‖ ≤ ‖Theta L (t : ℂ)‖ * ‖SB L‖ := norm_mul_le _ _
    _ = ‖Theta L (t : ℂ)‖ := by rw [norm_SB L hL, mul_one]
    _ ≤ (1 - ‖(t : ℂ)‖)⁻¹ := norm_Theta_le L hL hn
    _ = (1 - t)⁻¹ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]

theorem sum_norm_Theta_col_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (y : ZMod L) :
    ∑ c : ZMod L, ‖Theta L (t : ℂ) c y‖ ≤ (1 - t)⁻¹ := by
  have hn := norm_ofReal_lt_one ht0 ht1
  have hsym : ∀ c, Theta L (t : ℂ) c y = Theta L (t : ℂ) y c := fun c => by
    have h := congrFun (congrFun (Theta_transpose L hL hn) y) c
    simpa [Matrix.transpose_apply] using h
  simp_rw [hsym]
  refine (sum_norm_Theta_row_le L hL hn y).trans (le_of_eq ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]

theorem sum_norm_SB_col (hL : 3 ≤ L) (c : ZMod L) : ∑ d : ZMod L, ‖SB L d c‖ = 1 := by
  simp_rw [fun d => SB_apply_comm L d c]
  exact sum_norm_SB_apply_row L hL c

theorem norm_TST_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (x y : ZMod L) :
    ‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) x y‖
      ≤ (1 - t)⁻¹ * (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) := by
  rw [Matrix.mul_apply]
  calc ‖∑ c, (Theta L (t : ℂ) * SB L) x c * Theta L (t : ℂ) c y‖
      ≤ ∑ c, ‖(Theta L (t : ℂ) * SB L) x c‖ * (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_Theta_real_le L hL ht0 ht1 _ _) (norm_nonneg _)
    _ ≤ _ := by
        rw [← Finset.sum_mul]
        have hc : 0 ≤ cTwo52 / ((1 - t) * ellHat L (t : ℂ)) := by
          have := ellHat_real_pos' L hL ht0 ht1
          have := cTwo52_pos
          have : 0 < 1 - t := by linarith
          positivity
        exact mul_le_mul_of_nonneg_right (sum_norm_ThetaSB_row_le L hL ht0 ht1 x) hc

theorem norm_ThetaSB_le_of_far (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {x c : ZMod L} {R : ℝ} (hR : R + 1 ≤ zdist L (x - c)) :
    ‖(Theta L (t : ℂ) * SB L) x c‖
      ≤ cTwo52 / ((1 - t) * ellHat L (t : ℂ)) * exp (-(cZero * R / ellHat L (t : ℂ))) := by
  set ε := cTwo52 / ((1 - t) * ellHat L (t : ℂ)) * exp (-(cZero * R / ellHat L (t : ℂ)))
  have hterm : ∀ d, ‖Theta L (t : ℂ) x d * SB L d c‖ ≤ ε * ‖SB L d c‖ := by
    intro d
    rw [norm_mul]
    by_cases hd : 1 < zdist L (d - c)
    · rw [SB_apply_eq_zero L hL hd, norm_zero, mul_zero, mul_zero]
    · push Not at hd
      refine mul_le_mul_of_nonneg_right (norm_Theta_real_le_of_far L hL ht0 ht1 ?_) (norm_nonneg _)
      have h1 := zdist_add_le L (x - d) (d - c)
      have e : x - d + (d - c) = x - c := by ring
      rw [e] at h1
      have : (zdist L (x - c) : ℝ) ≤ zdist L (x - d) + zdist L (d - c) := by exact_mod_cast h1
      have : (zdist L (d - c) : ℝ) ≤ 1 := by exact_mod_cast hd
      linarith
  rw [Matrix.mul_apply]
  calc ‖∑ d, Theta L (t : ℂ) x d * SB L d c‖ ≤ ∑ d, ε * ‖SB L d c‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => hterm d)
    _ = ε := by rw [← Finset.mul_sum, sum_norm_SB_col L hL c, mul_one]

theorem norm_TST_le_of_far (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {x y : ZMod L} {R : ℝ} (hR : 2 * R + 1 ≤ zdist L (x - y)) :
    ‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) x y‖
      ≤ 2 * (1 - t)⁻¹ * (cTwo52 / ((1 - t) * ellHat L (t : ℂ))
        * exp (-(cZero * R / ellHat L (t : ℂ)))) := by
  set ε := cTwo52 / ((1 - t) * ellHat L (t : ℂ)) * exp (-(cZero * R / ellHat L (t : ℂ)))
  have hε : 0 ≤ ε := by
    have := ellHat_real_pos' L hL ht0 ht1
    have := cTwo52_pos
    have : 0 < 1 - t := by linarith
    positivity
  have hterm : ∀ c, ‖(Theta L (t : ℂ) * SB L) x c * Theta L (t : ℂ) c y‖
      ≤ ‖(Theta L (t : ℂ) * SB L) x c‖ * ε + ε * ‖Theta L (t : ℂ) c y‖ := by
    intro c
    rw [norm_mul]
    by_cases hc : R ≤ (zdist L (c - y) : ℝ)
    · have := norm_Theta_real_le_of_far L hL ht0 ht1 hc
      have := mul_nonneg hε (norm_nonneg (Theta L (t : ℂ) c y))
      nlinarith [norm_nonneg ((Theta L (t : ℂ) * SB L) x c)]
    · push Not at hc
      have h1 := zdist_add_le L (x - c) (c - y)
      have e : x - c + (c - y) = x - y := by ring
      rw [e] at h1
      have h1' : (zdist L (x - y) : ℝ) ≤ zdist L (x - c) + zdist L (c - y) := by exact_mod_cast h1
      have := norm_ThetaSB_le_of_far L hL ht0 ht1 (x := x) (c := c) (R := R) (by linarith)
      have := mul_nonneg (norm_nonneg ((Theta L (t : ℂ) * SB L) x c)) hε
      nlinarith [norm_nonneg (Theta L (t : ℂ) c y)]
  rw [Matrix.mul_apply]
  calc ‖∑ c, (Theta L (t : ℂ) * SB L) x c * Theta L (t : ℂ) c y‖
      ≤ ∑ c, (‖(Theta L (t : ℂ) * SB L) x c‖ * ε + ε * ‖Theta L (t : ℂ) c y‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hterm c)
    _ = (∑ c, ‖(Theta L (t : ℂ) * SB L) x c‖) * ε + ε * ∑ c, ‖Theta L (t : ℂ) c y‖ := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ ≤ (1 - t)⁻¹ * ε + ε * (1 - t)⁻¹ := by
        gcongr
        · exact sum_norm_ThetaSB_row_le L hL ht0 ht1 x
        · exact sum_norm_Theta_col_le L hL ht0 ht1 y
    _ = _ := by ring

end VarthetaDot

section VD
variable (L : ℕ) [NeZero L]

/-- Products of `Θ`-entries: `∏_{j ∈ s} |Θ_{a₁ a_j}| ≤ C^{|s|}`, and `≤ C^{|s|} e` if one of
the factors is far. -/
theorem prod_norm_Theta_le (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : LoopArg L (n + 1)) (s : Finset (Fin n)) :
    ∏ j ∈ s, ‖Theta L (t : ℂ) (a 0) (a j.succ)‖
      ≤ (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) ^ s.card := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun j _ => norm_Theta_real_le L hL ht0 ht1 _ _)

theorem prod_norm_Theta_le_of_far (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {a : LoopArg L (n + 1)} {s : Finset (Fin n)} {k : Fin n} (hk : k ∈ s) {R : ℝ}
    (hR : R ≤ zdist L (a 0 - a k.succ)) :
    ∏ j ∈ s, ‖Theta L (t : ℂ) (a 0) (a j.succ)‖
      ≤ (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) ^ s.card
        * exp (-(cZero * R / ellHat L (t : ℂ))) := by
  have hC : 0 ≤ cTwo52 / ((1 - t) * ellHat L (t : ℂ)) := by
    have := ellHat_real_pos' L hL ht0 ht1
    have := cTwo52_pos
    have : 0 < 1 - t := by linarith
    positivity
  have h1 := norm_Theta_real_le_of_far L hL ht0 ht1 hR
  have h2 := prod_norm_Theta_le L hL ht0 ht1 a (s.erase k)
  rw [← Finset.mul_prod_erase s _ hk]
  calc ‖Theta L (t : ℂ) (a 0) (a k.succ)‖ * ∏ j ∈ s.erase k, ‖Theta L (t : ℂ) (a 0) (a j.succ)‖
      ≤ (cTwo52 / ((1 - t) * ellHat L (t : ℂ)) * exp (-(cZero * R / ellHat L (t : ℂ))))
          * (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) ^ (s.erase k).card :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = _ := by rw [← Finset.card_erase_add_one hk, pow_succ]; ring

/-- `|ϑ̇_{t,a}| ≤ 2n (C/ℓ_t)^n (1-t)^{-1}`. -/
theorem norm_varthetaDot_le (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : LoopArg L (n + 1)) :
    ‖varthetaDot L t a‖ ≤ 2 * n * (cTwo52 / ellHat L (t : ℂ)) ^ n * (1 - t)⁻¹ := by
  have hℓ := ellHat_real_pos' L hL ht0 ht1
  have h1t : 0 < 1 - t := by linarith
  set C := cTwo52 / ((1 - t) * ellHat L (t : ℂ)) with hCdef
  have hC : 0 ≤ C := by have := cTwo52_pos; positivity
  have hn1 : ‖(1 : ℂ) - (t : ℂ)‖ = 1 - t := norm_one_sub_ofReal ht1.le
  rcases n with _ | k
  · simp [varthetaDot]
  · have hcl : (cTwo52 / ellHat L (t : ℂ)) ^ (k + 1) * (1 - t)⁻¹ = (1 - t) ^ k * C ^ (k + 1) := by
      rw [hCdef, div_pow, div_pow, mul_pow]
      field_simp
      ring
    have hA : ‖(-((k + 1 : ℕ) : ℂ) * (1 - (t : ℂ)) ^ (k + 1 - 1))
        * ∏ i : Fin (k + 1), Theta L (t : ℂ) (a 0) (a i.succ)‖ ≤ (k + 1) * ((1 - t) ^ k * C ^ (k + 1)) := by
      rw [norm_mul, norm_mul, norm_neg, norm_pow, hn1, Nat.add_sub_cancel, norm_prod]
      have := prod_norm_Theta_le L hL ht0 ht1 a Finset.univ
      rw [Finset.card_univ, Fintype.card_fin] at this
      simp only [Complex.norm_natCast]
      push_cast
      have : 0 ≤ (1 - t) ^ k := by positivity
      calc ((k : ℝ) + 1) * (1 - t) ^ k * ∏ i : Fin (k + 1), ‖Theta L (t : ℂ) (a 0) (a i.succ)‖
          ≤ ((k : ℝ) + 1) * (1 - t) ^ k * C ^ (k + 1) := by gcongr
        _ = _ := by ring
    have hB : ‖(1 - (t : ℂ)) ^ (k + 1) * ∑ i : Fin (k + 1),
        (∏ j ∈ univ.erase i, Theta L (t : ℂ) (a 0) (a j.succ))
          * (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a i.succ)‖
        ≤ (k + 1) * ((1 - t) ^ k * C ^ (k + 1)) := by
      rw [norm_mul, norm_pow, hn1]
      have hterm : ∀ i : Fin (k + 1), ‖(∏ j ∈ univ.erase i, Theta L (t : ℂ) (a 0) (a j.succ))
          * (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a i.succ)‖ ≤ C ^ k * ((1 - t)⁻¹ * C) := by
        intro i
        rw [norm_mul, norm_prod]
        have h1 := prod_norm_Theta_le L hL ht0 ht1 a (univ.erase i)
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
          Nat.add_sub_cancel] at h1
        exact mul_le_mul h1 (norm_TST_le L hL ht0 ht1 _ _) (norm_nonneg _) (by positivity)
      calc (1 - t) ^ (k + 1) * ‖∑ i : Fin (k + 1), (∏ j ∈ univ.erase i, Theta L (t : ℂ) (a 0) (a j.succ))
            * (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a i.succ)‖
          ≤ (1 - t) ^ (k + 1) * ∑ _i : Fin (k + 1), C ^ k * ((1 - t)⁻¹ * C) := by
            gcongr
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
        _ = (k + 1) * ((1 - t) ^ k * C ^ (k + 1)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            field_simp
            ring
    rw [varthetaDot, mul_assoc (2 * _), hcl]
    refine (norm_add_le _ _).trans ?_
    push_cast at hA hB ⊢
    linarith

/-- `ϑ̇_{t,a}` is small if some index is far from `a 0`. -/
theorem norm_varthetaDot_le_of_far (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {a : LoopArg L (n + 1)} {R : ℝ} (k : Fin n) (hk : 2 * R + 1 ≤ zdist L (a 0 - a k.succ))
    (hR : 0 ≤ R) :
    ‖varthetaDot L t a‖ ≤ 3 * n * (cTwo52 / ellHat L (t : ℂ)) ^ n * (1 - t)⁻¹
      * exp (-(cZero * R / ellHat L (t : ℂ))) := by
  have hℓ := ellHat_real_pos' L hL ht0 ht1
  have h1t : 0 < 1 - t := by linarith
  set C := cTwo52 / ((1 - t) * ellHat L (t : ℂ)) with hCdef
  have hC : 0 ≤ C := by have := cTwo52_pos; positivity
  set e := exp (-(cZero * R / ellHat L (t : ℂ))) with he
  have he0 : 0 ≤ e := (exp_pos _).le
  have hn1 : ‖(1 : ℂ) - (t : ℂ)‖ = 1 - t := norm_one_sub_ofReal ht1.le
  have hk' : R ≤ (zdist L (a 0 - a k.succ) : ℝ) := by linarith
  rcases n with _ | m
  · exact k.elim0
  · have hcl : (cTwo52 / ellHat L (t : ℂ)) ^ (m + 1) * (1 - t)⁻¹ = (1 - t) ^ m * C ^ (m + 1) := by
      rw [hCdef, div_pow, div_pow, mul_pow]
      field_simp
      ring
    have hA : ‖(-((m + 1 : ℕ) : ℂ) * (1 - (t : ℂ)) ^ (m + 1 - 1))
        * ∏ i : Fin (m + 1), Theta L (t : ℂ) (a 0) (a i.succ)‖
          ≤ (m + 1) * ((1 - t) ^ m * C ^ (m + 1)) * e := by
      rw [norm_mul, norm_mul, norm_neg, norm_pow, hn1, Nat.add_sub_cancel, norm_prod]
      have := prod_norm_Theta_le_of_far L hL ht0 ht1 (s := Finset.univ) (Finset.mem_univ k) hk'
      rw [Finset.card_univ, Fintype.card_fin] at this
      simp only [Complex.norm_natCast]
      push_cast
      have : 0 ≤ (1 - t) ^ m := by positivity
      calc ((m : ℝ) + 1) * (1 - t) ^ m * ∏ i : Fin (m + 1), ‖Theta L (t : ℂ) (a 0) (a i.succ)‖
          ≤ ((m : ℝ) + 1) * (1 - t) ^ m * (C ^ (m + 1) * e) := by gcongr
        _ = _ := by ring
    have hB : ‖(1 - (t : ℂ)) ^ (m + 1) * ∑ i : Fin (m + 1),
        (∏ j ∈ univ.erase i, Theta L (t : ℂ) (a 0) (a j.succ))
          * (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a i.succ)‖
        ≤ 2 * (m + 1) * ((1 - t) ^ m * C ^ (m + 1)) * e := by
      rw [norm_mul, norm_pow, hn1]
      have hterm : ∀ i : Fin (m + 1), ‖(∏ j ∈ univ.erase i, Theta L (t : ℂ) (a 0) (a j.succ))
          * (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a i.succ)‖
            ≤ 2 * (C ^ m * ((1 - t)⁻¹ * C)) * e := by
        intro i
        rw [norm_mul, norm_prod]
        have hcard : (univ.erase i).card = m := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
            Nat.add_sub_cancel]
        by_cases hik : i = k
        · subst hik
          have h1 := prod_norm_Theta_le L hL ht0 ht1 a (univ.erase i)
          rw [hcard] at h1
          have h2 := norm_TST_le_of_far L hL ht0 ht1 hk
          calc (∏ j ∈ univ.erase i, ‖Theta L (t : ℂ) (a 0) (a j.succ)‖)
                * ‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a i.succ)‖
              ≤ C ^ m * (2 * (1 - t)⁻¹ * (C * e)) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _ = _ := by ring
        · have hkm : k ∈ univ.erase i := Finset.mem_erase.2 ⟨fun h => hik h.symm, Finset.mem_univ _⟩
          have h1 := prod_norm_Theta_le_of_far L hL ht0 ht1 hkm hk'
          rw [hcard] at h1
          have h2 := norm_TST_le L hL ht0 ht1 (a 0) (a i.succ)
          calc (∏ j ∈ univ.erase i, ‖Theta L (t : ℂ) (a 0) (a j.succ)‖)
                * ‖(Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a i.succ)‖
              ≤ (C ^ m * e) * ((1 - t)⁻¹ * C) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _ ≤ _ := by
                have : 0 ≤ C ^ m * e * ((1 - t)⁻¹ * C) := by positivity
                nlinarith
      calc (1 - t) ^ (m + 1) * ‖∑ i : Fin (m + 1), (∏ j ∈ univ.erase i, Theta L (t : ℂ) (a 0) (a j.succ))
            * (Theta L (t : ℂ) * SB L * Theta L (t : ℂ)) (a 0) (a i.succ)‖
          ≤ (1 - t) ^ (m + 1) * ∑ _i : Fin (m + 1), 2 * (C ^ m * ((1 - t)⁻¹ * C)) * e := by
            gcongr
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
        _ = 2 * (m + 1) * ((1 - t) ^ m * C ^ (m + 1)) * e := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            field_simp
            ring
    rw [varthetaDot]
    refine (norm_add_le _ _).trans ?_
    have : 3 * ((m + 1 : ℕ) : ℝ) * (cTwo52 / ellHat L (t : ℂ)) ^ (m + 1) * (1 - t)⁻¹ * e
        = 3 * (m + 1) * ((1 - t) ^ m * C ^ (m + 1)) * e := by
      rw [← hcl]; push_cast; ring
    rw [this]
    push_cast at hA hB ⊢
    linarith

/-- `ϑ̇_t` is fast-decaying. -/
theorem fastDecay_varthetaDot (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {R : ℝ} (hR : 2 ≤ R) :
    FastDecay L R (3 * n * (cTwo52 / ellHat L (t : ℂ)) ^ n * (1 - t)⁻¹
      * exp (-(cZero * (R / 4 - 1 / 2) / ellHat L (t : ℂ)))) (varthetaDot L (n := n) t) := by
  intro a ha
  obtain ⟨k, hk⟩ := exists_far_zero L (by linarith) ha
  exact norm_varthetaDot_le_of_far L hL ht0 ht1 k (by linarith) (by linarith)

end VD

/-! ### `Q_t`: (5.101), the max-norm bound and the decay of Lemma 5.13 -/

section Qop

variable (L : ℕ) [NeZero L]

/-- The max-norm half of **Lemma 5.13 (5.87)** at a real time, given a bound `P` on the slot
sums: `|Q_t ∘ A| ≤ M + P (C/ℓ_t)^n`. -/
theorem norm_Qop_real_le (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {A : LoopArg L (n + 1) → ℂ} {M P : ℝ} (hM : ∀ b, ‖A b‖ ≤ M) (hP : ∀ x, ‖Psum L A x‖ ≤ P)
    (a : LoopArg L (n + 1)) :
    ‖Qop L (t : ℂ) A a‖ ≤ M + P * (cTwo52 / ellHat L (t : ℂ)) ^ n := by
  refine (norm_Qop_apply_le L A a).trans (add_le_add (hM a) ?_)
  exact mul_le_mul (hP _) (norm_vartheta_real_le L hL ht0 ht1 a) (norm_nonneg _)
    ((norm_nonneg _).trans (hP (a 0)))

omit [NeZero L] in
/-- `FastDecay` is monotone in the radius and in the error. -/
theorem FastDecay.mono {n : ℕ} {R R' δ δ' : ℝ} {A : LoopArg L n → ℂ} (h : FastDecay L R δ A)
    (hR : R ≤ R') (hδ : δ ≤ δ') : FastDecay L R' δ' A := by
  intro a ⟨i, j, hij⟩
  exact (h a ⟨i, j, hR.trans hij⟩).trans hδ

/-- The decay half of **Lemma 5.13**: `Q_t` preserves the fast decay. -/
theorem fastDecay_Qop (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {A : LoopArg L (n + 1) → ℂ} {R δ P : ℝ} (hR : 0 < R) (hA : FastDecay L R δ A)
    (hP : ∀ x, ‖Psum L A x‖ ≤ P) :
    FastDecay L R (δ + P * ((cTwo52 / ellHat L (t : ℂ)) ^ n
      * exp (-(cZero * (R / 2) / ellHat L (t : ℂ))))) (Qop L (t : ℂ) A) := by
  intro a ha
  refine (norm_Qop_apply_le L A a).trans (add_le_add (hA a ha) ?_)
  exact mul_le_mul (hP _) (fastDecay_vartheta L hL ht0 ht1 hR a ha) (norm_nonneg _)
    ((norm_nonneg _).trans (hP (a 0)))

omit [NeZero L] in
/-- A product `(P ∘ A)_{a₁} ϑ_a` is fast-decaying if `ϑ` is. -/
theorem fastDecay_Psum_mul {n : ℕ} {B : LoopArg L (n + 1) → ℂ} {R δ P : ℝ}
    (hB : FastDecay L R δ B) (hP0 : 0 ≤ P)
    {V : ZMod L → ℂ} (hV : ∀ x, ‖V x‖ ≤ P) :
    FastDecay L R (P * δ) (fun b => V (b 0) * B b) := by
  intro a ha
  rw [norm_mul]
  exact mul_le_mul (hV _) (hB a ha) (norm_nonneg _) hP0

end Qop

/-! ### The generator `Θ_{t,σ}` and the commutator `[Q_t, Θ_{t,σ}]`

The generator (5.16) of the evolution kernel `U_{s,t,σ}` of (5.17) — the operator that (5.19)
identifies with the `l_K = 2` term, by (2.57) and the factor `S^(B)_{ab}` of (5.14) — is
`∑ᵢ ξᵢ Θ^(B)_{tξᵢ} S^(B)`, consistent with (5.18).  We work with a general slot-wise generator
`(𝒢_M ∘ A)_a = ∑ᵢ ∑_c (Mᵢ)_{aᵢ c} A_{a^{(i)}}` (`genOp`), and `genS` is the case
`Mᵢ = ξᵢ Θ^(B)_{tξᵢ} S^(B)`.  Everything about `Q_t` only uses the row and column sums of the
`Mᵢ`.

`genS L ξ t` is definitionally `RBM.ThetaOp L ξ t`; `genS` is the `genOp` instance. -/

section GenOp

variable (L : ℕ) [NeZero L]

/-- A slot-wise generator `(𝒢_M ∘ A)_a = ∑ᵢ ∑_c (Mᵢ)_{aᵢ c} A_{a^{(i)}}`. -/
noncomputable def genOp {n : ℕ} (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    (A : LoopArg L n → ℂ) : LoopArg L n → ℂ :=
  fun a => ∑ i : Fin n, ∑ c : ZMod L, M i (a i) c * A (Function.update a i c)

theorem genOp_sub {n : ℕ} (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ) (A B : LoopArg L n → ℂ) :
    genOp L M (A - B) = genOp L M A - genOp L M B := by
  funext a
  simp only [genOp, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- **The slot-sum identity of §5.5** for a general generator: the slot sums of `𝒢_M ∘ A`.  If the
matrices of the slots `i ≥ 2` have constant column sums `r_i`, the first slot contributes an
`M₁`-average of `P ∘ A` and every other slot contributes `r_i (P ∘ A)_{a₁}`. -/
theorem Psum_genOp_eq {n : ℕ} (M : Fin (n + 1) → Matrix (ZMod L) (ZMod L) ℂ) (r : Fin n → ℂ)
    (hcol : ∀ j : Fin n, ∀ c, ∑ y : ZMod L, M j.succ y c = r j) (A : LoopArg L (n + 1) → ℂ)
    (x : ZMod L) :
    Psum L (genOp L M A) x = (∑ c : ZMod L, M 0 x c * Psum L A c) + (∑ j, r j) * Psum L A x := by
  have hexp : ∀ q : LoopArg L n, genOp L M A (Fin.cons x q)
      = ∑ i : Fin (n + 1), ∑ c : ZMod L, M i ((Fin.cons x q : LoopArg L (n + 1)) i) c
          * A (Function.update (Fin.cons x q : LoopArg L (n + 1)) i c) := fun q => rfl
  rw [Psum, Finset.sum_congr rfl fun q _ => hexp q, Finset.sum_comm, Fin.sum_univ_succ]
  congr 1
  · -- the first slot
    have hstep : ∀ (q : LoopArg L n) (c : ZMod L),
        M 0 ((Fin.cons x q : LoopArg L (n + 1)) 0) c
          * A (Function.update (Fin.cons x q : LoopArg L (n + 1)) 0 c)
        = M 0 x c * A (Fin.cons c q) := by
      intro q c
      rw [Fin.cons_zero, update_cons_zero L x c q]
    rw [Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun c _ => hstep q c,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_sum]
    rfl
  · -- the other slots
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hstep : ∀ (q : LoopArg L n) (c : ZMod L),
        M j.succ ((Fin.cons x q : LoopArg L (n + 1)) j.succ) c
          * A (Function.update (Fin.cons x q : LoopArg L (n + 1)) j.succ c)
        = M j.succ (q j) c * A (Fin.cons x (Function.update q j c)) := by
      intro q c
      rw [Fin.cons_succ, update_cons_succ L x c q j]
    rw [Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun c _ => hstep q c,
      sum_sum_update_swap L j (fun y c q => M j.succ y c * A (Fin.cons x q))]
    calc ∑ q : LoopArg L n, ∑ c : ZMod L, M j.succ c (q j) * A (Fin.cons x q)
        = ∑ q : LoopArg L n, (∑ c : ZMod L, M j.succ c (q j)) * A (Fin.cons x q) :=
          Finset.sum_congr rfl fun q _ => (Finset.sum_mul _ _ _).symm
      _ = ∑ q : LoopArg L n, r j * A (Fin.cons x q) :=
          Finset.sum_congr rfl fun q _ => by rw [hcol j (q j)]
      _ = r j * Psum L A x := by rw [← Finset.mul_sum]; rfl

/-- The sum-zero property is preserved by `𝒢_M`. -/
theorem SumZero_genOp {n : ℕ} (M : Fin (n + 1) → Matrix (ZMod L) (ZMod L) ℂ) (r : Fin n → ℂ)
    (hcol : ∀ j : Fin n, ∀ c, ∑ y : ZMod L, M j.succ y c = r j) {A : LoopArg L (n + 1) → ℂ}
    (hA : SumZero L A) : SumZero L (genOp L M A) := by
  intro x
  rw [Psum_genOp_eq L M r hcol A x, hA x, mul_zero,
    Finset.sum_congr rfl fun c _ => by rw [hA c, mul_zero]]
  simp

/-- The slot sums of `𝒢_M ∘ A` are controlled by those of `A` (the deterministic content of
(5.99)). -/
theorem norm_Psum_genOp_le {n : ℕ} (M : Fin (n + 1) → Matrix (ZMod L) (ZMod L) ℂ)
    (r : Fin n → ℂ) (hcol : ∀ j : Fin n, ∀ c, ∑ y : ZMod L, M j.succ y c = r j)
    (A : LoopArg L (n + 1) → ℂ) {ρ P : ℝ} (hP0 : 0 ≤ P) (hP : ∀ y, ‖Psum L A y‖ ≤ P)
    (hρ : ∀ x, ∑ c, ‖M 0 x c‖ ≤ ρ) (x : ZMod L) :
    ‖Psum L (genOp L M A) x‖ ≤ (ρ + ∑ j, ‖r j‖) * P := by
  rw [Psum_genOp_eq L M r hcol A x, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖∑ c, M 0 x c * Psum L A c‖ ≤ ∑ c, ‖M 0 x c‖ * P :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hP c) (norm_nonneg _))
      _ = (∑ c, ‖M 0 x c‖) * P := by rw [Finset.sum_mul]
      _ ≤ ρ * P := mul_le_mul_of_nonneg_right (hρ x) hP0
  · rw [norm_mul]
    exact mul_le_mul ((norm_sum_le _ _)) (hP x) (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- `|𝒢_M ∘ B| ≤ (∑ᵢ ρᵢ) max |B|`. -/
theorem norm_genOp_le {n : ℕ} (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    {B : LoopArg L n → ℂ} {ρ Q : ℝ} (hQ0 : 0 ≤ Q) (hB : ∀ b, ‖B b‖ ≤ Q)
    (hρ : ∀ i x, ∑ c, ‖M i x c‖ ≤ ρ) (a : LoopArg L n) :
    ‖genOp L M B a‖ ≤ n * ρ * Q := by
  calc ‖genOp L M B a‖ ≤ ∑ i : Fin n, ∑ c, ‖M i (a i) c‖ * Q := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    _ ≤ ∑ _i : Fin n, ρ * Q := Finset.sum_le_sum fun i _ => by
        rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hρ i (a i)) hQ0
    _ = n * ρ * Q := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The commutator `[Q_t, 𝒢_M]`. -/
noncomputable def commOp {n : ℕ} (M : Fin (n + 1) → Matrix (ZMod L) (ZMod L) ℂ) (t : ℂ)
    (A : LoopArg L (n + 1) → ℂ) : LoopArg L (n + 1) → ℂ :=
  Qop L t (genOp L M A) - genOp L M (Qop L t A)

/-- **(5.99)**, the formula: `[Q_t, 𝒢] ∘ A = 𝒢 ∘ ((P ∘ A) ϑ_t) - (P ∘ (𝒢 ∘ A)) ϑ_t`. -/
theorem commOp_eq {n : ℕ} (M : Fin (n + 1) → Matrix (ZMod L) (ZMod L) ℂ) (t : ℂ)
    (A : LoopArg L (n + 1) → ℂ) :
    commOp L M t A = genOp L M (fun b => Psum L A (b 0) * vartheta L t b)
      - fun a => Psum L (genOp L M A) (a 0) * vartheta L t a := by
  have hQ : Qop L t A = A - fun b => Psum L A (b 0) * vartheta L t b := rfl
  have hQ' : Qop L t (genOp L M A)
      = genOp L M A - fun a => Psum L (genOp L M A) (a 0) * vartheta L t a := rfl
  rw [commOp, hQ, hQ', genOp_sub]
  abel

/-- **(5.90)**: the commutator lands in the sum-zero tensors. -/
theorem SumZero_commOp (hL : 3 ≤ L) {n : ℕ} (M : Fin (n + 1) → Matrix (ZMod L) (ZMod L) ℂ)
    (r : Fin n → ℂ) (hcol : ∀ j : Fin n, ∀ c, ∑ y : ZMod L, M j.succ y c = r j) {t : ℂ}
    (ht : ‖t‖ < 1) (A : LoopArg L (n + 1) → ℂ) : SumZero L (commOp L M t A) := by
  intro x
  rw [commOp, Psum_sub]
  have h1 : Psum L (Qop L t (genOp L M A)) x = 0 := SumZero_Qop L hL ht _ x
  have h2 : Psum L (genOp L M (Qop L t A)) x = 0 :=
    SumZero_genOp L M r hcol (SumZero_Qop L hL ht A) x
  simp [h1, h2]

end GenOp

/-! ### The generator of `U_{s,t,σ}`: `Mᵢ = ξᵢ Θ^(B)_{tξᵢ} S^(B)` -/

section GenS

variable (L : ℕ) [NeZero L]

/-- The edge matrices of the generator: `ξᵢ Θ^(B)_{tξᵢ} S^(B)`. -/
noncomputable def genSM {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ) : Fin n → Matrix (ZMod L) (ZMod L) ℂ :=
  fun i => ξ i • (Theta L (t * ξ i) * SB L)

/-- **The generator `Θ_{t,σ}` of `U_{s,t,σ}`** ((5.16) with the factor `S^(B)`, see above). -/
noncomputable def genS {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ) (A : LoopArg L n → ℂ) : LoopArg L n → ℂ :=
  genOp L (genSM L ξ t) A

/-- The commutator `[Q_t, Θ_{t,σ}]` of (5.89). -/
noncomputable def commS {n : ℕ} (ξ : Fin (n + 1) → ℂ) (t : ℂ) (A : LoopArg L (n + 1) → ℂ) :
    LoopArg L (n + 1) → ℂ :=
  commOp L (genSM L ξ t) t A

theorem sum_SB_col (hL : 3 ≤ L) (c : ZMod L) : ∑ d : ZMod L, SB L d c = 1 := by
  simp_rw [fun d => SB_apply_comm L d c]
  exact sum_SB_row L hL c

omit [NeZero L] in
theorem smul_matrix_apply (ξ : ℂ) (M : Matrix (ZMod L) (ZMod L) ℂ) (x c : ZMod L) :
    (ξ • M) x c = ξ * M x c := rfl

/-- The column sums of `ξ Θ_{tξ} S^(B)` are `ξ / (1 - tξ)`. -/
theorem sum_genSM_col (hL : 3 ≤ L) {ξ t : ℂ} (h : ‖t * ξ‖ < 1) (c : ZMod L) :
    ∑ y : ZMod L, (ξ • (Theta L (t * ξ) * SB L)) y c = ξ * (1 - t * ξ)⁻¹ := by
  calc ∑ y : ZMod L, (ξ • (Theta L (t * ξ) * SB L)) y c
      = ξ * ∑ y : ZMod L, ∑ d : ZMod L, Theta L (t * ξ) y d * SB L d c := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by rw [smul_matrix_apply, Matrix.mul_apply]
    _ = ξ * ∑ d : ZMod L, (∑ y : ZMod L, Theta L (t * ξ) y d) * SB L d c := by
        rw [Finset.sum_comm]
        exact congrArg _ (Finset.sum_congr rfl fun d _ => (Finset.sum_mul _ _ _).symm)
    _ = ξ * ∑ d : ZMod L, (1 - t * ξ)⁻¹ * SB L d c := by
        exact congrArg _ (Finset.sum_congr rfl fun d _ => by rw [sum_Theta_col hL h d])
    _ = ξ * (1 - t * ξ)⁻¹ := by rw [← Finset.mul_sum, sum_SB_col L hL c, mul_one]

/-- The row sums of `|ξ Θ_{tξ} S^(B)|` are at most `|ξ| (1 - |tξ|)^{-1}`. -/
theorem sum_norm_genSM_row_le (hL : 3 ≤ L) {ξ t : ℂ} (h : ‖t * ξ‖ < 1) (x : ZMod L) :
    ∑ c : ZMod L, ‖(ξ • (Theta L (t * ξ) * SB L)) x c‖ ≤ ‖ξ‖ * (1 - ‖t * ξ‖)⁻¹ := by
  simp_rw [smul_matrix_apply, fun c => norm_mul ξ ((Theta L (t * ξ) * SB L) x c)]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_norm_row_le L _ x).trans ?_) (norm_nonneg _)
  calc ‖Theta L (t * ξ) * SB L‖ ≤ ‖Theta L (t * ξ)‖ * ‖SB L‖ := norm_mul_le _ _
    _ = ‖Theta L (t * ξ)‖ := by rw [norm_SB L hL, mul_one]
    _ ≤ (1 - ‖t * ξ‖)⁻¹ := norm_Theta_le L hL h

/-- For a real time `t ∈ [0,1)` and `|ξ| ≤ 1`: row sums `≤ (1-t)^{-1}`. -/
theorem sum_norm_genSM_row_le_real (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) (x : ZMod L) :
    ∑ c : ZMod L, ‖(ξ • (Theta L ((t : ℂ) * ξ) * SB L)) x c‖ ≤ (1 - t)⁻¹ := by
  have h := norm_ofReal_mul_lt_one ht0 ht1 hξ
  refine (sum_norm_genSM_row_le L hL h x).trans ?_
  have h1 : ‖(t : ℂ) * ξ‖ ≤ t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    nlinarith [norm_nonneg ξ]
  have h2 : 0 < 1 - ‖(t : ℂ) * ξ‖ := by linarith
  have h3 : (1 - ‖(t : ℂ) * ξ‖)⁻¹ ≤ (1 - t)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  calc ‖ξ‖ * (1 - ‖(t : ℂ) * ξ‖)⁻¹ ≤ 1 * (1 - t)⁻¹ :=
        mul_le_mul hξ h3 (by positivity) zero_le_one
    _ = (1 - t)⁻¹ := one_mul _

omit [NeZero L] in
theorem ellHat_le_ellHat_real {t : ℝ} (ht1 : t < 1) {ζ : ℂ} (h : 1 - t ≤ ‖1 - ζ‖) :
    ellHat L ζ ≤ ellHat L (t : ℂ) := by
  rw [ellHat_ofReal L ht1, ellHat]
  refine min_le_min ?_ le_rfl
  have h1 : 0 < √(1 - t) := Real.sqrt_pos.2 (by linarith)
  exact one_div_le_one_div_of_le h1 (Real.sqrt_le_sqrt h)

/-- (2.52) at `tξ`, `|ξ| ≤ 1`, with the exponential factor, in the real scales. -/
theorem norm_Theta_mul_le_exp (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) (x y : ZMod L) :
    ‖Theta L ((t : ℂ) * ξ) x y‖ ≤ cTwo52 / ((1 - t) * ellHat L (t : ℂ))
      * exp (-(cZero * zdist L (x - y) / ellHat L (t : ℂ))) := by
  have hζ := norm_ofReal_mul_lt_one ht0 ht1 hξ
  have h := norm_Theta_apply_le_complex hL hζ x y
  have hden : 0 < (1 - t) * ellHat L (t : ℂ) :=
    mul_pos (by linarith) (ellHat_real_pos' L hL ht0 ht1)
  have hge := one_sub_le_norm_one_sub_mul ht0 hξ
  have hmono := one_sub_mul_ellHat_le L ht1 hge
  have hℓζ : 0 < ellHat L ((t : ℂ) * ξ) := lt_of_lt_of_le (by norm_num) (half_le_ellHat L hL hζ)
  have hℓ := ellHat_le_ellHat_real L ht1 hge
  have hexp : exp (-(cZero * zdist L (x - y) / ellHat L ((t : ℂ) * ξ)))
      ≤ exp (-(cZero * zdist L (x - y) / ellHat L (t : ℂ))) := by
    apply exp_le_exp.2
    have : cZero * zdist L (x - y) / ellHat L (t : ℂ)
        ≤ cZero * zdist L (x - y) / ellHat L ((t : ℂ) * ξ) :=
      div_le_div_of_nonneg_left (by have := cZero_pos; positivity) hℓζ hℓ
    linarith
  refine h.trans ?_
  rw [div_mul_eq_mul_div]
  have hc := cTwo52_pos
  calc cTwo52 * exp (-(cZero * zdist L (x - y) / ellHat L ((t : ℂ) * ξ)))
        / (‖1 - (t : ℂ) * ξ‖ * ellHat L ((t : ℂ) * ξ))
      ≤ cTwo52 * exp (-(cZero * zdist L (x - y) / ellHat L (t : ℂ)))
        / (‖1 - (t : ℂ) * ξ‖ * ellHat L ((t : ℂ) * ξ)) := by gcongr
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden hmono

/-- The entries of `ξ Θ_{tξ} S^(B)` decay: at distance `≥ R + 1` they are
`≤ C/((1-t)ℓ_t) e^{-c₀ R/ℓ_t}`. -/
theorem norm_genSM_le_of_far (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) {x c : ZMod L} {R : ℝ} (hR : R + 1 ≤ zdist L (x - c)) :
    ‖(ξ • (Theta L ((t : ℂ) * ξ) * SB L)) x c‖
      ≤ cTwo52 / ((1 - t) * ellHat L (t : ℂ)) * exp (-(cZero * R / ellHat L (t : ℂ))) := by
  set ε := cTwo52 / ((1 - t) * ellHat L (t : ℂ)) * exp (-(cZero * R / ellHat L (t : ℂ)))
  have hℓ := ellHat_real_pos' L hL ht0 ht1
  have hterm : ∀ d, ‖Theta L ((t : ℂ) * ξ) x d * SB L d c‖ ≤ ε * ‖SB L d c‖ := by
    intro d
    rw [norm_mul]
    by_cases hd : 1 < zdist L (d - c)
    · rw [SB_apply_eq_zero L hL hd, norm_zero, mul_zero, mul_zero]
    · push Not at hd
      refine mul_le_mul_of_nonneg_right ((norm_Theta_mul_le_exp L hL ht0 ht1 hξ x d).trans ?_)
        (norm_nonneg _)
      have h1 := zdist_add_le L (x - d) (d - c)
      have e : x - d + (d - c) = x - c := by ring
      rw [e] at h1
      have h2 : (zdist L (x - c) : ℝ) ≤ zdist L (x - d) + zdist L (d - c) := by exact_mod_cast h1
      have h3 : (zdist L (d - c) : ℝ) ≤ 1 := by exact_mod_cast hd
      have hRd : R ≤ zdist L (x - d) := by linarith
      have hc := cTwo52_pos
      have : 0 < 1 - t := by linarith
      refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by positivity)
      have := cZero_pos
      have : cZero * R / ellHat L (t : ℂ) ≤ cZero * zdist L (x - d) / ellHat L (t : ℂ) := by
        gcongr
      linarith
  rw [smul_matrix_apply, norm_mul, Matrix.mul_apply]
  have hε : 0 ≤ ε := by
    have := cTwo52_pos
    have : 0 < 1 - t := by linarith
    positivity
  calc ‖ξ‖ * ‖∑ d, Theta L ((t : ℂ) * ξ) x d * SB L d c‖ ≤ 1 * ε := by
        refine mul_le_mul hξ ?_ (norm_nonneg _) zero_le_one
        calc ‖∑ d, Theta L ((t : ℂ) * ξ) x d * SB L d c‖ ≤ ∑ d, ε * ‖SB L d c‖ :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => hterm d)
          _ = ε := by rw [← Finset.mul_sum, sum_norm_SB_col L hL c, mul_one]
    _ = ε := one_mul _

/-- **(5.90)**: `P ∘ [Q_t, Θ_{t,σ}] ∘ A = 0`. -/
theorem SumZero_commS (hL : 3 ≤ L) {n : ℕ} {ξ : Fin (n + 1) → ℂ} {t : ℂ}
    (ht : ∀ i, ‖t * ξ i‖ < 1) (htt : ‖t‖ < 1) (A : LoopArg L (n + 1) → ℂ) :
    SumZero L (commS L ξ t A) :=
  SumZero_commOp L hL (genSM L ξ t) (fun j => ξ j.succ * (1 - t * ξ j.succ)⁻¹)
    (fun j c => sum_genSM_col L hL (ht j.succ) c) htt A

end GenS

/-! ### Fast decay of `Θ_{t,σ} ∘ B` and of the commutator -/

section GenDecay

variable (L : ℕ) [NeZero L]

theorem zdist_comm (x y : ZMod L) : zdist L (x - y) = zdist L (y - x) := by
  rw [← zdist_neg L (x - y), neg_sub]

theorem zdist_triangle (x y z : ZMod L) :
    (zdist L (x - z) : ℝ) ≤ zdist L (x - y) + zdist L (y - z) := by
  have h := zdist_add_le L (x - y) (y - z)
  rw [show x - y + (y - z) = x - z by ring] at h
  exact_mod_cast h

omit [NeZero L] in
theorem FastDecay.sub {n : ℕ} {R δ₁ δ₂ : ℝ} {A B : LoopArg L n → ℂ} (hA : FastDecay L R δ₁ A)
    (hB : FastDecay L R δ₂ B) : FastDecay L R (δ₁ + δ₂) (A - B) := fun a ha =>
  (norm_sub_le _ _).trans (add_le_add (hA a ha) (hB a ha))

omit [NeZero L] in
theorem FastDecay.add {n : ℕ} {R δ₁ δ₂ : ℝ} {A B : LoopArg L n → ℂ} (hA : FastDecay L R δ₁ A)
    (hB : FastDecay L R δ₂ B) : FastDecay L R (δ₁ + δ₂) (A + B) := fun a ha =>
  (norm_add_le _ _).trans (add_le_add (hA a ha) (hB a ha))

/-- **A slot-wise generator with decaying entries preserves the fast decay**, at the price of
doubling the radius. -/
theorem fastDecay_genOp {n : ℕ} (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ) {ρ ε R δ Q : ℝ}
    (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hρ : ∀ i x, ∑ c, ‖M i x c‖ ≤ ρ)
    (hdec : ∀ i x c, R + 1 ≤ (zdist L (x - c) : ℝ) → ‖M i x c‖ ≤ ε)
    {B : LoopArg L n → ℂ} (hB : FastDecay L R δ B) (hBQ : ∀ b, ‖B b‖ ≤ Q) :
    FastDecay L (2 * R + 1) (n * (ρ * δ + L * (ε * Q))) (genOp L M B) := by
  classical
  intro a ⟨j, k, hjk⟩
  have hterm : ∀ i c, ‖M i (a i) c * B (Function.update a i c)‖ ≤ ‖M i (a i) c‖ * δ + ε * Q := by
    intro i c
    rw [norm_mul]
    by_cases hfar : ∃ p q, R ≤ (zdist L (Function.update a i c p - Function.update a i c q) : ℝ)
    · have := hB _ hfar
      have := mul_le_mul_of_nonneg_left this (norm_nonneg (M i (a i) c))
      nlinarith [mul_nonneg hε hQ]
    · push Not at hfar
      have hjk' : j ≠ k := by
        rintro rfl
        simp at hjk
        linarith
      have hMQ : ‖M i (a i) c‖ ≤ ε → ‖M i (a i) c‖ * ‖B (Function.update a i c)‖ ≤ ‖M i (a i) c‖ * δ + ε * Q := by
        intro hM
        have := mul_le_mul hM (hBQ (Function.update a i c)) (norm_nonneg _) hε
        nlinarith [mul_nonneg (norm_nonneg (M i (a i) c)) hδ]
      by_cases hij : i = j
      · subst hij
        have h1 := hfar i k
        rw [Function.update_self, Function.update_of_ne (Ne.symm hjk')] at h1
        refine hMQ (hdec i (a i) c ?_)
        have := zdist_triangle L (a i) c (a k)
        linarith
      · by_cases hik : i = k
        · subst hik
          have h1 := hfar j i
          rw [Function.update_self, Function.update_of_ne hjk'] at h1
          refine hMQ (hdec i (a i) c ?_)
          have := zdist_triangle L (a j) c (a i)
          rw [zdist_comm L c (a i)] at this
          linarith
        · exfalso
          have h1 := hfar j k
          rw [Function.update_of_ne (Ne.symm hij), Function.update_of_ne (Ne.symm hik)] at h1
          linarith
  calc ‖genOp L M B a‖ ≤ ∑ i : Fin n, ∑ c, (‖M i (a i) c‖ * δ + ε * Q) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hterm i c))
    _ ≤ ∑ _i : Fin n, (ρ * δ + L * (ε * Q)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
          ZMod.card, nsmul_eq_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hρ i (a i)) hδ) le_rfl
    _ = n * (ρ * δ + L * (ε * Q)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `|ξ (1 - tξ)^{-1}| ≤ (1 - t)^{-1}` for `|ξ| ≤ 1`, `t ∈ [0,1)`. -/
theorem norm_xi_mul_inv_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) :
    ‖ξ * (1 - (t : ℂ) * ξ)⁻¹‖ ≤ (1 - t)⁻¹ := by
  have h := one_sub_le_norm_one_sub_mul ht0 hξ
  rw [norm_mul, norm_inv]
  calc ‖ξ‖ * ‖1 - (t : ℂ) * ξ‖⁻¹ ≤ 1 * (1 - t)⁻¹ :=
        mul_le_mul hξ (inv_anti₀ (by linarith) h) (by positivity) zero_le_one
    _ = (1 - t)⁻¹ := one_mul _

/-- The max-norm half of **(5.99)**: `|[Q_t, Θ_{t,σ}] ∘ A| ≤ 2(n+1) (1-t)^{-1} (C/ℓ_t)^n P`,
where `P` bounds `P ∘ A`. -/
theorem norm_commS_le (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {ξ : Fin (n + 1) → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1) {A : LoopArg L (n + 1) → ℂ} {P : ℝ}
    (hP0 : 0 ≤ P) (hP : ∀ x, ‖Psum L A x‖ ≤ P) (a : LoopArg L (n + 1)) :
    ‖commS L ξ (t : ℂ) A a‖ ≤ 2 * (n + 1) * (1 - t)⁻¹ * (cTwo52 / ellHat L (t : ℂ)) ^ n * P := by
  have hℓ := ellHat_real_pos' L hL ht0 ht1
  have h1t : 0 < 1 - t := by linarith
  set θ := (cTwo52 / ellHat L (t : ℂ)) ^ n with hθ
  have hθ0 : 0 ≤ θ := by have := cTwo52_pos; positivity
  have hρ : ∀ i x, ∑ c, ‖genSM L ξ (t : ℂ) i x c‖ ≤ (1 - t)⁻¹ :=
    fun i x => sum_norm_genSM_row_le_real L hL ht0 ht1 (hξ i) x
  have hcol : ∀ j : Fin n, ∀ c, ∑ y : ZMod L, genSM L ξ (t : ℂ) j.succ y c
      = ξ j.succ * (1 - (t : ℂ) * ξ j.succ)⁻¹ :=
    fun j c => sum_genSM_col L hL (norm_ofReal_mul_lt_one ht0 ht1 (hξ j.succ)) c
  -- the first piece
  have hB : ∀ b, ‖Psum L A (b 0) * vartheta L (t : ℂ) b‖ ≤ P * θ := fun b => by
    rw [norm_mul]
    exact mul_le_mul (hP _) (norm_vartheta_real_le L hL ht0 ht1 b) (norm_nonneg _) hP0
  have h1 := norm_genOp_le L (genSM L ξ (t : ℂ)) (mul_nonneg hP0 hθ0) hB hρ a
  -- the second piece
  have hr : ∑ j : Fin n, ‖ξ j.succ * (1 - (t : ℂ) * ξ j.succ)⁻¹‖ ≤ n * (1 - t)⁻¹ := by
    calc ∑ j : Fin n, ‖ξ j.succ * (1 - (t : ℂ) * ξ j.succ)⁻¹‖ ≤ ∑ _j : Fin n, (1 - t)⁻¹ :=
          Finset.sum_le_sum fun j _ => norm_xi_mul_inv_le ht0 ht1 (hξ j.succ)
      _ = n * (1 - t)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 := norm_Psum_genOp_le L (genSM L ξ (t : ℂ)) _ hcol A hP0 hP (hρ 0) (a 0)
  have h2' : ‖Psum L (genOp L (genSM L ξ (t : ℂ)) A) (a 0) * vartheta L (t : ℂ) a‖
      ≤ ((1 - t)⁻¹ + n * (1 - t)⁻¹) * P * θ := by
    rw [norm_mul]
    refine mul_le_mul (h2.trans ?_) (norm_vartheta_real_le L hL ht0 ht1 a) (norm_nonneg _)
      (by positivity)
    exact mul_le_mul_of_nonneg_right (add_le_add le_rfl hr) hP0
  rw [commS, commOp_eq]
  refine (norm_sub_le _ _).trans ?_
  have e : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
  rw [e] at h1
  nlinarith [mul_nonneg (mul_nonneg (inv_nonneg.2 h1t.le) hP0) hθ0]

/-- The decay half of **(5.99)**: `[Q_t, Θ_{t,σ}] ∘ A` is fast-decaying, with the radius
doubled, when `P ∘ A` is bounded by `P`. -/
theorem fastDecay_commS (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {ξ : Fin (n + 1) → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1) {A : LoopArg L (n + 1) → ℂ} {P R : ℝ}
    (hR : 0 < R) (hP0 : 0 ≤ P) (hP : ∀ x, ‖Psum L A x‖ ≤ P) :
    FastDecay L (2 * R + 1)
      ((n + 1) * ((1 - t)⁻¹ * (P * ((cTwo52 / ellHat L (t : ℂ)) ^ n
          * exp (-(cZero * (R / 2) / ellHat L (t : ℂ)))))
        + L * (cTwo52 / ((1 - t) * ellHat L (t : ℂ)) * exp (-(cZero * R / ellHat L (t : ℂ)))
          * (P * (cTwo52 / ellHat L (t : ℂ)) ^ n)))
      + (1 + n) * (1 - t)⁻¹ * P * ((cTwo52 / ellHat L (t : ℂ)) ^ n
          * exp (-(cZero * ((2 * R + 1) / 2) / ellHat L (t : ℂ)))))
      (commS L ξ (t : ℂ) A) := by
  have hℓ := ellHat_real_pos' L hL ht0 ht1
  have h1t : 0 < 1 - t := by linarith
  have hc := cTwo52_pos
  set θ := (cTwo52 / ellHat L (t : ℂ)) ^ n with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hρ : ∀ i x, ∑ c, ‖genSM L ξ (t : ℂ) i x c‖ ≤ (1 - t)⁻¹ :=
    fun i x => sum_norm_genSM_row_le_real L hL ht0 ht1 (hξ i) x
  have hcol : ∀ j : Fin n, ∀ c, ∑ y : ZMod L, genSM L ξ (t : ℂ) j.succ y c
      = ξ j.succ * (1 - (t : ℂ) * ξ j.succ)⁻¹ :=
    fun j c => sum_genSM_col L hL (norm_ofReal_mul_lt_one ht0 ht1 (hξ j.succ)) c
  -- `B = (P ∘ A) ϑ_t`
  have hBdec := fastDecay_Psum_mul L (fastDecay_vartheta L hL ht0 ht1 (n := n) hR) hP0
    (V := Psum L A) hP
  have hBQ : ∀ b, ‖Psum L A (b 0) * vartheta L (t : ℂ) b‖ ≤ P * θ := fun b => by
    rw [norm_mul]
    exact mul_le_mul (hP _) (norm_vartheta_real_le L hL ht0 ht1 b) (norm_nonneg _) hP0
  have hdec : ∀ i x c, R + 1 ≤ (zdist L (x - c) : ℝ) → ‖genSM L ξ (t : ℂ) i x c‖
      ≤ cTwo52 / ((1 - t) * ellHat L (t : ℂ)) * exp (-(cZero * R / ellHat L (t : ℂ))) :=
    fun i x c h => norm_genSM_le_of_far L hL ht0 ht1 (hξ i) h
  have h1 := fastDecay_genOp L (genSM L ξ (t : ℂ)) hR.le (mul_nonneg hP0 hθ0)
    (by positivity) (by positivity) hρ hdec hBdec hBQ
  -- the second piece
  have hr : ∑ j : Fin n, ‖ξ j.succ * (1 - (t : ℂ) * ξ j.succ)⁻¹‖ ≤ n * (1 - t)⁻¹ := by
    calc ∑ j : Fin n, ‖ξ j.succ * (1 - (t : ℂ) * ξ j.succ)⁻¹‖ ≤ ∑ _j : Fin n, (1 - t)⁻¹ :=
          Finset.sum_le_sum fun j _ => norm_xi_mul_inv_le ht0 ht1 (hξ j.succ)
      _ = n * (1 - t)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hP2 : ∀ x, ‖Psum L (genOp L (genSM L ξ (t : ℂ)) A) x‖ ≤ (1 + n) * (1 - t)⁻¹ * P := by
    intro x
    refine (norm_Psum_genOp_le L (genSM L ξ (t : ℂ)) _ hcol A hP0 hP (hρ 0) x).trans ?_
    have : (1 - t)⁻¹ + ∑ j : Fin n, ‖ξ j.succ * (1 - (t : ℂ) * ξ j.succ)⁻¹‖
        ≤ (1 + n) * (1 - t)⁻¹ := by linarith
    exact mul_le_mul_of_nonneg_right this hP0
  have h2 := fastDecay_Psum_mul L (fastDecay_vartheta L hL ht0 ht1 (n := n)
    (show 0 < 2 * R + 1 by linarith)) (by positivity) hP2
  rw [commS, commOp_eq]
  have e : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
  have h1' := h1
  rw [e] at h1'
  exact FastDecay.sub L h1' h2

end GenDecay

/-! ### (5.88): the `Q_t ∘ (L - K)` hierarchy (the drift part) -/

section Hierarchy588

variable (L : ℕ) [NeZero L]

end Hierarchy588

/-! ### The evolution kernel on the terms of (5.91): (5.93) and the time integrals -/

section KernelTerms

variable (L : ℕ) [NeZero L]

end KernelTerms

/-! ### `≺`: the good-event pattern, and the crude scale bounds of the flow -/

section StochHelpers

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- A constant times `N^a` is eventually below `N^b` for `a < b`. -/
theorem eventually_const_mul_rpow_le (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  filter_upwards [eventually_le_rpow C (sub_pos.2 hab), eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  calc C * (N : ℝ) ^ a ≤ (N : ℝ) ^ (b - a) * (N : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ b := by rw [← Real.rpow_add hN0]; ring_nf

end StochHelpers

section FlowScales

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

theorem Band.scale_eq (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ) :
    B.scale E N u = ((B.W N : ℝ) * (mE E).im) * ((1 - u) * ellHat (B.L N) (u : ℂ)) := by
  simp only [Band.scale, Band.ell, etaT]; ring

theorem ellHat_real_le_L {L : ℕ} {u : ℝ} (hu1 : u < 1) : ellHat L (u : ℂ) ≤ L := by
  rw [ellHat_ofReal L hu1]; exact min_le_right _ _

end FlowScales

/-! ### The random-layer interface

The loop tensors of the flow are `lkT X E N u ω σ a = (L - K)_{u,σ,a}`, for charges
`σ : Fin m → Bool` and labels `a : LoopArg (L N) m` (the representation bridge `LoopArg ↔
LoopIdx` is just `LoopData.idx = ⟨List.ofFn σ, List.ofFn a⟩`). -/

section Interface

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The tensor `(L - K)_{u,σ,·}` of an `m`-loop at the time `u`. -/
noncomputable def lkT (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) : LoopArg (B.L N) m → ℂ :=
  fun a => X.Lval E N u ω (LoopData.idx (σ, a)) - B.Kval E N u (LoopData.idx (σ, a))

theorem norm_lkT (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) :
    ‖lkT X E N u ω σ a‖ = X.lkErr E N u ω (LoopData.idx (σ, a)) := rfl

/-- `(Q_t ⊗ Q_t)` of (5.104), acting on a two-slot tensor written as a `(2m)`-tensor. -/
noncomputable def QQ (L : ℕ) [NeZero L] {n : ℕ} (t : ℂ)
    (Bt : LoopArg L ((n + 1) + (n + 1)) → ℂ) : LoopArg L ((n + 1) + (n + 1)) → ℂ :=
  fun c => Qop₁ L t (Qop₂ L t (fun a b => Bt (Fin.append a b)))
    (fun i => c (Fin.castAdd (n + 1) i)) (fun i => c (Fin.natAdd (n + 1) i))

/-- The edge parameters `(ξ, ξ̄)` of the doubled loop in (5.85), (5.103).

Lemma 5.5 writes the doubled operator as `U_{u,t,σ} ⊗ U_{u,t,σ̄}`, "where `σ̄` is the
conjugate sign vector of `σ`", and the glued loop of (5.23) carries the charges
`(σ_k, …, σ_k, σ̄_k, …, σ̄_k)`; the second factor therefore runs with the edge parameters
`m̄_i m̄_{i+1} = conj (m_i m_{i+1})`.  Accordingly the second half is `xiOf (mSigma E) (!∘σ)`,
which by `RBM.mSigma_not` is `conj ∘ xiOf (mSigma E) σ`.

Every estimate that factors through `RBM.SumZeroDyn.norm_xi2_le` uses only
`‖xiOf (mSigma E) σ i‖ = 1` for `|E| ≤ 2` (`RBM.norm_xiOf_mSigma`, valid for *any* charge
vector); the *identity* `RBM.EEUker.sum_Uker_mul_conj_Uker`, and hence the quadratic-variation
right-hand sides of (5.85) and (5.103), hold for the conjugated vector. -/
noncomputable def xi2 (E : ℝ) {n : ℕ} (σ : Fin (n + 2) → Bool) : Fin ((n + 2) + (n + 2)) → ℂ :=
  Fin.append (xiOf (mSigma E) σ) (xiOf (mSigma E) (fun i => !(σ i)))

end Interface

/-! ### (5.96): Ward's identity and the slot sums of `L - K` -/

section Ward596

variable (L : ℕ) [NeZero L]

/-- **(5.96)**, abstract form: if Ward's identity reduces the slot sum of `T` to slot sums of two
loops `T', T''` of one less length (with the factor `κ = (2iWη)^{-1}`), and these are bounded
by `d` and `(R, δ)`-fast-decaying, then `|P ∘ T| ≤ 2|κ| ((2e(R+1))^n d + L^n δ)`. -/
theorem norm_Psum_le_of_ward {n : ℕ} {T : LoopArg L (n + 2) → ℂ} {T' T'' : LoopArg L (n + 1) → ℂ}
    {κ : ℂ} {x : ZMod L} (hW : Psum L T x = κ * (Psum L T' x - Psum L T'' x)) {R d δ : ℝ}
    (hR : 0 < R) (hd : 0 ≤ d) (hδ : 0 ≤ δ) (hT'd : ∀ b, ‖T' b‖ ≤ d) (hT''d : ∀ b, ‖T'' b‖ ≤ d)
    (hT' : FastDecay L R δ T') (hT'' : FastDecay L R δ T'') :
    ‖Psum L T x‖ ≤ ‖κ‖ * (2 * ((2 * exp 1 * (R + 1)) ^ n * d + (L : ℝ) ^ n * δ)) := by
  rw [hW, norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
  have h1 := norm_Psum_le_of_fastDecay L hR hd hδ hT'd hT' x
  have h2 := norm_Psum_le_of_fastDecay L hR hd hδ hT''d hT'' x
  linarith

end Ward596

section WardFlow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

end WardFlow

section CombinedOuter

/-! ### Two-block tensors: `E ⊗ E`, `Q_t ⊗ Q_t` and (5.104)

`E ⊗ E` carries two label tuples; we write it as a `2m`-tensor `c = (a, b)` (`Fin.append`), so
that the evolution kernel `U ⊗ U` is `Uker` with the doubled edge parameters `xi2`.  `Q1`, `Q2`
are `Q_t` in the first, resp. second block; `QQ = Q1 ∘ Q2` is (5.104). -/

variable (L : ℕ) [NeZero L]

section Combined

/-- The first block of a two-block index. -/
def spl1 {m m' : ℕ} (c : LoopArg L (m + m')) : LoopArg L m := fun i => c (Fin.castAdd m' i)

/-- The second block of a two-block index. -/
def spl2 {m m' : ℕ} (c : LoopArg L (m + m')) : LoopArg L m' := fun i => c (Fin.natAdd m i)

omit [NeZero L] in
@[simp] theorem spl1_append {m m' : ℕ} (a : LoopArg L m) (b : LoopArg L m') :
    spl1 L (Fin.append a b) = a := funext fun i => Fin.append_left a b i

omit [NeZero L] in
@[simp] theorem spl2_append {m m' : ℕ} (a : LoopArg L m) (b : LoopArg L m') :
    spl2 L (Fin.append a b) = b := funext fun i => Fin.append_right a b i

omit [NeZero L] in
@[simp] theorem append_spl {m m' : ℕ} (c : LoopArg L (m + m')) :
    Fin.append (spl1 L c) (spl2 L c) = c := Fin.append_castAdd_natAdd

theorem sum_append {m m' : ℕ} (f : LoopArg L (m + m') → ℂ) :
    ∑ c, f c = ∑ a : LoopArg L m, ∑ b : LoopArg L m', f (Fin.append a b) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.appendEquiv m m') _ _ (fun p => rfl)).symm

/-- `Q_t` in the first block. -/
noncomputable def Q1 {k m' : ℕ} (t : ℂ) (Bc : LoopArg L ((k + 1) + m') → ℂ) :
    LoopArg L ((k + 1) + m') → ℂ :=
  fun c => Qop L t (fun a' => Bc (Fin.append a' (spl2 L c))) (spl1 L c)

/-- `Q_t` in the second block. -/
noncomputable def Q2 {m k : ℕ} (t : ℂ) (Bc : LoopArg L (m + (k + 1)) → ℂ) :
    LoopArg L (m + (k + 1)) → ℂ :=
  fun c => Qop L t (fun b' => Bc (Fin.append (spl1 L c) b')) (spl2 L c)

/-- Swapping the two blocks. -/
def swapT {m : ℕ} (Bc : LoopArg L (m + m) → ℂ) : LoopArg L (m + m) → ℂ :=
  fun c => Bc (Fin.append (spl2 L c) (spl1 L c))

theorem Q2_eq_swap {k : ℕ} (t : ℂ) (Bc : LoopArg L ((k + 1) + (k + 1)) → ℂ) :
    Q2 L t Bc = swapT L (Q1 L t (swapT L Bc)) := by
  funext c
  simp [Q2, Q1, swapT]

omit [NeZero L] in
/-- Swapping the blocks preserves the fast decay. -/
theorem FastDecay.swapT {m : ℕ} {R δ : ℝ} {Bc : LoopArg L (m + m) → ℂ} (h : FastDecay L R δ Bc) :
    FastDecay L R δ (swapT L Bc) := by
  intro c ⟨i, j, hij⟩
  refine h _ ?_
  have key : ∀ p : Fin (m + m), ∃ p' : Fin (m + m),
      Fin.append (spl2 L c) (spl1 L c) p' = c p := by
    intro p
    induction p using Fin.addCases with
    | left i => exact ⟨Fin.natAdd m i, by rw [Fin.append_right]; rfl⟩
    | right i => exact ⟨Fin.castAdd m i, by rw [Fin.append_left]; rfl⟩
  obtain ⟨i', hi'⟩ := key i
  obtain ⟨j', hj'⟩ := key j
  exact ⟨i', j', by rw [hi', hj']; exact hij⟩

omit [NeZero L] in
theorem FastDecay.block1 {m m' : ℕ} {R δ : ℝ} {Bc : LoopArg L (m + m') → ℂ}
    (h : FastDecay L R δ Bc) (b : LoopArg L m') :
    FastDecay L R δ (fun a' => Bc (Fin.append a' b)) := by
  intro a ⟨i, j, hij⟩
  refine h _ ⟨Fin.castAdd m' i, Fin.castAdd m' j, ?_⟩
  simpa [Fin.append_left] using hij

/-- `Q_t` in the first block is bounded. -/
theorem norm_Q1_le (hL : 3 ≤ L) {k m' : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {R e δ : ℝ}
    (hR : 0 < R) (he : 0 ≤ e) (hδ : 0 ≤ δ) {Bc : LoopArg L ((k + 1) + m') → ℂ}
    (hBe : ∀ c, ‖Bc c‖ ≤ e) (hB : FastDecay L R δ Bc) (c : LoopArg L ((k + 1) + m')) :
    ‖Q1 L (t : ℂ) Bc c‖
      ≤ e + ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ) * (cTwo52 / ellHat L (t : ℂ)) ^ k := by
  unfold Q1
  have hP := norm_Psum_le_of_fastDecay L hR he hδ (fun a' => hBe (Fin.append a' (spl2 L c)))
    (FastDecay.block1 L hB (spl2 L c))
  exact (norm_Qop_apply_le L _ _).trans (add_le_add (hBe _)
    (mul_le_mul (hP _) (norm_vartheta_real_le L hL ht0 ht1 _) (norm_nonneg _)
      ((norm_nonneg _).trans (hP (spl1 L c 0)))))

/-- `Q_t` in the first block preserves the fast decay (at twice the radius). -/
theorem fastDecay_Q1 (hL : 3 ≤ L) {k m' : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {R e δ : ℝ}
    (hR : 0 < R) (he : 0 ≤ e) (hδ : 0 ≤ δ) {Bc : LoopArg L ((k + 1) + m') → ℂ}
    (hBe : ∀ c, ‖Bc c‖ ≤ e) (hB : FastDecay L R δ Bc) :
    FastDecay L (2 * R) (δ + ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ)
      * (cTwo52 / ellHat L (t : ℂ)) ^ k * exp (-(cZero * R / ellHat L (t : ℂ)))
      + (L : ℝ) ^ k * δ * (cTwo52 / ellHat L (t : ℂ)) ^ k) (Q1 L (t : ℂ) Bc) := by
  classical
  intro c ⟨p, q, hpq⟩
  set a := spl1 L c with ha
  set b := spl2 L c with hb
  have hc : Fin.append a b = c := append_spl L c
  have hθ := norm_vartheta_real_le L hL ht0 ht1 (n := k) a
  have hP := norm_Psum_le_of_fastDecay L hR he hδ (fun a' => hBe (Fin.append a' b))
    (FastDecay.block1 L hB b) (a 0)
  have hθ0 : 0 ≤ (cTwo52 / ellHat L (t : ℂ)) ^ k := (norm_nonneg _).trans hθ
  have hE0 : 0 ≤ exp (-(cZero * R / ellHat L (t : ℂ))) := (exp_pos _).le
  have hP0 : 0 ≤ (2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ :=
    (norm_nonneg _).trans hP
  unfold Q1
  rw [← ha, ← hb]
  refine (norm_Qop_apply_le L _ _).trans ?_
  have h1 : ‖Bc (Fin.append a b)‖ ≤ δ := by
    rw [hc]; exact hB c ⟨p, q, by linarith⟩
  have hLk : 0 ≤ (L : ℝ) ^ k * δ * (cTwo52 / ellHat L (t : ℂ)) ^ k := by positivity
  have hPθ : 0 ≤ ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ)
      * (cTwo52 / ellHat L (t : ℂ)) ^ k * exp (-(cZero * R / ellHat L (t : ℂ))) := by positivity
  by_cases hA : ∃ i : Fin k, R ≤ (zdist L (a 0 - a i.succ) : ℝ)
  · obtain ⟨i, hi⟩ := hA
    have hθ' := norm_vartheta_real_le_of_far L hL ht0 ht1 i hi
    have := mul_le_mul hP hθ' (norm_nonneg _) hP0
    have e1 : ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ)
        * ((cTwo52 / ellHat L (t : ℂ)) ^ k * exp (-(cZero * R / ellHat L (t : ℂ))))
        = ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ)
          * (cTwo52 / ellHat L (t : ℂ)) ^ k * exp (-(cZero * R / ellHat L (t : ℂ))) := by ring
    linarith
  · push Not at hA
    -- every index of `a` is within `R` of `a 0`
    have hnear : ∀ i : Fin (k + 1), (zdist L (a i - a 0) : ℝ) < R := by
      intro i
      induction i using Fin.cases with
      | zero => simp; exact hR
      | succ i => rw [zdist_comm]; exact hA i
    -- every term of the slot sum has a far pair
    have hfar : ∀ r : LoopArg L k, ∃ i j,
        R ≤ (zdist L (Fin.append (Fin.cons (a 0) r) b i - Fin.append (Fin.cons (a 0) r) b j) : ℝ) := by
      intro r
      rw [← hc] at hpq
      induction p using Fin.addCases with
      | left i =>
        induction q using Fin.addCases with
        | left j =>
          exfalso
          simp only [Fin.append_left] at hpq
          have := zdist_triangle L (a i) (a 0) (a j)
          have h1 := hnear i
          have h2 := hnear j
          rw [zdist_comm L (a 0) (a j)] at this
          linarith
        | right j =>
          refine ⟨Fin.castAdd m' 0, Fin.natAdd (k + 1) j, ?_⟩
          simp only [Fin.append_left, Fin.append_right, Fin.cons_zero] at hpq ⊢
          have := zdist_triangle L (a i) (a 0) (b j)
          have h1 := hnear i
          linarith
      | right i =>
        induction q using Fin.addCases with
        | left j =>
          refine ⟨Fin.natAdd (k + 1) i, Fin.castAdd m' 0, ?_⟩
          simp only [Fin.append_left, Fin.append_right, Fin.cons_zero] at hpq ⊢
          have := zdist_triangle L (b i) (a 0) (a j)
          have h1 := hnear j
          rw [zdist_comm L (a 0) (a j)] at this
          linarith
        | right j =>
          refine ⟨Fin.natAdd (k + 1) i, Fin.natAdd (k + 1) j, ?_⟩
          simp only [Fin.append_right] at hpq ⊢
          linarith
    have hPs : ‖Psum L (fun a' => Bc (Fin.append a' b)) (a 0)‖ ≤ (L : ℝ) ^ k * δ := by
      calc ‖Psum L (fun a' => Bc (Fin.append a' b)) (a 0)‖
          ≤ ∑ r : LoopArg L k, ‖Bc (Fin.append (Fin.cons (a 0) r) b)‖ := norm_sum_le _ _
        _ ≤ ∑ _r : LoopArg L k, δ := Finset.sum_le_sum fun r _ => hB _ (hfar r)
        _ = (L : ℝ) ^ k * δ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin,
              nsmul_eq_mul]; push_cast; ring
    have := mul_le_mul hPs hθ (norm_nonneg _) (by positivity)
    linarith

/-- `Q_t` in the second block is bounded (by symmetry). -/
theorem norm_Q2_le (hL : 3 ≤ L) {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {R e δ : ℝ}
    (hR : 0 < R) (he : 0 ≤ e) (hδ : 0 ≤ δ) {Bc : LoopArg L ((k + 1) + (k + 1)) → ℂ}
    (hBe : ∀ c, ‖Bc c‖ ≤ e) (hB : FastDecay L R δ Bc) (c : LoopArg L ((k + 1) + (k + 1))) :
    ‖Q2 L (t : ℂ) Bc c‖
      ≤ e + ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ) * (cTwo52 / ellHat L (t : ℂ)) ^ k := by
  rw [Q2_eq_swap]
  exact norm_Q1_le L hL ht0 ht1 hR he hδ (fun c => hBe _) (FastDecay.swapT L hB) _

/-- `Q_t` in the second block preserves the fast decay (by symmetry). -/
theorem fastDecay_Q2 (hL : 3 ≤ L) {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {R e δ : ℝ}
    (hR : 0 < R) (he : 0 ≤ e) (hδ : 0 ≤ δ) {Bc : LoopArg L ((k + 1) + (k + 1)) → ℂ}
    (hBe : ∀ c, ‖Bc c‖ ≤ e) (hB : FastDecay L R δ Bc) :
    FastDecay L (2 * R) (δ + ((2 * exp 1 * (R + 1)) ^ k * e + (L : ℝ) ^ k * δ)
      * (cTwo52 / ellHat L (t : ℂ)) ^ k * exp (-(cZero * R / ellHat L (t : ℂ)))
      + (L : ℝ) ^ k * δ * (cTwo52 / ellHat L (t : ℂ)) ^ k) (Q2 L (t : ℂ) Bc) := by
  rw [Q2_eq_swap]
  exact FastDecay.swapT L (fastDecay_Q1 L hL ht0 ht1 hR he hδ (fun c => hBe _)
    (FastDecay.swapT L hB))

/-- `(Q_t ⊗ Q_t) = Q_t` in the first block after `Q_t` in the second. -/
theorem QQ_eq {k : ℕ} (t : ℂ) (Bt : LoopArg L ((k + 1) + (k + 1)) → ℂ) :
    QQ L t Bt = Q1 L t (Q2 L t Bt) := by
  funext c
  simp only [QQ, Q1, Q2, Qop₁, Qop₂, spl1_append, spl2_append]
  rfl

/-- **(5.104)**: `(Q_t ⊗ Q_t) ∘ B` has the sum-zero property in the first block, hence (as a
`2m`-tensor) at the coordinate `0`. -/
theorem sumZeroAt_QQ (hL : 3 ≤ L) {k : ℕ} {t : ℂ} (ht : ‖t‖ < 1)
    (Bt : LoopArg L ((k + 1) + (k + 1)) → ℂ) : SumZeroAt L 0 (QQ L t Bt) := by
  intro x
  rw [sum_append]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ => ?_
  have h0 : ∀ a : LoopArg L (k + 1), (Fin.append a b : LoopArg L ((k + 1) + (k + 1))) 0 = a 0 := by
    intro a
    have : (0 : Fin ((k + 1) + (k + 1))) = Fin.castAdd (k + 1) 0 := rfl
    rw [this, Fin.append_left]
  simp_rw [h0]
  rw [sum_loopArg_succ]
  simp only [Fin.cons_zero]
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [hy]) (by simp)]
  simp only [ite_true]
  rw [QQ_eq]
  simp only [Q1, Q2, spl1_append, spl2_append]
  exact SumZero_Qop L hL ht (fun a' => Qop L t (fun b' => Bt (Fin.append a' b')) b) x

end Combined

end CombinedOuter

/-! ### Scalar bookkeeping for the `≺` assembly -/

section Scalar

open Filter Topology in
/-- `C N^k e^{-c N^{τ₁}} ≤ 1` eventually: the exponential tails of `Θ` beat every power. -/
theorem eventually_exp_small (C k c : ℝ) {τ₁ : ℝ} (hc : 0 < c) (hτ₁ : 0 < τ₁) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ k * exp (-(c * (N : ℝ) ^ τ₁)) ≤ 1 := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k / τ₁) c hc
  have hg : Tendsto (fun N : ℕ => (N : ℝ) ^ τ₁) atTop atTop :=
    (tendsto_rpow_atTop hτ₁).comp tendsto_natCast_atTop_atTop
  have h2 := h.comp hg
  have hpos : (0 : ℝ) < (|C| + 1)⁻¹ := by positivity
  filter_upwards [h2.eventually (gt_mem_nhds hpos)] with N hN
  simp only [Function.comp_apply] at hN
  have e : ((N : ℝ) ^ τ₁) ^ (k / τ₁) = (N : ℝ) ^ k := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]; congr 1; field_simp
  rw [e] at hN
  have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  have hx : 0 ≤ (N : ℝ) ^ k * exp (-(c * (N : ℝ) ^ τ₁)) := by positivity
  have hN' : (N : ℝ) ^ k * exp (-c * (N : ℝ) ^ τ₁) < (|C| + 1)⁻¹ := hN
  rw [neg_mul] at hN'
  calc C * (N : ℝ) ^ k * exp (-(c * (N : ℝ) ^ τ₁))
      = C * ((N : ℝ) ^ k * exp (-(c * (N : ℝ) ^ τ₁))) := by ring
    _ ≤ (|C| + 1) * ((N : ℝ) ^ k * exp (-(c * (N : ℝ) ^ τ₁))) := mul_le_mul_of_nonneg_right hC hx
    _ ≤ (|C| + 1) * (|C| + 1)⁻¹ := mul_le_mul_of_nonneg_left hN'.le (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

section StochSums

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

end StochSums

theorem radius_le {ℓ K : ℝ} (hℓ : 1 / 2 ≤ ℓ) (hK : 1 ≤ K) : 2 * (ℓ * K) + 1 ≤ ℓ * (4 * K) := by
  nlinarith

theorem two_le_radius {ℓ K : ℝ} (hℓ : 1 / 2 ≤ ℓ) (hK : 1 ≤ K) : 2 ≤ ℓ * (4 * K) := by nlinarith

end Scalar

/-! ### Deterministic term bounds -/

section TermBounds

/-- `(2e(ℓK+1))^n (c/ℓ)^n ≤ (6ecK)^n` for `ℓ ≥ 1/2`, `K ≥ 1`. -/
theorem window_mul_le {n : ℕ} {ℓ K c : ℝ} (hℓ : 1 / 2 ≤ ℓ) (hK : 1 ≤ K) (hc : 0 ≤ c) :
    (2 * exp 1 * (ℓ * K + 1)) ^ n * (c / ℓ) ^ n ≤ (6 * exp 1 * c * K) ^ n := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by have := exp_pos 1; positivity) ?_ n
  have hℓ0 : 0 < ℓ := by linarith
  rw [mul_div_assoc', div_le_iff₀ hℓ0]
  have h1 : ℓ * K + 1 ≤ 3 * ℓ * K := by nlinarith
  have he := exp_pos 1
  nlinarith [mul_nonneg (mul_nonneg he.le hc) (sub_nonneg.2 h1)]

/-- `(c/ℓ)^n ≤ (2c)^n` for `ℓ ≥ 1/2`. -/
theorem div_pow_le_two_mul {n : ℕ} {ℓ c : ℝ} (hℓ : 1 / 2 ≤ ℓ) (hc : 0 ≤ c) :
    (c / ℓ) ^ n ≤ (2 * c) ^ n := by
  have hℓ0 : 0 < ℓ := by linarith
  refine pow_le_pow_left₀ (by positivity) ?_ n
  rw [div_le_iff₀ hℓ0]; nlinarith

variable (L : ℕ) [NeZero L]

/-- **Lemma 5.13 (5.87)** in the form used: for an `(ℓ_t K, δ)`-fast-decaying `A` bounded by `M`,
`|Q_t ∘ A| ≤ (1 + (6ecK)^n) M + (2c)^n L^n δ`. -/
theorem norm_Qop_le_of_fastDecay (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {K M δ : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ) {A : LoopArg L (n + 1) → ℂ}
    (hAM : ∀ b, ‖A b‖ ≤ M) (hA : FastDecay L (ellHat L (t : ℂ) * K) δ A) (a : LoopArg L (n + 1)) :
    ‖Qop L (t : ℂ) A a‖ ≤ (1 + (6 * exp 1 * cTwo52 * K) ^ n) * M
      + (2 * cTwo52) ^ n * (L : ℝ) ^ n * δ := by
  have hℓ := half_le_ellHat_real L hL ht0 ht1
  have hR : 0 < ellHat L (t : ℂ) * K := by nlinarith
  have hP := norm_Psum_le_of_fastDecay L hR hM hδ hAM hA
  have h := norm_Qop_real_le L hL ht0 ht1 hAM hP a
  have hc := cTwo52_pos.le
  have h1 := window_mul_le (n := n) hℓ hK hc
  have h2 := div_pow_le_two_mul (n := n) hℓ hc
  have hLδ : 0 ≤ (L : ℝ) ^ n * δ := by positivity
  calc ‖Qop L (t : ℂ) A a‖
      ≤ M + ((2 * exp 1 * (ellHat L (t : ℂ) * K + 1)) ^ n * M + (L : ℝ) ^ n * δ)
          * (cTwo52 / ellHat L (t : ℂ)) ^ n := h
    _ = M + ((2 * exp 1 * (ellHat L (t : ℂ) * K + 1)) ^ n * (cTwo52 / ellHat L (t : ℂ)) ^ n) * M
          + (cTwo52 / ellHat L (t : ℂ)) ^ n * ((L : ℝ) ^ n * δ) := by ring
    _ ≤ M + (6 * exp 1 * cTwo52 * K) ^ n * M + (2 * cTwo52) ^ n * ((L : ℝ) ^ n * δ) := by
        gcongr
    _ = _ := by ring

/-- The decay half of **Lemma 5.13**, in the same normalization. -/
theorem fastDecay_Qop_le (hL : 3 ≤ L) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {K M δ : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ) {A : LoopArg L (n + 1) → ℂ}
    (hAM : ∀ b, ‖A b‖ ≤ M) (hA : FastDecay L (ellHat L (t : ℂ) * K) δ A) :
    FastDecay L (ellHat L (t : ℂ) * K)
      (δ + ((6 * exp 1 * cTwo52 * K) ^ n * M + (2 * cTwo52) ^ n * (L : ℝ) ^ n * δ)
        * exp (-(cZero * K / 2))) (Qop L (t : ℂ) A) := by
  have hℓ := half_le_ellHat_real L hL ht0 ht1
  have hℓ0 : 0 < ellHat L (t : ℂ) := by linarith
  have hR : 0 < ellHat L (t : ℂ) * K := by nlinarith
  have hP := norm_Psum_le_of_fastDecay L hR hM hδ hAM hA
  have h := fastDecay_Qop L hL ht0 ht1 hR hA hP
  refine FastDecay.mono L h le_rfl ?_
  have hc := cTwo52_pos.le
  have h1 := window_mul_le (n := n) hℓ hK hc
  have h2 := div_pow_le_two_mul (n := n) hℓ hc
  have he : exp (-(cZero * (ellHat L (t : ℂ) * K / 2) / ellHat L (t : ℂ))) = exp (-(cZero * K / 2)) := by
    congr 2; field_simp
  rw [he]
  have hLδ : 0 ≤ (L : ℝ) ^ n * δ := by positivity
  have hE0 : 0 ≤ exp (-(cZero * K / 2)) := (exp_pos _).le
  refine add_le_add le_rfl ?_
  calc ((2 * exp 1 * (ellHat L (t : ℂ) * K + 1)) ^ n * M + (L : ℝ) ^ n * δ)
        * ((cTwo52 / ellHat L (t : ℂ)) ^ n * exp (-(cZero * K / 2)))
      = (((2 * exp 1 * (ellHat L (t : ℂ) * K + 1)) ^ n * (cTwo52 / ellHat L (t : ℂ)) ^ n) * M
          + (cTwo52 / ellHat L (t : ℂ)) ^ n * ((L : ℝ) ^ n * δ)) * exp (-(cZero * K / 2)) := by ring
    _ ≤ ((6 * exp 1 * cTwo52 * K) ^ n * M + (2 * cTwo52) ^ n * ((L : ℝ) ^ n * δ))
          * exp (-(cZero * K / 2)) := by gcongr
    _ = _ := by ring

end TermBounds

section Master

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

end Master

/-! ### The generic `≺`-assembly of a time-integral term of (5.94) -/

section GenericTerms

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

end GenericTerms

/-! ### Lemma 5.14 for charges with a `(-,+)` pair away from slot `0`: the terms of (5.94) -/

section TermsQ

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

omit X in
theorem Psum_mul_left {L : ℕ} [NeZero L] {n : ℕ} (V : ZMod L → ℂ) (f : LoopArg L (n + 1) → ℂ)
    (x : ZMod L) : Psum L (fun b => V (b 0) * f b) x = V x * Psum L f x := by
  simp only [Psum, Fin.cons_zero, Finset.mul_sum]

theorem norm_xi2_le (hE : |E| < 2) {n : ℕ} (σ : Fin (n + 2) → Bool) (i : Fin ((n + 2) + (n + 2))) :
    ‖xi2 E σ i‖ ≤ 1 := by
  unfold xi2
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left]; exact (norm_xiOf_mSigma hE.le σ i).le
  | right i => rw [Fin.append_right]; exact (norm_xiOf_mSigma hE.le (fun j => !(σ j)) i).le

end TermsQ

section ScQ

end ScQ

section TermsQ2

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end TermsQ2


/-! ### Lemma 5.11 / Case 1 of (7.16): the non-alternating charges -/

section Short

variable (L : ℕ) [NeZero L]

end Short

section TermsShort

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- Charges with a repeated sign `σ_k = σ_{k+1}` (cyclically): the non-alternating `σ` of
(5.82), for which Case 1 of (7.16) applies (Lemma 5.11). -/
def NonAlt {n : ℕ} (σ : Fin (n + 2) → Bool) : Prop := ∃ k : Fin (n + 2), σ k = σ (k + 1)

instance {n : ℕ} : DecidablePred (NonAlt (n := n)) := fun σ => by
  unfold NonAlt; infer_instance

end TermsShort

/-! ### Assembly: Lemma 5.14 (5.92) for the flow -/

section Assembly

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Assembly

section WardDischarge

open Finset

section WardLists

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
/-- `G(z̄) G(z) = (2i Im z)⁻¹ (G(z) - G(z̄))`. -/
theorem Gf_mul_Gt {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    Gsig H z false * Gsig H z true
      = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gsig H z true - Gsig H z false) := by
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by simp [Complex.I_ne_zero, hz]
  have h := green_sub_green_conj' (isUnit_sub_smul_one_of_im_ne_zero hH hz)
    (isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hz))
  simp only [Gsig_true, Gsig_false]
  rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **Ward's identity for `G`-loops, at an interior label**: summing the label between `G(-)`
and `G(+)` merges them into `(2iW Im z)⁻¹ (G(+) - G(-))`. -/
theorem sum_gloop_ward_mid {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (σ₁ σ₂ : List Bool) (a₁ a₂ : List (ZMod L))
    (h₁ : σ₁.length = a₁.length) (c : ZMod L) :
    ∑ b : ZMod L, gloop L W H z ⟨σ₁ ++ false :: true :: σ₂, a₁ ++ b :: c :: a₂⟩
      = (gloop L W H z ⟨σ₁ ++ true :: σ₂, a₁ ++ c :: a₂⟩
          - gloop L W H z ⟨σ₁ ++ false :: σ₂, a₁ ++ c :: a₂⟩) / (2 * W * Complex.I * z.im) := by
  set P₁ := gloopProd L W H z ⟨σ₁, a₁⟩
  set P₂ := gloopProd L W H z ⟨σ₂, a₂⟩
  have hterm : ∀ b : ZMod L, gloop L W H z ⟨σ₁ ++ false :: true :: σ₂, a₁ ++ b :: c :: a₂⟩
      = Matrix.trace (P₁ * Gsig H z false * Eblk L W b * (Gsig H z true * Eblk L W c * P₂)) := by
    intro b
    rw [gloop, gloopProd_append h₁, gloopProd_cons, gloopProd_cons]
    simp only [Matrix.mul_assoc]
    rfl
  simp_rw [hterm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, sum_Eblk L W]
  have e1 : gloop L W H z ⟨σ₁ ++ true :: σ₂, a₁ ++ c :: a₂⟩
      = Matrix.trace (P₁ * (Gsig H z true * Eblk L W c * P₂)) := by
    rw [gloop, gloopProd_append h₁, gloopProd_cons]
  have e2 : gloop L W H z ⟨σ₁ ++ false :: σ₂, a₁ ++ c :: a₂⟩
      = Matrix.trace (P₁ * (Gsig H z false * Eblk L W c * P₂)) := by
    rw [gloop, gloopProd_append h₁, gloopProd_cons]
  rw [e1, e2]
  have hG := Gf_mul_Gt hH hz
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by simp [Complex.I_ne_zero, hz]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  have key : P₁ * Gsig H z false * ((W : ℂ)⁻¹ • (1 : Matrix _ _ ℂ))
      * (Gsig H z true * Eblk L W c * P₂)
      = ((W : ℂ)⁻¹ * (2 * Complex.I * (z.im : ℂ))⁻¹)
        • (P₁ * (Gsig H z true * Eblk L W c * P₂) - P₁ * (Gsig H z false * Eblk L W c * P₂)) := by
    calc P₁ * Gsig H z false * ((W : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) * (Gsig H z true * Eblk L W c * P₂)
        = (W : ℂ)⁻¹ • (P₁ * (Gsig H z false * Gsig H z true) * Eblk L W c * P₂) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by
          rw [hG]
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.sub_mul, Matrix.mul_sub,
            Matrix.mul_assoc]
  rw [key, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  field_simp

/-- Ward's identity for `G`-loops at the last label (between `G(-)` at the end and `G(+)` at the
start). -/
theorem sum_gloop_ward_last {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (μ : List Bool) (x : ZMod L) (a' : List (ZMod L))
    (hμ : μ.length = a'.length) :
    ∑ b : ZMod L, gloop L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩
      = (gloop L W H z ⟨true :: μ, x :: a'⟩ - gloop L W H z ⟨false :: μ, x :: a'⟩)
        / (2 * W * Complex.I * z.im) := by
  set P := gloopProd L W H z ⟨μ, a'⟩
  have hl : (true :: μ).length = (x :: a').length := by simp [hμ]
  have hterm : ∀ b : ZMod L, gloop L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩
      = Matrix.trace (Gsig H z false * Eblk L W b * (Gsig H z true * Eblk L W x * P)) := by
    intro b
    rw [gloop, show true :: μ ++ [false] = (true :: μ) ++ [false] from rfl,
      show x :: a' ++ [b] = (x :: a') ++ [b] from rfl, gloopProd_append hl, gloopProd_cons,
      gloopProd_cons, gloopProd_nil, Matrix.mul_one, Matrix.trace_mul_comm]
  simp_rw [hterm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, sum_Eblk L W]
  have e1 : gloop L W H z ⟨true :: μ, x :: a'⟩ = Matrix.trace (Gsig H z true * Eblk L W x * P) := by
    rw [gloop, gloopProd_cons]
  have e2 : gloop L W H z ⟨false :: μ, x :: a'⟩ = Matrix.trace (Gsig H z false * Eblk L W x * P) := by
    rw [gloop, gloopProd_cons]
  rw [e1, e2]
  have hG := Gf_mul_Gt hH hz
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by simp [Complex.I_ne_zero, hz]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  have key : Gsig H z false * ((W : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) * (Gsig H z true * Eblk L W x * P)
      = ((W : ℂ)⁻¹ * (2 * Complex.I * (z.im : ℂ))⁻¹)
        • (Gsig H z true * Eblk L W x * P - Gsig H z false * Eblk L W x * P) := by
    calc Gsig H z false * ((W : ℂ)⁻¹ • (1 : Matrix _ _ ℂ)) * (Gsig H z true * Eblk L W x * P)
        = (W : ℂ)⁻¹ • ((Gsig H z false * Gsig H z true) * Eblk L W x * P) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by
          rw [hG]
          simp only [Matrix.smul_mul, smul_smul, Matrix.sub_mul, Matrix.mul_assoc]
  rw [key, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  field_simp

end WardLists

section WardK

variable {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) [NeZero W] {E : ℝ} (hE : |E| < 2)
include hL hE

/-- The primitive loop is invariant under all rotations. -/
theorem Kgen_rotate_eq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (I : LoopIdx (ZMod L)) (hI : I.WF)
    (h2 : 2 ≤ I.length) (k : ℕ) :
    Kgen L W (mSigma E) t ⟨I.σ.rotate k, I.a.rotate k⟩ = Kgen L W (mSigma E) t I := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hJ : (⟨I.σ.rotate k, I.a.rotate k⟩ : LoopIdx (ZMod L)).WF := by
      simp [LoopIdx.WF, List.length_rotate]; exact hI
    have hJ2 : 2 ≤ (⟨I.σ.rotate k, I.a.rotate k⟩ : LoopIdx (ZMod L)).length := by
      simp [LoopIdx.length, List.length_rotate]; exact h2
    have e : (⟨I.σ.rotate (k + 1), I.a.rotate (k + 1)⟩ : LoopIdx (ZMod L))
        = (⟨I.σ.rotate k, I.a.rotate k⟩ : LoopIdx (ZMod L)).rot := by
      simp [LoopIdx.rot, List.rotate_rotate]
    rw [e, Kgen_rot hL W hE ht0 ht1 _ hJ hJ2, ih]

/-- Swapping two blocks of a loop. -/
theorem Kgen_append_comm {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (l₁ l₂ : List Bool)
    (m₁ m₂ : List (ZMod L)) (h₁ : l₁.length = m₁.length) (h₂ : l₂.length = m₂.length)
    (h2 : 2 ≤ m₁.length + m₂.length) :
    Kgen L W (mSigma E) t ⟨l₁ ++ l₂, m₁ ++ m₂⟩ = Kgen L W (mSigma E) t ⟨l₂ ++ l₁, m₂ ++ m₁⟩ := by
  have h := Kgen_rotate_eq hL W hE ht0 ht1 ⟨l₁ ++ l₂, m₁ ++ m₂⟩
    (by simp [LoopIdx.WF, h₁, h₂]) (by simpa [LoopIdx.length] using h2) l₁.length
  simp only at h
  rw [List.rotate_append_length_eq, h₁, List.rotate_append_length_eq] at h
  exact h.symm

/-- **Ward's identity for the primitive loop at an interior label** (from `ward_Kgen` and the
cyclic invariance). -/
theorem sum_Kgen_ward_mid {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (σ₁ σ₂ : List Bool)
    (a₁ a₂ : List (ZMod L)) (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length)
    (hne : 1 ≤ a₁.length) (c : ZMod L) :
    ∑ b : ZMod L, Kgen L W (mSigma E) t ⟨σ₁ ++ false :: true :: σ₂, a₁ ++ b :: c :: a₂⟩
      = (Kgen L W (mSigma E) t ⟨σ₁ ++ true :: σ₂, a₁ ++ c :: a₂⟩
          - Kgen L W (mSigma E) t ⟨σ₁ ++ false :: σ₂, a₁ ++ c :: a₂⟩) / (2 * W * Complex.I * etaT E t) := by
  have hterm : ∀ b : ZMod L, Kgen L W (mSigma E) t ⟨σ₁ ++ false :: true :: σ₂, a₁ ++ b :: c :: a₂⟩
      = Kgen L W (mSigma E) t ⟨true :: (σ₂ ++ σ₁) ++ [false], c :: (a₂ ++ a₁) ++ [b]⟩ := by
    intro b
    have := Kgen_append_comm hL W hE ht0 ht1 (σ₁ ++ [false]) (true :: σ₂) (a₁ ++ [b]) (c :: a₂)
      (by simp [h₁]) (by simp [h₂]) (by simp; omega)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this
    rw [this]
    simp [List.append_assoc]
  simp_rw [hterm]
  rw [ward_Kgen hL W hE ht0 ht1 (σ₂ ++ σ₁) (c :: (a₂ ++ a₁)) (by simp [h₁, h₂])]
  have hb : ∀ s : Bool, Kgen L W (mSigma E) t ⟨s :: (σ₂ ++ σ₁), c :: (a₂ ++ a₁)⟩
      = Kgen L W (mSigma E) t ⟨σ₁ ++ s :: σ₂, a₁ ++ c :: a₂⟩ := by
    intro s
    have := Kgen_append_comm hL W hE ht0 ht1 σ₁ (s :: σ₂) a₁ (c :: a₂) h₁ (by simp [h₂])
      (by simp; omega)
    rw [this]
    simp
  rw [hb true, hb false]

end WardK

section WardFlowProof

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

theorem zt_im_eq (E u : ℝ) : (zt E u).im = etaT E u := by
  simp [zt, etaT]

/-- Splitting a sum over label lists into two consecutive blocks. -/
theorem allSum_add {L : ℕ} [NeZero L] (p q : ℕ) (g : List (ZMod L) → ℂ) :
    allSum L (p + q) g = allSum L p (fun l₁ => allSum L q (fun l₂ => g (l₁ ++ l₂))) := by
  induction p generalizing g with
  | zero => rw [Nat.zero_add]; rfl
  | succ p ih =>
    rw [show p + 1 + q = (p + q) + 1 by ring]
    conv_lhs => rw [allSum]
    conv_rhs => rw [allSum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ih]
    simp only [List.cons_append]

theorem ofFn_getD_eq {m : ℕ} (l : List Bool) (h : l.length = m) :
    List.ofFn (fun i : Fin m => l.getD i false) = l := by
  refine List.ext_getElem (by simp [h]) fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getD_eq_getElem]

end WardFlowProof

end WardDischarge

section Discharged

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Discharged

end SumZeroDyn

end RBM
