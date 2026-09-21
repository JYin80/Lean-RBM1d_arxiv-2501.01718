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
# §5.5, the dynamical half: Lemma 5.14 (5.92)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, §5.4–5.5, equations (5.84)–(5.107) (pp. 64–70): the bound (5.92) on
`Ξ^{(L-K)}_{u,n}` along the flow, for every loop length `n ≥ 2`, in the form
`RBM.Step3.Lemma514` that Step 3 (`RBM.Step3.hyp_flow`, `RBM.Step3.flow_sharpLoop`) and
Steps 4–5 use.

The static half of §5.5 (the operator `Q_t`, `P`, `ϑ_t`, (5.89)–(5.90)) is
`RBM1D/Hierarchy/SumZero.lean`; the kernel bounds (7.16) for `U_{s,t,σ}` are
`RBM1D/Hierarchy/KernelDecay.lean`.  This file adds the time derivative of `Q_t` and the
dynamical estimates, and assembles them.

## Main results

* `RBM.SumZeroDyn.varthetaDot`, `hasDerivAt_vartheta`, `fastDecay_varthetaDot`:
  `ϑ̇_t` and its decay.
* `RBM.SumZeroDyn.norm_le_norm_Qop_add`: **(5.101)**, `|A| ≤ |Q_t A| + |P A · ϑ_t|`.
* `RBM.SumZeroDyn.genS`, `commS`, `commOp_eq`: the generator `Θ_{t,σ}` of (5.19) and the
  commutator `[Q_t, Θ_{t,σ}]` of **(5.99)**; `SumZero_commS`: it is sum-zero.
* `RBM.SumZeroDyn.hasDerivAt_Qop_hierarchy`: **(5.88)**, the equation for `Q_t ∘ (L-K)`.
* `RBM.SumZeroDyn.norm_Psum_le_of_ward`: **(5.96)** in abstract form.
* `RBM.SumZeroDyn.stochDom_of_logBound`: the master `≺`-lemma turning the pathwise bounds
  `(7.16)` + power counting into stochastic domination.
* `RBM.SumZeroDyn.QV_Q_stochDom`: **(5.103)–(5.105)**, the quadratic variation of the
  `Q_t`-martingale; `QV1_stochDom`: **(5.85)–(5.86)** (Case 1).
* `RBM.SumZeroDyn.bound_qGood`, `bound_nonAlt`: (5.94) for charges with a `(-,+)` pair
  away from slot `0` (`Q_t` route, (5.91)–(5.107)), and (5.84) for charges with a short edge
  `σ_k = σ_{k+1}` (Case 1 of (7.16), no `Q_t` needed).
* `RBM.SumZeroDyn.wardP_holds`: Ward's identity (Lemma 3.6) for the slot sums of `L - K`,
  the input of (5.96): `P ∘ (L-K)_σ = (2iWη_u)^{-1} (P ∘ (L-K)_{σ'} - P ∘ (L-K)_{σ''})`.
* `RBM.SumZeroDyn.lemma514_flow'` (and `lemma514_flow`, which takes Ward's identity as the
  hypothesis `hW`): **Lemma 5.14, (5.92)** for all `n ≥ 2`.

## Hypotheses (the interface)

* `RBM.SumZeroDyn.Hierarchy` — the random layer (CLAUDE.md rule 6): the integrated
  hierarchies **(5.20)** and **(5.91)** (Itô's formula + Lemma 5.3), and the BDG inequality
  with the quadratic variations (5.85) / (5.103), as structure fields `bdg` / `bdgQ`.  `bdg`
  is stated on an arbitrary decidable class `good` of charges, since Case 1 uses it only on
  the non-alternating charges.
* `RBM.SumZeroDyn.Lemma510` — **placeholder for Lemma 5.10 (5.77)** (T59): the drift `F` and
  `E ⊗ E` satisfy the power counts of (5.77) and have the `(u, τ, D)` decay property.
* `RBM.SumZeroDyn.LKDecay` — **placeholder for Lemma 5.9 (5.75)** (T59): `L - K` has the
  `(u, τ, D)` decay property uniformly in `u ∈ [s, t]`.
* (2.68) at time `s` (`hLmK`) and (2.72) (`RBM.Cond272`), as in Theorem 2.21.

The T59 results (`RBM.Decay`) do not plug into `Lemma510` / `LKDecay` directly: `F` and `EE`
are abstract fields of `Hierarchy` (the `E^{(G)}` term and the gluing defining `E ⊗ E` are not
concrete in the library), and `RBM.Decay.lemma59` holds on the event of Lemma 4.1 with the
(2.75)/(2.76) inputs, not as a `≺` statement uniform in `u ∈ [s, t]`.

## Deviations from the paper

* The generator is `ξ Θ_{tξ} S^{(B)}` (`genS`), with the `S^{(B)}` that (5.19) carries and
  that the printed (5.16) drops.  `RBM.ThetaOp` now carries it too, so `genS L ξ t` and
  `RBM.ThetaOp L ξ t` are definitionally equal; `genS` remains as the instance
  `Mᵢ = ξᵢ Θ^(B)_{tξᵢ} S^(B)` of the general slot-wise generator `genOp`, which is what the
  `Q_t` estimates below are actually stated for.
* Charges `σ` with no `(-,+)` pair away from slot `0` are handled as the paper handles them:
  non-alternating ones via Case 1 of (7.16) ((5.84)); the only remaining one, `σ = (-,+)`,
  by rotating the `2`-loop (`lkT_swap2`).
* The maxima on the right of (5.77) are replaced by sums (`xiRhs`); this is weaker than the
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

/-- **(5.101)**, pointwise: `A = Q_t ∘ A + (P ∘ A) ϑ_t`. -/
theorem norm_le_norm_Qop_add {n : ℕ} (t : ℂ) (A : LoopArg L (n + 1) → ℂ) (a : LoopArg L (n + 1)) :
    ‖A a‖ ≤ ‖Qop L t A a‖ + ‖Psum L A (a 0)‖ * ‖vartheta L t a‖ := by
  have h : A a = Qop L t A a + Psum L A (a 0) * vartheta L t a := by rw [Qop]; ring
  rw [h, ← norm_mul]
  exact norm_add_le _ _

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

The paper's (5.16) writes the generator as `∑ᵢ ξᵢ (1 - tξᵢ S^(B))^{-1}`; the generator of the
evolution kernel `U_{s,t,σ}` of (5.17) (and the operator that (5.19) identifies with the
`l_K = 2` term, by (2.57) and the factor `S^(B)_{ab}` of (5.14)) is `∑ᵢ ξᵢ Θ^(B)_{tξᵢ} S^(B)`,
consistent with (5.18).  We work with a general slot-wise generator
`(𝒢_M ∘ A)_a = ∑ᵢ ∑_c (Mᵢ)_{aᵢ c} A_{a^{(i)}}` (`genOp`), and `genS` is the case
`Mᵢ = ξᵢ Θ^(B)_{tξᵢ} S^(B)`.  Everything about `Q_t` only uses the row and column sums of the
`Mᵢ`.

`RBM.ThetaOp` has since been corrected to carry the `S^(B)`, so `genS L ξ t` is now
definitionally `RBM.ThetaOp L ξ t`; `genS` is kept as the `genOp` instance. -/

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

theorem genOp_add {n : ℕ} (M : Fin n → Matrix (ZMod L) (ZMod L) ℂ) (A B : LoopArg L n → ℂ) :
    genOp L M (A + B) = genOp L M A + genOp L M B := by
  funext a
  simp only [genOp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- **p. 66** for a general generator: the slot sums of `𝒢_M ∘ A`.  If the matrices of the
slots `i ≥ 2` have constant column sums `r_i`, the first slot contributes an `M₁`-average of
`P ∘ A` and every other slot contributes `r_i (P ∘ A)_{a₁}`. -/
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

/-- The sum-zero property is preserved by `𝒢_M` (p. 66). -/
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

/-- `genS` preserves the sum-zero property. -/
theorem SumZero_genS (hL : 3 ≤ L) {n : ℕ} {ξ : Fin (n + 1) → ℂ} {t : ℂ}
    (ht : ∀ i, ‖t * ξ i‖ < 1) {A : LoopArg L (n + 1) → ℂ} (hA : SumZero L A) :
    SumZero L (genS L ξ t A) :=
  SumZero_genOp L (genSM L ξ t) (fun j => ξ j.succ * (1 - t * ξ j.succ)⁻¹)
    (fun j c => sum_genSM_col L hL (ht j.succ) c) hA

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

theorem Qop_add {n : ℕ} (t : ℂ) (A B : LoopArg L (n + 1) → ℂ) :
    Qop L t (A + B) = Qop L t A + Qop L t B := by
  funext a
  simp only [Qop, Pi.add_apply, Psum_add]
  ring

theorem hasDerivAt_Psum {n : ℕ} {A : ℝ → LoopArg L (n + 1) → ℂ} {A' : LoopArg L (n + 1) → ℂ}
    {t : ℝ} (hA : ∀ b, HasDerivAt (fun u => A u b) (A' b) t) (x : ZMod L) :
    HasDerivAt (fun u => Psum L (A u) x) (Psum L A' x) t := by
  simp only [Psum]
  exact HasDerivAt.fun_sum fun r _ => hA _

/-- The time derivative of `Q_t ∘ A_t`: `∂_t (Q_t ∘ A_t) = Q_t ∘ ∂_t A_t - (P ∘ A_t) ϑ̇_t`.
This is where the extra term `-(P ∘ (L - K))·ϑ̇_t dt` of (5.88) comes from. -/
theorem hasDerivAt_Qop (hL : 3 ≤ L) {n : ℕ} {A : ℝ → LoopArg L (n + 1) → ℂ}
    {A' : LoopArg L (n + 1) → ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hA : ∀ b, HasDerivAt (fun u => A u b) (A' b) t) (a : LoopArg L (n + 1)) :
    HasDerivAt (fun u : ℝ => Qop L (u : ℂ) (A u) a)
      (Qop L (t : ℂ) A' a - Psum L (A t) (a 0) * varthetaDot L t a) t := by
  have h := (hA a).sub ((hasDerivAt_Psum L hA (a 0)).mul (hasDerivAt_vartheta L hL ht0 ht1 a))
  refine h.congr_deriv ?_
  simp only [Qop]
  ring

/-- **(5.88)** (the drift): if `∂_t D_t = Θ_{t,σ} ∘ D_t + F_t` (this is (5.15), with the
`l_K = 2` term written as the generator by (5.19)), then
`∂_t (Q_t ∘ D_t) = Θ_{t,σ} ∘ (Q_t ∘ D_t) + [Q_t, Θ_{t,σ}] ∘ D_t + Q_t ∘ F_t - (P ∘ D_t) ϑ̇_t`.
In the paper the equation also carries the martingale `Q_t ∘ E^{(M)}`, which is the random
input of the integrated form (5.91) (`RBM.SumZeroDyn.Hierarchy.duhamelQ`). -/
theorem hasDerivAt_Qop_hierarchy (hL : 3 ≤ L) {n : ℕ} {ξ : Fin (n + 1) → ℂ}
    {D : ℝ → LoopArg L (n + 1) → ℂ} {F : LoopArg L (n + 1) → ℂ} {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (hD : ∀ b, HasDerivAt (fun u => D u b) (genS L ξ (t : ℂ) (D t) b + F b) t)
    (a : LoopArg L (n + 1)) :
    HasDerivAt (fun u : ℝ => Qop L (u : ℂ) (D u) a)
      (genS L ξ (t : ℂ) (Qop L (t : ℂ) (D t)) a + commS L ξ (t : ℂ) (D t) a
        + Qop L (t : ℂ) F a - Psum L (D t) (a 0) * varthetaDot L t a) t := by
  refine (hasDerivAt_Qop L hL (A' := genS L ξ (t : ℂ) (D t) + F) ht0 ht1 hD a).congr_deriv ?_
  rw [Qop_add]
  simp only [Pi.add_apply, commS, commOp, genS, Pi.sub_apply]
  ring

end Hierarchy588

/-! ### The evolution kernel on the terms of (5.91): (5.93) and the time integrals -/

section KernelTerms

variable (L : ℕ) [NeZero L]

theorem cKerSumZero_nonneg (n : ℕ) : 0 ≤ cKerSumZero n := by
  unfold cKerSumZero; have := cWin_nonneg; have := cLip_nonneg; positivity

theorem cKerSumZeroErr_nonneg (n : ℕ) : 0 ≤ cKerSumZeroErr n := by
  unfold cKerSumZeroErr; have := cTwo52_pos; positivity

theorem cKerShort_nonneg (n : ℕ) {κ : ℝ} (hκ : 0 < κ) : 0 ≤ cKerShort n κ := by
  unfold cKerShort; have := cWin_nonneg; have := cShort_nonneg; positivity

/-- The time integral of `α (1-u)^{-1} + β` over `[s, v]`. -/
theorem norm_integral_le_log {f : ℝ → ℂ} {s v α β : ℝ} (hsv : s ≤ v) (hv1 : v < 1)
    (hf : ∀ u, s ≤ u → u ≤ v → ‖f u‖ ≤ α * (1 - u)⁻¹ + β) :
    ‖∫ u in s..v, f u‖ ≤ α * Real.log ((1 - s) / (1 - v)) + β * (v - s) := by
  have hcont : ContinuousOn (fun u : ℝ => α * (1 - u)⁻¹ + β) (Set.uIcc s v) := by
    refine ContinuousOn.add (ContinuousOn.mul continuousOn_const ?_) continuousOn_const
    refine ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun u hu => ?_
    rw [Set.uIcc_of_le hsv] at hu
    linarith [hu.2]
  have hint : IntervalIntegrable (fun u : ℝ => α * (1 - u)⁻¹ + β) MeasureTheory.volume s v :=
    hcont.intervalIntegrable
  have hle := intervalIntegral.norm_integral_le_of_norm_le hsv
    (MeasureTheory.ae_of_all _ fun u hu => hf u hu.1.le hu.2) hint
  refine hle.trans (le_of_eq ?_)
  have hinv : IntervalIntegrable (fun u : ℝ => (1 - u)⁻¹) MeasureTheory.volume s v := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun u hu => ?_
    rw [Set.uIcc_of_le hsv] at hu
    linarith [hu.2]
  rw [intervalIntegral.integral_add (hinv.const_mul α) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
  have hlog : ∫ u in s..v, (1 - u)⁻¹ = Real.log ((1 - s) / (1 - v)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) 1,
      integral_inv_of_pos (by linarith) (by linarith)]
  rw [hlog]
  ring

/-- The ratio `ℓ_uη_u/(ℓ_vη_v)` for `s ≤ u ≤ v` is at most `(1-s)/(1-v)`. -/
theorem ratio_le (hL : 3 ≤ L) {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv1 : v < 1) :
    (1 - u) * ellHat L (u : ℂ) / ((1 - v) * ellHat L (v : ℂ)) ≤ (1 - s) / (1 - v) := by
  have hv := ellHat_real_pos' L hL (hs0.trans (hsu.trans huv)) hv1
  have h1v : 0 < 1 - v := by linarith
  rw [div_le_div_iff₀ (by positivity) h1v]
  have h1 : ellHat L (u : ℂ) ≤ ellHat L (v : ℂ) := ellHat_real_mono L huv hv1
  have h2 : 0 ≤ 1 - u := by linarith
  have h3 : (1 - u) * ellHat L (u : ℂ) ≤ (1 - s) * ellHat L (v : ℂ) :=
    mul_le_mul (by linarith) h1 (ellHat_real_pos' L hL (hs0.trans hsu) (huv.trans_lt hv1)).le
      (by linarith)
  nlinarith

/-- `(1-u)/(1-v) ≤ (1-s)/(1-v)` for `s ≤ u`. -/
theorem one_sub_div_le {s u v : ℝ} (hsu : s ≤ u) (hv1 : v < 1) :
    (1 - u) / (1 - v) ≤ (1 - s) / (1 - v) :=
  div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- **(5.93) on one term**, Case 2 of (7.16): for a sum-zero `(ℓ_u K, δ)`-fast-decaying tensor
bounded by `A_u^{-m} ψ' + ζ` (`A_u = c (1-u) ℓ_u`, the scale `W ℓ_u η_u`),
`|U_{u,v,σ} ∘ G| ≤ C_m K^{2m} A_v^{-m} ψ' + C_m K^{2m} ρ^m ζ + C'_m L^m ρ^m δ`,
`ρ = (1-s)/(1-v)`. -/
theorem norm_Uker_sumZero_scale_le (hL : 3 ≤ L) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2)
    (σ : Fin (n + 2) → Bool) {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v)
    (hv0 : 0 ≤ v) (hv1 : v < 1) {κA : ℝ} (hκA : 0 < κA) {K ψ ζ δ : ℝ} (hK : 1 ≤ K)
    (hψ : 0 ≤ ψ) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ) {G : LoopArg L (n + 2) → ℂ}
    (hGM : ∀ b, ‖G b‖ ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ + ζ)
    (hG : FastDecay L (ellHat L (u : ℂ) * K) δ G) (hz : SumZero L G) (a : LoopArg L (n + 2)) :
    ‖Uker L (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) G a‖
      ≤ cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * ψ
        + (cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * δ) := by
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓu := ellHat_real_pos' L hL hu0 hu1
  have hℓv := ellHat_real_pos' L hL (hu0.trans huv) hv1
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hM0 : 0 ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ + ζ := by positivity
  have key := norm_Uker_fastDecay_le_sumZero_sigma L (n := n + 2) (by omega) hL hE σ hu0 huv
    hv0 hv1 hK hM0 hδ hGM hG (sumZeroAt_zero_of_sumZero L hz) a
  · refine key.trans ?_
    set r := (1 - u) * ellHat L (u : ℂ) / ((1 - v) * ellHat L (v : ℂ)) with hr
    have hr0 : 0 ≤ r := by positivity
    have hrρ : r ≤ (1 - s) / (1 - v) := ratio_le L hL hs0 hsu huv hv1
    have hq : (1 - u) / (1 - v) ≤ (1 - s) / (1 - v) := one_sub_div_le hsu hv1
    have hcancel : r ^ (n + 2) * (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2)
        = (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) := by
      rw [← mul_pow]; congr 1; rw [hr]; field_simp
    have hc := cKerSumZero_nonneg (n + 2)
    have hc' := cKerSumZeroErr_nonneg (n + 2)
    have hK0 : 0 ≤ K ^ (2 * (n + 2)) := by positivity
    have e1 : cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * r ^ (n + 2)
        * ((κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ + ζ)
        = cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * ψ
          + cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * r ^ (n + 2) * ζ := by
      rw [← hcancel]; ring
    rw [e1, add_assoc]
    refine add_le_add le_rfl (add_le_add ?_ ?_)
    · gcongr
    · gcongr

end KernelTerms

/-! ### `≺`: the good-event pattern, and the crude scale bounds of the flow -/

section StochHelpers

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- **The good-event pattern**: if for every `τ > 0` there is a high-probability event on which
`ξ ≤ N^τ ζ` (eventually, uniformly in the parameter), then `ξ ≺ ζ`. -/
theorem stochDom_of_good {ξ ζ : ∀ N, U N → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), ∃ G : ℕ → Set Ω, HighProb P G ∧
      ∀ᶠ N : ℕ in atTop, ∀ ω ∈ G N, ∀ u, ξ N u ω ≤ (N : ℝ) ^ τ * ζ N u ω) :
    StochDom P ξ ζ := by
  intro τ hτ D hD
  obtain ⟨G, hG, hle⟩ := h τ hτ
  filter_upwards [hG D hD, hle] with N hN hle
  refine (measure_mono fun ω hω => ?_).trans hN
  obtain ⟨u, hu⟩ := hω
  intro hωG
  exact absurd (hle ω hωG u) (not_le.2 hu)

/-- The good event of a `≺`-bound. -/
theorem good_of_stochDom {ξ ζ : ∀ N, U N → Ω → ℝ} (h : StochDom P ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProb P fun N => {ω | ∀ u, ξ N u ω ≤ (N : ℝ) ^ τ * ζ N u ω} :=
  h.highProb hτ

/-- `N^a N^b = N^{a+b}` for the natural-number base. -/
theorem natCast_rpow_add (N : ℕ) (hN : 1 ≤ N) (a b : ℝ) :
    (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) ^ (a + b) := by
  rw [Real.rpow_add (by exact_mod_cast hN)]

/-- A constant times `N^a` is eventually below `N^b` for `a < b`. -/
theorem eventually_const_mul_rpow_le (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  filter_upwards [eventually_le_rpow C (sub_pos.2 hab), eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  calc C * (N : ℝ) ^ a ≤ (N : ℝ) ^ (b - a) * (N : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ b := by rw [← Real.rpow_add hN0]; ring_nf

/-- `log N ≤ N^ε / ε`. -/
theorem log_le_rpow_div_nat (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Real.log N ≤ (N : ℝ) ^ ε / ε :=
  Real.log_le_rpow_div (Nat.cast_nonneg N) hε

end StochHelpers

section FlowScales

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

theorem Band.scale_eq (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ) :
    B.scale E N u = ((B.W N : ℝ) * (mE E).im) * ((1 - u) * ellHat (B.L N) (u : ℂ)) := by
  simp only [Band.scale, Band.ell, etaT]; ring

theorem ellHat_real_le_L {L : ℕ} {u : ℝ} (hu1 : u < 1) : ellHat L (u : ℂ) ≤ L := by
  rw [ellHat_ofReal L hu1]; exact min_le_right _ _

/-- **Crude bounds on the scales of the flow**: eventually in `N`, uniformly in `u ∈ [s,t]`,
`1 ≤ W ℓ_u η_u ≤ N`, `L, W ≤ N` and `(1-u)^{-1} ≤ N`.  (From (2.72) and `W L ≤ N`.) -/
theorem flow_crude (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) :
    ∀ᶠ N : ℕ in atTop, (B.L N : ℝ) ≤ N ∧ (B.W N : ℝ) ≤ N ∧ 1 ≤ N ∧
      ∀ u : TimeIcc s t N, 1 ≤ B.scale E N u ∧ B.scale E N u ≤ N ∧ (1 - (u : ℝ))⁻¹ ≤ N := by
  have sc := Step3.scales_flow (B := B) hE hs0 hst ht1 hc
  filter_upwards [B.dim, sc.one_le_As, sc.one_le_R, sc.le_A, eventually_ge_atTop 1] with
    N hdim hAs hR hle hN1
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hL1 : (1 : ℝ) ≤ B.L N := by have := B.three_le_L N; exact_mod_cast (by omega : 1 ≤ B.L N)
  have hWL : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
  have hLN : (B.L N : ℝ) ≤ N := by nlinarith
  have hWN : (B.W N : ℝ) ≤ N := by nlinarith
  refine ⟨hLN, hWN, by exact_mod_cast hN1, fun u => ?_⟩
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hA1 : 1 ≤ B.scale E N u := by
    have h4 := hle u
    have h5 : 1 ≤ Step3.flowR B s t N ^ 2 := one_le_pow₀ hR
    have h6 : 1 ≤ Step3.flowAs B E s N ^ ((3 : ℝ) / 4) := Real.one_le_rpow hAs (by norm_num)
    have : 1 ≤ Step3.flowR B s t N ^ 2 * Step3.flowAs B E s N ^ ((3 : ℝ) / 4) := by nlinarith
    exact this.trans h4
  have him := mE_im_le_one hE
  have him0 := mE_im_pos hE
  have hℓ := ellHat_real_le_L (L := B.L N) hu1
  have hℓ0 := Step3.ellHat_pos_of_lt_one (L := B.L N) (by have := B.three_le_L N; omega) hu1
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have hscale := Band.scale_eq B E N u
  refine ⟨hA1, ?_, ?_⟩
  · rw [hscale]
    have h1 : (1 - (u : ℝ)) * ellHat (B.L N) (u : ℂ) ≤ B.L N := by nlinarith
    have h2 : (B.W N : ℝ) * (mE E).im ≤ B.W N := by nlinarith
    calc (B.W N : ℝ) * (mE E).im * ((1 - (u : ℝ)) * ellHat (B.L N) (u : ℂ))
        ≤ B.W N * B.L N := mul_le_mul h2 h1 (by positivity) (by positivity)
      _ ≤ N := hWL
  · rw [inv_le_iff_one_le_mul₀ h1u]
    rw [hscale] at hA1
    have h1 : (B.W N : ℝ) * (mE E).im * ellHat (B.L N) (u : ℂ) ≤ N := by
      calc (B.W N : ℝ) * (mE E).im * ellHat (B.L N) (u : ℂ) ≤ B.W N * 1 * B.L N := by gcongr
        _ ≤ N := by linarith
    nlinarith

end FlowScales

/-! ### The random-layer interface

The loop tensors of the flow are `lkT X E N u ω σ a = (L - K)_{u,σ,a}`, for charges
`σ : Fin m → Bool` and labels `a : LoopArg (L N) m` (the representation bridge `LoopArg ↔
LoopIdx` is just `LoopData.idx = ⟨List.ofFn σ, List.ofFn a⟩`).  The Itô-calculus inputs of §5.5
are the fields of `RBM.SumZeroDyn.Hierarchy`; the power counts of Lemma 5.10 and the decay of
Lemma 5.9 (T59) are the fields of `RBM.SumZeroDyn.Lemma510` and `RBM.SumZeroDyn.LKDecay`. -/

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

theorem norm_lkT_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) : ‖lkT X E N u ω σ a‖ ≤ X.lkMax E N u ω m :=
  X.lkErr_le_lkMax (σ, a)

open Classical in
/-- The indicator that two labels are at distance `≥ R` (the event of (5.74)). -/
noncomputable def farInd (L : ℕ) {m : ℕ} (R : ℝ) (a : LoopArg L m) : ℝ :=
  if ∃ i j, R ≤ (zdist L (a i - a j) : ℝ) then 1 else 0

theorem fastDecay_of_farInd {L : ℕ} {m : ℕ} {R δ : ℝ} {A : LoopArg L m → ℂ}
    (h : ∀ a, ‖A a‖ * farInd L R a ≤ δ) : FastDecay L R δ A := by
  intro a ha
  have := h a
  simpa [farInd, ha] using this

/-- `(Q_t ⊗ Q_t)` of (5.104), acting on a two-slot tensor written as a `(2m)`-tensor. -/
noncomputable def QQ (L : ℕ) [NeZero L] {n : ℕ} (t : ℂ)
    (Bt : LoopArg L ((n + 1) + (n + 1)) → ℂ) : LoopArg L ((n + 1) + (n + 1)) → ℂ :=
  fun c => Qop₁ L t (Qop₂ L t (fun a b => Bt (Fin.append a b)))
    (fun i => c (Fin.castAdd (n + 1) i)) (fun i => c (Fin.natAdd (n + 1) i))

/-- The edge parameters `(ξ, ξ)` of the doubled loop in (5.85), (5.103). -/
noncomputable def xi2 (E : ℝ) {n : ℕ} (σ : Fin (n + 2) → Bool) : Fin ((n + 2) + (n + 2)) → ℂ :=
  Fin.append (xiOf (mSigma E) σ) (xiOf (mSigma E) σ)

/-- **The random-layer inputs of §5.5 for loops of length `n + 2`.**

* `F` is the drift of (5.15) other than the `l_K = 2` term:
  `∑_{l_K > 2} [K ∼ (L-K)]^{l_K} + E^{((L-K)×(L-K))} + E^{(G)}`;
* `EE` is `E ⊗ E` of Definition 5.4, as a `2(n+2)`-tensor;
* `mart`, `martQ` are the martingale terms `∫_s^v U_{u,v,σ} ∘ E^{(M)}_u` of (5.20) and
  `∫_s^v U_{u,v,σ} ∘ Q_u ∘ E^{(M)}_u` of (5.91).

The fields are
* `duhamel` — **(5.20)** (Lemma 5.3 applied to (5.15));
* `duhamelQ` — **(5.91)** (Lemma 5.3 applied to (5.88); the drift of (5.88) is
  `RBM.SumZeroDyn.hasDerivAt_Qop_hierarchy`, the generator is `genS` and the commutator
  `commS`);
* `bdg`, `bdgQ` — **(5.85)**, **(5.103)** with the BDG inequality: if the integrand of the
  quadratic-variation bound, `((U_{u,v} ⊗ U_{u,v}) ∘ (E ⊗ E)_u)_{a,a}` (resp. with
  `Q_u ⊗ Q_u`), is `≺ Γ(v,σ,a) w(u,v)` uniformly in `s ≤ u ≤ v ≤ t` (and, for `bdg`, in the
  charges `σ` of a class `good`), then the martingale is `≺ (Γ ∫_s^v w)^{1/2}` (on that class).

These are the only places where the stochastic calculus enters. -/
structure Hierarchy (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) where
  /-- The drift of (5.15) without the `l_K = 2` term. -/
  F : ∀ N, ℝ → Ω → (Fin (n + 2) → Bool) → LoopArg (B.L N) (n + 2) → ℂ
  /-- `E ⊗ E` of Definition 5.4. -/
  EE : ∀ N, ℝ → Ω → (Fin (n + 2) → Bool) → LoopArg (B.L N) ((n + 2) + (n + 2)) → ℂ
  /-- The martingale term of (5.20). -/
  mart : ∀ N, ℝ → Ω → (Fin (n + 2) → Bool) → LoopArg (B.L N) (n + 2) → ℂ
  /-- The martingale term of (5.91). -/
  martQ : ∀ N, ℝ → Ω → (Fin (n + 2) → Bool) → LoopArg (B.L N) (n + 2) → ℂ
  /-- **(5.20)**, the integrated hierarchy. -/
  duhamel : ∀ N ω (σ : Fin (n + 2) → Bool) (v : ℝ), s N ≤ v → v ≤ t N →
    ∀ a, lkT X E N v ω σ a
      = Uker (B.L N) (xiOf (mSigma E) σ) (s N : ℂ) (v : ℂ) (lkT X E N (s N) ω σ) a
        + (∫ u in (s N)..v, Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) (F N u ω σ) a)
        + mart N v ω σ a
  /-- **(5.91)**, the integrated `Q_t ∘ (L - K)` hierarchy (seven terms). -/
  duhamelQ : ∀ N ω (σ : Fin (n + 2) → Bool) (v : ℝ), s N ≤ v → v ≤ t N →
    ∀ a, Qop (B.L N) (v : ℂ) (lkT X E N v ω σ) a
      = Uker (B.L N) (xiOf (mSigma E) σ) (s N : ℂ) (v : ℂ)
          (Qop (B.L N) (s N : ℂ) (lkT X E N (s N) ω σ)) a
        + (∫ u in (s N)..v, Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ)
            (Qop (B.L N) (u : ℂ) (F N u ω σ)) a)
        + martQ N v ω σ a
        + (∫ u in (s N)..v, Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ)
            (commS (B.L N) (xiOf (mSigma E) σ) (u : ℂ) (lkT X E N u ω σ)) a)
        - (∫ u in (s N)..v, Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ)
            (fun b => Psum (B.L N) (lkT X E N u ω σ) (b 0) * varthetaDot (B.L N) u b) a)
  /-- **(5.85) + BDG**: the martingale of (5.20), for the charges in any class `good`. -/
  bdg : ∀ (good : (Fin (n + 2) → Bool) → Prop) [DecidablePred good]
    (Γ : ∀ N, TimeIcc s t N × LoopData (B.L N) (n + 2) → ℝ) (w : ℕ → ℝ → ℝ → ℝ),
    (∀ N p, 0 ≤ Γ N p) → (∀ N u v, s N ≤ u → u ≤ v → v ≤ t N → 0 ≤ w N u v) →
    (∀ N (v : ℝ), s N ≤ v → v ≤ t N → IntervalIntegrable (fun u => w N u v) volume (s N) v) →
    StochDom B.P
      (fun N (q : TimeIcc s t N × (TimeIcc s t N × LoopData (B.L N) (n + 2))) ω =>
        if (q.1 : ℝ) ≤ q.2.1 ∧ good q.2.2.1 then
          ‖Uker (B.L N) (xi2 E q.2.2.1) ((q.1 : ℝ) : ℂ) ((q.2.1 : ℝ) : ℂ)
            (EE N q.1 ω q.2.2.1) (Fin.append q.2.2.2 q.2.2.2)‖
        else 0)
      (fun N q _ => Γ N q.2 * w N q.1 q.2.1) →
    StochDom B.P (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
        if good p.2.1 then ‖mart N p.1 ω p.2.1 p.2.2‖ else 0)
      (fun N p _ => (Γ N p * ∫ u in (s N)..(p.1 : ℝ), w N u p.1) ^ ((1 : ℝ) / 2))
  /-- **(5.103) + BDG**: the martingale of (5.91). -/
  bdgQ : ∀ (Γ : ∀ N, TimeIcc s t N × LoopData (B.L N) (n + 2) → ℝ) (w : ℕ → ℝ → ℝ → ℝ),
    (∀ N p, 0 ≤ Γ N p) → (∀ N u v, s N ≤ u → u ≤ v → v ≤ t N → 0 ≤ w N u v) →
    (∀ N (v : ℝ), s N ≤ v → v ≤ t N → IntervalIntegrable (fun u => w N u v) volume (s N) v) →
    StochDom B.P
      (fun N (q : TimeIcc s t N × (TimeIcc s t N × LoopData (B.L N) (n + 2))) ω =>
        if (q.1 : ℝ) ≤ q.2.1 then
          ‖Uker (B.L N) (xi2 E q.2.2.1) ((q.1 : ℝ) : ℂ) ((q.2.1 : ℝ) : ℂ)
            (QQ (B.L N) ((q.1 : ℝ) : ℂ) (EE N q.1 ω q.2.2.1)) (Fin.append q.2.2.2 q.2.2.2)‖
        else 0)
      (fun N q _ => Γ N q.2 * w N q.1 q.2.1) →
    StochDom B.P (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
        ‖martQ N p.1 ω p.2.1 p.2.2‖)
      (fun N p _ => (Γ N p * ∫ u in (s N)..(p.1 : ℝ), w N u p.1) ^ ((1 : ℝ) / 2))

/-- The right side of (5.77) for the drift at loop length `m`:
`∑_{k<m} Ξ^{(L-K)}_{u,k} + ∑_{2≤k≤m} Ξ^{(L-K)}_{u,k} Ξ^{(L-K)}_{u,m-k+2} (Wℓ_uη_u)^{-1} + Ξ^{(L)}_{u,m+1}`
(sums in place of the paper's maxima). -/
noncomputable def xiRhs (X : Sample B) (E : ℝ) (m N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Ico 1 m, X.xiLK E N u ω k
    + ∑ k ∈ Finset.Icc 2 m, X.xiLK E N u ω k * X.xiLK E N u ω (m - k + 2) * (B.scale E N u)⁻¹
    + X.xiL E N u ω (m + 1)

/-- **Placeholder for Lemma 5.10 (5.77)** (T59), in the shape used here: the drift `F` and
`E ⊗ E` obey the power counts of (5.77) uniformly in `u ∈ [s,t]`, and both have the
`(u, τ, D)` decay property (for every `τ, D > 0`, with the radius `ℓ_u N^τ` and the error
`N^{-D}`). -/
structure Lemma510 (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) {n : ℕ} (H : Hierarchy X E s t n) :
    Prop where
  /-- (5.77), lines 1–3 summed: `F ≺ Ξ-terms · (Wℓ_uη_u)^{-m} η_u^{-1}`. -/
  F_le : StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω => ‖H.F N p.1 ω p.2.1 p.2.2‖)
    (fun N p ω => (B.scale E N p.1)⁻¹ ^ (n + 2) * (etaT E p.1)⁻¹ * xiRhs X E (n + 2) N p.1 ω)
  /-- The decay of the drift. -/
  F_decay : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      ‖H.F N p.1 ω p.2.1 p.2.2‖ * farInd (B.L N) (B.ell N p.1 * (N : ℝ) ^ τ) p.2.2)
    (fun N _ _ => (N : ℝ) ^ (-D))
  /-- (5.77), line 4: `E ⊗ E ≺ Ξ^{(L)}_{u,2m+2} (Wℓ_uη_u)^{-2m} η_u^{-1}`. -/
  EE_le : StochDom B.P
    (fun N (p : TimeIcc s t N × ((Fin (n + 2) → Bool) × LoopArg (B.L N) ((n + 2) + (n + 2)))) ω =>
      ‖H.EE N p.1 ω p.2.1 p.2.2‖)
    (fun N p ω => (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) * (etaT E p.1)⁻¹
      * X.xiL E N p.1 ω (2 * (n + 2) + 2))
  /-- The decay of `E ⊗ E` (in all `2m` labels). -/
  EE_decay : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), StochDom B.P
    (fun N (p : TimeIcc s t N × ((Fin (n + 2) → Bool) × LoopArg (B.L N) ((n + 2) + (n + 2)))) ω =>
      ‖H.EE N p.1 ω p.2.1 p.2.2‖ * farInd (B.L N) (B.ell N p.1 * (N : ℝ) ^ τ) p.2.2)
    (fun N _ _ => (N : ℝ) ^ (-D))

/-- **Placeholder for Lemma 5.9 (5.75)** (T59): `L - K` has the `(u, τ, D)` decay property at
every loop length, uniformly in `u ∈ [s,t]`. -/
def LKDecay (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ m, 1 ≤ m → ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω =>
      X.lkErr E N p.1 ω p.2.idx * farInd (B.L N) (B.ell N p.1 * (N : ℝ) ^ τ) p.2.2)
    (fun N _ _ => (N : ℝ) ^ (-D))

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

/-- The charges for which the proof of Lemma 5.14 uses `Q_t`: a cyclic pair
`(σ_j, σ_{j+1}) = (-, +)` at a slot `j` other than the first (whose label `P` keeps fixed).
Every alternating `σ` of length `≥ 4`, and `(+,-)`, is of this kind. -/
def QGood {n : ℕ} (σ : Fin (n + 2) → Bool) : Prop :=
  ∃ j : Fin (n + 2), j ≠ 0 ∧ σ j = false ∧ σ (j + 1) = true

instance {n : ℕ} : DecidablePred (QGood (n := n)) := fun σ => by
  unfold QGood; infer_instance

/-- **Ward's identity (Lemma 3.6) for the slot sums of `L - K`**, the input of (5.96): for
`QGood` charges, summing the label between `G(-)` and `G(+)` gives
`P ∘ (L-K)_{σ} = κ_u (P ∘ (L-K)_{σ'} - P ∘ (L-K)_{σ''})` with `κ_u = (2iWη_u)^{-1}` and loops
`σ', σ''` of one less length. -/
def WardP (X : Sample B) (E : ℝ) (n : ℕ) : Prop :=
  ∀ σ : Fin (n + 2) → Bool, QGood σ → ∃ σ' σ'' : Fin (n + 1) → Bool,
    ∀ N (u : ℝ), 0 ≤ u → u < 1 → ∀ ω x,
      Psum (B.L N) (lkT X E N u ω σ) x
        = wardKappa (B.W N) E u
          * (Psum (B.L N) (lkT X E N u ω σ') x - Psum (B.L N) (lkT X E N u ω σ'') x)

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

omit [NeZero L] in
theorem FastDecay.block2 {m m' : ℕ} {R δ : ℝ} {Bc : LoopArg L (m + m') → ℂ}
    (h : FastDecay L R δ Bc) (a : LoopArg L m) :
    FastDecay L R δ (fun b' => Bc (Fin.append a b')) := by
  intro b ⟨i, j, hij⟩
  refine h _ ⟨Fin.natAdd m i, Fin.natAdd m j, ?_⟩
  simpa [Fin.append_right] using hij

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

omit [NeZero L] in
theorem norm_swapT {m : ℕ} (X : LoopArg L (m + m) → ℂ) {e : ℝ} (h : ∀ c, ‖X c‖ ≤ e)
    (c : LoopArg L (m + m)) : ‖swapT L X c‖ ≤ e := h _

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

/-- The power counting of the term `(P ∘ (L-K)_v) ϑ_v` of (5.101). -/
theorem scalarP {n : ℕ} {A W η ℓ Lr K Φ δ c : ℝ} (hA : A = W * ℓ * η) (hW : 0 < W)
    (hη : 0 < η) (hℓ : 1 / 2 ≤ ℓ) (hK : 1 ≤ K) (hΦ : 0 ≤ Φ) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hL : 0 ≤ Lr) :
    A ^ (n + 2) * (((2 * W * η)⁻¹ * (2 * ((2 * exp 1 * (ℓ * K + 1)) ^ n * (K * Φ * A⁻¹ ^ (n + 1))
        + Lr ^ n * δ))) * (c / ℓ) ^ (n + 1))
      ≤ (6 * exp 1) ^ n * c ^ (n + 1) * K ^ (n + 1) * Φ
        + 2 ^ n * c ^ (n + 1) * A ^ (n + 1) * Lr ^ n * δ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hA0 : 0 < A := by rw [hA]; positivity
  set ι := ℓ⁻¹ with hι
  set α := A⁻¹ with hα
  have hℓι : ℓ * ι = 1 := mul_inv_cancel₀ hℓ0.ne'
  have hAα : A * α = 1 := mul_inv_cancel₀ hA0.ne'
  have hWη : A * (W * η)⁻¹ * ι = 1 := by
    rw [hA, hι]; field_simp
  have hι2 : ι ≤ 2 := by rw [hι]; rw [inv_le_comm₀ hℓ0 (by norm_num)]; linarith
  have hι0 : 0 ≤ ι := by positivity
  have e1 : (2 * exp 1 * (ℓ * K + 1)) ^ n = ℓ ^ n * (2 * exp 1 * (K + ι)) ^ n := by
    rw [← mul_pow]; congr 1
    have : ℓ * ι = 1 := hℓι
    linear_combination (-(2 * exp 1)) * this
  have hdiv : (c / ℓ) = c * ι := by rw [hι, div_eq_mul_inv]
  rw [e1, hdiv]
  have e2 : A ^ (n + 2) * (((2 * W * η)⁻¹ * (2 * (ℓ ^ n * (2 * exp 1 * (K + ι)) ^ n
        * (K * Φ * α ^ (n + 1)) + Lr ^ n * δ))) * (c * ι) ^ (n + 1))
      = (A * (W * η)⁻¹ * ι) * (A * α) ^ (n + 1) * (ℓ * ι) ^ n
          * (2 * exp 1 * (K + ι)) ^ n * c ^ (n + 1) * K * Φ
        + (A * (W * η)⁻¹ * ι) * ι ^ n * c ^ (n + 1) * A ^ (n + 1) * Lr ^ n * δ := by
    ring
  rw [e2, hWη, hAα, hℓι, one_pow, one_pow]
  have h3 : (2 * exp 1 * (K + ι)) ^ n ≤ (6 * exp 1) ^ n * K ^ n := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    have : 0 ≤ 2 * K - ι := by linarith
    nlinarith [mul_nonneg (exp_pos 1).le this]
  have h4 : ι ^ n ≤ 2 ^ n := pow_le_pow_left₀ hι0 hι2 n
  have hc1 : 0 ≤ c ^ (n + 1) := by positivity
  have hK1 : 0 ≤ K := by linarith
  have := mul_le_mul_of_nonneg_right h3 (mul_nonneg (mul_nonneg hc1 hK1) hΦ)
  have := mul_le_mul_of_nonneg_right h4 (mul_nonneg (mul_nonneg (mul_nonneg hc1 (pow_nonneg hA0.le (n+1))) (pow_nonneg hL n)) hδ)
  calc 1 * 1 * 1 * (2 * exp 1 * (K + ι)) ^ n * c ^ (n + 1) * K * Φ
        + 1 * ι ^ n * c ^ (n + 1) * A ^ (n + 1) * Lr ^ n * δ
      ≤ (6 * exp 1) ^ n * K ^ n * (c ^ (n + 1) * K * Φ)
        + 2 ^ n * (c ^ (n + 1) * A ^ (n + 1) * Lr ^ n * δ) := by nlinarith
    _ = _ := by ring

open Filter in
/-- The two eventual inequalities that close every term: `C N^a ≤ N^τ` for `a < τ` and
`C' N^b N^{-D} ≤ 1` for `b < D`. -/
theorem eventually_finish (C C' : ℝ) {a τ b D : ℝ} (ha : a < τ) (hb : b < D) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ a ≤ (N : ℝ) ^ τ ∧ C' * (N : ℝ) ^ b * (N : ℝ) ^ (-D) ≤ 1 := by
  filter_upwards [eventually_const_mul_rpow_le C ha, eventually_const_mul_rpow_le C' (show b < D from hb),
    eventually_ge_atTop 1] with N h1 h2 hN1
  refine ⟨h1, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  calc C' * (N : ℝ) ^ b * (N : ℝ) ^ (-D) ≤ (N : ℝ) ^ D * (N : ℝ) ^ (-D) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hN0.le _)
    _ = 1 := by rw [← Real.rpow_add hN0]; simp

theorem natCast_pow_le_rpow {N : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ N) (k : ℕ) :
    x ^ k ≤ (N : ℝ) ^ (k : ℝ) := by
  rw [Real.rpow_natCast]; exact pow_le_pow_left₀ hx0 hx k

theorem rpow_pow_eq (N : ℕ) (a : ℝ) (k : ℕ) : ((N : ℝ) ^ a) ^ k = (N : ℝ) ^ (a * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]

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

/-- A finite sum of `≺ ζ` quantities is `≺ (#S) ζ`. -/
theorem stochDom_finset_sum {ι : Type*} (S : Finset ι) {ξ : ι → ∀ N, U N → Ω → ℝ}
    {ζ : ∀ N, U N → Ω → ℝ} (h : ∀ i ∈ S, StochDom P (ξ i) ζ) :
    StochDom P (fun N u ω => ∑ i ∈ S, ξ i N u ω) (fun N u ω => (S.card : ℝ) * ζ N u ω) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact StochDom.refl fun _ _ _ => le_rfl
  | insert i S hi ih =>
    have h1 := h i (Finset.mem_insert_self i S)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have h3 := h1.add h2
    have e1 : (fun N u ω => ∑ j ∈ insert i S, ξ j N u ω)
        = ξ i + fun N u ω => ∑ j ∈ S, ξ j N u ω := by
      funext N u ω; simp [Finset.sum_insert hi]
    have e2 : (fun N u ω => ((insert i S).card : ℝ) * ζ N u ω)
        = ζ + fun N u ω => (S.card : ℝ) * ζ N u ω := by
      funext N u ω; simp only [Pi.add_apply]; rw [Finset.card_insert_of_notMem hi]; push_cast; ring
    rw [e1, e2]; exact h3

end StochSums

/-- The polynomial bookkeeping of the error terms of (5.94). -/
theorem err_scalar {m : ℕ} {A ρ Lr K c₀ Nr ε ck ce x : ℝ} (hA0 : 0 ≤ A) (hAN : A ≤ Nr)
    (hρ0 : 0 ≤ ρ) (hρN : ρ ≤ Nr) (hL0 : 0 ≤ Lr) (hLN : Lr ≤ Nr) (hK0 : 0 ≤ K)
    (hKN : K ≤ c₀ * Nr) (hN1 : 1 ≤ Nr) (hc₀ : 1 ≤ c₀) (hε : 0 ≤ ε) (hck : 0 ≤ ck)
    (hce : 0 ≤ ce) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    A ^ m * ((ck * K ^ (2 * m) * ρ ^ m * ε + ce * Lr ^ m * ρ ^ m * ε) * x)
      ≤ (ck * c₀ ^ (2 * m) + ce) * Nr ^ (4 * m) * ε := by
  have h1 : A ^ m ≤ Nr ^ m := pow_le_pow_left₀ hA0 hAN m
  have h2 : K ^ (2 * m) ≤ (c₀ * Nr) ^ (2 * m) := pow_le_pow_left₀ hK0 hKN _
  have h3 : ρ ^ m ≤ Nr ^ m := pow_le_pow_left₀ hρ0 hρN m
  have h4 : Lr ^ m ≤ Nr ^ m := pow_le_pow_left₀ hL0 hLN m
  have hN0 : 0 ≤ Nr := by linarith
  have hb : ck * K ^ (2 * m) * ρ ^ m * ε + ce * Lr ^ m * ρ ^ m * ε
      ≤ ck * (c₀ * Nr) ^ (2 * m) * Nr ^ m * ε + ce * Nr ^ m * Nr ^ m * ε := by
    gcongr
  have hb0 : 0 ≤ ck * K ^ (2 * m) * ρ ^ m * ε + ce * Lr ^ m * ρ ^ m * ε := by positivity
  have hN3 : Nr ^ (3 * m) ≤ Nr ^ (4 * m) := pow_le_pow_right₀ hN1 (by omega)
  calc A ^ m * ((ck * K ^ (2 * m) * ρ ^ m * ε + ce * Lr ^ m * ρ ^ m * ε) * x)
      ≤ Nr ^ m * ((ck * (c₀ * Nr) ^ (2 * m) * Nr ^ m * ε + ce * Nr ^ m * Nr ^ m * ε) * 1) := by
        gcongr
    _ = ck * c₀ ^ (2 * m) * Nr ^ (4 * m) * ε + ce * Nr ^ (3 * m) * ε := by ring
    _ ≤ ck * c₀ ^ (2 * m) * Nr ^ (4 * m) * ε + ce * Nr ^ (4 * m) * ε := by gcongr
    _ = (ck * c₀ ^ (2 * m) + ce) * Nr ^ (4 * m) * ε := by ring

/-- Power counting of `Q_u ∘ F_u` (max norm). -/
theorem QF_scalar_max {n : ℕ} {K A u im Cf Φ c Lr Nr x : ℝ} (hK1 : 1 ≤ K) (hKN : K ≤ Nr)
    (hA : 0 < A) (hu : 0 < 1 - u) (him : 0 < im) (hCf : 0 ≤ Cf) (hΦ : 0 ≤ Φ) (hc : 0 ≤ c)
    (hL0 : 0 ≤ Lr) (hLN : Lr ≤ Nr) (hx : 0 ≤ x) :
    (1 + (6 * exp 1 * c * K) ^ (n + 1)) * (K * (A⁻¹ ^ (n + 2) * ((1 - u) * im)⁻¹ * (Cf * Φ)))
        + (2 * c) ^ (n + 1) * Lr ^ (n + 1) * (K * x)
      ≤ A⁻¹ ^ (n + 2) * (((1 + (6 * exp 1 * c) ^ (n + 1)) * Cf / im * K ^ (n + 2) * Φ) * (1 - u)⁻¹)
        + (2 * c) ^ (n + 1) * Nr ^ (n + 2) * x := by
  have hK0 : 0 ≤ K := by linarith
  have hN0 : 0 ≤ Nr := hL0.trans hLN
  have h1 : (1 + (6 * exp 1 * c * K) ^ (n + 1)) * K ≤ (1 + (6 * exp 1 * c) ^ (n + 1)) * K ^ (n + 2) := by
    rw [mul_pow, add_mul, add_mul, one_mul, one_mul, mul_assoc, ← pow_succ]
    have : K ≤ K ^ (n + 2) := by
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ (n + 2) := pow_le_pow_right₀ hK1 (by omega)
    linarith
  have h2 : Lr ^ (n + 1) * K ≤ Nr ^ (n + 2) := by
    rw [pow_succ Nr (n + 1)]
    exact mul_le_mul (pow_le_pow_left₀ hL0 hLN _) hKN hK0 (by positivity)
  have hA' : 0 ≤ A⁻¹ ^ (n + 2) := by positivity
  have e1 : (1 + (6 * exp 1 * c * K) ^ (n + 1)) * (K * (A⁻¹ ^ (n + 2) * ((1 - u) * im)⁻¹ * (Cf * Φ)))
      = A⁻¹ ^ (n + 2) * ((((1 + (6 * exp 1 * c * K) ^ (n + 1)) * K) * Cf / im * Φ) * (1 - u)⁻¹) := by
    field_simp
  rw [e1]
  have hc2 : 0 ≤ (2 * c) ^ (n + 1) := by positivity
  have hsec : (2 * c) ^ (n + 1) * Lr ^ (n + 1) * (K * x) ≤ (2 * c) ^ (n + 1) * Nr ^ (n + 2) * x := by
    have := mul_le_mul_of_nonneg_left h2 hc2
    nlinarith
  refine add_le_add ?_ hsec
  have h3 : (1 + (6 * exp 1 * c * K) ^ (n + 1)) * K * Cf / im
      ≤ (1 + (6 * exp 1 * c) ^ (n + 1)) * Cf / im * K ^ (n + 2) := by
    calc (1 + (6 * exp 1 * c * K) ^ (n + 1)) * K * Cf / im
        = ((1 + (6 * exp 1 * c * K) ^ (n + 1)) * K) * (Cf / im) := by ring
      _ ≤ ((1 + (6 * exp 1 * c) ^ (n + 1)) * K ^ (n + 2)) * (Cf / im) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  have h4 : 0 ≤ Φ * (1 - u)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_right h3 h4
  have := mul_le_mul_of_nonneg_left this hA'
  calc A⁻¹ ^ (n + 2) * ((1 + (6 * exp 1 * c * K) ^ (n + 1)) * K * Cf / im * Φ * (1 - u)⁻¹)
      = A⁻¹ ^ (n + 2) * ((1 + (6 * exp 1 * c * K) ^ (n + 1)) * K * Cf / im * (Φ * (1 - u)⁻¹)) := by
        ring
    _ ≤ A⁻¹ ^ (n + 2) * ((1 + (6 * exp 1 * c) ^ (n + 1)) * Cf / im * K ^ (n + 2) * (Φ * (1 - u)⁻¹)) :=
        this
    _ = _ := by ring

/-- Power counting of `Q_u ∘ F_u` (decay error). -/
theorem QF_scalar_dec {n : ℕ} {K A u im Cf Φ c Lr Nr x e e' : ℝ} (hK1 : 1 ≤ K) (hKN : K ≤ Nr)
    (hA1 : 1 ≤ A) (hu : 0 < 1 - u) (huN : (1 - u)⁻¹ ≤ Nr) (him : 0 < im) (hCf : 0 ≤ Cf)
    (hΦ : 0 ≤ Φ) (hc : 0 ≤ c) (hL0 : 0 ≤ Lr) (hLN : Lr ≤ Nr) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (he : 0 ≤ e) (hee : e ≤ e') (hN1 : 1 ≤ Nr) :
    K * x + ((6 * exp 1 * c * K) ^ (n + 1) * (K * (A⁻¹ ^ (n + 2) * ((1 - u) * im)⁻¹ * (Cf * Φ)))
        + (2 * c) ^ (n + 1) * Lr ^ (n + 1) * (K * x)) * e
      ≤ (1 + (6 * exp 1 * c) ^ (n + 1) * Cf / im + (2 * c) ^ (n + 1)) * Nr ^ (n + 3)
        * (x + e' * (1 + Φ)) := by
  have hK0 : 0 ≤ K := by linarith
  have hN0 : 0 ≤ Nr := by linarith
  have he' : 0 ≤ e' := he.trans hee
  have hA0 : 0 < A := by linarith
  have hAi : A⁻¹ ^ (n + 2) ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hA1)
  have hηi : ((1 - u) * im)⁻¹ ≤ Nr / im := by
    rw [mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right huN (by positivity)
  have hcK : (6 * exp 1 * c * K) ^ (n + 1) ≤ (6 * exp 1 * c) ^ (n + 1) * Nr ^ (n + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by gcongr) _
  have hM : K * (A⁻¹ ^ (n + 2) * ((1 - u) * im)⁻¹ * (Cf * Φ)) ≤ Nr * (Nr / im) * (Cf * Φ) := by
    have : A⁻¹ ^ (n + 2) * ((1 - u) * im)⁻¹ ≤ 1 * (Nr / im) :=
      mul_le_mul hAi hηi (by positivity) zero_le_one
    have h2 : 0 ≤ A⁻¹ ^ (n + 2) * ((1 - u) * im)⁻¹ * (Cf * Φ) := by positivity
    calc K * (A⁻¹ ^ (n + 2) * ((1 - u) * im)⁻¹ * (Cf * Φ)) ≤ Nr * (A⁻¹ ^ (n + 2) * ((1 - u) * im)⁻¹ * (Cf * Φ)) :=
          mul_le_mul_of_nonneg_right hKN h2
      _ ≤ Nr * (1 * (Nr / im) * (Cf * Φ)) := by gcongr
      _ = Nr * (Nr / im) * (Cf * Φ) := by ring
  have hLK : (2 * c) ^ (n + 1) * Lr ^ (n + 1) * (K * x) ≤ (2 * c) ^ (n + 1) * Nr ^ (n + 1) * Nr := by
    have : Lr ^ (n + 1) ≤ Nr ^ (n + 1) := pow_le_pow_left₀ hL0 hLN _
    have : K * x ≤ Nr := by nlinarith
    gcongr
  have hbr : (6 * exp 1 * c * K) ^ (n + 1) * (K * (A⁻¹ ^ (n + 2) * ((1 - u) * im)⁻¹ * (Cf * Φ)))
        + (2 * c) ^ (n + 1) * Lr ^ (n + 1) * (K * x)
      ≤ (6 * exp 1 * c) ^ (n + 1) * Cf / im * Nr ^ (n + 3) * Φ + (2 * c) ^ (n + 1) * Nr ^ (n + 3) := by
    have hNp : Nr ^ (n + 1) * Nr ≤ Nr ^ (n + 3) := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hN1 (by omega)
    have e1 : (6 * exp 1 * c) ^ (n + 1) * Nr ^ (n + 1) * (Nr * (Nr / im) * (Cf * Φ))
        = (6 * exp 1 * c) ^ (n + 1) * Cf / im * Nr ^ (n + 3) * Φ := by
      field_simp; ring
    have hA := mul_le_mul hcK hM (by positivity) (by positivity)
    rw [e1] at hA
    have hB : (2 * c) ^ (n + 1) * Nr ^ (n + 1) * Nr ≤ (2 * c) ^ (n + 1) * Nr ^ (n + 3) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hNp (by positivity)
    linarith
  have hbr0 : 0 ≤ (6 * exp 1 * c) ^ (n + 1) * Cf / im * Nr ^ (n + 3) * Φ
      + (2 * c) ^ (n + 1) * Nr ^ (n + 3) := by positivity
  have hKx : K * x ≤ Nr ^ (n + 3) * x := by
    have : K ≤ Nr ^ (n + 3) := hKN.trans (by
      calc Nr = Nr ^ 1 := (pow_one Nr).symm
        _ ≤ Nr ^ (n + 3) := pow_le_pow_right₀ hN1 (by omega))
    exact mul_le_mul_of_nonneg_right this hx
  have hmul := mul_le_mul hbr hee he hbr0
  have hN3 : 0 ≤ Nr ^ (n + 3) := by positivity
  have hc6 : 0 ≤ (6 * exp 1 * c) ^ (n + 1) * Cf / im := by positivity
  have hc2 : 0 ≤ (2 * c) ^ (n + 1) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hc6 hN3) (mul_nonneg he' hΦ), mul_nonneg (mul_nonneg hc2 hN3) (mul_nonneg he' hΦ),
    mul_nonneg hN3 he', mul_nonneg (mul_nonneg hc6 hN3) hx, mul_nonneg (mul_nonneg hc2 hN3) hx,
    mul_nonneg (mul_nonneg hc6 hN3) he', mul_nonneg hc2 (mul_nonneg hN3 he')]


theorem exp_arg1 {c₀ ℓ K : ℝ} (hc : 0 < c₀) (hℓ : 0 < ℓ) (hK : 0 ≤ K) :
    exp (-(c₀ * (ℓ * K / 2) / ℓ)) ≤ exp (-(c₀ / 4 * K)) := by
  apply exp_le_exp.2
  rw [show c₀ * (ℓ * K / 2) / ℓ = c₀ * K / 2 by field_simp]
  nlinarith

theorem exp_arg2 {c₀ ℓ K : ℝ} (hc : 0 < c₀) (hℓ : 0 < ℓ) (hK : 0 ≤ K) :
    exp (-(c₀ * (ℓ * K) / ℓ)) ≤ exp (-(c₀ / 4 * K)) := by
  apply exp_le_exp.2
  rw [show c₀ * (ℓ * K) / ℓ = c₀ * K by field_simp]
  nlinarith

theorem exp_arg3 {c₀ ℓ K : ℝ} (hc : 0 < c₀) (hℓ : 0 < ℓ) (hK : 0 ≤ K) :
    exp (-(c₀ * ((2 * (ℓ * K) + 1) / 2) / ℓ)) ≤ exp (-(c₀ / 4 * K)) := by
  apply exp_le_exp.2
  have : c₀ * K ≤ c₀ * ((2 * (ℓ * K) + 1) / 2) / ℓ := by
    rw [le_div_iff₀ hℓ]; nlinarith
  nlinarith

theorem exp_arg4 {c₀ ℓ K : ℝ} (hc : 0 < c₀) (hℓ : 1 / 2 ≤ ℓ) (hK : 0 ≤ K) :
    exp (-(c₀ * (ℓ * (4 * K) / 4 - 1 / 2) / ℓ)) ≤ exp c₀ * exp (-(c₀ / 4 * K)) := by
  have hℓ0 : 0 < ℓ := by linarith
  rw [← exp_add]; apply exp_le_exp.2
  have e : c₀ * (ℓ * (4 * K) / 4 - 1 / 2) / ℓ = c₀ * K - c₀ / (2 * ℓ) := by field_simp
  rw [e]
  have : c₀ / (2 * ℓ) ≤ c₀ := by rw [div_le_iff₀ (by positivity)]; nlinarith
  nlinarith

theorem div_le_two_mul {ℓ c : ℝ} (hℓ : 1 / 2 ≤ ℓ) (hc : 0 ≤ c) : c / ℓ ≤ 2 * c := by
  have hℓ0 : 0 < ℓ := by linarith
  rw [div_le_iff₀ hℓ0]; nlinarith

theorem radius_le {ℓ K : ℝ} (hℓ : 1 / 2 ≤ ℓ) (hK : 1 ≤ K) : 2 * (ℓ * K) + 1 ≤ ℓ * (4 * K) := by
  nlinarith

theorem two_le_radius {ℓ K : ℝ} (hℓ : 1 / 2 ≤ ℓ) (hK : 1 ≤ K) : 2 ≤ ℓ * (4 * K) := by nlinarith

/-- The composition of the two slot projections, as a scalar recursion. -/
theorem QQ_rec_scalar {α β e δ E e₂ δ₂ e₃ δ₃ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (he : 0 ≤ e)
    (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hE1 : E ≤ 1)
    (he2 : e₂ ≤ α * e + β * δ) (hd2 : δ₂ ≤ δ + (α * e + β * δ) * E + β * δ)
    (he3 : e₃ ≤ α * e₂ + β * δ₂) (hd3 : δ₃ ≤ δ₂ + (α * e₂ + β * δ₂) * E + β * δ₂)
    (hd20 : 0 ≤ δ₂) :
    e₃ ≤ α ^ 2 * e + 4 * (1 + α + β) ^ 2 * (δ + E * e) ∧
      δ₃ ≤ 10 * (1 + α + β) ^ 2 * (δ + E * e) := by
  set S := 1 + α + β with hS
  have hS1 : 1 ≤ S := by linarith
  have hαS : α ≤ S := by linarith
  have hβS : β ≤ S := by linarith
  have hEe : 0 ≤ E * e := mul_nonneg hE he
  have hX : 0 ≤ δ + E * e := by linarith
  have hd2' : δ₂ ≤ 3 * S * (δ + E * e) := by
    have h1 : (α * e + β * δ) * E = α * (E * e) + β * E * δ := by ring
    have h2 : α * (E * e) ≤ S * (E * e) := mul_le_mul_of_nonneg_right hαS hEe
    have h3 : β * E * δ ≤ S * δ := by
      have : β * E ≤ S := by nlinarith
      exact mul_le_mul_of_nonneg_right this hδ
    have h4 : β * δ ≤ S * δ := mul_le_mul_of_nonneg_right hβS hδ
    have h5 : δ ≤ S * δ := by nlinarith
    nlinarith
  have he2' : e₂ ≤ α * e + S * δ := by
    have := mul_le_mul_of_nonneg_right hβS hδ; linarith
  constructor
  · have h1 : α * e₂ ≤ α * (α * e + S * δ) := mul_le_mul_of_nonneg_left he2' hα
    have h2 : β * δ₂ ≤ S * (3 * S * (δ + E * e)) :=
      mul_le_mul hβS hd2' hd20 (by linarith)
    have h3 : α * (S * δ) ≤ S * S * δ := by
      have := mul_le_mul_of_nonneg_right hαS (mul_nonneg (by linarith : (0:ℝ) ≤ S) hδ); nlinarith
    have h4 : S * S * δ ≤ S ^ 2 * (δ + E * e) := by nlinarith
    nlinarith
  · have hS0 : 0 ≤ S := by linarith
    have hαE : α * E ≤ S := by nlinarith
    have hβE : β * E ≤ S := by nlinarith
    have ha1 : α * e₂ * E ≤ α * E * (α * e + S * δ) := by
      have := mul_le_mul_of_nonneg_left he2' (mul_nonneg hα hE)
      calc α * e₂ * E = α * E * e₂ := by ring
        _ ≤ _ := this
    have ha2 : α * E * (α * e) ≤ S ^ 2 * (E * e) := by
      have h1 : α * α ≤ S * S := mul_le_mul hαS hαS hα hS0
      calc α * E * (α * e) = (α * α) * (E * e) := by ring
        _ ≤ (S * S) * (E * e) := mul_le_mul_of_nonneg_right h1 hEe
        _ = S ^ 2 * (E * e) := by ring
    have ha3 : α * E * (S * δ) ≤ S ^ 2 * δ := by
      calc α * E * (S * δ) ≤ S * (S * δ) := mul_le_mul_of_nonneg_right hαE (mul_nonneg hS0 hδ)
        _ = S ^ 2 * δ := by ring
    have hb1 : β * δ₂ * E ≤ S * δ₂ := by
      calc β * δ₂ * E = (β * E) * δ₂ := by ring
        _ ≤ S * δ₂ := mul_le_mul_of_nonneg_right hβE hd20
    have hb2 : β * δ₂ ≤ S * δ₂ := mul_le_mul_of_nonneg_right hβS hd20
    have h5 : (1 + 2 * S) * δ₂ ≤ (1 + 2 * S) * (3 * S * (δ + E * e)) :=
      mul_le_mul_of_nonneg_left hd2' (by linarith)
    have h6 : (1 + 2 * S) * (3 * S) ≤ 9 * S ^ 2 := by nlinarith
    have h7 : (1 + 2 * S) * (3 * S * (δ + E * e)) ≤ 9 * S ^ 2 * (δ + E * e) := by
      calc (1 + 2 * S) * (3 * S * (δ + E * e)) = ((1 + 2 * S) * (3 * S)) * (δ + E * e) := by ring
        _ ≤ (9 * S ^ 2) * (δ + E * e) := mul_le_mul_of_nonneg_right h6 hX
    have e1 : (α * e₂ + β * δ₂) * E = α * e₂ * E + β * δ₂ * E := by ring
    have e2 : 10 * S ^ 2 * (δ + E * e) = 9 * S ^ 2 * (δ + E * e) + S ^ 2 * (E * e) + S ^ 2 * δ := by
      ring
    rw [e2]
    linarith

/-- The power counting of the quadratic-variation integrand (5.105). -/
theorem QV_final_scalar {m k : ℕ} {Av Au r ρ' Lr Nr K Λ im u x e' E ck ce α S e δ e₃ δ₃ α₀ S₀ : ℝ}
    (hck : 0 ≤ ck) (hce : 0 ≤ ce) (_hα₀ : 0 ≤ α₀) (_hS₀ : 0 ≤ S₀)
    (he3 : e₃ ≤ α ^ 2 * e + 4 * S ^ 2 * (δ + E * e)) (hd3 : δ₃ ≤ 10 * S ^ 2 * (δ + E * e))
    (hen : e ≤ K ^ 2 * Λ * (Au⁻¹ ^ (2 * m) * ((1 - u) * im)⁻¹)) (hec : e ≤ Nr ^ 3 * Λ / im)
    (he0 : 0 ≤ e) (hδ : δ ≤ Nr * x) (hδ0 : 0 ≤ δ) (hE : E ≤ e') (hE0 : 0 ≤ E)
    (hα : α ≤ α₀ * K ^ k) (hα0 : 0 ≤ α) (hS : S ≤ S₀ * Nr ^ k) (hS0 : 0 ≤ S)
    (hr : Av * r = Au) (hAv1 : 1 ≤ Av) (hAvN : Av ≤ Nr) (hAu1 : 1 ≤ Au) (hr0 : 0 ≤ r) (hrN : r ≤ Nr)
    (hρ0 : 0 ≤ ρ') (hρN : ρ' ≤ Nr) (hL0 : 0 ≤ Lr) (hLN : Lr ≤ Nr) (hK1 : 1 ≤ K) (hKN : K ≤ Nr)
    (hu : 0 < 1 - u) (hu1 : 1 - u ≤ 1) (him : 0 < im) (hΛ : 0 ≤ Λ) (hx : 0 ≤ x) (he' : 0 ≤ e')
    (_he30 : 0 ≤ e₃) (hδ30 : 0 ≤ δ₃) :
    Av ^ (2 * m) * (1 - u) * (ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m) * e₃
        + ce * Lr ^ (2 * m) * ρ' ^ (2 * m) * δ₃)
      ≤ (ck * 4 ^ (4 * m) * α₀ ^ 2 / im) * K ^ (4 * m + 2 * k + 2) * Λ
        + ((4 * ck * 4 ^ (4 * m) + 10 * ce) * S₀ ^ 2 * (1 + 1 / im)) * Nr ^ (8 * m + 2 * k + 3)
          * (x + e' * (1 + Λ)) := by
  have hN1 : 1 ≤ Nr := hK1.trans hKN
  have hN0 : 0 ≤ Nr := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hAu0 : 0 < Au := by linarith
  have hAv0 : 0 < Av := by linarith
  -- the main term
  have hmain : Av ^ (2 * m) * (1 - u) * (ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m) * (α ^ 2 * e))
      ≤ (ck * 4 ^ (4 * m) * α₀ ^ 2 / im) * K ^ (4 * m + 2 * k + 2) * Λ := by
    have hα2 : α ^ 2 ≤ (α₀ * K ^ k) ^ 2 := pow_le_pow_left₀ hα0 hα 2
    have hcancel : Av ^ (2 * m) * r ^ (2 * m) * Au⁻¹ ^ (2 * m) = 1 := by
      rw [← mul_pow, hr, ← mul_pow, mul_inv_cancel₀ hAu0.ne', one_pow]
    have hu' : (1 - u) * ((1 - u) * im)⁻¹ = im⁻¹ := by field_simp
    calc Av ^ (2 * m) * (1 - u) * (ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m) * (α ^ 2 * e))
        ≤ Av ^ (2 * m) * (1 - u) * (ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m)
            * ((α₀ * K ^ k) ^ 2 * (K ^ 2 * Λ * (Au⁻¹ ^ (2 * m) * ((1 - u) * im)⁻¹)))) := by
          gcongr
      _ = ck * 4 ^ (4 * m) * α₀ ^ 2 * (K ^ (4 * m) * (K ^ k) ^ 2 * K ^ 2) * Λ
            * (Av ^ (2 * m) * r ^ (2 * m) * Au⁻¹ ^ (2 * m)) * ((1 - u) * ((1 - u) * im)⁻¹) := by
          rw [mul_pow 4 K, show 2 * (2 * m) = 4 * m by ring]; ring
      _ = (ck * 4 ^ (4 * m) * α₀ ^ 2 / im) * K ^ (4 * m + 2 * k + 2) * Λ := by
          rw [hcancel, hu', ← pow_mul, ← pow_add, ← pow_add]; ring_nf
  -- the error terms
  set X := x + e' * (1 + Λ) with hX
  have hX0 : 0 ≤ X := by positivity
  have hδE : δ + E * e ≤ Nr ^ 3 * (1 + 1 / im) * X := by
    have h1 : δ ≤ Nr * x := hδ
    have h2 : E * e ≤ e' * (Nr ^ 3 * Λ / im) := mul_le_mul hE hec he0 he'
    have hN3 : Nr ≤ Nr ^ 3 := by simpa using pow_le_pow_right₀ hN1 (show 1 ≤ 3 by norm_num)
    have h3 : Nr * x ≤ Nr ^ 3 * (1 + 1 / im) * x := by
      have : Nr ≤ Nr ^ 3 * (1 + 1 / im) := by
        have : 0 ≤ Nr ^ 3 * (1 / im) := by positivity
        have e : Nr ^ 3 * (1 + 1 / im) = Nr ^ 3 + Nr ^ 3 * (1 / im) := by ring
        linarith
      exact mul_le_mul_of_nonneg_right this hx
    have h4 : e' * (Nr ^ 3 * Λ / im) ≤ Nr ^ 3 * (1 + 1 / im) * (e' * (1 + Λ)) := by
      have : Λ / im ≤ (1 + 1 / im) * (1 + Λ) := by
        rw [div_eq_mul_one_div]
        have hi : 0 ≤ 1 / im := by positivity
        have e : (1 + 1 / im) * (1 + Λ) = 1 + Λ + 1 / im + Λ * (1 / im) := by ring
        rw [e]
        linarith
      calc e' * (Nr ^ 3 * Λ / im) = Nr ^ 3 * e' * (Λ / im) := by ring
        _ ≤ Nr ^ 3 * e' * ((1 + 1 / im) * (1 + Λ)) := by gcongr
        _ = _ := by ring
    have : Nr ^ 3 * (1 + 1 / im) * X = Nr ^ 3 * (1 + 1 / im) * x
        + Nr ^ 3 * (1 + 1 / im) * (e' * (1 + Λ)) := by rw [hX]; ring
    linarith
  have hδE0 : 0 ≤ δ + E * e := by positivity
  have hS2 : S ^ 2 ≤ S₀ ^ 2 * Nr ^ (2 * k) := by
    calc S ^ 2 ≤ (S₀ * Nr ^ k) ^ 2 := pow_le_pow_left₀ hS0 hS 2
      _ = S₀ ^ 2 * Nr ^ (2 * k) := by rw [mul_pow, ← pow_mul, mul_comm k 2]
  have herr1 : Av ^ (2 * m) * (1 - u) * (ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m)
      * (4 * S ^ 2 * (δ + E * e))) ≤ 4 * ck * 4 ^ (4 * m) * S₀ ^ 2 * (1 + 1 / im)
        * Nr ^ (8 * m + 2 * k + 3) * X := by
    calc Av ^ (2 * m) * (1 - u) * (ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m)
          * (4 * S ^ 2 * (δ + E * e)))
        ≤ Nr ^ (2 * m) * 1 * (ck * (4 * Nr) ^ (2 * (2 * m)) * Nr ^ (2 * m)
          * (4 * (S₀ ^ 2 * Nr ^ (2 * k)) * (Nr ^ 3 * (1 + 1 / im) * X))) := by gcongr
      _ = 4 * ck * 4 ^ (4 * m) * S₀ ^ 2 * (1 + 1 / im) * Nr ^ (8 * m + 2 * k + 3) * X := by
          rw [mul_pow 4 Nr, show 2 * (2 * m) = 4 * m by ring]
          rw [show 8 * m + 2 * k + 3 = 2 * m + 4 * m + 2 * m + 2 * k + 3 by ring]
          simp only [pow_add]; ring
  have herr2 : Av ^ (2 * m) * (1 - u) * (ce * Lr ^ (2 * m) * ρ' ^ (2 * m) * δ₃)
      ≤ 10 * ce * S₀ ^ 2 * (1 + 1 / im) * Nr ^ (8 * m + 2 * k + 3) * X := by
    have hδ3 : δ₃ ≤ 10 * (S₀ ^ 2 * Nr ^ (2 * k)) * (Nr ^ 3 * (1 + 1 / im) * X) :=
      hd3.trans (by gcongr)
    calc Av ^ (2 * m) * (1 - u) * (ce * Lr ^ (2 * m) * ρ' ^ (2 * m) * δ₃)
        ≤ Nr ^ (2 * m) * 1 * (ce * Nr ^ (2 * m) * Nr ^ (2 * m)
          * (10 * (S₀ ^ 2 * Nr ^ (2 * k)) * (Nr ^ 3 * (1 + 1 / im) * X))) := by
          gcongr
      _ = 10 * ce * S₀ ^ 2 * (1 + 1 / im) * Nr ^ (6 * m + 2 * k + 3) * X := by
          rw [show 6 * m + 2 * k + 3 = 2 * m + 2 * m + 2 * m + 2 * k + 3 by ring]
          simp only [pow_add]; ring
      _ ≤ 10 * ce * S₀ ^ 2 * (1 + 1 / im) * Nr ^ (8 * m + 2 * k + 3) * X := by
          gcongr
          · omega
  have he3' : ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m) * e₃
      ≤ ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m) * (α ^ 2 * e)
        + ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m) * (4 * S ^ 2 * (δ + E * e)) := by
    rw [← mul_add]; gcongr
  have hpre : 0 ≤ Av ^ (2 * m) * (1 - u) := by positivity
  calc Av ^ (2 * m) * (1 - u) * (ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m) * e₃
        + ce * Lr ^ (2 * m) * ρ' ^ (2 * m) * δ₃)
      ≤ Av ^ (2 * m) * (1 - u) * (ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m) * (α ^ 2 * e))
        + Av ^ (2 * m) * (1 - u) * (ck * (4 * K) ^ (2 * (2 * m)) * r ^ (2 * m)
          * (4 * S ^ 2 * (δ + E * e)))
        + Av ^ (2 * m) * (1 - u) * (ce * Lr ^ (2 * m) * ρ' ^ (2 * m) * δ₃) := by
        rw [← mul_add, ← mul_add, add_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hpre
        linarith
    _ ≤ (ck * 4 ^ (4 * m) * α₀ ^ 2 / im) * K ^ (4 * m + 2 * k + 2) * Λ
        + 4 * ck * 4 ^ (4 * m) * S₀ ^ 2 * (1 + 1 / im) * Nr ^ (8 * m + 2 * k + 3) * X
        + 10 * ce * S₀ ^ 2 * (1 + 1 / im) * Nr ^ (8 * m + 2 * k + 3) * X := by
        linarith
    _ = _ := by ring

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

/-- Power counting of the commutator and `ϑ̇` terms (max norm). -/
theorem comm_scalar_max {n : ℕ} {k A W η ℓ u Lr Nr K Φ x c : ℝ} (hA : A = W * ℓ * η)
    (hW : 0 < W) (hη : 0 < η) (hℓ : 1 / 2 ≤ ℓ) (hℓL : ℓ ≤ Lr) (hK1 : 1 ≤ K) (hKN : K ≤ Nr)
    (hA1 : 1 ≤ A) (hΦ : 0 ≤ Φ) (hx : 0 ≤ x) (hc : 0 ≤ c) (hk : 0 ≤ k) (hu : 0 < 1 - u)
    (huN : (1 - u)⁻¹ ≤ Nr) (hLN : Lr ≤ Nr) :
    k * (1 - u)⁻¹ * (c / ℓ) ^ (n + 1) * ((2 * W * η)⁻¹ * (2 * ((2 * exp 1 * (ℓ * K + 1)) ^ n
        * (K * Φ * A⁻¹ ^ (n + 1)) + Lr ^ n * (K * x))))
      ≤ A⁻¹ ^ (n + 2) * ((k * c * (6 * exp 1 * c) ^ n * K ^ (n + 1) * Φ) * (1 - u)⁻¹)
        + k * (2 * c) ^ (n + 1) * Nr ^ (n + 3) * x := by
  have hℓ0 : 0 < ℓ := by linarith
  have hA0 : 0 < A := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ Lr := by linarith
  have hN0 : 0 ≤ Nr := by linarith
  have hWη : (2 * W * η)⁻¹ * 2 = ℓ * A⁻¹ := by rw [hA]; field_simp
  have hcl : (c / ℓ) ^ (n + 1) * ℓ = c * (c / ℓ) ^ n := by
    rw [pow_succ]; field_simp
  have e : k * (1 - u)⁻¹ * (c / ℓ) ^ (n + 1) * ((2 * W * η)⁻¹ * (2 * ((2 * exp 1 * (ℓ * K + 1)) ^ n
        * (K * Φ * A⁻¹ ^ (n + 1)) + Lr ^ n * (K * x))))
      = A⁻¹ ^ (n + 2) * ((k * c * ((2 * exp 1 * (ℓ * K + 1)) ^ n * (c / ℓ) ^ n) * K * Φ) * (1 - u)⁻¹)
        + k * (1 - u)⁻¹ * (c / ℓ) ^ (n + 1) * ℓ * A⁻¹ * Lr ^ n * (K * x) := by
    have : (2 * W * η)⁻¹ * (2 * ((2 * exp 1 * (ℓ * K + 1)) ^ n * (K * Φ * A⁻¹ ^ (n + 1))
        + Lr ^ n * (K * x))) = (ℓ * A⁻¹) * ((2 * exp 1 * (ℓ * K + 1)) ^ n * (K * Φ * A⁻¹ ^ (n + 1))
        + Lr ^ n * (K * x)) := by rw [← hWη]; ring
    rw [this]
    have h2 : k * (1 - u)⁻¹ * (c / ℓ) ^ (n + 1) * (ℓ * A⁻¹ * ((2 * exp 1 * (ℓ * K + 1)) ^ n
        * (K * Φ * A⁻¹ ^ (n + 1))))
        = A⁻¹ ^ (n + 2) * (k * ((c / ℓ) ^ (n + 1) * ℓ) * (2 * exp 1 * (ℓ * K + 1)) ^ n * K * Φ
          * (1 - u)⁻¹) := by ring
    calc k * (1 - u)⁻¹ * (c / ℓ) ^ (n + 1) * (ℓ * A⁻¹ * ((2 * exp 1 * (ℓ * K + 1)) ^ n
          * (K * Φ * A⁻¹ ^ (n + 1)) + Lr ^ n * (K * x)))
        = k * (1 - u)⁻¹ * (c / ℓ) ^ (n + 1) * (ℓ * A⁻¹ * ((2 * exp 1 * (ℓ * K + 1)) ^ n
          * (K * Φ * A⁻¹ ^ (n + 1))))
          + k * (1 - u)⁻¹ * (c / ℓ) ^ (n + 1) * ℓ * A⁻¹ * Lr ^ n * (K * x) := by ring
      _ = _ := by rw [h2, hcl]; ring
  rw [e]
  have h1 := window_mul_le (n := n) hℓ hK1 hc
  have hAi : 0 ≤ A⁻¹ ^ (n + 2) := by positivity
  refine add_le_add ?_ ?_
  · have : k * c * ((2 * exp 1 * (ℓ * K + 1)) ^ n * (c / ℓ) ^ n) * K * Φ
        ≤ k * c * (6 * exp 1 * c) ^ n * K ^ (n + 1) * Φ := by
      have h1' : (2 * exp 1 * (ℓ * K + 1)) ^ n * (c / ℓ) ^ n ≤ (6 * exp 1 * c) ^ n * K ^ n := by
        rw [← mul_pow (6 * exp 1 * c) K]; exact h1
      calc k * c * ((2 * exp 1 * (ℓ * K + 1)) ^ n * (c / ℓ) ^ n) * K * Φ
          ≤ k * c * ((6 * exp 1 * c) ^ n * K ^ n) * K * Φ := by gcongr
        _ = k * c * (6 * exp 1 * c) ^ n * K ^ (n + 1) * Φ := by ring
    gcongr
  · have h2 := div_pow_le_two_mul (n := n + 1) hℓ hc
    have hAi1 : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA1
    have hℓA : ℓ * A⁻¹ ≤ Nr := by
      calc ℓ * A⁻¹ ≤ Lr * 1 := mul_le_mul hℓL hAi1 (by positivity) hL0
        _ ≤ Nr := by linarith
    have hLn : Lr ^ n ≤ Nr ^ n := pow_le_pow_left₀ hL0 hLN n
    have hKx : K * x ≤ Nr * x := mul_le_mul_of_nonneg_right hKN hx
    calc k * (1 - u)⁻¹ * (c / ℓ) ^ (n + 1) * ℓ * A⁻¹ * Lr ^ n * (K * x)
        = k * (1 - u)⁻¹ * (c / ℓ) ^ (n + 1) * (ℓ * A⁻¹) * Lr ^ n * (K * x) := by ring
      _ ≤ k * Nr * (2 * c) ^ (n + 1) * Nr * Nr ^ n * (Nr * x) := by gcongr
      _ = k * (2 * c) ^ (n + 1) * Nr ^ (n + 3) * x := by ring

/-- A crude bound on the Ward bound of the slot sums. -/
theorem P_crude {n : ℕ} {A W η ℓ Lr Nr K Φ x : ℝ} (hA : A = W * ℓ * η) (hW : 0 < W)
    (hη : 0 < η) (hℓ : 1 / 2 ≤ ℓ) (hℓL : ℓ ≤ Lr) (hLN : Lr ≤ Nr) (hK1 : 1 ≤ K) (hKN : K ≤ Nr)
    (hA1 : 1 ≤ A) (hΦ : 0 ≤ Φ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (2 * W * η)⁻¹ * (2 * ((2 * exp 1 * (ℓ * K + 1)) ^ n * (K * Φ * A⁻¹ ^ (n + 1))
        + Lr ^ n * (K * x)))
      ≤ (4 * exp 1) ^ n * Nr ^ (2 * n + 2) * (1 + Φ) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hA0 : 0 < A := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ Lr := by linarith
  have hN1 : 1 ≤ Nr := by linarith
  have hN0 : 0 ≤ Nr := by linarith
  have hWη : (2 * W * η)⁻¹ * 2 = ℓ * A⁻¹ := by rw [hA]; field_simp
  have hAi1 : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA1
  have hℓA : ℓ * A⁻¹ ≤ Nr := by
    calc ℓ * A⁻¹ ≤ Lr * 1 := mul_le_mul hℓL hAi1 (by positivity) hL0
      _ ≤ Nr := by linarith
  have hAn : A⁻¹ ^ (n + 1) ≤ 1 := pow_le_one₀ (by positivity) hAi1
  have hw : 2 * exp 1 * (ℓ * K + 1) ≤ 4 * exp 1 * Nr ^ 2 := by
    have : ℓ * K + 1 ≤ 2 * Nr ^ 2 := by nlinarith
    nlinarith [exp_pos 1]
  have hwn : (2 * exp 1 * (ℓ * K + 1)) ^ n ≤ (4 * exp 1) ^ n * Nr ^ (2 * n) := by
    rw [pow_mul, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) hw n
  have e : (2 * W * η)⁻¹ * (2 * ((2 * exp 1 * (ℓ * K + 1)) ^ n * (K * Φ * A⁻¹ ^ (n + 1))
        + Lr ^ n * (K * x)))
      = (ℓ * A⁻¹) * ((2 * exp 1 * (ℓ * K + 1)) ^ n * (K * Φ * A⁻¹ ^ (n + 1)) + Lr ^ n * (K * x)) := by
    rw [← hWη]; ring
  rw [e]
  have h4 : 1 ≤ (4 * exp 1) ^ n := one_le_pow₀ (by nlinarith [add_one_le_exp (1 : ℝ)])
  have hLn : Lr ^ n ≤ Nr ^ n := pow_le_pow_left₀ hL0 hLN n
  have hKx : K * x ≤ Nr := by nlinarith
  have hA1' : (2 * exp 1 * (ℓ * K + 1)) ^ n * (K * Φ * A⁻¹ ^ (n + 1))
      ≤ (4 * exp 1) ^ n * Nr ^ (2 * n) * (Nr * Φ * 1) := by gcongr
  have hB1 : Lr ^ n * (K * x) ≤ Nr ^ n * Nr := mul_le_mul hLn hKx (by positivity) (by positivity)
  have hNn : Nr ^ n * Nr ≤ (4 * exp 1) ^ n * Nr ^ (2 * n + 1) := by
    rw [← pow_succ]
    calc Nr ^ (n + 1) ≤ Nr ^ (2 * n + 1) := pow_le_pow_right₀ hN1 (by omega)
      _ = 1 * Nr ^ (2 * n + 1) := (one_mul _).symm
      _ ≤ (4 * exp 1) ^ n * Nr ^ (2 * n + 1) := by gcongr
  have hsum : (2 * exp 1 * (ℓ * K + 1)) ^ n * (K * Φ * A⁻¹ ^ (n + 1)) + Lr ^ n * (K * x)
      ≤ (4 * exp 1) ^ n * Nr ^ (2 * n + 1) * (1 + Φ) := by
    have e2 : (4 * exp 1) ^ n * Nr ^ (2 * n) * (Nr * Φ * 1) = (4 * exp 1) ^ n * Nr ^ (2 * n + 1) * Φ := by
      ring
    nlinarith
  have hsum0 : 0 ≤ (2 * exp 1 * (ℓ * K + 1)) ^ n * (K * Φ * A⁻¹ ^ (n + 1)) + Lr ^ n * (K * x) := by
    positivity
  calc (ℓ * A⁻¹) * ((2 * exp 1 * (ℓ * K + 1)) ^ n * (K * Φ * A⁻¹ ^ (n + 1)) + Lr ^ n * (K * x))
      ≤ Nr * ((4 * exp 1) ^ n * Nr ^ (2 * n + 1) * (1 + Φ)) :=
        mul_le_mul hℓA hsum hsum0 hN0
    _ = (4 * exp 1) ^ n * Nr ^ (2 * n + 2) * (1 + Φ) := by ring


/-- Power counting of the decay error of the commutator term. -/
theorem comm_scalar_dec {m : ℕ} {k u ℓ c Lr Nr P e1 e2 e3 e' : ℝ} (hℓ : 1 / 2 ≤ ℓ)
    (hu : 0 < 1 - u) (huN : (1 - u)⁻¹ ≤ Nr) (hc : 0 ≤ c) (hL0 : 0 ≤ Lr) (hLN : Lr ≤ Nr)
    (hP : 0 ≤ P) (hk : 0 ≤ k) (he1 : 0 ≤ e1) (he1' : e1 ≤ e') (he2 : 0 ≤ e2) (he2' : e2 ≤ e')
    (he3 : 0 ≤ e3) (he3' : e3 ≤ e') (hN1 : 1 ≤ Nr) :
    (k + 1) * ((1 - u)⁻¹ * (P * ((c / ℓ) ^ m * e1)) + Lr * (c / ((1 - u) * ℓ) * e2 * (P * (c / ℓ) ^ m)))
        + (1 + k) * (1 - u)⁻¹ * P * ((c / ℓ) ^ m * e3)
      ≤ (k + 1) * (2 * c) ^ m * (2 + 2 * c) * Nr ^ 2 * P * e' := by
  have hℓ0 : 0 < ℓ := by linarith
  have hN0 : 0 ≤ Nr := by linarith
  have h1 := div_pow_le_two_mul (n := m) hℓ hc
  have hcl : c / ((1 - u) * ℓ) ≤ 2 * c * Nr := by
    rw [div_mul_eq_div_div_swap, div_eq_mul_inv]
    have : c / ℓ ≤ 2 * c := by rw [div_le_iff₀ hℓ0]; nlinarith
    exact mul_le_mul this huN (by positivity) (by positivity)
  have he' : 0 ≤ e' := he1.trans he1'
  have hA : (1 - u)⁻¹ * (P * ((c / ℓ) ^ m * e1)) ≤ Nr * (P * ((2 * c) ^ m * e')) := by gcongr
  have hB : Lr * (c / ((1 - u) * ℓ) * e2 * (P * (c / ℓ) ^ m)) ≤ Nr * (2 * c * Nr * e' * (P * (2 * c) ^ m)) := by
    gcongr
  have hC : (1 - u)⁻¹ * P * ((c / ℓ) ^ m * e3) ≤ Nr * P * ((2 * c) ^ m * e') := by gcongr
  have hNN : Nr ≤ Nr ^ 2 := by nlinarith
  have hq : 0 ≤ P * (2 * c) ^ m * e' := by positivity
  calc (k + 1) * ((1 - u)⁻¹ * (P * ((c / ℓ) ^ m * e1)) + Lr * (c / ((1 - u) * ℓ) * e2 * (P * (c / ℓ) ^ m)))
        + (1 + k) * (1 - u)⁻¹ * P * ((c / ℓ) ^ m * e3)
      = (k + 1) * ((1 - u)⁻¹ * (P * ((c / ℓ) ^ m * e1)) + Lr * (c / ((1 - u) * ℓ) * e2 * (P * (c / ℓ) ^ m))
        + (1 - u)⁻¹ * P * ((c / ℓ) ^ m * e3)) := by ring
    _ ≤ (k + 1) * (Nr * (P * ((2 * c) ^ m * e')) + Nr * (2 * c * Nr * e' * (P * (2 * c) ^ m))
        + Nr * P * ((2 * c) ^ m * e')) := by gcongr
    _ = (k + 1) * ((2 * Nr + 2 * c * Nr ^ 2) * (P * (2 * c) ^ m * e')) := by ring
    _ ≤ (k + 1) * ((2 * Nr ^ 2 + 2 * c * Nr ^ 2) * (P * (2 * c) ^ m * e')) := by gcongr
    _ = (k + 1) * (2 * c) ^ m * (2 + 2 * c) * Nr ^ 2 * P * e' := by ring

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

/-- **The time integrals of (5.94)**: `(W ℓ_v η_v)^m |∫_s^v U_{u,v,σ} ∘ G_u du|` for sum-zero,
`(ℓ_u K, δ)`-fast-decaying `G_u` of size `(W ℓ_u η_u)^{-m} ψ (1-u)^{-1} + ζ`: the main term is
`C_m K^{2m} ψ log((1-s)/(1-v))` — there is no `(η_s/η_v)` prefactor. -/
theorem integral_term_le (hL : 3 ≤ L) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (n + 2) → Bool)
    {s v : ℝ} (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1) {κA : ℝ} (hκA : 0 < κA)
    {K ψ ζ δ : ℝ} (hK : 1 ≤ K) (hψ : 0 ≤ ψ) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {G : ℝ → LoopArg L (n + 2) → ℂ}
    (hG : ∀ u, s ≤ u → u ≤ v → SumZero L (G u) ∧ FastDecay L (ellHat L (u : ℂ) * K) δ (G u) ∧
      ∀ b, ‖G u b‖ ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * (ψ * (1 - u)⁻¹) + ζ)
    (a : LoopArg L (n + 2)) :
    (κA * ((1 - v) * ellHat L (v : ℂ))) ^ (n + 2)
        * ‖∫ u in s..v, Uker L (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) (G u) a‖
      ≤ cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ψ * Real.log ((1 - s) / (1 - v))
        + (κA * ((1 - v) * ellHat L (v : ℂ))) ^ (n + 2)
          * ((cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
            + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * δ)
            * (v - s)) := by
  have hℓv := ellHat_real_pos' L hL (hs0.trans hsv) hv1
  have h1v : 0 < 1 - v := by linarith
  set Av := κA * ((1 - v) * ellHat L (v : ℂ)) with hAv
  have hAv0 : 0 < Av := by positivity
  have hint := norm_integral_le_log (f := fun u => Uker L (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) (G u) a)
    (α := cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * Av⁻¹ ^ (n + 2) * ψ)
    (β := cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
      + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * δ) hsv hv1
    (fun u hsu huv => by
      obtain ⟨hz, hd, hb⟩ := hG u hsu huv
      have h1u : 0 < 1 - u := by linarith
      have := norm_Uker_sumZero_scale_le L hL hE σ hs0 hsu huv hv0 hv1 hκA hK
        (by positivity : 0 ≤ ψ * (1 - u)⁻¹) hζ hδ hb hd hz a
      refine this.trans (le_of_eq ?_)
      rw [← hAv]; ring)
  have hlog : 0 ≤ Real.log ((1 - s) / (1 - v)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ h1v]; linarith
  have hAvn : Av ^ (n + 2) * Av⁻¹ ^ (n + 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hAv0.ne', one_pow]
  calc Av ^ (n + 2) * ‖∫ u in s..v, Uker L (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) (G u) a‖
      ≤ Av ^ (n + 2) * (cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * Av⁻¹ ^ (n + 2) * ψ
          * Real.log ((1 - s) / (1 - v))
          + (cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
            + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * δ)
            * (v - s)) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (Av ^ (n + 2) * Av⁻¹ ^ (n + 2)) * (cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ψ
          * Real.log ((1 - s) / (1 - v)))
        + Av ^ (n + 2) * ((cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
            + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * δ)
            * (v - s)) := by ring
    _ = _ := by rw [hAvn, one_mul]

end TermBounds

section Master

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- `ξ ≺ ζ` from `ξ ≺ 3ζ`. -/
theorem stochDom_of_three {ξ : ∀ N, U N → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (h : StochDom P ξ (fun N _ _ => 3 * (1 + Φ N))) : StochDom P ξ (fun N _ _ => 1 + Φ N) := by
  have h' := StochDom.const_mul_right (c := 3⁻¹) (by norm_num)
    (fun N _ _ => by have := hΦ N; positivity) h
  refine StochDom.of_subset h' fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, by simpa [badSet, ← mul_assoc] using hu⟩

/-- **The master `≺`-lemma of the terms of (5.94)**: a bound, on a high-probability event, of
the form `C N^{pτ₁} (1 + log N) Φ + C N^q (N^{-D} + e^{-c₁ N^{τ₁}} (1 + Φ))` for every small
`τ₁` and large `D` gives `≺ 1 + Φ`. -/
theorem stochDom_of_logBound {ξ : ∀ N, U N → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    {c₁ : ℝ} (hc₁ : 0 < c₁) (p q : ℕ)
    (hgood : ∀ τ₁ > (0 : ℝ), τ₁ ≤ 1 → ∀ D > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ Ev : ℕ → Set Ω,
      HighProb P Ev ∧ ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ev N, ∀ u,
        ξ N u ω ≤ C * (N : ℝ) ^ ((p : ℝ) * τ₁) * (1 + Real.log N) * (1 + Φ N)
          + C * (N : ℝ) ^ q * ((N : ℝ) ^ (-D) + exp (-(c₁ * (N : ℝ) ^ τ₁)) * (1 + Φ N))) :
    StochDom P ξ (fun N _ _ => 1 + Φ N) := by
  refine stochDom_of_three hΦ (stochDom_of_good fun τ hτ => ?_)
  set τ₁ := min τ 1 / (2 * (p + 2)) with hτ₁
  have hmin0 : 0 < min τ 1 := lt_min hτ one_pos
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁1 : τ₁ ≤ 1 := by
    rw [hτ₁, div_le_one (by positivity)]
    have := min_le_right τ 1
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith
  have hexp : ((p : ℝ) + 1) * τ₁ < τ := by
    rw [hτ₁, mul_div_assoc', div_lt_iff₀ (by positivity)]
    have := min_le_left τ 1
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith
  set D : ℝ := q + 1 with hD
  obtain ⟨C, hC0, Ev, hEv, hev⟩ := hgood τ₁ hτ₁0 hτ₁1 D (by positivity)
  refine ⟨Ev, hEv, ?_⟩
  have hf1 := eventually_const_mul_rpow_le (C * (1 + 1 / τ₁)) hexp
  have hf2 := eventually_const_mul_rpow_le C (show (q : ℝ) < D by rw [hD]; linarith)
  have hf3 := eventually_exp_small C q c₁ hc₁ hτ₁0
  filter_upwards [hev, hf1, hf2, hf3, eventually_ge_atTop 1] with N hN hf1 hf2 hf3 hN1
  intro ω hω u
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNτ : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1' hτ.le
  have hNτ₁ : 1 ≤ (N : ℝ) ^ τ₁ := Real.one_le_rpow hN1' hτ₁0.le
  have hΦN := hΦ N
  have hlog : 1 + Real.log N ≤ (1 + 1 / τ₁) * (N : ℝ) ^ τ₁ := by
    have := log_le_rpow_div_nat N hτ₁0
    have e : (1 + 1 / τ₁) * (N : ℝ) ^ τ₁ = (N : ℝ) ^ τ₁ + (N : ℝ) ^ τ₁ / τ₁ := by ring
    rw [e]; linarith
  have hmain : C * (N : ℝ) ^ ((p : ℝ) * τ₁) * (1 + Real.log N) * (1 + Φ N)
      ≤ (N : ℝ) ^ τ * (1 + Φ N) := by
    have h1 : C * (N : ℝ) ^ ((p : ℝ) * τ₁) * (1 + Real.log N)
        ≤ C * (1 + 1 / τ₁) * (N : ℝ) ^ (((p : ℝ) + 1) * τ₁) := by
      have e : (N : ℝ) ^ (((p : ℝ) + 1) * τ₁) = (N : ℝ) ^ ((p : ℝ) * τ₁) * (N : ℝ) ^ τ₁ := by
        rw [← Real.rpow_add hN0]; ring_nf
      rw [e]
      have : 0 ≤ C * (N : ℝ) ^ ((p : ℝ) * τ₁) := by positivity
      calc C * (N : ℝ) ^ ((p : ℝ) * τ₁) * (1 + Real.log N)
          ≤ C * (N : ℝ) ^ ((p : ℝ) * τ₁) * ((1 + 1 / τ₁) * (N : ℝ) ^ τ₁) := by gcongr
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right (h1.trans hf1) (by linarith)
  have herr : C * (N : ℝ) ^ q * ((N : ℝ) ^ (-D) + exp (-(c₁ * (N : ℝ) ^ τ₁)) * (1 + Φ N))
      ≤ 2 + Φ N := by
    have hq : (N : ℝ) ^ q = (N : ℝ) ^ (q : ℝ) := (Real.rpow_natCast _ _).symm
    rw [hq]
    have hD' : C * (N : ℝ) ^ (q : ℝ) * (N : ℝ) ^ (-D) ≤ 1 := by
      calc C * (N : ℝ) ^ (q : ℝ) * (N : ℝ) ^ (-D) ≤ (N : ℝ) ^ D * (N : ℝ) ^ (-D) :=
            mul_le_mul_of_nonneg_right hf2 (Real.rpow_nonneg hN0.le _)
        _ = 1 := by rw [← Real.rpow_add hN0]; simp
    have := mul_le_mul_of_nonneg_right hf3 (by linarith : (0 : ℝ) ≤ 1 + Φ N)
    have e : C * (N : ℝ) ^ (q : ℝ) * ((N : ℝ) ^ (-D) + exp (-(c₁ * (N : ℝ) ^ τ₁)) * (1 + Φ N))
        = C * (N : ℝ) ^ (q : ℝ) * (N : ℝ) ^ (-D)
          + C * (N : ℝ) ^ (q : ℝ) * exp (-(c₁ * (N : ℝ) ^ τ₁)) * (1 + Φ N) := by ring
    rw [e]; linarith
  calc ξ N u ω ≤ _ := hN ω hω u
    _ ≤ (N : ℝ) ^ τ * (1 + Φ N) + (2 + Φ N) := add_le_add hmain herr
    _ ≤ (N : ℝ) ^ τ * (3 * (1 + Φ N)) := by nlinarith

end Master

/-! ### The generic `≺`-assembly of a time-integral term of (5.94) -/

section GenericTerms

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

theorem rpow_le_self_of_le_one {N : ℕ} (hN : (1 : ℝ) ≤ N) {τ₁ : ℝ} (hτ₁ : τ₁ ≤ 1) :
    (N : ℝ) ^ τ₁ ≤ N := by
  calc (N : ℝ) ^ τ₁ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hτ₁
    _ = N := Real.rpow_one _

set_option maxHeartbeats 1000000 in
/-- **The integral terms of (5.94), assembled.**  Let `G_u` be a family of tensors which, for
every small `τ₁` and large `D`, on a high-probability event and uniformly in `u ∈ [s,t]` and `σ`,
is sum-zero, `(ℓ_u c₀N^{τ₁}, ε)`-fast-decaying and bounded by
`(Wℓ_uη_u)^{-m} C N^{pτ₁} Φ (1-u)^{-1} + ε`, with `ε = C N^q (N^{-D} + e^{-c₁N^{τ₁}}(1 + Φ))`.
Then `(Wℓ_vη_v)^m |∫_s^v U_{u,v,σ} ∘ G_u du| ≺ 1 + Φ`, uniformly in `v ∈ [s,t]`, `σ`, `a`.
This is (5.93) + the time integration, with all the `W^{Cτ}`, `log` and `W^{-D}` losses. -/
theorem integral_term_stochDom (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (G : ∀ N, ℝ → Ω → (Fin (n + 2) → Bool) → LoopArg (B.L N) (n + 2) → ℂ)
    {c₀ c₁ : ℝ} (hc₀ : 1 ≤ c₀) (hc₁ : 0 < c₁) (p q : ℕ)
    (hgood : ∀ τ₁ > (0 : ℝ), τ₁ ≤ 1 → ∀ D > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ Ev : ℕ → Set Ω,
      HighProb B.P Ev ∧ ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ev N, ∀ (σ : Fin (n + 2) → Bool) (u : ℝ),
        s N ≤ u → u ≤ t N →
        SumZero (B.L N) (G N u ω σ) ∧
        FastDecay (B.L N) (B.ell N u * (c₀ * (N : ℝ) ^ τ₁))
          (C * (N : ℝ) ^ q * ((N : ℝ) ^ (-D) + exp (-(c₁ * (N : ℝ) ^ τ₁)) * (1 + Φ N)))
          (G N u ω σ) ∧
        ∀ b, ‖G N u ω σ b‖ ≤ (B.scale E N u)⁻¹ ^ (n + 2)
            * ((C * (N : ℝ) ^ ((p : ℝ) * τ₁) * Φ N) * (1 - u)⁻¹)
          + C * (N : ℝ) ^ q * ((N : ℝ) ^ (-D) + exp (-(c₁ * (N : ℝ) ^ τ₁)) * (1 + Φ N))) :
    StochDom B.P (fun N (pp : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      B.scale E N pp.1 ^ (n + 2) * ‖∫ u in (s N)..(pp.1 : ℝ),
        Uker (B.L N) (xiOf (mSigma E) pp.2.1) (u : ℂ) ((pp.1 : ℝ) : ℂ) (G N u ω pp.2.1) pp.2.2‖)
      (fun N _ _ => 1 + Φ N) := by
  suffices h : StochDom B.P (fun N (pp : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      B.scale E N pp.1 ^ (n + 2) * ‖∫ u in (s N)..(pp.1 : ℝ),
        Uker (B.L N) (xiOf (mSigma E) pp.2.1) (u : ℂ) ((pp.1 : ℝ) : ℂ) (G N u ω pp.2.1) pp.2.2‖)
      (fun N _ _ => 3 * (1 + Φ N)) by
    have h' := StochDom.const_mul_right (c := 3⁻¹) (by norm_num)
      (fun N _ _ => by have := hΦ N; positivity) h
    refine StochDom.of_subset h' fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N ω hω => ?_⟩
    obtain ⟨u, hu⟩ := hω
    exact ⟨u, by simpa [badSet, ← mul_assoc] using hu⟩
  refine stochDom_of_good fun τ hτ => ?_
  set τ₁ := min τ 1 / (2 * (2 * (n + 2) + p + 1)) with hτ₁
  have hmin0 : 0 < min τ 1 := lt_min hτ one_pos
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁1 : τ₁ ≤ 1 := by
    rw [hτ₁, div_le_one (by positivity)]
    have := min_le_right τ 1
    have : (1 : ℝ) ≤ 2 * (2 * (n + 2) + p + 1) := by
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      have : (0 : ℝ) ≤ (n + 2) := by positivity
      linarith
    linarith
  have hexp : (2 * (n + 2) + p + 1 : ℝ) * τ₁ < τ := by
    rw [hτ₁, mul_div_assoc', div_lt_iff₀ (by positivity)]
    have := min_le_left τ 1
    have : (0 : ℝ) < 2 * (n + 2) + p + 1 := by positivity
    nlinarith
  set q' : ℕ := 4 * (n + 2) + q with hq'
  set D : ℝ := q' + 1 with hD
  obtain ⟨C, hC0, Ev, hEv, hev⟩ := hgood τ₁ hτ₁0 hτ₁1 D (by positivity)
  refine ⟨Ev, hEv, ?_⟩
  set C₂ := (cKerSumZero (n + 2) * c₀ ^ (2 * (n + 2)) + cKerSumZeroErr (n + 2)) * C with hC₂
  have hf1 := eventually_const_mul_rpow_le (cKerSumZero (n + 2) * c₀ ^ (2 * (n + 2)) * C / τ₁) hexp
  have hf2 := eventually_const_mul_rpow_le C₂ (show (q' : ℝ) < D by rw [hD]; linarith)
  have hf3 := eventually_exp_small C₂ q' c₁ hc₁ hτ₁0
  filter_upwards [hev, flow_crude hE (fun N => (hs0 N).le) hst ht1 hc, hf1, hf2, hf3] with
    N hN ⟨hLN, hWN, hN1, hu⟩ hf1 hf2 hf3
  intro ω hω pp
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNτ : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1' hτ.le
  have hNτ₁ : 1 ≤ (N : ℝ) ^ τ₁ := Real.one_le_rpow hN1' hτ₁0.le
  have hNτ₁N : (N : ℝ) ^ τ₁ ≤ N := rpow_le_self_of_le_one hN1' hτ₁1
  have hΦN := hΦ N
  have hL3 := B.three_le_L N
  obtain ⟨⟨v, hsv, hvt⟩, σ, a⟩ := pp
  have hv0 : 0 < v := (hs0 N).trans_le hsv
  have hv1 : v < 1 := hvt.trans_lt (ht1 N)
  obtain ⟨hA1, hAN, hvN⟩ := hu ⟨v, hsv, hvt⟩
  simp only at hA1 hAN hvN ⊢
  set K := c₀ * (N : ℝ) ^ τ₁ with hK
  have hK1 : 1 ≤ K := by nlinarith
  set ψ := C * (N : ℝ) ^ ((p : ℝ) * τ₁) * Φ N with hψ
  set ε := C * (N : ℝ) ^ q * ((N : ℝ) ^ (-D) + exp (-(c₁ * (N : ℝ) ^ τ₁)) * (1 + Φ N)) with hε
  have hψ0 : 0 ≤ ψ := by positivity
  have hε0 : 0 ≤ ε := by positivity
  set κA := (B.W N : ℝ) * (mE E).im with hκA
  have hκA0 : 0 < κA := mul_pos (by exact_mod_cast B.W_pos N) (mE_im_pos hE)
  have hG' : ∀ u, s N ≤ u → u ≤ v → SumZero (B.L N) (G N u ω σ) ∧
      FastDecay (B.L N) (ellHat (B.L N) (u : ℂ) * K) ε (G N u ω σ) ∧
      ∀ b, ‖G N u ω σ b‖ ≤ (κA * ((1 - u) * ellHat (B.L N) (u : ℂ)))⁻¹ ^ (n + 2) * (ψ * (1 - u)⁻¹)
        + ε := by
    intro u hsu huv
    obtain ⟨h1, h2, h3⟩ := hN ω hω σ u hsu (huv.trans hvt)
    refine ⟨h1, h2, fun b => ?_⟩
    have := h3 b
    rwa [Band.scale_eq] at this
  have key := integral_term_le (B.L N) hL3 hE.le σ (hs0 N).le hsv hv0.le hv1 hκA0 hK1 hψ0 hε0 hε0 hG' a
  rw [← Band.scale_eq B E N v] at key
  -- the scales
  have h1v : 0 < 1 - v := by linarith
  have hρ1 : 1 ≤ (1 - s N) / (1 - v) := by rw [le_div_iff₀ h1v]; linarith
  have hρN : (1 - s N) / (1 - v) ≤ N := by
    calc (1 - s N) / (1 - v) ≤ 1 / (1 - v) :=
          div_le_div_of_nonneg_right (by linarith [hs0 N]) h1v.le
      _ = (1 - v)⁻¹ := one_div _
      _ ≤ N := hvN
  have hlog : Real.log ((1 - s N) / (1 - v)) ≤ (N : ℝ) ^ τ₁ / τ₁ :=
    (Real.log_le_log (by linarith) hρN).trans (log_le_rpow_div_nat N hτ₁0)
  have hvs : v - s N ≤ 1 := by linarith [hs0 N]
  have hvs0 : 0 ≤ v - s N := by linarith
  -- the main term
  have hmain : cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ψ * Real.log ((1 - s N) / (1 - v))
      ≤ (N : ℝ) ^ τ * Φ N := by
    have hc := cKerSumZero_nonneg (n + 2)
    have hKp : K ^ (2 * (n + 2)) = c₀ ^ (2 * (n + 2)) * (N : ℝ) ^ (τ₁ * ((2 * (n + 2) : ℕ) : ℝ)) := by
      rw [hK, mul_pow, rpow_pow_eq]
    calc cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ψ * Real.log ((1 - s N) / (1 - v))
        ≤ cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ψ * ((N : ℝ) ^ τ₁ / τ₁) := by gcongr
      _ = (cKerSumZero (n + 2) * c₀ ^ (2 * (n + 2)) * C / τ₁)
          * ((N : ℝ) ^ (τ₁ * ((2 * (n + 2) : ℕ) : ℝ)) * (N : ℝ) ^ ((p : ℝ) * τ₁) * (N : ℝ) ^ τ₁) * Φ N := by
          rw [hKp, hψ]; field_simp
      _ = (cKerSumZero (n + 2) * c₀ ^ (2 * (n + 2)) * C / τ₁) * (N : ℝ) ^ ((2 * (n + 2) + p + 1 : ℝ) * τ₁) * Φ N := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 3; push_cast; ring
      _ ≤ (N : ℝ) ^ τ * Φ N := mul_le_mul_of_nonneg_right hf1 hΦN
  -- the error term
  have herr : B.scale E N v ^ (n + 2)
      * ((cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s N) / (1 - v)) ^ (n + 2) * ε
        + cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2) * ((1 - s N) / (1 - v)) ^ (n + 2) * ε)
        * (v - s N)) ≤ 2 + Φ N := by
    have hc := cKerSumZero_nonneg (n + 2)
    have hc' := cKerSumZeroErr_nonneg (n + 2)
    have hKN : K ≤ c₀ * N := by rw [hK]; gcongr
    have hA0 : 0 ≤ B.scale E N v := by linarith
    have hpoly := err_scalar (m := n + 2) hA0 hAN (by linarith) hρN (Nat.cast_nonneg _) hLN
      (by linarith) hKN hN1' hc₀ hε0 hc hc' hvs0 hvs
    have hq : (N : ℝ) ^ (4 * (n + 2)) * ε
        = C * (N : ℝ) ^ (q' : ℝ) * ((N : ℝ) ^ (-D) + exp (-(c₁ * (N : ℝ) ^ τ₁)) * (1 + Φ N)) := by
      rw [hε, hq', Real.rpow_natCast]; ring
    have hfin : (cKerSumZero (n + 2) * c₀ ^ (2 * (n + 2)) + cKerSumZeroErr (n + 2)) * (N : ℝ) ^ (4 * (n + 2)) * ε
        ≤ 2 + Φ N := by
      rw [mul_assoc, hq]
      have e2 : (cKerSumZero (n + 2) * c₀ ^ (2 * (n + 2)) + cKerSumZeroErr (n + 2))
          * (C * (N : ℝ) ^ (q' : ℝ) * ((N : ℝ) ^ (-D) + exp (-(c₁ * (N : ℝ) ^ τ₁)) * (1 + Φ N)))
          = C₂ * (N : ℝ) ^ (q' : ℝ) * (N : ℝ) ^ (-D)
            + C₂ * (N : ℝ) ^ (q' : ℝ) * exp (-(c₁ * (N : ℝ) ^ τ₁)) * (1 + Φ N) := by
        rw [hC₂]; ring
      rw [e2]
      have hD' : C₂ * (N : ℝ) ^ (q' : ℝ) * (N : ℝ) ^ (-D) ≤ 1 := by
        calc C₂ * (N : ℝ) ^ (q' : ℝ) * (N : ℝ) ^ (-D) ≤ (N : ℝ) ^ D * (N : ℝ) ^ (-D) :=
              mul_le_mul_of_nonneg_right hf2 (Real.rpow_nonneg hN0.le _)
          _ = 1 := by rw [← Real.rpow_add hN0]; simp
      have := mul_le_mul_of_nonneg_right hf3 (by linarith : (0 : ℝ) ≤ 1 + Φ N)
      linarith
    exact hpoly.trans hfin
  calc B.scale E N v ^ (n + 2) * ‖∫ u in (s N)..v,
        Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) (G N u ω σ) a‖
      ≤ _ := key
    _ ≤ (N : ℝ) ^ τ * Φ N + (2 + Φ N) := add_le_add hmain herr
    _ ≤ (N : ℝ) ^ τ * (3 * (1 + Φ N)) := by nlinarith

end GenericTerms

/-! ### Lemma 5.14 for `QGood` charges: the terms of (5.94) -/

section TermsQ

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

theorem norm_lkT_le_of_xiLK {N : ℕ} {u : ℝ} {ω : Ω} {m : ℕ} (σ : Fin m → Bool)
    (a : LoopArg (B.L N) m) (hA : 0 < B.scale E N u) {φ : ℝ} (h : X.xiLK E N u ω m ≤ φ) :
    ‖lkT X E N u ω σ a‖ ≤ φ * (B.scale E N u)⁻¹ ^ m := by
  have h1 := norm_lkT_le X E N u ω σ a
  have : X.lkMax E N u ω m = X.xiLK E N u ω m * (B.scale E N u)⁻¹ ^ m := by
    rw [Sample.xiLK, mul_assoc, ← mul_pow, mul_inv_cancel₀ hA.ne', one_pow, mul_one]
  rw [this] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right h (by positivity))

/-- The last term of (5.101), `(W ℓ_v η_v)^m (P ∘ (L-K)_v)_{a₁} ϑ_{v,a} ≺ 1 + Φ`, from Ward's
identity (5.96) and `Ξ^{(L-K)}_{v,m-1} ≺ Φ`. -/
theorem termP (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {n : ℕ} (hW : WardP X E n) (hdec : LKDecay X E s t)
    {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hX : StochDom B.P (Step3.flowXiLK X E s t (n + 1)) (fun N _ _ => Φ N)) :
    StochDom B.P (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      if QGood p.2.1 then B.scale E N p.1 ^ (n + 2)
        * (‖Psum (B.L N) (lkT X E N p.1 ω p.2.1) (p.2.2 0)‖
          * ‖vartheta (B.L N) ((p.1 : ℝ) : ℂ) p.2.2‖) else 0)
      (fun N _ _ => 1 + Φ N) := by
  classical
  refine stochDom_of_good fun τ hτ => ?_
  set τ₁ := τ / (2 * (n + 2)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  set D : ℝ := 2 * n + 3 + τ₁ with hD
  have hG1 := good_of_stochDom hX hτ₁0
  have hG2 := good_of_stochDom (hdec (n + 1) (by omega) τ₁ hτ₁0 D (by positivity)) hτ₁0
  refine ⟨_, hG1.inter hG2, ?_⟩
  have ha : τ₁ * (n + 1) < τ := by
    rw [hτ₁, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hfin := eventually_finish ((6 * exp 1) ^ n * cTwo52 ^ (n + 1)) (2 ^ n * cTwo52 ^ (n + 1))
    ha (show (2 * n + 1 : ℝ) + τ₁ < D by rw [hD]; linarith)
  filter_upwards [flow_crude hE (fun N => (hs0 N).le) hst ht1 hc, hfin] with N ⟨hLN, hWN, hN1, hu⟩ ⟨hf1, hf2⟩
  intro ω ⟨hω1, hω2⟩ p
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNτ : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1' hτ.le
  have hNτ₁ : 1 ≤ (N : ℝ) ^ τ₁ := Real.one_le_rpow hN1' hτ₁0.le
  simp only [Set.mem_ofPred_eq] at hω1 hω2
  split_ifs with hq
  · obtain ⟨σ', σ'', hw⟩ := hW p.2.1 hq
    set u : ℝ := (p.1 : ℝ) with hudef
    have hu0 : 0 ≤ u := ((hs0 N).trans_le p.1.2.1).le
    have hu1 : u < 1 := p.1.2.2.trans_lt (ht1 N)
    obtain ⟨hA1, hAN, -⟩ := hu p.1
    have hA0 : 0 < B.scale E N u := by linarith
    have hL3 := B.three_le_L N
    have hℓ := half_le_ellHat_real (B.L N) hL3 hu0 hu1
    have hℓ0 : 0 < B.ell N u := by
      show 0 < ellHat (B.L N) (u : ℂ); linarith
    have hΦN := hΦ N
    have hbd : ∀ (ρ : Fin (n + 1) → Bool) b,
        ‖lkT X E N u ω ρ b‖ ≤ (N : ℝ) ^ τ₁ * Φ N * (B.scale E N u)⁻¹ ^ (n + 1) :=
      fun ρ b => norm_lkT_le_of_xiLK X ρ b hA0 (hω1 p.1)
    have hfd : ∀ ρ : Fin (n + 1) → Bool, FastDecay (B.L N) (B.ell N u * (N : ℝ) ^ τ₁)
        ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)) (lkT X E N u ω ρ) :=
      fun ρ => fastDecay_of_farInd fun b => hω2 (p.1, (ρ, b))
    have hP := norm_Psum_le_of_ward (B.L N) (hw N u hu0 hu1 ω (p.2.2 0))
      (by positivity) (by positivity) (by positivity) (hbd σ') (hbd σ'') (hfd σ') (hfd σ'')
    rw [norm_wardKappa (B.W N) hE hu1] at hP
    have hϑ := norm_vartheta_real_le (B.L N) hL3 hu0 hu1 p.2.2
    have hη := etaT_pos hE hu1
    have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    have key := scalarP (n := n) (A := B.scale E N u) (W := B.W N) (η := etaT E u)
      (ℓ := B.ell N u) (Lr := B.L N) (K := (N : ℝ) ^ τ₁) (Φ := Φ N)
      (δ := (N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)) (c := cTwo52) rfl hW0 hη hℓ hNτ₁ hΦN
      (by positivity) cTwo52_pos.le (Nat.cast_nonneg _)
    have hpos : 0 ≤ B.scale E N u ^ (n + 2) := by positivity
    calc B.scale E N u ^ (n + 2) * (‖Psum (B.L N) (lkT X E N u ω p.2.1) (p.2.2 0)‖
          * ‖vartheta (B.L N) (u : ℂ) p.2.2‖)
        ≤ B.scale E N u ^ (n + 2) * (((2 * (B.W N : ℝ) * etaT E u)⁻¹ * (2 * ((2 * exp 1
            * (B.ell N u * (N : ℝ) ^ τ₁ + 1)) ^ n * ((N : ℝ) ^ τ₁ * Φ N * (B.scale E N u)⁻¹ ^ (n + 1))
            + (B.L N : ℝ) ^ n * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D))))) * (cTwo52 / B.ell N u) ^ (n + 1)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hP hϑ (norm_nonneg _) ?_) hpos
          positivity
      _ ≤ (6 * exp 1) ^ n * cTwo52 ^ (n + 1) * ((N : ℝ) ^ τ₁) ^ (n + 1) * Φ N
          + 2 ^ n * cTwo52 ^ (n + 1) * B.scale E N u ^ (n + 1) * (B.L N : ℝ) ^ n
            * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)) := key
      _ ≤ (N : ℝ) ^ τ * Φ N + 1 := by
          refine add_le_add ?_ ?_
          · rw [rpow_pow_eq]
            have : ((6 * exp 1) ^ n * cTwo52 ^ (n + 1) * (N : ℝ) ^ (τ₁ * ((n + 1 : ℕ) : ℝ)))
                ≤ (N : ℝ) ^ τ := by push_cast; exact hf1
            exact mul_le_mul_of_nonneg_right this hΦN
          · have h1 := natCast_pow_le_rpow hA0.le hAN (n + 1)
            have h2 := natCast_pow_le_rpow (Nat.cast_nonneg _) hLN n
            have hc0 : 0 ≤ 2 ^ n * cTwo52 ^ (n + 1) := by have := cTwo52_pos; positivity
            have e : (N : ℝ) ^ ((n + 1 : ℕ) : ℝ) * (N : ℝ) ^ ((n : ℕ) : ℝ) * (N : ℝ) ^ τ₁
                = (N : ℝ) ^ ((2 * n + 1 : ℝ) + τ₁) := by
              rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; push_cast; ring
            calc 2 ^ n * cTwo52 ^ (n + 1) * B.scale E N u ^ (n + 1) * (B.L N : ℝ) ^ n
                  * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D))
                ≤ 2 ^ n * cTwo52 ^ (n + 1) * (N : ℝ) ^ ((n + 1 : ℕ) : ℝ) * (N : ℝ) ^ ((n : ℕ) : ℝ)
                  * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)) := by gcongr
              _ = 2 ^ n * cTwo52 ^ (n + 1) * ((N : ℝ) ^ ((n + 1 : ℕ) : ℝ) * (N : ℝ) ^ ((n : ℕ) : ℝ)
                  * (N : ℝ) ^ τ₁) * (N : ℝ) ^ (-D) := by ring
              _ = 2 ^ n * cTwo52 ^ (n + 1) * (N : ℝ) ^ ((2 * n + 1 : ℝ) + τ₁) * (N : ℝ) ^ (-D) := by
                  rw [e]
              _ ≤ 1 := hf2
      _ ≤ (N : ℝ) ^ τ * (1 + Φ N) := by nlinarith
  · have := hΦ N
    positivity

/-- The right side of (5.77) is `≺ (2n+3) Φ` under the hypotheses of `Step3.Lemma514`. -/
theorem xiRhs_stochDom {n : ℕ} {Φ : ℕ → ℝ}
    (hX1 : ∀ m, 1 ≤ m → m < n + 2 →
      StochDom B.P (Step3.flowXiLK X E s t m) (fun N _ _ => Φ N))
    (hX2 : ∀ m, 2 ≤ m → m ≤ n + 2 →
      StochDom B.P (fun N u ω => Step3.flowXiLK X E s t m N u ω
        * Step3.flowXiLK X E s t (n + 2 - m + 2) N u ω * (Step3.flowA B E s t N u)⁻¹)
        (fun N _ _ => Φ N))
    (hY : StochDom B.P (Step3.flowXiL X E s t (n + 2 + 1)) (fun N _ _ => Φ N)) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => xiRhs X E (n + 2) N u ω)
      (fun N _ _ => (2 * n + 3 : ℝ) * Φ N) := by
  have h1 := stochDom_finset_sum (P := B.P) (Finset.Ico 1 (n + 2))
    (ξ := fun k => Step3.flowXiLK X E s t k) (ζ := fun N _ _ => Φ N)
    (fun k hk => by rw [Finset.mem_Ico] at hk; exact hX1 k hk.1 hk.2)
  have h2 := stochDom_finset_sum (P := B.P) (Finset.Icc 2 (n + 2))
    (ξ := fun k N u ω => Step3.flowXiLK X E s t k N u ω
        * Step3.flowXiLK X E s t (n + 2 - k + 2) N u ω * (Step3.flowA B E s t N u)⁻¹)
    (ζ := fun N _ _ => Φ N)
    (fun k hk => by rw [Finset.mem_Icc] at hk; exact hX2 k hk.1 hk.2)
  have h3 := (h1.add h2).add hY
  have hc1 : ((Finset.Ico 1 (n + 2)).card : ℝ) = n + 1 := by
    rw [Nat.card_Ico]; push_cast; ring
  have hc2 : ((Finset.Icc 2 (n + 2)).card : ℝ) = n + 1 := by
    rw [Nat.card_Icc]; push_cast; ring
  refine StochDom.of_le_left (fun N u ω => le_refl _) (StochDom.of_subset h3 fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun N ω hω => ?_⟩)
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  simp only [Pi.add_apply, hc1, hc2] at hu ⊢
  have e : xiRhs X E (n + 2) N u ω
      = ∑ i ∈ Finset.Ico 1 (n + 2), Step3.flowXiLK X E s t i N u ω
        + ∑ i ∈ Finset.Icc 2 (n + 2), Step3.flowXiLK X E s t i N u ω
            * Step3.flowXiLK X E s t (n + 2 - i + 2) N u ω * (Step3.flowA B E s t N u)⁻¹
        + Step3.flowXiL X E s t (n + 2 + 1) N u ω := rfl
  rw [e] at hu
  have : (N : ℝ) ^ τ * ((n + 1) * Φ N + (n + 1) * Φ N + Φ N) = (N : ℝ) ^ τ * ((2 * n + 3) * Φ N) := by
    ring
  linarith

/-- **(5.77) + the hypotheses of Lemma 5.14**: the drift is `≺ (Wℓ_uη_u)^{-m} η_u^{-1} (2n+3) Φ`. -/
theorem F_stochDom (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1) {n : ℕ}
    (H : Hierarchy X E s t n) (h510 : Lemma510 X E s t H) {Φ : ℕ → ℝ}
    (hxi : StochDom B.P (fun N (u : TimeIcc s t N) ω => xiRhs X E (n + 2) N u ω)
      (fun N _ _ => (2 * n + 3 : ℝ) * Φ N)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω => ‖H.F N p.1 ω p.2.1 p.2.2‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n + 2) * (etaT E p.1)⁻¹ * ((2 * n + 3 : ℝ) * Φ N)) := by
  have hpos : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)), 0 < B.scale E N p.1 := fun N p =>
    B.scale_pos hE N ((hs0 N).trans_le p.1.2.1) (p.1.2.2.trans_lt (ht1 N))
  have hη : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)), 0 < etaT E p.1 := fun N p =>
    etaT_pos hE (p.1.2.2.trans_lt (ht1 N))
  have hg : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) (_ : Ω),
      0 ≤ (B.scale E N p.1)⁻¹ ^ (n + 2) * (etaT E p.1)⁻¹ := fun N p _ => by
    have := hpos N p; have := hη N p; positivity
  have hxi0 : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω,
      0 ≤ xiRhs X E (n + 2) N p.1 ω := fun N p ω => by
    have hA := (hpos N p).le
    unfold xiRhs
    refine add_nonneg (add_nonneg (Finset.sum_nonneg fun k _ => X.xiLK_nonneg hA)
      (Finset.sum_nonneg fun k _ => ?_)) (X.xiL_nonneg hA)
    exact mul_nonneg (mul_nonneg (X.xiLK_nonneg hA) (X.xiLK_nonneg hA)) (inv_nonneg.2 hA)
  have hm := StochDom.mul hxi0 hg (StochDom.refl hg)
    (hxi.precomp_param (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) => p.1))
  exact h510.F_le.trans hm

/-- The high-probability bounds on `Q_u ∘ F_u`, in the shape of `integral_term_stochDom`
(Lemma 5.13 applied to the drift, with (5.77)). -/
theorem hgood_QF (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ} (H : Hierarchy X E s t n)
    (h510 : Lemma510 X E s t H) {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hF : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω => ‖H.F N p.1 ω p.2.1 p.2.2‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n + 2) * (etaT E p.1)⁻¹ * ((2 * n + 3 : ℝ) * Φ N))) :
    ∀ τ₁ > (0 : ℝ), τ₁ ≤ 1 → ∀ D > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ Ev : ℕ → Set Ω,
      HighProb B.P Ev ∧ ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ev N, ∀ (σ : Fin (n + 2) → Bool) (u : ℝ),
        s N ≤ u → u ≤ t N →
        SumZero (B.L N) (Qop (B.L N) (u : ℂ) (H.F N u ω σ)) ∧
        FastDecay (B.L N) (B.ell N u * (1 * (N : ℝ) ^ τ₁))
          (C * (N : ℝ) ^ (n + 3) * ((N : ℝ) ^ (-D) + exp (-(cZero / 4 * (N : ℝ) ^ τ₁)) * (1 + Φ N)))
          (Qop (B.L N) (u : ℂ) (H.F N u ω σ)) ∧
        ∀ b, ‖Qop (B.L N) (u : ℂ) (H.F N u ω σ) b‖ ≤ (B.scale E N u)⁻¹ ^ (n + 2)
            * ((C * (N : ℝ) ^ (((n + 2 : ℕ) : ℝ) * τ₁) * Φ N) * (1 - u)⁻¹)
          + C * (N : ℝ) ^ (n + 3) * ((N : ℝ) ^ (-D) + exp (-(cZero / 4 * (N : ℝ) ^ τ₁)) * (1 + Φ N)) := by
  intro τ₁ hτ₁ hτ₁1 D hD
  set c := cTwo52 with hcdef
  set im := (mE E).im with himdef
  have him : 0 < im := mE_im_pos hE
  set Cf : ℝ := 2 * n + 3 with hCf
  have hCf0 : 0 ≤ Cf := by positivity
  set C := 1 + (1 + (6 * exp 1 * c) ^ (n + 1)) * Cf / im + (2 * c) ^ (n + 1) with hC
  have hc0 : 0 ≤ c := cTwo52_pos.le
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, _, (good_of_stochDom hF hτ₁).inter
    (good_of_stochDom (h510.F_decay τ₁ hτ₁ D hD) hτ₁), ?_⟩
  filter_upwards [flow_crude hE (fun N => (hs0 N).le) hst ht1 hc] with N ⟨hLN, hWN, hN1, hu⟩
  intro ω ⟨hω1, hω2⟩ σ u hsu hut
  simp only [Set.mem_ofPred_eq] at hω1 hω2
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set uu : TimeIcc s t N := ⟨u, hsu, hut⟩
  obtain ⟨hA1, hAN, huN⟩ := hu uu
  have hu0 : 0 ≤ u := ((hs0 N).trans_le hsu).le
  have hu1 : u < 1 := hut.trans_lt (ht1 N)
  have h1u : 0 < 1 - u := by linarith
  have hL3 := B.three_le_L N
  set K := (N : ℝ) ^ τ₁ with hK
  have hK1 : 1 ≤ K := Real.one_le_rpow hN1' hτ₁.le
  have hKN : K ≤ N := rpow_le_self_of_le_one hN1' hτ₁1
  set M := K * ((B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ * (Cf * Φ N)) with hM
  have hA0 : 0 < B.scale E N u := by linarith
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hΦN := hΦ N
  have hM0 : 0 ≤ M := by positivity
  set x := (N : ℝ) ^ (-D) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0.le _
  have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  have hδ0 : 0 ≤ K * x := by positivity
  have hFb : ∀ b, ‖H.F N u ω σ b‖ ≤ M := fun b => hω1 (uu, (σ, b))
  have hFd : FastDecay (B.L N) (ellHat (B.L N) (u : ℂ) * K) (K * x) (H.F N u ω σ) :=
    fastDecay_of_farInd fun b => hω2 (uu, (σ, b))
  have hQmax := norm_Qop_le_of_fastDecay (B.L N) (n := n + 1) hL3 hu0 hu1 hK1 hM0 hδ0 hFb hFd
  have hQdec := fastDecay_Qop_le (B.L N) (n := n + 1) hL3 hu0 hu1 hK1 hM0 hδ0 hFb hFd
  have hetaT : etaT E u = (1 - u) * im := rfl
  refine ⟨SumZero_Qop (B.L N) hL3 (norm_ofReal_lt_one hu0 hu1) _, ?_, fun b => ?_⟩
  · rw [one_mul]
    refine FastDecay.mono (B.L N) hQdec le_rfl ?_
    have hee : exp (-(cZero * K / 2)) ≤ exp (-(cZero / 4 * K)) := by
      apply exp_le_exp.2
      have := cZero_pos
      nlinarith
    have key := QF_scalar_dec (n := n) (K := K) (A := B.scale E N u) (u := u) (im := im) (Cf := Cf)
      (Φ := Φ N) (c := c) (Lr := B.L N) (Nr := N) (x := x) (e := exp (-(cZero * K / 2)))
      (e' := exp (-(cZero / 4 * K))) hK1 hKN hA1 h1u huN him hCf0 hΦN hc0 (Nat.cast_nonneg _) hLN
      hx0 hx1 (exp_pos _).le hee hN1'
    rw [hM, hetaT]
    refine key.trans ?_
    have hc6 : (6 * exp 1 * c) ^ (n + 1) * Cf / im ≤ (1 + (6 * exp 1 * c) ^ (n + 1)) * Cf / im := by
      gcongr; linarith
    have : 0 ≤ (N : ℝ) ^ (n + 3) * (x + exp (-(cZero / 4 * K)) * (1 + Φ N)) := by positivity
    calc (1 + (6 * exp 1 * c) ^ (n + 1) * Cf / im + (2 * c) ^ (n + 1)) * (N : ℝ) ^ (n + 3)
          * (x + exp (-(cZero / 4 * K)) * (1 + Φ N))
        = (1 + (6 * exp 1 * c) ^ (n + 1) * Cf / im + (2 * c) ^ (n + 1))
          * ((N : ℝ) ^ (n + 3) * (x + exp (-(cZero / 4 * K)) * (1 + Φ N))) := by ring
      _ ≤ C * ((N : ℝ) ^ (n + 3) * (x + exp (-(cZero / 4 * K)) * (1 + Φ N))) := by
          gcongr; rw [hC]; linarith
      _ = _ := by ring
  · refine (hQmax b).trans ?_
    have key := QF_scalar_max (n := n) (K := K) (A := B.scale E N u) (u := u) (im := im) (Cf := Cf)
      (Φ := Φ N) (c := c) (Lr := B.L N) (Nr := N) (x := x) hK1 hKN hA0 h1u him hCf0 hΦN hc0
      (Nat.cast_nonneg _) hLN hx0
    rw [hM, hetaT]
    refine key.trans (add_le_add ?_ ?_)
    · rw [show ((n + 2 : ℕ) : ℝ) * τ₁ = τ₁ * ((n + 2 : ℕ) : ℝ) by ring, ← rpow_pow_eq]
      have hK' : 0 ≤ K ^ (n + 2) := by positivity
      have hCC : (1 + (6 * exp 1 * c) ^ (n + 1)) * Cf / im ≤ C := by
        rw [hC]; have : 0 ≤ (2 * c) ^ (n + 1) := by positivity
        linarith
      have : 0 ≤ Φ N * (1 - u)⁻¹ := by positivity
      have hAi : 0 ≤ (B.scale E N u)⁻¹ ^ (n + 2) := by positivity
      calc (B.scale E N u)⁻¹ ^ (n + 2)
            * ((1 + (6 * exp 1 * c) ^ (n + 1)) * Cf / im * K ^ (n + 2) * Φ N * (1 - u)⁻¹)
          = (B.scale E N u)⁻¹ ^ (n + 2) * (((1 + (6 * exp 1 * c) ^ (n + 1)) * Cf / im)
              * (K ^ (n + 2) * (Φ N * (1 - u)⁻¹))) := by ring
        _ ≤ (B.scale E N u)⁻¹ ^ (n + 2) * (C * (K ^ (n + 2) * (Φ N * (1 - u)⁻¹))) := by gcongr
        _ = _ := by ring
    · have hN23 : (N : ℝ) ^ (n + 2) ≤ (N : ℝ) ^ (n + 3) := pow_le_pow_right₀ hN1' (by omega)
      have hc2C : (2 * c) ^ (n + 1) ≤ C := by rw [hC]; have : 0 ≤ (1 + (6 * exp 1 * c) ^ (n + 1)) * Cf / im := by positivity
                                              linarith
      have : 0 ≤ exp (-(cZero / 4 * K)) * (1 + Φ N) := by positivity
      calc (2 * c) ^ (n + 1) * (N : ℝ) ^ (n + 2) * x ≤ C * (N : ℝ) ^ (n + 3) * x := by gcongr
        _ ≤ C * (N : ℝ) ^ (n + 3) * (x + exp (-(cZero / 4 * K)) * (1 + Φ N)) := by gcongr; linarith

/-- **The drift term of (5.94)**: `(Wℓ_vη_v)^m |∫_s^v U_{u,v,σ} ∘ Q_u ∘ F_u du| ≺ 1 + Φ`. -/
theorem termI2 (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ} (H : Hierarchy X E s t n)
    (h510 : Lemma510 X E s t H) {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hF : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω => ‖H.F N p.1 ω p.2.1 p.2.2‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n + 2) * (etaT E p.1)⁻¹ * ((2 * n + 3 : ℝ) * Φ N))) :
    StochDom B.P (fun N (pp : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      B.scale E N pp.1 ^ (n + 2) * ‖∫ u in (s N)..(pp.1 : ℝ),
        Uker (B.L N) (xiOf (mSigma E) pp.2.1) (u : ℂ) ((pp.1 : ℝ) : ℂ)
          (Qop (B.L N) (u : ℂ) (H.F N u ω pp.2.1)) pp.2.2‖)
      (fun N _ _ => 1 + Φ N) :=
  integral_term_stochDom hE hs0 hst ht1 hc hΦ (fun N u ω σ => Qop (B.L N) (u : ℂ) (H.F N u ω σ))
    le_rfl (by have := cZero_pos; positivity) (n + 2) (n + 3)
    (hgood_QF X hE hs0 hst ht1 hc H h510 hΦ hF)

theorem exp_neg_le_exp_neg {a b : ℝ} (h : a ≤ b) : exp (-b) ≤ exp (-a) :=
  exp_le_exp.2 (by linarith)

omit X in
theorem Psum_mul_left {L : ℕ} [NeZero L] {n : ℕ} (V : ZMod L → ℂ) (f : LoopArg L (n + 1) → ℂ)
    (x : ZMod L) : Psum L (fun b => V (b 0) * f b) x = V x * Psum L f x := by
  simp only [Psum, Fin.cons_zero, Finset.mul_sum]

/-- **(5.96) for the flow**: on the event where `Ξ^{(L-K)}_{u,m-1} ≤ K φ` and `L - K` decays,
Ward's identity bounds the slot sums of `(L - K)_{u,σ}` for `QGood` charges. -/
theorem norm_Psum_lkT_le (hE : |E| < 2) {n : ℕ} (hW : WardP X E n) {N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hA0 : 0 < B.scale E N u) {ω : Ω} {σ : Fin (n + 2) → Bool}
    (hq : QGood σ) {K φ δ : ℝ} (hK : 0 < K) (hφ : 0 ≤ φ) (hδ : 0 ≤ δ)
    (hX : X.xiLK E N u ω (n + 1) ≤ K * φ)
    (hdec : ∀ (ρ : Fin (n + 1) → Bool) b,
      X.lkErr E N u ω (LoopData.idx (ρ, b)) * farInd (B.L N) (B.ell N u * K) b ≤ δ)
    (x : ZMod (B.L N)) :
    ‖Psum (B.L N) (lkT X E N u ω σ) x‖
      ≤ (2 * (B.W N : ℝ) * etaT E u)⁻¹ * (2 * ((2 * exp 1 * (B.ell N u * K + 1)) ^ n
        * (K * φ * (B.scale E N u)⁻¹ ^ (n + 1)) + (B.L N : ℝ) ^ n * δ)) := by
  obtain ⟨σ', σ'', hw⟩ := hW σ hq
  have hL3 := B.three_le_L N
  have hℓ := half_le_ellHat_real (B.L N) hL3 hu0 hu1
  have hR : 0 < B.ell N u * K := by
    have : 0 < B.ell N u := by show 0 < ellHat (B.L N) (u : ℂ); linarith
    positivity
  have hbd : ∀ (ρ : Fin (n + 1) → Bool) b, ‖lkT X E N u ω ρ b‖ ≤ K * φ * (B.scale E N u)⁻¹ ^ (n + 1) :=
    fun ρ b => norm_lkT_le_of_xiLK X ρ b hA0 hX
  have hfd : ∀ ρ : Fin (n + 1) → Bool, FastDecay (B.L N) (B.ell N u * K) δ (lkT X E N u ω ρ) :=
    fun ρ => fastDecay_of_farInd fun b => hdec ρ b
  have hP := norm_Psum_le_of_ward (B.L N) (hw N u hu0 hu1 ω x) hR (by positivity) hδ
    (hbd σ') (hbd σ'') (hfd σ') (hfd σ'')
  rwa [norm_wardKappa (B.W N) hE hu1] at hP

/-- The tensor of the commutator term of (5.91), restricted to `QGood` charges. -/
noncomputable def commTerm (E : ℝ) {n : ℕ} (N : ℕ) (u : ℝ) (ω : Ω) (σ : Fin (n + 2) → Bool) :
    LoopArg (B.L N) (n + 2) → ℂ :=
  if QGood σ then commS (B.L N) (xiOf (mSigma E) σ) (u : ℂ) (lkT X E N u ω σ) else 0

/-- The tensor of the `ϑ̇` term of (5.91), restricted to `QGood` charges. -/
noncomputable def dotTerm (E : ℝ) {n : ℕ} (N : ℕ) (u : ℝ) (ω : Ω) (σ : Fin (n + 2) → Bool) :
    LoopArg (B.L N) (n + 2) → ℂ :=
  if QGood σ then (fun b => Psum (B.L N) (lkT X E N u ω σ) (b 0) * varthetaDot (B.L N) u b) else 0

set_option maxHeartbeats 1000000 in
/-- The high-probability bounds on the commutator and `ϑ̇` terms: (5.96) + (5.99), and the
decay (5.90) / of `ϑ̇`. -/
theorem hgood_commDot (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ} (hW : WardP X E n)
    (hdec : LKDecay X E s t) {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hX : StochDom B.P (Step3.flowXiLK X E s t (n + 1)) (fun N _ _ => Φ N)) (dot : Bool) :
    ∀ τ₁ > (0 : ℝ), τ₁ ≤ 1 → ∀ D > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ Ev : ℕ → Set Ω,
      HighProb B.P Ev ∧ ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ev N, ∀ (σ : Fin (n + 2) → Bool) (u : ℝ),
        s N ≤ u → u ≤ t N →
        SumZero (B.L N) ((if dot then dotTerm X E N u ω σ else commTerm X E N u ω σ)) ∧
        FastDecay (B.L N) (B.ell N u * (4 * (N : ℝ) ^ τ₁))
          (C * (N : ℝ) ^ (2 * n + 4) * ((N : ℝ) ^ (-D) + exp (-(cZero / 4 * (N : ℝ) ^ τ₁)) * (1 + Φ N)))
          ((if dot then dotTerm X E N u ω σ else commTerm X E N u ω σ)) ∧
        ∀ b, ‖(if dot then dotTerm X E N u ω σ else commTerm X E N u ω σ) b‖
          ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ((C * (N : ℝ) ^ (((n + 1 : ℕ) : ℝ) * τ₁) * Φ N) * (1 - u)⁻¹)
          + C * (N : ℝ) ^ (2 * n + 4) * ((N : ℝ) ^ (-D) + exp (-(cZero / 4 * (N : ℝ) ^ τ₁)) * (1 + Φ N)) := by
  intro τ₁ hτ₁ hτ₁1 D hD
  have hc0 : 0 ≤ cTwo52 := cTwo52_pos.le
  have hz0 := cZero_pos
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℝ, k₀ = 2 * (((n + 1 : ℕ) : ℝ) + 1) := ⟨_, rfl⟩
  have hk₀0 : 0 ≤ k₀ := by rw [hk₀]; positivity
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = k₀ * cTwo52 * (6 * exp 1 * cTwo52) ^ n := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = k₀ * (2 * cTwo52) ^ (n + 1) := ⟨_, rfl⟩
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = ((((n + 1 : ℕ) : ℝ) + 1) * (2 * cTwo52) ^ (n + 1)
      * (2 + 2 * cTwo52) + 3 * ((n + 1 : ℕ) : ℝ) * (2 * cTwo52) ^ (n + 1) * exp cZero)
      * (4 * exp 1) ^ n := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  refine ⟨C₁ + C₂ + C₃, by linarith, _, (good_of_stochDom hX hτ₁).inter
    (good_of_stochDom (hdec (n + 1) (by omega) τ₁ hτ₁ D hD) hτ₁), ?_⟩
  filter_upwards [flow_crude hE (fun N => (hs0 N).le) hst ht1 hc] with N ⟨hLN, hWN, hN1, hu⟩
  intro ω ⟨hω1, hω2⟩ σ u hsu hut
  simp only [Set.mem_ofPred_eq] at hω1 hω2
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have huu : ∃ uu : TimeIcc s t N, (uu : ℝ) = u := ⟨⟨u, hsu, hut⟩, rfl⟩
  obtain ⟨uu, rfl⟩ := huu
  obtain ⟨hA1, hAN, huN⟩ := hu uu
  have hu0 : 0 ≤ (uu : ℝ) := ((hs0 N).trans_le hsu).le
  have hu1 : (uu : ℝ) < 1 := hut.trans_lt (ht1 N)
  have h1u : 0 < 1 - (uu : ℝ) := by linarith
  have hL3 := B.three_le_L N
  have hℓ := half_le_ellHat_real (B.L N) hL3 hu0 hu1
  have hℓ0 : 0 < ellHat (B.L N) ((uu : ℝ) : ℂ) := by linarith
  have hℓL := ellHat_real_le_L (L := B.L N) hu1
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (N : ℝ) ^ τ₁ := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := hK ▸ Real.one_le_rpow hN1' hτ₁.le
  have hKN : K ≤ N := hK ▸ rpow_le_self_of_le_one hN1' hτ₁1
  have hA0 : 0 < B.scale E N uu := by linarith
  have hΦN := hΦ N
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (N : ℝ) ^ (-D) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ Real.rpow_nonneg hN0.le _
  have hx1 : x ≤ 1 := hx ▸ Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  obtain ⟨e', he'⟩ : ∃ e' : ℝ, e' = exp (-(cZero / 4 * K)) := ⟨_, rfl⟩
  have he'0 : 0 ≤ e' := he' ▸ (exp_pos _).le
  have hη := etaT_pos hE hu1
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  rw [← hK, ← hx, ← he']
  have hω1' : X.xiLK E N uu ω (n + 1) ≤ K * Φ N := by rw [hK]; exact hω1 uu
  have hω2' : ∀ (ρ : Fin (n + 1) → Bool) b, X.lkErr E N uu ω (LoopData.idx (ρ, b))
      * farInd (B.L N) (B.ell N uu * K) b ≤ K * x := by
    intro ρ b; rw [hK, hx]; exact hω2 (uu, (ρ, b))
  -- the target error term is nonnegative
  have herr0 : 0 ≤ (C₁ + C₂ + C₃) * (N : ℝ) ^ (2 * n + 4) * (x + e' * (1 + Φ N)) := by
    have : 0 ≤ C₁ + C₂ + C₃ := by linarith
    positivity
  by_cases hq : QGood σ
  swap
  · have h0 : (if dot then dotTerm X E N uu ω σ else commTerm X E N uu ω σ) = 0 := by
      cases dot <;> simp [dotTerm, commTerm, hq]
    rw [h0]
    refine ⟨fun y => by simp [Psum], fun a _ => by simpa using herr0, fun b => ?_⟩
    simp only [Pi.zero_apply, norm_zero]
    have : 0 ≤ C₁ + C₂ + C₃ := by linarith
    positivity
  -- the Ward bound on the slot sums
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = (2 * (B.W N : ℝ) * etaT E uu)⁻¹
      * (2 * ((2 * exp 1 * (B.ell N uu * K + 1)) ^ n * (K * Φ N * (B.scale E N uu)⁻¹ ^ (n + 1))
        + (B.L N : ℝ) ^ n * (K * x))) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hPb : ∀ y, ‖Psum (B.L N) (lkT X E N uu ω σ) y‖ ≤ P := fun y => by
    rw [hPdef]
    exact norm_Psum_lkT_le X hE hW hu0 hu1 hA0 hq (by positivity) hΦN (by positivity) hω1' hω2' y
  have hPc : P ≤ (4 * exp 1) ^ n * (N : ℝ) ^ (2 * n + 2) * (1 + Φ N) := by
    rw [hPdef]
    exact P_crude (n := n) (A := B.scale E N uu) (W := B.W N) (η := etaT E uu)
      (ℓ := B.ell N uu) (Lr := B.L N) (Nr := N) (K := K) (Φ := Φ N) (x := x) rfl hW0 hη hℓ hℓL hLN
      hK1 hKN hA1 hΦN hx0 hx1
  have hξ : ∀ i, ‖xiOf (mSigma E) σ i‖ ≤ 1 := fun i => (norm_xiOf_mSigma hE.le σ i).le
  -- the max bound, both cases
  have hmax : ∀ k : ℝ, 0 ≤ k → k ≤ k₀ → ∀ z : ℝ,
      z ≤ k * (1 - (uu : ℝ))⁻¹ * (cTwo52 / B.ell N uu) ^ (n + 1) * P →
      z ≤ (B.scale E N uu)⁻¹ ^ (n + 2) * (((C₁ + C₂ + C₃) * (N : ℝ) ^ (((n + 1 : ℕ) : ℝ) * τ₁)
          * Φ N) * (1 - (uu : ℝ))⁻¹)
        + (C₁ + C₂ + C₃) * (N : ℝ) ^ (2 * n + 4) * (x + e' * (1 + Φ N)) := by
    intro k hk hkk z hz
    have key := comm_scalar_max (n := n) (k := k) (A := B.scale E N uu) (W := B.W N)
      (η := etaT E uu) (ℓ := B.ell N uu) (u := uu) (Lr := B.L N) (Nr := N) (K := K) (Φ := Φ N)
      (x := x) (c := cTwo52) rfl hW0 hη hℓ hℓL hK1 hKN hA1 hΦN hx0 hc0 hk h1u huN hLN
    rw [← hPdef] at key
    refine hz.trans (key.trans (add_le_add ?_ ?_))
    · have h1 : k * cTwo52 * (6 * exp 1 * cTwo52) ^ n ≤ C₁ + C₂ + C₃ := by
        have : k * cTwo52 * (6 * exp 1 * cTwo52) ^ n ≤ k₀ * cTwo52 * (6 * exp 1 * cTwo52) ^ n := by
          gcongr
        rw [← hC₁] at this; linarith
      rw [show ((n + 1 : ℕ) : ℝ) * τ₁ = τ₁ * ((n + 1 : ℕ) : ℝ) by ring, ← rpow_pow_eq, ← hK]
      have : 0 ≤ K ^ (n + 1) * Φ N * (1 - (uu : ℝ))⁻¹ := by positivity
      have hAi : 0 ≤ (B.scale E N uu)⁻¹ ^ (n + 2) := by positivity
      calc (B.scale E N uu)⁻¹ ^ (n + 2) * (k * cTwo52 * (6 * exp 1 * cTwo52) ^ n * K ^ (n + 1) * Φ N
            * (1 - (uu : ℝ))⁻¹)
          = (B.scale E N uu)⁻¹ ^ (n + 2) * ((k * cTwo52 * (6 * exp 1 * cTwo52) ^ n)
              * (K ^ (n + 1) * Φ N * (1 - (uu : ℝ))⁻¹)) := by ring
        _ ≤ (B.scale E N uu)⁻¹ ^ (n + 2) * ((C₁ + C₂ + C₃) * (K ^ (n + 1) * Φ N * (1 - (uu : ℝ))⁻¹)) := by
            gcongr
        _ = _ := by ring
    · have h2 : k * (2 * cTwo52) ^ (n + 1) ≤ C₁ + C₂ + C₃ := by
        have : k * (2 * cTwo52) ^ (n + 1) ≤ k₀ * (2 * cTwo52) ^ (n + 1) := by gcongr
        rw [← hC₂] at this; linarith
      have hN3 : (N : ℝ) ^ (n + 3) ≤ (N : ℝ) ^ (2 * n + 4) := pow_le_pow_right₀ hN1' (by omega)
      have : 0 ≤ e' * (1 + Φ N) := by positivity
      calc k * (2 * cTwo52) ^ (n + 1) * (N : ℝ) ^ (n + 3) * x
          ≤ (C₁ + C₂ + C₃) * (N : ℝ) ^ (2 * n + 4) * x := by gcongr
        _ ≤ (C₁ + C₂ + C₃) * (N : ℝ) ^ (2 * n + 4) * (x + e' * (1 + Φ N)) := by gcongr; linarith
  -- the decay bound
  have hdecay : ∀ δ : ℝ, δ ≤ C₃ * (4 * exp 1)⁻¹ ^ n * (N : ℝ) ^ 2 * P * e' →
      δ ≤ (C₁ + C₂ + C₃) * (N : ℝ) ^ (2 * n + 4) * (x + e' * (1 + Φ N)) := by
    intro δ hδ
    refine hδ.trans ?_
    have h4 : 0 < (4 * exp 1) ^ n := by positivity
    have hC34 : C₃ * (4 * exp 1)⁻¹ ^ n * (4 * exp 1) ^ n = C₃ := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (by positivity), one_pow, mul_one]
    have h1 : C₃ * (4 * exp 1)⁻¹ ^ n * (N : ℝ) ^ 2 * P * e'
        ≤ C₃ * (4 * exp 1)⁻¹ ^ n * (N : ℝ) ^ 2 * ((4 * exp 1) ^ n * (N : ℝ) ^ (2 * n + 2)
          * (1 + Φ N)) * e' := by gcongr
    have e2 : C₃ * (4 * exp 1)⁻¹ ^ n * (N : ℝ) ^ 2 * ((4 * exp 1) ^ n * (N : ℝ) ^ (2 * n + 2)
          * (1 + Φ N)) * e' = C₃ * (N : ℝ) ^ (2 * n + 4) * (e' * (1 + Φ N)) := by
      calc C₃ * (4 * exp 1)⁻¹ ^ n * (N : ℝ) ^ 2 * ((4 * exp 1) ^ n * (N : ℝ) ^ (2 * n + 2)
            * (1 + Φ N)) * e'
          = (C₃ * (4 * exp 1)⁻¹ ^ n * (4 * exp 1) ^ n) * ((N : ℝ) ^ 2 * (N : ℝ) ^ (2 * n + 2))
            * (e' * (1 + Φ N)) := by ring
        _ = C₃ * (N : ℝ) ^ (2 * n + 4) * (e' * (1 + Φ N)) := by
            rw [hC34, ← pow_add, show 2 + (2 * n + 2) = 2 * n + 4 by omega]
    rw [e2] at h1
    refine h1.trans ?_
    have hNq : 0 ≤ (N : ℝ) ^ (2 * n + 4) := by positivity
    have hE1 : 0 ≤ e' * (1 + Φ N) := by positivity
    have hCs : 0 ≤ C₁ + C₂ + C₃ := by linarith
    have h3 : C₃ * ((N : ℝ) ^ (2 * n + 4) * (e' * (1 + Φ N)))
        ≤ (C₁ + C₂ + C₃) * ((N : ℝ) ^ (2 * n + 4) * (e' * (1 + Φ N))) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hNq hE1)
    have h5 : 0 ≤ (C₁ + C₂ + C₃) * (N : ℝ) ^ (2 * n + 4) * x := by positivity
    calc C₃ * (N : ℝ) ^ (2 * n + 4) * (e' * (1 + Φ N))
        = C₃ * ((N : ℝ) ^ (2 * n + 4) * (e' * (1 + Φ N))) := by ring
      _ ≤ (C₁ + C₂ + C₃) * ((N : ℝ) ^ (2 * n + 4) * (e' * (1 + Φ N))) := h3
      _ ≤ (C₁ + C₂ + C₃) * ((N : ℝ) ^ (2 * n + 4) * (e' * (1 + Φ N)))
          + (C₁ + C₂ + C₃) * (N : ℝ) ^ (2 * n + 4) * x := le_add_of_nonneg_right h5
      _ = (C₁ + C₂ + C₃) * (N : ℝ) ^ (2 * n + 4) * (x + e' * (1 + Φ N)) := by ring
  have hR : 0 < B.ell N uu * K := by
    have : 0 < B.ell N uu := hℓ0
    positivity
  have hℓ0' : 0 < B.ell N uu := hℓ0
  have hC3e : C₃ * (4 * exp 1)⁻¹ ^ n = (((n + 1 : ℕ) : ℝ) + 1) * (2 * cTwo52) ^ (n + 1)
      * (2 + 2 * cTwo52) + 3 * ((n + 1 : ℕ) : ℝ) * (2 * cTwo52) ^ (n + 1) * exp cZero := by
    have h4 : (4 * exp 1) ^ n * (4 * exp 1)⁻¹ ^ n = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
    calc C₃ * (4 * exp 1)⁻¹ ^ n = ((((n + 1 : ℕ) : ℝ) + 1) * (2 * cTwo52) ^ (n + 1)
          * (2 + 2 * cTwo52) + 3 * ((n + 1 : ℕ) : ℝ) * (2 * cTwo52) ^ (n + 1) * exp cZero)
          * ((4 * exp 1) ^ n * (4 * exp 1)⁻¹ ^ n) := by rw [hC₃]; ring
      _ = _ := by rw [h4, mul_one]
  have hc3 : (((n + 1 : ℕ) : ℝ) + 1) * (2 * cTwo52) ^ (n + 1) * (2 + 2 * cTwo52)
      ≤ C₃ * (4 * exp 1)⁻¹ ^ n := by
    rw [hC3e]
    have : 0 ≤ 3 * ((n + 1 : ℕ) : ℝ) * (2 * cTwo52) ^ (n + 1) * exp cZero := by positivity
    linarith
  have hc4 : 3 * ((n + 1 : ℕ) : ℝ) * (2 * cTwo52) ^ (n + 1) * exp cZero
      ≤ C₃ * (4 * exp 1)⁻¹ ^ n := by
    rw [hC3e]
    have : 0 ≤ (((n + 1 : ℕ) : ℝ) + 1) * (2 * cTwo52) ^ (n + 1) * (2 + 2 * cTwo52) := by positivity
    linarith
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    simpa using pow_le_pow_right₀ hN1' (show 1 ≤ 2 by norm_num)
  cases dot
  · -- the commutator term
    have hG : (if false = true then dotTerm X E N uu ω σ else commTerm X E N uu ω σ)
        = commS (B.L N) (xiOf (mSigma E) σ) ((uu : ℝ) : ℂ) (lkT X E N uu ω σ) := by
      simp [commTerm, hq]
    rw [hG]
    refine ⟨SumZero_commS (B.L N) hL3 (fun i => norm_ofReal_mul_lt_one hu0 hu1 (hξ i))
      (norm_ofReal_lt_one hu0 hu1) _, ?_, fun b => ?_⟩
    · have h := fastDecay_commS (B.L N) hL3 hu0 hu1 (n := n + 1) hξ (A := lkT X E N uu ω σ) hR hP0 hPb
      refine FastDecay.mono (B.L N) h (radius_le hℓ hK1) (hdecay _ ?_)
      · have hK0 : 0 ≤ K := by linarith
        have he1 : exp (-(cZero * (B.ell N uu * K / 2) / B.ell N uu)) ≤ e' :=
          he' ▸ exp_arg1 hz0 hℓ0' hK0
        have he2 : exp (-(cZero * (B.ell N uu * K) / B.ell N uu)) ≤ e' :=
          he' ▸ exp_arg2 hz0 hℓ0' hK0
        have he3 : exp (-(cZero * ((2 * (B.ell N uu * K) + 1) / 2) / B.ell N uu)) ≤ e' :=
          he' ▸ exp_arg3 hz0 hℓ0' hK0
        have key := comm_scalar_dec (m := n + 1) (k := ((n + 1 : ℕ) : ℝ)) (u := uu)
          (ℓ := B.ell N uu) (c := cTwo52) (Lr := B.L N) (Nr := N) (P := P) hℓ h1u huN hc0
          (Nat.cast_nonneg _) hLN hP0 (Nat.cast_nonneg _) (exp_pos _).le he1 (exp_pos _).le he2
          (exp_pos _).le he3 hN1'
        refine key.trans ?_
        have : 0 ≤ (N : ℝ) ^ 2 * P * e' := by positivity
        calc (((n + 1 : ℕ) : ℝ) + 1) * (2 * cTwo52) ^ (n + 1) * (2 + 2 * cTwo52) * (N : ℝ) ^ 2 * P * e'
            = ((((n + 1 : ℕ) : ℝ) + 1) * (2 * cTwo52) ^ (n + 1) * (2 + 2 * cTwo52)) * ((N : ℝ) ^ 2 * P * e') := by
              ring
          _ ≤ (C₃ * (4 * exp 1)⁻¹ ^ n) * ((N : ℝ) ^ 2 * P * e') := by gcongr
          _ = C₃ * (4 * exp 1)⁻¹ ^ n * (N : ℝ) ^ 2 * P * e' := by ring
    · refine hmax k₀ hk₀0 le_rfl _ ((norm_commS_le (B.L N) hL3 hu0 hu1 (n := n + 1) hξ hP0 hPb b).trans
        (le_of_eq ?_))
      rw [hk₀]; rfl
  · -- the `ϑ̇` term
    have hG : (if true = true then dotTerm X E N uu ω σ else commTerm X E N uu ω σ)
        = fun b => Psum (B.L N) (lkT X E N uu ω σ) (b 0) * varthetaDot (B.L N) uu b := by
      simp [dotTerm, hq]
    rw [hG]
    refine ⟨fun y => by rw [Psum_mul_left, Psum_varthetaDot (B.L N) hL3 hu0 hu1, mul_zero], ?_,
      fun b => ?_⟩
    · have hR2 : 2 ≤ B.ell N uu * (4 * K) := two_le_radius hℓ hK1
      have h := fastDecay_Psum_mul (B.L N)
        (fastDecay_varthetaDot (B.L N) hL3 hu0 hu1 (n := n + 1) hR2) hP0 hPb
      refine FastDecay.mono (B.L N) h le_rfl (hdecay _ ?_)
      have he4 : exp (-(cZero * (B.ell N uu * (4 * K) / 4 - 1 / 2) / B.ell N uu)) ≤ exp cZero * e' :=
        he' ▸ exp_arg4 hz0 hℓ (by linarith)
      have h2c := div_pow_le_two_mul (n := n + 1) hℓ hc0
      have hn0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      calc P * (3 * ((n + 1 : ℕ) : ℝ) * (cTwo52 / B.ell N uu) ^ (n + 1) * (1 - (uu : ℝ))⁻¹
            * exp (-(cZero * (B.ell N uu * (4 * K) / 4 - 1 / 2) / B.ell N uu)))
          ≤ P * (3 * ((n + 1 : ℕ) : ℝ) * (2 * cTwo52) ^ (n + 1) * (N : ℝ) * (exp cZero * e')) := by
            gcongr
            exact div_le_two_mul hℓ hc0
        _ = (3 * ((n + 1 : ℕ) : ℝ) * (2 * cTwo52) ^ (n + 1) * exp cZero) * ((N : ℝ) * P * e') := by ring
        _ ≤ (C₃ * (4 * exp 1)⁻¹ ^ n) * ((N : ℝ) ^ 2 * P * e') := by
            have : 0 ≤ P * e' := by positivity
            gcongr
        _ = C₃ * (4 * exp 1)⁻¹ ^ n * (N : ℝ) ^ 2 * P * e' := by ring
    · have hk : 2 * ((n + 1 : ℕ) : ℝ) ≤ k₀ := by rw [hk₀]; linarith
      refine hmax (2 * ((n + 1 : ℕ) : ℝ)) (by positivity) hk _ ?_
      rw [norm_mul]
      calc ‖Psum (B.L N) (lkT X E N uu ω σ) (b 0)‖ * ‖varthetaDot (B.L N) uu b‖
          ≤ P * (2 * ((n + 1 : ℕ) : ℝ) * (cTwo52 / ellHat (B.L N) ((uu : ℝ) : ℂ)) ^ (n + 1)
              * (1 - (uu : ℝ))⁻¹) :=
            mul_le_mul (hPb _) (norm_varthetaDot_le (B.L N) hL3 hu0 hu1 b) (norm_nonneg _) hP0
        _ = 2 * ((n + 1 : ℕ) : ℝ) * (1 - (uu : ℝ))⁻¹ * (cTwo52 / B.ell N uu) ^ (n + 1) * P := by
            simp only [Band.ell]; ring

/-- **(5.100)**: the commutator term of (5.94), `(Wℓ_vη_v)^m |∫_s^v U ∘ [Q_u, Θ_{u,σ}] ∘ (L-K)_u| ≺ 1 + Φ`
(for `QGood` charges; `commTerm` vanishes otherwise). -/
theorem termI3 (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ} (hW : WardP X E n)
    (hdec : LKDecay X E s t) {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hX : StochDom B.P (Step3.flowXiLK X E s t (n + 1)) (fun N _ _ => Φ N)) :
    StochDom B.P (fun N (pp : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      B.scale E N pp.1 ^ (n + 2) * ‖∫ u in (s N)..(pp.1 : ℝ),
        Uker (B.L N) (xiOf (mSigma E) pp.2.1) (u : ℂ) ((pp.1 : ℝ) : ℂ)
          (commTerm X E N u ω pp.2.1) pp.2.2‖)
      (fun N _ _ => 1 + Φ N) :=
  integral_term_stochDom hE hs0 hst ht1 hc hΦ (fun N u ω σ => commTerm X E N u ω σ)
    (by norm_num : (1 : ℝ) ≤ 4) (by have := cZero_pos; positivity) (n + 1) (2 * n + 4)
    (hgood_commDot X hE hs0 hst ht1 hc hW hdec hΦ hX false)

/-- **(5.97)**: the `ϑ̇` term of (5.94), `(Wℓ_vη_v)^m |∫_s^v U ∘ ((P ∘ (L-K)_u) ϑ̇_u)| ≺ 1 + Φ`
(for `QGood` charges). -/
theorem termI4 (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ} (hW : WardP X E n)
    (hdec : LKDecay X E s t) {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hX : StochDom B.P (Step3.flowXiLK X E s t (n + 1)) (fun N _ _ => Φ N)) :
    StochDom B.P (fun N (pp : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      B.scale E N pp.1 ^ (n + 2) * ‖∫ u in (s N)..(pp.1 : ℝ),
        Uker (B.L N) (xiOf (mSigma E) pp.2.1) (u : ℂ) ((pp.1 : ℝ) : ℂ)
          (dotTerm X E N u ω pp.2.1) pp.2.2‖)
      (fun N _ _ => 1 + Φ N) :=
  integral_term_stochDom hE hs0 hst ht1 hc hΦ (fun N u ω σ => dotTerm X E N u ω σ)
    (by norm_num : (1 : ℝ) ≤ 4) (by have := cZero_pos; positivity) (n + 1) (2 * n + 4)
    (hgood_commDot X hE hs0 hst ht1 hc hW hdec hΦ hX true)

set_option maxHeartbeats 1000000 in
/-- **The initial term of (5.94)**: `(Wℓ_vη_v)^m |U_{s,v,σ} ∘ Q_s ∘ (L-K)_s| ≺ 1`, from the
assumption (2.68) of Theorem 2.21 at time `s` and (5.93). -/
theorem termI1 (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ} (hdec : LKDecay X E s t)
    {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hLmK : StochDom B.P (fun N (w : LoopData (B.L N) (n + 2)) ω => X.lkErr E N (s N) ω w.idx)
      (fun N _ _ => (B.scale E N (s N))⁻¹ ^ (n + 2))) :
    StochDom B.P (fun N (pp : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      B.scale E N pp.1 ^ (n + 2) * ‖Uker (B.L N) (xiOf (mSigma E) pp.2.1) ((s N : ℝ) : ℂ)
        ((pp.1 : ℝ) : ℂ) (Qop (B.L N) ((s N : ℝ) : ℂ) (lkT X E N (s N) ω pp.2.1)) pp.2.2‖)
      (fun N _ _ => 1 + Φ N) := by
  refine stochDom_of_logBound hΦ (c₁ := cZero / 4) (by have := cZero_pos; positivity)
    (3 * n + 6) (5 * n + 11) fun τ₁ hτ₁ hτ₁1 D hD => ?_
  have hc0 : 0 ≤ cTwo52 := cTwo52_pos.le
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = 2 * (1 + (6 * exp 1 * cTwo52) ^ (n + 1) + (2 * cTwo52) ^ (n + 1)) :=
    ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = cKerSumZero (n + 2) * (1 + (6 * exp 1 * cTwo52) ^ (n + 1)) :=
    ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm]; have := cKerSumZero_nonneg (n + 2); positivity
  obtain ⟨Ce, hCe⟩ : ∃ Ce : ℝ, Ce = (cKerSumZero (n + 2) * 1 ^ (2 * (n + 2)) + cKerSumZeroErr (n + 2)) * C₀ :=
    ⟨_, rfl⟩
  have hCe0 : 0 ≤ Ce := by
    rw [hCe]; have := cKerSumZero_nonneg (n + 2); have := cKerSumZeroErr_nonneg (n + 2); positivity
  refine ⟨Cm + Ce, by linarith, _, (good_of_stochDom hLmK hτ₁).inter
    (good_of_stochDom (hdec (n + 2) (by omega) τ₁ hτ₁ D hD) hτ₁), ?_⟩
  filter_upwards [flow_crude hE (fun N => (hs0 N).le) hst ht1 hc] with N ⟨hLN, hWN, hN1, hu⟩
  intro ω ⟨hω1, hω2⟩ pp
  simp only [Set.mem_ofPred_eq] at hω1 hω2
  obtain ⟨⟨v, hsv, hvt⟩, σ, a⟩ := pp
  simp only
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hΦN := hΦ N
  have hL3 := B.three_le_L N
  set ss : TimeIcc s t N := ⟨s N, le_rfl, hst N⟩
  obtain ⟨hAs1, hAsN, hsN⟩ := hu ss
  obtain ⟨hAv1, hAvN, hvN⟩ := hu ⟨v, hsv, hvt⟩
  simp only at hAv1 hAvN hvN
  have hs0' : 0 ≤ s N := (hs0 N).le
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hv0 : 0 < v := (hs0 N).trans_le hsv
  have hv1 : v < 1 := hvt.trans_lt (ht1 N)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (N : ℝ) ^ τ₁ := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := hK ▸ Real.one_le_rpow hN1' hτ₁.le
  have hKN : K ≤ N := hK ▸ rpow_le_self_of_le_one hN1' hτ₁1
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (N : ℝ) ^ (-D) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ Real.rpow_nonneg hN0.le _
  have hx1 : x ≤ 1 := hx ▸ Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  obtain ⟨e', he'⟩ : ∃ e' : ℝ, e' = exp (-(cZero / 4 * K)) := ⟨_, rfl⟩
  have he'0 : 0 ≤ e' := he' ▸ (exp_pos _).le
  rw [← hK, ← hx, ← he']
  have hAs0 : 0 < B.scale E N (s N) := by linarith
  -- the tensor at time `s`
  set M := K * ((B.scale E N (s N))⁻¹ ^ (n + 2) * ((1 - 0) * 1)⁻¹ * (1 * 1)) with hM
  have hM0 : 0 ≤ M := by positivity
  have hTs : ∀ b, ‖lkT X E N (s N) ω σ b‖ ≤ M := fun b => by
    have := hω1 (σ, b)
    rw [← hK] at this
    rw [hM]; simp only [sub_zero, mul_one, inv_one]
    rw [norm_lkT]; exact this
  have hTd : FastDecay (B.L N) (ellHat (B.L N) ((s N : ℝ) : ℂ) * K) (K * x) (lkT X E N (s N) ω σ) :=
    fastDecay_of_farInd fun b => by rw [hK, hx]; exact hω2 (ss, (σ, b))
  have hQmax := norm_Qop_le_of_fastDecay (B.L N) (n := n + 1) hL3 hs0' hs1 hK1 hM0
    (by positivity) hTs hTd
  have hQdec := fastDecay_Qop_le (B.L N) (n := n + 1) hL3 hs0' hs1 hK1 hM0 (by positivity) hTs hTd
  have hmax := QF_scalar_max (n := n) (K := K) (A := B.scale E N (s N)) (u := 0) (im := 1)
    (Cf := 1) (Φ := 1) (c := cTwo52) (Lr := B.L N) (Nr := N) (x := x) hK1 hKN hAs0 (by norm_num)
    one_pos zero_le_one zero_le_one hc0 (Nat.cast_nonneg _) hLN hx0
  have hdc := QF_scalar_dec (n := n) (K := K) (A := B.scale E N (s N)) (u := 0) (im := 1)
    (Cf := 1) (Φ := 1) (c := cTwo52) (Lr := B.L N) (Nr := N) (x := x)
    (e := exp (-(cZero * K / 2))) (e' := e') hK1 hKN hAs1 (by norm_num) (by simpa using hN1')
    one_pos zero_le_one zero_le_one hc0 (Nat.cast_nonneg _) hLN hx0 hx1 (exp_pos _).le
    (he' ▸ exp_neg_le_exp_neg (by have := cZero_pos; nlinarith)) hN1'
  rw [← hM] at hmax hdc
  simp only [sub_zero, mul_one, inv_one, div_one] at hmax hdc
  -- ε : a common bound on the max-norm and decay errors
  set ε := C₀ * (N : ℝ) ^ (n + 3) * (x + e' * (1 + Φ N)) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hζ : (2 * cTwo52) ^ (n + 1) * (N : ℝ) ^ (n + 2) * x ≤ ε := by
    have h1 : (N : ℝ) ^ (n + 2) ≤ (N : ℝ) ^ (n + 3) := pow_le_pow_right₀ hN1' (by omega)
    have h2 : (2 * cTwo52) ^ (n + 1) ≤ C₀ := by
      rw [hC₀]; have : 0 ≤ (6 * exp 1 * cTwo52) ^ (n + 1) := by positivity
      have : (0 : ℝ) ≤ (2 * cTwo52) ^ (n + 1) := by positivity
      linarith
    have h3 : x ≤ x + e' * (1 + Φ N) := le_add_of_nonneg_right (by positivity)
    have h4 : 0 ≤ (N : ℝ) ^ (n + 2) := by positivity
    have h5 : (2 * cTwo52) ^ (n + 1) * (N : ℝ) ^ (n + 2) ≤ C₀ * (N : ℝ) ^ (n + 3) :=
      mul_le_mul h2 h1 h4 hC₀0
    exact mul_le_mul h5 h3 hx0 (by positivity)
  have hδ : FastDecay (B.L N) (ellHat (B.L N) ((s N : ℝ) : ℂ) * K) ε
      (Qop (B.L N) ((s N : ℝ) : ℂ) (lkT X E N (s N) ω σ)) := by
    refine FastDecay.mono (B.L N) hQdec le_rfl (hdc.trans ?_)
    rw [hε, hC₀]
    have : x + e' * (1 + 1) ≤ 2 * (x + e' * (1 + Φ N)) := by
      have := mul_nonneg he'0 hΦN
      nlinarith
    have hq : 0 ≤ (1 + (6 * exp 1 * cTwo52) ^ (n + 1) + (2 * cTwo52) ^ (n + 1)) * (N : ℝ) ^ (n + 3) := by
      positivity
    calc (1 + (6 * exp 1 * cTwo52) ^ (n + 1) + (2 * cTwo52) ^ (n + 1)) * (N : ℝ) ^ (n + 3) * (x + e' * (1 + 1))
        ≤ (1 + (6 * exp 1 * cTwo52) ^ (n + 1) + (2 * cTwo52) ^ (n + 1)) * (N : ℝ) ^ (n + 3)
            * (2 * (x + e' * (1 + Φ N))) := mul_le_mul_of_nonneg_left this hq
      _ = _ := by ring
  -- the kernel
  set κA := (B.W N : ℝ) * (mE E).im with hκA
  have hκA0 : 0 < κA := mul_pos (by exact_mod_cast B.W_pos N) (mE_im_pos hE)
  set ψ := (1 + (6 * exp 1 * cTwo52) ^ (n + 1)) * K ^ (n + 2) with hψ
  have hψ0 : 0 ≤ ψ := by positivity
  have hGM : ∀ b, ‖Qop (B.L N) ((s N : ℝ) : ℂ) (lkT X E N (s N) ω σ) b‖
      ≤ (κA * ((1 - s N) * ellHat (B.L N) ((s N : ℝ) : ℂ)))⁻¹ ^ (n + 2) * ψ + ε := by
    intro b
    refine (hQmax b).trans (hmax.trans ?_)
    rw [← Band.scale_eq B E N (s N)]
    exact add_le_add le_rfl hζ
  have key := norm_Uker_sumZero_scale_le (B.L N) hL3 hE.le σ hs0' le_rfl hsv hv0.le hv1 hκA0 hK1
    hψ0 hε0 hε0 hGM hδ (SumZero_Qop (B.L N) hL3 (norm_ofReal_lt_one hs0' hs1) _) a
  rw [← Band.scale_eq B E N v] at key
  have hAv0 : 0 < B.scale E N v := by linarith
  have hAvn : B.scale E N v ^ (n + 2) * (B.scale E N v)⁻¹ ^ (n + 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hAv0.ne', one_pow]
  have h1v : 0 < 1 - v := by linarith
  have hρN : (1 - s N) / (1 - v) ≤ N := by
    calc (1 - s N) / (1 - v) ≤ 1 / (1 - v) := div_le_div_of_nonneg_right (by linarith) h1v.le
      _ = (1 - v)⁻¹ := one_div _
      _ ≤ N := hvN
  have hρ0 : 0 ≤ (1 - s N) / (1 - v) := div_nonneg (by linarith) h1v.le
  have herr := err_scalar (m := n + 2) hAv0.le hAvN hρ0 hρN (Nat.cast_nonneg _) hLN
    (by linarith) (show K ≤ 1 * N by linarith) hN1' le_rfl hε0 (cKerSumZero_nonneg (n + 2))
    (cKerSumZeroErr_nonneg (n + 2)) zero_le_one le_rfl
  have hmain : cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ψ
      ≤ Cm * (N : ℝ) ^ (((3 * n + 6 : ℕ) : ℝ) * τ₁) * (1 + Real.log N) * (1 + Φ N) := by
    have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1'
    have e : cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ψ = Cm * K ^ (3 * n + 6) := by
      rw [hψ, hCm, show 3 * n + 6 = 2 * (n + 2) + (n + 2) by ring, pow_add]; ring
    rw [e, show ((3 * n + 6 : ℕ) : ℝ) * τ₁ = τ₁ * ((3 * n + 6 : ℕ) : ℝ) by ring, ← rpow_pow_eq, ← hK]
    have : 1 ≤ (1 + Real.log N) * (1 + Φ N) := by nlinarith
    have hK0 : 0 ≤ Cm * K ^ (3 * n + 6) := by positivity
    calc Cm * K ^ (3 * n + 6) = Cm * K ^ (3 * n + 6) * 1 := (mul_one _).symm
      _ ≤ Cm * K ^ (3 * n + 6) * ((1 + Real.log N) * (1 + Φ N)) := mul_le_mul_of_nonneg_left this hK0
      _ = _ := by ring
  have hfin : B.scale E N v ^ (n + 2) * ((cKerSumZero (n + 2) * K ^ (2 * (n + 2))
        * ((1 - s N) / (1 - v)) ^ (n + 2) * ε + cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2)
        * ((1 - s N) / (1 - v)) ^ (n + 2) * ε) * 1)
      ≤ Ce * (N : ℝ) ^ (5 * n + 11) * (x + e' * (1 + Φ N)) := by
    refine herr.trans (le_of_eq ?_)
    rw [hε, hCe, show 5 * n + 11 = 4 * (n + 2) + (n + 3) by ring, pow_add]; ring
  calc B.scale E N v ^ (n + 2) * ‖Uker (B.L N) (xiOf (mSigma E) σ) ((s N : ℝ) : ℂ) (v : ℂ)
        (Qop (B.L N) ((s N : ℝ) : ℂ) (lkT X E N (s N) ω σ)) a‖
      ≤ B.scale E N v ^ (n + 2) * (cKerSumZero (n + 2) * K ^ (2 * (n + 2))
          * (B.scale E N v)⁻¹ ^ (n + 2) * ψ + (cKerSumZero (n + 2) * K ^ (2 * (n + 2))
          * ((1 - s N) / (1 - v)) ^ (n + 2) * ε + cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2)
          * ((1 - s N) / (1 - v)) ^ (n + 2) * ε)) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = (B.scale E N v ^ (n + 2) * (B.scale E N v)⁻¹ ^ (n + 2)) * (cKerSumZero (n + 2)
          * K ^ (2 * (n + 2)) * ψ) + B.scale E N v ^ (n + 2) * ((cKerSumZero (n + 2)
          * K ^ (2 * (n + 2)) * ((1 - s N) / (1 - v)) ^ (n + 2) * ε + cKerSumZeroErr (n + 2)
          * (B.L N : ℝ) ^ (n + 2) * ((1 - s N) / (1 - v)) ^ (n + 2) * ε) * 1) := by ring
    _ ≤ Cm * (N : ℝ) ^ (((3 * n + 6 : ℕ) : ℝ) * τ₁) * (1 + Real.log N) * (1 + Φ N)
        + Ce * (N : ℝ) ^ (5 * n + 11) * (x + e' * (1 + Φ N)) := by
        rw [hAvn, one_mul]; exact add_le_add hmain hfin
    _ ≤ (Cm + Ce) * (N : ℝ) ^ (((3 * n + 6 : ℕ) : ℝ) * τ₁) * (1 + Real.log N) * (1 + Φ N)
        + (Cm + Ce) * (N : ℝ) ^ (5 * n + 11) * (x + e' * (1 + Φ N)) := by
        have hlog := Real.log_nonneg hN1'
        gcongr ?_ * _ * _ * _ + ?_ * _ * _
        · linarith
        · linarith

theorem xi2_ne_zero (hE : |E| < 2) {n : ℕ} (σ : Fin (n + 2) → Bool) (i : Fin ((n + 2) + (n + 2))) :
    xi2 E σ i ≠ 0 := by
  unfold xi2
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left]; exact xiOf_mSigma_ne_zero hE.le σ i
  | right i => rw [Fin.append_right]; exact xiOf_mSigma_ne_zero hE.le σ i

theorem norm_xi2_le (hE : |E| < 2) {n : ℕ} (σ : Fin (n + 2) → Bool) (i : Fin ((n + 2) + (n + 2))) :
    ‖xi2 E σ i‖ ≤ 1 := by
  unfold xi2
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left]; exact (norm_xiOf_mSigma hE.le σ i).le
  | right i => rw [Fin.append_right]; exact (norm_xiOf_mSigma hE.le σ i).le

/-- (5.77), line 4, + the hypothesis `Ξ^{(L)}_{u,2m+2} ≺ Λ` of Lemma 5.14:
`E ⊗ E ≺ (Wℓ_uη_u)^{-2m} η_u^{-1} Λ`. -/
theorem EE_stochDom (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1) {n : ℕ}
    (H : Hierarchy X E s t n) (h510 : Lemma510 X E s t H) {Λ : ℕ → ℝ}
    (hY : StochDom B.P (Step3.flowXiL X E s t (2 * (n + 2) + 2)) (fun N _ _ => Λ N)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × ((Fin (n + 2) → Bool) × LoopArg (B.L N) ((n + 2) + (n + 2)))) ω =>
        ‖H.EE N p.1 ω p.2.1 p.2.2‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) * (etaT E p.1)⁻¹ * Λ N) := by
  have hpos : ∀ N (p : TimeIcc s t N × ((Fin (n + 2) → Bool) × LoopArg (B.L N) ((n + 2) + (n + 2)))),
      0 < B.scale E N p.1 := fun N p =>
    B.scale_pos hE N ((hs0 N).trans_le p.1.2.1) (p.1.2.2.trans_lt (ht1 N))
  have hg : ∀ N (p : TimeIcc s t N × ((Fin (n + 2) → Bool) × LoopArg (B.L N) ((n + 2) + (n + 2))))
      (_ : Ω), 0 ≤ (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) * (etaT E p.1)⁻¹ := fun N p _ => by
    have := hpos N p; have := etaT_pos hE (p.1.2.2.trans_lt (ht1 N)); positivity
  have hY0 : ∀ N (p : TimeIcc s t N × ((Fin (n + 2) → Bool) × LoopArg (B.L N) ((n + 2) + (n + 2)))) ω,
      0 ≤ X.xiL E N p.1 ω (2 * (n + 2) + 2) := fun N p ω => X.xiL_nonneg (hpos N p).le
  have hm := StochDom.mul hY0 hg (StochDom.refl hg)
    (hY.precomp_param (fun N (p : TimeIcc s t N × ((Fin (n + 2) → Bool)
      × LoopArg (B.L N) ((n + 2) + (n + 2)))) => p.1))
  exact h510.EE_le.trans hm


end TermsQ

section ScQ
/-- The two slot projections of `Q_t ⊗ Q_t`, composed: the scalar bookkeeping. -/
theorem QQ_chain_scalar {W₁ W₂ θ Lk e δ α β E₁ E₂ : ℝ} (hW₁θ : 1 + W₁ * θ ≤ α)
    (hW₂θ : 1 + W₂ * θ ≤ α) (hLθ : Lk * θ ≤ β) (hW₁ : 0 ≤ W₁) (_hW₂ : 0 ≤ W₂) (hθ : 0 ≤ θ)
    (hLk : 0 ≤ Lk) (he : 0 ≤ e) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) (hE₁ : 0 ≤ E₁)
    (hE₂ : 0 ≤ E₂) (hE21 : E₂ ≤ E₁) (hE1 : E₁ ≤ 1) :
    (e + (W₁ * e + Lk * δ) * θ) + (W₂ * (e + (W₁ * e + Lk * δ) * θ)
        + Lk * (δ + (W₁ * e + Lk * δ) * θ * E₁ + Lk * δ * θ)) * θ
      ≤ α ^ 2 * e + 4 * (1 + α + β) ^ 2 * (δ + E₁ * e) ∧
    (δ + (W₁ * e + Lk * δ) * θ * E₁ + Lk * δ * θ)
        + (W₂ * (e + (W₁ * e + Lk * δ) * θ) + Lk * (δ + (W₁ * e + Lk * δ) * θ * E₁ + Lk * δ * θ))
          * θ * E₂ + Lk * (δ + (W₁ * e + Lk * δ) * θ * E₁ + Lk * δ * θ) * θ
      ≤ 10 * (1 + α + β) ^ 2 * (δ + E₁ * e) := by
  have hα : 0 ≤ α := by have : 0 ≤ W₁ * θ := mul_nonneg hW₁ hθ; linarith
  set e₂ := e + (W₁ * e + Lk * δ) * θ with he₂
  set δ₂ := δ + (W₁ * e + Lk * δ) * θ * E₁ + Lk * δ * θ with hδ₂
  have he₂0 : 0 ≤ e₂ := by positivity
  have hδ₂0 : 0 ≤ δ₂ := by positivity
  have hWθ1 : W₁ * θ ≤ α := by linarith
  have a1 : W₁ * e * θ ≤ α * e := by
    calc W₁ * e * θ = (W₁ * θ) * e := by ring
      _ ≤ α * e := mul_le_mul_of_nonneg_right hWθ1 he
  have hLδ : Lk * δ * θ ≤ β * δ := by
    calc Lk * δ * θ = (Lk * θ) * δ := by ring
      _ ≤ β * δ := mul_le_mul_of_nonneg_right hLθ hδ
  have h1 : (W₁ * e + Lk * δ) * θ ≤ α * e + β * δ := by
    calc (W₁ * e + Lk * δ) * θ = W₁ * e * θ + Lk * δ * θ := by ring
      _ ≤ α * e + β * δ := add_le_add a1 hLδ
  have hc2 : e₂ ≤ α * e + β * δ := by
    have : e + W₁ * θ * e ≤ α * e := by
      calc e + W₁ * θ * e = (1 + W₁ * θ) * e := by ring
        _ ≤ α * e := mul_le_mul_of_nonneg_right hW₁θ he
    calc e₂ = e + W₁ * θ * e + Lk * δ * θ := by rw [he₂]; ring
      _ ≤ α * e + β * δ := add_le_add this hLδ
  have hd2 : δ₂ ≤ δ + (α * e + β * δ) * E₁ + β * δ := by
    have := mul_le_mul_of_nonneg_right h1 hE₁
    rw [hδ₂]; linarith
  have hLδ₂ : Lk * δ₂ * θ ≤ β * δ₂ := by
    calc Lk * δ₂ * θ = (Lk * θ) * δ₂ := by ring
      _ ≤ β * δ₂ := mul_le_mul_of_nonneg_right hLθ hδ₂0
  have hc3 : e₂ + (W₂ * e₂ + Lk * δ₂) * θ ≤ α * e₂ + β * δ₂ := by
    have : e₂ + W₂ * θ * e₂ ≤ α * e₂ := by
      calc e₂ + W₂ * θ * e₂ = (1 + W₂ * θ) * e₂ := by ring
        _ ≤ α * e₂ := mul_le_mul_of_nonneg_right hW₂θ he₂0
    calc e₂ + (W₂ * e₂ + Lk * δ₂) * θ = e₂ + W₂ * θ * e₂ + Lk * δ₂ * θ := by ring
      _ ≤ α * e₂ + β * δ₂ := add_le_add this hLδ₂
  have hd3 : δ₂ + (W₂ * e₂ + Lk * δ₂) * θ * E₂ + Lk * δ₂ * θ
      ≤ δ₂ + (α * e₂ + β * δ₂) * E₁ + β * δ₂ := by
    have hW2 : W₂ * θ ≤ α := by linarith
    have b1 : (W₂ * e₂ + Lk * δ₂) * θ ≤ α * e₂ + β * δ₂ := by
      have c1 : W₂ * e₂ * θ ≤ α * e₂ := by
        calc W₂ * e₂ * θ = (W₂ * θ) * e₂ := by ring
          _ ≤ α * e₂ := mul_le_mul_of_nonneg_right hW2 he₂0
      calc (W₂ * e₂ + Lk * δ₂) * θ = W₂ * e₂ * θ + Lk * δ₂ * θ := by ring
        _ ≤ α * e₂ + β * δ₂ := add_le_add c1 hLδ₂
    have b0 : 0 ≤ α * e₂ + β * δ₂ := by positivity
    have := mul_le_mul b1 hE21 hE₂ b0
    linarith
  exact QQ_rec_scalar hα hβ he hδ hE₁ hE1 hc2 hd2 hc3 hd3 hδ₂0

theorem window1_le {k : ℕ} {ℓ K c : ℝ} (hℓ : 1 / 2 ≤ ℓ) (hK : 1 ≤ K) (hc : 0 ≤ c) :
    1 + (2 * exp 1 * (ℓ * K + 1)) ^ k * (c / ℓ) ^ k ≤ 1 + (12 * exp 1 * c * K) ^ k := by
  have h1 := window_mul_le (n := k) hℓ hK hc
  have h2 : (6 * exp 1 * c * K) ^ k ≤ (12 * exp 1 * c * K) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    have : 0 ≤ exp 1 * c * K := by have := exp_pos 1; have : 0 ≤ K := by linarith
                                   positivity
    linarith
  linarith

theorem window2_le {k : ℕ} {ℓ K c : ℝ} (hℓ : 1 / 2 ≤ ℓ) (hK : 1 ≤ K) (hc : 0 ≤ c) :
    1 + (2 * exp 1 * (2 * (ℓ * K) + 1)) ^ k * (c / ℓ) ^ k ≤ 1 + (12 * exp 1 * c * K) ^ k := by
  have h1 := window_mul_le (n := k) hℓ (show 1 ≤ 2 * K by linarith) hc
  have e1 : ℓ * (2 * K) = 2 * (ℓ * K) := by ring
  have e2 : 6 * exp 1 * c * (2 * K) = 12 * exp 1 * c * K := by ring
  rw [e1, e2] at h1
  linarith

theorem alpha_le {k : ℕ} {K c : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c) :
    1 + (12 * exp 1 * c * K) ^ k ≤ 2 * (1 + 12 * exp 1 * c) ^ k * K ^ k := by
  have hK0 : 0 ≤ K := by linarith
  have hKk : 1 ≤ K ^ k := one_le_pow₀ hK
  have he := exp_pos 1
  have h1 : 1 ≤ (1 + 12 * exp 1 * c) ^ k := one_le_pow₀ (by nlinarith)
  have h2 : (12 * exp 1 * c) ^ k ≤ (1 + 12 * exp 1 * c) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  rw [mul_pow]
  have h3 : 1 ≤ (1 + 12 * exp 1 * c) ^ k * K ^ k := by nlinarith
  have h4 : (12 * exp 1 * c) ^ k * K ^ k ≤ (1 + 12 * exp 1 * c) ^ k * K ^ k :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  linarith

theorem exp_E2_le_E1 {c₀ ℓ K : ℝ} (hc : 0 < c₀) (hℓ : 0 < ℓ) (hK : 0 ≤ K) :
    exp (-(c₀ * (2 * (ℓ * K)) / ℓ)) ≤ exp (-(c₀ * (ℓ * K) / ℓ)) := by
  apply exp_le_exp.2
  rw [show c₀ * (2 * (ℓ * K)) / ℓ = 2 * (c₀ * K) by field_simp,
    show c₀ * (ℓ * K) / ℓ = c₀ * K by field_simp]
  nlinarith

theorem exp_E1_le_one {c₀ ℓ K : ℝ} (hc : 0 < c₀) (hℓ : 0 < ℓ) (hK : 0 ≤ K) :
    exp (-(c₀ * (ℓ * K) / ℓ)) ≤ 1 := by
  apply exp_le_one_iff.2
  have : 0 ≤ c₀ * (ℓ * K) / ℓ := by positivity
  linarith

end ScQ

section TermsQ2

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
/-- **(5.105)**: the integrand of the quadratic variation (5.103) of the martingale of (5.91),
`(Wℓ_vη_v)^{2m} (1-u) ((U_{u,v} ⊗ U_{u,v}) ∘ (Q_u ⊗ Q_u) ∘ (E ⊗ E)_u)_{a,a} ≺ 1 + Λ`, uniformly in
`s ≤ u ≤ v ≤ t`, `σ`, `a` ((7.16) Case 2 on the doubled loop, (5.104), (5.77)). -/
theorem QV_Q_stochDom (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ} (H : Hierarchy X E s t n)
    (h510 : Lemma510 X E s t H) {Λ : ℕ → ℝ} (hΛ : ∀ N, 0 ≤ Λ N)
    (hEE : StochDom B.P
      (fun N (p : TimeIcc s t N × ((Fin (n + 2) → Bool) × LoopArg (B.L N) ((n + 2) + (n + 2)))) ω =>
        ‖H.EE N p.1 ω p.2.1 p.2.2‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) * (etaT E p.1)⁻¹ * Λ N)) :
    StochDom B.P (fun N (q : TimeIcc s t N × (TimeIcc s t N × LoopData (B.L N) (n + 2))) ω =>
      if (q.1 : ℝ) ≤ q.2.1 then B.scale E N q.2.1 ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))
        * ‖Uker (B.L N) (xi2 E q.2.2.1) ((q.1 : ℝ) : ℂ) ((q.2.1 : ℝ) : ℂ)
          (QQ (B.L N) ((q.1 : ℝ) : ℂ) (H.EE N q.1 ω q.2.2.1)) (Fin.append q.2.2.2 q.2.2.2)‖
      else 0) (fun N _ _ => 1 + Λ N) := by
  refine stochDom_of_logBound hΛ (c₁ := cZero / 4) (by have := cZero_pos; positivity)
    (4 * (n + 2) + 2 * (n + 1) + 2) (8 * (n + 2) + 2 * (n + 1) + 3) fun τ₁ hτ₁ hτ₁1 D hD => ?_
  have hc0 : 0 ≤ cTwo52 := cTwo52_pos.le
  have hz0 := cZero_pos
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : ℝ, α₀ = 2 * (1 + 12 * exp 1 * cTwo52) ^ (n + 1) := ⟨_, rfl⟩
  have hα₀0 : 0 ≤ α₀ := by rw [hα₀]; positivity
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : ℝ, S₀ = 1 + α₀ + (2 * cTwo52) ^ (n + 1) := ⟨_, rfl⟩
  have hS₀0 : 0 ≤ S₀ := by rw [hS₀]; positivity
  obtain ⟨ck, hck⟩ : ∃ ck : ℝ, ck = cKerSumZero ((n + 2) + (n + 2)) := ⟨_, rfl⟩
  obtain ⟨ce, hce⟩ : ∃ ce : ℝ, ce = cKerSumZeroErr ((n + 2) + (n + 2)) := ⟨_, rfl⟩
  have hck0 : 0 ≤ ck := hck ▸ cKerSumZero_nonneg _
  have hce0 : 0 ≤ ce := hce ▸ cKerSumZeroErr_nonneg _
  have him : 0 < (mE E).im := mE_im_pos hE
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = ck * 4 ^ (4 * (n + 2)) * α₀ ^ 2 / (mE E).im := ⟨_, rfl⟩
  obtain ⟨Ce, hCe⟩ : ∃ Ce : ℝ,
      Ce = (4 * ck * 4 ^ (4 * (n + 2)) + 10 * ce) * S₀ ^ 2 * (1 + 1 / (mE E).im) := ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  have hCe0 : 0 ≤ Ce := by rw [hCe]; positivity
  refine ⟨Cm + Ce, add_nonneg hCm0 hCe0, _, (good_of_stochDom hEE hτ₁).inter
    (good_of_stochDom (h510.EE_decay τ₁ hτ₁ D hD) hτ₁), ?_⟩
  filter_upwards [flow_crude hE (fun N => (hs0 N).le) hst ht1 hc] with N ⟨hLN, hWN, hN1, hu⟩
  intro ω ⟨hω1, hω2⟩ q
  simp only [Set.mem_ofPred_eq] at hω1 hω2
  obtain ⟨uu, vv, σ, a⟩ := q
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hΛN := hΛ N
  have hlog := Real.log_nonneg hN1'
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (N : ℝ) ^ τ₁ := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := hK ▸ Real.one_le_rpow hN1' hτ₁.le
  have hKN : K ≤ N := hK ▸ rpow_le_self_of_le_one hN1' hτ₁1
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (N : ℝ) ^ (-D) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ Real.rpow_nonneg hN0.le _
  obtain ⟨e', he'⟩ : ∃ e' : ℝ, e' = exp (-(cZero / 4 * K)) := ⟨_, rfl⟩
  have he'0 : 0 ≤ e' := he' ▸ (exp_pos _).le
  have htarget0 : 0 ≤ (Cm + Ce) * (N : ℝ) ^ (((4 * (n + 2) + 2 * (n + 1) + 2 : ℕ) : ℝ) * τ₁)
      * (1 + Real.log N) * (1 + Λ N) + (Cm + Ce) * (N : ℝ) ^ (8 * (n + 2) + 2 * (n + 1) + 3)
      * ((N : ℝ) ^ (-D) + exp (-(cZero / 4 * (N : ℝ) ^ τ₁)) * (1 + Λ N)) := by
    have : 0 ≤ Cm + Ce := add_nonneg hCm0 hCe0
    positivity
  dsimp only
  split_ifs with huv
  swap
  · exact htarget0
  rw [← hK, ← hx, ← he']
  -- the times
  have hu0 : 0 ≤ (uu : ℝ) := ((hs0 N).trans_le uu.2.1).le
  have hu1 : (uu : ℝ) < 1 := uu.2.2.trans_lt (ht1 N)
  have hv0 : 0 < (vv : ℝ) := (hs0 N).trans_le vv.2.1
  have hv1 : (vv : ℝ) < 1 := vv.2.2.trans_lt (ht1 N)
  have h1u : 0 < 1 - (uu : ℝ) := by linarith
  have h1v : 0 < 1 - (vv : ℝ) := by linarith
  obtain ⟨hAu1, hAuN, huN⟩ := hu uu
  obtain ⟨hAv1, hAvN, hvN⟩ := hu vv
  have hL3 := B.three_le_L N
  have hℓu := half_le_ellHat_real (B.L N) hL3 hu0 hu1
  have hℓu0 : 0 < ellHat (B.L N) ((uu : ℝ) : ℂ) := by linarith
  have hℓv0 := ellHat_real_pos' (B.L N) hL3 hv0.le hv1
  -- the input tensor
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = K * ((B.scale E N uu)⁻¹ ^ (2 * (n + 2)) * (etaT E uu)⁻¹ * Λ N) :=
    ⟨_, rfl⟩
  have hη := etaT_pos hE hu1
  have hAu0 : 0 < B.scale E N uu := by linarith
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hBe : ∀ c, ‖H.EE N uu ω σ c‖ ≤ e := fun c => by rw [he, hK]; exact hω1 (uu, (σ, c))
  have hBd : FastDecay (B.L N) (ellHat (B.L N) ((uu : ℝ) : ℂ) * K) (K * x) (H.EE N uu ω σ) :=
    fastDecay_of_farInd fun c => by rw [hK, hx]; exact hω2 (uu, (σ, c))
  have hδ0 : 0 ≤ K * x := mul_nonneg hK0 hx0
  have hR : 0 < ellHat (B.L N) ((uu : ℝ) : ℂ) * K := mul_pos hℓu0 (by linarith)
  have hR2 : 0 < 2 * (ellHat (B.L N) ((uu : ℝ) : ℂ) * K) := by linarith
  -- the two slot projections
  have h2max := norm_Q2_le (B.L N) hL3 hu0 hu1 (k := n + 1) hR he0 hδ0 hBe hBd
  have h2dec := fastDecay_Q2 (B.L N) hL3 hu0 hu1 (k := n + 1) hR he0 hδ0 hBe hBd
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (cTwo52 / ellHat (B.L N) ((uu : ℝ) : ℂ)) ^ (n + 1) := ⟨_, rfl⟩
  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : ℝ,
      W₁ = (2 * exp 1 * (ellHat (B.L N) ((uu : ℝ) : ℂ) * K + 1)) ^ (n + 1) := ⟨_, rfl⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W₂ : ℝ,
      W₂ = (2 * exp 1 * (2 * (ellHat (B.L N) ((uu : ℝ) : ℂ) * K) + 1)) ^ (n + 1) := ⟨_, rfl⟩
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : ℝ, E₁ = exp (-(cZero * (ellHat (B.L N) ((uu : ℝ) : ℂ) * K)
      / ellHat (B.L N) ((uu : ℝ) : ℂ))) := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E₂ : ℝ, E₂ = exp (-(cZero * (2 * (ellHat (B.L N) ((uu : ℝ) : ℂ) * K))
      / ellHat (B.L N) ((uu : ℝ) : ℂ))) := ⟨_, rfl⟩
  obtain ⟨Lk, hLk⟩ : ∃ Lk : ℝ, Lk = (B.L N : ℝ) ^ (n + 1) := ⟨_, rfl⟩
  rw [← hW₁, ← hθ, ← hLk] at h2max
  rw [← hW₁, ← hθ, ← hLk, ← hE₁] at h2dec
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : ℝ, e₂ = e + (W₁ * e + Lk * (K * x)) * θ := ⟨_, rfl⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ₂ : ℝ, δ₂ = K * x + (W₁ * e + Lk * (K * x)) * θ * E₁ + Lk * (K * x) * θ :=
    ⟨_, rfl⟩
  rw [← he₂] at h2max
  rw [← hδ₂] at h2dec
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hW₁0 : 0 ≤ W₁ := by rw [hW₁]; positivity
  have hW₂0 : 0 ≤ W₂ := by rw [hW₂]; positivity
  have hLk0 : 0 ≤ Lk := by rw [hLk]; positivity
  have hE₁0 : 0 ≤ E₁ := hE₁ ▸ (exp_pos _).le
  have hE₂0 : 0 ≤ E₂ := hE₂ ▸ (exp_pos _).le
  have he₂0 : 0 ≤ e₂ := by rw [he₂]; positivity
  have hδ₂0 : 0 ≤ δ₂ := by rw [hδ₂]; positivity
  have h3max := norm_Q1_le (B.L N) hL3 hu0 hu1 (k := n + 1) hR2 he₂0 hδ₂0 h2max h2dec
  have h3dec := fastDecay_Q1 (B.L N) hL3 hu0 hu1 (k := n + 1) hR2 he₂0 hδ₂0 h2max h2dec
  rw [← hW₂, ← hθ, ← hLk] at h3max
  rw [← hW₂, ← hθ, ← hLk, ← hE₂] at h3dec
  rw [← QQ_eq] at h3max h3dec
  -- the scalar recursion
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 + (12 * exp 1 * cTwo52 * K) ^ (n + 1) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (2 * cTwo52) ^ (n + 1) * Lk := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hW₁θ : 1 + W₁ * θ ≤ α := by rw [hW₁, hθ, hα]; exact window1_le hℓu hK1 hc0
  have hW₂θ : 1 + W₂ * θ ≤ α := by rw [hW₂, hθ, hα]; exact window2_le hℓu hK1 hc0
  have hLθ : Lk * θ ≤ β := by
    rw [hθ, hβ, mul_comm]
    exact mul_le_mul_of_nonneg_right (div_pow_le_two_mul hℓu hc0) hLk0
  have hE21 : E₂ ≤ E₁ := by rw [hE₂, hE₁]; exact exp_E2_le_E1 hz0 hℓu0 hK0
  have hE1 : E₁ ≤ 1 := by rw [hE₁]; exact exp_E1_le_one hz0 hℓu0 hK0
  obtain ⟨hrec1, hrec2⟩ := QQ_chain_scalar hW₁θ hW₂θ hLθ hW₁0 hW₂0 hθ0 hLk0 he0 hδ0 hβ0 hE₁0 hE₂0
    hE21 hE1
  rw [← he₂, ← hδ₂] at hrec1 hrec2
  obtain ⟨e₃, he₃⟩ : ∃ e₃ : ℝ, e₃ = e₂ + (W₂ * e₂ + Lk * δ₂) * θ := ⟨_, rfl⟩
  obtain ⟨δ₃, hδ₃⟩ : ∃ δ₃ : ℝ, δ₃ = δ₂ + (W₂ * e₂ + Lk * δ₂) * θ * E₂ + Lk * δ₂ * θ := ⟨_, rfl⟩
  rw [← he₃] at h3max hrec1
  rw [← hδ₃] at h3dec hrec2
  have he₃0 : 0 ≤ e₃ := by rw [he₃]; positivity
  have hδ₃0 : 0 ≤ δ₃ := by rw [hδ₃]; positivity
  -- (5.93) on the doubled loop
  have hdec4 : FastDecay (B.L N) (ellHat (B.L N) ((uu : ℝ) : ℂ) * (4 * K)) δ₃
      (QQ (B.L N) ((uu : ℝ) : ℂ) (H.EE N uu ω σ)) :=
    FastDecay.mono (B.L N) h3dec (le_of_eq (by ring)) le_rfl
  have hker := norm_Uker_fastDecay_le_sumZero (B.L N) (n := (n + 2) + (n + 2)) (by omega) hL3 hu0
    huv hv0.le hv1 (ξ := xi2 E σ) (xi2_ne_zero hE σ) (norm_xi2_le hE σ) (K := 4 * K) (M := e₃)
    (δ := δ₃) (by linarith) he₃0 hδ₃0 h3max hdec4
    (sumZeroAt_QQ (B.L N) hL3 (norm_ofReal_lt_one hu0 hu1) _) (Fin.append a a)
  rw [← hck, ← hce] at hker
  have hexp2 : ∀ (y : ℝ), y ^ ((n + 2) + (n + 2)) = y ^ (2 * (n + 2)) := fun y => by
    rw [show (n + 2) + (n + 2) = 2 * (n + 2) by ring]
  rw [hexp2, hexp2, hexp2, show 2 * ((n + 2) + (n + 2)) = 2 * (2 * (n + 2)) by ring] at hker
  -- the scales
  set κA := (B.W N : ℝ) * (mE E).im with hκA
  have hκA0 : 0 < κA := mul_pos (by exact_mod_cast B.W_pos N) him
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 - (uu : ℝ)) * ellHat (B.L N) ((uu : ℝ) : ℂ)
      / ((1 - (vv : ℝ)) * ellHat (B.L N) ((vv : ℝ) : ℂ)) := ⟨_, rfl⟩
  rw [← hr] at hker
  have hAvr : B.scale E N vv * r = B.scale E N uu := by
    rw [hr, Band.scale_eq, Band.scale_eq]; field_simp
  have hAv0 : 0 < B.scale E N vv := by linarith
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hrN : r ≤ N := by
    have : r ≤ B.scale E N uu := by
      rw [← hAvr]; exact le_mul_of_one_le_left hr0 hAv1
    linarith
  have hρ0 : 0 ≤ (1 - (uu : ℝ)) / (1 - (vv : ℝ)) := div_nonneg h1u.le h1v.le
  have hρN : (1 - (uu : ℝ)) / (1 - (vv : ℝ)) ≤ N := by
    calc (1 - (uu : ℝ)) / (1 - (vv : ℝ)) ≤ 1 / (1 - (vv : ℝ)) :=
          div_le_div_of_nonneg_right (by linarith) h1v.le
      _ = (1 - (vv : ℝ))⁻¹ := one_div _
      _ ≤ N := hvN
  -- the inputs of the final power counting
  have hetaT : etaT E uu = (1 - (uu : ℝ)) * (mE E).im := rfl
  have hen : e ≤ K ^ 2 * Λ N * ((B.scale E N uu)⁻¹ ^ (2 * (n + 2))
      * ((1 - (uu : ℝ)) * (mE E).im)⁻¹) := by
    rw [he, ← hetaT]
    have hK2 : K ≤ K ^ 2 := by simpa using pow_le_pow_right₀ hK1 (show 1 ≤ 2 by norm_num)
    have : 0 ≤ (B.scale E N uu)⁻¹ ^ (2 * (n + 2)) * (etaT E uu)⁻¹ * Λ N := by positivity
    calc K * ((B.scale E N uu)⁻¹ ^ (2 * (n + 2)) * (etaT E uu)⁻¹ * Λ N)
        ≤ K ^ 2 * ((B.scale E N uu)⁻¹ ^ (2 * (n + 2)) * (etaT E uu)⁻¹ * Λ N) :=
          mul_le_mul_of_nonneg_right hK2 this
      _ = _ := by ring
  have hec : e ≤ (N : ℝ) ^ 3 * Λ N / (mE E).im := by
    rw [he, hetaT]
    have hAi : (B.scale E N uu)⁻¹ ^ (2 * (n + 2)) ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hAu1)
    have hηi : ((1 - (uu : ℝ)) * (mE E).im)⁻¹ ≤ N / (mE E).im := by
      rw [mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right huN (by positivity)
    have hN2 : (N : ℝ) * N ≤ (N : ℝ) ^ 3 := by
      rw [← pow_two]; exact pow_le_pow_right₀ hN1' (by norm_num)
    calc K * ((B.scale E N uu)⁻¹ ^ (2 * (n + 2)) * ((1 - (uu : ℝ)) * (mE E).im)⁻¹ * Λ N)
        ≤ N * (1 * (N / (mE E).im) * Λ N) := by gcongr
      _ = ((N : ℝ) * N) * Λ N / (mE E).im := by ring
      _ ≤ (N : ℝ) ^ 3 * Λ N / (mE E).im := by gcongr
  have hδN : K * x ≤ N * x := mul_le_mul_of_nonneg_right hKN hx0
  have hE₁e' : E₁ ≤ e' := by rw [hE₁, he']; exact exp_arg2 hz0 hℓu0 hK0
  have hαb : α ≤ α₀ * K ^ (n + 1) := by
    rw [hα, hα₀]; have := alpha_le (k := n + 1) hK1 hc0; linarith
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hSb : 1 + α + β ≤ S₀ * (N : ℝ) ^ (n + 1) := by
    have h1 : α ≤ α₀ * (N : ℝ) ^ (n + 1) :=
      hαb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK0 hKN _) hα₀0)
    have h2 : β ≤ (2 * cTwo52) ^ (n + 1) * (N : ℝ) ^ (n + 1) := by
      rw [hβ, hLk]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hLN _)
        (by positivity)
    have h3 : (1 : ℝ) ≤ (N : ℝ) ^ (n + 1) := one_le_pow₀ hN1'
    rw [hS₀]
    have e1 : (1 + α₀ + (2 * cTwo52) ^ (n + 1)) * (N : ℝ) ^ (n + 1)
        = (N : ℝ) ^ (n + 1) + α₀ * (N : ℝ) ^ (n + 1) + (2 * cTwo52) ^ (n + 1) * (N : ℝ) ^ (n + 1) := by
      ring
    linarith
  have hfinal := QV_final_scalar (m := n + 2) (k := n + 1) (Av := B.scale E N vv)
    (Au := B.scale E N uu) (r := r) (ρ' := (1 - (uu : ℝ)) / (1 - (vv : ℝ))) (Lr := B.L N)
    (Nr := N) (K := K) (Λ := Λ N) (im := (mE E).im) (u := uu) (x := x) (e' := e') (E := E₁)
    (ck := ck) (ce := ce) (α := α) (S := 1 + α + β) (e := e) (δ := K * x) (e₃ := e₃) (δ₃ := δ₃)
    (α₀ := α₀) (S₀ := S₀) hck0 hce0 hα₀0 hS₀0 hrec1 hrec2 hen hec he0 hδN hδ0 hE₁e' hE₁0 hαb hα0
    hSb (by positivity) hAvr hAv1 hAvN hAu1 hr0 hrN hρ0 hρN (Nat.cast_nonneg _) hLN hK1 hKN h1u
    (by linarith) him hΛN hx0 he'0 he₃0 hδ₃0
  have hpre : 0 ≤ B.scale E N vv ^ (2 * (n + 2)) * (1 - (uu : ℝ)) := by positivity
  calc B.scale E N vv ^ (2 * (n + 2)) * (1 - (uu : ℝ))
        * ‖Uker (B.L N) (xi2 E σ) ((uu : ℝ) : ℂ) ((vv : ℝ) : ℂ)
          (QQ (B.L N) ((uu : ℝ) : ℂ) (H.EE N uu ω σ)) (Fin.append a a)‖
      ≤ B.scale E N vv ^ (2 * (n + 2)) * (1 - (uu : ℝ)) * (ck * (4 * K) ^ (2 * (2 * (n + 2)))
          * r ^ (2 * (n + 2)) * e₃ + ce * (B.L N : ℝ) ^ (2 * (n + 2))
          * ((1 - (uu : ℝ)) / (1 - (vv : ℝ))) ^ (2 * (n + 2)) * δ₃) :=
        mul_le_mul_of_nonneg_left hker hpre
    _ ≤ _ := hfinal
    _ ≤ (Cm + Ce) * K ^ (4 * (n + 2) + 2 * (n + 1) + 2) * ((1 + Real.log N) * (1 + Λ N))
        + (Cm + Ce) * (N : ℝ) ^ (8 * (n + 2) + 2 * (n + 1) + 3) * (x + e' * (1 + Λ N)) := by
        rw [← hCm, ← hCe]
        have hKp : 0 ≤ K ^ (4 * (n + 2) + 2 * (n + 1) + 2) := by positivity
        have h1 : Λ N ≤ (1 + Real.log N) * (1 + Λ N) := by
          have e : (1 + Real.log N) * (1 + Λ N) = 1 + Λ N + Real.log N + Real.log N * Λ N := by ring
          rw [e]; linarith [mul_nonneg hlog hΛN]
        have hX : 0 ≤ (N : ℝ) ^ (8 * (n + 2) + 2 * (n + 1) + 3) * (x + e' * (1 + Λ N)) := by
          positivity
        have a1 : Cm * K ^ (4 * (n + 2) + 2 * (n + 1) + 2) * Λ N
            ≤ (Cm + Ce) * K ^ (4 * (n + 2) + 2 * (n + 1) + 2) * ((1 + Real.log N) * (1 + Λ N)) := by
          gcongr; linarith
        have a2 : Ce * (N : ℝ) ^ (8 * (n + 2) + 2 * (n + 1) + 3) * (x + e' * (1 + Λ N))
            ≤ (Cm + Ce) * (N : ℝ) ^ (8 * (n + 2) + 2 * (n + 1) + 3) * (x + e' * (1 + Λ N)) := by
          gcongr; linarith
        linarith
    _ = _ := by
        rw [hK, show ((4 * (n + 2) + 2 * (n + 1) + 2 : ℕ) : ℝ) * τ₁
          = τ₁ * ((4 * (n + 2) + 2 * (n + 1) + 2 : ℕ) : ℝ) by ring, ← rpow_pow_eq]
        ring

theorem integral_inv_one_sub_eq {s v : ℝ} (hsv : s ≤ v) (hv1 : v < 1) :
    ∫ u in s..v, (1 - u)⁻¹ = Real.log ((1 - s) / (1 - v)) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) 1,
    integral_inv_of_pos (by linarith) (by linarith)]

omit X in
/-- A deterministic bound that is `≤ N^τ g` for every `τ > 0` (eventually) is `≺ g`. -/
theorem stochDom_trans_det {U : ℕ → Type*} {ξ : ∀ N, U N → Ω → ℝ} {f g : ∀ N, U N → ℝ}
    (h : StochDom B.P ξ (fun N u _ => f N u))
    (hfg : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u, f N u ≤ (N : ℝ) ^ τ * g N u) :
    StochDom B.P ξ (fun N u _ => g N u) := by
  refine h.trans (StochDom.of_eventually_empty fun τ hτ => ?_)
  filter_upwards [hfg τ hτ] with N hN
  ext ω
  simp only [badSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  exact hN

/-- **The martingale term of (5.94)**: `(Wℓ_vη_v)^m |∫_s^v U_{u,v,σ} ∘ Q_u ∘ dE^{(M)}_u| ≺ Λ^{1/2}`,
from (5.103) + BDG (`Hierarchy.bdgQ`) and (5.105) (`QV_Q_stochDom`). -/
theorem termM (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ} (H : Hierarchy X E s t n)
    (h510 : Lemma510 X E s t H) {Λ : ℕ → ℝ} (hΛ : ∀ N, 0 ≤ Λ N) (hΛ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Λ N)
    (hY : StochDom B.P (Step3.flowXiL X E s t (2 * (n + 2) + 2)) (fun N _ _ => Λ N)) :
    StochDom B.P (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      B.scale E N p.1 ^ (n + 2) * ‖H.martQ N p.1 ω p.2.1 p.2.2‖)
      (fun N _ _ => Λ N ^ ((1 : ℝ) / 2)) := by
  have hApos : ∀ N (v : TimeIcc s t N), 0 < B.scale E N v := fun N v =>
    B.scale_pos hE N ((hs0 N).trans_le v.2.1) (v.2.2.trans_lt (ht1 N))
  have h1u : ∀ N (u : TimeIcc s t N), 0 < 1 - (u : ℝ) := fun N u => by
    linarith [u.2.2.trans_lt (ht1 N)]
  have hQV := QV_Q_stochDom X hE hs0 hst ht1 hc H h510 hΛ (EE_stochDom X hE hs0 ht1 H h510 hY)
  -- the premise of `bdgQ`
  set Γ : ∀ N, TimeIcc s t N × LoopData (B.L N) (n + 2) → ℝ :=
    fun N p => 2 * (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) * Λ N with hΓ
  set w : ℕ → ℝ → ℝ → ℝ := fun _ u _ => (1 - u)⁻¹ with hw
  have hΓ0 : ∀ N p, 0 ≤ Γ N p := fun N p => by
    have := hApos N p.1; have := hΛ N; simp only [hΓ]; positivity
  have hw0 : ∀ N u v, s N ≤ u → u ≤ v → v ≤ t N → 0 ≤ w N u v := fun N u v _ huv hvt => by
    simp only [hw]; have := ht1 N; exact inv_nonneg.2 (by linarith)
  have hwint : ∀ N (v : ℝ), s N ≤ v → v ≤ t N →
      IntervalIntegrable (fun u => w N u v) MeasureTheory.volume (s N) v := fun N v hsv hvt => by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun u hu => ?_
    rw [Set.uIcc_of_le hsv] at hu
    have := ht1 N
    linarith [hu.2]
  set g : ∀ N, TimeIcc s t N × (TimeIcc s t N × LoopData (B.L N) (n + 2)) → Ω → ℝ :=
    fun N q _ => (B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))⁻¹ with hg
  have hg0 : ∀ N q ω, 0 ≤ g N q ω := fun N q ω => by
    have := hApos N q.2.1; have := h1u N q.1; simp only [hg]; positivity
  have hξ0 : ∀ N (q : TimeIcc s t N × (TimeIcc s t N × LoopData (B.L N) (n + 2))) ω,
      0 ≤ (if (q.1 : ℝ) ≤ q.2.1 then B.scale E N q.2.1 ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))
        * ‖Uker (B.L N) (xi2 E q.2.2.1) ((q.1 : ℝ) : ℂ) ((q.2.1 : ℝ) : ℂ)
          (QQ (B.L N) ((q.1 : ℝ) : ℂ) (H.EE N q.1 ω q.2.2.1)) (Fin.append q.2.2.2 q.2.2.2)‖
      else 0) := fun N q ω => by
    have := hApos N q.2.1; have := h1u N q.1
    split_ifs <;> positivity
  have hm := StochDom.mul hξ0 hg0 (StochDom.refl hg0) hQV
  have hprem : StochDom B.P
      (fun N (q : TimeIcc s t N × (TimeIcc s t N × LoopData (B.L N) (n + 2))) ω =>
        if (q.1 : ℝ) ≤ q.2.1 then
          ‖Uker (B.L N) (xi2 E q.2.2.1) ((q.1 : ℝ) : ℂ) ((q.2.1 : ℝ) : ℂ)
            (QQ (B.L N) ((q.1 : ℝ) : ℂ) (H.EE N q.1 ω q.2.2.1)) (Fin.append q.2.2.2 q.2.2.2)‖
        else 0)
      (fun N q _ => Γ N q.2 * w N q.1 q.2.1) := by
    refine Step3.stochDom_mono (fun N q _ => mul_nonneg (hΓ0 N q.2)
      (by simp only [hw]; exact (inv_pos.2 (h1u N q.1)).le)) 1 ?_ (StochDom.of_le_left ?_ hm)
    · filter_upwards [hΛ1] with N hN q ω
      simp only [hg, hΓ, hw, one_mul, Pi.mul_apply]
      have := hApos N q.2.1; have := h1u N q.1
      have hpos : 0 ≤ (B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))⁻¹ := by positivity
      calc (B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))⁻¹ * (1 + Λ N)
          ≤ (B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))⁻¹ * (2 * Λ N) :=
            mul_le_mul_of_nonneg_left (by linarith) hpos
        _ = _ := by ring
    · intro N q ω
      simp only [hg, Pi.mul_apply]
      have hA := hApos N q.2.1; have hu := h1u N q.1
      split_ifs with h
      · have e1 : (B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))⁻¹
            * (B.scale E N q.2.1 ^ (2 * (n + 2)) * (1 - (q.1 : ℝ)) * ‖Uker (B.L N) (xi2 E q.2.2.1)
              ((q.1 : ℝ) : ℂ) ((q.2.1 : ℝ) : ℂ) (QQ (B.L N) ((q.1 : ℝ) : ℂ) (H.EE N q.1 ω q.2.2.1))
              (Fin.append q.2.2.2 q.2.2.2)‖)
            = ‖Uker (B.L N) (xi2 E q.2.2.1) ((q.1 : ℝ) : ℂ) ((q.2.1 : ℝ) : ℂ)
              (QQ (B.L N) ((q.1 : ℝ) : ℂ) (H.EE N q.1 ω q.2.2.1)) (Fin.append q.2.2.2 q.2.2.2)‖ := by
          have hAA : (B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * B.scale E N q.2.1 ^ (2 * (n + 2)) = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hA.ne', one_pow]
          have huu : (1 - (q.1 : ℝ))⁻¹ * (1 - (q.1 : ℝ)) = 1 := inv_mul_cancel₀ hu.ne'
          calc _ = ((B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * B.scale E N q.2.1 ^ (2 * (n + 2)))
                * ((1 - (q.1 : ℝ))⁻¹ * (1 - (q.1 : ℝ))) * ‖Uker (B.L N) (xi2 E q.2.2.1)
                  ((q.1 : ℝ) : ℂ) ((q.2.1 : ℝ) : ℂ) (QQ (B.L N) ((q.1 : ℝ) : ℂ)
                  (H.EE N q.1 ω q.2.2.1)) (Fin.append q.2.2.2 q.2.2.2)‖ := by ring
            _ = _ := by rw [hAA, huu, one_mul, one_mul]
        rw [e1]
      · simp
  have hM := H.bdgQ Γ w hΓ0 hw0 hwint hprem
  -- multiply by `(Wℓ_vη_v)^m`
  have hA0 : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) (_ : Ω),
      0 ≤ B.scale E N p.1 ^ (n + 2) := fun N p _ => (pow_pos (hApos N p.1) _).le
  have hM2 := StochDom.mul (fun N p ω => norm_nonneg (H.martQ N p.1 ω p.2.1 p.2.2)) hA0
    (StochDom.refl hA0) hM
  refine stochDom_trans_det (f := fun N p => B.scale E N p.1 ^ (n + 2)
    * (Γ N p * ∫ u in (s N)..(p.1 : ℝ), w N u p.1) ^ ((1 : ℝ) / 2)) hM2 fun τ hτ => ?_
  have hlogN : ∀ᶠ N : ℕ in atTop, 2 * Real.log N ≤ (N : ℝ) ^ (2 * τ) := by
    filter_upwards [eventually_ge_atTop 1,
      eventually_const_mul_rpow_le (2 / τ) (show τ < 2 * τ by linarith)] with N hN1 hN
    have := log_le_rpow_div_nat N hτ
    have e : 2 * ((N : ℝ) ^ τ / τ) = 2 / τ * (N : ℝ) ^ τ := by ring
    linarith
  filter_upwards [hlogN, flow_crude hE (fun N => (hs0 N).le) hst ht1 hc] with N hN ⟨hLN, hWN, hN1, hu⟩
  intro p
  have hA := hApos N p.1
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
  have hsv : s N ≤ (p.1 : ℝ) := p.1.2.1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  obtain ⟨-, -, hvN⟩ := hu p.1
  have hint : ∫ u in (s N)..(p.1 : ℝ), w N u p.1 = Real.log ((1 - s N) / (1 - (p.1 : ℝ))) := by
    simp only [hw]; exact integral_inv_one_sub_eq hsv hu1
  have h1v : 0 < 1 - (p.1 : ℝ) := by linarith
  have hρ1 : 1 ≤ (1 - s N) / (1 - (p.1 : ℝ)) := by rw [le_div_iff₀ h1v]; linarith
  have hρN : (1 - s N) / (1 - (p.1 : ℝ)) ≤ N := by
    calc (1 - s N) / (1 - (p.1 : ℝ)) ≤ 1 / (1 - (p.1 : ℝ)) :=
          div_le_div_of_nonneg_right (by linarith [hs0 N]) h1v.le
      _ = (1 - (p.1 : ℝ))⁻¹ := one_div _
      _ ≤ N := hvN
  have hlog0 : 0 ≤ Real.log ((1 - s N) / (1 - (p.1 : ℝ))) := Real.log_nonneg hρ1
  have hlogle : Real.log ((1 - s N) / (1 - (p.1 : ℝ))) ≤ Real.log N :=
    Real.log_le_log (by linarith) hρN
  have hΛN := hΛ N
  rw [hint]
  simp only [hΓ]
  -- `A^m (2 A^{-2m} Λ log ρ)^{1/2} = (2 Λ log ρ)^{1/2}`
  have hsq : B.scale E N p.1 ^ (n + 2)
      = (B.scale E N p.1 ^ (2 * (n + 2))) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hA.le]; congr 1; push_cast; ring
  rw [hsq, ← Real.mul_rpow (by positivity) (by positivity)]
  have e1 : B.scale E N p.1 ^ (2 * (n + 2)) * (2 * (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) * Λ N
      * Real.log ((1 - s N) / (1 - (p.1 : ℝ)))) = (2 * Real.log ((1 - s N) / (1 - (p.1 : ℝ)))) * Λ N := by
    have : B.scale E N p.1 ^ (2 * (n + 2)) * (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hA.ne', one_pow]
    calc B.scale E N p.1 ^ (2 * (n + 2)) * (2 * (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) * Λ N
          * Real.log ((1 - s N) / (1 - (p.1 : ℝ))))
        = (B.scale E N p.1 ^ (2 * (n + 2)) * (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)))
          * (2 * Real.log ((1 - s N) / (1 - (p.1 : ℝ)))) * Λ N := by ring
      _ = _ := by rw [this, one_mul]
  rw [e1, Real.mul_rpow (by positivity) hΛN]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hΛN _)
  have h2 : 2 * Real.log ((1 - s N) / (1 - (p.1 : ℝ))) ≤ (N : ℝ) ^ (2 * τ) := by linarith
  calc (2 * Real.log ((1 - s N) / (1 - (p.1 : ℝ)))) ^ ((1 : ℝ) / 2)
      ≤ ((N : ℝ) ^ (2 * τ)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    _ = (N : ℝ) ^ τ := by rw [← Real.rpow_mul (Nat.cast_nonneg N)]; congr 1; ring

end TermsQ2


/-! ### Lemma 5.11 / Case 1 of (7.16): the non-alternating charges -/

section Short

variable (L : ℕ) [NeZero L]

/-- **(7.16) Case 1 on one term** (a short edge `σ_k = σ_{k+1}`), in the scale form:
for a `(ℓ_u K, δ)`-fast-decaying tensor bounded by `A_u^{-m} ψ + ζ`,
`|U_{u,v,σ} ∘ G| ≤ C K^m A_v^{-m} ψ + C K^m ρ^m ζ + ρ^m δ`. -/
theorem norm_Uker_short_scale_le (hL : 3 ≤ L) {n : ℕ} {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) {σ : Fin (n + 2) → Bool} {k : Fin (n + 2)} (hk : σ k = σ (k + 1))
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv1 : v < 1) {κA : ℝ} (hκA : 0 < κA)
    {K ψ ζ δ : ℝ} (hK : 1 ≤ K) (hψ : 0 ≤ ψ) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ) {G : LoopArg L (n + 2) → ℂ}
    (hGM : ∀ b, ‖G b‖ ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ + ζ)
    (hG : FastDecay L (ellHat L (u : ℂ) * K) δ G) (a : LoopArg L (n + 2)) :
    ‖Uker L (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) G a‖
      ≤ cKerShort (n + 2) √κ * K ^ (n + 2) * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * ψ
        + (cKerShort (n + 2) √κ * K ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + ((1 - s) / (1 - v)) ^ (n + 2) * δ) := by
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓu := ellHat_real_pos' L hL hu0 hu1
  have hℓv := ellHat_real_pos' L hL (hu0.trans huv) hv1
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hM0 : 0 ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ + ζ := by positivity
  have key := norm_Uker_fastDecay_le_of_eq L hL hκ0 hκ1 hE hk hu0 huv hv1 hK hM0 hδ hGM hG a
  refine key.trans ?_
  set r := (1 - u) * ellHat L (u : ℂ) / ((1 - v) * ellHat L (v : ℂ)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hrρ : r ≤ (1 - s) / (1 - v) := ratio_le L hL hs0 hsu huv hv1
  have hq : (1 - u) / (1 - v) ≤ (1 - s) / (1 - v) := one_sub_div_le hsu hv1
  have hcancel : r ^ (n + 2) * (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2)
      = (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) := by
    rw [← mul_pow]; congr 1; rw [hr]; field_simp
  have hc := cKerShort_nonneg (n + 2) (Real.sqrt_pos.2 hκ0)
  have e1 : cKerShort (n + 2) √κ * K ^ (n + 2) * r ^ (n + 2)
      * ((κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ + ζ)
      = cKerShort (n + 2) √κ * K ^ (n + 2) * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * ψ
        + cKerShort (n + 2) √κ * K ^ (n + 2) * r ^ (n + 2) * ζ := by
    rw [← hcancel]; ring
  rw [e1, add_assoc]
  refine add_le_add le_rfl (add_le_add ?_ ?_)
  · gcongr
  · gcongr

/-- The time integrals of (5.84) (Case 1 of (7.16)). -/
theorem integral_term_short_le (hL : 3 ≤ L) {n : ℕ} {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) {σ : Fin (n + 2) → Bool} {k : Fin (n + 2)} (hk : σ k = σ (k + 1))
    {s v : ℝ} (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) {κA : ℝ} (hκA : 0 < κA)
    {K ψ ζ δ : ℝ} (hK : 1 ≤ K) (hψ : 0 ≤ ψ) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {G : ℝ → LoopArg L (n + 2) → ℂ}
    (hG : ∀ u, s ≤ u → u ≤ v → FastDecay L (ellHat L (u : ℂ) * K) δ (G u) ∧
      ∀ b, ‖G u b‖ ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * (ψ * (1 - u)⁻¹) + ζ)
    (a : LoopArg L (n + 2)) :
    (κA * ((1 - v) * ellHat L (v : ℂ))) ^ (n + 2)
        * ‖∫ u in s..v, Uker L (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) (G u) a‖
      ≤ cKerShort (n + 2) √κ * K ^ (n + 2) * ψ * Real.log ((1 - s) / (1 - v))
        + (κA * ((1 - v) * ellHat L (v : ℂ))) ^ (n + 2)
          * ((cKerShort (n + 2) √κ * K ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
            + ((1 - s) / (1 - v)) ^ (n + 2) * δ) * (v - s)) := by
  have hℓv := ellHat_real_pos' L hL (hs0.trans hsv) hv1
  have h1v : 0 < 1 - v := by linarith
  set Av := κA * ((1 - v) * ellHat L (v : ℂ)) with hAv
  have hAv0 : 0 < Av := by positivity
  have hint := norm_integral_le_log (f := fun u => Uker L (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) (G u) a)
    (α := cKerShort (n + 2) √κ * K ^ (n + 2) * Av⁻¹ ^ (n + 2) * ψ)
    (β := cKerShort (n + 2) √κ * K ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
      + ((1 - s) / (1 - v)) ^ (n + 2) * δ) hsv hv1
    (fun u hsu huv => by
      obtain ⟨hd, hb⟩ := hG u hsu huv
      have h1u : 0 < 1 - u := by linarith
      have := norm_Uker_short_scale_le L hL hκ0 hκ1 hE hk hs0 hsu huv hv1 hκA hK
        (by positivity : 0 ≤ ψ * (1 - u)⁻¹) hζ hδ hb hd a
      refine this.trans (le_of_eq ?_)
      rw [← hAv]; ring)
  have hAvn : Av ^ (n + 2) * Av⁻¹ ^ (n + 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hAv0.ne', one_pow]
  calc Av ^ (n + 2) * ‖∫ u in s..v, Uker L (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) (G u) a‖
      ≤ Av ^ (n + 2) * (cKerShort (n + 2) √κ * K ^ (n + 2) * Av⁻¹ ^ (n + 2) * ψ
          * Real.log ((1 - s) / (1 - v))
          + (cKerShort (n + 2) √κ * K ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
            + ((1 - s) / (1 - v)) ^ (n + 2) * δ) * (v - s)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (Av ^ (n + 2) * Av⁻¹ ^ (n + 2)) * (cKerShort (n + 2) √κ * K ^ (n + 2) * ψ
          * Real.log ((1 - s) / (1 - v)))
        + Av ^ (n + 2) * ((cKerShort (n + 2) √κ * K ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
            + ((1 - s) / (1 - v)) ^ (n + 2) * δ) * (v - s)) := by ring
    _ = _ := by rw [hAvn, one_mul]

end Short

section TermsShort

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- Charges with a repeated sign `σ_k = σ_{k+1}` (cyclically): the non-alternating `σ` of
(5.82), for which Case 1 of (7.16) applies (Lemma 5.11). -/
def NonAlt {n : ℕ} (σ : Fin (n + 2) → Bool) : Prop := ∃ k : Fin (n + 2), σ k = σ (k + 1)

instance {n : ℕ} : DecidablePred (NonAlt (n := n)) := fun σ => by
  unfold NonAlt; infer_instance

/-- The scalar bookkeeping of the Case-1 terms. -/
theorem short_scalar {A ρ K x c ψ₀ Nr lg Φ e' : ℝ} {m : ℕ} (hA0 : 0 ≤ A) (hAN : A ≤ Nr)
    (hρ0 : 0 ≤ ρ) (hρN : ρ ≤ Nr) (hK1 : 1 ≤ K) (hKN : K ≤ Nr) (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hψ₀ : 0 ≤ ψ₀) (hlog : 0 ≤ lg) (hΦ : 0 ≤ Φ) (he' : 0 ≤ e') :
    c * K ^ m * (K * (ψ₀ * Φ)) * lg + A ^ m * ((c * K ^ m * ρ ^ m * 0 + ρ ^ m * (K * x)) * 1)
      ≤ (c * ψ₀ + 1) * K ^ (m + 1) * (1 + lg) * (1 + Φ)
        + (c * ψ₀ + 1) * Nr ^ (2 * m + 1) * (x + e' * (1 + Φ)) := by
  have hN0 : 0 ≤ Nr := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hcψ : 0 ≤ c * ψ₀ := mul_nonneg hc hψ₀
  have h1 : c * K ^ m * (K * (ψ₀ * Φ)) * lg ≤ (c * ψ₀ + 1) * K ^ (m + 1) * (1 + lg) * (1 + Φ) := by
    have e : c * K ^ m * (K * (ψ₀ * Φ)) * lg = (c * ψ₀) * K ^ (m + 1) * (Φ * lg) := by ring
    rw [e]
    have hΦl : Φ * lg ≤ (1 + lg) * (1 + Φ) := by
      have e2 : (1 + lg) * (1 + Φ) = 1 + Φ + lg + Φ * lg := by ring
      rw [e2]; linarith
    have : (c * ψ₀) * K ^ (m + 1) * (Φ * lg) ≤ (c * ψ₀ + 1) * K ^ (m + 1) * ((1 + lg) * (1 + Φ)) := by
      gcongr; linarith
    linarith
  have h2 : A ^ m * ((c * K ^ m * ρ ^ m * 0 + ρ ^ m * (K * x)) * 1)
      ≤ (c * ψ₀ + 1) * Nr ^ (2 * m + 1) * (x + e' * (1 + Φ)) := by
    have e : A ^ m * ((c * K ^ m * ρ ^ m * 0 + ρ ^ m * (K * x)) * 1) = A ^ m * ρ ^ m * K * x := by ring
    rw [e]
    have h3 : A ^ m * ρ ^ m * K * x ≤ Nr ^ m * Nr ^ m * Nr * x := by gcongr
    have e2 : Nr ^ m * Nr ^ m * Nr = Nr ^ (2 * m + 1) := by ring
    rw [e2] at h3
    have h4 : Nr ^ (2 * m + 1) * x ≤ (c * ψ₀ + 1) * Nr ^ (2 * m + 1) * (x + e' * (1 + Φ)) := by
      have hx' : x ≤ x + e' * (1 + Φ) := le_add_of_nonneg_right (by positivity)
      calc Nr ^ (2 * m + 1) * x = 1 * Nr ^ (2 * m + 1) * x := by ring
        _ ≤ (c * ψ₀ + 1) * Nr ^ (2 * m + 1) * (x + e' * (1 + Φ)) := by gcongr; linarith
    linarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **(5.84), the drift term, Case 1** (non-alternating `σ`): `(Wℓ_vη_v)^m |∫_s^v U_{u,v,σ} ∘ F_u| ≺ 1 + Φ`. -/
theorem term1F {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 < s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ}
    (H : Hierarchy X E s t n) (h510 : Lemma510 X E s t H) {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hF : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω => ‖H.F N p.1 ω p.2.1 p.2.2‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n + 2) * (etaT E p.1)⁻¹ * ((2 * n + 3 : ℝ) * Φ N))) :
    StochDom B.P (fun N (pp : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      if NonAlt pp.2.1 then B.scale E N pp.1 ^ (n + 2) * ‖∫ u in (s N)..(pp.1 : ℝ),
        Uker (B.L N) (xiOf (mSigma E) pp.2.1) (u : ℂ) ((pp.1 : ℝ) : ℂ) (H.F N u ω pp.2.1) pp.2.2‖
      else 0) (fun N _ _ => 1 + Φ N) := by
  have hE : |E| < 2 := by linarith
  refine stochDom_of_logBound hΦ (c₁ := cZero / 4) (by have := cZero_pos; positivity)
    (n + 3) (2 * (n + 2) + 1) fun τ₁ hτ₁ hτ₁1 D hD => ?_
  have him : 0 < (mE E).im := mE_im_pos hE
  obtain ⟨cS, hcS⟩ : ∃ cS : ℝ, cS = cKerShort (n + 2) √κ := ⟨_, rfl⟩
  have hcS0 : 0 ≤ cS := hcS ▸ cKerShort_nonneg _ (Real.sqrt_pos.2 hκ0)
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : ℝ, ψ₀ = (2 * n + 3 : ℝ) / (mE E).im := ⟨_, rfl⟩
  have hψ₀0 : 0 ≤ ψ₀ := by rw [hψ₀]; positivity
  refine ⟨cS * ψ₀ + 1, by positivity, _, (good_of_stochDom hF hτ₁).inter
    (good_of_stochDom (h510.F_decay τ₁ hτ₁ D hD) hτ₁), ?_⟩
  filter_upwards [flow_crude hE (fun N => (hs0 N).le) hst ht1 hc] with N ⟨hLN, hWN, hN1, hu⟩
  intro ω ⟨hω1, hω2⟩ pp
  simp only [Set.mem_ofPred_eq] at hω1 hω2
  obtain ⟨vv, σ, a⟩ := pp
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hΦN := hΦ N
  have hlogN := Real.log_nonneg hN1'
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (N : ℝ) ^ τ₁ := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := hK ▸ Real.one_le_rpow hN1' hτ₁.le
  have hKN : K ≤ N := hK ▸ rpow_le_self_of_le_one hN1' hτ₁1
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (N : ℝ) ^ (-D) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ Real.rpow_nonneg hN0.le _
  have htarget0 : 0 ≤ (cS * ψ₀ + 1) * (N : ℝ) ^ (((n + 3 : ℕ) : ℝ) * τ₁) * (1 + Real.log N)
      * (1 + Φ N) + (cS * ψ₀ + 1) * (N : ℝ) ^ (2 * (n + 2) + 1)
      * ((N : ℝ) ^ (-D) + exp (-(cZero / 4 * (N : ℝ) ^ τ₁)) * (1 + Φ N)) := by positivity
  dsimp only
  split_ifs with hna
  swap
  · exact htarget0
  obtain ⟨k, hk⟩ := hna
  rw [← hK, ← hx]
  have hv1 : (vv : ℝ) < 1 := vv.2.2.trans_lt (ht1 N)
  have hsv : s N ≤ (vv : ℝ) := vv.2.1
  obtain ⟨hAv1, hAvN, hvN⟩ := hu vv
  have hL3 := B.three_le_L N
  set κA := (B.W N : ℝ) * (mE E).im with hκA
  have hκA0 : 0 < κA := mul_pos (by exact_mod_cast B.W_pos N) him
  -- the drift at the times `u ∈ [s, v]`
  have hG : ∀ u, s N ≤ u → u ≤ vv → FastDecay (B.L N) (ellHat (B.L N) (u : ℂ) * K) (K * x)
      (H.F N u ω σ) ∧ ∀ b, ‖H.F N u ω σ b‖
        ≤ (κA * ((1 - u) * ellHat (B.L N) (u : ℂ)))⁻¹ ^ (n + 2) * ((K * ψ₀ * Φ N) * (1 - u)⁻¹) + 0 := by
    intro u hsu huv
    obtain ⟨uu, huu⟩ : ∃ uu : TimeIcc s t N, (uu : ℝ) = u := ⟨⟨u, hsu, huv.trans vv.2.2⟩, rfl⟩
    subst huu
    refine ⟨fastDecay_of_farInd fun b => by rw [hK, hx]; exact hω2 (uu, (σ, b)), fun b => ?_⟩
    have h := hω1 (uu, (σ, b))
    rw [← hK] at h
    refine h.trans (le_of_eq ?_)
    rw [Band.scale_eq, hψ₀, add_zero]
    have hu1 : (uu : ℝ) < 1 := uu.2.2.trans_lt (ht1 N)
    have h1u : (1 : ℝ) - uu ≠ 0 := by linarith
    simp only [etaT, hκA]
    field_simp
  have key := integral_term_short_le (B.L N) hL3 hκ0 hκ1 hEκ hk (hs0 N).le hsv hv1 hκA0 hK1
    (by positivity) le_rfl (by positivity) hG a
  rw [← Band.scale_eq B E N vv, ← hcS] at key
  have h1v : 0 < 1 - (vv : ℝ) := by linarith
  have hρN : (1 - s N) / (1 - (vv : ℝ)) ≤ N := by
    calc (1 - s N) / (1 - (vv : ℝ)) ≤ 1 / (1 - (vv : ℝ)) :=
          div_le_div_of_nonneg_right (by linarith [hs0 N]) h1v.le
      _ = (1 - (vv : ℝ))⁻¹ := one_div _
      _ ≤ N := hvN
  have hρ1 : 1 ≤ (1 - s N) / (1 - (vv : ℝ)) := by rw [le_div_iff₀ h1v]; linarith
  have hlog : Real.log ((1 - s N) / (1 - (vv : ℝ))) ≤ Real.log N := Real.log_le_log (by linarith) hρN
  have hvs1 : (vv : ℝ) - s N ≤ 1 := by linarith [hs0 N]
  have hvs0 : 0 ≤ (vv : ℝ) - s N := by linarith
  calc B.scale E N vv ^ (n + 2) * ‖∫ u in (s N)..(vv : ℝ),
        Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) ((vv : ℝ) : ℂ) (H.F N u ω σ) a‖
      ≤ _ := key
    _ ≤ cS * K ^ (n + 2) * (K * (ψ₀ * Φ N)) * Real.log N + B.scale E N vv ^ (n + 2)
        * ((cS * K ^ (n + 2) * ((1 - s N) / (1 - (vv : ℝ))) ^ (n + 2) * 0
          + ((1 - s N) / (1 - (vv : ℝ))) ^ (n + 2) * (K * x)) * 1) := by
        have e : cS * K ^ (n + 2) * (K * ψ₀ * Φ N) = cS * K ^ (n + 2) * (K * (ψ₀ * Φ N)) := by ring
        rw [e]
        refine add_le_add (by gcongr) ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left hvs1 ?_
        positivity
    _ ≤ (cS * ψ₀ + 1) * K ^ (n + 2 + 1) * (1 + Real.log N) * (1 + Φ N)
        + (cS * ψ₀ + 1) * (N : ℝ) ^ (2 * (n + 2) + 1) * (x + exp (-(cZero / 4 * K)) * (1 + Φ N)) :=
        short_scalar (by linarith) hAvN (by positivity) hρN hK1 hKN hx0 hcS0 hψ₀0 hlogN hΦN
          (exp_pos _).le
    _ = _ := by
        rw [hK, show ((n + 3 : ℕ) : ℝ) * τ₁ = τ₁ * ((n + 2 + 1 : ℕ) : ℝ) by push_cast; ring,
          ← rpow_pow_eq]

omit X in
/-- **The martingale terms, generic**: from the BDG hypothesis and a bound `≺ 1 + Λ` on the
quadratic-variation integrand (normalized by `(Wℓ_vη_v)^{2m} (1-u)`), the martingale is
`(Wℓ_vη_v)^{-m} Λ^{1/2}`. -/
theorem mart_of_QV (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ} {Λ : ℕ → ℝ} (hΛ : ∀ N, 0 ≤ Λ N)
    (hΛ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Λ N)
    (I : ∀ N, TimeIcc s t N × (TimeIcc s t N × LoopData (B.L N) (n + 2)) → Ω → ℝ)
    (hI0 : ∀ N q ω, 0 ≤ I N q ω)
    (Mt : ∀ N, TimeIcc s t N × LoopData (B.L N) (n + 2) → Ω → ℝ) (hM0 : ∀ N p ω, 0 ≤ Mt N p ω)
    (hbdg : ∀ (Γ : ∀ N, TimeIcc s t N × LoopData (B.L N) (n + 2) → ℝ) (w : ℕ → ℝ → ℝ → ℝ),
      (∀ N p, 0 ≤ Γ N p) → (∀ N u v, s N ≤ u → u ≤ v → v ≤ t N → 0 ≤ w N u v) →
      (∀ N (v : ℝ), s N ≤ v → v ≤ t N →
        IntervalIntegrable (fun u => w N u v) MeasureTheory.volume (s N) v) →
      StochDom B.P I (fun N q _ => Γ N q.2 * w N q.1 q.2.1) →
      StochDom B.P Mt (fun N p _ => (Γ N p * ∫ u in (s N)..(p.1 : ℝ), w N u p.1) ^ ((1 : ℝ) / 2)))
    (hQV : StochDom B.P (fun N (q : TimeIcc s t N × (TimeIcc s t N × LoopData (B.L N) (n + 2))) ω =>
      B.scale E N q.2.1 ^ (2 * (n + 2)) * (1 - (q.1 : ℝ)) * I N q ω) (fun N _ _ => 1 + Λ N)) :
    StochDom B.P (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      B.scale E N p.1 ^ (n + 2) * Mt N p ω)
      (fun N _ _ => Λ N ^ ((1 : ℝ) / 2)) := by
  have hApos : ∀ N (v : TimeIcc s t N), 0 < B.scale E N v := fun N v =>
    B.scale_pos hE N ((hs0 N).trans_le v.2.1) (v.2.2.trans_lt (ht1 N))
  have h1u : ∀ N (u : TimeIcc s t N), 0 < 1 - (u : ℝ) := fun N u => by
    linarith [u.2.2.trans_lt (ht1 N)]
  -- the premise of `bdgQ`
  set Γ : ∀ N, TimeIcc s t N × LoopData (B.L N) (n + 2) → ℝ :=
    fun N p => 2 * (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) * Λ N with hΓ
  set w : ℕ → ℝ → ℝ → ℝ := fun _ u _ => (1 - u)⁻¹ with hw
  have hΓ0 : ∀ N p, 0 ≤ Γ N p := fun N p => by
    have := hApos N p.1; have := hΛ N; simp only [hΓ]; positivity
  have hw0 : ∀ N u v, s N ≤ u → u ≤ v → v ≤ t N → 0 ≤ w N u v := fun N u v _ huv hvt => by
    simp only [hw]; have := ht1 N; exact inv_nonneg.2 (by linarith)
  have hwint : ∀ N (v : ℝ), s N ≤ v → v ≤ t N →
      IntervalIntegrable (fun u => w N u v) MeasureTheory.volume (s N) v := fun N v hsv hvt => by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun u hu => ?_
    rw [Set.uIcc_of_le hsv] at hu
    have := ht1 N
    linarith [hu.2]
  set g : ∀ N, TimeIcc s t N × (TimeIcc s t N × LoopData (B.L N) (n + 2)) → Ω → ℝ :=
    fun N q _ => (B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))⁻¹ with hg
  have hg0 : ∀ N q ω, 0 ≤ g N q ω := fun N q ω => by
    have := hApos N q.2.1; have := h1u N q.1; simp only [hg]; positivity
  have hξ0 : ∀ N (q : TimeIcc s t N × (TimeIcc s t N × LoopData (B.L N) (n + 2))) ω,
      0 ≤ B.scale E N q.2.1 ^ (2 * (n + 2)) * (1 - (q.1 : ℝ)) * I N q ω := fun N q ω => by
    have := hApos N q.2.1; have := h1u N q.1; have := hI0 N q ω
    positivity
  have hm := StochDom.mul hξ0 hg0 (StochDom.refl hg0) hQV
  have hprem : StochDom B.P I (fun N q _ => Γ N q.2 * w N q.1 q.2.1) := by
    refine Step3.stochDom_mono (fun N q _ => mul_nonneg (hΓ0 N q.2)
      (by simp only [hw]; exact (inv_pos.2 (h1u N q.1)).le)) 1 ?_ (StochDom.of_le_left ?_ hm)
    · filter_upwards [hΛ1] with N hN q ω
      simp only [hg, hΓ, hw, one_mul, Pi.mul_apply]
      have := hApos N q.2.1; have := h1u N q.1
      have hpos : 0 ≤ (B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))⁻¹ := by positivity
      calc (B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))⁻¹ * (1 + Λ N)
          ≤ (B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))⁻¹ * (2 * Λ N) :=
            mul_le_mul_of_nonneg_left (by linarith) hpos
        _ = _ := by ring
    · intro N q ω
      simp only [hg, Pi.mul_apply]
      have hA := hApos N q.2.1; have hu := h1u N q.1
      have hAA : (B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * B.scale E N q.2.1 ^ (2 * (n + 2)) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hA.ne', one_pow]
      have huu : (1 - (q.1 : ℝ))⁻¹ * (1 - (q.1 : ℝ)) = 1 := inv_mul_cancel₀ hu.ne'
      apply le_of_eq
      calc I N q ω = ((B.scale E N q.2.1)⁻¹ ^ (2 * (n + 2)) * B.scale E N q.2.1 ^ (2 * (n + 2)))
            * ((1 - (q.1 : ℝ))⁻¹ * (1 - (q.1 : ℝ))) * I N q ω := by rw [hAA, huu]; ring
        _ = _ := by ring
  have hM := hbdg Γ w hΓ0 hw0 hwint hprem
  -- multiply by `(Wℓ_vη_v)^m`
  have hA0 : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) (_ : Ω),
      0 ≤ B.scale E N p.1 ^ (n + 2) := fun N p _ => (pow_pos (hApos N p.1) _).le
  have hM2 := StochDom.mul hM0 hA0 (StochDom.refl hA0) hM
  refine stochDom_trans_det (f := fun N p => B.scale E N p.1 ^ (n + 2)
    * (Γ N p * ∫ u in (s N)..(p.1 : ℝ), w N u p.1) ^ ((1 : ℝ) / 2)) hM2 fun τ hτ => ?_
  have hlogN : ∀ᶠ N : ℕ in atTop, 2 * Real.log N ≤ (N : ℝ) ^ (2 * τ) := by
    filter_upwards [eventually_ge_atTop 1,
      eventually_const_mul_rpow_le (2 / τ) (show τ < 2 * τ by linarith)] with N hN1 hN
    have := log_le_rpow_div_nat N hτ
    have e : 2 * ((N : ℝ) ^ τ / τ) = 2 / τ * (N : ℝ) ^ τ := by ring
    linarith
  filter_upwards [hlogN, flow_crude hE (fun N => (hs0 N).le) hst ht1 hc] with N hN ⟨hLN, hWN, hN1, hu⟩
  intro p
  have hA := hApos N p.1
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
  have hsv : s N ≤ (p.1 : ℝ) := p.1.2.1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  obtain ⟨-, -, hvN⟩ := hu p.1
  have hint : ∫ u in (s N)..(p.1 : ℝ), w N u p.1 = Real.log ((1 - s N) / (1 - (p.1 : ℝ))) := by
    simp only [hw]; exact integral_inv_one_sub_eq hsv hu1
  have h1v : 0 < 1 - (p.1 : ℝ) := by linarith
  have hρ1 : 1 ≤ (1 - s N) / (1 - (p.1 : ℝ)) := by rw [le_div_iff₀ h1v]; linarith
  have hρN : (1 - s N) / (1 - (p.1 : ℝ)) ≤ N := by
    calc (1 - s N) / (1 - (p.1 : ℝ)) ≤ 1 / (1 - (p.1 : ℝ)) :=
          div_le_div_of_nonneg_right (by linarith [hs0 N]) h1v.le
      _ = (1 - (p.1 : ℝ))⁻¹ := one_div _
      _ ≤ N := hvN
  have hlog0 : 0 ≤ Real.log ((1 - s N) / (1 - (p.1 : ℝ))) := Real.log_nonneg hρ1
  have hlogle : Real.log ((1 - s N) / (1 - (p.1 : ℝ))) ≤ Real.log N :=
    Real.log_le_log (by linarith) hρN
  have hΛN := hΛ N
  rw [hint]
  simp only [hΓ]
  -- `A^m (2 A^{-2m} Λ log ρ)^{1/2} = (2 Λ log ρ)^{1/2}`
  have hsq : B.scale E N p.1 ^ (n + 2)
      = (B.scale E N p.1 ^ (2 * (n + 2))) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hA.le]; congr 1; push_cast; ring
  rw [hsq, ← Real.mul_rpow (by positivity) (by positivity)]
  have e1 : B.scale E N p.1 ^ (2 * (n + 2)) * (2 * (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) * Λ N
      * Real.log ((1 - s N) / (1 - (p.1 : ℝ)))) = (2 * Real.log ((1 - s N) / (1 - (p.1 : ℝ)))) * Λ N := by
    have : B.scale E N p.1 ^ (2 * (n + 2)) * (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hA.ne', one_pow]
    calc B.scale E N p.1 ^ (2 * (n + 2)) * (2 * (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) * Λ N
          * Real.log ((1 - s N) / (1 - (p.1 : ℝ))))
        = (B.scale E N p.1 ^ (2 * (n + 2)) * (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)))
          * (2 * Real.log ((1 - s N) / (1 - (p.1 : ℝ)))) * Λ N := by ring
      _ = _ := by rw [this, one_mul]
  rw [e1, Real.mul_rpow (by positivity) hΛN]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hΛN _)
  have h2 : 2 * Real.log ((1 - s N) / (1 - (p.1 : ℝ))) ≤ (N : ℝ) ^ (2 * τ) := by linarith
  calc (2 * Real.log ((1 - s N) / (1 - (p.1 : ℝ)))) ^ ((1 : ℝ) / 2)
      ≤ ((N : ℝ) ^ (2 * τ)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    _ = (N : ℝ) ^ τ := by rw [← Real.rpow_mul (Nat.cast_nonneg N)]; congr 1; ring

/-- The power counting of the Case-1 quadratic variation (5.85)–(5.86). -/
theorem QV1_scalar {m : ℕ} {Av Au r ρ Nr K Λ im u x e' c lg : ℝ} (hc : 0 ≤ c)
    (hr : Av * r = Au) (hAv1 : 1 ≤ Av) (hAvN : Av ≤ Nr) (hAu1 : 1 ≤ Au) (_hr0 : 0 ≤ r)
    (hρ0 : 0 ≤ ρ) (hρN : ρ ≤ Nr) (hK1 : 1 ≤ K) (hKN : K ≤ Nr) (hu : 0 < 1 - u) (hu1 : 1 - u ≤ 1)
    (him : 0 < im) (hΛ : 0 ≤ Λ) (hx : 0 ≤ x) (he' : 0 ≤ e') (hlg : 0 ≤ lg) :
    Av ^ (2 * m) * (1 - u) * (c * K ^ (2 * m) * r ^ (2 * m)
        * (K * (Au⁻¹ ^ (2 * m) * ((1 - u) * im)⁻¹ * Λ)) + ρ ^ (2 * m) * (K * x))
      ≤ (c / im + 1) * K ^ (2 * m + 1) * (1 + lg) * (1 + Λ)
        + (c / im + 1) * Nr ^ (4 * m + 1) * (x + e' * (1 + Λ)) := by
  have hN1 : 1 ≤ Nr := hK1.trans hKN
  have hN0 : 0 ≤ Nr := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hAu0 : 0 < Au := by linarith
  have hcim : 0 ≤ c / im := by positivity
  have h1 : Av ^ (2 * m) * (1 - u) * (c * K ^ (2 * m) * r ^ (2 * m)
      * (K * (Au⁻¹ ^ (2 * m) * ((1 - u) * im)⁻¹ * Λ))) = c / im * K ^ (2 * m + 1) * Λ := by
    have hcancel : Av ^ (2 * m) * r ^ (2 * m) * Au⁻¹ ^ (2 * m) = 1 := by
      rw [← mul_pow, hr, ← mul_pow, mul_inv_cancel₀ hAu0.ne', one_pow]
    have hu' : (1 - u) * ((1 - u) * im)⁻¹ = im⁻¹ := by field_simp
    calc Av ^ (2 * m) * (1 - u) * (c * K ^ (2 * m) * r ^ (2 * m)
          * (K * (Au⁻¹ ^ (2 * m) * ((1 - u) * im)⁻¹ * Λ)))
        = c * (K ^ (2 * m) * K) * Λ * (Av ^ (2 * m) * r ^ (2 * m) * Au⁻¹ ^ (2 * m))
          * ((1 - u) * ((1 - u) * im)⁻¹) := by ring
      _ = c / im * K ^ (2 * m + 1) * Λ := by rw [hcancel, hu', ← pow_succ]; ring
  have h2 : Av ^ (2 * m) * (1 - u) * (ρ ^ (2 * m) * (K * x)) ≤ Nr ^ (4 * m + 1) * x := by
    calc Av ^ (2 * m) * (1 - u) * (ρ ^ (2 * m) * (K * x)) ≤ Nr ^ (2 * m) * 1 * (Nr ^ (2 * m) * (Nr * x)) := by
          gcongr
      _ = Nr ^ (4 * m + 1) * x := by ring
  have h3 : c / im * K ^ (2 * m + 1) * Λ ≤ (c / im + 1) * K ^ (2 * m + 1) * (1 + lg) * (1 + Λ) := by
    have hΛl : Λ ≤ (1 + lg) * (1 + Λ) := by
      have e2 : (1 + lg) * (1 + Λ) = 1 + Λ + lg + lg * Λ := by ring
      rw [e2]; nlinarith [mul_nonneg hlg hΛ]
    have : c / im * K ^ (2 * m + 1) * Λ ≤ (c / im + 1) * K ^ (2 * m + 1) * ((1 + lg) * (1 + Λ)) := by
      gcongr; linarith
    linarith
  have h4 : Nr ^ (4 * m + 1) * x ≤ (c / im + 1) * Nr ^ (4 * m + 1) * (x + e' * (1 + Λ)) := by
    have hx' : x ≤ x + e' * (1 + Λ) := le_add_of_nonneg_right (by positivity)
    calc Nr ^ (4 * m + 1) * x = 1 * Nr ^ (4 * m + 1) * x := by ring
      _ ≤ (c / im + 1) * Nr ^ (4 * m + 1) * (x + e' * (1 + Λ)) := by gcongr; linarith
  rw [mul_add, h1]
  linarith

set_option maxHeartbeats 1000000 in
/-- **(5.86)**: the Case-1 quadratic variation integrand is `≺ 1 + Λ` (after normalization). -/
theorem QV1_stochDom {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 < s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ}
    (H : Hierarchy X E s t n) (h510 : Lemma510 X E s t H) {Λ : ℕ → ℝ} (hΛ : ∀ N, 0 ≤ Λ N)
    (hEE : StochDom B.P
      (fun N (p : TimeIcc s t N × ((Fin (n + 2) → Bool) × LoopArg (B.L N) ((n + 2) + (n + 2)))) ω =>
        ‖H.EE N p.1 ω p.2.1 p.2.2‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (2 * (n + 2)) * (etaT E p.1)⁻¹ * Λ N)) :
    StochDom B.P (fun N (q : TimeIcc s t N × (TimeIcc s t N × LoopData (B.L N) (n + 2))) ω =>
      B.scale E N q.2.1 ^ (2 * (n + 2)) * (1 - (q.1 : ℝ))
        * (if (q.1 : ℝ) ≤ q.2.1 ∧ NonAlt q.2.2.1 then
          ‖Uker (B.L N) (xi2 E q.2.2.1) ((q.1 : ℝ) : ℂ) ((q.2.1 : ℝ) : ℂ)
            (H.EE N q.1 ω q.2.2.1) (Fin.append q.2.2.2 q.2.2.2)‖ else 0))
      (fun N _ _ => 1 + Λ N) := by
  have hE : |E| < 2 := by linarith
  refine stochDom_of_logBound hΛ (c₁ := cZero / 4) (by have := cZero_pos; positivity)
    (2 * (n + 2) + 1) (4 * (n + 2) + 1) fun τ₁ hτ₁ hτ₁1 D hD => ?_
  have him : 0 < (mE E).im := mE_im_pos hE
  obtain ⟨cS, hcS⟩ : ∃ cS : ℝ, cS = cKerShort ((n + 2) + (n + 2)) √κ := ⟨_, rfl⟩
  have hcS0 : 0 ≤ cS := hcS ▸ cKerShort_nonneg _ (Real.sqrt_pos.2 hκ0)
  refine ⟨cS / (mE E).im + 1, by positivity, _, (good_of_stochDom hEE hτ₁).inter
    (good_of_stochDom (h510.EE_decay τ₁ hτ₁ D hD) hτ₁), ?_⟩
  filter_upwards [flow_crude hE (fun N => (hs0 N).le) hst ht1 hc] with N ⟨hLN, hWN, hN1, hu⟩
  intro ω ⟨hω1, hω2⟩ q
  simp only [Set.mem_ofPred_eq] at hω1 hω2
  obtain ⟨uu, vv, σ, a⟩ := q
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hΛN := hΛ N
  have hlogN := Real.log_nonneg hN1'
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (N : ℝ) ^ τ₁ := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := hK ▸ Real.one_le_rpow hN1' hτ₁.le
  have hKN : K ≤ N := hK ▸ rpow_le_self_of_le_one hN1' hτ₁1
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (N : ℝ) ^ (-D) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ Real.rpow_nonneg hN0.le _
  have hu0 : 0 ≤ (uu : ℝ) := ((hs0 N).trans_le uu.2.1).le
  have hu1 : (uu : ℝ) < 1 := uu.2.2.trans_lt (ht1 N)
  have h1u : 0 < 1 - (uu : ℝ) := by linarith
  have htarget0 : 0 ≤ (cS / (mE E).im + 1) * (N : ℝ) ^ (((2 * (n + 2) + 1 : ℕ) : ℝ) * τ₁)
      * (1 + Real.log N) * (1 + Λ N) + (cS / (mE E).im + 1) * (N : ℝ) ^ (4 * (n + 2) + 1)
      * ((N : ℝ) ^ (-D) + exp (-(cZero / 4 * (N : ℝ) ^ τ₁)) * (1 + Λ N)) := by positivity
  dsimp only
  split_ifs with hh
  swap
  · rw [mul_zero]; exact htarget0
  obtain ⟨huv, k, hk⟩ := hh
  rw [← hK, ← hx]
  have hv0 : 0 < (vv : ℝ) := (hs0 N).trans_le vv.2.1
  have hv1 : (vv : ℝ) < 1 := vv.2.2.trans_lt (ht1 N)
  have h1v : 0 < 1 - (vv : ℝ) := by linarith
  obtain ⟨hAu1, hAuN, huN⟩ := hu uu
  obtain ⟨hAv1, hAvN, hvN⟩ := hu vv
  have hL3 := B.three_le_L N
  have hℓu0 := ellHat_real_pos' (B.L N) hL3 hu0 hu1
  have hℓv0 := ellHat_real_pos' (B.L N) hL3 hv0.le hv1
  have hη := etaT_pos hE hu1
  have hAu0 : 0 < B.scale E N uu := by linarith
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = K * ((B.scale E N uu)⁻¹ ^ (2 * (n + 2)) * (etaT E uu)⁻¹ * Λ N) :=
    ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hBe : ∀ c, ‖H.EE N uu ω σ c‖ ≤ e := fun c => by rw [he, hK]; exact hω1 (uu, (σ, c))
  have hBd : FastDecay (B.L N) (ellHat (B.L N) ((uu : ℝ) : ℂ) * K) (K * x) (H.EE N uu ω σ) :=
    fastDecay_of_farInd fun c => by rw [hK, hx]; exact hω2 (uu, (σ, c))
  have hκt : √κ ≤ ‖1 - ((vv : ℝ) : ℂ) * xi2 E σ (Fin.castAdd (n + 2) k)‖ := by
    rw [xi2, Fin.append_left]
    exact sqrt_le_norm_one_sub_xiOf hκ0 hκ1 hEκ hv0.le hv1.le hk
  have hker := norm_Uker_fastDecay_le_short (B.L N) hL3 hu0 huv hv1 (ξ := xi2 E σ)
    (norm_xi2_le hE σ) (Real.sqrt_pos.2 hκ0) (Fin.castAdd (n + 2) k) hκt hK1 he0
    (mul_nonneg hK0 hx0) hBe hBd (Fin.append a a)
  rw [← hcS] at hker
  have hexp2 : ∀ (y : ℝ), y ^ ((n + 2) + (n + 2)) = y ^ (2 * (n + 2)) := fun y => by
    rw [show (n + 2) + (n + 2) = 2 * (n + 2) by ring]
  rw [hexp2, hexp2, hexp2] at hker
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 - (uu : ℝ)) * ellHat (B.L N) ((uu : ℝ) : ℂ)
      / ((1 - (vv : ℝ)) * ellHat (B.L N) ((vv : ℝ) : ℂ)) := ⟨_, rfl⟩
  rw [← hr] at hker
  have hAvr : B.scale E N vv * r = B.scale E N uu := by
    rw [hr, Band.scale_eq, Band.scale_eq]; field_simp
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hρ0 : 0 ≤ (1 - (uu : ℝ)) / (1 - (vv : ℝ)) := div_nonneg h1u.le h1v.le
  have hρN : (1 - (uu : ℝ)) / (1 - (vv : ℝ)) ≤ N := by
    calc (1 - (uu : ℝ)) / (1 - (vv : ℝ)) ≤ 1 / (1 - (vv : ℝ)) :=
          div_le_div_of_nonneg_right (by linarith) h1v.le
      _ = (1 - (vv : ℝ))⁻¹ := one_div _
      _ ≤ N := hvN
  have hetaT : etaT E uu = (1 - (uu : ℝ)) * (mE E).im := rfl
  rw [he, hetaT] at hker
  have hfin := QV1_scalar (m := n + 2) (Av := B.scale E N vv) (Au := B.scale E N uu) (r := r)
    (ρ := (1 - (uu : ℝ)) / (1 - (vv : ℝ))) (Nr := N) (K := K) (Λ := Λ N) (im := (mE E).im)
    (u := uu) (x := x) (e' := exp (-(cZero / 4 * K))) (c := cS) (lg := Real.log N) hcS0 hAvr hAv1
    hAvN hAu1 hr0 hρ0 hρN hK1 hKN h1u (by linarith) him hΛN hx0 (exp_pos _).le hlogN
  have hpre : 0 ≤ B.scale E N vv ^ (2 * (n + 2)) * (1 - (uu : ℝ)) := by positivity
  calc B.scale E N vv ^ (2 * (n + 2)) * (1 - (uu : ℝ))
        * ‖Uker (B.L N) (xi2 E σ) ((uu : ℝ) : ℂ) ((vv : ℝ) : ℂ) (H.EE N uu ω σ) (Fin.append a a)‖
      ≤ B.scale E N vv ^ (2 * (n + 2)) * (1 - (uu : ℝ)) * (cS * K ^ (2 * (n + 2)) * r ^ (2 * (n + 2))
          * (K * ((B.scale E N uu)⁻¹ ^ (2 * (n + 2)) * ((1 - (uu : ℝ)) * (mE E).im)⁻¹ * Λ N))
          + ((1 - (uu : ℝ)) / (1 - (vv : ℝ))) ^ (2 * (n + 2)) * (K * x)) :=
        mul_le_mul_of_nonneg_left hker hpre
    _ ≤ _ := hfin
    _ = _ := by
        rw [hK, show ((2 * (n + 2) + 1 : ℕ) : ℝ) * τ₁ = τ₁ * ((2 * (n + 2) + 1 : ℕ) : ℝ) by ring,
          ← rpow_pow_eq]

/-- **The Case-1 martingale term**: `(Wℓ_vη_v)^m |∫_s^v U_{u,v,σ} ∘ dE^{(M)}_u| ≺ Λ^{1/2}` for
non-alternating `σ` ((5.85), (5.86), BDG). -/
theorem term1M {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 < s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ}
    (H : Hierarchy X E s t n) (h510 : Lemma510 X E s t H) {Λ : ℕ → ℝ} (hΛ : ∀ N, 0 ≤ Λ N)
    (hΛ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Λ N)
    (hY : StochDom B.P (Step3.flowXiL X E s t (2 * (n + 2) + 2)) (fun N _ _ => Λ N)) :
    StochDom B.P (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      B.scale E N p.1 ^ (n + 2) * (if NonAlt p.2.1 then ‖H.mart N p.1 ω p.2.1 p.2.2‖ else 0))
      (fun N _ _ => Λ N ^ ((1 : ℝ) / 2)) := by
  have hE : |E| < 2 := by linarith
  refine mart_of_QV hE hs0 hst ht1 hc hΛ hΛ1
    (fun N q ω => if (q.1 : ℝ) ≤ q.2.1 ∧ NonAlt q.2.2.1 then
      ‖Uker (B.L N) (xi2 E q.2.2.1) ((q.1 : ℝ) : ℂ) ((q.2.1 : ℝ) : ℂ)
        (H.EE N q.1 ω q.2.2.1) (Fin.append q.2.2.2 q.2.2.2)‖ else 0)
    (fun N q ω => by split_ifs <;> positivity)
    (fun N p ω => if NonAlt p.2.1 then ‖H.mart N p.1 ω p.2.1 p.2.2‖ else 0)
    (fun N p ω => by split_ifs <;> positivity)
    (fun Γ w hΓ hw hint hprem => H.bdg NonAlt Γ w hΓ hw hint hprem)
    (QV1_stochDom X hκ0 hκ1 hEκ hs0 hst ht1 hc H h510 hΛ (EE_stochDom X hE hs0 ht1 H h510 hY))

set_option maxHeartbeats 1000000 in
/-- **The Case-1 initial term**: `(Wℓ_vη_v)^m |U_{s,v,σ} ∘ (L-K)_s| ≺ 1` for non-alternating `σ`. -/
theorem term1I {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 < s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {n : ℕ}
    (hdec : LKDecay X E s t) {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hLmK : StochDom B.P (fun N (w : LoopData (B.L N) (n + 2)) ω => X.lkErr E N (s N) ω w.idx)
      (fun N _ _ => (B.scale E N (s N))⁻¹ ^ (n + 2))) :
    StochDom B.P (fun N (pp : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
      if NonAlt pp.2.1 then B.scale E N pp.1 ^ (n + 2) * ‖Uker (B.L N) (xiOf (mSigma E) pp.2.1)
        ((s N : ℝ) : ℂ) ((pp.1 : ℝ) : ℂ) (lkT X E N (s N) ω pp.2.1) pp.2.2‖ else 0)
      (fun N _ _ => 1 + Φ N) := by
  have hE : |E| < 2 := by linarith
  refine stochDom_of_logBound hΦ (c₁ := cZero / 4) (by have := cZero_pos; positivity)
    (n + 3) (2 * (n + 2) + 1) fun τ₁ hτ₁ hτ₁1 D hD => ?_
  have him : 0 < (mE E).im := mE_im_pos hE
  obtain ⟨cS, hcS⟩ : ∃ cS : ℝ, cS = cKerShort (n + 2) √κ := ⟨_, rfl⟩
  have hcS0 : 0 ≤ cS := hcS ▸ cKerShort_nonneg _ (Real.sqrt_pos.2 hκ0)
  refine ⟨cS + 1, by positivity, _, (good_of_stochDom hLmK hτ₁).inter
    (good_of_stochDom (hdec (n + 2) (by omega) τ₁ hτ₁ D hD) hτ₁), ?_⟩
  filter_upwards [flow_crude hE (fun N => (hs0 N).le) hst ht1 hc] with N ⟨hLN, hWN, hN1, hu⟩
  intro ω ⟨hω1, hω2⟩ pp
  simp only [Set.mem_ofPred_eq] at hω1 hω2
  obtain ⟨vv, σ, a⟩ := pp
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hΦN := hΦ N
  have hlogN := Real.log_nonneg hN1'
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (N : ℝ) ^ τ₁ := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := hK ▸ Real.one_le_rpow hN1' hτ₁.le
  have hKN : K ≤ N := hK ▸ rpow_le_self_of_le_one hN1' hτ₁1
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (N : ℝ) ^ (-D) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ Real.rpow_nonneg hN0.le _
  have htarget0 : 0 ≤ (cS + 1) * (N : ℝ) ^ (((n + 3 : ℕ) : ℝ) * τ₁) * (1 + Real.log N)
      * (1 + Φ N) + (cS + 1) * (N : ℝ) ^ (2 * (n + 2) + 1)
      * ((N : ℝ) ^ (-D) + exp (-(cZero / 4 * (N : ℝ) ^ τ₁)) * (1 + Φ N)) := by positivity
  dsimp only
  split_ifs with hna
  swap
  · exact htarget0
  obtain ⟨k, hk⟩ := hna
  rw [← hK, ← hx]
  have hs0' : 0 ≤ s N := (hs0 N).le
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hv1 : (vv : ℝ) < 1 := vv.2.2.trans_lt (ht1 N)
  have hsv : s N ≤ (vv : ℝ) := vv.2.1
  set ss : TimeIcc s t N := ⟨s N, le_rfl, hst N⟩
  obtain ⟨hAs1, -, -⟩ := hu ss
  obtain ⟨hAv1, hAvN, hvN⟩ := hu vv
  have hL3 := B.three_le_L N
  set κA := (B.W N : ℝ) * (mE E).im with hκA
  have hκA0 : 0 < κA := mul_pos (by exact_mod_cast B.W_pos N) him
  have hGM : ∀ b, ‖lkT X E N (s N) ω σ b‖
      ≤ (κA * ((1 - s N) * ellHat (B.L N) ((s N : ℝ) : ℂ)))⁻¹ ^ (n + 2) * K + 0 := by
    intro b
    rw [add_zero, norm_lkT]
    have h := hω1 (σ, b)
    rw [← hK, Band.scale_eq] at h
    linarith [h, show K * (κA * ((1 - s N) * ellHat (B.L N) ((s N : ℝ) : ℂ)))⁻¹ ^ (n + 2)
      = (κA * ((1 - s N) * ellHat (B.L N) ((s N : ℝ) : ℂ)))⁻¹ ^ (n + 2) * K by ring]
  have hGd : FastDecay (B.L N) (ellHat (B.L N) ((s N : ℝ) : ℂ) * K) (K * x) (lkT X E N (s N) ω σ) :=
    fastDecay_of_farInd fun b => by rw [hK, hx]; exact hω2 (ss, (σ, b))
  have key := norm_Uker_short_scale_le (B.L N) hL3 hκ0 hκ1 hEκ hk hs0' le_rfl hsv hv1 hκA0 hK1
    hK0 le_rfl (by positivity) hGM hGd a
  rw [← Band.scale_eq B E N vv, ← hcS] at key
  have h1v : 0 < 1 - (vv : ℝ) := by linarith
  have hρN : (1 - s N) / (1 - (vv : ℝ)) ≤ N := by
    calc (1 - s N) / (1 - (vv : ℝ)) ≤ 1 / (1 - (vv : ℝ)) :=
          div_le_div_of_nonneg_right (by linarith) h1v.le
      _ = (1 - (vv : ℝ))⁻¹ := one_div _
      _ ≤ N := hvN
  have hρ0 : 0 ≤ (1 - s N) / (1 - (vv : ℝ)) := div_nonneg (by linarith) h1v.le
  have hAv0 : 0 < B.scale E N vv := by linarith
  have hAvn : B.scale E N vv ^ (n + 2) * (B.scale E N vv)⁻¹ ^ (n + 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hAv0.ne', one_pow]
  have hpre : 0 ≤ B.scale E N vv ^ (n + 2) := by positivity
  have hmain : cS * K ^ (n + 2) * K ≤ (cS + 1) * K ^ (n + 3) * (1 + Real.log N) * (1 + Φ N) := by
    have : 1 ≤ (1 + Real.log N) * (1 + Φ N) := by nlinarith
    calc cS * K ^ (n + 2) * K = cS * K ^ (n + 3) * 1 := by ring
      _ ≤ (cS + 1) * K ^ (n + 3) * ((1 + Real.log N) * (1 + Φ N)) := by gcongr; linarith
      _ = _ := by ring
  have herr : B.scale E N vv ^ (n + 2) * (cS * K ^ (n + 2) * ((1 - s N) / (1 - (vv : ℝ))) ^ (n + 2) * 0
      + ((1 - s N) / (1 - (vv : ℝ))) ^ (n + 2) * (K * x))
      ≤ (cS + 1) * (N : ℝ) ^ (2 * (n + 2) + 1) * (x + exp (-(cZero / 4 * K)) * (1 + Φ N)) := by
    have h3 : B.scale E N vv ^ (n + 2) * (cS * K ^ (n + 2) * ((1 - s N) / (1 - (vv : ℝ))) ^ (n + 2) * 0
        + ((1 - s N) / (1 - (vv : ℝ))) ^ (n + 2) * (K * x)) ≤ (N : ℝ) ^ (n + 2) * ((N : ℝ) ^ (n + 2) * (N * x)) := by
      rw [mul_zero, zero_add]; gcongr
    have hx' : x ≤ x + exp (-(cZero / 4 * K)) * (1 + Φ N) := le_add_of_nonneg_right (by positivity)
    have h4 : (N : ℝ) ^ (n + 2) * ((N : ℝ) ^ (n + 2) * (N * x)) = 1 * (N : ℝ) ^ (2 * (n + 2) + 1) * x := by ring
    rw [h4] at h3
    refine h3.trans ?_
    gcongr; linarith
  calc B.scale E N vv ^ (n + 2) * ‖Uker (B.L N) (xiOf (mSigma E) σ) ((s N : ℝ) : ℂ) ((vv : ℝ) : ℂ)
        (lkT X E N (s N) ω σ) a‖
      ≤ B.scale E N vv ^ (n + 2) * (cS * K ^ (n + 2) * (B.scale E N vv)⁻¹ ^ (n + 2) * K
          + (cS * K ^ (n + 2) * ((1 - s N) / (1 - (vv : ℝ))) ^ (n + 2) * 0
            + ((1 - s N) / (1 - (vv : ℝ))) ^ (n + 2) * (K * x))) :=
        mul_le_mul_of_nonneg_left key hpre
    _ = (B.scale E N vv ^ (n + 2) * (B.scale E N vv)⁻¹ ^ (n + 2)) * (cS * K ^ (n + 2) * K)
        + B.scale E N vv ^ (n + 2) * (cS * K ^ (n + 2) * ((1 - s N) / (1 - (vv : ℝ))) ^ (n + 2) * 0
            + ((1 - s N) / (1 - (vv : ℝ))) ^ (n + 2) * (K * x)) := by ring
    _ ≤ (cS + 1) * K ^ (n + 3) * (1 + Real.log N) * (1 + Φ N)
        + (cS + 1) * (N : ℝ) ^ (2 * (n + 2) + 1) * (x + exp (-(cZero / 4 * K)) * (1 + Φ N)) := by
        rw [hAvn, one_mul]; exact add_le_add hmain herr
    _ = _ := by
        rw [hK, show ((n + 3 : ℕ) : ℝ) * τ₁ = τ₁ * ((n + 3 : ℕ) : ℝ) by ring, ← rpow_pow_eq]

end TermsShort

/-! ### Assembly: Lemma 5.14 (5.92) for the flow -/

section Assembly

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- `L - K` is invariant under rotating a `2`-loop: `(L-K)_{(σ₁,σ₂),(a₁,a₂)} = (L-K)_{(σ₂,σ₁),(a₂,a₁)}`. -/
theorem lkT_swap2 (hE : |E| < 2) {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) :
    lkT X E N u ω σ a = lkT X E N u ω (fun i => σ (i + 1)) (fun i => a (i + 1)) := by
  have hidx : LoopData.idx (σ, a) = (⟨[σ 0, σ 1], [a 0, a 1]⟩ : LoopIdx (ZMod (B.L N))) := by
    simp [LoopData.idx, List.ofFn_succ]
  have hidx' : LoopData.idx ((fun i => σ (i + 1)), (fun i => a (i + 1)))
      = (⟨[σ 1, σ 0], [a 1, a 0]⟩ : LoopIdx (ZMod (B.L N))) := by
    simp [LoopData.idx, List.ofFn_succ]
  unfold lkT
  rw [hidx, hidx']
  congr 1
  · -- the `G`-loop
    simp only [Sample.Lval]
    exact gloop_rotate (σ 0) (a 0) (σ := [σ 1]) (a := [a 1]) rfl
  · -- the primitive loop
    simp only [Band.Kval]
    have hL3 := B.three_le_L N
    have h := Kgen_rot hL3 (B.W N) hE hu0 hu1 (⟨[σ 0, σ 1], [a 0, a 1]⟩ : LoopIdx (ZMod (B.L N)))
      (by simp [LoopIdx.WF]) (by simp [LoopIdx.length])
    rw [← h]
    rfl

/-- The charges that are neither non-alternating nor `QGood`: only `(-,+)` at length `2`. -/
theorem eq_zero_of_not_nonAlt_not_qGood {n : ℕ} {σ : Fin (n + 2) → Bool} (h1 : ¬ NonAlt σ)
    (h2 : ¬ QGood σ) : n = 0 := by
  unfold NonAlt at h1
  unfold QGood at h2
  push Not at h1 h2
  rcases n with _ | k
  · rfl
  · exfalso
    have hflip : ∀ j : Fin (k + 1 + 2), σ (j + 1) = !σ j := by
      intro j
      have := h1 j
      cases h : σ j <;> cases h' : σ (j + 1) <;> simp_all
    have hv1 : ((1 : Fin (k + 1 + 2)) : ℕ) = 1 := Fin.val_one _
    have hne1 : (1 : Fin (k + 1 + 2)) ≠ 0 := by
      intro h; have := congrArg Fin.val h; rw [hv1] at this; simp at this
    have hne2 : (1 + 1 : Fin (k + 1 + 2)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      rw [Fin.val_add, hv1, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
      omega
    have ht1 : σ 1 = true := by
      by_contra hc
      simp only [Bool.not_eq_true] at hc
      exact h2 1 hne1 hc (by rw [hflip, hc]; rfl)
    have ht2 : σ (1 + 1) = true := by
      by_contra hc
      simp only [Bool.not_eq_true] at hc
      exact h2 (1 + 1) hne2 hc (by rw [hflip, hc]; rfl)
    rw [hflip, ht1] at ht2
    exact absurd ht2 (by decide)

theorem qGood_swap2 : ∀ σ : Fin 2 → Bool, ¬ NonAlt σ → ¬ QGood σ →
    QGood (fun i => σ (i + 1)) := by
  unfold NonAlt QGood
  decide

/-- From a bound on every `(W ℓ_u η_u)^m |(L-K)_{u,σ,a}|` to a bound on `Ξ^{(L-K)}_{u,m}` (5.76). -/
theorem stochDom_xiLK_of (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1) {m : ℕ}
    {ζ : ∀ N, TimeIcc s t N → ℝ}
    (h : StochDom B.P (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω =>
      B.scale E N p.1 ^ m * ‖lkT X E N p.1 ω p.2.1 p.2.2‖) (fun N p _ => ζ N p.1)) :
    StochDom B.P (Step3.flowXiLK X E s t m) (fun N u _ => ζ N u) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine (measure_mono fun ω hω => ?_).trans hN
  obtain ⟨u, hu⟩ := hω
  have hA : 0 < B.scale E N u ^ m :=
    pow_pos (B.scale_pos hE N ((hs0 N).trans_le u.2.1) (u.2.2.trans_lt (ht1 N))) m
  have hu' : (N : ℝ) ^ τ * ζ N u / B.scale E N u ^ m < X.lkMax E N u ω m := by
    rw [div_lt_iff₀ hA]
    have : Step3.flowXiLK X E s t m N u ω = X.lkMax E N u ω m * B.scale E N u ^ m := rfl
    linarith
  obtain ⟨ld, hld⟩ := exists_lt_of_lt_ciSup hu'
  refine ⟨(u, ld), ?_⟩
  show (N : ℝ) ^ τ * ζ N u < B.scale E N u ^ m * ‖lkT X E N u ω ld.1 ld.2‖
  rw [div_lt_iff₀ hA] at hld
  rw [norm_lkT]
  linarith

/-- **(5.101) + (5.91)**, pointwise, for `QGood` charges: `(W ℓ_v η_v)^m |(L-K)_{v,σ,a}|` is at
most the sum of the six terms of (5.94). -/
theorem bound_qGood (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1) {n : ℕ}
    (H : Hierarchy X E s t n) {N : ℕ} (ω : Ω) (v : TimeIcc s t N)
    {σ : Fin (n + 2) → Bool} (hq : QGood σ) (a : LoopArg (B.L N) (n + 2)) :
    B.scale E N v ^ (n + 2) * ‖lkT X E N v ω σ a‖
      ≤ (if QGood σ then B.scale E N v ^ (n + 2)
          * (‖Psum (B.L N) (lkT X E N v ω σ) (a 0)‖ * ‖vartheta (B.L N) ((v : ℝ) : ℂ) a‖) else 0)
        + B.scale E N v ^ (n + 2) * ‖Uker (B.L N) (xiOf (mSigma E) σ) ((s N : ℝ) : ℂ)
            ((v : ℝ) : ℂ) (Qop (B.L N) ((s N : ℝ) : ℂ) (lkT X E N (s N) ω σ)) a‖
        + B.scale E N v ^ (n + 2) * ‖∫ u in (s N)..(v : ℝ),
            Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) ((v : ℝ) : ℂ)
              (Qop (B.L N) (u : ℂ) (H.F N u ω σ)) a‖
        + B.scale E N v ^ (n + 2) * ‖∫ u in (s N)..(v : ℝ),
            Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) ((v : ℝ) : ℂ) (commTerm X E N u ω σ) a‖
        + B.scale E N v ^ (n + 2) * ‖∫ u in (s N)..(v : ℝ),
            Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) ((v : ℝ) : ℂ) (dotTerm X E N u ω σ) a‖
        + B.scale E N v ^ (n + 2) * ‖H.martQ N v ω σ a‖ := by
  have hA : 0 ≤ B.scale E N v ^ (n + 2) :=
    (pow_pos (B.scale_pos hE N ((hs0 N).trans_le v.2.1) (v.2.2.trans_lt (ht1 N))) _).le
  have h101 := norm_le_norm_Qop_add (B.L N) ((v : ℝ) : ℂ) (lkT X E N v ω σ) a
  rw [H.duhamelQ N ω σ v v.2.1 v.2.2 a] at h101
  simp only [commTerm, dotTerm, hq, ite_true]
  set I1 := Uker (B.L N) (xiOf (mSigma E) σ) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
    (Qop (B.L N) ((s N : ℝ) : ℂ) (lkT X E N (s N) ω σ)) a
  set I2 := ∫ u in (s N)..(v : ℝ), Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) ((v : ℝ) : ℂ)
    (Qop (B.L N) (u : ℂ) (H.F N u ω σ)) a
  set I3 := ∫ u in (s N)..(v : ℝ), Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) ((v : ℝ) : ℂ)
    (commS (B.L N) (xiOf (mSigma E) σ) (u : ℂ) (lkT X E N u ω σ)) a
  set I4 := ∫ u in (s N)..(v : ℝ), Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) ((v : ℝ) : ℂ)
    (fun b => Psum (B.L N) (lkT X E N u ω σ) (b 0) * varthetaDot (B.L N) u b) a
  set M := H.martQ N v ω σ a
  set P := ‖Psum (B.L N) (lkT X E N v ω σ) (a 0)‖ * ‖vartheta (B.L N) ((v : ℝ) : ℂ) a‖
  have htri : ‖I1 + I2 + M + I3 - I4‖ ≤ ‖I1‖ + ‖I2‖ + ‖M‖ + ‖I3‖ + ‖I4‖ := by
    refine (norm_sub_le _ _).trans ?_
    have := norm_add_le (I1 + I2 + M) I3
    have := norm_add_le (I1 + I2) M
    have := norm_add_le I1 I2
    linarith
  have h2 : ‖lkT X E N v ω σ a‖ ≤ P + ‖I1‖ + ‖I2‖ + ‖I3‖ + ‖I4‖ + ‖M‖ := by linarith
  have := mul_le_mul_of_nonneg_left h2 hA
  have e : B.scale E N v ^ (n + 2) * (P + ‖I1‖ + ‖I2‖ + ‖I3‖ + ‖I4‖ + ‖M‖)
      = B.scale E N v ^ (n + 2) * P + B.scale E N v ^ (n + 2) * ‖I1‖
        + B.scale E N v ^ (n + 2) * ‖I2‖ + B.scale E N v ^ (n + 2) * ‖I3‖
        + B.scale E N v ^ (n + 2) * ‖I4‖ + B.scale E N v ^ (n + 2) * ‖M‖ := by ring
  linarith

/-- **(5.20)**, pointwise, for non-alternating charges (Lemma 5.11). -/
theorem bound_nonAlt (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1) {n : ℕ}
    (H : Hierarchy X E s t n) {N : ℕ} (ω : Ω) (v : TimeIcc s t N)
    {σ : Fin (n + 2) → Bool} (hna : NonAlt σ) (a : LoopArg (B.L N) (n + 2)) :
    B.scale E N v ^ (n + 2) * ‖lkT X E N v ω σ a‖
      ≤ (if NonAlt σ then B.scale E N v ^ (n + 2) * ‖Uker (B.L N) (xiOf (mSigma E) σ)
          ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ) (lkT X E N (s N) ω σ) a‖ else 0)
        + (if NonAlt σ then B.scale E N v ^ (n + 2) * ‖∫ u in (s N)..(v : ℝ),
          Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) ((v : ℝ) : ℂ) (H.F N u ω σ) a‖ else 0)
        + B.scale E N v ^ (n + 2) * (if NonAlt σ then ‖H.mart N v ω σ a‖ else 0) := by
  have hA : 0 ≤ B.scale E N v ^ (n + 2) :=
    (pow_pos (B.scale_pos hE N ((hs0 N).trans_le v.2.1) (v.2.2.trans_lt (ht1 N))) _).le
  simp only [hna, ite_true]
  rw [H.duhamel N ω σ v v.2.1 v.2.2 a]
  have := norm_add_le (Uker (B.L N) (xiOf (mSigma E) σ) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
    (lkT X E N (s N) ω σ) a + ∫ u in (s N)..(v : ℝ),
      Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) ((v : ℝ) : ℂ) (H.F N u ω σ) a) (H.mart N v ω σ a)
  have := norm_add_le (Uker (B.L N) (xiOf (mSigma E) σ) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
    (lkT X E N (s N) ω σ) a) (∫ u in (s N)..(v : ℝ),
      Uker (B.L N) (xiOf (mSigma E) σ) (u : ℂ) ((v : ℝ) : ℂ) (H.F N u ω σ) a)
  rw [← mul_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (by linarith) hA

set_option maxHeartbeats 4000000 in
/-- **Lemma 5.14 (5.92) for the flow**, in the form `RBM.Step3.Lemma514` used by Step 3
(`RBM.Step3.hyp_flow`, `RBM.Step3.flow_sharpLoop`) and Steps 4–5, for every loop length
`n ≥ 2`.

Inputs: the bulk `|E| ≤ 2 - κ`, the times `0 < s ≤ t < 1` with (2.72); the assumption (2.68) of
Theorem 2.21 at the time `s` (`hLmK`, the field `RBM.BoundsCore.LmK`); the random-layer interface
`H n` ((5.20), (5.91), BDG with (5.85)/(5.103)); the placeholders for T59 — Lemma 5.10 (5.77)
(`h510`) and Lemma 5.9 (5.75) (`hdec`); and Ward's identity for the slot sums (`hW`, (5.96)). -/
theorem lemma514_flow {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hLmK : ∀ m : ℕ, 1 ≤ m → StochDom B.P
      (fun N (w : LoopData (B.L N) m) ω => X.lkErr E N (s N) ω w.idx)
      (fun N _ _ => (B.scale E N (s N))⁻¹ ^ m))
    (H : ∀ n, Hierarchy X E s t n) (h510 : ∀ n, Lemma510 X E s t (H n))
    (hdec : LKDecay X E s t) (hW : ∀ n, WardP X E n) :
    ∀ n, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t) (Step3.flowA B E s t) n := by
  intro n' hn'
  obtain ⟨n, rfl⟩ : ∃ n, n' = n + 2 := ⟨n' - 2, by omega⟩
  intro Λ Φ hΛ0 hΦ0 hΛ1 hY hX1 hX2 hY1
  have hE : |E| < 2 := by linarith
  have hXn1 := hX1 (n + 1) (by omega) (by omega)
  have hF := F_stochDom X hE hs0 ht1 (H n) (h510 n) (xiRhs_stochDom X hX1 hX2 hY1)
  -- the terms of (5.94) (charges `QGood`)
  have tP := termP X hE hs0 hst ht1 hc (hW n) hdec hΦ0 hXn1
  have tI1 := termI1 X hE hs0 hst ht1 hc hdec hΦ0 (hLmK (n + 2) (by omega))
  have tI2 := termI2 X hE hs0 hst ht1 hc (H n) (h510 n) hΦ0 hF
  have tI3 := termI3 X hE hs0 hst ht1 hc (hW n) hdec hΦ0 hXn1
  have tI4 := termI4 X hE hs0 hst ht1 hc (hW n) hdec hΦ0 hXn1
  have tM := termM X hE hs0 hst ht1 hc (H n) (h510 n) hΛ0 hΛ1 hY
  have hQ := ((((tP.add tI1).add tI2).add tI3).add tI4).add tM
  -- the terms of (5.84) (non-alternating charges)
  have t1I := term1I X hκ0 hκ1 hEκ hs0 hst ht1 hc hdec hΦ0 (hLmK (n + 2) (by omega))
  have t1F := term1F X hκ0 hκ1 hEκ hs0 hst ht1 hc (H n) (h510 n) hΦ0 hF
  have t1M := term1M X hκ0 hκ1 hEκ hs0 hst ht1 hc (H n) (h510 n) hΛ0 hΛ1 hY
  have hC := (t1I.add t1F).add t1M
  -- the rotated terms (for `σ = (-,+)`)
  have hQr := hQ.precomp_param (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) =>
    (p.1, ((fun i => p.2.1 (i + 1)), (fun i => p.2.2 (i + 1)))))
  have hT := (hQ.add hC).add hQr
  refine stochDom_xiLK_of X hE hs0 ht1 (ζ := fun N _ => Λ N ^ ((1 : ℝ) / 2) + Φ N)
    (Step3.stochDom_mono (fun N _ _ => by have := hΛ0 N; have := hΦ0 N; positivity) 15 ?_
      (StochDom.of_le_left (fun N p ω => ?_) hT))
  · filter_upwards [hΛ1] with N hN p ω
    have h1 : 1 ≤ Λ N ^ ((1 : ℝ) / 2) := Real.one_le_rpow hN (by norm_num)
    have := hΦ0 N
    simp only [Pi.add_apply]
    linarith
  · obtain ⟨v, σ, a⟩ := p
    have hA : 0 ≤ B.scale E N v ^ (n + 2) :=
      (pow_pos (B.scale_pos hE N ((hs0 N).trans_le v.2.1) (v.2.2.trans_lt (ht1 N))) _).le
    simp only [Pi.add_apply]
    have hv0 : 0 ≤ (v : ℝ) := ((hs0 N).trans_le v.2.1).le
    have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
    by_cases hq : QGood σ
    · exact (bound_qGood X hE hs0 ht1 (H n) ω v hq a).trans
        (le_add_of_le_of_nonneg (le_add_of_nonneg_right (by positivity)) (by positivity))
    · by_cases hna : NonAlt σ
      · exact (bound_nonAlt X hE hs0 ht1 (H n) ω v hna a).trans
          (le_add_of_le_of_nonneg (le_add_of_nonneg_left (by positivity)) (by positivity))
      · obtain rfl := eq_zero_of_not_nonAlt_not_qGood hna hq
        rw [lkT_swap2 X hE hv0 hv1 ω σ a]
        exact (bound_qGood X hE hs0 ht1 (H 0) ω v (qGood_swap2 σ hna hq) _).trans
          (le_add_of_nonneg_left (by positivity))

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

/-- `L - K` on loop indices. -/
noncomputable def Dl (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) (I : LoopIdx (ZMod (B.L N))) : ℂ :=
  X.Lval E N u ω I - B.Kval E N u I

theorem zt_im_eq (E u : ℝ) : (zt E u).im = etaT E u := by
  simp [zt, etaT]

/-- **Ward's identity for `L - K` at an interior label.** -/
theorem sum_Dl_ward_mid (hE : |E| < 2) {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (ZMod (B.L N))) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) (hne : 1 ≤ a₁.length) (c : ZMod (B.L N)) :
    ∑ b : ZMod (B.L N), Dl X E N u ω ⟨σ₁ ++ false :: true :: σ₂, a₁ ++ b :: c :: a₂⟩
      = wardKappa (B.W N) E u * (Dl X E N u ω ⟨σ₁ ++ true :: σ₂, a₁ ++ c :: a₂⟩
          - Dl X E N u ω ⟨σ₁ ++ false :: σ₂, a₁ ++ c :: a₂⟩) := by
  have hη := etaT_pos hE hu1
  have hz : (zt E u).im ≠ 0 := by rw [zt_im_eq]; exact hη.ne'
  have hL := sum_gloop_ward_mid (L := B.L N) (W := B.W N) (X.hermitian N u ω) hz σ₁ σ₂ a₁ a₂ h₁ c
  have hK := sum_Kgen_ward_mid (B.three_le_L N) (B.W N) hE hu0 hu1 σ₁ σ₂ a₁ a₂ h₁ h₂ hne c
  simp only [Dl, Sample.Lval, Band.Kval]
  rw [Finset.sum_sub_distrib, hL, hK, zt_im_eq, wardKappa]
  ring

/-- **Ward's identity for `L - K` at the last label.** -/
theorem sum_Dl_ward_last (hE : |E| < 2) {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    (μ : List Bool) (x : ZMod (B.L N)) (a' : List (ZMod (B.L N))) (hμ : μ.length = a'.length) :
    ∑ b : ZMod (B.L N), Dl X E N u ω ⟨true :: μ ++ [false], x :: a' ++ [b]⟩
      = wardKappa (B.W N) E u * (Dl X E N u ω ⟨true :: μ, x :: a'⟩
          - Dl X E N u ω ⟨false :: μ, x :: a'⟩) := by
  have hη := etaT_pos hE hu1
  have hz : (zt E u).im ≠ 0 := by rw [zt_im_eq]; exact hη.ne'
  have hL := sum_gloop_ward_last (L := B.L N) (W := B.W N) (X.hermitian N u ω) hz μ x a' hμ
  have hK := ward_Kgen (B.three_le_L N) (B.W N) hE hu0 hu1 μ (x :: a') (by simp [hμ])
  simp only [Dl, Sample.Lval, Band.Kval]
  rw [Finset.sum_sub_distrib, hL, hK, zt_im_eq, wardKappa]
  ring

/-- The slot sum of `(L-K)_{u,σ}` as a sum over label lists. -/
theorem Psum_lkT_eq {n : ℕ} (N : ℕ) (u : ℝ) (ω : Ω) (σ : Fin (n + 1) → Bool) (x : ZMod (B.L N)) :
    Psum (B.L N) (lkT X E N u ω σ) x
      = allSum (B.L N) n (fun rest => Dl X E N u ω ⟨List.ofFn σ, x :: rest⟩) := by
  rw [allSum_eq_sum_ofFn, Psum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [lkT, Dl, LoopData.idx, List.ofFn_succ]

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

/-- List form of the Ward step at an interior slot. -/
theorem ward_list_mid (hE : |E| < 2) {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    {p q m m' : ℕ} (hm : m = p + (q + 2)) (hm' : m' = p + (q + 1)) (σ₁ σ₂ : List Bool)
    (h₁ : σ₁.length = p + 1) (h₂ : σ₂.length = q) (x : ZMod (B.L N)) :
    allSum (B.L N) m (fun rest => Dl X E N u ω ⟨σ₁ ++ false :: true :: σ₂, x :: rest⟩)
      = wardKappa (B.W N) E u
        * (allSum (B.L N) m' (fun rest => Dl X E N u ω ⟨σ₁ ++ true :: σ₂, x :: rest⟩)
          - allSum (B.L N) m' (fun rest => Dl X E N u ω ⟨σ₁ ++ false :: σ₂, x :: rest⟩)) := by
  subst hm hm'
  rw [allSum_add, allSum_add, allSum_add, ← allSum_linear]
  refine allSum_congr p fun l₁ hl₁ => ?_
  simp only [allSum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← allSum_sum, ← allSum_linear]
  refine allSum_congr q fun l₂ hl₂ => ?_
  have := sum_Dl_ward_mid X hE hu0 hu1 ω σ₁ σ₂ (x :: l₁) l₂ (by simp [h₁, hl₁])
    (by rw [h₂, hl₂]) (by simp) c
  simpa only [List.cons_append] using this

/-- List form of the Ward step at the last slot. -/
theorem ward_list_last (hE : |E| < 2) {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    {n : ℕ} (μ : List Bool) (hμ : μ.length = n) (x : ZMod (B.L N)) :
    allSum (B.L N) (n + 1) (fun rest => Dl X E N u ω ⟨true :: μ ++ [false], x :: rest⟩)
      = wardKappa (B.W N) E u
        * (allSum (B.L N) n (fun rest => Dl X E N u ω ⟨true :: μ, x :: rest⟩)
          - allSum (B.L N) n (fun rest => Dl X E N u ω ⟨false :: μ, x :: rest⟩)) := by
  rw [allSum_succ_last, ← allSum_linear]
  refine allSum_congr n fun l hl => ?_
  have := sum_Dl_ward_last X hE hu0 hu1 ω μ x l (by rw [hμ, hl])
  simpa only [List.cons_append] using this

/-- **Ward's identity for the slot sums of `L - K`** (Lemma 3.6 applied to (5.96)):
the hypothesis `WardP` holds for every sample. -/
theorem wardP_holds (hE : |E| < 2) (n : ℕ) : WardP X E n := by
  intro σ ⟨j, hj0, hjf, hjt⟩
  by_cases hjl : j = Fin.last (n + 1)
  · -- the last slot: `σ = (+, μ, -)`
    subst hjl
    rw [Fin.last_add_one] at hjt
    set τ : Fin n → Bool := fun i => σ i.succ.castSucc with hτ
    refine ⟨Fin.cons true τ, Fin.cons false τ, fun N u hu0 hu1 ω x => ?_⟩
    have hσ : List.ofFn σ = true :: List.ofFn τ ++ [false] := by
      rw [List.ofFn_succ', List.ofFn_succ, hjf, List.concat_eq_append]
      simp only [Fin.castSucc_zero, hjt, hτ, List.cons_append]
    rw [Psum_lkT_eq, Psum_lkT_eq, Psum_lkT_eq, hσ, List.ofFn_cons, List.ofFn_cons]
    exact ward_list_last X hE hu0 hu1 ω _ (List.length_ofFn) x
  · -- an interior slot `j = p + 1 ≤ n`
    obtain ⟨p, hp⟩ : ∃ p, j.val = p + 1 := ⟨j.val - 1, by
      have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      omega⟩
    have hjn : j.val ≤ n := by
      have := j.isLt
      have : j.val ≠ n + 1 := fun h => hjl (Fin.ext (by simp [h]))
      omega
    have hj1 : (j + 1).val = p + 2 := by
      rw [Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr hjl), hp]
    set l := List.ofFn σ with hl
    have hll : l.length = n + 2 := List.length_ofFn
    set σ₁ := l.take (p + 1) with hσ₁
    set σ₂ := l.drop (p + 3) with hσ₂
    have h₁ : σ₁.length = p + 1 := by simp [hσ₁, hll]; omega
    have h₂ : σ₂.length = n - 1 - p := by simp [hσ₂, hll]; omega
    have hsplit : l = σ₁ ++ false :: true :: σ₂ := by
      conv_lhs => rw [← List.take_append_drop (p + 1) l]
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
      have e1 : l[p + 1]'(by omega) = false := by
        simp only [hl, List.getElem_ofFn]
        rw [← hjf]; congr 1; exact Fin.ext hp.symm
      have e2 : l[p + 1 + 1]'(by omega) = true := by
        simp only [hl, List.getElem_ofFn]
        rw [← hjt]; congr 1; exact Fin.ext hj1.symm
      rw [e1, e2]
    have hlen' : (σ₁ ++ true :: σ₂).length = n + 1 := by simp [h₁, h₂]; omega
    have hlen'' : (σ₁ ++ false :: σ₂).length = n + 1 := by simp [h₁, h₂]; omega
    refine ⟨fun i => (σ₁ ++ true :: σ₂).getD i false, fun i => (σ₁ ++ false :: σ₂).getD i false,
      fun N u hu0 hu1 ω x => ?_⟩
    rw [Psum_lkT_eq, Psum_lkT_eq, Psum_lkT_eq, ofFn_getD_eq _ hlen', ofFn_getD_eq _ hlen'',
      ← hl, hsplit]
    exact ward_list_mid X hE hu0 hu1 ω (p := p) (q := n - 1 - p) (by omega) (by omega)
      σ₁ σ₂ h₁ h₂ x

end WardFlowProof

end WardDischarge

section Discharged

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **Lemma 5.14 (5.92) for the flow**, with Ward's identity discharged (`wardP_holds`): the
same statement as `lemma514_flow` without the hypothesis `hW`. -/
theorem lemma514_flow' {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hLmK : ∀ m : ℕ, 1 ≤ m → StochDom B.P
      (fun N (w : LoopData (B.L N) m) ω => X.lkErr E N (s N) ω w.idx)
      (fun N _ _ => (B.scale E N (s N))⁻¹ ^ m))
    (H : ∀ n, Hierarchy X E s t n) (h510 : ∀ n, Lemma510 X E s t (H n))
    (hdec : LKDecay X E s t) :
    ∀ n, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t) (Step3.flowA B E s t) n :=
  lemma514_flow X hκ0 hκ1 hEκ hs0 hst ht1 hc hLmK H h510 hdec
    (fun n => wardP_holds X (by linarith) n)

end Discharged

end SumZeroDyn

end RBM
