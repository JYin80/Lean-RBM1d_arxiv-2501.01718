/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2

/-!
# T1510: the weighted Duhamel sum for the drift terms, (5.39)–(5.41) on the grid

Ticket `docs/tickets/T1510.md`, paper (5.39)–(5.41), p. 57.  The drift terms of the stopped
discrete hierarchy are transported by `U_{u_{j+1},u_k}` and summed.  This uses the
**label-weighted** kernel estimate `RBM.Step2.norm_Uker_le_of_tail` (the `T_u` profile maps to
the `T_v` profile), not the sup-norm bound of T1504 (T3), which loses the profile.

## Main declarations

* `RBM.Gauss.Grid.tailT_mono_time` : an unconditional bridging fact — `T_{u,D}(d) ≤ T_{v,D}(d)`
  for `u ≤ v < 1` — reproved locally here because T1508 (whose (T1) is exactly this statement)
  was not yet merged at the time this ticket was executed.  It follows from two purely
  structural facts about `ℓ̂(x) = min(1/√(1-x), L)`: `ℓ̂` is non-decreasing in `x`
  (`RBM.Step3.ellHat_mono`) and `ℓ̂(x) · (1 - x)` is non-increasing in `x` (proved here as
  `ellHat_mul_one_sub_antitone`, from the identity `ℓ̂(x)(1-x) = min(√(1-x), L(1-x))`, a `min`
  of two manifestly non-increasing functions of `x`).
* `RBM.Gauss.Grid.weighted_duhamel_sum_le` : (T1), the deterministic weighted Duhamel sum bound
  for the drift terms at a fixed grid index `k`, obtained by applying
  `RBM.Step2.norm_Uker_le_of_tail` termwise (bridging each drift term's `u_j`-profile bound up to
  a `u_{j+1}`-profile bound via `tailT_mono_time`), then summing with the triangle inequality and
  factoring the common `T_{u_k}` profile out of the sum.
* `RBM.Gauss.Grid.weighted_duhamel_sum_stopped` : (T2), the pointwise (per `ω`) corollary of (T1)
  with `k` replaced by `min k (τ ω)`, the hypothesis restricted to `j < τ ω`.

See `docs/reports/T1510-prove.md` for the math preflight.
-/

namespace RBM.Gauss.Grid

open Finset Real

section Bridge

/-- **Structural fact**: `ℓ̂_L(x) · (1 - x)` is non-increasing on `x < 1`.  Since
`ℓ̂_L(x) = min(1/√(1-x), L)` and `1 - x ≥ 0`, multiplying through gives
`ℓ̂_L(x)(1-x) = min(√(1-x), L(1-x))`, a `min` of two functions each manifestly non-increasing
in `x` (as `1 - x` is non-increasing and both `√` and `L · (·)` are monotone). -/
private lemma ellHat_mul_one_sub_antitone (L : ℕ) [NeZero L] {u v : ℝ} (huv : u ≤ v)
    (hv1 : v < 1) :
    ellHat L (v : ℂ) * (1 - v) ≤ ellHat L (u : ℂ) * (1 - u) := by
  have hu1 : u < 1 := huv.trans_lt hv1
  have hp0 : 0 < 1 - v := by linarith
  have hq0 : 0 < 1 - u := by linarith
  have hpq : (1 - v : ℝ) ≤ (1 - u) := by linarith
  rw [ellHat_ofReal L hu1, ellHat_ofReal L hv1,
      min_mul_of_nonneg _ _ hp0.le, min_mul_of_nonneg _ _ hq0.le]
  have e1 : (1 / Real.sqrt (1 - v)) * (1 - v) = Real.sqrt (1 - v) := by
    rw [div_mul_eq_mul_div, one_mul, Real.div_sqrt]
  have e2 : (1 / Real.sqrt (1 - u)) * (1 - u) = Real.sqrt (1 - u) := by
    rw [div_mul_eq_mul_div, one_mul, Real.div_sqrt]
  rw [e1, e2]
  exact min_le_min (Real.sqrt_le_sqrt hpq) (mul_le_mul_of_nonneg_left hpq (Nat.cast_nonneg L))

/-- **T1508 (T1), reproved locally** (T1508 not yet merged; cited by name for the audit): the
tail function `T_{u,D}` is non-decreasing in time, for any fixed distance `d ≥ 0`.  Uses that
`ℓ̂` is non-decreasing (`RBM.Step3.ellHat_mono`) and that `ℓ̂ · (1-·) · m` (hence the kernel
weight `W ℓ̂ η`) is non-increasing (`ellHat_mul_one_sub_antitone`). -/
theorem tailT_mono_time (L : ℕ) [NeZero L] (hL : 3 ≤ L) {m : ℝ} (hm0 : 0 < m)
    {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1) {W D d : ℝ} (hW0 : 0 < W)
    (hd : 0 ≤ d) :
    tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D d ≤
      tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D d := by
  have hL1 : 1 ≤ L := by omega
  have hu1 : u < 1 := huv.trans_lt hv1
  have hv0 : 0 ≤ v := hu0.trans huv
  have hℓu1 : 1 ≤ ellHat L (u : ℂ) := one_le_ellHat_of_nonneg hL1 hu0 hu1
  have hℓv1 : 1 ≤ ellHat L (v : ℂ) := one_le_ellHat_of_nonneg hL1 hv0 hv1
  have hℓuv : ellHat L (u : ℂ) ≤ ellHat L (v : ℂ) := Step3.ellHat_mono huv hv1
  have hAmono : W * ellHat L (v : ℂ) * ((1 - v) * m) ≤ W * ellHat L (u : ℂ) * ((1 - u) * m) := by
    have hgap := ellHat_mul_one_sub_antitone L huv hv1
    nlinarith [mul_le_mul_of_nonneg_left hgap (mul_nonneg hW0.le hm0.le)]
  have hAu0 : 0 < W * ellHat L (u : ℂ) * ((1 - u) * m) := by positivity
  have hAv0 : 0 < W * ellHat L (v : ℂ) * ((1 - v) * m) := by positivity
  have hinv : ((W * ellHat L (u : ℂ) * ((1 - u) * m)) ^ 2)⁻¹ ≤
      ((W * ellHat L (v : ℂ) * ((1 - v) * m)) ^ 2)⁻¹ := by
    have hAvsq : 0 < (W * ellHat L (v : ℂ) * ((1 - v) * m)) ^ 2 := by positivity
    have hsq : (W * ellHat L (v : ℂ) * ((1 - v) * m)) ^ 2 ≤
        (W * ellHat L (u : ℂ) * ((1 - u) * m)) ^ 2 := by
      nlinarith [hAmono, hAv0.le, hAu0.le]
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hAvsq hsq
  have hexp : Real.exp (-Real.sqrt (d / ellHat L (u : ℂ))) ≤
      Real.exp (-Real.sqrt (d / ellHat L (v : ℂ))) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left hd (by linarith : (0 : ℝ) < ellHat L (u : ℂ)) hℓuv
  have hterm1 : ((W * ellHat L (u : ℂ) * ((1 - u) * m)) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt (d / ellHat L (u : ℂ))) ≤
      ((W * ellHat L (v : ℂ) * ((1 - v) * m)) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt (d / ellHat L (v : ℂ))) :=
    mul_le_mul hinv hexp (Real.exp_pos _).le (by positivity)
  unfold tailT
  linarith [hterm1]

end Bridge

section Fixed

variable (L : ℕ) [NeZero L]

/-- **(T1)**: the weighted Duhamel sum bound for the drift terms at a fixed grid index `k`.
Grid times `u_j` in `[s,t]` (given as `u : ℕ → ℝ` with `u 0 ≥ 0` and `u` non-decreasing along
consecutive indices), `t = u k < 1`; `A_j` the drift at step `j`, bounded by `M_j` against the
`T_{u_j}` profile.  Route: apply `Step2.norm_Uker_le_of_tail` termwise, bridging each `A_j`'s
`u_j`-profile bound up to a `u_{j+1}`-profile bound via `tailT_mono_time`, then sum by the
triangle inequality and factor the common `T_{u_k}` profile out of the sum. -/
theorem weighted_duhamel_sum_le (hL : 3 ≤ L) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1)
    (u : ℕ → ℝ) (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {k : ℕ} (huk1 : u k < 1) {W D : ℝ} (hW : Real.exp 1 ≤ W)
    {Δ : ℝ} (hΔ0 : 0 ≤ Δ) (A : ℕ → LoopArg L 2 → ℂ) (M : ℕ → ℝ) (hM0 : ∀ j, 0 ≤ M j)
    (hA : ∀ j < k, ∀ b, ‖A j b‖ ≤
        M j * tailT W (ellHat L (u j : ℂ)) ((1 - u j) * m) D (zdist L (b 0 - b 1)))
    (hAuv : ∀ j < k, W * ellHat L (u k : ℂ) * ((1 - u k) * m)
        ≤ W * ellHat L (u (j + 1) : ℂ) * ((1 - u (j + 1)) * m))
    (a : LoopArg L 2) :
    ‖(∑ j ∈ Finset.range k,
        Δ • Uker L (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (u k : ℂ) (A j)) a‖ ≤
      (∑ j ∈ Finset.range k,
          Δ * M j * (((1 - u (j + 1)) / (1 - u k)) ^ 2) * Step2.xiK L W m) *
        tailT W (ellHat L (u k : ℂ)) ((1 - u k) * m) D (zdist L (a 0 - a 1)) := by
  classical
  have hW0 : 0 < W := lt_of_lt_of_le (Real.exp_pos 1) hW
  have hmono : Monotone u := monotone_nat_of_le_succ hu_succ
  have hu0k : 0 ≤ u k := hu0.trans (hmono (Nat.zero_le k))
  have hterm : ∀ j ∈ Finset.range k,
      ‖(Δ • Uker L (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (u k : ℂ) (A j)) a‖ ≤
        Δ * M j * (((1 - u (j + 1)) / (1 - u k)) ^ 2) * Step2.xiK L W m *
          tailT W (ellHat L (u k : ℂ)) ((1 - u k) * m) D (zdist L (a 0 - a 1)) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hj1k : u (j + 1) ≤ u k := hmono (by omega)
    have hu0j : 0 ≤ u j := hu0.trans (hmono (Nat.zero_le j))
    have hu0j1 : 0 ≤ u (j + 1) := hu0.trans (hmono (Nat.zero_le (j + 1)))
    have hstep : u j ≤ u (j + 1) := hu_succ j
    have huj1lt1 : u (j + 1) < 1 := hj1k.trans_lt huk1
    have hAj' : ∀ b, ‖A j b‖ ≤
        M j * tailT W (ellHat L (u (j + 1) : ℂ)) ((1 - u (j + 1)) * m) D
          (zdist L (b 0 - b 1)) := by
      intro b
      refine (hA j hjk b).trans ?_
      exact mul_le_mul_of_nonneg_left
        (tailT_mono_time L hL hm0 hu0j hstep huj1lt1 hW0 (Nat.cast_nonneg _)) (hM0 j)
    have hbound := Step2.norm_Uker_le_of_tail hL hm0 hm1 hu0j1 hj1k hu0k huk1 hW (hM0 j)
      (hAuv j hjk) hAj' a
    have heval : (Δ • Uker L (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (u k : ℂ) (A j)) a
        = (Δ : ℂ) * Uker L (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (u k : ℂ) (A j) a := by
      rw [Pi.smul_apply, Complex.real_smul]
    rw [heval, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
    calc Δ * ‖Uker L (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (u k : ℂ) (A j) a‖
        ≤ Δ * (M j * ((1 - u (j + 1)) / (1 - u k)) ^ 2 * Step2.xiK L W m *
            tailT W (ellHat L (u k : ℂ)) ((1 - u k) * m) D
              (zdist L (a 0 - a 1))) := mul_le_mul_of_nonneg_left hbound hΔ0
      _ = Δ * M j * (((1 - u (j + 1)) / (1 - u k)) ^ 2) * Step2.xiK L W m *
            tailT W (ellHat L (u k : ℂ)) ((1 - u k) * m) D (zdist L (a 0 - a 1)) := by ring
  calc ‖(∑ j ∈ Finset.range k,
        Δ • Uker L (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (u k : ℂ) (A j)) a‖
      = ‖∑ j ∈ Finset.range k,
          (Δ • Uker L (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (u k : ℂ) (A j)) a‖ := by
        rw [Finset.sum_apply]
    _ ≤ ∑ j ∈ Finset.range k,
          ‖(Δ • Uker L (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (u k : ℂ) (A j)) a‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k,
          Δ * M j * (((1 - u (j + 1)) / (1 - u k)) ^ 2) * Step2.xiK L W m *
            tailT W (ellHat L (u k : ℂ)) ((1 - u k) * m) D (zdist L (a 0 - a 1)) :=
        Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range k,
          Δ * M j * (((1 - u (j + 1)) / (1 - u k)) ^ 2) * Step2.xiK L W m) *
          tailT W (ellHat L (u k : ℂ)) ((1 - u k) * m) D (zdist L (a 0 - a 1)) := by
        rw [Finset.sum_mul]

/-- **(T2)**: the stopped version of (T1) — a pointwise (per `ω`) corollary with `k` replaced by
`min k (τ ω)`, the hypotheses on `A`/`M` and the side condition of `Step2.norm_Uker_le_of_tail`
required only for `j < τ ω` (rather than for all `j < min k (τ ω)`, of which they are a
super-hypothesis since `min k (τ ω) ≤ τ ω`). -/
theorem weighted_duhamel_sum_stopped (hL : 3 ≤ L) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1)
    (u : ℕ → ℝ) (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {Ω' : Type*} (τ : Ω' → ℕ) (ω : Ω') (k : ℕ)
    (huk1 : u (min k (τ ω)) < 1) {W D : ℝ} (hW : Real.exp 1 ≤ W)
    {Δ : ℝ} (hΔ0 : 0 ≤ Δ) (A : ℕ → LoopArg L 2 → ℂ) (M : ℕ → ℝ) (hM0 : ∀ j, 0 ≤ M j)
    (hA : ∀ j < τ ω, ∀ b, ‖A j b‖ ≤
        M j * tailT W (ellHat L (u j : ℂ)) ((1 - u j) * m) D (zdist L (b 0 - b 1)))
    (hAuv : ∀ j < τ ω, W * ellHat L (u (min k (τ ω)) : ℂ) * ((1 - u (min k (τ ω))) * m)
        ≤ W * ellHat L (u (j + 1) : ℂ) * ((1 - u (j + 1)) * m))
    (a : LoopArg L 2) :
    ‖(∑ j ∈ Finset.range (min k (τ ω)),
        Δ • Uker L (fun _ => (1 : ℂ)) (u (j + 1) : ℂ) (u (min k (τ ω)) : ℂ) (A j)) a‖ ≤
      (∑ j ∈ Finset.range (min k (τ ω)),
          Δ * M j * (((1 - u (j + 1)) / (1 - u (min k (τ ω)))) ^ 2) * Step2.xiK L W m) *
        tailT W (ellHat L (u (min k (τ ω)) : ℂ)) ((1 - u (min k (τ ω))) * m) D
          (zdist L (a 0 - a 1)) := by
  have hsub : ∀ j, j < min k (τ ω) → j < τ ω := fun j hj => hj.trans_le (min_le_right k (τ ω))
  exact weighted_duhamel_sum_le L hL hm0 hm1 u hu0 hu_succ huk1 hW hΔ0 A M hM0
    (fun j hj b => hA j (hsub j hj) b) (fun j hj => hAuv j (hsub j hj)) a

end Fixed

section Witness

/-! ### Non-degeneracy witness for (T1)

A single grid step `u 0 = 0 → u 1 = 1/2 < 1`, `L = 3`, `W = e`, `m = 1`, `D = 0`, `Δ = 1`, with
`A 0` set to the *exact*, non-zero (`tailT_pos`) tail profile at `u 0` and `M 0 = 1` — so `hA`
holds with equality.  `hAuv` (the side condition of `Step2.norm_Uker_le_of_tail`) holds because
`ellHat_mul_one_sub_antitone` is unconditional: it only needs `u 1 ≤ u 1`, never an extra
restriction on the data.  This shows the hypotheses of (T1) are jointly satisfiable by a
genuine, non-zero instance, not merely by `A ≡ 0`. -/
example : True := by
  have hL : (3 : ℕ) ≤ 3 := le_refl 3
  have hm0 : (0 : ℝ) < 1 := one_pos
  have hm1 : (1 : ℝ) ≤ 1 := le_refl 1
  have hW : Real.exp 1 ≤ Real.exp 1 := le_refl _
  set u : ℕ → ℝ := fun j => (j : ℝ) / 2 with hudef
  have hu0 : (0 : ℝ) ≤ u 0 := by simp [hudef]
  have hu_succ : ∀ j : ℕ, u j ≤ u (j + 1) := by
    intro j; simp only [hudef]; push_cast; linarith
  have huk1 : u 1 < 1 := by simp [hudef]; norm_num
  have hΔ0 : (0 : ℝ) ≤ 1 := zero_le_one
  set A : ℕ → LoopArg 3 2 → ℂ :=
    fun j b => (tailT (Real.exp 1) (ellHat 3 (u j : ℂ)) ((1 - u j) * 1) 0
      (zdist 3 (b 0 - b 1)) : ℂ) with hAdef
  have hW0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hnonneg : ∀ j (b : LoopArg 3 2), 0 ≤
      tailT (Real.exp 1) (ellHat 3 (u j : ℂ)) ((1 - u j) * 1) 0 (zdist 3 (b 0 - b 1)) :=
    fun j b => tailT_nonneg hW0.le _
  have hApos : ∀ (b : LoopArg 3 2), 0 <
      tailT (Real.exp 1) (ellHat 3 (u 0 : ℂ)) ((1 - u 0) * 1) 0 (zdist 3 (b 0 - b 1)) :=
    fun b => tailT_pos hW0 _
  have hM0 : ∀ j : ℕ, (0 : ℝ) ≤ (1 : ℝ) := fun _ => zero_le_one
  have hA : ∀ j < 1, ∀ b : LoopArg 3 2, ‖A j b‖ ≤
      (1 : ℝ) * tailT (Real.exp 1) (ellHat 3 (u j : ℂ)) ((1 - u j) * 1) 0
        (zdist 3 (b 0 - b 1)) := by
    intro j _ b
    simp only [hAdef, one_mul]
    rw [Complex.norm_real, Real.norm_of_nonneg (hnonneg j b)]
  have hAuv : ∀ j < 1, Real.exp 1 * ellHat 3 (u 1 : ℂ) * ((1 - u 1) * 1)
      ≤ Real.exp 1 * ellHat 3 (u (j + 1) : ℂ) * ((1 - u (j + 1)) * 1) := by
    intro j hj
    interval_cases j
    exact le_refl _
  have hne : A 0 (fun _ => 0) ≠ 0 := by
    have := hApos (fun _ => 0)
    simp only [hAdef]
    exact_mod_cast this.ne'
  have hconcl := weighted_duhamel_sum_le 3 hL hm0 hm1 u hu0 hu_succ huk1 hW hΔ0 A (fun _ => 1)
    hM0 hA hAuv (fun _ => 0)
  clear hne hconcl
  trivial

end Witness

end RBM.Gauss.Grid
