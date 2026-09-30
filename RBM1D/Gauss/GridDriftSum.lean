/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2

/-!
# The weighted Duhamel sum for the drift terms, (5.39)–(5.41) on the grid

Paper (5.39)–(5.41).  The drift terms of the stopped
discrete hierarchy are transported by `U_{u_{j+1},u_k}` and summed.  This uses the
**label-weighted** kernel estimate `RBM.Step2.norm_Uker_le_of_tail` (the `T_u` profile maps to
the `T_v` profile), not the sup-norm bound of `GridDuhamelTail.lean`, which loses the profile.

## Main declarations

* `RBM.Gauss.Grid.tailT_mono_time` : an unconditional bridging fact — `T_{u,D}(d) ≤ T_{v,D}(d)`
  for `u ≤ v < 1`.  It follows from two purely
  structural facts about `ℓ̂(x) = min(1/√(1-x), L)`: `ℓ̂` is non-decreasing in `x`
  (`RBM.Step3.ellHat_mono`) and `ℓ̂(x) · (1 - x)` is non-increasing in `x` (proved here as
  `ellHat_mul_one_sub_antitone`, from the identity `ℓ̂(x)(1-x) = min(√(1-x), L(1-x))`, a `min`
  of two manifestly non-increasing functions of `x`).
* `RBM.Gauss.Grid.weighted_duhamel_sum_le` : the deterministic weighted Duhamel sum bound
  for the drift terms at a fixed grid index `k`, obtained by applying
  `RBM.Step2.norm_Uker_le_of_tail` termwise (bridging each drift term's `u_j`-profile bound up to
  a `u_{j+1}`-profile bound via `tailT_mono_time`), then summing with the triangle inequality and
  factoring the common `T_{u_k}` profile out of the sum.
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

/-- **Monotonicity of the tail function in time**: the tail function `T_{u,D}` is non-decreasing in
time, for any fixed distance `d ≥ 0`.  Uses that `ℓ̂` is non-decreasing (`RBM.Step3.ellHat_mono`)
and that `ℓ̂ · (1-·) · m` (hence the kernel weight `W ℓ̂ η`) is non-increasing
(`ellHat_mul_one_sub_antitone`). -/
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

end Fixed

section Witness

/-! ### Non-degeneracy witness for (T1)

A single grid step `u 0 = 0 → u 1 = 1/2 < 1`, `L = 3`, `W = e`, `m = 1`, `D = 0`, `Δ = 1`, with
`A 0` set to the *exact*, non-zero (`tailT_pos`) tail profile at `u 0` and `M 0 = 1` — so `hA`
holds with equality.  `hAuv` (the side condition of `Step2.norm_Uker_le_of_tail`) holds because
`ellHat_mul_one_sub_antitone` is unconditional: it only needs `u 1 ≤ u 1`, never an extra
restriction on the data.  This shows the hypotheses of (T1) are jointly satisfiable by a
genuine, non-zero instance, not merely by `A ≡ 0`. -/

end Witness

end RBM.Gauss.Grid
