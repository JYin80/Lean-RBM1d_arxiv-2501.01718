/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.EnergyN.Unif.Flow.Iteration

/-!
# The bound (2.61) on `L` at an `N`-dependent energy

`RBM.stochDom_norm_Lval_of_LmKN` derives (2.61) from (2.60) and (2.59) at an energy
`E : ℕ → ℝ`, with the single `E`-uniform kernel constant `RBM.Band.norm_Kval_le_unif`
(`RBM1D/EnergyN/Unif/Flow/Iteration.lean`). The rest of the proof is energy-free arithmetic on
`Y N := (B.scale (E N) N (t N))⁻¹` with the constants `1` and `2`.
-/

namespace RBM

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℕ → ℝ}

open MeasureTheory Filter

/-- **(2.61) from (2.60) and (2.59), `N`-form.** For `|E N| ≤ 2 - k`: if `|L - K| ≺ Y ^ n`
with `Y N = (B.scale (E N) N (t N))⁻¹ ≤ 1` eventually, then `|L| ≺ Y ^ (n - 1)`. The kernel
constant `C` is the single uniform-in-`E` constant from `RBM.Band.norm_Kval_le_unif`, fixed
before `hE`/`∀ N`. -/
theorem stochDom_norm_Lval_of_LmKN {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hE : ∀ N, |E N| ≤ 2 - k) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N) (ht1 : ∀ N, t N < 1)
    (hA : ∀ᶠ N : ℕ in atTop, 1 ≤ B.scale (E N) N (t N)) {n : ℕ} (hn : 1 ≤ n)
    (hLK : StochDom B.P (fun N (u : LoopData (B.L N) n) ω => X.lkErr (E N) N (t N) ω u.idx)
      (fun N _ _ => (B.scale (E N) N (t N))⁻¹ ^ n)) :
    StochDom B.P (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval (E N) N (t N) ω u.idx‖)
      (fun N _ _ => (B.scale (E N) N (t N))⁻¹ ^ (n - 1)) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨C, hC0, hC⟩ := B.norm_Kval_le_unif hk0 hk1 hn
  set Y : ℕ → ℝ := fun N => (B.scale (E N) N (t N))⁻¹ with hYdef
  have hY0 : ∀ N, 0 ≤ Y N := fun N => inv_nonneg.2 (B.scale_nonneg (E N) N (ht1 N).le)
  -- `|L - K| ≺ Y^{n-1}`
  have h1 : StochDom B.P (fun N (u : LoopData (B.L N) n) ω => X.lkErr (E N) N (t N) ω u.idx)
      (fun N _ _ => Y N ^ (n - 1)) := by
    refine hLK.trans ?_
    refine StochDom.of_unifDetDom (f := fun N (_ : LoopData (B.L N) n) => Y N ^ n)
      (g := fun N _ => Y N ^ (n - 1)) ?_
    refine UnifDetDom.of_eventually_le_const_mul (fun N _ => pow_nonneg (hY0 N) _) 1 ?_
    filter_upwards [hA] with N hN u
    have hY1 : Y N ≤ 1 := inv_le_one_of_one_le₀ hN
    have : Y N ^ n = Y N * Y N ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this, one_mul]
    exact mul_le_of_le_one_left (pow_nonneg (hY0 N) _) hY1
  -- `|K| ≺ Y^{n-1}`
  have h2 : StochDom B.P (fun N (u : LoopData (B.L N) n) (_ : Ω) => ‖B.Kval (E N) N (t N) u.idx‖)
      (fun N _ _ => Y N ^ (n - 1)) :=
    StochDom.of_unifDetDom (UnifDetDom.of_eventually_le_const_mul
      (fun N _ => pow_nonneg (hY0 N) _) C (Eventually.of_forall fun N u =>
        hC (E N) (hE N) N (t N) (ht0 N) (ht1 N) u.idx u.idx_wf (by simp)))
  have h3 : StochDom B.P (fun N (_ : LoopData (B.L N) n) (_ : Ω) => Y N ^ (n - 1) + Y N ^ (n - 1))
      (fun N _ _ => Y N ^ (n - 1)) := by
    refine StochDom.of_unifDetDom (f := fun N (_ : LoopData (B.L N) n) => Y N ^ (n - 1) +
      Y N ^ (n - 1)) (g := fun N _ => Y N ^ (n - 1)) ?_
    exact UnifDetDom.of_eventually_le_const_mul (fun N _ => pow_nonneg (hY0 N) _) 2
      (Eventually.of_forall fun N _ => by linarith)
  refine StochDom.of_le_left (fun N u ω => ?_) ((h1.add h2).trans h3)
  have := norm_sub_norm_le (X.Lval (E N) N (t N) ω u.idx) (B.Kval (E N) N (t N) u.idx)
  simp only [Pi.add_apply, Sample.lkErr]
  linarith

end RBM
