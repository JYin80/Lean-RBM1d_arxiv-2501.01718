/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DistEq
import RBM1D.EnergyN.Loop.ContinuityAssembly

/-!
# (6.1) for the Gaussian model at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, (6.1).

`RBM.Gauss.loopScaling_gaussN` proves `RBM.LoopScalingN`
(`RBM1D/EnergyN/Loop/ContinuityAssembly.lean`) for the Gaussian flow at an `N`-dependent energy
`E : ℕ → ℝ`. No energy-dependent constant is fixed here: the proof is a pointwise algebraic
identity (`RBM.Gauss.gloop_Hflow_ztTilde_eq`, energy-free, used at `E N`) with a deterministic
factor `≤ 1`; no `(mE E).im`-type constant is fixed before `∀ᶠ N`.
-/

namespace RBM.Gauss

variable (d : Dims)

/-- **(6.1) as a transfer of `≺`-bounds** for the moment route, at an `N`-dependent energy. -/
theorem loopScaling_gaussN {E : ℕ → ℝ} {t₁ t₂ : ℕ → ℝ} (h₁ : ∀ N, 0 < t₁ N)
    (h₁₂ : ∀ N, t₁ N ≤ t₂ N) :
    RBM.LoopScalingN (sample d) E t₁ t₂ where
  transfer := by
    intro n _ ζ h
    refine RBM.StochDom.of_le_left (fun N u ω => ?_) h
    set r : ℝ := Real.sqrt (t₂ N / t₁ N) with hr_def
    have hr1 : 1 ≤ r := by
      rw [hr_def, show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt ((one_le_div (h₁ N)).2 (h₁₂ N))
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
    have hkey := gloop_Hflow_ztTilde_eq d N (E := E N) (h₁ N) (h₁₂ N) ω u.idx
    have hL : RBM.gloop ((band d).L N) ((band d).W N) ((sample d).H N (t₂ N) ω)
        (RBM.ztTilde (E N) (t₁ N) (t₂ N)) u.idx
        = ((r : ℂ))⁻¹ ^ (u.idx.σ.zip u.idx.a).length *
          (sample d).Lval (E N) N (t₁ N) ω u.idx := hkey
    rw [hL, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0]
    have hle : |r|⁻¹ ^ (u.idx.σ.zip u.idx.a).length ≤ 1 := by
      rw [abs_of_pos hr0]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hr1)
    rw [abs_of_pos hr0] at hle
    calc r⁻¹ ^ (u.idx.σ.zip u.idx.a).length *
        ‖(sample d).Lval (E N) N (t₁ N) ω u.idx‖
        ≤ 1 * ‖(sample d).Lval (E N) N (t₁ N) ω u.idx‖ :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ = _ := one_mul _

end RBM.Gauss
