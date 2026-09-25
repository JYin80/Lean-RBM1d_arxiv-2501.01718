/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2

/-!
# The initial condition `J*_{s,D} ≺ 1` (M1 of `docs/reports/T1488-prove.md`)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.3: the initial condition
`J*_{s,D} ≺ 1` used to start the stopping-time argument of Step 2, from (2.68)/(2.69).

This extracts as a named statement the argument that is inlined as `hinit` in the proof of
`RBM.Step2.jS_highProb` (`Hierarchy/Step2.lean`): `RBM.BoundsCore.decay` ((2.69)) gives a
high-probability bound on `‖(L-K)_{s,σ,a}‖`, `RBM.Step2.decayProf_le_tT` converts the decay
profile to the tail function `T_{s,D}`, and `RBM.Step2.jStar_le` turns the resulting bound
`f a ≤ c T_{s,D}(...)` into `J* ≤ c + 1`.
-/

namespace RBM

namespace Step2

open Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The initial condition (2.68)/(2.69), M1 of `docs/reports/T1488-prove.md`**:
`J*_{s,D} ≺ 1`. -/
theorem stochDom_jS_init (X : Sample B) {E : ℝ} {s : ℕ → ℝ} (hB : BoundsCore X E s)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hs1 : ∀ N, s N < 1)
    (hAs : ∀ᶠ N : ℕ in atTop, 1 ≤ B.scale E N (s N)) :
    ∀ D : ℝ, 0 < D →
      StochDom B.P (fun N (_ : Unit) ω => jS X E D N (s N) ω) (fun _ _ _ => 1) := by
  intro D hD0
  refine SumZeroDyn.stochDom_of_good fun τ hτ => ?_
  refine ⟨_, (hB.decay D hD0).highProb (half_pos hτ), ?_⟩
  filter_upwards [hAs, eventually_le_rpow 2 (half_pos hτ)] with N hAsN hle2
  intro ω hω u
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hbound : ∀ b : LoopArg (B.L N) 2,
      ‖lk X E N (s N) ω b‖ ≤
        (N : ℝ) ^ (τ / 2) * tT B E N D (s N) (zdist (B.L N) (b 0 - b 1)) := by
    intro b
    rw [norm_lk_eq]
    have h1 := hω (b 0, b 1)
    have h2 := decayProf_le_tT (E := E) (N := N) (u := s N) (D := D) hAsN (b 0) (b 1)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  have hJ := jStar_le hW0 hbound
  have hhalf : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ :=
    UnifDetDom.rpow_half_mul_rpow_half N hτ
  have h1le : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := le_trans (by norm_num) hle2
  change jS X E D N (s N) ω ≤ (N : ℝ) ^ τ * 1
  rw [mul_one]
  calc jS X E D N (s N) ω
      ≤ (N : ℝ) ^ (τ / 2) + 1 := hJ
    _ ≤ (N : ℝ) ^ (τ / 2) + (N : ℝ) ^ (τ / 2) := by linarith
    _ = 2 * (N : ℝ) ^ (τ / 2) := by ring
    _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by nlinarith
    _ = (N : ℝ) ^ τ := hhalf

end Step2

end RBM
