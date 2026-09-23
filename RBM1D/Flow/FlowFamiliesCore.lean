/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Hypotheses
import RBM1D.Flow.Scales
import RBM1D.Loop.Split

/-!
# Elementary flow families used by Step 3

This file isolates the elementary `Ξᴸ` flow family, the length-scale ratio, and their basic
length-scale facts below the Step 3 hierarchy.
-/

namespace RBM

namespace Step3

variable {W : ℝ} {L : ℕ} {E s u t : ℝ}

theorem ellHat_pos_of_lt_one (hL : 1 ≤ L) {x : ℝ} (hx : x < 1) : 0 < ellHat L (x : ℂ) := by
  rw [ellHat_ofReal L hx]
  have : (0 : ℝ) < L := by exact_mod_cast hL
  have : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.2 (by linarith)
  exact lt_min (by positivity) (by assumption)

theorem ellHat_mono (hst : s ≤ t) (ht1 : t < 1) : ellHat L (s : ℂ) ≤ ellHat L (t : ℂ) := by
  rw [ellHat_ofReal L (hst.trans_lt ht1), ellHat_ofReal L ht1]
  refine min_le_min ?_ le_rfl
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by linarith))
    (Real.sqrt_le_sqrt (by linarith))

end Step3

namespace Sample

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B)

/-- **(5.76)** `Ξ^{(L)}_{t,m} = max_{σ,a} |L_{t,σ,a}| · (W ℓ_t η_t)^{m-1}`, the maximum over
`σ ∈ {+,-}^m`, `a ∈ ℤ_L^m` (`RBM.loopXi` of `Loop/Split.lean` at `H = H_t`, `z = z_t`). -/
noncomputable def xiL (E : ℝ) (N : ℕ) (t : ℝ) (ω : Ω) (m : ℕ) : ℝ :=
  loopXi (B.L N) (B.W N) (X.H N t ω) (zt E t) (B.scale E N t) m

end Sample

namespace Step3

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `Ξ^{(L)}_{u,n}` for `u ∈ [s,t]`. -/
noncomputable def flowXiL (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) :
    ℕ → ∀ N, TimeIcc s t N → Ω → ℝ :=
  fun n N u ω => X.xiL E N u ω n

/-- `R N = ℓ_t/ℓ_s`. -/
noncomputable def flowR (B : Band Ω) (s t : ℕ → ℝ) : ℕ → ℝ :=
  fun N => B.ell N (t N) / B.ell N (s N)

end Step3

end RBM
