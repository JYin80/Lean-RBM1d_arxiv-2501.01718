/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore

/-!
# T314 compatibility facade for the smooth-prefix core
-/

namespace RBM
namespace APrimeSmoothPrefix

open Real Finset Step2Bootstrap
open scoped Matrix.Norms.L2Operator

section Model

open Gauss

theorem jSnorm_le_smoothJS (d : Gauss.Dims) {E D u ε : ℝ} {s : ℕ → ℝ}
    (hE : |E| < 2) {N : ℕ} (hs : s N < 1) (hu : u < 1)
    (hε : 0 ≤ ε) {m : ℕ} (hm : 1 ≤ m) (ω : Gauss.Ω d) :
    Step2Moment.jSnorm (Gauss.sample d) E D s N u ω ≤
      smoothJS d E D s N u ε m ω := by
  let f : LoopArg (d.L N) 2 → ℝ := fun a => ‖Step2.lk (Gauss.sample d) E N u ω a‖
  let c : LoopArg (d.L N) 2 → ℝ := fun a =>
    Step2.tT (Gauss.band d) E N D u (zdist (d.L N) (a 0 - a 1))
  have hc : ∀ a, 0 < c a := by
    intro a
    exact tailT_pos (by exact_mod_cast (Gauss.band d).W_pos N) _
  have hW : 0 < (d.W N : ℝ) := by exact_mod_cast (Gauss.band d).W_pos N
  have hnum : Step2.jS (Gauss.sample d) E D N u ω = hardJ f c := by
    rw [hardJ_eq]
    simp only [Step2.jS, Step2.jStar, Step2.tT, f, c,
      Gauss.band_W, Gauss.band_L]
    conv_lhs => rw [add_comm]
    congr 1
  have hR : 0 < (Step2Moment.ratR E s N u) ^ 4 :=
    pow_pos (Step2Moment.ratR_pos hE hs hu) _
  rw [Step2Moment.jSnorm, smoothJS, hnum]
  exact div_le_div_of_nonneg_right
    (hardJ_sandwich (fun a => norm_nonneg _) hc hε
      (Real.rpow_pos_of_pos hW _) (by
        intro a
        exact rpow_neg_le_tailT _) hm).1 hR.le

theorem first_cell_witness (d : Gauss.Dims) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) (ω : Gauss.Ω d) :
    Step2Moment.jSnorm (Gauss.sample d) 0 0 (fun _ => 0) N (1 / 4) ω ≤
      smoothJS d 0 0 (fun _ => 0) N (1 / 4) ε 1 ω ∧
    0 < smoothJS d 0 0 (fun _ => 0) N (1 / 4) ε 1 ω ∧
    ContDiff ℝ 1 (smoothJSMatrix d 0 0 (fun _ => 0) N (1 / 4) ε 1) := by
  refine ⟨jSnorm_le_smoothJS d (by norm_num) (by norm_num) (by norm_num)
    hε.le (by norm_num) ω,
    smoothJS_pos d (by norm_num) (by norm_num) (by norm_num) 1 ω,
    contDiff_smoothJSMatrix d (by norm_num) (by norm_num) (by norm_num)
      hε (by norm_num)⟩

end Model

end APrimeSmoothPrefix
end RBM
