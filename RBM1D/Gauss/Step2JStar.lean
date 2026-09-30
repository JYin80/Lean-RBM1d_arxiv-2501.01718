/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LoopC2
import RBM1D.Analysis.StretchedExp

/-!
# Clean smooth-prefix and canonical calibration core

This file contains the dependency-clean producer surface for the literal smooth-prefix
construction and its canonical smoothing order.
-/

set_option maxHeartbeats 1000000

namespace RBM

namespace Step2Bootstrap

variable {ι : Type*}

end Step2Bootstrap

namespace Step2

open Finset Real

noncomputable def jStar (L : ℕ) [NeZero L] (f : LoopArg L 2 → ℝ)
    (W ℓu ηu D : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => f a / tailT W ℓu ηu D (zdist L (a 0 - a 1))) + 1

def sigPM : Fin 2 → Bool := ![true, false]

noncomputable def lk {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
    (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) :
    LoopArg (B.L N) 2 → ℂ :=
  fun a => X.Lval E N u ω (LoopData.idx (sigPM, a)) -
    B.Kval E N u (LoopData.idx (sigPM, a))

noncomputable def tT {Ω : Type*} [MeasurableSpace Ω]
    (B : Band Ω) (E : ℝ) (N : ℕ) (D u ℓ : ℝ) : ℝ :=
  tailT (B.W N) (B.ell N u) (etaT E u) D ℓ

noncomputable def jS {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
    (X : Sample B) (E D : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  jStar (B.L N) (fun a => ‖lk X E N u ω a‖)
    (B.W N) (B.ell N u) (etaT E u) D

end Step2

namespace Step2Moment

end Step2Moment

namespace CutHypTheta

end CutHypTheta

end RBM
