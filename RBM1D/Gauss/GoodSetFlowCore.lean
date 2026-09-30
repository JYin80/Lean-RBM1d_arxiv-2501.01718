/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2JStar
import RBM1D.Gauss.DimsExample

/-! The literal general-moving carrier and transition predicates. -/

namespace RBM.Step1

variable {Ω : Type*} [MeasurableSpace Ω]
/-- The right side of (2.73) and (5.8): `(ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}`. -/
noncomputable def aprioriRhs (B : Band Ω) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) :
    ∀ N, TimeIcc s t N × LoopData (B.L N) n → Ω → ℝ :=
  fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale E N p.1)⁻¹ ^ (n - 1)

end RBM.Step1

namespace RBM.Gauss

open MeasureTheory Set
/-- The time-independent threshold `δ_N = (W ℓ_{t_N} η_{t_N})^{-1/6}` of (4.1) used along the
whole flow interval `[s_N, t_N]`.  `RBM.flowScale` is antitone in the time, so this dominates
the `u`-dependent threshold `(W ℓ_u η_u)^{-1/6}` of `RBM.Step1.goodEv` for every `u ≤ t_N`. -/
noncomputable def flowDelta (d : Dims) (E : ℝ) (t : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((band d).scale E N (t N))⁻¹ ^ ((1 : ℝ) / 6)

/-- **The good event (4.1) uniformly in `u ∈ [s_N, t_N]`.**

`RBM.goodSet` pins one time in the matrix *and* in the spectral parameter; the hypothesis `hΩ`
of `RBM1D/Gauss/CondStableInst.lean` is that set's `HighProb`.  Along the flow both times move
together and the event must hold at every `u` simultaneously — this is the flow analogue, and it is
what the net lift of the three (4.5) inputs consumes. -/
def goodSetFlow (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (δ : ℕ → ℝ) (N : ℕ) : Set (Ω d) :=
  {ω | ∀ u ∈ Set.Icc (s N) (t N), GoodEvent (green (Hflow d N u ω) (zt E u)) (mE E) (δ N)}

variable {Ω : Type*} [MeasurableSpace Ω]

end RBM.Gauss

namespace RBM.BlockGreen

open Finset Real MeasureTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
/-- Maximum Green entry between two physical blocks, over both charges. -/
noncomputable def gmBlk (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (x y : ZMod (B.L N)) : ℝ :=
  (Finset.univ : Finset (Bool × Fin (B.W N) × Fin (B.W N))).sup'
    ⟨(true, ⟨0, B.W_pos N⟩, ⟨0, B.W_pos N⟩), Finset.mem_univ _⟩
    (fun z => ‖Gsig (X.H N u ω) (zt E u) z.1 (x, z.2.1) (y, z.2.2)‖)

/-- Squared block control that retains the neighbour in the row of `SB`. -/
noncomputable def gsqBlk (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (x y : ZMod (B.L N)) : ℝ :=
  (Finset.univ : Finset (ZMod (B.L N))).sup'
    ⟨0, Finset.mem_univ _⟩
    (fun x' => if SB (B.L N) x x' ≠ 0 then
      gmBlk X E N u ω y x' * gmBlk X E N u ω x' y else 0)

/-- The block-level `J` in (5.42), normalized only over far block pairs. -/
noncomputable def jG (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (ℓu ηu D : ℝ) : ℝ :=
  1 + (Finset.univ : Finset (ZMod (B.L N) × ZMod (B.L N))).sup'
    ⟨(0, 0), Finset.mem_univ _⟩
    (fun p => if ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (p.1 - p.2) : ℝ)
      then gsqBlk X E N u ω p.1 p.2 /
        tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (p.1 - p.2))
      else 0)

end RBM.BlockGreen
