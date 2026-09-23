/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSmoothPrefixCanonicalCore
import RBM1D.Gauss.DimsExample

/-! The literal general-moving carrier and transition predicates. -/

namespace RBM.Step1

variable {Ω : Type*} [MeasurableSpace Ω]
/-- The right side of (2.73) and (5.8): `(ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}`. -/
noncomputable def aprioriRhs (B : Band Ω) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) :
    ∀ N, TimeIcc s t N × LoopData (B.L N) n → Ω → ℝ :=
  fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale E N p.1)⁻¹ ^ (n - 1)

end RBM.Step1

namespace RBM.APrimeGeneralMovingGoodMesh

open Gauss
open scoped Matrix.Norms.L2Operator
/-- The fixed norm event, independent of every window and bootstrap
parameter. -/
def good (N : ℕ) : Set (Ω Dims.exampleGrow) :=
  {ω : Ω Dims.exampleGrow |
    ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)}

end RBM.APrimeGeneralMovingGoodMesh

namespace RBM.APrimeGeneralMovingRawSources

noncomputable section

open Gauss
private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d
def rawEvent (E : ℝ) (s t : ℕ → ℝ) (ζ : ℝ)
    (n N : ℕ) : Set (Ω d) :=
  {ω | ∀ p : TimeIcc s t N × LoopData (d.L N) n,
    ‖(sample d).Lval E N p.1 ω p.2.idx‖ ≤
      (N : ℝ) ^ ζ * Step1.aprioriRhs B E s t n N p ω}

def sourceGood (E : ℝ) (s t : ℕ → ℝ) (ζ : ℝ)
    (N : ℕ) : Set (Ω d) :=
  APrimeGeneralMovingGoodMesh.good N ∩
    rawEvent E s t ζ 3 N ∩
    rawEvent E s t ζ 4 N ∩
    rawEvent E s t ζ 6 N

end

end RBM.APrimeGeneralMovingRawSources

namespace RBM.Gauss

open MeasureTheory Set
/-- The time-independent threshold `δ_N = (W ℓ_{t_N} η_{t_N})^{-1/6}` of (4.1) used along the
whole flow interval `[s_N, t_N]`.  `RBM.flowScale` is antitone in the time, so this dominates
the `u`-dependent threshold `(W ℓ_u η_u)^{-1/6}` of `RBM.Step1.goodEv` for every `u ≤ t_N`. -/
noncomputable def flowDelta (d : Dims) (E : ℝ) (t : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((band d).scale E N (t N))⁻¹ ^ ((1 : ℝ) / 6)

/-- **The good event (4.1) uniformly in `u ∈ [s_N, t_N]`.**

`RBM.goodSet` pins one time in the matrix *and* in the spectral parameter; the `hΩ` that T119
leaves open is that set's `HighProb`.  Along the flow both times move together and the event
must hold at every `u` simultaneously — this is the flow analogue, and it is what the net lift
of the three (4.5) inputs consumes. -/
def goodSetFlow (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (δ : ℕ → ℝ) (N : ℕ) : Set (Ω d) :=
  {ω | ∀ u ∈ Set.Icc (s N) (t N), GoodEvent (green (Hflow d N u ω) (zt E u)) (mE E) (δ N)}

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The measurable core of `Ξ`**: the complement of a measurable hull of `Ξᶜ`.

It is a measurable subset of `Ξ` whose complement has the same outer measure as `Ξᶜ`.  Every
hypothesis of the form `∀ ω ∈ Ξ, …` therefore holds on it, and `RBM.HighProb` transports to
it unchanged. -/
noncomputable def measCore (P : Measure Ω) (Ξ : Set Ω) : Set Ω := (toMeasurable P Ξᶜ)ᶜ

theorem measCore_subset (P : Measure Ω) (Ξ : Set Ω) : measCore P Ξ ⊆ Ξ := by
  intro ω hω
  by_contra h
  exact hω (subset_toMeasurable P Ξᶜ h)

/-- **The core costs nothing**: its complement has the same measure as `Ξᶜ`. -/
theorem measure_compl_measCore (P : Measure Ω) (Ξ : Set Ω) :
    P (measCore P Ξ)ᶜ = P Ξᶜ := by
  rw [measCore, compl_compl]
  exact measure_toMeasurable Ξᶜ

end RBM.Gauss

namespace RBM.APrimeGeneralMovingControlExtension

noncomputable section

open Gauss
private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d
/-- The original moving-window one-loop control. -/
def q (E : ℝ) (s : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (B.ell N u / B.ell N (s N)) / B.scale E N u

/-- Clamp an arbitrary real time to the moving window. -/
def clampTime (s t : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  max (s N) (min (t N) u)

/-- A global extension of `q` using only deterministic clamping. -/
def qExt (E : ℝ) (s t : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  q E s N (clampTime s t N u)

end

end RBM.APrimeGeneralMovingControlExtension

namespace RBM.APrimeGeneralMovingTwoChargeModulus

open Gauss
private noncomputable abbrev d : Dims := Dims.exampleGrow
/-- The centered block trace at either resolvent charge. -/
noncomputable def centeredTrace (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω d)
    (σ : Bool) (b : ZMod (d.L N)) : ℂ :=
  Matrix.trace ((Gsig (Hflow d N u ω) (zt E u) σ
    - mSigma E σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
      Eblk (d.L N) (d.W N) b)

end RBM.APrimeGeneralMovingTwoChargeModulus

namespace RBM.APrimeJG

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

end RBM.APrimeJG

namespace RBM.APrimeGeneralMovingCommonSources

noncomputable section

open Gauss
private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d
/-- The two centered charges, with one fixed loss, on the whole moving window. -/
def centeredEvent (E : Real) (s t : Nat -> Real) (zetaCtr : Real)
    (N : Nat) : Set (Ω d) :=
  {omega | forall sigma : Bool,
    forall p : TimeIcc s t N × ZMod (d.L N),
      norm (APrimeGeneralMovingTwoChargeModulus.centeredTrace
        E N (p.1 : Real) omega sigma p.2) <=
      (N : Real)^zetaCtr *
        (2 * APrimeGeneralMovingControlExtension.qExt
          E s t N (p.1 : Real))}

/-- The all-time block-resolved Green event supplied by `APrimeJG`. -/
def blockEvent (E D : Real) (s t : Nat -> Real) (tauG : Real)
    (N : Nat) : Set (Ω d) :=
  {omega | forall u : TimeIcc s t N,
    APrimeJG.jG (Gauss.sample d) E N (u : Real) omega
      (B.ell N (u : Real)) (etaT E (u : Real)) D <=
    1 + (N : Real)^tauG *
      (9 * Real.exp (Real.sqrt 3) *
        Step2.jS (Gauss.sample d) E D N (u : Real) omega + 2)}

/-- The literal intersection of the four source events. -/
def rawCarrier (E D : Real) (s t : Nat -> Real)
    (zetaSrc zetaCtr tauG : Real) (N : Nat) : Set (Ω d) :=
  APrimeGeneralMovingRawSources.sourceGood E s t zetaSrc N ∩
  Gauss.goodSetFlow d E s t (Gauss.flowDelta d E t) N ∩
  centeredEvent E s t zetaCtr N ∩
  blockEvent E D s t tauG N

/-- A measurable subset of the literal carrier with the same complement measure. -/
noncomputable def commonEvent (E D : Real) (s t : Nat -> Real)
    (zetaSrc zetaCtr tauG : Real) (N : Nat) : Set (Ω d) :=
  Gauss.measCore (Gauss.P d)
    (rawCarrier E D s t zetaSrc zetaCtr tauG N)

end

end RBM.APrimeGeneralMovingCommonSources

namespace RBM.APrimeCrossJointSplit

open RBM.Gauss
noncomputable def transition (d : Gauss.Dims) (E D δ : ℝ)
    (s mesh : ℕ → ℝ) (N k m : ℕ) : Set (Gauss.Ω d) :=
  {ω | 1 < APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω /
    APrimeSmoothWeightActual.threshold δ N ∧
    APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω /
    APrimeSmoothWeightActual.threshold δ N < 2}

end RBM.APrimeCrossJointSplit
