/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridGoodEvent
import RBM1D.Gauss.GridStopFilt
import RBM1D.Gauss.GridBootstrap
import RBM1D.Gauss.LoopDecayFixed
import RBM1D.Gauss.OneLoopSharpGrid
import RBM1D.Gauss.Step2Plain

/-!
# The (+,+) good set, good-set-exit stopping time, initial value

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.6: **no threshold stopping time** anywhere for the (+,+) bootstrap.  The bootstrap
itself is a good-set stopping time plus a deterministic induction along the grid
(`RBM1D/Gauss/PPInduction.lean`); this file supplies the good set, the good-set-exit stopping
time and the good event.

## Design notes

* `goodSetPP d E N v ε Kd D` has exactly the four bare-real parameters `(v, ε, Kd, D)`. `Kd` plays
  the role of the reference scale `ℓ_s := (band d).ell N (s N)` that `(G2)`/`(G3)` need (exactly as
  `goodSet`/`eq273Set` take a bare real `ℓs`, filled in by the caller); `ε` is reused both as the
  `N^ε` loss exponent of `(G1)`–`(G3)` and as the decay-radius exponent `τ` of Definition 5.8 in
  `(G4)` (both roles only need *some* positive real, so sharing one value adds no hypothesis and
  loses nothing); `D` is `(G4)`'s tail exponent, verbatim `D`.
* `(G4)` uses loop-length cap `m₀ := 6` in `decaySet`/`lkDecaySet`: `Decay.LoopDecay` quantifies
  "every length `≤ m₀`", so `m₀ = 6` gives simultaneous decay at lengths 1,…,6, in particular at
  the lengths `{2,3,6}` that are used — a stronger, not weaker, statement, and one `m₀`
  covers both `L` and `L−K`.
* **No threshold stopping time.** `JPP` (the quantity bounded in `RBM1D/Gauss/PPInduction.lean`)
  is defined independently of
  `tauPP`; `tauPP` is the *single* `firstHit` of the good-set-exit indicator, with no `min`.
  `JPP` occurs nowhere in `tauPP` or `lt_tauPP_imp`.

## Main results

* `sigPP` — `σ = (+,+)`.
* `xiOnePP` (`(G1)`), `goodSetPP` (`(G1)`–`(G4)`), both measurable unconditionally.
* `JPP`, `measurable_JPP` — the quantity bounded in `RBM1D/Gauss/PPInduction.lean`, defined
  independently of `tauPP`.
* `tauPP`, `lt_tauPP_imp` — the good-set-exit stopping time only, **no** `min`, **no**
  threshold on `JPP`.
* `goodEventPP`, `goodEvent_pp_imp` — the good event bundles only the
  good-set-exit event and (T4)'s initial bound; on it, the good set holds at every `j ≤ K`
  (so `tauPP = K`), and (T4) holds.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-- `σ = (+,+)`: both edges of the loop carry the same charge. -/
def sigPP : Fin 2 → Bool := ![true, true]

/-! ## (T1) : `goodSetPP` -/

section GoodSetPP

variable (E : ℝ) (N : ℕ) (v ε Kd D : ℝ)

/-- **(G1)** The sharp one-loop bound `Ξ^{(L−K)}_{v,1} ≤ N^ε`, both charges
(`LoopData (d.L N) 1 = Bool × ZMod (d.L N)` ranges over both signs). -/
def xiOnePP : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | ∀ w : LoopData (d.L N) 1, (band d).scale E N v * lkErrMat d E N v M w.idx ≤ (N : ℝ) ^ ε}

theorem measurableSet_xiOnePP : MeasurableSet (xiOnePP d E N v ε) := by
  have heq : xiOnePP d E N v ε = ⋂ w : LoopData (d.L N) 1,
      {M | (band d).scale E N v * lkErrMat d E N v M w.idx ≤ (N : ℝ) ^ ε} := by
    unfold xiOnePP; ext M; simp
  rw [heq]
  exact MeasurableSet.iInter fun w =>
    measurableSet_le ((measurable_lkErrMat d E N v w.idx).const_mul _) measurable_const

/-- **`goodSetPP`**: `(G1) ∩ (G2) ∩ (G3) ∩ (G4)`. `(G2)`/`(G3)` are (2.73) at loop length
`3, 6` (`eq273Set`, `GridJStar.lean`); `(G4)` is Definition 5.8's `(v,ε,D)`-decay of `L`
and `L−K` at every length `≤ 6` (`decaySet`/`lkDecaySet`, `LoopDecayFixed.lean`). -/
def goodSetPP : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  xiOnePP d E N v ε ∩ eq273Set d E N 3 v Kd ε ∩ eq273Set d E N 6 v Kd ε ∩
    decaySet d E N 6 v ε D ∩ lkDecaySet d E N 6 v ε D

/-- `goodSetPP` is measurable, unconditionally (no `|E| < 2` is needed anywhere: unlike
`goodSet`, none of `(G1)`–`(G4)` uses `Gsig`/`mSigma`). -/
theorem measurableSet_goodSetPP : MeasurableSet (goodSetPP d E N v ε Kd D) :=
  ((((measurableSet_xiOnePP d E N v ε).inter (measurableSet_eq273Set d E N 3 v Kd ε)).inter
    (measurableSet_eq273Set d E N 6 v Kd ε)).inter
    (measurableSet_decaySet d E N 6 v ε D)).inter (measurableSet_lkDecaySet d E N 6 v ε D)

end GoodSetPP

/-! ## `JPP`, defined independently of `tauPP` -/

section JPP

variable (E : ℝ) (N : ℕ) (v : ℝ)

/-- **`JPP`**: `A_v² · max_a |(L−K)_{v,σ_pp,a}(M)|`, the quantity `J_j` that
`RBM1D/Gauss/PPInduction.lean` bounds by a deterministic induction along the grid. Defined here only
as data — **it is not combined with any threshold or `firstHit` in this file.** -/
def JPP (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  (band d).scale E N v ^ 2 * Finset.univ.sup' Finset.univ_nonempty
    (fun a : LoopArg (d.L N) 2 => lkErrMat d E N v M (LoopData.idx (sigPP, a)))

theorem measurable_JPP : Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => JPP d E N v M) := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (a : LoopArg (d.L N) 2) (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
        lkErrMat d E N v M (LoopData.idx (sigPP, a)))) :=
    Finset.measurable_sup' Finset.univ_nonempty
      fun a _ => measurable_lkErrMat d E N v (LoopData.idx (sigPP, a))
  have heq : (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => JPP d E N v M) = fun M =>
      (band d).scale E N v ^ 2 * (Finset.univ.sup' Finset.univ_nonempty
        (fun (a : LoopArg (d.L N) 2) (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
          lkErrMat d E N v M (LoopData.idx (sigPP, a)))) M := by
    funext M
    unfold JPP
    rw [Finset.sup'_apply]
  rw [heq]
  exact measurable_const.mul hsup

end JPP

/-! ## The grid `HighProb` of `goodSetPP`, from (2.73) -/

/-! ## `tauPP`, the good-set-exit stopping time only -/

section TauPP

/-- **`tauPP`**: the first grid index at which the grid state leaves `goodSetPP`
(`K N` if it never does). A *single* `firstHit` — **no** `min`, **no** threshold on `JPP`. -/
def tauPP (E ε Kd D : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (ω : Ωg d) : ℕ :=
  firstHit (fun j (ω' : Ωg d) =>
    (goodSetPP d E N (time s u K N j) ε Kd D)ᶜ.indicator (fun _ => (1 : ℝ)) (H d s u K N j ω'))
    (1 / 2) (K N) ω

/-- **(T3)** Strictly before `tauPP`, the grid state is in `goodSetPP`. -/
theorem lt_tauPP_imp {E ε Kd D : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ} {ω : Ωg d}
    (h : j < tauPP d E ε Kd D s u K N ω) :
    H d s u K N j ω ∈ goodSetPP d E N (time s u K N j) ε Kd D := by
  have h1 : (goodSetPP d E N (time s u K N j) ε Kd D)ᶜ.indicator (fun _ => (1 : ℝ))
      (H d s u K N j ω) < 1 / 2 :=
    lt_firstHit_imp
      (fun j' (ω' : Ωg d) => (goodSetPP d E N (time s u K N j') ε Kd D)ᶜ.indicator
        (fun _ => (1 : ℝ)) (H d s u K N j' ω'))
      (1 / 2) (K N) h
  by_contra hmem
  rw [Set.indicator_of_mem (Set.mem_compl hmem)] at h1
  norm_num at h1

end TauPP

/-! ## (T4) : the initial value, (2.68) at `s`, both charges -/

/-! ## `goodEventPP`, the good-set exit only -/

/-- **`goodEventPP`**: the good-set event (the grid state in `goodSetPP` at every grid index)
intersected with (T4)'s initial bound — no Azuma/Chebyshev tail (there is no threshold half). -/
def goodEventPP (E ε Kd D : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) : Set (Ωg d) :=
  {ω | ∀ k : Fin (K N + 1), H d s t K N k ω ∈ goodSetPP d E N (time s t K N k) ε Kd D} ∩
    {ω | JPP d E N (time s t K N 0) (H d s t K N 0 ω) ≤ (N : ℝ) ^ ε}

/-- **`goodEvent_pp_imp`**: on `goodEventPP`, the good set holds at every `j ≤ K N` (so
`tauPP = K N`, via `firstHit_eq_of_below`), and (T4)'s initial bound holds. -/
theorem goodEvent_pp_imp {E ε Kd D : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} {ω : Ωg d}
    (hω : ω ∈ goodEventPP d E ε Kd D s t K N) :
    (∀ j ≤ K N, H d s t K N j ω ∈ goodSetPP d E N (time s t K N j) ε Kd D) ∧
      tauPP d E ε Kd D s t K N ω = K N ∧
      JPP d E N (time s t K N 0) (H d s t K N 0 ω) ≤ (N : ℝ) ^ ε := by
  obtain ⟨hgood, hinit⟩ := hω
  have hgood' : ∀ j ≤ K N, H d s t K N j ω ∈ goodSetPP d E N (time s t K N j) ε Kd D :=
    fun j hj => hgood ⟨j, by omega⟩
  refine ⟨hgood', ?_, hinit⟩
  unfold tauPP
  refine firstHit_eq_of_below _ (1 / 2) (K N) fun j hj => ?_
  have hmem := hgood' j hj
  have hnotmem : H d s t K N j ω ∉ (goodSetPP d E N (time s t K N j) ε Kd D)ᶜ :=
    fun hc => hc hmem
  rw [Set.indicator_of_notMem hnotmem]
  norm_num

end RBM.Gauss.Grid

end

