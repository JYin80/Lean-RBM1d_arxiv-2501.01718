/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Gauss
import RBM1D.Gauss.GridStop

/-!
# The grid bootstrap: from a per-endpoint threshold bound to `GridPointwise` — T1520

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.3: the last step of Step 2's route
through the discrete grid (R4c-2a), assembling the discrete continuity argument (T1) with the
deterministic `jSMat → lkErrMat` conversion (T2) into the closing lemmas (T3), (T4).

## Main results

* `below_of_bootstrap`, `firstHit_eq_of_below`, `min_firstHit_eq_of_below` — (T1): if the
  bootstrap step (below threshold at all earlier grid indices implies below threshold now) holds
  at every index up to `K`, the process never reaches the threshold on `[0, K]`, so the grid
  stopping time never fires.
* `lk_le_of_jS` — (T2): the deterministic, pointwise conversion of a `jSMat` bound into an
  `lkErrMat` bound with the decay profile, via `RBM.Step2.le_jStar_mul` (the tautological
  `f ≤ J* T`) and `RBM.Step2.tT_le_decayProf` (the `D`-shift).
* `gridPointwise_of_endpoint` — (T3): `GridPointwise d E s t` from a per-endpoint `HighProb`
  bound on `jSMat` (`hend`), with the grid `K` chosen *before* `δ`.
* `endpoint_of_bootstrap` — (T4): the `HighProb` transfer of (T1) along a `HighProb` event
  family `G`, to the grid endpoint, via `time_last`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-! ### (T1): discrete continuity of the bootstrap step -/

/-- **(T1)** If, for every grid index `k ≤ K`, being below the threshold at all strictly earlier
indices implies being below the threshold at `k`, then the process is below the threshold at
every `k ≤ K`.  Strong induction on `k`. -/
theorem below_of_bootstrap (J θ : ℕ → ℝ) (K : ℕ)
    (hstep : ∀ k ≤ K, (∀ j < k, J j < θ j) → J k < θ k) :
    ∀ k ≤ K, J k < θ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    exact hstep k hk fun j hj => ih j hj (hj.le.trans hk)

/-- **(T1)** If `J` never reaches `θ` up to grid index `K`, the grid stopping time
`firstHit J θ K` never fires: it equals `K`. -/
theorem firstHit_eq_of_below {Ω' : Type*} (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) {ω : Ω'}
    (h : ∀ j ≤ K, J j ω < θ) : firstHit J θ K ω = K := by
  by_contra hne
  have hlt : firstHit J θ K ω < K := lt_of_le_of_ne (firstHit_le J θ K ω) hne
  have hmem : θ ≤ J (firstHit J θ K ω) ω :=
    MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  exact absurd (h _ hlt.le) (not_lt.2 hmem)

/-- **(T1)**, the analogue for the minimum of two grid stopping times: if neither `J` nor `J'`
reaches its own threshold up to grid index `K`, the minimum of their `firstHit`s is also `K`. -/
theorem min_firstHit_eq_of_below {Ω' : Type*} (J J' : ℕ → Ω' → ℝ) (θ θ' : ℝ) (K : ℕ) {ω : Ω'}
    (h : ∀ j ≤ K, J j ω < θ) (h' : ∀ j ≤ K, J' j ω < θ') :
    min (firstHit J θ K ω) (firstHit J' θ' K ω) = K := by
  rw [firstHit_eq_of_below J θ K h, firstHit_eq_of_below J' θ' K h', min_self]

/-! ### (T2): the deterministic pointwise bound from `jSMat` to `lkErrMat` -/

/-- **(T2)** Deterministic, pointwise: a bound `jSMat d E D' N u M ≤ Λ` at loss order
`D' ≥ D + 4`, together with the scale bracket `1 ≤ scale ≤ W²`, converts into the `lkErrMat`
bound with the decay profile at order `D`.  Route: `Step2.le_jStar_mul` (the tautological
`f ≤ J* T`, applied to `jSMat`'s own integrand), `Step2.tT_le_decayProf` (the `D`-shift), and
`Step2.idx_sigPM` (`σ = (+,-)`'s index is `pmLoop`) to identify the integrand with `lkErrMat`.
`M.IsHermitian` is carried for interface parity with `Grid.H` (T3's call site) but is not needed
by the proof: `jSMat`/`lkErrMat` are defined for a general matrix. -/
theorem lk_le_of_jS {E D D' Λ : ℝ} {N : ℕ} {u : ℝ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) (hDD : D + 4 ≤ D')
    (hA1 : 1 ≤ (band d).scale E N u) (hAW : (band d).scale E N u ≤ ((band d).W N : ℝ) ^ 2)
    (hJ : jSMat d E D' N u M ≤ Λ) (a b : ZMod (d.L N)) :
    lkErrMat d E N u M (pmLoop a b)
      ≤ Λ * ((band d).scale E N u)⁻¹ ^ 2 * (band d).decayProf N u D a b := by
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have h1 : (1 : ℝ) ≤ jSMat d E D' N u M :=
    RBM.Step2.one_le_jStar hW0 (fun c => norm_nonneg _)
  have hΛ0 : 0 ≤ Λ := le_trans (le_trans zero_le_one h1) hJ
  have hab0 : (![a, b] : LoopArg (d.L N) 2) 0 = a := by simp
  have hab1 : (![a, b] : LoopArg (d.L N) 2) 1 = b := by simp
  have h0 := RBM.Step2.le_jStar_mul
    (f := fun c => ‖gloop (d.L N) (d.W N) M (zt E u) (LoopData.idx (RBM.Step2.sigPM, c))
        - (band d).Kval E N u (LoopData.idx (RBM.Step2.sigPM, c))‖)
    (ℓu := (band d).ell N u) (ηu := etaT E u) (D := D') hW0 (![a, b] : LoopArg (d.L N) 2)
  simp only [RBM.Step2.idx_sigPM, hab0, hab1] at h0
  have hkey : lkErrMat d E N u M (pmLoop a b)
      ≤ jSMat d E D' N u M * RBM.Step2.tT (band d) E N D' u (zdist (d.L N) (a - b)) := h0
  have htT : RBM.Step2.tT (band d) E N D' u (zdist (d.L N) (a - b))
      ≤ ((band d).scale E N u)⁻¹ ^ 2 * (band d).decayProf N u D a b :=
    RBM.Step2.tT_le_decayProf hDD hA1 hAW a b
  have htT0 : 0 ≤ RBM.Step2.tT (band d) E N D' u (zdist (d.L N) (a - b)) :=
    RBM.tailT_nonneg hW0.le _
  calc lkErrMat d E N u M (pmLoop a b)
      ≤ jSMat d E D' N u M * RBM.Step2.tT (band d) E N D' u (zdist (d.L N) (a - b)) := hkey
    _ ≤ Λ * RBM.Step2.tT (band d) E N D' u (zdist (d.L N) (a - b)) :=
        mul_le_mul_of_nonneg_right hJ htT0
    _ ≤ Λ * (((band d).scale E N u)⁻¹ ^ 2 * (band d).decayProf N u D a b) :=
        mul_le_mul_of_nonneg_left htT hΛ0
    _ = Λ * ((band d).scale E N u)⁻¹ ^ 2 * (band d).decayProf N u D a b := by ring

/-! ### (T3): `GridPointwise` from a per-endpoint `HighProb` bound on `jSMat` -/

/-- **(T3)** `GridPointwise d E s t` from `hend`: for every `D' ≥ 64` and every endpoint sequence
`u`, there is a grid `K` (chosen *before* `δ`: `K` and its `∀ᶠ N, K N + 1 ≤ N^C` card bound sit
outside the `∀ δ ∈ (0, δ₀]` quantifier) along which `jSMat` at the endpoint is, with high
probability, at most `N^δ (η_s/η_u)⁴`.  Route: for a given `D`, `D' := max(D+4,64)`; for the
`StochDom` target `τ`, `δ := min(τ,δ₀)`; (T2) turns the `hend` event into the `lkErrMat` bound
with factor `N^δ ≤ N^τ`; `hend`'s own `∀ D₁ > 0` (from `HighProb`) supplies `StochDom`'s `∀ D₁`.
The scale bracket `1 ≤ scale ≤ W²` (T2's other hypothesis) comes from `SumZeroDyn.flow_crude` +
`Step2.eventually_le_W_sq`, exactly how `Step2.aprioriDecay`'s own proof obtains it. -/
theorem gridPointwise_of_endpoint {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (hend : ∀ D' : ℝ, 64 ≤ D' → ∀ u : ∀ N, TimeIcc s t N,
      ∃ K : ℕ → ℕ, (∀ N, K N ≠ 0) ∧ ∃ C : ℝ, 0 ≤ C ∧
        (∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          HighProb (Pg d) (fun N => {ω | jSMat d E D' N (u N : ℝ)
            (H d s (fun N => (u N : ℝ)) K N (K N) ω)
            ≤ (N : ℝ) ^ δ * (etaT E (s N) / etaT E (u N : ℝ)) ^ 4})) :
    GridPointwise d E s t := by
  intro D hD u
  set D' := max (D + 4) 64 with hD'def
  have hD'64 : (64 : ℝ) ≤ D' := le_max_right _ _
  have hDD : D + 4 ≤ D' := le_max_left _ _
  obtain ⟨K, hK0, C, hC0, hKcard, δ₀, hδ₀pos, hHP⟩ := hend D' hD'64 u
  refine ⟨K, hK0, C, hC0, hKcard, ?_⟩
  have h272 := RBM.Step2.cond272_of_strict hE hst ht1 hc0 hreg
  have hcr := RBM.SumZeroDyn.flow_crude hE hs0 hst ht1 h272
  intro τ hτ Dexp hDexp
  set δ := min τ δ₀ with hδdef
  have hδ0 : 0 < δ := lt_min hτ hδ₀pos
  have hδτ : δ ≤ τ := min_le_left _ _
  have hδδ₀ : δ ≤ δ₀ := min_le_right _ _
  filter_upwards [hHP δ hδ0 hδδ₀ Dexp hDexp, hcr, RBM.Step2.eventually_le_W_sq (band d),
    eventually_ge_atTop 1] with N hHPN hcrN hW2 hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  refine le_trans (measure_mono ?_) hHPN
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  intro hjS
  obtain ⟨p, hp⟩ := hω
  have hM : (H d s (fun N => (u N : ℝ)) K N (K N) ω).IsHermitian :=
    H_isHermitian d s (fun N => (u N : ℝ)) K N (K N) ω
  have hA1 : 1 ≤ (band d).scale E N (u N : ℝ) := (hcrN.2.2.2 (u N)).1
  have hAW : (band d).scale E N (u N : ℝ) ≤ ((band d).W N : ℝ) ^ 2 :=
    (hcrN.2.2.2 (u N)).2.1.trans hW2
  have hlk := lk_le_of_jS d hM hDD hA1 hAW hjS p.1 p.2
  have hδτN : (N : ℝ) ^ δ ≤ (N : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hN1' hδτ
  have hratio0 : (0 : ℝ) ≤ (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 := by positivity
  have hdecay0 : 0 ≤ (band d).decayProf N (u N : ℝ) D p.1 p.2 := by
    unfold Band.decayProf; positivity
  have hstep1 : (N : ℝ) ^ δ * (etaT E (s N) / etaT E (u N : ℝ)) ^ 4
      ≤ (N : ℝ) ^ τ * (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 :=
    mul_le_mul_of_nonneg_right hδτN hratio0
  have hstep2 : (N : ℝ) ^ δ * (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
        ((band d).scale E N (u N : ℝ))⁻¹ ^ 2
      ≤ (N : ℝ) ^ τ * (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
        ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 :=
    mul_le_mul_of_nonneg_right hstep1 (by positivity)
  have hstep3 : (N : ℝ) ^ δ * (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
        ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 * (band d).decayProf N (u N : ℝ) D p.1 p.2
      ≤ (N : ℝ) ^ τ * (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
        ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 * (band d).decayProf N (u N : ℝ) D p.1 p.2 :=
    mul_le_mul_of_nonneg_right hstep2 hdecay0
  have hfinal : lkErrMat d E N (u N : ℝ) (H d s (fun N => (u N : ℝ)) K N (K N) ω)
        (pmLoop p.1 p.2)
      ≤ (N : ℝ) ^ τ * ((etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
        ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 * (band d).decayProf N (u N : ℝ) D p.1 p.2) := by
    refine hlk.trans (le_of_le_of_eq hstep3 ?_)
    ring
  linarith [hfinal, hp]

/-! ### (T4): the `HighProb` transfer of the bootstrap to the grid endpoint -/

/-- **(T4)** The `HighProb` transfer of (T1) to the grid endpoint: given a `HighProb` event
family `G`, on which (for every `N`) the bootstrap step holds for `jSMat`/`Step2.thr` at every
grid index `k ≤ K N`, the endpoint value is, with high probability, below the threshold
`Step2.thr E s δ N (u N) = N^δ (η_s/η_{u N})⁴`.  `time_last` (`K N ≠ 0`) identifies the grid's
last time `u_{K N}` with `u N`. This is (T1) applied pointwise on `G`. -/
theorem endpoint_of_bootstrap {E δ D : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} (hK0 : ∀ N, K N ≠ 0)
    (u : ∀ N, TimeIcc s t N) (G : ℕ → Set (Ωg d)) (hG : HighProb (Pg d) G)
    (hstep : ∀ N, ∀ ω ∈ G N, ∀ k ≤ K N,
      (∀ j < k, jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
          (H d s (fun N => (u N : ℝ)) K N j ω)
        < RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j))
      → jSMat d E D N (time s (fun N => (u N : ℝ)) K N k)
          (H d s (fun N => (u N : ℝ)) K N k ω)
        < RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N k)) :
    HighProb (Pg d) (fun N => {ω | jSMat d E D N (u N : ℝ)
        (H d s (fun N => (u N : ℝ)) K N (K N) ω) ≤ RBM.Step2.thr E s δ N (u N : ℝ)}) := by
  refine hG.mono (Filter.Eventually.of_forall fun N ω hω => ?_)
  have hbelow := below_of_bootstrap
    (J := fun j => jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
      (H d s (fun N => (u N : ℝ)) K N j ω))
    (θ := fun j => RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j))
    (K N) (hstep N ω hω) (K N) le_rfl
  have htime : time s (fun N => (u N : ℝ)) K N (K N) = (u N : ℝ) :=
    time_last s (fun N => (u N : ℝ)) K N (hK0 N)
  rw [htime] at hbelow
  exact hbelow.le

/-! ### Amended (T3′): `GridPointwise'`, with `K` depending on `δ` and `D₁` -/

/-- **Amended (T3′), data: `GridPointwise'`.** The grid-side input with `K` allowed to depend
on the loss exponent `δ ∈ (0, δ₀]` **and** on the target exponent `D₁` (ticket T1520 amend
note, after T1519-amend-1).  For every `D > 0` and every endpoint sequence `u`, there is
`δ₀ > 0` such that for every `δ ∈ (0, δ₀]` and `D₁ > 0` there is a grid `K` (`K N ≠ 0`,
`K N + 1 ≤ N^C` eventually) along which, eventually in `N`, the probability that the last grid
step's `lkErrMat` exceeds `N^δ` times the (2.76) bound at some label pair is `≤ N^{-D₁}`.
The bad set is literally `RBM.badSet` at exponent `δ` for T1517's `GridPointwise` integrand and
bound. -/
def GridPointwise' (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ u : ∀ N, TimeIcc s t N,
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ D₁ : ℝ, 0 < D₁ →
      ∃ K : ℕ → ℕ, (∀ N, K N ≠ 0) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) ∧
        ∀ᶠ N : ℕ in atTop, Pg d {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
          (N : ℝ) ^ δ * ((etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
            ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 * (band d).decayProf N (u N : ℝ) D p.1 p.2)
          < lkErrMat d E N (u N : ℝ) (H d s (fun N => (u N : ℝ)) K N (K N) ω)
            (pmLoop p.1 p.2)}
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁))

/-- **The per-`N` transfer of a bad-set probability** from the grid (at the last grid step
`k = K N`) to the flow at `uR N`: both events are preimages of one measurable matrix set, and
`map_H_eq` at `k = K N` with `time_last` identifies the two image laws.  Only this single `N` is
involved, so `K` may depend on anything that does not depend on `ω`. -/
theorem pg_bad_eq_flow {E δ : ℝ} {s uR : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (hs0 : 0 ≤ s N)
    (hsu : s N ≤ uR N) (hK : K N ≠ 0) (ζ : ZMod (d.L N) × ZMod (d.L N) → ℝ) :
    Pg d {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
        (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) (H d s uR K N (K N) ω) (pmLoop p.1 p.2)}
      = RBM.Gauss.P d {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
        (N : ℝ) ^ δ * ζ p < (sample d).lkErr E N (uR N) ω (pmLoop p.1 p.2)} := by
  set S : Set (Matrix (d.Idx N) (d.Idx N) ℂ) := {M | ∃ p : ZMod (d.L N) × ZMod (d.L N),
    (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) M (pmLoop p.1 p.2)} with hSdef
  have hS : MeasurableSet S := by
    have heq : S = ⋃ p : ZMod (d.L N) × ZMod (d.L N),
        {M | (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) M (pmLoop p.1 p.2)} := by
      ext M; simp [hSdef]
    rw [heq]
    exact MeasurableSet.iUnion fun p =>
      measurableSet_lt measurable_const (measurable_lkErrMat d E N (uR N) (pmLoop p.1 p.2))
  have hmap : (Pg d).map (H d s uR K N (K N)) = (RBM.Gauss.P d).map (Hflow d N (uR N)) := by
    have h := map_H_eq (d := d) s uR K N (K N) hs0 hsu hK
    rwa [time_last s uR K N hK] at h
  have hHm : Measurable (H d s uR K N (K N)) :=
    (H_measurable_filt d s uR K N (K N)).mono ((filt d).le (K N)) le_rfl
  have hFm : Measurable (Hflow d N (uR N)) := RBM.measurable_H (sample d) N (uR N)
  have e1 : {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
      (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) (H d s uR K N (K N) ω) (pmLoop p.1 p.2)}
      = H d s uR K N (K N) ⁻¹' S := rfl
  have e2 : {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
      (N : ℝ) ^ δ * ζ p < (sample d).lkErr E N (uR N) ω (pmLoop p.1 p.2)}
      = Hflow d N (uR N) ⁻¹' S := rfl
  rw [e1, e2, ← Measure.map_apply hHm hS, ← Measure.map_apply hFm hS, hmap]

/-- **Amended (T3′): `hpt` from `GridPointwise'`.** h276's pointwise input `hpt` (the `hpt`
binder of T1517's `step2_gauss_of_pointwise`) from `GridPointwise'`.  For StochDom's target `τ`,
take `δ := min(τ, δ₀)`; the grid bad set at `δ` (with its own `K = K(δ, D₁)`) has, for each `N`
separately, the same probability as the flow bad set at `δ` (`pg_bad_eq_flow`, i.e. `map_H_eq`
at `k = K N` + `time_last`), which contains the flow bad set at `τ` since `N^δ ≤ N^τ`.  The flow
event does not involve `K`. -/
theorem hpt_of_gridPointwise' {E : ℝ} {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hG : GridPointwise' d E s t) :
    ∀ D : ℝ, 0 < D → ∀ u : ∀ N, TimeIcc s t N, StochDom (RBM.Gauss.P d)
      (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
        (sample d).lkErr E N (u N) ω (pmLoop p.1 p.2))
      (fun N p _ => (etaT E (s N) / etaT E (u N)) ^ 4 *
        ((band d).scale E N (u N))⁻¹ ^ 2 * (band d).decayProf N (u N) D p.1 p.2) := by
  intro D hD u
  obtain ⟨δ₀, hδ₀, hG'⟩ := hG D hD u
  intro τ hτ D₁ hD₁
  obtain ⟨K, hK0, -, hbad⟩ := hG' (min τ δ₀) (lt_min hτ hδ₀) (min_le_right _ _) D₁ hD₁
  filter_upwards [hbad, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  rw [pg_bad_eq_flow d (E := E) (δ := min τ δ₀) (uR := fun N => (u N : ℝ)) (hs0 N) (u N).2.1
    (hK0 N) (fun p => (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
      ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 * (band d).decayProf N (u N : ℝ) D p.1 p.2)] at hN
  refine le_trans (measure_mono ?_) hN
  intro ω hω
  obtain ⟨p, hp⟩ := hω
  refine ⟨p, lt_of_le_of_lt ?_ hp⟩
  have hr0 : (0 : ℝ) ≤ (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 := by positivity
  have hsc0 : (0 : ℝ) ≤ ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 := by positivity
  have hdp0 : 0 ≤ (band d).decayProf N (u N : ℝ) D p.1 p.2 := by
    unfold Band.decayProf; positivity
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN1' (min_le_left _ _))
    (mul_nonneg (mul_nonneg hr0 hsc0) hdp0)

/-- **Amended (T3′): `Step2.step2`'s conclusion for `sample d` under `GridPointwise'`** —
T1517's `step2_gauss_of_pointwise` composed with `hpt_of_gridPointwise'`.  Hypotheses and
conclusion are those of T1517's `step2_gauss_of_grid`, with `GridPointwise` replaced by
`GridPointwise'`; the conclusion is syntactically `Step2.step2`'s at `X := sample d`. -/
theorem step2_gauss_of_gridPointwise' {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ}
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (hgp : GridPointwise' d E s t) :
    StochDom (band d).P
      (fun N (p : TimeIcc s t N × ((band d).Idx N × (band d).Idx N)) ω =>
        (sample d).llErr E N p.1 ω p.2)
      (fun N p _ => ((band d).scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * ((band d).scale E N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) :=
  step2_gauss_of_pointwise d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg
    (hpt_of_gridPointwise' d hs0 hgp)

/-- **`GridPointwise ⇒ GridPointwise'`** (non-vacuity of `GridPointwise'`): take `δ₀ := 1` and,
for every `(δ, D₁)`, the same `K, C`; the event bound is `StochDom`'s at exponent `δ` and target
`D₁`, since `GridPointwise'`'s bad set is literally `RBM.badSet … δ N`. -/
theorem gridPointwise'_of_gridPointwise {E : ℝ} {s t : ℕ → ℝ} (hG : GridPointwise d E s t) :
    GridPointwise' d E s t := by
  intro D hD u
  obtain ⟨K, hK0, C, hC0, hKcard, hSD⟩ := hG D hD u
  exact ⟨1, one_pos, fun δ hδ _ D₁ hD₁ => ⟨K, hK0, ⟨C, hC0, hKcard⟩, hSD δ hδ D₁ hD₁⟩⟩

/-- **`GridPointwise'` is not vacuous**: it follows from `Step2.step2`'s own second conjunct
(2.76) for `sample d` (with the full label set and step2's window), via the trivial one-step
grid `K := 1` (`stochDom_grid_iff_flow`) and `gridPointwise'_of_gridPointwise`. -/
example {E : ℝ} {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hconcl : ∀ D : ℝ, 0 < D → StochDom (RBM.Gauss.P d)
      (fun N (p : TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) ω =>
        (sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * ((band d).scale E N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2)) :
    GridPointwise' d E s t := by
  refine gridPointwise'_of_gridPointwise d ?_
  intro D hD u
  refine ⟨fun _ => 1, fun _ => one_ne_zero, 1, zero_le_one, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [show ((1 + 1 : ℕ) : ℝ) = 2 by norm_num, Real.rpow_one]
    exact hN2
  · have hpoint := (hconcl D hD).precomp_param
      (fun N (p : ZMod (d.L N) × ZMod (d.L N)) => (u N, p))
    exact (stochDom_grid_iff_flow d E s (fun N => (u N : ℝ)) (fun _ => 1) hs0
      (fun N => (u N).2.1) (fun _ => one_ne_zero)
      (fun N p => (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
        ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 *
        (band d).decayProf N (u N : ℝ) D p.1 p.2)).2 hpoint

/-! ### Amended (T4′): the bootstrap only at the random target `τ` -/

/-- **Amended (T4′), deterministic core.** Let `τ ω := min (firstHit (J − θ) 0 K ω)
(firstHit J' θ' K ω)`.  If the second process never reaches its level up to `K` and
`J τ < θ τ` holds at the random target, then `τ ω = K`: otherwise the first `firstHit` is `< K`,
and the hitting property gives `J τ ≥ θ τ`. -/
theorem min_firstHit_eq_of_at {Ω' : Type*} (J J' : ℕ → Ω' → ℝ) (θ : ℕ → ℝ) (θ' : ℝ) (K : ℕ)
    {ω : Ω'} (hgood : ∀ j ≤ K, J' j ω < θ')
    (hat : J (min (firstHit (fun j ω => J j ω - θ j) 0 K ω) (firstHit J' θ' K ω)) ω
      < θ (min (firstHit (fun j ω => J j ω - θ j) 0 K ω) (firstHit J' θ' K ω))) :
    min (firstHit (fun j ω => J j ω - θ j) 0 K ω) (firstHit J' θ' K ω) = K := by
  have hb : firstHit J' θ' K ω = K := firstHit_eq_of_below J' θ' K hgood
  have haK : firstHit (fun j ω => J j ω - θ j) 0 K ω ≤ K := firstHit_le _ _ _ _
  rw [hb, min_eq_left haK] at hat ⊢
  by_contra hne
  have hlt : firstHit (fun j ω => J j ω - θ j) 0 K ω < K := lt_of_le_of_ne haK hne
  have hmem : (0 : ℝ) ≤ J (firstHit (fun j ω => J j ω - θ j) 0 K ω) ω
      - θ (firstHit (fun j ω => J j ω - θ j) 0 K ω) :=
    MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  linarith

/-- **Amended (T4′) `endpoint_of_bootstrap'`: the bootstrap only at the random target.** The grid
stopping time is
`τ ω := min (firstHit (j ↦ J_j − thr(u_j)) 0 (K N) ω) (firstHit (J' N) θ' (K N) ω)`,
with `J_j ω := jSMat d E D N u_j (H_j ω)`; with `J' N j := 1_{goodSet(u_j)ᶜ}(H_j)` and `θ' := 1/2`
this is definitionally T1519's `gridTau` (for the endpoint `fun N => (u N : ℝ)`).  Given a
`HighProb` family `G` on which the second process never fires (`hgood`: the good set holds at
every `j ≤ K N`) and `J_τ < thr(u_τ)` at the random target (`hat`), with high probability
`τ = K N` and `J_{K N} < thr(u N)` (`u_{K N} = u N` by `time_last`). -/
theorem endpoint_of_bootstrap' {E δ D θ' : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} (hK0 : ∀ N, K N ≠ 0)
    (u : ∀ N, TimeIcc s t N) (J' : ℕ → ℕ → Ωg d → ℝ) (G : ℕ → Set (Ωg d))
    (hG : HighProb (Pg d) G)
    (hgood : ∀ N, ∀ ω ∈ G N, ∀ j ≤ K N, J' N j ω < θ')
    (hat : ∀ N, ∀ ω ∈ G N,
      jSMat d E D N (time s (fun N => (u N : ℝ)) K N
          (min (firstHit (fun j ω => jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
              (H d s (fun N => (u N : ℝ)) K N j ω)
              - RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j)) 0 (K N) ω)
            (firstHit (J' N) θ' (K N) ω)))
        (H d s (fun N => (u N : ℝ)) K N
          (min (firstHit (fun j ω => jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
              (H d s (fun N => (u N : ℝ)) K N j ω)
              - RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j)) 0 (K N) ω)
            (firstHit (J' N) θ' (K N) ω)) ω)
      < RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N
          (min (firstHit (fun j ω => jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
              (H d s (fun N => (u N : ℝ)) K N j ω)
              - RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j)) 0 (K N) ω)
            (firstHit (J' N) θ' (K N) ω)))) :
    HighProb (Pg d) (fun N => {ω |
      min (firstHit (fun j ω => jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
          (H d s (fun N => (u N : ℝ)) K N j ω)
          - RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j)) 0 (K N) ω)
        (firstHit (J' N) θ' (K N) ω) = K N ∧
      jSMat d E D N (u N : ℝ) (H d s (fun N => (u N : ℝ)) K N (K N) ω)
        < RBM.Step2.thr E s δ N (u N : ℝ)}) := by
  refine hG.mono (Filter.Eventually.of_forall fun N ω hω => ?_)
  have heq : min (firstHit (fun j ω => jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
          (H d s (fun N => (u N : ℝ)) K N j ω)
          - RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j)) 0 (K N) ω)
        (firstHit (J' N) θ' (K N) ω) = K N :=
    min_firstHit_eq_of_at
      (fun j ω => jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
        (H d s (fun N => (u N : ℝ)) K N j ω)) (J' N)
      (fun j => RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j)) θ' (K N)
      (hgood N ω hω) (hat N ω hω)
  refine ⟨heq, ?_⟩
  have h := hat N ω hω
  rw [heq, time_last s (fun N => (u N : ℝ)) K N (hK0 N)] at h
  exact h

/-- **(T4′) hypotheses are weaker than the old (T4)'s**: the old all-`k` bootstrap on `G`
(`endpoint_of_bootstrap`'s `hstep`) gives `hat` at the random target (any `τ ≤ K N`), so every
instance of the old (T4) is an instance of (T4′). -/
example {E δ D θ' : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} (u : ∀ N, TimeIcc s t N)
    (J' : ℕ → ℕ → Ωg d → ℝ) (G : ℕ → Set (Ωg d))
    (hstep : ∀ N, ∀ ω ∈ G N, ∀ k ≤ K N,
      (∀ j < k, jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
          (H d s (fun N => (u N : ℝ)) K N j ω)
        < RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j))
      → jSMat d E D N (time s (fun N => (u N : ℝ)) K N k)
          (H d s (fun N => (u N : ℝ)) K N k ω)
        < RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N k))
    (N : ℕ) (ω : Ωg d) (hω : ω ∈ G N) :
    jSMat d E D N (time s (fun N => (u N : ℝ)) K N
        (min (firstHit (fun j ω => jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
            (H d s (fun N => (u N : ℝ)) K N j ω)
            - RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j)) 0 (K N) ω)
          (firstHit (J' N) θ' (K N) ω)))
      (H d s (fun N => (u N : ℝ)) K N
        (min (firstHit (fun j ω => jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
            (H d s (fun N => (u N : ℝ)) K N j ω)
            - RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j)) 0 (K N) ω)
          (firstHit (J' N) θ' (K N) ω)) ω)
    < RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N
        (min (firstHit (fun j ω => jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
            (H d s (fun N => (u N : ℝ)) K N j ω)
            - RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j)) 0 (K N) ω)
          (firstHit (J' N) θ' (K N) ω))) :=
  below_of_bootstrap
    (fun j => jSMat d E D N (time s (fun N => (u N : ℝ)) K N j)
      (H d s (fun N => (u N : ℝ)) K N j ω))
    (fun j => RBM.Step2.thr E s δ N (time s (fun N => (u N : ℝ)) K N j))
    (K N) (hstep N ω hω) _ ((min_le_left _ _).trans (firstHit_le _ _ _ _))

end RBM.Gauss.Grid
