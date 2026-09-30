/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridStopFilt
import RBM1D.Gauss.EntryBoundTime
import RBM1D.Hierarchy.Step2Near47
import RBM1D.Gauss.Step6Hyp
import Mathlib.Analysis.Calculus.Deriv.Abs
import RBM1D.Hierarchy.DriftDef
import RBM1D.Gauss.MomentDuhamelGauss
import RBM1D.Gauss.TestFunHerm
import RBM1D.Gauss.WeightedSumSqrt
import RBM1D.Gauss.EarlyQVRate
import RBM1D.Flow.FirstCell
import RBM1D.Gauss.EarlyQVRateEv
import RBM1D.Gauss.Lemma514Moment
import RBM1D.Gauss.QVEndpoint
import RBM1D.Gauss.GoodSetFlow
import RBM1D.Gauss.MinorDiffCond
import RBM1D.Gauss.Step2JStar
import RBM1D.Defs.MatrixMeasurable

/-!
# `J*` on the grid: `jSMat` and the matrix-set forms of σ's inputs

The interface between the paper's `J*_{u,D}` (`RBM.Step2.jS`, defined through a `Sample`'s
Green's function) and the discrete grid path `RBM.Gauss.Grid.H`.

## Main results

* `jSMat`, `jS_eq_jSMat` — `jSMat` is `Step2.jS` taking the matrix directly, and it is the
  exact same formula (the equation is `rfl`).
* `measurable_jSMat` — `jSMat E D N u` is measurable on the whole matrix space (the
  prerequisite for the grid stopping times).
* `highProb_grid_of_flow` — the transfer of a flow-level `HighProb` statement to the grid, via
  `map_H_eq`.
* `eq273Set`, `eq557Set` — the matrix-set forms of `(2.73)` and `(5.57)`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-! ### T2 (building blocks): the matrix inverse / loop chain is measurable, unconditionally

`green`, `Gsig`, `gloopProd`, `gloop` are functions of an **arbitrary** matrix `M`
(`Matrix (d.Idx N) (d.Idx N) ℂ`), not only of Hermitian matrices reached along the flow. The
resolvent `green M z = (M - z • 1)⁻¹` is *not* continuous at singular `M` (continuity there needs
`M` Hermitian and `z.im ≠ 0`, `RBM.Gauss.continuous_green_comp`), but it *is* measurable
everywhere: `Matrix.inv` unfolds to `Ring.inverse (det M) • adjugate M`, with `det`/`adjugate`
continuous and `Ring.inverse = (·)⁻¹` measurable on `ℂ`
(`RBM.Gauss.measurable_matrix_inv_apply`). This section proves that `green`, `Gsig`,
`gloopProd` and `gloop` are measurable as functions of the matrix itself, so the results apply
to every matrix, not only to matrices of the form `X.H N u ω` along a sample. -/

section MeasurableMatrixOps

variable (N : ℕ)

private theorem measurable_sub_smul_one_matrix (z : ℂ) :
    Measurable fun M : Matrix (d.Idx N) (d.Idx N) ℂ => M - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) :=
  (continuous_id.sub continuous_const).measurable

/-- Entries of the resolvent `G = (M - z)⁻¹` are measurable in the matrix `M`, unconditionally
(no Hermitian hypothesis: this is global measurability on the whole matrix space, not continuity
at a Hermitian point). -/
theorem measurable_green_matrix (z : ℂ) (i j : d.Idx N) :
    Measurable fun M : Matrix (d.Idx N) (d.Idx N) ℂ => green M z i j :=
  Gauss.measurable_matrix_inv_apply (measurable_sub_smul_one_matrix d N z) i j

/-- The same for `G(σ)` of Definition 2.9 (`z` for `σ = +`, `z̄` for `σ = -`). -/
theorem measurable_Gsig_matrix (z : ℂ) (σ : Bool) (i j : d.Idx N) :
    Measurable fun M : Matrix (d.Idx N) (d.Idx N) ℂ => Gsig M z σ i j := by
  cases σ
  · simpa [Gsig] using measurable_green_matrix d N ((starRingEnd ℂ) z) i j
  · simpa [Gsig] using measurable_green_matrix d N z i j

/-- Entries of a product of two matrix-valued maps with measurable entries are measurable
(`(AC)_{ij} = ∑_k A_{ik}C_{kj}`, a finite sum). -/
private theorem measurable_mul_matrix {ι : Type*} [Fintype ι]
    {Θ : Type*} [MeasurableSpace Θ] {A C : Θ → Matrix ι ι ℂ}
    (hA : ∀ i j, Measurable fun x => A x i j) (hC : ∀ i j, Measurable fun x => C x i j)
    (i j : ι) : Measurable fun x => (A x * C x) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hC k j)

/-- Entries of the loop product `∏_i G(σ_i)E_{a_i}` of (2.41) are measurable in the matrix `M`.
The induction is on the zipped charge/label list that `RBM.gloopProd` folds over; `RBM.Eblk` is
deterministic. -/
theorem measurable_gloopProd_matrix (z : ℂ) (I : LoopIdx (ZMod (d.L N))) (i j : d.Idx N) :
    Measurable fun M : Matrix (d.Idx N) (d.Idx N) ℂ => gloopProd (d.L N) (d.W N) M z I i j := by
  suffices h : ∀ l : List (Bool × ZMod (d.L N)), ∀ i j : d.Idx N,
      Measurable fun M : Matrix (d.Idx N) (d.Idx N) ℂ => (l.foldr
        (fun (p : Bool × ZMod (d.L N)) (Acc : Matrix (d.Idx N) (d.Idx N) ℂ) =>
          Gsig M z p.1 * Eblk (d.L N) (d.W N) p.2 * Acc)
        (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j by
    simpa [gloopProd] using h (I.σ.zip I.a) i j
  intro l
  induction l with
  | nil => intro i j; simp
  | cons p l ih =>
      intro i j
      simp only [List.foldr_cons]
      refine measurable_mul_matrix ?_ (fun a b => ih a b) i j
      intro a b
      refine measurable_mul_matrix (fun c e => measurable_Gsig_matrix d N z p.1 c e)
        (C := fun _ => Eblk (d.L N) (d.W N) p.2) (fun _ _ => measurable_const) a b

/-- **The `G`-loop is measurable in the matrix `M`**, unconditionally: the trace of the loop
product, a finite sum of diagonal entries. -/
theorem measurable_gloop_matrix (z : ℂ) (I : LoopIdx (ZMod (d.L N))) :
    Measurable fun M : Matrix (d.Idx N) (d.Idx N) ℂ => gloop (d.L N) (d.W N) M z I := by
  have h : ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, gloop (d.L N) (d.W N) M z I
      = ∑ i : d.Idx N, gloopProd (d.L N) (d.W N) M z I i i := fun _ => rfl
  simp only [h]
  exact Finset.measurable_sum _ fun i _ => measurable_gloopProd_matrix d N z I i i

end MeasurableMatrixOps

/-! ### T1 : `jSMat`, the matrix form of `Step2.jS` -/

/-- **(T1)** `jSMat E D N u M` is `Step2.jS`'s formula with the matrix `M` taken directly as
input, instead of going through a `Sample`'s `ω`. -/
def jSMat (E D : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  RBM.Step2.jStar (d.L N)
    (fun a => ‖gloop (d.L N) (d.W N) M (zt E u) (LoopData.idx (RBM.Step2.sigPM, a))
        - (band d).Kval E N u (LoopData.idx (RBM.Step2.sigPM, a))‖)
    (d.W N) ((band d).ell N u) (etaT E u) D

/-- `jSMat` is measurable, unconditionally on the whole matrix space — the prerequisite
for the grid stopping times of `Gauss/GridStopFilt.lean`. -/
theorem measurable_jSMat (E D : ℝ) (N : ℕ) (u : ℝ) : Measurable (jSMat d E D N u) := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (a : LoopArg (d.L N) 2) (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
        ‖gloop (d.L N) (d.W N) M (zt E u) (LoopData.idx (RBM.Step2.sigPM, a))
            - (band d).Kval E N u (LoopData.idx (RBM.Step2.sigPM, a))‖
          / tailT (d.W N) ((band d).ell N u) (etaT E u) D
            (zdist (d.L N) (a 0 - a 1)))) :=
    Finset.measurable_sup' Finset.univ_nonempty fun a _ =>
      (((measurable_gloop_matrix d N (zt E u)
        (LoopData.idx (RBM.Step2.sigPM, a))).sub measurable_const).norm).div_const _
  have heq : jSMat d E D N u = Finset.univ.sup' Finset.univ_nonempty
      (fun (a : LoopArg (d.L N) 2) (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
        ‖gloop (d.L N) (d.W N) M (zt E u) (LoopData.idx (RBM.Step2.sigPM, a))
            - (band d).Kval E N u (LoopData.idx (RBM.Step2.sigPM, a))‖
          / tailT (d.W N) ((band d).ell N u) (etaT E u) D
            (zdist (d.L N) (a 0 - a 1))) + fun _ => (1 : ℝ) := by
    funext M
    simp only [Pi.add_apply, Finset.sup'_apply]
    rfl
  rw [heq]
  exact hsup.add measurable_const

/-- **(T1)** `jSMat` evaluated at `Hflow d N u ω` is literally `Step2.jS (sample d) E D N u ω`:
`Sample.Lval` for `sample d` unfolds to `gloop` applied to `Hflow d N u ω`, and `(band d).L N`,
`(band d).W N` reduce to `d.L N`, `d.W N` by structure projection. -/
theorem jS_eq_jSMat (E D : ℝ) (N : ℕ) (u : ℝ) (ω : Ω d) :
    RBM.Step2.jS (sample d) E D N u ω = jSMat d E D N u (Hflow d N u ω) := rfl

/-! ### T3 : the single-time law transfer to the grid -/

/-! ### Matrix-set forms of single-time inputs, transferred to the grid

`(2.73)` and `(5.57)`. -/

/-- `time s t K N k ∈ [s N, t N]` for `k ≤ K N`, so that a continuum-uniform (`∀ u ∈ [s N, t N]`)
statement specializes to every grid time. -/
theorem mem_Icc_time (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ)
    (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (hk : k ≤ K N) :
    time s t K N k ∈ Set.Icc (s N) (t N) := by
  rcases Nat.eq_zero_or_pos (K N) with h0 | h0
  · have hk0 : k = 0 := by omega
    subst hk0
    rw [time_zero]
    exact ⟨le_rfl, hst⟩
  · have hstep0 : 0 ≤ step s t K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
    have hkR : (k : ℝ) ≤ (K N : ℝ) := by exact_mod_cast hk
    have hmulle : (k : ℝ) * step s t K N ≤ (K N : ℝ) * step s t K N :=
      mul_le_mul_of_nonneg_right hkR hstep0
    have hKN0 : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.ne'
    have heq : (K N : ℝ) * step s t K N = t N - s N := by
      unfold step; field_simp
    rw [heq] at hmulle
    unfold time
    constructor
    · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hstep0]
    · linarith

/-- **The generic transfer lemma.** A continuum-uniform flow-level `HighProb` statement (membership
of `Hflow d N u ω` in a measurable matrix-set family `S N u`, uniform over `u ∈ [s N, t N]`, as
the a-priori bound (2.73) and the column bound (5.57) produce) transfers, at each
grid index `k ≤ K N`, to the grid via `map_H_eq` (equality of probabilities, no loss); combining
the `K N + 1` many single-grid-time statements into one event needs a genuine probability union
bound (`HighProb.biInter`), hence the added hypothesis that the grid has polynomially many points. -/
theorem highProb_grid_of_flow (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (hK0 : ∀ N, K N ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C)
    (S : ∀ N : ℕ, ℝ → Set (Matrix (d.Idx N) (d.Idx N) ℂ))
    (hSmeas : ∀ N u, MeasurableSet (S N u))
    (hFlow : HighProb (P d)
      (fun N => {ω | ∀ u : TimeIcc s t N, Hflow d N (u : ℝ) ω ∈ S N (u : ℝ)})) :
    HighProb (Pg d)
      (fun N => {ω | ∀ k : Fin (K N + 1), H d s t K N k ω ∈ S N (time s t K N k)}) := by
  have hset : ∀ N, {ω | ∀ k : Fin (K N + 1), H d s t K N k ω ∈ S N (time s t K N k)}
      = ⋂ k : Fin (K N + 1), {ω | H d s t K N k ω ∈ S N (time s t K N k)} := by
    intro N; ext ω; simp
  simp only [hset]
  refine HighProb.biInter hC0 (by simpa [Fintype.card_fin] using hKcard) ?_
  intro D hD
  filter_upwards [hFlow D hD] with N hN k
  set u0 : ℝ := time s t K N k with hu0def
  have hHmeas : Measurable (H d s t K N k) :=
    (H_measurable_filt d s t K N k).mono ((filt d).le k) le_rfl
  have hHflowmeas : Measurable (Hflow d N u0) := RBM.measurable_H (sample d) N u0
  have hmem : u0 ∈ Set.Icc (s N) (t N) :=
    mem_Icc_time s t K N k (hs0 N) (hst N) (Nat.lt_succ_iff.mp k.isLt)
  have hcompl_eq : (Pg d) {ω | H d s t K N k ω ∈ S N u0}ᶜ
      = (P d) {ω' | Hflow d N u0 ω' ∈ S N u0}ᶜ := by
    show (Pg d) ((H d s t K N k) ⁻¹' (S N u0))ᶜ = (P d) ((Hflow d N u0) ⁻¹' (S N u0))ᶜ
    rw [← Set.preimage_compl, ← Set.preimage_compl,
      ← Measure.map_apply hHmeas (hSmeas N u0).compl,
      ← Measure.map_apply hHflowmeas (hSmeas N u0).compl,
      map_H_eq s t K N k (hs0 N) (hst N) (hK0 N)]
  have hsub : {ω | ∀ u : TimeIcc s t N, Hflow d N (u : ℝ) ω ∈ S N (u : ℝ)}
      ⊆ {ω' | Hflow d N u0 ω' ∈ S N u0} := fun ω hω => hω ⟨u0, hmem⟩
  have hle : (P d) {ω' | Hflow d N u0 ω' ∈ S N u0}ᶜ
      ≤ (P d) {ω | ∀ u : TimeIcc s t N, Hflow d N (u : ℝ) ω ∈ S N (u : ℝ)}ᶜ :=
    measure_mono (Set.compl_subset_compl.mpr hsub)
  calc (Pg d) {ω | H d s t K N k ω ∈ S N u0}ᶜ
      = (P d) {ω' | Hflow d N u0 ω' ∈ S N u0}ᶜ := hcompl_eq
    _ ≤ (P d) {ω | ∀ u : TimeIcc s t N, Hflow d N (u : ℝ) ω ∈ S N (u : ℝ)}ᶜ := hle
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := hN

/-! #### (2.73) -/

/-- The matrix-set form of `(2.73)`: the `n`-loop bound of the a-priori estimate, as a set of
matrices. -/
def eq273Set (E : ℝ) (N n : ℕ) (u ℓs τ : ℝ) : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | ∀ v : LoopData (d.L N) n,
    ‖gloop (d.L N) (d.W N) M (zt E u) v.idx‖ ≤
      (N : ℝ) ^ τ * ((band d).ell N u / ℓs) ^ (n - 1) * ((band d).scale E N u)⁻¹ ^ (n - 1)}

theorem measurableSet_eq273Set (E : ℝ) (N n : ℕ) (u ℓs τ : ℝ) :
    MeasurableSet (eq273Set d E N n u ℓs τ) := by
  have heq : eq273Set d E N n u ℓs τ =
      ⋂ v : LoopData (d.L N) n, {M | ‖gloop (d.L N) (d.W N) M (zt E u) v.idx‖ ≤
        (N : ℝ) ^ τ * ((band d).ell N u / ℓs) ^ (n - 1) * ((band d).scale E N u)⁻¹ ^ (n - 1)} := by
    unfold eq273Set; ext M; simp
  rw [heq]
  exact MeasurableSet.iInter fun v =>
    measurableSet_le (measurable_gloop_matrix d N (zt E u) v.idx).norm measurable_const

/-! #### (5.57) -/

/-- A finite intersection of measurable sets with a decidable side condition:
`{x | ∀ i, p i → x ∈ s i} = ⋂ i, if p i then s i else univ`. -/
private theorem measurableSet_setOf_forall_imp {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    MeasurableSet {x | ∀ i, p i → x ∈ s i} := by
  have heq : {x | ∀ i, p i → x ∈ s i} = ⋂ i, (if p i then s i else Set.univ) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h i
      by_cases hpi : p i
      · simpa [hpi] using h i hpi
      · simp [hpi]
    · intro h i hpi
      simpa [hpi] using h i
  rw [heq]
  exact MeasurableSet.iInter fun i => by
    split
    · exact hs i
    · exact MeasurableSet.univ

/-- The matrix-set form of `(5.57)`, column orientation, at the (2.73)-reduced strength. -/
def eq557Set (E : ℝ) (N : ℕ) (u ℓs τ : ℝ) : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | ∀ x y : ZMod (d.L N), ∀ p : ZMod (d.L N) × Fin (d.W N), p.1 = y →
    ∑ r, RBM.Lemma57.blkW (d.L N) (d.W N) r x * ‖green M (zt E u) r p‖ ≤
      (N : ℝ) ^ τ * Real.sqrt ((band d).ell N u / ℓs) * (Real.sqrt ((band d).scale E N u))⁻¹}

theorem measurableSet_eq557Set (E : ℝ) (N : ℕ) (u ℓs τ : ℝ) :
    MeasurableSet (eq557Set d E N u ℓs τ) := by
  have heq : eq557Set d E N u ℓs τ =
      ⋂ x : ZMod (d.L N), ⋂ y : ZMod (d.L N),
        {M | ∀ p : ZMod (d.L N) × Fin (d.W N), p.1 = y →
          ∑ r, RBM.Lemma57.blkW (d.L N) (d.W N) r x * ‖green M (zt E u) r p‖ ≤
            (N : ℝ) ^ τ * Real.sqrt ((band d).ell N u / ℓs)
              * (Real.sqrt ((band d).scale E N u))⁻¹} := by
    unfold eq557Set; ext M; simp
  rw [heq]
  refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
  refine measurableSet_setOf_forall_imp (fun p : ZMod (d.L N) × Fin (d.W N) => p.1 = y)
    (fun p => {M | ∑ r, RBM.Lemma57.blkW (d.L N) (d.W N) r x * ‖green M (zt E u) r p‖ ≤
      (N : ℝ) ^ τ * Real.sqrt ((band d).ell N u / ℓs) * (Real.sqrt ((band d).scale E N u))⁻¹})
    fun p => ?_
  refine measurableSet_le ?_ measurable_const
  exact Finset.measurable_sum _ fun r _ =>
    measurable_const.mul (measurable_green_matrix d N (zt E u) r p).norm

end RBM.Gauss.Grid

end
