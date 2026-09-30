/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GUEPhaseGrid
import RBM1D.Green.EntryBound
import RBM1D.Gauss.LDEFlow
import RBM1D.Loop.Split
import RBM1D.Gauss.LDEQuadDom
import RBM1D.Loop.Continuity
import RBM1D.Flow.Scales

/-!
# Lemma 4.1 (4.2)/(4.3) for the GUE-phase profile

At every grid time
`u = Grid.time t1 t0 K N k`, `k ≤ K = gueGridK n0 N`, the GUE-phase grid path
`gueH` of `Flow/GUEPhaseGrid.lean` has entry variances `S_u = t₁ S + (u - t₁)/M` (profile
`gueEntryProf`, row sums `u`). On the a priori event `‖G - m‖_max ≤ δ_N`,
`|G_ij - m δ_ij|² ≺ 9 max L₂ + 2 W⁻¹` (paper, Lemma 4.1 (4.2)/(4.3)), uniformly in
the grid time and the indices: `RBM.Gauss.GUEGrid.gueGrid_entry_bound`.

## Route

* **Deterministic core** (`gueEntry_det`): `Green/EntryBound.lean`'s profile-generic (4.11)/(4.3)
  with the normalised profile `S' = S_u / u` and `t = u`. The `J`-part of `S'` is controlled by
  the Ward identity `∑_l |G_kl|² = Im G_kk / η` (`gueEntry_ward_row`/`_col`) and the lower bound
  `(Mη)⁻¹ ≤ (2/Im m) max L₂` (`gueEntry_inv_Meta_le`); stability of `1 - u m² S'` is obtained
  by averaging out the `J`-part (`|1 - u m²| ≥ √κ`) and `stable_Sblk_short_edge`
  (`gueEntry_stable`). The hypotheses `h730` and `hτU` of the main statement are therefore not
  used.
* **Probabilistic layer.** Only the one-time law of `gueH d … k` at each grid step is used
  (`gueEntry_law_HG`): it is realised on an auxiliary band model `gueEntryDG` (`L ≡ 3`, so every
  coordinate variance is positive) by an injective reindexing and scaling of coordinates. There
  every large deviation input of Lemma 4.1 is a Gaussian row chaos (`RBM.Gauss.RowChaos`): the
  quadratic form of (4.7) directly (`gueEntryQuadChaos`), the row/column sums of (4.8) as
  rank-one chaoses (`gueEntryLinChaos`), and the Hanson–Wright moment bound gives the tails
  (`gueEntry_chaos_tail`, generic in the chaos). A union bound over the polynomially many grid
  times and indices gives the four `StochDom` families (`gueEntry_stochDom_row`,
  `gueEntry_stochDom_col`, `gueEntry_stochDom_quad`, `gueEntry_stochDom_diag`), and
  `RBM.StochDom.of_det` assembles.

No pathwise statement is moved between carriers; `gueEntryDG` and
`gueGridK` are proof devices, not hypothesis witnesses.
-/

noncomputable section

namespace RBM.Gauss.GUEGrid

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ### An auxiliary band model all of whose coordinates have positive variance -/

/-- The auxiliary dimensions `L ≡ 3`, `W n = max 1 (n / 3)`: with three blocks every pair of
blocks is adjacent, so every coordinate variance is positive. A proof device only. -/
def gueEntryDG : Dims where
  W n := max 1 (n / 3)
  L _ := 3
  W_pos n := lt_of_lt_of_le Nat.one_pos (le_max_left _ _)
  three_le_L _ := le_rfl
  dim := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have h1 : max 1 (n / 3) = n / 3 := max_eq_right (by omega)
    rw [h1]
    constructor <;> omega
  c := 1 / 4
  c_pos := by norm_num
  bandwidth := by
    filter_upwards [eventually_ge_atTop 1296] with n hn
    have hn' : (1296 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have h1 : max 1 (n / 3) = n / 3 := max_eq_right (by omega)
    rw [h1]
    have h3 : ((n / 3 : ℕ) : ℝ) ≥ (n : ℝ) / 6 := by
      have : n ≤ 3 * (n / 3) + 2 := by omega
      have h' : (n : ℝ) ≤ 3 * ((n / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast this
      linarith
    have h4 : (6 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
      have : (6 : ℝ) = ((1296 : ℝ)) ^ ((1 : ℝ) / 4) := by
        rw [show (1296 : ℝ) = 6 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [this]
      exact Real.rpow_le_rpow (by norm_num) hn' (by norm_num)
    have h5 : (n : ℝ) ^ ((1 : ℝ) / 2 + 1 / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = n := by
      rw [← Real.rpow_add hnpos]; norm_num
    have h6 : 0 < (n : ℝ) ^ ((1 : ℝ) / 2 + 1 / 4) := Real.rpow_pos_of_pos hnpos _
    nlinarith

variable (d : Dims)

/-- The slot of `gueEntryDG` used for size `N`: `3 · pair(N, M)`, `M = L W`. -/
def gueEntrySlot (N : ℕ) : ℕ := 3 * Nat.pair N (d.L N * d.W N)

theorem gueEntryDG_W_slot (N : ℕ) :
    gueEntryDG.W (gueEntrySlot d N) = Nat.pair N (d.L N * d.W N) := by
  change max 1 (3 * Nat.pair N (d.L N * d.W N) / 3) = _
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  have hM : 1 ≤ d.L N * d.W N := Nat.mul_pos (by have := d.three_le_L N; omega) (d.W_pos N)
  have := Nat.right_le_pair N (d.L N * d.W N)
  exact max_eq_right (by omega)

theorem gueEntrySlot_injective : Function.Injective (gueEntrySlot d) := by
  intro N N' h
  unfold gueEntrySlot at h
  have h' : Nat.pair N (d.L N * d.W N) = Nat.pair N' (d.L N' * d.W N') := by omega
  exact (Nat.pair_eq_pair.1 h').1

theorem gueEntry_idxKey_lt (N : ℕ) (i : d.Idx N) :
    idxKey d N i < gueEntryDG.W (gueEntrySlot d N) := by
  rw [gueEntryDG_W_slot]
  have h1 : idxKey d N i < d.L N * d.W N := by
    unfold idxKey
    have ha : i.1.val < d.L N := ZMod.val_lt i.1
    have hα : (i.2 : ℕ) < d.W N := i.2.isLt
    have : d.W N * i.1.val + d.W N ≤ d.W N * d.L N := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ha
    rw [Nat.mul_comm (d.L N)]
    omega
  exact lt_of_lt_of_le h1 (Nat.right_le_pair _ _)

/-- The order-preserving embedding of `d.Idx N` into block `0` of the auxiliary slot. -/
def gueEntryEmb (N : ℕ) (i : d.Idx N) : gueEntryDG.Idx (gueEntrySlot d N) :=
  ((0 : ZMod 3), ⟨idxKey d N i, gueEntry_idxKey_lt d N i⟩)

theorem gueEntryEmb_injective (N : ℕ) : Function.Injective (gueEntryEmb d N) := by
  intro i j h
  have h2 := congrArg (fun p => (p.2 : ℕ)) h
  exact idxKey_injective d N h2

/-- The coordinate injection `Coord d ↪ Coord gueEntryDG`. -/
def gueEntryRho (c : Coord d) : Coord gueEntryDG :=
  ⟨gueEntrySlot d c.1, gueEntryEmb d c.1 c.2.1, gueEntryEmb d c.1 c.2.2.1, c.2.2.2⟩

theorem gueEntryRho_injective : Function.Injective (gueEntryRho d) := by
  rintro ⟨N, i, j, b⟩ ⟨N', i', j', b'⟩ h
  simp only [gueEntryRho] at h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 h
  have hN : N = N' := gueEntrySlot_injective d h1
  subst hN
  have h3 := eq_of_heq h2
  simp only [Prod.mk.injEq] at h3
  obtain ⟨hi, hj, hb⟩ := h3
  rw [gueEntryEmb_injective d N hi, gueEntryEmb_injective d N hj, hb]

theorem gueEntry_sbSupport_three (u : ZMod 3) : u ∈ sbSupport 3 := by
  have h : ∀ v : ZMod 3, v ∈ ({0, 1, -1} : Finset (ZMod 3)) := by decide
  exact h u

/-- Every coordinate of the auxiliary model has positive variance. -/
theorem gueEntryDG_gvar_pos (c : Coord gueEntryDG) : 0 < (gvar gueEntryDG c : ℝ) := by
  obtain ⟨n, x, y, b⟩ := c
  have hW : (0 : ℝ) < gueEntryDG.W n := by exact_mod_cast gueEntryDG.W_pos n
  have hS : 0 < Sblk (gueEntryDG.L n) (gueEntryDG.W n) x y := by
    have hmem : (x.1 - y.1 : ZMod (gueEntryDG.L n)) ∈ sbSupport (gueEntryDG.L n) :=
      gueEntry_sbSupport_three (x.1 - y.1)
    change 0 < sbKre (gueEntryDG.L n) (x.1 - y.1) / (gueEntryDG.W n : ℝ)
    unfold sbKre
    simp only [hmem, ite_true]
    positivity
  change 0 < ((if x = y then Sblk (gueEntryDG.L n) (gueEntryDG.W n) x y
    else Sblk (gueEntryDG.L n) (gueEntryDG.W n) x y / 2 : ℝ))
  split_ifs <;> positivity

/-! ### Injective reindexing of a product measure -/

theorem gueEntry_infinitePi_map_comp {ι α : Type*} [Nonempty α] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {ρ : α → ι} (hρ : Function.Injective ρ) :
    (Measure.infinitePi μ).map (fun ω : ι → ℝ => fun a => ω (ρ a))
      = Measure.infinitePi (fun a => μ (ρ a)) := by
  classical
  have hmeas : Measurable (fun ω : ι → ℝ => fun a => ω (ρ a)) :=
    measurable_pi_iff.2 fun a => measurable_pi_apply (ρ a)
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun a _ => ht a)]
  have hpre : (fun ω : ι → ℝ => fun a => ω (ρ a)) ⁻¹' ((s : Set α).pi t)
      = ((s.map ⟨ρ, hρ⟩ : Finset ι) : Set ι).pi (fun i => t (Function.invFun ρ i)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.coe_map,
      Function.Embedding.coeFn_mk, Set.mem_image]
    constructor
    · rintro h i ⟨a, ha, rfl⟩
      rw [Function.leftInverse_invFun hρ a]
      exact h a ha
    · intro h a ha
      have := h (ρ a) ⟨a, ha, rfl⟩
      rwa [Function.leftInverse_invFun hρ a] at this
  rw [hpre, Measure.infinitePi_pi _ (fun i _ => ht _), Finset.prod_map]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [Function.Embedding.coeFn_mk, Function.leftInverse_invFun hρ a]

/-! ### The one-time law of the grid path (reproducing the mixed-grid computation of
`Flow/GUEPhaseGrid.lean`) -/

section MixedLaw

variable {d}

private lemma gueEntryXentry_add (N : ℕ) (ω1 ω2 : Ω d) (i j : d.Idx N) :
    Xentry d N (ω1 + ω2) i j = Xentry d N ω1 i j + Xentry d N ω2 i j := by
  simp only [Xentry, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

private lemma gueEntryXentry_smul (N : ℕ) (a : ℝ) (ω : Ω d) (i j : d.Idx N) :
    Xentry d N (a • ω) i j = (a : ℂ) * Xentry d N ω i j := by
  simp only [Xentry, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

private lemma gueEntryXentry_zero (N : ℕ) (i j : d.Idx N) : Xentry d N (0 : Ω d) i j = 0 := by
  simp only [Xentry, Pi.zero_apply]
  split_ifs <;> simp

private lemma gueEntryXentry_sum {ι : Type*} (N : ℕ) (S : Finset ι) (ω : ι → Ω d)
    (i j : d.Idx N) : Xentry d N (∑ l ∈ S, ω l) i j = ∑ l ∈ S, Xentry d N (ω l) i j := by
  classical
  induction S using Finset.induction with
  | empty => simp [gueEntryXentry_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, gueEntryXentry_add, ih, Finset.sum_insert ha]

private def gueEntryMixedStep (v0 v1 : Coord d → ℝ≥0) : ℕ → Measure (Ω d)
  | 0 => Measure.infinitePi fun c => gaussianReal 0 (v0 c)
  | _ + 1 => Measure.infinitePi fun c => gaussianReal 0 (v1 c)

private def gueEntryRawStep (v0 v1 : Coord d → ℝ≥0) (c : Coord d) (i : ℕ) : Measure ℝ :=
  if i = 0 then gaussianReal 0 (v0 c) else gaussianReal 0 (v1 c)

private instance gueEntryRawStep_isProb (v0 v1 : Coord d → ℝ≥0) (c : Coord d) (i : ℕ) :
    IsProbabilityMeasure (gueEntryRawStep v0 v1 c i) := by
  unfold gueEntryRawStep; split_ifs <;> infer_instance

private lemma gueEntryMixedStep_eq (v0 v1 : Coord d → ℝ≥0) (i : ℕ) :
    gueEntryMixedStep v0 v1 i = Measure.infinitePi (fun c => gueEntryRawStep v0 v1 c i) := by
  cases i <;> simp [gueEntryMixedStep, gueEntryRawStep]

private def gueEntryRaw' (v0 v1 : Coord d → ℝ≥0) : Measure (Coord d → ℕ → ℝ) :=
  Measure.infinitePi (fun c : Coord d =>
    Measure.infinitePi (fun i : ℕ => gueEntryRawStep v0 v1 c i))

private def gueEntrySwap : (Coord d → ℕ → ℝ) → (ℕ → Ω d) :=
  (MeasurableEquiv.curry ℕ (Coord d) ℝ) ∘
    (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ)) ∘
    (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm

private lemma measurable_gueEntrySwap : Measurable (gueEntrySwap (d := d)) :=
  (MeasurableEquiv.curry ℕ (Coord d) ℝ).measurable.comp
    ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ)
      (Equiv.prodComm (Coord d) ℕ)).measurable.comp
      (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm.measurable)

private lemma gueEntrySwap_apply (X : Coord d → ℕ → ℝ) (i : ℕ) (c : Coord d) :
    gueEntrySwap X i c = X c i := by
  change (MeasurableEquiv.curry ℕ (Coord d) ℝ)
      ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ))
        ((MeasurableEquiv.curry (Coord d) ℕ ℝ).symm X)) i c = X c i
  rw [MeasurableEquiv.coe_curry]
  change (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ))
      ((MeasurableEquiv.curry (Coord d) ℕ ℝ).symm X) (i, c) = X c i
  have key := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.prodComm (Coord d) ℕ)
    (β := fun _ : ℕ × Coord d => ℝ) ((MeasurableEquiv.curry (Coord d) ℕ ℝ).symm X) (c, i)
  rw [show Equiv.prodComm (Coord d) ℕ (c, i) = (i, c) from rfl] at key
  rw [key, MeasurableEquiv.coe_curry_symm]
  rfl

private lemma gueEntryRaw'_swap_eq (v0 v1 : Coord d → ℝ≥0) :
    (gueEntryRaw' v0 v1).map gueEntrySwap = Measure.infinitePi (gueEntryMixedStep v0 v1) := by
  have ha : (gueEntryRaw' v0 v1).map ((MeasurableEquiv.curry (Coord d) ℕ ℝ).symm)
      = Measure.infinitePi (fun p : Coord d × ℕ => gueEntryRawStep v0 v1 p.1 p.2) :=
    Measure.infinitePi_map_curry_symm
      (μ := fun (c : Coord d) (i : ℕ) => gueEntryRawStep v0 v1 c i)
  have hb : (Measure.infinitePi (fun p : Coord d × ℕ => gueEntryRawStep v0 v1 p.1 p.2)).map
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ))
      = Measure.infinitePi (fun p : ℕ × Coord d => gueEntryRawStep v0 v1 p.2 p.1) :=
    Measure.infinitePi_map_piCongrLeft
      (μ := fun p : ℕ × Coord d => gueEntryRawStep v0 v1 p.2 p.1) (Equiv.prodComm (Coord d) ℕ)
  have hc : (Measure.infinitePi (fun p : ℕ × Coord d => gueEntryRawStep v0 v1 p.2 p.1)).map
      (MeasurableEquiv.curry ℕ (Coord d) ℝ) = Measure.infinitePi (gueEntryMixedStep v0 v1) := by
    rw [Measure.infinitePi_map_curry
      (μ := fun (i : ℕ) (c : Coord d) => gueEntryRawStep v0 v1 c i)]
    exact congrArg Measure.infinitePi (funext fun i => (gueEntryMixedStep_eq v0 v1 i).symm)
  change (gueEntryRaw' v0 v1).map ((MeasurableEquiv.curry ℕ (Coord d) ℝ) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ)) ∘
      (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm) = Measure.infinitePi (gueEntryMixedStep v0 v1)
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop), ha, hb, hc]

private lemma gueEntry_sumIcc_map {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Y : ℕ → Ω' → ℝ} (hYm : ∀ i, Measurable (Y i))
    (hY : iIndepFun Y μ') {w : ℝ≥0} (hYd : ∀ i, 1 ≤ i → μ'.map (Y i) = gaussianReal 0 w)
    (k : ℕ) :
    μ'.map (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) = gaussianReal 0 (k • w) := by
  induction k with
  | zero =>
      have hEmpty : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
      simp only [hEmpty, Finset.sum_empty]
      rw [Measure.map_const, measure_univ, one_smul, zero_smul, gaussianReal_zero_var]
  | succ k ih =>
      have hnotmem : (k + 1) ∉ Finset.Icc 1 k := by simp
      have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hfun : (fun ω => ∑ i ∈ Finset.Icc 1 (k + 1), Y i ω)
          = (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) + Y (k + 1) := by
        funext ω
        rw [hins, Finset.sum_insert hnotmem, add_comm]
        rfl
      rw [hfun]
      have hsummeas : Measurable (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) :=
        Finset.measurable_sum _ fun i _ => hYm i
      have hlaw1 : HasLaw (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (gaussianReal 0 (k • w)) μ' :=
        ⟨hsummeas.aemeasurable, ih⟩
      have hlaw2 : HasLaw (Y (k + 1)) (gaussianReal 0 w) μ' :=
        ⟨(hYm (k + 1)).aemeasurable, hYd (k + 1) (by omega)⟩
      have hindep : IndepFun (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (Y (k + 1)) μ' := by
        have h := hY.indepFun_finsetSum_of_notMem hYm hnotmem
        have heq : (∑ j ∈ Finset.Icc 1 k, Y j) = fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω := by
          funext ω; simp [Finset.sum_apply]
        rwa [heq] at h
      have hres := gaussianReal_add_gaussianReal_of_indepFun hindep hlaw1 hlaw2
      rw [hres, add_zero, ← succ_nsmul]

private lemma gueEntry_weightedSum_map {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Y : ℕ → Ω' → ℝ} (hYm : ∀ i, Measurable (Y i))
    (hY : iIndepFun Y μ') {w0 w1 : ℝ≥0} (hY0 : μ'.map (Y 0) = gaussianReal 0 w0)
    (hY1 : ∀ i, 1 ≤ i → μ'.map (Y i) = gaussianReal 0 w1) (a b : ℝ) (k : ℕ) :
    μ'.map (fun ω => a * Y 0 ω + b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * w0
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * w1)) := by
  classical
  have hindep : IndepFun (fun ω => a * Y 0 ω)
      (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω) μ' := by
    have h0 : IndepFun (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (Y 0) μ' := by
      have h := hY.indepFun_finsetSum_of_notMem hYm (s := Finset.Icc 1 k) (i := 0) (by simp)
      have heq : (∑ j ∈ Finset.Icc 1 k, Y j) = fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω := by
        funext ω; simp [Finset.sum_apply]
      rwa [heq] at h
    exact h0.symm.comp (φ := (a * ·)) (ψ := (b * ·)) (by fun_prop) (by fun_prop)
  have hlaw0 : HasLaw (fun ω => a * Y 0 ω)
      (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * w0)) μ' := by
    refine ⟨by fun_prop, ?_⟩
    have : (fun ω => a * Y 0 ω) = (a * ·) ∘ Y 0 := rfl
    rw [this, ← Measure.map_map (by fun_prop) (hYm 0), hY0, gaussianReal_map_const_mul, mul_zero]
  have hsummeas : Measurable (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) :=
    Finset.measurable_sum _ fun i _ => hYm i
  have hlawsum : μ'.map (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) = gaussianReal 0 (k • w1) :=
    gueEntry_sumIcc_map hYm hY hY1 k
  have hlaw1 : HasLaw (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      (gaussianReal 0 (NNReal.mk (b ^ 2) (sq_nonneg b) * (k • w1))) μ' := by
    refine ⟨by fun_prop, ?_⟩
    have heq : (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
        = (b * ·) ∘ (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) := rfl
    rw [heq, ← Measure.map_map (by fun_prop) hsummeas, hlawsum, gaussianReal_map_const_mul,
      mul_zero]
  have hgoal_eq : (fun ω => a * Y 0 ω + b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      = (fun ω => a * Y 0 ω) + fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω := rfl
  rw [hgoal_eq]
  have hres := gaussianReal_add_gaussianReal_of_indepFun hindep hlaw0 hlaw1
  rw [hres, add_zero]
  congr 1
  rw [nsmul_eq_mul, nsmul_eq_mul]
  apply NNReal.coe_injective
  push_cast
  ring

private lemma gueEntry_map_column (v0 v1 : Coord d → ℝ≥0) (c : Coord d) (a b : ℝ) (k : ℕ) :
    (Measure.infinitePi (fun i : ℕ => gueEntryRawStep v0 v1 c i)).map
        (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c)) := by
  have hY : iIndepFun (fun i : ℕ => (fun y : ℕ → ℝ => y i))
      (Measure.infinitePi (fun i : ℕ => gueEntryRawStep v0 v1 c i)) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (mX := fun _ => measurable_id)
  have hYm : ∀ i : ℕ, Measurable (fun y : ℕ → ℝ => y i) := fun i => measurable_pi_apply i
  have hY0 : (Measure.infinitePi (fun i : ℕ => gueEntryRawStep v0 v1 c i)).map
      (fun y : ℕ → ℝ => y 0) = gaussianReal 0 (v0 c) := by
    rw [Measure.infinitePi_map_eval]
    simp [gueEntryRawStep]
  have hY1 : ∀ i : ℕ, 1 ≤ i → (Measure.infinitePi (fun i : ℕ => gueEntryRawStep v0 v1 c i)).map
      (fun y : ℕ → ℝ => y i) = gaussianReal 0 (v1 c) := by
    intro i hi
    rw [Measure.infinitePi_map_eval]
    unfold gueEntryRawStep
    rw [ite_eq_right_iff.2 (fun h => absurd h (by omega))]
  exact gueEntry_weightedSum_map hYm hY hY0 hY1 a b k

private lemma gueEntry_map_combined (v0 v1 : Coord d → ℝ≥0) (a b : ℝ) (k : ℕ) :
    (Measure.infinitePi (gueEntryMixedStep v0 v1)).map (fun ω : ℕ → Ω d =>
        a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i)
      = Measure.infinitePi (fun c : Coord d => gaussianReal 0
          (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
            + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c))) := by
  have hmeasComb : Measurable (fun ω : ℕ → Ω d =>
      a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := by
    have h1 : Measurable (fun ω : ℕ → Ω d => ω 0) := measurable_pi_apply 0
    have h2 : Measurable (fun ω : ℕ → Ω d => ∑ i ∈ Finset.Icc 1 k, ω i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_smul a).add (h2.const_smul b)
  have hcomp : (fun ω : ℕ → Ω d => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) ∘ gueEntrySwap
      = (fun X : Coord d → ℕ → ℝ => fun c => a * X c 0 + b * ∑ i ∈ Finset.Icc 1 k, X c i) := by
    funext X
    funext c
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      gueEntrySwap_apply]
  rw [← gueEntryRaw'_swap_eq v0 v1, Measure.map_map hmeasComb measurable_gueEntrySwap, hcomp]
  have hfmeas : ∀ c : Coord d,
      Measurable (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) :=
    fun c => by
      have h1 : Measurable (fun y : ℕ → ℝ => y 0) := measurable_pi_apply 0
      have h2 : Measurable (fun y : ℕ → ℝ => ∑ i ∈ Finset.Icc 1 k, y i) :=
        Finset.measurable_sum _ fun i _ => measurable_pi_apply i
      exact (h1.const_mul _).add (h2.const_mul _)
  have hpi := Measure.infinitePi_map_pi
      (μ := fun c : Coord d => Measure.infinitePi (fun i : ℕ => gueEntryRawStep v0 v1 c i))
      (f := fun c : Coord d => fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) hfmeas
  rw [gueEntryRaw']
  exact hpi.trans (congrArg Measure.infinitePi
    (funext fun c => gueEntry_map_column v0 v1 c a b k))

private lemma gueEntry_Pgue_eq_mixed :
    Pgue d = Measure.infinitePi (gueEntryMixedStep (gvar d) (gueUnitVar d)) := by
  unfold Pgue
  refine congrArg Measure.infinitePi (funext fun k => ?_)
  cases k with
  | zero => rfl
  | succ k => rfl

end MixedLaw

/-- The coordinate variances of the grid path at step `k`:
`t₁ gvar_c + k (Δ/M) gueUnitVar_c`, in the normal form produced by the mixed-grid law. -/
def gueEntryVar (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (c : Coord d) : ℝ≥0 :=
  NNReal.mk (Real.sqrt (t1 N) ^ 2) (sq_nonneg _) * gvar d c
    + k • (NNReal.mk (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) ^ 2)
        (sq_nonneg _) * gueUnitVar d c)

/-- **The one-time law of the grid path at step `k`**: `Xmat` of independent centred Gaussian
coordinates with variances `gueEntryVar`. -/
theorem gueEntry_map_gueH (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    (Pgue d).map (gueH d t1 t0 K N k)
      = (Measure.infinitePi (fun c => gaussianReal 0 (gueEntryVar d t1 t0 K N k c))).map
          (Xmat d N) := by
  set a : ℝ := Real.sqrt (t1 N)
  set b : ℝ := Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ))
  have hXm : Measurable (Xmat d N) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry d N i j
  have hHeq : gueH d t1 t0 K N k
      = fun ω => Xmat d N (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := by
    funext ω
    ext i j
    simp only [gueH, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Xmat_apply,
      smul_eq_mul]
    rw [gueEntryXentry_add, gueEntryXentry_smul, gueEntryXentry_smul, gueEntryXentry_sum]
  have hmeasComb : Measurable (fun ω : ℕ → Ω d => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := by
    have h1 : Measurable (fun ω : ℕ → Ω d => ω 0) := measurable_pi_apply 0
    have h2 : Measurable (fun ω : ℕ → Ω d => ∑ i ∈ Finset.Icc 1 k, ω i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_smul a).add (h2.const_smul b)
  rw [hHeq, show (fun ω : Grid.Ωg d => Xmat d N (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i))
      = Xmat d N ∘ (fun ω => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) from rfl,
    ← Measure.map_map hXm hmeasComb, gueEntry_Pgue_eq_mixed,
    gueEntry_map_combined (gvar d) (gueUnitVar d) a b k]
  rfl

/-! ### Realising the one-time law on the auxiliary model -/

/-- The scale turning the auxiliary coordinate `ρ c` into a coordinate of variance `v c`. -/
def gueEntryScale (v : Coord d → ℝ≥0) (c : Coord d) : ℝ :=
  Real.sqrt ((v c : ℝ) / (gvar gueEntryDG (gueEntryRho d c) : ℝ))

/-- The coordinate map `Ω gueEntryDG → Ω d`, `(T ω) c = s_c · ω (ρ c)`. -/
def gueEntryT (v : Coord d → ℝ≥0) (ω : Ω gueEntryDG) : Ω d :=
  fun c => gueEntryScale d v c * ω (gueEntryRho d c)

theorem gueEntryT_measurable (v : Coord d → ℝ≥0) : Measurable (gueEntryT d v) :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).const_mul _

theorem gueEntryT_continuous (v : Coord d → ℝ≥0) : Continuous (gueEntryT d v) :=
  continuous_pi fun _ => continuous_const.mul (continuous_apply _)

instance gueEntry_nonempty_coord : Nonempty (Coord d) :=
  ⟨⟨0, (0, ⟨0, d.W_pos 0⟩), (0, ⟨0, d.W_pos 0⟩), true⟩⟩

theorem gueEntry_map_T (v : Coord d → ℝ≥0) :
    (P gueEntryDG).map (gueEntryT d v) = Measure.infinitePi (fun c => gaussianReal 0 (v c)) := by
  have hre : gueEntryT d v = (fun y : Coord d → ℝ => fun c => gueEntryScale d v c * y c) ∘
      (fun ω : Ω gueEntryDG => fun c => ω (gueEntryRho d c)) := rfl
  have hm1 : Measurable (fun ω : Ω gueEntryDG => fun c => ω (gueEntryRho d c)) :=
    measurable_pi_iff.2 fun c => measurable_pi_apply _
  have hm2 : ∀ c : Coord d, Measurable (fun x : ℝ => gueEntryScale d v c * x) :=
    fun c => measurable_const.mul measurable_id
  rw [hre, ← Measure.map_map (measurable_pi_iff.2 fun c => (measurable_pi_apply c).const_mul _)
    hm1, P, gueEntry_infinitePi_map_comp _ (gueEntryRho_injective d)]
  refine (Measure.infinitePi_map_pi
    (μ := fun c : Coord d => gaussianReal 0 (gvar gueEntryDG (gueEntryRho d c)))
    (f := fun c (x : ℝ) => gueEntryScale d v c * x) hm2).trans ?_
  refine congrArg Measure.infinitePi (funext fun c => ?_)
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.coe_injective
  have hg := gueEntryDG_gvar_pos (gueEntryRho d c)
  simp only [NNReal.coe_mul, NNReal.coe_mk, gueEntryScale]
  rw [Real.sq_sqrt (div_nonneg (v c).coe_nonneg hg.le)]
  field_simp

/-- **The grid path at step `k` and the auxiliary matrix have the same law.** -/
theorem gueEntry_law (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    (Pgue d).map (gueH d t1 t0 K N k)
      = (P gueEntryDG).map (fun ω => Xmat d N (gueEntryT d (gueEntryVar d t1 t0 K N k) ω)) := by
  have hXm : Measurable (Xmat d N) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry d N i j
  rw [gueEntry_map_gueH, show (fun ω => Xmat d N (gueEntryT d (gueEntryVar d t1 t0 K N k) ω))
      = Xmat d N ∘ gueEntryT d (gueEntryVar d t1 t0 K N k) from rfl,
    ← Measure.map_map hXm (gueEntryT_measurable d _), gueEntry_map_T]

/-! ### A tail bound for an arbitrary row chaos (the `ε`-normalisation, made generic) -/

section ChaosTail

variable {D : Dims} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem gueEntry_continuous_Vq (C : RowChaos D κ) : Continuous C.Vq := by
  change Continuous fun ω => ∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    (continuous_const.mul ((C.B_cont k l).norm.pow 2)).mul continuous_const

theorem gueEntry_Vq_congr (C : RowChaos D κ) {ω ω' : Ω D} (h : ∀ c ∈ C.Ifree, ω c = ω' c) :
    C.Vq ω = C.Vq ω' := by
  change (∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l)
    = ∑ k, ∑ l, C.sg k * ‖C.B ω' k l‖ ^ 2 * C.sg l
  rw [C.B_free ω ω' h]

/-- The chaos with its matrix divided by `(V_q + ε)^{1/2}`. -/
def gueEntryChaosEps (C : RowChaos D κ) (ε : ℝ) (hε : 0 < ε) : RowChaos D κ :=
  { C with
    B := fun ω k l => C.B ω k l / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)
    B_cont := fun k l => by
      refine (C.B_cont k l).div ?_ ?_
      · exact Complex.continuous_ofReal.comp
          ((gueEntry_continuous_Vq C).add continuous_const).sqrt
      · intro ω
        have : 0 < Real.sqrt (C.Vq ω + ε) :=
          Real.sqrt_pos.2 (by linarith [RowChaos.Vq_nonneg (C := C) ω])
        exact_mod_cast this.ne'
    Bbd := C.Bbd / Real.sqrt ε
    B_bdd := fun ω k l => by
      have hpos : 0 < Real.sqrt (C.Vq ω + ε) :=
        Real.sqrt_pos.2 (by linarith [RowChaos.Vq_nonneg (C := C) ω])
      have hge : Real.sqrt ε ≤ Real.sqrt (C.Vq ω + ε) :=
        Real.sqrt_le_sqrt (by linarith [RowChaos.Vq_nonneg (C := C) ω])
      have hεp : (0 : ℝ) < Real.sqrt ε := Real.sqrt_pos.2 hε
      have hB0 : 0 ≤ C.Bbd := (norm_nonneg _).trans (C.B_bdd ω k l)
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le]
      exact div_le_div₀ hB0 (C.B_bdd ω k l) hεp hge
    B_free := fun ω ω' h => by
      have hs : C.Vq ω = C.Vq ω' := gueEntry_Vq_congr C h
      funext k l
      rw [C.B_free ω ω' h, hs] }

theorem gueEntryChaosEps_chaos (C : RowChaos D κ) {ε : ℝ} (hε : 0 < ε) (ω : Ω D) :
    (gueEntryChaosEps C ε hε).chaos ω = C.chaos ω / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ) := by
  unfold RowChaos.chaos RowChaos.cen
  rw [sub_div]
  congr 1
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    change C.h ω k * (C.B ω k l / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)) * (starRingEnd ℂ) (C.h ω l)
      = C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)
    ring
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    change ((C.sg k : ℝ) : ℂ) * (C.B ω k k / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ))
      = ((C.sg k : ℝ) : ℂ) * C.B ω k k / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)
    ring

theorem gueEntryChaosEps_Vq (C : RowChaos D κ) {ε : ℝ} (hε : 0 < ε) (ω : Ω D) :
    (gueEntryChaosEps C ε hε).Vq ω = C.Vq ω / (C.Vq ω + ε) := by
  have hV0 := RowChaos.Vq_nonneg (C := C) ω
  have hpos : 0 < Real.sqrt (C.Vq ω + ε) := Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt (C.Vq ω + ε) ^ 2 = C.Vq ω + ε := Real.sq_sqrt (by linarith)
  change (∑ k, ∑ l, C.sg k * ‖C.B ω k l / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)‖ ^ 2 * C.sg l)
    = (∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l) / (C.Vq ω + ε)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le, div_pow, hsq]
  ring

theorem gueEntryChaosEps_Vq_le_one (C : RowChaos D κ) {ε : ℝ} (hε : 0 < ε) (ω : Ω D) :
    (gueEntryChaosEps C ε hε).Vq ω ≤ 1 := by
  rw [gueEntryChaosEps_Vq C hε ω]
  have h0 := RowChaos.Vq_nonneg (C := C) ω
  rw [div_le_one (by linarith)]
  linarith

theorem gueEntryChaosEps_mom_le (C : RowChaos D κ) {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    (gueEntryChaosEps C ε hε).mom (q + 1) ≤ hwConst q := by
  have h := (gueEntryChaosEps C ε hε).mom_le_momVpow (gaussIBP D) q
  have hV : (gueEntryChaosEps C ε hε).momVpow (q + 1) ≤ 1 := by
    change (∫ ω, (gueEntryChaosEps C ε hε).Vq ω ^ (q + 1) ∂(P D)) ≤ 1
    calc ∫ ω, (gueEntryChaosEps C ε hε).Vq ω ^ (q + 1) ∂(P D)
        ≤ ∫ _ω : Ω D, (1 : ℝ) ∂(P D) :=
          MeasureTheory.integral_mono
            ((gueEntryChaosEps C ε hε).integrable_Vq_pow (gaussIBP D) (q + 1))
            (MeasureTheory.integrable_const 1)
            (fun ω => pow_le_one₀ (RowChaos.Vq_nonneg ω)
              (gueEntryChaosEps_Vq_le_one C hε ω))
      _ = 1 := by simp
  have hc : (0 : ℝ) ≤ hwConst q := (hwConst_pos q).le
  refine h.trans ?_
  calc ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1)
        * (gueEntryChaosEps C ε hε).momVpow (q + 1)
      ≤ hwConst q * 1 := mul_le_mul_of_nonneg_left hV hc
    _ = hwConst q := mul_one _

theorem gueEntry_chaos_tail_eps (C : RowChaos D κ) {lam : ℝ} (hlam : 0 < lam) (q : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    (P D) {ω | lam * (C.Vq ω + ε) < ‖C.chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  set C' := gueEntryChaosEps C ε hε with hC'
  set Y : Ω D → ℝ := fun ω => ‖C'.chaos ω‖ with hY
  have hYnn : ∀ ω, 0 ≤ Y ω := fun ω => norm_nonneg _
  have habs : ∀ ω, |Y ω| ^ (2 * (q + 1)) = ‖C'.chaos ω‖ ^ (2 * (q + 1)) := fun ω => by
    rw [hY, abs_of_nonneg (hYnn ω)]
  have hint : Integrable (fun ω => |Y ω| ^ (2 * (q + 1))) (P D) := by
    simpa only [habs] using C'.integrable_norm_pow (gaussIBP D) (q + 1)
  have hmom0 : (∫ ω, ‖C'.chaos ω‖ ^ (2 * (q + 1)) ∂(P D)) ≤ hwConst q :=
    gueEntryChaosEps_mom_le C hε q
  have hmom : ∫ ω, |Y ω| ^ (2 * (q + 1)) ∂(P D) ≤ hwConst q := by
    simpa only [habs] using hmom0
  have ht : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hmark := meas_gt_le_of_moment (P := P D) (Y := Y) ht hint hmom
  have hset : {ω | lam * (C.Vq ω + ε) < ‖C.chaos ω‖ ^ 2} = {ω | Real.sqrt lam < Y ω} := by
    ext ω
    have hV0 := RowChaos.Vq_nonneg (C := C) ω
    have hs : 0 < Real.sqrt (C.Vq ω + ε) := Real.sqrt_pos.2 (by linarith)
    have hsq : Real.sqrt (C.Vq ω + ε) ^ 2 = C.Vq ω + ε := Real.sq_sqrt (by linarith)
    have hYv : Y ω = ‖C.chaos ω‖ / Real.sqrt (C.Vq ω + ε) := by
      change ‖(gueEntryChaosEps C ε hε).chaos ω‖ = _
      rw [gueEntryChaosEps_chaos C hε ω, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hs.le]
    have hc : (0 : ℝ) ≤ ‖C.chaos ω‖ := norm_nonneg _
    have hsl : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
    have hsln : (0 : ℝ) ≤ Real.sqrt lam := Real.sqrt_nonneg lam
    simp only [Set.mem_ofPred_eq, hYv]
    rw [lt_div_iff₀ hs]
    have hprod : (Real.sqrt lam * Real.sqrt (C.Vq ω + ε)) ^ 2 = lam * (C.Vq ω + ε) := by
      rw [mul_pow, hsl, hsq]
    have hp0 : 0 ≤ Real.sqrt lam * Real.sqrt (C.Vq ω + ε) := mul_nonneg hsln hs.le
    constructor
    · intro h
      by_contra hno
      have := pow_le_pow_left₀ hc (not_lt.1 hno) 2
      linarith
    · intro h
      have := pow_lt_pow_left₀ h hp0 (by norm_num : (2 : ℕ) ≠ 0)
      linarith
  rw [hset]
  refine hmark.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpow : Real.sqrt lam ^ (2 * (q + 1)) = lam ^ (q + 1) := by
    rw [pow_mul, Real.sq_sqrt hlam.le]
  rw [hpow]

/-- **The Hanson–Wright tail for an arbitrary row chaos**: `P(λ V_q < |Q|²) ≤ A_q / λ^{q+1}`,
with no condition on `V_q`. -/
theorem gueEntry_chaos_tail (C : RowChaos D κ) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    (P D) {ω | lam * C.Vq ω < ‖C.chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  set S : ℕ → Set (Ω D) := fun n =>
    {ω | lam * (C.Vq ω + 1 / ((n : ℝ) + 1)) < ‖C.chaos ω‖ ^ 2} with hS
  have hmono : Monotone S := by
    intro m n hmn ω hω
    simp only [hS, Set.mem_ofPred_eq] at hω ⊢
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hmn' : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
        have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
        linarith
      exact one_div_le_one_div_of_le hm hmn'
    nlinarith [hω, h1, hlam]
  have hunion : (⋃ n, S n) = {ω | lam * C.Vq ω < ‖C.chaos ω‖ ^ 2} := by
    ext ω
    simp only [Set.mem_iUnion, hS, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      nlinarith [hn, hlam, hpos]
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt
        (show (0 : ℝ) < (‖C.chaos ω‖ ^ 2 - lam * C.Vq ω) / lam by
          apply div_pos _ hlam; linarith)
      refine ⟨n, ?_⟩
      rw [lt_div_iff₀ hlam] at hn
      nlinarith [hn]
  rw [← hunion]
  refine le_of_tendsto (tendsto_measure_iUnion_atTop (μ := P D) hmono)
    (Filter.Eventually.of_forall fun n => ?_)
  exact gueEntry_chaos_tail_eps C hlam q (by positivity)

end ChaosTail

/-! ### Ward identities and the stability factor -/

section WardStab

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Ward, column form**: `∑_x |G_{xi}|² = Im G_{ii} / Im z`. -/
theorem gueEntry_ward_col {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (i : n) : ∑ x, ‖green H z x i‖ ^ 2 = (green H z i i).im / z.im := by
  have h := im_green_diag hH hz i
  have hdot : (star (green H z *ᵥ Pi.single i 1) ⬝ᵥ (green H z *ᵥ Pi.single i 1)).re
      = ∑ x, ‖green H z x i‖ ^ 2 := by
    have hv : ∀ x, (green H z *ᵥ Pi.single i 1) x = green H z x i := by
      intro x; simp
    simp only [dotProduct, Pi.star_apply, hv]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [RCLike.star_def, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.mul_re]
  rw [hdot] at h
  rw [h]; field_simp

theorem gueEntry_green_transpose {H : Matrix n n ℂ} (z : ℂ) :
    (green H z)ᵀ = green Hᵀ z := by
  unfold green
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one]

/-- **Ward, row form**: `∑_l |G_{kl}|² = Im G_{kk} / Im z`. -/
theorem gueEntry_ward_row {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (k : n) : ∑ l, ‖green H z k l‖ ^ 2 = (green H z k k).im / z.im := by
  have hHt : (Hᵀ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose, Matrix.transpose_transpose]
    have := hH.eq
    rw [Matrix.conjTranspose] at this
    ext a b
    have h2 := congrArg (fun M => M b a) this
    simp only [Matrix.map_apply, Matrix.transpose_apply] at h2 ⊢
    exact h2
  have h := gueEntry_ward_col hHt hz k
  have ht : ∀ a b, green Hᵀ z a b = green H z b a := by
    intro a b
    rw [← gueEntry_green_transpose]; rfl
  simp only [ht] at h
  exact h

end WardStab

/-! ### The GUE-phase profile and its deterministic properties -/

section Profile

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The GUE-phase variance profile `S_u = a S + b` (entry variances); along the grid
`a = t₁`, `b = (u - t₁)/M`. -/
def gueEntryProf (L W : ℕ) (a b : ℝ) (x y : ZMod L × Fin W) : ℝ := a * Sblk L W x y + b

omit [NeZero L] [NeZero W] in
theorem gueEntryProf_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : ZMod L × Fin W) :
    0 ≤ gueEntryProf L W a b x y :=
  add_nonneg (mul_nonneg ha (Sblk_nonneg _ _)) hb

omit [NeZero W] in
theorem gueEntry_card_idx : (Fintype.card (ZMod L × Fin W) : ℝ) = ((L * W : ℕ) : ℝ) := by
  rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]

theorem gueEntryProf_sum_row (hL : 3 ≤ L) (a b : ℝ) (x : ZMod L × Fin W) :
    ∑ y, gueEntryProf L W a b x y = a + ((L * W : ℕ) : ℝ) * b := by
  simp only [gueEntryProf, Finset.sum_add_distrib, ← Finset.mul_sum, sum_Sblk_row hL,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, gueEntry_card_idx]
  ring

theorem gueEntryProf_sum_col (hL : 3 ≤ L) (a b : ℝ) (y : ZMod L × Fin W) :
    ∑ x, gueEntryProf L W a b x y = a + ((L * W : ℕ) : ℝ) * b := by
  simp only [gueEntryProf, Finset.sum_add_distrib, ← Finset.mul_sum, sum_Sblk_col hL,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, gueEntry_card_idx]
  ring

omit [NeZero L] [NeZero W] in
theorem gueEntryProf_symm (a b : ℝ) (x y : ZMod L × Fin W) :
    gueEntryProf L W a b x y = gueEntryProf L W a b y x := by
  unfold gueEntryProf; rw [Sblk_comm]

/-- **Stability of `1 - u m² S'`**, `S' = S_u / u`, uniformly: the `J`-part is removed by
averaging, since `|1 - u m²| ≥ √κ`. -/
theorem gueEntry_stable (hL : 3 ≤ L) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : u = a + ((L * W : ℕ) : ℝ) * b) (hupos : 0 < u)
    (hu1 : u < 1) :
    Stable (fun x y => gueEntryProf L W a b x y / u) ((u : ℂ) * mE E ^ 2)
      (Kstab κ * (1 + 1 / Real.sqrt κ)) := by
  intro v B hB i
  set m := mE E with hm
  set M : ℝ := ((L * W : ℕ) : ℝ) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]; exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L))
      (Nat.pos_of_ne_zero (NeZero.ne W))
  have hne : Nonempty (ZMod L × Fin W) := ⟨(0, ⟨0, Nat.pos_of_ne_zero (NeZero.ne W)⟩)⟩
  obtain ⟨j₀⟩ := hne
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB j₀)
  set V : ℂ := ∑ k, v k with hV
  have hsk : Real.sqrt κ ≤ ‖1 - (u : ℂ) * m ^ 2‖ :=
    sqrt_le_norm_one_sub_short hκ0 hκ1 hE hupos.le hu1.le
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ0
  -- the key identity
  have hkey : ∀ j, (u : ℂ) * m ^ 2 * ∑ k, ((gueEntryProf L W a b j k / u : ℝ) : ℂ) * v k
      = (a : ℂ) * m ^ 2 * ∑ k, (Sblk L W j k : ℂ) * v k + (b : ℂ) * m ^ 2 * V := by
    intro j
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hupos.ne'
    have : ∀ k, (u : ℂ) * (((gueEntryProf L W a b j k / u : ℝ) : ℂ) * v k)
        = (a : ℂ) * ((Sblk L W j k : ℂ) * v k) + (b : ℂ) * v k := by
      intro k
      simp only [gueEntryProf]
      push_cast
      field_simp
    calc (u : ℂ) * m ^ 2 * ∑ k, ((gueEntryProf L W a b j k / u : ℝ) : ℂ) * v k
        = m ^ 2 * ∑ k, (u : ℂ) * (((gueEntryProf L W a b j k / u : ℝ) : ℂ) * v k) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = m ^ 2 * ∑ k, ((a : ℂ) * ((Sblk L W j k : ℂ) * v k) + (b : ℂ) * v k) := by
          simp only [this]
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hV]
          ring
  set r : ZMod L × Fin W → ℂ := fun j =>
    v j - (u : ℂ) * m ^ 2 * ∑ k, ((gueEntryProf L W a b j k / u : ℝ) : ℂ) * v k with hr
  have hrB : ∀ j, ‖r j‖ ≤ B := hB
  -- the average
  have hSV : ∑ j, ∑ k, (Sblk L W j k : ℂ) * v k = V := by
    rw [Finset.sum_comm, hV]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ j, (Sblk L W j k : ℂ) = 1 := by exact_mod_cast sum_Sblk_col hL k
    rw [this, one_mul]
  have hsumr : ∑ j, r j = (1 - (u : ℂ) * m ^ 2) * V := by
    simp only [hr, hkey, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hSV,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hV]
    have hcard : ((Fintype.card (ZMod L × Fin W) : ℕ) : ℂ) = (M : ℂ) := by
      rw [hMdef]; exact_mod_cast gueEntry_card_idx
    rw [hcard, hu]
    push_cast
    ring
  have hnorm_sumr : ‖∑ j, r j‖ ≤ M * B := by
    calc ‖∑ j, r j‖ ≤ ∑ j, ‖r j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : ZMod L × Fin W, B := Finset.sum_le_sum fun j _ => hrB j
      _ = M * B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, gueEntry_card_idx]
  have hVle : ‖V‖ ≤ M * B / Real.sqrt κ := by
    rw [le_div_iff₀ hsκ]
    calc ‖V‖ * Real.sqrt κ ≤ ‖V‖ * ‖1 - (u : ℂ) * m ^ 2‖ :=
          mul_le_mul_of_nonneg_left hsk (norm_nonneg _)
      _ = ‖∑ j, r j‖ := by rw [hsumr, norm_mul, mul_comm]
      _ ≤ M * B := hnorm_sumr
  have hbM : b * M ≤ 1 := by
    have : b * M = u - a := by rw [hu]; ring
    rw [this]; linarith
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hm1 : ‖m‖ = 1 := norm_mE hE2
  have hr' : ∀ j, ‖v j - (a : ℂ) * m ^ 2 * ∑ k, (Sblk L W j k : ℂ) * v k‖
      ≤ B + B / Real.sqrt κ := by
    intro j
    have hj : v j - (a : ℂ) * m ^ 2 * ∑ k, (Sblk L W j k : ℂ) * v k
        = r j + (b : ℂ) * m ^ 2 * V := by
      simp only [hr, hkey]; ring
    rw [hj]
    calc ‖r j + (b : ℂ) * m ^ 2 * V‖ ≤ ‖r j‖ + ‖(b : ℂ) * m ^ 2 * V‖ := norm_add_le _ _
      _ = ‖r j‖ + b * ‖V‖ := by
          rw [norm_mul, norm_mul, norm_pow, hm1, one_pow, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hb]
      _ ≤ B + b * (M * B / Real.sqrt κ) :=
          add_le_add (hrB j) (mul_le_mul_of_nonneg_left hVle hb)
      _ ≤ B + B / Real.sqrt κ := by
          have : b * (M * B / Real.sqrt κ) = (b * M) * (B / Real.sqrt κ) := by ring
          rw [this]
          have hBk : 0 ≤ B / Real.sqrt κ := div_nonneg hB0 hsκ.le
          nlinarith
  have ha1 : a < 1 := by
    have : 0 ≤ ((L * W : ℕ) : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb
    linarith
  have hst := stable_Sblk_short_edge (W := W) hL hκ0 hκ1 hE ha ha1 v (B + B / Real.sqrt κ) hr' i
  calc ‖v i‖ ≤ Kstab κ * (B + B / Real.sqrt κ) := hst
    _ = Kstab κ * (1 + 1 / Real.sqrt κ) * B := by ring

end Profile

/-! ### The `J`-part: Ward and the lower bound on `max L₂` -/

section Lambda

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

omit [NeZero W] in
/-- On the good event, `Im G_{xx} ≥ Im m / 2`. -/
theorem gueEntry_im_diag_ge {m : ℂ} {δ : ℝ} (hΩ : GoodEvent (green H z) m δ)
    (hδ : δ ≤ m.im / 2) (x : ZMod L × Fin W) : m.im / 2 ≤ (green H z x x).im := by
  have h1 := hΩ.norm_diag_sub_le x
  have h2 : |(green H z x x - m).im| ≤ ‖green H z x x - m‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at h2
  have := neg_abs_le ((green H z x x).im - m.im)
  linarith

omit [NeZero W] in
/-- On the good event, `Im G_{xx} ≤ 3/2`. -/
theorem gueEntry_im_diag_le {m : ℂ} (hm : ‖m‖ = 1) {δ : ℝ} (hΩ : GoodEvent (green H z) m δ)
    (hδ : δ ≤ 1 / 2) (x : ZMod L × Fin W) : (green H z x x).im ≤ 3 / 2 := by
  have h1 := hΩ.norm_diag_le hm x
  have h2 : |(green H z x x).im| ≤ ‖green H z x x‖ := Complex.abs_im_le_norm _
  have := le_abs_self (green H z x x).im
  linarith

/-- **The lower bound `(M η)⁻¹ ≤ (2 / Im m) max L₂`** on the good event (Ward over a block
column). -/
theorem gueEntry_inv_Meta_le (hH : H.IsHermitian) (hz : 0 < z.im) {m : ℂ} (him : 0 < m.im)
    {δ : ℝ} (hΩ : GoodEvent (green H z) m δ) (hδ : δ ≤ m.im / 2) :
    1 / (((L * W : ℕ) : ℝ) * z.im) ≤ 2 / m.im * Lmax H z := by
  have hW : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set a0 : ZMod L := 0
  have hsum : ∑ b : ZMod L, Lre H z a0 b
      = ((W : ℝ)⁻¹) ^ 2 * ∑ α : Fin W, (green H z (a0, α) (a0, α)).im / z.im := by
    simp only [Lre_eq hH, ← Finset.mul_sum]
    congr 1
    calc ∑ b : ZMod L, ∑ β : Fin W, ∑ α : Fin W, ‖green H z (b, β) (a0, α)‖ ^ 2
        = ∑ b : ZMod L, ∑ α : Fin W, ∑ β : Fin W, ‖green H z (b, β) (a0, α)‖ ^ 2 :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ α : Fin W, ∑ b : ZMod L, ∑ β : Fin W, ‖green H z (b, β) (a0, α)‖ ^ 2 :=
          Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [← gueEntry_ward_col hH hz.ne' (a0, α), Fintype.sum_prod_type]
  have hlow : ((W : ℝ)⁻¹) ^ 2 * ((W : ℝ) * (m.im / 2 / z.im))
      ≤ ∑ b : ZMod L, Lre H z a0 b := by
    rw [hsum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (W : ℝ) * (m.im / 2 / z.im) = ∑ _α : Fin W, m.im / 2 / z.im := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun α _ =>
          div_le_div_of_nonneg_right (gueEntry_im_diag_ge hΩ hδ _) hz.le
  have hup : ∑ b : ZMod L, Lre H z a0 b ≤ (L : ℝ) * Lmax H z := by
    calc ∑ b : ZMod L, Lre H z a0 b ≤ ∑ _b : ZMod L, Lmax H z :=
          Finset.sum_le_sum fun b _ => Lre_le_Lmax a0 b
      _ = (L : ℝ) * Lmax H z := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hkey : m.im / (2 * (W : ℝ) * z.im) ≤ (L : ℝ) * Lmax H z := by
    have : ((W : ℝ)⁻¹) ^ 2 * ((W : ℝ) * (m.im / 2 / z.im)) = m.im / (2 * (W : ℝ) * z.im) := by
      field_simp
    linarith
  push_cast
  rw [div_le_iff₀ (by positivity)]
  have e : 2 / m.im * Lmax H z * ((L : ℝ) * W * z.im)
      = 2 * (W : ℝ) * z.im / m.im * ((L : ℝ) * Lmax H z) := by ring
  rw [e]
  have hpos : 0 < 2 * (W : ℝ) * z.im / m.im := by positivity
  calc (1 : ℝ) = 2 * (W : ℝ) * z.im / m.im * (m.im / (2 * (W : ℝ) * z.im)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hkey hpos.le

/-- **The two-sided sum with the normalised GUE-phase profile** is `≤ (1 + 3/Im m) max L₂`. -/
theorem gueEntry_sum_prof_le (hL : 3 ≤ L) (hH : H.IsHermitian) (hz : 0 < z.im) {m : ℂ}
    (hm : ‖m‖ = 1) (him : 0 < m.im) {δ : ℝ} (hΩ : GoodEvent (green H z) m δ)
    (hδ12 : δ ≤ 1 / 2) (hδm : δ ≤ m.im / 2) {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : u = a + ((L * W : ℕ) : ℝ) * b) (hupos : 0 < u) (i j : ZMod L × Fin W) :
    ∑ k, ∑ l, gueEntryProf L W a b i k / u * ‖green H z k l‖ ^ 2 * (gueEntryProf L W a b l j / u)
      ≤ (1 + 3 / m.im) * Lmax H z := by
  set G := green H z with hG
  set M : ℝ := ((L * W : ℕ) : ℝ) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]; exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L))
      (Nat.pos_of_ne_zero (NeZero.ne W))
  have hLm := Lmax_nonneg (z := z) hH
  set Y : ℝ := 3 / 2 / z.im with hY
  have hR : ∀ k, ∑ l, ‖G k l‖ ^ 2 ≤ Y := by
    intro k
    rw [gueEntry_ward_row hH hz.ne' k]
    exact div_le_div_of_nonneg_right (gueEntry_im_diag_le hm hΩ hδ12 k) hz.le
  have hC : ∀ l, ∑ k, ‖G k l‖ ^ 2 ≤ Y := by
    intro l
    rw [gueEntry_ward_col hH hz.ne' l]
    exact div_le_div_of_nonneg_right (gueEntry_im_diag_le hm hΩ hδ12 l) hz.le
  have hYle : Y ≤ 3 * M / m.im * Lmax H z := by
    have h := gueEntry_inv_Meta_le hH hz him hΩ hδm
    have e : Y = 3 / 2 * M * (1 / (M * z.im)) := by rw [hY]; field_simp
    rw [e]
    calc 3 / 2 * M * (1 / (M * z.im)) ≤ 3 / 2 * M * (2 / m.im * Lmax H z) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 3 * M / m.im * Lmax H z := by field_simp
  have hS := fun x y => Sblk_nonneg (L := L) (W := W) x y
  -- expansion
  have hpt : ∀ k l, gueEntryProf L W a b i k / u * ‖G k l‖ ^ 2 * (gueEntryProf L W a b l j / u)
      = (u ^ 2)⁻¹ * (a ^ 2 * (Sblk L W i k * ‖G k l‖ ^ 2 * Sblk L W l j)
        + a * b * (Sblk L W i k * ‖G k l‖ ^ 2) + a * b * (‖G k l‖ ^ 2 * Sblk L W l j)
        + b ^ 2 * ‖G k l‖ ^ 2) := by
    intro k l; simp only [gueEntryProf]; field_simp; ring
  have hT1 := sum_sum_Sblk_le_Lmax (z := z) hL hH i j
  have hT2 : ∑ k, ∑ l, Sblk L W i k * ‖G k l‖ ^ 2 ≤ Y := by
    calc ∑ k, ∑ l, Sblk L W i k * ‖G k l‖ ^ 2 = ∑ k, Sblk L W i k * ∑ l, ‖G k l‖ ^ 2 := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ k, Sblk L W i k * Y :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hR k) (hS i k)
      _ = Y := by rw [← Finset.sum_mul, sum_Sblk_row hL, one_mul]
  have hT3 : ∑ k, ∑ l, ‖G k l‖ ^ 2 * Sblk L W l j ≤ Y := by
    calc ∑ k, ∑ l, ‖G k l‖ ^ 2 * Sblk L W l j = ∑ l, (∑ k, ‖G k l‖ ^ 2) * Sblk L W l j := by
          rw [Finset.sum_comm]; simp only [Finset.sum_mul]
      _ ≤ ∑ l, Y * Sblk L W l j :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hC l) (hS l j)
      _ = Y := by rw [← Finset.mul_sum, sum_Sblk_col hL, mul_one]
  have hT4 : ∑ k, ∑ l, ‖G k l‖ ^ 2 ≤ M * Y := by
    calc ∑ k, ∑ l, ‖G k l‖ ^ 2 ≤ ∑ _k : ZMod L × Fin W, Y := Finset.sum_le_sum fun k _ => hR k
      _ = M * Y := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, gueEntry_card_idx]
  have hsplit : ∑ k, ∑ l, gueEntryProf L W a b i k / u * ‖G k l‖ ^ 2
        * (gueEntryProf L W a b l j / u)
      = (u ^ 2)⁻¹ * (a ^ 2 * ∑ k, ∑ l, Sblk L W i k * ‖G k l‖ ^ 2 * Sblk L W l j
        + a * b * ∑ k, ∑ l, Sblk L W i k * ‖G k l‖ ^ 2
        + a * b * ∑ k, ∑ l, ‖G k l‖ ^ 2 * Sblk L W l j
        + b ^ 2 * ∑ k, ∑ l, ‖G k l‖ ^ 2) := by
    simp only [hpt, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsplit]
  have hu2 : 0 < u ^ 2 := by positivity
  rw [inv_mul_le_iff₀ hu2]
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have e1 : a ^ 2 * ∑ k, ∑ l, Sblk L W i k * ‖G k l‖ ^ 2 * Sblk L W l j ≤ a ^ 2 * Lmax H z :=
    mul_le_mul_of_nonneg_left hT1 (sq_nonneg a)
  have e2 := mul_le_mul_of_nonneg_left hT2 hab
  have e3 := mul_le_mul_of_nonneg_left hT3 hab
  have e4 := mul_le_mul_of_nonneg_left hT4 hb2
  have hY' : (2 * a * b + b ^ 2 * M) * Y ≤ (u ^ 2 - a ^ 2) * (3 / m.im) * Lmax H z := by
    have hc : 0 ≤ 2 * a * b + b ^ 2 * M := by positivity
    calc (2 * a * b + b ^ 2 * M) * Y ≤ (2 * a * b + b ^ 2 * M) * (3 * M / m.im * Lmax H z) :=
          mul_le_mul_of_nonneg_left hYle hc
      _ = (u ^ 2 - a ^ 2) * (3 / m.im) * Lmax H z := by rw [hu]; field_simp; ring
  have hfin : a ^ 2 * Lmax H z + (u ^ 2 - a ^ 2) * (3 / m.im) * Lmax H z
      ≤ u ^ 2 * ((1 + 3 / m.im) * Lmax H z) := by
    have h3 : 0 ≤ 3 / m.im * Lmax H z := by positivity
    have ha2 : a ^ 2 ≤ u ^ 2 := by
      have : a ≤ u := by rw [hu]; nlinarith
      exact pow_le_pow_left₀ ha this 2
    nlinarith
  nlinarith

end Lambda

/-! ### The deterministic core for the GUE-phase profile -/

section DetCore

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}

/-- `c_κ = √(2κ)/2 ≤ Im m(E)`. -/
def gueEntryC (κ : ℝ) : ℝ := Real.sqrt (2 * κ) / 2

/-- The stability constant `K_stab(κ)(1 + κ^{-1/2})`. -/
def gueEntryK (κ : ℝ) : ℝ := Kstab κ * (1 + 1 / Real.sqrt κ)

/-- The smallness threshold for `δ`. -/
def gueEntryDelta (κ : ℝ) : ℝ := min (1 / 2) (min (1 / (2 * gueEntryK κ)) (gueEntryC κ / 2))

/-- The constant of the deterministic bound. -/
def gueEntryCdet (κ : ℝ) : ℝ := (2160 * gueEntryK κ ^ 2 + 162) * (1 + 3 / gueEntryC κ)

theorem gueEntryC_pos {κ : ℝ} (hκ : 0 < κ) : 0 < gueEntryC κ := by
  unfold gueEntryC; have : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.2 (by linarith); positivity

theorem gueEntryK_one_le {κ : ℝ} (hκ : 0 < κ) : 1 ≤ gueEntryK κ := by
  unfold gueEntryK
  have h1 : (1 : ℝ) ≤ Kstab κ := by
    have h1 := cTwo52_pos
    have h2 := cZero_pos
    unfold Kstab
    have : 0 ≤ 2 * cTwo52 * (1 / cZero + 2) / Real.sqrt κ := by positivity
    linarith
  have h2 : (1 : ℝ) ≤ 1 + 1 / Real.sqrt κ := by
    have : 0 ≤ 1 / Real.sqrt κ := by positivity
    linarith
  nlinarith

theorem gueEntryDelta_pos {κ : ℝ} (hκ : 0 < κ) : 0 < gueEntryDelta κ := by
  unfold gueEntryDelta
  have hK := gueEntryK_one_le hκ
  have hc := gueEntryC_pos hκ
  refine lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem gueEntryCdet_nonneg {κ : ℝ} (hκ : 0 < κ) : 0 ≤ gueEntryCdet κ := by
  unfold gueEntryCdet
  have hc := gueEntryC_pos hκ
  positivity

omit [NeZero W] in
theorem gueEntry_Lmax_le_loopMax (z : ℂ) : Lmax H z ≤ loopMax L W H z 2 := by
  refine Finset.sup'_le _ _ fun p _ => ?_
  refine (Complex.re_le_norm _).trans ?_
  exact norm_gloop_le_loopMax _ rfl rfl

omit [NeZero W] in
theorem gueEntry_ldeRowRHS_smul (u : ℝ) (S : ZMod L × Fin W → ZMod L × Fin W → ℝ)
    (G : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (i j : ZMod L × Fin W) :
    ldeRowRHS (fun x y => u * S x y) G i j = u * ldeRowRHS S G i j := by
  unfold ldeRowRHS; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

omit [NeZero W] in
theorem gueEntry_ldeColRHS_smul (u : ℝ) (S : ZMod L × Fin W → ZMod L × Fin W → ℝ)
    (G : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (i j : ZMod L × Fin W) :
    ldeColRHS (fun x y => u * S x y) G i j = u * ldeColRHS S G i j := by
  unfold ldeColRHS; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

omit [NeZero W] in
theorem gueEntry_ldeQuadRHS_smul (u : ℝ) (S : ZMod L × Fin W → ZMod L × Fin W → ℝ)
    (G : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (i : ZMod L × Fin W) :
    ldeQuadRHS (fun x y => u * S x y) G i = u ^ 2 * ldeQuadRHS S G i := by
  unfold ldeQuadRHS; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring

omit [NeZero W] in
theorem gueEntry_ldeQuadLHS_smul (u : ℝ) (S : ZMod L × Fin W → ZMod L × Fin W → ℝ)
    (H G : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (i : ZMod L × Fin W) :
    ldeQuadLHS H G (fun x y => u * S x y) 1 i = ldeQuadLHS H G S u i := by
  unfold ldeQuadLHS
  congr 2
  push_cast
  rw [one_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Lemma 4.1 (4.2)+(4.3) for the GUE-phase profile, deterministic form.** On the good event,
given the four large deviation inputs with the profile `S_u = a S + b` and factor `Φ`,
`|G_{ij} - m δ_{ij}|² ≤ C_κ Φ² (max L₂ + W⁻¹)`. -/
theorem gueEntry_det (hL : 3 ≤ L) (hH : H.IsHermitian) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : u = a + ((L * W : ℕ) : ℝ) * b) (hupos : 0 < u) (hu1 : u < 1) {δ Φ : ℝ}
    (hΩ : GoodEvent (green H (zt E u)) (mE E) δ) (hδ : δ ≤ gueEntryDelta κ) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hrow : ∀ i j, i ≠ j → ldeRowLHS H (green H (zt E u)) i j
      ≤ Φ * ldeRowRHS (gueEntryProf L W a b) (green H (zt E u)) i j)
    (hcol : ∀ k j, k ≠ j → ldeColLHS H (green H (zt E u)) k j
      ≤ Φ * ldeColRHS (gueEntryProf L W a b) (green H (zt E u)) k j)
    (hquad : ∀ i, ldeQuadLHS H (green H (zt E u)) (gueEntryProf L W a b) 1 i
      ≤ Φ * ldeQuadRHS (gueEntryProf L W a b) (green H (zt E u)) i)
    (hdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * gueEntryProf L W a b i i) (i j : ZMod L × Fin W) :
    ‖(green H (zt E u) - mE E • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) i j‖ ^ 2
      ≤ gueEntryCdet κ * Φ ^ 2 * (loopMax L W H (zt E u) 2 + ((W : ℕ) : ℝ)⁻¹) := by
  set z := zt E u with hzdef
  set m := mE E with hmdef
  set G := green H z with hGdef
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hm : ‖m‖ = 1 := norm_mE hE2
  have hmim : gueEntryC κ ≤ m.im := mE_im_ge hκ0 (by linarith) hE
  have hc := gueEntryC_pos hκ0
  have him : 0 < m.im := lt_of_lt_of_le hc hmim
  have hzpos : 0 < z.im := by
    rw [hzdef, zt_im]; exact mul_pos (by linarith) him
  have hz : z.im ≠ 0 := hzpos.ne'
  have hK1 := gueEntryK_one_le hκ0
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i i)
  have hδ12 : δ ≤ 1 / 2 := hδ.trans (min_le_left _ _)
  have hδK : gueEntryK κ * δ ≤ 1 / 2 := by
    have h1 : δ ≤ 1 / (2 * gueEntryK κ) := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ gueEntryK κ)
    rwa [show gueEntryK κ * (1 / (2 * gueEntryK κ)) = 1 / 2 by field_simp] at h2
  have hδc : δ ≤ m.im / 2 := by
    have h1 : δ ≤ gueEntryC κ / 2 := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  set S' : ZMod L × Fin W → ZMod L × Fin W → ℝ := fun x y => gueEntryProf L W a b x y / u
    with hS'def
  have hprof : gueEntryProf L W a b = fun x y => u * S' x y := by
    funext x y; simp only [hS'def]; field_simp
  have hS0 : ∀ x y, 0 ≤ S' x y := fun x y => div_nonneg (gueEntryProf_nonneg ha hb x y) hupos.le
  have hSrow : ∀ x, ∑ y, S' x y = 1 := by
    intro x; simp only [hS'def, ← Finset.sum_div, gueEntryProf_sum_row hL, ← hu]
    exact div_self hupos.ne'
  have hScol : ∀ y, ∑ x, S' x y ≤ 1 := by
    intro y; simp only [hS'def, ← Finset.sum_div, gueEntryProf_sum_col hL, ← hu]
    rw [div_self hupos.ne']
  have hW : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hS'W : ∀ x y, S' x y ≤ (W : ℝ)⁻¹ := by
    intro x y
    simp only [hS'def, gueEntryProf]
    rw [div_le_iff₀ hupos, hu]
    have h1 : Sblk L W x y ≤ 1 / 3 * (W : ℝ)⁻¹ := by
      rw [Sblk, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (sbKre_le _) (by positivity)
    have h2 : b ≤ ((L * W : ℕ) : ℝ) * b * (W : ℝ)⁻¹ := by
      have e : ((L * W : ℕ) : ℝ) * b * (W : ℝ)⁻¹ = (L : ℝ) * b := by
        push_cast; field_simp
      rw [e]; nlinarith
    have h3 : a * Sblk L W x y ≤ a * (W : ℝ)⁻¹ := by
      refine mul_le_mul_of_nonneg_left (h1.trans ?_) ha
      have : 0 ≤ (W : ℝ)⁻¹ := by positivity
      linarith
    nlinarith
  have hu1' : u ≤ 1 := hu1.le
  -- the four inputs in the normalised form
  have hLr : LDERow H G S' Φ := by
    intro i j hij
    have h := hrow i j hij
    rw [hprof, gueEntry_ldeRowRHS_smul] at h
    have hR : 0 ≤ ldeRowRHS S' G i j :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hS0 _ _) (sq_nonneg _)
    have : Φ * (u * ldeRowRHS S' G i j) ≤ Φ * ldeRowRHS S' G i j :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  have hLc : LDECol H G S' Φ := by
    intro k j hkj
    have h := hcol k j hkj
    rw [hprof, gueEntry_ldeColRHS_smul] at h
    have hR : 0 ≤ ldeColRHS S' G k j :=
      Finset.sum_nonneg fun l _ => mul_nonneg (sq_nonneg _) (hS0 _ _)
    have : Φ * (u * ldeColRHS S' G k j) ≤ Φ * ldeColRHS S' G k j :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  have hLq : LDEQuad H G S' u Φ := by
    intro i
    have h := hquad i
    rw [hprof, gueEntry_ldeQuadLHS_smul, gueEntry_ldeQuadRHS_smul] at h
    have hR : 0 ≤ ldeQuadRHS S' G i :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        mul_nonneg (mul_nonneg (hS0 _ _) (sq_nonneg _)) (hS0 _ _)
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    have : Φ * (u ^ 2 * ldeQuadRHS S' G i) ≤ Φ * ldeQuadRHS S' G i :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  have hLd : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S' i i := by
    intro i
    have h := hdiag i
    rw [hprof] at h
    have : Φ * (u * S' i i) ≤ Φ * S' i i :=
      mul_le_mul_of_nonneg_left (by nlinarith [hS0 i i]) (by linarith)
    linarith
  -- `Λ`
  set Λ : ℝ := (1 + 3 / gueEntryC κ) * Lmax H z + (W : ℝ)⁻¹ with hΛdef
  have hLm0 : 0 ≤ Lmax H z := Lmax_nonneg hH
  have h3c : 3 / m.im ≤ 3 / gueEntryC κ := div_le_div_of_nonneg_left (by norm_num) hc hmim
  have hΛ1 : ∀ i j, ∑ k, ∑ l, S' i k * ‖G k l‖ ^ 2 * S' l j ≤ Λ := by
    intro i j
    have h := gueEntry_sum_prof_le hL hH hzpos hm him hΩ hδ12 hδc ha hb hu hupos i j
    have h2 : (1 + 3 / m.im) * Lmax H z ≤ (1 + 3 / gueEntryC κ) * Lmax H z :=
      mul_le_mul_of_nonneg_right (by linarith) hLm0
    have h3 : 0 ≤ (W : ℝ)⁻¹ := by positivity
    simp only [hS'def]
    linarith
  have hΛ2 : ∀ i j, S' i j ≤ Λ := by
    intro i j
    have : 0 ≤ (1 + 3 / gueEntryC κ) * Lmax H z := by positivity
    linarith [hS'W i j]
  have hGM := green_mul_sub_of_im hH hz
  have hMG := sub_mul_green_of_im hH hz
  have hΩ' : GoodEvent G m δ := hΩ
  have hΛle : Λ ≤ (1 + 3 / gueEntryC κ) * (loopMax L W H z 2 + ((W : ℕ) : ℝ)⁻¹) := by
    have h1 := gueEntry_Lmax_le_loopMax (H := H) z
    have h4 : 0 ≤ 3 / gueEntryC κ * (W : ℝ)⁻¹ := by positivity
    have : (1 + 3 / gueEntryC κ) * Lmax H z ≤ (1 + 3 / gueEntryC κ) * loopMax L W H z 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hΛdef]; nlinarith
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΦ2 : 0 ≤ Φ ^ 2 := sq_nonneg Φ
  have hfinal : ∀ X : ℝ, X ≤ (2160 * gueEntryK κ ^ 2 + 162) * Φ ^ 2 * Λ →
      X ≤ gueEntryCdet κ * Φ ^ 2 * (loopMax L W H z 2 + ((W : ℕ) : ℝ)⁻¹) := by
    intro X hX
    refine hX.trans ?_
    unfold gueEntryCdet
    have hA : 0 ≤ (2160 * gueEntryK κ ^ 2 + 162) * Φ ^ 2 := by positivity
    calc (2160 * gueEntryK κ ^ 2 + 162) * Φ ^ 2 * Λ
        ≤ (2160 * gueEntryK κ ^ 2 + 162) * Φ ^ 2 *
          ((1 + 3 / gueEntryC κ) * (loopMax L W H z 2 + ((W : ℕ) : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hΛle hA
      _ = _ := by ring
  by_cases hij : i = j
  · subst hij
    have hentry : (G - m • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) i i = G i i - m := by
      simp
    rw [hentry]
    have hStab := gueEntry_stable (W := W) hL hκ0 hκ1 hE ha hb hu hupos hu1
    have h := norm_sq_green_diag_sub_le hGM hMG hm (mE_mul_add_zt hE2 u) hupos.le hu1' hΩ'
      hδ12 hS0 hSrow hScol hΦ1 hΦδ hLr hLc hLq hLd hΛ1 hΛ2 hδK hStab i
    refine hfinal _ (h.trans ?_)
    have h0 : 0 ≤ Φ ^ 2 * Λ := mul_nonneg hΦ2 hΛ0
    calc 2160 * gueEntryK κ ^ 2 * Φ ^ 2 * Λ = 2160 * gueEntryK κ ^ 2 * (Φ ^ 2 * Λ) := by ring
      _ ≤ (2160 * gueEntryK κ ^ 2 + 162) * (Φ ^ 2 * Λ) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
      _ = (2160 * gueEntryK κ ^ 2 + 162) * Φ ^ 2 * Λ := by ring
  · have hentry : (G - m • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) i j = G i j := by
      simp [hij]
    rw [hentry]
    have h := norm_sq_green_offdiag_le hGM hMG hm hΩ' hδ12 hS0 (fun x => (hSrow x).le) hScol
      hΦ1 hΦδ hLr hLc hΛ1 hΛ2 hij
    refine hfinal _ (h.trans ?_)
    have h0 : 0 ≤ Φ ^ 2 * Λ := mul_nonneg hΦ2 hΛ0
    have hK2 : 0 ≤ 2160 * gueEntryK κ ^ 2 := by positivity
    calc 162 * Φ ^ 2 * Λ = 162 * (Φ ^ 2 * Λ) := by ring
      _ ≤ (2160 * gueEntryK κ ^ 2 + 162) * (Φ ^ 2 * Λ) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
      _ = (2160 * gueEntryK κ ^ 2 + 162) * Φ ^ 2 * Λ := by ring

end DetCore

/-! ### The auxiliary matrix and its row chaoses -/

section AuxModel

/-- The auxiliary matrix `H = X_d(T ω)` on the auxiliary carrier `P gueEntryDG`. -/
def gueEntryHG (N : ℕ) (v : Coord d → ℝ≥0) (ω : Ω gueEntryDG) : Matrix (d.Idx N) (d.Idx N) ℂ :=
  Hflow d N 1 (gueEntryT d v ω)

variable {d}

theorem gueEntryHG_isHermitian (N : ℕ) (v : Coord d → ℝ≥0) (ω : Ω gueEntryDG) :
    (gueEntryHG d N v ω).IsHermitian := Hflow_isHermitian d N 1 _

theorem gueEntryHG_continuous (N : ℕ) (v : Coord d → ℝ≥0) :
    Continuous (gueEntryHG d N v) :=
  (continuous_Hflow d N 1).comp (gueEntryT_continuous d v)

theorem gueEntryHG_measurable (N : ℕ) (v : Coord d → ℝ≥0) :
    Measurable (gueEntryHG d N v) := (gueEntryHG_continuous N v).measurable

theorem gueEntry_Hflow_one (N : ℕ) : Hflow d N 1 = Xmat d N := by
  funext ω; rw [Hflow_eq_realSmul, Real.sqrt_one, one_smul]

/-- **The law of the grid path at step `k` is the law of the auxiliary matrix.** -/
theorem gueEntry_law_HG (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    (Pgue d).map (gueH d t1 t0 K N k)
      = (P gueEntryDG).map (gueEntryHG d N (gueEntryVar d t1 t0 K N k)) := by
  rw [gueEntry_law]
  unfold gueEntryHG
  rw [gueEntry_Hflow_one]

/-- A variance function that does not see the real/imaginary tag. -/
def GueEntryTagFree (v : Coord d → ℝ≥0) : Prop :=
  ∀ (N : ℕ) (x y : d.Idx N) (b : Bool), v ⟨N, x, y, b⟩ = v ⟨N, x, y, true⟩

theorem gueEntryVar_tagFree (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    GueEntryTagFree (gueEntryVar d t1 t0 K N k) := fun _ _ _ _ => rfl

theorem gueEntryScale_tag {v : Coord d → ℝ≥0} (hv : GueEntryTagFree v) (N : ℕ)
    (x y : d.Idx N) (b : Bool) :
    gueEntryScale d v ⟨N, x, y, b⟩ = gueEntryScale d v ⟨N, x, y, true⟩ := by
  unfold gueEntryScale
  rw [hv N x y b]
  rfl

theorem gueEntryScale_rowCoord {v : Coord d → ℝ≥0} (hv : GueEntryTagFree v) (N : ℕ)
    (i k : d.Idx N) (b : Bool) :
    gueEntryScale d v (rowCoord d N i k b) = gueEntryScale d v (rowCoord d N i k true) := by
  unfold rowCoord
  split_ifs
  · exact gueEntryScale_tag hv N i k b
  · exact gueEntryScale_tag hv N k i b

theorem gueEntryScale_nonneg (v : Coord d → ℝ≥0) (c : Coord d) : 0 ≤ gueEntryScale d v c :=
  Real.sqrt_nonneg _

theorem gueEntryScale_sq (v : Coord d → ℝ≥0) (c : Coord d) :
    gueEntryScale d v c ^ 2 * (gvar gueEntryDG (gueEntryRho d c) : ℝ) = v c := by
  have hg := gueEntryDG_gvar_pos (gueEntryRho d c)
  unfold gueEntryScale
  rw [Real.sq_sqrt (div_nonneg (v c).coe_nonneg hg.le)]
  field_simp

/-- The row coordinate of the auxiliary model. -/
def gueEntryCo (N : ℕ) (i k : d.Idx N) (b : Bool) : Coord gueEntryDG :=
  gueEntryRho d (rowCoord d N i k b)

/-- The row scale `λ_k`. -/
def gueEntryLam (v : Coord d → ℝ≥0) (N : ℕ) (i k : d.Idx N) : ℝ :=
  gueEntryScale d v (rowCoord d N i k true)

/-- **The off-diagonal entry**: `H_{ik} = λ_k (ω_{co k tt} + ε_k i ω_{co k ff})`. -/
theorem gueEntryHG_apply {v : Coord d → ℝ≥0} (hv : GueEntryTagFree v) (N : ℕ) {i k : d.Idx N}
    (hik : i ≠ k) (ω : Ω gueEntryDG) :
    gueEntryHG d N v ω i k = (gueEntryLam v N i k : ℂ) *
      ((ω (gueEntryCo N i k true) : ℂ)
        + ((rowSign d N i k : ℝ) : ℂ) * Complex.I * (ω (gueEntryCo N i k false) : ℂ)) := by
  unfold gueEntryHG
  rw [Hflow_apply, Real.sqrt_one, Complex.ofReal_one, one_mul, Xentry_eq_rowCoord hik]
  simp only [gueEntryT, gueEntryCo, gueEntryLam]
  rw [gueEntryScale_rowCoord hv N i k false]
  push_cast
  ring

/-- **The diagonal entry** is one real coordinate. -/
theorem gueEntryHG_diag (v : Coord d → ℝ≥0) (N : ℕ) (i : d.Idx N) (ω : Ω gueEntryDG) :
    gueEntryHG d N v ω i i = ((gueEntryScale d v ⟨N, i, i, true⟩ *
      ω (gueEntryRho d ⟨N, i, i, true⟩) : ℝ) : ℂ) := by
  unfold gueEntryHG
  rw [Hflow_apply, Real.sqrt_one, Complex.ofReal_one, one_mul]
  unfold Xentry
  simp only [lt_irrefl, ↓reduceIte]
  rfl

theorem gueEntryCo_injective (N : ℕ) (i : d.Idx N) :
    Function.Injective fun p : {a : d.Idx N // a ≠ i} × Bool => gueEntryCo N i p.1.1 p.2 := by
  rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨l, hl⟩, c⟩ h
  have h' := gueEntryRho_injective d h
  obtain ⟨h1, h2⟩ := rowCoord_injOn hk hl h'
  subst h1; subst h2; rfl

theorem gueEntryCo_gvar_tag (N : ℕ) (i k : d.Idx N) :
    (gvar gueEntryDG (gueEntryCo N i k false) : ℝ)
      = (gvar gueEntryDG (gueEntryCo N i k true) : ℝ) := by
  unfold gueEntryCo rowCoord
  split_ifs <;> rfl

/-- The off-row block of the auxiliary model. -/
def gueEntryFree (N : ℕ) (i : d.Idx N) : Finset (Coord gueEntryDG) :=
  (offRowCoord d N i).image (gueEntryRho d)

theorem gueEntryCo_not_mem_free (N : ℕ) (i k : d.Idx N) (b : Bool) :
    gueEntryCo N i k b ∉ gueEntryFree N i := by
  intro hmem
  obtain ⟨c, hc, hce⟩ := Finset.mem_image.1 hmem
  have := gueEntryRho_injective d hce
  subst this
  exact (Finset.mem_sdiff.1 hc).2 (rowCoord_mem_rowSet i k b)

theorem gueEntryHG_submatrix_congr (N : ℕ) (v : Coord d → ℝ≥0) {i : d.Idx N}
    {ω ω' : Ω gueEntryDG} (h : ∀ c ∈ gueEntryFree N i, ω c = ω' c) :
    (gueEntryHG d N v ω).submatrix (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
      = (gueEntryHG d N v ω').submatrix (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N) := by
  unfold gueEntryHG
  refine Hflow_submatrix_congr_offRowCoord 1 fun c hc => ?_
  simp only [gueEntryT]
  rw [h _ (Finset.mem_image_of_mem _ hc)]

/-- The minor resolvent of the auxiliary matrix. -/
def gueEntryMinorRes (N : ℕ) (v : Coord d → ℝ≥0) (z : ℂ) (i : d.Idx N) (ω : Ω gueEntryDG) :
    Matrix {a : d.Idx N // a ≠ i} {a : d.Idx N // a ≠ i} ℂ :=
  green ((gueEntryHG d N v ω).submatrix Subtype.val Subtype.val) z

theorem gueEntryMinorRes_norm_le (N : ℕ) (v : Coord d → ℝ≥0) {z : ℂ} (hz : z.im ≠ 0)
    (i : d.Idx N) (ω : Ω gueEntryDG) (k l : {a : d.Idx N // a ≠ i}) :
    ‖gueEntryMinorRes N v z i ω k l‖ ≤ |z.im|⁻¹ :=
  le_trans (norm_apply_le_l2_opNorm _ k l)
    (norm_green_le ((gueEntryHG_isHermitian N v ω).submatrix _) (abs_pos.2 hz) le_rfl)

theorem gueEntryMinorRes_continuous (N : ℕ) (v : Coord d → ℝ≥0) {z : ℂ} (hz : z.im ≠ 0)
    (i : d.Idx N) (k l : {a : d.Idx N // a ≠ i}) :
    Continuous fun ω => gueEntryMinorRes N v z i ω k l := by
  refine Continuous.matrix_elem ?_ k l
  exact continuous_green_of_isHermitian ((gueEntryHG_continuous N v).matrix_submatrix _ _)
    (fun ω => (gueEntryHG_isHermitian N v ω).submatrix _) hz

theorem gueEntryMinorRes_congr (N : ℕ) (v : Coord d → ℝ≥0) (z : ℂ) {i : d.Idx N}
    {ω ω' : Ω gueEntryDG} (h : ∀ c ∈ gueEntryFree N i, ω c = ω' c) :
    gueEntryMinorRes N v z i ω = gueEntryMinorRes N v z i ω' := by
  unfold gueEntryMinorRes
  rw [gueEntryHG_submatrix_congr N v h]

theorem gueEntryMinorRes_eq (N : ℕ) (v : Coord d → ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) (i : d.Idx N)
    (ω : Ω gueEntryDG) (k l : {a : d.Idx N // a ≠ i}) :
    gueEntryMinorRes N v z i ω k l = greenMinor (green (gueEntryHG d N v ω) z) i k.1 l.1 := by
  unfold gueEntryMinorRes green
  rw [inv_minor_resolvent (isUnit_det_sub_smul_one (gueEntryHG_isHermitian N v ω) hz) i
    (green_diag_ne_zero (gueEntryHG_isHermitian N v ω) hz i)]
  rfl

theorem gueEntryLam_nonneg (v : Coord d → ℝ≥0) (N : ℕ) (i k : d.Idx N) :
    0 ≤ gueEntryLam v N i k := gueEntryScale_nonneg v _

/-- **The quadratic row chaos** at row `i`: `B_{kl} = λ_k λ_l G^{(i)}_{kl}`. -/
def gueEntryQuadChaos (N : ℕ) (v : Coord d → ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) (i : d.Idx N) :
    RowChaos gueEntryDG {a : d.Idx N // a ≠ i} where
  co k b := gueEntryCo N i k.1 b
  co_inj := gueEntryCo_injective N i
  gvar_tag k := gueEntryCo_gvar_tag N i k.1
  eps k := rowSign d N i k.1
  eps_sq k := by unfold rowSign; split_ifs <;> norm_num
  r := 1
  B ω k l := ((gueEntryLam v N i k.1 * gueEntryLam v N i l.1 : ℝ) : ℂ) *
    gueEntryMinorRes N v z i ω k l
  B_cont k l := continuous_const.mul (gueEntryMinorRes_continuous N v hz i k l)
  Bbd := (∑ k : {a : d.Idx N // a ≠ i}, gueEntryLam v N i k.1) ^ 2 * |z.im|⁻¹
  B_bdd ω k l := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (gueEntryLam_nonneg v N i k.1) (gueEntryLam_nonneg v N i l.1))]
    have hk : gueEntryLam v N i k.1 ≤ ∑ k : {a : d.Idx N // a ≠ i}, gueEntryLam v N i k.1 :=
      Finset.single_le_sum (f := fun k : {a : d.Idx N // a ≠ i} => gueEntryLam v N i k.1)
        (fun k _ => gueEntryLam_nonneg v N i k.1) (Finset.mem_univ k)
    have hl : gueEntryLam v N i l.1 ≤ ∑ k : {a : d.Idx N // a ≠ i}, gueEntryLam v N i k.1 :=
      Finset.single_le_sum (f := fun k : {a : d.Idx N // a ≠ i} => gueEntryLam v N i k.1)
        (fun k _ => gueEntryLam_nonneg v N i k.1) (Finset.mem_univ l)
    have h1 := gueEntryMinorRes_norm_le N v hz i ω k l
    have h0 := gueEntryLam_nonneg v N i k.1
    have h0' := gueEntryLam_nonneg v N i l.1
    have hprod : gueEntryLam v N i k.1 * gueEntryLam v N i l.1
        ≤ (∑ k : {a : d.Idx N // a ≠ i}, gueEntryLam v N i k.1) ^ 2 := by
      rw [sq]; exact mul_le_mul hk hl h0' (h0.trans hk)
    exact mul_le_mul hprod h1 (norm_nonneg _) (sq_nonneg _)
  Ifree := gueEntryFree N i
  Ifree_free k b := gueEntryCo_not_mem_free N i k.1 b
  B_free ω ω' h := by
    funext k l
    rw [gueEntryMinorRes_congr N v z h]

/-- **The rank-one row chaos** at row `i` with coefficient vector `c`:
`B_{kl} = (λ_k c_k) conj(λ_l c_l)`; its chaos is `|∑_k H_{ik} c_k|² - ∑_k σ_k λ_k² |c_k|²`. -/
def gueEntryLinChaos (N : ℕ) (v : Coord d → ℝ≥0) (i : d.Idx N)
    (c : Ω gueEntryDG → {a : d.Idx N // a ≠ i} → ℂ) (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ gueEntryFree N i, ω x = ω' x) → c ω = c ω') :
    RowChaos gueEntryDG {a : d.Idx N // a ≠ i} where
  co k b := gueEntryCo N i k.1 b
  co_inj := gueEntryCo_injective N i
  gvar_tag k := gueEntryCo_gvar_tag N i k.1
  eps k := rowSign d N i k.1
  eps_sq k := by unfold rowSign; split_ifs <;> norm_num
  r := 1
  B ω k l := ((gueEntryLam v N i k.1 : ℝ) : ℂ) * c ω k *
    (starRingEnd ℂ) (((gueEntryLam v N i l.1 : ℝ) : ℂ) * c ω l)
  B_cont k l := (continuous_const.mul (hc k)).mul
    (Complex.continuous_conj.comp (continuous_const.mul (hc l)))
  Bbd := ((∑ k : {a : d.Idx N // a ≠ i}, gueEntryLam v N i k.1) * Cb) ^ 2
  B_bdd ω k l := by
    have hsum : ∀ k : {a : d.Idx N // a ≠ i},
        gueEntryLam v N i k.1 ≤ ∑ k : {a : d.Idx N // a ≠ i}, gueEntryLam v N i k.1 :=
      fun k => Finset.single_le_sum
        (f := fun k : {a : d.Idx N // a ≠ i} => gueEntryLam v N i k.1)
        (fun k _ => gueEntryLam_nonneg v N i k.1) (Finset.mem_univ k)
    have hb : ∀ k : {a : d.Idx N // a ≠ i}, ‖((gueEntryLam v N i k.1 : ℝ) : ℂ) * c ω k‖
        ≤ (∑ k : {a : d.Idx N // a ≠ i}, gueEntryLam v N i k.1) * Cb := by
      intro k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (gueEntryLam_nonneg v N i k.1)]
      have hC0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb ω k)
      exact mul_le_mul (hsum k) (hCb ω k) (norm_nonneg _)
        ((gueEntryLam_nonneg v N i k.1).trans (hsum k))
    rw [norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul (hb k) (hb l) (norm_nonneg _) ((norm_nonneg _).trans (hb k))
  Ifree := gueEntryFree N i
  Ifree_free k b := gueEntryCo_not_mem_free N i k.1 b
  B_free ω ω' h := by
    funext k l
    rw [hcf ω ω' h]

end AuxModel

/-! ### The chaoses are the two sides of the large deviation estimates -/

section Ident

variable {d} {N : ℕ} {v : Coord d → ℝ≥0}

theorem gueEntry_sum_erase {M : Type*} [AddCommMonoid M] (i : d.Idx N) (f : d.Idx N → M) :
    ∑ k ∈ Finset.univ.erase i, f k = ∑ k : {a : d.Idx N // a ≠ i}, f k.1 :=
  Finset.sum_subtype _ (fun x => by simp) f

/-- The profile hypothesis: `2 v_{⟨N,x,y,tt⟩} = S_{xy}` off the diagonal, `S` symmetric. -/
structure GueEntryProfOK (v : Coord d → ℝ≥0) (N : ℕ) (S : d.Idx N → d.Idx N → ℝ) : Prop where
  symm : ∀ x y, S x y = S y x
  off : ∀ x y, x ≠ y → 2 * (v ⟨N, x, y, true⟩ : ℝ) = S x y
  diag : ∀ x, (v ⟨N, x, x, true⟩ : ℝ) = S x x

theorem gueEntry_sg_lam {S : d.Idx N → d.Idx N → ℝ} (hS : GueEntryProfOK v N S) (i : d.Idx N)
    (k : {a : d.Idx N // a ≠ i}) :
    2 * (1 : ℝ) ^ 2 * (gvar gueEntryDG (gueEntryCo N i k.1 true) : ℝ) * gueEntryLam v N i k.1 ^ 2
      = S i k.1 := by
  unfold gueEntryCo gueEntryLam
  have h := gueEntryScale_sq v (rowCoord d N i k.1 true)
  have e : 2 * (1 : ℝ) ^ 2 * (gvar gueEntryDG (gueEntryRho d (rowCoord d N i k.1 true)) : ℝ)
      * gueEntryScale d v (rowCoord d N i k.1 true) ^ 2
      = 2 * (v (rowCoord d N i k.1 true) : ℝ) := by rw [← h]; ring
  rw [e]
  unfold rowCoord
  split_ifs
  · exact hS.off i k.1 (Ne.symm k.2)
  · rw [hS.off k.1 i k.2, hS.symm]

theorem gueEntry_h_lam (hv : GueEntryTagFree v) {z : ℂ} (hz : z.im ≠ 0) (i : d.Idx N)
    (ω : Ω gueEntryDG) (k : {a : d.Idx N // a ≠ i}) :
    (gueEntryLam v N i k.1 : ℂ) * (gueEntryQuadChaos N v hz i).h ω k
      = gueEntryHG d N v ω i k.1 := by
  rw [gueEntryHG_apply hv N (Ne.symm k.2) ω]
  change _ * (((1 : ℝ) : ℂ) * ((ω (gueEntryCo N i k.1 true) : ℂ) +
    (((rowSign d N i k.1 : ℝ) : ℂ) * Complex.I) * (ω (gueEntryCo N i k.1 false) : ℂ))) = _
  push_cast
  ring

theorem gueEntry_hc_lam (hv : GueEntryTagFree v) {z : ℂ} (hz : z.im ≠ 0) (i : d.Idx N)
    (ω : Ω gueEntryDG) (k : {a : d.Idx N // a ≠ i}) :
    (gueEntryLam v N i k.1 : ℂ) * (starRingEnd ℂ) ((gueEntryQuadChaos N v hz i).h ω k)
      = gueEntryHG d N v ω k.1 i := by
  have h := gueEntry_h_lam hv hz i ω k
  have hH := (gueEntryHG_isHermitian N v ω).apply k.1 i
  rw [← hH, ← h]
  change _ = star (_ * _)
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]

/-- **The quadratic chaos is the left side of (4.7)** with the profile `S` and `t = 1`. -/
theorem gueEntryQuad_chaos (hv : GueEntryTagFree v) {S : d.Idx N → d.Idx N → ℝ}
    (hS : GueEntryProfOK v N S) {z : ℂ} (hz : z.im ≠ 0) (i : d.Idx N) (ω : Ω gueEntryDG) :
    ‖(gueEntryQuadChaos N v hz i).chaos ω‖ ^ 2
      = ldeQuadLHS (gueEntryHG d N v ω) (green (gueEntryHG d N v ω) z) S 1 i := by
  unfold ldeQuadLHS
  congr 2
  unfold RowChaos.chaos RowChaos.cen
  congr 1
  · rw [gueEntry_sum_erase i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [gueEntry_sum_erase i]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← gueEntryMinorRes_eq N v hz i ω k l, ← gueEntry_h_lam hv hz i ω k,
      ← gueEntry_hc_lam hv hz i ω l]
    change (gueEntryQuadChaos N v hz i).h ω k *
      (((gueEntryLam v N i k.1 * gueEntryLam v N i l.1 : ℝ) : ℂ) *
      gueEntryMinorRes N v z i ω k l) * (starRingEnd ℂ) ((gueEntryQuadChaos N v hz i).h ω l) = _
    push_cast
    ring
  · rw [gueEntry_sum_erase i, Complex.ofReal_one, one_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← gueEntryMinorRes_eq N v hz i ω k k, ← gueEntry_sg_lam hS i k]
    change ((2 * (1 : ℝ) ^ 2 * (gvar gueEntryDG (gueEntryCo N i k.1 true) : ℝ) : ℝ) : ℂ) *
      (((gueEntryLam v N i k.1 * gueEntryLam v N i k.1 : ℝ) : ℂ) *
        gueEntryMinorRes N v z i ω k k) = _
    push_cast
    ring

/-- **The control of the quadratic chaos is the right side of (4.7).** -/
theorem gueEntryQuad_Vq {S : d.Idx N → d.Idx N → ℝ} (hS : GueEntryProfOK v N S) {z : ℂ}
    (hz : z.im ≠ 0) (i : d.Idx N) (ω : Ω gueEntryDG) :
    (gueEntryQuadChaos N v hz i).Vq ω
      = ldeQuadRHS S (green (gueEntryHG d N v ω) z) i := by
  unfold ldeQuadRHS
  change ∑ k, ∑ l, (gueEntryQuadChaos N v hz i).sg k * ‖(gueEntryQuadChaos N v hz i).B ω k l‖ ^ 2
    * (gueEntryQuadChaos N v hz i).sg l = _
  rw [gueEntry_sum_erase i]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gueEntry_sum_erase i]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← gueEntryMinorRes_eq N v hz i ω k l, hS.symm l.1 i, ← gueEntry_sg_lam hS i k,
    ← gueEntry_sg_lam hS i l]
  change 2 * (1 : ℝ) ^ 2 * (gvar gueEntryDG (gueEntryCo N i k.1 true) : ℝ) *
      ‖((gueEntryLam v N i k.1 * gueEntryLam v N i l.1 : ℝ) : ℂ)
        * gueEntryMinorRes N v z i ω k l‖ ^ 2
      * (2 * (1 : ℝ) ^ 2 * (gvar gueEntryDG (gueEntryCo N i l.1 true) : ℝ)) = _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (gueEntryLam_nonneg v N i k.1) (gueEntryLam_nonneg v N i l.1))]
  ring

/-- **The rank-one chaos is `|∑ H_{ik} c_k|² - ∑ S_{ik}|c_k|²`.** -/
theorem gueEntryLin_chaos (hv : GueEntryTagFree v) {S : d.Idx N → d.Idx N → ℝ}
    (hS : GueEntryProfOK v N S) {z : ℂ} (hz : z.im ≠ 0) (i : d.Idx N)
    (c : Ω gueEntryDG → {a : d.Idx N // a ≠ i} → ℂ) (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ gueEntryFree N i, ω x = ω' x) → c ω = c ω') (ω : Ω gueEntryDG) :
    (gueEntryLinChaos N v i c hc Cb hCb hcf).chaos ω
      = ((‖∑ k : {a : d.Idx N // a ≠ i}, gueEntryHG d N v ω i k.1 * c ω k‖ ^ 2
          - ∑ k : {a : d.Idx N // a ≠ i}, S i k.1 * ‖c ω k‖ ^ 2 : ℝ) : ℂ) := by
  set C := gueEntryLinChaos N v i c hc Cb hCb hcf
  have hh : ∀ k, C.h ω k = (gueEntryQuadChaos N v hz i).h ω k := fun k => rfl
  have hY : ∀ k : {a : d.Idx N // a ≠ i},
      C.h ω k * ((gueEntryLam v N i k.1 : ℂ) * c ω k) = gueEntryHG d N v ω i k.1 * c ω k := by
    intro k
    rw [hh, ← gueEntry_h_lam hv hz i ω k]; ring
  unfold RowChaos.chaos RowChaos.cen
  have e1 : ∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l)
      = (∑ k, gueEntryHG d N v ω i k.1 * c ω k) *
        (starRingEnd ℂ) (∑ k, gueEntryHG d N v ω i k.1 * c ω k) := by
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← hY k, ← hY l]
    change C.h ω k * (((gueEntryLam v N i k.1 : ℝ) : ℂ) * c ω k *
      (starRingEnd ℂ) (((gueEntryLam v N i l.1 : ℝ) : ℂ) * c ω l)) * (starRingEnd ℂ) (C.h ω l)
      = _
    rw [map_mul (starRingEnd ℂ) (C.h ω l)]
    ring
  have e2 : ∑ k, ((C.sg k : ℝ) : ℂ) * C.B ω k k
      = ((∑ k : {a : d.Idx N // a ≠ i}, S i k.1 * ‖c ω k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← gueEntry_sg_lam hS i k]
    change ((2 * (1 : ℝ) ^ 2 * (gvar gueEntryDG (gueEntryCo N i k.1 true) : ℝ) : ℝ) : ℂ) *
      (((gueEntryLam v N i k.1 : ℝ) : ℂ) * c ω k *
        (starRingEnd ℂ) (((gueEntryLam v N i k.1 : ℝ) : ℂ) * c ω k)) = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (gueEntryLam_nonneg v N i k.1)]
    push_cast
    ring
  rw [e1, e2, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **The control of the rank-one chaos is `(∑ S_{ik}|c_k|²)²`.** -/
theorem gueEntryLin_Vq {S : d.Idx N → d.Idx N → ℝ} (hS : GueEntryProfOK v N S) (i : d.Idx N)
    (c : Ω gueEntryDG → {a : d.Idx N // a ≠ i} → ℂ) (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ gueEntryFree N i, ω x = ω' x) → c ω = c ω') (ω : Ω gueEntryDG) :
    (gueEntryLinChaos N v i c hc Cb hCb hcf).Vq ω
      = (∑ k : {a : d.Idx N // a ≠ i}, S i k.1 * ‖c ω k‖ ^ 2) ^ 2 := by
  set C := gueEntryLinChaos N v i c hc Cb hCb hcf
  have hpt : ∀ k l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l
      = (S i k.1 * ‖c ω k‖ ^ 2) * (S i l.1 * ‖c ω l‖ ^ 2) := by
    intro k l
    rw [← gueEntry_sg_lam hS i k, ← gueEntry_sg_lam hS i l]
    change 2 * (1 : ℝ) ^ 2 * (gvar gueEntryDG (gueEntryCo N i k.1 true) : ℝ) *
      ‖((gueEntryLam v N i k.1 : ℝ) : ℂ) * c ω k *
        (starRingEnd ℂ) (((gueEntryLam v N i l.1 : ℝ) : ℂ) * c ω l)‖ ^ 2 *
      (2 * (1 : ℝ) ^ 2 * (gvar gueEntryDG (gueEntryCo N i l.1 true) : ℝ)) = _
    rw [norm_mul, Complex.norm_conj, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (gueEntryLam_nonneg v N i k.1),
      abs_of_nonneg (gueEntryLam_nonneg v N i l.1)]
    ring
  change ∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l = _
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hpt k l

end Ident

/-! ### Tail bounds on the auxiliary carrier -/

section AuxTail

variable {d} {N : ℕ} {v : Coord d → ℝ≥0}

/-- A rank-one chaos `Q = Y - R`, `V_q = R²`: `P(Λ R < Y) ≤ A_q / ((Λ-1)²)^{q+1}`. -/
theorem gueEntry_lin_tail_aux {D : Dims} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : RowChaos D κ) (Y R : Ω D → ℝ) (hR0 : ∀ ω, 0 ≤ R ω)
    (hchaos : ∀ ω, C.chaos ω = ((Y ω - R ω : ℝ) : ℂ)) (hV : ∀ ω, C.Vq ω = R ω ^ 2)
    {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    (P D) {ω | Λ * R ω < Y ω} ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) := by
  have hlam : 0 < (Λ - 1) ^ 2 := by have : 0 < Λ - 1 := by linarith
                                    positivity
  refine (measure_mono ?_).trans (gueEntry_chaos_tail C hlam q)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hV, hchaos, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h0 := hR0 ω
  have h1 : (Λ - 1) * R ω < Y ω - R ω := by linarith
  have h2 : 0 ≤ (Λ - 1) * R ω := mul_nonneg (by linarith) h0
  have h3 := pow_lt_pow_left₀ h1 h2 (by norm_num : (2 : ℕ) ≠ 0)
  nlinarith [h3]

theorem gueEntry_meas_entry {n : Type*} (k l : n) :
    Measurable fun H : Matrix n n ℂ => H k l :=
  (measurable_pi_apply l).comp (measurable_pi_apply k)

theorem gueEntry_meas_green {n : Type*} [Fintype n] [DecidableEq n] (z : ℂ) (k l : n) :
    Measurable fun H : Matrix n n ℂ => green H z k l := by
  unfold green
  refine measurable_inv_entries (fun a b => ?_) k l
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  exact (gueEntry_meas_entry a b).sub measurable_const

theorem gueEntry_meas_greenMinor {n : Type*} [Fintype n] [DecidableEq n] (z : ℂ) (i k l : n) :
    Measurable fun H : Matrix n n ℂ => greenMinor (green H z) i k l := by
  unfold greenMinor
  exact (gueEntry_meas_green z k l).sub
    (((gueEntry_meas_green z k i).mul (gueEntry_meas_green z i l)).div (gueEntry_meas_green z i i))

/-- **Quadratic LDE on the auxiliary carrier.** -/
theorem gueEntry_quad_tail (hv : GueEntryTagFree v) {S : d.Idx N → d.Idx N → ℝ}
    (hS : GueEntryProfOK v N S) {z : ℂ} (hz : z.im ≠ 0) (i : d.Idx N) {lam : ℝ} (hlam : 0 < lam)
    (q : ℕ) :
    (P gueEntryDG) {ω | lam * ldeQuadRHS S (green (gueEntryHG d N v ω) z) i
        < ldeQuadLHS (gueEntryHG d N v ω) (green (gueEntryHG d N v ω) z) S 1 i}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  have h := gueEntry_chaos_tail (gueEntryQuadChaos N v hz i) hlam q
  have hset : {ω | lam * ldeQuadRHS S (green (gueEntryHG d N v ω) z) i
        < ldeQuadLHS (gueEntryHG d N v ω) (green (gueEntryHG d N v ω) z) S 1 i}
      = {ω | lam * (gueEntryQuadChaos N v hz i).Vq ω
        < ‖(gueEntryQuadChaos N v hz i).chaos ω‖ ^ 2} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [gueEntryQuad_chaos hv hS hz i ω, gueEntryQuad_Vq hS hz i ω]
  rw [hset]; exact h

/-- **Row LDE on the auxiliary carrier.** -/
theorem gueEntry_row_tail (hv : GueEntryTagFree v) {S : d.Idx N → d.Idx N → ℝ}
    (hS : GueEntryProfOK v N S) {z : ℂ} (hz : z.im ≠ 0) {i j : d.Idx N} (hij : i ≠ j)
    {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    (P gueEntryDG) {ω | Λ * ldeRowRHS S (green (gueEntryHG d N v ω) z) i j
        < ldeRowLHS (gueEntryHG d N v ω) (green (gueEntryHG d N v ω) z) i j}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) := by
  set j' : {a : d.Idx N // a ≠ i} := ⟨j, Ne.symm hij⟩
  set c : Ω gueEntryDG → {a : d.Idx N // a ≠ i} → ℂ := fun ω k => gueEntryMinorRes N v z i ω k j'
  have hc : ∀ k, Continuous fun ω => c ω k := fun k => gueEntryMinorRes_continuous N v hz i k j'
  have hCb : ∀ ω k, ‖c ω k‖ ≤ |z.im|⁻¹ := fun ω k => gueEntryMinorRes_norm_le N v hz i ω k j'
  have hcf : ∀ ω ω', (∀ x ∈ gueEntryFree N i, ω x = ω' x) → c ω = c ω' := by
    intro ω ω' h; funext k; simp only [c]; rw [gueEntryMinorRes_congr N v z h]
  have hY : ∀ ω, ldeRowLHS (gueEntryHG d N v ω) (green (gueEntryHG d N v ω) z) i j
      = ‖∑ k : {a : d.Idx N // a ≠ i}, gueEntryHG d N v ω i k.1 * c ω k‖ ^ 2 := by
    intro ω
    unfold ldeRowLHS
    rw [gueEntry_sum_erase i]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c, gueEntryMinorRes_eq N v hz i ω k j']
    rfl
  have hR : ∀ ω, ldeRowRHS S (green (gueEntryHG d N v ω) z) i j
      = ∑ k : {a : d.Idx N // a ≠ i}, S i k.1 * ‖c ω k‖ ^ 2 := by
    intro ω
    unfold ldeRowRHS
    rw [gueEntry_sum_erase i]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c, gueEntryMinorRes_eq N v hz i ω k j']
    rfl
  have hS0 : ∀ ω, 0 ≤ ∑ k : {a : d.Idx N // a ≠ i}, S i k.1 * ‖c ω k‖ ^ 2 := by
    intro ω
    refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (sq_nonneg _)
    rw [← gueEntry_sg_lam hS i k]; positivity
  have h := gueEntry_lin_tail_aux (gueEntryLinChaos N v i c hc _ hCb hcf)
    (fun ω => ‖∑ k : {a : d.Idx N // a ≠ i}, gueEntryHG d N v ω i k.1 * c ω k‖ ^ 2)
    (fun ω => ∑ k : {a : d.Idx N // a ≠ i}, S i k.1 * ‖c ω k‖ ^ 2) hS0
    (fun ω => gueEntryLin_chaos hv hS hz i c hc _ hCb hcf ω)
    (fun ω => gueEntryLin_Vq hS i c hc _ hCb hcf ω) hΛ q
  have hset : {ω | Λ * ldeRowRHS S (green (gueEntryHG d N v ω) z) i j
        < ldeRowLHS (gueEntryHG d N v ω) (green (gueEntryHG d N v ω) z) i j}
      = {ω | Λ * (∑ k : {a : d.Idx N // a ≠ i}, S i k.1 * ‖c ω k‖ ^ 2)
        < ‖∑ k : {a : d.Idx N // a ≠ i}, gueEntryHG d N v ω i k.1 * c ω k‖ ^ 2} := by
    ext ω; simp only [Set.mem_ofPred_eq]; rw [hY ω, hR ω]
  rw [hset]; exact h

/-- **Column LDE on the auxiliary carrier** (row `j`, conjugated minor row `k`). -/
theorem gueEntry_col_tail (hv : GueEntryTagFree v) {S : d.Idx N → d.Idx N → ℝ}
    (hS : GueEntryProfOK v N S) {z : ℂ} (hz : z.im ≠ 0) {k j : d.Idx N} (hkj : k ≠ j)
    {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    (P gueEntryDG) {ω | Λ * ldeColRHS S (green (gueEntryHG d N v ω) z) k j
        < ldeColLHS (gueEntryHG d N v ω) (green (gueEntryHG d N v ω) z) k j}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) := by
  set k' : {a : d.Idx N // a ≠ j} := ⟨k, hkj⟩
  set c : Ω gueEntryDG → {a : d.Idx N // a ≠ j} → ℂ :=
    fun ω l => (starRingEnd ℂ) (gueEntryMinorRes N v z j ω k' l)
  have hc : ∀ l, Continuous fun ω => c ω l := fun l =>
    Complex.continuous_conj.comp (gueEntryMinorRes_continuous N v hz j k' l)
  have hCb : ∀ ω l, ‖c ω l‖ ≤ |z.im|⁻¹ := fun ω l => by
    simp only [c, Complex.norm_conj]; exact gueEntryMinorRes_norm_le N v hz j ω k' l
  have hcf : ∀ ω ω', (∀ x ∈ gueEntryFree N j, ω x = ω' x) → c ω = c ω' := by
    intro ω ω' h; funext l; simp only [c]; rw [gueEntryMinorRes_congr N v z h]
  have hY : ∀ ω, ldeColLHS (gueEntryHG d N v ω) (green (gueEntryHG d N v ω) z) k j
      = ‖∑ l : {a : d.Idx N // a ≠ j}, gueEntryHG d N v ω j l.1 * c ω l‖ ^ 2 := by
    intro ω
    unfold ldeColLHS
    rw [gueEntry_sum_erase j]
    have e : ∑ l : {a : d.Idx N // a ≠ j}, greenMinor (green (gueEntryHG d N v ω) z) j k l.1
          * gueEntryHG d N v ω l.1 j
        = (starRingEnd ℂ) (∑ l : {a : d.Idx N // a ≠ j}, gueEntryHG d N v ω j l.1 * c ω l) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [c, map_mul, Complex.conj_conj]
      rw [gueEntryMinorRes_eq N v hz j ω k' l]
      have hH := (gueEntryHG_isHermitian N v ω).apply l.1 j
      rw [← hH]
      change _ = star (gueEntryHG d N v ω j l.1) * _
      ring
    rw [e, Complex.norm_conj]
  have hR : ∀ ω, ldeColRHS S (green (gueEntryHG d N v ω) z) k j
      = ∑ l : {a : d.Idx N // a ≠ j}, S j l.1 * ‖c ω l‖ ^ 2 := by
    intro ω
    unfold ldeColRHS
    rw [gueEntry_sum_erase j]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [c, Complex.norm_conj, gueEntryMinorRes_eq N v hz j ω k' l]
    rw [hS.symm]; ring
  have hS0 : ∀ ω, 0 ≤ ∑ l : {a : d.Idx N // a ≠ j}, S j l.1 * ‖c ω l‖ ^ 2 := by
    intro ω
    refine Finset.sum_nonneg fun l _ => mul_nonneg ?_ (sq_nonneg _)
    rw [← gueEntry_sg_lam hS j l]; positivity
  have h := gueEntry_lin_tail_aux (gueEntryLinChaos N v j c hc _ hCb hcf)
    (fun ω => ‖∑ l : {a : d.Idx N // a ≠ j}, gueEntryHG d N v ω j l.1 * c ω l‖ ^ 2)
    (fun ω => ∑ l : {a : d.Idx N // a ≠ j}, S j l.1 * ‖c ω l‖ ^ 2) hS0
    (fun ω => gueEntryLin_chaos hv hS hz j c hc _ hCb hcf ω)
    (fun ω => gueEntryLin_Vq hS j c hc _ hCb hcf ω) hΛ q
  have hset : {ω | Λ * ldeColRHS S (green (gueEntryHG d N v ω) z) k j
        < ldeColLHS (gueEntryHG d N v ω) (green (gueEntryHG d N v ω) z) k j}
      = {ω | Λ * (∑ l : {a : d.Idx N // a ≠ j}, S j l.1 * ‖c ω l‖ ^ 2)
        < ‖∑ l : {a : d.Idx N // a ≠ j}, gueEntryHG d N v ω j l.1 * c ω l‖ ^ 2} := by
    ext ω; simp only [Set.mem_ofPred_eq]; rw [hY ω, hR ω]
  rw [hset]; exact h

/-- **The diagonal entry on the auxiliary carrier**: `P(Λ S_{ii} < |H_{ii}|²) ≤ (2q-1)!!/Λ^q`. -/
theorem gueEntry_diag_tail {S : d.Idx N → d.Idx N → ℝ} (hS : GueEntryProfOK v N S)
    (i : d.Idx N) {Λ : ℝ} (hΛ : 0 < Λ) (q : ℕ) :
    (P gueEntryDG) {ω | Λ * S i i < ‖gueEntryHG d N v ω i i‖ ^ 2}
      ≤ ENNReal.ofReal (dfac q / Λ ^ q) := by
  set c0 : Coord d := ⟨N, i, i, true⟩
  set sc := gueEntryScale d v c0
  set g : ℝ := (gvar gueEntryDG (gueEntryRho d c0) : ℝ)
  have hg : 0 < g := gueEntryDG_gvar_pos _
  have hSii : S i i = sc ^ 2 * g := by rw [← hS.diag i, ← gueEntryScale_sq v c0]
  have hHii : ∀ ω, ‖gueEntryHG d N v ω i i‖ ^ 2 = sc ^ 2 * (ω (gueEntryRho d c0)) ^ 2 := by
    intro ω
    rw [gueEntryHG_diag, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  by_cases hsc : sc = 0
  · have : {ω | Λ * S i i < ‖gueEntryHG d N v ω i i‖ ^ 2} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hHii, hSii, hsc]; simp
    rw [this, measure_empty]; exact zero_le
  have hsc0 : 0 < sc ^ 2 := by positivity
  set Y : Ω gueEntryDG → ℝ := fun ω => |ω (gueEntryRho d c0)|
  have ht : 0 < Real.sqrt (Λ * g) := Real.sqrt_pos.2 (by positivity)
  have habs : ∀ ω, |Y ω| ^ (2 * q) = (ω (gueEntryRho d c0)) ^ (2 * q) := fun ω => by
    simp only [Y, abs_abs, pow_mul, sq_abs]
  have hint : Integrable (fun ω => |Y ω| ^ (2 * q)) (P gueEntryDG) := by
    simp only [habs]; exact integrable_pow_coord _ _ _
  have hmom : ∫ ω, |Y ω| ^ (2 * q) ∂(P gueEntryDG) ≤ dfac q * g ^ q := by
    simp only [habs]
    rw [integral_pow_coord, integral_pow_gaussianReal']
  have hmark := meas_gt_le_of_moment (P := P gueEntryDG) (Y := Y) ht hint hmom
  refine (measure_mono ?_).trans (hmark.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  · intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hHii, hSii] at hω
    have h1 : Λ * g < (ω (gueEntryRho d c0)) ^ 2 := by
      have : sc ^ 2 * (Λ * g) < sc ^ 2 * (ω (gueEntryRho d c0)) ^ 2 := by linarith
      exact lt_of_mul_lt_mul_left this hsc0.le
    have h2 : Real.sqrt (Λ * g) < Real.sqrt ((ω (gueEntryRho d c0)) ^ 2) :=
      Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq_eq_abs] at h2
  · rw [pow_mul, Real.sq_sqrt (by positivity), mul_pow]
    field_simp

end AuxTail

/-! ### Back on the grid: profiles, transfer, measurability -/

section GridTransfer

variable {d}

/-- The GUE-phase profile at grid step `k`: `S_u = t₁ S + k Δ / M`. -/
def gueEntryGridProf (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    d.Idx N → d.Idx N → ℝ :=
  gueEntryProf (d.L N) (d.W N) (t1 N) (k * (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)))

theorem gueEntry_step_nonneg {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (h : t1 N ≤ t0 N) :
    0 ≤ Grid.step t1 t0 K N :=
  div_nonneg (by linarith) (Nat.cast_nonneg _)

theorem gueEntry_M_pos (N : ℕ) : (0 : ℝ) < (ouMatrixSize d N : ℝ) := by
  exact_mod_cast ouMatrixSize_pos d N

theorem gueEntryGridProf_ok {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (ht1 : 0 ≤ t1 N)
    (h10 : t1 N ≤ t0 N) (k : ℕ) :
    GueEntryProfOK (gueEntryVar d t1 t0 K N k) N (gueEntryGridProf t1 t0 K N k) := by
  have hΔ : 0 ≤ Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ) :=
    div_nonneg (gueEntry_step_nonneg h10) (gueEntry_M_pos N).le
  have hv : ∀ c : Coord d, (gueEntryVar d t1 t0 K N k c : ℝ)
      = t1 N * (gvar d c : ℝ) + k * (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ))
        * (gueUnitVar d c : ℝ) := by
    intro c
    simp only [gueEntryVar, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, nsmul_eq_mul,
      NNReal.coe_natCast]
    rw [Real.sq_sqrt ht1, Real.sq_sqrt hΔ]
    ring
  refine ⟨fun x y => gueEntryProf_symm _ _ x y, fun x y hxy => ?_, fun x => ?_⟩
  · rw [hv, gvar_offDiag d N x y true hxy]
    have hu : (gueUnitVar d ⟨N, x, y, true⟩ : ℝ) = 1 / 2 := by
      simp only [gueUnitVar, hxy, ↓reduceIte]; push_cast; ring
    rw [hu]
    simp only [gueEntryGridProf, gueEntryProf]
    ring
  · rw [hv, gvar_diag]
    have hu : (gueUnitVar d ⟨N, x, x, true⟩ : ℝ) = 1 := by
      simp only [gueUnitVar, ↓reduceIte]; push_cast; ring
    rw [hu]
    simp only [gueEntryGridProf, gueEntryProf]
    ring

theorem gueEntry_time_eq {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} (N k : ℕ) :
    Grid.time t1 t0 K N k = t1 N + ((d.L N * d.W N : ℕ) : ℝ)
      * (k * (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ))) := by
  have hM := gueEntry_M_pos (d := d) N
  unfold Grid.time
  rw [show ((d.L N * d.W N : ℕ) : ℝ) = (ouMatrixSize d N : ℝ) from rfl]
  field_simp

theorem gueEntry_time_le {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N k : ℕ} (h10 : t1 N ≤ t0 N)
    (hK : K N ≠ 0) (hk : k ≤ K N) : Grid.time t1 t0 K N k ≤ t0 N := by
  unfold Grid.time Grid.step
  have hK' : (0 : ℝ) < K N := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hk' : (k : ℝ) ≤ K N := by exact_mod_cast hk
  have : (k : ℝ) * ((t0 N - t1 N) / K N) ≤ t0 N - t1 N := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ hK']
    nlinarith
  linarith

theorem gueEntry_time_ge {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N k : ℕ} (h10 : t1 N ≤ t0 N) :
    t1 N ≤ Grid.time t1 t0 K N k := by
  unfold Grid.time
  have := gueEntry_step_nonneg (K := K) h10
  have : 0 ≤ (k : ℝ) * Grid.step t1 t0 K N := mul_nonneg (Nat.cast_nonneg _) this
  linarith

/-- **Transfer of a one-time event from the grid to the auxiliary carrier.** -/
theorem gueEntry_transfer (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ)
    {A B : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ} (hA : Measurable A) (hB : Measurable B) (c : ℝ) :
    (Pgue d) {ω | c * B (gueH d t1 t0 K N k ω) < A (gueH d t1 t0 K N k ω)}
      = (P gueEntryDG) {ω | c * B (gueEntryHG d N (gueEntryVar d t1 t0 K N k) ω)
          < A (gueEntryHG d N (gueEntryVar d t1 t0 K N k) ω)} := by
  have hset : MeasurableSet {H : Matrix (d.Idx N) (d.Idx N) ℂ | c * B H < A H} :=
    measurableSet_lt (hB.const_mul c) hA
  have h1 := Measure.map_apply (μ := Pgue d) (gueH_measurable d t1 t0 K N k) hset
  have h2 := Measure.map_apply (μ := P gueEntryDG)
    (gueEntryHG_measurable (d := d) N (gueEntryVar d t1 t0 K N k)) hset
  rw [gueEntry_law_HG] at h1
  rw [h1] at h2
  exact h2

section Meas

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem gueEntry_meas_ldeRowLHS (z : ℂ) (i j : n) :
    Measurable fun H : Matrix n n ℂ => ldeRowLHS H (green H z) i j := by
  unfold ldeRowLHS
  exact (Finset.measurable_sum _ fun k _ =>
    (gueEntry_meas_entry i k).mul (gueEntry_meas_greenMinor z i k j)).norm.pow_const 2

theorem gueEntry_meas_ldeRowRHS (S : n → n → ℝ) (z : ℂ) (i j : n) :
    Measurable fun H : Matrix n n ℂ => ldeRowRHS S (green H z) i j := by
  unfold ldeRowRHS
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.mul ((gueEntry_meas_greenMinor z i k j).norm.pow_const 2)

theorem gueEntry_meas_ldeColLHS (z : ℂ) (k j : n) :
    Measurable fun H : Matrix n n ℂ => ldeColLHS H (green H z) k j := by
  unfold ldeColLHS
  exact (Finset.measurable_sum _ fun l _ =>
    (gueEntry_meas_greenMinor z j k l).mul (gueEntry_meas_entry l j)).norm.pow_const 2

theorem gueEntry_meas_ldeColRHS (S : n → n → ℝ) (z : ℂ) (k j : n) :
    Measurable fun H : Matrix n n ℂ => ldeColRHS S (green H z) k j := by
  unfold ldeColRHS
  exact Finset.measurable_sum _ fun l _ =>
    ((gueEntry_meas_greenMinor z j k l).norm.pow_const 2).mul measurable_const

theorem gueEntry_meas_ldeQuadLHS (S : n → n → ℝ) (t : ℝ) (z : ℂ) (i : n) :
    Measurable fun H : Matrix n n ℂ => ldeQuadLHS H (green H z) S t i := by
  unfold ldeQuadLHS
  refine (((Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
    ((gueEntry_meas_entry i k).mul (gueEntry_meas_greenMinor z i k l)).mul
      (gueEntry_meas_entry l i)).sub
    (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      measurable_const.mul (gueEntry_meas_greenMinor z i k k)))).norm).pow_const 2

theorem gueEntry_meas_ldeQuadRHS (S : n → n → ℝ) (z : ℂ) (i : n) :
    Measurable fun H : Matrix n n ℂ => ldeQuadRHS S (green H z) i := by
  unfold ldeQuadRHS
  exact Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
    (measurable_const.mul ((gueEntry_meas_greenMinor z i k l).norm.pow_const 2)).mul
      measurable_const

end Meas

end GridTransfer

/-! ### From per-index tails to stochastic domination -/

section Families

theorem gueEntry_tail_eventually {τ D Cst : ℝ} (hτ : 0 < τ) (_hC : 0 ≤ Cst) {q : ℕ}
    (hq : D + τ ≤ (q : ℝ) * τ) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ τ ∧ Cst / ((N : ℝ) ^ τ / 2) ^ q ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [eventually_ge_atTop 1, eventually_le_rpow 2 hτ,
    eventually_le_rpow (Cst * 2 ^ q) hτ] with N hN1 h2 hC'
  refine ⟨h2, ?_⟩
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hX : ((N : ℝ) ^ τ / 2) ^ q = (N : ℝ) ^ ((q : ℝ) * τ) / 2 ^ q := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, mul_comm]
  have hmono : (N : ℝ) ^ (D + τ) ≤ (N : ℝ) ^ ((q : ℝ) * τ) :=
    Real.rpow_le_rpow_of_exponent_le hN hq
  have hpos : 0 < (N : ℝ) ^ (D + τ) := Real.rpow_pos_of_pos hN0 _
  have hsplit : (N : ℝ) ^ (D + τ) = (N : ℝ) ^ D * (N : ℝ) ^ τ := Real.rpow_add hN0 D τ
  have hnegD : (N : ℝ) ^ (-D) = ((N : ℝ) ^ D)⁻¹ := Real.rpow_neg hN0.le D
  have hD0 : 0 < (N : ℝ) ^ D := Real.rpow_pos_of_pos hN0 _
  have hτ0 : 0 < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hN0 _
  rw [hX, div_div_eq_mul_div, hnegD]
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hN0 _)]
  calc Cst * 2 ^ q ≤ (N : ℝ) ^ τ := hC'
    _ = ((N : ℝ) ^ D)⁻¹ * (N : ℝ) ^ (D + τ) := by rw [hsplit]; field_simp
    _ ≤ ((N : ℝ) ^ D)⁻¹ * (N : ℝ) ^ ((q : ℝ) * τ) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)

theorem gueEntry_exists_q {τ D : ℝ} (hτ : 0 < τ) : ∃ q : ℕ, D + τ ≤ (q : ℝ) * τ := by
  refine ⟨⌈(D + τ) / τ⌉₊, ?_⟩
  have := Nat.le_ceil ((D + τ) / τ)
  rw [div_le_iff₀ hτ] at this
  exact this

theorem gueEntry_stochDom_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U : ℕ → Type*} [∀ N, Fintype (U N)] {C : ℝ}
    (hC : ∀ᶠ N : ℕ in atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ C)
    {ξ ζ : ∀ N, U N → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), ∀ q : ℕ, ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ τ →
      ∀ u, P {ω | (N : ℝ) ^ τ * ζ N u ω < ξ N u ω}
        ≤ ENNReal.ofReal (Cst / ((N : ℝ) ^ τ / 2) ^ q)) :
    StochDom P ξ ζ := by
  refine StochDom.of_forall_le hC fun τ hτ D _ => ?_
  obtain ⟨q, hq⟩ := gueEntry_exists_q (D := D) hτ
  obtain ⟨Cst, hCst, hev⟩ := h τ hτ q
  filter_upwards [hev, gueEntry_tail_eventually hτ hCst hq] with N hN hN' u
  exact (hN hN'.1 u).trans (ENNReal.ofReal_le_ofReal hN'.2)

/-- `(N^τ/2)^q ≤ ((N^τ - 1)²)^{q+1}` once `N^τ ≥ 2`. -/
theorem gueEntry_pow_le_sq {x : ℝ} (hx : 2 ≤ x) (q : ℕ) :
    (x / 2) ^ q ≤ ((x - 1) ^ 2) ^ (q + 1) := by
  have h1 : 1 ≤ x / 2 := by linarith
  have h2 : x / 2 ≤ (x - 1) ^ 2 := by nlinarith
  calc (x / 2) ^ q ≤ (x / 2) ^ (q + 1) := pow_le_pow_right₀ h1 (Nat.le_succ q)
    _ ≤ ((x - 1) ^ 2) ^ (q + 1) := pow_le_pow_left₀ (by linarith) h2 _

theorem gueEntry_pow_le_self {x : ℝ} (hx : 2 ≤ x) (q : ℕ) : (x / 2) ^ q ≤ x ^ (q + 1) := by
  have h1 : 1 ≤ x / 2 := by linarith
  calc (x / 2) ^ q ≤ (x / 2) ^ (q + 1) := pow_le_pow_right₀ h1 (Nat.le_succ q)
    _ ≤ x ^ (q + 1) := pow_le_pow_left₀ (by linarith) (by linarith) _

theorem gueEntry_div_le_div {Cst Y Y' : ℝ} (hC : 0 ≤ Cst) (hY' : 0 < Y') (h : Y' ≤ Y) :
    Cst / Y ≤ Cst / Y' := div_le_div_of_nonneg_left hC hY' h

theorem gueEntry_card_grid (n0 : ℕ) :
    ∀ᶠ N : ℕ in atTop, ((gueGridK n0 N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ ((32 * n0 + 65 : ℕ) : ℝ) := by
  filter_upwards [eventually_ge_atTop (2 ^ (32 * n0 + 64) + 1)] with N hN
  rw [Real.rpow_natCast]
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hN
  have hnat : gueGridK n0 N + 1 ≤ N ^ (32 * n0 + 65) := by
    unfold gueGridK
    have h1 : (N + 1) ^ (32 * n0 + 64) ≤ (2 * N) ^ (32 * n0 + 64) :=
      Nat.pow_le_pow_left (by omega) _
    have h2 : (2 * N) ^ (32 * n0 + 64) = 2 ^ (32 * n0 + 64) * N ^ (32 * n0 + 64) := mul_pow _ _ _
    have h3 : 1 ≤ N ^ (32 * n0 + 64) := Nat.one_le_pow _ _ hN1
    have h4 : (2 ^ (32 * n0 + 64) + 1) * N ^ (32 * n0 + 64) ≤ N * N ^ (32 * n0 + 64) :=
      Nat.mul_le_mul_right _ hN
    have h5 : (2 ^ (32 * n0 + 64) + 1) * N ^ (32 * n0 + 64)
        = 2 ^ (32 * n0 + 64) * N ^ (32 * n0 + 64) + N ^ (32 * n0 + 64) := by ring
    rw [show N ^ (32 * n0 + 65) = N * N ^ (32 * n0 + 64) by ring]
    omega
  exact_mod_cast hnat

theorem gueEntry_card_grid_offPair (n0 : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (Fintype.card (Fin (gueGridK n0 N + 1) × OffPair d.L d.W N) : ℝ)
        ≤ (N : ℝ) ^ (((32 * n0 + 65 : ℕ) : ℝ) + 2) := by
  filter_upwards [gueEntry_card_grid n0, card_OffPair_le d, eventually_ge_atTop 1]
    with N h1 h2 hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Real.rpow_add hN0]
  exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)

theorem gueEntry_card_grid_idx (n0 : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (Fintype.card (Fin (gueGridK n0 N + 1) × d.Idx N) : ℝ)
        ≤ (N : ℝ) ^ (((32 * n0 + 65 : ℕ) : ℝ) + 1) := by
  filter_upwards [gueEntry_card_grid n0, eventually_card_Idx_le d, eventually_ge_atTop 1]
    with N h1 h2 hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Real.rpow_add hN0]
  exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)

variable {d}

theorem gueEntry_zt_im_pos {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| < 2) (h10 : ∀ N, t1 N ≤ t0 N)
    (ht0 : ∀ N, t0 N < 1) (n0 N : ℕ) (k : Fin (gueGridK n0 N + 1)) :
    0 < (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)).im := by
  rw [zt_im]
  have hu := gueEntry_time_le (K := gueGridK n0) (h10 N) (gueGridK_ne_zero n0 N)
    (Nat.lt_succ_iff.1 k.2)
  exact mul_pos (by linarith [ht0 N]) (mE_im_pos (hE N))

/-- **The row large deviation estimate along the grid.** -/
theorem gueEntry_stochDom_row {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, 0 ≤ t1 N)
    (h10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1) (n0 : ℕ) :
    StochDom (Pgue d)
      (fun N (p : Fin (gueGridK n0 N + 1) × OffPair d.L d.W N) ω =>
        ldeRowLHS (gueH d t1 t0 (gueGridK n0) N p.1 ω)
          (green (gueH d t1 t0 (gueGridK n0) N p.1 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1))) p.2.1.1 p.2.1.2)
      (fun N p ω => ldeRowRHS (gueEntryGridProf t1 t0 (gueGridK n0) N p.1)
          (green (gueH d t1 t0 (gueGridK n0) N p.1 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1))) p.2.1.1 p.2.1.2) := by
  refine gueEntry_stochDom_of_tail (gueEntry_card_grid_offPair d n0) fun τ _ q => ⟨hwConst q,
    (hwConst_pos q).le, Filter.Eventually.of_forall fun N h2 p => ?_⟩
  obtain ⟨k, ⟨⟨i, j⟩, hij⟩⟩ := p
  have hz := (gueEntry_zt_im_pos hE h10 ht0 n0 N k).ne'
  rw [gueEntry_transfer t1 t0 (gueGridK n0) N k (gueEntry_meas_ldeRowLHS _ i j)
    (gueEntry_meas_ldeRowRHS _ _ i j)]
  refine (gueEntry_row_tail (gueEntryVar_tagFree t1 t0 _ N k)
    (gueEntryGridProf_ok (ht1 N) (h10 N) k) hz hij (by linarith) q).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact gueEntry_div_le_div (hwConst_pos q).le (by positivity) (gueEntry_pow_le_sq h2 q)

/-- **The column large deviation estimate along the grid.** -/
theorem gueEntry_stochDom_col {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, 0 ≤ t1 N)
    (h10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1) (n0 : ℕ) :
    StochDom (Pgue d)
      (fun N (p : Fin (gueGridK n0 N + 1) × OffPair d.L d.W N) ω =>
        ldeColLHS (gueH d t1 t0 (gueGridK n0) N p.1 ω)
          (green (gueH d t1 t0 (gueGridK n0) N p.1 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1))) p.2.1.1 p.2.1.2)
      (fun N p ω => ldeColRHS (gueEntryGridProf t1 t0 (gueGridK n0) N p.1)
          (green (gueH d t1 t0 (gueGridK n0) N p.1 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1))) p.2.1.1 p.2.1.2) := by
  refine gueEntry_stochDom_of_tail (gueEntry_card_grid_offPair d n0) fun τ _ q => ⟨hwConst q,
    (hwConst_pos q).le, Filter.Eventually.of_forall fun N h2 p => ?_⟩
  obtain ⟨k, ⟨⟨i, j⟩, hij⟩⟩ := p
  have hz := (gueEntry_zt_im_pos hE h10 ht0 n0 N k).ne'
  rw [gueEntry_transfer t1 t0 (gueGridK n0) N k (gueEntry_meas_ldeColLHS _ i j)
    (gueEntry_meas_ldeColRHS _ _ i j)]
  refine (gueEntry_col_tail (gueEntryVar_tagFree t1 t0 _ N k)
    (gueEntryGridProf_ok (ht1 N) (h10 N) k) hz hij (by linarith) q).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact gueEntry_div_le_div (hwConst_pos q).le (by positivity) (gueEntry_pow_le_sq h2 q)

/-- **The quadratic large deviation estimate along the grid.** -/
theorem gueEntry_stochDom_quad {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, 0 ≤ t1 N)
    (h10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1) (n0 : ℕ) :
    StochDom (Pgue d)
      (fun N (p : Fin (gueGridK n0 N + 1) × d.Idx N) ω =>
        ldeQuadLHS (gueH d t1 t0 (gueGridK n0) N p.1 ω)
          (green (gueH d t1 t0 (gueGridK n0) N p.1 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)))
          (gueEntryGridProf t1 t0 (gueGridK n0) N p.1) 1 p.2)
      (fun N p ω => ldeQuadRHS (gueEntryGridProf t1 t0 (gueGridK n0) N p.1)
          (green (gueH d t1 t0 (gueGridK n0) N p.1 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1))) p.2) := by
  refine gueEntry_stochDom_of_tail (gueEntry_card_grid_idx d n0) fun τ _ q => ⟨hwConst q,
    (hwConst_pos q).le, Filter.Eventually.of_forall fun N h2 p => ?_⟩
  obtain ⟨k, i⟩ := p
  have hz := (gueEntry_zt_im_pos hE h10 ht0 n0 N k).ne'
  rw [gueEntry_transfer t1 t0 (gueGridK n0) N k (gueEntry_meas_ldeQuadLHS _ _ _ i)
    (gueEntry_meas_ldeQuadRHS _ _ i)]
  refine (gueEntry_quad_tail (gueEntryVar_tagFree t1 t0 _ N k)
    (gueEntryGridProf_ok (ht1 N) (h10 N) k) hz i (by linarith) q).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact gueEntry_div_le_div (hwConst_pos q).le (by positivity) (gueEntry_pow_le_self h2 q)

/-- **The diagonal entries along the grid**: `|H_{ii}|² ≺ S_u(i,i)`. -/
theorem gueEntry_stochDom_diag {t1 t0 : ℕ → ℝ} (ht1 : ∀ N, 0 ≤ t1 N)
    (h10 : ∀ N, t1 N ≤ t0 N) (n0 : ℕ) :
    StochDom (Pgue d)
      (fun N (p : Fin (gueGridK n0 N + 1) × d.Idx N) ω =>
        ‖gueH d t1 t0 (gueGridK n0) N p.1 ω p.2 p.2‖ ^ 2)
      (fun N p _ => gueEntryGridProf t1 t0 (gueGridK n0) N p.1 p.2 p.2) := by
  refine gueEntry_stochDom_of_tail (gueEntry_card_grid_idx d n0) fun τ _ q => ⟨dfac q,
    by unfold dfac; positivity, Filter.Eventually.of_forall fun N h2 p => ?_⟩
  obtain ⟨k, i⟩ := p
  have hA : Measurable fun H : Matrix (d.Idx N) (d.Idx N) ℂ => ‖H i i‖ ^ 2 :=
    (gueEntry_meas_entry i i).norm.pow_const 2
  have hB : Measurable fun _ : Matrix (d.Idx N) (d.Idx N) ℂ =>
      gueEntryGridProf t1 t0 (gueGridK n0) N k i i := measurable_const
  have htr := gueEntry_transfer t1 t0 (gueGridK n0) N k hA hB ((N : ℝ) ^ τ)
  dsimp only
  rw [htr]
  refine (gueEntry_diag_tail (gueEntryGridProf_ok (ht1 N) (h10 N) k) i (by linarith) q).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hq : ((N : ℝ) ^ τ / 2) ^ q ≤ ((N : ℝ) ^ τ) ^ q :=
    pow_le_pow_left₀ (by linarith) (by linarith) q
  exact gueEntry_div_le_div (by unfold dfac; positivity) (by positivity) hq

end Families

/-! ### Assembly -/

section Assembly

theorem gueEntry_gueH_eq_zero {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N k : ℕ} (ht1 : 0 ≤ t1 N)
    (h10 : t1 N ≤ t0 N) (hu : Grid.time t1 t0 K N k = 0) (ω : Grid.Ωg d) :
    gueH d t1 t0 K N k ω = 0 := by
  have hs := gueEntry_step_nonneg (K := K) h10
  have hks : 0 ≤ (k : ℝ) * Grid.step t1 t0 K N := mul_nonneg (Nat.cast_nonneg _) hs
  unfold Grid.time at hu
  have ht : t1 N = 0 := by linarith
  have hk : (k : ℝ) * Grid.step t1 t0 K N = 0 := by linarith
  unfold gueH
  rw [ht, Real.sqrt_zero, Complex.ofReal_zero, zero_smul, zero_add]
  rcases mul_eq_zero.1 hk with h | h
  · have hk0 : k = 0 := by exact_mod_cast h
    subst hk0
    simp
  · rw [h, zero_div, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]

theorem gueEntry_green_zero {n : Type*} [Fintype n] [DecidableEq n] {z m : ℂ}
    (hmz : m * z = -1) : green (0 : Matrix n n ℂ) z = m • (1 : Matrix n n ℂ) := by
  unfold green
  refine Matrix.inv_eq_left_inv ?_
  rw [zero_sub, Matrix.mul_neg, smul_mul_smul_comm, Matrix.one_mul, ← neg_smul, hmz, neg_neg,
    one_smul]

theorem gueEntry_goodEvent {n : Type*} [DecidableEq n] {G : Matrix n n ℂ} {m : ℂ}
    {δ : ℝ} (h : ∀ i j, ‖(G - m • (1 : Matrix n n ℂ)) i j‖ ≤ δ) : GoodEvent G m δ := by
  intro x y
  have hx := h x y
  have e : (G - m • (1 : Matrix n n ℂ)) x y = G x y - (if x = y then m else 0) := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
  rwa [e] at hx

/-- **Lemma 4.1, (4.2)+(4.3), for the GUE-phase profile** at every grid time, on the
a priori event `‖G - m‖_max ≤ δ_N`. -/
theorem gueGrid_entry_bound {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ) (ht1 : ∀ N, 0 ≤ t1 N)
    (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1)
    (h730 : ∀ᶠ N : ℕ in atTop, t0 N - t1 N ≤ (N : ℝ) ^ (-τU) * etaT (E N) (t0 N))
    {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) :
    StochDom (Pgue d)
      (fun N (p : Fin (gueGridK n0 N + 1) × (d.Idx N × d.Idx N)) ω =>
        {ω' | ∀ i j, ‖(green (gueH d t1 t0 (gueGridK n0) N p.1 ω')
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) -
            mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j‖ ≤ δ N}.indicator
          (fun ω' => ‖(green (gueH d t1 t0 (gueGridK n0) N p.1 ω')
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) -
            mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) p.2.1 p.2.2‖ ^ 2) ω)
      (fun N p ω => 9 * loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N p.1 ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) 2 + 2 * ((d.W N : ℕ) : ℝ)⁻¹) := by
  -- `h730` and `hτU` are not needed: the `J`-part of the profile is controlled by the Ward
  -- identity and the lower bound on `max L₂` (see the module docstring).
  set κ' := min κ 1 with hκ'
  have hκ'0 : 0 < κ' := lt_min hκ one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hE' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  have hE2 : ∀ N, |E N| < 2 := fun N => lt_of_le_of_lt (hE' N) (by linarith)
  have hR := gueEntry_stochDom_row (d := d) (E := E) hE2 ht1 ht10 ht0 n0
  have hC := gueEntry_stochDom_col (d := d) (E := E) hE2 ht1 ht10 ht0 n0
  have hQ := gueEntry_stochDom_quad (d := d) (E := E) hE2 ht1 ht10 ht0 n0
  have hD := gueEntry_stochDom_diag (d := d) ht1 ht10 n0
  refine StochDom.of_det (((hR.sumElim hC).sumElim hQ).sumElim hD) ?_ hδ0 hc₀ hδ
    (gueEntryDelta_pos hκ'0) (gueEntryCdet κ') 2 ?_
  · intro N p ω
    have := loopMax_nonneg (L := d.L N) (W := d.W N)
      (H := gueH d t1 t0 (gueGridK n0) N p.1 ω)
      (z := zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) 2
    positivity
  intro N ω Φ hΦ1 hΦδ hδε hAB p
  obtain ⟨k, i, j⟩ := p
  have hCd := gueEntryCdet_nonneg hκ'0
  have hLM := loopMax_nonneg (L := d.L N) (W := d.W N)
    (H := gueH d t1 t0 (gueGridK n0) N k ω)
    (z := zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) 2
  have hW0 : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  have hΦ2 : 0 ≤ Φ ^ 2 := sq_nonneg Φ
  have hRHS0 : 0 ≤ gueEntryCdet κ' * Φ ^ 2 *
      (9 * loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N k ω)
        (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) 2 + 2 * ((d.W N : ℕ) : ℝ)⁻¹) := by
    positivity
  have hu_ge : t1 N ≤ Grid.time t1 t0 (gueGridK n0) N k := gueEntry_time_ge (ht10 N)
  have hu_le : Grid.time t1 t0 (gueGridK n0) N k ≤ t0 N :=
    gueEntry_time_le (ht10 N) (gueGridK_ne_zero n0 N) (Nat.lt_succ_iff.1 k.2)
  have key : {ω' | ∀ i j, ‖(green (gueH d t1 t0 (gueGridK n0) N k ω')
        (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) -
        mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j‖ ≤ δ N}.indicator
      (fun ω' => ‖(green (gueH d t1 t0 (gueGridK n0) N k ω')
        (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) -
        mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j‖ ^ 2) ω
      ≤ gueEntryCdet κ' * Φ ^ 2 *
        (9 * loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N k ω)
          (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) 2 + 2 * ((d.W N : ℕ) : ℝ)⁻¹) := by
    by_cases hω : ω ∈ {ω' | ∀ i j, ‖(green (gueH d t1 t0 (gueGridK n0) N k ω')
        (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) -
        mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j‖ ≤ δ N}
    · rw [Set.indicator_of_mem hω]
      by_cases hu0 : Grid.time t1 t0 (gueGridK n0) N k = 0
      · have hH0 := gueEntry_gueH_eq_zero (d := d) (ht1 N) (ht10 N) hu0 ω
        have hmz : mE (E N) * zt (E N) (Grid.time t1 t0 (gueGridK n0) N k) = -1 := by
          have := mE_mul_add_zt (le_trans (hE' N) (by linarith)) 0
          rw [hu0]
          simpa using this
        have hL0 : ‖(green (gueH d t1 t0 (gueGridK n0) N k ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N k)) -
            mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i j‖ ^ 2 = 0 := by
          rw [hH0, gueEntry_green_zero hmz, sub_self]
          simp
        rw [hL0]
        exact hRHS0
      · have hupos : 0 < Grid.time t1 t0 (gueGridK n0) N k :=
          lt_of_le_of_ne (le_trans (ht1 N) hu_ge) (Ne.symm hu0)
        have hb : 0 ≤ (k : ℝ) * (Grid.step t1 t0 (gueGridK n0) N / (ouMatrixSize d N : ℝ)) :=
          mul_nonneg (Nat.cast_nonneg _)
            (div_nonneg (gueEntry_step_nonneg (ht10 N)) (gueEntry_M_pos N).le)
        have hΩ := gueEntry_goodEvent hω
        have h := gueEntry_det (d.three_le_L N) (gueH_isHermitian d t1 t0 (gueGridK n0) N k ω)
          hκ'0 hκ'1 (hE' N) (ht1 N) hb (gueEntry_time_eq N k) hupos
          (lt_of_le_of_lt hu_le (ht0 N)) hΩ hδε hΦ1 hΦδ
          (fun i j hij => hAB (Sum.inl (Sum.inl (Sum.inl (k, ⟨(i, j), hij⟩)))))
          (fun i j hij => hAB (Sum.inl (Sum.inl (Sum.inr (k, ⟨(i, j), hij⟩)))))
          (fun i => hAB (Sum.inl (Sum.inr (k, i))))
          (fun i => hAB (Sum.inr (k, i))) i j
        refine h.trans ?_
        have hA : 0 ≤ gueEntryCdet κ' * Φ ^ 2 := mul_nonneg hCd hΦ2
        refine mul_le_mul_of_nonneg_left ?_ hA
        linarith
    · rw [Set.indicator_of_notMem hω]
      exact hRHS0
  exact key

end Assembly

end RBM.Gauss.GUEGrid
