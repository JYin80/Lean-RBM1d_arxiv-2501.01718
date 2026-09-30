/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.EntryBoundTime
import RBM1D.EnergyN.Gauss.Lemma41FlowGauss
import RBM1D.EnergyN.Hierarchy.Step1
import RBM1D.EnergyN.Gauss.LDENetClose
import RBM1D.EnergyN.Green.EntryBoundFloor
import RBM1D.EnergyN.Green.EntryBoundFloorIdx
import RBM1D.EnergyN.Gauss.Step1Hyp
import RBM1D.EnergyN.Gauss.DistEq

/-!
# The entry bounds of Lemma 4.1 along the flow, at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 4.1, (4.2) and (4.3).

At an `N`-dependent energy `E : ℕ → ℝ`: the predicates `RBM.Gauss.EntryBoundFlow'N` ((4.2) on
the good set, with a floor) and `RBM.Gauss.DiagBoundFlow'N` ((4.3) on the good set, with a
floor); their proofs for the Gaussian flow, `RBM.Gauss.entryBoundFlow_floorN` and
`RBM.Gauss.diagBoundFlow_floorN`; the resulting bounds on `|G|²` on the event `Step1.goodEv`;
Lemma 4.1 along the flow (`RBM.Gauss.lemma41Flow''N`, `RBM.Gauss.lemma41Flow_gaussN`); and the
hypotheses of Step 1 (`RBM.Gauss.step1Hyp_gauss_of_scale''N`). None fixes an energy-dependent
constant.

The inputs of `diagBoundFlow_floorN` are the floored large-deviation bounds of
`RBM1D/EnergyN/Gauss/LDENetClose.lean` and `RBM.diag_bound_stochDom_floor_idxN`
(`RBM1D/EnergyN/Green/EntryBoundFloor.lean`). `entryBoundFlow_floorN` calls the (4.2) engine
`RBM.entry_bound_stochDom_floor_idxN` (`RBM1D/EnergyN/Green/EntryBoundFloorIdx.lean`) at
`zf N := zt (E N)`, `m N := mE (E N)`; the engine takes `N`-dependent `zf` and `m`, so no
`N`-independent value is fixed across `StochDom`. `lemma41Flow_gaussN` and
`step1Hyp_gauss_of_scale''N` follow.
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset

section Flow

variable {d : Dims} {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **(4.2) along the flow, on the good set, with the floor `fl`**: for `i ≠ j`,
`1_{goodSet} |G_ij|²` is dominated by the sum of `Lre` over the `S`-neighbourhoods of the two
blocks, plus `W⁻¹` when the blocks are `S`-adjacent, plus `fl`, uniformly in `u ∈ [s, t]`. No
energy-dependent constant is fixed here (only the events `goodSet`/`green`/`Lre` are threaded
through). -/
def EntryBoundFlow'N (d : Dims) (E : ℕ → ℝ) (s t : ℕ → ℝ) (fl : ℕ → ℝ) : Prop :=
  StochDom (P d)
    (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ))
          (mE (E N)) (flowDelta d (E N) t) N).indicator
        (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) p.2.1.1 p.2.1.2‖ ^ 2) ω)
    (fun N p ω =>
      (∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
          Lre (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) (p.2.1.2.1 + b) (p.2.1.1.1 + a))
        + (if p.2.1.1.1 - p.2.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        + fl N)

/-- **`EntryBoundFlow'N` with the floor `2 N^{-B}` for the Gaussian flow**, when `N^{-K} ≤ η_t`
and `flowDelta ≤ N^{-c₀}` eventually. No energy-dependent constant is fixed here: the (4.2)
engine `RBM.entry_bound_stochDom_floor_idxN` is called at `zf := fun N => zt (E N)`,
`m := fun N => mE (E N)`, with the floored row/column inputs. -/
theorem entryBoundFlow_floorN (d : Dims) (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (t N)) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, flowDelta d (E N) t N ≤ (N : ℝ) ^ (-c₀)) {B : ℝ} (hB : 0 ≤ B) :
    EntryBoundFlow'N d E s t (fun N => 2 * (N : ℝ) ^ (-B)) := by
  have hδ0 : ∀ N, 0 ≤ flowDelta d (E N) t N := by
    intro N
    have ht0 : (0 : ℝ) ≤ t N := le_trans (hs0 N) (hst N)
    have hpos : 0 < (band d).scale (E N) N (t N) := (band d).scale_pos' (hE N) N ht0 (ht1 N)
    exact Real.rpow_nonneg (by positivity) _
  exact entry_bound_stochDom_floor_idxN (P d) (L := d.L) (W := d.W)
    (U := fun N => RBM.TimeIcc s t N) d.three_le_L
    (fun N u ω => Hflow d N u ω) (fun N u => (u : ℝ)) (fun N => zt (E N))
    (fun N u ω => Hflow_isHermitian d N u ω)
    (fun N u => zt_im_ne_zero_of_lt_one (hE N) (lt_of_le_of_lt u.2.2 (ht1 N)))
    (m := fun N => mE (E N)) (fun N => norm_mE (le_of_lt (hE N)))
    (δ := fun N => flowDelta d (E N) t N) hδ0 hc₀ hδ
    (fun N => Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (stochDom_ldeRow_flow_floorN d hE hs0 hst ht1 hK hη hB)
    (stochDom_ldeCol_flow_floorN d hE hs0 hst ht1 hK hη hB)

/-- **(4.3) along the flow, on the good set, with the floor `fl`**:
`1_{goodSet} |G_ii - m|² ≺ Lmax + fl`, uniformly in `u ∈ [s, t]`. No energy-dependent constant
is fixed here. -/
def DiagBoundFlow'N (d : Dims) (E : ℕ → ℝ) (s t : ℕ → ℝ) (fl : ℕ → ℝ) : Prop :=
  StochDom (P d)
    (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
      (goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ))
          (mE (E N)) (flowDelta d (E N) t) N).indicator
        (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) p.2 p.2 - mE (E N)‖ ^ 2) ω)
    (fun N p ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) + fl N)

/-- **`DiagBoundFlow'N` with the floor `N^{-B}` for the Gaussian flow**, when `N^{-K} ≤ η_t` and
`flowDelta ≤ N^{-c₀}` eventually. No energy-dependent constant is fixed here: the gap `κ` is
explicit, `∀ N, |E N| ≤ 2 - κ` with `0 < κ ≤ 1`. -/
theorem diagBoundFlow_floorN (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (t N)) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, flowDelta d (E N) t N ≤ (N : ℝ) ^ (-c₀)) {B : ℝ} (hB : 0 ≤ B) :
    DiagBoundFlow'N d E s t (fun N => (N : ℝ) ^ (-B)) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by have := hE N; linarith
  have hδ0 : ∀ N, 0 ≤ flowDelta d (E N) t N := by
    intro N
    have ht0 : (0 : ℝ) ≤ t N := le_trans (hs0 N) (hst N)
    have hpos : 0 < (band d).scale (E N) N (t N) := (band d).scale_pos' (hE2 N) N ht0 (ht1 N)
    exact Real.rpow_nonneg (by positivity) _
  exact diag_bound_stochDom_floor_idxN (P d) (L := d.L) (W := d.W)
    (U := fun N => RBM.TimeIcc s t N) d.three_le_L
    (fun N u ω => Hflow d N u ω) (fun N u => (u : ℝ))
    (fun N u ω => Hflow_isHermitian d N u ω) hκ0 hκ1 hE
    (fun N u => le_trans (hs0 N) u.2.1)
    (fun N u => lt_of_le_of_lt u.2.2 (ht1 N))
    (δ := fun N => flowDelta d (E N) t N)
    hδ0 hc₀ hδ (fun N => Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (stochDom_ldeRow_flow_floorN d hE2 hs0 hst ht1 hK hη hB)
    (stochDom_ldeCol_flow_floorN d hE2 hs0 hst ht1 hK hη hB)
    (stochDom_ldeQuad_flow_floorN d hE2 hs0 hst ht1 hK hη hB)
    (stochDom_normSq_Hflow_diag_idx (d := d) (fun N (u : RBM.TimeIcc s t N) => (u : ℝ))
      (fun N u => le_trans (hs0 N) u.2.1)
      (fun N u => le_of_lt (lt_of_le_of_lt u.2.2 (ht1 N))))

section Consumer

variable {Φ : ∀ N, RBM.TimeIcc s t N → ℝ}

/-- **`1_{goodEv} |G_ij|² ≺ Φ + W⁻¹` for `i ≠ j`**, uniformly in `u ∈ [s, t]`, from
`EntryBoundFlow'N` with a floor `fl ≤ W⁻¹` and the loop bound `LoopHypFlowN` with the control
`Φ`. -/
theorem stochDom_indicator_offdiag_flow'N (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) {fl : ℕ → ℝ}
    (hflW : ∀ᶠ N : ℕ in atTop, fl N ≤ ((d.W N : ℕ) : ℝ)⁻¹)
    (hEntry : EntryBoundFlow'N d E s t fl) (hΦ0 : ∀ N u, 0 ≤ Φ N u)
    (hΦ : LoopHypFlowN d E s t Φ) :
    StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
        (Step1.goodEv (sample d) (E N) N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) p.2.1.1 p.2.1.2‖ ^ 2) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) := by
  have h1 : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
        (Step1.goodEv (sample d) (E N) N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) p.2.1.1 p.2.1.2‖ ^ 2) ω)
      (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
        ((∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
            Lre (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) (p.2.1.2.1 + b) (p.2.1.1.1 + a))
          + if p.2.1.1.1 - p.2.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
          + fl N) :=
    stochDom_mono_left hEntry fun N p ω =>
      Set.indicator_le_indicator_of_subset (goodEv_subset_goodSet_flow (hE N) hs0 ht1 N p.1)
        (fun _ => by positivity) ω
  have h2 := stochDom_indicator_add_const
    (A := fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) =>
      Step1.goodEv (sample d) (E N) N (p.1 : ℝ))
    (c := fl) (stochDom_indicator_entryControl_flowN hΦ0 hΦ)
    (fun N p _ => by
      have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
      linarith [hΦ0 N p.1])
    (by
      filter_upwards [hflW] with N hN p _
      linarith [hΦ0 N p.1])
  refine stochDom_trans_indicator_idx h1 h2 (fun N p _ => ?_)
  have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  linarith [hΦ0 N p.1]

/-- **`1_{goodEv} llMax² ≺ Φ + W⁻¹`**, uniformly in `u ∈ [s, t]`, from the off-diagonal bound
`hoff` and the diagonal bound `hdg` of the same form. -/
theorem stochDom_indicator_llMax_sq_flow_ofN (hΦ0 : ∀ N u, 0 ≤ Φ N u)
    (hoff : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × OffPair d.L d.W N) ω =>
        (Step1.goodEv (sample d) (E N) N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) p.2.1.1 p.2.1.2‖ ^ 2) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹))
    (hdg : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) (E N) N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) p.2 p.2 - mE (E N)‖ ^ 2)
            ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹)) :
    StochDom (P d)
      (fun N (u : RBM.TimeIcc s t N) ω =>
        (Step1.goodEv (sample d) (E N) N (u : ℝ)).indicator
          (fun ω => Step1.llMax (sample d) (E N) N (u : ℝ) ω ^ 2) ω)
      (fun N u _ => Φ N u + ((d.W N : ℕ) : ℝ)⁻¹) := by
  refine StochDom.of_subset_union hoff hdg fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards with N
  intro ω hω
  simp only [badSet, Set.mem_ofPred_eq] at hω
  obtain ⟨u, hlt⟩ := hω
  have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  have hC : (0 : ℝ) ≤ (N : ℝ) ^ τ * (Φ N u + ((d.W N : ℕ) : ℝ)⁻¹) := by
    have h1 : (0 : ℝ) ≤ Φ N u + ((d.W N : ℕ) : ℝ)⁻¹ := by linarith [hΦ0 N u]
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) τ
    positivity
  by_cases hmem : ω ∈ Step1.goodEv (sample d) (E N) N (u : ℝ)
  · rw [Set.indicator_of_mem hmem] at hlt
    set c : ℝ := (N : ℝ) ^ τ * (Φ N u + ((d.W N : ℕ) : ℝ)⁻¹) with hc
    set r : ℝ := Real.sqrt c with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg c
    have hr2 : r ^ 2 = c := Real.sq_sqrt hC
    have hex : ∃ ij : (band d).Idx N × (band d).Idx N,
        r < (sample d).llErr (E N) N (u : ℝ) ω ij := by
      by_contra hcon
      push Not at hcon
      have : Step1.llMax (sample d) (E N) N (u : ℝ) ω ≤ r := Step1.llMax_le _ hcon
      have hm0 : 0 ≤ Step1.llMax (sample d) (E N) N (u : ℝ) ω :=
        Step1.llMax_nonneg _ N (u : ℝ) ω
      nlinarith [hlt, hr2, this, hm0]
    obtain ⟨ij, hij⟩ := hex
    have hij0 : 0 ≤ (sample d).llErr (E N) N (u : ℝ) ω ij := norm_nonneg _
    have hsq : c < (sample d).llErr (E N) N (u : ℝ) ω ij ^ 2 := by
      nlinarith [hij, hr0, hr2, hij0]
    rw [(sample d).llErr_eq N (u : ℝ) ω ij] at hsq
    by_cases hne : ij.1 = ij.2
    · refine Set.mem_union_right _ ⟨(u, ij.2), ?_⟩
      show c < (Step1.goodEv (sample d) (E N) N (u : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (u : ℝ) ω) (zt (E N) (u : ℝ)) ij.2 ij.2 - mE (E N)‖ ^ 2) ω
      rw [Set.indicator_of_mem hmem]
      rw [hne] at hsq
      simp only [↓reduceIte] at hsq
      exact hsq
    · refine Set.mem_union_left _ ⟨(u, ⟨(ij.1, ij.2), hne⟩), ?_⟩
      show c < (Step1.goodEv (sample d) (E N) N (u : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (u : ℝ) ω) (zt (E N) (u : ℝ)) ij.1 ij.2‖ ^ 2) ω
      rw [Set.indicator_of_mem hmem]
      simp only [hne, ↓reduceIte, sub_zero] at hsq
      exact hsq
  · rw [Set.indicator_of_notMem hmem] at hlt
    exact absurd hlt (not_lt.2 hC)

/-- **`N^{-1} ≤ η_t` eventually**, from `N^c ≤ W ℓ_t η_t` eventually. -/
theorem rpow_neg_one_le_etaT_of_scale_geN (d : Dims) (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT (E N) (t N) := by
  filter_upwards [hreg, (band d).dim, Filter.eventually_ge_atTop 1] with N hregN hdim hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hW : (0 : ℝ) < (band d).W N := by exact_mod_cast (band d).W_pos N
  have hη : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE N) (ht1 N)
  have hℓL : (band d).ell N (t N) ≤ (((band d).L N : ℕ) : ℝ) := min_le_right _ _
  have hWL : (((band d).W N : ℕ) : ℝ) * (((band d).L N : ℕ) : ℝ) ≤ N := by exact_mod_cast hdim.1
  have hscale : (band d).scale (E N) N (t N) ≤ (N : ℝ) * etaT (E N) (t N) := by
    rw [Band.scale]
    calc (((band d).W N : ℕ) : ℝ) * (band d).ell N (t N) * etaT (E N) (t N)
        ≤ (((band d).W N : ℕ) : ℝ) * (((band d).L N : ℕ) : ℝ) * etaT (E N) (t N) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓL hW.le) hη.le
      _ ≤ (N : ℝ) * etaT (E N) (t N) := mul_le_mul_of_nonneg_right hWL hη.le
  have hkey : (N : ℝ) ^ (c - 1) ≤ etaT (E N) (t N) := by
    have h1 := hregN.trans hscale
    have he : (N : ℝ) ^ (c - 1) = (N : ℝ) ^ c / (N : ℝ) := by
      rw [show c - 1 = c + -(1 : ℝ) by ring, Real.rpow_add hN0, Real.rpow_neg_one,
        div_eq_mul_inv]
    rw [he, div_le_iff₀ hN0]
    linarith
  exact le_trans (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)) hkey

/-- **`flowDelta ≤ N^{-c/6}` eventually**, from `N^c ≤ W ℓ_t η_t` eventually. -/
theorem flowDelta_le_rpow_negN (d : Dims) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ᶠ N : ℕ in atTop, flowDelta d (E N) t N ≤ (N : ℝ) ^ (-(c / 6)) := by
  filter_upwards [hreg, Filter.eventually_ge_atTop 1] with N hregN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNc : (0 : ℝ) < (N : ℝ) ^ c := Real.rpow_pos_of_pos hN0 c
  have hinv : ((band d).scale (E N) N (t N))⁻¹ ≤ ((N : ℝ) ^ c)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hNc hregN
  have hlast : (((N : ℝ) ^ c)⁻¹) ^ ((1 : ℝ) / 6) = (N : ℝ) ^ (-(c / 6)) := by
    rw [← Real.rpow_neg hN0.le, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  have hsc : 0 < (band d).scale (E N) N (t N) := lt_of_lt_of_le hNc hregN
  show ((band d).scale (E N) N (t N))⁻¹ ^ ((1 : ℝ) / 6) ≤ (N : ℝ) ^ (-(c / 6))
  rw [← hlast]
  exact Real.rpow_le_rpow (le_of_lt (inv_pos.2 hsc)) hinv (by norm_num)

/-- **`1_{goodEv} |G_ii - m|² ≺ Φ + W⁻¹`**, uniformly in `u ∈ [s, t]`, from `DiagBoundFlow'N`
with a floor `fl ≤ W⁻¹` and the loop bound `LoopHypFlowN` with the control `Φ`. -/
theorem stochDom_indicator_diag_flow'N (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1)
    {fl : ℕ → ℝ} (hflW : ∀ᶠ N : ℕ in atTop, fl N ≤ ((d.W N : ℕ) : ℝ)⁻¹)
    (hDiag : DiagBoundFlow'N d E s t fl) (hΦ0 : ∀ N u, 0 ≤ Φ N u)
    (hΦ : LoopHypFlowN d E s t Φ) :
    StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) (E N) N (p.1 : ℝ)).indicator
          (fun ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) p.2 p.2 - mE (E N)‖ ^ 2) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) := by
  have h1 : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) (E N) N (p.1 : ℝ)).indicator
          (fun ω =>
            ‖green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) p.2 p.2 - mE (E N)‖ ^ 2) ω)
      (fun N p ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) + fl N) :=
    stochDom_mono_left hDiag fun N p ω =>
      Set.indicator_le_indicator_of_subset (goodEv_subset_goodSet_flow (hE N) hs0 ht1 N p.1)
        (fun _ => by positivity) ω
  have hLmax : StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) (E N) N (p.1 : ℝ)).indicator
          (fun ω => Lmax (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ))) ω)
      (fun N p _ => Φ N p.1 + ((d.W N : ℕ) : ℝ)⁻¹) :=
    StochDom.control_mono
      (stochDom_indicator_Lmax_flowN (V := fun N => BIdx d.L d.W N) hΦ0 hΦ)
      (fun N p _ => by
        have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
        linarith)
  have h2 := stochDom_indicator_add_const
    (A := fun N (p : RBM.TimeIcc s t N × BIdx d.L d.W N) =>
      Step1.goodEv (sample d) (E N) N (p.1 : ℝ))
    (c := fl) hLmax
    (fun N p _ => by
      have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
      linarith [hΦ0 N p.1])
    (by
      filter_upwards [hflW] with N hN p _
      linarith [hΦ0 N p.1])
  refine stochDom_trans_indicator_idx h1 h2 (fun N p _ => ?_)
  have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  linarith [hΦ0 N p.1]

/-- **Lemma 4.1 along the flow (`Step1.Lemma41FlowN`)**, from `EntryBoundFlow'N` and
`DiagBoundFlow'N` with floors at most `W⁻¹`. -/
theorem lemma41Flow''N (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {flE flD : ℕ → ℝ}
    (hflE : ∀ᶠ N : ℕ in atTop, flE N ≤ ((d.W N : ℕ) : ℝ)⁻¹)
    (hflD : ∀ᶠ N : ℕ in atTop, flD N ≤ ((d.W N : ℕ) : ℝ)⁻¹)
    (hEntry : EntryBoundFlow'N d E s t flE) (hDiag : DiagBoundFlow'N d E s t flD) :
    Step1.Lemma41FlowN (sample d) E s t := by
  intro Ψ hΨ0 hloop
  exact stochDom_indicator_llMax_sq_flow_ofN hΨ0
    (stochDom_indicator_offdiag_flow'N hE hs0 ht1 hflE hEntry hΨ0 (loopHypFlow_iffN.2 hloop))
    (stochDom_indicator_diag_flow'N hE hs0 ht1 hflD hDiag hΨ0 (loopHypFlow_iffN.2 hloop))

/-- **Lemma 4.1 along the Gaussian flow (`Step1.Lemma41FlowN`)**, when `N^{-K} ≤ η_t` and
`flowDelta ≤ N^{-c₀}` eventually. No energy-dependent constant is fixed here: the gap `κ`
(`0 < κ ≤ 1`) is explicit, `∀ N, |E N| ≤ 2 - κ`. -/
theorem lemma41Flow_gaussN (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (t N)) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, flowDelta d (E N) t N ≤ (N : ℝ) ^ (-c₀)) :
    Step1.Lemma41FlowN (sample d) E s t := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by have := hE N; linarith
  exact lemma41Flow''N hE2 hs0 ht1 (eventually_two_rpow_neg_one_le_W_inv d)
    (eventually_rpow_neg_one_le_W_inv d)
    (entryBoundFlow_floorN d hE2 hs0 hst ht1 hK hη hc₀ hδ zero_le_one)
    (diagBoundFlow_floorN d hκ0 hκ1 hE hs0 hst ht1 hK hη hc₀ hδ zero_le_one)

/-- **The hypotheses of Step 1 (`Step1.HypN`) for the Gaussian flow**, from (2.68)–(2.70) at `s`,
(2.72) and `N^c ≤ W ℓ_t η_t` eventually. No energy-dependent constant is fixed here: the gap
`κ` is explicit, and the inputs `eq58_seq_thrN` and `netLift_gaussN` take it. -/
theorem step1Hyp_gauss_of_scale''N (d : Dims) {κ : ℝ} (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    Step1.HypN (sample d) E s t := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by have := hE N; linarith
  have hκ0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ1 : min κ 1 ≤ 1 := min_le_right _ _
  have hEκ : ∀ N, |E N| ≤ 2 - min κ 1 := by
    intro N
    have hmin : min κ 1 ≤ κ := min_le_left _ _
    have := hE N
    linarith
  have hS : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
      LoopScalingN (sample d) E t₁ t₂ := fun t₁ t₂ h1 h12 _ =>
    loopScaling_gaussN (d := d) (fun N => lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (h1 N)) h12
  exact
    { scaling := hS
      lift := fun n hn => netLift_gaussN d hκ hE hs0 hst ht1 one_pos
        (rpow_neg_one_le_one_sub_of_scale_geN (band d) hE2 ht1 hc0 hreg) hn
        (fun u => eq58_seq_thrN (sample d) hκ hE (C₀ := 3) (by norm_num) hB hs0 hst ht1 hcond
          hS u hn)
      lemma41 := lemma41Flow_gaussN d hκ0 hκ1 hEκ hs0 hst ht1 zero_le_one
        (rpow_neg_one_le_etaT_of_scale_geN d hE2 ht1 hc0 hreg)
        (by linarith : (0 : ℝ) < c / 6) (flowDelta_le_rpow_negN d hreg)
      cont := cont_gaussN d hE2 (fun N => (hs0 N)) ht1 }

end Consumer

end Flow

section Compat

variable {d : Dims} {E : ℝ} {s t : ℕ → ℝ}

end Compat

end RBM.Gauss
