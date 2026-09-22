/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Eq45FlowBudget
import RBM1D.Gauss.FirstCellStep1LocalLaw

/-!
# Deterministic-scale Gaussian fluctuation averaging at a fixed time

`fixedTimeFAStatement` records the exact T332 target.  It is a proposition, not a theorem:
the results below establish the first two fixed moments at the already proved first-cell
scale, and do not claim the general deterministic-scale implication.
-/

namespace RBM.Gauss

open Filter MeasureTheory Finset

#check LocalLawUnifIcc
#check highProb_goodSetFlow_of_localLaw
#check hsmall_of_highProb
#check flucGainUpTo'_goodSetFlow
#check integral_norm_flucAvg_pow_le_iter_budget
#check firstCellFlucGain_from_localLaw
#check firstCell_localLawUnifIcc_of_step1

/-- The fixed-time (4.12) claim at a deterministic scale, with actual Gaussian flow,
polynomial spectral window and deterministic weights.  The degenerate interval `u..u` is
deliberate: its domination constants may be uniform in the prescribed deterministic time
sequence, while no path supremum is requested. -/
def fixedTimeFAStatement (d : Dims) (E : ℝ) (u Ψ : ℕ → ℝ) (a K : ℝ) : Prop :=
  0 < a → 0 ≤ K → |E| < 2 →
  (∀ N, 0 ≤ u N ∧ u N < 1) →
  (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N)) →
  (∀ᶠ N : ℕ in atTop,
    ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N ∧
      Ψ N ≤ (N : ℝ) ^ (-a)) →
  LocalLawUnifIcc d E u u Ψ →
  (UnifDomIcc (P d) u u
    (fun N v (i : d.Idx N) ω =>
      ‖flucAvg d N v (zt E v) (mE E)
        (fun j => Sblk (d.L N) (d.W N) i j) ω‖)
    (fun N _ _ _ => Ψ N ^ 2) ∧
  UnifDomIcc (P d) u u
    (fun N v (b : ZMod (d.L N)) ω =>
      ‖flucAvg d N v (zt E v) (mE E) (blkCoef (d.L N) (d.W N) b) ω‖)
    (fun N _ _ _ => Ψ N ^ 2))

/-- At the initial time the matrix is deterministic, hence every row fluctuation vanishes. -/
theorem flucDiag_at_zero (d : Dims) (N : ℕ) (z m : ℂ)
    (k : d.Idx N) (ω : Ω d) : flucDiag d N 0 z m k ω = 0 := by
  have hconst : greenDiagCentered d N 0 z m k =
      fun _ => green (0 : Matrix (d.Idx N) (d.Idx N) ℂ) z k k - m := by
    funext ω'
    simp [greenDiagCentered]
  simp [flucDiag, hconst]

theorem flucAvg_at_zero (d : Dims) (N : ℕ) (z m : ℂ)
    (Tw : d.Idx N → ℝ) (ω : Ω d) : flucAvg d N 0 z m Tw ω = 0 := by
  simp [flucAvg, flucDiag_at_zero]

/-- The fixed-`2p` finite-word/resampling producer at any deterministic threshold `δ`.
The only stochastic input is the ordinary high-probability entry event (4.1); the
exceptional resampling tower is paid by `hsmall_of_highProb`. -/
theorem fixedMoment_gain_of_goodSetFlow (d : Dims) {E : ℝ} {s t δ : ℕ → ℝ}
    (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (hδpos : ∀ N, 0 < δ N) (hδ4 : ∀ N, δ N ≤ 1 / 4)
    (hδlo : PolyLo δ)
    (hηhi : PolyHi fun N => (etaT E (t N))⁻¹ + 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (p : ℕ)
    (hMδ : ∀ᶠ N : ℕ in atTop, 8 * (2 * p : ℝ) * δ N ≤ 1)
    (hδC : ∀ᶠ N : ℕ in atTop,
      2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N v (zt E v) (mE E)
        (2 * (2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N))
        (4 * δ N) (2 * p) (2 * p) := by
  have hsmall := hsmall_of_highProb d hE ht1 hδpos hδlo hηhi hΩ p
  filter_upwards [hMδ, hδC, hsmall] with N hMδN hδCN hsmallN v hv
  have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
  have hΨ : (0 : ℝ) < 2 * δ N := by linarith [hδpos N]
  have hcc : condCost E v (2 * p) (2 * δ N)
      (condEps E v (2 * p) (2 * δ N)) = 2 * δ N :=
    condCost_condEps hE hv1 (2 * p) hΨ
  have h := flucGainUpTo'_goodSetFlow (E := E) (s := s) (t := t) (δ := δ)
    (M := 2 * p) (n := 2 * p) hE hv1 hv
    (condEps_nonneg hE hv1 (2 * p) hΨ.le)
    (hδpos N) (hδ4 N) (by push_cast; linarith [hMδN])
    (by rw [hcc]; exact hδCN) (by rw [hcc]; exact hsmallN v hv)
  convert h using 1 <;> norm_num [hcc] <;> ring

/-- The compiled `2p` core on an actual positive Gaussian window.  Its only stochastic
premise is the already established entry local law; the budgeted finite-word gain is
constructed by `firstCellFlucGain_from_localLaw`, not assumed. -/
theorem firstCell_fixedMoment_core {τ' θ : ℝ} (hτ' : 0 < τ')
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 32)
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi)
    {V : ℕ → Type*}
    {Tw : ∀ N, V N → Dims.exampleGrow.Idx N → ℝ}
    {cw : ℕ → ℝ} {Aw : ∀ N, V N → Finset (Dims.exampleGrow.Idx N)}
    (hw : ∀ N (j : V N), UniformWeight (Tw N j) (cw N) (Aw N j))
    (hcW : ∀ N, cw N ≤ ((Dims.exampleGrow.W N : ℝ))⁻¹)
    (hcard : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ j : V N, 2 * p ≤ (Aw N j).card)
    (p : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ v ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N), ∀ j : V N,
        ∫ ω, ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0) (Tw N j) ω‖ ^ (2 * p)
          ∂(P Dims.exampleGrow)
          ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * ((2 : ℝ) ^ (2 * p - 1) * firstCellBudgetRho θ N *
                  firstCellBudgetB θ p N) ^ (2 * p) := by
  have hg := firstCellFlucGain_from_localLaw hτ' hθ0 hθ hll p
  filter_upwards [hg, hcard p] with N hgN hcardN v hv j
  have hv1 : v < 1 :=
    lt_of_le_of_lt hv.2 ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
  have hcρ : cw N ≤ firstCellBudgetRho θ N ^ 2 :=
    (hcW N).trans (firstCellBudgetRho_sq_ge_W_inv hθ0.le N)
  exact integral_norm_flucAvg_pow_le_iter_budget (by norm_num : |(0 : ℝ)| < 2)
    hv1 (hgN v hv) le_rfl le_rfl
    (firstCellBudgetRho_le_one hθ0.le N) hcρ (hw N j) (hcardN j)

/-- The second moment, with moment order fixed before `N`. -/
theorem firstCell_fixedMoment_two {τ' θ : ℝ} (hτ' : 0 < τ')
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 32)
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi)
    {V : ℕ → Type*}
    {Tw : ∀ N, V N → Dims.exampleGrow.Idx N → ℝ}
    {cw : ℕ → ℝ} {Aw : ∀ N, V N → Finset (Dims.exampleGrow.Idx N)}
    (hw : ∀ N (j : V N), UniformWeight (Tw N j) (cw N) (Aw N j))
    (hcW : ∀ N, cw N ≤ ((Dims.exampleGrow.W N : ℝ))⁻¹)
    (hcard : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ j : V N, 2 * p ≤ (Aw N j).card) :
    ∀ᶠ N : ℕ in atTop,
      ∀ v ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N), ∀ j : V N,
        ∫ ω, ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0) (Tw N j) ω‖ ^ 2
          ∂(P Dims.exampleGrow)
          ≤ (3 : ℝ) * 2 ^ 2 *
              (2 * firstCellBudgetRho θ N * firstCellBudgetB θ 1 N) ^ 2 := by
  have h := firstCell_fixedMoment_core hτ' hθ0 hθ hll hw hcW hcard 1
  convert h using 1 <;> norm_num

/-- The fourth moment, with moment order fixed before `N`. -/
theorem firstCell_fixedMoment_four {τ' θ : ℝ} (hτ' : 0 < τ')
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 32)
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi)
    {V : ℕ → Type*}
    {Tw : ∀ N, V N → Dims.exampleGrow.Idx N → ℝ}
    {cw : ℕ → ℝ} {Aw : ∀ N, V N → Finset (Dims.exampleGrow.Idx N)}
    (hw : ∀ N (j : V N), UniformWeight (Tw N j) (cw N) (Aw N j))
    (hcW : ∀ N, cw N ≤ ((Dims.exampleGrow.W N : ℝ))⁻¹)
    (hcard : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ j : V N, 2 * p ≤ (Aw N j).card) :
    ∀ᶠ N : ℕ in atTop,
      ∀ v ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N), ∀ j : V N,
        ∫ ω, ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0) (Tw N j) ω‖ ^ 4
          ∂(P Dims.exampleGrow)
          ≤ (5 : ℝ) * 4 ^ 4 *
              (8 * firstCellBudgetRho θ N * firstCellBudgetB θ 2 N) ^ 4 := by
  have h := firstCell_fixedMoment_core hτ' hθ0 hθ hll hw hcW hcard 2
  convert h using 1 <;> norm_num

/-- A positive-length Gaussian first cell with the genuine Step 1 entry input exists. -/
theorem firstCell_fixedMoment_window_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ') firstCellPsi ∧
      (∀ᶠ N : ℕ in atTop, firstCellS τ' N < firstCellT τ' N) := by
  obtain ⟨τ', hτ', hll⟩ := firstCell_localLawUnifIcc_of_step1
  refine ⟨τ', hτ', hll, ?_⟩
  exact first_cell_window_nondegenerate Dims.exampleGrow hτ'

/-- The generic fixed-moment core applies to every actual variance-profile row. -/
theorem firstCell_rowMoment_core {τ' θ : ℝ} (hτ' : 0 < τ')
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 32)
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) (p : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ v ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
      ∀ i : Dims.exampleGrow.Idx N,
        ∫ ω, ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0)
          (fun j => Sblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) i j) ω‖ ^ (2 * p)
          ∂(P Dims.exampleGrow)
          ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * ((2 : ℝ) ^ (2 * p - 1) * firstCellBudgetRho θ N *
                  firstCellBudgetB θ p N) ^ (2 * p) := by
  let d := Dims.exampleGrow
  apply firstCell_fixedMoment_core hτ' hθ0 hθ hll
    (hw := fun N i => uniformWeight_Sblk i)
    (hcW := ?_)
    (hcard := ?_) p
  · intro N
    have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
    rw [inv_le_inv₀ (by linarith : (0 : ℝ) < 3 * d.W N) hw]
    linarith
  · intro q
    filter_upwards [eventually_le_W d (2 * q)] with N hN i
    rw [card_Sblk_support]
    change 2 * q ≤ 3 * d.W N
    omega

/-- The generic fixed-moment core also applies to every actual block average. -/
theorem firstCell_blockMoment_core {τ' θ : ℝ} (hτ' : 0 < τ')
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 32)
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) (p : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ v ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
      ∀ b : ZMod (Dims.exampleGrow.L N),
        ∫ ω, ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0)
          (blkCoef (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) b) ω‖ ^ (2 * p)
          ∂(P Dims.exampleGrow)
          ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * ((2 : ℝ) ^ (2 * p - 1) * firstCellBudgetRho θ N *
                  firstCellBudgetB θ p N) ^ (2 * p) := by
  let d := Dims.exampleGrow
  apply firstCell_fixedMoment_core hτ' hθ0 hθ hll
    (hw := fun N b => uniformWeight_blockAvg b)
    (hcW := fun N => le_rfl)
    (hcard := ?_) p
  intro q
  filter_upwards [eventually_le_W d (2 * q)] with N hN b
  rw [card_blockAvg_support]
  exact hN

#print axioms flucDiag_at_zero
#print axioms flucAvg_at_zero
#print axioms fixedMoment_gain_of_goodSetFlow
#print axioms firstCell_fixedMoment_core
#print axioms firstCell_fixedMoment_two
#print axioms firstCell_fixedMoment_four
#print axioms firstCell_fixedMoment_window_witness
#print axioms firstCell_rowMoment_core
#print axioms firstCell_blockMoment_core

end RBM.Gauss
