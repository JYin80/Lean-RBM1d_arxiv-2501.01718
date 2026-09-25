/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeAssembly
import RBM1D.Gauss.APrimeGeneralMovingEndpointFamily
import RBM1D.Gauss.APrimeFirstCellCrossOrderWeight
import RBM1D.Gauss.APrimeFirstCellFamilyHighMoment
import RBM1D.Gauss.APrimeGeneralMovingCommonSources

/-!
# T1307: conditional actual-coordinate to widened moving-family bridge

The sole probabilistic input below is a uniform, same-actual-weight coordinate
`L^(2q)` estimate.  Its order `q` is selected after the target loss and order,
but before the eventual size cutoff.  Endpoint maximum, the `L_N^2 ≤ N^2`
family cost, weighted Lyapunov, and the accepted same-loss cross-order
comparison then give the exact widened-family consumer of `APrimeAssembly`.

This module does not prove the coordinate input, or identify it with a paper
theorem.  It only records the conditional bridge at the prescribed loss
schedule.
-/

namespace RBM.APrimeFreeLossFamilyBridge

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

private theorem rpow_nat_power {x α : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (x ^ α) ^ n = x ^ (α * (n : ℝ)) := by
  calc
    (x ^ α) ^ n = (x ^ α) ^ (n : ℝ) := (Real.rpow_natCast (x ^ α) n).symm
    _ = x ^ (α * (n : ℝ)) := (Real.rpow_mul hx α (n : ℝ)).symm

/-- The corrected free-loss schedule for one target loss. -/
noncomputable def sourceLoss (loss : ℝ) : ℝ := loss / 1000
noncomputable def xi (loss : ℝ) : ℝ := loss
noncomputable def capLoss (loss : ℝ) : ℝ := 2 * loss

/-- The corrected losses have all required strict room when
`loss ≤ min (1/10000) (c/10000)`. -/
theorem corrected_loss_schedule {loss c : ℝ} (hc : 0 < c)
    (hloss : 0 < loss) (hsmall : loss ≤ min (1 / 10000) (c / 10000)) :
    0 < sourceLoss loss ∧ xi loss = loss ∧ capLoss loss = loss + xi loss ∧
      sourceLoss loss ≤ loss / 16 ∧ sourceLoss loss ≤ capLoss loss / 16 ∧
      capLoss loss ≤ c / 20 ∧
      sourceLoss loss + 2 * capLoss loss + (2 : ℝ) / 15 < 1 := by
  have hloss1 : loss ≤ 1 / 10000 := hsmall.trans (min_le_left _ _)
  have hlossc : loss ≤ c / 10000 := hsmall.trans (min_le_right _ _)
  dsimp [sourceLoss, xi, capLoss]
  constructor
  · positivity
  constructor
  · rfl
  constructor
  · ring
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The actual endpoint coordinate used by the moving endpoint producer. -/
noncomputable def endpointCoordinate (E D : ℝ) (s : ℕ → ℝ)
    (N k : ℕ) (a : LoopArg (d.L N) 2) (ω : Ω d) : ℝ :=
  ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N)
    (cutNetPt s (mesh D) N k) (cutNetPt s (mesh D) N k)
    (Hflow d N (cutNetPt s (mesh D) N k) ω)‖

/-- The canonical same-actual-weight coordinate estimate at loss `loss` and
fixed order `q`.  Integrability is explicit, so the Bochner integral cannot
make the hypothesis vacuous. -/
def SameActualCoordinateMoment (E D loss C₀ : ℝ) (s t : ℕ → ℝ)
    (q N k : ℕ) : Prop :=
  ∀ a : LoopArg (d.L N) 2,
    AEStronglyMeasurable (endpointCoordinate E D s N k a) (Gauss.P d) ∧
    Integrable
      (fun ω =>
        APrimeSmoothWeightActual.weight d E D loss s t (mesh D) 2 q N k
          (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω *
          |endpointCoordinate E D s N k a ω| ^ (2 * q)) (Gauss.P d) ∧
    ∫ ω,
      APrimeSmoothWeightActual.weight d E D loss s t (mesh D) 2 q N k
        (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω *
        |endpointCoordinate E D s N k a ω| ^ (2 * q) ∂(Gauss.P d) ≤
      (C₀ * (N : ℝ) ^ (5 * loss / 32)) ^ (2 * q)

/-- For each requested positive loss and order, the high coordinate order and
its constant are fixed before the eventual threshold in `N`. -/
def UniformSameActualCoordinateInput (E D c : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ loss : ℝ, 0 < loss → loss ≤ min (1 / 10000) (c / 10000) →
    ∀ p : ℕ, 1 ≤ p →
      ∃ q : ℕ, max p (Nat.ceil (16 / loss)) ≤ q ∧
        ∃ C₀ : ℝ, 0 < C₀ ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ k : ℕ, k ≤ cutNetTop s t (mesh D) N →
              SameActualCoordinateMoment E D loss C₀ s t q N k

noncomputable def targetWeight (E D δ : ℝ) (s t : ℕ → ℝ)
    (p N k : ℕ) : Ω d → ℝ :=
  APrimeWeight.widenedW (APrimeWeight.canonicalR s t (mesh D)) 1
    (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
    s t (mesh D) δ p N k

noncomputable def targetJ (E D : ℝ) (s : ℕ → ℝ)
    (N : ℕ) (u : ℝ) (ω : Ω d) : ℝ :=
  Step2Moment.jSnorm (Gauss.sample d) E D s N u ω

private theorem targetWeight_fields {E D δ : ℝ} {s t : ℕ → ℝ}
    (N p k : ℕ) :
    (∀ ω, 0 ≤ targetWeight E D δ s t p N k ω) ∧
    (∀ ω, targetWeight E D δ s t p N k ω ≤ 1) ∧
    AEStronglyMeasurable (targetWeight E D δ s t p N k) (Gauss.P d) := by
  let J : ℕ → ℝ → Ω d → ℝ := fun N u ω => targetJ E D s N u ω
  have hJ : ∀ N u, Measurable (fun ω => J N u ω) := by
    intro N u
    exact APrimeSlotFields.measurable_jSnorm (Gauss.sample d) E D s N u
  refine ⟨?_, ?_, ?_⟩
  · intro ω
    exact APrimeWeight.widenedW_nonneg _ _ _ _ _ _ _ _ _ _ ω
  · intro ω
    exact APrimeWeight.widenedW_le_one _ _ _ _ _ _ _ _ _ _ ω
  · exact APrimeWeight.widenedW_meas
      (r := APrimeWeight.canonicalR s t (mesh D)) (N₀ := 1)
      (J := fun N u ω => targetJ E D s N u ω)
      (s := s) (t := t) (mesh := mesh D) hJ p δ N k

private theorem actualWeight_cross_order {E D loss : ℝ} {s t : ℕ → ℝ}
    {p q N k : ℕ} (hE : |E| < 2) (hloss : 0 ≤ loss)
    (hst : s N ≤ t N) (ht1 : t N < 1)
    (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ ω : Ω d,
      targetWeight E D loss s t p N k ω ≤
        APrimeSmoothWeightActual.weight d E D loss s t (mesh D) 2 q N k
          (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω := by
  intro ω
  exact APrimeFirstCellCrossOrderWeight.widenedW_le_actualWeight_cross_order
    d hE hloss N p q k ω hst ht1 (APrimeGeneralMovingMesh.targetMesh_pos D N)
    hp hq

private theorem integrable_target_coordinate
    {E D loss C₀ : ℝ} {s t : ℕ → ℝ} {q N k : ℕ}
    {p : ℕ}
    (hcoord : SameActualCoordinateMoment E D loss C₀ s t q N k)
    (hw : AEStronglyMeasurable (targetWeight E D loss s t p N k) (Gauss.P d))
    (hcross : ∀ ω, targetWeight E D loss s t p N k ω ≤
      APrimeSmoothWeightActual.weight d E D loss s t (mesh D) 2 q N k
        (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω)
    (a : LoopArg (d.L N) 2) :
    Integrable
      (fun ω => targetWeight E D loss s t p N k ω *
        |endpointCoordinate E D s N k a ω| ^ (2 * q)) (Gauss.P d) := by
  obtain ⟨haem, haint, _⟩ := hcoord a
  have hpow : AEStronglyMeasurable
      (fun ω => |endpointCoordinate E D s N k a ω| ^ (2 * q)) (Gauss.P d) :=
    (continuous_pow (2 * q)).comp_aestronglyMeasurable
      (continuous_abs.comp_aestronglyMeasurable haem)
  apply haint.mono' (hw.mul hpow)
  filter_upwards [] with ω
  change |targetWeight E D loss s t p N k ω *
      |endpointCoordinate E D s N k a ω| ^ (2 * q)| ≤ _
  calc
    _ = targetWeight E D loss s t p N k ω *
        |endpointCoordinate E D s N k a ω| ^ (2 * q) :=
      abs_of_nonneg (mul_nonneg
        (APrimeWeight.widenedW_nonneg _ _ _ _ _ _ _ _ _ _ ω) (by positivity))
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcross ω) (by positivity)

/-- Main conditional bridge.  It returns exactly the `hfamily` moment used by
`APrimeAssembly.aprimeSlot_of_widened_family`, with `δweight = δ`; all
positive losses are fixed before the eventual cutoff, and the conclusion is
uniform over every active moving cell, including `k = 0`. -/
theorem moving_hfamily_of_same_actual_coordinate_input
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hc : 0 < c)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hcoord : UniformSameActualCoordinateInput E D c s t) :
    ∀ δ : ℝ, 0 < δ → δ ≤ min (1 / 10000) (c / 10000) →
      ∀ p : ℕ, ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
          k ≤ cutNetTop s t (mesh D) N →
          ∫ ω, targetWeight E D δ s t p N k ω *
            |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ))
              (targetJ E D s N (cutNetPt s (mesh D) N k) ω)| ^ (2 * p)
            ∂(Gauss.band d).P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  letI := (Gauss.band d).isProbabilityMeasure
  intro δ hδ hδsmall p
  by_cases hp : 1 ≤ p
  · obtain ⟨q, hq, C₀, hC₀, hcoordN⟩ := hcoord δ hδ hδsmall p hp
    have hq1 : 1 ≤ q := le_trans hp (le_trans (le_max_left _ _) hq)
    have hqδ : 16 / δ ≤ (q : ℝ) := by
      have hceilNat : Nat.ceil (16 / δ) ≤ q :=
        le_trans (le_max_right _ _) hq
      exact (Nat.le_ceil (16 / δ)).trans (by exact_mod_cast hceilNat)
    refine ⟨(2 * (1 + C₀)) ^ (2 * p), by positivity, ?_⟩
    filter_upwards [hcoordN, eventually_ge_atTop 81] with N hcoordN' hN81
    have hN1 : 1 ≤ N := by omega
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hmesh : 0 < mesh D N := APrimeGeneralMovingMesh.targetMesh_pos D N
    let v := cutNetPt s (mesh D) N
    let W := targetWeight E D δ s t p N
    have hfields : ∀ k,
        (∀ ω, 0 ≤ targetWeight E D δ s t p N k ω) ∧
        (∀ ω, targetWeight E D δ s t p N k ω ≤ 1) ∧
        AEStronglyMeasurable (targetWeight E D δ s t p N k) (Gauss.P d) := by
      intro k
      exact targetWeight_fields (E := E) (D := D) (δ := δ)
        (s := s) (t := t) N p k
    have hW0 : ∀ k, ∀ ω, 0 ≤ W k ω := by
      intro k ω
      exact (hfields k).1 ω
    have hW1 : ∀ k, ∀ ω, W k ω ≤ 1 := by
      intro k ω
      exact (hfields k).2.1 ω
    have hWmeas : ∀ k, AEStronglyMeasurable (W k) (Gauss.P d) := by
      intro k
      simpa [W] using (hfields k).2.2
    intro k hk
    let vk := v k
    let Jk : Ω d → ℝ := fun ω => targetJ E D s N vk ω
    let Yk : Ω d → ℝ := fun ω =>
      MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ)) (Jk ω)
    have hv : vk ∈ Icc (s N) (t N) :=
      MomentDuhamelCut.netFinset_subset_Icc (hst N) hmesh vk
        (cutNetPt_mem_netFinset hk)
    have hv1 : vk < 1 := hv.2.trans_lt (ht1 N)
    have hcross : ∀ ω, W k ω ≤
        APrimeSmoothWeightActual.weight d E D δ s t (mesh D) 2 q N k
          (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) ω := by
      simpa [W] using actualWeight_cross_order hE hδ.le (hst N) (ht1 N)
        (p := p) (q := q) hp hq1
    have hcoord : SameActualCoordinateMoment E D δ C₀ s t q N k := hcoordN' k hk
    have hcoordInt : ∀ a : LoopArg (d.L N) 2,
        Integrable (fun ω => W k ω *
          |endpointCoordinate E D s N k a ω| ^ (2 * q)) (Gauss.P d) := by
      intro a
      exact integrable_target_coordinate hcoord (hWmeas k) hcross a
    have hcoordBound : ∀ a : LoopArg (d.L N) 2,
        ∫ ω, W k ω * |endpointCoordinate E D s N k a ω| ^ (2 * q)
          ∂(Gauss.P d) ≤ (C₀ * (N : ℝ) ^ (5 * δ / 32)) ^ (2 * q) := by
      intro a
      obtain ⟨_, _, ha⟩ := hcoord a
      have hactual := (hcoord a).2.1
      have htarget := hcoordInt a
      have hmono := integral_mono htarget hactual (fun ω => by
        exact mul_le_mul_of_nonneg_right (hcross ω) (by positivity))
      exact hmono.trans ha
    have hJ0 : ∀ ω, 0 ≤ targetJ E D s N vk ω := by
      intro ω
      exact Step2Moment.jSnorm_nonneg (Gauss.sample d) (E := E) (D := D)
        (s := s) (by exact hE) ((hst N).trans_lt (ht1 N)) hv1 ω
    have hcutAEM : AEStronglyMeasurable Yk (Gauss.P d) := by
      dsimp [Yk, Jk]
      exact ((MomentDuhamelCut.continuous_cutTrunc ((N : ℝ) ^ (2 * δ))).measurable.comp
        (APrimeSlotFields.measurable_jSnorm (Gauss.sample d) E D s N vk)).aestronglyMeasurable
    have hHighAEM : AEStronglyMeasurable
        (fun ω => W k ω * |Yk ω| ^ (2 * q)) (Gauss.P d) :=
      (hWmeas k).mul ((continuous_pow (2 * q)).comp_aestronglyMeasurable
        (continuous_abs.comp_aestronglyMeasurable hcutAEM))
    have hWint : Integrable (W k) (Gauss.P d) := by
      apply (integrable_const (1 : ℝ)).mono' (hWmeas k)
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hW0 k ω)]
      exact hW1 k ω
    have hmajor : Integrable
        (fun ω => W k ω + ∑ a : LoopArg (d.L N) 2,
          W k ω * |endpointCoordinate E D s N k a ω| ^ (2 * q))
        (Gauss.P d) := by
      have hsumInt : Integrable
          (fun ω : Ω d => ∑ a : LoopArg (d.L N) 2,
            W k ω * |endpointCoordinate E D s N k a ω| ^ (2 * q)) (Gauss.P d) :=
        integrable_finsetSum Finset.univ
          (fun a (_ha : a ∈ Finset.univ) => hcoordInt a)
      exact hWint.add hsumInt
    have hHighInt : Integrable (fun ω => W k ω * |Yk ω| ^ (2 * q))
        (Gauss.P d) := by
      apply (hmajor.const_mul (2 ^ (2 * q - 1))).mono'
        hHighAEM
      filter_upwards [] with ω
      have hendpoint :=
        APrimeGeneralMovingEndpointFamily.cutTrunc_jSnorm_pow_le_endpoint_family
          (E := E) (D := D) (s := s) (theta := (N : ℝ) ^ (2 * δ))
          (p := q) N hE (hs0 N) hv.1 hv1 hq1 ω
      have hendpoint' : |Yk ω| ^ (2 * q) ≤
          2 ^ (2 * q - 1) *
            (1 + ∑ a : LoopArg (d.L N) 2,
              |endpointCoordinate E D s N k a ω| ^ (2 * q)) := by
        simpa [Yk, Jk, targetJ, endpointCoordinate, Real.norm_eq_abs] using hendpoint
      have hnonneg : 0 ≤ W k ω := hW0 k ω
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg hnonneg (by positivity))]
      calc
        W k ω * |Yk ω| ^ (2 * q) ≤
            W k ω * (2 ^ (2 * q - 1) *
              (1 + ∑ a : LoopArg (d.L N) 2,
                |endpointCoordinate E D s N k a ω| ^ (2 * q))) :=
          mul_le_mul_of_nonneg_left hendpoint' hnonneg
        _ = 2 ^ (2 * q - 1) *
            (W k ω + ∑ a : LoopArg (d.L N) 2,
              W k ω * |endpointCoordinate E D s N k a ω| ^ (2 * q)) := by
          have hsumDist : W k ω *
              (∑ a : LoopArg (d.L N) 2,
                |endpointCoordinate E D s N k a ω| ^ (2 * q)) =
                ∑ a : LoopArg (d.L N) 2,
                  W k ω * |endpointCoordinate E D s N k a ω| ^ (2 * q) := by
            simpa using (Finset.mul_sum Finset.univ
              (fun a : LoopArg (d.L N) 2 =>
                |endpointCoordinate E D s N k a ω| ^ (2 * q)) (W k ω))
          calc
            _ = 2 ^ (2 * q - 1) *
                (W k ω + W k ω *
                  (∑ a : LoopArg (d.L N) 2,
                    |endpointCoordinate E D s N k a ω| ^ (2 * q))) := by ring
            _ = _ := by rw [hsumDist]
    have hWintle : ∫ ω, W k ω ∂(Gauss.P d) ≤ 1 := by
      calc
        _ ≤ ∫ _ω : Ω d, (1 : ℝ) ∂(Gauss.P d) :=
          integral_mono hWint (integrable_const (1 : ℝ)) (fun ω => hW1 k ω)
        _ = 1 := by simp
    have hsumBound :
        ∑ a : LoopArg (d.L N) 2,
          ∫ ω, W k ω * |endpointCoordinate E D s N k a ω| ^ (2 * q)
            ∂(Gauss.P d) ≤
        (Fintype.card (LoopArg (d.L N) 2) : ℝ) *
          (C₀ * (N : ℝ) ^ (5 * δ / 32)) ^ (2 * q) := by
      calc
        _ ≤ ∑ _a : LoopArg (d.L N) 2,
            (C₀ * (N : ℝ) ^ (5 * δ / 32)) ^ (2 * q) :=
          Finset.sum_le_sum (fun a _ => hcoordBound a)
        _ = _ := by
          rw [Finset.sum_const]
          simp only [nsmul_eq_mul, Finset.card_univ]
    have hIhigh :
        ∫ ω, W k ω * |Yk ω| ^ (2 * q) ∂(Gauss.P d) ≤
          2 ^ (2 * q - 1) *
            (1 + (Fintype.card (LoopArg (d.L N) 2) : ℝ) *
              (C₀ * (N : ℝ) ^ (5 * δ / 32)) ^ (2 * q)) := by
      calc
        _ ≤ ∫ ω, 2 ^ (2 * q - 1) *
            (W k ω + ∑ a : LoopArg (d.L N) 2,
              W k ω * |endpointCoordinate E D s N k a ω| ^ (2 * q))
              ∂(Gauss.P d) :=
          integral_mono hHighInt (hmajor.const_mul (2 ^ (2 * q - 1))) (fun ω => by
            have hendpoint :=
              APrimeGeneralMovingEndpointFamily.cutTrunc_jSnorm_pow_le_endpoint_family
                (E := E) (D := D) (s := s) (theta := (N : ℝ) ^ (2 * δ))
                (p := q) N hE (hs0 N) hv.1 hv1 hq1 ω
            have hendpoint' : |Yk ω| ^ (2 * q) ≤
                2 ^ (2 * q - 1) *
                  (1 + ∑ a : LoopArg (d.L N) 2,
                    |endpointCoordinate E D s N k a ω| ^ (2 * q)) := by
              simpa [Yk, Jk, targetJ, endpointCoordinate, Real.norm_eq_abs] using hendpoint
            calc
              W k ω * |Yk ω| ^ (2 * q) ≤
                  W k ω * (2 ^ (2 * q - 1) *
                    (1 + ∑ a : LoopArg (d.L N) 2,
                      |endpointCoordinate E D s N k a ω| ^ (2 * q))) :=
                mul_le_mul_of_nonneg_left hendpoint' (hW0 k ω)
              _ = 2 ^ (2 * q - 1) * W k ω *
                    (1 + ∑ a : LoopArg (d.L N) 2,
                      |endpointCoordinate E D s N k a ω| ^ (2 * q)) := by ring
              _ = 2 ^ (2 * q - 1) *
                  (W k ω + ∑ a : LoopArg (d.L N) 2,
                    W k ω * |endpointCoordinate E D s N k a ω| ^ (2 * q)) := by
                have hsumDist : W k ω *
                    (∑ a : LoopArg (d.L N) 2,
                      |endpointCoordinate E D s N k a ω| ^ (2 * q)) =
                    ∑ a : LoopArg (d.L N) 2,
                      W k ω * |endpointCoordinate E D s N k a ω| ^ (2 * q) := by
                  simpa using (Finset.mul_sum Finset.univ
                    (fun a : LoopArg (d.L N) 2 =>
                      |endpointCoordinate E D s N k a ω| ^ (2 * q)) (W k ω))
                calc
                  _ = 2 ^ (2 * q - 1) *
                      (W k ω + W k ω *
                        (∑ a : LoopArg (d.L N) 2,
                          |endpointCoordinate E D s N k a ω| ^ (2 * q))) := by ring
                  _ = _ := by rw [hsumDist])
        _ = 2 ^ (2 * q - 1) *
            ((∫ ω, W k ω ∂(Gauss.P d)) +
              ∑ a : LoopArg (d.L N) 2,
                ∫ ω, W k ω * |endpointCoordinate E D s N k a ω| ^ (2 * q)
                  ∂(Gauss.P d)) := by
          rw [integral_const_mul,
            integral_add hWint
              (integrable_finsetSum Finset.univ
                (fun a (_ha : a ∈ Finset.univ) => hcoordInt a)),
            integral_finsetSum Finset.univ
              (fun a (_ha : a ∈ Finset.univ) => hcoordInt a)]
        _ ≤ _ := by
          gcongr <;> linarith [hWintle, hsumBound]

    let Y : Ω d → ℝ := Yk
    let Wk : Ω d → ℝ := W k
    have hW0k : ∀ ω, 0 ≤ Wk ω := hW0 k
    have hW1k : ∀ ω, Wk ω ≤ 1 := hW1 k
    have hLowInt : Integrable (fun ω => Wk ω * |Y ω| ^ (2 * p))
        (Gauss.P d) := by
      let M : Ω d → ℝ := fun ω => Wk ω + Wk ω * |Y ω| ^ (2 * q)
      have hMint : Integrable M (Gauss.P d) := hWint.add hHighInt
      apply hMint.mono' ((hWmeas k).mul ((continuous_pow (2 * p)).comp_aestronglyMeasurable
        (continuous_abs.comp_aestronglyMeasurable hcutAEM)))
      filter_upwards [] with ω
      dsimp [M, Wk, Y]
      change |W k ω * |Yk ω| ^ (2 * p)| ≤
        W k ω + W k ω * |Yk ω| ^ (2 * q)
      rw [abs_of_nonneg (mul_nonneg (hW0k ω) (by positivity))]
      by_cases hy : |Y ω| ≤ 1
      · calc
          Wk ω * |Y ω| ^ (2 * p) ≤ Wk ω * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hy) (hW0k ω)
          _ ≤ Wk ω + Wk ω * |Y ω| ^ (2 * q) := by
            nlinarith [mul_nonneg (hW0k ω) (by positivity : 0 ≤ |Y ω| ^ (2 * q))]
      · have hy1 : 1 ≤ |Y ω| := le_of_not_ge hy
        have hpow : |Y ω| ^ (2 * p) ≤ |Y ω| ^ (2 * q) := by
          exact pow_le_pow_right₀ hy1 (by omega)
        calc
          Wk ω * |Y ω| ^ (2 * p) ≤ Wk ω * |Y ω| ^ (2 * q) :=
            mul_le_mul_of_nonneg_left hpow (hW0k ω)
          _ ≤ Wk ω + Wk ω * |Y ω| ^ (2 * q) := by linarith [hW0k ω]
    have hRootLowInt :
        Integrable
          (fun ω => |Wk ω ^ (((2 * q : ℕ) : ℝ)⁻¹) * Y ω| ^ (2 * p))
          (Gauss.P d) := by
      let root : Ω d → ℝ := fun ω => Wk ω ^ (((2 * q : ℕ) : ℝ)⁻¹)
      have hexp : (0 : ℝ) ≤ (((2 * q : ℕ) : ℝ)⁻¹) := by positivity
      have hrootAEM : AEStronglyMeasurable root (Gauss.P d) :=
        (Real.continuous_rpow_const hexp).comp_aestronglyMeasurable (hWmeas k)
      have hfunAEM := (continuous_pow (2 * p)).comp_aestronglyMeasurable
        (continuous_abs.comp_aestronglyMeasurable (hrootAEM.mul hcutAEM))
      have hmajor : Integrable
          (fun ω => (1 : ℝ) + Wk ω * |Y ω| ^ (2 * q)) (Gauss.P d) :=
        (integrable_const (1 : ℝ)).add hHighInt
      apply hmajor.mono' hfunAEM
      filter_upwards [] with ω
      have hq1' : 1 ≤ q := hq1
      have hpowEq := APrimeInit.fractional_pow_high (hW0k ω) hq1' (z := Y ω)
      have hx0 : 0 ≤ |root ω * Y ω| := abs_nonneg _
      have hxp : |root ω * Y ω| ^ (2 * p) ≤
          1 + |root ω * Y ω| ^ (2 * q) := by
        by_cases hz : |root ω * Y ω| ≤ 1
        · calc
            _ ≤ 1 := pow_le_one₀ hx0 hz
            _ ≤ 1 + |root ω * Y ω| ^ (2 * q) := by
              have hpow0 : 0 ≤ |root ω * Y ω| ^ (2 * q) := by positivity
              linarith
        · have hz1 : 1 ≤ |root ω * Y ω| := le_of_not_ge hz
          have hpow : |root ω * Y ω| ^ (2 * p) ≤
              |root ω * Y ω| ^ (2 * q) := pow_le_pow_right₀ hz1 (by omega)
          exact hpow.trans (by linarith)
      change ‖|root ω * Y ω| ^ (2 * p)‖ ≤
        1 + Wk ω * |Y ω| ^ (2 * q)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hpowEq] at hxp
      exact hxp
    have hLyap := APrimeInit.momNormW_le_momNormW_of_exponent_le
      hp (le_trans (le_max_left _ _) hq) hW0k hW1k hLowInt hHighInt hRootLowInt
    have hI0 : 0 ≤ ∫ ω, Wk ω * |Y ω| ^ (2 * q) ∂(Gauss.P d) :=
      integral_nonneg fun ω => mul_nonneg (hW0k ω) (by positivity)
    have hC1 : 0 < 2 * (1 + C₀) := by positivity
    have hNpow : 0 ≤ 5 * δ / 16 + 2 / (q : ℝ) := by positivity
    have hcardNat : Fintype.card (LoopArg (d.L N) 2) ≤ N ^ 2 :=
      APrimeFirstCellFamilyHighMoment.family_card_le (by omega)
    have hcardReal : (Fintype.card (LoopArg (d.L N) 2) : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast hcardNat
    have hqBound : 2 ≤ δ * (q : ℝ) / 8 := by
      have hmul := mul_le_mul_of_nonneg_left hqδ (by positivity : (0 : ℝ) ≤ δ)
      have hdiv : δ * (16 / δ) = 16 := by field_simp [ne_of_gt hδ]
      nlinarith
    have hmomentUpper :
        ∫ ω, Wk ω * |Y ω| ^ (2 * q) ∂(Gauss.P d) ≤
          (2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32)) ^ (2 * q) := by
      have hcoordPow :
          (C₀ * (N : ℝ) ^ (5 * δ / 32)) ^ (2 * q) =
            C₀ ^ (2 * q) * (N : ℝ) ^ (5 * δ / 32 * (2 * q : ℝ)) := by
        rw [mul_pow, rpow_nat_power (Nat.cast_nonneg N)
          (α := 5 * δ / 32) (n := 2 * q)]
        congr 1
        push_cast
        ring
      have hNbase : 1 ≤ (N : ℝ) := by exact_mod_cast hN1
      have hNexp : 0 ≤ 5 * δ / 16 := by positivity
      have hscale : (N : ℝ) ^ 2 * (N : ℝ) ^ (5 * δ / 32 * (2 * q : ℝ)) ≤
          (N : ℝ) ^ (7 * δ / 32 * (2 * q : ℝ)) := by
        have hexp : 2 + 5 * δ / 32 * (2 * q : ℝ) ≤
            7 * δ / 32 * (2 * q : ℝ) := by
          nlinarith [hqBound]
        calc
          (N : ℝ) ^ 2 * (N : ℝ) ^ (5 * δ / 32 * (2 * q : ℝ)) =
              (N : ℝ) ^ (2 + 5 * δ / 32 * (2 * q : ℝ)) := by
            rw [show (N : ℝ) ^ 2 = (N : ℝ) ^ (2 : ℝ) by
              exact (Real.rpow_natCast (N : ℝ) 2).symm,
              ← Real.rpow_add hNr]
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNbase hexp
      have hsumPow : 1 + C₀ ^ (2 * q) ≤ 2 * (1 + C₀) ^ (2 * q) := by
        have hpow1 : 1 ≤ (1 + C₀) ^ (2 * q) :=
          one_le_pow₀ (by linarith)
        have hpow2 : C₀ ^ (2 * q) ≤ (1 + C₀) ^ (2 * q) := by
          gcongr
          linarith
        linarith
      have hboundBase :
          2 ^ (2 * q - 1) *
            (1 + (Fintype.card (LoopArg (d.L N) 2) : ℝ) *
              (C₀ * (N : ℝ) ^ (5 * δ / 32)) ^ (2 * q)) ≤
          (2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32)) ^ (2 * q) := by
        rw [hcoordPow]
        have hNpower : 1 ≤ (N : ℝ) ^ (5 * δ / 32 * (2 * q : ℝ)) :=
          Real.one_le_rpow hNbase (by positivity)
        have hcardBound :
            (Fintype.card (LoopArg (d.L N) 2) : ℝ) *
                C₀ ^ (2 * q) * (N : ℝ) ^ (5 * δ / 32 * (2 * q : ℝ)) ≤
              C₀ ^ (2 * q) * (N : ℝ) ^ (7 * δ / 32 * (2 * q : ℝ)) := by
          calc
            _ ≤ (N : ℝ) ^ 2 * C₀ ^ (2 * q) *
                (N : ℝ) ^ (5 * δ / 32 * (2 * q : ℝ)) := by
                  gcongr
            _ = C₀ ^ (2 * q) *
                ((N : ℝ) ^ 2 * (N : ℝ) ^ (5 * δ / 32 * (2 * q : ℝ))) := by ring
            _ ≤ C₀ ^ (2 * q) *
                (N : ℝ) ^ (7 * δ / 32 * (2 * q : ℝ)) := by
                  exact mul_le_mul_of_nonneg_left hscale (by positivity)
        have hNbase' : 1 ≤ (N : ℝ) ^ (7 * δ / 32 * (2 * q : ℝ)) :=
          Real.one_le_rpow hNbase (by positivity)
        have hbracket :
            1 + (Fintype.card (LoopArg (d.L N) 2) : ℝ) *
              C₀ ^ (2 * q) * (N : ℝ) ^ (5 * δ / 32 * (2 * q : ℝ)) ≤
            2 * (1 + C₀) ^ (2 * q) *
              (N : ℝ) ^ (7 * δ / 32 * (2 * q : ℝ)) := by
          have hCpow0 : 0 ≤ C₀ ^ (2 * q) := by positivity
          calc
            _ ≤ (1 + C₀ ^ (2 * q)) *
                (N : ℝ) ^ (7 * δ / 32 * (2 * q : ℝ)) := by
              nlinarith [mul_nonneg hCpow0 (sub_nonneg.mpr hNbase')]
            _ ≤ _ :=
              mul_le_mul_of_nonneg_right hsumPow
                (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        have hbracket' :
            1 + (Fintype.card (LoopArg (d.L N) 2) : ℝ) *
                ((C₀ : ℝ) ^ (2 * q) * (N : ℝ) ^ (5 * δ / 32 * (2 * q : ℝ))) ≤
              2 * (1 + C₀) ^ (2 * q) * (N : ℝ) ^ (7 * δ / 32 * (2 * q : ℝ)) := by
          convert hbracket using 1 <;> ring
        have hpowN :
            (N : ℝ) ^ (7 * δ / 32 * (2 * q : ℝ)) =
              ((N : ℝ) ^ (7 * δ / 32)) ^ (2 * q) := by
          have hexp : 7 * δ / 32 * (2 * q : ℝ) =
              7 * δ / 32 * ((2 * q : ℕ) : ℝ) := by push_cast; ring
          rw [hexp]
          exact (rpow_nat_power (Nat.cast_nonneg N) (α := 7 * δ / 32)
            (n := 2 * q)).symm
        have hconst : (2 : ℝ) ^ (2 * q - 1) * 2 ≤ (2 : ℝ) ^ (2 * q) := by
          apply le_of_eq
          calc
            (2 : ℝ) ^ (2 * q - 1) * 2 =
                (2 : ℝ) ^ ((2 * q - 1) + 1) := by
              simpa [Nat.succ_eq_add_one] using
                (pow_succ (2 : ℝ) (2 * q - 1)).symm
            _ = (2 : ℝ) ^ (2 * q) := by rw [Nat.sub_add_cancel (by omega)]
        calc
          _ ≤ 2 ^ (2 * q - 1) *
              (2 * (1 + C₀) ^ (2 * q) *
                (N : ℝ) ^ (7 * δ / 32 * (2 * q : ℝ))) :=
            by
              simpa [mul_assoc] using
                (mul_le_mul_of_nonneg_left hbracket' (by positivity :
                  0 ≤ (2 : ℝ) ^ (2 * q - 1)))
          _ = 2 ^ (2 * q - 1) * 2 *
              ((1 + C₀) ^ (2 * q) *
                ((N : ℝ) ^ (7 * δ / 32)) ^ (2 * q)) := by rw [hpowN]; ring
          _ ≤ (2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32)) ^ (2 * q) := by
            have hpowRhs :
                (2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32)) ^ (2 * q) =
                  2 ^ (2 * q) * (1 + C₀) ^ (2 * q) *
                    ((N : ℝ) ^ (7 * δ / 32)) ^ (2 * q) := by
              rw [mul_pow, mul_pow]
            rw [hpowRhs]
            calc
              _ = ((2 : ℝ) ^ (2 * q - 1) * 2) *
                    ((1 + C₀) ^ (2 * q) *
                      ((N : ℝ) ^ (7 * δ / 32)) ^ (2 * q)) := by ring
              _ ≤ (2 : ℝ) ^ (2 * q) *
                    ((1 + C₀) ^ (2 * q) *
                      ((N : ℝ) ^ (7 * δ / 32)) ^ (2 * q)) :=
                mul_le_mul_of_nonneg_right hconst (by positivity)
              _ = _ := by ring
      exact hIhigh.trans hboundBase
    have hnormq :
        MomentDuhamel.momNormW (Gauss.P d) Wk q Y ≤
          2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32) := by
      have hexp : (1 : ℝ) / (2 * (q : ℝ)) = (((2 * q : ℕ) : ℝ))⁻¹ := by
        push_cast
        field_simp
      have hroot :
          ((2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32)) ^ (2 * q)) ^
            (((2 * q : ℕ) : ℝ))⁻¹ =
            2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32) :=
        Real.pow_rpow_inv_natCast (by positivity) (by omega)
      change (∫ ω, Wk ω * |Y ω| ^ (2 * q) ∂(Gauss.P d)) ^
        ((1 : ℝ) / (2 * (q : ℝ))) ≤ _
      calc
        _ ≤ ((2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32)) ^ (2 * q)) ^
            ((1 : ℝ) / (2 * (q : ℝ))) :=
          Real.rpow_le_rpow hI0 hmomentUpper (by positivity)
        _ = 2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32) := by
          rw [hexp]
          exact hroot
    have hnormp :
        MomentDuhamel.momNormW (Gauss.P d) Wk p Y ≤
          2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32) := hLyap.trans hnormq
    have hpq : p ≤ q := le_trans (le_max_left _ _) hq
    have hnormp' :
        MomentDuhamel.momNormW (Gauss.P d) Wk p Yk ≤
          2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32) := by
      simpa [Y] using hnormp
    have hfamilyInt := APrimeOneStep.integral_le_of_momNormW_le
      (P := Gauss.P d) (W := Wk) (Y := Yk) (fun ω => hW0 k ω) hp hnormp'
    have hExponent : 7 * δ / 16 * (p : ℝ) ≤ δ / 2 * (p : ℝ) := by
      have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      nlinarith [hδ]
    have hNpowle : (N : ℝ) ^ (7 * δ / 16 * (p : ℝ)) ≤
        (N : ℝ) ^ (δ / 2 * (p : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) hExponent
    have hfinalArithmetic :
        (2 * (1 + C₀) * (N : ℝ) ^ (7 * δ / 32)) ^ (2 * p) ≤
          (2 * (1 + C₀)) ^ (2 * p) * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
      rw [mul_pow, rpow_nat_power hNr.le (α := 7 * δ / 32) (n := 2 * p)]
      have hexp : (7 * δ / 32) * ((2 * p : ℕ) : ℝ) =
          7 * δ / 16 * (p : ℝ) := by
        push_cast
        ring
      rw [hexp]
      exact mul_le_mul_of_nonneg_left hNpowle (by positivity)
    exact hfamilyInt.trans hfinalArithmetic
  · have hp0 : p = 0 := by omega
    subst p
    refine ⟨1, by norm_num, ?_⟩
    filter_upwards [] with N
    intro k hk
    have hW := targetWeight_fields (E := E) (D := D) (δ := δ)
      (s := s) (t := t) N 0 k
    have hI :
        ∫ ω, targetWeight E D δ s t 0 N k ω *
          |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ))
            (targetJ E D s N (cutNetPt s (mesh D) N k) ω)| ^ (2 * 0)
          ∂(Gauss.band d).P ≤ 1 := by
      calc
        _ ≤ ∫ _ω : Ω d, (1 : ℝ) ∂(Gauss.band d).P := by
          exact integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun ω => by simpa using hW.1 ω)
            (integrable_const (1 : ℝ))
            (Filter.Eventually.of_forall fun ω => by simpa using hW.2.1 ω)
        _ = 1 := by simp
    simpa [Real.rpow_zero] using hI

/-! ## Nondegenerate common-support witness -/

/-- The prescribed losses, a positive-length `E=0`, `D=60` window, and a
same-sample common-event resident with widened weight one and positive actual
weight are jointly satisfiable.  This witness concerns the event and weight
geometry; the conditional coordinate estimate remains a separate input. -/
theorem nondegenerate_loss_window_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg (Gauss.band d) 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∀ loss : ℝ, 0 < loss → loss ≤ min (1 / 10000) (c / 10000) →
        ∀ᶠ N : ℕ in atTop,
          s N < t N ∧ ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t (sourceLoss loss) (sourceLoss loss) (sourceLoss loss) N ∧
            1 ≤ cutNetTop s t (mesh 60) N ∧
            targetWeight 0 60 loss s t 1 N 1 ω = 1 ∧
            0 < APrimeSmoothWeightActual.weight d 0 60 loss s t (mesh 60)
              2 1 N 1 (APrimeSmoothWeightActual.canonicalM d s t (mesh 60) N) ω := by
  obtain ⟨τ, hτ, c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, hcommon⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, ?_⟩
  intro loss hloss hsmall
  have hsch := corrected_loss_schedule hc hloss hsmall
  have hsrc : 0 < sourceLoss loss := hsch.1
  have hcommon' := hcommon (sourceLoss loss) (sourceLoss loss) (sourceLoss loss) loss
    hsrc hsrc hsrc hloss
  filter_upwards [hcommon'] with N hN
  obtain ⟨hwindow, ω, hω, hk, hplateau⟩ := hN
  have hplateau1 : targetWeight 0 60 loss s t 1 N 1 ω = 1 := by
    simpa [targetWeight, targetJ, APrimeGeneralMovingDetFields.J] using hplateau 1
  have hcross := actualWeight_cross_order (E := 0) (D := 60) (loss := loss)
    (s := s) (t := t) (p := 1) (q := 1) (N := N) (k := 1)
    (by norm_num) hloss.le (hst N) (ht1 N) (by norm_num) (by norm_num) ω
  refine ⟨hwindow, ω, hω, hk, hplateau1, ?_⟩
  rw [hplateau1] at hcross
  exact lt_of_lt_of_le (by norm_num) hcross

#print axioms corrected_loss_schedule
#print axioms moving_hfamily_of_same_actual_coordinate_input
#print axioms nondegenerate_loss_window_witness

end

end RBM.APrimeFreeLossFamilyBridge
