/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDetFields
import RBM1D.Gauss.APrimeWeight
import RBM1D.Gauss.APrimeFirstCellCommon

/-!
# T484: support propagation on general moving windows

Positive support of the actual widened prefix weight controls the normalized
loop on the whole interval already traversed by an active positive prefix.
-/

namespace RBM.APrimeGeneralMovingPrefixSupport

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- Positive support of an active widened prefix propagates the discrete
cutoff bound to every time up to its endpoint.  The index `k = 0` is excluded
because its prefix is empty. -/
theorem eventually_running_cap {E D c δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) (hδ : 0 < δ) (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      1 ≤ k → k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
        0 < APrimeWeight.widenedW
          (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
          (APrimeGeneralMovingDetFields.J E D s) s t
          (APrimeGeneralMovingMesh.targetMesh D) δ p N k ω →
        ∀ u ∈ Icc (s N)
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
          APrimeGeneralMovingDetFields.J E D s N u ω ≤
            (4 * Real.exp 1 + 2) * (N : ℝ) ^ (2 * δ) := by
  let H := APrimeGeneralMovingDetFields.detFieldPackage
    hE hD hs0 hst ht1 hc hreg
  filter_upwards [H.modulus, H.mesh_fine, eventually_ge_atTop 1]
    with N hmod hfine hN
  intro k hk hkTop ω hω hwide u hu
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let J := APrimeGeneralMovingDetFields.J E D s
  let r := APrimeWeight.canonicalR s t mesh
  let θ := 2 * Real.exp 1 * APrimePrior.priorLevel δ (fun _ => 1) N
  have hactive : k ≤ cutNetTop s t mesh N ∧ 1 ≤ N := ⟨hkTop, hN⟩
  have hpne : 2 * p ≠ 0 := by omega
  have hprefix : APrimeWeight.prefixSoftW (r N) J s mesh N k θ ω ≠ 0 := by
    intro hz
    have hwide' := hwide
    rw [APrimeWeight.widenedW, if_pos hactive] at hwide'
    change 0 < (APrimeWeight.prefixSoftW (r N) J s mesh N k θ ω) ^ (2 * p) at hwide'
    rw [hz, zero_pow hpne] at hwide'
    exact (lt_irrefl 0) hwide'
  have hθ : 0 < θ := by
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
      (APrimePrior.priorLevel_pos hN (by norm_num))
  have hr : 1 ≤ r N := by simp [r, APrimeWeight.canonicalR]
  have hbase := APrimeWeight.le_of_prefixSoftW_ne_zero_of_modulus
    (r := r N) hr (J := J) (s := s) (t := t) (mesh := mesh)
    (N := N) (k := k)
    (Kmod := APrimeGeneralMovingFieldPackage.Kmod D)
    (γ := APrimeGeneralMovingFieldPackage.gamma) (θ := θ) (Θ := 1)
    H.gamma_pos hθ (H.window N) (H.mesh_pos N) hk hkTop hprefix
    (hmod ω hω) hfine u hu
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : 1 ≤ (N : ℝ) ^ (2 * δ) :=
    Real.one_le_rpow hNreal (by linarith)
  calc
    J N u ω ≤ 2 * θ + 1 := hbase
    _ = 4 * Real.exp 1 * (N : ℝ) ^ (2 * δ) + 1 := by
      simp [θ, APrimePrior.priorLevel]
      ring
    _ ≤ (4 * Real.exp 1 + 2) * (N : ℝ) ^ (2 * δ) := by
      have hexp : 0 < Real.exp 1 := Real.exp_pos 1
      nlinarith

private theorem eventually_firstCellT_half {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, Gauss.firstCellT τ' N = 1 / 2 := by
  have hWt : Tendsto (fun N : ℕ => ((d.W N : ℝ)) ^ (-τ'))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hτ').comp (Step2.tendsto_W B)
  filter_upwards [hWt.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with N hW
  change gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1 = 1 / 2
  apply gridT_of_le
  rw [gridS]
  norm_num
  change (Gauss.Dims.growW N : ℝ) ^ (-τ') < 1 / 2 at hW
  linarith

/-- The active-support hypotheses are jointly inhabited on an admissible
positive-length Gaussian first cell.  The sample is the zero sample in the
same concrete norm event, the active prefix is `k = 1`, and every positive
moment order gives widened weight exactly one. -/
theorem positive_length_same_good_support_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧
      let s := Gauss.firstCellS τ'
      let t := Gauss.firstCellT τ'
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      ∀ᶠ N : ℕ in atTop,
        s N < t N ∧
        ∃ ω ∈ APrimeGeneralMovingGoodMesh.good N,
          1 ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N ∧
          ∀ p : ℕ, 1 ≤ p →
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (APrimeGeneralMovingDetFields.J 0 60 s) s t
              (APrimeGeneralMovingMesh.targetMesh 60) 1 p N 1 ω = 1 := by
  obtain ⟨τ', hτ', c, hc, _n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain B (κ := 1) (τ := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)
  have hcap : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-1 + (1 : ℝ) / 2) ≤ 1 - (1 / 2 : ℝ) := by
    filter_upwards [eventually_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_ge_atTop 1] with N hNpow hN
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hEq : (N : ℝ) ^ (-1 + (1 : ℝ) / 2) =
        ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [show -1 + (1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
        Real.rpow_neg hN0]
    rw [hEq]
    have hInv : ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ (2 : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hNpow)
    norm_num at hInv ⊢
    exact hInv
  obtain ⟨_, hsteps⟩ := hgrid 0 (by norm_num) (fun _ => (1 / 2 : ℝ))
    (fun _ => by norm_num) hcap
  obtain ⟨hs0, hst, ht1, hreg⟩ := hsteps 0
  let s := Gauss.firstCellS τ'
  let t := Gauss.firstCellT τ'
  change (∀ N, 0 ≤ s N) at hs0
  change (∀ N, s N ≤ t N) at hst
  change (∀ N, t N < 1) at ht1
  change Cond272Reg B 0 s t c at hreg
  refine ⟨τ', hτ', c, hc, hs0, hst, ht1, hreg, ?_⟩
  filter_upwards [eventually_firstCellT_half hτ', eventually_ge_atTop 2]
    with N ht hN
  have hs : s N = 0 := by
    change gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0 = 0
    exact gridT_zero (by norm_num)
  have hactive : 1 ≤ cutNetTop s t
      (APrimeGeneralMovingMesh.targetMesh 60) N := by
    have ht' : t N = 1 / 2 := ht
    unfold cutNetTop APrimeGeneralMovingMesh.targetMesh
    rw [hs, ht', APrimeGeneralMovingMesh.polynomialMesh_eq_of_pos (by omega)]
    apply Nat.le_floor
    norm_num
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hNone : (1 : ℝ) ≤ N := by linarith
    have hpow : (2 : ℝ) ≤ (N : ℝ) ^
        (2 * (2 * (60 : ℝ) + 7) + 4) := by
      calc
        (2 : ℝ) ≤ N := hNr
        _ = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ (2 * (2 * (60 : ℝ) + 7) + 4) :=
          Real.rpow_le_rpow_of_exponent_le hNone (by norm_num)
    norm_num at hpow
    calc
      (1 : ℝ) = (1 / 2) * 2 := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hsfun : s = fun _ => (0 : ℝ) := by
    funext M
    change gridT ((B.W M : ℝ)) τ' (1 / 2 : ℝ) 0 = 0
    exact gridT_zero (by norm_num)
  let mesh := APrimeGeneralMovingMesh.targetMesh 60
  let J := APrimeGeneralMovingDetFields.J 0 60 s
  have hpref : (0 : Ω d) ∈
      prefNet J s mesh (fun M _ => (M : ℝ) ^ (2 * (1 : ℝ)) * 1) N 1 := by
    intro j hj
    have hj0 : j = 0 := by simpa only [Finset.mem_range, Nat.lt_one_iff] using hj
    subst j
    have hJzero : J N (cutNetPt s mesh N 0) (0 : Ω d) = 1 := by
      simp only [cutNetPt_zero]
      rw [hs]
      dsimp [J, APrimeGeneralMovingDetFields.J]
      rw [hsfun]
      exact APrimeFirstCellCommon.J_zero N (0 : Ω Dims.exampleGrow)
    rw [hJzero]
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hpow : 1 ≤ (N : ℝ) ^ (2 * (1 : ℝ)) :=
      Real.one_le_rpow hNreal (by norm_num)
    simpa using hpow
  have hpieceLower : 1 ≤ APrimeWeight.piecewiseW
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh 1 N 1 (0 : Ω d) :=
    APrimeWeight.piecewiseW_dom_canonical
      (APrimeGeneralMovingDetFields.J_nonneg 0 60 s) 1 N 1 (0 : Ω d) hpref
  have hpieceUpper := APrimeWeight.piecewiseW_le_one
    (APrimeWeight.canonicalR s t mesh) 1 J s t mesh 1 N 1 (0 : Ω d)
  have hpiece : APrimeWeight.piecewiseW
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh 1 N 1 (0 : Ω d) = 1 :=
    le_antisymm hpieceUpper hpieceLower
  refine ⟨?_, 0, APrimeGeneralMovingGoodMesh.zero_mem_good N, hactive, ?_⟩
  · change s N < t N
    have ht' : t N = 1 / 2 := ht
    rw [hs, ht']
    norm_num
  · intro p hp
    have hlower := APrimeWeight.piecewiseW_le_widenedW
      (r := APrimeWeight.canonicalR s t mesh) (N₀ := 1)
      (J := J) (s := s) (t := t) (mesh := mesh)
      (by norm_num) 1 p N 1 (0 : Ω d)
    have hupper := APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh 1 p N 1 (0 : Ω d)
    rw [hpiece] at hlower
    exact le_antisymm hupper hlower

#print axioms eventually_running_cap
#print axioms positive_length_same_good_support_witness

end
end RBM.APrimeGeneralMovingPrefixSupport
