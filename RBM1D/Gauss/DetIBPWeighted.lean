/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CondStableFlow
import RBM1D.Gauss.FirstCellStep1LocalLaw
import RBM1D.Gauss.LDENetClose

/-!
# Deterministic-scale weighted Gaussian IBP remainder

The diagonal IBP remainder is weighted by `Sblk i i`.  Its stochastic size one is
therefore sufficient when `W⁻¹ ≤ Ψ²`; no fluctuation averaging is used here.
-/

namespace RBM.Gauss

open Filter MeasureTheory

variable {d : Dims} {N : ℕ} {E u : ℝ}

/-- The actual conditional IBP residual, with the diagonal coefficient kept. -/
theorem norm_condExpDiag_sub_le_two_phi (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (i : d.Idx N) (ω : Ω d) {A Φ : ℝ}
    (hA0 : 0 ≤ A) (hΦ0 : 0 ≤ Φ)
    (hWΦ : ((d.W N : ℝ))⁻¹ ≤ Φ)
    (hoff : ∀ k : d.Idx N, k ≠ i → ‖ibpRem d N E u (i, k) ω‖ ≤ A * Φ)
    (hdiag : ‖ibpRem d N E u (i, i) ω‖ ≤ A) :
    ‖condExpDiag d N u (zt E u) (mE E) i ω
        - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N u ω) (zt E u) k k - mE E)‖ ≤ 2 * A * Φ := by
  have hS : Sblk (d.L N) (d.W N) i i ≤ ((d.W N : ℝ))⁻¹ := by
    have h := Sblk_le (L := d.L N) (W := d.W N) i i
    simpa [sbSupport] using h
  calc
    _ ≤ A * Φ + Sblk (d.L N) (d.W N) i i * A :=
      norm_condExpDiag_sub_le_offdiag (gaussIBP d) hE hu0 hu1 i ω
        (mul_nonneg hA0 hΦ0) hoff hdiag
    _ ≤ A * Φ + Φ * A :=
      add_le_add_right (mul_le_mul_of_nonneg_right (hS.trans hWΦ) hA0) _
    _ = 2 * A * Φ := by ring

#print axioms norm_condExpDiag_sub_le_two_phi

variable {s t Ψ : ℕ → ℝ}

/-- The weighted residual follows from the two-regime IBP remainder on the actual flow. -/
theorem unifDomIcc_condExpDiag_weighted_of_rem (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hWΨ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ Ψ N * Ψ N)
    (hrem : UnifDomIcc (P d) s t
      (fun N u (q : d.Idx N × d.Idx N) ω => ‖ibpRem d N E u q ω‖)
      (fun N _ (q : d.Idx N × d.Idx N) _ =>
        if q.1 = q.2 then (1 : ℝ) else Ψ N * Ψ N)) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖condExpDiag d N u (zt E u) (mE E) i ω
          - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
            * (green (Hflow d N u ω) (zt E u) k k - mE E)‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  classical
  intro τ hτ D hD
  have hτ2 : (0 : ℝ) < τ / 2 := by linarith
  filter_upwards [hrem (τ / 2) hτ2 (D + 2) (by linarith),
    card_Idx_le d, eventually_ge_atTop 1, eventually_le_rpow 2 hτ2] with
    N hremN hcardN hN1 h2N u hu i
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hu0 : 0 ≤ u := (hs0 N).trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt (ht1 N)
  set a : ℝ := (N : ℝ) ^ (τ / 2) with hadef
  have ha0 : 0 ≤ a := (Real.rpow_pos_of_pos hNpos _).le
  have ha2 : a * a = (N : ℝ) ^ τ := by
    rw [hadef, ← Real.rpow_add hNpos]
    congr 1
    ring
  set T : d.Idx N → Set (Ω d) := fun k =>
    {ω | a * (if i = k then (1 : ℝ) else Ψ N * Ψ N) <
      ‖ibpRem d N E u (i, k) ω‖} with hTdef
  have hTk : ∀ k : d.Idx N, (P d) (T k) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) := by
    intro k
    exact hremN u hu (i, k)
  have hunion : (P d) (⋃ k, T k) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
    have hpow : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hNpos.le _
    have hcard' : (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) := by
      rw [Real.rpow_one] at hcardN
      exact hcardN
    calc
      (P d) (⋃ k, T k) ≤ ∑ k : d.Idx N, (P d) (T k) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : d.Idx N, ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) :=
          Finset.sum_le_sum fun k _ => hTk k
      _ = ENNReal.ofReal ((Fintype.card (d.Idx N) : ℝ) *
          (N : ℝ) ^ (-(D + 2))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (Fintype.card (d.Idx N) : ℝ) * (N : ℝ) ^ (-(D + 2)) ≤
              (N : ℝ) * (N : ℝ) ^ (-(D + 2)) :=
            mul_le_mul_of_nonneg_right hcard' hpow
          have h2 : (N : ℝ) * (N : ℝ) ^ (-(D + 2)) =
              (N : ℝ) ^ (-(D + 1)) := by
            have hsplit := Real.rpow_add hNpos 1 (-(D + 2))
            rw [Real.rpow_one] at hsplit
            rw [← hsplit]
            congr 1
            ring
          have h3 : (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) :=
            Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
          linarith
  have hsub : {ω | (N : ℝ) ^ τ * (Ψ N * Ψ N) <
      ‖condExpDiag d N u (zt E u) (mE E) i ω
        - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N u ω) (zt E u) k k - mE E)‖} ⊆ ⋃ k, T k := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists] at hcon
    have hTle : ∀ k : d.Idx N, ‖ibpRem d N E u (i, k) ω‖ ≤
        a * (if i = k then (1 : ℝ) else Ψ N * Ψ N) := by
      intro k
      have := hcon k
      rw [hTdef] at this
      simpa only [Set.mem_ofPred_eq, not_lt] using this
    have hΦ0 : 0 ≤ Ψ N * Ψ N := mul_nonneg (hΨ0 N) (hΨ0 N)
    have hbound := norm_condExpDiag_sub_le_two_phi hE hu0 hu1 i ω ha0 hΦ0
      (hWΨ N) (fun k hk => by simpa [Ne.symm hk] using hTle k)
      (by simpa using hTle i)
    have h2a : 2 * a ≤ a * a := by
      have ha : 2 ≤ a := h2N
      nlinarith
    have hfin : ‖condExpDiag d N u (zt E u) (mE E) i ω
        - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N u ω) (zt E u) k k - mE E)‖ ≤
        (N : ℝ) ^ τ * (Ψ N * Ψ N) := by
      calc
        _ ≤ 2 * a * (Ψ N * Ψ N) := hbound
        _ ≤ (a * a) * (Ψ N * Ψ N) :=
          mul_le_mul_of_nonneg_right h2a hΦ0
        _ = _ := by rw [ha2]
    exact (not_le.2 hω) hfin
  exact (measure_mono hsub).trans hunion

#print axioms unifDomIcc_condExpDiag_weighted_of_rem

variable {δ : ℕ → ℝ} {Kenv B : ℝ}

/-- The actual Gaussian-flow residual is dominated by the deterministic scale `Ψ²`. -/
theorem unifDomIcc_condExpDiag_weighted (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop,
      ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hWΨ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ Ψ N * Ψ N)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hll : LocalLawUnifIcc d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖condExpDiag d N u (zt E u) (mE E) i ω
          - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
            * (green (Hflow d N u ω) (zt E u) k k - mE E)‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  exact unifDomIcc_condExpDiag_weighted_of_rem hE hs0 ht1 hΨ0 hWΨ
    (unifDomIcc_ibpRem d hE ht1 hΨ0 hKenv hB hEnv hΨlow hΨ1 hδ1 hΩ hll)

#print axioms unifDomIcc_condExpDiag_weighted

/-- The first-cell local-law scale enlarged exactly enough to dominate `W⁻¹` after squaring. -/
noncomputable def firstCellPsiWeighted (N : ℕ) : ℝ := 2 * firstCellPsi N

/-- The weighted IBP residual and an inhabited positive-length first-cell event coexist
for the growing Gaussian band model. -/
theorem firstCell_condExpDiag_weighted_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
        (fun N u (i : Dims.exampleGrow.Idx N) ω =>
          ‖condExpDiag Dims.exampleGrow N u (zt 0 u) (mE 0) i ω
            - (u : ℂ) * mE 0 ^ 2 * ∑ k,
              (Sblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) i k : ℂ)
                * (green (Hflow Dims.exampleGrow N u ω) (zt 0 u) k k - mE 0)‖)
        (fun N _ _ _ => firstCellPsiWeighted N * firstCellPsiWeighted N) ∧
      ∀ᶠ N : ℕ in atTop,
        firstCellS τ' N < firstCellT τ' N ∧
          (flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
            firstCellDelta N).Nonempty := by
  obtain ⟨τ', hτ', hll, hnonempty⟩ := firstCell_step1_localLaw_witness
  let d := Dims.exampleGrow
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := by
    intro N
    change 0 ≤ gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have ht1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := by
    intro N
    exact gridT_mono (by exact_mod_cast (band d).one_le_W N) hτ'.le (1 / 2 : ℝ)
      (Nat.zero_le 1)
  obtain ⟨hΨpos, h2Ψ1, hWinv, _, hΨlow, hΨlowLL, _,
    hmargin, hδ1, _, _, _, _, _, _⟩ := first_cell_joint_grid_scales hτ'
  obtain ⟨hKbig, _, _, hEnv⟩ := first_cell_polynomial_regime d τ'
  have hΩ : HighProb (P d)
      (goodSetFlow d 0 (firstCellS τ') (firstCellT τ') firstCellDelta) :=
    highProb_goodSetFlow_of_localLaw d (by norm_num : (0 : ℝ) < 1 / 16)
      (by norm_num) hs0 ht1 hst (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (0 : ℝ) ≤ 2) hKbig (fun N => (hΨpos N).le)
      hΨlowLL hll hmargin
  have hΨ0 : ∀ N, 0 ≤ firstCellPsiWeighted N := by
    intro N
    exact mul_nonneg (by norm_num) (hΨpos N).le
  have hΨ1 : ∀ᶠ N : ℕ in atTop,
      firstCellPsiWeighted N * firstCellPsiWeighted N ≤ 1 := by
    filter_upwards [eventually_ge_atTop 1] with N _
    have hp : 0 ≤ firstCellPsi N := (hΨpos N).le
    have hle := h2Ψ1 N
    change 2 * firstCellPsi N ≤ 1 at hle
    dsimp [firstCellPsiWeighted]
    nlinarith [mul_nonneg (sub_nonneg.mpr hle)
      (by linarith : 0 ≤ 1 + 2 * firstCellPsi N)]
  have hΨlow' : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(2 : ℝ)) ≤
        firstCellPsiWeighted N * firstCellPsiWeighted N := by
    filter_upwards [hΨlow] with N hN
    change (N : ℝ) ^ (-(2 : ℝ)) ≤ firstCellPsi N * firstCellPsi N at hN
    have hp : 0 ≤ firstCellPsi N := (hΨpos N).le
    dsimp [firstCellPsiWeighted]
    nlinarith [sq_nonneg (firstCellPsi N)]
  have hWΨ : ∀ N, ((d.W N : ℝ))⁻¹ ≤
      firstCellPsiWeighted N * firstCellPsiWeighted N := by
    intro N
    have h := hWinv N
    change ((d.W N : ℝ))⁻¹ ≤ 4 * firstCellPsi N ^ 2 at h
    dsimp [firstCellPsiWeighted]
    nlinarith
  have hll' : LocalLawUnifIcc d 0 (firstCellS τ') (firstCellT τ')
      firstCellPsiWeighted := by
    apply hll.mono_control
    intro N u ij ω
    dsimp [firstCellPsiWeighted]
    have hp : 0 ≤ firstCellPsi N := (hΨpos N).le
    linarith
  refine ⟨τ', hτ', ?_, hnonempty⟩
  exact unifDomIcc_condExpDiag_weighted (d := d) (E := 0)
    (s := firstCellS τ') (t := firstCellT τ') (Ψ := firstCellPsiWeighted)
    (δ := firstCellDelta) (Kenv := 2) (B := 2)
    (by norm_num) hs0 ht1 hΨ0 (by norm_num) (by norm_num) hEnv
    hΨlow' hΨ1 hWΨ hδ1 hΩ hll'

#print axioms firstCell_condExpDiag_weighted_witness

end RBM.Gauss
