/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.RandomLmaxFirstFace
import RBM1D.Gauss.RandomLmaxMinorEndpointRows

/-!
# Actual first-cell first-face bound at the same-sample full `Lmax`

The proof combines the accepted first-cell endpoint event with the zero-embedded (4.9)
identity.  A Ward estimate for each Hermitian principal minor supplies the block norm needed
for Cauchy--Schwarz; no finite telescoping comparison with the full matrix is used.
-/

namespace RBM.Gauss

open Filter MeasureTheory Matrix
open scoped BigOperators

private theorem firstCell_minor_ward_column_sq_le
    {τ' : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (S : Finset (Dims.exampleGrow.Idx N))
    (q : {i : Dims.exampleGrow.Idx N // i ∉ S}) :
    (∑ p : {i : Dims.exampleGrow.Idx N // i ∉ S},
        ‖greenSetMat Dims.exampleGrow N u (zt 0 u) S ω p q‖ ^ 2) ≤ 4 := by
  have hu1 : u < 1 := by
    have ht : firstCellT τ' N < 1 :=
      (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
    exact lt_of_le_of_lt hu.2 ht
  have huHalf : u ≤ 1 / 2 := by
    have ht : firstCellT τ' N ≤ 1 / 2 := by
      change gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 1 ≤ 1 / 2
      exact gridT_le (1 / 2 : ℝ) 1
    exact hu.2.trans ht
  have hηeq : etaT 0 u = 1 - u := by
    have htwo : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp [etaT, mE_im, htwo]
  have hη : 0 < etaT 0 u := by rw [hηeq]; linarith
  have hηhalf : (1 / 2 : ℝ) ≤ etaT 0 u := by rw [hηeq]; linarith
  have hz : (zt 0 u).im ≠ 0 := by
    rw [← etaT_eq_zt_im]
    exact hη.ne'
  let Hs : Matrix {i : Dims.exampleGrow.Idx N // i ∉ S}
      {i : Dims.exampleGrow.Idx N // i ∉ S} ℂ :=
    (Hflow Dims.exampleGrow N u ω).submatrix
    (Subtype.val : {i : Dims.exampleGrow.Idx N // i ∉ S} → Dims.exampleGrow.Idx N)
    Subtype.val
  have hHs : Hs.IsHermitian := (Hflow_isHermitian Dims.exampleGrow N u ω).submatrix _
  have hUsDet := isUnit_det_Hflow_submatrix_sub Dims.exampleGrow N u ω hz S
  have hUs : IsUnit (Hs - (zt 0 u) • (1 : Matrix _ _ ℂ)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (by simpa [Hs] using hUsDet)
  have hUs' : IsUnit (Hs - ((starRingEnd ℂ) (zt 0 u)) • (1 : Matrix _ _ ℂ)) := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    have hz' : ((starRingEnd ℂ) (zt 0 u)).im ≠ 0 := by
      rw [Complex.conj_im]
      exact neg_ne_zero.mpr hz
    have hdet := isUnit_det_Hflow_submatrix_sub (z := (starRingEnd ℂ) (zt 0 u))
      Dims.exampleGrow N u ω hz' S
    simpa [Hs] using hdet
  have hward := im_green_apply_eq_mul_sum_normSq hHs hUs hUs' q
  rw [← greenSetMat_eq_green_submatrix] at hward
  rw [← etaT_eq_zt_im] at hward
  have hsum :
    (∑ p : {i : Dims.exampleGrow.Idx N // i ∉ S},
        ‖greenSetMat Dims.exampleGrow N u (zt 0 u) S ω p q‖ ^ 2) =
      ∑ p : {i : Dims.exampleGrow.Idx N // i ∉ S},
        Complex.normSq (greenSetMat Dims.exampleGrow N u (zt 0 u) S ω p q) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    exact (Complex.normSq_eq_norm_sq _).symm
  rw [hsum]
  have him : (greenSetMat Dims.exampleGrow N u (zt 0 u) S ω q q).im ≤ (etaT 0 u)⁻¹ := by
    rw [greenSetMat_eq_green_submatrix]
    exact le_trans (Complex.im_le_norm _) (norm_greenSetMat_apply_le_etaT
      (by norm_num : |(0 : ℝ)| < 2) hu1 u q q ω)
  have hmul : etaT 0 u *
      (∑ p : {i : Dims.exampleGrow.Idx N // i ∉ S},
        Complex.normSq (greenSetMat Dims.exampleGrow N u (zt 0 u) S ω p q))
      ≤ (etaT 0 u)⁻¹ := by
    rw [← hward]
    exact him
  have hkey := mul_le_mul_of_nonneg_left hmul (le_of_lt (inv_pos.mpr hη))
  have heq : (etaT 0 u)⁻¹ *
      (etaT 0 u *
        ∑ p : {i : Dims.exampleGrow.Idx N // i ∉ S},
          Complex.normSq (greenSetMat Dims.exampleGrow N u (zt 0 u) S ω p q)) =
      ∑ p : {i : Dims.exampleGrow.Idx N // i ∉ S},
        Complex.normSq (greenSetMat Dims.exampleGrow N u (zt 0 u) S ω p q) := by
    field_simp
  rw [heq] at hkey
  calc
    (∑ p : {i : Dims.exampleGrow.Idx N // i ∉ S},
        Complex.normSq (greenSetMat Dims.exampleGrow N u (zt 0 u) S ω p q))
        ≤ (etaT 0 u)⁻¹ * (etaT 0 u)⁻¹ := hkey
    _ ≤ 4 := by
      have hinv : (etaT 0 u)⁻¹ ≤ 2 := by
        calc
          (etaT 0 u)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hηhalf
          _ = 2 := by norm_num
      have hprod := mul_le_mul hinv hinv (inv_nonneg.mpr hη.le) (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith

private theorem firstCell_minor_full_column_sq_le
    {τ' : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (S : Finset (Dims.exampleGrow.Idx N))
    (q : Dims.exampleGrow.Idx N) :
    (∑ p : Dims.exampleGrow.Idx N,
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω p q S‖ ^ 2) ≤ 4 := by
  classical
  by_cases hq : q ∈ S
  · have hz : ∀ p : Dims.exampleGrow.Idx N,
        gEnt Dims.exampleGrow N u (zt 0 u) ω p q S = 0 := fun p =>
          gEnt_eq_zero_right hq
    simp [hz]
  · let q' : {i : Dims.exampleGrow.Idx N // i ∉ S} := ⟨q, hq⟩
    let F : Dims.exampleGrow.Idx N → ℝ := fun p =>
      if hp : p ∉ S then
        ‖greenSetMat Dims.exampleGrow N u (zt 0 u) S ω ⟨p, hp⟩ q'‖ ^ 2 else 0
    have hsub :
        (∑ p : Dims.exampleGrow.Idx N,
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω p q S‖ ^ 2) =
        ∑ p : {i : Dims.exampleGrow.Idx N // i ∉ S},
          ‖greenSetMat Dims.exampleGrow N u (zt 0 u) S ω p q'‖ ^ 2 := by
      classical
      calc
        _ = ∑ p : Dims.exampleGrow.Idx N, F p := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              by_cases hpS : p ∉ S
              · rw [gEnt_apply hpS hq]
                simp [F, hpS, q']
              · rw [gEnt_eq_zero_left (not_not.mp hpS)]
                simp [F, hpS]
        _ = ∑ p ∈ Finset.univ.filter (fun p : Dims.exampleGrow.Idx N => p ∉ S), F p := by
              symm
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro p hp hnot
              have hpS : p ∈ S := by
                by_contra hnotS
                apply hnot
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hnotS⟩
              simp [F, hpS]
        _ = ∑ p : {i : Dims.exampleGrow.Idx N // i ∉ S}, F p.1 := by
              simpa using (Finset.sum_subtype
                (Finset.univ.filter (fun p : Dims.exampleGrow.Idx N => p ∉ S))
                (fun p => by simp) F)
        _ = ∑ p : {i : Dims.exampleGrow.Idx N // i ∉ S},
              ‖greenSetMat Dims.exampleGrow N u (zt 0 u) S ω p q'‖ ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              simp [F, p.2]
    rw [hsub]
    exact firstCell_minor_ward_column_sq_le hu S q'

private theorem firstCell_sum_block_ite_real {L W : ℕ} [NeZero L] [NeZero W]
    (f : ZMod L × Fin W → ZMod L × Fin W → ℝ) (a b : ZMod L) :
    (∑ p : ZMod L × Fin W, ∑ q : ZMod L × Fin W,
        (if p.1 = b then if q.1 = a then f p q else 0 else 0))
      = ∑ β : Fin W, ∑ α : Fin W, f (b, β) (a, α) := by
  have hq : ∀ p : ZMod L × Fin W,
      (∑ q : ZMod L × Fin W,
          (if p.1 = b then if q.1 = a then f p q else 0 else 0))
        = if p.1 = b then ∑ α : Fin W, f p (a, α) else 0 := by
    intro p
    by_cases hp : p.1 = b
    · simp only [if_pos hp, Fintype.sum_prod_type]
      refine (Finset.sum_eq_single a ?_ ?_).trans ?_
      · intro q₁ _ hne
        simp [hne]
      · intro h
        exact absurd (Finset.mem_univ a) h
      · simp
    · simp [hp]
  simp_rw [hq]
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_eq_single b ?_ ?_).trans ?_
  · intro p₁ _ hne
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ b) h
  · simp

set_option maxHeartbeats 1000000 in
private theorem embeddedMinorLoop_eq_offset_sum
    {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (S : Finset (Dims.exampleGrow.Idx N))
    (a b : ZMod (Dims.exampleGrow.L N)) :
    embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) S ω a b =
      ((Dims.exampleGrow.W N : ℝ)⁻¹) ^ 2 *
        ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω
            (a, p.1) (b, p.2) S‖ ^ 2 := by
  classical
  unfold embeddedMinorLoop
  congr 1
  conv_lhs => rw [Fintype.sum_prod_type]
  change (∑ p : Dims.exampleGrow.Idx N, ∑ q : Dims.exampleGrow.Idx N,
      (if p.1 = a ∧ q.1 = b then
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω p q S‖ ^ 2 else 0)) = _
  let f : Dims.exampleGrow.Idx N → Dims.exampleGrow.Idx N → ℝ := fun p q =>
    ‖gEnt Dims.exampleGrow N u (zt 0 u) ω p q S‖ ^ 2
  have hterm (p q : Dims.exampleGrow.Idx N) :
      (if p.1 = a ∧ q.1 = b then
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω p q S‖ ^ 2 else 0) =
        (if p.1 = a then
          if q.1 = b then ‖gEnt Dims.exampleGrow N u (zt 0 u) ω p q S‖ ^ 2
          else 0 else 0) := by
    by_cases hp : p.1 = a
    · by_cases hq : q.1 = b
      · rw [if_pos ⟨hp, hq⟩, if_pos hp, if_pos hq]
      · rw [if_neg (by intro h; exact hq h.2), if_pos hp, if_neg hq]
    · rw [if_neg (by intro h; exact hp h.1), if_neg hp]
  simp_rw [hterm]
  conv_rhs => rw [Fintype.sum_prod_type]
  change (∑ p : ZMod (Dims.exampleGrow.L N) × Fin (Dims.exampleGrow.W N),
      ∑ q : ZMod (Dims.exampleGrow.L N) × Fin (Dims.exampleGrow.W N),
        (if p.1 = a then if q.1 = b then f p q else 0 else 0)) =
    ∑ β : Fin (Dims.exampleGrow.W N),
      ∑ α : Fin (Dims.exampleGrow.W N), f (a, β) (b, α)
  exact firstCell_sum_block_ite_real
    (L := Dims.exampleGrow.L N) (W := Dims.exampleGrow.W N)
    (f := f) (a := b) (b := a)

private theorem firstCell_minor_block_column_sq_le
    {τ' : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (S : Finset (Dims.exampleGrow.Idx N))
    (a b : ZMod (Dims.exampleGrow.L N)) (α : Fin (Dims.exampleGrow.W N)) :
    (∑ β : Fin (Dims.exampleGrow.W N),
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, β) (b, α) S‖ ^ 2) ≤ 4 := by
  have hfull := firstCell_minor_full_column_sq_le
    (τ' := τ') (N := N) (u := u) (ω := ω) hu S (b, α)
  have hfull' :
      (∑ c : ZMod (Dims.exampleGrow.L N),
        ∑ β : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (c, β) (b, α) S‖ ^ 2) ≤ 4 := by
    simpa only [Fintype.sum_prod_type] using hfull
  calc
    (∑ β : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, β) (b, α) S‖ ^ 2)
        ≤ ∑ c : ZMod (Dims.exampleGrow.L N),
            ∑ β : Fin (Dims.exampleGrow.W N),
              ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (c, β) (b, α) S‖ ^ 2 := by
          refine Finset.single_le_sum (f := fun c : ZMod (Dims.exampleGrow.L N) =>
            ∑ β : Fin (Dims.exampleGrow.W N),
              ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (c, β) (b, α) S‖ ^ 2)
            (fun c _ => Finset.sum_nonneg fun β _ => sq_nonneg _) (Finset.mem_univ a)
    _ ≤ 4 := hfull'

private theorem firstCell_minor_block_raw_sq_le
    {τ' : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (S : Finset (Dims.exampleGrow.Idx N))
    (a b : ZMod (Dims.exampleGrow.L N)) :
    (∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (b, p.2) S‖ ^ 2)
        ≤ 4 * (Dims.exampleGrow.W N : ℝ) := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ β : Fin (Dims.exampleGrow.W N),
      ∑ α : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, β) (b, α) S‖ ^ 2)
        = ∑ α : Fin (Dims.exampleGrow.W N),
            ∑ β : Fin (Dims.exampleGrow.W N),
              ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, β) (b, α) S‖ ^ 2 := by
          exact Finset.sum_comm
    _ ≤ ∑ α : Fin (Dims.exampleGrow.W N), 4 :=
          Finset.sum_le_sum fun α _ => firstCell_minor_block_column_sq_le hu S a b α
    _ = 4 * (Dims.exampleGrow.W N : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring

private theorem firstCell_minor_cross_sum_le
    {τ' loss : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (hN : 1 ≤ N) (hΓ0 : 0 ≤ Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u))
    (T R : Finset (Dims.exampleGrow.Idx N))
    (_hT : T.card ≤ M) (κ : Dims.exampleGrow.Idx N) (_hκ : κ ∉ T)
    (a c : ZMod (Dims.exampleGrow.L N))
    (hrow : ((Dims.exampleGrow.W N : ℝ)⁻¹) *
      (∑ β : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, β) κ T‖ ^ 2) ≤
        20 * (N : ℝ) ^ loss * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u))
    (hcol : ((Dims.exampleGrow.W N : ℝ)⁻¹) *
      (∑ α : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (c, α) T‖ ^ 2) ≤
        20 * (N : ℝ) ^ loss * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) :
    (∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) R‖ *
        (‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) κ T‖ *
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (c, p.2) T‖)) ≤
      40 * Real.sqrt (Dims.exampleGrow.W N : ℝ) * (Dims.exampleGrow.W N : ℝ) *
        (N : ℝ) ^ loss * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by
  let f : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N) → ℝ := fun p =>
    ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) R‖
  let g : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N) → ℝ := fun p =>
    ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) κ T‖ *
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (c, p.2) T‖
  let W : ℝ := Dims.exampleGrow.W N
  let Γ : ℝ := Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)
  have hWpos : 0 < W := by
    dsimp [W]
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hW0 : 0 ≤ W := hWpos.le
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNpow : 0 ≤ (N : ℝ) ^ loss := Real.rpow_nonneg (Nat.cast_nonneg N) loss
  have hΓ : 0 ≤ Γ := hΓ0
  have hrowRaw :
      (∑ β : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, β) κ T‖ ^ 2) ≤
        20 * W * (N : ℝ) ^ loss * Γ := by
    have heq : W * (W⁻¹ *
        (∑ β : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, β) κ T‖ ^ 2)) =
        ∑ β : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, β) κ T‖ ^ 2 := by
      field_simp [ne_of_gt hWpos]
    calc
      _ = W * (W⁻¹ *
          (∑ β : Fin (Dims.exampleGrow.W N),
            ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, β) κ T‖ ^ 2)) := heq.symm
      _ ≤ W * (20 * (N : ℝ) ^ loss * Γ) :=
        mul_le_mul_of_nonneg_left hrow hW0
      _ = 20 * W * (N : ℝ) ^ loss * Γ := by ring
  have hcolRaw :
      (∑ α : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (c, α) T‖ ^ 2) ≤
        20 * W * (N : ℝ) ^ loss * Γ := by
    have heq : W * (W⁻¹ *
        (∑ α : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (c, α) T‖ ^ 2)) =
        ∑ α : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (c, α) T‖ ^ 2 := by
      field_simp [ne_of_gt hWpos]
    calc
      _ = W * (W⁻¹ *
          (∑ α : Fin (Dims.exampleGrow.W N),
            ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (c, α) T‖ ^ 2)) := heq.symm
      _ ≤ W * (20 * (N : ℝ) ^ loss * Γ) :=
        mul_le_mul_of_nonneg_left hcol hW0
      _ = 20 * W * (N : ℝ) ^ loss * Γ := by ring
  have hfsq : (∑ p, f p ^ 2) ≤ 4 * W := by
    simpa only [f, Fintype.sum_prod_type, W] using
      firstCell_minor_block_raw_sq_le
        (τ' := τ') (N := N) (u := u) (ω := ω) hu R a c
  have hgsq : (∑ p, g p ^ 2) =
      (∑ β : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, β) κ T‖ ^ 2) *
      (∑ α : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (c, α) T‖ ^ 2) := by
    conv_lhs => rw [Fintype.sum_prod_type]
    simp_rw [g, mul_pow]
    exact (Fintype.sum_mul_sum _ _).symm
  have hgsqBound : (∑ p, g p ^ 2) ≤ (20 * W * (N : ℝ) ^ loss * Γ) ^ 2 := by
    rw [hgsq]
    have hrow0 : 0 ≤
        ∑ β : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, β) κ T‖ ^ 2 :=
      Finset.sum_nonneg fun β _ => sq_nonneg _
    have hcol0 : 0 ≤
        ∑ α : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (c, α) T‖ ^ 2 :=
      Finset.sum_nonneg fun α _ => sq_nonneg _
    have hB0 : 0 ≤ 20 * W * (N : ℝ) ^ loss * Γ := by positivity
    calc
      _ ≤ (20 * W * (N : ℝ) ^ loss * Γ) *
          (20 * W * (N : ℝ) ^ loss * Γ) :=
        mul_le_mul hrowRaw hcolRaw hcol0 hB0
      _ = (20 * W * (N : ℝ) ^ loss * Γ) ^ 2 := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N))) f g
  have hcross0 : 0 ≤ ∑ p, f p * g p :=
    Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hWsqrt : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hW0
  have hWcube : W ^ 3 = (Real.sqrt W) ^ 2 * W ^ 2 := by
    rw [hWsqrt]
    ring
  have htargetSq : (4 * W) * (20 * W * (N : ℝ) ^ loss * Γ) ^ 2 =
      (40 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ) ^ 2 := by
    calc
      (4 * W) * (20 * W * (N : ℝ) ^ loss * Γ) ^ 2 =
          1600 * W ^ 3 * ((N : ℝ) ^ loss) ^ 2 * Γ ^ 2 := by ring
      _ = 1600 * (Real.sqrt W) ^ 2 * W ^ 2 *
          ((N : ℝ) ^ loss) ^ 2 * Γ ^ 2 := by rw [hWcube]; ring
      _ = (40 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ) ^ 2 := by ring
  have hcrossSq : (∑ p, f p * g p) ^ 2 ≤
      (40 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ) ^ 2 := by
    calc
      (∑ p, f p * g p) ^ 2 ≤ (∑ p, f p ^ 2) * (∑ p, g p ^ 2) := hcs
      _ ≤ (4 * W) * (20 * W * (N : ℝ) ^ loss * Γ) ^ 2 :=
        mul_le_mul hfsq hgsqBound (Finset.sum_nonneg fun p _ => sq_nonneg _) (by positivity)
      _ = (40 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ) ^ 2 := htargetSq
  have htarget0 : 0 ≤ 40 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ := by
    positivity
  have hsumle : ∑ p, f p * g p ≤
      40 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ :=
    (sq_le_sq₀ hcross0 htarget0).mp hcrossSq
  simpa [f, g, W, Γ, mul_assoc] using hsumle

private theorem firstCell_abs_norm_sq_sub_le (x y : ℂ) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have hnorm := abs_norm_sub_norm_le x y
  have hsum : 0 ≤ ‖x‖ + ‖y‖ := by positivity
  rw [show ‖x‖ ^ 2 - ‖y‖ ^ 2 = (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) by ring,
    abs_mul, abs_of_nonneg hsum]
  calc
    |‖x‖ - ‖y‖| * (‖x‖ + ‖y‖) ≤ ‖x - y‖ * (‖x‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_right hnorm hsum
    _ = (‖x‖ + ‖y‖) * ‖x - y‖ := by ring

/-- Pointwise first-face estimate on a fixed event sample and time.  The loss is the one
already reserved in the endpoint event; the same `Lmax` controls both endpoint rows and the
face. -/
theorem firstCell_randomLmax_first_face_le
    {τ' loss : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta loss) N)
    (hloss : 0 < loss)
    (hδquarter : firstCellMinorEndpointDelta loss N ≤ 1 / 4)
    (hMδ : 8 * (M : ℝ) * firstCellMinorEndpointDelta loss N ≤ 1)
    (hN : 1 ≤ N)
    (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (S : Finset (Dims.exampleGrow.Idx N)) (hS : S.card < M)
    (κ : Dims.exampleGrow.Idx N) (hκ : κ ∉ S)
    (a c : ZMod (Dims.exampleGrow.L N)) :
    |embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) S ω a c -
      embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) (insert κ S) ω a c| ≤
      320 * (N : ℝ) ^ loss *
        (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ ((3 : ℝ) / 2) := by
  let δ := firstCellMinorEndpointDelta loss N
  let W : ℝ := Dims.exampleGrow.W N
  let Γ : ℝ := Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)
  have hflow : ω ∈ goodSetFlow Dims.exampleGrow 0 (firstCellS τ')
      (firstCellT τ') (firstCellMinorEndpointDelta loss) N := hω.1
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, firstCellMinorEndpointDelta]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (firstCellPsi_pos N).le
  have hδq : δ ≤ 1 / 4 := hδquarter
  have hMδ' : 8 * (M : ℝ) * δ ≤ 1 := hMδ
  have hu1 : u < 1 := lt_of_le_of_lt hu.2
    ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
  have hz : (zt 0 u).im ≠ 0 := zt_im_ne_zero_of_lt_one (by norm_num) hu1
  have hG : GoodEvent (green (Hflow Dims.exampleGrow N u ω) (zt 0 u)) (mE 0) δ :=
    hflow u hu
  have hg : MinorGoodLe Dims.exampleGrow N u (zt 0 u) (mE 0) ω (2 * δ) M :=
    minorGoodLe_of_goodEvent_flow (by norm_num) hz hδ0 hδq hMδ' hG
  have hScard : S.card ≤ M := Nat.le_of_lt hS
  have hInsertCard : (insert κ S).card ≤ M := by
    rw [Finset.card_insert_of_notMem hκ]
    omega
  have hΓ0 : 0 ≤ Γ := Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
  have hWpos : 0 < W := by
    dsimp [W]
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hW0 : 0 ≤ W := hWpos.le
  have hrowcolA := firstCell_randomLmax_minor_endpoint_row_column_le
    (τ' := τ') (b := loss) (N := N) (u := u) (ω := ω) (M := M)
    hω hloss hδq hMδ' hN hu S hScard κ hκ a
  have hrowcolC := firstCell_randomLmax_minor_endpoint_row_column_le
    (τ' := τ') (b := loss) (N := N) (u := u) (ω := ω) (M := M)
    hω hloss hδq hMδ' hN hu S hScard κ hκ c
  have hcrossS := firstCell_minor_cross_sum_le
    (τ' := τ') (loss := loss) (N := N) (u := u) (ω := ω) (M := M)
    hu hN hΓ0 S S hScard κ hκ a c hrowcolA.1 hrowcolC.2
  have hcrossI := firstCell_minor_cross_sum_le
    (τ' := τ') (loss := loss) (N := N) (u := u) (ω := ω) (M := M)
    hu hN hΓ0 S (insert κ S) hScard κ hκ a c hrowcolA.1 hrowcolC.2
  let fS : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N) → ℝ := fun p =>
    ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) S‖
  let fI : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N) → ℝ := fun p =>
    ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) (insert κ S)‖
  let g : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N) → ℝ := fun p =>
    ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) κ S‖ *
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω κ (c, p.2) S‖
  have hentry (p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N)) :
      |‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) S‖ ^ 2 -
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) (insert κ S)‖ ^ 2| ≤
      2 * (fS p * g p + fI p * g p) := by
    let x := gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) S
    let y := gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) (insert κ S)
    let r := gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) κ S
    let s := gEnt Dims.exampleGrow N u (zt 0 u) ω κ (c, p.2) S
    have hrank := gEnt_sub_insert_rankOne Dims.exampleGrow N u (zt 0 u) (mE 0)
      ω (2 * δ) M S κ (a, p.1) (c, p.2) hg hInsertCard
    have hinv := hg.inv_le S hScard κ
    have hdiff : ‖x - y‖ ≤ 2 * ‖r‖ * ‖s‖ := by
      calc
        ‖x - y‖ = ‖r * s *
            (gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S)⁻¹‖ := by
              rw [show x - y = r * s *
                (gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S)⁻¹ by
                  simpa [x, y, r, s] using hrank]
        _ = (‖r‖ * ‖s‖) *
            ‖(gEnt Dims.exampleGrow N u (zt 0 u) ω κ κ S)⁻¹‖ := by
              simp only [norm_mul]
        _ ≤ (‖r‖ * ‖s‖) * 2 :=
              mul_le_mul_of_nonneg_left hinv (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = 2 * ‖r‖ * ‖s‖ := by ring
    have hsum : 0 ≤ ‖x‖ + ‖y‖ := by positivity
    calc
      _ ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := firstCell_abs_norm_sq_sub_le x y
      _ ≤ (‖x‖ + ‖y‖) * (2 * ‖r‖ * ‖s‖) :=
        mul_le_mul_of_nonneg_left hdiff hsum
      _ = 2 * (fS p * g p + fI p * g p) := by
        dsimp [x, y, r, s, fS, fI, g]
        ring
  have hsumFace :
      (∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
        |‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) S‖ ^ 2 -
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) (insert κ S)‖ ^ 2|) ≤
        160 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ := by
    calc
      _ ≤ ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          2 * (fS p * g p + fI p * g p) :=
        Finset.sum_le_sum fun p _ => hentry p
      _ = 2 * ((∑ p, fS p * g p) + (∑ p, fI p * g p)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * ((40 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ) +
          (40 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hcrossS hcrossI) (by norm_num)
      _ = 160 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ := by ring
  have hsumAbs :
      |∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
        (‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) S‖ ^ 2 -
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) (insert κ S)‖ ^ 2)| ≤
      160 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ := by
    calc
      _ ≤ ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          |‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) S‖ ^ 2 -
            ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) (insert κ S)‖ ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ 160 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ := hsumFace
  have hloop :
      embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) S ω a c -
        embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) (insert κ S) ω a c =
        ((Dims.exampleGrow.W N : ℝ)⁻¹) ^ 2 *
          ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
            (‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) S‖ ^ 2 -
              ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) (insert κ S)‖ ^ 2) := by
    rw [embeddedMinorLoop_eq_offset_sum S a c,
      embeddedMinorLoop_eq_offset_sum (insert κ S) a c]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hscaled :
      |embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) S ω a c -
        embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) (insert κ S) ω a c| ≤
        160 * (Real.sqrt W / W) * (N : ℝ) ^ loss * Γ := by
    rw [hloop, abs_mul, abs_of_nonneg (sq_nonneg ((Dims.exampleGrow.W N : ℝ)⁻¹))]
    calc
      ((Dims.exampleGrow.W N : ℝ)⁻¹) ^ 2 *
          |∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
            (‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) S‖ ^ 2 -
              ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) (insert κ S)‖ ^ 2)|
          ≤ ((Dims.exampleGrow.W N : ℝ)⁻¹) ^ 2 *
            (160 * Real.sqrt W * W * (N : ℝ) ^ loss * Γ) :=
              mul_le_mul_of_nonneg_left hsumAbs (sq_nonneg _)
      _ = 160 * (Real.sqrt W / W) * (N : ℝ) ^ loss * Γ := by
          dsimp [W]
          field_simp [ne_of_gt (by exact_mod_cast Dims.exampleGrow.W_pos N :
            0 < (Dims.exampleGrow.W N : ℝ))]
          
  have hWLower : W⁻¹ ≤ 4 * Γ := by
    dsimp [W, Γ]
    exact inv_W_le_Lmax_flow (d := Dims.exampleGrow) (s := firstCellS τ')
      (t := firstCellT τ') (δ := firstCellMinorEndpointDelta loss) (E := 0)
      (by norm_num) (hδquarter.trans (by norm_num)) hflow hu
  have hΓpos : 0 < Γ := by
    have hWinv : 0 < W⁻¹ := inv_pos.mpr hWpos
    nlinarith [hWLower]
  have hRatioSq : (Real.sqrt W / W) ^ 2 = W⁻¹ := by
    have hs := Real.sq_sqrt hW0
    field_simp [ne_of_gt hWpos]
    nlinarith [hs]
  have hGammaPow : Γ ^ ((3 : ℝ) / 2) = Γ * Real.sqrt Γ := by
    rw [show (3 : ℝ) / 2 = 1 + (1 : ℝ) / 2 by ring,
      Real.rpow_add hΓpos]
    simp only [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hRatio : Real.sqrt W / W ≤ 2 * Real.sqrt Γ := by
    have hrightSq : (2 * Real.sqrt Γ) ^ 2 = 4 * Γ := by
      rw [mul_pow, Real.sq_sqrt hΓpos.le]
      norm_num
    have hSq : (Real.sqrt W / W) ^ 2 ≤ (2 * Real.sqrt Γ) ^ 2 := by
      rw [hRatioSq, hrightSq]
      exact hWLower
    apply (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg _) hWpos.le)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    exact hSq
  calc
    |embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) S ω a c -
        embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) (insert κ S) ω a c|
        ≤ 160 * (Real.sqrt W / W) * (N : ℝ) ^ loss * Γ := hscaled
    _ ≤ 160 * (2 * Real.sqrt Γ) * (N : ℝ) ^ loss * Γ := by
      calc
        160 * (Real.sqrt W / W) * (N : ℝ) ^ loss * Γ =
            160 * ((Real.sqrt W / W) * ((N : ℝ) ^ loss * Γ)) := by ring
        _ ≤ 160 * ((2 * Real.sqrt Γ) * ((N : ℝ) ^ loss * Γ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hRatio
              (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) loss) hΓ0))
            (by norm_num : (0 : ℝ) ≤ 160)
        _ = 160 * (2 * Real.sqrt Γ) * (N : ℝ) ^ loss * Γ := by ring
    _ = 320 * (N : ℝ) ^ loss * Γ ^ ((3 : ℝ) / 2) := by
      rw [hGammaPow]
      ring

private theorem firstFace_delta_small {loss : ℝ} (M : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      firstCellMinorEndpointDelta loss N ≤ 1 / 4 ∧
        8 * (M : ℝ) * firstCellMinorEndpointDelta loss N ≤ 1 := by
  have hbeta := firstCellMinorEndpointBeta_le_one_sixteenth loss
  have hpsi := firstCellPsi_le_rpow_neg_quarter
  have hMpow : ∀ᶠ N : ℕ in atTop,
      8 * (M : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 16) :=
    eventually_le_rpow _ (by norm_num)
  have hfourpow : ∀ᶠ N : ℕ in atTop,
      4 ≤ (N : ℝ) ^ ((3 : ℝ) / 16) :=
    eventually_le_rpow 4 (by norm_num)
  filter_upwards [hpsi, hMpow, hfourpow, eventually_ge_atTop 1]
    with N hpsiN hMpowN hfourpowN hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hδle : firstCellMinorEndpointDelta loss N ≤ (N : ℝ) ^ (-(3 : ℝ) / 16) := by
    have hmul := mul_le_mul_of_nonneg_left hpsiN
      (Real.rpow_nonneg (Nat.cast_nonneg N) (firstCellMinorEndpointBeta loss))
    have hpow : (N : ℝ) ^ firstCellMinorEndpointBeta loss *
        (N : ℝ) ^ (-(1 : ℝ) / 4) =
          (N : ℝ) ^ (firstCellMinorEndpointBeta loss - 1 / 4) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    calc
      firstCellMinorEndpointDelta loss N =
          (N : ℝ) ^ firstCellMinorEndpointBeta loss * firstCellPsi N := rfl
      _ ≤ (N : ℝ) ^ firstCellMinorEndpointBeta loss *
          (N : ℝ) ^ (-(1 : ℝ) / 4) := hmul
      _ = (N : ℝ) ^ (firstCellMinorEndpointBeta loss - 1 / 4) := hpow
      _ ≤ (N : ℝ) ^ (-(3 : ℝ) / 16) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1
        linarith
  have hnegpow : (N : ℝ) ^ (-(3 : ℝ) / 16) =
      ((N : ℝ) ^ ((3 : ℝ) / 16))⁻¹ := by
    rw [show -(3 : ℝ) / 16 = -((3 : ℝ) / 16) by ring,
      Real.rpow_neg (Nat.cast_nonneg N)]
  have hquarter : (N : ℝ) ^ (-(3 : ℝ) / 16) ≤ 1 / 4 := by
    rw [hnegpow]
    have hpos : (0 : ℝ) < (N : ℝ) ^ ((3 : ℝ) / 16) := Real.rpow_pos_of_pos hN0 _
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 4) hfourpowN
    norm_num at hinv ⊢
    exact hinv
  have hsmall : firstCellMinorEndpointDelta loss N ≤ 1 / 4 := hδle.trans hquarter
  have hbudget : 8 * (M : ℝ) * firstCellMinorEndpointDelta loss N ≤ 1 := by
    by_cases hM : M = 0
    · simp [hM]
    · have hMpos : (0 : ℝ) < 8 * (M : ℝ) := by
        exact mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM))
      have hpowpos : (0 : ℝ) < (N : ℝ) ^ ((3 : ℝ) / 16) :=
        Real.rpow_pos_of_pos hN0 _
      have hinv : ((N : ℝ) ^ ((3 : ℝ) / 16))⁻¹ ≤ (8 * (M : ℝ))⁻¹ :=
        inv_anti₀ hMpos hMpowN
      have hdeltaInv : (N : ℝ) ^ (-(3 : ℝ) / 16) ≤ (8 * (M : ℝ))⁻¹ := by
        rw [hnegpow]
        exact hinv
      calc
        8 * (M : ℝ) * firstCellMinorEndpointDelta loss N
            ≤ 8 * (M : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 16) :=
              mul_le_mul_of_nonneg_left hδle (by positivity)
        _ ≤ 8 * (M : ℝ) * (8 * (M : ℝ))⁻¹ :=
              mul_le_mul_of_nonneg_left hdeltaInv (by positivity)
        _ = 1 := by field_simp
  exact ⟨hsmall, hbudget⟩

/-- Actual Gaussian witness for the arbitrary-loss same-sample first-face estimate.  The
time, all minors of size below the fixed budget, both blocks, and the full-matrix `Lmax` all
belong to the same event sample supplied by the accepted endpoint witness. -/
theorem firstCell_randomLmax_actual_first_face_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ') firstCellPsi ∧
      ∀ loss : ℝ, 0 < loss → ∀ M : ℕ,
        ∀ᶠ N : ℕ in atTop,
          ∃ ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
              (firstCellMinorEndpointDelta loss) N,
            ∃ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
              0 < u ∧ u < firstCellT τ' N ∧
                ∀ S : Finset (Dims.exampleGrow.Idx N), S.card < M →
                  ∀ κ : Dims.exampleGrow.Idx N, κ ∉ S →
                    ∀ a c : ZMod (Dims.exampleGrow.L N),
                      |embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) S ω a c -
                        embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) (insert κ S) ω a c| ≤
                        320 * (N : ℝ) ^ loss *
                          (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ ((3 : ℝ) / 2) := by
  obtain ⟨τ', hτ', hll, hendpoint⟩ :=
    firstCell_randomLmax_actual_minor_endpoint_witness
  refine ⟨τ', hτ', hll, ?_⟩
  intro loss hloss M
  filter_upwards [hendpoint loss hloss M, firstFace_delta_small M,
    eventually_ge_atTop 1] with N hdata hsmall hN
  rcases hdata with ⟨ω, hω, u, hu, hu0, hut, _hrows⟩
  have hN1 : 1 ≤ N := hN
  refine ⟨ω, hω, u, hu, hu0, hut, ?_⟩
  intro S hS κ hκ a c
  exact firstCell_randomLmax_first_face_le hω hloss hsmall.1 hsmall.2 hN1
    hu S hS κ hκ a c

#print axioms firstCell_randomLmax_first_face_le
#print axioms firstCell_randomLmax_actual_first_face_witness

end RBM.Gauss
