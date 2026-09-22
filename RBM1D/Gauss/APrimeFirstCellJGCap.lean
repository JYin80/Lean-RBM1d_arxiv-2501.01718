/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellCommon

/-! A one-time actual block Green cap on the first positive subcell. -/

namespace RBM.APrimeFirstCellJGCap

open Filter Real Gauss
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

noncomputable def firstTime (N : ℕ) : ℝ := ((N : ℝ) ^ (248 : ℕ))⁻¹

noncomputable def sourceEll (ζ : ℝ) (N : ℕ) : ℝ :=
  (2 * (N : ℝ) ^ ζ) ^ (-(1 / 5 : ℝ))

noncomputable def sourceC4 (ζ : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ ζ * (B.ell N (firstTime N)) ^ (3 : ℕ) *
    ((B.scale 0 N (firstTime N))⁻¹) ^ (3 : ℕ)

private theorem zero_green_off_block (N : ℕ) (ω : Gauss.Ω d)
    {x y : ZMod (d.L N)} (hxy : x ≠ y) (p q : Fin (d.W N)) :
    green (Hflow d N 0 ω) (zt 0 0) (x, p) (y, q) = 0 := by
  have hz : zt 0 0 ≠ 0 := by
    rw [zt, Gauss.mE_zero]
    norm_num
  rw [Hflow_zero, green_zero hz, Matrix.smul_apply, smul_eq_mul]
  have hij : (x, p) ≠ (y, q) := by
    intro heq
    exact hxy (congrArg Prod.fst heq)
  have hone : (1 : Matrix (d.Idx N) (d.Idx N) ℂ) (x, p) (y, q) = 0 := by
    rw [Matrix.one_apply, if_neg hij]
  rw [hone, mul_zero]

theorem norm_green_off_block_le (N : ℕ) (ω : Gauss.Ω d)
    (hX : ‖Xmat d N ω‖ ≤ (N : ℝ))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2))
    {x y : ZMod (d.L N)} (hxy : x ≠ y) (p q : Fin (d.W N)) :
    ‖green (Hflow d N u ω) (zt 0 u) (x, p) (y, q)‖ ≤
      4 * ((N : ℝ) + 1) * Real.sqrt u := by
  have hG := Gauss.norm_green_flow_sub_le_sqrt d N (E := 0)
    (by norm_num) (s := 0) (t := 1 / 2)
    (by norm_num) (by norm_num) ω hu
    (show (0 : ℝ) ∈ Set.Icc 0 (1 / 2) by constructor <;> norm_num)
  have hη : etaT 0 (1 / 2) = 1 / 2 := by
    norm_num [etaT, Gauss.mE_zero]
  rw [hη] at hG
  norm_num at hG
  have hentry := norm_apply_le_l2_opNorm
    (green (Hflow d N u ω) (zt 0 u) - green (Hflow d N 0 ω) (zt 0 0))
    (x, p) (y, q)
  have hzero := zero_green_off_block N ω hxy p q
  simp only [Matrix.sub_apply, hzero, sub_zero] at hentry
  calc
    _ ≤ ‖green (Hflow d N u ω) (zt 0 u) - green (Hflow d N 0 ω) (zt 0 0)‖ := hentry
    _ ≤ 4 * ((N : ℝ) + 1) * Real.sqrt u := by
      have hsqrt : Real.sqrt |u - 0| = Real.sqrt u := by
        rw [sub_zero, abs_of_nonneg hu.1]
      rw [abs_of_nonneg hu.1] at hG
      simpa only [Hflow_zero] using
        (hG.trans (by nlinarith [Real.sqrt_nonneg u, hX] :
          4 * (‖Xmat d N ω‖ + 1) * √u ≤ 4 * ((N : ℝ) + 1) * √u))

#print axioms norm_green_off_block_le

private theorem firstTime_mem (N : ℕ) (hN : 2 ≤ N) :
    firstTime N ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (2 : ℝ) ≤ (N : ℝ) ^ (248 : ℕ) := by
    calc
      (2 : ℝ) ≤ (N : ℝ) := hNr
      _ ≤ (N : ℝ) ^ (248 : ℕ) := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ N) (by norm_num : 1 ≤ 248))
  constructor
  · unfold firstTime
    positivity
  · unfold firstTime
    simpa [one_div] using
      (inv_le_inv₀ (show (0 : ℝ) < (N : ℝ) ^ 248 by linarith)
        (show (0 : ℝ) < 2 by norm_num)).2 hp

private theorem sqrt_firstTime (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt (firstTime N) = ((N : ℝ) ^ (124 : ℕ))⁻¹ := by
  unfold firstTime
  have he : (N : ℝ) ^ (248 : ℕ) = ((N : ℝ) ^ (124 : ℕ)) ^ (2 : ℕ) := by
    rw [← pow_mul]
  rw [he, Real.sqrt_inv, Real.sqrt_sq (by positivity)]

theorem norm_green_firstTime_off_block_le (N : ℕ) (hN : 2 ≤ N)
    (ω : Gauss.Ω d) (hX : ‖Xmat d N ω‖ ≤ (N : ℝ))
    {x y : ZMod (d.L N)} (hxy : x ≠ y) (p q : Fin (d.W N)) :
    ‖green (Hflow d N (firstTime N) ω) (zt 0 (firstTime N))
      (x, p) (y, q)‖ ≤ 8 * (((N : ℝ) ^ (123 : ℕ))⁻¹) := by
  have hbase := norm_green_off_block_le N ω hX (firstTime_mem N hN) hxy p q
  rw [sqrt_firstTime N (by omega)] at hbase
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNz : (N : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ 4 * ((N : ℝ) + 1) * (((N : ℝ) ^ (124 : ℕ))⁻¹) := hbase
    _ ≤ 8 * (N : ℝ) * (((N : ℝ) ^ (124 : ℕ))⁻¹) := by
      have hh : 4 * ((N : ℝ) + 1) ≤ 8 * (N : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right hh (by positivity)
    _ = 8 * (((N : ℝ) ^ (123 : ℕ))⁻¹) := by
      rw [show (124 : ℕ) = 123 + 1 by omega, pow_succ]
      field_simp

#print axioms norm_green_firstTime_off_block_le

private theorem tail_floor_N (N : ℕ) (hN : 81 ≤ N)
    (ℓ η r : ℝ) :
    (((N : ℝ) ^ (60 : ℕ))⁻¹) ≤
      tailT (d.W N : ℝ) ℓ η 60 r := by
  have hWN : d.W N ≤ N := by
    change Dims.growW N ≤ N
    rw [Dims.growW_eq N (by omega)]
    exact Nat.div_le_self N (Dims.growL N)
  have hWpos : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hWp : (d.W N : ℝ) ^ (60 : ℕ) ≤ (N : ℝ) ^ (60 : ℕ) :=
    pow_le_pow_left₀ hWpos.le (by exact_mod_cast hWN) 60
  have hinv : (((N : ℝ) ^ (60 : ℕ))⁻¹) ≤
      (((d.W N : ℝ) ^ (60 : ℕ))⁻¹) :=
    (inv_le_inv₀ (pow_pos hNpos _) (pow_pos hWpos _)).2 hWp
  have hfloor := rpow_neg_le_tailT (W := (d.W N : ℝ)) (ℓu := ℓ)
    (ηu := η) (D := (60 : ℝ)) r
  have hfloor' : (((d.W N : ℝ) ^ (60 : ℕ))⁻¹) ≤
      tailT (d.W N : ℝ) ℓ η 60 r := by
    simpa only [Real.rpow_neg hWpos.le, Real.rpow_ofNat] using hfloor
  exact hinv.trans hfloor'

private theorem square_ledger (N : ℕ) (hN : 1 ≤ N) :
    (8 * (((N : ℝ) ^ (123 : ℕ))⁻¹)) ^ 2 =
      64 * (((N : ℝ) ^ (246 : ℕ))⁻¹) := by
  have hz : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [show (246 : ℕ) = 123 * 2 by omega, pow_mul]
  ring

private theorem floor_ledger (N : ℕ) (hN : 1 ≤ N) :
    64 * (((N : ℝ) ^ (246 : ℕ))⁻¹) =
      (64 * (((N : ℝ) ^ (186 : ℕ))⁻¹)) *
        (((N : ℝ) ^ (60 : ℕ))⁻¹) := by
  rw [show (246 : ℕ) = 186 + 60 by omega, pow_add, mul_inv_rev]
  ring

private theorem jG_firstTime_le (N : ℕ) (hN : 81 ≤ N)
    (hstar : 12 ≤ ellStar (d.W N : ℝ) (B.ell N (firstTime N)))
    (ω : Gauss.Ω d) (hX : ‖Xmat d N ω‖ ≤ (N : ℝ)) :
    APrimeJG.jG (Gauss.sample d) 0 N (firstTime N) ω
      (B.ell N (firstTime N)) (etaT 0 (firstTime N)) 60 ≤
      1 + 64 * (((N : ℝ) ^ (186 : ℕ))⁻¹) := by
  let F : ℝ := 64 * (((N : ℝ) ^ (186 : ℕ))⁻¹)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hW : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  apply APrimeJG.jG_le_of_neighbor_green_sq
    (X := Gauss.sample d) 0 N (firstTime N) ω
    (B.ell N (firstTime N)) (etaT 0 (firstTime N)) 60 F hW hF
  intro x y x' hxy hxx' p q
  have hfar := APrimeJG.far_neighbor_not_support (d.three_le_L N)
    hxx' hstar hxy
  have hne : x' ≠ y := by
    intro heq
    apply hfar
    rw [heq]
    change y - y ∈ sbSupport ((Gauss.band d).L N)
    rw [sub_self]
    change (0 : ZMod ((Gauss.band d).L N)) ∈
      ({0, 1, -1} : Finset (ZMod ((Gauss.band d).L N)))
    exact Finset.mem_insert_self _ _
  have hfloor := tail_floor_N N hN (B.ell N (firstTime N))
    (etaT 0 (firstTime N)) (zdist (d.L N) (x-y))
  have hnum : (8 * (((N : ℝ) ^ (123 : ℕ))⁻¹)) ^ 2 ≤
      F * tailT (d.W N : ℝ) (B.ell N (firstTime N))
        (etaT 0 (firstTime N)) 60 (zdist (d.L N) (x-y)) := by
    rw [square_ledger N (by omega)]
    calc
      64 * (((N : ℝ) ^ (246 : ℕ))⁻¹) =
          F * (((N : ℝ) ^ (60 : ℕ))⁻¹) := floor_ledger N (by omega)
      _ ≤ F * tailT (d.W N : ℝ) (B.ell N (firstTime N))
          (etaT 0 (firstTime N)) 60 (zdist (d.L N) (x-y)) :=
            mul_le_mul_of_nonneg_left hfloor hF
  constructor
  · have hb := norm_green_firstTime_off_block_le N (by omega) ω hX
      (x := y) (y := x') (Ne.symm hne) p q
    exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans hnum
  · have hb := norm_green_firstTime_off_block_le N (by omega) ω hX
      (x := x') (y := y) hne p q
    exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans hnum

private theorem eventually_hstar :
    ∀ᶠ N : ℕ in atTop,
      12 ≤ ellStar (d.W N : ℝ) (B.ell N (firstTime N)) := by
  have h := APrimeJG.eventually_twelve_le_ellStar (B := B)
    (s := fun _ => (0 : ℝ)) (t := fun _ => (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [h, eventually_ge_atTop 2] with N hNstar hN
  exact hNstar ⟨firstTime N, firstTime_mem N hN⟩

theorem eventually_jG_le_N_of_norm :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Gauss.Ω d,
      ‖Xmat d N ω‖ ≤ (N : ℝ) →
      APrimeJG.jG (Gauss.sample d) 0 N (firstTime N) ω
        (B.ell N (firstTime N)) (etaT 0 (firstTime N)) 60 ≤ (N : ℝ) := by
  filter_upwards [eventually_hstar, eventually_ge_atTop 81] with N hstar hN ω hX
  have hb := jG_firstTime_le N hN hstar ω hX
  have hNr : (81 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (1 : ℝ) ≤ (N : ℝ) ^ (186 : ℕ) := by
    exact one_le_pow₀ (by linarith)
  have hi : (((N : ℝ) ^ (186 : ℕ))⁻¹) ≤ 1 := by
    rw [← one_div, div_le_iff₀ (by positivity)]
    simpa using hp
  linarith

#print axioms eventually_jG_le_N_of_norm

/-- The independent numerical hypotheses of T334, at the same one-time first subcell. -/
theorem eventually_firstTime_T334_scales :
    ∀ᶠ N : ℕ in atTop,
      Real.exp 1 ≤ (d.W N : ℝ) ∧
      4 ≤ Real.log (d.W N : ℝ) ∧
      (4 * (60 : ℝ)) ^ 2 ≤ Real.log (d.W N : ℝ) ∧
      1 ≤ (N : ℝ) ∧
      (N : ℝ)⁻¹ ≤ etaT 0 (firstTime N) ∧
      1 ≤ (d.W N : ℝ) * B.ell N (firstTime N) * etaT 0 (firstTime N) ∧
      (d.W N : ℝ) * B.ell N (firstTime N) * etaT 0 (firstTime N) ≤ N ∧
      (d.W N : ℝ) * (d.L N : ℝ) ≤ N ∧
      (N : ℝ) ≤ (d.W N : ℝ) ^ 2 := by
  have hlogEv : ∀ᶠ N : ℕ in atTop,
      Real.exp (57600 : ℝ) ≤ (d.W N : ℝ) :=
    B.eventually_le_W (Real.exp (57600 : ℝ))
  have hdim := d.dim
  have hbw := d.bandwidth
  filter_upwards [hlogEv, hdim, hbw, eventually_ge_atTop 81] with
    N hWlarge hdimN hbwN hN
  have hNr : (81 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hWpos : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hL3 : (3 : ℝ) ≤ d.L N := by exact_mod_cast d.three_le_L N
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by exact_mod_cast hdimN.1
  have hWN : (d.W N : ℝ) ≤ N := by
    nlinarith [mul_nonneg (le_of_lt hWpos) (show (0 : ℝ) ≤ (d.L N : ℝ) - 1 by linarith)]
  have hlog : (57600 : ℝ) ≤ Real.log (d.W N : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos _) hWlarge
    simpa using hh
  have hW2 : (2 : ℝ) ≤ d.W N := by
    have he : (2 : ℝ) ≤ Real.exp (57600 : ℝ) := by
      calc (2 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
        _ ≤ Real.exp (57600 : ℝ) := Real.exp_le_exp.mpr (by norm_num)
    exact he.trans hWlarge
  have hη : etaT 0 (firstTime N) = 1 - firstTime N := by
    norm_num [etaT, Gauss.mE_zero]
  have hmem := firstTime_mem N (by omega)
  have hηhalf : (1 / 2 : ℝ) ≤ etaT 0 (firstTime N) := by
    rw [hη]
    linarith [hmem.2]
  have hηN : (N : ℝ)⁻¹ ≤ etaT 0 (firstTime N) := by
    have hi : (N : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
      rw [← one_div]
      exact (div_le_iff₀ (by linarith : (0 : ℝ) < N)).2 (by linarith)
    linarith
  have hℓ : 1 ≤ B.ell N (firstTime N) :=
    one_le_ellHat (d.L N) (d.three_le_L N) hmem.1 (by linarith [hmem.2])
  have hA1 : 1 ≤ (d.W N : ℝ) * B.ell N (firstTime N) * etaT 0 (firstTime N) := by
    calc
      (1 : ℝ) = 2 * 1 * (1 / 2) := by norm_num
      _ ≤ (d.W N : ℝ) * B.ell N (firstTime N) * etaT 0 (firstTime N) := by
        gcongr
  have hηℓ : etaT 0 (firstTime N) * B.ell N (firstTime N) ≤ 1 := by
    exact etaT_mul_ellHat_le (L := d.L N) (d.three_le_L N)
      (by norm_num : |(0 : ℝ)| ≤ 2)
      hmem.1 (by linarith [hmem.2])
  have hAN : (d.W N : ℝ) * B.ell N (firstTime N) * etaT 0 (firstTime N) ≤ N := by
    calc
      _ = (d.W N : ℝ) * (etaT 0 (firstTime N) * B.ell N (firstTime N)) := by ring
      _ ≤ (d.W N : ℝ) * 1 := mul_le_mul_of_nonneg_left hηℓ hWpos.le
      _ = (d.W N : ℝ) := by ring
      _ ≤ N := hWN
  have hbw' : (N : ℝ) ^ ((5 : ℝ) / 8) ≤ (d.W N : ℝ) := by
    convert hbwN using 1 <;> norm_num [d, Gauss.Dims.exampleGrow_c]
  have hNW : (N : ℝ) ≤ (d.W N : ℝ) ^ 2 := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ ((5 : ℝ) / 4) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = ((N : ℝ) ^ ((5 : ℝ) / 8)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        ring
      _ ≤ (d.W N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hbw' 2
  exact ⟨(Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 57600) |>.trans hWlarge),
    by linarith, by norm_num at hlog ⊢; linarith, hN1, hηN, hA1, hAN, hWL, hNW⟩

#print axioms eventually_firstTime_T334_scales

/-- The T348 source, first active smooth weight, and actual block cap hold on one
Gaussian sample at the same strictly positive time. -/
theorem exists_positive_time_firstCell_jG_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ N : ℕ in atTop, ∃ ω : Gauss.Ω d,
        ‖Xmat d N ω‖ ≤ (N : ℝ) ∧
        0 < firstTime N ∧
        firstTime N ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) ∧
        sourceEll ζ N < 1 ∧
        (∀ p : ℕ, APrimeSmoothWeightActual.weight d 0 60 δ
          (firstCellS τ') (firstCellT τ')
          (fun M => (max 1 M : ℝ) ^ (248 : ℕ)) 2 p N 2 N ω = 1) ∧
        APrimeFullQV.SourceEvent (Gauss.sample d) 0 N (firstTime N) ω
          (sourceEll ζ N) (sourceC4 ζ N) ∧
        APrimeJG.jG (Gauss.sample d) 0 N (firstTime N) ω
          (B.ell N (firstTime N)) (etaT 0 (firstTime N)) 60 ≤ (N : ℝ) := by
  obtain ⟨τ', hτ', hw⟩ := APrimeFirstCellCommon.exists_positive_time_firstCell_witness
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ δ hδ
  filter_upwards [hw ζ hζ δ hδ, eventually_jG_le_N_of_norm,
    eventually_ge_atTop 81] with N hwN hcap hN
  obtain ⟨ω, hω, _hmeas, hhpos, hhmem, hell, hweight, hsource⟩ := hwN
  have hnorm : ‖Xmat d N ω‖ ≤ (N : ℝ) := hω.1.1.1
  have htime : 0 < firstTime N := by
    unfold firstTime
    positivity
  have hEq : ((max 1 N : ℝ) ^ (248 : ℕ))⁻¹ = firstTime N := by
    rw [max_eq_right (by exact_mod_cast (by omega : 1 ≤ N))]
    rfl
  have hmem : firstTime N ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) := by
    change ((max 1 N : ℝ) ^ (248 : ℕ))⁻¹ ∈
      Set.Icc (firstCellS τ' N) (firstCellT τ' N) at hhmem
    rw [hEq] at hhmem
    exact hhmem
  have hell' : sourceEll ζ N < 1 := by
    change (2 * (N : ℝ) ^ ζ) ^ (-(1 / 5 : ℝ)) < 1 at hell
    exact hell
  refine ⟨ω, hnorm, htime, hmem, hell', ?_, ?_, hcap ω hnorm⟩
  · exact hweight
  · change APrimeFullQV.SourceEvent (Gauss.sample d) 0 N
        (((max 1 N : ℝ) ^ (248 : ℕ))⁻¹) ω
        ((2 * (N : ℝ) ^ ζ) ^ (-(1 / 5 : ℝ)))
        ((N : ℝ) ^ ζ * (B.ell N (((max 1 N : ℝ) ^ (248 : ℕ))⁻¹)) ^ (3 : ℕ) *
          ((B.scale 0 N (((max 1 N : ℝ) ^ (248 : ℕ))⁻¹))⁻¹) ^ (3 : ℕ)) at hsource
    rw [hEq] at hsource
    change APrimeFullQV.SourceEvent (Gauss.sample d) 0 N (firstTime N) ω
      (sourceEll ζ N) (sourceC4 ζ N) at hsource
    exact hsource

#print axioms exists_positive_time_firstCell_jG_witness

end RBM.APrimeFirstCellJGCap
