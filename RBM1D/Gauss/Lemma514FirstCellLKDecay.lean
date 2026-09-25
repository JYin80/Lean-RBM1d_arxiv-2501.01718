/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellCTDecay
import RBM1D.Gauss.APrimeFirstCellJGActual
import RBM1D.Hierarchy.DecayBridge

/-!
# T1349: actual first-half all-charge loop decay

On the actual growing Gaussian model, the first-cell Combes--Thomas entry bound gives the
all-charge loop decay of Lemma 5.9 on the same measurable high-probability event, uniformly for
the whole interval `[0, 1/2]`.
-/

namespace RBM.Gauss.Lemma514FirstCellLKDecay

open Filter MeasureTheory Real

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

private theorem eventually_const_exp_le_rpow_neg (C c τ D : ℝ)
    (hc : 0 < c) (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.exp (-(c * (N : ℝ) ^ τ)) ≤ (N : ℝ) ^ (-D) := by
  have hsmall := SumZeroDyn.eventually_exp_small C D c hc hτ
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hNsmall hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hpow : (N : ℝ) ^ D * (N : ℝ) ^ (-D) = 1 := by
    rw [← Real.rpow_add hN0]
    simp
  have hsmall' : C * Real.exp (-(c * (N : ℝ) ^ τ)) * (N : ℝ) ^ D ≤ 1 := by
    calc
      C * Real.exp (-(c * (N : ℝ) ^ τ)) * (N : ℝ) ^ D =
          C * (N : ℝ) ^ D * Real.exp (-(c * (N : ℝ) ^ τ)) := by ring
      _ ≤ 1 := hNsmall
  calc
    C * Real.exp (-(c * (N : ℝ) ^ τ)) =
        (C * Real.exp (-(c * (N : ℝ) ^ τ)) * (N : ℝ) ^ D) * (N : ℝ) ^ (-D) := by
          calc
            _ = (C * Real.exp (-(c * (N : ℝ) ^ τ))) * 1 := by simp
            _ = (C * Real.exp (-(c * (N : ℝ) ^ τ))) *
                ((N : ℝ) ^ D * (N : ℝ) ^ (-D)) := by rw [hpow]
            _ = _ := by ring
    _ ≤ 1 * (N : ℝ) ^ (-D) :=
      mul_le_mul_of_nonneg_right hsmall' (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ (-D) := one_mul _

/-- The raw `G` loops and their difference from the primitive loop decay on the actual common
first-cell event, simultaneously for every time in the closed half interval. -/
theorem eventually_loopDecay_pair_on_first_half_good
    (m : ℕ) (hm : 1 ≤ m) {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellJGAllTime.good N,
        ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
          Decay.LoopDecay ((Gauss.band d).L N) m
            ((Gauss.band d).ell N u * (N : ℝ) ^ τ)
            ((N : ℝ) ^ (-D))
            (gloop ((Gauss.band d).L N) ((Gauss.band d).W N)
              ((Gauss.sample d).H N u ω) (zt 0 u)) ∧
          Decay.LoopDecay ((Gauss.band d).L N) m
            ((Gauss.band d).ell N u * (N : ℝ) ^ τ)
            ((N : ℝ) ^ (-D))
            (gloop ((Gauss.band d).L N) ((Gauss.band d).W N)
              ((Gauss.sample d).H N u ω) (zt 0 u) -
              (Gauss.band d).Kval 0 N u) := by
  let α : ℝ := APrimeFirstCellJGAllTime.ctAlpha
  let cG : ℝ := α / (2 * (m : ℝ))
  let cK : ℝ := cor35Rate (1 / 2 : ℝ)
  let CG : ℝ := 4 * (2 : ℝ) ^ m
  let CK : ℝ := Decay.cKdecay m (1 / 2 : ℝ)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hcG : 0 < cG := by
    dsimp [cG, α]
    exact div_pos APrimeFirstCellJGAllTime.ctAlpha_pos (by positivity)
  have hcK : 0 < cK := by
    dsimp [cK, cor35Rate]
    have := cZero_pos
    positivity
  have hCG : 0 ≤ CG := by positivity
  have hCK : 0 ≤ CK := by
    dsimp [CK, Decay.cKdecay]
    have hsum : 0 ≤ ∑ n ∈ Finset.range (m + 1), cor35Const n (1 / 2 : ℝ) :=
      Finset.sum_nonneg fun n _ => cor35Const_nonneg n (by norm_num)
    have hc := cTwo52_pos
    positivity
  have hrawSmall := eventually_const_exp_le_rpow_neg (2 * CG) cG τ (D + 1) hcG hτ
  have hKSmall := eventually_const_exp_le_rpow_neg (2 * CK) cK τ (D + 1) hcK hτ
  have htwo := eventually_two_mul_rpow_le D
  have hN1 : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  filter_upwards [hrawSmall, hKSmall, htwo, hN1] with N hrawSmallN hKSmallN htwoN hN
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNp : 0 ≤ (N : ℝ) ^ τ := Real.rpow_nonneg hNr.le _
  intro ω hω u hu
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (by norm_num)
  have hL3 : 3 ≤ (B.L N) := B.three_le_L N
  have hWpos : 0 < B.W N := B.W_pos N
  let L : ℕ := B.L N
  let W : ℕ := B.W N
  let H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
    (Gauss.sample d).H N u ω
  let z : ℂ := zt 0 u
  have hL3' : 3 ≤ L := by dsimp [L]; exact hL3
  have hWpos' : 0 < W := by dsimp [W]; exact hWpos
  letI : NeZero L := ⟨by omega⟩
  letI : NeZero W := ⟨by omega⟩
  have hH : H.IsHermitian := by
    dsimp [H]
    exact (Gauss.sample d).hermitian N u ω
  have hm0 : mE 0 = Complex.I := by
    rw [mE]
    norm_num
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    push_cast
    ring
  have him : z.im = 1 - u := by
    dsimp [z]
    rw [zt_im, hm0]
    norm_num
  have hz : z.im ≠ 0 := by rw [him]; linarith
  have hell1 : 1 ≤ B.ell N u := by
    dsimp [Band.ell]
    exact one_le_ellHat_of_nonneg (by omega : 1 ≤ L) hu0 hu1
  let R : ℝ := (B.ell N u * (N : ℝ) ^ τ) / (2 * (m : ℝ))
  have hR : 0 < R := by
    dsimp [R]
    exact div_pos (mul_pos (lt_of_lt_of_le one_pos hell1) (Real.rpow_pos_of_pos hNr _))
      (by positivity)
  have hInv : |z.im|⁻¹ ≤ 2 := by
    rw [him, abs_of_pos (by linarith : 0 < 1 - u)]
    have hhalf : (2 : ℝ)⁻¹ ≤ 1 - u := by norm_num at hu ⊢; linarith
    exact (inv_le_comm₀ (by linarith : 0 < 1 - u) (by norm_num : (0 : ℝ) < 2)).2 hhalf
  have hmax : max 1 |z.im|⁻¹ ≤ 2 := max_le (by norm_num) hInv
  have hpowMax : max 1 |z.im|⁻¹ ^ m ≤ (2 : ℝ) ^ m :=
    pow_le_pow_left₀ (by positivity) hmax _
  have hscale : (2 : ℝ) * (m : ℝ) * R = B.ell N u * (N : ℝ) ^ τ := by
    dsimp [R]
    field_simp
  have hGentry : ∀ (sigma : Bool) (x y : ZMod L × Fin W),
      R ≤ (zdist L (x.1 - y.1) : ℝ) → ‖Gsig H z sigma x y‖ ≤ 4 * Real.exp (-α * R) := by
    intro sigma x y hxy
    have hentry := APrimeFirstCellCTDecay.Gsig_entry_decay_on_good N u ω hu hω
      sigma x.1 y.1 x.2 y.2
    dsimp [H, z, α, L, W] at hentry ⊢
    have harg : -APrimeFirstCellJGAllTime.ctAlpha *
          (zdist ((Gauss.band d).L N) (x.1 - y.1) : ℝ) ≤
        -APrimeFirstCellJGAllTime.ctAlpha * R := by
      have hmul := mul_le_mul_of_nonneg_left hxy APrimeFirstCellJGAllTime.ctAlpha_pos.le
      nlinarith
    calc
      ‖Gsig ((Gauss.sample d).H N u ω) (zt 0 u) sigma x y‖ ≤
          4 * Real.exp (-APrimeFirstCellJGAllTime.ctAlpha *
            (zdist ((Gauss.band d).L N) (x.1 - y.1) : ℝ)) := hentry
      _ ≤ 4 * Real.exp (-APrimeFirstCellJGAllTime.ctAlpha * R) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
  have hgl := Decay.loopDecay_gloop (L := L) (W := W) (H := H) (z := z) hH hz hR
    (by positivity : 0 ≤ 4 * Real.exp (-α * R)) hGentry m
  have hraw0 : Decay.LoopDecay L m
      (B.ell N u * (N : ℝ) ^ τ)
      (4 * Real.exp (-α * R) * max 1 |z.im|⁻¹ ^ m)
      (gloop L W H z) := by
    simpa [hscale] using hgl
  have hargG : -α * R ≤ -(cG * (N : ℝ) ^ τ) := by
    have heq : α * R = cG * B.ell N u * (N : ℝ) ^ τ := by
      dsimp [R, cG, α]
      field_simp
    have hneg : -α * R = -(α * R) := by ring
    rw [hneg, heq]
    have hrad : (1 : ℝ) * (N : ℝ) ^ τ ≤ B.ell N u * (N : ℝ) ^ τ :=
      mul_le_mul_of_nonneg_right hell1 hNp
    have hrate : cG * (N : ℝ) ^ τ ≤ cG * B.ell N u * (N : ℝ) ^ τ := by
      calc
        cG * (N : ℝ) ^ τ = cG * (1 * (N : ℝ) ^ τ) := by ring
        _ ≤ cG * (B.ell N u * (N : ℝ) ^ τ) :=
          mul_le_mul_of_nonneg_left hrad hcG.le
        _ = cG * B.ell N u * (N : ℝ) ^ τ := by ring
    exact neg_le_neg hrate
  have hrawExp : 4 * Real.exp (-α * R) * max 1 |z.im|⁻¹ ^ m ≤
      CG * Real.exp (-(cG * (N : ℝ) ^ τ)) := by
    calc
      4 * Real.exp (-α * R) * max 1 |z.im|⁻¹ ^ m ≤
          4 * Real.exp (-α * R) * (2 : ℝ) ^ m := by
            exact mul_le_mul_of_nonneg_left hpowMax (by positivity)
      _ = CG * Real.exp (-α * R) := by dsimp [CG]; ring
      _ ≤ CG * Real.exp (-(cG * (N : ℝ) ^ τ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hargG) hCG
  have hrawErr : 4 * Real.exp (-α * R) * max 1 |z.im|⁻¹ ^ m ≤
      (N : ℝ) ^ (-(D + 1)) := by
    have hsmall : CG * Real.exp (-(cG * (N : ℝ) ^ τ)) ≤ (N : ℝ) ^ (-(D + 1)) := by
      have hx : 0 ≤ CG * Real.exp (-(cG * (N : ℝ) ^ τ)) :=
        mul_nonneg hCG (Real.exp_pos _).le
      nlinarith [hrawSmallN, hx]
    exact hrawExp.trans hsmall
  have hmSigma : ∀ s : Bool, ‖mSigma 0 s‖ ≤ 1 := by
    intro s
    exact (norm_mSigma (by norm_num : |(0 : ℝ)| ≤ 2) s).le
  have hKbase := Decay.loopDecay_Kgen L hL3' W hmSigma hu0 hu1
    (δ := 1 / 2) (by norm_num)
      (fun s s' => by
      have hgap := Decay.one_sub_le_norm_one_sub hmSigma hu0 s s'
      have htime : (1 / 2 : ℝ) ≤ 1 - u := by linarith [hu.2]
      exact le_trans htime hgap)
    m (by positivity : 0 < B.ell N u * (N : ℝ) ^ τ)
  have hK0 : Decay.LoopDecay L m (B.ell N u * (N : ℝ) ^ τ)
      (CK * Real.exp (-(cK * (B.ell N u * (N : ℝ) ^ τ))))
      (B.Kval 0 N u) := by
    change Decay.LoopDecay L m (B.ell N u * (N : ℝ) ^ τ)
      (Decay.cKdecay m (1 / 2 : ℝ) *
        Real.exp (-(cor35Rate (1 / 2 : ℝ) * (B.ell N u * (N : ℝ) ^ τ))))
      (Kgen L W (mSigma 0) u)
    exact hKbase
  have hargK : -(cK * (B.ell N u * (N : ℝ) ^ τ)) ≤ -(cK * (N : ℝ) ^ τ) := by
    have hrad : (1 : ℝ) * (N : ℝ) ^ τ ≤ B.ell N u * (N : ℝ) ^ τ :=
      mul_le_mul_of_nonneg_right hell1 hNp
    have hrate : cK * (N : ℝ) ^ τ ≤ cK * (B.ell N u * (N : ℝ) ^ τ) := by
      calc
        cK * (N : ℝ) ^ τ = cK * (1 * (N : ℝ) ^ τ) := by ring
        _ ≤ cK * (B.ell N u * (N : ℝ) ^ τ) :=
          mul_le_mul_of_nonneg_left hrad hcK.le
    exact neg_le_neg hrate
  have hKExp : CK * Real.exp (-(cK * (B.ell N u * (N : ℝ) ^ τ))) ≤
      CK * Real.exp (-(cK * (N : ℝ) ^ τ)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hargK) hCK
  have hKErr : CK * Real.exp (-(cK * (B.ell N u * (N : ℝ) ^ τ))) ≤
      (N : ℝ) ^ (-(D + 1)) := by
    have hsmall : CK * Real.exp (-(cK * (N : ℝ) ^ τ)) ≤ (N : ℝ) ^ (-(D + 1)) := by
      have hx : 0 ≤ CK * Real.exp (-(cK * (N : ℝ) ^ τ)) :=
        mul_nonneg hCK (Real.exp_pos _).le
      nlinarith [hKSmallN, hx]
    exact hKExp.trans hsmall
  have hK := hK0.mono L le_rfl le_rfl hKErr
  have hpowExp : (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith : -(D + 1) ≤ -D)
  have hRaw := hraw0.mono L le_rfl le_rfl (hrawErr.trans hpowExp)
  have hdiff0 := hraw0.sub L hK0
  have hdiff := hdiff0.mono L le_rfl le_rfl (by
    calc
      4 * Real.exp (-α * R) * max 1 |z.im|⁻¹ ^ m +
          CK * Real.exp (-(cK * (B.ell N u * (N : ℝ) ^ τ)))
          ≤ (N : ℝ) ^ (-(D + 1)) + (N : ℝ) ^ (-(D + 1)) :=
            add_le_add hrawErr hKErr
      _ = 2 * (N : ℝ) ^ (-(D + 1)) := by ring
      _ ≤ (N : ℝ) ^ (-D) := htwoN)
  refine ⟨?_, ?_⟩
  · simpa [L, W, H, z] using hRaw
  · simpa [L, W, H, z] using hdiff

/-- The common first-cell event is measurable at every size. -/
theorem measurableSet_first_half_good (N : ℕ) :
    MeasurableSet (APrimeFirstCellJGAllTime.good N) :=
  APrimeFirstCellJGAllTime.measurableSet_good N

/-- The common first-cell event has high probability for the actual growing Gaussian model. -/
theorem highProb_first_half_good :
    HighProb (Gauss.P d) APrimeFirstCellJGAllTime.good :=
  APrimeFirstCellJGActual.highProb_good

/-- In particular, the common event has positive probability eventually. -/
theorem eventually_positive_probability_first_half_good :
    ∀ᶠ N : ℕ in atTop, 0 < (Gauss.P d) (APrimeFirstCellJGAllTime.good N) := by
  letI := Gauss.isProbabilityMeasure_P d
  have hhp := APrimeFirstCellJGActual.highProb_good 1 (by norm_num)
  filter_upwards [hhp, eventually_ge_atTop 2] with N hhp hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hpow : (N : ℝ) ^ (-1 : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hNreal (by norm_num)
  have hcompl : (Gauss.P d) (APrimeFirstCellJGAllTime.good N)ᶜ < 1 :=
    lt_of_le_of_lt hhp (ENNReal.ofReal_lt_one.2 hpow)
  by_contra hnot
  have hz : (Gauss.P d) (APrimeFirstCellJGAllTime.good N) = 0 :=
    le_antisymm (le_of_not_gt hnot) bot_le
  have hsum := MeasureTheory.measure_add_measure_compl (μ := Gauss.P d)
    (APrimeFirstCellJGAllTime.measurableSet_good N)
  have hcompl_eq : (Gauss.P d) (APrimeFirstCellJGAllTime.good N)ᶜ = 1 := by
    simpa [hz] using hsum
  rw [hcompl_eq] at hcompl
  exact (lt_irrefl 1) hcompl

/-- The literal `E=0`, `[0,1/2]` instance of the paper's `LKDecay` interface for the actual
growing Gaussian model. -/
theorem lkDecay_first_half_exampleGrow :
    SumZeroDyn.LKDecay (Gauss.sample d) 0 (fun _ => 0) (fun _ => 1 / 2) := by
  apply DecayBridge.lkDecay_of_highProb
  intro m hm τ hτ D hD
  apply APrimeFirstCellJGActual.highProb_good.mono
  filter_upwards [eventually_loopDecay_pair_on_first_half_good m hm hτ hD]
    with N hdec ω hω
  intro u
  have hu : (u : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨u.2.1, u.2.2⟩
  exact (hdec ω hω (u : ℝ) hu).2

private theorem nat_le_growL_add_one_pow_four (N : ℕ) :
    N ≤ (Gauss.Dims.growL N + 1) ^ 4 := by
  let q := Nat.sqrt N
  let r := Nat.sqrt q
  have hNq : N ≤ (q + 1) ^ 2 := by
    have h := (Nat.lt_succ_sqrt' N).le
    simpa [q, Nat.succ_eq_add_one] using h
  have hqr : q + 1 ≤ (r + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' q
    simpa [r, Nat.succ_eq_add_one] using h
  have hrL : r ≤ Gauss.Dims.growL N := by
    dsimp [r, q, Gauss.Dims.growL]
    exact le_max_right _ _
  calc
    N ≤ (q + 1) ^ 2 := hNq
    _ ≤ ((r + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hqr 2
    _ = (r + 1) ^ 4 := by ring
    _ ≤ (Gauss.Dims.growL N + 1) ^ 4 :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hrL 1) 4

private theorem eventually_first_half_radius_le_half_block :
    ∀ᶠ N : ℕ in atTop,
      20 ≤ B.L N ∧
        B.ell N (1 / 4) * (N : ℝ) ^ ((1 : ℝ) / 16) ≤ ((B.L N / 2 : ℕ) : ℝ) := by
  have hlarge : ∀ᶠ N : ℕ in atTop, 20 ≤ B.L N := by
    simpa [B, d, Gauss.band_L, Gauss.Dims.exampleGrow_L] using
      (tendsto_atTop.1 Gauss.Dims.tendsto_growL 20)
  filter_upwards [hlarge] with N hL
  have hNboundNat := nat_le_growL_add_one_pow_four N
  have hNbound : (N : ℝ) ≤ ((B.L N + 1 : ℕ) : ℝ) ^ 4 := by
    exact_mod_cast (by
      simpa [B, d, Gauss.band_L, Gauss.Dims.exampleGrow_L] using hNboundNat)
  have hroot : (N : ℝ) ^ ((1 : ℝ) / 16) ≤
      ((B.L N + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg N) hNbound
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 16)
    have heq : (((B.L N + 1 : ℕ) : ℝ) ^ 4) ^ ((1 : ℝ) / 16) =
        ((B.L N + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      norm_num
    exact h.trans_eq heq
  have hLreal : (20 : ℝ) ≤ (B.L N : ℝ) := by exact_mod_cast hL
  have hLnonneg : (0 : ℝ) ≤ (B.L N : ℝ) := by linarith
  have hLcube : (20 : ℝ) ^ 3 ≤ (B.L N : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hLreal 3
  have hLfour : (20 : ℝ) ^ 3 * (B.L N : ℝ) ≤ (B.L N : ℝ) ^ 4 := by
    calc
      (20 : ℝ) ^ 3 * (B.L N : ℝ) ≤ (B.L N : ℝ) ^ 3 * (B.L N : ℝ) :=
        mul_le_mul_of_nonneg_right hLcube (le_trans (by norm_num) hLreal)
      _ = (B.L N : ℝ) ^ 4 := by ring
  have hlargePow : (4096 : ℝ) * ((B.L N : ℝ) + 1) ≤ (B.L N : ℝ) ^ 4 := by
    nlinarith [hLfour, hLreal]
  have hbase : (B.L N : ℝ) + 1 ≤ ((B.L N : ℝ) / 8) ^ 4 := by
    calc
      (B.L N : ℝ) + 1 ≤ (B.L N : ℝ) ^ 4 / 4096 :=
        (le_div_iff₀ (by norm_num : (0 : ℝ) < 4096)).2 (by simpa [mul_comm] using hlargePow)
      _ = ((B.L N : ℝ) / 8) ^ 4 := by rw [div_pow]; norm_num
  have hLquarter : ((B.L N + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤
      (B.L N : ℝ) / 8 := by
    have h := Gauss.rpow_div_le_of_pow_le
      (x := (B.L N : ℝ) + 1) (y := (B.L N : ℝ) / 8)
      (by positivity) (by positivity) (m := 1) (n := 4) (by norm_num)
      (by simpa using hbase)
    simpa using h
  have hNquarter : (N : ℝ) ^ ((1 : ℝ) / 16) ≤ (B.L N : ℝ) / 8 :=
    hroot.trans hLquarter
  have hell : B.ell N (1 / 4) ≤ 2 := by
    change ellHat (B.L N) ((1 / 4 : ℝ) : ℂ) ≤ 2
    calc
      ellHat (B.L N) ((1 / 4 : ℝ) : ℂ) ≤ 1 / √(1 - (1 / 4 : ℝ)) :=
        ellHat_real_le_inv_sqrt (L := B.L N) (by norm_num)
      _ = 1 / √(3 / 4 : ℝ) := by congr 1; norm_num
      _ ≤ 1 / (1 / 2 : ℝ) := by
        have hsqrt : (1 / 2 : ℝ) ≤ √(3 / 4 : ℝ) :=
          (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
        exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hsqrt
      _ = 2 := by norm_num
  have hNpow : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hrad : B.ell N (1 / 4) * (N : ℝ) ^ ((1 : ℝ) / 16) ≤
      (B.L N : ℝ) / 4 := by
    calc
      B.ell N (1 / 4) * (N : ℝ) ^ ((1 : ℝ) / 16) ≤
          2 * (N : ℝ) ^ ((1 : ℝ) / 16) := mul_le_mul_of_nonneg_right hell hNpow
      _ ≤ 2 * ((B.L N : ℝ) / 8) := by nlinarith [hNquarter]
      _ = (B.L N : ℝ) / 4 := by ring
  have hfloor : B.L N ≤ 4 * (B.L N / 2) := by omega
  have hfloorR : (B.L N : ℝ) / 4 ≤ ((B.L N / 2 : ℕ) : ℝ) := by
    have hfloat : (B.L N : ℝ) ≤ 4 * ((B.L N / 2 : ℕ) : ℝ) := by exact_mod_cast hfloor
    nlinarith
  exact ⟨hL, hrad.trans hfloorR⟩

/-- A concrete nonzero sample on the same event carries the two loop-decay conclusions at
`u=1/4`, `m=2`, `τ=1/16`, and `D=1`; the two blocks are at cyclic distance `⌊L/2⌋`. -/
theorem eventually_joint_nonzero_far_witness :
    ∀ᶠ N : ℕ in atTop,
      ∃ ω : Gauss.Ω d,
        ω ∈ APrimeFirstCellJGAllTime.good N ∧
        Xmat d N ω ≠ 0 ∧
        ∃ a : LoopArg (B.L N) 2,
          a 0 ≠ a 1 ∧
          B.ell N (1 / 4) * (N : ℝ) ^ ((1 : ℝ) / 16) ≤
            (zdist (B.L N) (a 0 - a 1) : ℝ) ∧
          0 < B.ell N (1 / 4) * (N : ℝ) ^ ((1 : ℝ) / 16) ∧
          0 < (N : ℝ) ^ (-1 : ℝ) ∧
          Decay.LoopDecay (B.L N) 2
            (B.ell N (1 / 4) * (N : ℝ) ^ ((1 : ℝ) / 16)) ((N : ℝ) ^ (-1 : ℝ))
            (gloop (B.L N) (B.W N) ((Gauss.sample d).H N (1 / 4) ω) (zt 0 (1 / 4))) ∧
          Decay.LoopDecay (B.L N) 2
            (B.ell N (1 / 4) * (N : ℝ) ^ ((1 : ℝ) / 16)) ((N : ℝ) ^ (-1 : ℝ))
            (gloop (B.L N) (B.W N) ((Gauss.sample d).H N (1 / 4) ω) (zt 0 (1 / 4)) -
              (B.Kval 0 N (1 / 4)) ) := by
  filter_upwards [eventually_first_half_radius_le_half_block,
    eventually_loopDecay_pair_on_first_half_good 2 (by norm_num)
      (τ := (1 : ℝ) / 16) (D := 1) (by norm_num) (by norm_num)]
    with N hgeom hdec
  obtain ⟨ω, hω, hX⟩ := APrimeFirstCellBlockUnionPrep.exists_nonzero_mem_good N
  letI : NeZero (B.L N) := ⟨by omega⟩
  let a : LoopArg (B.L N) 2 := ![((B.L N / 2 : ℕ) : ZMod (B.L N)), 0]
  have ha0 : a 0 = ((B.L N / 2 : ℕ) : ZMod (B.L N)) := by simp [a]
  have ha1 : a 1 = 0 := rfl
  have hhalfLt : B.L N / 2 < B.L N := Nat.div_lt_self (by omega) (by norm_num)
  have hdistNat : zdist (B.L N) (a 0 - a 1) = B.L N / 2 := by
    rw [ha0, ha1, sub_zero, zdist, ZMod.val_cast_of_lt hhalfLt]
    exact min_eq_left (by omega)
  have hab : a 0 ≠ a 1 := by
    intro hab
    have hzero : zdist (B.L N) (a 0 - a 1) = 0 := by
      rw [hab, sub_self]
      exact zdist_zero _
    rw [hdistNat] at hzero
    omega
  have hfar : B.ell N (1 / 4) * (N : ℝ) ^ ((1 : ℝ) / 16) ≤
      (zdist (B.L N) (a 0 - a 1) : ℝ) := by
    rw [hdistNat]
    exact hgeom.2
  have hpair := hdec ω hω (1 / 4) (by norm_num)
  have hposN : 0 < (N : ℝ) := by
    have hroot : 20 ≤ Nat.sqrt (Nat.sqrt N) := by
      have hh : 20 ≤ max 3 (Nat.sqrt (Nat.sqrt N)) := by
        simpa [B, d, Gauss.band_L, Gauss.Dims.exampleGrow_L, Gauss.Dims.growL] using hgeom.1
      omega
    have hsq : 20 ^ 2 ≤ Nat.sqrt N := (Nat.le_sqrt').1 hroot
    have hN : (20 ^ 2) ^ 2 ≤ N := (Nat.le_sqrt').1 hsq
    exact_mod_cast (show 0 < N by omega)
  have hellpos : 0 < B.ell N (1 / 4) := by
    change 0 < ellHat (B.L N) ((1 / 4 : ℝ) : ℂ)
    exact lt_of_lt_of_le one_pos
      (one_le_ellHat_of_nonneg (by omega) (by norm_num) (by norm_num))
  have hradius : 0 < B.ell N (1 / 4) * (N : ℝ) ^ ((1 : ℝ) / 16) :=
    mul_pos hellpos (Real.rpow_pos_of_pos hposN _)
  have herror : 0 < (N : ℝ) ^ (-1 : ℝ) := Real.rpow_pos_of_pos hposN _
  refine ⟨ω, hω, hX, a, hab, hfar, hradius, herror, ?_, ?_⟩
  · exact hpair.1
  · exact hpair.2

#print axioms eventually_loopDecay_pair_on_first_half_good
#print axioms measurableSet_first_half_good
#print axioms highProb_first_half_good
#print axioms eventually_positive_probability_first_half_good
#print axioms lkDecay_first_half_exampleGrow
#print axioms eventually_joint_nonzero_far_witness

end RBM.Gauss.Lemma514FirstCellLKDecay
