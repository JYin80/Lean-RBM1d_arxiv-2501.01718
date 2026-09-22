/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeQVRateTime
import RBM1D.Gauss.APrimeQVEndpoint

/-! # T378: polynomial envelope for the actual uncut evolved QV -/

namespace RBM.APrimeQVGlobalPoly

open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

/-- The actual two-edge propagator has a polynomial row bound, uniformly in
the endpoint label and the charge vector. -/
theorem ukerRow_le_ratio_sq (d : Gauss.Dims) {E : ℝ} (hE : |E| < 2)
    (N : ℕ) (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2)
    {u v : ℝ} (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    Gauss.ukerRow (xiOf (mSigma E) σ) (v : ℂ) a u
      ≤ ((1 - u) / (1 - v)) ^ 2 := by
  let f : Fin 2 → ZMod (d.L N) → ℝ :=
    fun i b => ‖edgeKer (d.L N) (xiOf (mSigma E) σ i)
      (u : ℂ) (v : ℂ) (a i) b‖
  have hden : 0 < 1 - v := by linarith
  have hrow (i : Fin 2) :
      ∑ b : ZMod (d.L N), f i b ≤ (1 - u) / (1 - v) := by
    have hξ : ‖xiOf (mSigma E) σ i‖ = 1 := norm_xiOf_mSigma hE.le σ i
    have ht : ‖(v : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv0, hξ, mul_one]
      exact hv1
    have h := sum_norm_edgeKer_row_le (d.L N) (d.three_le_L N)
      (ξ := xiOf (mSigma E) σ i) (s := (u : ℂ)) (t := (v : ℂ)) ht (a i)
    have hvξ : ‖(v : ℂ) * xiOf (mSigma E) σ i‖ = v := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv0, hξ, mul_one]
    have hdu : ‖((u : ℂ) - (v : ℂ)) * xiOf (mSigma E) σ i‖ = v - u := by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith), hξ, mul_one]
      ring
    rw [hvξ, hdu] at h
    change ∑ b : ZMod (d.L N), f i b ≤ _
    convert h using 1
    field_simp
    ring
  have hnonneg (i : Fin 2) : 0 ≤ ∑ b : ZMod (d.L N), f i b :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc
    Gauss.ukerRow (xiOf (mSigma E) σ) (v : ℂ) a u
      = ∑ b : LoopArg (d.L N) 2, ∏ i : Fin 2, f i (b i) := by
          exact Finset.sum_congr rfl fun b _ => by simp [f]
    _ = ∏ i : Fin 2, ∑ b : ZMod (d.L N), f i b := sum_prod_pi (d.L N) f
    _ ≤ ∏ _i : Fin 2, (1 - u) / (1 - v) :=
      Finset.prod_le_prod₀ (fun i _ => hnonneg i) (fun i _ => hrow i)
    _ = ((1 - u) / (1 - v)) ^ 2 := by simp [div_pow]

/-- The fixed endpoint scale absorbs both propagator edges before the QV
derivative is squared. -/
theorem inv_driftScale_mul_ukerRow_le (d : Gauss.Dims) {E D s u v : ℝ}
    (hE : |E| < 2) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hsu : s ≤ u)
    (huv : u ≤ v) (hv1 : v < 1) (N : ℕ)
    (hWN : (d.W N : ℝ) ≤ N)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) :
    (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
        Gauss.ukerRow (xiOf (mSigma E) σ) (v : ℂ) a u
      ≤ (N : ℝ) ^ D := by
  let R : ℝ := etaT E s / etaT E v
  let T : ℝ := Step2.tT (Gauss.band d) E N D v (zdist (d.L N) (a 0 - a 1))
  have hs1 : s < 1 := (hsu.trans huv).trans_lt hv1
  have hR1 : 1 ≤ R := by
    dsimp [R]
    rw [Step2.etaT_ratio hE]
    exact (le_div_iff₀ (by linarith : 0 < 1 - v)).2 (by linarith)
  have hR0 : 0 ≤ R := by linarith
  have hrow : Gauss.ukerRow (xiOf (mSigma E) σ) (v : ℂ) a u ≤ R ^ 2 := by
    have hden : 0 < 1 - v := by linarith
    have hRu : (1 - u) / (1 - v) ≤ R := by
      dsimp [R]
      rw [Step2.etaT_ratio hE]
      apply (div_le_div_iff₀ hden hden).2
      nlinarith [mul_nonneg (by linarith : 0 ≤ u - s) hden.le]
    exact (ukerRow_le_ratio_sq d hE N σ a huv
      (hs0.trans (hsu.trans huv)) hv1).trans
      (pow_le_pow_left₀ (div_nonneg (by linarith) hden.le) hRu 2)
  have hR24 : R ^ 2 ≤ R ^ 4 := by
    have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
    calc R ^ 2 = R ^ 2 * 1 := (mul_one _).symm
      _ ≤ R ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hR2 (sq_nonneg _)
      _ = R ^ 4 := by ring
  have hW0 : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hP0 : 0 ≤ (d.W N : ℝ) ^ D := Real.rpow_nonneg hW0.le _
  have hfloor : (d.W N : ℝ) ^ (-D) ≤ T := by
    dsimp [T, Step2.tT]
    exact rpow_neg_le_tailT _
  have hpow : (d.W N : ℝ) ^ D * (d.W N : ℝ) ^ (-D) = 1 := by
    rw [← Real.rpow_add hW0]
    simp
  have hPT : 1 ≤ (d.W N : ℝ) ^ D * T := by
    have h := mul_le_mul_of_nonneg_left hfloor hP0
    rw [← hpow]
    exact h
  have hT0 : 0 < T := by
    dsimp [T, Step2.tT]
    exact tailT_pos hW0 _
  have hc : 0 < APrimeDriftTimeFamily.driftScale d E D N a s v :=
    APrimeDriftTimeFamily.driftScale_pos d hE (hsu.trans huv) hv1 N a
  have hscale : APrimeDriftTimeFamily.driftScale d E D N a s v = T * R ^ 4 := rfl
  have hmain : Gauss.ukerRow (xiOf (mSigma E) σ) (v : ℂ) a u
      ≤ (d.W N : ℝ) ^ D * APrimeDriftTimeFamily.driftScale d E D N a s v := by
    calc
      _ ≤ R ^ 2 := hrow
      _ ≤ R ^ 4 := hR24
      _ = 1 * R ^ 4 := (one_mul _).symm
      _ ≤ ((d.W N : ℝ) ^ D * T) * R ^ 4 :=
        mul_le_mul_of_nonneg_right hPT (pow_nonneg hR0 _)
      _ = (d.W N : ℝ) ^ D * APrimeDriftTimeFamily.driftScale d E D N a s v := by
        rw [hscale]; ring
  have hdiv : (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
      Gauss.ukerRow (xiOf (mSigma E) σ) (v : ℂ) a u ≤ (d.W N : ℝ) ^ D := by
    calc
      _ = Gauss.ukerRow (xiOf (mSigma E) σ) (v : ℂ) a u /
          APrimeDriftTimeFamily.driftScale d E D N a s v := by ring
      _ ≤ _ := (div_le_iff₀ hc).2 hmain
  exact hdiv.trans (Real.rpow_le_rpow hW0.le hWN hD)

private theorem norm_single_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (c : ℂ) : ‖Matrix.single i j c‖ ≤ ‖c‖ := by
  rw [Matrix.cstar_norm_def]
  refine (Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.single i j c)).opNorm_le_bound
    (norm_nonneg c) ?_
  intro x
  have h := PiLp.norm_apply_le x j
  have heq : Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.single i j c) x =
      (c * x j) • (PiLp.single 2 i (1 : ℂ)) := by
    conv_lhs => rw [show x = WithLp.toLp 2 x.ofLp from rfl]
    rw [Matrix.toEuclideanCLM_toLp, Matrix.single_mulVec_eq]
    simp
  rw [heq, norm_smul, PiLp.norm_single, norm_one, mul_one, norm_mul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg c)

private theorem norm_Bmat_le_two (d : Gauss.Dims) (N : ℕ)
    (i j : d.Idx N) (b : Bool) : ‖Gauss.Bmat d N i j b‖ ≤ 2 := by
  classical
  by_cases hij : i = j
  · subst j
    have heq : Gauss.Bmat d N i i b =
        Matrix.single i i (if b then (1 : ℂ) else Complex.I) := by
      ext k l
      simp only [Gauss.Bmat_apply, Matrix.single_apply]
      by_cases hkl : k = i ∧ l = i
      · rcases hkl with ⟨rfl, rfl⟩
        simp
      · have hkl' : ¬(i = k ∧ i = l) := by simpa [eq_comm] using hkl
        simp [hkl, hkl']
    rw [heq]
    have h := norm_single_le i i (if b then (1 : ℂ) else Complex.I)
    have hc : ‖(if b then (1 : ℂ) else Complex.I)‖ ≤ 2 := by
      cases b <;> norm_num
    exact h.trans hc
  · have heq : Gauss.Bmat d N i j b =
        Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
          Matrix.single j i (if b then (1 : ℂ) else -Complex.I) := by
      ext k l
      simp only [Gauss.Bmat_apply, Matrix.add_apply, Matrix.single_apply]
      by_cases h₁ : k = i ∧ l = j
      · simp [h₁, hij, eq_comm]
      · by_cases h₂ : k = j ∧ l = i
        · simp [h₂, hij, eq_comm]
        · have h₁' : ¬(i = k ∧ j = l) := by simpa [eq_comm] using h₁
          have h₂' : ¬(j = k ∧ i = l) := by simpa [eq_comm] using h₂
          simp [h₁, h₂, h₁', h₂']
    rw [heq]
    have h₁ := norm_single_le i j (if b then (1 : ℂ) else Complex.I)
    have h₂ := norm_single_le j i (if b then (1 : ℂ) else -Complex.I)
    have hsum := norm_add_le
      (Matrix.single i j (if b then (1 : ℂ) else Complex.I))
      (Matrix.single j i (if b then (1 : ℂ) else -Complex.I))
    have hc₁ : ‖(if b then (1 : ℂ) else Complex.I)‖ = 1 := by
      cases b <;> norm_num
    have hc₂ : ‖(if b then (1 : ℂ) else -Complex.I)‖ = 1 := by
      cases b <;> norm_num
    rw [hc₁] at h₁
    rw [hc₂] at h₂
    linarith

private theorem gvar_le_one (d : Gauss.Dims) (N : ℕ)
    (i j : d.Idx N) (b : Bool) :
    (Gauss.gvar d ⟨N, i, j, b⟩ : ℝ) ≤ 1 := by
  have hS : Sblk (d.L N) (d.W N) i j ≤ 1 := by
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (d.Idx N)))
      (fun k _ => Sblk_nonneg i k) (Finset.mem_univ j)
    rw [sum_Sblk_row (d.three_le_L N) i] at hsingle
    exact hsingle
  by_cases hij : i = j
  · subst j
    simpa using hS
  · rw [Gauss.gvar_offDiag d N i j b hij]
    nlinarith [Sblk_nonneg i j]

/-- A deliberately coarse, dimension-explicit bound on the weighted matrix
directions appearing in the actual Gaussian quadratic variation. -/
theorem coordWt2_le (d : Gauss.Dims) (N : ℕ)
    (hM : (Fintype.card (d.Idx N) : ℝ) ≤ N) :
    APrimeDuhamelModel.coordWt2 d N ≤ 8 * (N : ℝ) ^ 2 := by
  classical
  have hcard : (Gauss.usedCoord d N).card ≤
      2 * (Fintype.card (d.Idx N)) ^ 2 := by
    calc
      (Gauss.usedCoord d N).card ≤
          (Finset.univ : Finset (d.Idx N × d.Idx N × Bool)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 * (Fintype.card (d.Idx N)) ^ 2 := by
        simp [Fintype.card_prod, Fintype.card_bool]
        ring
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hM0 : 0 ≤ (Fintype.card (d.Idx N) : ℝ) := Nat.cast_nonneg _
  have hcardR : ((Gauss.usedCoord d N).card : ℝ) ≤ 2 * (N : ℝ) ^ 2 := by
    have hcast : ((Gauss.usedCoord d N).card : ℝ) ≤
        2 * (Fintype.card (d.Idx N) : ℝ) ^ 2 := by exact_mod_cast hcard
    nlinarith [sq_nonneg ((N : ℝ) - Fintype.card (d.Idx N))]
  have hterm (q : d.Idx N × d.Idx N × Bool) :
      (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
        (‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ *
          ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖) ≤ 4 := by
    have hv : (Gauss.gvar d (Gauss.crd d N q) : ℝ) ≤ 1 :=
      gvar_le_one d N q.1 q.2.1 q.2.2
    have hv0 := (Gauss.gvar d (Gauss.crd d N q)).2
    have hB := norm_Bmat_le_two d N q.1 q.2.1 q.2.2
    have hB0 := norm_nonneg (Gauss.Bmat d N q.1 q.2.1 q.2.2)
    nlinarith [sq_nonneg (2 - ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖)]
  unfold APrimeDuhamelModel.coordWt2
  calc
    (∑ q ∈ Gauss.usedCoord d N,
      (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
        (‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ *
          ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖))
      ≤ ∑ _q ∈ Gauss.usedCoord d N, (4 : ℝ) :=
        Finset.sum_le_sum fun q _ => hterm q
    _ = 4 * ((Gauss.usedCoord d N).card : ℝ) := by simp; ring
    _ ≤ 8 * (N : ℝ) ^ 2 := by nlinarith

private theorem derivative_coefficient_le (d : Gauss.Dims) (N : ℕ)
    {E v Kη : ℝ} (hE : |E| < 2) (hv1 : v < 1) (hKη : 0 ≤ Kη)
    (hN : 1 ≤ (N : ℝ))
    (hM : (Fintype.card (d.Idx N) : ℝ) ≤ N)
    (hη : (N : ℝ) ^ (-Kη) ≤ etaT E v) :
    (Fintype.card (d.Idx N) : ℝ) *
        (2 * (2 * (1 + (etaT E v)⁻¹) ^ 3) ^ 2)
      ≤ 512 * (N : ℝ) ^ (1 + 6 * Kη) := by
  have hNpos : 0 < (N : ℝ) := by linarith
  have hηpos : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hηinv : (etaT E v)⁻¹ ≤ (N : ℝ) ^ Kη := by
    have h := inv_anti₀ (Real.rpow_pos_of_pos hNpos _) hη
    simpa only [Real.rpow_neg hNpos.le, inv_inv] using h
  have hNK : 1 ≤ (N : ℝ) ^ Kη := Real.one_le_rpow hN hKη
  have hbase : 1 + (etaT E v)⁻¹ ≤ 2 * (N : ℝ) ^ Kη := by linarith
  have hbase0 : 0 ≤ 1 + (etaT E v)⁻¹ := by positivity
  have hpow := pow_le_pow_left₀ hbase0 hbase 6
  have hM0 : 0 ≤ (Fintype.card (d.Idx N) : ℝ) := Nat.cast_nonneg _
  have hNK0 : 0 ≤ (N : ℝ) ^ Kη := Real.rpow_nonneg hNpos.le _
  calc
    (Fintype.card (d.Idx N) : ℝ) *
        (2 * (2 * (1 + (etaT E v)⁻¹) ^ 3) ^ 2)
      = 8 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E v)⁻¹) ^ 6 := by ring
    _ ≤ 8 * (N : ℝ) * (2 * (N : ℝ) ^ Kη) ^ 6 := by
      gcongr
    _ = 512 * (N : ℝ) ^ (1 + 6 * Kη) := by
      rw [mul_pow, show (2 : ℝ) ^ 6 = 64 by norm_num]
      have hp : ((N : ℝ) ^ Kη) ^ 6 = (N : ℝ) ^ (Kη * 6) := by
        rw [Real.rpow_mul hNpos.le, Real.rpow_ofNat]
      rw [hp]
      calc
        8 * (N : ℝ) * (64 * (N : ℝ) ^ (Kη * 6))
          = 512 * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (Kη * 6)) := by
              rw [Real.rpow_one]; ring
        _ = 512 * (N : ℝ) ^ (1 + 6 * Kη) := by
          rw [← Real.rpow_add hNpos]
          ring

/-- The matrix first derivative of the *actual* normalized evolved coordinate
is polynomially bounded on the entire closed time window. The primitive bound
is needed to invoke `bddC2C_ukerObsT`, but its numerical value is absent from
the first-derivative coefficient. -/
theorem fderiv_coordAt_le (d : Gauss.Dims) {E D Kη : ℝ} (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hD : 0 ≤ D) (hKη : 0 ≤ Kη)
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (hN : 1 ≤ (N : ℝ)) (hWN : (d.W N : ℝ) ≤ N)
    (hM : (Fintype.card (d.Idx N) : ℝ) ≤ N)
    (hη : (N : ℝ) ^ (-Kη) ≤ etaT E v) :
    ∀ r ∈ Set.Icc s v, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖fderiv ℝ (APrimeDriftTimeFamily.coordAt d E D N σ a s v r) M‖
        ≤ 512 * (N : ℝ) ^ (D + 1 + 6 * Kη) := by
  classical
  let row : ℝ → ℝ := Gauss.ukerRow (xiOf (mSigma E) σ) (v : ℂ) a
  let B : ℝ := (Fintype.card (d.Idx N) : ℝ) *
    (2 * (2 * (1 + (etaT E v)⁻¹) ^ 3) ^ 2)
  obtain ⟨cK, _hcK, hKb, _⟩ :=
    Gauss.exists_bdd_Kval_Kprim (d := d) E N hE.le hs0 hv1 (v := v) σ
  have hc : 0 < APrimeDriftTimeFamily.driftScale d E D N a s v :=
    APrimeDriftTimeFamily.driftScale_pos d hE hsv hv1 N a
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB : B ≤ 512 * (N : ℝ) ^ (1 + 6 * Kη) :=
    derivative_coefficient_le d N hE hv1 hKη hN hM hη
  have hN0 : 0 < (N : ℝ) := by linarith
  have hND0 : 0 ≤ (N : ℝ) ^ D := Real.rpow_nonneg hN0.le _
  intro r hr M
  have hraw := Gauss.bddC2C_ukerObsT (d := d) (N := N)
    (σ := List.ofFn σ) (m := 2) (Step2.etaT_pos' hE hv1)
    (Gauss.window_im_ne_zero hE hv1 r hr)
    (Gauss.window_le_abs_im hE hv1 r hr) (List.length_ofFn)
    (xiOf (mSigma E) σ) (v : ℂ)
    (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a
    (hKb r hr)
  have hraw1 :
      ‖fderiv ℝ (Gauss.ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ)
        (v : ℂ)
        (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r) M‖
        ≤ row r * B := by
    simpa only [row, B, Nat.cast_ofNat] using hraw.bdd₁ M
  have hnorm :
      ‖fderiv ℝ (APrimeDriftTimeFamily.coordAt d E D N σ a s v r) M‖ =
        (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
          ‖fderiv ℝ (Gauss.ukerObsT d N E (List.ofFn σ)
            (xiOf (mSigma E) σ) (v : ℂ)
            (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r) M‖ := by
    have heq : APrimeDriftTimeFamily.coordAt d E D N σ a s v r =
        (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ •
          Gauss.ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ)
            (v : ℂ)
            (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r := by
      funext M'
      change _ / ((APrimeDriftTimeFamily.driftScale d E D N a s v : ℝ) : ℂ) =
        (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ • _
      simp [Complex.real_smul, div_eq_mul_inv, Complex.ofReal_inv, mul_comm]
    rw [heq, fderiv_const_smul_field]
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hc)]
  have hscaleRow :
      (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ * row r
        ≤ (N : ℝ) ^ D :=
    inv_driftScale_mul_ukerRow_le d hE hD hs0 hr.1 hr.2 hv1 N hWN σ a
  calc
    ‖fderiv ℝ (APrimeDriftTimeFamily.coordAt d E D N σ a s v r) M‖
      = (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
          ‖fderiv ℝ (Gauss.ukerObsT d N E (List.ofFn σ)
            (xiOf (mSigma E) σ) (v : ℂ)
            (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r) M‖ := hnorm
    _ ≤ (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ * (row r * B) :=
      mul_le_mul_of_nonneg_left hraw1 (inv_nonneg.mpr hc.le)
    _ = ((APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ * row r) * B := by ring
    _ ≤ (N : ℝ) ^ D * B := mul_le_mul_of_nonneg_right hscaleRow hB0
    _ ≤ (N : ℝ) ^ D * (512 * (N : ℝ) ^ (1 + 6 * Kη)) :=
      mul_le_mul_of_nonneg_left hB hND0
    _ = 512 * (N : ℝ) ^ (D + 1 + 6 * Kη) := by
      calc
        (N : ℝ) ^ D * (512 * (N : ℝ) ^ (1 + 6 * Kη))
          = 512 * ((N : ℝ) ^ D * (N : ℝ) ^ (1 + 6 * Kη)) := by ring
        _ = 512 * (N : ℝ) ^ (D + (1 + 6 * Kη)) := by
          rw [Real.rpow_add hN0 D (1 + 6 * Kη)]
        _ = 512 * (N : ℝ) ^ (D + 1 + 6 * Kη) := by ring

/-- All-sample polynomial envelope for the actual, uncut, evolved quadratic
variation. No good event, spatial support, or A-prime hypothesis appears. -/
theorem qvAt_le_poly (d : Gauss.Dims) {E D Kη : ℝ} (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hD : 0 ≤ D) (hKη : 0 ≤ Kη)
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (hN : 1 ≤ (N : ℝ)) (hWN : (d.W N : ℝ) ≤ N)
    (hM : (Fintype.card (d.Idx N) : ℝ) ≤ N)
    (hη : (N : ℝ) ^ (-Kη) ≤ etaT E v)
    (u : ℝ) (hu : u ∈ Set.Icc s v) (ω : Gauss.Ω d) :
    0 ≤ APrimeDriftTimeFamily.qvAt d E D N σ a s v u ω ∧
      APrimeDriftTimeFamily.qvAt d E D N σ a s v u ω
        ≤ 2 ^ (21 : ℕ) * (N : ℝ) ^ (2 * D + 4 + 12 * Kη) := by
  let C₁ : ℝ := 512 * (N : ℝ) ^ (D + 1 + 6 * Kη)
  have hC₁0 : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hderiv : ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖fderiv ℝ (APrimeDriftTimeFamily.coordAt d E D N σ a s v u) M‖ ≤ C₁ :=
    fderiv_coordAt_le d N σ a hE hD hKη hs0 hsv hv1 hN hWN hM hη u hu
  have hqv0 : 0 ≤ APrimeDriftTimeFamily.qvAt d E D N σ a s v u ω :=
    Gauss.quadVar_nonneg _ _
  have hqv : APrimeDriftTimeFamily.qvAt d E D N σ a s v u ω
      ≤ C₁ ^ 2 * APrimeDuhamelModel.coordWt2 d N := by
    unfold APrimeDriftTimeFamily.qvAt Gauss.quadVar APrimeDuhamelModel.coordWt2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hd := Gauss.norm_coordD1_le hderiv (Gauss.Hflow d N u ω) q
    have hv0 := (Gauss.gvar d (Gauss.crd d N q)).2
    have hB0 := norm_nonneg (Gauss.Bmat d N q.1 q.2.1 q.2.2)
    calc
      (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          ‖Gauss.coordD1 d N
            (APrimeDriftTimeFamily.coordAt d E D N σ a s v u)
            (Gauss.Hflow d N u ω) q‖ ^ 2
        ≤ (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            (C₁ * ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) hd 2) hv0
      _ = C₁ ^ 2 * ((Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖ *
            ‖Gauss.Bmat d N q.1 q.2.1 q.2.2‖)) := by ring
  have hwt := coordWt2_le d N hM
  have hNpos : 0 < (N : ℝ) := by linarith
  have hpow : ((N : ℝ) ^ (D + 1 + 6 * Kη)) ^ 2 =
      (N : ℝ) ^ ((D + 1 + 6 * Kη) * 2) := by
    rw [Real.rpow_mul hNpos.le, Real.rpow_ofNat]
  constructor
  · exact hqv0
  · calc
      APrimeDriftTimeFamily.qvAt d E D N σ a s v u ω
        ≤ C₁ ^ 2 * APrimeDuhamelModel.coordWt2 d N := hqv
      _ ≤ C₁ ^ 2 * (8 * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hwt (sq_nonneg _)
      _ = 2 ^ (21 : ℕ) * (N : ℝ) ^ (2 * D + 4 + 12 * Kη) := by
        dsimp [C₁]
        rw [mul_pow, hpow]
        have hp : (N : ℝ) ^ 2 = (N : ℝ) ^ (2 : ℝ) := by
          rw [Real.rpow_ofNat]
        rw [hp]
        calc
          512 ^ 2 * (N : ℝ) ^ ((D + 1 + 6 * Kη) * 2) *
              (8 * (N : ℝ) ^ (2 : ℝ))
            = (2 : ℝ) ^ (21 : ℕ) *
                ((N : ℝ) ^ ((D + 1 + 6 * Kη) * 2) * (N : ℝ) ^ (2 : ℝ)) := by
                  norm_num; ring
          _ = (2 : ℝ) ^ (21 : ℕ) *
                (N : ℝ) ^ (((D + 1 + 6 * Kη) * 2) + 2) := by
                  rw [← Real.rpow_add hNpos]
          _ = (2 : ℝ) ^ (21 : ℕ) *
                (N : ℝ) ^ (2 * D + 4 + 12 * Kη) := by ring

/-- The model dimension condition supplies the two finite-size assumptions of
`qvAt_le_poly` eventually, uniformly in all windows, labels, and samples. -/
theorem eventually_qvAt_le_poly (d : Gauss.Dims) {E D Kη : ℝ}
    (hE : |E| < 2) (hD : 0 ≤ D) (hKη : 0 ≤ Kη) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ s v : ℝ, 0 ≤ s → s ≤ v → v < 1 →
        (N : ℝ) ^ (-Kη) ≤ etaT E v →
        ∀ (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2)
          (u : ℝ), u ∈ Set.Icc s v → ∀ ω : Gauss.Ω d,
          0 ≤ APrimeDriftTimeFamily.qvAt d E D N σ a s v u ω ∧
            APrimeDriftTimeFamily.qvAt d E D N σ a s v u ω
              ≤ 2 ^ (21 : ℕ) * (N : ℝ) ^ (2 * D + 4 + 12 * Kη) := by
  filter_upwards [d.dim, Filter.eventually_ge_atTop 1] with N hdim hNnat
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast hNnat
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by
    exact_mod_cast hdim.1
  have hL : 1 ≤ (d.L N : ℝ) := by
    exact_mod_cast (show 1 ≤ d.L N by have := d.three_le_L N; omega)
  have hW0 : 0 ≤ (d.W N : ℝ) := Nat.cast_nonneg _
  have hWN : (d.W N : ℝ) ≤ N := by nlinarith
  have hM : (Fintype.card (d.Idx N) : ℝ) ≤ N := by
    have hc : (Fintype.card (d.Idx N) : ℝ) =
        (d.W N : ℝ) * (d.L N : ℝ) := by
      simp [Gauss.Dims.Idx, Fintype.card_prod]
      ring
    rw [hc]
    exact hWL
  intro s v hs0 hsv hv1 hη σ a u hu ω
  exact qvAt_le_poly d N σ a hE hD hKη hs0 hsv hv1 hN hWN hM hη u hu ω

#print axioms RBM.APrimeQVGlobalPoly.ukerRow_le_ratio_sq
#print axioms RBM.APrimeQVGlobalPoly.coordWt2_le
#print axioms RBM.APrimeQVGlobalPoly.fderiv_coordAt_le
#print axioms RBM.APrimeQVGlobalPoly.qvAt_le_poly
#print axioms RBM.APrimeQVGlobalPoly.eventually_qvAt_le_poly

end RBM.APrimeQVGlobalPoly
