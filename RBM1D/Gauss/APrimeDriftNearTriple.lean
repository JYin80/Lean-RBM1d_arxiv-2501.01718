/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeJG
import RBM1D.Gauss.APrimeNearRem
import RBM1D.Gauss.LoopLipschitz

/-!
# T350: actual three-loop bound in the near-output, far-internal region

The bound is pointwise for the actual Gaussian sample.  No favorable event or
polynomial bound on the block witness is assumed.
-/

namespace RBM.APrimeDriftNearTriple

open Real Finset

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The maximum over both charges has the same value after reversing the two
blocks: the reversed entry is present with the opposite charge. -/
theorem gmBlk_comm (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (x y : ZMod (B.L N)) :
    APrimeJG.gmBlk X E N u ω x y = APrimeJG.gmBlk X E N u ω y x := by
  have hflip (s : Bool) (p q : Fin (B.W N)) :
      ‖Gsig (X.H N u ω) (zt E u) s (x, p) (y, q)‖ =
        ‖Gsig (X.H N u ω) (zt E u) (!s) (y, q) (x, p)‖ := by
    rw [APrimeJG.norm_Gsig_eq_green_or_swap (X.hermitian N u ω),
      APrimeJG.norm_Gsig_eq_green_or_swap (X.hermitian N u ω)]
    cases s <;> rfl
  apply le_antisymm
  · change (Finset.univ : Finset (Bool × Fin (B.W N) × Fin (B.W N))).sup'
        ⟨(true, ⟨0, B.W_pos N⟩, ⟨0, B.W_pos N⟩), Finset.mem_univ _⟩
        (fun z => ‖Gsig (X.H N u ω) (zt E u) z.1 (x, z.2.1) (y, z.2.2)‖)
        ≤ APrimeJG.gmBlk X E N u ω y x
    refine Finset.sup'_le _ _ (fun z _ => ?_)
    exact (hflip z.1 z.2.1 z.2.2).trans_le
      (APrimeJG.norm_Gsig_le_gmBlk X E N u ω (!z.1) y x z.2.2 z.2.1)
  · change (Finset.univ : Finset (Bool × Fin (B.W N) × Fin (B.W N))).sup'
        ⟨(true, ⟨0, B.W_pos N⟩, ⟨0, B.W_pos N⟩), Finset.mem_univ _⟩
        (fun z => ‖Gsig (X.H N u ω) (zt E u) z.1 (y, z.2.1) (x, z.2.2)‖)
        ≤ APrimeJG.gmBlk X E N u ω x y
    refine Finset.sup'_le _ _ (fun z _ => ?_)
    have h := hflip (!z.1) z.2.2 z.2.1
    simp only [Bool.not_not] at h
    exact h.symm.trans_le
      (APrimeJG.norm_Gsig_le_gmBlk X E N u ω (!z.1) x y z.2.2 z.2.1)

/-- An individual far block maximum obeys the square-root form of the actual
`jG` tail. -/
theorem gmBlk_le_sqrt_jG_tail (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ)
    (ω : Ω) {ℓu ηu D : ℝ} (x y : ZMod (B.L N))
    (hxy : ellStar (B.W N : ℝ) ℓu / 2 ≤
      (zdist (B.L N) (x - y) : ℝ)) :
    APrimeJG.gmBlk X E N u ω x y ≤
      Real.sqrt (APrimeJG.jG X E N u ω ℓu ηu D *
        tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) := by
  have hW : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hJ : 0 ≤ APrimeJG.jG X E N u ω ℓu ηu D :=
    (APrimeJG.one_le_jG X E N u ω hW).trans' (by norm_num)
  have hT : 0 ≤ tailT (B.W N : ℝ) ℓu ηu D
      (zdist (B.L N) (x - y)) := (tailT_pos hW _).le
  have hsq : APrimeJG.gmBlk X E N u ω x y ^ 2 ≤
      APrimeJG.jG X E N u ω ℓu ηu D *
        tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) := by
    calc
      _ = APrimeJG.gmBlk X E N u ω x y *
            APrimeJG.gmBlk X E N u ω y x := by rw [← gmBlk_comm X E N u ω x y]; ring
      _ ≤ APrimeJG.gsqBlk X E N u ω x y :=
        APrimeJG.gmBlk_mul_swap_le_gsqBlk X E N u ω x y
      _ ≤ _ := APrimeJG.gsqBlk_le_jG_mul_tailT X E N u ω hW x y hxy
  have hK : 0 ≤ APrimeJG.jG X E N u ω ℓu ηu D *
      tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) :=
    mul_nonneg hJ hT
  nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg
    (APrimeJG.jG X E N u ω ℓu ηu D *
      tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))),
    APrimeJG.gmBlk_nonneg X E N u ω x y]

/-- The actual `(-,+,+)` three-loop in the near-output/far-internal part of
(5.35).  This is a local statement: the near geometry is an explicit premise,
and no estimate for far output pairs is inferred from it. -/
theorem norm_gloop_three_near_far_le (X : Sample B) {E : ℝ} (hE : |E| < 2)
    (N : ℕ) {u : ℝ} (hu : u < 1) (ω : Ω)
    {ℓu D : ℝ} (hℓu : 0 < ℓu)
    (hlog : 4 ≤ Real.log (B.W N : ℝ))
    (a₁ a₂ b : ZMod (B.L N))
    (hnear : (zdist (B.L N) (a₂ - a₁) : ℝ) ≤
      ellStar (B.W N : ℝ) ℓu)
    (hb : Lemma57.ellStarStar (B.W N : ℝ) ℓu <
      (zdist (B.L N) (a₂ - b) : ℝ)) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      (etaT E u)⁻¹ *
        APrimeJG.jG X E N u ω ℓu (etaT E u) D *
          tailT (B.W N : ℝ) ℓu (etaT E u) D
            (Lemma57.ellStarStar (B.W N : ℝ) ℓu -
              ellStar (B.W N : ℝ) ℓu) := by
  letI : NeZero (B.L N) := ⟨by have := B.three_le_L N; omega⟩
  letI : NeZero (B.W N) := ⟨by have := B.W_pos N; omega⟩
  let W : ℝ := B.W N
  let F : ℝ := Lemma57.ellStarStar W ℓu - ellStar W ℓu
  let J : ℝ := APrimeJG.jG X E N u ω ℓu (etaT E u) D
  let T : ℝ := tailT W ℓu (etaT E u) D F
  let K : ℝ := J * T
  have hW : 0 < W := by dsimp [W]; exact_mod_cast B.W_pos N
  have hW1 : 1 ≤ W := by dsimp [W]; exact_mod_cast B.one_le_W N
  have hη : 0 < etaT E u := Gauss.etaT_pos_of_lt_one' hE hu
  have hJ : 0 ≤ J := (APrimeJG.one_le_jG X E N u ω hW).trans' (by norm_num)
  have hT : 0 ≤ T := (tailT_pos hW F).le
  have hK : 0 ≤ K := mul_nonneg hJ hT
  have hstar : 0 ≤ ellStar W ℓu := by
    unfold ellStar
    exact mul_nonneg (Real.rpow_nonneg (Real.log_nonneg hW1) _) hℓu.le
  have hmargin : (9 / 2 : ℝ) * ellStar W ℓu ≤
      Lemma57.ellStarStar W ℓu :=
    EEDef.ellStarStar_ge_nine_halves_ellStar hlog hℓu.le
  have hFfar : ellStar W ℓu / 2 ≤ F := by dsimp [F]; linarith
  have htri : (zdist (B.L N) (a₂ - b) : ℝ) ≤
      (zdist (B.L N) (a₂ - a₁) : ℝ) +
        (zdist (B.L N) (a₁ - b) : ℝ) := by
    have h := zdist_sub_le_add (B.L N) a₂ b a₁
    rw [Lemma57.zdist_sub_comm (B.L N) b a₁] at h
    exact h
  have hb2F : F ≤ (zdist (B.L N) (a₂ - b) : ℝ) := by
    dsimp [F]
    linarith
  have hb1F : F ≤ (zdist (B.L N) (a₁ - b) : ℝ) := by
    dsimp [F]
    linarith
  have hfar2 : ellStar W ℓu / 2 ≤ (zdist (B.L N) (a₂ - b) : ℝ) :=
    hFfar.trans hb2F
  have hfar1 : ellStar W ℓu / 2 ≤ (zdist (B.L N) (b - a₁) : ℝ) := by
    rw [Lemma57.zdist_sub_comm]
    exact hFfar.trans hb1F
  have htail2 : tailT W ℓu (etaT E u) D (zdist (B.L N) (a₂ - b)) ≤ T :=
    tailT_antitone hℓu hb2F
  have htail1 : tailT W ℓu (etaT E u) D (zdist (B.L N) (b - a₁)) ≤ T := by
    rw [Lemma57.zdist_sub_comm]
    exact tailT_antitone hℓu hb1F
  have hG2 : APrimeJG.gmBlk X E N u ω a₂ b ≤ Real.sqrt K := by
    have h := gmBlk_le_sqrt_jG_tail X E N u ω (ℓu := ℓu)
      (ηu := etaT E u) (D := D) a₂ b hfar2
    have hmul := mul_le_mul_of_nonneg_left htail2 hJ
    exact h.trans (Real.sqrt_le_sqrt (by simpa only [J, T, K] using hmul))
  have hG1 : APrimeJG.gmBlk X E N u ω b a₁ ≤ Real.sqrt K := by
    have h := gmBlk_le_sqrt_jG_tail X E N u ω (ℓu := ℓu)
      (ηu := etaT E u) (D := D) b a₁ hfar1
    have hmul := mul_le_mul_of_nonneg_left htail1 hJ
    exact h.trans (Real.sqrt_le_sqrt (by simpa only [J, T, K] using hmul))
  have hG0 : APrimeJG.gmBlk X E N u ω a₁ a₂ ≤ (etaT E u)⁻¹ :=
    APrimeJG.gmBlk_le_inv_etaT X hE N hu ω a₁ a₂
  have htrip :
      ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
        APrimeJG.gmBlk X E N u ω a₁ a₂ *
          (APrimeJG.gmBlk X E N u ω a₂ b *
            APrimeJG.gmBlk X E N u ω b a₁) := by
    apply Lemma57.norm_gloop_three_le (L := B.L N) (Wb := B.W N)
      (H := X.H N u ω) (z := zt E u) false true true a₂ b a₁
    · exact APrimeJG.gmBlk_nonneg X E N u ω
    · intro p q hp hq
      rcases p with ⟨px, pi⟩
      rcases q with ⟨qy, qi⟩
      dsimp at hp hq ⊢
      subst px
      subst qy
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u ω false a₁ a₂ pi qi
    · intro q r hq hr
      rcases q with ⟨qx, qi⟩
      rcases r with ⟨ry, ri⟩
      dsimp at hq hr ⊢
      subst qx
      subst ry
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u ω true a₂ b qi ri
    · intro r p hr hp
      rcases r with ⟨rx, ri⟩
      rcases p with ⟨py, pi⟩
      dsimp at hr hp ⊢
      subst rx
      subst py
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u ω true b a₁ ri pi
  have hprod : APrimeJG.gmBlk X E N u ω a₂ b *
      APrimeJG.gmBlk X E N u ω b a₁ ≤ Real.sqrt K * Real.sqrt K :=
    mul_le_mul hG2 hG1 (APrimeJG.gmBlk_nonneg X E N u ω b a₁)
      (Real.sqrt_nonneg K)
  have hfinal : APrimeJG.gmBlk X E N u ω a₁ a₂ *
      (APrimeJG.gmBlk X E N u ω a₂ b *
        APrimeJG.gmBlk X E N u ω b a₁) ≤ (etaT E u)⁻¹ * K := by
    calc
      _ ≤ (etaT E u)⁻¹ * (Real.sqrt K * Real.sqrt K) :=
        mul_le_mul hG0 hprod (mul_nonneg
          (APrimeJG.gmBlk_nonneg X E N u ω a₂ b)
          (APrimeJG.gmBlk_nonneg X E N u ω b a₁))
          (inv_nonneg.mpr hη.le)
      _ = (etaT E u)⁻¹ * K := by rw [Real.mul_self_sqrt hK]
  exact htrip.trans (by simpa only [J, T, K, W, F, mul_assoc] using hfinal)

/-- The preceding local inequality, explicitly instantiated at every sample of
the actual Gaussian flow. -/
theorem gaussian_three_near_far_le (d : Gauss.Dims) {E : ℝ} (hE : |E| < 2)
    (N : ℕ) {u : ℝ} (hu : u < 1) (ω : Gauss.Ω d)
    {ℓu D : ℝ} (hℓu : 0 < ℓu)
    (hlog : 4 ≤ Real.log (d.W N : ℝ))
    (a₁ a₂ b : ZMod (d.L N))
    (hnear : (zdist (d.L N) (a₂ - a₁) : ℝ) ≤
      ellStar (d.W N : ℝ) ℓu)
    (hb : Lemma57.ellStarStar (d.W N : ℝ) ℓu <
      (zdist (d.L N) (a₂ - b) : ℝ)) :
    ‖gloop (d.L N) (d.W N) ((Gauss.sample d).H N u ω) (zt E u)
      ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      (etaT E u)⁻¹ *
        APrimeJG.jG (Gauss.sample d) E N u ω ℓu (etaT E u) D *
          tailT (d.W N : ℝ) ℓu (etaT E u) D
            (Lemma57.ellStarStar (d.W N : ℝ) ℓu -
              ellStar (d.W N : ℝ) ℓu) :=
  norm_gloop_three_near_far_le (Gauss.sample d) hE N hu ω hℓu hlog
    a₁ a₂ b hnear hb

/-- The near support remains visible when this three-loop bound is passed to
the eventual near/far split of `eG`.  For far output pairs, both sides vanish. -/
theorem gaussian_three_near_far_indicator_le (d : Gauss.Dims)
    {E : ℝ} (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu : u < 1)
    (ω : Gauss.Ω d) {ℓu D : ℝ} (hℓu : 0 < ℓu)
    (hlog : 4 ≤ Real.log (d.W N : ℝ))
    (a₁ a₂ b : ZMod (d.L N))
    (hb : Lemma57.ellStarStar (d.W N : ℝ) ℓu <
      (zdist (d.L N) (a₂ - b) : ℝ)) :
    ‖gloop (d.L N) (d.W N) ((Gauss.sample d).H N u ω) (zt E u)
      ⟨[false, true, true], [a₂, b, a₁]⟩‖ *
        (if (zdist (d.L N) (a₂ - a₁) : ℝ) ≤
          ellStar (d.W N : ℝ) ℓu then (1 : ℝ) else 0) ≤
      ((etaT E u)⁻¹ *
        APrimeJG.jG (Gauss.sample d) E N u ω ℓu (etaT E u) D *
          tailT (d.W N : ℝ) ℓu (etaT E u) D
            (Lemma57.ellStarStar (d.W N : ℝ) ℓu -
              ellStar (d.W N : ℝ) ℓu)) *
        (if (zdist (d.L N) (a₂ - a₁) : ℝ) ≤
          ellStar (d.W N : ℝ) ℓu then (1 : ℝ) else 0) := by
  by_cases hnear : (zdist (d.L N) (a₂ - a₁) : ℝ) ≤
      ellStar (d.W N : ℝ) ℓu
  · simpa only [if_pos hnear, mul_one] using
      gaussian_three_near_far_le d hE N hu ω hℓu hlog a₁ a₂ b hnear hb
  · simp [hnear]

private theorem witness_L : Gauss.Dims.growL (2 ^ 400) = 2 ^ 100 := by
  decide +kernel

private theorem witness_W : Gauss.Dims.growW (2 ^ 400) = 2 ^ 300 := by
  decide +kernel

/-- A concrete first grid cell of the growing Gaussian band has a near output
pair and a genuinely far internal block.  Its tail is strictly positive and
the pointwise three-loop estimate holds on a real Gaussian sample. -/
theorem first_cell_real_sample_witness :
    let d := Gauss.Dims.exampleGrow
    let B := Gauss.band d
    let N : ℕ := 2 ^ 400
    ∃ (ω : Gauss.Ω d) (b : ZMod (B.L N)),
      gridT (B.W N : ℝ) 1 (1 / 2) 0 = 0 ∧
      0 < gridT (B.W N : ℝ) 1 (1 / 2) 1 ∧
      (zdist (B.L N) ((0 : ZMod (B.L N)) - 0) : ℝ) ≤
        ellStar (B.W N : ℝ) (B.ell N 0) ∧
      Lemma57.ellStarStar (B.W N : ℝ) (B.ell N 0) <
        (zdist (B.L N) ((0 : ZMod (B.L N)) - b) : ℝ) ∧
      0 < tailT (B.W N : ℝ) (B.ell N 0) (etaT 0 0) 60
        (Lemma57.ellStarStar (B.W N : ℝ) (B.ell N 0) -
          ellStar (B.W N : ℝ) (B.ell N 0)) ∧
      ‖gloop (B.L N) (B.W N) ((Gauss.sample d).H N 0 ω) (zt 0 0)
        ⟨[false, true, true], [0, b, 0]⟩‖ ≤
        (etaT 0 0)⁻¹ *
          APrimeJG.jG (Gauss.sample d) 0 N 0 ω (B.ell N 0) (etaT 0 0) 60 *
            tailT (B.W N : ℝ) (B.ell N 0) (etaT 0 0) 60
              (Lemma57.ellStarStar (B.W N : ℝ) (B.ell N 0) -
                ellStar (B.W N : ℝ) (B.ell N 0)) := by
  let d := Gauss.Dims.exampleGrow
  let B := Gauss.band d
  let N : ℕ := 2 ^ 400
  let ω : Gauss.Ω d := fun _ => 0
  let b : ZMod (B.L N) := (bHalf B N).1
  have hL : B.L N = 2 ^ 100 := witness_L
  have hW : B.W N = 2 ^ 300 := witness_W
  have hWr : (1 : ℝ) < (B.W N : ℝ) := by
    rw [hW]
    exact_mod_cast (by decide +kernel : 1 < (2 ^ 300 : ℕ))
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hℓ : B.ell N 0 = 1 := by
    change ellHat (B.L N) (0 : ℂ) = 1
    exact ellHat_zero (B.L N) (B.three_le_L N)
  have hlogle : Real.log (B.W N : ℝ) ≤ 300 := by
    rw [hW, Nat.cast_pow, Real.log_pow]
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    have hmul := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 300)
    norm_num at hmul ⊢
    exact hmul
  have hlog0 : 0 ≤ Real.log (B.W N : ℝ) :=
    Real.log_nonneg (by linarith)
  have hlog4 : 4 ≤ Real.log (B.W N : ℝ) := by
    rw [hW, Nat.cast_pow, Real.log_pow]
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_two_gt_d9
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlog2 (by norm_num : (0 : ℝ) ≤ 300)
    norm_num at hmul ⊢
    linarith
  have hss : Lemma57.ellStarStar (B.W N : ℝ) (B.ell N 0) <
      (zdist (B.L N) ((0 : ZMod (B.L N)) - b) : ℝ) := by
    rw [hℓ]
    have hz := zdist_bHalf B N
    have hb0 : (bHalf B N).2 = 0 := rfl
    rw [hb0] at hz
    have hdist : (zdist (B.L N) ((0 : ZMod (B.L N)) - b) : ℝ) =
        ((B.L N / 2 : ℕ) : ℝ) := by
      rw [Lemma57.zdist_sub_comm]
      simpa only [b, sub_zero] using hz
    rw [hdist]
    have hp := pow_le_pow_left₀ hlog0 hlogle 3
    have hnum : (300 : ℝ) ^ 3 < (((2 ^ 100 : ℕ) / 2 : ℕ) : ℝ) := by norm_num
    change Real.log (B.W N : ℝ) ^ (3 : ℝ) * 1 <
      (((B.L N / 2 : ℕ)) : ℝ)
    rw [mul_one, hL]
    have hpow : Real.log (B.W N : ℝ) ^ (3 : ℝ) =
        Real.log (B.W N : ℝ) ^ (3 : ℕ) := by norm_num
    rw [hpow]
    exact lt_of_le_of_lt hp hnum
  have hnear : (zdist (B.L N) ((0 : ZMod (B.L N)) - 0) : ℝ) ≤
      ellStar (B.W N : ℝ) (B.ell N 0) := by
    simp only [sub_self, zdist_zero, Nat.cast_zero]
    unfold ellStar
    positivity
  have hT : 0 < tailT (B.W N : ℝ) (B.ell N 0) (etaT 0 0) 60
      (Lemma57.ellStarStar (B.W N : ℝ) (B.ell N 0) -
        ellStar (B.W N : ℝ) (B.ell N 0)) := tailT_pos hW0 _
  have hgrid0 : gridT (B.W N : ℝ) 1 (1 / 2) 0 = 0 :=
    gridT_zero (by norm_num)
  have hgrid1 : 0 < gridT (B.W N : ℝ) 1 (1 / 2) 1 := by
    have hp : (B.W N : ℝ) ^ (-(1 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hWr (by norm_num)
    unfold gridT gridS
    simp only [Nat.cast_one, one_mul]
    exact lt_min (sub_pos.mpr hp) (by norm_num)
  have htrip := norm_gloop_three_near_far_le (Gauss.sample d)
    (E := 0) (by norm_num) N (u := 0) (by norm_num) ω
    (ℓu := B.ell N 0) (D := 60) (by rw [hℓ]; norm_num)
    hlog4 (0 : ZMod (B.L N)) 0 b hnear hss
  exact ⟨ω, b, hgrid0, hgrid1, hnear, hss, hT, htrip⟩

end RBM.APrimeDriftNearTriple

#print axioms RBM.APrimeDriftNearTriple.gmBlk_comm
#print axioms RBM.APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail
#print axioms RBM.APrimeDriftNearTriple.norm_gloop_three_near_far_le
#print axioms RBM.APrimeDriftNearTriple.gaussian_three_near_far_le
#print axioms RBM.APrimeDriftNearTriple.gaussian_three_near_far_indicator_le
#print axioms RBM.APrimeDriftNearTriple.first_cell_real_sample_witness
