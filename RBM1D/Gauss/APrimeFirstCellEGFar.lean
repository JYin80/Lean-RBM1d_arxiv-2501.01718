/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellEGNear
import RBM1D.Gauss.APrimeDriftNearTriple
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Far-output Green drift at the first positive cut-net time
-/

namespace RBM.APrimeFirstCellEGFar

open Filter Gauss
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

/-! The two orientations of the single-G block average in (5.57). -/

private theorem goodEvent_entry_le {n : Type*} [DecidableEq n]
    {G : Matrix n n ℂ} {m : ℂ} {δ : ℝ}
    (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (x y : n) :
    ‖G x y‖ ≤ δ + if x = y then 1 else 0 := by
  by_cases hxy : x = y
  · subst y
    simpa [add_comm] using h.norm_diag_le hm x
  · simpa [hxy] using h.norm_offdiag_le hxy

theorem goodEvent_column_block_average {L Wb : ℕ} [NeZero L] [NeZero Wb]
    {G : Matrix (ZMod L × Fin Wb) (ZMod L × Fin Wb) ℂ}
    {m : ℂ} {δ : ℝ} (h : GoodEvent G m δ) (hm : ‖m‖ = 1)
    (x : ZMod L) (p : ZMod L × Fin Wb) :
    ∑ r : ZMod L × Fin Wb, Lemma57.blkW L Wb r x * ‖G r p‖ ≤
      δ + (Wb : ℝ)⁻¹ := by
  have hW : 0 ≤ ((Wb : ℝ)⁻¹) := by positivity
  have hsum :
      (∑ r : ZMod L × Fin Wb,
        Lemma57.blkW L Wb r x * (if r = p then (1 : ℝ) else 0)) ≤
        (Wb : ℝ)⁻¹ := by
    simp only [mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    unfold Lemma57.blkW
    split_ifs <;> simp [hW]
  calc
    (∑ r : ZMod L × Fin Wb, Lemma57.blkW L Wb r x * ‖G r p‖)
        ≤ ∑ r : ZMod L × Fin Wb,
            Lemma57.blkW L Wb r x * (δ + if r = p then 1 else 0) := by
              apply Finset.sum_le_sum
              intro r _
              exact mul_le_mul_of_nonneg_left (goodEvent_entry_le h hm r p)
                (Lemma57.blkW_nonneg L Wb r x)
    _ = δ + ∑ r : ZMod L × Fin Wb,
          Lemma57.blkW L Wb r x * (if r = p then 1 else 0) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
              Lemma57.sum_blkW, one_mul]
    _ ≤ δ + (Wb : ℝ)⁻¹ := by
          simpa only [add_comm δ] using add_le_add_left hsum δ

theorem goodEvent_row_block_average {L Wb : ℕ} [NeZero L] [NeZero Wb]
    {G : Matrix (ZMod L × Fin Wb) (ZMod L × Fin Wb) ℂ}
    {m : ℂ} {δ : ℝ} (h : GoodEvent G m δ) (hm : ‖m‖ = 1)
    (y : ZMod L) (r : ZMod L × Fin Wb) :
    ∑ p : ZMod L × Fin Wb, Lemma57.blkW L Wb p y * ‖G r p‖ ≤
      δ + (Wb : ℝ)⁻¹ := by
  have hW : 0 ≤ ((Wb : ℝ)⁻¹) := by positivity
  have hsum :
      (∑ p : ZMod L × Fin Wb,
        Lemma57.blkW L Wb p y * (if r = p then (1 : ℝ) else 0)) ≤
        (Wb : ℝ)⁻¹ := by
    simp only [mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    unfold Lemma57.blkW
    split_ifs <;> simp [hW]
  calc
    (∑ p : ZMod L × Fin Wb, Lemma57.blkW L Wb p y * ‖G r p‖)
        ≤ ∑ p : ZMod L × Fin Wb,
            Lemma57.blkW L Wb p y * (δ + if r = p then 1 else 0) := by
              apply Finset.sum_le_sum
              intro p _
              exact mul_le_mul_of_nonneg_left (goodEvent_entry_le h hm r p)
                (Lemma57.blkW_nonneg L Wb p y)
    _ = δ + ∑ p : ZMod L × Fin Wb,
          Lemma57.blkW L Wb p y * (if r = p then 1 else 0) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
              Lemma57.sum_blkW, one_mul]
    _ ≤ δ + (Wb : ℝ)⁻¹ := by
          simpa only [add_comm δ] using add_le_add_left hsum δ

/-- The two block orientations of (5.57) hold at the same positive source
time on the actual joint event, with its unchanged `N^(1/16)` local-law loss. -/
theorem jointEvent_block_averages {τ' ζ₁ ζ₃ : ℝ} (hτ' : 0 < τ')
    {N : ℕ} {ω : Gauss.Ω d}
    (hω : ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N) :
    let u := APrimeFirstCellNearSources.sourceTime τ' N
    (∀ (x y : ZMod (d.L N)) (p : ZMod (d.L N) × Fin (d.W N)),
      p.1 = y →
      ∑ r : ZMod (d.L N) × Fin (d.W N),
        Lemma57.blkW (d.L N) (d.W N) r x *
          ‖green (Gauss.Hflow d N u ω) (zt 0 u) r p‖ ≤
        Gauss.firstCellDelta N + (d.W N : ℝ)⁻¹) ∧
    (∀ (x y : ZMod (d.L N)) (r : ZMod (d.L N) × Fin (d.W N)),
      r.1 = x →
      ∑ p : ZMod (d.L N) × Fin (d.W N),
        Lemma57.blkW (d.L N) (d.W N) p y *
          ‖green (Gauss.Hflow d N u ω) (zt 0 u) r p‖ ≤
        Gauss.firstCellDelta N + (d.W N : ℝ)⁻¹) := by
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  letI : NeZero (d.W N) := ⟨by have := d.W_pos N; omega⟩
  let u := APrimeFirstCellNearSources.sourceTime τ' N
  have hgood : GoodEvent (green (Gauss.Hflow d N u ω) (zt 0 u))
      (mE 0) (Gauss.firstCellDelta N) :=
    hω.1.2 u (APrimeFirstCellNearSources.sourceTime_mem hτ' N)
  have hm : ‖mE 0‖ = 1 := norm_mE (by norm_num : |(0 : ℝ)| ≤ 2)
  constructor
  · intro x y p _
    exact goodEvent_column_block_average hgood hm x p
  · intro x y r _
    exact goodEvent_row_block_average hgood hm y r

/-- The norm component of the same joint event gives the sharp block cap. -/
theorem eventually_jointEvent_jG_le_two {τ' : ℝ} (hτ' : 0 < τ')
    (ζ₁ ζ₃ : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N,
        APrimeJG.jG (Gauss.sample d) 0 N
          (APrimeFirstCellNearSources.sourceTime τ' N) ω
          (B.ell N (APrimeFirstCellNearSources.sourceTime τ' N))
          (etaT 0 (APrimeFirstCellNearSources.sourceTime τ' N)) 60 ≤ 2 := by
  filter_upwards [APrimeFirstCellNearSources.eventually_sourceTime_eq_firstTime hτ',
    APrimeFirstCellJGCap.eventually_jG_le_two_of_norm] with N htime hJ ω hω
  have hX : ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ) := hω.1.1.1.1.1
  simpa only [htime.1] using (hJ ω hX).2

/-- The actual `(-,+,+)` triple loop is bounded by its three block maxima,
with the output swap required by the `eGpm` expansion. -/
theorem norm_gloop_three_le_gmBlk (X : Sample B) (E : ℝ) (N : ℕ)
    (u : ℝ) (ω : Gauss.Ω d) (a₁ a₂ b : ZMod (B.L N)) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      APrimeJG.gmBlk X E N u ω a₂ b *
        APrimeJG.gmBlk X E N u ω a₁ b *
          APrimeJG.gmBlk X E N u ω a₂ a₁ := by
  letI : NeZero (B.L N) := ⟨by have := B.three_le_L N; omega⟩
  letI : NeZero (B.W N) := ⟨by have := B.W_pos N; omega⟩
  have h := Lemma57.norm_gloop_three_le (L := B.L N) (Wb := B.W N)
    (H := X.H N u ω) (z := zt E u) false true true a₂ b a₁
    (APrimeJG.gmBlk_nonneg X E N u ω)
    (by
      intro p q hp hq
      rcases p with ⟨px, pi⟩
      rcases q with ⟨qy, qi⟩
      dsimp at hp hq ⊢
      subst px
      subst qy
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u ω false a₁ a₂ pi qi)
    (by
      intro q r hq hr
      rcases q with ⟨qx, qi⟩
      rcases r with ⟨ry, ri⟩
      dsimp at hq hr ⊢
      subst qx
      subst ry
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u ω true a₂ b qi ri)
    (by
      intro r p hr hp
      rcases r with ⟨rx, ri⟩
      rcases p with ⟨py, pi⟩
      dsimp at hr hp ⊢
      subst rx
      subst py
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u ω true b a₁ ri pi)
  rw [APrimeDriftNearTriple.gmBlk_comm X E N u ω b a₁,
    APrimeDriftNearTriple.gmBlk_comm X E N u ω a₁ a₂] at h
  convert h using 1 <;> ring

/-- The block two-loop is bounded by the actual neighbour-square witness.
This is the deterministic `h531` bridge, before insertion of a tail. -/
theorem two_loop_re_le_gsqBlk (X : Sample B) (E : ℝ) (N : ℕ)
    (u : ℝ) (ω : Gauss.Ω d) (x y : ZMod (B.L N)) :
    (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      ⟨[true, false], [x, y]⟩).re ≤ APrimeJG.gsqBlk X E N u ω x y := by
  letI : NeZero (B.L N) := ⟨by have := B.three_le_L N; omega⟩
  letI : NeZero (B.W N) := ⟨by have := B.W_pos N; omega⟩
  let M : ℝ := APrimeJG.gmBlk X E N u ω x y
  have hM : 0 ≤ M := APrimeJG.gmBlk_nonneg X E N u ω x y
  have hterm (p q : ZMod (B.L N) × Fin (B.W N)) :
      Lemma57.blkW (B.L N) (B.W N) p y *
          (Lemma57.blkW (B.L N) (B.W N) q x *
            ‖green (X.H N u ω) (zt E u) p q‖ ^ 2) ≤
      Lemma57.blkW (B.L N) (B.W N) p y *
          (Lemma57.blkW (B.L N) (B.W N) q x * M ^ 2) := by
    by_cases hp : p.1 = y
    · by_cases hq : q.1 = x
      · have hentry : ‖green (X.H N u ω) (zt E u) p q‖ ≤ M := by
          rcases p with ⟨px, pi⟩
          rcases q with ⟨qx, qi⟩
          dsimp at hp hq ⊢
          subst px
          subst qx
          have h := APrimeJG.norm_Gsig_le_gmBlk X E N u ω true y x pi qi
          rw [Gsig_true] at h
          rw [APrimeDriftNearTriple.gmBlk_comm X E N u ω y x] at h
          exact h
        have hsq : ‖green (X.H N u ω) (zt E u) p q‖ ^ 2 ≤ M ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hentry 2
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsq
            (Lemma57.blkW_nonneg (B.L N) (B.W N) q x))
          (Lemma57.blkW_nonneg (B.L N) (B.W N) p y)
      · simp only [Lemma57.blkW, if_neg hq, zero_mul, mul_zero]
        exact le_rfl
    · simp only [Lemma57.blkW, if_neg hp, zero_mul]
      exact le_rfl
  calc
    (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[true, false], [x, y]⟩).re =
        ∑ p : ZMod (B.L N) × Fin (B.W N),
          ∑ q : ZMod (B.L N) × Fin (B.W N),
            Lemma57.blkW (B.L N) (B.W N) p y *
              (Lemma57.blkW (B.L N) (B.W N) q x *
                ‖green (X.H N u ω) (zt E u) p q‖ ^ 2) :=
      (Lemma57.sum_blkW_normSq (B.L N) (B.W N)
        (X.hermitian N u ω) x y).symm
    _ ≤ ∑ p : ZMod (B.L N) × Fin (B.W N),
          ∑ q : ZMod (B.L N) × Fin (B.W N),
            Lemma57.blkW (B.L N) (B.W N) p y *
              (Lemma57.blkW (B.L N) (B.W N) q x * M ^ 2) := by
      exact Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hterm p q
    _ = M ^ 2 := by
      have hinner (p : ZMod (B.L N) × Fin (B.W N)) :
          (∑ q : ZMod (B.L N) × Fin (B.W N),
              Lemma57.blkW (B.L N) (B.W N) p y *
                (Lemma57.blkW (B.L N) (B.W N) q x * M ^ 2)) =
            Lemma57.blkW (B.L N) (B.W N) p y * M ^ 2 := by
        rw [← Finset.mul_sum, ← Finset.sum_mul,
          Lemma57.sum_blkW, one_mul]
      simp_rw [hinner, ← Finset.sum_mul, Lemma57.sum_blkW, one_mul]
    _ ≤ APrimeJG.gsqBlk X E N u ω x y := by
      have hcomm : M = APrimeJG.gmBlk X E N u ω y x :=
        APrimeDriftNearTriple.gmBlk_comm X E N u ω x y
      rw [show M ^ 2 = APrimeJG.gmBlk X E N u ω x y *
        APrimeJG.gmBlk X E N u ω y x from by
          change M ^ 2 = M * APrimeJG.gmBlk X E N u ω y x
          rw [← hcomm]
          ring]
      exact APrimeJG.gmBlk_mul_swap_le_gsqBlk X E N u ω x y

/-- The exact far-field coefficient of (5.35) for the actual Gaussian `eGpm`
at T379's source time. The abstract Lemma57 outputs are swapped to `(a₂,a₁)`;
the actual `eGpm` keeps its `(a₁,a₂)` arguments. -/
theorem norm_eGpm_far_source_bound {τ' ζ₁ ζ₃ : ℝ} (hτ' : 0 < τ')
    {N : ℕ} {ω : Gauss.Ω d}
    (hω : ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N)
    (hW : 1 ≤ (d.W N : ℝ))
    (hℓ : 1 ≤ B.ell N (APrimeFirstCellNearSources.sourceTime τ' N))
    (hη : 0 < etaT 0 (APrimeFirstCellNearSources.sourceTime τ' N))
    (hN : 1 ≤ (N : ℝ))
    (hr : 0 ≤ B.ell N (APrimeFirstCellNearSources.sourceTime τ' N) /
      B.ell N (Gauss.firstCellS τ' N))
    (a₁ a₂ : ZMod (d.L N))
    (hfar : ellStar (d.W N : ℝ)
      (B.ell N (APrimeFirstCellNearSources.sourceTime τ' N)) ≤
      (zdist (d.L N) (a₂ - a₁) : ℝ)) :
    let u := APrimeFirstCellNearSources.sourceTime τ' N
    let ℓ := B.ell N u
    let η := etaT 0 u
    let J := APrimeJG.jG (Gauss.sample d) 0 N u ω ℓ η 60
    let κ₁ := 2 * (N : ℝ) ^ ζ₁ * (ℓ / B.ell N (Gauss.firstCellS τ' N))
    let κ₂ := Gauss.firstCellDelta N + (d.W N : ℝ)⁻¹
    ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
      (Gauss.Hflow d N u ω) (zt 0 u) a₁ a₂‖ ≤
      η⁻¹ * κ₁ *
        (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂ +
          J * Real.sqrt J *
            (168 * ((d.W N : ℝ) * ℓ * η)⁻¹ +
              (d.L N : ℝ) * Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ)) *
          tailT (d.W N : ℝ) ℓ η 60 (zdist (d.L N) (a₂ - a₁)) := by
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  letI : NeZero (d.W N) := ⟨by have := d.W_pos N; omega⟩
  let u := APrimeFirstCellNearSources.sourceTime τ' N
  let ℓ := B.ell N u
  let η := etaT 0 u
  let J := APrimeJG.jG (Gauss.sample d) 0 N u ω ℓ η 60
  let κ₁ := 2 * (N : ℝ) ^ ζ₁ * (ℓ / B.ell N (Gauss.firstCellS τ' N))
  let κ₂ := Gauss.firstCellDelta N + (d.W N : ℝ)⁻¹
  let H := Gauss.Hflow d N u ω
  let z := zt 0 u
  let Gm := APrimeJG.gmBlk (Gauss.sample d) 0 N u ω
  let L2 : ZMod (d.L N) → ZMod (d.L N) → ℝ :=
    fun x y => (gloop (d.L N) (d.W N) H z ⟨[true, false], [x, y]⟩).re
  let L3 : ZMod (d.L N) → ℝ :=
    fun b => ‖gloop (d.L N) (d.W N) H z ⟨[false, true, true], [a₂, b, a₁]⟩‖
  have hWpos : (0 : ℝ) < (d.W N : ℝ) := by linarith
  have hJ : 1 ≤ J := APrimeJG.one_le_jG (Gauss.sample d) 0 N u ω hWpos
  have hJ0 : 0 ≤ J := by linarith
  have hκ₁ : 0 ≤ κ₁ := by dsimp [κ₁]; positivity
  have hδ : 0 ≤ Gauss.firstCellDelta N := by
    unfold Gauss.firstCellDelta Gauss.firstCellPsi
    positivity
  have hκ₂ : 0 ≤ κ₂ := by dsimp [κ₂]; positivity
  have hGm : ∀ x y, 0 ≤ Gm x y :=
    APrimeJG.gmBlk_nonneg (Gauss.sample d) 0 N u ω
  have h531 : ∀ x y : ZMod (d.L N),
      ellStar (d.W N : ℝ) ℓ / 2 ≤ (zdist (d.L N) (x - y) : ℝ) →
      L2 x y ≤ J * tailT (d.W N : ℝ) ℓ η 60 (zdist (d.L N) (x - y)) := by
    intro x y hxy
    exact (two_loop_re_le_gsqBlk (Gauss.sample d) 0 N u ω x y).trans
      (APrimeJG.gsqBlk_le_jG_mul_tailT (Gauss.sample d) 0 N u ω hWpos x y hxy)
  have h42 : ∀ x y : ZMod (d.L N),
      ellStar (d.W N : ℝ) ℓ / 2 ≤ (zdist (d.L N) (x - y) : ℝ) →
      Gm x y ≤ Real.sqrt J *
        Real.sqrt (tailT (d.W N : ℝ) ℓ η 60 (zdist (d.L N) (x - y))) := by
    intro x y hxy
    have h := APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail
      (Gauss.sample d) 0 N u ω (ℓu := ℓ) (ηu := η) (D := 60) x y hxy
    rw [Real.sqrt_mul hJ0] at h
    convert h using 1 <;> simp only [Gm, J, Gauss.band_W, Gauss.band_L] <;> rfl
  have h557 := jointEvent_block_averages hτ' hω
  have h558a : ∀ b, (zdist (d.L N) (a₂ - b) : ℝ) ≤
      ellStar (d.W N : ℝ) ℓ / 2 →
      L3 b ≤ (L2 a₁ a₂ + L2 a₁ b) * κ₂ := by
    intro b _
    exact Lemma57.gloop_h558a' (d.L N) (d.W N)
      (Gauss.Hflow_isHermitian d N u ω) a₂ a₁ b hκ₂
      (h557.1 a₂ b) (h557.2 a₂ b)
  have h558b : ∀ b, (zdist (d.L N) (a₁ - b) : ℝ) ≤
      ellStar (d.W N : ℝ) ℓ / 2 →
      L3 b ≤ (L2 a₁ a₂ + L2 b a₂) * κ₂ := by
    intro b _
    exact Lemma57.gloop_h558b' (d.L N) (d.W N)
      (Gauss.Hflow_isHermitian d N u ω) a₂ a₁ b hκ₂
      (h557.1 b a₁) (h557.2 b a₁)
  have h560 : ∀ b, L3 b ≤ Gm a₂ b * Gm a₁ b * Gm a₂ a₁ := by
    intro b
    exact norm_gloop_three_le_gmBlk (Gauss.sample d) 0 N u ω a₁ a₂ b
  have hEG :
      ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0) H z a₁ a₂‖ ≤
        κ₁ * (ℓ * η)⁻¹ * ∑ b : ZMod (d.L N), L3 b :=
    APrimeFirstCellEGNear.norm_eGpm_source_bound hτ' hω (by linarith) hη a₁ a₂
  exact Lemma57.eG_far_le (d.L N) hW hℓ hη hJ hfar
    hκ₁ hκ₂ hGm h531 h42 h558a h558b h560 hEG

/-- One event controls every far output pair at the positive first-cell time.
The coefficient keeps the literal `firstCellDelta N`, hence its `N^(1/16)`
loss, and uses the same sample's sharp `J ≤ 2`. -/
theorem eventually_far_output_indicator {τ' : ℝ} (hτ' : 0 < τ')
    (ζ₁ ζ₃ : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N,
        ∀ a₁ a₂ : ZMod (d.L N),
          let u := APrimeFirstCellNearSources.sourceTime τ' N
          let ℓ := B.ell N u
          let η := etaT 0 u
          let J := APrimeJG.jG (Gauss.sample d) 0 N u ω ℓ η 60
          let κ₁ := 2 * (N : ℝ) ^ ζ₁ *
            (ℓ / B.ell N (Gauss.firstCellS τ' N))
          let κ₂ := Gauss.firstCellDelta N + (d.W N : ℝ)⁻¹
          J ≤ 2 ∧
          ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
            (Gauss.Hflow d N u ω) (zt 0 u) a₁ a₂‖ *
              (if ellStar (d.W N : ℝ) ℓ ≤
                  (zdist (d.L N) (a₂ - a₁) : ℝ) then (1 : ℝ) else 0) ≤
            (η⁻¹ * κ₁ *
              (Lemma57.cFar (d.W N : ℝ) ℓ * J * κ₂ +
                J * Real.sqrt J *
                  (168 * ((d.W N : ℝ) * ℓ * η)⁻¹ +
                    (d.L N : ℝ) * Real.sqrt ((d.W N : ℝ) ^ (-(60 : ℝ))) / ℓ)) *
                tailT (d.W N : ℝ) ℓ η 60 (zdist (d.L N) (a₂ - a₁))) *
              (if ellStar (d.W N : ℝ) ℓ ≤
                  (zdist (d.L N) (a₂ - a₁) : ℝ) then (1 : ℝ) else 0) := by
  filter_upwards [APrimeFirstCellEGNear.eventually_source_scales hτ' ζ₁ ζ₃,
    eventually_jointEvent_jG_le_two hτ' ζ₁ ζ₃] with N hscales hJ2 ω hω a₁ a₂
  rcases hscales with ⟨hu, htime, hWexp, hlog4, hlog, hN, hℓ,
    hℓs, hr, hη, hηinv, hA1, hAle, hL, hNW, hW4, hJcap⟩
  constructor
  · exact hJ2 ω hω
  · by_cases hfar : ellStar (d.W N : ℝ)
        (B.ell N (APrimeFirstCellNearSources.sourceTime τ' N)) ≤
        (zdist (d.L N) (a₂ - a₁) : ℝ)
    · simpa only [if_pos hfar, mul_one] using
        norm_eGpm_far_source_bound hτ' hω (by linarith) hℓ hη hN
          (by linarith : 0 ≤ B.ell N
            (APrimeFirstCellNearSources.sourceTime τ' N) /
              B.ell N (Gauss.firstCellS τ' N))
          a₁ a₂ hfar
    · simp only [if_neg hfar, mul_zero, le_refl]

/-- The antipodal block pair is genuinely far at the same positive source
time, uniformly for all sufficiently large sizes. -/
theorem eventually_positive_far_pair {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop,
      0 < APrimeFirstCellNearSources.sourceTime τ' N ∧
      APrimeFirstCellNearSources.sourceTime τ' N =
        APrimeFirstCellJGCap.firstTime N ∧
      (bHalf B N).1 ≠ (bHalf B N).2 ∧
      ellStar (d.W N : ℝ)
        (B.ell N (APrimeFirstCellNearSources.sourceTime τ' N)) ≤
        (zdist (d.L N) ((bHalf B N).1 - (bHalf B N).2) : ℝ) := by
  filter_upwards [APrimeFirstCellNearSources.eventually_sourceTime_eq_firstTime hτ',
    twelve_ellStar_le_half_exampleGrow (t₀ := 1 / 2)
      (by norm_num) (by norm_num)] with N htime hsep
  let u := APrimeFirstCellNearSources.sourceTime τ' N
  have huHalf : u ≤ (1 / 2 : ℝ) :=
    (APrimeFirstCellNearSources.sourceTime_mem hτ' N).2.trans
      (gridT_le (1 / 2 : ℝ) 1)
  have hℓ : 0 ≤ B.ell N u :=
    (one_le_ellHat_of_nonneg (by have := B.three_le_L N; omega)
      htime.2.le (APrimeFirstCellNearSources.sourceTime_lt_one hτ' N)).trans' (by norm_num)
  have hstar : 0 ≤ ellStar (d.W N : ℝ) (B.ell N u) :=
    Step2FarMart.ellStar_nonneg_of_one_le (by exact_mod_cast B.one_le_W N) hℓ
  have h12 : 12 * ellStar (d.W N : ℝ) (B.ell N u) ≤
      ((d.L N / 2 : ℕ) : ℝ) := by
    change 12 * ellStar (Dims.growW N : ℝ)
      (ellHat (Dims.growL N) (u : ℂ)) ≤ ((Dims.growL N / 2 : ℕ) : ℝ)
    exact hsep u htime.2 huHalf
  refine ⟨htime.2, htime.1, bHalf_fst_ne_snd B N, ?_⟩
  have hdist :
      (zdist (d.L N) ((bHalf B N).1 - (bHalf B N).2) : ℝ) =
        ((d.L N / 2 : ℕ) : ℝ) := by
    change (zdist (B.L N) ((bHalf B N).1 - (bHalf B N).2) : ℝ) =
      ((B.L N / 2 : ℕ) : ℝ)
    exact zdist_bHalf B N
  rw [hdist]
  linarith

/-- A high-probability *same-sample* far event exists. The pair, the positive
source time, and the order-one `J` cap all occur at the same size and sample;
`eventually_far_output_indicator` applies to every output pair on this event. -/
theorem exists_highProb_far_event :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ ζ₁ ζ₃ : ℝ, 0 < ζ₁ → 0 < ζ₃ →
        HighProb (Gauss.P d)
          (APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃) ∧
        ∀ᶠ N : ℕ in atTop,
          0 < APrimeFirstCellNearSources.sourceTime τ' N ∧
          APrimeFirstCellNearSources.sourceTime τ' N =
            APrimeFirstCellJGCap.firstTime N ∧
          MeasurableSet (APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N) ∧
          ∃ ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ₁ ζ₃ N,
            (bHalf B N).1 ≠ (bHalf B N).2 ∧
            ellStar (d.W N : ℝ)
              (B.ell N (APrimeFirstCellNearSources.sourceTime τ' N)) ≤
              (zdist (d.L N) ((bHalf B N).1 - (bHalf B N).2) : ℝ) ∧
            APrimeJG.jG (Gauss.sample d) 0 N
              (APrimeFirstCellNearSources.sourceTime τ' N) ω
              (B.ell N (APrimeFirstCellNearSources.sourceTime τ' N))
              (etaT 0 (APrimeFirstCellNearSources.sourceTime τ' N)) 60 ≤ 2 := by
  obtain ⟨τ', hτ', hHP⟩ :=
    APrimeFirstCellNearSources.exists_highProb_jointEvent
  refine ⟨τ', hτ', ?_⟩
  intro ζ₁ ζ₃ hζ₁ hζ₃
  have hp := hHP ζ₁ ζ₃ hζ₁ hζ₃
  have hne := HighProb.nonempty (by simp) hp
  refine ⟨hp, ?_⟩
  filter_upwards [eventually_positive_far_pair hτ',
    eventually_jointEvent_jG_le_two hτ' ζ₁ ζ₃, hne]
    with N hpair hJ hne
  obtain ⟨ω, hω⟩ := hne
  exact ⟨hpair.1, hpair.2.1,
    APrimeFirstCellNearSources.jointEvent_measurable hτ' ζ₁ ζ₃ N,
    ω, hω, hpair.2.2.1, hpair.2.2.2, hJ ω hω⟩

/-- The far shift coefficient is subpolynomial at the same source time.
This is independent of the event and keeps the `loss32` constant. -/
theorem eventually_cFar_le {τ' : ℝ} (hτ' : 0 < τ')
    {ν : ℝ} (hν : 0 < ν) :
    ∀ᶠ N : ℕ in atTop,
      Lemma57.cFar (d.W N : ℝ)
        (B.ell N (APrimeFirstCellNearSources.sourceTime τ' N)) ≤
          (N : ℝ) ^ (ν / 4) := by
  have hθ : (0 : ℝ) < ν / 8 := by positivity
  have hlogR : ∀ᶠ W : ℝ in atTop,
      8 * Real.log W ^ (3 / 2 : ℝ) ≤ W ^ (ν / 8) := by
    have hsmall := (Asymptotics.isLittleO_iff_nat_mul_le'.1
      (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ) hθ)) 8
    filter_upwards [hsmall, eventually_ge_atTop 1] with W hsmall hW1
    have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
    have hp0 : 0 ≤ Real.log W ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlog0 _
    have hwp0 : 0 ≤ W ^ (ν / 8) := Real.rpow_nonneg (by linarith : 0 ≤ W) _
    simpa only [Nat.cast_ofNat, Real.norm_eq_abs, abs_of_nonneg hp0,
      abs_of_nonneg hwp0] using hsmall
  have hlog := (Step2.tendsto_W B).eventually hlogR
  have hExp := (Step2.tendsto_W B).eventually
    (eventually_exp_mul_log_rpow_le (Real.sqrt (1 / 2)) hθ)
  have hPow16 : ∀ᶠ N : ℕ in atTop,
      (16 : ℝ) ≤ (d.W N : ℝ) ^ (ν / 8) :=
    ((tendsto_rpow_atTop hθ).comp (Step2.tendsto_W B)).eventually_ge_atTop 16
  filter_upwards [APrimeFirstCellEGNear.eventually_source_scales hτ' 1 1,
    Gauss.W_le_self d, hlog, hExp, hPow16] with N hs hWN hlog hExp hPow16
  dsimp only at hs
  rcases hs with ⟨_, _, hW, _, _, _, hℓ, _, _, _, _, _, _, _, _, _, _⟩
  let W : ℝ := d.W N
  let ℓ : ℝ := B.ell N (APrimeFirstCellNearSources.sourceTime τ' N)
  have hWpos : 0 < W := by
    change (0 : ℝ) < (d.W N : ℝ)
    exact_mod_cast d.W_pos N
  have hWle : W ≤ (N : ℝ) := by
    change (d.W N : ℝ) ≤ (N : ℝ)
    exact_mod_cast hWN
  have hdiv : 8 / ℓ ≤ (8 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < ℓ)).2
    nlinarith
  change 8 * Real.log W ^ (3 / 2 : ℝ) ≤ W ^ (ν / 8) at hlog
  change (16 : ℝ) ≤ W ^ (ν / 8) at hPow16
  have hExp' : Lemma57.loss32 W ≤ W ^ (ν / 8) := by
    change Lemma57.loss32 (d.W N : ℝ) ≤ (d.W N : ℝ) ^ (ν / 8)
    simpa only [Lemma57.loss32, Gauss.band_W] using hExp
  have hpoly : 4 * Real.log W ^ (3 / 2 : ℝ) + 8 / ℓ ≤ W ^ (ν / 8) := by
    nlinarith
  have hc : Lemma57.cFar W ℓ ≤ W ^ (ν / 8) * W ^ (ν / 8) := by
    unfold Lemma57.cFar
    exact mul_le_mul hpoly hExp' (Lemma57.loss32_pos W).le
      (Real.rpow_nonneg hWpos.le _)
  calc
    Lemma57.cFar W ℓ ≤ W ^ (ν / 8) * W ^ (ν / 8) := hc
    _ = W ^ (ν / 4) := by
      rw [← Real.rpow_add hWpos]
      congr 1
      ring
    _ ≤ (N : ℝ) ^ (ν / 4) :=
      Real.rpow_le_rpow hWpos.le hWle (by positivity)

#print axioms goodEvent_column_block_average
#print axioms goodEvent_row_block_average
#print axioms jointEvent_block_averages
#print axioms eventually_jointEvent_jG_le_two
#print axioms norm_gloop_three_le_gmBlk
#print axioms two_loop_re_le_gsqBlk
#print axioms norm_eGpm_far_source_bound
#print axioms eventually_far_output_indicator
#print axioms eventually_positive_far_pair
#print axioms exists_highProb_far_event
#print axioms eventually_cFar_le

end RBM.APrimeFirstCellEGFar
