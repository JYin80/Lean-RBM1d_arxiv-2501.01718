/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514QAssembly

/-!
# Deterministic positive-error budgets for the weighted Lemma 5.14 producers

The moment and high-probability hypotheses of the model producers remain separate.
-/

namespace RBM.Gauss

/-- The nonzero short-kernel decay remainder on a growth-grid cell.  The exponent
`D` is selected only after the loop length, grid step and decay loss are fixed. -/
theorem short_decay_group_le_rpow (r N : ℕ) {A R τ' τ₁ D : ℝ}
    (hN : 1 ≤ (N : ℝ)) (hA0 : 0 ≤ A) (hR0 : 0 ≤ R)
    (hA : A ≤ (N : ℝ)) (hR : R ≤ (N : ℝ) ^ τ') :
    A ^ r * R ^ r * (N : ℝ) ^ (τ₁ - D)
      ≤ (N : ℝ) ^ ((r : ℝ) * (1 + τ') + τ₁ - D) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  calc
    A ^ r * R ^ r * (N : ℝ) ^ (τ₁ - D)
        ≤ (N : ℝ) ^ r * ((N : ℝ) ^ τ') ^ r * (N : ℝ) ^ (τ₁ - D) := by
          gcongr
    _ = (N : ℝ) ^ ((r : ℝ) * (1 + τ') + τ₁ - D) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ τ') r,
        ← Real.rpow_mul hN0.le, ← Real.rpow_natCast (N : ℝ) r,
        ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      ring

/-- The offset part of the Q-kernel error.  The fourfold radius is a fixed
constant; its power is kept visible for eventual absorption. -/
theorem q_offset_group_le_rpow (r N : ℕ) {A R K τ' θ τ₁ D : ℝ}
    (hN : 1 ≤ (N : ℝ)) (hA0 : 0 ≤ A) (hR0 : 0 ≤ R) (hK0 : 0 ≤ K)
    (hA : A ≤ (N : ℝ)) (hR : R ≤ (N : ℝ) ^ τ')
    (hK : K ≤ (N : ℝ) ^ θ) :
    A ^ r * R ^ r * (4 * K) ^ (2 * r) * (N : ℝ) ^ (τ₁ - D) ≤
      4 ^ (2 * r) * (N : ℝ) ^
        ((r : ℝ) * (1 + τ' + 2 * θ) + τ₁ - D) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  calc
    A ^ r * R ^ r * (4 * K) ^ (2 * r) * (N : ℝ) ^ (τ₁ - D) ≤
        (N : ℝ) ^ r * ((N : ℝ) ^ τ') ^ r *
          (4 * (N : ℝ) ^ θ) ^ (2 * r) * (N : ℝ) ^ (τ₁ - D) := by
      gcongr
    _ = 4 ^ (2 * r) * (N : ℝ) ^
        ((r : ℝ) * (1 + τ' + 2 * θ) + τ₁ - D) := by
      rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ τ') r,
        ← Real.rpow_mul hN0.le,
        ← Real.rpow_natCast ((N : ℝ) ^ θ) (2 * r),
        ← Real.rpow_mul hN0.le,
        ← Real.rpow_natCast (N : ℝ) r]
      calc
        _ = 4 ^ (2 * r) * ((N : ℝ) ^ (r : ℝ) *
              (N : ℝ) ^ (τ' * (r : ℝ)) *
              (N : ℝ) ^ (θ * ((2 * r : ℕ) : ℝ)) *
              (N : ℝ) ^ (τ₁ - D)) := by ring
        _ = 4 ^ (2 * r) * (N : ℝ) ^
              ((r : ℝ) * (1 + τ' + 2 * θ) + τ₁ - D) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0,
            ← Real.rpow_add hN0]
          congr 1
          push_cast
          ring

/-- The offset part of the short-kernel error spends one radius power per
loop rather than the Q-kernel's two. -/
theorem short_offset_group_le_rpow (r N : ℕ) {A R K τ' θ τ₁ D : ℝ}
    (hN : 1 ≤ (N : ℝ)) (hA0 : 0 ≤ A) (hR0 : 0 ≤ R) (hK0 : 0 ≤ K)
    (hA : A ≤ (N : ℝ)) (hR : R ≤ (N : ℝ) ^ τ')
    (hK : K ≤ (N : ℝ) ^ θ) :
    A ^ r * R ^ r * K ^ r * (N : ℝ) ^ (τ₁ - D) ≤
      (N : ℝ) ^ ((r : ℝ) * (1 + τ' + θ) + τ₁ - D) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  calc
    A ^ r * R ^ r * K ^ r * (N : ℝ) ^ (τ₁ - D) ≤
        (N : ℝ) ^ r * ((N : ℝ) ^ τ') ^ r *
          ((N : ℝ) ^ θ) ^ r * (N : ℝ) ^ (τ₁ - D) := by
      gcongr
    _ = (N : ℝ) ^ ((r : ℝ) * (1 + τ' + θ) + τ₁ - D) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ τ') r,
        ← Real.rpow_mul hN0.le,
        ← Real.rpow_natCast ((N : ℝ) ^ θ) r,
        ← Real.rpow_mul hN0.le,
        ← Real.rpow_natCast (N : ℝ) r,
        ← Real.rpow_add hN0, ← Real.rpow_add hN0,
        ← Real.rpow_add hN0]
      congr 1
      ring

/-- One Q-block error keeps the input decay budget as a separate, nonexponential
term.  This identity is the component of T253's `errBudget` which cannot be
discarded by an exponential estimate. -/
theorem qBlockErrBd_decay_split (L k : ℕ) {R c e δ ε : ℝ}
    (hR : 0 ≤ R) (he : 0 ≤ e) (hδ : 0 ≤ δ)
    (hexp : Real.exp (-(cZero * c)) ≤ ε) :
    FastDecayFlow.qBlockErrBd L k R c e δ ≤
      δ * (1 + (L : ℝ) ^ k * cTwo52 ^ k) +
        ε * (((2 * Real.exp 1 * (R + 1)) ^ k * e +
          (L : ℝ) ^ k * δ) * cTwo52 ^ k) := by
  have hc : 0 ≤ cTwo52 := cTwo52_pos.le
  have hbase : 0 ≤ 2 * Real.exp 1 * (R + 1) := by positivity
  have hterm : 0 ≤ ((2 * Real.exp 1 * (R + 1)) ^ k * e +
      (L : ℝ) ^ k * δ) * cTwo52 ^ k := by positivity
  have hmul := mul_le_mul_of_nonneg_left hexp hterm
  unfold FastDecayFlow.qBlockErrBd
  nlinarith

/-- An explicit two-block decomposition of the T253 quadratic-variation error.
The second coefficient contains the polynomial-times-`δ` branch; it is not
absorbed into the exponential branch. -/
theorem qqErrBd_decay_split (L k : ℕ) {K e δ : ℝ}
    (hK : 0 ≤ K) (he : 0 ≤ e) (hδ : 0 ≤ δ) :
    let C := cTwo52 ^ k
    let U := (L : ℝ) ^ k
    let B₁ := (2 * Real.exp 1 * ((L : ℝ) * K + 1)) ^ k
    let B₂ := (2 * Real.exp 1 * (2 * ((L : ℝ) * K) + 1)) ^ k
    let P := 1 + 2 * U * C
    FastDecayFlow.qqErrBd L k K e δ ≤
      (P ^ 2 + B₂ * U * C ^ 2) * δ +
        (P * B₁ * C + B₂ * C * (1 + B₁ * C)) * e *
          Real.exp (-(cZero * K / 2)) := by
  let C : ℝ := cTwo52 ^ k
  let U : ℝ := (L : ℝ) ^ k
  let B₁ : ℝ := (2 * Real.exp 1 * ((L : ℝ) * K + 1)) ^ k
  let B₂ : ℝ := (2 * Real.exp 1 * (2 * ((L : ℝ) * K) + 1)) ^ k
  let P : ℝ := 1 + 2 * U * C
  let ε : ℝ := Real.exp (-(cZero * K / 2))
  let S : ℝ := FastDecayFlow.qBlockSizeBd L k ((L : ℝ) * K) e δ
  let E₁ : ℝ := FastDecayFlow.qBlockErrBd L k ((L : ℝ) * K) K e δ
  have hC : 0 ≤ C := by dsimp [C]; have := cTwo52_pos; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hB₁ : 0 ≤ B₁ := by dsimp [B₁]; positivity
  have hB₂ : 0 ≤ B₂ := by dsimp [B₂]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    calc Real.exp (-(cZero * K / 2)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by have := cZero_pos; nlinarith [mul_nonneg this.le hK])
      _ = 1 := Real.exp_zero
  have hK1 : Real.exp (-(cZero * K)) ≤ ε := by
    dsimp [ε]
    exact Real.exp_le_exp.mpr (by have := cZero_pos; nlinarith [mul_nonneg this.le hK])
  have hK2 : Real.exp (-(cZero * (2 * K))) ≤ ε := by
    dsimp [ε]
    exact Real.exp_le_exp.mpr (by have := cZero_pos; nlinarith [mul_nonneg this.le hK])
  have hS : S = e + (B₁ * e + U * δ) * C := by
    rfl
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hE₁0 : 0 ≤ E₁ := by
    exact FastDecayFlow.qBlockErrBd_nonneg L k (by positivity) he hδ
  have hinner : E₁ ≤ P * δ + ε * B₁ * e * C := by
    have hs := qBlockErrBd_decay_split L k (R := (L : ℝ) * K) (c := K)
      (e := e) (δ := δ) (ε := ε) (by positivity) he hδ hK1
    have hεδ : ε * δ ≤ δ := by nlinarith [mul_le_mul_of_nonneg_right hε1 hδ]
    have hεδ' := mul_le_mul_of_nonneg_left hεδ (mul_nonneg hU hC)
    dsimp [E₁, P, B₁, U, C] at hs ⊢
    nlinarith
  have houter : FastDecayFlow.qqErrBd L k K e δ ≤ P * E₁ + ε * B₂ * S * C := by
    have hs := qBlockErrBd_decay_split L k
      (R := 2 * ((L : ℝ) * K)) (c := 2 * K) (e := S) (δ := E₁)
      (ε := ε) (by positivity) hS0 hE₁0 hK2
    have hεE : ε * E₁ ≤ E₁ := by nlinarith [mul_le_mul_of_nonneg_right hε1 hE₁0]
    have hεE' := mul_le_mul_of_nonneg_left hεE (mul_nonneg hU hC)
    change FastDecayFlow.qBlockErrBd L k (2 * ((L : ℝ) * K)) (2 * K) S E₁ ≤
      E₁ * (1 + U * C) + ε * ((B₂ * S + U * E₁) * C) at hs
    change FastDecayFlow.qBlockErrBd L k (2 * ((L : ℝ) * K)) (2 * K) S E₁ ≤
      P * E₁ + ε * B₂ * S * C
    dsimp [P]
    nlinarith
  have hsmall : ε * (B₂ * U * C ^ 2 * δ) ≤ B₂ * U * C ^ 2 * δ := by
    simpa using (mul_le_mul_of_nonneg_right hε1
      (show 0 ≤ B₂ * U * C ^ 2 * δ by positivity))
  calc
    FastDecayFlow.qqErrBd L k K e δ ≤ P * E₁ + ε * B₂ * S * C := houter
    _ ≤ P * (P * δ + ε * B₁ * e * C) + ε * B₂ * S * C := by
      gcongr
    _ = P * (P * δ + ε * B₁ * e * C) +
          ε * B₂ * (e + (B₁ * e + U * δ) * C) * C := by rw [hS]
    _ ≤ (P ^ 2 + B₂ * U * C ^ 2) * δ +
          (P * B₁ * C + B₂ * C * (1 + B₁ * C)) * e * ε := by
      nlinarith [hsmall]

/-- The complete T253 budget is a polynomial multiple of the input decay error
plus an exponentially small multiple of the three size envelopes.  The
coefficient of `δ` includes both Q blocks and remains outside `exp`. -/
theorem errBudget_decay_split (L n : ℕ) {v K M δ Pb e : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hPb : 0 ≤ Pb) (he : 0 ≤ e) :
    let k := n + 1
    let C := cTwo52 ^ k
    let U := (L : ℝ) ^ k
    let B₁ := (2 * Real.exp 1 * ((L : ℝ) * K + 1)) ^ k
    let B₂ := (2 * Real.exp 1 * (2 * ((L : ℝ) * K) + 1)) ^ k
    let P := 1 + 2 * U * C
    let dCoeff := 1 + (2 * cTwo52) ^ k * U + P ^ 2 + B₂ * U * C ^ 2
    let mCoeff := (6 * Real.exp 1 * cTwo52 * K) ^ k
    let pCoeff := ((n : ℝ) + 2) * (1 - v)⁻¹ * cTwo52 ^ k *
        (2 + (L : ℝ) * cTwo52) +
        3 * ((n : ℝ) + 1) * cTwo52 ^ k * (1 - v)⁻¹ * Real.exp (cZero / 2)
    let eCoeff := P * B₁ * C + B₂ * C * (1 + B₁ * C)
    FastDecayFlow.errBudget L n v K M δ Pb e ≤
      dCoeff * δ + Real.exp (-(cZero * K / 2)) *
        (mCoeff * M + pCoeff * Pb + eCoeff * e) := by
  let k := n + 1
  let C : ℝ := cTwo52 ^ k
  let U : ℝ := (L : ℝ) ^ k
  let B₁ : ℝ := (2 * Real.exp 1 * ((L : ℝ) * K + 1)) ^ k
  let B₂ : ℝ := (2 * Real.exp 1 * (2 * ((L : ℝ) * K) + 1)) ^ k
  let P : ℝ := 1 + 2 * U * C
  let dCoeff : ℝ := 1 + (2 * cTwo52) ^ k * U + P ^ 2 + B₂ * U * C ^ 2
  let mCoeff : ℝ := (6 * Real.exp 1 * cTwo52 * K) ^ k
  let pCoeff : ℝ := ((n : ℝ) + 2) * (1 - v)⁻¹ * cTwo52 ^ k *
        (2 + (L : ℝ) * cTwo52) +
        3 * ((n : ℝ) + 1) * cTwo52 ^ k * (1 - v)⁻¹ * Real.exp (cZero / 2)
  let eCoeff : ℝ := P * B₁ * C + B₂ * C * (1 + B₁ * C)
  let ε : ℝ := Real.exp (-(cZero * K / 2))
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    calc Real.exp (-(cZero * K / 2)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by have := cZero_pos; nlinarith [mul_nonneg this.le hK])
      _ = 1 := Real.exp_zero
  have hqδ : ε * ((2 * cTwo52) ^ k * U * δ) ≤
      (2 * cTwo52) ^ k * U * δ := by
    simpa using (mul_le_mul_of_nonneg_right hε1
      (show 0 ≤ (2 * cTwo52) ^ k * U * δ by dsimp [U]; have := cTwo52_pos; positivity))
  have hqq := qqErrBd_decay_split L k hK he hδ
  have hqop : FastDecayFlow.qopErr1 L n K M δ ≤
      (1 + (2 * cTwo52) ^ k * U) * δ + ε * mCoeff * M := by
    dsimp [FastDecayFlow.qopErr1, ε, mCoeff, U, k]
    nlinarith [hqδ]
  have hc : FastDecayFlow.commErrBd L n v K Pb + FastDecayFlow.dotErrBd n v K Pb =
      ε * pCoeff * Pb := by
    dsimp [FastDecayFlow.commErrBd, FastDecayFlow.dotErrBd, pCoeff, ε, k]
    ring
  calc
    FastDecayFlow.errBudget L n v K M δ Pb e =
        FastDecayFlow.qopErr1 L n K M δ +
          (FastDecayFlow.commErrBd L n v K Pb + FastDecayFlow.dotErrBd n v K Pb) +
          FastDecayFlow.qqErrBd L k K e δ := by
            dsimp [FastDecayFlow.errBudget, k]
            ring
    _ ≤ (1 + (2 * cTwo52) ^ k * U) * δ + ε * mCoeff * M +
          ε * pCoeff * Pb +
          ((P ^ 2 + B₂ * U * C ^ 2) * δ + eCoeff * e * ε) := by
      rw [hc]
      exact add_le_add (add_le_add hqop (le_refl _)) hqq
    _ = dCoeff * δ + ε * (mCoeff * M + pCoeff * Pb + eCoeff * e) := by
      dsimp [dCoeff, eCoeff]
      ring

/-- A deterministic polynomial envelope for the coefficient of the input decay
budget and the three exponentially suppressed size coefficients.  It contains
no inverse decay error and no inverse exponential. -/
noncomputable def errBudgetPoly (L n : ℕ) (v K M Pb e : ℝ) : ℝ :=
  let k := n + 1
  let C := cTwo52 ^ k
  let U := (L : ℝ) ^ k
  let B₁ := (2 * Real.exp 1 * ((L : ℝ) * K + 1)) ^ k
  let B₂ := (2 * Real.exp 1 * (2 * ((L : ℝ) * K) + 1)) ^ k
  let P := 1 + 2 * U * C
  let dCoeff := 1 + (2 * cTwo52) ^ k * U + P ^ 2 + B₂ * U * C ^ 2
  let mCoeff := (6 * Real.exp 1 * cTwo52 * K) ^ k
  let pCoeff := ((n : ℝ) + 2) * (1 - v)⁻¹ * cTwo52 ^ k *
      (2 + (L : ℝ) * cTwo52) +
      3 * ((n : ℝ) + 1) * cTwo52 ^ k * (1 - v)⁻¹ * Real.exp (cZero / 2)
  let eCoeff := P * B₁ * C + B₂ * C * (1 + B₁ * C)
  1 + dCoeff + mCoeff + pCoeff + eCoeff + M + Pb + e

-- The final normalization compares several expanded polynomial coefficients.
set_option maxHeartbeats 800000 in
/-- The actual T253 budget is controlled by its explicit polynomial envelope.
The `δ` branch remains separate from the exponentially suppressed branch. -/
theorem errBudget_le_poly (L n : ℕ) {v K M δ Pb e : ℝ}
    (hv : v < 1) (hK : 0 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hPb : 0 ≤ Pb) (he : 0 ≤ e) :
    FastDecayFlow.errBudget L n v K M δ Pb e ≤
      (errBudgetPoly L n v K M Pb e) ^ 2 *
        (δ + Real.exp (-(cZero * K / 2))) := by
  let k := n + 1
  let C : ℝ := cTwo52 ^ k
  let U : ℝ := (L : ℝ) ^ k
  let B₁ : ℝ := (2 * Real.exp 1 * ((L : ℝ) * K + 1)) ^ k
  let B₂ : ℝ := (2 * Real.exp 1 * (2 * ((L : ℝ) * K) + 1)) ^ k
  let P : ℝ := 1 + 2 * U * C
  let dCoeff : ℝ := 1 + (2 * cTwo52) ^ k * U + P ^ 2 + B₂ * U * C ^ 2
  let mCoeff : ℝ := (6 * Real.exp 1 * cTwo52 * K) ^ k
  let pCoeff : ℝ := ((n : ℝ) + 2) * (1 - v)⁻¹ * cTwo52 ^ k *
        (2 + (L : ℝ) * cTwo52) +
        3 * ((n : ℝ) + 1) * cTwo52 ^ k * (1 - v)⁻¹ * Real.exp (cZero / 2)
  let eCoeff : ℝ := P * B₁ * C + B₂ * C * (1 + B₁ * C)
  let T : ℝ := errBudgetPoly L n v K M Pb e
  let ε : ℝ := Real.exp (-(cZero * K / 2))
  have hC : 0 ≤ C := by dsimp [C]; have := cTwo52_pos; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hB₁ : 0 ≤ B₁ := by dsimp [B₁]; positivity
  have hB₂ : 0 ≤ B₂ := by dsimp [B₂]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hd : 0 ≤ dCoeff := by dsimp [dCoeff]; have := cTwo52_pos; positivity
  have hm : 0 ≤ mCoeff := by dsimp [mCoeff]; have := cTwo52_pos; positivity
  have hp : 0 ≤ pCoeff := by
    dsimp [pCoeff]
    have hvi : 0 ≤ (1 - v)⁻¹ := inv_nonneg.mpr (by linarith)
    have := cTwo52_pos
    positivity
  have hec : 0 ≤ eCoeff := by dsimp [eCoeff]; positivity
  have hTdef : T = 1 + dCoeff + mCoeff + pCoeff + eCoeff + M + Pb + e := by rfl
  have hT1 : 1 ≤ T := by rw [hTdef]; linarith
  have hdT : dCoeff ≤ T := by rw [hTdef]; linarith
  have hcoeffT : mCoeff + pCoeff + eCoeff ≤ T := by rw [hTdef]; linarith
  have hsizeT : M + Pb + e ≤ T := by rw [hTdef]; linarith
  have hweighted : mCoeff * M + pCoeff * Pb + eCoeff * e ≤ T ^ 2 := by
    have hcross : 0 ≤ mCoeff * (Pb + e) + pCoeff * (M + e) +
        eCoeff * (M + Pb) := by positivity
    have hprod := mul_le_mul hcoeffT hsizeT (by positivity) (by positivity)
    nlinarith [hcross]
  have hsplit := errBudget_decay_split L n (v := v) (K := K) (M := M)
    (δ := δ) (Pb := Pb) (e := e) hK hM hδ hPb he
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hmulD := mul_le_mul_of_nonneg_right hdT hδ
  have hmulE := mul_le_mul_of_nonneg_left hweighted hε
  have hTle : T ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
  have hmulT := mul_le_mul_of_nonneg_right hTle hδ
  dsimp only at hsplit
  change FastDecayFlow.errBudget L n v K M δ Pb e ≤
    dCoeff * δ + ε * (mCoeff * M + pCoeff * Pb + eCoeff * e) at hsplit
  calc
    FastDecayFlow.errBudget L n v K M δ Pb e ≤
        dCoeff * δ + ε * (mCoeff * M + pCoeff * Pb + eCoeff * e) := hsplit
    _ ≤ T * δ + ε * T ^ 2 := by nlinarith
    _ ≤ T ^ 2 * (δ + ε) := by nlinarith

/-- Exact exponent of the polynomial prefactor in a normalized Q decay term. -/
theorem q_poly_group_le_rpow (r N : ℕ) {A R Lp P τ' b : ℝ}
    (hN : 1 ≤ (N : ℝ)) (hA0 : 0 ≤ A) (hR0 : 0 ≤ R)
    (hL0 : 0 ≤ Lp) (hP0 : 0 ≤ P)
    (hA : A ≤ (N : ℝ)) (hR : R ≤ (N : ℝ) ^ τ')
    (hL : Lp ≤ (N : ℝ)) (hP : P ≤ (N : ℝ) ^ b) :
    A ^ r * R ^ r * Lp ^ r * P ^ 2 ≤
      (N : ℝ) ^ ((r : ℝ) * (2 + τ') + 2 * b) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  calc
    A ^ r * R ^ r * Lp ^ r * P ^ 2 ≤
        (N : ℝ) ^ r * ((N : ℝ) ^ τ') ^ r * (N : ℝ) ^ r * ((N : ℝ) ^ b) ^ 2 := by
      gcongr
    _ = (N : ℝ) ^ ((r : ℝ) * (2 + τ') + 2 * b) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ τ') r,
        ← Real.rpow_mul hN0.le,
        ← Real.rpow_natCast ((N : ℝ) ^ b) 2,
        ← Real.rpow_mul hN0.le,
        ← Real.rpow_natCast (N : ℝ) r,
        ← Real.rpow_add hN0, ← Real.rpow_add hN0,
        ← Real.rpow_add hN0]
      congr 1
      ring

/-- The actual nonzero T253 budget in the normalized Q kernel remainder.
The two terms display separately the raw decay loss and the exponential tail. -/
theorem q_errBudget_group_le_rpow (n r N L : ℕ)
    {A R v K M δ Pb e τ' b τ₁ D Dexp : ℝ}
    (hN : 1 ≤ (N : ℝ)) (hv : v < 1) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hδ0 : 0 ≤ δ) (hPb : 0 ≤ Pb) (he : 0 ≤ e)
    (hA0 : 0 ≤ A) (hR0 : 0 ≤ R)
    (hA : A ≤ (N : ℝ)) (hR : R ≤ (N : ℝ) ^ τ')
    (hL : (L : ℝ) ≤ (N : ℝ))
    (hPoly0 : 0 ≤ errBudgetPoly L n v K M Pb e)
    (hPoly : errBudgetPoly L n v K M Pb e ≤ (N : ℝ) ^ b)
    (hδ : δ ≤ (N : ℝ) ^ (τ₁ - D))
    (hExp : Real.exp (-(cZero * K / 2)) ≤ (N : ℝ) ^ (-Dexp)) :
    A ^ r * R ^ r * (L : ℝ) ^ r *
        FastDecayFlow.errBudget L n v K M δ Pb e ≤
      (N : ℝ) ^ ((r : ℝ) * (2 + τ') + 2 * b + τ₁ - D) +
        (N : ℝ) ^ ((r : ℝ) * (2 + τ') + 2 * b - Dexp) := by
  let Q : ℝ := A ^ r * R ^ r * (L : ℝ) ^ r
  let P : ℝ := errBudgetPoly L n v K M Pb e
  let ε : ℝ := Real.exp (-(cZero * K / 2))
  let t : ℝ := (r : ℝ) * (2 + τ') + 2 * b
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hQP : Q * P ^ 2 ≤ (N : ℝ) ^ t := by
    exact q_poly_group_le_rpow r N hN hA0 hR0 (by positivity) hPoly0
      hA hR hL hPoly
  have hsum : δ + ε ≤ (N : ℝ) ^ (τ₁ - D) + (N : ℝ) ^ (-Dexp) :=
    add_le_add hδ hExp
  have hQP0 : 0 ≤ Q * P ^ 2 := by positivity
  have hb := errBudget_le_poly L n hv hK hM hδ0 hPb he
  calc
    Q * FastDecayFlow.errBudget L n v K M δ Pb e ≤ Q * (P ^ 2 * (δ + ε)) :=
      mul_le_mul_of_nonneg_left hb hQ0
    _ = (Q * P ^ 2) * (δ + ε) := by ring
    _ ≤ (Q * P ^ 2) * ((N : ℝ) ^ (τ₁ - D) + (N : ℝ) ^ (-Dexp)) :=
      mul_le_mul_of_nonneg_left hsum hQP0
    _ ≤ (N : ℝ) ^ t * ((N : ℝ) ^ (τ₁ - D) + (N : ℝ) ^ (-Dexp)) :=
      mul_le_mul_of_nonneg_right hQP (by positivity)
    _ = (N : ℝ) ^ (t + τ₁ - D) + (N : ℝ) ^ (t - Dexp) := by
      rw [mul_add, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1 <;> congr 1 <;> ring

/-- The positive bad-event payment has its own decay row. -/
theorem bad_event_group_le_rpow (r N : ℕ) {A cE τ₁ D : ℝ}
    (hN : 1 ≤ (N : ℝ)) (hA0 : 0 ≤ A) (hcE0 : 0 ≤ cE)
    (hA : A ≤ (N : ℝ)) (hcE : cE ≤ (N : ℝ) ^ (τ₁ - D)) :
    A ^ r * cE ≤ (N : ℝ) ^ ((r : ℝ) + τ₁ - D) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  calc
    A ^ r * cE ≤ (N : ℝ) ^ r * (N : ℝ) ^ (τ₁ - D) := by gcongr
    _ = (N : ℝ) ^ ((r : ℝ) + τ₁ - D) := by
      rw [← Real.rpow_natCast (N : ℝ) r, ← Real.rpow_add hN0]
      congr 1
      ring

/-- All positive Q-kernel errors, using the actual T253 budget.  The three
exponents show exactly which costs must be beaten when `D` is chosen. -/
theorem q_normalized_error_group_le (n r N L : ℕ)
    {A R K ζ δ M Pb e cE s v τ' θ b τ₁ D Dexp : ℝ}
    (hN : 1 ≤ (N : ℝ)) (hv : v < 1) (hK0 : 0 ≤ K)
    (hM : 0 ≤ M) (hδ0 : 0 ≤ δ) (hPb : 0 ≤ Pb) (he : 0 ≤ e)
    (hA0 : 0 ≤ A) (hR0 : 0 ≤ R) (hζ0 : 0 ≤ ζ) (hcE0 : 0 ≤ cE)
    (hA : A ≤ (N : ℝ)) (hR : R ≤ (N : ℝ) ^ τ')
    (hK : K ≤ (N : ℝ) ^ θ) (hL : (L : ℝ) ≤ (N : ℝ))
    (hRatio : (1 - s) / (1 - v) = R)
    (hPoly0 : 0 ≤ errBudgetPoly L n v K M Pb e)
    (hPoly : errBudgetPoly L n v K M Pb e ≤ (N : ℝ) ^ b)
    (hζ : ζ ≤ (N : ℝ) ^ (τ₁ - D))
    (hδ : δ ≤ (N : ℝ) ^ (τ₁ - D))
    (hcE : cE ≤ (N : ℝ) ^ (τ₁ - D))
    (hExp : Real.exp (-(cZero * K / 2)) ≤ (N : ℝ) ^ (-Dexp)) :
    A ^ r * (errKer716 L r (4 * K) ζ
        (FastDecayFlow.errBudget L n v K M δ Pb e) s v + cE) ≤
      (cKerSumZero r * 4 ^ (2 * r)) *
        (N : ℝ) ^ ((r : ℝ) * (1 + τ' + 2 * θ) + τ₁ - D) +
      cKerSumZeroErr r *
        ((N : ℝ) ^ ((r : ℝ) * (2 + τ') + 2 * b + τ₁ - D) +
         (N : ℝ) ^ ((r : ℝ) * (2 + τ') + 2 * b - Dexp)) +
      (N : ℝ) ^ ((r : ℝ) + τ₁ - D) := by
  have hOff := q_offset_group_le_rpow r N (τ₁ := τ₁) (D := D)
    hN hA0 hR0 hK0 hA hR hK
  have hOff' : A ^ r * R ^ r * (4 * K) ^ (2 * r) * ζ ≤
      4 ^ (2 * r) *
        (N : ℝ) ^ ((r : ℝ) * (1 + τ' + 2 * θ) + τ₁ - D) := by
    calc
      _ ≤ A ^ r * R ^ r * (4 * K) ^ (2 * r) *
          (N : ℝ) ^ (τ₁ - D) := by gcongr
      _ ≤ _ := hOff
  have hErr := q_errBudget_group_le_rpow n r N L hN hv hK0 hM hδ0 hPb he
    hA0 hR0 hA hR hL hPoly0 hPoly hδ hExp
  have hBad := bad_event_group_le_rpow r N hN hA0 hcE0 hA hcE
  have hc1 : 0 ≤ cKerSumZero r := SumZeroDyn.cKerSumZero_nonneg r
  have hc2 : 0 ≤ cKerSumZeroErr r := SumZeroDyn.cKerSumZeroErr_nonneg r
  calc
    A ^ r * (errKer716 L r (4 * K) ζ
        (FastDecayFlow.errBudget L n v K M δ Pb e) s v + cE) =
      cKerSumZero r * (A ^ r * R ^ r * (4 * K) ^ (2 * r) * ζ) +
      cKerSumZeroErr r * (A ^ r * R ^ r * (L : ℝ) ^ r *
        FastDecayFlow.errBudget L n v K M δ Pb e) + A ^ r * cE := by
          simp only [errKer716, hRatio]
          ring
    _ ≤ cKerSumZero r * (4 ^ (2 * r) *
        (N : ℝ) ^ ((r : ℝ) * (1 + τ' + 2 * θ) + τ₁ - D)) +
      cKerSumZeroErr r *
        ((N : ℝ) ^ ((r : ℝ) * (2 + τ') + 2 * b + τ₁ - D) +
         (N : ℝ) ^ ((r : ℝ) * (2 + τ') + 2 * b - Dexp)) +
      (N : ℝ) ^ ((r : ℝ) + τ₁ - D) := by
          have h1 := mul_le_mul_of_nonneg_left hOff' hc1
          have h2 := mul_le_mul_of_nonneg_left hErr hc2
          linarith
    _ = _ := by ring

/-- All positive short-kernel errors on one adjacent cell. -/
theorem short_normalized_error_group_le (r N : ℕ)
    {κg A R K ζ δ cE s v τ' θ τ₁ D : ℝ}
    (hκg : 0 < κg) (hN : 1 ≤ (N : ℝ))
    (hA0 : 0 ≤ A) (hR0 : 0 ≤ R) (hK0 : 0 ≤ K)
    (hζ0 : 0 ≤ ζ) (hδ0 : 0 ≤ δ) (hcE0 : 0 ≤ cE)
    (hA : A ≤ (N : ℝ)) (hR : R ≤ (N : ℝ) ^ τ')
    (hK : K ≤ (N : ℝ) ^ θ)
    (hRatio : (1 - s) / (1 - v) = R)
    (hζ : ζ ≤ (N : ℝ) ^ (τ₁ - D))
    (hδ : δ ≤ (N : ℝ) ^ (τ₁ - D))
    (hcE : cE ≤ (N : ℝ) ^ (τ₁ - D)) :
    A ^ r * (errKer716Short r κg K ζ δ s v + cE) ≤
      cKerShort r κg *
        (N : ℝ) ^ ((r : ℝ) * (1 + τ' + θ) + τ₁ - D) +
      (N : ℝ) ^ ((r : ℝ) * (1 + τ') + τ₁ - D) +
      (N : ℝ) ^ ((r : ℝ) + τ₁ - D) := by
  have hOff := short_offset_group_le_rpow r N (τ₁ := τ₁) (D := D)
    hN hA0 hR0 hK0 hA hR hK
  have hOff' : A ^ r * R ^ r * K ^ r * ζ ≤
      (N : ℝ) ^ ((r : ℝ) * (1 + τ' + θ) + τ₁ - D) := by
    calc
      _ ≤ A ^ r * R ^ r * K ^ r * (N : ℝ) ^ (τ₁ - D) := by gcongr
      _ ≤ _ := hOff
  have hDecay := short_decay_group_le_rpow r N (τ₁ := τ₁) (D := D)
    hN hA0 hR0 hA hR
  have hDecay' : A ^ r * R ^ r * δ ≤
      (N : ℝ) ^ ((r : ℝ) * (1 + τ') + τ₁ - D) := by
    calc
      _ ≤ A ^ r * R ^ r * (N : ℝ) ^ (τ₁ - D) := by gcongr
      _ ≤ _ := hDecay
  have hBad := bad_event_group_le_rpow r N hN hA0 hcE0 hA hcE
  have hc : 0 ≤ cKerShort r κg := SumZeroDyn.cKerShort_nonneg r hκg
  calc
    A ^ r * (errKer716Short r κg K ζ δ s v + cE) =
      cKerShort r κg * (A ^ r * R ^ r * K ^ r * ζ) +
        A ^ r * R ^ r * δ + A ^ r * cE := by
          simp only [errKer716Short, hRatio]
          ring
    _ ≤ cKerShort r κg *
        (N : ℝ) ^ ((r : ℝ) * (1 + τ' + θ) + τ₁ - D) +
      (N : ℝ) ^ ((r : ℝ) * (1 + τ') + τ₁ - D) +
      (N : ℝ) ^ ((r : ℝ) + τ₁ - D) := by
          have h1 := mul_le_mul_of_nonneg_left hOff' hc
          linarith

/-- Any prescribed negative power absorbs all four Q error branches at once.
The constants depend on the fixed loop length, never on the grid index. -/
theorem eventually_q_error_envelope_le (r : ℕ)
    {τ' θ b τ₁ D Dexp d : ℝ}
    (h1 : (r : ℝ) * (1 + τ' + 2 * θ) + τ₁ - D < -d)
    (h2 : (r : ℝ) * (2 + τ') + 2 * b + τ₁ - D < -d)
    (h3 : (r : ℝ) * (2 + τ') + 2 * b - Dexp < -d)
    (h4 : (r : ℝ) + τ₁ - D < -d) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (cKerSumZero r * 4 ^ (2 * r)) *
        (N : ℝ) ^ ((r : ℝ) * (1 + τ' + 2 * θ) + τ₁ - D) +
      cKerSumZeroErr r *
        ((N : ℝ) ^ ((r : ℝ) * (2 + τ') + 2 * b + τ₁ - D) +
         (N : ℝ) ^ ((r : ℝ) * (2 + τ') + 2 * b - Dexp)) +
      (N : ℝ) ^ ((r : ℝ) + τ₁ - D) ≤ (N : ℝ) ^ (-d) := by
  have he1 := SumZeroDyn.eventually_const_mul_rpow_le
    (4 * (cKerSumZero r * 4 ^ (2 * r))) h1
  have he2 := SumZeroDyn.eventually_const_mul_rpow_le
    (4 * cKerSumZeroErr r) h2
  have he3 := SumZeroDyn.eventually_const_mul_rpow_le
    (4 * cKerSumZeroErr r) h3
  have he4 := SumZeroDyn.eventually_const_mul_rpow_le (4 : ℝ) h4
  filter_upwards [he1, he2, he3, he4] with N hN1 hN2 hN3 hN4
  nlinarith

/-- The three short-error branches obey the same arbitrary-power principle. -/
theorem eventually_short_error_envelope_le (r : ℕ)
    {κg τ' θ τ₁ D d : ℝ} (hκg : 0 < κg)
    (h1 : (r : ℝ) * (1 + τ' + θ) + τ₁ - D < -d)
    (h2 : (r : ℝ) * (1 + τ') + τ₁ - D < -d)
    (h3 : (r : ℝ) + τ₁ - D < -d) :
    ∀ᶠ N : ℕ in Filter.atTop,
      cKerShort r κg *
        (N : ℝ) ^ ((r : ℝ) * (1 + τ' + θ) + τ₁ - D) +
      (N : ℝ) ^ ((r : ℝ) * (1 + τ') + τ₁ - D) +
      (N : ℝ) ^ ((r : ℝ) + τ₁ - D) ≤ (N : ℝ) ^ (-d) := by
  have he1 := SumZeroDyn.eventually_const_mul_rpow_le (3 * cKerShort r κg) h1
  have he2 := SumZeroDyn.eventually_const_mul_rpow_le (3 : ℝ) h2
  have he3 := SumZeroDyn.eventually_const_mul_rpow_le (3 : ℝ) h3
  filter_upwards [he1, he2, he3] with N hN1 hN2 hN3
  nlinarith

/-- After `θ`, the grid growth and all fixed polynomial costs are specified,
one may choose the raw decay exponent and the exponential-tail exponent. -/
theorem q_decay_exponents_exist (r : ℕ) {τ' θ b τ₁ d : ℝ}
    (hτ' : 0 ≤ τ') (hθ : 0 ≤ θ) (hb : 0 ≤ b)
    (hτ₁ : 0 < τ₁) (hd : 0 ≤ d) :
    ∃ D Dexp : ℝ, 0 < D ∧ 0 < Dexp ∧
      (r : ℝ) * (1 + τ' + 2 * θ) + τ₁ - D < -d ∧
      (r : ℝ) * (2 + τ') + 2 * b + τ₁ - D < -d ∧
      (r : ℝ) * (2 + τ') + 2 * b - Dexp < -d ∧
      (r : ℝ) + τ₁ - D < -d := by
  let D : ℝ := d + τ₁ + (r : ℝ) * (2 + τ' + 2 * θ) + 2 * b + 1
  let Dexp : ℝ := d + (r : ℝ) * (2 + τ') + 2 * b + 1
  refine ⟨D, Dexp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    dsimp [D, Dexp]
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith [mul_nonneg hr hθ, mul_nonneg hr hτ']

/-- The short row needs no separate exponential-tail budget. -/
theorem short_decay_exponent_exists (r : ℕ) {τ' θ τ₁ d : ℝ}
    (hτ' : 0 ≤ τ') (hθ : 0 ≤ θ) (hτ₁ : 0 < τ₁) (hd : 0 ≤ d) :
    ∃ D : ℝ, 0 < D ∧
      (r : ℝ) * (1 + τ' + θ) + τ₁ - D < -d ∧
      (r : ℝ) * (1 + τ') + τ₁ - D < -d ∧
      (r : ℝ) + τ₁ - D < -d := by
  let D : ℝ := d + τ₁ + (r : ℝ) * (1 + τ' + θ) + 1
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  all_goals
    dsimp [D]
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith [mul_nonneg hr hθ, mul_nonneg hr hτ']

/-- The geometric factor in both exact error definitions is `R=W^τ'` on
every adjacent growth-grid cell, uniformly in its index. -/
theorem gridS_adjacent_ratio_eq {W τ' : ℝ} (hW : 0 < W) (k : ℕ) :
    (1 - gridS W τ' k) / (1 - gridS W τ' (k + 1)) = W ^ τ' := by
  have hb : 1 - gridS W τ' (k + 1) ≠ 0 :=
    (sub_pos.mpr (gridS_lt_one (τ' := τ') hW (k + 1))).ne'
  apply (div_eq_iff hb).2
  rw [one_sub_gridS_succ (τ' := τ') hW k, ← mul_assoc,
    ← Real.rpow_add hW]
  have he : τ' + -τ' = 0 := by ring
  rw [he, Real.rpow_zero, one_mul]

/-- The time integral is exactly logarithmic and admits one eventually uniform
small-power bound for all adjacent grid cells. -/
theorem eventually_gridS_integral_le_rpow {E τ' η : ℝ}
    (hE : |E| < 2) (hτ' : 0 < τ') (hη : 0 < η)
    {W : ℕ → ℝ}
    (hW : ∀ᶠ N : ℕ in Filter.atTop, 1 ≤ W N ∧ W N ≤ (N : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ k : ℕ,
      0 ≤ (∫ u in gridS (W N) τ' k..gridS (W N) τ' (k + 1), (etaT E u)⁻¹) ∧
      (∫ u in gridS (W N) τ' k..gridS (W N) τ' (k + 1), (etaT E u)⁻¹)
        ≤ (N : ℝ) ^ (η / 8) := by
  let ε : ℝ := η / 16
  have hε : 0 < ε := by dsimp [ε]; linarith
  have him : 0 < (mE E).im := mE_im_pos hE
  have hconst := SumZeroDyn.eventually_const_mul_rpow_le
    (τ' / (ε * (mE E).im))
    (show ε < η / 8 by dsimp [ε]; linarith)
  filter_upwards [hW, hconst, Filter.eventually_ge_atTop 1] with N hWN hpow hN k
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hW0 : 0 < W N := by linarith [hWN.1]
  have hlog0 : 0 ≤ Real.log (W N) := Real.log_nonneg hWN.1
  have hlogWN : Real.log (W N) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hW0 hWN.2
  have hlogN := SumZeroDyn.log_le_rpow_div_nat N hε
  have hscale : τ' * Real.log (W N) / (mE E).im ≤
      (τ' / (ε * (mE E).im)) * (N : ℝ) ^ ε := by
    have hdiv := div_le_div_of_nonneg_right (hlogWN.trans hlogN) him.le
    have hmul := mul_le_mul_of_nonneg_left hdiv hτ'.le
    have hne : ε ≠ 0 := hε.ne'
    have hine : (mE E).im ≠ 0 := him.ne'
    convert hmul using 1 <;> field_simp <;> ring
  rw [integral_etaT_inv_gridS_succ hE hWN.1 hτ'.le k]
  exact ⟨div_nonneg (mul_nonneg hτ'.le hlog0) him.le,
    hscale.trans hpow⟩

/-- A fixed kernel constant is absorbed after a strictly smaller radius
exponent has been selected. -/
theorem eventually_q_coefficient_le_rpow (r : ℕ) {θ β : ℝ}
    (hgap : θ * ((2 * r : ℕ) : ℝ) < β) {Kd : ℕ → ℝ}
    (hKd : ∀ᶠ N : ℕ in Filter.atTop,
      0 ≤ Kd N ∧ Kd N ≤ (N : ℝ) ^ θ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      cKer716 r (4 * Kd N) ≤ (N : ℝ) ^ β := by
  have hev := SumZeroDyn.eventually_const_mul_rpow_le
    (cKerSumZero r * 4 ^ (2 * r)) hgap
  filter_upwards [hKd, hev, Filter.eventually_ge_atTop 1] with N hK hc hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact (cKer716_four_le_rpow r N hN1 hK.1 hK.2 (le_refl _)).trans hc

theorem eventually_short_coefficient_le_rpow (r : ℕ) {κg θ β : ℝ}
    (hκg : 0 < κg) (hgap : θ * (r : ℝ) < β) {Kd : ℕ → ℝ}
    (hKd : ∀ᶠ N : ℕ in Filter.atTop,
      0 ≤ Kd N ∧ Kd N ≤ (N : ℝ) ^ θ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      cKer716Short r κg (Kd N) ≤ (N : ℝ) ^ β := by
  have hev := SumZeroDyn.eventually_const_mul_rpow_le (cKerShort r κg) hgap
  filter_upwards [hKd, hev, Filter.eventually_ge_atTop 1] with N hK hc hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact (cKer716Short_le_rpow r N hκg hN1 hK.1 hK.2 (le_refl _)).trans hc

/-- A lower polynomial growth bound on the band width converts raw `W` decay
into the natural-number powers used in the positive-error rows. -/
theorem width_decay_le_nat_decay (N : ℕ) {W γ Draw : ℝ}
    (hN : 1 ≤ (N : ℝ)) (hγ : 0 < γ) (hDraw : 0 ≤ Draw)
    (hWlow : (N : ℝ) ^ γ ≤ W) :
    W ^ (-Draw) ≤ (N : ℝ) ^ (-γ * Draw) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  calc
    W ^ (-Draw) ≤ ((N : ℝ) ^ γ) ^ (-Draw) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 γ)
        hWlow (by linarith)
    _ = (N : ℝ) ^ (-γ * Draw) := by
      rw [← Real.rpow_mul hN0.le]
      congr 1
      ring

/-- A single eventual estimate controls the actual T253 error uniformly over
an arbitrary index type; the finite grid and the loop family can both be put
in this index.  The data bundle lists only polynomial and positive-decay
premises. -/
theorem eventually_q_normalized_error_le {ι : Type*} (n r : ℕ)
    {L : ℕ → ι → ℕ}
    {A R K ζ δ M Pb e cE s v : ℕ → ι → ℝ}
    {τ' θ b τ₁ D Dexp d : ℝ}
    (h1 : (r : ℝ) * (1 + τ' + 2 * θ) + τ₁ - D < -d)
    (h2 : (r : ℝ) * (2 + τ') + 2 * b + τ₁ - D < -d)
    (h3 : (r : ℝ) * (2 + τ') + 2 * b - Dexp < -d)
    (h4 : (r : ℝ) + τ₁ - D < -d)
    (hData : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      v N i < 1 ∧ 0 ≤ K N i ∧ 0 ≤ M N i ∧ 0 ≤ δ N i ∧
      0 ≤ Pb N i ∧ 0 ≤ e N i ∧ 0 ≤ A N i ∧ 0 ≤ R N i ∧
      0 ≤ ζ N i ∧ 0 ≤ cE N i ∧
      A N i ≤ (N : ℝ) ∧ R N i ≤ (N : ℝ) ^ τ' ∧
      K N i ≤ (N : ℝ) ^ θ ∧ (L N i : ℝ) ≤ (N : ℝ) ∧
      (1 - s N i) / (1 - v N i) = R N i ∧
      0 ≤ errBudgetPoly (L N i) n (v N i) (K N i) (M N i) (Pb N i) (e N i) ∧
      errBudgetPoly (L N i) n (v N i) (K N i) (M N i) (Pb N i) (e N i)
        ≤ (N : ℝ) ^ b ∧
      ζ N i ≤ (N : ℝ) ^ (τ₁ - D) ∧
      δ N i ≤ (N : ℝ) ^ (τ₁ - D) ∧
      cE N i ≤ (N : ℝ) ^ (τ₁ - D) ∧
      Real.exp (-(cZero * K N i / 2)) ≤ (N : ℝ) ^ (-Dexp)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      (A N i) ^ r *
        (errKer716 (L N i) r (4 * K N i) (ζ N i)
          (FastDecayFlow.errBudget (L N i) n (v N i) (K N i)
            (M N i) (δ N i) (Pb N i) (e N i))
          (s N i) (v N i) + cE N i) ≤ (N : ℝ) ^ (-d) := by
  have hEnv := eventually_q_error_envelope_le r h1 h2 h3 h4
  filter_upwards [hData, hEnv, Filter.eventually_ge_atTop 1] with
    N hd henv hN i
  rcases hd i with ⟨hv, hK0, hM0, hδ0, hPb0, he0, hA0, hR0,
    hζ0, hcE0, hA, hR, hK, hL, hRatio, hPoly0, hPoly,
    hζ, hδ, hcE, hExp⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact (q_normalized_error_group_le n r N (L N i)
    hN1 hv hK0 hM0 hδ0 hPb0 he0 hA0 hR0 hζ0 hcE0
    hA hR hK hL hRatio hPoly0 hPoly hζ hδ hcE hExp).trans henv

/-- Uniform short-error decay with positive `ζ`, `δ`, and `cE`. -/
theorem eventually_short_normalized_error_le {ι : Type*} (r : ℕ)
    {κg τ' θ τ₁ D d : ℝ}
    (hκg : 0 < κg)
    (h1 : (r : ℝ) * (1 + τ' + θ) + τ₁ - D < -d)
    (h2 : (r : ℝ) * (1 + τ') + τ₁ - D < -d)
    (h3 : (r : ℝ) + τ₁ - D < -d)
    {A R K ζ δ cE s v : ℕ → ι → ℝ}
    (hData : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      0 ≤ A N i ∧ 0 ≤ R N i ∧ 0 ≤ K N i ∧
      0 ≤ ζ N i ∧ 0 ≤ δ N i ∧ 0 ≤ cE N i ∧
      A N i ≤ (N : ℝ) ∧ R N i ≤ (N : ℝ) ^ τ' ∧
      K N i ≤ (N : ℝ) ^ θ ∧
      (1 - s N i) / (1 - v N i) = R N i ∧
      ζ N i ≤ (N : ℝ) ^ (τ₁ - D) ∧
      δ N i ≤ (N : ℝ) ^ (τ₁ - D) ∧
      cE N i ≤ (N : ℝ) ^ (τ₁ - D)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      (A N i) ^ r *
        (errKer716Short r κg (K N i) (ζ N i) (δ N i)
          (s N i) (v N i) + cE N i) ≤ (N : ℝ) ^ (-d) := by
  have hEnv := eventually_short_error_envelope_le r hκg h1 h2 h3
  filter_upwards [hData, hEnv, Filter.eventually_ge_atTop 1] with
    N hd henv hN i
  rcases hd i with ⟨hA0, hR0, hK0, hζ0, hδ0, hcE0,
    hA, hR, hK, hRatio, hζ, hδ, hcE⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact (short_normalized_error_group_le r N hκg hN1 hA0 hR0 hK0
    hζ0 hδ0 hcE0 hA hR hK hRatio hζ hδ hcE).trans henv

/-- Common normalized arithmetic for the weighted Q and short `hnum` rows.
The exponent budget is deliberately loose: `x=N^(η/8)` leaves `x^4=N^(η/2)`.
Both additive errors may be strictly positive. -/
theorem weighted_hnum_normalized {a x c I cm c2 φ φE em e2 : ℝ}
    (ha : 0 ≤ a) (hx : 1 ≤ x) (hc : 1 ≤ c)
    (hI0 : 0 ≤ I) (hI : I ≤ x)
    (hcm0 : 0 ≤ cm) (hcm : cm ≤ x)
    (hc20 : 0 ≤ c2) (hc2 : c2 ≤ x ^ 2)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ c)
    (hφE0 : 0 ≤ φE) (hφE : φE ≤ c ^ 2)
    (hem0 : 0 ≤ em) (hem : em ≤ 1)
    (he20 : 0 ≤ e2) (he2 : e2 ≤ 1) :
    (cm * φ + em) * (1 + a * I) +
        (I * (c2 * φE + e2)) ^ ((1 : ℝ) / 2) ≤
      (4 + 2 * a) * x ^ 4 * c := by
  have hxc : 1 ≤ x * c := by nlinarith
  have hcmφ : cm * φ ≤ x * c :=
    mul_le_mul hcm hφ (by linarith) (by linarith)
  have hlin : cm * φ + em ≤ 2 * x * c := by nlinarith
  have hlin0 : 0 ≤ cm * φ + em := by positivity
  have hw : 1 + a * I ≤ (1 + a) * x := by nlinarith
  have hw0 : 0 ≤ 1 + a * I := by positivity
  have hfirst : (cm * φ + em) * (1 + a * I) ≤
      2 * (1 + a) * x ^ 2 * c := by
    have h := mul_le_mul hlin hw (by positivity) (by positivity)
    nlinarith [h]
  have hc2φE : c2 * φE ≤ x ^ 2 * c ^ 2 :=
    mul_le_mul hc2 hφE (by positivity) (by positivity)
  have hx2c2 : 1 ≤ x ^ 2 * c ^ 2 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (c - 1)]
  have hbr : c2 * φE + e2 ≤ 2 * x ^ 2 * c ^ 2 := by nlinarith
  have hbr0 : 0 ≤ c2 * φE + e2 := by positivity
  have hquad : I * (c2 * φE + e2) ≤ 2 * x ^ 3 * c ^ 2 := by
    have h := mul_le_mul hI hbr (by positivity) (by positivity)
    nlinarith [h]
  have hquad0 : 0 ≤ I * (c2 * φE + e2) := by positivity
  have hx38 : x ^ 3 ≤ x ^ 8 := pow_le_pow_right₀ hx (by norm_num)
  have hquadBig : I * (c2 * φE + e2) ≤ (2 * x ^ 4 * c) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hx38 (show 0 ≤ c ^ 2 by positivity)
    nlinarith [h]
  have hroot : (I * (c2 * φE + e2)) ^ ((1 : ℝ) / 2) ≤ 2 * x ^ 4 * c := by
    rw [← Real.sqrt_eq_rpow]
    calc
      Real.sqrt (I * (c2 * φE + e2)) ≤ Real.sqrt ((2 * x ^ 4 * c) ^ 2) :=
        Real.sqrt_le_sqrt hquadBig
      _ = 2 * x ^ 4 * c := Real.sqrt_sq (by positivity)
  have hx24 : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx (by norm_num)
  have hpow := mul_le_mul_of_nonneg_right hx24 (show 0 ≤ 2 * (1 + a) * c by positivity)
  nlinarith

/-- Move the normalized weighted row back to the exact inverse-scale syntax
required by both `'''` producers.  Unlike the zero-error bridge, both `em`
and `e2` remain present. -/
theorem weighted_hnum_scale (m : ℕ) {A I cm c2 φ φE em e2 w B : ℝ}
    (hA : 0 < A) (hI : 0 ≤ I) (hc2 : 0 ≤ c2) (hφE : 0 ≤ φE)
    (he2 : 0 ≤ e2)
    (hNorm : (cm * φ + A ^ m * em) * w +
      (I * (c2 * φE + A ^ (m + m) * e2)) ^ ((1 : ℝ) / 2) ≤ B) :
    (cm * A⁻¹ ^ m * φ + em) * w +
      (I * (c2 * A⁻¹ ^ (m + m) * φE + e2)) ^ ((1 : ℝ) / 2) ≤
      B * (A ^ m)⁻¹ := by
  have hAne : A ≠ 0 := hA.ne'
  have hcancel : A⁻¹ ^ m * A ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hAne, one_pow]
  have hcancel2 : A⁻¹ ^ (m + m) * A ^ (m + m) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hAne, one_pow]
  have hlin : cm * A⁻¹ ^ m * φ + em =
      A⁻¹ ^ m * (cm * φ + A ^ m * em) := by
    calc
      cm * A⁻¹ ^ m * φ + em =
          A⁻¹ ^ m * (cm * φ) + (A⁻¹ ^ m * A ^ m) * em := by rw [hcancel]; ring
      _ = _ := by ring
  have hquad : I * (c2 * A⁻¹ ^ (m + m) * φE + e2) =
      A⁻¹ ^ (m + m) * (I * (c2 * φE + A ^ (m + m) * e2)) := by
    calc
      I * (c2 * A⁻¹ ^ (m + m) * φE + e2) =
          A⁻¹ ^ (m + m) * (I * c2 * φE) +
            (A⁻¹ ^ (m + m) * A ^ (m + m)) * (I * e2) := by
              rw [hcancel2]
              ring
      _ = _ := by ring
  have hPhiE : 0 ≤ I * (c2 * φE + A ^ (m + m) * e2) := by positivity
  have haux := num_zero_err_aux m (cK := 1) (cK2 := 1) (A := A)
    (Phi := cm * φ + A ^ m * em)
    (PhiE := I * (c2 * φE + A ^ (m + m) * e2)) (w := w)
    (by norm_num) hA hPhiE
  calc
    (cm * A⁻¹ ^ m * φ + em) * w +
        (I * (c2 * A⁻¹ ^ (m + m) * φE + e2)) ^ ((1 : ℝ) / 2) =
      (A⁻¹ ^ m * (cm * φ + A ^ m * em)) * w +
        (A⁻¹ ^ (m + m) * (I * (c2 * φE + A ^ (m + m) * e2))) ^ ((1 : ℝ) / 2) := by
          rw [hlin, hquad]
    _ ≤ ((cm * φ + A ^ m * em) * w +
          (I * (c2 * φE + A ^ (m + m) * e2)) ^ ((1 : ℝ) / 2)) * (A ^ m)⁻¹ := by
            simpa only [one_mul] using haux
    _ ≤ B * (A ^ m)⁻¹ :=
      mul_le_mul_of_nonneg_right hNorm (by positivity)

/-- The exact inverse-scale weighted numeric row, with strictly positive errors
allowed.  The two error hypotheses are normalized at powers `m` and `2m`. -/
theorem weighted_hnum_of_normalized_budgets (m : ℕ)
    {a A I cm c2 φ φE em e2 x c : ℝ}
    (ha : 0 ≤ a) (hA : 0 < A) (hx : 1 ≤ x) (hc : 1 ≤ c)
    (hI0 : 0 ≤ I) (hI : I ≤ x)
    (hcm0 : 0 ≤ cm) (hcm : cm ≤ x)
    (hc20 : 0 ≤ c2) (hc2 : c2 ≤ x ^ 2)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ c)
    (hφE0 : 0 ≤ φE) (hφE : φE ≤ c ^ 2)
    (hem0 : 0 ≤ em) (hem : A ^ m * em ≤ 1)
    (he20 : 0 ≤ e2) (he2 : A ^ (m + m) * e2 ≤ 1) :
    (cm * A⁻¹ ^ m * φ + em) * (1 + a * I) +
      (I * (c2 * A⁻¹ ^ (m + m) * φE + e2)) ^ ((1 : ℝ) / 2) ≤
      ((4 + 2 * a) * x ^ 4 * c) * (A ^ m)⁻¹ := by
  have hNorm := weighted_hnum_normalized ha hx hc hI0 hI hcm0 hcm hc20 hc2
    hφ0 hφ hφE0 hφE (by positivity : 0 ≤ A ^ m * em) hem
    (by positivity : 0 ≤ A ^ (m + m) * e2) he2
  exact weighted_hnum_scale m hA hI0 hc20 hφE0 he20 hNorm

/-- The actual model moment inputs share a common envelope.  The square-root
term remains visible in the final coefficient. -/
theorem moment_envelopes_to_common {Cm Λ Φ φ φE : ℝ}
    (hCm : 1 ≤ Cm) (hΛ : 1 ≤ Λ) (hΦ : 0 ≤ Φ)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ Cm * (1 + Φ))
    (hφE0 : 0 ≤ φE) (hφE : φE ≤ Cm * Λ) :
    let c := Real.sqrt Λ + Φ
    1 ≤ c ∧ 0 ≤ φ ∧ φ ≤ 2 * Cm * c ∧
      0 ≤ φE ∧ φE ≤ (2 * Cm * c) ^ 2 := by
  let c : ℝ := Real.sqrt Λ + Φ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hs1 : 1 ≤ Real.sqrt Λ := by
    simpa using (Real.sqrt_le_sqrt hΛ)
  have hs0 : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg Λ
  have hs2 : (Real.sqrt Λ) ^ 2 = Λ := Real.sq_sqrt hΛ0
  have hc1 : 1 ≤ c := by dsimp [c]; linarith
  have hφb : φ ≤ 2 * Cm * c := by
    calc
      φ ≤ Cm * (1 + Φ) := hφ
      _ ≤ 2 * Cm * c := by
        dsimp [c]
        have hcm0 : 0 ≤ Cm := by linarith
        nlinarith [mul_nonneg hcm0 hΦ]
  have hΛc : Λ ≤ c ^ 2 := by
    dsimp [c]
    nlinarith [mul_nonneg hs0 hΦ, sq_nonneg Φ]
  have hφEb : φE ≤ (2 * Cm * c) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hΛc (by linarith : 0 ≤ Cm)
    have hc0 : 0 ≤ c := by linarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ Cm) (sq_nonneg c),
      mul_nonneg (by linarith : 0 ≤ Cm) (sq_nonneg c)]
  exact ⟨hc1, hφ0, hφb, hφE0, hφEb⟩

/-- The Q producer's exact weighted `hnum` syntax, reduced to explicit
coefficient, integral and positive-error budgets. -/
theorem weighted_q_hnum_of_budgets (n L : ℕ)
    {A K ζ δ' s v cE I x c φ φE : ℝ}
    (hA : 0 < A) (hx : 1 ≤ x) (hc : 1 ≤ c)
    (hI0 : 0 ≤ I) (hI : I ≤ x)
    (hK : 0 ≤ K) (hζ : 0 ≤ ζ) (hδ' : 0 ≤ δ')
    (hcE : 0 ≤ cE) (hsv : s ≤ v) (hv1 : v < 1)
    (hcm : cKer716 (n + 2) (4 * K) ≤ x)
    (hc2 : cKer716 ((n + 2) + (n + 2)) (4 * K) ≤ x ^ 2)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ c)
    (hφE0 : 0 ≤ φE) (hφE : φE ≤ c ^ 2)
    (hem : A ^ (n + 2) *
      (errKer716 L (n + 2) (4 * K) ζ δ' s v + cE) ≤ 1)
    (he2 : A ^ ((n + 2) + (n + 2)) *
      (errKer716 L ((n + 2) + (n + 2)) (4 * K) ζ δ' s v + cE) ≤ 1) :
    (cKer716 (n + 2) (4 * K) * A⁻¹ ^ (n + 2) * φ +
        (errKer716 L (n + 2) (4 * K) ζ δ' s v + cE)) * (1 + 6 * I) +
      (I * (cKer716 ((n + 2) + (n + 2)) (4 * K) *
          A⁻¹ ^ ((n + 2) + (n + 2)) * φE +
        (errKer716 L ((n + 2) + (n + 2)) (4 * K) ζ δ' s v + cE))) ^
          ((1 : ℝ) / 2) ≤
      (16 * x ^ 4 * c) * (A ^ (n + 2))⁻¹ := by
  have hem0 : 0 ≤ errKer716 L (n + 2) (4 * K) ζ δ' s v + cE := by
    exact add_nonneg (errKer716_nonneg L (n + 2) (by positivity) hζ hδ' hsv hv1) hcE
  have he20 : 0 ≤ errKer716 L ((n + 2) + (n + 2)) (4 * K) ζ δ' s v + cE := by
    exact add_nonneg (errKer716_nonneg L _ (by positivity) hζ hδ' hsv hv1) hcE
  have h := weighted_hnum_of_normalized_budgets (n + 2) (a := 6)
    (by norm_num : (0 : ℝ) ≤ 6) hA hx hc
    hI0 hI (cKer716_nonneg _ (by positivity)) hcm
    (cKer716_nonneg _ (by positivity)) hc2 hφ0 hφ hφE0 hφE
    hem0 hem he20 he2
  simpa only [show (4 : ℝ) + 2 * 6 = 16 by norm_num, mul_assoc] using h

/-- The short producer's exact weighted `hnum` syntax, with positive `ζ`,
`δ` and bad-event error retained. -/
theorem weighted_short_hnum_of_budgets (n : ℕ)
    {κg A K ζ δ s v cE I x c φ φE : ℝ}
    (hκg : 0 < κg) (hA : 0 < A) (hx : 1 ≤ x) (hc : 1 ≤ c)
    (hI0 : 0 ≤ I) (hI : I ≤ x)
    (hK : 0 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    (hcE : 0 ≤ cE) (hsv : s ≤ v) (hv1 : v < 1)
    (hcm : cKer716Short (n + 2) κg K ≤ x)
    (hc2 : cKer716Short ((n + 2) + (n + 2)) κg K ≤ x ^ 2)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ c)
    (hφE0 : 0 ≤ φE) (hφE : φE ≤ c ^ 2)
    (hem : A ^ (n + 2) *
      (errKer716Short (n + 2) κg K ζ δ s v + cE) ≤ 1)
    (he2 : A ^ ((n + 2) + (n + 2)) *
      (errKer716Short ((n + 2) + (n + 2)) κg K ζ δ s v + cE) ≤ 1) :
    (cKer716Short (n + 2) κg K * A⁻¹ ^ (n + 2) * φ +
        (errKer716Short (n + 2) κg K ζ δ s v + cE)) * (1 + 2 * I) +
      (I * (cKer716Short ((n + 2) + (n + 2)) κg K *
          A⁻¹ ^ ((n + 2) + (n + 2)) * φE +
        (errKer716Short ((n + 2) + (n + 2)) κg K ζ δ s v + cE))) ^
          ((1 : ℝ) / 2) ≤
      (8 * x ^ 4 * c) * (A ^ (n + 2))⁻¹ := by
  have hem0 : 0 ≤ errKer716Short (n + 2) κg K ζ δ s v + cE := by
    exact add_nonneg (errKer716Short_nonneg _ hκg hK hζ hδ hsv hv1) hcE
  have he20 : 0 ≤ errKer716Short ((n + 2) + (n + 2)) κg K ζ δ s v + cE := by
    exact add_nonneg (errKer716Short_nonneg _ hκg hK hζ hδ hsv hv1) hcE
  have h := weighted_hnum_of_normalized_budgets (n + 2) (a := 2)
    (by norm_num : (0 : ℝ) ≤ 2) hA hx hc
    hI0 hI (cKer716Short_nonneg _ hκg hK) hcm
    (cKer716Short_nonneg _ hκg hK) hc2 hφ0 hφ hφE0 hφE
    hem0 hem he20 he2
  simpa only [show (4 : ℝ) + 2 * 2 = 8 by norm_num, mul_assoc] using h

/-- The Q numeric row with the model moment assumptions displayed verbatim.
All other hypotheses are deterministic budgets proved above from small radius
and sufficiently strong positive-error decay. -/
theorem weighted_q_hnum_of_model_budgets (n L : ℕ)
    {A K ζ δ' s v cE I x Cm Λ Φ φ φE : ℝ}
    (hA : 0 < A) (hx : 1 ≤ x)
    (hI0 : 0 ≤ I) (hI : I ≤ x)
    (hK : 0 ≤ K) (hζ : 0 ≤ ζ) (hδ' : 0 ≤ δ')
    (hcE : 0 ≤ cE) (hsv : s ≤ v) (hv1 : v < 1)
    (hcm : cKer716 (n + 2) (4 * K) ≤ x)
    (hc2 : cKer716 ((n + 2) + (n + 2)) (4 * K) ≤ x ^ 2)
    (hCm : 1 ≤ Cm) (hΛ : 1 ≤ Λ) (hΦ : 0 ≤ Φ)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ Cm * (1 + Φ))
    (hφE0 : 0 ≤ φE) (hφE : φE ≤ Cm * Λ)
    (hem : A ^ (n + 2) *
      (errKer716 L (n + 2) (4 * K) ζ δ' s v + cE) ≤ 1)
    (he2 : A ^ ((n + 2) + (n + 2)) *
      (errKer716 L ((n + 2) + (n + 2)) (4 * K) ζ δ' s v + cE) ≤ 1) :
    (cKer716 (n + 2) (4 * K) * A⁻¹ ^ (n + 2) * φ +
        (errKer716 L (n + 2) (4 * K) ζ δ' s v + cE)) * (1 + 6 * I) +
      (I * (cKer716 ((n + 2) + (n + 2)) (4 * K) *
          A⁻¹ ^ ((n + 2) + (n + 2)) * φE +
        (errKer716 L ((n + 2) + (n + 2)) (4 * K) ζ δ' s v + cE))) ^
          ((1 : ℝ) / 2) ≤
      (32 * Cm * x ^ 4 * (Real.sqrt Λ + Φ)) * (A ^ (n + 2))⁻¹ := by
  obtain ⟨hc1, _, hφc, _, hφEc⟩ :=
    moment_envelopes_to_common hCm hΛ hΦ hφ0 hφ hφE0 hφE
  have h := weighted_q_hnum_of_budgets n L hA hx
    (show 1 ≤ 2 * Cm * (Real.sqrt Λ + Φ) by nlinarith)
    hI0 hI hK hζ hδ' hcE hsv hv1 hcm hc2 hφ0 hφc hφE0 hφEc hem he2
  convert h using 1 <;> ring

/-- The short numeric row keeps the same model moment envelopes, with the
short kernel's factor `1+2I` and coefficient `16 Cm`. -/
theorem weighted_short_hnum_of_model_budgets (n : ℕ)
    {κg A K ζ δ s v cE I x Cm Λ Φ φ φE : ℝ}
    (hκg : 0 < κg) (hA : 0 < A) (hx : 1 ≤ x)
    (hI0 : 0 ≤ I) (hI : I ≤ x)
    (hK : 0 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    (hcE : 0 ≤ cE) (hsv : s ≤ v) (hv1 : v < 1)
    (hcm : cKer716Short (n + 2) κg K ≤ x)
    (hc2 : cKer716Short ((n + 2) + (n + 2)) κg K ≤ x ^ 2)
    (hCm : 1 ≤ Cm) (hΛ : 1 ≤ Λ) (hΦ : 0 ≤ Φ)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ Cm * (1 + Φ))
    (hφE0 : 0 ≤ φE) (hφE : φE ≤ Cm * Λ)
    (hem : A ^ (n + 2) *
      (errKer716Short (n + 2) κg K ζ δ s v + cE) ≤ 1)
    (he2 : A ^ ((n + 2) + (n + 2)) *
      (errKer716Short ((n + 2) + (n + 2)) κg K ζ δ s v + cE) ≤ 1) :
    (cKer716Short (n + 2) κg K * A⁻¹ ^ (n + 2) * φ +
        (errKer716Short (n + 2) κg K ζ δ s v + cE)) * (1 + 2 * I) +
      (I * (cKer716Short ((n + 2) + (n + 2)) κg K *
          A⁻¹ ^ ((n + 2) + (n + 2)) * φE +
        (errKer716Short ((n + 2) + (n + 2)) κg K ζ δ s v + cE))) ^
          ((1 : ℝ) / 2) ≤
      (16 * Cm * x ^ 4 * (Real.sqrt Λ + Φ)) * (A ^ (n + 2))⁻¹ := by
  obtain ⟨hc1, _, hφc, _, hφEc⟩ :=
    moment_envelopes_to_common hCm hΛ hΦ hφ0 hφ hφE0 hφE
  have h := weighted_short_hnum_of_budgets n hκg hA hx
    (show 1 ≤ 2 * Cm * (Real.sqrt Λ + Φ) by nlinarith)
    hI0 hI hK hζ hδ hcE hsv hv1 hcm hc2 hφ0 hφc hφE0 hφEc hem he2
  convert h using 1 <;> ring

/-- The first actual grid cell has a positive time-integral cost. -/
noncomputable def firstCellI : ℝ :=
  ∫ u in gridS 2 1 0..gridS 2 1 1, (etaT 0 u)⁻¹

theorem firstCellI_pos : 0 < firstCellI := by
  rw [firstCellI, integral_etaT_inv_gridS_succ (by norm_num : |(0 : ℝ)| < 2)
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1) 0]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have him := mE_im_pos (by norm_num : |(0 : ℝ)| < 2)
  norm_num
  positivity

/-- T253's *actual* budget at positive first-cell inputs. -/
noncomputable def firstCellDeltaPrime : ℝ :=
  FastDecayFlow.errBudget 3 0 (1 / 2) 1 1 1 1 1

theorem firstCellDeltaPrime_pos : 0 < firstCellDeltaPrime := by
  have hc : 0 < cTwo52 := cTwo52_pos
  have hz : 0 < cZero := cZero_pos
  dsimp [firstCellDeltaPrime, FastDecayFlow.errBudget,
    FastDecayFlow.qopErr1, FastDecayFlow.commErrBd,
    FastDecayFlow.dotErrBd, FastDecayFlow.qqErrBd,
    FastDecayFlow.qBlockErrBd, FastDecayFlow.qBlockSizeBd]
  positivity

noncomputable def firstCellQActual : ℝ :=
  (cKer716 2 4 + (errKer716 3 2 4 1 firstCellDeltaPrime 0 (1 / 2) + 1)) *
      (1 + 6 * firstCellI) +
    (firstCellI * (cKer716 4 4 +
      (errKer716 3 4 4 1 firstCellDeltaPrime 0 (1 / 2) + 1))) ^ ((1 : ℝ) / 2)

noncomputable def firstCellShortActual : ℝ :=
  (cKer716Short 2 1 1 + (errKer716Short 2 1 1 1 1 0 (1 / 2) + 1)) *
      (1 + 2 * firstCellI) +
    (firstCellI * (cKer716Short 4 1 1 +
      (errKer716Short 4 1 1 1 1 0 (1 / 2) + 1))) ^ ((1 : ℝ) / 2)

/-- One common positive constant witnesses both weighted rows on `[0,1/2]`
with positive offset, decay, bad-event and actual T253 error budgets. -/
theorem positive_first_cell_numeric_witness (η : ℝ) (hη : 0 < η) :
    gridS 2 1 0 = 0 ∧ gridS 2 1 1 = (1 / 2 : ℝ) ∧
    0 < firstCellI ∧ 0 < firstCellDeltaPrime ∧
    ∃ C₀ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
      firstCellQActual ≤ C₀ * (N : ℝ) ^ (η / 2) ∧
      firstCellShortActual ≤ C₀ * (N : ℝ) ^ (η / 2) := by
  obtain ⟨hleft, hright⟩ := gridS_two_one_first
  refine ⟨hleft, hright, firstCellI_pos, firstCellDeltaPrime_pos, ?_⟩
  let C₀ : ℝ := max (max firstCellQActual firstCellShortActual) 0 + 1
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    have := le_max_right (max firstCellQActual firstCellShortActual) 0
    linarith
  refine ⟨C₀, hC₀, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hp : 1 ≤ (N : ℝ) ^ (η / 2) :=
    Real.one_le_rpow hN1 (by linarith)
  have hq : firstCellQActual ≤ C₀ := by
    dsimp [C₀]
    have := le_max_left firstCellQActual firstCellShortActual
    have := le_max_left (max firstCellQActual firstCellShortActual) 0
    linarith
  have hs : firstCellShortActual ≤ C₀ := by
    dsimp [C₀]
    have := le_max_right firstCellQActual firstCellShortActual
    have := le_max_left (max firstCellQActual firstCellShortActual) 0
    linarith
  have hCp : C₀ ≤ C₀ * (N : ℝ) ^ (η / 2) := by
    nlinarith [mul_nonneg hC₀.le (sub_nonneg.mpr hp)]
  exact ⟨hq.trans hCp, hs.trans hCp⟩

/-- Uniform weighted Q numeric row for any index and loop family.  In the
application the index is a finite grid cell, `I` is its exact logarithmic
integral, and `δ'` is instantiated by T253's `errBudget` using the preceding
uniform error theorem. -/
theorem eventually_weighted_q_hnum {ι : Type*} {Q : ℕ → ι → Type*}
    (n : ℕ) {η Cm d : ℝ} (hη : 0 < η) (hCm : 1 ≤ Cm) (hd : 0 ≤ d)
    {L : ℕ → ι → ℕ}
    {A K ζ δ' s v cE I Λ Φ : ℕ → ι → ℝ}
    {φ φE : ∀ N i, Q N i → ℝ}
    (hBase : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      0 < A N i ∧ 0 ≤ K N i ∧ 0 ≤ ζ N i ∧
      0 ≤ δ' N i ∧ 0 ≤ cE N i ∧ s N i ≤ v N i ∧
      v N i < 1 ∧ 1 ≤ Λ N i ∧ 0 ≤ Φ N i)
    (hI : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      0 ≤ I N i ∧ I N i ≤ (N : ℝ) ^ (η / 8))
    (hCoef : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      cKer716 (n + 2) (4 * K N i) ≤ (N : ℝ) ^ (η / 8) ∧
      cKer716 ((n + 2) + (n + 2)) (4 * K N i)
        ≤ ((N : ℝ) ^ (η / 8)) ^ 2)
    (hErr : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      (A N i) ^ (n + 2) *
        (errKer716 (L N i) (n + 2) (4 * K N i) (ζ N i) (δ' N i)
          (s N i) (v N i) + cE N i) ≤ (N : ℝ) ^ (-d) ∧
      (A N i) ^ ((n + 2) + (n + 2)) *
        (errKer716 (L N i) ((n + 2) + (n + 2)) (4 * K N i)
          (ζ N i) (δ' N i) (s N i) (v N i) + cE N i)
          ≤ (N : ℝ) ^ (-d))
    (hMom : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι, ∀ q : Q N i,
      0 ≤ φ N i q ∧ φ N i q ≤ Cm * (1 + Φ N i) ∧
      0 ≤ φE N i q ∧ φE N i q ≤ Cm * Λ N i) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι, ∀ q : Q N i,
      (cKer716 (n + 2) (4 * K N i) * (A N i)⁻¹ ^ (n + 2) * φ N i q +
          (errKer716 (L N i) (n + 2) (4 * K N i) (ζ N i) (δ' N i)
            (s N i) (v N i) + cE N i)) * (1 + 6 * I N i) +
        (I N i * (cKer716 ((n + 2) + (n + 2)) (4 * K N i) *
            (A N i)⁻¹ ^ ((n + 2) + (n + 2)) * φE N i q +
          (errKer716 (L N i) ((n + 2) + (n + 2)) (4 * K N i)
            (ζ N i) (δ' N i) (s N i) (v N i) + cE N i))) ^
            ((1 : ℝ) / 2) ≤
        (32 * Cm * (N : ℝ) ^ (η / 2) *
          (Real.sqrt (Λ N i) + Φ N i)) * ((A N i) ^ (n + 2))⁻¹ := by
  filter_upwards [hBase, hI, hCoef, hErr, hMom,
    Filter.eventually_ge_atTop 1] with N hb hi hc he hm hN i q
  rcases hb i with ⟨hA, hK, hζ, hδ', hcE, hsv, hv1, hΛ, hΦ⟩
  rcases hi i with ⟨hI0, hIle⟩
  rcases hc i with ⟨hc1, hc2⟩
  rcases he i with ⟨he1, he2⟩
  rcases hm i q with ⟨hφ0, hφ, hφE0, hφE⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hx : 1 ≤ (N : ℝ) ^ (η / 8) :=
    Real.one_le_rpow hN1 (by linarith)
  have hsmall : (N : ℝ) ^ (-d) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hpow : ((N : ℝ) ^ (η / 8)) ^ 4 = (N : ℝ) ^ (η / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  have h := weighted_q_hnum_of_model_budgets n (L N i) hA hx
    hI0 hIle hK hζ hδ' hcE hsv hv1 hc1 hc2
    hCm hΛ hΦ hφ0 hφ hφE0 hφE (he1.trans hsmall) (he2.trans hsmall)
  simpa only [hpow] using h

/-- Uniform weighted short numeric row for the same index and loop families.
The final envelope retains `sqrt Λ + Φ`, with `Λ ≥ 1`. -/
theorem eventually_weighted_short_hnum {ι : Type*} {Q : ℕ → ι → Type*}
    (n : ℕ) {κg η Cm d : ℝ}
    (hκg : 0 < κg) (hη : 0 < η) (hCm : 1 ≤ Cm) (hd : 0 ≤ d)
    {A K ζ δ s v cE I Λ Φ : ℕ → ι → ℝ}
    {φ φE : ∀ N i, Q N i → ℝ}
    (hBase : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      0 < A N i ∧ 0 ≤ K N i ∧ 0 ≤ ζ N i ∧
      0 ≤ δ N i ∧ 0 ≤ cE N i ∧ s N i ≤ v N i ∧
      v N i < 1 ∧ 1 ≤ Λ N i ∧ 0 ≤ Φ N i)
    (hI : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      0 ≤ I N i ∧ I N i ≤ (N : ℝ) ^ (η / 8))
    (hCoef : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      cKer716Short (n + 2) κg (K N i) ≤ (N : ℝ) ^ (η / 8) ∧
      cKer716Short ((n + 2) + (n + 2)) κg (K N i)
        ≤ ((N : ℝ) ^ (η / 8)) ^ 2)
    (hErr : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι,
      (A N i) ^ (n + 2) *
        (errKer716Short (n + 2) κg (K N i) (ζ N i) (δ N i)
          (s N i) (v N i) + cE N i) ≤ (N : ℝ) ^ (-d) ∧
      (A N i) ^ ((n + 2) + (n + 2)) *
        (errKer716Short ((n + 2) + (n + 2)) κg (K N i)
          (ζ N i) (δ N i) (s N i) (v N i) + cE N i)
          ≤ (N : ℝ) ^ (-d))
    (hMom : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι, ∀ q : Q N i,
      0 ≤ φ N i q ∧ φ N i q ≤ Cm * (1 + Φ N i) ∧
      0 ≤ φE N i q ∧ φE N i q ≤ Cm * Λ N i) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ι, ∀ q : Q N i,
      (cKer716Short (n + 2) κg (K N i) *
          (A N i)⁻¹ ^ (n + 2) * φ N i q +
          (errKer716Short (n + 2) κg (K N i) (ζ N i) (δ N i)
            (s N i) (v N i) + cE N i)) * (1 + 2 * I N i) +
        (I N i * (cKer716Short ((n + 2) + (n + 2)) κg (K N i) *
            (A N i)⁻¹ ^ ((n + 2) + (n + 2)) * φE N i q +
          (errKer716Short ((n + 2) + (n + 2)) κg (K N i)
            (ζ N i) (δ N i) (s N i) (v N i) + cE N i))) ^
            ((1 : ℝ) / 2) ≤
        (16 * Cm * (N : ℝ) ^ (η / 2) *
          (Real.sqrt (Λ N i) + Φ N i)) * ((A N i) ^ (n + 2))⁻¹ := by
  filter_upwards [hBase, hI, hCoef, hErr, hMom,
    Filter.eventually_ge_atTop 1] with N hb hi hc he hm hN i q
  rcases hb i with ⟨hA, hK, hζ, hδ, hcE, hsv, hv1, hΛ, hΦ⟩
  rcases hi i with ⟨hI0, hIle⟩
  rcases hc i with ⟨hc1, hc2⟩
  rcases he i with ⟨he1, he2⟩
  rcases hm i q with ⟨hφ0, hφ, hφE0, hφE⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hx : 1 ≤ (N : ℝ) ^ (η / 8) :=
    Real.one_le_rpow hN1 (by linarith)
  have hsmall : (N : ℝ) ^ (-d) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hpow : ((N : ℝ) ^ (η / 8)) ^ 4 = (N : ℝ) ^ (η / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  have h := weighted_short_hnum_of_model_budgets n hκg hA hx
    hI0 hIle hK hζ hδ hcE hsv hv1 hc1 hc2
    hCm hΛ hΦ hφ0 hφ hφE0 hφE (he1.trans hsmall) (he2.trans hsmall)
  simpa only [hpow] using h

#print axioms short_decay_group_le_rpow
#print axioms qBlockErrBd_decay_split
#print axioms qqErrBd_decay_split
#print axioms errBudget_decay_split
#print axioms errBudget_le_poly
#print axioms q_poly_group_le_rpow
#print axioms q_errBudget_group_le_rpow
#print axioms weighted_hnum_normalized
#print axioms weighted_hnum_scale
#print axioms weighted_hnum_of_normalized_budgets
#print axioms weighted_q_hnum_of_budgets
#print axioms weighted_short_hnum_of_budgets
#print axioms q_normalized_error_group_le
#print axioms short_normalized_error_group_le
#print axioms eventually_q_normalized_error_le
#print axioms eventually_short_normalized_error_le
#print axioms eventually_gridS_integral_le_rpow
#print axioms eventually_q_coefficient_le_rpow
#print axioms eventually_short_coefficient_le_rpow
#print axioms width_decay_le_nat_decay
#print axioms moment_envelopes_to_common
#print axioms weighted_q_hnum_of_model_budgets
#print axioms weighted_short_hnum_of_model_budgets
#print axioms positive_first_cell_numeric_witness
#print axioms eventually_weighted_q_hnum
#print axioms eventually_weighted_short_hnum

end RBM.Gauss
