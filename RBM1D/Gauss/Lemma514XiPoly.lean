/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Holder
import RBM1D.Gauss.Envelope
import RBM1D.Hierarchy.DriftBound

/-!
# Polynomial envelope for the `L-K` loop sum

The additive term in (5.77) needs only a polynomial bound on its finite loop sum.
The bound below uses the Hermitian resolvent estimate and the primitive-loop estimate;
it does not use Lemma 5.14 or Step 4.
-/

namespace RBM.Gauss

open Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- One constant covers the finite lengths `1,...,M`; length one is the explicit
`Band.norm_Kval_le` case and the remaining lengths use the existing bounded result. -/
theorem exists_norm_Kval_le_upto_one (B : Band Ω) {E : ℝ} (hE : |E| < 2) (M : ℕ) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (N : ℕ) (u : ℝ), 0 ≤ u → u < 1 →
      ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 1 ≤ J.length → J.length ≤ M →
        ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1) := by
  obtain ⟨κ, hκ0, hκ1, hEκ⟩ := exists_gap_of_abs_lt_two hE
  obtain ⟨C1, hC10, hC1⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 1) (by omega)
  obtain ⟨C2, hC20, hC2⟩ := exists_norm_Kval_le_upto B hE M
  refine ⟨max C1 C2, le_max_of_le_left hC10, fun N u hu0 hu1 J hJ hlen hM => ?_⟩
  have hA : 0 ≤ (B.scale E N u)⁻¹ ^ (J.length - 1) :=
    pow_nonneg (inv_nonneg.mpr (B.scale_pos' hE N hu0 hu1).le) _
  rcases eq_or_lt_of_le hlen with h1 | h2
  · have hk := hC1 N u hu0 hu1 J hJ h1.symm
    have hk' : ‖B.Kval E N u J‖ ≤
        C1 * (B.scale E N u)⁻¹ ^ (J.length - 1) := by simpa [← h1] using hk
    exact hk'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hA)
  · have hk := hC2 N u hu0 hu1 J hJ (by omega) hM
    exact hk.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hA)

/-- The crude flow window makes the inverse spectral height at most `N²`, uniformly
over the window. -/
theorem eventually_etaT_inv_le_sq_window (B : Band Ω) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT E (u : ℝ))⁻¹ ≤ (N : ℝ) ^ 2 := by
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  filter_upwards [SumZeroDyn.flow_crude hE hs0 hst ht1 hc,
    eventually_le_rpow (mE E).im⁻¹ one_pos] with N hcr hmN u
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hcr.2.2.1
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hpos : 0 < 1 - (u : ℝ) := by linarith
  have hinv : (1 - (u : ℝ))⁻¹ ≤ (N : ℝ) := (hcr.2.2.2 u).2.2
  have hmN' : (mE E).im⁻¹ ≤ (N : ℝ) := by simpa using hmN
  have hmul := mul_le_mul hinv hmN' (inv_nonneg.mpr hm0.le) hN0
  calc
    (etaT E (u : ℝ))⁻¹ = (1 - (u : ℝ))⁻¹ * (mE E).im⁻¹ := by
      rw [Step2.etaT_eq, mul_inv_rev]
      ring
    _ ≤ (N : ℝ) * N := hmul
    _ = (N : ℝ) ^ 2 := by ring

theorem eventually_rpow_neg_two_le_etaT_window (B : Band Ω) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT E (u : ℝ) := by
  filter_upwards [eventually_etaT_inv_le_sq_window B hE hs0 hst ht1 hc,
    eventually_ge_atTop 1] with N hN hN1 u
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hη0 : 0 < etaT E (u : ℝ) := etaT_pos hE (u.2.2.trans_lt (ht1 N))
  have h := inv_anti₀ (inv_pos.mpr hη0) (hN u)
  simpa [Real.rpow_neg, Real.rpow_natCast, inv_inv] using h

/-- A single loop length has a deterministic polynomial envelope. The value of `CK`
may depend on the chosen finite length cutoff, but the exponent does not. -/
theorem xiLK_le_poly_of_K (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {N m : ℕ} {u : ℝ} {ω : Ω} (hm : 1 ≤ m) (hu1 : u < 1)
    (hN1 : (1 : ℝ) ≤ N) (hA1 : 1 ≤ B.scale E N u)
    (hAN : B.scale E N u ≤ N) (hηN : (etaT E u)⁻¹ ≤ (N : ℝ) ^ 2)
    {CK : ℝ} (hCK : 0 ≤ CK)
    (hK : ∀ q : LoopData (B.L N) m,
      ‖B.Kval E N u q.idx‖ ≤ CK * (B.scale E N u)⁻¹ ^ (m - 1)) :
    X.xiLK E N u ω m ≤ (1 + CK) * (N : ℝ) ^ (3 * m + 1) := by
  have hN0 : 0 ≤ (N : ℝ) := by linarith
  have hA0 : 0 < B.scale E N u := by linarith
  have hη0 : 0 < etaT E u := etaT_pos hE hu1
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hWinv : (B.W N : ℝ)⁻¹ ≤ 1 := (inv_le_one_iff₀).2 (Or.inr hW1)
  have hWinv0 : 0 ≤ (B.W N : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hWinvPow : (B.W N : ℝ)⁻¹ ^ (m - 1) ≤ 1 :=
    pow_le_one₀ hWinv0 hWinv
  have hApow : B.scale E N u ^ (m - 1) ≤ (N : ℝ) ^ m := by
    calc
      _ ≤ (N : ℝ) ^ (m - 1) := pow_le_pow_left₀ hA0.le hAN _
      _ ≤ (N : ℝ) ^ m := pow_le_pow_right₀ hN1 (by omega)
  have hloop := loopXi_le_det (X.hermitian N u ω) hE hu1 hA0.le hm
  have hXiL : X.xiL E N u ω m ≤ (N : ℝ) ^ (3 * m) := by
    calc
      X.xiL E N u ω m ≤ (etaT E u)⁻¹ ^ m * (B.W N : ℝ)⁻¹ ^ (m - 1) *
          B.scale E N u ^ (m - 1) := hloop
      _ ≤ ((N : ℝ) ^ 2) ^ m * 1 * (N : ℝ) ^ m := by
        gcongr
      _ = (N : ℝ) ^ (3 * m) := by
        simp only [mul_one]
        rw [← mul_pow, show (N : ℝ) ^ 2 * N = (N : ℝ) ^ 3 by ring, pow_mul]
  have hraw := X.xiLK_le_mul (E := E) (N := N) (t := u) (ω := ω)
    (m := m) hA0 hm hK
  have hNp : (N : ℝ) ≤ (N : ℝ) ^ (3 * m + 1) := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ (N : ℝ) ^ (3 * m + 1) := pow_le_pow_right₀ hN1 (by omega)
  have hXiL0 : 0 ≤ X.xiL E N u ω m := X.xiL_nonneg hA0.le
  calc
    X.xiLK E N u ω m ≤ B.scale E N u * (X.xiL E N u ω m + CK) := hraw
    _ ≤ (N : ℝ) * ((N : ℝ) ^ (3 * m) + CK) := by gcongr
    _ = (N : ℝ) ^ (3 * m + 1) + CK * (N : ℝ) := by rw [pow_succ]; ring
    _ ≤ (1 + CK) * (N : ℝ) ^ (3 * m + 1) := by
      nlinarith [mul_nonneg hCK (sub_nonneg.mpr hNp)]

/-- The finite error sum in (5.77) has a deterministic polynomial envelope for
every sample point. No stochastic bound at its top length is used. -/
theorem exists_xiSum_poly_window (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (u : TimeIcc s t N) (ω : Ω),
        DriftBound.xiSum X E M N (u : ℝ) ω ≤ C * (N : ℝ) ^ (3 * M + 1) := by
  obtain ⟨CK, hCK, hK⟩ := exists_norm_Kval_le_upto_one B hE M
  refine ⟨(M : ℝ) * (1 + CK), by positivity, ?_⟩
  filter_upwards [SumZeroDyn.flow_crude hE hs0 hst ht1 hc,
    eventually_etaT_inv_le_sq_window B hE hs0 hst ht1 hc] with N hcr hη u ω
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hcr.2.2.1
  have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hA1 : 1 ≤ B.scale E N (u : ℝ) := (hcr.2.2.2 u).1
  have hAN : B.scale E N (u : ℝ) ≤ N := (hcr.2.2.2 u).2.1
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      X.xiLK E N (u : ℝ) ω m ≤ (1 + CK) * (N : ℝ) ^ (3 * M + 1) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
    have hk : ∀ q : LoopData (B.L N) m,
        ‖B.Kval E N (u : ℝ) q.idx‖ ≤
          CK * (B.scale E N (u : ℝ))⁻¹ ^ (m - 1) := by
      intro q
      simpa only [q.idx_length] using
        (hK N u hu0 hu1 q.idx q.idx_wf (by simpa using hm1) (by simpa using hmM))
    have hpt := xiLK_le_poly_of_K (ω := ω) X hE hm1 hu1 hN1 hA1 hAN (hη u) hCK hk
    exact hpt.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hN1 (by omega : 3 * m + 1 ≤ 3 * M + 1)) (by linarith))
  calc
    DriftBound.xiSum X E M N (u : ℝ) ω
        = ∑ m ∈ Finset.Icc 1 M, X.xiLK E N (u : ℝ) ω m := rfl
    _ ≤ ∑ _m ∈ Finset.Icc 1 M, (1 + CK) * (N : ℝ) ^ (3 * M + 1) :=
      Finset.sum_le_sum fun m hm => hterm m hm
    _ = (M : ℝ) * (1 + CK) * (N : ℝ) ^ (3 * M + 1) := by
      simp [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_assoc]

end RBM.Gauss
