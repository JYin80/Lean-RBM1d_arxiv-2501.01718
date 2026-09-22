/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514XiPoly
import RBM1D.Gauss.Step6EnvWindow
import RBM1D.Gauss.FastDecayFlow
import RBM1D.Hierarchy.DriftDef

/-!
# High-probability fast decay of the pinned drift

The deterministic Lemma-5.9 bound for the drift consumes the three decay clauses
and two sup bounds at all lengths up to `n+2`, including zero.  The latter are
polynomial on the actual flow window and are paid by choosing the input decay
exponent after `n`.
-/

namespace RBM.Gauss

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- Polynomial sup bounds for the two loop functions read by the drift decay
lemma.  The zero-length `L-K` loop is the nonzero trace `L W`; it is covered
separately rather than silently omitted. -/
theorem eventually_drift_loop_sizes (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) (n : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (u : TimeIcc s t N) (ω : Ω)
      (J : LoopIdx (ZMod (B.L N))), J.WF → J.length ≤ n + 2 →
      ‖B.Kval E N (u : ℝ) J‖ ≤ (N : ℝ) ^ (2 * (n + 2) + 3) ∧
      ‖(gloop (B.L N) (B.W N) (X.H N (u : ℝ) ω) (zt E (u : ℝ)) -
        B.Kval E N (u : ℝ)) J‖ ≤ (N : ℝ) ^ (2 * (n + 2) + 3) := by
  obtain ⟨CK, hCK, hK⟩ := exists_norm_Kval_le_upto_one B hE (n + 2)
  have habs := SumZeroDyn.eventually_const_mul_rpow_le (1 + CK)
    (show (2 * (n + 2) : ℝ) < (2 * (n + 2) + 3 : ℝ) by push_cast; linarith)
  filter_upwards [habs, SumZeroDyn.flow_crude hE hs0 hst ht1 hc,
    eventually_etaT_inv_le_sq_window B hE hs0 hst ht1 hc]
    with N habsN hcr hη u ω J hJ hJM
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hcr.2.2.1
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hA1 : 1 ≤ B.scale E N (u : ℝ) := (hcr.2.2.2 u).1
  have hAinv : (B.scale E N (u : ℝ))⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 hA1
  have hAinv0 : 0 ≤ (B.scale E N (u : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
  have hbig0 : 0 ≤ (N : ℝ) ^ (2 * (n + 2)) := pow_nonneg hN0 _
  have hbig1 : 1 ≤ (N : ℝ) ^ (2 * (n + 2)) := one_le_pow₀ hN1
  have habsNat : (1 + CK) * (N : ℝ) ^ (2 * (n + 2)) ≤
      (N : ℝ) ^ (2 * (n + 2) + 3) := by
    convert habsN using 1 <;> rw [← Real.rpow_natCast] <;> congr 1 <;> push_cast <;> ring
  have hKCK : 1 ≤ J.length → ‖B.Kval E N (u : ℝ) J‖ ≤ CK := by
    intro hJ1
    have hk := hK N u hu0 hu1 J hJ hJ1 hJM
    have hpow : (B.scale E N (u : ℝ))⁻¹ ^ (J.length - 1) ≤ 1 :=
      pow_le_one₀ hAinv0 hAinv
    exact hk.trans (by nlinarith [mul_nonneg hCK (sub_nonneg.mpr hpow)])
  by_cases hJ0 : J.length = 0
  · have hnil := loopIdx_eq_nil hJ hJ0
    subst J
    have hKzero : B.Kval E N (u : ℝ) (⟨[], []⟩ : LoopIdx (ZMod (B.L N))) = 0 := rfl
    have hLW : ((B.L N * B.W N : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
      have hL : (B.L N : ℝ) ≤ N := hcr.1
      have hW : (B.W N : ℝ) ≤ N := hcr.2.1
      have hW0 : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
      have h := mul_le_mul hL hW (Nat.cast_nonneg _) hN0
      simpa [Nat.cast_mul, pow_two] using h
    have hpow : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 * (n + 2) + 3) :=
      pow_le_pow_right₀ hN1 (by omega)
    constructor
    · simpa [hKzero] using (pow_nonneg hN0 (2 * (n + 2) + 3))
    · change ‖lkPath X E N (u : ℝ) ω (⟨[], []⟩ : LoopIdx (ZMod (B.L N)))‖ ≤ _
      rw [lkPath_nil]
      simpa using hLW.trans hpow
  · have hJ1 : 1 ≤ J.length := by omega
    have hk := hKCK hJ1
    have hg : ‖gloop (B.L N) (B.W N) (X.H N (u : ℝ) ω) (zt E (u : ℝ)) J‖ ≤
        (N : ℝ) ^ (2 * (n + 2)) := by
      have h := norm_gloop_le_win (X.hermitian N (u : ℝ) ω) hE hu0 le_rfl hu1
        (n + 2) J hJ hJ1 hJM
      exact h.trans (by
        have hp := pow_le_pow_left₀ (inv_nonneg.mpr (etaT_pos hE hu1).le)
          (hη u) (n + 2)
        simpa [pow_mul] using hp)
    have hsum : (N : ℝ) ^ (2 * (n + 2)) + CK ≤
        (1 + CK) * (N : ℝ) ^ (2 * (n + 2)) := by
      nlinarith [mul_nonneg hCK (sub_nonneg.mpr hbig1)]
    constructor
    · exact hk.trans (by
        have hck : CK ≤ (1 + CK) * (N : ℝ) ^ (2 * (n + 2)) := by nlinarith
        exact hck.trans habsNat)
    · exact (norm_sub_le _ _).trans ((add_le_add hg hk).trans (hsum.trans habsNat))

/-- The three additive errors of the deterministic drift decay lemma are bounded
by one polynomial factor, before the selectable input tail is applied. -/
private theorem drift_decay_budget_le_poly (n : ℕ) {W L N δ : ℝ}
    (hN : 1 ≤ N) (hW0 : 0 ≤ W) (hL0 : 0 ≤ L)
    (hWN : W ≤ N) (hLN : L ≤ N) (hδ : 0 ≤ δ) :
    W * ((n : ℝ) + 2) * (L * (N ^ (2 * (n + 2) + 3) * δ))
      + (n : ℝ) * (2 * (W * ((n : ℝ) + 2) ^ 2 * L * δ *
          (N ^ (2 * (n + 2) + 3) + N ^ (2 * (n + 2) + 3))))
      + 2 * W * ((n : ℝ) + 2) ^ 2 * L * δ * N ^ (2 * (n + 2) + 3)
      ≤ (((n : ℝ) + 2) + 4 * (n : ℝ) * ((n : ℝ) + 2) ^ 2
          + 2 * ((n : ℝ) + 2) ^ 2) * N ^ (2 * (n + 2) + 5) * δ := by
  have hN0 : 0 ≤ N := by linarith
  have hm0 : 0 ≤ (n : ℝ) + 2 := by positivity
  have hMb0 : 0 ≤ N ^ (2 * (n + 2) + 3) := pow_nonneg hN0 _
  calc
    _ ≤ N * ((n : ℝ) + 2) * (N * (N ^ (2 * (n + 2) + 3) * δ))
        + (n : ℝ) * (2 * (N * ((n : ℝ) + 2) ^ 2 * N * δ *
            (N ^ (2 * (n + 2) + 3) + N ^ (2 * (n + 2) + 3))))
        + 2 * N * ((n : ℝ) + 2) ^ 2 * N * δ * N ^ (2 * (n + 2) + 3) := by
          gcongr
    _ = (((n : ℝ) + 2) + 4 * (n : ℝ) * ((n : ℝ) + 2) ^ 2
          + 2 * ((n : ℝ) + 2) ^ 2) * N ^ (2 * (n + 2) + 5) * δ := by
          rw [show 2 * (n + 2) + 5 = (2 * (n + 2) + 3) + 2 by omega, pow_add]
          ring

/-- Choose the input decay exponent after `n`; the polynomial size of the
zero-length and positive-length loops is absorbed by the input tail. -/
private theorem eventually_drift_decay_budget (B : Band Ω) (n : ℕ) {D : ℝ} (hD : 0 < D) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ᶠ N : ℕ in atTop,
      1 ≤ (N : ℝ) ∧
      (B.W N : ℝ) * ((n : ℝ) + 2) *
          ((B.L N : ℝ) * ((N : ℝ) ^ (2 * (n + 2) + 3) * (N : ℝ) ^ (-D₀)))
        + (n : ℝ) * (2 * ((B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * (B.L N : ℝ) *
            (N : ℝ) ^ (-D₀) *
              ((N : ℝ) ^ (2 * (n + 2) + 3) + (N : ℝ) ^ (2 * (n + 2) + 3))))
        + 2 * (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * (B.L N : ℝ) *
            (N : ℝ) ^ (-D₀) * (N : ℝ) ^ (2 * (n + 2) + 3)
        ≤ (N : ℝ) ^ (-D) := by
  let b : ℕ := 2 * (n + 2) + 3
  let D₀ : ℝ := D + (b : ℝ) + 4
  let c : ℝ := ((n : ℝ) + 2) + 4 * (n : ℝ) * ((n : ℝ) + 2) ^ 2 +
    2 * ((n : ℝ) + 2) ^ 2
  have hev := SumZeroDyn.eventually_const_mul_rpow_le c
    (show -D - 2 < -D by linarith)
  refine ⟨D₀, by dsimp [D₀]; positivity, ?_⟩
  filter_upwards [hev, B.dim, eventually_ge_atTop 1] with N hevN hdim hN1
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hLpos : 0 < B.L N := by have := B.three_le_L N; omega
  have hWN : (B.W N : ℝ) ≤ N := by
    exact_mod_cast (Nat.le_trans
      (Nat.le_mul_of_pos_right (B.W N) hLpos) hdim.1)
  have hLN : (B.L N : ℝ) ≤ N := by
    exact_mod_cast (Nat.le_trans
      (Nat.le_mul_of_pos_left (B.L N) (B.W_pos N)) hdim.1)
  refine ⟨hN, ?_⟩
  have hpoly := drift_decay_budget_le_poly n (δ := (N : ℝ) ^ (-D₀))
    hN (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hWN hLN (Real.rpow_nonneg hN0.le _)
  have hpow : (N : ℝ) ^ (b + 2) * (N : ℝ) ^ (-D₀) =
      (N : ℝ) ^ (-D - 2) := by
    calc
      _ = (N : ℝ) ^ ((b : ℝ) + 2) * (N : ℝ) ^ (-D₀) := by
        rw [← Real.rpow_natCast]; congr 1; push_cast; ring
      _ = (N : ℝ) ^ ((b : ℝ) + 2 + -D₀) :=
        (Real.rpow_add hN0 ((b : ℝ) + 2) (-D₀)).symm
      _ = _ := by congr 1; dsimp [D₀]; ring
  exact hpoly.trans (by
    change c * (N : ℝ) ^ (b + 2) * (N : ℝ) ^ (-D₀) ≤ (N : ℝ) ^ (-D)
    rw [mul_assoc, hpow]
    exact hevN)

/-- The `H.F` fast-decay input of the projected-drift envelope.  Its event is
the same joint Lemma-5.9 event as the three decay clauses; the input tail is
chosen after the fixed loop length so the polynomial sup bounds are harmless. -/
theorem highProb_Fpath_fastDecay (X : Sample B) {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hFI : LKDecayQuant.FlowInputs X E s t) :
    ∀ θ > (0 : ℝ), ∀ D > (0 : ℝ),
      HighProb B.P (fun N => {ω | ∀ u : TimeIcc s t N,
        ∀ q : LoopData (B.L N) (n + 2),
          FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) *
            (4 * (N : ℝ) ^ θ)) ((N : ℝ) ^ (-D))
            (H.F N (u : ℝ) (X.H N (u : ℝ) ω) q.1)}) := by
  intro θ hθ D hD
  obtain ⟨D₀, hD₀, hbudget⟩ := eventually_drift_decay_budget B n hD
  have hdec := highProb_driftInputs_decay X hE hs0 ht1 hFI n θ hθ D₀ hD₀
  have hsize := eventually_drift_loop_sizes X hE hs0 hst ht1 hc n
  refine HighProb.mono hdec ?_
  filter_upwards [hbudget, hsize] with N hbudgetN hsizeN ω hω
  intro u q
  have hN1 : (1 : ℝ) ≤ N := hbudgetN.1
  have hN0 : (0 : ℝ) < N := by linarith
  have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hK1 : 1 ≤ (N : ℝ) ^ θ := Real.one_le_rpow hN1 hθ.le
  have hδ0 : 0 ≤ (N : ℝ) ^ (-D₀) := Real.rpow_nonneg hN0.le _
  have hM0 : 0 ≤ (N : ℝ) ^ (2 * (n + 2) + 3) := pow_nonneg hN0.le _
  have hfd := FastDecayFlow.fastDecay_driftF_window (δF := (N : ℝ) ^ (-D)) B E N (u : ℝ)
    (B.three_le_L N) hu0 hu1 (X.H N (u : ℝ) ω) q.1 hK1 hδ0 hM0 hM0
    (hω u).1 (hω u).2.1 (hω u).2.2
    (fun J hJ hJM => (hsizeN u ω J hJ hJM).1)
    (fun J hJ hJM => (hsizeN u ω J hJ hJM).2)
    (by convert hbudgetN.2 using 1 <;> ring)
  have hF : H.F N (u : ℝ) (X.H N (u : ℝ) ω) q.1 =
      DriftDef.driftF B E N (u : ℝ) (X.H N (u : ℝ) ω) q.1 := by
    funext a
    exact DriftDef.Fpath_eq_driftF_of_lt_one H hE hu0 hu1 u.2.1 u.2.2 ω q.1 a
  simpa only [hF] using hfd

/-- The joint decay event used above is eventually inhabited. -/
theorem eventually_Fpath_fastDecay_nonempty (X : Sample B) {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hFI : LKDecayQuant.FlowInputs X E s t) :
    ∀ θ > (0 : ℝ), ∀ D > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop, ({ω | ∀ u : TimeIcc s t N,
        ∀ q : LoopData (B.L N) (n + 2),
          FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) *
            (4 * (N : ℝ) ^ θ)) ((N : ℝ) ^ (-D))
            (H.F N (u : ℝ) (X.H N (u : ℝ) ω) q.1)} : Set Ω).Nonempty := by
  intro θ hθ D hD
  letI := B.isProbabilityMeasure
  exact (highProb_Fpath_fastDecay X H hE hs0 hst ht1 hc hFI θ hθ D hD).nonempty
    measure_univ

end RBM.Gauss
