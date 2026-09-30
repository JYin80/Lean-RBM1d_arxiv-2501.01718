/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.ContinuityAssembly

/-!
# Lemma 5.1 and its threshold generalization, at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.4, Lemma 5.1, and (6.1).

The hypothesis (6.1) and Lemma 5.1 at an `N`-dependent energy `E : ℕ → ℝ`. No declaration fixes
an energy-dependent constant: the `(mE E).im`-type quantities of the proofs are computed inside
the per-`N` proof (never fixed as a single constant before `∀ᶠ N`), so no κ-bound is needed.

## Main declarations

* `RBM.LoopScalingN` — (6.1) as a hypothesis, with its field `transfer`.
* `RBM.lemma_5_1N`, `RBM.lemma_5_1'N` — Lemma 5.1 (continuity estimate on loops), the second one
  in the form (5.7).
* `RBM.lemma_5_1_thrN`, `RBM.lemma_5_1'_thrN` — the same at a general threshold `C₀ ≥ 0`.
-/

namespace RBM

open Filter MeasureTheory

section Lemma51N

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(6.1) as a hypothesis**, at an `N`-dependent energy. -/
structure LoopScalingN (X : Sample B) (E : ℕ → ℝ) (t₁ t₂ : ℕ → ℝ) : Prop where
  transfer : ∀ n : ℕ, 1 ≤ n → ∀ ζ : ℕ → ℝ,
    StochDom B.P (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval (E N) N (t₁ N) ω u.idx‖)
      (fun N _ _ => ζ N) →
    StochDom B.P (fun N (u : LoopData (B.L N) n) ω =>
      ‖gloop (B.L N) (B.W N) (X.H N (t₂ N) ω) (ztTilde (E N) (t₁ N) (t₂ N)) u.idx‖)
      (fun N _ _ => ζ N)

variable {X : Sample B}

/-- **Lemma 5.1 (continuity estimate on loops)**, at an `N`-dependent energy `E : ℕ → ℝ` with
`|E N| ≤ 2 - κ` for every `N`. -/
theorem lemma_5_1N (X : Sample B) {E : ℕ → ℝ} {κ c : ℝ} (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hc : 0 < c)
    {t₁ t₂ : ℕ → ℝ} (h₁ : ∀ N, c ≤ t₁ N) (h₁₂ : ∀ N, t₁ N ≤ t₂ N) (h₂ : ∀ N, t₂ N < 1)
    (hS : LoopScalingN X E t₁ t₂)
    (h55 : ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval (E N) N (t₁ N) ω u.idx‖)
      (fun N _ _ => (B.scale (E N) N (t₁ N))⁻¹ ^ (n - 1))) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω =>
        (X.gmaxEvent (E N) t₂ N).indicator (fun ω => ‖X.Lval (E N) N (t₂ N) ω u.idx‖) ω)
      (fun N _ _ => ((B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₂ N))⁻¹ ^ (n - 1)) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  obtain ⟨C, hC0, hC⟩ := ztTilde_arith hc hκ
  set a : ℕ → ℝ := fun N => ((B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₂ N))⁻¹ with ha_def
  set a1 : ℕ → ℝ := fun N => (B.scale (E N) N (t₁ N))⁻¹ with ha1_def
  set zz : ℕ → ℂ := fun N => zt (E N) (t₂ N)
  set zw : ℕ → ℂ := fun N => ztTilde (E N) (t₁ N) (t₂ N)
  set K : ℕ → ℝ := fun N => ‖zz N - zw N‖ ^ 2 * ((zz N).im * (zw N).im)⁻¹ with hK_def
  have ht₁0 : ∀ N, 0 < t₁ N := fun N => hc.trans_le (h₁ N)
  have ht₁1 : ∀ N, t₁ N < 1 := fun N => (h₁₂ N).trans_lt (h₂ N)
  have hW : ∀ N, (0 : ℝ) < B.W N := fun N => by exact_mod_cast B.W_pos N
  have hℓ : ∀ N, 1 ≤ B.ell N (t₁ N) := fun N =>
    one_le_ellHat (B.L N) (B.three_le_L N) (ht₁0 N).le (ht₁1 N)
  have hη1 : ∀ N, 0 < etaT (E N) (t₁ N) := fun N => etaT_pos (hE2 N) (ht₁1 N)
  have hη2 : ∀ N, 0 < etaT (E N) (t₂ N) := fun N => etaT_pos (hE2 N) (h₂ N)
  have hmIm : ∀ N, 0 ≤ (mE (E N)).im := fun N => (mE_im_pos (hE2 N)).le
  have hη12 : ∀ N, etaT (E N) (t₂ N) ≤ etaT (E N) (t₁ N) := fun N => by
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith [h₁₂ N]) (hmIm N)
  have hzz : ∀ N, (zz N).im = etaT (E N) (t₂ N) := fun N => (etaT_eq_zt_im (E N) (t₂ N)).symm
  have harith := fun N => hC (E N) (t₁ N) (t₂ N) (h₁ N) (h₁₂ N) (h₂ N).le (hE N)
  have hzw : ∀ N, etaT (E N) (t₁ N) ≤ (zw N).im := fun N => (harith N).2.2.2.1
  have hzw0 : ∀ N, 0 < (zw N).im := fun N => (hη1 N).trans_le (hzw N)
  have hA2 : ∀ N, 0 < (B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₂ N) := fun N =>
    mul_pos (mul_pos (hW N) (by linarith [hℓ N])) (hη2 N)
  have ha1 : ∀ N, 0 < a1 N := fun N => inv_pos.mpr (B.scale_pos (hE2 N) N (ht₁0 N) (ht₁1 N))
  have ha1a : ∀ N, a1 N ≤ a N := fun N => by
    simp only [ha1_def, ha_def, Band.scale]
    refine inv_anti₀ (hA2 N) ?_
    have hℓ0 : (0 : ℝ) < B.ell N (t₁ N) := by linarith [hℓ N]
    exact mul_le_mul_of_nonneg_left (hη12 N) (mul_pos (hW N) hℓ0).le
  have hK0 : ∀ N, 0 ≤ K N := fun N =>
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (mul_nonneg (by rw [hzz]; exact (hη2 N).le)
      (hzw0 N).le))
  have hK : ∀ N, K N * a1 N ≤ C * a N := by
    intro N
    have hsq := (harith N).2.1
    set x := ‖zz N - zw N‖ ^ 2
    have hx : x ≤ C * etaT (E N) (t₁ N) * (zw N).im := by
      calc x ≤ C * etaT (E N) (t₁ N) ^ 2 := hsq
        _ = C * etaT (E N) (t₁ N) * etaT (E N) (t₁ N) := by ring
        _ ≤ C * etaT (E N) (t₁ N) * (zw N).im :=
            mul_le_mul_of_nonneg_left (hzw N) (mul_nonneg hC0.le (hη1 N).le)
    simp only [hK_def, ha1_def, ha_def, Band.scale, hzz]
    have hq := hzw0 N
    have hℓ0 : 0 < B.ell N (t₁ N) := by linarith [hℓ N]
    have hden : 0 < etaT (E N) (t₂ N) * (zw N).im := mul_pos (hη2 N) hq
    calc
      x * (etaT (E N) (t₂ N) * (zw N).im)⁻¹
          * ((B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₁ N))⁻¹
        ≤ (C * etaT (E N) (t₁ N) * (zw N).im) * (etaT (E N) (t₂ N) * (zw N).im)⁻¹
          * ((B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₁ N))⁻¹ := by
          have hA1 : 0 < (B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₁ N) :=
            mul_pos (mul_pos (hW N) hℓ0) (hη1 N)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx
            (inv_nonneg.mpr hden.le)) (inv_nonneg.mpr hA1.le)
      _ = C * ((B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₂ N))⁻¹ := by
          have := hη1 N; have := hη2 N; have := hW N
          field_simp
  have hNev : ∀ᶠ N : ℕ in atTop, (a1 N)⁻¹ ≤ N := by
    filter_upwards [B.dim] with N hdim
    simp only [ha1_def, inv_inv, Band.scale]
    have hWL : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
    have hℓL : B.ell N (t₁ N) ≤ B.L N := min_le_right _ _
    have hη1' : etaT (E N) (t₁ N) ≤ 1 := by
      unfold etaT
      have hm1 : (mE (E N)).im ≤ 1 := (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans
        (norm_mE (by linarith [hE2 N])).le)
      have : 1 - t₁ N ≤ 1 := by linarith [ht₁0 N]
      nlinarith [ht₁1 N]
    calc (B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₁ N) ≤ (B.W N : ℝ) * B.L N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hℓL (hW N).le) hη1' (hη1 N).le
            (mul_nonneg (hW N).le (Nat.cast_nonneg _))
      _ ≤ N := by rw [mul_one]; exact hWL
  set Ωs : ℕ → Set Ω := fun N => X.gmaxEvent (E N) t₂ N with hΩs
  set Y : ℕ → ∀ N, (fun _ => Unit) N → Ω → ℝ := fun n N _ ω =>
    (Ωs N).indicator (fun ω => loopMax (B.L N) (B.W N) (X.H N (t₂ N) ω) (zz N) n) ω with hY
  set T : ℕ → ∀ N, (fun _ => Unit) N → Ω → ℝ := fun n N _ ω =>
    loopMax (B.L N) (B.W N) (X.H N (t₂ N) ω) (zw N) n with hT
  have hY0 : ∀ n N u ω, 0 ≤ Y n N u ω := fun n N u ω =>
    Set.indicator_nonneg (fun ω _ => loopMax_nonneg _) ω
  have hT0 : ∀ n N u ω, 0 ≤ T n N u ω := fun n N u ω => loopMax_nonneg _
  have hTd : ∀ n, 1 ≤ n → StochDom B.P (T n) (fun N _ _ => a1 N ^ (n - 1)) := fun n hn =>
    stochDom_loopMax_of_loopData (hS.transfer n hn _ (h55 n hn))
  have hY1 : ∀ N u ω, Y 1 N u ω ≤ 2 := by
    intro N u ω
    by_cases hω : ω ∈ Ωs N
    · simp only [hY, Set.indicator_of_mem hω]
      exact loopMax_one_le (X.hermitian N (t₂ N) ω) (fun i => hω i i)
    · simp only [hY, Set.indicator_of_notMem hω]
      norm_num
  have hodd : ∀ l, 1 ≤ l → ∀ N u ω,
      Y (2 * l + 1) N u ω ^ 2 ≤ Y (2 * l) N u ω * Y (2 * l + 2) N u ω := by
    intro l hl N u ω
    by_cases hω : ω ∈ Ωs N
    · simp only [hY, Set.indicator_of_mem hω]
      exact loopMax_odd_sq_le (X.hermitian N (t₂ N) ω) hl
    · simp [hY, Set.indicator_of_notMem hω]
  have hrec : ∀ m, 1 ≤ m → ∀ p, 1 ≤ p → ∀ N u ω, Y (2 * m) N u ω ≤ (m + 1 : ℝ) *
      (T (2 * m) N u ω + K N * ∑ l ∈ Finset.range m,
        Y (2 * l + 1) N u ω * T (p * (2 * (m - l) - 1)) N u ω ^ (1 / (p : ℝ))) := by
    intro m hm p hp N u ω
    by_cases hω : ω ∈ Ωs N
    · simp only [hY, hT, Set.indicator_of_mem hω]
      have hz : 0 < (zz N).im := by rw [hzz]; exact hη2 N
      refine (loopMax_two_mul_le_tilde (X.hermitian N (t₂ N) ω) hz (hzw0 N) hm hp).trans
        (le_of_eq ?_)
      simp only [hK_def]
      ring
    · simp only [hY, hT, Set.indicator_of_notMem hω, zero_mul, Finset.sum_const_zero,
        mul_zero, add_zero]
      exact mul_nonneg (by positivity) (loopMax_nonneg _)
  have hmain := StochDom.continuity_recursion (P := B.P) hY0 hT0 ha1 ha1a hK0 hC0.le hK hNev
    hTd hY1 hodd hrec
  intro n hn
  have h1 := (hmain n hn).precomp_param (fun N (_ : LoopData (B.L N) n) => ())
  refine StochDom.of_le_left (fun N u ω => ?_) h1
  exact Set.indicator_le_indicator
    (norm_gloop_le_loopMax u.idx (by simp [LoopData.idx]) (by simp [LoopData.idx]))

/-- **Lemma 5.1, (5.7) in the paper's second form**, at an `N`-dependent energy. -/
theorem lemma_5_1'N (X : Sample B) {E : ℕ → ℝ} {κ c : ℝ} (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hc : 0 < c)
    {t₁ t₂ : ℕ → ℝ} (h₁ : ∀ N, c ≤ t₁ N) (h₁₂ : ∀ N, t₁ N ≤ t₂ N) (h₂ : ∀ N, t₂ N < 1)
    (hS : LoopScalingN X E t₁ t₂)
    (h55 : ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval (E N) N (t₁ N) ω u.idx‖)
      (fun N _ _ => (B.scale (E N) N (t₁ N))⁻¹ ^ (n - 1))) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω =>
        (X.gmaxEvent (E N) t₂ N).indicator (fun ω => ‖X.Lval (E N) N (t₂ N) ω u.idx‖) ω)
      (fun N _ _ => (B.ell N (t₂ N) / B.ell N (t₁ N)) ^ (n - 1)
        * (B.scale (E N) N (t₂ N))⁻¹ ^ (n - 1)) := by
  intro n hn
  have h := lemma_5_1N X hκ hE hc h₁ h₁₂ h₂ hS h55 n hn
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  convert h using 3 with N u ω
  have ht₂0 : 0 < t₂ N := (hc.trans_le (h₁ N)).trans_le (h₁₂ N)
  have hℓ1 : 0 < B.ell N (t₁ N) := lt_of_lt_of_le zero_lt_one
    (one_le_ellHat (B.L N) (B.three_le_L N) (hc.trans_le (h₁ N)).le ((h₁₂ N).trans_lt (h₂ N)))
  have hℓ2 : 0 < B.ell N (t₂ N) := lt_of_lt_of_le zero_lt_one
    (one_le_ellHat (B.L N) (B.three_le_L N) ht₂0.le (h₂ N))
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hη : 0 < etaT (E N) (t₂ N) := etaT_pos (hE2 N) (h₂ N)
  rw [← mul_pow, Band.scale]
  field_simp

/-- **Lemma 5.1 at a general threshold `C₀ ≥ 0`**, at an `N`-dependent energy. -/
theorem lemma_5_1_thrN (X : Sample B) {E : ℕ → ℝ} {κ c C₀ : ℝ} (hκ : 0 < κ)
    (hE : ∀ N, |E N| ≤ 2 - κ) (hc : 0 < c) (hC₀ : 0 ≤ C₀)
    {t₁ t₂ : ℕ → ℝ} (h₁ : ∀ N, c ≤ t₁ N) (h₁₂ : ∀ N, t₁ N ≤ t₂ N) (h₂ : ∀ N, t₂ N < 1)
    (hS : LoopScalingN X E t₁ t₂)
    (h55 : ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval (E N) N (t₁ N) ω u.idx‖)
      (fun N _ _ => (B.scale (E N) N (t₁ N))⁻¹ ^ (n - 1))) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω =>
        (X.gmaxEventThr (E N) t₂ C₀ N).indicator (fun ω => ‖X.Lval (E N) N (t₂ N) ω u.idx‖) ω)
      (fun N _ _ => ((B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₂ N))⁻¹ ^ (n - 1)) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  obtain ⟨C, hC0, hC⟩ := ztTilde_arith hc hκ
  set a : ℕ → ℝ := fun N => ((B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₂ N))⁻¹ with ha_def
  set a1 : ℕ → ℝ := fun N => (B.scale (E N) N (t₁ N))⁻¹ with ha1_def
  set zz : ℕ → ℂ := fun N => zt (E N) (t₂ N)
  set zw : ℕ → ℂ := fun N => ztTilde (E N) (t₁ N) (t₂ N)
  set K : ℕ → ℝ := fun N => ‖zz N - zw N‖ ^ 2 * ((zz N).im * (zw N).im)⁻¹ with hK_def
  have ht₁0 : ∀ N, 0 < t₁ N := fun N => hc.trans_le (h₁ N)
  have ht₁1 : ∀ N, t₁ N < 1 := fun N => (h₁₂ N).trans_lt (h₂ N)
  have hW : ∀ N, (0 : ℝ) < B.W N := fun N => by exact_mod_cast B.W_pos N
  have hℓ : ∀ N, 1 ≤ B.ell N (t₁ N) := fun N =>
    one_le_ellHat (B.L N) (B.three_le_L N) (ht₁0 N).le (ht₁1 N)
  have hη1 : ∀ N, 0 < etaT (E N) (t₁ N) := fun N => etaT_pos (hE2 N) (ht₁1 N)
  have hη2 : ∀ N, 0 < etaT (E N) (t₂ N) := fun N => etaT_pos (hE2 N) (h₂ N)
  have hmIm : ∀ N, 0 ≤ (mE (E N)).im := fun N => (mE_im_pos (hE2 N)).le
  have hη12 : ∀ N, etaT (E N) (t₂ N) ≤ etaT (E N) (t₁ N) := fun N => by
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith [h₁₂ N]) (hmIm N)
  have hzz : ∀ N, (zz N).im = etaT (E N) (t₂ N) := fun N => (etaT_eq_zt_im (E N) (t₂ N)).symm
  have harith := fun N => hC (E N) (t₁ N) (t₂ N) (h₁ N) (h₁₂ N) (h₂ N).le (hE N)
  have hzw : ∀ N, etaT (E N) (t₁ N) ≤ (zw N).im := fun N => (harith N).2.2.2.1
  have hzw0 : ∀ N, 0 < (zw N).im := fun N => (hη1 N).trans_le (hzw N)
  have hA2 : ∀ N, 0 < (B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₂ N) := fun N =>
    mul_pos (mul_pos (hW N) (by linarith [hℓ N])) (hη2 N)
  have ha1 : ∀ N, 0 < a1 N := fun N => inv_pos.mpr (B.scale_pos (hE2 N) N (ht₁0 N) (ht₁1 N))
  have ha1a : ∀ N, a1 N ≤ a N := fun N => by
    simp only [ha1_def, ha_def, Band.scale]
    refine inv_anti₀ (hA2 N) ?_
    have hℓ0 : (0 : ℝ) < B.ell N (t₁ N) := by linarith [hℓ N]
    exact mul_le_mul_of_nonneg_left (hη12 N) (mul_pos (hW N) hℓ0).le
  have hK0 : ∀ N, 0 ≤ K N := fun N =>
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (mul_nonneg (by rw [hzz]; exact (hη2 N).le)
      (hzw0 N).le))
  have hK : ∀ N, K N * a1 N ≤ C * a N := by
    intro N
    have hsq := (harith N).2.1
    set x := ‖zz N - zw N‖ ^ 2
    have hx : x ≤ C * etaT (E N) (t₁ N) * (zw N).im := by
      calc x ≤ C * etaT (E N) (t₁ N) ^ 2 := hsq
        _ = C * etaT (E N) (t₁ N) * etaT (E N) (t₁ N) := by ring
        _ ≤ C * etaT (E N) (t₁ N) * (zw N).im :=
            mul_le_mul_of_nonneg_left (hzw N) (mul_nonneg hC0.le (hη1 N).le)
    simp only [hK_def, ha1_def, ha_def, Band.scale, hzz]
    have hq := hzw0 N
    have hℓ0 : 0 < B.ell N (t₁ N) := by linarith [hℓ N]
    have hden : 0 < etaT (E N) (t₂ N) * (zw N).im := mul_pos (hη2 N) hq
    calc
      x * (etaT (E N) (t₂ N) * (zw N).im)⁻¹
          * ((B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₁ N))⁻¹
        ≤ (C * etaT (E N) (t₁ N) * (zw N).im) * (etaT (E N) (t₂ N) * (zw N).im)⁻¹
          * ((B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₁ N))⁻¹ := by
          have hA1 : 0 < (B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₁ N) :=
            mul_pos (mul_pos (hW N) hℓ0) (hη1 N)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx
            (inv_nonneg.mpr hden.le)) (inv_nonneg.mpr hA1.le)
      _ = C * ((B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₂ N))⁻¹ := by
          have := hη1 N; have := hη2 N; have := hW N
          field_simp
  have hNev : ∀ᶠ N : ℕ in atTop, (a1 N)⁻¹ ≤ N := by
    filter_upwards [B.dim] with N hdim
    simp only [ha1_def, inv_inv, Band.scale]
    have hWL : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
    have hℓL : B.ell N (t₁ N) ≤ B.L N := min_le_right _ _
    have hη1' : etaT (E N) (t₁ N) ≤ 1 := by
      unfold etaT
      have hm1 : (mE (E N)).im ≤ 1 := (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans
        (norm_mE (by linarith [hE2 N])).le)
      have : 1 - t₁ N ≤ 1 := by linarith [ht₁0 N]
      nlinarith [ht₁1 N]
    calc (B.W N : ℝ) * B.ell N (t₁ N) * etaT (E N) (t₁ N) ≤ (B.W N : ℝ) * B.L N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hℓL (hW N).le) hη1' (hη1 N).le
            (mul_nonneg (hW N).le (Nat.cast_nonneg _))
      _ ≤ N := by rw [mul_one]; exact hWL
  set Ωs : ℕ → Set Ω := fun N => X.gmaxEventThr (E N) t₂ C₀ N with hΩs
  set Y : ℕ → ∀ N, (fun _ => Unit) N → Ω → ℝ := fun n N _ ω =>
    (Ωs N).indicator (fun ω => loopMax (B.L N) (B.W N) (X.H N (t₂ N) ω) (zz N) n) ω with hY
  set T : ℕ → ∀ N, (fun _ => Unit) N → Ω → ℝ := fun n N _ ω =>
    loopMax (B.L N) (B.W N) (X.H N (t₂ N) ω) (zw N) n with hT
  have hY0 : ∀ n N u ω, 0 ≤ Y n N u ω := fun n N u ω =>
    Set.indicator_nonneg (fun ω _ => loopMax_nonneg _) ω
  have hT0 : ∀ n N u ω, 0 ≤ T n N u ω := fun n N u ω => loopMax_nonneg _
  have hTd : ∀ n, 1 ≤ n → StochDom B.P (T n) (fun N _ _ => a1 N ^ (n - 1)) := fun n hn =>
    stochDom_loopMax_of_loopData (hS.transfer n hn _ (h55 n hn))
  have hY1 : ∀ N u ω, Y 1 N u ω ≤ C₀ := by
    intro N u ω
    by_cases hω : ω ∈ Ωs N
    · simp only [hY, Set.indicator_of_mem hω]
      exact loopMax_one_le (X.hermitian N (t₂ N) ω) (fun i => hω i i)
    · simp only [hY, Set.indicator_of_notMem hω]
      exact hC₀
  have hodd : ∀ l, 1 ≤ l → ∀ N u ω,
      Y (2 * l + 1) N u ω ^ 2 ≤ Y (2 * l) N u ω * Y (2 * l + 2) N u ω := by
    intro l hl N u ω
    by_cases hω : ω ∈ Ωs N
    · simp only [hY, Set.indicator_of_mem hω]
      exact loopMax_odd_sq_le (X.hermitian N (t₂ N) ω) hl
    · simp [hY, Set.indicator_of_notMem hω]
  have hrec : ∀ m, 1 ≤ m → ∀ p, 1 ≤ p → ∀ N u ω, Y (2 * m) N u ω ≤ (m + 1 : ℝ) *
      (T (2 * m) N u ω + K N * ∑ l ∈ Finset.range m,
        Y (2 * l + 1) N u ω * T (p * (2 * (m - l) - 1)) N u ω ^ (1 / (p : ℝ))) := by
    intro m hm p hp N u ω
    by_cases hω : ω ∈ Ωs N
    · simp only [hY, hT, Set.indicator_of_mem hω]
      have hz : 0 < (zz N).im := by rw [hzz]; exact hη2 N
      refine (loopMax_two_mul_le_tilde (X.hermitian N (t₂ N) ω) hz (hzw0 N) hm hp).trans
        (le_of_eq ?_)
      simp only [hK_def]
      ring
    · simp only [hY, hT, Set.indicator_of_notMem hω, zero_mul, Finset.sum_const_zero,
        mul_zero, add_zero]
      exact mul_nonneg (by positivity) (loopMax_nonneg _)
  have hmain := StochDom.continuity_recursion_thr (P := B.P) hY0 hT0 ha1 ha1a hK0 hC0.le hK hNev
    hTd hC₀ hY1 hodd hrec
  intro n hn
  have h1 := (hmain n hn).precomp_param (fun N (_ : LoopData (B.L N) n) => ())
  refine StochDom.of_le_left (fun N u ω => ?_) h1
  exact Set.indicator_le_indicator
    (norm_gloop_le_loopMax u.idx (by simp [LoopData.idx]) (by simp [LoopData.idx]))

/-- **Lemma 5.1 at a general threshold, (5.7) form**, at an `N`-dependent energy. -/
theorem lemma_5_1'_thrN (X : Sample B) {E : ℕ → ℝ} {κ c C₀ : ℝ} (hκ : 0 < κ)
    (hE : ∀ N, |E N| ≤ 2 - κ) (hc : 0 < c) (hC₀ : 0 ≤ C₀)
    {t₁ t₂ : ℕ → ℝ} (h₁ : ∀ N, c ≤ t₁ N) (h₁₂ : ∀ N, t₁ N ≤ t₂ N) (h₂ : ∀ N, t₂ N < 1)
    (hS : LoopScalingN X E t₁ t₂)
    (h55 : ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval (E N) N (t₁ N) ω u.idx‖)
      (fun N _ _ => (B.scale (E N) N (t₁ N))⁻¹ ^ (n - 1))) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω =>
        (X.gmaxEventThr (E N) t₂ C₀ N).indicator (fun ω => ‖X.Lval (E N) N (t₂ N) ω u.idx‖) ω)
      (fun N _ _ => (B.ell N (t₂ N) / B.ell N (t₁ N)) ^ (n - 1)
        * (B.scale (E N) N (t₂ N))⁻¹ ^ (n - 1)) := by
  intro n hn
  have h := lemma_5_1_thrN X hκ hE hc hC₀ h₁ h₁₂ h₂ hS h55 n hn
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  convert h using 3 with N u ω
  have ht₂0 : 0 < t₂ N := (hc.trans_le (h₁ N)).trans_le (h₁₂ N)
  have hℓ1 : 0 < B.ell N (t₁ N) := lt_of_lt_of_le zero_lt_one
    (one_le_ellHat (B.L N) (B.three_le_L N) (hc.trans_le (h₁ N)).le ((h₁₂ N).trans_lt (h₂ N)))
  have hℓ2 : 0 < B.ell N (t₂ N) := lt_of_lt_of_le zero_lt_one
    (one_le_ellHat (B.L N) (B.three_le_L N) ht₂0.le (h₂ N))
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hη : 0 < etaT (E N) (t₂ N) := etaT_pos (hE2 N) (h₂ N)
  rw [← mul_pow, Band.scale]
  field_simp

end Lemma51N

end RBM
