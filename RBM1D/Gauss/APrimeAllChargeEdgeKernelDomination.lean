/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Kernel

/-!
# Exact entrywise comparison for a unit-charge edge kernel

This proves the entrywise domination suggested by (5.17)--(5.18): for a complex phase
ξ of modulus one, the kernel from time s to t is dominated entry by entry by the
real unit-charge kernel. The proof uses the positive Neumann series of Theta and the sign
t - s ≥ 0; it treats the diagonal identity term explicitly.
-/

namespace RBM

open Matrix Finset

private theorem SB_entry_eq_re (L : ℕ) (a b : ZMod L) :
    SB L a b = ((SB L a b).re : ℂ) := by
  rw [SB_apply]
  simp only [sbKernel]
  split_ifs <;> norm_num

private theorem SB_entry_re_nonneg (L : ℕ) (a b : ZMod L) :
    0 ≤ (SB L a b).re := by
  rw [SB_apply]
  simp only [sbKernel]
  split_ifs <;> norm_num

private theorem pow_SB_entry_nonneg_real (L : ℕ) [NeZero L] :
    ∀ k : ℕ, ∀ a b : ZMod L,
      ∃ r : ℝ, 0 ≤ r ∧ (SB L ^ k) a b = (r : ℂ) := by
  intro k
  induction k with
  | zero =>
      intro a b
      by_cases hab : a = b
      · subst b
        refine ⟨1, by norm_num, ?_⟩
        simp
      · refine ⟨0, by norm_num, ?_⟩
        simp [hab]
  | succ k ih =>
      intro a b
      let f : ZMod L → ℝ := fun c => ((SB L ^ k) a c).re * (SB L c b).re
      have hterm (c : ZMod L) :
          (SB L ^ k) a c * SB L c b = (f c : ℂ) := by
        obtain ⟨r, hr, hpow⟩ := ih a c
        have hreal : ((SB L ^ k) a c).re = r := by
          have := congrArg Complex.re hpow
          simpa using this
        calc
          (SB L ^ k) a c * SB L c b = (r : ℂ) * SB L c b := by rw [hpow]
          _ = (r : ℂ) * ((SB L c b).re : ℂ) := by
                rw [SB_entry_eq_re L c b]
                simp only [Complex.ofReal_re]
          _ = (r * (SB L c b).re : ℂ) := by rw [← Complex.ofReal_mul]
          _ = (f c : ℂ) := by simp [f, hreal]
      refine ⟨∑ c : ZMod L, f c, Finset.sum_nonneg (fun c hc => ?_), ?_⟩
      · have hreal : 0 ≤ ((SB L ^ k) a c).re := by
          obtain ⟨r, hr, hpow⟩ := ih a c
          have := congrArg Complex.re hpow
          rw [Complex.ofReal_re] at this
          exact this.symm ▸ hr
        exact mul_nonneg hreal (SB_entry_re_nonneg L c b)
      · rw [pow_succ, Matrix.mul_apply]
        calc
          (∑ c : ZMod L, (SB L ^ k) a c * SB L c b)
              = ∑ c : ZMod L, (f c : ℂ) := by
                  exact Finset.sum_congr rfl fun c hc => hterm c
          _ = ((∑ c : ZMod L, f c : ℝ) : ℂ) :=
                (Complex.ofReal_sum (Finset.univ : Finset (ZMod L)) f).symm

private theorem theta_entry_series_summable (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {z : ℂ} (hz : ‖z‖ < 1) (a b : ZMod L) :
    Summable (fun k : ℕ => (((z • SB L) ^ k) a b)) := by
  have hpow := summable_norm_pow L hL hz
  have hnorm : Summable (fun k : ℕ => ‖(((z • SB L) ^ k) a b)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_entry_le_norm L _ a b) hpow
  exact hnorm.of_norm

private theorem theta_apply_tsum (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {z : ℂ} (hz : ‖z‖ < 1) (a b : ZMod L) :
    Theta L z a b = ∑' k : ℕ, (((z • SB L) ^ k) a b) := by
  have hpow := summable_norm_pow L hL hz
  have hentries : ∀ a b : ZMod L,
      Summable (fun k : ℕ => (((z • SB L) ^ k) a b)) :=
    fun a b => theta_entry_series_summable L hL hz a b
  have hrows : ∀ a : ZMod L,
      Summable (fun k : ℕ => (((z • SB L) ^ k) a)) :=
    fun a => Pi.summable.mpr (fun b => hentries a b)
  have hmat : Summable (fun k : ℕ => (z • SB L) ^ k) := Pi.summable.mpr hrows
  rw [Theta_eq_tsum L hL hz]
  have h1 := congrFun (Pi.tsum_apply (x := a) hmat) b
  have hrow := hrows a
  have h2 := Pi.tsum_apply (x := b) hrow
  exact h1.trans h2

private theorem theta_real_entry_data (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a b : ZMod L) :
    ∃ r : ℝ, 0 ≤ r ∧ Theta L (t : ℂ) a b = (r : ℂ) := by
  have htNorm : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact ht1
  have hentries := theta_entry_series_summable L hL htNorm a b
  let f : ℕ → ℝ := fun k => ((((t : ℂ) • SB L) ^ k) a b).re
  have hterm (k : ℕ) :
      ∃ r : ℝ, 0 ≤ r ∧ (((t : ℂ) • SB L) ^ k) a b = (r : ℂ) := by
    obtain ⟨r, hr, hpow⟩ := pow_SB_entry_nonneg_real L k a b
    refine ⟨t ^ k * r, mul_nonneg (pow_nonneg ht0 k) hr, ?_⟩
    have hentry : (((t : ℂ) • SB L) ^ k) a b
        = (t : ℂ) ^ k * ((SB L ^ k) a b) := by
      rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
    calc
      (((t : ℂ) • SB L) ^ k) a b = (t : ℂ) ^ k * ((SB L ^ k) a b) := hentry
      _ = ((t ^ k * r : ℝ) : ℂ) := by
            rw [hpow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  have hcast (k : ℕ) : (((t : ℂ) • SB L) ^ k) a b = (f k : ℂ) := by
    obtain ⟨r, hr, hpow⟩ := hterm k
    change (((t : ℂ) • SB L) ^ k) a b
      = (((((t : ℂ) • SB L) ^ k) a b).re : ℂ)
    rw [hpow]
    simp
  have hnonneg (k : ℕ) : 0 ≤ f k := by
    obtain ⟨r, hr, hpow⟩ := hterm k
    change 0 ≤ ((((t : ℂ) • SB L) ^ k) a b).re
    rw [hpow]
    simpa using hr
  have hnorm (k : ℕ) : f k = ‖(((t : ℂ) • SB L) ^ k) a b‖ := by
    obtain ⟨r, hr, hpow⟩ := hterm k
    change ((((t : ℂ) • SB L) ^ k) a b).re
      = ‖(((t : ℂ) • SB L) ^ k) a b‖
    rw [hpow]
    simp only [Complex.ofReal_re, Complex.norm_of_nonneg hr]
  have hf : Summable f := by
    have hfun : f = fun k => ‖(((t : ℂ) • SB L) ^ k) a b‖ := funext hnorm
    rw [hfun]
    exact hentries.norm
  have hsum : Theta L (t : ℂ) a b = ((∑' k : ℕ, f k : ℝ) : ℂ) := by
    rw [theta_apply_tsum L hL htNorm a b, Complex.ofReal_tsum]
    exact tsum_congr hcast
  exact ⟨∑' k : ℕ, f k, tsum_nonneg hnonneg, hsum⟩

private theorem theta_real_entry_nonneg (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a b : ZMod L) :
    0 ≤ (Theta L (t : ℂ) a b).re := by
  obtain ⟨r, hr, hΘ⟩ := theta_real_entry_data L hL ht0 ht1 a b
  rw [hΘ]
  simpa using hr

/-- Every entry of the real nonnegative-time propagator is a nonnegative real. -/
private theorem theta_real_entry_eq_re (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a b : ZMod L) :
    Theta L (t : ℂ) a b = ((Theta L (t : ℂ) a b).re : ℂ) := by
  obtain ⟨r, hr, hΘ⟩ := theta_real_entry_data L hL ht0 ht1 a b
  rw [hΘ]
  simp

/-- Pointwise phase domination for Theta, from its positive random-walk power series. -/
private theorem norm_theta_phase_le_real (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {t : ℝ} {ξ : ℂ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hξ : ‖ξ‖ = 1)
    (a b : ZMod L) :
    ‖Theta L ((t : ℂ) * ξ) a b‖ ≤ (Theta L (t : ℂ) a b).re := by
  let z : ℂ := (t : ℂ) * ξ
  have hzNorm : ‖z‖ = t := by
    change ‖(t : ℂ) * ξ‖ = t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, hξ, mul_one]
  have hz : ‖z‖ < 1 := by rw [hzNorm]; exact ht1
  have htNorm : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact ht1
  have hEntrySummableZ := theta_entry_series_summable L hL hz a b
  have hEntrySummableT := theta_entry_series_summable L hL htNorm a b
  have hEntryZ := theta_apply_tsum L hL hz a b
  have hEntryT := theta_apply_tsum L hL htNorm a b
  have hEntryNorms : ∀ k : ℕ,
      ‖(((z • SB L) ^ k) a b)‖ = ‖((((t : ℂ) • SB L) ^ k) a b)‖ := by
    intro k
    obtain ⟨r, hr, hpow⟩ := pow_SB_entry_nonneg_real L k a b
    have hzEntry : (((z • SB L) ^ k) a b)
        = z ^ k * ((SB L ^ k) a b) := by
      rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
    have htEntry : ((((t : ℂ) • SB L) ^ k) a b)
        = (t : ℂ) ^ k * ((SB L ^ k) a b) := by
      rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
    rw [hzEntry, htEntry, hpow]
    simp only [Complex.norm_mul, Complex.norm_pow, hzNorm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht0, Complex.norm_of_nonneg hr]
  have hsumNorm :
      (∑' k : ℕ, ‖(((z • SB L) ^ k) a b)‖)
        = (∑' k : ℕ, ‖((((t : ℂ) • SB L) ^ k) a b)‖) :=
    tsum_congr hEntryNorms
  have htermTNonneg : ∀ k : ℕ, 0 ≤ ((((t : ℂ) • SB L) ^ k) a b).re := by
    intro k
    obtain ⟨r, hr, hpow⟩ := pow_SB_entry_nonneg_real L k a b
    have htEntry : ((((t : ℂ) • SB L) ^ k) a b)
        = (t : ℂ) ^ k * ((SB L ^ k) a b) := by
      rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
    rw [htEntry, hpow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    simp only [Complex.ofReal_re]
    exact mul_nonneg (pow_nonneg ht0 k) hr
  have htermTCast (k : ℕ) :
      ((((t : ℂ) • SB L) ^ k) a b)
        = (((((t : ℂ) • SB L) ^ k) a b).re : ℂ) := by
    obtain ⟨r, hr, hpow⟩ := pow_SB_entry_nonneg_real L k a b
    have htEntry : ((((t : ℂ) • SB L) ^ k) a b)
        = (t : ℂ) ^ k * ((SB L ^ k) a b) := by
      rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
    rw [htEntry, hpow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    simp only [Complex.ofReal_re]
  have hsumTNorm :
      (∑' k : ℕ, ‖((((t : ℂ) • SB L) ^ k) a b)‖)
        = (Theta L (t : ℂ) a b).re := by
    calc
      (∑' k : ℕ, ‖((((t : ℂ) • SB L) ^ k) a b)‖)
          = ∑' k : ℕ, ((((t : ℂ) • SB L) ^ k) a b).re :=
              tsum_congr fun k => by
                rw [htermTCast k]
                exact Complex.norm_of_nonneg (htermTNonneg k)
      _ = (∑' k : ℕ, (((t : ℂ) • SB L) ^ k) a b).re :=
            (Complex.re_tsum hEntrySummableT).symm
      _ = (Theta L (t : ℂ) a b).re := by rw [← hEntryT]
  calc
    ‖Theta L z a b‖
        = ‖(∑' k : ℕ, (((z • SB L) ^ k) a b))‖ := by rw [hEntryZ]
    _ ≤ ∑' k : ℕ, ‖(((z • SB L) ^ k) a b)‖ :=
          norm_tsum_le_tsum_norm hEntrySummableZ.norm
    _ = ∑' k : ℕ, ‖((((t : ℂ) • SB L) ^ k) a b)‖ := hsumNorm
    _ = (Theta L (t : ℂ) a b).re := hsumTNorm

private theorem SB_mul_theta_real_entry (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a b : ZMod L) :
    0 ≤ ((SB L * Theta L (t : ℂ)) a b).re ∧
      (SB L * Theta L (t : ℂ)) a b
        = (((SB L * Theta L (t : ℂ)) a b).re : ℂ) := by
  let f : ZMod L → ℝ := fun c => (SB L a c).re * (Theta L (t : ℂ) c b).re
  have hterm (c : ZMod L) :
      SB L a c * Theta L (t : ℂ) c b = (f c : ℂ) := by
    rw [SB_entry_eq_re L a c, theta_real_entry_eq_re L hL ht0 ht1 c b]
    rw [← Complex.ofReal_mul]
  have hnonneg (c : ZMod L) : 0 ≤ f c := by
    exact mul_nonneg (SB_entry_re_nonneg L a c)
      (theta_real_entry_nonneg L hL ht0 ht1 c b)
  have hsum : (SB L * Theta L (t : ℂ)) a b = ((∑ c : ZMod L, f c : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    calc
      (∑ c : ZMod L, SB L a c * Theta L (t : ℂ) c b)
          = ∑ c : ZMod L, (f c : ℂ) :=
              Finset.sum_congr rfl fun c hc => hterm c
      _ = ((∑ c : ZMod L, f c : ℝ) : ℂ) :=
            (Complex.ofReal_sum (Finset.univ : Finset (ZMod L)) f).symm
  constructor
  · rw [hsum, Complex.ofReal_re]
    exact Finset.sum_nonneg fun c hc => hnonneg c
  · rw [hsum, Complex.ofReal_re]

private theorem norm_SB_mul_theta_phase_le_real (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {t : ℝ} {ξ : ℂ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hξ : ‖ξ‖ = 1)
    (a b : ZMod L) :
    ‖(SB L * Theta L ((t : ℂ) * ξ)) a b‖
      ≤ ((SB L * Theta L (t : ℂ)) a b).re := by
  calc
    ‖(SB L * Theta L ((t : ℂ) * ξ)) a b‖
        = ‖∑ c : ZMod L, SB L a c * Theta L ((t : ℂ) * ξ) c b‖ := by
            rw [Matrix.mul_apply]
    _ ≤ ∑ c : ZMod L,
          ‖SB L a c * Theta L ((t : ℂ) * ξ) c b‖ :=
            norm_sum_le Finset.univ _
    _ = ∑ c : ZMod L,
          (SB L a c).re * ‖Theta L ((t : ℂ) * ξ) c b‖ := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [norm_mul, SB_entry_eq_re L a c,
            Complex.norm_of_nonneg (SB_entry_re_nonneg L a c)]
          simp only [Complex.ofReal_re]
    _ ≤ ∑ c : ZMod L,
          (SB L a c).re * (Theta L (t : ℂ) c b).re := by
          apply Finset.sum_le_sum
          intro c hc
          exact mul_le_mul_of_nonneg_left
            (norm_theta_phase_le_real L hL ht0 ht1 hξ c b)
            (SB_entry_re_nonneg L a c)
    _ = ((SB L * Theta L (t : ℂ)) a b).re := by
          rcases SB_mul_theta_real_entry L hL ht0 ht1 a b with ⟨_, hq⟩
          rw [Matrix.mul_apply, Complex.re_sum]
          apply Finset.sum_congr rfl
          intro c hc
          rw [SB_entry_eq_re L a c, theta_real_entry_eq_re L hL ht0 ht1 c b,
            Complex.mul_re]
          simp

private theorem edgeKer_apply_eq_add_phase (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {s t : ℝ} {ξ : ℂ} (htξ : ‖(t : ℂ) * ξ‖ < 1) (a b : ZMod L) :
    edgeKer L ξ (s : ℂ) (t : ℂ) a b
      = (if a = b then (1 : ℂ) else 0)
          + (↑(t - s : ℝ) : ℂ) * ξ * (SB L * Theta L ((t : ℂ) * ξ)) a b := by
  rw [edgeKer_eq L hL htξ]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- Exact entrywise domination of a unit-phase kernel by the positive unit-charge kernel. -/
theorem norm_edgeKer_unit_phase_le_one (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {s t : ℝ} {ξ : ℂ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1)
    (hξ : ‖ξ‖ = 1) (a b : ZMod L) :
    ‖edgeKer L ξ (s : ℂ) (t : ℂ) a b‖
      ≤ (edgeKer L 1 (s : ℂ) (t : ℂ) a b).re := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have htξ : ‖(t : ℂ) * ξ‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, hξ, mul_one]
    exact ht1
  have htOne : ‖(t : ℂ) * (1 : ℂ)‖ < 1 := by
    rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact ht1
  have hq := norm_SB_mul_theta_phase_le_real L hL ht0 ht1 hξ a b
  have hqReal := SB_mul_theta_real_entry L hL ht0 ht1 a b
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  let d : ℝ := if a = b then 1 else 0
  have hd : 0 ≤ d := by
    dsimp [d]
    split_ifs <;> norm_num
  have hnormd : ‖(d : ℂ)‖ = d := Complex.norm_of_nonneg hd
  have hdcast : (d : ℂ) = if a = b then (1 : ℂ) else 0 := by
    dsimp [d]
    split_ifs <;> norm_num
  have hmain :
      ‖(d : ℂ) + (↑(t - s : ℝ) : ℂ) * ξ
          * (SB L * Theta L ((t : ℂ) * ξ)) a b‖
        ≤ d + (t - s) * ((SB L * Theta L (t : ℂ)) a b).re := by
    calc
      _ ≤ ‖(d : ℂ)‖
            + ‖(↑(t - s : ℝ) : ℂ) * ξ
                * (SB L * Theta L ((t : ℂ) * ξ)) a b‖ := norm_add_le _ _
      _ = d + (t - s) *
            ‖(SB L * Theta L ((t : ℂ) * ξ)) a b‖ := by
            rw [hnormd, norm_mul, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hts, hξ, mul_one]
      _ ≤ d + (t - s) * ((SB L * Theta L (t : ℂ)) a b).re :=
            add_le_add_right (mul_le_mul_of_nonneg_left hq hts) d
  have hRhs :
      (edgeKer L 1 (s : ℂ) (t : ℂ) a b).re
        = d + (t - s) * ((SB L * Theta L (t : ℂ)) a b).re := by
    rw [edgeKer_apply_eq_add_phase L hL htOne a b, ← hdcast]
    rcases hqReal with ⟨_, hqRealEq⟩
    rw [hqRealEq]
    simp only [Complex.add_re, Complex.ofReal_re]
    simp [d]
  rw [edgeKer_apply_eq_add_phase L hL htξ a b, ← hdcast, hRhs]
  exact hmain

/-- Nonnegativity of the real kernel on the stated time interval. -/
theorem edgeKer_one_entry_re_nonneg (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) (a b : ZMod L) :
    0 ≤ (edgeKer L 1 (s : ℂ) (t : ℂ) a b).re := by
  have h := norm_edgeKer_unit_phase_le_one L hL hs0 hst ht1 (ξ := 1) (by simp) a b
  exact le_trans (norm_nonneg _) h

end RBM
