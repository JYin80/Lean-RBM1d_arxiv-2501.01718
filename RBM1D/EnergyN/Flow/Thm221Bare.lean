/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.EnergyUniformReg

/-!
# The bare-(2.72) arithmetic at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7.

Two consequences of the step condition (2.72) at an `N`-dependent energy `E : ℕ → ℝ`. The
`N`-suffix is on the predicate: `RBM.Cond272N.pow_thirty_le` and `RBM.Cond272NReg.margin`.
Neither theorem fixes an energy-dependent constant; both take only `hE : ∀ N, |E N| < 2` (no
`κ`). The predicates `RBM.Cond272N` and `RBM.Cond272NReg` are those of `Flow/EnergyUniform.lean`
and `Flow/EnergyUniformReg.lean`.

## Main declarations

* `RBM.Cond272N.pow_thirty_le` — `(η_s/η_u)^30 ≤ W ℓ_u η_u` for every `u ∈ [s, t]`, from the
  bare (2.72).
* `RBM.Cond272NReg.margin` — the gained (2.72) at every exponent `b` with `e/c + b/30 ≤ a`.
-/

namespace RBM

open MeasureTheory Filter

section Thm221BareN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **`(η_s/η_u)^30 ≤ W ℓ_u η_u` for every `u ∈ [s, t]`**, at an `N`-dependent energy, from the
bare (2.72) at `t`. -/
theorem Cond272N.pow_thirty_le (hE : ∀ N, |E N| < 2) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (h : Cond272N B E s t) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT (E N) (s N) / etaT (E N) u) ^ 30 ≤ B.scale (E N) N u := by
  filter_upwards [h] with N hN u
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hL := B.one_le_L N
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have h1s : 0 < 1 - s N := by linarith [hst N, ht1 N]
  have hAt : 0 < B.scale (E N) N (t N) :=
    B.scale_eq_flowScale (E N) N (t N) ▸ flowScale_pos hW hL (hE N) (ht1 N)
  -- (2.72), inverted
  have hAt' : ((1 - s N) / (1 - t N)) ^ 30 ≤ B.scale (E N) N (t N) := by
    have hinv := inv_anti₀ (inv_pos.2 hAt) hN
    rw [inv_inv] at hinv
    have heq : ((1 - s N) / (1 - t N)) ^ 30 = (((1 - t N) / (1 - s N)) ^ 30)⁻¹ := by
      rw [← inv_pow, inv_div]
    rw [heq]; exact hinv
  -- the scale is antitone, the ratio is monotone
  have hanti : B.scale (E N) N (t N) ≤ B.scale (E N) N u := by
    rw [B.scale_eq_flowScale, B.scale_eq_flowScale]
    exact flowScale_antitoneOn hW.le (B.L N) (E N) (Set.mem_Iic.2 hu1.le)
      (Set.mem_Iic.2 (ht1 N).le) u.2.2
  have hratio : etaT (E N) (s N) / etaT (E N) u ≤ (1 - s N) / (1 - t N) := by
    rw [etaT_div_etaT (hE N)]
    exact div_le_div_of_nonneg_left h1s.le h1t (by linarith [u.2.2])
  have hr0 : (0 : ℝ) ≤ etaT (E N) (s N) / etaT (E N) u := by
    rw [etaT_div_etaT (hE N)]; positivity
  calc (etaT (E N) (s N) / etaT (E N) u) ^ 30 ≤ ((1 - s N) / (1 - t N)) ^ 30 :=
        pow_le_pow_left₀ hr0 hratio 30
    _ ≤ B.scale (E N) N (t N) := hAt'
    _ ≤ B.scale (E N) N u := hanti

/-- **The gained (2.72) at every exponent `b` with `e/c + b/30 ≤ a`**, uniformly in `u ∈ [s, t]`,
at an `N`-dependent energy, from the bare (2.72) plus the regime bound. -/
theorem Cond272NReg.margin (hE : ∀ N, |E N| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc : 0 < c) (h : Cond272NReg B E s t c) {e b a : ℝ} (he : 0 ≤ e) (hb : 0 ≤ b)
    (hsum : e / c + b / 30 ≤ a) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (N : ℝ) ^ e * (etaT (E N) (s N) / etaT (E N) u) ^ b ≤ B.scale (E N) N u ^ a := by
  filter_upwards [h.1.pow_thirty_le hE hst ht1, h.2, eventually_ge_atTop 1] with N h30 hreg hN1 u
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hL := B.one_le_L N
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have h1s : 0 < 1 - s N := by linarith [u.2.1]
  have hR1 : (1 : ℝ) ≤ etaT (E N) (s N) / etaT (E N) u := by
    rw [etaT_div_etaT (hE N), le_div_iff₀ h1u]; linarith [u.2.1]
  have hanti : B.scale (E N) N (t N) ≤ B.scale (E N) N u := by
    rw [B.scale_eq_flowScale, B.scale_eq_flowScale]
    exact flowScale_antitoneOn hW.le (B.L N) (E N) (Set.mem_Iic.2 hu1.le)
      (Set.mem_Iic.2 (ht1 N).le) u.2.2
  exact rpow_mul_rpow_le_of_pow_thirty hN1' hR1 hc he hb (h30 u) (hreg.trans hanti) hsum

end Thm221BareN

end RBM
