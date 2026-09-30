/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Eq45Small

/-!
# Smallness of the bad-event tower on the good set, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`: `RBM.Gauss.hsmall_of_highProb_auxN` and
`RBM.Gauss.hsmall_of_highProbN`. Neither fixes an energy-dependent constant: every `E`-use in the
two proofs is either a plain argument of the deterministic functions
`condEnv`/`condEps`/`etaT`/`goodSetFlow`/`badBase` (per-`N` values, not global constants) or is
threaded through `RBM.Gauss.measureReal_compl_le_of_polyLo`/`RBM.Gauss.PolyLo`/`RBM.Gauss.PolyHi`,
which have no energy binder at all. `RBM.Gauss.goodSetFlow d E s t δ` (a plain function
`ℕ → Set Ω`) is used as `fun N => goodSetFlow d (E N) s t δ N`, the same eta-expansion pattern
as for `Step3.flowXiLK`/`Step45.FlowEq548N`.
-/

namespace RBM.Gauss

open MeasureTheory Filter

open scoped ENNReal

variable {d : Dims} {E : ℕ → ℝ} {s t δ : ℕ → ℝ}

/-- **The bad-event tower is small on `[s, t]`**: eventually, for every `u ∈ [s, t]`,
`condEnv^M · P(badTower) ≤ (2 C_M (2δ) + 2δ)^M (4δ)^{M²}`, from the good set `hΩ` with high
probability, `δ` polynomially small and `η_t⁻¹` polynomially bounded. No energy-dependent
constant is fixed here: every `E`-use is a plain argument of `condEnv`/`condEps`/`etaT`, computed
at the ambient `N` of each `have` block. -/
theorem hsmall_of_highProb_auxN (d : Dims) (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, t N < 1)
    (hδpos : ∀ N, 0 < δ N) (hδlo : PolyLo δ)
    (hηhi : PolyHi fun N => (etaT (E N) (t N))⁻¹ + 1)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N)) (M : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      condEnv (E N) u M ^ M
          * (P d).real (badTower d N (condEps (E N) u M (2 * δ N))
              (badBase d (E N) s t δ N) (M + 1))
        ≤ (2 * minorDiffC M * (2 * δ N) + 2 * δ N) ^ M * (2 * (2 * δ N)) ^ (M * M) := by
  classical
  have hΨpos : ∀ N, (0 : ℝ) < 2 * δ N := fun N => by linarith [hδpos N]
  have hηt : ∀ N, 0 < etaT (E N) (t N) := fun N => etaT_pos_of_lt_one' (hE N) (ht1 N)
  have hEnvt0 : ∀ N, (0 : ℝ) < condEnv (E N) (t N) M := fun N =>
    lt_of_lt_of_le zero_lt_one (one_le_condEnv (hE N) (ht1 N) M)
  have hMEnv0 : ∀ N, (0 : ℝ) < ((M : ℝ) + 1) * condEnv (E N) (t N) M := fun N => by
    have := hEnvt0 N; positivity
  have heT0 : ∀ N, (0 : ℝ) < condEps (E N) (t N) M (2 * δ N) := by
    intro N
    change (0 : ℝ) < (2 * δ N) * (2 * (2 * δ N)) ^ M
      * (((M : ℝ) + 1) * condEnv (E N) (t N) M)⁻¹
    have h1 := hΨpos N
    have h3 : (0 : ℝ) < (2 * (2 * δ N)) ^ M := by positivity
    exact mul_pos (mul_pos h1 h3) (inv_pos.2 (hMEnv0 N))
  have hR0 : ∀ N, (0 : ℝ) ≤ (Fintype.card (d.Idx N) : ℝ) := fun N => Nat.cast_nonneg _
  have hq0 : ∀ N, (0 : ℝ) < (condEps (E N) (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
      / condEps (E N) (t N) M (2 * δ N) := fun N =>
    div_pos (add_pos_of_pos_of_nonneg (heT0 N) (hR0 N)) (heT0 N)
  have hG0 : ∀ N, (0 : ℝ) < condEnv (E N) (t N) M ^ M
      * ((condEps (E N) (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
          / condEps (E N) (t N) M (2 * δ N)) ^ (M + 1) := fun N =>
    mul_pos (pow_pos (hEnvt0 N) M) (pow_pos (hq0 N) (M + 1))
  -- the target is bounded below by a fixed negative power of `N`
  have hΨlo : PolyLo fun N => 2 * δ N :=
    hδlo.mono (Filter.Eventually.of_forall fun N => by linarith [(hδpos N).le])
  have hB0lo : PolyLo fun N => 2 * minorDiffC M * (2 * δ N) + 2 * δ N :=
    hΨlo.mono (Filter.Eventually.of_forall fun N => by
      have h1 := minorDiffC_nonneg M
      have h2 := (hδpos N).le
      nlinarith)
  have h2Ψlo : PolyLo fun N => 2 * (2 * δ N) :=
    hΨlo.mono (Filter.Eventually.of_forall fun N => by linarith [(hδpos N).le])
  have hSlo : PolyLo fun N =>
      (2 * minorDiffC M * (2 * δ N) + 2 * δ N) ^ M * (2 * (2 * δ N)) ^ (M * M) :=
    (hB0lo.pow M).mul (h2Ψlo.pow (M * M))
  -- the price is bounded above by a fixed power of `N`
  have hEnvthi : PolyHi fun N => condEnv (E N) (t N) M := by
    have hc : PolyHi fun _ : ℕ => (2 : ℝ) ^ (2 * M + 1) := polyHi_const (by positivity)
    have hnn : ∀ᶠ N : ℕ in atTop, (0 : ℝ) ≤ (etaT (E N) (t N))⁻¹ + 1 :=
      Filter.Eventually.of_forall fun N => by
        have : (0 : ℝ) ≤ (etaT (E N) (t N))⁻¹ := inv_nonneg.2 (hηt N).le
        linarith
    have h := hc.mul hηhi (Filter.Eventually.of_forall fun _ => by positivity) hnn
    exact h.mono (Filter.Eventually.of_forall fun N => le_of_eq rfl)
  have hMEnvhi : PolyHi fun N => ((M : ℝ) + 1) * condEnv (E N) (t N) M :=
    (polyHi_const (c := (M : ℝ) + 1) (by positivity)).mul hEnvthi
      (Filter.Eventually.of_forall fun _ => by positivity)
      (Filter.Eventually.of_forall fun N => (hEnvt0 N).le)
  have heTlo : PolyLo fun N => condEps (E N) (t N) M (2 * δ N) := by
    have h := (hΨlo.mul (h2Ψlo.pow M)).mul
      (PolyLo.inv hMEnvhi (Filter.Eventually.of_forall hMEnv0))
    exact h.mono (Filter.Eventually.of_forall fun N => le_of_eq rfl)
  have hRhi : PolyHi fun N => (Fintype.card (d.Idx N) : ℝ) := by
    refine ⟨1, one_pos, 1, ?_⟩
    filter_upwards [card_Idx_le d] with N h
    rw [one_mul]; exact h
  have hquothi : PolyHi fun N =>
      (condEps (E N) (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
        / condEps (E N) (t N) M (2 * δ N) := by
    have hprod : PolyHi fun N =>
        (Fintype.card (d.Idx N) : ℝ) * (condEps (E N) (t N) M (2 * δ N))⁻¹ :=
      hRhi.mul (PolyHi.inv heTlo) (Filter.Eventually.of_forall hR0)
        (Filter.Eventually.of_forall fun N => (inv_pos.2 (heT0 N)).le)
    refine ((polyHi_const (c := (1 : ℝ)) one_pos).add hprod).mono
      (Filter.Eventually.of_forall fun N => le_of_eq ?_)
    rw [add_div, div_self (heT0 N).ne', div_eq_mul_inv]
  have hGhi : PolyHi fun N => condEnv (E N) (t N) M ^ M
      * ((condEps (E N) (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
          / condEps (E N) (t N) M (2 * δ N)) ^ (M + 1) :=
    (hEnvthi.pow (Filter.Eventually.of_forall fun N => (hEnvt0 N).le) M).mul
      (hquothi.pow (Filter.Eventually.of_forall fun N => (hq0 N).le) (M + 1))
      (Filter.Eventually.of_forall fun N => pow_nonneg (hEnvt0 N).le M)
      (Filter.Eventually.of_forall fun N => pow_nonneg (hq0 N).le (M + 1))
  -- and (4.1) beats the quotient
  have hkey := measureReal_compl_le_of_polyLo hΩ
    (hSlo.div hGhi (Filter.Eventually.of_forall hG0))
  filter_upwards [hkey] with N hN u hu
  -- uniformity in `u`: `η` is antitone, hence `condEnv` is monotone and `condEps` antitone
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  have hηu : 0 < etaT (E N) u := etaT_pos_of_lt_one' (hE N) hu1
  have hEnvu0 : (0 : ℝ) < condEnv (E N) u M :=
    lt_of_lt_of_le zero_lt_one (one_le_condEnv (hE N) hu1 M)
  have hEnvle : condEnv (E N) u M ≤ condEnv (E N) (t N) M := by
    have hinv : (etaT (E N) u)⁻¹ ≤ (etaT (E N) (t N))⁻¹ :=
      inv_anti₀ (hηt N) (etaT_le_of_le (hE N) hu.2)
    change (2 : ℝ) ^ (2 * M + 1) * ((etaT (E N) u)⁻¹ + 1)
      ≤ (2 : ℝ) ^ (2 * M + 1) * ((etaT (E N) (t N))⁻¹ + 1)
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * M + 1) := by positivity
    nlinarith
  have hMEnvu0 : (0 : ℝ) < ((M : ℝ) + 1) * condEnv (E N) u M := by positivity
  have heu0 : (0 : ℝ) < condEps (E N) u M (2 * δ N) := by
    change (0 : ℝ) < (2 * δ N) * (2 * (2 * δ N)) ^ M * (((M : ℝ) + 1) * condEnv (E N) u M)⁻¹
    have h1 := hΨpos N
    have h3 : (0 : ℝ) < (2 * (2 * δ N)) ^ M := by positivity
    exact mul_pos (mul_pos (hΨpos N) h3) (inv_pos.2 hMEnvu0)
  have hege : condEps (E N) (t N) M (2 * δ N) ≤ condEps (E N) u M (2 * δ N) := by
    change (2 * δ N) * (2 * (2 * δ N)) ^ M * (((M : ℝ) + 1) * condEnv (E N) (t N) M)⁻¹
      ≤ (2 * δ N) * (2 * (2 * δ N)) ^ M * (((M : ℝ) + 1) * condEnv (E N) u M)⁻¹
    have hmono : (((M : ℝ) + 1) * condEnv (E N) (t N) M)⁻¹
        ≤ (((M : ℝ) + 1) * condEnv (E N) u M)⁻¹ :=
      inv_anti₀ hMEnvu0 (by nlinarith [hEnvle, (Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))])
    have h1 := hΨpos N
    have hnn : (0 : ℝ) ≤ (2 * δ N) * (2 * (2 * δ N)) ^ M := by positivity
    exact mul_le_mul_of_nonneg_left hmono hnn
  -- the tower's measure
  have hε0 : (0 : ℝ) ≤ condEps (E N) u M (2 * δ N) := heu0.le
  have htow := meas_badTower_le d N (ε := condEps (E N) u M (2 * δ N))
    (measurableSet_badBase d (E N) s t δ N) (M + 1)
  have hfin : ((ENNReal.ofReal (condEps (E N) u M (2 * δ N))
      + (Fintype.card (d.Idx N) : ℝ≥0∞)) ^ (M + 1) * (P d) (badBase d (E N) s t δ N)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.natCast_ne_top _⟩)) (measure_ne_top _ _)
  have hL : (ENNReal.ofReal (condEps (E N) u M (2 * δ N)) ^ (M + 1)
        * (P d) (badTower d N (condEps (E N) u M (2 * δ N))
            (badBase d (E N) s t δ N) (M + 1))).toReal
      = condEps (E N) u M (2 * δ N) ^ (M + 1)
        * (P d).real (badTower d N (condEps (E N) u M (2 * δ N))
            (badBase d (E N) s t δ N) (M + 1)) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hε0, measureReal_def]
  have hRr : ((ENNReal.ofReal (condEps (E N) u M (2 * δ N))
        + (Fintype.card (d.Idx N) : ℝ≥0∞)) ^ (M + 1) * (P d) (badBase d (E N) s t δ N)).toReal
      = (condEps (E N) u M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ)) ^ (M + 1)
        * (P d).real (badBase d (E N) s t δ N) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _),
      ENNReal.toReal_ofReal hε0, ENNReal.toReal_natCast, measureReal_def]
  have hreal := ENNReal.toReal_mono hfin htow
  rw [hL, hRr] at hreal
  have hp0 : (P d).real (badBase d (E N) s t δ N)
      = (P d).real (goodSetFlow d (E N) s t δ N)ᶜ := by
    rw [measureReal_def, measureReal_def, meas_badBase]
  have hp0nn : (0 : ℝ) ≤ (P d).real (badBase d (E N) s t δ N) := measureReal_nonneg
  -- divide by `ε^{M+1}`
  have hA : (P d).real
        (badTower d N (condEps (E N) u M (2 * δ N)) (badBase d (E N) s t δ N) (M + 1))
      ≤ ((condEps (E N) u M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
          / condEps (E N) u M (2 * δ N)) ^ (M + 1) * (P d).real (badBase d (E N) s t δ N) := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos heu0 (M + 1)), mul_comm]
    exact hreal
  -- pass from `u` to `t N`
  have hquot : (condEps (E N) u M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
        / condEps (E N) u M (2 * δ N)
      ≤ (condEps (E N) (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
        / condEps (E N) (t N) M (2 * δ N) := by
    rw [add_div, div_self heu0.ne', add_div, div_self (heT0 N).ne']
    have h := div_le_div_of_nonneg_left (hR0 N) (heT0 N) hege
    linarith
  have hqu0 : (0 : ℝ) ≤ (condEps (E N) u M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
      / condEps (E N) u M (2 * δ N) :=
    (div_pos (add_pos_of_pos_of_nonneg heu0 (hR0 N)) heu0).le
  calc condEnv (E N) u M ^ M
        * (P d).real
          (badTower d N (condEps (E N) u M (2 * δ N)) (badBase d (E N) s t δ N) (M + 1))
      ≤ condEnv (E N) (t N) M ^ M
          * (((condEps (E N) (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
              / condEps (E N) (t N) M (2 * δ N)) ^ (M + 1)
            * (P d).real (badBase d (E N) s t δ N)) := by
        refine mul_le_mul (pow_le_pow_left₀ hEnvu0.le hEnvle M) (hA.trans ?_)
          measureReal_nonneg (pow_nonneg (hEnvt0 N).le M)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hqu0 hquot (M + 1)) hp0nn
    _ = (condEnv (E N) (t N) M ^ M
          * ((condEps (E N) (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
              / condEps (E N) (t N) M (2 * δ N)) ^ (M + 1))
        * (P d).real (badBase d (E N) s t δ N) := by ring
    _ ≤ (condEnv (E N) (t N) M ^ M
          * ((condEps (E N) (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
              / condEps (E N) (t N) M (2 * δ N)) ^ (M + 1))
        * (((2 * minorDiffC M * (2 * δ N) + 2 * δ N) ^ M * (2 * (2 * δ N)) ^ (M * M))
          / (condEnv (E N) (t N) M ^ M
            * ((condEps (E N) (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
                / condEps (E N) (t N) M (2 * δ N)) ^ (M + 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ (hG0 N).le
        rw [hp0]; exact hN
    _ = (2 * minorDiffC M * (2 * δ N) + 2 * δ N) ^ M * (2 * (2 * δ N)) ^ (M * M) := by
        have hGne : condEnv (E N) (t N) M ^ M
            * ((condEps (E N) (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
                / condEps (E N) (t N) M (2 * δ N)) ^ (M + 1) ≠ 0 := (hG0 N).ne'
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hGne]

/-- **The same bound at the two budgets `M = n = 2p`.** -/
theorem hsmall_of_highProbN (d : Dims) (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, t N < 1)
    (hδpos : ∀ N, 0 < δ N) (hδlo : PolyLo δ)
    (hηhi : PolyHi fun N => (etaT (E N) (t N))⁻¹ + 1)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N)) (p : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      condEnv (E N) u (2 * p) ^ (2 * p)
          * (P d).real (badTower d N (condEps (E N) u (2 * p) (2 * δ N))
              (badBase d (E N) s t δ N) (2 * p + 1))
        ≤ (2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N) ^ (2 * p)
            * (2 * (2 * δ N)) ^ (2 * p * (2 * p)) :=
  hsmall_of_highProb_auxN d hE ht1 hδpos hδlo hηhi hΩ (2 * p)

end RBM.Gauss
