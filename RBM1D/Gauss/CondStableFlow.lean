/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GoodSetFlow
import RBM1D.Gauss.CondStableInst

/-!
# `≺` under the row conditional expectation `E_k`, uniformly in the time

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4: the integration-by-parts input of (4.5) along the flow.

`RBM.Gauss.UnifDomIcc` is `≺` uniformly in the time `u ∈ [s_N, t_N]`: the failure probability is
bounded at each index and each time separately, and the eventual-in-`N` thresholds do not depend
on `u`.  This file provides, in that form, the tools for the row conditional expectation `E_k` of
`RBM1D/Gauss/CondRow.lean`: every quantifier over `u` comes before `N`.

## Where `η_{t_N}` is allowed to appear

Only inside a *deterministic envelope* of polynomial size, `Env N ≤ N^{Kenv}` with `Kenv` free.
Such an envelope is harmless because it is multiplied by the probability of an exceptional set
(`Kenv` is absorbed into the exponent `D₁`).  It is *never* allowed to appear as a
multiplicative constant in a `≺`.  Since `η_u` is decreasing in `u`
(`RBM.Gauss.inv_etaT_le_inv_etaT`), `η_{t_N}^{-1}` bounds every `η_u^{-1}` on the interval.

## Main results

* `RBM.Gauss.UnifDomIcc.of_le_left`, `RBM.Gauss.UnifDomIcc.refl`,
  `RBM.Gauss.UnifDomIcc.const_mul_left`, `RBM.Gauss.UnifDomIcc.add'`,
  `RBM.Gauss.UnifDomIcc.precomp`, `RBM.Gauss.UnifDomIcc.mul'`,
  `RBM.Gauss.UnifDomIcc.of_le_left_on`, `RBM.Gauss.unifDomIcc_of_highProb`,
  `RBM.Gauss.unifDomIcc_const` — combinators for `RBM.Gauss.UnifDomIcc`.
* `RBM.Gauss.unifDomIcc_condRow_of_envelope` — `≺` under `E_k`, uniformly in the time, with no
  cardinality hypothesis.
* `RBM.Gauss.unifDomIcc_condRow_sub_self` — the same for `E_k[X] - X` through a surrogate that
  does not read row `k`.
* `RBM.Gauss.norm_green_diag_sub_mE_le_flow` — the envelope `|G_{ii} - m| ≤ η_{t_N}^{-1} + 1` on
  the whole flow interval.
* `RBM.Gauss.norm_greenDiagCentered_sub_minor_le` — the minor replacement (4.9) pointwise on the
  good event.
-/
namespace RBM.Gauss

open MeasureTheory Filter

open scoped ENNReal

/-! ### Combinators for `RBM.Gauss.UnifDomIcc` -/

section Comb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {V : ℕ → Type*} {s t : ℕ → ℝ}
variable {ξ ξ' ζ χ : ∀ N, ℝ → V N → Ω → ℝ}

/-- Monotonicity in the dominated quantity. -/
theorem UnifDomIcc.of_le_left (hle : ∀ N u a ω, ξ' N u a ω ≤ ξ N u a ω)
    (h : UnifDomIcc P s t ξ ζ) : UnifDomIcc P s t ξ' ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN u hu a
  refine le_trans (measure_mono ?_) (hN u hu a)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_lt_of_le hω (hle N u a ω)

/-- Monotonicity in the dominated quantity, needed only on the flow interval. -/
theorem UnifDomIcc.of_le_left_icc
    (hle : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), ∀ (a : V N) (ω : Ω), ξ' N u a ω ≤ ξ N u a ω)
    (h : UnifDomIcc P s t ξ ζ) : UnifDomIcc P s t ξ' ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN u hu a
  refine le_trans (measure_mono ?_) (hN u hu a)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_lt_of_le hω (hle N u hu a ω)

/-- Reflexivity. -/
theorem UnifDomIcc.refl (hζ : ∀ N u a ω, 0 ≤ ζ N u a ω) : UnifDomIcc P s t ζ ζ := by
  intro τ hτ D hD
  filter_upwards [eventually_ge_atTop 1, eventually_le_rpow 1 hτ] with N hN1 h1N u hu a
  have hsub : {ω | (N : ℝ) ^ τ * ζ N u a ω < ζ N u a ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    nlinarith [hζ N u a ω]
  rw [hsub, measure_empty]
  exact zero_le

/-- A constant multiple. -/
theorem UnifDomIcc.const_mul_left {c : ℝ} (hc : 0 ≤ c) (hζ : ∀ N u a ω, 0 ≤ ζ N u a ω)
    (h : UnifDomIcc P s t ξ ζ) : UnifDomIcc P s t (fun N u a ω => c * ξ N u a ω) ζ := by
  intro τ hτ D hD
  have hτ2 : (0 : ℝ) < τ / 2 := by linarith
  filter_upwards [h (τ / 2) hτ2 D hD, eventually_le_rpow c hτ2, eventually_ge_atTop 1]
    with N hN hcN hN1 u hu a
  refine le_trans (measure_mono ?_) (hN u hu a)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hhalf : (0 : ℝ) < (N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hNpos _
  have hζ0 := hζ N u a ω
  have hτpos : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg hNpos.le _
  have hξpos : 0 < ξ N u a ω := by
    by_contra hx
    rw [not_lt] at hx
    nlinarith
  have hstep : c * ξ N u a ω ≤ (N : ℝ) ^ (τ / 2) * ξ N u a ω :=
    mul_le_mul_of_nonneg_right hcN hξpos.le
  have hsq := UnifDetDom.rpow_half_mul_rpow_half N hτ
  nlinarith

/-- A sum, when both controls agree. -/
theorem UnifDomIcc.add' {ξ₁ ξ₂ : ∀ N, ℝ → V N → Ω → ℝ} (hζ : ∀ N u a ω, 0 ≤ ζ N u a ω)
    (h₁ : UnifDomIcc P s t ξ₁ ζ) (h₂ : UnifDomIcc P s t ξ₂ ζ) :
    UnifDomIcc P s t (fun N u a ω => ξ₁ N u a ω + ξ₂ N u a ω) ζ := by
  intro τ hτ D hD
  have hτ2 : (0 : ℝ) < τ / 2 := by linarith
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  filter_upwards [h₁ (τ / 2) hτ2 (D + 1) hD1, h₂ (τ / 2) hτ2 (D + 1) hD1,
    eventually_two_mul_rpow_le D, eventually_ge_atTop 1,
    eventually_le_rpow 2 hτ2] with N h1 h2 h3 hN1 h2N u hu a
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hsub : {ω | (N : ℝ) ^ τ * ζ N u a ω < ξ₁ N u a ω + ξ₂ N u a ω}
      ⊆ {ω | (N : ℝ) ^ (τ / 2) * ζ N u a ω < ξ₁ N u a ω}
        ∪ {ω | (N : ℝ) ^ (τ / 2) * ζ N u a ω < ξ₂ N u a ω} := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hno
    simp only [Set.mem_ofPred_eq] at hω
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hhalf : (0 : ℝ) < (N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hNpos _
    have hζ0 := hζ N u a ω
    have hsq := UnifDetDom.rpow_half_mul_rpow_half N hτ
    have hkey : ξ₁ N u a ω + ξ₂ N u a ω ≤ 2 * ((N : ℝ) ^ (τ / 2) * ζ N u a ω) := by
      linarith [hno.1, hno.2]
    have h2 : 2 * ((N : ℝ) ^ (τ / 2) * ζ N u a ω)
        ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * ζ N u a ω) :=
      mul_le_mul_of_nonneg_right h2N (by positivity)
    nlinarith
  calc P {ω | (N : ℝ) ^ τ * ζ N u a ω < ξ₁ N u a ω + ξ₂ N u a ω}
      ≤ P ({ω | (N : ℝ) ^ (τ / 2) * ζ N u a ω < ξ₁ N u a ω}
          ∪ {ω | (N : ℝ) ^ (τ / 2) * ζ N u a ω < ξ₂ N u a ω}) := measure_mono hsub
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add (h1 u hu a) (h2 u hu a)
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [two_mul, ENNReal.ofReal_add hp hp]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- Reindexing the index family. -/
theorem UnifDomIcc.precomp {V' : ℕ → Type*} (f : ∀ N, V' N → V N) (h : UnifDomIcc P s t ξ ζ) :
    UnifDomIcc P s t (fun N u a ω => ξ N u (f N a) ω) (fun N u a ω => ζ N u (f N a) ω) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN u hu a
  exact hN u hu (f N a)

/-- **A deterministic bound on a high-probability event gives a `RBM.Gauss.UnifDomIcc`.** -/
theorem unifDomIcc_of_highProb {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ)
    (hle : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ u ∈ Set.Icc (s N) (t N),
      ∀ a : V N, ξ N u a ω ≤ (N : ℝ) ^ τ * ζ N u a ω) :
    UnifDomIcc P s t ξ ζ := by
  intro τ hτ D hD
  filter_upwards [hΞ D hD, hle τ hτ] with N hΞN hleN u hu a
  refine le_trans (measure_mono ?_) hΞN
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  exact fun hmem => absurd (hleN ω hmem u hu a) (not_le.2 hω)

end Comb

/-! ### The row integral, uniformly in the time -/

section Tool

variable {d : Dims} {V : ℕ → Type*} {s t : ℕ → ℝ}

/-- **`≺` under `E_k`, uniformly in the time**, in the form `RBM.Gauss.UnifDomIcc`.

Two features of the statement:

* **No cardinality hypothesis.**  `RBM.Gauss.UnifDomIcc` bounds the failure probability at each
  index and each time separately, so the exceptional set of `hdom` may be taken at the single
  index `a` under consideration; no union over indices (which would need a `Fintype` index type
  and a cardinality bound) is taken here.  (It is taken later, by the net.)
* **Everything is quantified over `u` before `N`.**  The eventual-in-`N` thresholds come only
  from `hEnvpoly`, `hdom`, `hstab` and `hlow`, each of which is already uniform in `u`; the
  time enters the proof only through the data `X`, `ζ`, `χ`, `k`.

The deterministic envelope `Env N` may grow polynomially — `Kenv` is free and is absorbed into
the exponent `D₁` of the exceptional set.  This is why a time-dependent envelope such as
`η_{t_N}^{-1}` is harmless here, whereas it would not be as a *multiplicative* constant in a
`≺`. -/
theorem unifDomIcc_condRow_of_envelope
    {X : ∀ N, ℝ → V N → Ω d → ℂ} {ζ χ : ∀ N, ℝ → V N → Ω d → ℝ}
    {k : ∀ N, ℝ → V N → d.Idx N} {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hXmeas : ∀ (N : ℕ) (u : ℝ) (a : V N), Measurable (X N u a))
    (hζmeas : ∀ (N : ℕ) (u : ℝ) (a : V N), Measurable (ζ N u a))
    (hζ0 : ∀ (N : ℕ) (u : ℝ) (a : V N) (ω : Ω d), 0 ≤ ζ N u a ω)
    (hχ0 : ∀ (N : ℕ) (u : ℝ) (a : V N) (ω : Ω d), 0 ≤ χ N u a ω)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (henv : ∀ (N : ℕ), ∀ u ∈ Set.Icc (s N) (t N), ∀ (a : V N) (ω : Ω d),
      ‖X N u a ω‖ ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hrowint : ∀ (N : ℕ) (u : ℝ) (a : V N) (ω : Ω d),
      Integrable (fun ω' => ζ N u a (rowSplit d N (k N u a) ω ω')) (P d))
    (hlow : UnifDomIcc (P d) s t (fun N _ (_ : V N) (_ : Ω d) => (N : ℝ) ^ (-B)) χ)
    (hstab : UnifDomIcc (P d) s t
      (fun N u a ω => condRowReal d N (k N u a) (ζ N u a) ω) χ)
    (hdom : UnifDomIcc (P d) s t (fun N u a ω => ‖X N u a ω‖) ζ) :
    UnifDomIcc (P d) s t
      (fun N u a ω => ‖condRow d N (k N u a) (X N u a) ω‖) χ := by
  intro τ hτ D hD
  have hτ3 : 0 < τ / 3 := by linarith
  set M : ℝ := Kenv + B with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith
  set D₁ : ℝ := M + D + 2 with hD₁def
  have hD₁0 : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hEnvpoly, hdom (τ / 3) hτ3 D₁ hD₁0, hstab (τ / 3) hτ3 (D + 2) (by linarith),
    hlow (τ / 3) hτ3 (D + 2) (by linarith), eventually_ge_atTop 1,
    eventually_le_rpow 2 hτ3, eventually_two_mul_rpow_le (D + 1),
    eventually_two_mul_rpow_le D] with
    N hEnvN hbadN hstabN hlowN hN1 h2N hdbl1 hdbl2 u hu a
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  set S : Set (Ω d) := {σ | (N : ℝ) ^ (τ / 3) * ζ N u a σ < ‖X N u a σ‖} with hSdef
  have hSmeas : MeasurableSet S :=
    measurableSet_lt (measurable_const.mul (hζmeas N u a)) ((hXmeas N u a).norm)
  have hSsmall : (P d) S ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := hbadN u hu a
  set ε : ℝ≥0∞ := ENNReal.ofReal ((N : ℝ) ^ (-M)) with hεdef
  have hεpos : (0 : ℝ) < (N : ℝ) ^ (-M) := Real.rpow_pos_of_pos hNpos _
  have hε0 : ε ≠ 0 := by
    rw [hεdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hεpos
  set A1 : Set (Ω d) := {ω | ε ≤ (P d) (rowSlice d N (k N u a) S ω)} with hA1def
  set A2 : Set (Ω d) :=
    {ω | (N : ℝ) ^ (τ / 3) * χ N u a ω < condRowReal d N (k N u a) (ζ N u a) ω} with hA2def
  set A3 : Set (Ω d) := {ω | (N : ℝ) ^ (τ / 3) * χ N u a ω < (N : ℝ) ^ (-B)} with hA3def
  have hA1small : (P d) A1 ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) := by
    have h2 : ε * (P d) A1 ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) :=
      (meas_measure_rowSlice_ge d N (k N u a) hSmeas ε).trans hSsmall
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl ENNReal.ofReal_ne_top)] at h2
    refine h2.trans (le_of_eq ?_)
    have hexp : -D₁ - -M = -(D + 2) := by rw [hD₁def, hMdef]; ring
    rw [hεdef, ← ENNReal.ofReal_div_of_pos hεpos, ← Real.rpow_sub hNpos, hexp]
  have hsub : {ω | (N : ℝ) ^ τ * χ N u a ω < ‖condRow d N (k N u a) (X N u a) ω‖}
      ⊆ A1 ∪ A2 ∪ A3 := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    rw [hA1def] at h1
    simp only [Set.mem_ofPred_eq, not_le] at h1
    rw [hA2def] at h2
    simp only [Set.mem_ofPred_eq, not_lt] at h2
    rw [hA3def] at h3
    simp only [Set.mem_ofPred_eq, not_lt] at h3
    have hgood : ∀ σ : Ω d, σ ∉ S → ‖X N u a σ‖ ≤ (N : ℝ) ^ (τ / 3) * ζ N u a σ := by
      intro σ hσ
      rw [hSdef] at hσ
      simpa only [Set.mem_ofPred_eq, not_lt] using hσ
    have hsplit := norm_condRow_le_split (hXmeas N u a) (hζ0 N u a) (hrowint N u a)
      (henv N u hu a) (Real.rpow_nonneg hNpos.le _) hSmeas hgood ω
    have hr1 : (P d).real (rowSlice d N (k N u a) S ω) ≤ (N : ℝ) ^ (-M) :=
      ENNReal.toReal_le_of_le_ofReal hεpos.le h1.le
    have hr0 : (0 : ℝ) ≤ (P d).real (rowSlice d N (k N u a) S ω) := measureReal_nonneg
    have hEnvterm : Env N * (P d).real (rowSlice d N (k N u a) S ω) ≤ (N : ℝ) ^ (-B) := by
      have hstep : Env N * (P d).real (rowSlice d N (k N u a) S ω)
          ≤ (N : ℝ) ^ Kenv * (N : ℝ) ^ (-M) :=
        mul_le_mul hEnvN hr1 hr0 (Real.rpow_nonneg hNpos.le _)
      refine hstep.trans (le_of_eq ?_)
      rw [← Real.rpow_add hNpos, hMdef]
      congr 1
      ring
    have hχu := hχ0 N u a ω
    have hr3 : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 3) := Real.rpow_nonneg hNpos.le _
    have hmono : (N : ℝ) ^ (τ / 3) ≤ (N : ℝ) ^ (2 * τ / 3) :=
      Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
    have hprod : (N : ℝ) ^ (τ / 3) * (N : ℝ) ^ (τ / 3) = (N : ℝ) ^ (2 * τ / 3) := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have hfin : (N : ℝ) ^ (τ / 3) * (N : ℝ) ^ (2 * τ / 3) = (N : ℝ) ^ τ := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have hchain : ‖condRow d N (k N u a) (X N u a) ω‖ ≤ (N : ℝ) ^ τ * χ N u a ω := by
      have e1 : (N : ℝ) ^ (τ / 3) * condRowReal d N (k N u a) (ζ N u a) ω
          ≤ (N : ℝ) ^ (τ / 3) * ((N : ℝ) ^ (τ / 3) * χ N u a ω) :=
        mul_le_mul_of_nonneg_left h2 hr3
      have e3 : (N : ℝ) ^ (τ / 3) * χ N u a ω ≤ (N : ℝ) ^ (2 * τ / 3) * χ N u a ω :=
        mul_le_mul_of_nonneg_right hmono hχu
      have e4 : (N : ℝ) ^ (τ / 3) * ((N : ℝ) ^ (τ / 3) * χ N u a ω)
          = (N : ℝ) ^ (2 * τ / 3) * χ N u a ω := by rw [← mul_assoc, hprod]
      have e5 : (2 : ℝ) * ((N : ℝ) ^ (2 * τ / 3) * χ N u a ω) ≤ (N : ℝ) ^ τ * χ N u a ω := by
        have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (2 * τ / 3) * χ N u a ω :=
          mul_nonneg (Real.rpow_nonneg hNpos.le _) hχu
        calc (2 : ℝ) * ((N : ℝ) ^ (2 * τ / 3) * χ N u a ω)
            ≤ (N : ℝ) ^ (τ / 3) * ((N : ℝ) ^ (2 * τ / 3) * χ N u a ω) :=
              mul_le_mul_of_nonneg_right h2N hnn
          _ = ((N : ℝ) ^ (τ / 3) * (N : ℝ) ^ (2 * τ / 3)) * χ N u a ω := (mul_assoc _ _ _).symm
          _ = (N : ℝ) ^ τ * χ N u a ω := by rw [hfin]
      linarith
    exact absurd hchain (not_le.2 hω)
  have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hNpos.le _
  refine (measure_mono hsub).trans ?_
  calc (P d) (A1 ∪ A2 ∪ A3) ≤ (P d) (A1 ∪ A2) + (P d) A3 := measure_union_le _ _
    _ ≤ ((P d) A1 + (P d) A2) + (P d) A3 := by gcongr; exact measure_union_le _ _
    _ ≤ (ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
        + ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) :=
          add_le_add (add_le_add hA1small (hstabN u hu a)) (hlowN u hu a)
    _ = ENNReal.ofReal (3 * (N : ℝ) ^ (-(D + 2))) := by
        rw [show (3 : ℝ) * (N : ℝ) ^ (-(D + 2))
            = (N : ℝ) ^ (-(D + 2)) + (N : ℝ) ^ (-(D + 2)) + (N : ℝ) ^ (-(D + 2)) by ring,
          ENNReal.ofReal_add (by positivity) hnn, ENNReal.ofReal_add hnn hnn]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : 2 * (N : ℝ) ^ (-(D + 1 + 1)) ≤ (N : ℝ) ^ (-(D + 1)) := hdbl1
        have e2 : 2 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := hdbl2
        have e3 : (N : ℝ) ^ (-(D + 1 + 1)) = (N : ℝ) ^ (-(D + 2)) := by congr 1; ring
        rw [e3] at e1
        linarith

end Tool

/-! ### The deterministic envelope along the flow -/

section Env

variable {E : ℝ}

/-- `η_u` is decreasing in `u`, so `η_{t_N}^{-1}` bounds `η_u^{-1}` for every `u ≤ t_N`.  This
is the only way the endpoint `t_N` enters the envelopes below, and it enters *polynomially*
(through `Kenv`), never as a multiplicative constant in a `≺`. -/
theorem inv_etaT_le_inv_etaT (hE : |E| < 2) {u v : ℝ} (huv : u ≤ v) (hv : v < 1) :
    (etaT E u)⁻¹ ≤ (etaT E v)⁻¹ := by
  have hvpos : 0 < etaT E v := etaT_pos_of_lt_one hE hv
  have hupos : 0 < etaT E u := etaT_pos_of_lt_one hE (lt_of_le_of_lt huv hv)
  have him : 0 < (mE E).im := mE_im_pos hE
  have hle : etaT E v ≤ etaT E u := by
    simp only [etaT]
    exact mul_le_mul_of_nonneg_right (by linarith) him.le
  have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hvpos hle
  simpa [one_div] using h

end Env

/-! ### `≺` is closed under products, uniformly in the time -/

section Mul

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {V : ℕ → Type*} {s t : ℕ → ℝ}

/-- The `RBM.Gauss.UnifDomIcc` analogue of `RBM.StochDom.mul`. -/
theorem UnifDomIcc.mul' {ξ₁ ξ₂ ζ₁ ζ₂ : ∀ N, ℝ → V N → Ω → ℝ}
    (hξ₂ : ∀ N u a ω, 0 ≤ ξ₂ N u a ω) (hζ₁ : ∀ N u a ω, 0 ≤ ζ₁ N u a ω)
    (h₁ : UnifDomIcc P s t ξ₁ ζ₁) (h₂ : UnifDomIcc P s t ξ₂ ζ₂) :
    UnifDomIcc P s t (fun N u a ω => ξ₁ N u a ω * ξ₂ N u a ω)
      (fun N u a ω => ζ₁ N u a ω * ζ₂ N u a ω) := by
  intro τ hτ D hD
  have hτ2 : (0 : ℝ) < τ / 2 := by linarith
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  filter_upwards [h₁ (τ / 2) hτ2 (D + 1) hD1, h₂ (τ / 2) hτ2 (D + 1) hD1,
    eventually_two_mul_rpow_le D, eventually_ge_atTop 1] with N h1 h2 h3 hN1 u hu a
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hNpos.le _
  have hhalf : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  have hsub : {ω | (N : ℝ) ^ τ * (ζ₁ N u a ω * ζ₂ N u a ω) < ξ₁ N u a ω * ξ₂ N u a ω}
      ⊆ {ω | (N : ℝ) ^ (τ / 2) * ζ₁ N u a ω < ξ₁ N u a ω}
        ∪ {ω | (N : ℝ) ^ (τ / 2) * ζ₂ N u a ω < ξ₂ N u a ω} := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hno
    simp only [Set.mem_ofPred_eq] at hω
    have hchain : ξ₁ N u a ω * ξ₂ N u a ω
        ≤ (N : ℝ) ^ τ * (ζ₁ N u a ω * ζ₂ N u a ω) :=
      calc ξ₁ N u a ω * ξ₂ N u a ω ≤ ((N : ℝ) ^ (τ / 2) * ζ₁ N u a ω) * ξ₂ N u a ω :=
            mul_le_mul_of_nonneg_right hno.1 (hξ₂ N u a ω)
        _ ≤ ((N : ℝ) ^ (τ / 2) * ζ₁ N u a ω) * ((N : ℝ) ^ (τ / 2) * ζ₂ N u a ω) :=
            mul_le_mul_of_nonneg_left hno.2 (mul_nonneg hhalf (hζ₁ N u a ω))
        _ = ((N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2)) * (ζ₁ N u a ω * ζ₂ N u a ω) := by ring
        _ = (N : ℝ) ^ τ * (ζ₁ N u a ω * ζ₂ N u a ω) := by
            rw [UnifDetDom.rpow_half_mul_rpow_half N hτ]
    linarith
  calc P {ω | (N : ℝ) ^ τ * (ζ₁ N u a ω * ζ₂ N u a ω) < ξ₁ N u a ω * ξ₂ N u a ω}
      ≤ P ({ω | (N : ℝ) ^ (τ / 2) * ζ₁ N u a ω < ξ₁ N u a ω}
          ∪ {ω | (N : ℝ) ^ (τ / 2) * ζ₂ N u a ω < ξ₂ N u a ω}) := measure_mono hsub
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add (h1 u hu a) (h2 u hu a)
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [two_mul, ENNReal.ofReal_add hp hp]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

end Mul

/-! ### What the `u`-uniform weak local law gives -/

section LocalLaw

variable {d : Dims} {E : ℝ} {s t Ψ : ℕ → ℝ}

end LocalLaw

/-! ### Two more combinators -/

section Comb2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {V : ℕ → Type*} {s t : ℕ → ℝ}
variable {ξ ξ' ζ : ∀ N, ℝ → V N → Ω → ℝ}

/-- Monotonicity in the dominated quantity, needed only on a high-probability event. -/
theorem UnifDomIcc.of_le_left_on {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ)
    (hle : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ u ∈ Set.Icc (s N) (t N), ∀ a : V N,
      ξ' N u a ω ≤ ξ N u a ω)
    (h : UnifDomIcc P s t ξ ζ) : UnifDomIcc P s t ξ' ζ := by
  intro τ hτ D hD
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  filter_upwards [h τ hτ (D + 1) hD1, hΞ (D + 1) hD1, hle, eventually_two_mul_rpow_le D,
    eventually_ge_atTop 1] with N hN hΞN hleN hdbl hN1 u hu a
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hNpos.le _
  have hsub : {ω | (N : ℝ) ^ τ * ζ N u a ω < ξ' N u a ω}
      ⊆ {ω | (N : ℝ) ^ τ * ζ N u a ω < ξ N u a ω} ∪ (Ξ N)ᶜ := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_cases hmem : ω ∈ Ξ N
    · exact Or.inl (lt_of_lt_of_le hω (hleN ω hmem u hu a))
    · exact Or.inr hmem
  calc P {ω | (N : ℝ) ^ τ * ζ N u a ω < ξ' N u a ω}
      ≤ P ({ω | (N : ℝ) ^ τ * ζ N u a ω < ξ N u a ω} ∪ (Ξ N)ᶜ) := measure_mono hsub
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add (hN u hu a) hΞN
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [two_mul, ENNReal.ofReal_add hp hp]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hdbl

/-- A deterministic eventual inequality between two sequences. -/
theorem unifDomIcc_const {f g : ℕ → ℝ} (hg : ∀ N, 0 ≤ g N)
    (hfg : ∀ᶠ N : ℕ in atTop, f N ≤ g N) :
    UnifDomIcc P s t (fun N _ (_ : V N) (_ : Ω) => f N) (fun N _ _ _ => g N) := by
  intro τ hτ D hD
  filter_upwards [hfg, eventually_le_rpow 1 hτ, eventually_ge_atTop 1] with N hN h1N hN1 u hu a
  have hsub : {ω : Ω | (N : ℝ) ^ τ * g N < f N} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    nlinarith [hg N]
  rw [hsub, measure_empty]
  exact zero_le

end Comb2

/-! ### `E_k[X] - X` through a row-free surrogate, uniformly in the time -/

section SubSelf

variable {d : Dims} {V : ℕ → Type*} {s t : ℕ → ℝ}

/-- **`E_k[X] - X` under `≺`, uniformly in the time**, through a surrogate `X'` that does not read
row `k` and satisfies `‖X - X'‖ ≺ ζ`. -/
theorem unifDomIcc_condRow_sub_self
    {X X' : ∀ N, ℝ → V N → Ω d → ℂ} {ζ χ : ∀ N, ℝ → V N → Ω d → ℝ}
    {k : ∀ N, ℝ → V N → d.Idx N} {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hXmeas : ∀ (N : ℕ) (u : ℝ) (a : V N), Measurable (X N u a))
    (hX'meas : ∀ (N : ℕ) (u : ℝ) (a : V N), Measurable (X' N u a))
    (hζmeas : ∀ (N : ℕ) (u : ℝ) (a : V N), Measurable (ζ N u a))
    (hζ0 : ∀ (N : ℕ) (u : ℝ) (a : V N) (ω : Ω d), 0 ≤ ζ N u a ω)
    (hχ0 : ∀ (N : ℕ) (u : ℝ) (a : V N) (ω : Ω d), 0 ≤ χ N u a ω)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (henv : ∀ (N : ℕ), ∀ u ∈ Set.Icc (s N) (t N), ∀ (a : V N) (ω : Ω d),
      ‖X N u a ω - X' N u a ω‖ ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hrowint : ∀ (N : ℕ) (u : ℝ) (a : V N) (ω : Ω d),
      Integrable (fun ω' => ζ N u a (rowSplit d N (k N u a) ω ω')) (P d))
    (hlow : UnifDomIcc (P d) s t (fun N _ (_ : V N) (_ : Ω d) => (N : ℝ) ^ (-B)) χ)
    (hstab : UnifDomIcc (P d) s t
      (fun N u a ω => condRowReal d N (k N u a) (ζ N u a) ω) χ)
    (hζχ : UnifDomIcc (P d) s t ζ χ)
    (hfd : ∀ (N : ℕ) (u : ℝ) (a : V N), FinDepOffRow d N (k N u a) (X' N u a))
    (hXint : ∀ (N : ℕ), ∀ u ∈ Set.Icc (s N) (t N), ∀ a : V N,
      RowIntegrable d N (k N u a) (X N u a))
    (hdiff : UnifDomIcc (P d) s t (fun N u a ω => ‖X N u a ω - X' N u a ω‖) ζ) :
    UnifDomIcc (P d) s t
      (fun N u a ω => ‖condRow d N (k N u a) (X N u a) ω - X N u a ω‖) χ := by
  have hX'int : ∀ (N : ℕ) (u : ℝ) (a : V N), RowIntegrable d N (k N u a) (X' N u a) := by
    intro N u a ω
    have h : (fun ω' => X' N u a (rowSplit d N (k N u a) ω ω')) = fun _ => X' N u a ω := by
      funext ω'; exact (hfd N u a).rowSplit_eq ω ω'
    rw [h]; exact integrable_const _
  have hbound : ∀ (N : ℕ), ∀ u ∈ Set.Icc (s N) (t N), ∀ (a : V N) (ω : Ω d),
      ‖condRow d N (k N u a) (X N u a) ω - X N u a ω‖
        ≤ ‖condRow d N (k N u a) (fun η => X N u a η - X' N u a η) ω‖
          + ‖X N u a ω - X' N u a ω‖ := by
    intro N u hu a ω
    have e1 := congrFun (condRow_sub (k N u a) (hXint N u hu a) (hX'int N u a)) ω
    have e2 := congrFun (condRow_of_finDepOffRow (hfd N u a)) ω
    have hid : condRow d N (k N u a) (X N u a) ω - X N u a ω
        = condRow d N (k N u a) (fun η => X N u a η - X' N u a η) ω
          - (X N u a ω - X' N u a ω) := by
      rw [e1, e2]; ring
    rw [hid]
    exact norm_sub_le _ _
  have htool : UnifDomIcc (P d) s t
      (fun N u a ω => ‖condRow d N (k N u a) (fun η => X N u a η - X' N u a η) ω‖) χ :=
    unifDomIcc_condRow_of_envelope
      (fun N u a => (hXmeas N u a).sub (hX'meas N u a)) hζmeas hζ0 hχ0 hKenv hB henv hEnvpoly
      hrowint hlow hstab hdiff
  exact UnifDomIcc.of_le_left_icc hbound (UnifDomIcc.add' hχ0 htool (hdiff.trans hζχ))

end SubSelf

/-! ### The two halves of `RBM.Gauss.ibpRem`, uniformly in the time -/

section Rem

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- The envelope of `|G_{ii} - m|` along the whole flow interval, with the endpoint `t_N`. -/
theorem norm_green_diag_sub_mE_le_flow (hE : |E| < 2) {N : ℕ} (ht1 : t N < 1)
    {u : ℝ} (hu : u ∈ Set.Icc (s N) (t N)) (i : d.Idx N) (ω : Ω d) :
    ‖green (Hflow d N u ω) (zt E u) i i - mE E‖ ≤ (etaT E (t N))⁻¹ + 1 := by
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 ht1
  refine le_trans (norm_green_diag_sub_mE_le hE hu1 u i ω) ?_
  have := inv_etaT_le_inv_etaT hE hu.2 ht1
  linarith

end Rem

/-! ### The minor replacement (4.9) along the flow -/

section Repl

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **(4.9) pointwise, on the good event.**  The replacement error is
`|G_{lκ} G_{κl} / G_{κκ}| ≤ 2 |G_{lκ}| |G_{κl}|`, since `|G_{κκ}| ≥ 1/2` there.  The
identification of `RBM.Gauss.greenMinorMat` with the explicit formula needs no event: `H_u` is
Hermitian and `Im z_u ≠ 0`. -/
theorem norm_greenDiagCentered_sub_minor_le (d : Dims) (N : ℕ) {E u : ℝ} (hE : |E| < 2)
    (hu1 : u < 1) {δ' : ℝ} (hδ' : δ' ≤ 1 / 2) {ω : Ω d}
    (hω : GoodEvent (green (Hflow d N u ω) (zt E u)) (mE E) δ') (v : OffPair d.L d.W N) :
    ‖greenDiagCentered d N u (zt E u) (mE E) v.1.2 ω
        - greenMinorDiagCentered d N u (zt E u) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω‖
      ≤ 2 * (‖green (Hflow d N u ω) (zt E u) v.1.2 v.1.1‖
          * ‖green (Hflow d N u ω) (zt E u) v.1.1 v.1.2‖) := by
  have hzt : (zt E u).im ≠ 0 := by
    rw [← etaT_eq_zt_im]
    exact (etaT_pos_of_lt_one hE hu1).ne'
  have hid : greenDiagCentered d N u (zt E u) (mE E) v.1.2 ω
      - greenMinorDiagCentered d N u (zt E u) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω
      = -(greenMinor (green (Hflow d N u ω) (zt E u)) v.1.1 v.1.2 v.1.2
          - green (Hflow d N u ω) (zt E u) v.1.2 v.1.2) := by
    simp only [greenDiagCentered, greenMinorDiagCentered]
    rw [greenMinorMat_eq_minorGreen d N u (zt E u) v.1.1 ω
      (isUnit_det_Hflow_sub d N u ω hzt) (green_Hflow_diag_ne_zero d N u ω hzt v.1.1),
      minorGreen_eq_greenMinor]
    ring
  rw [hid, norm_neg]
  exact hω.norm_greenMinor_sub_le (norm_mE hE.le) hδ' v.1.1 v.1.2 v.1.2

end Repl

/-! ### `RBM.Gauss.ibpRem` off the diagonal, uniformly in the time -/

section IbpRem

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

end IbpRem

/-! ### The diagonal term `k = i` -/

section Diag

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

end Diag

/-! ### `RBM.Gauss.ibpRem` at every pair, uniformly in the time -/

section RemAll

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

end RemAll

section Assembly

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

end Assembly

section Slot

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B K : ℝ}

end Slot

section Holder

open scoped Matrix.Norms.L2Operator

variable {d : Dims} {E : ℝ} {s t δ : ℕ → ℝ} {K Kc : ℝ}

end Holder
