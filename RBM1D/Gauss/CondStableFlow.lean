/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GoodSetFlow
import RBM1D.Gauss.CondStableInst

/-!
# `hfixIBP`: the time-uniform form of the integration-by-parts input of (4.5) — T136

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4 (pp. 49-51).

`RBM.Gauss.eq45Flow_of_unifDom` (T124, `RBM1D/Gauss/Eq45FlowInputs.lean`) reduces (4.5) along
the flow to three *fixed-time* inputs stated uniformly in the time, as `RBM.Gauss.UnifDomIcc`.
T128 discharged two of them; the third, `hfixIBP`, it could not, and named the gap precisely:
`RBM.Gauss.condExpDiag_stochDom_of_highProb` (T119) is a `RBM.StochDom` **at one time** whose
eventual-in-`N` threshold is not known to be uniform in that time, because the whole chain
`RBM.Gauss.stochDom_condRow_of_envelope` → `RBM.Gauss.condStable_Lmax` →
`RBM.Gauss.stochDom_normSq_green_diag_sub_Lmax` quantifies `∀ᶠ N` *after* fixing `t`.  Unlike
the fluctuation-averaging side, there is no single deterministic per-`(N,u)` estimate to
re-quantify.  This file re-runs the chain with the time carried through.

## What had to change, and why it is not a mechanical copy

The obstruction is **not** the `∀ᶠ N` bookkeeping — that part is mechanical, and in fact
*simpler* uniformly in the time: `RBM.Gauss.UnifDomIcc` bounds the failure probability at each
index and each time separately, so the union over indices that forces a `Fintype` hypothesis on
`RBM.Gauss.stochDom_condRow_of_envelope` is never taken (`RBM.Gauss.unifDomIcc_condRow_of_envelope`
has no `hcard`), exactly as T128 found for `RBM.Gauss.unifDomIcc_of_moment`.

The obstruction is the **control**.  T119's chain dominates every conditional expectation by
the random `L^max_u`, and therefore needs `E_i[L^max] ≺ L^max`
(`RBM.Gauss.condStable_Lmax`), which it proves through the sandwich `L^max ≍ W^{-1}` at the
cost of `η_t^{-2}`.  T119's own caveat says this fails as a `≺` when `t_N → 1`, and T124
repeated the warning.  So the chain is re-run with a **deterministic control** throughout:

* every conditional expectation is dominated by `Ψ²`, for which `E_i` is the identity, so
  `RBM.Gauss.CondStable` degenerates and `RBM.Gauss.LmaxRowProxy` is not needed at all;
* `L^max` is met only in the final line, and only through the **lower** half
  `W^{-1} ≤ 4 L^max` of T119's sandwich (`RBM.Gauss.inv_W_le_Lmax_flow`), which holds at every
  time on the flow good event and costs no power of `η`.  This is the same move T128 made for
  the fluctuation-averaging side (`RBM.Gauss.unifDomIcc_const_Lmax`), and its price is the same
  hypothesis: `W Ψ² = N^{o(1)}`, which is the paper's `Ψ² ≍ W^{-1}`.

Consequently the inputs are the `u`-uniform weak local law `RBM.Gauss.LocalLawUnifIcc` — the
*same* hypothesis T130 needs for the flow good event — together with numerical conditions.  In
particular the fixed-time `hloc`/`hrepl` of `RBM1D/Gauss/CondStableInst.lean` are not lifted:
`hloc` is read off the local law directly, and `hrepl` is redone from (4.9) with the two
off-diagonal factors taken from the local law
(`RBM.Gauss.unifDomIcc_greenDiagCentered_sub_minor`) rather than from (4.2) with the control
`L^max`.

## Where `η_{t_N}` is allowed to appear

Only inside a *deterministic envelope*, through the hypothesis

  `hEnv : ∀ᶠ N, (η_{t_N}^{-1} + 1)² ≤ N^{Kenv}`   (`Kenv` free),

which is the standing regime `W ℓ_u η_u ≥ 1` of §4 and is the same shape as T130's `hKbig`.
An envelope of polynomial size is harmless because it is multiplied by the probability of an
exceptional set (`Kenv` is absorbed into the exponent `D₁`).  It is *never* allowed to appear
as a multiplicative constant in a `≺`: that is precisely what
`RBM.Gauss.condExpDiag_stochDom_of_offdiag` does with `(η_t^{-1}+1)²` at fixed time, and the
reason the diagonal term `k = i` is handled here by `RBM.Gauss.unifDomIcc_ibpRem_diag`
(`ibpRem(i,i) ≺ 1`, proved with the constant control `1`) instead.

## Main results

* `RBM.Gauss.unifDomIcc_condRow_of_envelope` — `≺` under `E_k`, uniformly in the time; the
  `RBM.Gauss.UnifDomIcc` analogue of `RBM.Gauss.stochDom_condRow_of_envelope`, with no
  cardinality hypothesis.
* `RBM.Gauss.unifDomIcc_condRow_sub_self` — the same for `E_k[X] - X` through a row-free
  surrogate.
* `RBM.Gauss.unifDomIcc_greenDiagCentered_sub_minor` — (4.9) along the flow, with the
  deterministic control `Ψ²`.
* `RBM.Gauss.unifDomIcc_ibpRem_offdiag`, `RBM.Gauss.unifDomIcc_ibpRem_diag`,
  `RBM.Gauss.unifDomIcc_ibpRem` — the p. 50 remainder at every pair, with control `Ψ²` off the
  diagonal and `1` on it.
* `RBM.Gauss.unifDomIcc_condExpDiag_flow` — **`hfixIBP`**.
* `RBM.Gauss.eq45Flow_of_unifDom_ibp`, `RBM.Gauss.eq45Flow_of_localLaw_gain` — the compile-time
  checks that the above fills the frozen slot of `RBM.Gauss.eq45Flow_of_unifDom`, and that with
  T128's two fluctuation inputs all three `hfix` of (4.5) are now supplied.

No signature in `RBM1D/Gauss/Eq45FlowInputs.lean`, `RBM1D/Gauss/CondStableInst.lean`,
`RBM1D/Gauss/CondDom.lean` or `RBM1D/Gauss/GoodSetFlow.lean` is touched.
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

/-- **`≺` under `E_k`, uniformly in the time** — the `RBM.Gauss.UnifDomIcc` analogue of
`RBM.Gauss.stochDom_condRow_of_envelope`.

Two things change relative to the fixed-time tool, and both are simplifications.

* **No cardinality hypothesis.**  `RBM.Gauss.UnifDomIcc` bounds the failure probability at each
  index and each time separately, so the exceptional set of `hdom` may be taken at the single
  index `a` under consideration; the union over indices that forces `[∀ N, Fintype (U N)]` and
  `hcard` in the fixed-time version is never taken here.  (It is taken later, by the net.)
* **Everything is quantified over `u` before `N`.**  The eventual-in-`N` thresholds come only
  from `hEnvpoly`, `hdom`, `hstab` and `hlow`, each of which is already uniform in `u`; the
  time enters the proof only through the data `X`, `ζ`, `χ`, `k`.

The deterministic envelope `Env N` may grow polynomially — `Kenv` is free and is absorbed into
the exponent `D₁` of the exceptional set.  This is why a time-dependent envelope such as
`η_{t_N}^{-1}` is harmless here, in contrast with the *multiplicative* constant `η_t^{-2}` that
T119's `RBM.Gauss.stochDom_Lmax_inv_W` carries. -/
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

/-- `|G_u(ω)_{ii} - m| ≺ Ψ`, uniformly in `u ∈ [s_N, t_N]`. -/
theorem unifDomIcc_green_diag_sub (hll : LocalLawUnifIcc d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω => ‖green (Hflow d N u ω) (zt E u) i i - mE E‖)
      (fun N _ _ _ => Ψ N) := by
  refine UnifDomIcc.of_le_left (ξ := fun N u (i : d.Idx N) ω =>
    ‖green (Hflow d N u ω) (zt E u) i i - (if i = i then mE E else 0)‖)
    (fun N u i ω => by simp) (hll.precomp fun N (i : d.Idx N) => (i, i))

/-- `|G_u(ω)_{ij}| ≺ Ψ` for `i ≠ j`, uniformly in `u ∈ [s_N, t_N]`. -/
theorem unifDomIcc_green_offdiag (hll : LocalLawUnifIcc d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (v : OffPair d.L d.W N) ω =>
        ‖green (Hflow d N u ω) (zt E u) v.1.1 v.1.2‖)
      (fun N _ _ _ => Ψ N) := by
  refine UnifDomIcc.of_le_left (ξ := fun N u (v : OffPair d.L d.W N) ω =>
    ‖green (Hflow d N u ω) (zt E u) v.1.1 v.1.2
      - (if v.1.1 = v.1.2 then mE E else 0)‖)
    (fun N u v ω => by rw [ite_eq_right v.2, sub_zero])
    (hll.precomp fun N (v : OffPair d.L d.W N) => v.1)

/-- `|G_{ii} - m| |G_{kk} - m| ≺ Ψ²`, uniformly in `u ∈ [s_N, t_N]`. -/
theorem unifDomIcc_prod_green_diag_sub (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hll : LocalLawUnifIcc d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (q : d.Idx N × d.Idx N) ω =>
        ‖(green (Hflow d N u ω) (zt E u) q.1 q.1 - mE E)
          * (green (Hflow d N u ω) (zt E u) q.2 q.2 - mE E)‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  have h1 := (unifDomIcc_green_diag_sub hll).precomp
    fun N (q : d.Idx N × d.Idx N) => q.1
  have h2 := (unifDomIcc_green_diag_sub hll).precomp
    fun N (q : d.Idx N × d.Idx N) => q.2
  refine UnifDomIcc.of_le_left ?_
    (UnifDomIcc.mul' (fun N u q ω => norm_nonneg _) (fun N u q ω => hΨ0 N) h1 h2)
  intro N u q ω
  exact le_of_eq (norm_mul _ _)

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

/-- The `RBM.Gauss.UnifDomIcc` analogue of `RBM.Gauss.stochDom_condRow_sub_self`. -/
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

/-- **`hprod`, uniformly in the time**: `E_i[(G_{ii} - m)(G_{kk} - m)] ≺ Ψ²`.

The control is the *deterministic* `Ψ²`, so `RBM.Gauss.CondStable` is the triviality
`E_i[Ψ²] = Ψ²` and nothing has to pass through the row integral except the observable itself.
This is what replaces T119's `RBM.Gauss.condStable_Lmax`, whose proof compares `L^max` with
`W^{-1}` and therefore costs `η^{-2}`. -/
theorem unifDomIcc_condRow_prod_green_diag (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hll : LocalLawUnifIcc d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (q : d.Idx N × d.Idx N) ω =>
        ‖condRow d N q.1 (fun η => (green (Hflow d N u η) (zt E u) q.1 q.1 - mE E)
          * (green (Hflow d N u η) (zt E u) q.2 q.2 - mE E)) ω‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  have hΨΨ0 : ∀ (N : ℕ) (u : ℝ) (q : d.Idx N × d.Idx N) (ω : Ω d), 0 ≤ Ψ N * Ψ N :=
    fun N _ _ _ => mul_nonneg (hΨ0 N) (hΨ0 N)
  refine unifDomIcc_condRow_of_envelope
    (X := fun N u (q : d.Idx N × d.Idx N) ω =>
      (green (Hflow d N u ω) (zt E u) q.1 q.1 - mE E)
        * (green (Hflow d N u ω) (zt E u) q.2 q.2 - mE E))
    (k := fun N _ (q : d.Idx N × d.Idx N) => q.1)
    (Env := fun N => ((etaT E (t N))⁻¹ + 1) ^ 2)
    (fun N u q => ((measurable_green_apply d N u (zt E u) q.1 q.1).sub
      measurable_const).mul ((measurable_green_apply d N u (zt E u) q.2 q.2).sub
        measurable_const))
    (fun N u q => measurable_const) hΨΨ0 hΨΨ0 hKenv hB ?_ hEnv
    (fun N u q ω => integrable_const _)
    (unifDomIcc_const (fun N => mul_nonneg (hΨ0 N) (hΨ0 N)) hΨlow) ?_
    (unifDomIcc_prod_green_diag_sub hΨ0 hll)
  · intro N u hu q ω
    rw [norm_mul, sq]
    have h1 := norm_green_diag_sub_mE_le_flow (s := s) hE (ht1 N) hu q.1 ω
    have h2 := norm_green_diag_sub_mE_le_flow (s := s) hE (ht1 N) hu q.2 ω
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  · simp only [condRowReal_const]
    exact UnifDomIcc.refl hΨΨ0

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

/-- **(4.9), uniformly in the time, with the deterministic control `Ψ²`.**

Unlike T119's `RBM.Gauss.stochDom_greenDiagCentered_sub_minor_Lmax`, which redoes (4.2) with
the control `L^max`, this reads the two off-diagonal factors straight off the weak local law.
The control therefore stays deterministic, which is what keeps every later step free of the
`L^max ≍ W^{-1}` comparison. -/
theorem unifDomIcc_greenDiagCentered_sub_minor (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ)) (hll : LocalLawUnifIcc d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (v : OffPair d.L d.W N) ω =>
        ‖greenDiagCentered d N u (zt E u) (mE E) v.1.2 ω
          - greenMinorDiagCentered d N u (zt E u) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  have hswap := (unifDomIcc_green_offdiag hll).precomp
    fun N (v : OffPair d.L d.W N) => (⟨(v.1.2, v.1.1), Ne.symm v.2⟩ : OffPair d.L d.W N)
  have hprod := UnifDomIcc.mul' (fun N u (v : OffPair d.L d.W N) ω => norm_nonneg _)
    (fun N u (v : OffPair d.L d.W N) ω => hΨ0 N) hswap (unifDomIcc_green_offdiag hll)
  refine UnifDomIcc.of_le_left_on hΩ ?_
    (UnifDomIcc.const_mul_left (by norm_num : (0 : ℝ) ≤ 2)
      (fun N u (v : OffPair d.L d.W N) ω => mul_nonneg (hΨ0 N) (hΨ0 N)) hprod)
  filter_upwards [hδ1] with N hδN ω hω u hu v
  exact norm_greenDiagCentered_sub_minor_le d N hE (lt_of_le_of_lt hu.2 (ht1 N)) hδN
    (hω u hu) v

end Repl

/-! ### `RBM.Gauss.ibpRem` off the diagonal, uniformly in the time -/

section IbpRem

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **`hminor`, uniformly in the time**: `E_i(G_{kk} - m) - (G_{kk} - m) ≺ Ψ²` for `k ≠ i`. -/
theorem unifDomIcc_condRow_greenDiagCentered_sub_self (d : Dims) (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1) (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ)) (hll : LocalLawUnifIcc d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (v : OffPair d.L d.W N) ω =>
        ‖condRow d N v.1.1 (greenDiagCentered d N u (zt E u) (mE E) v.1.2) ω
          - greenDiagCentered d N u (zt E u) (mE E) v.1.2 ω‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  have hΨΨ0 : ∀ (N : ℕ) (u : ℝ) (v : OffPair d.L d.W N) (ω : Ω d), 0 ≤ Ψ N * Ψ N :=
    fun N _ _ _ => mul_nonneg (hΨ0 N) (hΨ0 N)
  refine unifDomIcc_condRow_sub_self
    (X := fun N u (v : OffPair d.L d.W N) =>
      greenDiagCentered d N u (zt E u) (mE E) v.1.2)
    (X' := fun N u (v : OffPair d.L d.W N) =>
      greenMinorDiagCentered d N u (zt E u) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩)
    (k := fun N _ (v : OffPair d.L d.W N) => v.1.1)
    (Env := fun N => ((etaT E (t N))⁻¹ + 1) ^ 2)
    (fun N u v => measurable_greenDiagCentered d N u (zt E u) (mE E) v.1.2)
    (fun N u v => measurable_greenMinorDiagCentered d N u (zt E u) (mE E) v.1.1 _)
    (fun N u v => measurable_const) hΨΨ0 hΨΨ0 hKenv hB ?_ hEnv
    (fun N u v ω => integrable_const _)
    (unifDomIcc_const (fun N => mul_nonneg (hΨ0 N) (hΨ0 N)) hΨlow) ?_
    (UnifDomIcc.refl hΨΨ0)
    (fun N u v => (finDepOffRow_greenMinorMat_apply d N u (zt E u) v.1.1
      ⟨v.1.2, Ne.symm v.2⟩ ⟨v.1.2, Ne.symm v.2⟩).comp fun z => z - mE E)
    ?_ (unifDomIcc_greenDiagCentered_sub_minor d hE ht1 hΨ0 hδ1 hΩ hll)
  · intro N u hu v ω
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hηu : 0 < etaT E u := etaT_pos_of_lt_one hE hu1
    have h1 := norm_green_apply_le_etaT hE hu1 u v.1.2 v.1.2 ω
    have h2 := norm_greenMinorMat_apply_le_etaT (d := d) (N := N) hE hu1 u
      (κ := v.1.1) ⟨v.1.2, Ne.symm v.2⟩ ⟨v.1.2, Ne.symm v.2⟩ ω
    have hmono := inv_etaT_le_inv_etaT hE hu.2 (ht1 N)
    have hη0 : (0 : ℝ) ≤ (etaT E (t N))⁻¹ := by
      have := etaT_pos_of_lt_one hE (ht1 N); positivity
    have hstep : ‖greenDiagCentered d N u (zt E u) (mE E) v.1.2 ω
        - greenMinorDiagCentered d N u (zt E u) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω‖
        ≤ 2 * (etaT E (t N))⁻¹ := by
      have he : greenDiagCentered d N u (zt E u) (mE E) v.1.2 ω
          - greenMinorDiagCentered d N u (zt E u) (mE E) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω
          = green (Hflow d N u ω) (zt E u) v.1.2 v.1.2
            - greenMinorMat d N u (zt E u) v.1.1 ω ⟨v.1.2, Ne.symm v.2⟩
              ⟨v.1.2, Ne.symm v.2⟩ := by
        simp only [greenDiagCentered, greenMinorDiagCentered]; ring
      rw [he]
      refine le_trans (norm_sub_le _ _) ?_
      linarith
    refine hstep.trans ?_
    nlinarith
  · simp only [condRowReal_const]
    exact UnifDomIcc.refl hΨΨ0
  · intro N u hu v
    exact rowIntegrable_of_measurable_of_bound
      (measurable_greenDiagCentered d N u (zt E u) (mE E) v.1.2)
      (norm_greenDiagCentered_le_env hE (lt_of_le_of_lt hu.2 (ht1 N)) u v.1.2)

/-- **`RBM.Gauss.ibpRem ≺ Ψ²` off the diagonal, uniformly in the time.**  This is
`RBM.Gauss.stochDom_ibpRem_offdiag` re-run with the time carried through and with the
*deterministic* control `Ψ²` in place of `L^max`. -/
theorem unifDomIcc_ibpRem_offdiag (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ)) (hll : LocalLawUnifIcc d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (v : OffPair d.L d.W N) ω => ‖ibpRem d N E u (v.1.1, v.1.2) ω‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  have hΨΨ0 : ∀ (N : ℕ) (u : ℝ) (v : OffPair d.L d.W N) (ω : Ω d), 0 ≤ Ψ N * Ψ N :=
    fun N _ _ _ => mul_nonneg (hΨ0 N) (hΨ0 N)
  have hp := (unifDomIcc_condRow_prod_green_diag d hE ht1 hΨ0 hKenv hB hEnv hΨlow hll).precomp
    fun N (v : OffPair d.L d.W N) => (v.1.1, v.1.2)
  have hm := unifDomIcc_condRow_greenDiagCentered_sub_self d hE ht1 hΨ0 hKenv hB hEnv hΨlow
    hδ1 hΩ hll
  refine UnifDomIcc.of_le_left_icc ?_ (UnifDomIcc.add' hΨΨ0 hp hm)
  intro N u hu v ω
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  rw [ibpRem_eq_add (gaussIBP d) hE hu1 v.1.1 v.1.2 ω]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mE hE.le, one_mul]
  exact le_rfl

end IbpRem

/-! ### The diagonal term `k = i` -/

section Diag

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- `|G_{ii} - m| ≺ 1`, uniformly in the time: on the flow good event it is at most `δ_N`. -/
theorem unifDomIcc_greenDiagCentered_one (d : Dims) {V : ℕ → Type*}
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2) (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (kk : ∀ N, V N → d.Idx N) :
    UnifDomIcc (P d) s t
      (fun N u (a : V N) ω => ‖greenDiagCentered d N u (zt E u) (mE E) (kk N a) ω‖)
      (fun _ _ _ _ => (1 : ℝ)) := by
  refine unifDomIcc_of_highProb hΩ fun τ hτ => ?_
  filter_upwards [hδ1, eventually_le_rpow 1 hτ] with N hδN h1N ω hω u hu a
  have h := (hω u hu).norm_diag_sub_le (kk N a)
  simp only [greenDiagCentered]
  rw [mul_one]
  linarith

/-- **`E_i(G_{ii} - m) ≺ 1`, uniformly in the time.**

At `k = i` there is no minor surrogate and the quantity is of size `Ψ`, not `Ψ²` — but it
enters the sum of p. 50 with the coefficient `S_{ii} ≤ 2 L^max`, so `≺ 1` is all that is
needed.  Proving `≺ 1` costs nothing beyond the row-integral tool with the **constant** control
`1`, which is trivially `E_i`-stable; in particular the `η^{-2}` of T119's
`RBM.Gauss.condStable_Lmax` never appears.  The deterministic envelope `η_u^{-1} + 1` is
polynomial and is absorbed by `Kenv`. -/
theorem unifDomIcc_condExpDiag_one (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ)) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω => ‖condExpDiag d N u (zt E u) (mE E) i ω‖)
      (fun _ _ _ _ => (1 : ℝ)) := by
  have hone : ∀ (N : ℕ) (u : ℝ) (i : d.Idx N) (ω : Ω d), (0 : ℝ) ≤ 1 := fun _ _ _ _ => zero_le_one
  have hlow : UnifDomIcc (P d) s t
      (fun N _ (_ : d.Idx N) (_ : Ω d) => (N : ℝ) ^ (-B)) (fun _ _ _ _ => (1 : ℝ)) := by
    refine unifDomIcc_const (fun _ => zero_le_one) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN1
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
  refine unifDomIcc_condRow_of_envelope
    (X := fun N u (i : d.Idx N) => greenDiagCentered d N u (zt E u) (mE E) i)
    (k := fun N _ (i : d.Idx N) => i)
    (Env := fun N => ((etaT E (t N))⁻¹ + 1) ^ 2)
    (fun N u i => measurable_greenDiagCentered d N u (zt E u) (mE E) i)
    (fun N u i => measurable_const) hone hone hKenv hB ?_ hEnv
    (fun N u i ω => integrable_const _) hlow ?_
    (unifDomIcc_greenDiagCentered_one d hδ1 hΩ fun N (i : d.Idx N) => i)
  · intro N u hu i ω
    have h1 := norm_green_diag_sub_mE_le_flow (s := s) hE (ht1 N) hu i ω
    have hη0 : (0 : ℝ) ≤ (etaT E (t N))⁻¹ := (inv_pos.2 (etaT_pos_of_lt_one hE (ht1 N))).le
    simp only [greenDiagCentered]
    nlinarith
  · simp only [condRowReal_const]
    exact UnifDomIcc.refl hone

end Diag

/-! ### `RBM.Gauss.ibpRem` at every pair, uniformly in the time -/

section RemAll

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **`ibpRem(i,i) ≺ 1`, uniformly in the time.**  The diagonal remainder is *not* of size `Ψ²`
— there is no minor surrogate at `k = i` — but it is bounded, and that is enough because its
coefficient in the p. 50 sum is `S_{ii} ≤ 2 L^max`. -/
theorem unifDomIcc_ibpRem_diag (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ)) (hll : LocalLawUnifIcc d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω => ‖ibpRem d N E u (i, i) ω‖)
      (fun _ _ _ _ => (1 : ℝ)) := by
  have hone : ∀ (N : ℕ) (u : ℝ) (i : d.Idx N) (ω : Ω d), (0 : ℝ) ≤ 1 := fun _ _ _ _ => zero_le_one
  have hP1 : UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖condRow d N i (fun η => (green (Hflow d N u η) (zt E u) i i - mE E)
          * (green (Hflow d N u η) (zt E u) i i - mE E)) ω‖) (fun _ _ _ _ => (1 : ℝ)) :=
    ((unifDomIcc_condRow_prod_green_diag d hE ht1 hΨ0 hKenv hB hEnv hΨlow hll).precomp
      fun N (i : d.Idx N) => (i, i)).trans
      (unifDomIcc_const (fun _ => zero_le_one) hΨ1)
  have hP2 := unifDomIcc_condExpDiag_one (s := s) d hE ht1 hKenv hB hEnv hδ1 hΩ
  have hP3 := unifDomIcc_greenDiagCentered_one (s := s) d hδ1 hΩ fun N (i : d.Idx N) => i
  refine UnifDomIcc.of_le_left_icc ?_
    (UnifDomIcc.add' hone hP1 (UnifDomIcc.add' hone hP2 hP3))
  intro N u hu i ω
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  rw [ibpRem_eq_add (gaussIBP d) hE hu1 i i ω]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mE hE.le, one_mul]
  refine add_le_add le_rfl ?_
  have hrw : condRow d N i (greenDiagCentered d N u (zt E u) (mE E) i) ω
      - (green (Hflow d N u ω) (zt E u) i i - mE E)
      = condExpDiag d N u (zt E u) (mE E) i ω
        - greenDiagCentered d N u (zt E u) (mE E) i ω := rfl
  rw [hrw]
  exact norm_sub_le _ _

/-- **`RBM.Gauss.ibpRem` at every pair, uniformly in the time**, with the two-regime control
`Ψ²` off the diagonal and `1` on it. -/
theorem unifDomIcc_ibpRem (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ)) (hll : LocalLawUnifIcc d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (q : d.Idx N × d.Idx N) ω => ‖ibpRem d N E u q ω‖)
      (fun N _ (q : d.Idx N × d.Idx N) _ => if q.1 = q.2 then (1 : ℝ) else Ψ N * Ψ N) := by
  have hoff := unifDomIcc_ibpRem_offdiag d hE ht1 hΨ0 hKenv hB hEnv hΨlow hδ1 hΩ hll
  have hdiag := unifDomIcc_ibpRem_diag d hE ht1 hΨ0 hKenv hB hEnv hΨlow hΨ1 hδ1 hΩ hll
  intro τ hτ D hD
  filter_upwards [hoff τ hτ D hD, hdiag τ hτ D hD] with N h1 h2 u hu q
  obtain ⟨i, j⟩ := q
  by_cases hq : i = j
  · subst hq
    simpa using h2 u hu i
  · have := h1 u hu ⟨(i, j), hq⟩
    simpa [hq] using this

end RemAll

/-! ### `hfixIBP`: the assembly -/

section Assembly

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **`hfixIBP`, the time-uniform form of `RBM.Gauss.condExpDiag_stochDom_of_highProb`.**

This is the hypothesis `hfixIBP` of `RBM.Gauss.eq45Flow_of_unifDom`, at `y = condExpDiag`.

The route is T119's, re-run with the time carried through, with one change that is forced by
the `t_N → 1` regime: **the control stays deterministic all the way to the last line.**  The
fixed-time chain dominates `E_i[·]` by the random `L^max`, and therefore needs
`E_i[L^max] ≺ L^max`, which T119 proves through `L^max ≍ W^{-1}` at the cost of `η^{-2}`.  Here
every conditional expectation is dominated by `Ψ²` instead, for which `E_i` is the identity;
`L^max` is met only in the final line, and only through the *lower* half `W^{-1} ≤ 4 L^max` of
T119's sandwich, which holds at every time on the flow good event and costs no power of `η`.
The prices are the hypothesis `hΨW` — the paper's `Ψ² ≍ W^{-1}` — and `hEnv`, which asks that
`η_{t_N}^{-1}` be polynomially bounded (`Kenv` is free).

The diagonal term `k = i`, where no minor surrogate exists, is handled as in
`RBM.Gauss.norm_condExpDiag_sub_le_offdiag`: it enters with the coefficient
`S_{ii} ≤ 2 L^max`, so `RBM.Gauss.unifDomIcc_ibpRem_diag`'s `≺ 1` suffices.  Note that the
*deterministic* envelope `(η^{-1}+1)²` used at fixed time by
`RBM.Gauss.condExpDiag_stochDom_of_offdiag` would **not** do here: it enters that proof as a
multiplicative constant, and is polynomially large when `t_N → 1`. -/
theorem unifDomIcc_condExpDiag_flow (d : Dims) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ)) (hll : LocalLawUnifIcc d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖condExpDiag d N u (zt E u) (mE E) i ω
          - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
            * (green (Hflow d N u ω) (zt E u) k k - mE E)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)) := by
  classical
  have hrem := unifDomIcc_ibpRem d hE ht1 hΨ0 hKenv hB hEnv hΨlow hΨ1 hδ1 hΩ hll
  intro τ hτ D hD
  have hτ3 : (0 : ℝ) < τ / 3 := by linarith
  filter_upwards [hrem (τ / 3) hτ3 (D + 3) (by linarith), hΩ (D + 1) (by linarith), hδ1,
    card_Idx_le d, hΨW (τ / 3) hτ3, eventually_ge_atTop 1, eventually_le_rpow 2 hτ3,
    eventually_two_mul_rpow_le D] with
    N hremN hΩN hδN hcardN hΨWN hN1 h2N hdbl u hu i
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hu0 : 0 ≤ u := le_trans (hs0 N) hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  set a : ℝ := (N : ℝ) ^ (τ / 3) with hadef
  have ha0 : (0 : ℝ) < a := Real.rpow_pos_of_pos hNpos _
  have hacube : a * a * a = (N : ℝ) ^ τ := by
    rw [hadef, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    ring
  -- the exceptional sets
  set T : d.Idx N → Set (Ω d) := fun k =>
    {ω | a * (if i = k then (1 : ℝ) else Ψ N * Ψ N) < ‖ibpRem d N E u (i, k) ω‖} with hTdef
  have hTk : ∀ k : d.Idx N, (P d) (T k) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 3))) := by
    intro k
    exact hremN u hu (i, k)
  have hunion : (P d) (⋃ k, T k) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := by
    have hpow : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 3)) := Real.rpow_nonneg hNpos.le _
    have hcard' : (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) := by
      rw [Real.rpow_one] at hcardN; exact hcardN
    calc (P d) (⋃ k, T k) ≤ ∑ k : d.Idx N, (P d) (T k) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : d.Idx N, ENNReal.ofReal ((N : ℝ) ^ (-(D + 3))) :=
          Finset.sum_le_sum fun k _ => hTk k
      _ = ENNReal.ofReal ((Fintype.card (d.Idx N) : ℝ) * (N : ℝ) ^ (-(D + 3))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (Fintype.card (d.Idx N) : ℝ) * (N : ℝ) ^ (-(D + 3))
              ≤ (N : ℝ) * (N : ℝ) ^ (-(D + 3)) :=
            mul_le_mul_of_nonneg_right hcard' hpow
          have h2 : (N : ℝ) * (N : ℝ) ^ (-(D + 3)) = (N : ℝ) ^ (-(D + 2)) := by
            have hsplit := Real.rpow_add hNpos 1 (-(D + 3))
            rw [Real.rpow_one] at hsplit
            rw [← hsplit]
            congr 1
            ring
          have h3 : (N : ℝ) ^ (-(D + 2)) ≤ (N : ℝ) ^ (-(D + 1)) :=
            Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
          linarith
  -- the failure event is contained in the union
  have hsub : {ω | (N : ℝ) ^ τ * Lmax (Hflow d N u ω) (zt E u)
        < ‖condExpDiag d N u (zt E u) (mE E) i ω
          - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
            * (green (Hflow d N u ω) (zt E u) k k - mE E)‖}
      ⊆ (goodSetFlow d E s t δ N)ᶜ ∪ ⋃ k, T k := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨hgoodc, hT⟩ := hcon
    have hgood : ω ∈ goodSetFlow d E s t δ N := by
      by_contra hx
      exact hgoodc hx
    simp only [Set.mem_iUnion, not_exists] at hT
    have hTle : ∀ k : d.Idx N, ‖ibpRem d N E u (i, k) ω‖
        ≤ a * (if i = k then (1 : ℝ) else Ψ N * Ψ N) := by
      intro k
      have := hT k
      rw [hTdef] at this
      simpa only [Set.mem_ofPred_eq, not_lt] using this
    have hGE : GoodEvent (green (Hflow d N u ω) (zt E u)) (mE E) (δ N) := hgood u hu
    have hL0 : 0 ≤ Lmax (Hflow d N u ω) (zt E u) :=
      Lmax_nonneg (Hflow_isHermitian d N u ω)
    have hΨ2 : 0 ≤ Ψ N * Ψ N := mul_nonneg (hΨ0 N) (hΨ0 N)
    have hbound := norm_condExpDiag_sub_le_offdiag (gaussIBP d) hE hu0 hu1 i ω
      (A := a * (Ψ N * Ψ N)) (Adiag := a) (by positivity)
      (fun k hk => by simpa [Ne.symm hk] using hTle k)
      (by simpa using hTle i)
    -- `S_{ii} ≤ 2 L^max` and `W^{-1} ≤ 4 L^max` on the good event
    have hS := Sblk_le_Lmax (Hflow_isHermitian d N u ω) (norm_mE hE.le) hGE hδN i i
    have hW := inv_W_le_Lmax_flow (δ := δ) hE.le hδN hgood hu
    have hWpos : (0 : ℝ) < ((d.W N : ℕ) : ℝ) := by exact_mod_cast d.W_pos N
    have hΨL : Ψ N * Ψ N ≤ a * Lmax (Hflow d N u ω) (zt E u) := by
      have h1 : 4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ a := hΨWN
      have h2 : (1 : ℝ) ≤ 4 * Lmax (Hflow d N u ω) (zt E u) * ((d.W N : ℕ) : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hW hWpos.le
        rwa [inv_mul_cancel₀ hWpos.ne'] at h
      nlinarith [mul_le_mul_of_nonneg_left h1 hL0, mul_le_mul_of_nonneg_left h2 hΨ2]
    have hfin : ‖condExpDiag d N u (zt E u) (mE E) i ω
        - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N u ω) (zt E u) k k - mE E)‖
        ≤ (N : ℝ) ^ τ * Lmax (Hflow d N u ω) (zt E u) := by
      refine hbound.trans ?_
      rw [← hacube]
      have hstep1 : a * (Ψ N * Ψ N) ≤ a * (a * Lmax (Hflow d N u ω) (zt E u)) :=
        mul_le_mul_of_nonneg_left hΨL ha0.le
      have hstep2 : Sblk (d.L N) (d.W N) i i * a
          ≤ 2 * Lmax (Hflow d N u ω) (zt E u) * a :=
        mul_le_mul_of_nonneg_right hS ha0.le
      have hkey : (0 : ℝ) ≤ (a - 2) * (a + 1) * a * Lmax (Hflow d N u ω) (zt E u) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) ha0.le) hL0
      nlinarith [hstep1, hstep2, hkey]
    exact absurd hfin (not_le.2 hω)
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hNpos.le _
  calc (P d) {ω | (N : ℝ) ^ τ * Lmax (Hflow d N u ω) (zt E u)
        < ‖condExpDiag d N u (zt E u) (mE E) i ω
          - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
            * (green (Hflow d N u ω) (zt E u) k k - mE E)‖}
      ≤ (P d) ((goodSetFlow d E s t δ N)ᶜ ∪ ⋃ k, T k) := measure_mono hsub
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add hΩN hunion
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [two_mul, ENNReal.ofReal_add hp hp]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hdbl

end Assembly

/-! ### Filling the `hfixIBP` slot of (4.5) -/

section Slot

variable {d : Dims} {E : ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B K : ℝ}

/-- **The compile-time check: `RBM.Gauss.unifDomIcc_condExpDiag_flow` really fills the
`hfixIBP` slot of `RBM.Gauss.eq45Flow_of_unifDom`.**

`RBM1D/Gauss/Eq45FlowInputs.lean` is not touched: the `y` slot is instantiated at
`RBM.Gauss.condExpDiag`, which is what the other two inputs (T128) already use. -/
theorem eq45Flow_of_unifDom_ibp (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ)
    (hll : LocalLawUnifIcc d E s t Ψ)
    (hHolIBP : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖condExpDiag d N u (zt E u) (mE E) i ω
              - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N u ω) (zt E u) k k - mE E)‖
          - ‖condExpDiag d N v (zt E v) (mE E) i ω
              - (v : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N v ω) (zt E v) k k - mE E)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hHolRow : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfixRow : UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E)
            - condExpDiag d N u (zt E u) (mE E) k ω)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)))
    (hHolBlk : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : ZMod (d.L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hfixBlk : UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E)
            - condExpDiag d N u (zt E u) (mE E) k ω)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u))) :
    StepGlue.Eq45Flow (sample d) E s t :=
  eq45Flow_of_unifDom d hκ0 hκ1 hEκ hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ
    (y := fun N u ω i => condExpDiag d N u (zt E u) (mE E) i ω)
    hHolIBP
    (unifDomIcc_condExpDiag_flow d hE hs0 ht1 hΨ0 hKenv hB hEnv hΨlow hΨ1 hδ1 hΨW hΩ hll)
    hHolRow hfixRow hHolBlk hfixBlk

/-- **(4.5) along the flow with all three fixed-time inputs supplied.**

The `hfix` slots are now: this file's `RBM.Gauss.unifDomIcc_condExpDiag_flow` for the
integration-by-parts input, and T128's `RBM.Gauss.unifDomIcc_flucRow_condExpDiag` /
`RBM.Gauss.unifDomIcc_flucBlk_condExpDiag` for the two fluctuation-averaging inputs.  What is
left is *not* a fixed-time estimate any more: the three Hölder moduli in the time, the
`RBM.Gauss.FlucGain` interface, the `u`-uniform weak local law `hll`, the flow good event `hΩ`
(T130 produces it from `hll`), and purely numerical regime conditions. -/
theorem eq45Flow_of_localLaw_gain (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ)
    (hll : LocalLawUnifIcc d E s t Ψ)
    {Bp ep : ℕ → ℝ}
    (hg : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), FlucGain d N u (zt E u) (mE E) (Bp N) (ep N))
    (hpos : ∀ N, 0 < ep N * Bp N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ3 : ∀ N, ((3 * d.W N : ℝ))⁻¹ ≤ ep N ^ 2)
    (hcρ1 : ∀ N, ((d.W N : ℝ))⁻¹ ≤ ep N ^ 2)
    (hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (ep N * Bp N) ≤ (N : ℝ) ^ τ)
    (hHolIBP : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖condExpDiag d N u (zt E u) (mE E) i ω
              - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N u ω) (zt E u) k k - mE E)‖
          - ‖condExpDiag d N v (zt E v) (mE E) i ω
              - (v : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N v ω) (zt E v) k k - mE E)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hHolRow : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hHolBlk : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : ZMod (d.L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2)) :
    StepGlue.Eq45Flow (sample d) E s t :=
  eq45Flow_of_unifDom_ibp d hκ0 hκ1 hEκ hE hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ hΨ0 hKenv hB
    hEnv hΨlow hΨ1 hΨW hll hHolIBP hHolRow
    (unifDomIcc_flucRow_condExpDiag d hE ht1 hg hpos hρ1 hcρ3 hδ1 hΩ hΦW) hHolBlk
    (unifDomIcc_flucBlk_condExpDiag d hE ht1 hg hpos hρ1 hcρ1 hδ1 hΩ hΦW)

/-- **(4.5) along the flow, against the *graded* gain interface** — T151.

The word-for-word analogue of `RBM.Gauss.eq45Flow_of_localLaw_gain`, with the one interface
that was mismatched replaced: `RBM.Gauss.FlucGain` at the paper's size `ρ ≍ Ψ` is not a
theorem and T137/T142 do not prove it — what they prove is the word-length-graded
`RBM.Gauss.FlucGainUpTo` (`RBM.Gauss.flucGainUpTo_of_minorDiff'`, at `ρ = 2Ψ`).  The `2p`-th
moment of (4.12) only ever builds words of length `≤ 2p`, so the gain is asked for only at
`M = 2 * p` for each `p`; the grade-dependence of the size is carried by the factorization
`Bp p N ≤ Kp p * Ψ N`, whose `p`-dependent factor the constant of
`RBM.Gauss.unifDomIcc_of_moment` absorbs.

**The conclusion is verbatim that of the unprimed version**, `RBM.StepGlue.Eq45Flow`, and the
unprimed version is untouched (`RBM.Gauss.FlucGain.upTo` still connects the two).

**`hΦW` is gone.**  At T142's size the control is `ρ B = 2Ψ²`, and
`RBM.Gauss.flucPhiW_of_psiW` derives `4 W ρ B ≤ N^τ` from the `hΨW` this theorem already
carries; likewise the two size conditions `(3W)⁻¹ ≤ ρ²` and `W⁻¹ ≤ ρ²` collapse into the
single `hΨW'`, `W⁻¹ ≤ 4Ψ²`.  So moving to the graded interface *removes* hypotheses. -/
theorem eq45Flow_of_localLaw_gain' (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ)
    (hll : LocalLawUnifIcc d E s t Ψ)
    {Bp : ℕ → ℕ → ℝ} {Kp : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo d N u (zt E u) (mE E) (Bp p N) (2 * Ψ N) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBK : ∀ p N, Bp p N ≤ Kp p * Ψ N)
    (hΨpos : ∀ N, 0 < Ψ N) (hΨhalf : ∀ N, 2 * Ψ N ≤ 1)
    (hΨW' : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * Ψ N ^ 2)
    (hHolIBP : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖condExpDiag d N u (zt E u) (mE E) i ω
              - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N u ω) (zt E u) k k - mE E)‖
          - ‖condExpDiag d N v (zt E v) (mE E) i ω
              - (v : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N v ω) (zt E v) k k - mE E)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hHolRow : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hHolBlk : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : ZMod (d.L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2)) :
    StepGlue.Eq45Flow (sample d) E s t :=
  eq45Flow_of_unifDom_ibp d hκ0 hκ1 hEκ hE hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ hΨ0 hKenv hB
    hEnv hΨlow hΨ1 hΨW hll hHolIBP hHolRow
    (unifDomIcc_flucRow_condExpDiag_psi d hE ht1 hg hKp hBK hΨpos hΨhalf hΨW' hδ1 hΩ hΨW)
    hHolBlk
    (unifDomIcc_flucBlk_condExpDiag_psi d hE ht1 hg hKp hBK hΨpos hΨhalf hΨW' hδ1 hΩ hΨW)

end Slot

