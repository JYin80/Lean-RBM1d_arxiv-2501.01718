/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.IBP
import RBM1D.Gauss.MinorReplace

/-!
# `≺` under the conditional expectation `E_k`, and the diagonal term of the integration by parts

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4, the proof of (4.5).

## Why `≺` does not simply pass through `E_k`

Definition 2.1 (i) carries an **exceptional event**: `X ≺ Y` says only that
`P(|X| > N^τ Y) ≤ N^{-D}`, and says *nothing* about the size of `X` there.  Integrating over
row `k` does not make that event disappear — `E_k[1_{bad} X]` has no a priori smallness — so
"`X ≺ Y` implies `E_k[X] ≺ Y`" is **false as stated**.  Two things have to be added.

1. A **deterministic envelope** `‖X ω‖ ≤ Env N` valid on the *whole* space.  Along the flow
   `z_t` of (2.35) this is free: `Im z_t = η_t > 0`, so `‖G_t‖_op ≤ η_t⁻¹` pointwise in `ω`
   (`RBM.Gauss.norm_green_zt_le`).  With it, the bad part of the row integral is at most
   `Env(N) · P(slice)`, where `slice` is the row-`k` section of the bad event.
2. A way to make `P(slice)` small.  For a *fixed* `ω` the section can have probability one;
   what is true is the Fubini identity
   `∫ P(slice_ω) dP(ω) = P(bad)` (`RBM.Gauss.lintegral_measure_rowSlice`, which is exactly
   `RBM.Gauss.measurePreserving_rowSplit`), and then Markov moves the smallness of the
   *average* to smallness *outside a small set of `ω`*
   (`RBM.Gauss.meas_measure_rowSlice_ge`).

The same accounting as `RBM1D/Gauss/Envelope.lean`: a good-event bound, plus an envelope
on the complement, plus a quantitative bound on the probability of the complement.

Finally, the control itself has to survive the row integral.  Writing `E_k` out as the exact
coordinate integral of `RBM1D/Gauss/CondRow.lean` gives

  `‖E_k[X](ω)‖ ≤ N^τ · E_k[ζ](ω) + Env(N) · P(slice_ω)`,

so the natural conclusion is a bound by `E_k[ζ]`, not by `ζ`.  One needs in addition the
comparison `E_k[ζ] ≺ χ` (and the integrability that makes `E_k[ζ]` an honest integral); for a
control that does not read row `k` — a minor observable, or a deterministic `Ψ²` — it is
trivially satisfied.

## Main results

* `RBM.Gauss.condRowReal` — `E_k` of a real observable, the exact row integral of
  `RBM1D/Gauss/CondRow.lean`.
* `RBM.Gauss.lintegral_measure_rowSlice`, `RBM.Gauss.meas_measure_rowSlice_ge` — the Fubini
  identity for the row section of a set, and Markov applied to it.
* `RBM.Gauss.norm_condRow_le_split` — the pointwise good/bad split of the row integral.
* `RBM.Gauss.card_Idx_prod_le`, `RBM.Gauss.norm_green_diag_sub_mE_le` — the cardinality bound
  for a pair of indices and the deterministic envelope `|G_{ii} - m| ≤ η_t⁻¹ + 1`.
* `RBM.Gauss.norm_condExpDiag_sub_le_offdiag` — the weighted reduction of the remainder of the
  integration by parts in the proof of (4.5).  On the diagonal the statement
  `E_i(G_{ii}-m) - (G_{ii}-m) ≺ Ψ²` is *false* (the left side is the fluctuation
  `-(1 - E_i)(G_{ii}-m)`, of size `Ψ`); the diagonal term carries the coefficient
  `S_{ii} ≤ 2 L_max`, so the deterministic envelope of `RBM.Gauss.ibpRem` suffices for it.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal

variable {d : Dims} {N : ℕ}

/-! ### `E_k` of a real observable -/

/-- **`E_k[f]` for a real-valued `f`**, the same exact coordinate integral as
`RBM.Gauss.condRow`: integrate the row-`k` coordinates out and freeze the others.  No
`MeasureTheory.condExp` is involved, and the identity is pointwise in `ω`. -/
noncomputable def condRowReal (d : Dims) (N : ℕ) (k : d.Idx N) (f : Ω d → ℝ) : Ω d → ℝ :=
  fun ω => ∫ ω', f (rowSplit d N k ω ω') ∂(P d)

@[simp] theorem condRowReal_const (k : d.Idx N) (c : ℝ) :
    condRowReal d N k (fun _ => c) = fun _ => c := by
  funext ω; simp [condRowReal]

/-! ### The row section of a set, and its measure -/

/-- The **row-`k` section** of `S` at `ω`: the `ω'` for which the split point `rowSplit k ω ω'`
lands in `S`.  `E_k[1_S](ω)` is its probability. -/
def rowSlice (d : Dims) (N : ℕ) (k : d.Idx N) (S : Set (Ω d)) (ω : Ω d) : Set (Ω d) :=
  {ω' | rowSplit d N k ω ω' ∈ S}

theorem measurableSet_rowSlice {k : d.Idx N} {S : Set (Ω d)} (hS : MeasurableSet S) (ω : Ω d) :
    MeasurableSet (rowSlice d N k S ω) :=
  hS.preimage (measurable_rowSplit_right d N k ω)

theorem measurable_measure_rowSlice (d : Dims) (N : ℕ) (k : d.Idx N) {S : Set (Ω d)}
    (hS : MeasurableSet S) : Measurable fun ω => (P d) (rowSlice d N k S ω) := by
  have hpre : MeasurableSet ((fun p : Ω d × Ω d => rowSplit d N k p.1 p.2) ⁻¹' S) :=
    hS.preimage (measurable_rowSplit d N k)
  exact measurable_measure_prodMk_left hpre

/-- **The Fubini identity for the row section.**  Averaging the probability of the section over
the frozen coordinates returns the probability of the set itself.  This is
`RBM.Gauss.measurePreserving_rowSplit`, and it is the reason the exceptional event of
Definition 2.1 (i) can be controlled *after* conditioning. -/
theorem lintegral_measure_rowSlice (d : Dims) (N : ℕ) (k : d.Idx N) {S : Set (Ω d)}
    (hS : MeasurableSet S) :
    ∫⁻ ω, (P d) (rowSlice d N k S ω) ∂(P d) = (P d) S := by
  have hmeas := measurable_rowSplit d N k
  have hpre : MeasurableSet ((fun p : Ω d × Ω d => rowSplit d N k p.1 p.2) ⁻¹' S) :=
    hS.preimage hmeas
  have h1 : (P d) S
      = ((P d).prod (P d)) ((fun p : Ω d × Ω d => rowSplit d N k p.1 p.2) ⁻¹' S) := by
    conv_lhs => rw [← (measurePreserving_rowSplit d N k).map_eq]
    exact Measure.map_apply hmeas hS
  rw [h1, Measure.prod_apply hpre]
  rfl

/-- **Markov for the row section.**  The set of frozen configurations whose section is not small
is itself small: `ε · P{ω : P(slice_ω) ≥ ε} ≤ P(S)`. -/
theorem meas_measure_rowSlice_ge (d : Dims) (N : ℕ) (k : d.Idx N) {S : Set (Ω d)}
    (hS : MeasurableSet S) (ε : ℝ≥0∞) :
    ε * (P d) {ω | ε ≤ (P d) (rowSlice d N k S ω)} ≤ (P d) S := by
  have h := mul_meas_ge_le_lintegral₀
    (μ := P d) (measurable_measure_rowSlice d N k hS).aemeasurable ε
  rwa [lintegral_measure_rowSlice d N k hS] at h

/-! ### The pointwise good/bad split of a row integral

This is the accounting of `RBM1D/Gauss/Envelope.lean`, transplanted from the integral over the
whole space to the integral over one row: on the good set the integrand obeys `‖X‖ ≤ c f`, and
on the bad set it obeys only the deterministic envelope, whose contribution is the envelope
times the probability of the row section. -/

/-- **The split.**  If `‖X‖ ≤ c f` off a set `S` and `‖X‖ ≤ Env` everywhere, then

  `‖E_k[X](ω)‖ ≤ c E_k[f](ω) + Env · P(slice of S at ω)`. -/
theorem norm_condRow_le_split {k : d.Idx N} {X : Ω d → ℂ} (hX : Measurable X)
    {f : Ω d → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hfint : ∀ ω : Ω d, Integrable (fun ω' => f (rowSplit d N k ω ω')) (P d))
    {Env c : ℝ} (hEnv : ∀ σ, ‖X σ‖ ≤ Env) (hc : 0 ≤ c)
    {S : Set (Ω d)} (hS : MeasurableSet S)
    (hgood : ∀ σ, σ ∉ S → ‖X σ‖ ≤ c * f σ) (ω : Ω d) :
    ‖condRow d N k X ω‖
      ≤ c * condRowReal d N k f ω + Env * (P d).real (rowSlice d N k S ω) := by
  have hsm := measurable_rowSplit_right d N k ω
  have hSω : MeasurableSet (rowSlice d N k S ω) := measurableSet_rowSlice hS ω
  have hXint : Integrable (fun ω' => X (rowSplit d N k ω ω')) (P d) :=
    Integrable.mono' (integrable_const Env) ((hX.comp hsm).aestronglyMeasurable)
      (Eventually.of_forall fun _ => hEnv _)
  have hindint : Integrable ((rowSlice d N k S ω).indicator fun _ => Env) (P d) :=
    (integrable_const Env).indicator hSω
  have hcf : Integrable (fun ω' => c * f (rowSplit d N k ω ω')) (P d) := (hfint ω).const_mul c
  have hpt : ∀ ω' : Ω d, ‖X (rowSplit d N k ω ω')‖
      ≤ c * f (rowSplit d N k ω ω')
        + (rowSlice d N k S ω).indicator (fun _ => Env) ω' := by
    intro ω'
    by_cases hω' : ω' ∈ rowSlice d N k S ω
    · rw [Set.indicator_of_mem hω']
      have h1 := hEnv (rowSplit d N k ω ω')
      have h2 : 0 ≤ c * f (rowSplit d N k ω ω') := mul_nonneg hc (hf0 _)
      linarith
    · rw [Set.indicator_of_notMem hω']
      have h1 := hgood (rowSplit d N k ω ω') hω'
      linarith
  rw [condRow_apply]
  calc ‖∫ ω', X (rowSplit d N k ω ω') ∂(P d)‖
      ≤ ∫ ω', ‖X (rowSplit d N k ω ω')‖ ∂(P d) := norm_integral_le_integral_norm _
    _ ≤ ∫ ω', (c * f (rowSplit d N k ω ω')
        + (rowSlice d N k S ω).indicator (fun _ => Env) ω') ∂(P d) :=
        integral_mono hXint.norm (hcf.add hindint) hpt
    _ = c * condRowReal d N k f ω + Env * (P d).real (rowSlice d N k S ω) := by
        rw [integral_add hcf hindint, integral_const_mul,
          integral_indicator_const _ hSω, smul_eq_mul, mul_comm ((P d).real _) Env]
        rfl

/-! ### The general tool -/

section Tool

variable {U : ℕ → Type*}

end Tool

/-! ### The paper's control `L_max`

Two facts about `RBM.Lmax` are needed to feed it into the tool: it is a measurable function of
`ω`, and it is not super-polynomially small.  The second holds on the event `Ω(t,c)` of (4.1),
where `W⁻¹ ≤ 4 L_max` (`RBM.inv_W_le_Lmax`); since `W ≤ N` this gives `N^{-1} ≺ L_max`. -/

section LmaxControl

variable {E t : ℝ} {δ : ℕ → ℝ}

end LmaxControl

/-! ### Cardinality and envelope inputs -/

section Pieces

variable {E t : ℝ} {δ : ℕ → ℝ}

/-- `#(Idx × Idx) ≤ N²` eventually — the Definition 2.1 (i) cardinality bound for a pair of
indices. -/
theorem card_Idx_prod_le (d : Dims) :
    ∀ᶠ N : ℕ in atTop, (Fintype.card (d.Idx N × d.Idx N) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
  filter_upwards [card_Idx_le d, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [Real.rpow_one] at hN
  have h0 : (0 : ℝ) ≤ (Fintype.card (d.Idx N) : ℝ) := Nat.cast_nonneg _
  have hsq : (N : ℝ) * (N : ℝ) = (N : ℝ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  rw [Fintype.card_prod]
  push_cast
  calc (Fintype.card (d.Idx N) : ℝ) * (Fintype.card (d.Idx N) : ℝ)
      ≤ (N : ℝ) * (N : ℝ) := mul_le_mul hN hN h0 hN0
    _ = (N : ℝ) ^ (2 : ℝ) := hsq

/-- `|G_{ii} - m| ≤ η_t⁻¹ + 1` on the whole space. -/
theorem norm_green_diag_sub_mE_le (hE : |E| < 2) (ht : t < 1) (u : ℝ) (i : d.Idx N) (ω : Ω d) :
    ‖green (Hflow d N u ω) (zt E t) i i - mE E‖ ≤ (etaT E t)⁻¹ + 1 :=
  norm_greenDiagCentered_le_env hE ht u i ω

/-! ### The diagonal term of the integration by parts

A bound on the remainder that is uniform in `(i, k)` would need a bound `≺ Ψ²` at **every**
pair `(i, k)`, including `k = i`; but at `k = i` the quantity `E_i(G_{ii} - m) - (G_{ii} - m)`
is the fluctuation `-(1 - E_i)(G_{ii} - m)`, of size `Ψ`, not `Ψ²`.

The diagonal term does not have to be small, because it enters the sum
`∑_k S_{ik} · ibpRem(i,k)` with the coefficient `S_{ii} ≍ W⁻¹`, and on the event `Ω(t,c)` of
(4.1) one has `S_{ii} ≤ 2 L_max` (`RBM.Sblk_le_Lmax`).  Since `ibpRem` has a *deterministic*
envelope, the single diagonal term contributes `O(L_max)` by itself.  So the reduction below is
a weighted bound, and needs `ibpRem ≺ L_max` **only off the diagonal**. -/

section Assembly

variable {E t : ℝ} {δ : ℕ → ℝ}

/-- **The weighted reduction** of the remainder of the integration by parts in the proof of
(4.5).  Instead of a *uniform* bound on `ibpRem d N E t (i, ·)`, the diagonal term is kept
separate, with its own bound and its own coefficient `S_{ii}`: the row sums of `S` are one, so

  `‖remainder‖ ≤ A + S_{ii} · A_diag`

as soon as `‖ibpRem(i,k)‖ ≤ A` for `k ≠ i` and `‖ibpRem(i,i)‖ ≤ A_diag`. -/
theorem norm_condExpDiag_sub_le_offdiag (hG : GaussIBP d) (hE : |E| < 2) (ht0 : 0 ≤ t)
    (ht : t < 1) (i : d.Idx N) (ω : Ω d) {A Adiag : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ k : d.Idx N, k ≠ i → ‖ibpRem d N E t (i, k) ω‖ ≤ A)
    (hAd : ‖ibpRem d N E t (i, i) ω‖ ≤ Adiag) :
    ‖condExpDiag d N t (zt E t) (mE E) i ω
        - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N t ω) (zt E t) k k - mE E)‖
      ≤ A + Sblk (d.L N) (d.W N) i i * Adiag := by
  classical
  have hterm : ∀ k : d.Idx N, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω
      = (Sblk (d.L N) (d.W N) i k : ℂ) * condRow d N i
          (fun η => green (Hflow d N t η) (zt E t) i i
            * (green (Hflow d N t η) (zt E t) k k - mE E)) ω
        - mE E * ((Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N t ω) (zt E t) k k - mE E)) := by
    intro k
    simp only [ibpRem]
    ring
  have hkey : condExpDiag d N t (zt E t) (mE E) i ω
      - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
        * (green (Hflow d N t ω) (zt E t) k k - mE E)
      = (t : ℂ) * mE E * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω := by
    rw [condExpDiag_eq_sum_Sblk hG hE hE.le ht0 ht i ω,
      Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k),
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hSrow := sum_Sblk_row (L := d.L N) (W := d.W N) (d.three_le_L N) i
  have hsum : ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖
      ≤ A + Sblk (d.L N) (d.W N) i i * Adiag := by
    have hstep : ∑ k, Sblk (d.L N) (d.W N) i k * ‖ibpRem d N E t (i, k) ω‖
        ≤ A + Sblk (d.L N) (d.W N) i i * Adiag := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun k => Sblk (d.L N) (d.W N) i k * ‖ibpRem d N E t (i, k) ω‖) (Finset.mem_univ i)]
      have hdiagle : Sblk (d.L N) (d.W N) i i * ‖ibpRem d N E t (i, i) ω‖
          ≤ Sblk (d.L N) (d.W N) i i * Adiag :=
        mul_le_mul_of_nonneg_left hAd (Sblk_nonneg _ _)
      have hoffle : ∑ k ∈ Finset.univ.erase i,
            Sblk (d.L N) (d.W N) i k * ‖ibpRem d N E t (i, k) ω‖ ≤ A := by
        calc ∑ k ∈ Finset.univ.erase i,
              Sblk (d.L N) (d.W N) i k * ‖ibpRem d N E t (i, k) ω‖
            ≤ ∑ k ∈ Finset.univ.erase i, Sblk (d.L N) (d.W N) i k * A := by
              refine Finset.sum_le_sum fun k hk => ?_
              exact mul_le_mul_of_nonneg_left (hA k (Finset.ne_of_mem_erase hk))
                (Sblk_nonneg _ _)
          _ = (∑ k ∈ Finset.univ.erase i, Sblk (d.L N) (d.W N) i k) * A := by
              rw [Finset.sum_mul]
          _ ≤ (∑ k, Sblk (d.L N) (d.W N) i k) * A := by
              refine mul_le_mul_of_nonneg_right ?_ hA0
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                fun k _ _ => Sblk_nonneg _ _
          _ = A := by rw [hSrow, one_mul]
      linarith
    calc ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖
        ≤ ∑ k, ‖(Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖ := norm_sum_le _ _
      _ = ∑ k, Sblk (d.L N) (d.W N) i k * ‖ibpRem d N E t (i, k) ω‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Sblk_nonneg _ _)]
      _ ≤ A + Sblk (d.L N) (d.W N) i i * Adiag := hstep
  rw [hkey, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mE hE.le, mul_one]
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht.le
  calc |t| * ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖
      ≤ 1 * ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖ :=
        mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ = ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ) * ibpRem d N E t (i, k) ω‖ := one_mul _
    _ ≤ A + Sblk (d.L N) (d.W N) i i * Adiag := hsum

end Assembly

end Pieces

end RBM.Gauss


