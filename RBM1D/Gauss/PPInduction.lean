/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridAssemblyKerClass
import RBM1D.Gauss.PPDrift
import RBM1D.Gauss.PPGoodEvent
import RBM1D.Gauss.PPCondVar
import RBM1D.Gauss.GridHierarchyN
import RBM1D.Gauss.GridStepBound
import RBM1D.Gauss.FlowHolder
import RBM1D.Gauss.LoopLipschitz
import RBM1D.Gauss.TraceMoment

/-!
# The `(+,+)` 2-loop grid bound, induction form

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (5.92) at `n = 2`, `σ = (+,+)` (Lemma 5.10, (5.79)–(5.81)), with the causal form and
the forbidden-zone argument of the continuity argument in §5.6, realized on the grid by a
**good-set stopping time** (`tauPP`, a single `firstHit` of the good-set-exit indicator) and a
**deterministic discrete Bihari induction**. **No threshold stopping time** (no
`firstHit (J − θ)`, no `min_firstHit_eq_of_at`, no `gridTau`) occurs anywhere in this file.

## Main declarations

* **(T2)** `discrete_bihari` (strong induction, "every `m` dominating `f_j`, `j < k`" form).
* **(T1)** `PPAssemblyHyp`, `PPAssemblyHyp.toPW` — the hypotheses of
  `grid_assembly_stopped_pathwise` at `σ = (+,+)`, `κ = C_U(κ)²`, `εK = 0`.
* Ingredient Y, **general loop length `n`**: `Ymoments_of_ae_eq`,
  `stepYC_norm_le_incr_ae`, `measurable_stepYC_filt`, `condExp_fun_incr`.
* The real `(+,+)` objects: `App`, `Dpp`, `Zpp`, `Ypp`, `Rraw`, `Rpp`, `Ast`; `one_step_pp`
  (pathwise one-step identity), `hexp_pp` (stopped Duhamel expansion), `ae_Rpp_eq`,
  `norm_drift_pp_le` ((5.79)+(5.80) on the good set), `goodSetPP_shift` (the QV time shift),
  `hqv_pp` (per-target paired `vC` QV), `ppY_fields`, `ppHyp_real`.
* Closure: `stepErrN_two_le`, `drift_sum_bound` (linear small term absorbed),
  `qv_sum_bound`, `sqrt_qv_le`, `R_sum_bound`, `pp_closure_fixedN_core`,
  `pp_closure_fixedN_plain`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open Finset MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ### (T2) The deterministic discrete Bihari lemma -/

section Bihari

/-- **`discrete_bihari`** (strong-induction form). If `4 C c′ L_N ≤ A` and, for every
`k ≤ K` and every `m ≥ 0` dominating all earlier values `f_j` (`j < k`),
`f_k ≤ c′ + C m² L_N / A`, then `f_k ≤ 2c′` for every `k ≤ K`. Only the values at `j < k` enter
the step at `k`. -/
theorem discrete_bihari {K : ℕ} {f : ℕ → ℝ} {c' C LN A : ℝ} (hC : 0 ≤ C) (hLN : 0 ≤ LN)
    (hA : 0 < A) (hc' : 0 ≤ c') (hzone : 4 * C * c' * LN ≤ A) (_h0 : f 0 ≤ c')
    (hstep : ∀ k ≤ K, ∀ m : ℝ, 0 ≤ m → (∀ j < k, f j ≤ m) → f k ≤ c' + C * m ^ 2 * LN / A) :
    ∀ k ≤ K, f k ≤ 2 * c' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hprev : ∀ j < k, f j ≤ 2 * c' := fun j hj => ih j hj (by omega)
    have h1 := hstep k hk (2 * c') (by linarith) hprev
    have h2 : C * (2 * c') ^ 2 * LN / A ≤ c' := by
      rw [div_le_iff₀ hA]
      have : C * (2 * c') ^ 2 * LN = c' * (4 * C * c' * LN) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hzone hc'
    linarith

end Bihari

/-! ### (T1) The `(+,+)` instantiation of the pathwise assembly -/

section Instantiation

/-- The charge `σ_pp = (+,+)` edge parameters `ξ = xiOf (mSigma E) (+,+)` (both `m²`). -/
abbrev xiPP (E : ℝ) : Fin 2 → ℂ := xiOf (mSigma E) (![true, true] : Fin 2 → Bool)

theorem norm_xiPP_le_one {E : ℝ} (hE : |E| ≤ 2) (p : Fin 2) : ‖xiPP E p‖ ≤ 1 := by
  show ‖mSigma E _ * mSigma E _‖ ≤ 1
  rw [norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul]

/-- **The analytic hypotheses of (T1)**: `GridAssemblyHypPW` with the kernel fields
(`hker`, `hκ0`, `hε0`, `hδ0`, `hA0cls`, `hδD0`, `hDcls`) **removed** — they are discharged at
`σ = (+,+)` by the bounded kernel (`PPAssemblyHyp.toPW`) — and with the grid times
nondecreasing on `[0,K]` (needed for `u_i ≤ u_k`). -/
structure PPAssemblyHyp {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω')
    (ℱ : Filtration ℕ mΩ') (L : ℕ) [NeZero L] (E : ℝ) (u : ℕ → ℝ)
    (τ : Ω' → ℕ) (Δ : ℝ) (K : ℕ) (A0 : Ω' → LoopArg L 2 → ℂ)
    (A Dr Z Y R : ℕ → Ω' → LoopArg L 2 → ℂ) (dDrift : ℕ → Ω' → ℝ)
    (c : ℕ → LoopArg L 2 → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) : Prop where
  hL3 : 3 ≤ L
  hu0 : ∀ i ≤ K, 0 ≤ u i
  hu1 : ∀ i ≤ K, u i < 1
  hmono : ∀ i k, i ≤ k → k ≤ K → u i ≤ u k
  hΔ0 : 0 ≤ Δ
  hexp : ∀ k ≤ K, ∀ᵐ ω ∂μ, A k ω = Uker L (xiPP E) (u 0 : ℂ) (u k : ℂ) (A0 ω)
      + ∑ j ∈ range (min k (τ ω)), Uker L (xiPP E) (u (j + 1) : ℂ) (u k : ℂ)
          ((Δ : ℂ) • Dr j ω + Z (j + 1) ω + Y (j + 1) ω + R j ω)
  hdDrift0 : ∀ ω j, j < K → 0 ≤ dDrift j ω
  hdrift : ∀ ω j, j < K → j < τ ω → ∀ b, ‖Dr j ω b‖ ≤ dDrift j ω
  hc_pos : ∀ k, 1 ≤ k → k ≤ K → ∀ a, 0 < ∑ j ∈ range k, (c k a j : ℝ)
  hYmeas : ∀ i, StronglyMeasurable[ℱ i] (Y i)
  hv0 : ∀ j < K, 0 ≤ v j
  hw0 : ∀ j < K, 0 ≤ w j
  hYmeanRe : ∀ k ≤ K, ∀ (b : LoopArg L 2) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L (xiPP E) u (u k) τ Y b j ω).re | ℱ j] =ᵐ[μ] 0
  hYmeanIm : ∀ k ≤ K, ∀ (b : LoopArg L 2) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L (xiPP E) u (u k) τ Y b j ω).im | ℱ j] =ᵐ[μ] 0
  hYintRe : ∀ k ≤ K, ∀ (b : LoopArg L 2) (j : ℕ), j < k →
      Integrable (fun ω => (stoppedEdge L (xiPP E) u (u k) τ Y b j ω).re ^ 4) μ
  hYintIm : ∀ k ≤ K, ∀ (b : LoopArg L 2) (j : ℕ), j < k →
      Integrable (fun ω => (stoppedEdge L (xiPP E) u (u k) τ Y b j ω).im ^ 4) μ
  hYcondRe : ∀ k ≤ K, ∀ (b : LoopArg L 2) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L (xiPP E) u (u k) τ Y b j ω).re ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => v j
  hYcondIm : ∀ k ≤ K, ∀ (b : LoopArg L 2) (j : ℕ), j < k →
      μ[fun ω => (stoppedEdge L (xiPP E) u (u k) τ Y b j ω).im ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => v j
  hY4Re : ∀ k ≤ K, ∀ (b : LoopArg L 2) (j : ℕ), j < k →
      ∫ ω, (stoppedEdge L (xiPP E) u (u k) τ Y b j ω).re ^ 4 ∂μ ≤ w j
  hY4Im : ∀ k ≤ K, ∀ (b : LoopArg L 2) (j : ℕ), j < k →
      ∫ ω, (stoppedEdge L (xiPP E) u (u k) τ Y b j ω).im ^ 4 ∂μ ≤ w j
  hstepErr0 : ∀ j < K, 0 ≤ stepErr j
  hR : ∀ ω j, j < K → j < τ ω → ∀ b, ‖R j ω b‖ ≤ stepErr j

/-- For `u ∈ [0,1)`, the decay radius `ellHat(u)·L` exceeds every cyclic distance, so
`FastDecay (ellHat(u)·L) 0 X` holds for every `X` (vacuously). -/
theorem fastDecay_ellHat_mul_L {L : ℕ} [NeZero L] (hL : 3 ≤ L) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) (X : LoopArg L 2 → ℂ) :
    FastDecay L (ellHat L ((x : ℝ) : ℂ) * (L : ℝ)) 0 X := by
  intro a ⟨i, j, hij⟩
  exfalso
  have h1 : 1 ≤ ellHat L ((x : ℝ) : ℂ) := one_le_ellHat L hL hx0 hx1
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have h2 : (L : ℝ) ≤ ellHat L ((x : ℝ) : ℂ) * (L : ℝ) := by nlinarith
  have h3 := zdist_le_half (L := L) (a i - a j)
  linarith

/-- **Discharge of the kernel fields at `σ = (+,+)`**: `norm_Uker_pp_apply_le` is
`‖U_{i,k}X‖ ≤ C_U(κ)²‖X‖` on **all** inputs, so `κ := C_U(κ)²`, `εK := 0`; the class fields are
discharged with the decay-radius slot `Kd := L` (vacuous fast decay, `δ0 = δD = 0`), since the
error weight `εK = 0` makes the values of `δ0`, `δD` irrelevant. -/
theorem PPAssemblyHyp.toPW {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {ℱ : Filtration ℕ mΩ'} {L : ℕ} [NeZero L] {κ E : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) {u : ℕ → ℝ} {τ : Ω' → ℕ} {Δ : ℝ} {K : ℕ} {A0 : Ω' → LoopArg L 2 → ℂ}
    {A Dr Z Y R : ℕ → Ω' → LoopArg L 2 → ℂ} {dDrift : ℕ → Ω' → ℝ}
    {c : ℕ → LoopArg L 2 → ℕ → ℝ≥0} {v w stepErr : ℕ → ℝ}
    (h : PPAssemblyHyp μ ℱ L E u τ Δ K A0 A Dr Z Y R dDrift c v w stepErr) :
    GridAssemblyHypPW μ ℱ L (xiPP E) u τ Δ K (L : ℝ) false A0 A Dr Z Y R
      (fun _ _ => CU κ ^ 2) (fun _ _ => 0) 0 dDrift (fun _ _ => 0) c v w stepErr where
  hL3 := h.hL3
  hξ := norm_xiPP_le_one (by linarith)
  hu0 := h.hu0
  hu1 := h.hu1
  hΔ0 := h.hΔ0
  hexp := h.hexp
  hκ0 := fun _ _ _ _ => sq_nonneg _
  hε0 := fun _ _ _ _ => le_rfl
  hker := by
    intro i k hik hkK X M δ hM _ hX _ a
    have hb := norm_Uker_pp_apply_le h.hL3 hκ0 hκ1 hE (h.hu0 i (hik.trans hkK))
      (h.hmono i k hik hkK) (h.hu1 k hkK) hM hX a
    simpa using hb
  hδ0 := le_rfl
  hA0cls := fun ω _ => ⟨fastDecay_ellHat_mul_L h.hL3 (h.hu0 0 (Nat.zero_le _))
      (h.hu1 0 (Nat.zero_le _)) (A0 ω), fun hf => absurd hf (by decide)⟩
  hdDrift0 := h.hdDrift0
  hδD0 := fun _ _ _ => le_rfl
  hdrift := h.hdrift
  hDcls := fun ω j hj _ => ⟨fastDecay_ellHat_mul_L h.hL3 (h.hu0 (j + 1) (by omega))
      (h.hu1 (j + 1) (by omega)) (Dr j ω), fun hf => absurd hf (by decide)⟩
  hc_pos := h.hc_pos
  hYmeas := h.hYmeas
  hv0 := h.hv0
  hw0 := h.hw0
  hYmeanRe := h.hYmeanRe
  hYmeanIm := h.hYmeanIm
  hYintRe := h.hYintRe
  hYintIm := h.hYintIm
  hYcondRe := h.hYcondRe
  hYcondIm := h.hYcondIm
  hY4Re := h.hY4Re
  hY4Im := h.hY4Im
  hstepErr0 := h.hstepErr0
  hR := h.hR

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] {μ : Measure Ω'}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'}

end Instantiation

/-! ### Ingredient Y, general loop length `n`

The fields `hYcondRe/Im`, `hY4Re/Im` are proved here for a general loop length `n`, a general label
family `Φ` (`TestFun`, uniform `C₂`) and a general complex kernel `U` with row sum `≤ ρ`. -/

section YMoments

variable {d : Dims}

/-- `m_p = E‖X‖^p`, the `p`-th moment of the operator norm of one draw of `X`. -/
def xMom (d : Dims) (N p : ℕ) : ℝ := ∫ x, ‖Xmat d N x‖ ^ p ∂(P d)

theorem xMom_nonneg (d : Dims) (N p : ℕ) : 0 ≤ xMom d N p :=
  integral_nonneg fun _ => by positivity

theorem integrable_normPow_incr (d : Dims) (N k p : ℕ) :
    Integrable (fun ω : Ωg d => ‖Xmat d N (ω (k + 1))‖ ^ (2 * p)) (Pg d) := by
  have hg : Integrable (fun x : Ω d => ‖Xmat d N x‖ ^ (2 * p)) (P d) :=
    integrable_norm_Xmat_pow d N p
  have hf : AEMeasurable (fun ω : Ωg d => ω (k + 1)) (Pg d) :=
    (measurable_pi_apply (k + 1)).aemeasurable
  have hmap : (Pg d).map (fun ω : Ωg d => ω (k + 1)) = P d := map_incr d k
  have hgASM : AEStronglyMeasurable (fun x : Ω d => ‖Xmat d N x‖ ^ (2 * p))
      ((Pg d).map fun ω => ω (k + 1)) := by
    rw [hmap]; exact hg.aestronglyMeasurable
  exact (integrable_map_measure hgASM hf).1 (by rw [hmap]; exact hg)

theorem integral_normPow_incr (d : Dims) (N k p : ℕ) :
    ∫ ω, ‖Xmat d N (ω (k + 1))‖ ^ p ∂(Pg d) = xMom d N p := by
  have hf : AEMeasurable (fun ω : Ωg d => ω (k + 1)) (Pg d) :=
    (measurable_pi_apply (k + 1)).aemeasurable
  have hc : Continuous (fun x : Ω d => ‖Xmat d N x‖ ^ p) := ((continuous_Xmat d N).norm).pow p
  have h := integral_map hf (hc.aestronglyMeasurable (μ := (Pg d).map fun ω => ω (k + 1)))
  rw [map_incr d k] at h
  exact h.symm

/-- **Conditioning on `F_j` averages a function of the next draw** (the freezing lemma with
a constant frozen variable). -/
theorem condExp_fun_incr (d : Dims) (N j : ℕ) {f : Ω d → ℝ} (hf : Measurable f)
    (hint : Integrable (fun ω : Ωg d => f (ω (j + 1))) (Pg d)) :
    (Pg d)[fun ω => f (ω (j + 1)) | filt d j] =ᵐ[Pg d] fun _ => ∫ x, f x ∂(P d) :=
  condExp_freeze (d := d) j (Y := fun _ : Ωg d => (0 : ℝ)) measurable_const
    (F := fun _ x => f x) (hf.comp measurable_snd) hint

/-- `stepYC` is `filt d (j+1)`-measurable. -/
theorem measurable_stepYC_filt (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) :
    Measurable[filt d (j + 1)] (fun ω => stepYC d s t K N j n Φ U b ω) := by
  have h1 : Measurable[filt d (j + 1)]
      (fun ω => ∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N (j + 1) ω)) :=
    Finset.measurable_sum _ fun a _ =>
      ((hΦ a).contDiff.continuous.measurable.comp (H_measurable_filt d s t K N (j + 1))).const_mul _
  have h2 : Measurable[filt d (j + 1)] ((Pg d)[fun ω' => ∑ a : LoopArg (d.L N) n,
      U b a * Φ a (H d s t K N (j + 1) ω') | filt d j]) :=
    (stronglyMeasurable_condExp.measurable).mono ((filt d).mono (Nat.le_succ j)) le_rfl
  have h3 := measurable_stepZC_filt s t K N j n hΦ U b
  exact (h1.sub h2).sub h3

/-- The pathwise bound on `Y^C` with the conditional term evaluated:
`‖Y^C_b‖ ≤ (Σ_a‖U_{b,a}‖)(C₂/2)Δ (‖X_{j+1}‖² + m₂)` a.e. -/
theorem stepYC_norm_le_incr_ae (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) :
    ∀ᵐ ω ∂(Pg d), ‖stepYC d s t K N j n Φ U b ω‖
      ≤ (∑ a : LoopArg (d.L N) n, ‖U b a‖) * ((C₂ / 2) * step s t K N)
          * (‖Xmat d N (ω (j + 1))‖ ^ 2 + xMom d N 2) := by
  have h := stepYC_norm_le_ae d s t K N j n hΦ hC₂ hΔ U b
    (integrable_stepZC_re_of_testFun d s t K N j n hΦ hC₂ hΔ U b)
    (integrable_stepZC_im_of_testFun d s t K N j n hΦ hC₂ hΔ U b)
  have hc := condExp_fun_incr d N j
    (f := fun x => (∑ a : LoopArg (d.L N) n, ‖U b a‖) * ((C₂ / 2) * step s t K N)
      * ‖Xmat d N x‖ ^ 2)
    (measurable_const.mul ((continuous_Xmat d N).norm.pow 2).measurable)
    ((integrable_normSq_incr d N j).const_mul _)
  filter_upwards [h, hc] with ω h1 h2
  rw [h2, integral_const_mul] at h1
  have : ∫ x, ‖Xmat d N x‖ ^ 2 ∂(P d) = xMom d N 2 := rfl
  rw [this] at h1
  linarith

private lemma sq_add_le_two' (x m : ℝ) : (x + m) ^ 2 ≤ 2 * x ^ 2 + 2 * m ^ 2 := by
  nlinarith [sq_nonneg (x - m)]

private lemma pow4_add_le_eight' (x m : ℝ) : (x + m) ^ 4 ≤ 8 * (x ^ 4 + m ^ 4) := by
  nlinarith [sq_nonneg (x - m), sq_nonneg (x + m), sq_nonneg (x ^ 2 - m ^ 2),
    mul_nonneg (sq_nonneg (x - m)) (sq_nonneg (x + m)), sq_nonneg (x * m),
    mul_nonneg (sq_nonneg (x - m)) (sq_nonneg (x - m))]

/-- **Ingredient Y, general `n`**. Let `F =ᵐ S.indicator (Y^C_b)` with `S ∈ F_j`,
`Y^C = stepYC … Φ U b`, `Σ_a ‖U_{b,a}‖ ≤ ρ`, and `T : ℂ →L[ℝ] ℝ` with `‖T z‖ ≤ ‖z‖`
(`T = Re` or `Im`). With `c := ρ (C₂/2) Δ`:
`E[T F | F_j] = 0`, `(T F)⁴` integrable, `E[(T F)² | F_j] ≤ c² (2m₄ + 2m₂²)` and
`E (T F)⁴ ≤ c⁴ · 8(m₈ + m₂⁴)`. -/
theorem Ymoments_of_ae_eq (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) {ρ : ℝ}
    (hρ : ∑ a : LoopArg (d.L N) n, ‖U b a‖ ≤ ρ) {S : Set (Ωg d)} (hS : MeasurableSet[filt d j] S)
    {F : Ωg d → ℂ} (hF : F =ᵐ[Pg d] S.indicator (fun ω => stepYC d s t K N j n Φ U b ω))
    (T : ℂ →L[ℝ] ℝ) (hT : ∀ z, ‖T z‖ ≤ ‖z‖) :
    (Pg d)[fun ω => T (F ω) | filt d j] =ᵐ[Pg d] 0
    ∧ Integrable (fun ω => T (F ω) ^ 4) (Pg d)
    ∧ (Pg d)[fun ω => T (F ω) ^ 2 | filt d j] ≤ᵐ[Pg d]
        (fun _ => (ρ * ((C₂ / 2) * step s t K N)) ^ 2 * (2 * xMom d N 4 + 2 * xMom d N 2 ^ 2))
    ∧ ∫ ω, T (F ω) ^ 4 ∂(Pg d)
        ≤ (ρ * ((C₂ / 2) * step s t K N)) ^ 4 * (8 * (xMom d N 8 + xMom d N 2 ^ 4)) := by
  classical
  set Y : Ωg d → ℂ := fun ω => stepYC d s t K N j n Φ U b ω with hYdef
  set c : ℝ := ρ * ((C₂ / 2) * step s t K N) with hcdef
  set m2 : ℝ := xMom d N 2 with hm2
  obtain ⟨a0⟩ := (inferInstance : Nonempty (LoopArg (d.L N) n))
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ a0 0)
  have hρ0 : 0 ≤ ρ := (Finset.sum_nonneg fun a _ => norm_nonneg (U b a)).trans hρ
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hm20 : 0 ≤ m2 := xMom_nonneg d N 2
  have hSm : MeasurableSet S := (filt d).le j S hS
  have hYm : Measurable Y :=
    (measurable_stepYC_filt s t K N j n hΦ U b).mono ((filt d).le (j + 1)) le_rfl
  have hGm : Measurable (S.indicator Y) := hYm.indicator hSm
  -- the dominating function `B ω = c (‖X_{j+1}‖² + m₂)`
  set B : Ωg d → ℝ := fun ω => c * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m2) with hBdef
  have hB0 : ∀ ω, 0 ≤ B ω := fun ω => by rw [hBdef]; positivity
  have hYB : ∀ᵐ ω ∂(Pg d), ‖Y ω‖ ≤ B ω := by
    filter_upwards [stepYC_norm_le_incr_ae s t K N j n hΦ hC₂ hΔ U b] with ω hω
    refine hω.trans ?_
    have hx : 0 ≤ ‖Xmat d N (ω (j + 1))‖ ^ 2 + m2 := by positivity
    have hcoef : (∑ a : LoopArg (d.L N) n, ‖U b a‖) * ((C₂ / 2) * step s t K N) ≤ c := by
      rw [hcdef]; exact mul_le_mul_of_nonneg_right hρ (by positivity)
    exact mul_le_mul_of_nonneg_right hcoef hx
  have hFB : ∀ᵐ ω ∂(Pg d), ‖F ω‖ ≤ B ω := by
    filter_upwards [hF, hYB] with ω h1 h2
    rw [h1]
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]; exact h2
    · rw [Set.indicator_of_notMem hω, norm_zero]; exact hB0 ω
  have hTFB : ∀ᵐ ω ∂(Pg d), |T (F ω)| ≤ B ω := by
    filter_upwards [hFB] with ω h
    exact (Real.norm_eq_abs _ ▸ hT (F ω)).trans h
  have hFae : AEStronglyMeasurable F (Pg d) := hGm.aestronglyMeasurable.congr hF.symm
  have hTFae : AEStronglyMeasurable (fun ω => T (F ω)) (Pg d) :=
    T.continuous.comp_aestronglyMeasurable hFae
  -- integrability of the dominating functions
  have hX4 : Integrable (fun ω : Ωg d => ‖Xmat d N (ω (j + 1))‖ ^ 4) (Pg d) := by
    simpa using integrable_normPow_incr d N j 2
  have hX8 : Integrable (fun ω : Ωg d => ‖Xmat d N (ω (j + 1))‖ ^ 8) (Pg d) := by
    simpa using integrable_normPow_incr d N j 4
  have hX2 : Integrable (fun ω : Ωg d => ‖Xmat d N (ω (j + 1))‖ ^ 2) (Pg d) :=
    integrable_normSq_incr d N j
  have hBint : Integrable B (Pg d) := (hX2.add (integrable_const m2)).const_mul c
  set g2 : Ωg d → ℝ := fun ω => c ^ 2 * (2 * ‖Xmat d N (ω (j + 1))‖ ^ 4 + 2 * m2 ^ 2) with hg2
  set g4 : Ωg d → ℝ := fun ω => c ^ 4 * (8 * (‖Xmat d N (ω (j + 1))‖ ^ 8 + m2 ^ 4)) with hg4
  have hg2int : Integrable g2 (Pg d) :=
    ((hX4.const_mul 2).add (integrable_const _)).const_mul _
  have hg4int : Integrable g4 (Pg d) :=
    ((hX8.add (integrable_const _)).const_mul 8).const_mul _
  have hsq_le : ∀ᵐ ω ∂(Pg d), T (F ω) ^ 2 ≤ g2 ω := by
    filter_upwards [hTFB] with ω h
    have h1 : T (F ω) ^ 2 ≤ B ω ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have h2 : B ω ^ 2 ≤ g2 ω := by
      rw [hBdef, hg2]
      have := sq_add_le_two' (‖Xmat d N (ω (j + 1))‖ ^ 2) m2
      have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
      calc (c * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m2)) ^ 2
          = c ^ 2 * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m2) ^ 2 := by ring
        _ ≤ c ^ 2 * (2 * (‖Xmat d N (ω (j + 1))‖ ^ 2) ^ 2 + 2 * m2 ^ 2) :=
            mul_le_mul_of_nonneg_left this hc2
        _ = c ^ 2 * (2 * ‖Xmat d N (ω (j + 1))‖ ^ 4 + 2 * m2 ^ 2) := by ring
    exact h1.trans h2
  have hpow4_le : ∀ᵐ ω ∂(Pg d), T (F ω) ^ 4 ≤ g4 ω := by
    filter_upwards [hTFB] with ω h
    have h1 : T (F ω) ^ 4 ≤ B ω ^ 4 := by
      have : T (F ω) ^ 4 = |T (F ω)| ^ 4 := by
        rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
      rw [this]; exact pow_le_pow_left₀ (abs_nonneg _) h 4
    have h2 : B ω ^ 4 ≤ g4 ω := by
      rw [hBdef, hg4]
      have := pow4_add_le_eight' (‖Xmat d N (ω (j + 1))‖ ^ 2) m2
      have hc4 : 0 ≤ c ^ 4 := by positivity
      calc (c * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m2)) ^ 4
          = c ^ 4 * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m2) ^ 4 := by ring
        _ ≤ c ^ 4 * (8 * ((‖Xmat d N (ω (j + 1))‖ ^ 2) ^ 4 + m2 ^ 4)) :=
            mul_le_mul_of_nonneg_left this hc4
        _ = c ^ 4 * (8 * (‖Xmat d N (ω (j + 1))‖ ^ 8 + m2 ^ 4)) := by ring
    exact h1.trans h2
  have hTF2int : Integrable (fun ω => T (F ω) ^ 2) (Pg d) :=
    hg2int.mono' (hTFae.pow 2) (by
      filter_upwards [hsq_le] with ω h
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h)
  have hTF4int : Integrable (fun ω => T (F ω) ^ 4) (Pg d) :=
    hg4int.mono' (hTFae.pow 4) (by
      filter_upwards [hpow4_le] with ω h
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact h)
  -- mean zero
  have hYint : Integrable Y (Pg d) :=
    hBint.mono' hYm.aestronglyMeasurable (by filter_upwards [hYB] with ω h using h)
  have hYmean : (Pg d)[Y | filt d j] =ᵐ[Pg d] fun _ => (0 : ℂ) :=
    (stepDecompC d s t K N j n hΦ hC₂ hΔ U b
      (integrable_stepZC_re_of_testFun d s t K N j n hΦ hC₂ hΔ U b)
      (integrable_stepZC_im_of_testFun d s t K N j n hΦ hC₂ hΔ U b)).2.2.2
  have hTY : (Pg d)[fun ω => T (Y ω) | filt d j] =ᵐ[Pg d] 0 := by
    have hcomm := T.comp_condExp_comm (μ := Pg d) (m := filt d j) hYint
    refine hcomm.symm.trans ?_
    filter_upwards [hYmean] with ω hω
    simp [Function.comp_apply, hω]
  have hTFeq : (fun ω => T (F ω)) =ᵐ[Pg d] S.indicator (fun ω => T (Y ω)) := by
    filter_upwards [hF] with ω hω
    rw [hω]
    by_cases hmem : ω ∈ S
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, map_zero]
  have hmean : (Pg d)[fun ω => T (F ω) | filt d j] =ᵐ[Pg d] 0 := by
    refine (condExp_congr_ae hTFeq).trans ?_
    refine (condExp_indicator (T.integrable_comp hYint) hS).trans ?_
    filter_upwards [hTY] with ω hω
    by_cases hmem : ω ∈ S
    · rw [Set.indicator_of_mem hmem]; exact hω
    · rw [Set.indicator_of_notMem hmem]; rfl
  refine ⟨hmean, hTF4int, ?_, ?_⟩
  · -- conditional second moment
    have hmono := condExp_mono (m := filt d j) hTF2int hg2int hsq_le
    have hg2cond := condExp_fun_incr d N j
      (f := fun x => c ^ 2 * (2 * ‖Xmat d N x‖ ^ 4 + 2 * m2 ^ 2))
      (measurable_const.mul ((measurable_const.mul
        ((continuous_Xmat d N).norm.pow 4).measurable).add measurable_const)) hg2int
    filter_upwards [hmono, hg2cond] with ω h1 h2
    refine h1.trans (le_of_eq ?_)
    rw [show g2 = fun ω => c ^ 2 * (2 * ‖Xmat d N (ω (j + 1))‖ ^ 4 + 2 * m2 ^ 2) from rfl] at *
    rw [h2, integral_const_mul, integral_add ((integrable_norm_Xmat_pow d N 2).const_mul 2 |>.congr
      (Filter.Eventually.of_forall fun x => by simp)) (integrable_const _), integral_const_mul,
      integral_const]
    simp [xMom, hm2]
  · -- fourth moment
    calc ∫ ω, T (F ω) ^ 4 ∂(Pg d) ≤ ∫ ω, g4 ω ∂(Pg d) := integral_mono_ae hTF4int hg4int hpow4_le
      _ = c ^ 4 * (8 * (xMom d N 8 + m2 ^ 4)) := by
          rw [hg4, integral_const_mul, integral_const_mul, integral_add hX8 (integrable_const _),
            integral_normPow_incr d N j 8, integral_const]
          simp

end YMoments

/-! ### The deterministic `(+,+)` drift bound on the good set -/

section DriftPP

variable (d : Dims)

theorem ofFn_sigmaPP : List.ofFn sigmaPP = [true, true] := by
  simp [sigmaPP, List.ofFn_succ]

theorem ofFn_sigPP : List.ofFn sigPP = [true, true] := by
  simp [sigPP, List.ofFn_succ]

theorem ofFn_two {L : ℕ} (a : LoopArg L 2) : List.ofFn a = [a 0, a 1] := by
  simp [List.ofFn_succ]

theorem trace_Eblk (L W : ℕ) [NeZero L] [NeZero W] (x : ZMod L) :
    Matrix.trace (Eblk L W x) = 1 := by
  unfold Eblk
  rw [Matrix.trace_diagonal, Fintype.sum_prod_type]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hin : ∀ x1 : ZMod L, (∑ _x2 : Fin W, (if x1 = x then (W : ℂ)⁻¹ else 0))
      = if x1 = x then 1 else 0 := by
    intro x1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    split_ifs
    · field_simp
    · simp
  simp only [hin, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The one-loop `L − K` is the trace of `(G_s − m_s)E_x` (`⟨E_x⟩ = 1`, `K_{(s),x} = m_s`). -/
theorem gloop_one_sub_Kval (E : ℝ) (N : ℕ) (v : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (s : Bool) (x : ZMod (d.L N)) :
    gloop (d.L N) (d.W N) M (zt E v) ⟨[s], [x]⟩ - (band d).Kval E N v ⟨[s], [x]⟩
      = Matrix.trace ((Gsig M (zt E v) s - mSigma E s • (1 : Matrix (d.Idx N) (d.Idx N) ℂ))
          * Eblk (d.L N) (d.W N) x) := by
  have hK : (band d).Kval E N v ⟨[s], [x]⟩ = mSigma E s := Kgen_one _ _ _ s x
  rw [hK, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, Matrix.one_mul,
    trace_Eblk, smul_eq_mul, mul_one]
  simp [gloop, gloopProd]

/-- **The drift bound of (5.79)+(5.80) at `n = 2`, `σ = (+,+)`**, on the good set at the
grid time `v` (decay tail exponent `D₀`): with `J = JPP(v, M)` (so `‖(L−K)_{(+,+)}‖ ≤ J A_v^{-2}`),
`φ₁ = N^ε` from `xiOnePP`, `φ₃ = N^ε(ℓ_v/ℓ_s)²` from `eq273Set` at loop length `3`, and the decay
sets `decaySet`/`lkDecaySet` at radius `ℓ_v W^ε` (the components of `goodSetPP`). -/
def dBoundPP (E : ℝ) (N : ℕ) (v ε D₀ ℓs J : ℝ) : ℝ :=
  6 * Real.exp 1 * (d.W N : ℝ) ^ ε * J ^ 2 * ((band d).scale E N v)⁻¹ ^ 3 * (etaT E v)⁻¹
  + 6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-D₀) * J
      * ((band d).scale E N v)⁻¹ ^ 2
  + 12 * Real.exp 1 * (d.W N : ℝ) ^ ε * (N : ℝ) ^ ε * ((N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 2)
      * ((band d).scale E N v)⁻¹ ^ 2 * (etaT E v)⁻¹
  + 12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε * (d.W N : ℝ) ^ (-D₀)
      * ((band d).scale E N v)⁻¹

theorem JPP_nonneg (E : ℝ) (N : ℕ) (v : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    0 ≤ JPP d E N v M := by
  unfold JPP
  obtain ⟨a0⟩ := (inferInstance : Nonempty (LoopArg (d.L N) 2))
  exact mul_nonneg (sq_nonneg _) ((norm_nonneg _).trans
    (Finset.le_sup' (fun a : LoopArg (d.L N) 2 => lkErrMat d E N v M (LoopData.idx (sigPP, a)))
      (Finset.mem_univ a0)))

/-- Each `(+,+)` entry is bounded by `J A_v^{-2}`. -/
theorem norm_lk_pp_le_JPP {E : ℝ} (hE : |E| < 2) {N : ℕ} {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (a : LoopArg (d.L N) 2) :
    ‖gloop (d.L N) (d.W N) M (zt E v) ⟨[true, true], List.ofFn a⟩
        - (band d).Kval E N v ⟨[true, true], List.ofFn a⟩‖
      ≤ JPP d E N v M * ((band d).scale E N v)⁻¹ ^ 2 := by
  have hA : 0 < (band d).scale E N v := (band d).scale_pos' hE N hv0 hv1
  have hle := Finset.le_sup' (fun a : LoopArg (d.L N) 2 => lkErrMat d E N v M
    (LoopData.idx (sigPP, a))) (Finset.mem_univ a)
  have hidx : (LoopData.idx (sigPP, a) : LoopIdx (ZMod (d.L N)))
      = ⟨[true, true], List.ofFn a⟩ := by
    show (⟨List.ofFn sigPP, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))) = _
    rw [ofFn_sigPP]
  simp only [lkErrMat, hidx] at hle
  unfold JPP
  rw [show (band d).scale E N v ^ 2 * Finset.univ.sup' Finset.univ_nonempty
      (fun a : LoopArg (d.L N) 2 => lkErrMat d E N v M (LoopData.idx (sigPP, a)))
      * ((band d).scale E N v)⁻¹ ^ 2
      = Finset.univ.sup' Finset.univ_nonempty
      (fun a : LoopArg (d.L N) 2 => lkErrMat d E N v M (LoopData.idx (sigPP, a))) by
    field_simp]
  exact hle

theorem norm_drift_pp_le {E : ℝ} (hE : |E| < 2) {N : ℕ} {v ε D₀ ℓs : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v < 1) (hε : 0 ≤ ε) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M ∈ goodSetPP d E N v ε ℓs D₀) (a : LoopArg (d.L N) 2) :
    ‖eGterm (d.L N) (d.W N) (mSigma E) M (zt E v) ⟨List.ofFn sigmaPP, List.ofFn a⟩
      + primBil (d.L N) (d.W N) (fun I => gloop (d.L N) (d.W N) M (zt E v) I - (band d).Kval E N v I)
          (fun I => gloop (d.L N) (d.W N) M (zt E v) I - (band d).Kval E N v I)
          ⟨List.ofFn sigmaPP, List.ofFn a⟩‖
      ≤ dBoundPP d E N v ε D₀ ℓs (JPP d E N v M) := by
  obtain ⟨⟨⟨⟨hG1, hG2⟩, _hG3⟩, hG4⟩, hG5⟩ := hM
  have hL3 : 3 ≤ d.L N := d.three_le_L N
  have hA : 0 < (band d).scale E N v := (band d).scale_pos' hE N hv0 hv1
  have hη : 0 < etaT E v := etaT_pos_of_lt_one' hE hv1
  have hℓ : 1 ≤ (band d).ell N v := one_le_ellHat (d.L N) hL3 hv0 hv1
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hWε : 1 ≤ (d.W N : ℝ) ^ ε := Real.one_le_rpow hW1 hε
  have hWℓ : (d.W N : ℝ) * (band d).ell N v = (band d).scale E N v / etaT E v := by
    show _ = (d.W N : ℝ) * (band d).ell N v * etaT E v / etaT E v
    field_simp
  have hδ0 : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D₀) := Real.rpow_nonneg (by linarith) _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [ofFn_sigmaPP, ofFn_two]
  -- the `primBil` part, (5.79)
  have hAdecay : FastDecay (d.L N) ((band d).ell N v * (d.W N : ℝ) ^ ε) ((d.W N : ℝ) ^ (-D₀))
      (fun v' : LoopArg (d.L N) 2 => (fun I => gloop (d.L N) (d.W N) M (zt E v) I - (band d).Kval E N v I)
        ⟨[true, true], List.ofFn v'⟩) := by
    have h2 : Decay.LoopDecay (d.L N) 2 ((band d).ell N v * (d.W N : ℝ) ^ ε)
        ((d.W N : ℝ) ^ (-D₀))
        (fun I => gloop (d.L N) (d.W N) M (zt E v) I - (band d).Kval E N v I) :=
      fun J hJ hlen => hG5 J hJ (hlen.trans (by norm_num))
    exact Decay.LoopDecay.fastDecay (d.L N) h2 [true, true] rfl
  have hAbound : ∀ v' : LoopArg (d.L N) 2,
      ‖(fun I => gloop (d.L N) (d.W N) M (zt E v) I - (band d).Kval E N v I) ⟨[true, true], List.ofFn v'⟩‖
        ≤ JPP d E N v M * ((band d).scale E N v)⁻¹ ^ 2 :=
    fun v' => norm_lk_pp_le_JPP d hE hv0 hv1 M v'
  have hPB := norm_primBil_pp_le hL3 (d.W N)
    (fun I => gloop (d.L N) (d.W N) M (zt E v) I - (band d).Kval E N v I) (a 0) (a 1) hWε (by linarith) hδ0
    (JPP_nonneg d E N v M) hA hη hWℓ hAdecay hAbound
  -- the `eGterm` part, (5.80)
  have hXi1 : ∀ (s : Bool) (x : ZMod (d.L N)),
      ‖Matrix.trace ((Gsig M (zt E v) s - mSigma E s • (1 : Matrix (d.Idx N) (d.Idx N) ℂ))
        * Eblk (d.L N) (d.W N) x)‖ ≤ (N : ℝ) ^ ε * ((band d).scale E N v)⁻¹ := by
    intro s x
    have h0 := hG1 (fun _ => s, fun _ => x)
    have key : ‖Matrix.trace ((Gsig M (zt E v) s
        - mSigma E s • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) x)‖
        = lkErrMat d E N v M (LoopData.idx ((fun _ => s, fun _ => x) : LoopData (d.L N) 1)) := by
      unfold lkErrMat
      have hidx : (LoopData.idx ((fun _ => s, fun _ => x) : LoopData (d.L N) 1)
          : LoopIdx (ZMod (d.L N))) = ⟨[s], [x]⟩ := by
        simp [LoopData.idx]
      rw [hidx]
      exact congrArg norm (gloop_one_sub_Kval d E N v M s x).symm
    have h : (band d).scale E N v * ‖Matrix.trace ((Gsig M (zt E v) s
        - mSigma E s • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) x)‖
        ≤ (N : ℝ) ^ ε := by rw [key]; exact h0
    calc ‖Matrix.trace ((Gsig M (zt E v) s - mSigma E s • (1 : Matrix (d.Idx N) (d.Idx N) ℂ))
          * Eblk (d.L N) (d.W N) x)‖
        = ((band d).scale E N v)⁻¹ * ((band d).scale E N v * ‖Matrix.trace ((Gsig M (zt E v) s
            - mSigma E s • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) x)‖) := by
          field_simp
      _ ≤ ((band d).scale E N v)⁻¹ * (N : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 hA.le)
      _ = (N : ℝ) ^ ε * ((band d).scale E N v)⁻¹ := by ring
  have hL3bound : ∀ v' : LoopArg (d.L N) 3,
      ‖gloop (d.L N) (d.W N) M (zt E v) ⟨[true, true, true], List.ofFn v'⟩‖
        ≤ (N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 2 * ((band d).scale E N v)⁻¹ ^ 2 := by
    intro v'
    have h := hG2 (fun _ => true, v')
    have hidx : (LoopData.idx ((fun _ => true, v') : LoopData (d.L N) 3)
        : LoopIdx (ZMod (d.L N))) = ⟨[true, true, true], List.ofFn v'⟩ := by
      simp [LoopData.idx, List.ofFn_succ]
    rw [hidx] at h
    simpa using h
  have hL3decay : FastDecay (d.L N) ((band d).ell N v * (d.W N : ℝ) ^ ε) ((d.W N : ℝ) ^ (-D₀))
      (fun v' : LoopArg (d.L N) 3 => gloop (d.L N) (d.W N) M (zt E v)
        ⟨[true, true, true], List.ofFn v'⟩) := by
    have h3 : Decay.LoopDecay (d.L N) 3 ((band d).ell N v * (d.W N : ℝ) ^ ε)
        ((d.W N : ℝ) ^ (-D₀)) (fun I => gloop (d.L N) (d.W N) M (zt E v) I) :=
      fun J hJ hlen => hG4 J hJ (hlen.trans (by norm_num))
    exact Decay.LoopDecay.fastDecay (d.L N) h3 [true, true, true] rfl
  have hEG := norm_eGterm_pp_le hL3 (mSigma E) M (zt E v) (a 0) (a 1) hWε (by linarith) hδ0 hN0
    (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 2) hA hη hWℓ hXi1
    hL3bound hL3decay
  refine (norm_add_le _ _).trans ?_
  unfold dBoundPP
  linarith [hPB, hEG]

end DriftPP

/-! ### The real `(+,+)` grid objects and the stopped expansion (`hexp`) -/

section RealPP

variable (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N : ℕ)

/-- `A_j(a) = L_{u_j,(+,+),a}(H_j) − K_{u_j,(+,+),a}` (`LvalN − KvN` at `σ_pp`). -/
def App (j : ℕ) (ω : Ωg d) : LoopArg (d.L N) 2 → ℂ := fun a =>
  LvalN (band d) E N (time s t Kf N j) (H d s t Kf N j ω) sigmaPP a
    - KvN (band d) E N (time s t Kf N j) sigmaPP a

/-- `D_j = eGterm + primBil(A_j, A_j)`, (5.15) at `n = 2` (the `Σ_{l_K ≥ 3}` is empty). -/
def Dpp (j : ℕ) (ω : Ωg d) : LoopArg (d.L N) 2 → ℂ := fun a =>
  eGterm ((band d).L N) ((band d).W N) (mSigma E) (H d s t Kf N j ω) (zt E (time s t Kf N j))
      ⟨List.ofFn sigmaPP, List.ofFn a⟩
    + primBil ((band d).L N) ((band d).W N)
        (gloop ((band d).L N) ((band d).W N) (H d s t Kf N j ω) (zt E (time s t Kf N j))
          - (band d).Kval E N (time s t Kf N j))
        (gloop ((band d).L N) ((band d).W N) (H d s t Kf N j ω) (zt E (time s t Kf N j))
          - (band d).Kval E N (time s t Kf N j))
        ⟨List.ofFn sigmaPP, List.ofFn a⟩

/-- The `(+,+)` label family at the grid times (`ΦgridG`). -/
abbrev Φpp : ℕ → LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  gridΦG d E s t Kf N sigmaPP

/-- The exactly linear grid increment. -/
abbrev Zpp : ℕ → Ωg d → LoopArg (d.L N) 2 → ℂ := gridZC d s t Kf N 2 (Φpp d E s t Kf N)

/-- The second-order grid increment `Y_i = stepYC(Φ_{u_i}, δ)` (cut to `1 ≤ i ≤ K`). -/
def Ypp (i : ℕ) (ω : Ωg d) : LoopArg (d.L N) 2 → ℂ := fun a =>
  if 1 ≤ i ∧ i ≤ Kf N then
    stepYC d s t Kf N (i - 1) 2 (Φpp d E s t Kf N i) (gridDeltaC (d.L N) 2) a ω else 0

/-- The raw one-step remainder, named by subtraction. -/
def Rraw (j : ℕ) (ω : Ωg d) (a : LoopArg (d.L N) 2) : ℂ :=
  (Pg d)[fun ω' => App d E s t Kf N (j + 1) ω' a | filt d j] ω
    - Uker (d.L N) (xiPP E) (time s t Kf N j : ℂ) (time s t Kf N (j + 1) : ℂ)
        (App d E s t Kf N j ω) a
    - (step s t Kf N : ℂ) * Dpp d E s t Kf N j ω a

/-- The deterministic step error (`stepErrN` at `n = 2`, made nonnegative). -/
def errPP (Bk : ℝ) (j : ℕ) : ℝ :=
  max 0 (stepErrN (band d) E N 2 (time s t Kf N j) (time s t Kf N (j + 1)) (step s t Kf N) Bk)

/-- The remainder, truncated to `0` off the (full-measure) event where it obeys `errPP`. -/
def Rpp (Bk : ℝ) (j : ℕ) (ω : Ωg d) : LoopArg (d.L N) 2 → ℂ :=
  if ∀ a, ‖Rraw d E s t Kf N j ω a‖ ≤ errPP d E s t Kf N Bk j then Rraw d E s t Kf N j ω
  else 0

/-- The stopped process `A^τ_k = U_{k∧τ, k} A_{k∧τ}`. -/
def Ast (τ : Ωg d → ℕ) (k : ℕ) (ω : Ωg d) : LoopArg (d.L N) 2 → ℂ :=
  Uker (d.L N) (xiPP E) (time s t Kf N (min k (τ ω)) : ℂ) (time s t Kf N k : ℂ)
    (App d E s t Kf N (min k (τ ω)) ω)

theorem Uker_sub' {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (a b : ℂ) (A B : LoopArg L n → ℂ) :
    Uker L ξ a b (A - B) = Uker L ξ a b A - Uker L ξ a b B := by
  funext c
  simp only [Uker_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem norm_ofReal_mul_lt_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(x : ℂ) * z‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0]
  nlinarith [norm_nonneg z]

/-- **Duhamel telescoping along the grid** (pure algebra, semigroup `Uker_comp`). -/
theorem telescope_Uker {L : ℕ} [NeZero L] (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ}
    (hξ : ∀ p, ‖ξ p‖ ≤ 1) (u : ℕ → ℝ) {K : ℕ} (hu0 : ∀ i ≤ K, 0 ≤ u i) (hu1 : ∀ i ≤ K, u i < 1)
    (f : ℕ → LoopArg L n → ℂ) {k : ℕ} (hkK : k ≤ K) :
    ∀ m ≤ k, ∑ j ∈ range m, Uker L ξ (u (j + 1) : ℂ) (u k : ℂ)
        (f (j + 1) - Uker L ξ (u j : ℂ) (u (j + 1) : ℂ) (f j))
      = Uker L ξ (u m : ℂ) (u k : ℂ) (f m) - Uker L ξ (u 0 : ℂ) (u k : ℂ) (f 0) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [Finset.sum_range_succ, ih (by omega), Uker_sub']
    have hcomp : Uker L ξ (u (m + 1) : ℂ) (u k : ℂ) (Uker L ξ (u m : ℂ) (u (m + 1) : ℂ) (f m))
        = Uker L ξ (u m : ℂ) (u k : ℂ) (f m) :=
      Uker_comp L hL (fun p => norm_ofReal_mul_lt_one (hu0 _ (by omega)) (hu1 _ (by omega)) (hξ p))
        (fun p => norm_ofReal_mul_lt_one (hu0 _ hkK) (hu1 _ hkK) (hξ p)) (f m)
    rw [hcomp]
    abel

variable {d E s t Kf N}

theorem time_nonneg_pp (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (i : ℕ) : 0 ≤ time s t Kf N i := by
  have h := step_nonneg' s t Kf N hst
  unfold time; positivity

theorem time_lt_one_pp (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : Kf N ≠ 0) {i : ℕ}
    (hi : i ≤ Kf N) : time s t Kf N i < 1 := by
  have h := time_mono_of_le (K := Kf) hst hi
  rw [time_last s t Kf N hK0] at h
  exact h.trans_lt ht1

theorem time_le_t_pp (hst : s N ≤ t N) (hK0 : Kf N ≠ 0) {i : ℕ}
    (hi : i ≤ Kf N) : time s t Kf N i ≤ t N := by
  have h := time_mono_of_le (K := Kf) hst hi
  rwa [time_last s t Kf N hK0] at h

/-- `Φ_{u,a}(H) = A(a)` on the (Hermitian) grid path. -/
theorem Φpp_H_eq (i : ℕ) (a : LoopArg (d.L N) 2) (ω : Ωg d) :
    Φpp d E s t Kf N i a (H d s t Kf N i ω) = App d E s t Kf N i ω a := by
  show loopObs (band d).toDims N (zt E (time s t Kf N i)) (LoopData.idx (sigmaPP, a))
      (H d s t Kf N i ω) - (band d).Kval E N (time s t Kf N i) (LoopData.idx (sigmaPP, a)) = _
  rw [loopObs_of_isHermitian (d := (band d).toDims) (H_isHermitian d s t Kf N i ω)]
  rfl

/-- **The pathwise one-step identity**
`A_{j+1} = U_{u_j,u_{j+1}} A_j + Δ D_j + Z_{j+1} + Y_{j+1} + R^{raw}_j`, for every `ω`. -/
theorem one_step_pp {j : ℕ} (hj : j < Kf N) (ω : Ωg d) (a : LoopArg (d.L N) 2) :
    App d E s t Kf N (j + 1) ω a
      = Uker (d.L N) (xiPP E) (time s t Kf N j : ℂ) (time s t Kf N (j + 1) : ℂ)
          (App d E s t Kf N j ω) a
        + (step s t Kf N : ℂ) * Dpp d E s t Kf N j ω a
        + Zpp d E s t Kf N (j + 1) ω a + Ypp d E s t Kf N (j + 1) ω a
        + Rraw d E s t Kf N j ω a := by
  have hZ : Zpp d E s t Kf N (j + 1) ω a
      = stepZC d s t Kf N j 2 (Φpp d E s t Kf N (j + 1)) (gridDeltaC (d.L N) 2) a ω := by
    show gridZC d s t Kf N 2 (Φpp d E s t Kf N) (j + 1) ω a = _
    rw [gridZC_succ s t Kf N 2 (Φpp d E s t Kf N) hj ω]
  have hY : Ypp d E s t Kf N (j + 1) ω a
      = stepYC d s t Kf N j 2 (Φpp d E s t Kf N (j + 1)) (gridDeltaC (d.L N) 2) a ω := by
    have hc : 1 ≤ j + 1 ∧ j + 1 ≤ Kf N := ⟨by omega, by omega⟩
    simp only [Ypp, hc, and_self, ↓reduceIte, Nat.add_sub_cancel]
  have hfun : (fun ω' => ∑ c : LoopArg (d.L N) 2, gridDeltaC (d.L N) 2 a c
      * Φpp d E s t Kf N (j + 1) c (H d s t Kf N (j + 1) ω'))
      = fun ω' => App d E s t Kf N (j + 1) ω' a := by
    funext ω'
    rw [Finset.sum_eq_single a]
    · simp [gridDeltaC, Φpp_H_eq]
    · intro c _ hc; simp [gridDeltaC, Ne.symm hc]
    · simp
  have hXi : stepZC d s t Kf N j 2 (Φpp d E s t Kf N (j + 1)) (gridDeltaC (d.L N) 2) a ω
      + stepYC d s t Kf N j 2 (Φpp d E s t Kf N (j + 1)) (gridDeltaC (d.L N) 2) a ω
      = App d E s t Kf N (j + 1) ω a
        - (Pg d)[fun ω' => App d E s t Kf N (j + 1) ω' a | filt d j] ω := by
    have h1 : stepZC d s t Kf N j 2 (Φpp d E s t Kf N (j + 1)) (gridDeltaC (d.L N) 2) a ω
        + stepYC d s t Kf N j 2 (Φpp d E s t Kf N (j + 1)) (gridDeltaC (d.L N) 2) a ω
        = stepXiC d s t Kf N j 2 (Φpp d E s t Kf N (j + 1)) (gridDeltaC (d.L N) 2) a ω := by
      unfold stepYC; ring
    rw [h1]
    unfold stepXiC
    rw [hfun, congrFun hfun ω]
  rw [hZ, hY]
  unfold Rraw
  linear_combination -hXi


theorem norm_xiLoop_le_one {E : ℝ} (hE : |E| ≤ 2) {L : ℕ} (I : LoopIdx (ZMod L)) (i : ℕ) :
    ‖xiLoop (mSigma E) I i‖ ≤ 1 := by
  unfold xiLoop
  rw [norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul]

/-- **The hierarchy remainder obeys `errPP` a.e., simultaneously for all `j < K`** (
`discrete_hierarchy_step_n` at `n = 2`, `σ = (+,+)`; the `Σ_{l_K ≥ 3}` is empty). -/
theorem ae_Rpp_eq (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1)
    (hK0 : Kf N ≠ 0) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (t N), ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval E N w J‖ ≤ Bk) :
    ∀ᵐ ω ∂(Pg d), ∀ j < Kf N, Rpp d E s t Kf N Bk j ω = Rraw d E s t Kf N j ω := by
  have hall : ∀ j : ℕ, ∀ᵐ ω ∂(Pg d), j < Kf N → Rpp d E s t Kf N Bk j ω = Rraw d E s t Kf N j ω := by
    intro j
    by_cases hj : j < Kf N
    · have hu0 : 0 ≤ time s t Kf N j := time_nonneg_pp hs0 hst.le j
      have hu1 : time s t Kf N (j + 1) < 1 := time_lt_one_pp hst.le ht1 hK0 (by omega)
      have hut : time s t Kf N (j + 1) ≤ t N := time_le_t_pp hst.le hK0 (by omega)
      have hBk' : ∀ w ∈ Set.Icc (0 : ℝ) (time s t Kf N (j + 1)), ∀ J : LoopIdx (ZMod ((band d).L N)),
          J.WF → 2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval E N w J‖ ≤ Bk :=
        fun w hw => hBk w ⟨hw.1, hw.2.trans hut⟩
      have hξ : ∀ a : LoopArg ((band d).L N) 2, ‖(time s t Kf N j : ℂ) * xiLoop (mSigma E)
          (⟨List.ofFn sigmaPP, List.ofFn a⟩ : LoopIdx (ZMod ((band d).L N))) (2 - 1)‖ < 1 :=
        fun a => norm_ofReal_mul_lt_one hu0
          (lt_of_le_of_lt (time_mono_of_le hst.le (Nat.le_succ j)) hu1)
          (norm_xiLoop_le_one hE.le _ _)
      have h := discrete_hierarchy_step_n (band d) s t Kf N j E hE hst hj hu0 hu1 (n := 2)
        le_rfl sigmaPP hBk0 hBk' hξ
      filter_upwards [h] with ω hω _
      unfold Rpp
      rw [if_pos]
      intro a
      have h1 := hω a
      simp only [show Finset.Icc 3 2 = (∅ : Finset ℕ) by decide, Finset.sum_empty,
        add_zero] at h1
      exact le_max_of_le_right h1
    · exact Filter.Eventually.of_forall fun ω hj' => absurd hj' hj
  filter_upwards [ae_all_iff.mpr hall] with ω hω j hj using hω j hj

/-- **h-exp** for the stopped `(+,+)` process: for every `k ≤ K`, a.e.,
`A^τ_k = U_{0,k}A_0 + Σ_{j<k∧τ} U_{j+1,k}(ΔD_j + Z_{j+1} + Y_{j+1} + R_j)`. -/
theorem hexp_pp (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1)
    (hK0 : Kf N ≠ 0) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (t N), ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval E N w J‖ ≤ Bk) (τ : Ωg d → ℕ) :
    ∀ k ≤ Kf N, ∀ᵐ ω ∂(Pg d), Ast d E s t Kf N τ k ω
      = Uker (d.L N) (xiPP E) (time s t Kf N 0 : ℂ) (time s t Kf N k : ℂ) (App d E s t Kf N 0 ω)
        + ∑ j ∈ range (min k (τ ω)), Uker (d.L N) (xiPP E) (time s t Kf N (j + 1) : ℂ)
            (time s t Kf N k : ℂ) ((step s t Kf N : ℂ) • Dpp d E s t Kf N j ω
              + Zpp d E s t Kf N (j + 1) ω + Ypp d E s t Kf N (j + 1) ω + Rpp d E s t Kf N Bk j ω) := by
  intro k hk
  filter_upwards [ae_Rpp_eq hE hs0 hst ht1 hK0 hBk0 hBk] with ω hω
  have hm : min k (τ ω) ≤ k := min_le_left _ _
  have hincr : ∀ j ∈ range (min k (τ ω)), (step s t Kf N : ℂ) • Dpp d E s t Kf N j ω
      + Zpp d E s t Kf N (j + 1) ω + Ypp d E s t Kf N (j + 1) ω + Rpp d E s t Kf N Bk j ω
      = App d E s t Kf N (j + 1) ω - Uker (d.L N) (xiPP E) (time s t Kf N j : ℂ)
          (time s t Kf N (j + 1) : ℂ) (App d E s t Kf N j ω) := by
    intro j hj
    have hjK : j < Kf N := by have := Finset.mem_range.mp hj; omega
    rw [hω j hjK]
    funext a
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [one_step_pp hjK ω a]
    ring
  rw [Finset.sum_congr rfl (fun j hj => by rw [hincr j hj]), telescope_Uker (d.three_le_L N) (norm_xiPP_le_one hE.le)
    (time s t Kf N) (K := Kf N) (fun i _ => time_nonneg_pp hs0 hst.le i)
    (fun i hi => time_lt_one_pp hst.le ht1 hK0 hi) (fun i => App d E s t Kf N i ω) hk (min k (τ ω)) hm]
  unfold Ast
  abel

/-! #### O2: the QV time shift `z_{u_j} → z_{u_{j+1}}` at a fixed matrix -/

/-- **Loop modulus in the spectral parameter at a fixed Hermitian matrix**: for `v ≤ w < 1` and
`0 < η ≤ min(1, η_w)`, every loop of length `≤ 6` moves by at most `LW·6·η^{-6}·(η^{-1}(w−v)η^{-1})`
(resolvent identity and `‖z_w − z_v‖ = |w − v|`). -/
theorem norm_gloop_shift_le {E : ℝ} (hE : |E| < 2) {N : ℕ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {v w η : ℝ} (hvw : v ≤ w) (hw1 : w < 1) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hηw : η ≤ etaT E w) (I : LoopIdx (ZMod (d.L N))) (hI : I.WF) (hlen : I.σ.length ≤ 6) :
    ‖gloop (d.L N) (d.W N) M (zt E w) I - gloop (d.L N) (d.W N) M (zt E v) I‖
      ≤ (d.L N : ℝ) * (d.W N : ℝ) * 6 * η⁻¹ ^ 6 * (η⁻¹ * (w - v) * η⁻¹) := by
  have hv1 : v < 1 := hvw.trans_lt hw1
  have hetaw : etaT E w ≤ etaT E v := etaT_le_of_le hE hvw
  have himw : η ≤ |(zt E w).im| := by
    rw [zt_im, abs_of_nonneg (mul_nonneg (by linarith) (mE_im_pos hE).le)]; exact hηw
  have himv : η ≤ |(zt E v).im| := by
    rw [zt_im, abs_of_nonneg (mul_nonneg (by linarith) (mE_im_pos hE).le)]
    exact hηw.trans hetaw
  have hzw : (zt E w).im ≠ 0 := fun h => by rw [h] at himw; simp at himw; linarith
  have hzv : (zt E v).im ≠ 0 := fun h => by rw [h] at himv; simp at himv; linarith
  have hGw : ‖green M (zt E w)‖ ≤ η⁻¹ := norm_green_le hM hη0 himw
  have hGv : ‖green M (zt E v)‖ ≤ η⁻¹ := norm_green_le hM hη0 himv
  have hK1 : 1 ≤ η⁻¹ := one_le_inv₀ hη0 |>.mpr hη1
  have hsub : ‖green M (zt E w) - green M (zt E v)‖ ≤ η⁻¹ * (w - v) * η⁻¹ := by
    refine (RBM.norm_green_sub_le hM hM hzw hzv).trans ?_
    rw [sub_self, norm_zero, zero_add, norm_zt_sub hE.le, abs_of_nonneg (by linarith)]
    have h1 : 0 ≤ w - v := by linarith
    gcongr
  have h := RBM.norm_gloop_sub_le (L := d.L N) (W := d.W N) hK1 (by positivity) hM hM hGw hGv
    hsub I hI
  refine h.trans ?_
  have hlen' : (I.σ.length : ℝ) ≤ 6 := by exact_mod_cast hlen
  have hpow : η⁻¹ ^ I.σ.length ≤ η⁻¹ ^ 6 := pow_le_pow_right₀ hK1 hlen
  have hLW : (0 : ℝ) ≤ (d.L N : ℝ) * (d.W N : ℝ) := by positivity
  have hΔ : 0 ≤ η⁻¹ * (w - v) * η⁻¹ := by
    have : 0 ≤ w - v := by linarith
    positivity
  calc (d.L N : ℝ) * (d.W N : ℝ) * (I.σ.length : ℝ) * η⁻¹ ^ I.σ.length * (η⁻¹ * (w - v) * η⁻¹)
      ≤ (d.L N : ℝ) * (d.W N : ℝ) * 6 * η⁻¹ ^ 6 * (η⁻¹ * (w - v) * η⁻¹) := by gcongr

/-- **O2 transfer of the good set to the shifted spectral parameter.** If `H ∈ goodSetPP(v)` with
decay tail `D₀`, then at `z_w` (`v ≤ w`): `Ξ^{(L)}_6(z_w, A_w) ≤ N^ε(ℓ_v/ℓ_s)⁵ + 1` provided
`A_w⁵δ′ ≤ 1`, and the 6-loop decay holds at `w` (radius `ℓ_wW^ε`) with tail `W^{-D₂}` provided
`W^{-D₀} + δ′ ≤ W^{-D₂}`, where `δ′` is the loop modulus of `norm_gloop_shift_le`. -/
theorem goodSetPP_shift {E : ℝ} (hE : |E| < 2) {N : ℕ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {v w ε ℓs D₀ D₂ η : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hηw : η ≤ etaT E w) (hℓs : 0 < ℓs)
    (hgood : M ∈ goodSetPP d E N v ε ℓs D₀)
    (hsmall : (band d).scale E N w ^ 5
      * ((d.L N : ℝ) * (d.W N : ℝ) * 6 * η⁻¹ ^ 6 * (η⁻¹ * (w - v) * η⁻¹)) ≤ 1)
    (htail : (d.W N : ℝ) ^ (-D₀)
      + (d.L N : ℝ) * (d.W N : ℝ) * 6 * η⁻¹ ^ 6 * (η⁻¹ * (w - v) * η⁻¹) ≤ (d.W N : ℝ) ^ (-D₂)) :
    loopXi (d.L N) (d.W N) M (zt E w) ((band d).scale E N w) 6
        ≤ (N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 5 + 1
      ∧ M ∈ decaySet d E N 6 w ε D₂ := by
  obtain ⟨⟨⟨⟨_hG1, _hG2⟩, hG3⟩, hG4⟩, _hG5⟩ := hgood
  set δ' : ℝ := (d.L N : ℝ) * (d.W N : ℝ) * 6 * η⁻¹ ^ 6 * (η⁻¹ * (w - v) * η⁻¹) with hδ'
  have hv1 : v < 1 := hvw.trans_lt hw1
  have hAv : 0 < (band d).scale E N v := (band d).scale_pos' hE N hv0 hv1
  have hAw : 0 < (band d).scale E N w := (band d).scale_pos' hE N (hv0.trans hvw) hw1
  have hAwv : (band d).scale E N w ≤ (band d).scale E N v :=
    flowScale_antitoneOn (Nat.cast_nonneg _) _ E (Set.mem_Iic.mpr hv1.le)
      (Set.mem_Iic.mpr hw1.le) hvw
  refine ⟨?_, ?_⟩
  · -- `Ξ^{(L)}_6` at the shifted parameter
    have hbound : ∀ x : (Fin 6 → Bool) × (Fin 6 → ZMod (d.L N)),
        ‖gloop (d.L N) (d.W N) M (zt E w) ⟨List.ofFn x.1, List.ofFn x.2⟩‖
          ≤ (N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 5 * ((band d).scale E N v)⁻¹ ^ 5 + δ' := by
      intro x
      have h1 := hG3 x
      have hwf : (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (ZMod (d.L N))).WF := by
        simp [LoopIdx.WF]
      have h2 := norm_gloop_shift_le hE hM hvw hw1 hη0 hη1 hηw _ hwf (by simp)
      have h3 : ‖gloop (d.L N) (d.W N) M (zt E w) ⟨List.ofFn x.1, List.ofFn x.2⟩‖
          ≤ ‖gloop (d.L N) (d.W N) M (zt E v) ⟨List.ofFn x.1, List.ofFn x.2⟩‖ + δ' := by
        have := norm_sub_norm_le (gloop (d.L N) (d.W N) M (zt E w) ⟨List.ofFn x.1, List.ofFn x.2⟩)
          (gloop (d.L N) (d.W N) M (zt E v) ⟨List.ofFn x.1, List.ofFn x.2⟩)
        linarith
      have h1' : ‖gloop (d.L N) (d.W N) M (zt E v) ⟨List.ofFn x.1, List.ofFn x.2⟩‖
          ≤ (N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 5 * ((band d).scale E N v)⁻¹ ^ 5 := by
        simpa [LoopData.idx] using h1
      linarith
    have hmax : loopMax (d.L N) (d.W N) M (zt E w) 6
        ≤ (N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 5 * ((band d).scale E N v)⁻¹ ^ 5 + δ' :=
      ciSup_le hbound
    unfold loopXi
    have hA5 : 0 ≤ (band d).scale E N w ^ (6 - 1) := by positivity
    calc loopMax (d.L N) (d.W N) M (zt E w) 6 * (band d).scale E N w ^ (6 - 1)
        ≤ ((N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 5 * ((band d).scale E N v)⁻¹ ^ 5 + δ')
          * (band d).scale E N w ^ (6 - 1) := mul_le_mul_of_nonneg_right hmax hA5
      _ = (N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 5
            * ((band d).scale E N w / (band d).scale E N v) ^ 5
          + (band d).scale E N w ^ 5 * δ' := by
          rw [show (6 : ℕ) - 1 = 5 from rfl, div_pow]; field_simp
      _ ≤ (N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 5 * 1 + 1 := by
          have hr : ((band d).scale E N w / (band d).scale E N v) ^ 5 ≤ 1 :=
            pow_le_one₀ (by positivity) ((div_le_one hAv).mpr hAwv)
          have hN0 : 0 ≤ (N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 5 := by
            have : 0 ≤ (band d).ell N v := le_trans zero_le_one
              (one_le_ellHat (d.L N) (d.three_le_L N) hv0 hv1)
            positivity
          gcongr
      _ = (N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 5 + 1 := by ring
  · -- the decay at `w`
    intro J hJ hlen x hx y hy hxy
    have hell : (band d).ell N v ≤ (band d).ell N w := RBM.Step3.ellHat_mono hvw hw1
    have hWε : 0 ≤ (d.W N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hxy' : (band d).ell N v * (d.W N : ℝ) ^ ε ≤ (zdist (d.L N) (x - y) : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hell hWε) hxy
    have h1 := hG4 J hJ hlen x hx y hy hxy'
    have hσlen : J.σ.length ≤ 6 := by
      have : J.σ.length = J.length := hJ
      omega
    have h2 := norm_gloop_shift_le hE hM hvw hw1 hη0 hη1 hηw J hJ hσlen
    have h3 : ‖gloop (d.L N) (d.W N) M (zt E w) J‖
        ≤ ‖gloop (d.L N) (d.W N) M (zt E v) J‖ + δ' := by
      have := norm_sub_norm_le (gloop (d.L N) (d.W N) M (zt E w) J)
        (gloop (d.L N) (d.W N) M (zt E v) J)
      linarith
    show ‖gloop (d.L N) (d.W N) M (zt E w) J‖ ≤ (d.W N : ℝ) ^ (-D₂)
    linarith

/-! #### The analytic hypotheses of (T1) for the real `(+,+)` objects -/

/-- `C₂` of `ΦgridG` at `n = 2`, with `η = η_t`. -/
def C2pp (d : Dims) (E : ℝ) (t : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Fintype.card (d.Idx N) : ℝ) * (((2 : ℕ) : ℝ) ^ 2 * (2 * (1 + (etaT E (t N))⁻¹) ^ 3) ^ 2)

theorem C2pp_nonneg (d : Dims) (E : ℝ) (t : ℕ → ℝ) (N : ℕ) : 0 ≤ C2pp d E t N := by
  unfold C2pp; positivity

/-- The conditional second-moment bound `v_j` of the Y increments. -/
def vPP (d : Dims) (κ E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N : ℕ) : ℝ :=
  (CU κ ^ 2 * ((C2pp d E t N / 2) * step s t Kf N)) ^ 2 * (2 * xMom d N 4 + 2 * xMom d N 2 ^ 2)

/-- The fourth-moment bound `w_j` of the Y increments. -/
def wPP (d : Dims) (κ E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N : ℕ) : ℝ :=
  (CU κ ^ 2 * ((C2pp d E t N / 2) * step s t Kf N)) ^ 4 * (8 * (xMom d N 8 + xMom d N 2 ^ 4))

/-- The pathwise drift bound `d_j(ω)`, a function of `H_j(ω)`. -/
def dPP (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N : ℕ) (ε D₀ ℓs : ℝ) (j : ℕ)
    (ω : Ωg d) : ℝ :=
  dBoundPP d E N (time s t Kf N j) ε D₀ ℓs (JPP d E N (time s t Kf N j) (H d s t Kf N j ω))

/-- The per-target QV constant (`cPP`, made nonnegative). -/
def cPPnn (d : Dims) (κ E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N : ℕ) (ε D₂ φ6 : ℝ) (j : ℕ) : ℝ≥0 :=
  (cPP d N E ε D₂ φ6 (CU κ ^ 2) (step s t Kf N) (time s t Kf N (j + 1))).toNNReal

/-- The `(+,+)` good-set-exit stopping time (`tauPP`, with `Kd = ℓ_s`). -/
abbrev tauPP' (d : Dims) (E ε D₀ : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N : ℕ) : Ωg d → ℕ :=
  tauPP d E ε ((band d).ell N (s N)) D₀ s t Kf N

theorem CU_pos {κ : ℝ} (hκ0 : 0 < κ) : 0 < CU κ := by
  have h1 := cTwo52_pos
  have h2 := cZero_pos
  have h3 := Real.sqrt_pos.mpr hκ0
  unfold CU
  positivity

theorem dBoundPP_nonneg (d : Dims) {E : ℝ} (hE : |E| < 2) {N : ℕ} {v : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v < 1) (ε D₀ ℓs : ℝ) {J : ℝ} (hJ : 0 ≤ J) : 0 ≤ dBoundPP d E N v ε D₀ ℓs J := by
  have hA := inv_nonneg.mpr ((band d).scale_pos' hE N hv0 hv1).le
  have hη := inv_nonneg.mpr (etaT_pos_of_lt_one' hE hv1).le
  have hW : (0 : ℝ) ≤ (d.W N : ℝ) := Nat.cast_nonneg _
  have hWε : 0 ≤ (d.W N : ℝ) ^ ε := Real.rpow_nonneg hW _
  have hWD : 0 ≤ (d.W N : ℝ) ^ (-D₀) := Real.rpow_nonneg hW _
  have hNε : 0 ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hL : (0 : ℝ) ≤ (d.L N : ℝ) := Nat.cast_nonneg _
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  unfold dBoundPP
  have t1 : 0 ≤ 6 * Real.exp 1 * (d.W N : ℝ) ^ ε * J ^ 2 * ((band d).scale E N v)⁻¹ ^ 3
      * (etaT E v)⁻¹ := by
    have := pow_nonneg hA 3
    have := sq_nonneg J
    positivity
  have t2 : 0 ≤ 6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-D₀) * J
      * ((band d).scale E N v)⁻¹ ^ 2 := by
    have := pow_nonneg hA 2
    positivity
  have t3 : 0 ≤ 12 * Real.exp 1 * (d.W N : ℝ) ^ ε * (N : ℝ) ^ ε
      * ((N : ℝ) ^ ε * ((band d).ell N v / ℓs) ^ 2)
      * ((band d).scale E N v)⁻¹ ^ 2 * (etaT E v)⁻¹ := by
    have := pow_nonneg hA 2
    have := sq_nonneg ((band d).ell N v / ℓs)
    positivity
  have t4 : 0 ≤ 12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε
      * (d.W N : ℝ) ^ (-D₀) * ((band d).scale E N v)⁻¹ := by
    positivity
  linarith

theorem measurableSet_lt_tauPP' (d : Dims) (E ε D₀ : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N j : ℕ) :
    MeasurableSet[filt d j] {ω | j < tauPP' d E ε D₀ s t Kf N ω} :=
  lt_firstHit_grid_measurableSet d s t Kf N
    (F := fun j M => (goodSetPP d E N (time s t Kf N j) ε ((band d).ell N (s N)) D₀)ᶜ.indicator
      (fun _ => (1 : ℝ)) M)
    (fun _ => measurable_const.indicator (measurableSet_goodSetPP d E N _ ε _ D₀).compl)
    (1 / 2) (Kf N) j

theorem stronglyMeasurable_Ypp (i : ℕ) (hE : |E| < 2) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hK0 : Kf N ≠ 0) :
    StronglyMeasurable[filt d i] (Ypp d E s t Kf N i) := by
  by_cases hi : 1 ≤ i ∧ i ≤ Kf N
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hfun : Ypp d E s t Kf N (j + 1) = fun ω a =>
        stepYC d s t Kf N j 2 (Φpp d E s t Kf N (j + 1)) (gridDeltaC (d.L N) 2) a ω := by
      funext ω a
      simp only [Ypp, hi, and_self, ↓reduceIte, Nat.add_sub_cancel]
    rw [hfun]
    refine Measurable.stronglyMeasurable ?_
    refine @Measurable.of_eval _ _ _ (filt d (j + 1)) _ _ fun a => ?_
    exact measurable_stepYC_filt s t Kf N j 2
      (gridΦG_testFun d hE hst ht1 hK0 (by norm_num) sigmaPP (j + 1) hi.1 hi.2) _ a
  · have : Ypp d E s t Kf N i = fun _ _ => 0 := by
      funext ω a
      simp only [Ypp, hi, ↓reduceIte]
    rw [this]
    exact stronglyMeasurable_const

/-- The stopped Y edge equals the indicator of `stepYC` with the kernel folded in, a.e. -/
theorem stoppedEdge_Ypp_ae (hE : |E| < 2) (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : Kf N ≠ 0)
    (τ : Ωg d → ℕ) {j k : ℕ} (hjk : j < k) (hk : k ≤ Kf N) (b : LoopArg (d.L N) 2) :
    stoppedEdge (d.L N) (xiPP E) (time s t Kf N) (time s t Kf N k) τ (Ypp d E s t Kf N) b j
      =ᵐ[Pg d] {ω | j < τ ω}.indicator (fun ω => stepYC d s t Kf N j 2 (Φpp d E s t Kf N (j + 1))
          (ukerMatC (xiPP E) (time s t Kf N (j + 1)) (time s t Kf N k)) b ω) := by
  have hi : 1 ≤ j + 1 ∧ j + 1 ≤ Kf N := ⟨by omega, by omega⟩
  have hYfun : ∀ ω, Ypp d E s t Kf N (j + 1) ω = fun a =>
      stepYC d s t Kf N j 2 (Φpp d E s t Kf N (j + 1)) (gridDeltaC (d.L N) 2) a ω := by
    intro ω; funext a
    simp only [Ypp, hi, and_self, ↓reduceIte, Nat.add_sub_cancel]
  filter_upwards [stepYC_ukerMatC_eq_Uker_ae d s t Kf N j 2
    (gridΦG_testFun d hE hst ht1 hK0 (by norm_num) sigmaPP (j + 1) hi.1 hi.2) (xiPP E)
    (time s t Kf N (j + 1)) (time s t Kf N k)] with ω hω
  unfold stoppedEdge
  by_cases hmem : ω ∈ {ω | j < τ ω}
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hYfun ω, hω b]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-- **The Y fields of (T1) for the real `(+,+)` objects** (general-`n` ingredient Y at `n = 2`,
row sum `ρ = C_U(κ)²`, `C₂ = C2pp`). -/
theorem ppY_fields {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : 0 ≤ s N)
    (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : Kf N ≠ 0) (τ : Ωg d → ℕ)
    (hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω}) {j k : ℕ} (hjk : j < k)
    (hk : k ≤ Kf N) (b : LoopArg (d.L N) 2) (T : ℂ →L[ℝ] ℝ) (hT : ∀ z, ‖T z‖ ≤ ‖z‖) :
    (Pg d)[fun ω => T (stoppedEdge (d.L N) (xiPP E) (time s t Kf N) (time s t Kf N k) τ
        (Ypp d E s t Kf N) b j ω) | filt d j] =ᵐ[Pg d] 0
    ∧ Integrable (fun ω => T (stoppedEdge (d.L N) (xiPP E) (time s t Kf N) (time s t Kf N k) τ
        (Ypp d E s t Kf N) b j ω) ^ 4) (Pg d)
    ∧ (Pg d)[fun ω => T (stoppedEdge (d.L N) (xiPP E) (time s t Kf N) (time s t Kf N k) τ
        (Ypp d E s t Kf N) b j ω) ^ 2 | filt d j] ≤ᵐ[Pg d] (fun _ => vPP d κ E s t Kf N)
    ∧ ∫ ω, T (stoppedEdge (d.L N) (xiPP E) (time s t Kf N) (time s t Kf N k) τ
        (Ypp d E s t Kf N) b j ω) ^ 4 ∂(Pg d) ≤ wPP d κ E s t Kf N := by
  have hE : |E| < 2 := by linarith
  have hi : 1 ≤ j + 1 ∧ j + 1 ≤ Kf N := ⟨by omega, by omega⟩
  have hΦ := gridΦG_testFun d hE hst ht1 hK0 (by norm_num) sigmaPP (j + 1) hi.1 hi.2
  have hηt : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE ht1
  have hu1 : time s t Kf N (j + 1) < 1 := time_lt_one_pp hst ht1 hK0 hi.2
  have hut : time s t Kf N (j + 1) ≤ t N := time_le_t_pp hst hK0 hi.2
  have hzη : etaT E (t N) ≤ |(zt E (time s t Kf N (j + 1))).im| := by
    rw [zt_im, abs_of_nonneg (mul_nonneg (by linarith) (mE_im_pos hE).le)]
    exact etaT_le_of_le hE hut
  have hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φpp d E s t Kf N (j + 1) a)) A‖ ≤ C2pp d E t N :=
    fun a A => ΦgridG_bdd2 (band d) hE N hu1 hηt hzη sigmaPP a A
  have hρ : ∑ a : LoopArg (d.L N) 2,
      ‖ukerMatC (xiPP E) (time s t Kf N (j + 1)) (time s t Kf N k) b a‖ ≤ CU κ ^ 2 :=
    sum_norm_Uker_pp_le (d.three_le_L N) hκ0 hκ1 hEκ (time_nonneg_pp hs0 hst (j + 1))
      (time_mono_of_le hst (by omega)) (time_lt_one_pp hst ht1 hK0 hk) b
  exact Ymoments_of_ae_eq s t Kf N j 2 hΦ hC₂ (step_nonneg' s t Kf N hst) _ b hρ (hτmeas j)
    (stoppedEdge_Ypp_ae hE hst ht1 hK0 τ hjk hk b) T hT

/-- The O2 loop modulus over one grid step, `δ = LW·6·η_t^{-6}·(η_t^{-1}Δη_t^{-1})`. -/
def deltaShift (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N : ℕ) : ℝ :=
  (d.L N : ℝ) * (d.W N : ℝ) * 6 * (etaT E (t N))⁻¹ ^ 6
    * ((etaT E (t N))⁻¹ * step s t Kf N * (etaT E (t N))⁻¹)

/-- **h-qv for the real `(+,+)` linear increments** (per target `k`; paired `vC` form),
from `condVar_pp_grid` via `hqv_of_vC`, with the QV time shift handled by
`goodSetPP_shift`. -/
theorem hqv_pp {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : 0 ≤ s N)
    (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : Kf N ≠ 0) {ε D₀ D₂ φ6 : ℝ} (hε : 0 ≤ ε)
    (hA1 : 1 ≤ (band d).scale E N (t N))
    (hφ6 : (N : ℝ) ^ ε * ((band d).ell N (t N) / (band d).ell N (s N)) ^ 5 + 1 ≤ φ6)
    (hsmall : (band d).scale E N (s N) ^ 5 * deltaShift d E s t Kf N ≤ 1)
    (htail : (d.W N : ℝ) ^ (-D₀) + deltaShift d E s t Kf N ≤ (d.W N : ℝ) ^ (-D₂)) :
    ∀ k ≤ Kf N, ∀ (a : LoopArg (d.L N) 2) (j : ℕ), j < k →
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < tauPP' d E ε D₀ s t Kf N ω'}.indicator
          (fun ω' => Uker (d.L N) (xiPP E) (time s t Kf N (j + 1) : ℂ) (time s t Kf N k : ℂ)
            (Zpp d E s t Kf N (j + 1) ω') a) ω).re) (cPPnn d κ E s t Kf N ε D₂ φ6 j) (Pg d) ∧
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < tauPP' d E ε D₀ s t Kf N ω'}.indicator
          (fun ω' => Uker (d.L N) (xiPP E) (time s t Kf N (j + 1) : ℂ) (time s t Kf N k : ℂ)
            (Zpp d E s t Kf N (j + 1) ω') a) ω).im) (cPPnn d κ E s t Kf N ε D₂ φ6 j) (Pg d) := by
  have hE : |E| < 2 := by linarith
  have hΦ : ∀ i, 1 ≤ i → i ≤ Kf N → ∀ a, TestFun d N (Φpp d E s t Kf N i a) :=
    gridΦG_testFun d hE hst ht1 hK0 (by norm_num) sigmaPP
  have hΔ := step_nonneg' s t Kf N hst
  have hηt : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE ht1
  have hηt1 : etaT E (t N) ≤ 1 := by
    show (1 - t N) * (mE E).im ≤ 1
    have h1 := mE_im_le_one hE
    have h2 := (mE_im_pos hE).le
    nlinarith
  have hℓs : 0 < (band d).ell N (s N) := lt_of_lt_of_le zero_lt_one
    (one_le_ellHat (d.L N) (d.three_le_L N) hs0 (hst.trans_lt ht1))
  have hδ0 : 0 ≤ deltaShift d E s t Kf N := by
    have := inv_nonneg.mpr hηt.le
    unfold deltaShift; positivity
  refine hqv_of_vC s t Kf N 2 (xiPP E) (tauPP' d E ε D₀ s t Kf N)
    (measurableSet_lt_tauPP' d E ε D₀ s t Kf N) (Φpp d E s t Kf N) hΦ hΔ
    (fun _ _ j => cPPnn d κ E s t Kf N ε D₂ φ6 j) ?_
  intro k hk a j hjk ω hjτ
  have hjK : j < Kf N := lt_of_lt_of_le hjk hk
  have hmem := lt_tauPP_imp d hjτ
  have hv0 : 0 ≤ time s t Kf N j := time_nonneg_pp hs0 hst j
  have hvw : time s t Kf N j ≤ time s t Kf N (j + 1) := time_mono_of_le hst (Nat.le_succ j)
  have hw1 : time s t Kf N (j + 1) < 1 := time_lt_one_pp hst ht1 hK0 (by omega)
  have hwt : time s t Kf N (j + 1) ≤ t N := time_le_t_pp hst hK0 (by omega)
  have hηw : etaT E (t N) ≤ etaT E (time s t Kf N (j + 1)) := etaT_le_of_le hE hwt
  have hwv : time s t Kf N (j + 1) - time s t Kf N j = step s t Kf N := by
    rw [time_succ']; ring
  have hAw_s : (band d).scale E N (time s t Kf N (j + 1)) ≤ (band d).scale E N (s N) := by
    have h := flowScale_antitoneOn (Nat.cast_nonneg (d.W N)) (d.L N) E
      (Set.mem_Iic.mpr (le_of_lt (hst.trans_lt ht1))) (Set.mem_Iic.mpr hw1.le)
      (show s N ≤ time s t Kf N (j + 1) by
        have := time_mono_of_le (K := Kf) (N := N) hst (Nat.zero_le (j + 1))
        rwa [time_zero] at this)
    exact h
  have hAw0 : 0 < (band d).scale E N (time s t Kf N (j + 1)) :=
    (band d).scale_pos' hE N (hv0.trans hvw) hw1
  have hsmall' : (band d).scale E N (time s t Kf N (j + 1)) ^ 5
      * ((d.L N : ℝ) * (d.W N : ℝ) * 6 * (etaT E (t N))⁻¹ ^ 6
        * ((etaT E (t N))⁻¹ * (time s t Kf N (j + 1) - time s t Kf N j) * (etaT E (t N))⁻¹))
      ≤ 1 := by
    rw [hwv]
    refine le_trans ?_ hsmall
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hAw0.le hAw_s 5) hδ0
  have htail' : (d.W N : ℝ) ^ (-D₀)
      + (d.L N : ℝ) * (d.W N : ℝ) * 6 * (etaT E (t N))⁻¹ ^ 6
        * ((etaT E (t N))⁻¹ * (time s t Kf N (j + 1) - time s t Kf N j) * (etaT E (t N))⁻¹)
      ≤ (d.W N : ℝ) ^ (-D₂) := by
    rw [hwv]; exact htail
  obtain ⟨hΞ, hdec⟩ := goodSetPP_shift hE (H_isHermitian d s t Kf N j ω) hv0 hvw hw1 hηt hηt1
    hηw hℓs hmem hsmall' htail'
  have hell : (band d).ell N (time s t Kf N j) ≤ (band d).ell N (t N) :=
    RBM.Step3.ellHat_mono (time_le_t_pp hst hK0 hjK.le) ht1
  have hell0 : 0 ≤ (band d).ell N (time s t Kf N j) / (band d).ell N (s N) :=
    div_nonneg (le_trans zero_le_one (one_le_ellHat (d.L N) (d.three_le_L N) hv0
      (lt_of_le_of_lt hvw hw1))) hℓs.le
  have hΞ6 : loopXi (d.L N) (d.W N) (H d s t Kf N j ω) (zt E (time s t Kf N (j + 1)))
      ((band d).scale E N (time s t Kf N (j + 1))) 6 ≤ φ6 := by
    refine hΞ.trans (le_trans ?_ hφ6)
    have h5 : ((band d).ell N (time s t Kf N j) / (band d).ell N (s N)) ^ 5
        ≤ ((band d).ell N (t N) / (band d).ell N (s N)) ^ 5 :=
      pow_le_pow_left₀ hell0 (div_le_div_of_nonneg_right hell hℓs.le) 5
    have hN : 0 ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith
  have hA1' : 1 ≤ (band d).scale E N (time s t Kf N (j + 1)) := by
    refine hA1.trans ?_
    exact flowScale_antitoneOn (Nat.cast_nonneg (d.W N)) (d.L N) E
      (Set.mem_Iic.mpr hw1.le) (Set.mem_Iic.mpr ht1.le) hwt
  have hWτ1 : 1 ≤ (d.W N : ℝ) ^ ε :=
    Real.one_le_rpow (by exact_mod_cast d.W_pos N) hε
  have hCU : ∑ b : LoopArg (d.L N) 2,
      ‖ukerMatC (xiOf (mSigma E) sigmaPP) (time s t Kf N (j + 1)) (time s t Kf N k) a b‖
        ≤ CU κ ^ 2 :=
    sum_norm_Uker_pp_le (d.three_le_L N) hκ0 hκ1 hEκ (hv0.trans hvw)
      (time_mono_of_le hst hjk) (time_lt_one_pp hst ht1 hK0 hk) a
  have hcv := condVar_pp_grid E hE s t Kf j k (hv0.trans hvw) hw1 hA1' hWτ1 hΔ ω hΞ6 hdec a hCU
  exact hcv.trans (Real.le_coe_toNNReal _)

/-- **The analytic hypotheses of (T1) for the real `(+,+)` objects** (all fields except h-qv,
which is `hqv_pp`). -/
theorem ppHyp_real {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : 0 ≤ s N)
    (hst : s N < t N) (ht1 : t N < 1) (hK0 : Kf N ≠ 0) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (t N), ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval E N w J‖ ≤ Bk)
    {ε D₀ D₂ φ6 : ℝ} (hε : 0 ≤ ε) (hφ6 : 0 ≤ φ6) :
    PPAssemblyHyp (Pg d) (filt d) (d.L N) E (time s t Kf N) (tauPP' d E ε D₀ s t Kf N)
      (step s t Kf N) (Kf N) (App d E s t Kf N 0) (Ast d E s t Kf N (tauPP' d E ε D₀ s t Kf N))
      (Dpp d E s t Kf N) (Zpp d E s t Kf N) (Ypp d E s t Kf N) (Rpp d E s t Kf N Bk)
      (dPP d E s t Kf N ε D₀ ((band d).ell N (s N)))
      (fun _ _ j => cPPnn d κ E s t Kf N ε D₂ φ6 j) (fun _ => vPP d κ E s t Kf N)
      (fun _ => wPP d κ E s t Kf N) (errPP d E s t Kf N Bk) := by
  have hE : |E| < 2 := by linarith
  have hΔ := step_nonneg' s t Kf N hst.le
  have hΔpos : 0 < step s t Kf N := by
    unfold step
    exact div_pos (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero hK0)
  have hreT : ∀ z : ℂ, ‖Complex.reCLM z‖ ≤ ‖z‖ := fun z => by
    rw [Complex.reCLM_apply, Real.norm_eq_abs]; exact Complex.abs_re_le_norm z
  have himT : ∀ z : ℂ, ‖Complex.imCLM z‖ ≤ ‖z‖ := fun z => by
    rw [Complex.imCLM_apply, Real.norm_eq_abs]; exact Complex.abs_im_le_norm z
  have hτm := measurableSet_lt_tauPP' d E ε D₀ s t Kf N
  have hYf := fun {j k : ℕ} (hjk : j < k) (hk : k ≤ Kf N) (b : LoopArg (d.L N) 2) =>
    ppY_fields (d := d) (E := E) (s := s) (t := t) (Kf := Kf) (N := N) hκ0 hκ1 hEκ hs0 hst.le ht1
      hK0 (tauPP' d E ε D₀ s t Kf N) hτm hjk hk b
  exact
  { hL3 := d.three_le_L N
    hu0 := fun i _ => time_nonneg_pp hs0 hst.le i
    hu1 := fun i hi => time_lt_one_pp hst.le ht1 hK0 hi
    hmono := fun i k hik _ => time_mono_of_le hst.le hik
    hΔ0 := hΔ
    hexp := hexp_pp hE hs0 hst ht1 hK0 hBk0 hBk _
    hdDrift0 := fun ω j hj => dBoundPP_nonneg d hE (time_nonneg_pp hs0 hst.le j)
      (time_lt_one_pp hst.le ht1 hK0 hj.le) _ _ _ (JPP_nonneg d E N _ _)
    hdrift := fun ω j hj hjτ b => norm_drift_pp_le d hE (time_nonneg_pp hs0 hst.le j)
      (time_lt_one_pp hst.le ht1 hK0 hj.le) hε (lt_tauPP_imp d hjτ) b
    hc_pos := by
      intro k hk1 hkK a
      have hpos0 : 0 < (cPPnn d κ E s t Kf N ε D₂ φ6 0 : ℝ) := by
        have hw1 : time s t Kf N (0 + 1) < 1 := time_lt_one_pp hst.le ht1 hK0 (by omega)
        have hw0 : 0 ≤ time s t Kf N (0 + 1) := time_nonneg_pp hs0 hst.le _
        have hη := inv_nonneg.mpr (etaT_pos_of_lt_one' hE hw1).le
        have hA := inv_nonneg.mpr ((band d).scale_pos' hE N hw0 hw1).le
        have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
        have hL : (0 : ℝ) < (d.L N : ℝ) := by
          have := d.three_le_L N; exact_mod_cast (show 0 < d.L N by omega)
        have hCU := CU_pos hκ0
        have hpos : 0 < cPP d N E ε D₂ φ6 (CU κ ^ 2) (step s t Kf N) (time s t Kf N (0 + 1)) := by
          unfold cPP eeHermBdPP
          have h1 : 0 ≤ 24 * Real.exp 1 * φ6 * (d.W N : ℝ) ^ ε
              * ((band d).scale E N (time s t Kf N (0 + 1)))⁻¹ ^ 4
              * (etaT E (time s t Kf N (0 + 1)))⁻¹ := by
            have := pow_nonneg hA 4
            have := Real.rpow_nonneg hW.le ε
            positivity
          have h2 : 0 < 4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D₂) := by
            have := Real.rpow_pos_of_pos hW (-D₂)
            positivity
          positivity
        simp only [cPPnn, Real.coe_toNNReal _ hpos.le]
        exact hpos
      calc (0 : ℝ) < (cPPnn d κ E s t Kf N ε D₂ φ6 0 : ℝ) := hpos0
        _ ≤ ∑ j ∈ range k, (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ) :=
          Finset.single_le_sum (f := fun j => (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ))
            (fun _ _ => NNReal.coe_nonneg _) (Finset.mem_range.mpr (by omega))
    hYmeas := fun i => stronglyMeasurable_Ypp i hE hst.le ht1 hK0
    hv0 := fun _ _ => mul_nonneg (sq_nonneg _) (by
      have := xMom_nonneg d N 4; have := xMom_nonneg d N 2; positivity)
    hw0 := fun _ _ => mul_nonneg (by positivity) (by
      have := xMom_nonneg d N 8; have := xMom_nonneg d N 2; positivity)
    hYmeanRe := fun k hk b j hjk => by
      simpa only [Complex.reCLM_apply] using (hYf hjk hk b Complex.reCLM hreT).1
    hYmeanIm := fun k hk b j hjk => by
      simpa only [Complex.imCLM_apply] using (hYf hjk hk b Complex.imCLM himT).1
    hYintRe := fun k hk b j hjk => by
      simpa only [Complex.reCLM_apply] using (hYf hjk hk b Complex.reCLM hreT).2.1
    hYintIm := fun k hk b j hjk => by
      simpa only [Complex.imCLM_apply] using (hYf hjk hk b Complex.imCLM himT).2.1
    hYcondRe := fun k hk b j hjk => by
      simpa only [Complex.reCLM_apply] using (hYf hjk hk b Complex.reCLM hreT).2.2.1
    hYcondIm := fun k hk b j hjk => by
      simpa only [Complex.imCLM_apply] using (hYf hjk hk b Complex.imCLM himT).2.2.1
    hY4Re := fun k hk b j hjk => by
      simpa only [Complex.reCLM_apply] using (hYf hjk hk b Complex.reCLM hreT).2.2.2
    hY4Im := fun k hk b j hjk => by
      simpa only [Complex.imCLM_apply] using (hYf hjk hk b Complex.imCLM himT).2.2.2
    hstepErr0 := fun _ _ => le_max_left _ _
    hR := by
      intro ω j _ _ b
      unfold Rpp
      split_ifs with h
      · exact h b
      · simp only [Pi.zero_apply, norm_zero]; exact le_max_left _ _ }

set_option maxHeartbeats 1000000 in
/-- **The `n = 2` step error is polynomially `O(Δ^{3/2})`** (C4): with `WL ≤ N`,
`((1 − u_{k+1}) Im m)^{-1} ≤ N`, `0 ≤ Δ ≤ 1`,
`stepErrN(n=2) ≤ 2^{17} N^{15} (1 + B_K)⁴ Δ^{3/2}`. -/
theorem stepErrN_two_le (d : Dims) {E : ℝ} (hE : |E| < 2) {N : ℕ} (hN1 : (1 : ℝ) ≤ N)
    (hWL : (d.W N : ℝ) * d.L N ≤ N) {uk uk1 Δ Bk : ℝ} (hBk0 : 0 ≤ Bk) (hΔ0 : 0 ≤ Δ)
    (hΔ1 : Δ ≤ 1) (hukuk1 : uk ≤ uk1) (huk1 : uk1 < 1)
    (hη : ((1 - uk1) * (mE E).im)⁻¹ ≤ N) :
    stepErrN (band d) E N 2 uk uk1 Δ Bk ≤ 2 ^ 17 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4 * Δ ^ (3 / 2 : ℝ) := by
  have hm0 := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have h1u : 0 < 1 - uk1 := by linarith
  have hη1 : 0 < (1 - uk1) * (mE E).im := mul_pos h1u hm0
  have hη0 : (1 - uk1) * (mE E).im ≤ |(zt E uk).im| := by
    rw [zt_im, abs_of_nonneg (mul_nonneg (by linarith) hm0.le)]
    exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  have hη0pos : 0 < |(zt E uk).im| := hη1.trans_le hη0
  have hη0N : |(zt E uk).im|⁻¹ ≤ N := (inv_anti₀ hη1 hη0).trans hη
  have hu1N : (1 - uk1)⁻¹ ≤ N := by
    refine le_trans ?_ hη
    rw [mul_inv]
    exact le_mul_of_one_le_right (inv_nonneg.2 h1u.le) (one_le_inv₀ hm0 |>.2 hm1)
  have hmx : max ‖mSigma E true‖ ‖mSigma E false‖ ≤ 1 := by
    rw [norm_mSigma hE.le, norm_mSigma hE.le, max_self]
  have hW1 : 1 ≤ d.W N := d.W_pos N
  have hW1' : (1 : ℝ) ≤ d.W N := by exact_mod_cast hW1
  have hWinv : ((d.W N : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1'
  have hZZ : zMotionZLip ((band d).L N) ((band d).W N) 2 ((1 - uk1) * (mE E).im) (mSigma E)
      ≤ 192 * (N : ℝ) ^ 7 := zMotionZLip_le (L := d.L N) (W := d.W N) hWL hη1 hη hN1 hmx
  have hZL : zMotionLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)
      ≤ 48 * (N : ℝ) ^ 7 := zMotionLip_le (L := d.L N) (W := d.W N) hWL hη0pos hη0N hN1 hmx
  have hDL : driftLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)
      ≤ 27648 * (N : ℝ) ^ 14 := driftLip_le (L := d.L N) (W := d.W N) hWL hW1 hη0pos hη0N hN1 hmx
  have hX := integral_norm_Xmat_le d N
  have hLWn : (((d.L N * d.W N : ℕ) : ℝ)) ≤ N := by
    have : ((d.L N * d.W N : ℕ) : ℝ) = (d.W N : ℝ) * d.L N := by push_cast; ring
    rw [this]; exact hWL
  have hX2 : ∫ x, ‖Xmat d N x‖ ∂(P d) ≤ 2 * N := by linarith
  have hX0 : 0 ≤ ∫ x, ‖Xmat d N x‖ ∂(P d) := integral_nonneg fun _ => norm_nonneg _
  have hZZ0 : 0 ≤ zMotionZLip ((band d).L N) ((band d).W N) 2 ((1 - uk1) * (mE E).im) (mSigma E) := by
    have : 0 ≤ ((1 - uk1) * (mE E).im)⁻¹ := inv_nonneg.2 hη1.le
    unfold zMotionZLip; positivity
  have hZL0 : 0 ≤ zMotionLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E) := by
    unfold zMotionLip; positivity
  have hDL0 : 0 ≤ driftLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E) := by
    unfold driftLip; positivity
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hΔ2 : Δ ^ 2 ≤ Δ ^ (3 / 2 : ℝ) := by
    rw [show Δ ^ 2 = Δ ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_ge' hΔ0 hΔ1 (by norm_num) (by norm_num)
  have hΔ32 : 0 ≤ Δ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hΔ0 _
  have hB1 : (1 : ℝ) ≤ (1 + Bk) ^ 4 := one_le_pow₀ (by linarith)
  have hBk3 : Bk ^ 3 ≤ (1 + Bk) ^ 4 := by
    calc Bk ^ 3 ≤ (1 + Bk) ^ 3 := pow_le_pow_left₀ hBk0 (by linarith) 3
      _ ≤ (1 + Bk) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hBk4 : Bk ^ 4 ≤ (1 + Bk) ^ 4 := pow_le_pow_left₀ hBk0 (by linarith) 4
  have hBk1 : Bk ≤ (1 + Bk) ^ 4 := by
    calc Bk ≤ 1 + Bk := by linarith
      _ ≤ (1 + Bk) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hNp : ∀ k : ℕ, k ≤ 15 → (N : ℝ) ^ k ≤ (N : ℝ) ^ 15 := fun k hk =>
    pow_le_pow_right₀ hN1 hk
  unfold stepErrN
  rw [norm_mE hE.le]
  -- term 1
  have t1 : zMotionZLip ((band d).L N) ((band d).W N) 2 ((1 - uk1) * (mE E).im) (mSigma E) * 1 * Δ ^ 2 / 2
      ≤ 96 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4 * Δ ^ (3 / 2 : ℝ) := by
    have h7 := hNp 7 (by norm_num)
    have : zMotionZLip ((band d).L N) ((band d).W N) 2 ((1 - uk1) * (mE E).im) (mSigma E) * 1 * Δ ^ 2 / 2
        ≤ 96 * (N : ℝ) ^ 7 * Δ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hZZ (sq_nonneg Δ)
      linarith
    refine this.trans ?_
    have hN15 : 0 ≤ (N : ℝ) ^ 15 := by positivity
    calc 96 * (N : ℝ) ^ 7 * Δ ^ 2 ≤ 96 * (N : ℝ) ^ 15 * 1 * Δ ^ (3 / 2 : ℝ) := by
          have := mul_le_mul h7 hΔ2 (sq_nonneg Δ) hN15
          linarith
      _ ≤ 96 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4 * Δ ^ (3 / 2 : ℝ) := by gcongr
  -- term 2
  have t2 : (zMotionLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)
        + (2 / 3) * genPtLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E))
        * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat (band d).toDims N x‖ ∂ (P (band d).toDims))
      ≤ 37024 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4 * Δ ^ (3 / 2 : ℝ) := by
    unfold genPtLip
    have hc : zMotionLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)
        + (2 / 3) * (driftLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)
          + zMotionLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)) ≤ 18512 * (N : ℝ) ^ 14 := by
      have h7 : (N : ℝ) ^ 7 ≤ (N : ℝ) ^ 14 := pow_le_pow_right₀ hN1 (by norm_num)
      linarith
    have hc0 : 0 ≤ zMotionLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)
        + (2 / 3) * (driftLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)
          + zMotionLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)) := by positivity
    have hX2' : ∫ x, ‖Xmat (band d).toDims N x‖ ∂ (P (band d).toDims) ≤ 2 * N := hX2
    have hX0' : 0 ≤ ∫ x, ‖Xmat (band d).toDims N x‖ ∂ (P (band d).toDims) := hX0
    calc (zMotionLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)
          + (2 / 3) * (driftLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)
            + zMotionLip ((band d).L N) ((band d).W N) 2 |(zt E uk).im| (mSigma E)))
          * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat (band d).toDims N x‖ ∂ (P (band d).toDims))
        ≤ (18512 * (N : ℝ) ^ 14) * Δ ^ (3 / 2 : ℝ) * (2 * N) := by gcongr
      _ = 37024 * (N : ℝ) ^ 15 * 1 * Δ ^ (3 / 2 : ℝ) := by ring
      _ ≤ 37024 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4 * Δ ^ (3 / 2 : ℝ) := by gcongr
  -- term 3
  have t3 : (2 * ((band d).W N : ℝ) * ((2 : ℕ) : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk
          * (((band d).W N : ℝ) * ((2 : ℕ) : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2)
        + ((band d).W N : ℝ) * ((2 : ℕ) : ℝ) ^ 2 * ((band d).L N : ℝ)
            * (((band d).W N : ℝ) * ((2 : ℕ) : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2) ^ 2) * Δ ^ 2
      ≤ 96 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4 * Δ ^ (3 / 2 : ℝ) := by
    have hWLb : ((band d).W N : ℝ) * ((band d).L N : ℝ) ≤ N := hWL
    have hWL0 : (0 : ℝ) ≤ ((band d).W N : ℝ) * ((band d).L N : ℝ) := by positivity
    have e : (2 * ((band d).W N : ℝ) * ((2 : ℕ) : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk
          * (((band d).W N : ℝ) * ((2 : ℕ) : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2)
        + ((band d).W N : ℝ) * ((2 : ℕ) : ℝ) ^ 2 * ((band d).L N : ℝ)
            * (((band d).W N : ℝ) * ((2 : ℕ) : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2) ^ 2)
        = 32 * (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ 2 * Bk ^ 3
          + 64 * (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ 3 * Bk ^ 4 := by
      push_cast; ring
    rw [e]
    have h2 : (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ 2 ≤ (N : ℝ) ^ 15 :=
      (pow_le_pow_left₀ hWL0 hWLb 2).trans (hNp 2 (by norm_num))
    have h3 : (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ 3 ≤ (N : ℝ) ^ 15 :=
      (pow_le_pow_left₀ hWL0 hWLb 3).trans (hNp 3 (by norm_num))
    have hN15 : 0 ≤ (N : ℝ) ^ 15 := by positivity
    have hBk3' : 0 ≤ Bk ^ 3 := pow_nonneg hBk0 3
    have hBk4' : 0 ≤ Bk ^ 4 := pow_nonneg hBk0 4
    have hA : (32 * (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ 2 * Bk ^ 3
          + 64 * (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ 3 * Bk ^ 4)
        ≤ 96 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4 := by
      have e1 := mul_le_mul h2 hBk3 hBk3' hN15
      have e2 := mul_le_mul h3 hBk4 hBk4' hN15
      linarith
    have hA0 : 0 ≤ 32 * (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ 2 * Bk ^ 3
          + 64 * (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ 3 * Bk ^ 4 := by positivity
    calc (32 * (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ 2 * Bk ^ 3
          + 64 * (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ 3 * Bk ^ 4) * Δ ^ 2
        ≤ (96 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4) * Δ ^ (3 / 2 : ℝ) :=
          mul_le_mul hA hΔ2 (sq_nonneg Δ) (by positivity)
      _ = 96 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4 * Δ ^ (3 / 2 : ℝ) := by ring
  -- term 4
  have t4 : (((2 : ℕ) : ℝ) * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2
        + ((1 + Δ * (1 - uk1)⁻¹) ^ 2 - 1 - ((2 : ℕ) : ℝ) * Δ * (1 - uk1)⁻¹))
        * (|(zt E uk).im|⁻¹ ^ 2 * ((band d).W N : ℝ)⁻¹ ^ (2 - 1) + Bk)
      ≤ 6 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4 * Δ ^ (3 / 2 : ℝ) := by
    have e : (((2 : ℕ) : ℝ) * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2
        + ((1 + Δ * (1 - uk1)⁻¹) ^ 2 - 1 - ((2 : ℕ) : ℝ) * Δ * (1 - uk1)⁻¹))
        = 3 * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2 := by push_cast; ring
    rw [e]
    have hu0 : 0 ≤ (1 - uk1)⁻¹ := inv_nonneg.2 h1u.le
    have hi0 : 0 ≤ |(zt E uk).im|⁻¹ := inv_nonneg.2 hη0pos.le
    have hW0 : 0 ≤ ((band d).W N : ℝ)⁻¹ := by positivity
    have hWinv' : ((band d).W N : ℝ)⁻¹ ≤ 1 := hWinv
    have hq : |(zt E uk).im|⁻¹ ^ 2 * ((band d).W N : ℝ)⁻¹ ^ (2 - 1) + Bk ≤ (N : ℝ) ^ 2 + Bk := by
      have : |(zt E uk).im|⁻¹ ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hi0 hη0N 2
      have h' : ((band d).W N : ℝ)⁻¹ ^ (2 - 1) ≤ 1 := by simpa using hWinv'
      have h'' : 0 ≤ ((band d).W N : ℝ)⁻¹ ^ (2 - 1) := by positivity
      have h3 : |(zt E uk).im|⁻¹ ^ 2 * ((band d).W N : ℝ)⁻¹ ^ (2 - 1) ≤ (N : ℝ) ^ 2 * 1 :=
        mul_le_mul this h' h'' (by positivity)
      linarith
    have hu2 : (1 - uk1)⁻¹ ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hu0 hu1N 2
    have hq0 : 0 ≤ |(zt E uk).im|⁻¹ ^ 2 * ((band d).W N : ℝ)⁻¹ ^ (2 - 1) + Bk := by positivity
    calc 3 * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2
          * (|(zt E uk).im|⁻¹ ^ 2 * ((band d).W N : ℝ)⁻¹ ^ (2 - 1) + Bk)
        ≤ 3 * Δ ^ 2 * (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk) := by gcongr
      _ ≤ 3 * Δ ^ (3 / 2 : ℝ) * (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk) := by gcongr
      _ ≤ 6 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4 * Δ ^ (3 / 2 : ℝ) := by
          have h4 : (N : ℝ) ^ 2 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 15 := by
            rw [← pow_add]; exact hNp 4 (by norm_num)
          have h2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 15 := hNp 2 (by norm_num)
          have hN15 : 0 ≤ (N : ℝ) ^ 15 := by positivity
          have hBB : (N : ℝ) ^ 2 * Bk ≤ (N : ℝ) ^ 15 * (1 + Bk) ^ 4 :=
            mul_le_mul h2 hBk1 hBk0 hN15
          have hNN : (N : ℝ) ^ 2 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 15 * (1 + Bk) ^ 4 := by
            have := mul_le_mul h4 hB1 zero_le_one hN15
            linarith
          have hsplit : (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk)
              = (N : ℝ) ^ 2 * (N : ℝ) ^ 2 + (N : ℝ) ^ 2 * Bk := by ring
          have : (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk) ≤ 2 * ((N : ℝ) ^ 15 * (1 + Bk) ^ 4) := by
            rw [hsplit]; linarith
          have hΔ' : 0 ≤ 3 * Δ ^ (3 / 2 : ℝ) := by positivity
          have := mul_le_mul_of_nonneg_left this hΔ'
          have e2 : 3 * Δ ^ (3 / 2 : ℝ) * (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk)
              = 3 * Δ ^ (3 / 2 : ℝ) * ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk)) := by ring
          rw [e2]
          linarith
  have hfin : (96 : ℝ) + 37024 + 96 + 6 ≤ 2 ^ 17 := by norm_num
  have hP0 : 0 ≤ (N : ℝ) ^ 15 * (1 + Bk) ^ 4 * Δ ^ (3 / 2 : ℝ) := by positivity
  linarith [t1, t2, t3, t4]

/-! #### Deterministic bookkeeping for the closure -/

theorem scale_le_N_pp {E : ℝ} (hE : |E| < 2) {N : ℕ} (hWL : (d.W N : ℝ) * d.L N ≤ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : (band d).scale E N u ≤ N := by
  have hm1 := mE_im_le_one hE
  have hm0 := (mE_im_pos hE).le
  have hell : (band d).ell N u ≤ (d.L N : ℝ) := min_le_right _ _
  have hη : etaT E u ≤ 1 := by
    show (1 - u) * (mE E).im ≤ 1
    nlinarith
  have hη0 : 0 ≤ etaT E u := (etaT_pos_of_lt_one' hE hu1).le
  have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
  show (d.W N : ℝ) * (band d).ell N u * etaT E u ≤ N
  calc (d.W N : ℝ) * (band d).ell N u * etaT E u ≤ (d.W N : ℝ) * d.L N * 1 := by
        gcongr
    _ ≤ N := by linarith

theorem scale_anti_pp {E : ℝ} {N : ℕ} {u v : ℝ} (huv : u ≤ v) (hv1 : v < 1) :
    (band d).scale E N v ≤ (band d).scale E N u :=
  flowScale_antitoneOn (Nat.cast_nonneg (d.W N)) (d.L N) E
    (Set.mem_Iic.mpr (huv.trans hv1.le)) (Set.mem_Iic.mpr hv1.le) huv

/-- `J_k = A_k² max_a ‖A_k(a)‖`. -/
theorem JPP_eq_App (k : ℕ) (ω : Ωg d) :
    JPP d E N (time s t Kf N k) (H d s t Kf N k ω)
      = (band d).scale E N (time s t Kf N k) ^ 2
        * Finset.univ.sup' Finset.univ_nonempty (fun a => ‖App d E s t Kf N k ω a‖) := by
  unfold JPP
  rfl

/-- The deterministic coarse bound `J ≤ N²(N² + B_K)` (`|G| ≤ η^{-1}`, `|K| ≤ B_K`). -/
theorem JPP_coarse {E : ℝ} (hE : |E| < 2) {N : ℕ} (hWL : (d.W N : ℝ) * d.L N ≤ N)
    {u η Bk : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hη0 : 0 < η) (hηu : η ≤ etaT E u)
    (hηN : η⁻¹ ≤ N) (hBk : ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 → ‖(band d).Kval E N u J‖ ≤ Bk)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (hM : M.IsHermitian) :
    JPP d E N u M ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk) := by
  have hA0 : 0 < (band d).scale E N u := (band d).scale_pos' hE N hu0 hu1
  have hAN := scale_le_N_pp hE hWL hu0 hu1
  have himu : η ≤ |(zt E u).im| := by
    rw [zt_im, abs_of_nonneg (mul_nonneg (by linarith) (mE_im_pos hE).le)]; exact hηu
  have hW1 : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
  have hsup : Finset.univ.sup' Finset.univ_nonempty (fun a : LoopArg (d.L N) 2 =>
      lkErrMat d E N u M (LoopData.idx (sigPP, a))) ≤ (N : ℝ) ^ 2 + Bk := by
    refine Finset.sup'_le _ _ fun a _ => ?_
    unfold lkErrMat
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · have h := norm_gloop_le_of_le_abs_im (L := d.L N) (W := d.W N) hM hη0 himu
        (LoopData.idx (sigPP, a)) (LoopData.idx_wf _) (by simp [LoopData.idx])
      have hlen : (LoopData.idx (sigPP, a) : LoopIdx (ZMod (d.L N))).a.length = 2 := by
        simp [LoopData.idx]
      rw [hlen] at h
      have h1 : η⁻¹ ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hη0.le) hηN 2
      have h2 : (d.W N : ℝ)⁻¹ ^ (2 - 1) ≤ 1 := by
        simpa using inv_le_one_of_one_le₀ hW1
      have h3 : 0 ≤ (d.W N : ℝ)⁻¹ ^ (2 - 1) := by positivity
      calc _ ≤ η⁻¹ ^ 2 * (d.W N : ℝ)⁻¹ ^ (2 - 1) := h
        _ ≤ (N : ℝ) ^ 2 * 1 := mul_le_mul h1 h2 h3 (by positivity)
        _ = (N : ℝ) ^ 2 := by ring
    · exact hBk _ (LoopData.idx_wf _) (le_of_eq (LoopData.idx_length (sigPP, a)).symm)
        (le_of_eq (LoopData.idx_length (sigPP, a)))
  unfold JPP
  have hA2 : (band d).scale E N u ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hA0.le hAN 2
  have hs0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun a : LoopArg (d.L N) 2 =>
      lkErrMat d E N u M (LoopData.idx (sigPP, a))) := by
    obtain ⟨a0⟩ := (inferInstance : Nonempty (LoopArg (d.L N) 2))
    exact (norm_nonneg _).trans (Finset.le_sup' (fun a : LoopArg (d.L N) 2 =>
      lkErrMat d E N u M (LoopData.idx (sigPP, a))) (Finset.mem_univ a0))
  have hB : 0 ≤ (N : ℝ) ^ 2 + Bk := hs0.trans hsup
  exact mul_le_mul hA2 hsup hs0 (by positivity)

/-- On `{τ = K}`, the stopped process is the process: `A^τ_k = A_k` for `k ≤ K`. -/
theorem Ast_eq_App {E : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hK0 : Kf N ≠ 0) (τ : Ωg d → ℕ) {ω : Ωg d} (hτ : τ ω = Kf N) {k : ℕ} (hk : k ≤ Kf N) :
    Ast d E s t Kf N τ k ω = App d E s t Kf N k ω := by
  unfold Ast
  rw [hτ, min_eq_left hk]
  exact Uker_self (d.L N) (d.three_le_L N)
    (fun p => norm_ofReal_mul_lt_one (time_nonneg_pp hs0 hst k)
      (time_lt_one_pp hst ht1 hK0 hk) (norm_xiPP_le_one hE.le p)) _

/-! #### The closure estimates -/

/-- **P1, the drift sum**: `A_k² Δ Σ_{j<k} C_U² d_j ≤ 6e C_U² N^ε m² ℒ/A_t + 12e C_U² N^{3ε}R² ℒ + 2`,
`ℒ = (Im m)^{-1} log N`, for any `m ≥ J_j` (`j < k`); the linear small term (T2) and the
decay tail are absorbed (`hX2`, `hX4`) with the coarse bound `J ≤ N²(N² + B_K)`. -/
theorem drift_sum_bound {κ : ℝ} (hκ0 : 0 < κ) {E : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s N)
    (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : Kf N ≠ 0) {ε D₀ ℓs Bk R : ℝ} (hε : 0 ≤ ε)
    (hℓs : 0 < ℓs) (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (t N), ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval E N w J‖ ≤ Bk)
    (hWL : (d.W N : ℝ) * d.L N ≤ N) (hWN : (d.W N : ℝ) ≤ N) (hηt : (etaT E (t N))⁻¹ ≤ N)
    (hsum : ∑ j ∈ range (Kf N), step s t Kf N / etaT E (time s t Kf N j)
      ≤ (mE E).im⁻¹ * Real.log N)
    (hKΔ : (Kf N : ℝ) * step s t Kf N ≤ 1)
    (hX2 : CU κ ^ 2 * (6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-D₀)
      * ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk))) ≤ 1)
    (hX4 : CU κ ^ 2 * (12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε
      * (d.W N : ℝ) ^ (-D₀) * N) ≤ 1)
    (hR : ∀ j ≤ Kf N, (band d).ell N (time s t Kf N j) / ℓs ≤ R) (hR0 : 0 ≤ R)
    (ω : Ωg d) {k : ℕ} (hk : k ≤ Kf N) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ j < k, JPP d E N (time s t Kf N j) (H d s t Kf N j ω) ≤ m) :
    (band d).scale E N (time s t Kf N k) ^ 2
        * (step s t Kf N * ∑ j ∈ range k, CU κ ^ 2 * dPP d E s t Kf N ε D₀ ℓs j ω)
      ≤ 6 * Real.exp 1 * CU κ ^ 2 * (N : ℝ) ^ ε * m ^ 2 * ((mE E).im⁻¹ * Real.log N)
          / (band d).scale E N (t N)
        + 12 * Real.exp 1 * CU κ ^ 2 * ((N : ℝ) ^ ε) ^ 3 * R ^ 2 * ((mE E).im⁻¹ * Real.log N)
        + 2 := by
  set Δ := step s t Kf N with hΔdef
  set At := (band d).scale E N (t N) with hAtdef
  set Ak := (band d).scale E N (time s t Kf N k) with hAkdef
  have hΔ0 : 0 ≤ Δ := step_nonneg' s t Kf N hst
  have hCU := CU_pos hκ0
  have hCU2 : 0 ≤ CU κ ^ 2 := sq_nonneg _
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
  have hNε0 : 0 ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hWε : (d.W N : ℝ) ^ ε ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow hW0 hWN hε
  have hWε0 : 0 ≤ (d.W N : ℝ) ^ ε := Real.rpow_nonneg hW0 _
  have hWD0 : 0 ≤ (d.W N : ℝ) ^ (-D₀) := Real.rpow_nonneg hW0 _
  have hηt0 : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE ht1
  have hkt : time s t Kf N k ≤ t N := time_le_t_pp hst hK0 hk
  have hk1 : time s t Kf N k < 1 := time_lt_one_pp hst ht1 hK0 hk
  have hAt0 : 0 < At := (band d).scale_pos' hE N (hs0.trans (hst)) ht1
  have hAtk : At ≤ Ak := scale_anti_pp hkt ht1
  have hAk0 : 0 < Ak := hAt0.trans_le hAtk
  -- the per-`j` bound
  set α : ℝ := 6 * Real.exp 1 * CU κ ^ 2 * (N : ℝ) ^ ε * m ^ 2 * At⁻¹
    + 12 * Real.exp 1 * CU κ ^ 2 * ((N : ℝ) ^ ε) ^ 3 * R ^ 2 with hαdef
  set β : ℝ := CU κ ^ 2 * (6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-D₀)
      * ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk)))
    + CU κ ^ 2 * (12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε
      * (d.W N : ℝ) ^ (-D₀) * N) with hβdef
  have hper : ∀ j ∈ range k, Ak ^ 2 * (CU κ ^ 2 * dPP d E s t Kf N ε D₀ ℓs j ω)
      ≤ α * (etaT E (time s t Kf N j))⁻¹ + β := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hjK : j ≤ Kf N := by omega
    have hj0 : 0 ≤ time s t Kf N j := time_nonneg_pp hs0 hst j
    have hj1 : time s t Kf N j < 1 := time_lt_one_pp hst ht1 hK0 hjK
    have hjt : time s t Kf N j ≤ t N := time_le_t_pp hst hK0 hjK
    set Aj := (band d).scale E N (time s t Kf N j) with hAjdef
    set ηj := etaT E (time s t Kf N j) with hηjdef
    set J := JPP d E N (time s t Kf N j) (H d s t Kf N j ω) with hJdef
    have hAj0 : 0 < Aj := (band d).scale_pos' hE N hj0 hj1
    have hAkj : Ak ≤ Aj := scale_anti_pp (time_mono_of_le hst hjk.le) hk1
    have hAjN : Aj ≤ N := scale_le_N_pp hE hWL hj0 hj1
    have hAtj : At ≤ Aj := scale_anti_pp hjt ht1
    have hηj0 : 0 < ηj := etaT_pos_of_lt_one' hE hj1
    have hb0 : 0 ≤ ηj⁻¹ := inv_nonneg.2 hηj0.le
    have hJ0 : 0 ≤ J := JPP_nonneg d E N _ _
    have hJm : J ≤ m := hm j hjk
    have hJc : J ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk) :=
      JPP_coarse hE hWL hj0 hj1 hηt0 (etaT_le_of_le hE hjt) hηt
        (fun J' hJ' h2 h2' => hBk _ ⟨hj0, hjt⟩ J' hJ' h2 h2') _ (H_isHermitian d s t Kf N j ω)
    have hRj : (band d).ell N (time s t Kf N j) / ℓs ≤ R := hR j hjK
    have hRj0 : 0 ≤ (band d).ell N (time s t Kf N j) / ℓs :=
      div_nonneg (le_trans zero_le_one (one_le_ellHat (d.L N) (d.three_le_L N) hj0 hj1)) hℓs.le
    -- ratios
    have r1 : Ak ^ 2 * Aj⁻¹ ^ 3 ≤ At⁻¹ := by
      have h1 : Ak ^ 2 * Aj⁻¹ ^ 3 ≤ Aj ^ 2 * Aj⁻¹ ^ 3 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hAk0.le hAkj 2) (by positivity)
      have h2 : Aj ^ 2 * Aj⁻¹ ^ 3 = Aj⁻¹ := by field_simp
      have h3 : Aj⁻¹ ≤ At⁻¹ := inv_anti₀ hAt0 hAtj
      linarith
    have r2 : Ak ^ 2 * Aj⁻¹ ^ 2 ≤ 1 := by
      have h1 : Ak ^ 2 * Aj⁻¹ ^ 2 ≤ Aj ^ 2 * Aj⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hAk0.le hAkj 2) (by positivity)
      have h2 : Aj ^ 2 * Aj⁻¹ ^ 2 = 1 := by field_simp
      linarith
    have r3 : Ak ^ 2 * Aj⁻¹ ≤ N := by
      have h1 : Ak ^ 2 * Aj⁻¹ ≤ Aj ^ 2 * Aj⁻¹ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hAk0.le hAkj 2) (by positivity)
      have h2 : Aj ^ 2 * Aj⁻¹ = Aj := by field_simp
      linarith
    unfold dPP dBoundPP
    rw [← hAjdef, ← hηjdef, ← hJdef]
    -- term by term
    have e1 : Ak ^ 2 * (6 * Real.exp 1 * (d.W N : ℝ) ^ ε * J ^ 2 * Aj⁻¹ ^ 3 * ηj⁻¹)
        ≤ 6 * Real.exp 1 * (N : ℝ) ^ ε * m ^ 2 * At⁻¹ * ηj⁻¹ := by
      have hJ2 : J ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hJ0 hJm 2
      calc Ak ^ 2 * (6 * Real.exp 1 * (d.W N : ℝ) ^ ε * J ^ 2 * Aj⁻¹ ^ 3 * ηj⁻¹)
          = 6 * Real.exp 1 * (d.W N : ℝ) ^ ε * J ^ 2 * (Ak ^ 2 * Aj⁻¹ ^ 3) * ηj⁻¹ := by ring
        _ ≤ 6 * Real.exp 1 * (N : ℝ) ^ ε * m ^ 2 * At⁻¹ * ηj⁻¹ := by
          have := inv_nonneg.2 hAt0.le
          gcongr
    have e2 : Ak ^ 2 * (6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-D₀) * J
          * Aj⁻¹ ^ 2)
        ≤ 6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-D₀)
          * ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk)) := by
      calc Ak ^ 2 * (6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-D₀) * J
            * Aj⁻¹ ^ 2)
          = 6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-D₀) * J
            * (Ak ^ 2 * Aj⁻¹ ^ 2) := by ring
        _ ≤ 6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-D₀)
            * ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk)) * 1 := by
          have := sq_nonneg (d.L N : ℝ)
          have : 0 ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk) := by positivity
          gcongr
        _ = _ := by ring
    have e3 : Ak ^ 2 * (12 * Real.exp 1 * (d.W N : ℝ) ^ ε * (N : ℝ) ^ ε
          * ((N : ℝ) ^ ε * ((band d).ell N (time s t Kf N j) / ℓs) ^ 2) * Aj⁻¹ ^ 2 * ηj⁻¹)
        ≤ 12 * Real.exp 1 * ((N : ℝ) ^ ε) ^ 3 * R ^ 2 * ηj⁻¹ := by
      have hR2 : ((band d).ell N (time s t Kf N j) / ℓs) ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ hRj0 hRj 2
      calc Ak ^ 2 * (12 * Real.exp 1 * (d.W N : ℝ) ^ ε * (N : ℝ) ^ ε
            * ((N : ℝ) ^ ε * ((band d).ell N (time s t Kf N j) / ℓs) ^ 2) * Aj⁻¹ ^ 2 * ηj⁻¹)
          = 12 * Real.exp 1 * (d.W N : ℝ) ^ ε * (N : ℝ) ^ ε * (N : ℝ) ^ ε
            * ((band d).ell N (time s t Kf N j) / ℓs) ^ 2 * (Ak ^ 2 * Aj⁻¹ ^ 2) * ηj⁻¹ := by ring
        _ ≤ 12 * Real.exp 1 * (N : ℝ) ^ ε * (N : ℝ) ^ ε * (N : ℝ) ^ ε * R ^ 2 * 1 * ηj⁻¹ := by
          gcongr
        _ = 12 * Real.exp 1 * ((N : ℝ) ^ ε) ^ 3 * R ^ 2 * ηj⁻¹ := by ring
    have e4 : Ak ^ 2 * (12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε
          * (d.W N : ℝ) ^ (-D₀) * Aj⁻¹)
        ≤ 12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε * (d.W N : ℝ) ^ (-D₀) * N := by
      calc Ak ^ 2 * (12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε
            * (d.W N : ℝ) ^ (-D₀) * Aj⁻¹)
          = 12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε * (d.W N : ℝ) ^ (-D₀)
            * (Ak ^ 2 * Aj⁻¹) := by ring
        _ ≤ _ := by
          have := (Nat.cast_nonneg (d.L N) : (0 : ℝ) ≤ d.L N)
          gcongr
    have hsplit : Ak ^ 2 * (CU κ ^ 2 * (6 * Real.exp 1 * (d.W N : ℝ) ^ ε * J ^ 2 * Aj⁻¹ ^ 3 * ηj⁻¹
        + 6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-D₀) * J * Aj⁻¹ ^ 2
        + 12 * Real.exp 1 * (d.W N : ℝ) ^ ε * (N : ℝ) ^ ε
            * ((N : ℝ) ^ ε * ((band d).ell N (time s t Kf N j) / ℓs) ^ 2) * Aj⁻¹ ^ 2 * ηj⁻¹
        + 12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε * (d.W N : ℝ) ^ (-D₀) * Aj⁻¹))
        = CU κ ^ 2 * (Ak ^ 2 * (6 * Real.exp 1 * (d.W N : ℝ) ^ ε * J ^ 2 * Aj⁻¹ ^ 3 * ηj⁻¹))
          + CU κ ^ 2 * (Ak ^ 2 * (6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2
              * (d.W N : ℝ) ^ (-D₀) * J * Aj⁻¹ ^ 2))
          + CU κ ^ 2 * (Ak ^ 2 * (12 * Real.exp 1 * (d.W N : ℝ) ^ ε * (N : ℝ) ^ ε
            * ((N : ℝ) ^ ε * ((band d).ell N (time s t Kf N j) / ℓs) ^ 2) * Aj⁻¹ ^ 2 * ηj⁻¹))
          + CU κ ^ 2 * (Ak ^ 2 * (12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε
            * (d.W N : ℝ) ^ (-D₀) * Aj⁻¹)) := by ring
    rw [hsplit]
    have f1 := mul_le_mul_of_nonneg_left e1 hCU2
    have f2 := mul_le_mul_of_nonneg_left e2 hCU2
    have f3 := mul_le_mul_of_nonneg_left e3 hCU2
    have f4 := mul_le_mul_of_nonneg_left e4 hCU2
    have hαe : α * ηj⁻¹ = CU κ ^ 2 * (6 * Real.exp 1 * (N : ℝ) ^ ε * m ^ 2 * At⁻¹ * ηj⁻¹)
        + CU κ ^ 2 * (12 * Real.exp 1 * ((N : ℝ) ^ ε) ^ 3 * R ^ 2 * ηj⁻¹) := by
      rw [hαdef]; ring
    rw [hαe, hβdef]
    linarith
  -- sum up
  have hsum' : ∑ j ∈ range k, Δ * (etaT E (time s t Kf N j))⁻¹ ≤ (mE E).im⁻¹ * Real.log N := by
    refine le_trans ?_ hsum
    have hsub : ∑ j ∈ range k, Δ * (etaT E (time s t Kf N j))⁻¹
        ≤ ∑ j ∈ range (Kf N), Δ * (etaT E (time s t Kf N j))⁻¹ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) fun j hj _ => ?_
      have hj1 : time s t Kf N j < 1 := time_lt_one_pp hst ht1 hK0 (Finset.mem_range.mp hj).le
      exact mul_nonneg hΔ0 (inv_nonneg.2 (etaT_pos_of_lt_one' hE hj1).le)
    refine hsub.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_eq_mul_inv]
  have hkΔ : (k : ℝ) * Δ ≤ 1 := by
    refine le_trans ?_ hKΔ
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hΔ0
  have hβle : β ≤ 2 := by rw [hβdef]; linarith
  have hβ0 : 0 ≤ β := by
    rw [hβdef]
    have := sq_nonneg (d.L N : ℝ)
    have hL0 : (0 : ℝ) ≤ d.L N := Nat.cast_nonneg _
    have hBkN : 0 ≤ (N : ℝ) ^ 2 + Bk := by positivity
    positivity
  have hα0 : 0 ≤ α := by
    rw [hαdef]
    have := inv_nonneg.2 hAt0.le
    positivity
  calc Ak ^ 2 * (Δ * ∑ j ∈ range k, CU κ ^ 2 * dPP d E s t Kf N ε D₀ ℓs j ω)
      = ∑ j ∈ range k, Δ * (Ak ^ 2 * (CU κ ^ 2 * dPP d E s t Kf N ε D₀ ℓs j ω)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j ∈ range k, Δ * (α * (etaT E (time s t Kf N j))⁻¹ + β) :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hper j hj) hΔ0
    _ = α * ∑ j ∈ range k, Δ * (etaT E (time s t Kf N j))⁻¹ + β * ((k : ℝ) * Δ) := by
        have e : ∑ j ∈ range k, Δ * (α * (etaT E (time s t Kf N j))⁻¹ + β)
            = ∑ j ∈ range k, (α * (Δ * (etaT E (time s t Kf N j))⁻¹) + β * Δ) :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        ring
    _ ≤ α * ((mE E).im⁻¹ * Real.log N) + β * 1 := by gcongr
    _ ≤ _ := by
        rw [hαdef]
        have e : (6 * Real.exp 1 * CU κ ^ 2 * (N : ℝ) ^ ε * m ^ 2 * At⁻¹
            + 12 * Real.exp 1 * CU κ ^ 2 * ((N : ℝ) ^ ε) ^ 3 * R ^ 2)
            * ((mE E).im⁻¹ * Real.log N)
            = 6 * Real.exp 1 * CU κ ^ 2 * (N : ℝ) ^ ε * m ^ 2 * ((mE E).im⁻¹ * Real.log N) / At
              + 12 * Real.exp 1 * CU κ ^ 2 * ((N : ℝ) ^ ε) ^ 3 * R ^ 2
                * ((mE E).im⁻¹ * Real.log N) := by
          field_simp
        rw [e]
        linarith

/-- `Σ_{j<K} Δ/η_{u_{j+1}} ≤ Σ_{j<K} Δ/η_{u_j} + Δ/η_t` (right endpoints). -/
theorem sum_step_eta_succ_le {E : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N)
    (ht1 : t N < 1) (hK0 : Kf N ≠ 0) :
    ∑ j ∈ range (Kf N), step s t Kf N * (etaT E (time s t Kf N (j + 1)))⁻¹
      ≤ ∑ j ∈ range (Kf N), step s t Kf N / etaT E (time s t Kf N j)
        + step s t Kf N * (etaT E (t N))⁻¹ := by
  have hΔ0 := step_nonneg' s t Kf N hst
  have h := Finset.sum_range_succ' (fun j => step s t Kf N * (etaT E (time s t Kf N j))⁻¹) (Kf N)
  have h2 := Finset.sum_range_succ (fun j => step s t Kf N * (etaT E (time s t Kf N j))⁻¹) (Kf N)
  have h0 : 0 ≤ step s t Kf N * (etaT E (time s t Kf N 0))⁻¹ := by
    rw [time_zero]
    exact mul_nonneg hΔ0 (inv_nonneg.2 (etaT_pos_of_lt_one' hE (hst.trans_lt ht1)).le)
  have hlast : time s t Kf N (Kf N) = t N := time_last s t Kf N hK0
  have heq : ∑ j ∈ range (Kf N), step s t Kf N / etaT E (time s t Kf N j)
      = ∑ j ∈ range (Kf N), step s t Kf N * (etaT E (time s t Kf N j))⁻¹ :=
    Finset.sum_congr rfl fun j _ => div_eq_mul_inv _ _
  rw [heq]
  rw [hlast] at h2
  linarith

/-- **P2, the martingale term**: `A_k² N^ε (Σ_{j<k} c_j)^{1/2} ≤ N^ε (C_U⁴·24e φ₆ N^ε ℒ′ + 1)^{1/2}`,
`ℒ′ = (Im m)^{-1} log N + 1`, using `A_k ≤ A_{j+1}` (per-target constants). -/
theorem qv_sum_bound {κ : ℝ} (hκ0 : 0 < κ) {E : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s N)
    (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : Kf N ≠ 0) {ε D₂ φ6 : ℝ} (hε : 0 ≤ ε)
    (hφ6 : 0 ≤ φ6) (hWN : (d.W N : ℝ) ≤ N) (hWL : (d.W N : ℝ) * d.L N ≤ N)
    (hηt : (etaT E (t N))⁻¹ ≤ N) (hAt1 : 1 ≤ (band d).scale E N (t N))
    (hsum : ∑ j ∈ range (Kf N), step s t Kf N / etaT E (time s t Kf N j)
      ≤ (mE E).im⁻¹ * Real.log N)
    (hKΔ : (Kf N : ℝ) * step s t Kf N ≤ 1) (hΔN : step s t Kf N * N ≤ 1)
    (hqvtail : (CU κ ^ 2) ^ 2 * (4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D₂))
      * (N : ℝ) ^ 4 ≤ 1)
    {k : ℕ} (hk : k ≤ Kf N) :
    (band d).scale E N (time s t Kf N k) ^ 2
        * ((N : ℝ) ^ ε * Real.sqrt (∑ j ∈ range k, (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ)))
      ≤ (N : ℝ) ^ ε * Real.sqrt ((CU κ ^ 2) ^ 2 * (24 * Real.exp 1 * φ6 * (N : ℝ) ^ ε)
          * ((mE E).im⁻¹ * Real.log N + 1) + 1) := by
  set Δ := step s t Kf N with hΔdef
  set Ak := (band d).scale E N (time s t Kf N k) with hAkdef
  have hΔ0 : 0 ≤ Δ := step_nonneg' s t Kf N hst
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ d.L N := Nat.cast_nonneg _
  have hNε0 : 0 ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hWε : (d.W N : ℝ) ^ ε ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow hW0 hWN hε
  have hWε0 : 0 ≤ (d.W N : ℝ) ^ ε := Real.rpow_nonneg hW0 _
  have hWD0 : 0 ≤ (d.W N : ℝ) ^ (-D₂) := Real.rpow_nonneg hW0 _
  have hC4 : 0 ≤ (CU κ ^ 2) ^ 2 := sq_nonneg _
  have hηt0 : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE ht1
  have hk0 : 0 ≤ time s t Kf N k := time_nonneg_pp hs0 hst k
  have hk1 : time s t Kf N k < 1 := time_lt_one_pp hst ht1 hK0 hk
  have hAk0 : 0 < Ak := (band d).scale_pos' hE N hk0 hk1
  have hAkN : Ak ≤ N := scale_le_N_pp hE hWL hk0 hk1
  have hper : ∀ j ∈ range k, Ak ^ 4 * (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ)
      ≤ (CU κ ^ 2) ^ 2 * (24 * Real.exp 1 * φ6 * (N : ℝ) ^ ε)
          * (Δ * (etaT E (time s t Kf N (j + 1)))⁻¹)
        + (CU κ ^ 2) ^ 2 * (4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D₂)) * (N : ℝ) ^ 4
          * Δ := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hw0 : 0 ≤ time s t Kf N (j + 1) := time_nonneg_pp hs0 hst _
    have hw1 : time s t Kf N (j + 1) < 1 := time_lt_one_pp hst ht1 hK0 (by omega)
    have hwt : time s t Kf N (j + 1) ≤ t N := time_le_t_pp hst hK0 (by omega)
    set Aw := (band d).scale E N (time s t Kf N (j + 1)) with hAwdef
    have hAw0 : 0 < Aw := (band d).scale_pos' hE N hw0 hw1
    have hAkw : Ak ≤ Aw := scale_anti_pp (time_mono_of_le hst (by omega)) hk1
    have hηw := inv_nonneg.2 (etaT_pos_of_lt_one' hE hw1).le
    have hEe0 : 0 ≤ eeHermBdPP d N E (time s t Kf N (j + 1)) ε D₂ φ6 := by
      have h1 : 1 ≤ Aw := hAt1.trans (scale_anti_pp hwt ht1)
      have hWτ : 0 ≤ (d.W N : ℝ) ^ ε := hWε0
      unfold eeHermBdPP
      have := inv_nonneg.2 hAw0.le
      have := pow_nonneg this 4
      positivity
    have hc : (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ)
        = Δ * ((CU κ ^ 2) ^ 2 * eeHermBdPP d N E (time s t Kf N (j + 1)) ε D₂ φ6) := by
      unfold cPPnn cPP
      rw [Real.coe_toNNReal _ (by positivity)]
    rw [hc]
    unfold eeHermBdPP
    rw [← hAwdef]
    have r4 : Ak ^ 4 * Aw⁻¹ ^ 4 ≤ 1 := by
      have h1 : Ak ^ 4 * Aw⁻¹ ^ 4 ≤ Aw ^ 4 * Aw⁻¹ ^ 4 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hAk0.le hAkw 4) (by positivity)
      have h2 : Aw ^ 4 * Aw⁻¹ ^ 4 = 1 := by field_simp
      linarith
    have hAk4 : Ak ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ hAk0.le hAkN 4
    have t1 : Ak ^ 4 * (24 * Real.exp 1 * φ6 * (d.W N : ℝ) ^ ε * Aw⁻¹ ^ 4
          * (etaT E (time s t Kf N (j + 1)))⁻¹)
        ≤ 24 * Real.exp 1 * φ6 * (N : ℝ) ^ ε * (etaT E (time s t Kf N (j + 1)))⁻¹ := by
      calc Ak ^ 4 * (24 * Real.exp 1 * φ6 * (d.W N : ℝ) ^ ε * Aw⁻¹ ^ 4
            * (etaT E (time s t Kf N (j + 1)))⁻¹)
          = 24 * Real.exp 1 * φ6 * (d.W N : ℝ) ^ ε * (Ak ^ 4 * Aw⁻¹ ^ 4)
            * (etaT E (time s t Kf N (j + 1)))⁻¹ := by ring
        _ ≤ 24 * Real.exp 1 * φ6 * (N : ℝ) ^ ε * 1 * (etaT E (time s t Kf N (j + 1)))⁻¹ := by
          gcongr
        _ = _ := by ring
    have t2 : Ak ^ 4 * (4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D₂))
        ≤ 4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D₂) * (N : ℝ) ^ 4 := by
      have : 0 ≤ 4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D₂) := by positivity
      nlinarith
    have e : Ak ^ 4 * (Δ * ((CU κ ^ 2) ^ 2 * (24 * Real.exp 1 * φ6 * (d.W N : ℝ) ^ ε * Aw⁻¹ ^ 4
          * (etaT E (time s t Kf N (j + 1)))⁻¹
          + 4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D₂))))
        = Δ * (CU κ ^ 2) ^ 2 * (Ak ^ 4 * (24 * Real.exp 1 * φ6 * (d.W N : ℝ) ^ ε * Aw⁻¹ ^ 4
          * (etaT E (time s t Kf N (j + 1)))⁻¹))
          + Δ * (CU κ ^ 2) ^ 2 * (Ak ^ 4 * (4 * (d.W N : ℝ) * (d.L N : ℝ)
            * (d.W N : ℝ) ^ (-D₂))) := by ring
    rw [e]
    have hΔC : 0 ≤ Δ * (CU κ ^ 2) ^ 2 := mul_nonneg hΔ0 hC4
    have f1 := mul_le_mul_of_nonneg_left t1 hΔC
    have f2 := mul_le_mul_of_nonneg_left t2 hΔC
    have e2 : (CU κ ^ 2) ^ 2 * (24 * Real.exp 1 * φ6 * (N : ℝ) ^ ε)
          * (Δ * (etaT E (time s t Kf N (j + 1)))⁻¹)
        = Δ * (CU κ ^ 2) ^ 2 * (24 * Real.exp 1 * φ6 * (N : ℝ) ^ ε
          * (etaT E (time s t Kf N (j + 1)))⁻¹) := by ring
    have e3 : (CU κ ^ 2) ^ 2 * (4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D₂))
          * (N : ℝ) ^ 4 * Δ
        = Δ * (CU κ ^ 2) ^ 2 * (4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D₂)
          * (N : ℝ) ^ 4) := by ring
    rw [e2, e3]
    linarith
  -- the sum of the right endpoints
  have hsucc := sum_step_eta_succ_le (s := s) (t := t) (N := N) (Kf := Kf) hE hs0 hst ht1 hK0
  have hsum1 : ∑ j ∈ range k, Δ * (etaT E (time s t Kf N (j + 1)))⁻¹
      ≤ (mE E).im⁻¹ * Real.log N + 1 := by
    have hsub : ∑ j ∈ range k, Δ * (etaT E (time s t Kf N (j + 1)))⁻¹
        ≤ ∑ j ∈ range (Kf N), Δ * (etaT E (time s t Kf N (j + 1)))⁻¹ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) fun j hj _ => ?_
      have hw1 : time s t Kf N (j + 1) < 1 :=
        time_lt_one_pp hst ht1 hK0 (by have := Finset.mem_range.mp hj; omega)
      exact mul_nonneg hΔ0 (inv_nonneg.2 (etaT_pos_of_lt_one' hE hw1).le)
    have hlast : Δ * (etaT E (t N))⁻¹ ≤ 1 := by
      calc Δ * (etaT E (t N))⁻¹ ≤ Δ * N := mul_le_mul_of_nonneg_left hηt hΔ0
        _ ≤ 1 := hΔN
    linarith
  have hkΔ : (k : ℝ) * Δ ≤ 1 := by
    refine le_trans ?_ hKΔ
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hΔ0
  have hS0 : 0 ≤ ∑ j ∈ range k, (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ) :=
    Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  have hSbound : Ak ^ 4 * ∑ j ∈ range k, (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ)
      ≤ (CU κ ^ 2) ^ 2 * (24 * Real.exp 1 * φ6 * (N : ℝ) ^ ε)
          * ((mE E).im⁻¹ * Real.log N + 1) + 1 := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hper).trans ?_
    rw [Finset.sum_add_distrib]
    have hQ0 : 0 ≤ (CU κ ^ 2) ^ 2 * (24 * Real.exp 1 * φ6 * (N : ℝ) ^ ε) := by positivity
    have hT0 : 0 ≤ (CU κ ^ 2) ^ 2 * (4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D₂))
        * (N : ℝ) ^ 4 := by positivity
    have e1 : ∑ j ∈ range k, (CU κ ^ 2) ^ 2 * (24 * Real.exp 1 * φ6 * (N : ℝ) ^ ε)
          * (Δ * (etaT E (time s t Kf N (j + 1)))⁻¹)
        = (CU κ ^ 2) ^ 2 * (24 * Real.exp 1 * φ6 * (N : ℝ) ^ ε)
          * ∑ j ∈ range k, Δ * (etaT E (time s t Kf N (j + 1)))⁻¹ := (Finset.mul_sum _ _ _).symm
    have e2 : ∑ j ∈ range k, (CU κ ^ 2) ^ 2 * (4 * (d.W N : ℝ) * (d.L N : ℝ)
          * (d.W N : ℝ) ^ (-D₂)) * (N : ℝ) ^ 4 * Δ
        = (CU κ ^ 2) ^ 2 * (4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D₂))
          * (N : ℝ) ^ 4 * ((k : ℝ) * Δ) := by
      rw [← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [e1, e2]
    have f1 := mul_le_mul_of_nonneg_left hsum1 hQ0
    have f2 := mul_le_mul_of_nonneg_left hkΔ hT0
    linarith
  have hsq : Ak ^ 2 * Real.sqrt (∑ j ∈ range k, (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ))
      = Real.sqrt (Ak ^ 4 * ∑ j ∈ range k, (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ)) := by
    rw [Real.sqrt_mul (by positivity), show Ak ^ 4 = (Ak ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  calc Ak ^ 2 * ((N : ℝ) ^ ε
        * Real.sqrt (∑ j ∈ range k, (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ)))
      = (N : ℝ) ^ ε * (Ak ^ 2
          * Real.sqrt (∑ j ∈ range k, (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ))) := by ring
    _ = (N : ℝ) ^ ε
          * Real.sqrt (Ak ^ 4 * ∑ j ∈ range k, (cPPnn d κ E s t Kf N ε D₂ φ6 j : ℝ)) := by
        rw [hsq]
    _ ≤ _ := by gcongr

/-- The elementary square-root bound of the martingale term:
`(c²·24e(n x² + 1) n ℒ + 1)^{1/2} ≤ 9 c n (x + 1) ℒ + 1` for `n, ℒ ≥ 1`, `c, x ≥ 0`. -/
theorem sqrt_qv_le {c n x Lg : ℝ} (hc : 0 ≤ c) (hn : 1 ≤ n) (hx : 0 ≤ x) (hL : 1 ≤ Lg) :
    Real.sqrt (c ^ 2 * (24 * Real.exp 1 * (n * x ^ 2 + 1) * n) * Lg + 1)
      ≤ 9 * c * n * (x + 1) * Lg + 1 := by
  have he3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; linarith
  have hY0 : 0 ≤ 9 * c * n * (x + 1) * Lg + 1 := by
    have : 0 ≤ n := by linarith
    have : 0 ≤ Lg := by linarith
    positivity
  rw [Real.sqrt_le_left hY0]
  have hn0 : 0 ≤ n := by linarith
  have hL0 : 0 ≤ Lg := by linarith
  have h1 : n * x ^ 2 + 1 ≤ n * (x ^ 2 + 1) := by nlinarith
  have h2 : c ^ 2 * (24 * Real.exp 1 * (n * x ^ 2 + 1) * n) * Lg
      ≤ c ^ 2 * (72 * (n * (x ^ 2 + 1)) * n) * Lg := by
    have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
    have h3 : 24 * Real.exp 1 * (n * x ^ 2 + 1) ≤ 72 * (n * (x ^ 2 + 1)) := by
      have : 0 ≤ n * x ^ 2 + 1 := by positivity
      nlinarith
    gcongr
  have h4 : c ^ 2 * (72 * (n * (x ^ 2 + 1)) * n) * Lg
      ≤ (9 * c * n * (x + 1) * Lg) ^ 2 := by
    have hxx : x ^ 2 + 1 ≤ (x + 1) ^ 2 := by nlinarith
    have hLL : Lg ≤ Lg ^ 2 := by nlinarith
    have e : (9 * c * n * (x + 1) * Lg) ^ 2 = 81 * (c ^ 2 * n ^ 2) * ((x + 1) ^ 2 * Lg ^ 2) := by
      ring
    rw [e]
    have e2 : c ^ 2 * (72 * (n * (x ^ 2 + 1)) * n) * Lg = 72 * (c ^ 2 * n ^ 2) * ((x ^ 2 + 1) * Lg) := by
      ring
    rw [e2]
    have hcn : 0 ≤ c ^ 2 * n ^ 2 := by positivity
    have hm : (x ^ 2 + 1) * Lg ≤ (x + 1) ^ 2 * Lg ^ 2 :=
      mul_le_mul hxx hLL hL0 (by positivity)
    have hm0 : 0 ≤ (x ^ 2 + 1) * Lg := by positivity
    nlinarith
  have h5 : 0 ≤ 9 * c * n * (x + 1) * Lg := by positivity
  nlinarith

/-- **P3, the remainder term**: `A_k² Σ_{j<k}(1+(1−u_k)^{-1})² errPP_j ≤ 1`. -/
theorem R_sum_bound {E : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hK0 : Kf N ≠ 0) {Bk : ℝ} (hBk0 : 0 ≤ Bk) (hN1 : (1 : ℝ) ≤ N)
    (hWL : (d.W N : ℝ) * d.L N ≤ N) (hηt : (etaT E (t N))⁻¹ ≤ N)
    (hKΔ : (Kf N : ℝ) * step s t Kf N ≤ 1) (hΔ1 : step s t Kf N ≤ 1)
    (hRt : (N : ℝ) ^ 2 * (1 + N) ^ 2 * (2 ^ 17 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4)
      * step s t Kf N ^ (1 / 2 : ℝ) ≤ 1)
    {k : ℕ} (hk : k ≤ Kf N) :
    (band d).scale E N (time s t Kf N k) ^ 2
        * ∑ j ∈ range k, (1 + (1 - time s t Kf N k)⁻¹) ^ 2 * errPP d E s t Kf N Bk j ≤ 1 := by
  set Δ := step s t Kf N with hΔdef
  have hΔ0 : 0 ≤ Δ := step_nonneg' s t Kf N hst
  have hm0 := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hηt0 : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE ht1
  have hk0 : 0 ≤ time s t Kf N k := time_nonneg_pp hs0 hst k
  have hk1 : time s t Kf N k < 1 := time_lt_one_pp hst ht1 hK0 hk
  have hkt : time s t Kf N k ≤ t N := time_le_t_pp hst hK0 hk
  have hAk0 : 0 < (band d).scale E N (time s t Kf N k) := (band d).scale_pos' hE N hk0 hk1
  have hAkN := scale_le_N_pp hE hWL hk0 hk1
  set C : ℝ := 2 ^ 17 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4 with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hinvN : ∀ u, u ≤ t N → (1 - u)⁻¹ ≤ N := by
    intro u hu
    have h1u : 0 < 1 - u := by linarith
    have hη : etaT E (t N) ≤ (1 - u) * (mE E).im := etaT_le_of_le hE hu
    have h2 : ((1 - u) * (mE E).im)⁻¹ ≤ N := (inv_anti₀ hηt0 hη).trans hηt
    refine le_trans ?_ h2
    rw [mul_inv]
    exact le_mul_of_one_le_right (inv_nonneg.2 h1u.le) (one_le_inv₀ hm0 |>.2 hm1)
  have herr : ∀ j ∈ range k, errPP d E s t Kf N Bk j ≤ C * Δ ^ (3 / 2 : ℝ) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hw1 : time s t Kf N (j + 1) < 1 := time_lt_one_pp hst ht1 hK0 (by omega)
    have hwt : time s t Kf N (j + 1) ≤ t N := time_le_t_pp hst hK0 (by omega)
    have hη : ((1 - time s t Kf N (j + 1)) * (mE E).im)⁻¹ ≤ N :=
      (inv_anti₀ hηt0 (etaT_le_of_le hE hwt)).trans hηt
    have h := stepErrN_two_le d hE hN1 hWL hBk0 hΔ0 hΔ1 (time_mono_of_le hst (Nat.le_succ j))
      hw1 hη
    unfold errPP
    exact max_le (by positivity) h
  have hfac : (1 + (1 - time s t Kf N k)⁻¹) ^ 2 ≤ (1 + N) ^ 2 := by
    have h := hinvN _ hkt
    have h0 : 0 ≤ (1 - time s t Kf N k)⁻¹ := inv_nonneg.2 (by linarith)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h32 : Δ ^ (3 / 2 : ℝ) = Δ * Δ ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hΔ0 (by norm_num),
      Real.rpow_one]
  have hsum : ∑ j ∈ range k, (1 + (1 - time s t Kf N k)⁻¹) ^ 2 * errPP d E s t Kf N Bk j
      ≤ (k : ℝ) * ((1 + N) ^ 2 * (C * Δ ^ (3 / 2 : ℝ))) := by
    have := Finset.sum_le_sum (s := range k) fun j hj =>
      mul_le_mul hfac (herr j hj) (le_max_left _ _) (by positivity)
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have hkΔ : (k : ℝ) * Δ ≤ 1 := by
    refine le_trans ?_ hKΔ
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hΔ0
  have hΔh : 0 ≤ Δ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hΔ0 _
  calc (band d).scale E N (time s t Kf N k) ^ 2
        * ∑ j ∈ range k, (1 + (1 - time s t Kf N k)⁻¹) ^ 2 * errPP d E s t Kf N Bk j
      ≤ (N : ℝ) ^ 2 * ((k : ℝ) * ((1 + N) ^ 2 * (C * Δ ^ (3 / 2 : ℝ)))) := by
        gcongr
        · exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (le_max_left _ _)
    _ = (N : ℝ) ^ 2 * (1 + N) ^ 2 * C * Δ ^ (1 / 2 : ℝ) * ((k : ℝ) * Δ) := by
        rw [h32]; ring
    _ ≤ (N : ℝ) ^ 2 * (1 + N) ^ 2 * C * Δ ^ (1 / 2 : ℝ) * 1 := by gcongr
    _ ≤ 1 := by rw [mul_one]; exact hRt

/-! #### The closure at a fixed `N` (deterministic) -/

/-- `ℒ′ = (Im m)^{-1} log N + 1`. -/
def LgPP (E : ℝ) (N : ℕ) : ℝ := (mE E).im⁻¹ * Real.log N + 1

/-- `R = ℓ_t/ℓ_s`. -/
def RPP (d : Dims) (s t : ℕ → ℝ) (N : ℕ) : ℝ := (band d).ell N (t N) / (band d).ell N (s N)

/-- `φ₆ = N^ε R⁵ + 1` (written with `R⁵ = (R^{5/2})²`). -/
def phi6PP (d : Dims) (ε : ℝ) (s t : ℕ → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ ε * (RPP d s t N ^ (5 / 2 : ℝ)) ^ 2 + 1

/-- The constant `C₀(κ) = 50 C_U(κ)² + 5` (independent of `N`). -/
def C0PP (κ : ℝ) : ℝ := 50 * CU κ ^ 2 + 5

/-- **`c′ = C₀ N^{3ε} (1 + R² + R^{5/2}) ℒ′`.** -/
def cPrimePP (d : Dims) (κ E ε : ℝ) (s t : ℕ → ℝ) (N : ℕ) : ℝ :=
  C0PP κ * ((N : ℝ) ^ ε) ^ 3 * (1 + RPP d s t N ^ 2 + RPP d s t N ^ (5 / 2 : ℝ)) * LgPP E N

theorem RPP_nonneg (d : Dims) (s t : ℕ → ℝ) (N : ℕ) : 0 ≤ RPP d s t N := by
  unfold RPP Band.ell ellHat
  positivity

/-- Arithmetic of the constant part of the closure (clean context). -/
theorem cprime_combine {C2 n R R52 Lg Lraw : ℝ} (hC2 : 0 ≤ C2) (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hR52 : 0 ≤ R52) (hLg : 1 ≤ Lg) (hL0 : 0 ≤ Lraw) (hLL : Lraw ≤ Lg) :
    C2 * n + (12 * Real.exp 1 * C2 * n ^ 3 * R ^ 2 * Lraw + 2)
        + n * (9 * C2 * n * (R52 + 1) * Lg + 1) + 1 + 1
      ≤ (50 * C2 + 5) * n ^ 3 * (1 + R ^ 2 + R52) * Lg := by
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  set P := 1 + R ^ 2 + R52 with hP
  have hn0 : 0 ≤ n := by linarith
  have hn3 : n ≤ n ^ 3 := le_self_pow₀ hn (by norm_num)
  have hn2 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn (by norm_num)
  have hn30 : 0 ≤ n ^ 3 := by positivity
  have hP1 : 1 ≤ P := by rw [hP]; nlinarith [sq_nonneg R]
  have hPL : 1 ≤ P * Lg := by nlinarith
  have hR2 : R ^ 2 ≤ P := by rw [hP]; linarith
  have hR5 : R52 + 1 ≤ P := by rw [hP]; nlinarith [sq_nonneg R]
  set X := n ^ 3 * (P * Lg) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hnX : n ≤ X := by rw [hX]; nlinarith
  have t1 : C2 * n ≤ C2 * X := mul_le_mul_of_nonneg_left hnX hC2
  have t2 : 12 * Real.exp 1 * C2 * n ^ 3 * R ^ 2 * Lraw ≤ 36 * C2 * X := by
    have h1 : R ^ 2 * Lraw ≤ P * Lg := mul_le_mul hR2 hLL hL0 (by linarith)
    have h3 : 0 ≤ R ^ 2 * Lraw := mul_nonneg (sq_nonneg R) hL0
    calc 12 * Real.exp 1 * C2 * n ^ 3 * R ^ 2 * Lraw
        = (12 * Real.exp 1) * (C2 * n ^ 3) * (R ^ 2 * Lraw) := by ring
      _ ≤ 36 * (C2 * n ^ 3) * (P * Lg) := by gcongr; linarith
      _ = 36 * C2 * X := by rw [hX]; ring
  have t3 : n * (9 * C2 * n * (R52 + 1) * Lg + 1) ≤ 9 * C2 * X + X := by
    have h1 : n * (9 * C2 * n * (R52 + 1) * Lg) = 9 * C2 * (n ^ 2 * ((R52 + 1) * Lg)) := by ring
    have h2 : n ^ 2 * ((R52 + 1) * Lg) ≤ X := by
      rw [hX]
      exact mul_le_mul hn2 (mul_le_mul_of_nonneg_right hR5 (by linarith)) (by positivity) hn30
    have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 9 * C2)
    calc n * (9 * C2 * n * (R52 + 1) * Lg + 1)
        = 9 * C2 * (n ^ 2 * ((R52 + 1) * Lg)) + n := by rw [mul_add, h1, mul_one]
      _ ≤ 9 * C2 * X + X := by linarith
  have hgoal : (50 * C2 + 5) * n ^ 3 * P * Lg = 50 * C2 * X + 5 * X := by rw [hX]; ring
  rw [hgoal]
  nlinarith

theorem one_le_cprime {C2 n R R52 Lg : ℝ} (hC2 : 0 ≤ C2) (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hR52 : 0 ≤ R52) (hLg : 1 ≤ Lg) :
    n ≤ (50 * C2 + 5) * n ^ 3 * (1 + R ^ 2 + R52) * Lg := by
  have hn3 : n ≤ n ^ 3 := le_self_pow₀ hn (by norm_num)
  have hP1 : 1 ≤ 1 + R ^ 2 + R52 := by nlinarith [sq_nonneg R]
  have hPL : 1 ≤ (1 + R ^ 2 + R52) * Lg := by nlinarith
  have h5 : 1 ≤ 50 * C2 + 5 := by nlinarith
  have hn30 : 0 ≤ n ^ 3 := by positivity
  calc n ≤ n ^ 3 := hn3
    _ = 1 * n ^ 3 * 1 := by ring
    _ ≤ (50 * C2 + 5) * n ^ 3 * ((1 + R ^ 2 + R52) * Lg) := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- ** The closure at a fixed `N`, with the forbidden zone as a hypothesis.** The forbidden-zone
calc is the binder `hzone' : 4·Cq·c′·ℒ′ ≤ A_t` (`Cq = 6e C_U² N^ε`).
`pp_closure_fixedN_plain` (plain (2.72) pair, zone at `N^{c/4}`, via `pp_zone_plain`) is a
wrapper. -/
theorem pp_closure_fixedN_core {κ : ℝ} (hκ0 : 0 < κ) {E : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s N)
    (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : Kf N ≠ 0) {ε Bk : ℝ} (hε : 0 ≤ ε)
    (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (t N), ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval E N w J‖ ≤ Bk)
    (hN1 : (1 : ℝ) ≤ N) (hWL : (d.W N : ℝ) * d.L N ≤ N) (hWN : (d.W N : ℝ) ≤ N)
    (hηt : (etaT E (t N))⁻¹ ≤ N) (hAt1 : 1 ≤ (band d).scale E N (t N))
    (hsum : ∑ j ∈ range (Kf N), step s t Kf N / etaT E (time s t Kf N j)
      ≤ (mE E).im⁻¹ * Real.log N)
    (hlog : 0 ≤ Real.log N)
    (hKΔ : (Kf N : ℝ) * step s t Kf N ≤ 1) (hΔN : step s t Kf N * N ≤ 1)
    (hΔ1 : step s t Kf N ≤ 1)
    (hX2 : CU κ ^ 2 * (6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-(20 : ℝ))
      * ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk))) ≤ 1)
    (hX4 : CU κ ^ 2 * (12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε
      * (d.W N : ℝ) ^ (-(20 : ℝ)) * N) ≤ 1)
    (hqvtail : (CU κ ^ 2) ^ 2 * (4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-(19 : ℝ)))
      * (N : ℝ) ^ 4 ≤ 1)
    (hRt : (N : ℝ) ^ 2 * (1 + N) ^ 2 * (2 ^ 17 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4)
      * step s t Kf N ^ (1 / 2 : ℝ) ≤ 1)
    (hzone' : 4 * (6 * Real.exp 1 * CU κ ^ 2 * (N : ℝ) ^ ε) * cPrimePP d κ E ε s t N * LgPP E N
      ≤ (band d).scale E N (t N))
    (τ : Ωg d → ℕ) (ω : Ωg d) (hτ : τ ω = Kf N)
    (hJ0 : JPP d E N (time s t Kf N 0) (H d s t Kf N 0 ω) ≤ (N : ℝ) ^ ε)
    (hbd : ∀ k ≤ Kf N, ∀ a : LoopArg (d.L N) 2,
      ‖Ast d E s t Kf N τ k ω a‖
        ≤ CU κ ^ 2 * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖App d E s t Kf N 0 ω b‖))
          + step s t Kf N * ∑ j ∈ range k, CU κ ^ 2
              * dPP d E s t Kf N ε 20 ((band d).ell N (s N)) j ω
          + (N : ℝ) ^ ε * Real.sqrt (∑ j ∈ range k,
              (cPPnn d κ E s t Kf N ε 19 (phi6PP d ε s t N) j : ℝ))
          + (N : ℝ) ^ (-(3 : ℝ))
          + ∑ j ∈ range k, (1 + (1 - time s t Kf N k)⁻¹) ^ 2 * errPP d E s t Kf N Bk j) :
    ∀ k ≤ Kf N, JPP d E N (time s t Kf N k) (H d s t Kf N k ω) ≤ 2 * cPrimePP d κ E ε s t N := by
  set R := RPP d s t N with hRdef
  set Lg := LgPP E N with hLgdef
  set At := (band d).scale E N (t N) with hAtdef
  set Cq : ℝ := 6 * Real.exp 1 * CU κ ^ 2 * (N : ℝ) ^ ε with hCqdef
  set c' := cPrimePP d κ E ε s t N with hc'def
  have hR0 : 0 ≤ R := RPP_nonneg d s t N
  have hm0' := mE_im_pos hE
  have hLg1 : 1 ≤ Lg := by
    rw [hLgdef, LgPP]
    have : 0 ≤ (mE E).im⁻¹ * Real.log N := mul_nonneg (inv_nonneg.2 hm0'.le) hlog
    linarith
  have hℒ : (mE E).im⁻¹ * Real.log N ≤ Lg := by rw [hLgdef, LgPP]; linarith
  have hNε1 : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε
  have hCU := CU_pos hκ0
  have hCU2 : 0 ≤ CU κ ^ 2 := sq_nonneg _
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hAt0 : 0 < At := lt_of_lt_of_le one_pos hAt1
  have hℓs : 0 < (band d).ell N (s N) := lt_of_lt_of_le zero_lt_one
    (one_le_ellHat (d.L N) (d.three_le_L N) hs0 (hst.trans_lt ht1))
  have hRj : ∀ j ≤ Kf N, (band d).ell N (time s t Kf N j) / (band d).ell N (s N) ≤ R := by
    intro j hj
    rw [hRdef, RPP]
    exact div_le_div_of_nonneg_right (RBM.Step3.ellHat_mono (time_le_t_pp hst hK0 hj) ht1) hℓs.le
  have hR52 : 0 ≤ R ^ (5 / 2 : ℝ) := Real.rpow_nonneg hR0 _
  have hφ6 : 0 ≤ phi6PP d ε s t N := by unfold phi6PP; positivity
  have hpos3 : 1 ≤ 1 + R ^ 2 + R ^ (5 / 2 : ℝ) := by nlinarith [sq_nonneg R]
  have hc'0 : 0 ≤ c' := by
    rw [hc'def, cPrimePP, C0PP]; positivity
  -- the constant part of the closure
  have hconst : ∀ k ≤ Kf N, ∀ m : ℝ, 0 ≤ m →
      (∀ j < k, JPP d E N (time s t Kf N j) (H d s t Kf N j ω) ≤ m) →
      JPP d E N (time s t Kf N k) (H d s t Kf N k ω) ≤ c' + Cq * m ^ 2 * Lg / At := by
    intro k hk m hm0 hm
    set Ak := (band d).scale E N (time s t Kf N k) with hAkdef
    have hk0 : 0 ≤ time s t Kf N k := time_nonneg_pp hs0 hst k
    have hk1 : time s t Kf N k < 1 := time_lt_one_pp hst ht1 hK0 hk
    have hAk0 : 0 < Ak := (band d).scale_pos' hE N hk0 hk1
    have hAkN : Ak ≤ N := scale_le_N_pp hE hWL hk0 hk1
    have hAk0s : Ak ≤ (band d).scale E N (time s t Kf N 0) :=
      scale_anti_pp (time_mono_of_le hst (Nat.zero_le k)) hk1
    -- `J_k ≤ A_k² · RHS_k`
    set RHS := CU κ ^ 2 * (Finset.univ.sup' Finset.univ_nonempty
          (fun b => ‖App d E s t Kf N 0 ω b‖))
        + step s t Kf N * ∑ j ∈ range k, CU κ ^ 2
            * dPP d E s t Kf N ε 20 ((band d).ell N (s N)) j ω
        + (N : ℝ) ^ ε * Real.sqrt (∑ j ∈ range k,
            (cPPnn d κ E s t Kf N ε 19 (phi6PP d ε s t N) j : ℝ))
        + (N : ℝ) ^ (-(3 : ℝ))
        + ∑ j ∈ range k, (1 + (1 - time s t Kf N k)⁻¹) ^ 2 * errPP d E s t Kf N Bk j with hRHS
    have hJk : JPP d E N (time s t Kf N k) (H d s t Kf N k ω) ≤ Ak ^ 2 * RHS := by
      rw [JPP_eq_App]
      refine mul_le_mul_of_nonneg_left (Finset.sup'_le _ _ fun a _ => ?_) (sq_nonneg _)
      have h := hbd k hk a
      rwa [Ast_eq_App hE hs0 hst ht1 hK0 τ hτ hk] at h
    refine hJk.trans ?_
    -- P4
    have hM0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖App d E s t Kf N 0 ω b‖) := by
      obtain ⟨b0⟩ := (inferInstance : Nonempty (LoopArg (d.L N) 2))
      exact (norm_nonneg _).trans (Finset.le_sup' (fun b => ‖App d E s t Kf N 0 ω b‖)
        (Finset.mem_univ b0))
    have hP4 : Ak ^ 2 * (CU κ ^ 2 * (Finset.univ.sup' Finset.univ_nonempty
        (fun b => ‖App d E s t Kf N 0 ω b‖))) ≤ CU κ ^ 2 * (N : ℝ) ^ ε := by
      have hJ0' := hJ0
      rw [JPP_eq_App] at hJ0'
      have h1 : Ak ^ 2 * Finset.univ.sup' Finset.univ_nonempty (fun b => ‖App d E s t Kf N 0 ω b‖)
          ≤ (band d).scale E N (time s t Kf N 0) ^ 2
            * Finset.univ.sup' Finset.univ_nonempty (fun b => ‖App d E s t Kf N 0 ω b‖) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hAk0.le hAk0s 2) hM0
      calc Ak ^ 2 * (CU κ ^ 2 * (Finset.univ.sup' Finset.univ_nonempty
            (fun b => ‖App d E s t Kf N 0 ω b‖)))
          = CU κ ^ 2 * (Ak ^ 2 * Finset.univ.sup' Finset.univ_nonempty
            (fun b => ‖App d E s t Kf N 0 ω b‖)) := by ring
        _ ≤ CU κ ^ 2 * (N : ℝ) ^ ε := mul_le_mul_of_nonneg_left (h1.trans hJ0') hCU2
    -- P1
    have hP1 := drift_sum_bound (d := d) (s := s) (t := t) (Kf := Kf) (N := N) hκ0 hE hs0 hst ht1
      hK0 hε hℓs hBk0 hBk hWL hWN hηt hsum hKΔ hX2 hX4 hRj hR0 ω hk hm0 hm
    -- P2
    have hP2 := qv_sum_bound (d := d) (s := s) (t := t) (Kf := Kf) (N := N) hκ0 hE hs0 hst ht1
      hK0 hε hφ6 hWN hWL hηt hAt1 hsum hKΔ hΔN hqvtail hk
    have hsq := sqrt_qv_le (c := CU κ ^ 2) (n := (N : ℝ) ^ ε) (x := R ^ (5 / 2 : ℝ)) (Lg := Lg)
      hCU2 hNε1 hR52 hLg1
    have hP2' : Ak ^ 2 * ((N : ℝ) ^ ε * Real.sqrt (∑ j ∈ range k,
        (cPPnn d κ E s t Kf N ε 19 (phi6PP d ε s t N) j : ℝ)))
        ≤ (N : ℝ) ^ ε * (9 * CU κ ^ 2 * (N : ℝ) ^ ε * (R ^ (5 / 2 : ℝ) + 1) * Lg + 1) := by
      refine hP2.trans (mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) hsq)
        (by positivity))
      congr 1
    -- P3
    have hP3 := R_sum_bound (d := d) (s := s) (t := t) (Kf := Kf) (N := N) hE hs0 hst ht1 hK0
      hBk0 hN1 hWL hηt hKΔ hΔ1 hRt hk
    -- P5
    have hP5 : Ak ^ 2 * (N : ℝ) ^ (-(3 : ℝ)) ≤ 1 := by
      have hN0 : (0 : ℝ) < N := by linarith
      rw [Real.rpow_neg hN0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have h1 : Ak ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hAk0.le hAkN 2
      have h2 : (N : ℝ) ^ 2 * ((N : ℝ) ^ 3)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by positivity)]
        exact pow_le_pow_right₀ hN1 (by norm_num)
      calc Ak ^ 2 * ((N : ℝ) ^ 3)⁻¹ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 3)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ 1 := h2
    -- combine
    have hdist : Ak ^ 2 * RHS
        = Ak ^ 2 * (CU κ ^ 2 * (Finset.univ.sup' Finset.univ_nonempty
            (fun b => ‖App d E s t Kf N 0 ω b‖)))
          + Ak ^ 2 * (step s t Kf N * ∑ j ∈ range k, CU κ ^ 2
            * dPP d E s t Kf N ε 20 ((band d).ell N (s N)) j ω)
          + Ak ^ 2 * ((N : ℝ) ^ ε * Real.sqrt (∑ j ∈ range k,
            (cPPnn d κ E s t Kf N ε 19 (phi6PP d ε s t N) j : ℝ)))
          + Ak ^ 2 * (N : ℝ) ^ (-(3 : ℝ))
          + Ak ^ 2 * ∑ j ∈ range k, (1 + (1 - time s t Kf N k)⁻¹) ^ 2
            * errPP d E s t Kf N Bk j := by
      rw [hRHS]; ring
    rw [hdist]
    -- the quadratic term
    have hq : 6 * Real.exp 1 * CU κ ^ 2 * (N : ℝ) ^ ε * m ^ 2 * ((mE E).im⁻¹ * Real.log N) / At
        ≤ Cq * m ^ 2 * Lg / At := by
      rw [hCqdef]
      have : 0 ≤ 6 * Real.exp 1 * CU κ ^ 2 * (N : ℝ) ^ ε * m ^ 2 := by positivity
      gcongr
    -- the constant terms are bounded by `c′`
    have hN3 : 0 ≤ ((N : ℝ) ^ ε) ^ 3 := by positivity
    have hcon : CU κ ^ 2 * (N : ℝ) ^ ε
          + (12 * Real.exp 1 * CU κ ^ 2 * ((N : ℝ) ^ ε) ^ 3 * R ^ 2
              * ((mE E).im⁻¹ * Real.log N) + 2)
          + (N : ℝ) ^ ε * (9 * CU κ ^ 2 * (N : ℝ) ^ ε * (R ^ (5 / 2 : ℝ) + 1) * Lg + 1)
          + 1 + 1 ≤ c' := by
      rw [hc'def, cPrimePP, C0PP, ← hRdef, ← hLgdef]
      exact cprime_combine hCU2 hNε1 hR0 hR52 hLg1
        (mul_nonneg (inv_nonneg.2 hm0'.le) hlog) hℒ
    linarith [hP4, hP1, hP2', hP3, hP5, hq, hcon]
  -- the strong induction (T2)
  have hCq0 : 0 ≤ Cq := by rw [hCqdef]; positivity
  have hJ0c : JPP d E N (time s t Kf N 0) (H d s t Kf N 0 ω) ≤ c' := by
    refine hJ0.trans ?_
    rw [hc'def, cPrimePP, C0PP, ← hRdef, ← hLgdef]
    exact one_le_cprime hCU2 hNε1 hR0 hR52 hLg1
  exact discrete_bihari hCq0 (by linarith) hAt0 hc'0 hzone' hJ0c hconst

/-- ** The forbidden zone, plain form**:
from the plain fixed-`N` (2.72) pair `r^{30} ≤ A_t`, `N^c ≤ A_t`, `A_t ≥ 1` and the zone
`72e C_U² C₀ ℒ′² ≤ N^{c/4}`,
`4·Cq·c′·ℒ′ = X N^{4ε} P ≤ 3X·N^{c/2} r^{5/4} ≤ N^{c/4}N^{c/2} r^{5/4} = (N^c)^{3/4}(r^{30})^{1/24}
≤ A_t^{3/4}A_t^{1/24} = A_t^{19/24} ≤ A_t` (`P = 1 + R² + R^{5/2} ≤ 3r^{5/4}`, `4ε ≤ c/2`).
Exponent check: `3/4 + (5/4)/30 = 19/24 < 1`, slack `A_t^{5/24}`. -/
theorem pp_zone_plain {κ : ℝ} {E : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N)
    (ht1 : t N < 1) {ε c : ℝ} (hε : 0 ≤ ε) (hεc : 4 * ε ≤ c / 2) (hN1 : (1 : ℝ) ≤ N)
    (hlog : 0 ≤ Real.log N) (hAt1 : 1 ≤ (band d).scale E N (t N))
    (hreg0 : (etaT E (s N) / etaT E (t N)) ^ 30 ≤ (band d).scale E N (t N))
    (hAc : (N : ℝ) ^ c ≤ (band d).scale E N (t N))
    (hzone : 72 * Real.exp 1 * CU κ ^ 2 * C0PP κ * LgPP E N ^ 2 ≤ (N : ℝ) ^ (c / 4)) :
    4 * (6 * Real.exp 1 * CU κ ^ 2 * (N : ℝ) ^ ε) * cPrimePP d κ E ε s t N * LgPP E N
      ≤ (band d).scale E N (t N) := by
  set R := RPP d s t N with hRdef
  set Lg := LgPP E N with hLgdef
  set At := (band d).scale E N (t N) with hAtdef
  have hR0 : 0 ≤ R := RPP_nonneg d s t N
  have hm0' := mE_im_pos hE
  have hLg1 : 1 ≤ Lg := by
    rw [hLgdef, LgPP]
    have : 0 ≤ (mE E).im⁻¹ * Real.log N := mul_nonneg (inv_nonneg.2 hm0'.le) hlog
    linarith
  have hNε1 : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε
  have hCU2 : 0 ≤ CU κ ^ 2 := sq_nonneg _
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hℓs : 0 < (band d).ell N (s N) := lt_of_lt_of_le zero_lt_one
    (one_le_ellHat (d.L N) (d.three_le_L N) hs0 (hst.trans_lt ht1))
  rw [cPrimePP, ← hRdef, ← hLgdef]
  set r := etaT E (s N) / etaT E (t N) with hrdef
  have hηt0 : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE ht1
  have hηs : etaT E (t N) ≤ etaT E (s N) := etaT_le_of_le hE hst
  have hr1 : 1 ≤ r := (one_le_div₀ hηt0).mpr hηs
  have hr0 : 0 ≤ r := by linarith
  -- `R ≤ r^{1/2}`
  have hRr : R ≤ Real.sqrt r := by
    rw [hRdef, RPP, div_le_iff₀ hℓs]
    have h := RBM.Step3.ellHat_le_sqrt_mul (L := d.L N) hst ht1
    have hr' : r = (1 - s N) / (1 - t N) := by
      rw [hrdef]
      show (1 - s N) * (mE E).im / ((1 - t N) * (mE E).im) = _
      field_simp
    rw [hr']; exact h
  have hsr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0
  have hR2 : R ^ 2 ≤ r := by
    calc R ^ 2 ≤ Real.sqrt r ^ 2 := pow_le_pow_left₀ hR0 hRr 2
      _ = r := hsr
  have hR52' : R ^ (5 / 2 : ℝ) ≤ r ^ (5 / 4 : ℝ) := by
    calc R ^ (5 / 2 : ℝ) ≤ Real.sqrt r ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow hR0 hRr (by norm_num)
      _ = r ^ (5 / 4 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr0]; norm_num
  -- `P = 1 + R² + R^{5/2} ≤ 3 r^{5/4}` (instead of the cruder `≤ 3 r^{30}`)
  have hr_54 : r ≤ r ^ (5 / 4 : ℝ) := by
    calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
      _ ≤ r ^ (5 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
  have hone54 : (1 : ℝ) ≤ r ^ (5 / 4 : ℝ) := Real.one_le_rpow hr1 (by norm_num)
  have hP3 : 1 + R ^ 2 + R ^ (5 / 2 : ℝ) ≤ 3 * r ^ (5 / 4 : ℝ) := by linarith
  -- the interpolation `(N^c)^{3/4}(r^{30})^{1/24} ≤ A_t`
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hA0 : 0 < At := by linarith
  have hn4 : ((N : ℝ) ^ ε) ^ 4 ≤ (N : ℝ) ^ (c / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hNc34 : (N : ℝ) ^ (3 * c / 4) ≤ At ^ ((3 : ℝ) / 4) := by
    rw [show 3 * c / 4 = c * (3 / 4) by ring, Real.rpow_mul hN0]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hAc (by norm_num)
  have hr54 : r ^ (5 / 4 : ℝ) ≤ At ^ ((1 : ℝ) / 24) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ r ^ (30 : ℕ)) hreg0
      (show (0 : ℝ) ≤ 1 / 24 by norm_num)
    rwa [← Real.rpow_natCast r 30, ← Real.rpow_mul hr0, show ((30 : ℕ) : ℝ) * (1 / 24) = 5 / 4 by
      norm_num] at h
  have hsplit : (N : ℝ) ^ (3 * c / 4) = (N : ℝ) ^ (c / 4) * (N : ℝ) ^ (c / 2) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  -- the final normalisation: `A_t^{3/4} A_t^{1/24} = A_t^{19/24} ≤ A_t` (slack `A_t^{5/24}`)
  have h1924 : At ^ ((3 : ℝ) / 4) * At ^ ((1 : ℝ) / 24) ≤ At := by
    rw [← Real.rpow_add hA0]
    calc At ^ ((3 : ℝ) / 4 + 1 / 24) ≤ At ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hAt1 (by norm_num)
      _ = At := Real.rpow_one At
  have hr54_0 : 0 ≤ r ^ (5 / 4 : ℝ) := Real.rpow_nonneg hr0 _
  have hNε0 : 0 ≤ (N : ℝ) ^ ε := by linarith
  have hLg0 : 0 ≤ Lg := by linarith
  have hC00 : 0 ≤ C0PP κ := by unfold C0PP; positivity
  have hA34 : 0 ≤ At ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hA0.le _
  calc 4 * (6 * Real.exp 1 * CU κ ^ 2 * (N : ℝ) ^ ε)
        * (C0PP κ * ((N : ℝ) ^ ε) ^ 3 * (1 + R ^ 2 + R ^ (5 / 2 : ℝ)) * Lg) * Lg
      = (24 * Real.exp 1 * CU κ ^ 2 * C0PP κ * Lg ^ 2) * ((N : ℝ) ^ ε) ^ 4
        * (1 + R ^ 2 + R ^ (5 / 2 : ℝ)) := by ring
    _ ≤ (24 * Real.exp 1 * CU κ ^ 2 * C0PP κ * Lg ^ 2) * (N : ℝ) ^ (c / 2)
        * (3 * r ^ (5 / 4 : ℝ)) := by gcongr
    _ = (72 * Real.exp 1 * CU κ ^ 2 * C0PP κ * LgPP E N ^ 2) * (N : ℝ) ^ (c / 2)
        * r ^ (5 / 4 : ℝ) := by rw [hLgdef]; ring
    _ ≤ (N : ℝ) ^ (c / 4) * (N : ℝ) ^ (c / 2) * r ^ (5 / 4 : ℝ) := by gcongr
    _ = (N : ℝ) ^ (3 * c / 4) * r ^ (5 / 4 : ℝ) := by rw [hsplit]
    _ ≤ At ^ ((3 : ℝ) / 4) * At ^ ((1 : ℝ) / 24) := by gcongr
    _ ≤ At := h1924

/-- ** `pp_closure_fixedN_plain`**: the closure at a fixed `N` from the plain (2.72) pair
`hreg0 : r^{30} ≤ A_t`, `hAc : N^c ≤ A_t`, with the zone exponent `c/4`. Proof:
`pp_closure_fixedN_core` + `pp_zone_plain`. -/
theorem pp_closure_fixedN_plain {κ : ℝ} (hκ0 : 0 < κ) {E : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s N)
    (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : Kf N ≠ 0) {ε c Bk : ℝ} (hε : 0 ≤ ε)
    (hεc : 4 * ε ≤ c / 2) (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (t N), ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval E N w J‖ ≤ Bk)
    (hN1 : (1 : ℝ) ≤ N) (hWL : (d.W N : ℝ) * d.L N ≤ N) (hWN : (d.W N : ℝ) ≤ N)
    (hηt : (etaT E (t N))⁻¹ ≤ N) (hAt1 : 1 ≤ (band d).scale E N (t N))
    (hreg0 : (etaT E (s N) / etaT E (t N)) ^ 30 ≤ (band d).scale E N (t N))
    (hAc : (N : ℝ) ^ c ≤ (band d).scale E N (t N))
    (hsum : ∑ j ∈ range (Kf N), step s t Kf N / etaT E (time s t Kf N j)
      ≤ (mE E).im⁻¹ * Real.log N)
    (hlog : 0 ≤ Real.log N)
    (hKΔ : (Kf N : ℝ) * step s t Kf N ≤ 1) (hΔN : step s t Kf N * N ≤ 1)
    (hΔ1 : step s t Kf N ≤ 1)
    (hX2 : CU κ ^ 2 * (6 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-(20 : ℝ))
      * ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + Bk))) ≤ 1)
    (hX4 : CU κ ^ 2 * (12 * Real.exp 1 * (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε
      * (d.W N : ℝ) ^ (-(20 : ℝ)) * N) ≤ 1)
    (hqvtail : (CU κ ^ 2) ^ 2 * (4 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-(19 : ℝ)))
      * (N : ℝ) ^ 4 ≤ 1)
    (hRt : (N : ℝ) ^ 2 * (1 + N) ^ 2 * (2 ^ 17 * (N : ℝ) ^ 15 * (1 + Bk) ^ 4)
      * step s t Kf N ^ (1 / 2 : ℝ) ≤ 1)
    (hzone : 72 * Real.exp 1 * CU κ ^ 2 * C0PP κ * LgPP E N ^ 2 ≤ (N : ℝ) ^ (c / 4))
    (τ : Ωg d → ℕ) (ω : Ωg d) (hτ : τ ω = Kf N)
    (hJ0 : JPP d E N (time s t Kf N 0) (H d s t Kf N 0 ω) ≤ (N : ℝ) ^ ε)
    (hbd : ∀ k ≤ Kf N, ∀ a : LoopArg (d.L N) 2,
      ‖Ast d E s t Kf N τ k ω a‖
        ≤ CU κ ^ 2 * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖App d E s t Kf N 0 ω b‖))
          + step s t Kf N * ∑ j ∈ range k, CU κ ^ 2
              * dPP d E s t Kf N ε 20 ((band d).ell N (s N)) j ω
          + (N : ℝ) ^ ε * Real.sqrt (∑ j ∈ range k,
              (cPPnn d κ E s t Kf N ε 19 (phi6PP d ε s t N) j : ℝ))
          + (N : ℝ) ^ (-(3 : ℝ))
          + ∑ j ∈ range k, (1 + (1 - time s t Kf N k)⁻¹) ^ 2 * errPP d E s t Kf N Bk j) :
    ∀ k ≤ Kf N, JPP d E N (time s t Kf N k) (H d s t Kf N k ω) ≤ 2 * cPrimePP d κ E ε s t N :=
  pp_closure_fixedN_core hκ0 hE hs0 hst ht1 hK0 hε hBk0 hBk hN1 hWL hWN hηt hAt1 hsum hlog hKΔ hΔN
    hΔ1 hX2 hX4 hqvtail hRt
    (pp_zone_plain hE hs0 hst ht1 hε hεc hN1 hlog hAt1 hreg0 hAc hzone) τ ω hτ hJ0 hbd

/-! #### Asymptotic (`∀ᶠ N`) helpers -/

theorem ev_natpow (C : ℝ) {p q : ℕ} (hpq : p < q) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ p ≤ (N : ℝ) ^ q := by
  filter_upwards [eventually_const_mul_rpow_le_rpow C (show (p : ℝ) < q by exact_mod_cast hpq)]
    with N h
  simpa [Real.rpow_natCast] using h

/-- The grid size `K_N = max(1, ⌈N^{D₁+100}⌉)`, **chosen after `D₁`**. -/
def KPP (D₁ : ℝ) (N : ℕ) : ℕ := max 1 ⌈(N : ℝ) ^ (D₁ + 100)⌉₊

theorem KPP_ne_zero (D₁ : ℝ) (N : ℕ) : KPP D₁ N ≠ 0 := by
  unfold KPP; omega

theorem KPP_ge (D₁ : ℝ) (N : ℕ) : (N : ℝ) ^ (D₁ + 100) ≤ KPP D₁ N := by
  unfold KPP
  calc (N : ℝ) ^ (D₁ + 100) ≤ ⌈(N : ℝ) ^ (D₁ + 100)⌉₊ := Nat.le_ceil _
    _ ≤ (max 1 ⌈(N : ℝ) ^ (D₁ + 100)⌉₊ : ℕ) := by exact_mod_cast le_max_right _ _

theorem KPP_le (D₁ : ℝ) {N : ℕ} (hN : 1 ≤ N) : KPP D₁ N ≤ ⌈(N : ℝ) ^ (D₁ + 100)⌉₊ := by
  unfold KPP
  have : 1 ≤ ⌈(N : ℝ) ^ (D₁ + 100)⌉₊ := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hN0 _)).ne'
  omega

theorem KPP_card (D₁ : ℝ) (hD₁ : 0 < D₁) :
    ∀ᶠ N : ℕ in atTop, ((KPP D₁ N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (D₁ + 101) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hx1 : 1 ≤ (N : ℝ) ^ (D₁ + 100) := Real.one_le_rpow hN1 (by linarith)
  have hK : (KPP D₁ N : ℝ) ≤ (N : ℝ) ^ (D₁ + 100) + 1 := by
    unfold KPP
    rcases le_total 1 ⌈(N : ℝ) ^ (D₁ + 100)⌉₊ with h | h
    · rw [max_eq_right h]
      exact (Nat.ceil_lt_add_one (by linarith)).le
    · rw [max_eq_left h]; push_cast; linarith
  have e : (N : ℝ) ^ (D₁ + 101) = (N : ℝ) ^ (D₁ + 100) * N := by
    rw [show D₁ + 101 = (D₁ + 100) + 1 by ring, Real.rpow_add (by linarith), Real.rpow_one]
  push_cast
  rw [e]
  have hx0 : 0 ≤ (N : ℝ) ^ (D₁ + 100) := by linarith
  have h2 := mul_le_mul_of_nonneg_left hN2 hx0
  have hx2 : (N : ℝ) ≤ (N : ℝ) ^ (D₁ + 100) := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (D₁ + 100) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  linarith

theorem step_KPP_le {s t : ℕ → ℝ} (D₁ : ℝ) {N : ℕ} (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N)
    (hst : s N ≤ t N) (ht1 : t N < 1) :
    step s t (KPP D₁) N ≤ (N : ℝ) ^ (-(D₁ + 100)) := by
  have hK := KPP_ge D₁ N
  have hN0 : (0 : ℝ) < N := by linarith
  have hx : 0 < (N : ℝ) ^ (D₁ + 100) := Real.rpow_pos_of_pos hN0 _
  unfold step
  rw [Real.rpow_neg hN0.le, div_le_iff₀ (hx.trans_le hK)]
  calc t N - s N ≤ 1 := by linarith
    _ = ((N : ℝ) ^ (D₁ + 100))⁻¹ * (N : ℝ) ^ (D₁ + 100) := by field_simp
    _ ≤ ((N : ℝ) ^ (D₁ + 100))⁻¹ * (KPP D₁ N : ℝ) :=
        mul_le_mul_of_nonneg_left hK (inv_nonneg.2 hx.le)

theorem rpow_neg_W_le {W N a : ℝ} (hN1 : 1 ≤ N) (hW : N ^ (1 / 2 : ℝ) ≤ W) (ha : 0 ≤ a) :
    W ^ (-a) ≤ N ^ (-(a / 2)) := by
  have hN0 : 0 < N := by linarith
  have h1 : 0 < N ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hN0 _
  calc W ^ (-a) ≤ (N ^ (1 / 2 : ℝ)) ^ (-a) := Real.rpow_le_rpow_of_nonpos h1 hW (by linarith)
    _ = N ^ (-(a / 2)) := by rw [← Real.rpow_mul hN0.le]; ring_nf

/-! #### The polynomial size `P` of the Y moments -/

/-- `Q = 2m₄ + 2m₂² + 8(m₈ + m₂⁴) + 1`. -/
def QPP (d : Dims) (N : ℕ) : ℝ :=
  2 * xMom d N 4 + 2 * xMom d N 2 ^ 2 + 8 * (xMom d N 8 + xMom d N 2 ^ 4) + 1

/-- `P = C_U⁴ (C₂/2)² Q` (so that `v_j ≤ Δ² P`, `w_j ≤ Δ⁴ P²`). -/
def PPP (d : Dims) (κ E : ℝ) (t : ℕ → ℝ) (N : ℕ) : ℝ :=
  (CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2 * QPP d N

theorem QPP_ge_one (d : Dims) (N : ℕ) : 1 ≤ QPP d N := by
  unfold QPP
  have := xMom_nonneg d N 4; have := xMom_nonneg d N 8; have := xMom_nonneg d N 2
  nlinarith [sq_nonneg (xMom d N 2), pow_nonneg (xMom_nonneg d N 2) 4]

theorem PPP_nonneg (d : Dims) (κ E : ℝ) (t : ℕ → ℝ) (N : ℕ) : 0 ≤ PPP d κ E t N := by
  unfold PPP
  have := QPP_ge_one d N
  positivity

theorem vPP_le (d : Dims) (κ E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N : ℕ) :
    vPP d κ E s t Kf N ≤ step s t Kf N ^ 2 * PPP d κ E t N := by
  unfold vPP PPP
  have hQ : 2 * xMom d N 4 + 2 * xMom d N 2 ^ 2 ≤ QPP d N := by
    unfold QPP
    have := xMom_nonneg d N 8; have := xMom_nonneg d N 2
    nlinarith [pow_nonneg (xMom_nonneg d N 2) 4]
  have e : (CU κ ^ 2 * ((C2pp d E t N / 2) * step s t Kf N)) ^ 2
      = step s t Kf N ^ 2 * ((CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2) := by ring
  rw [e]
  have h0 : 0 ≤ step s t Kf N ^ 2 * ((CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2) := by positivity
  calc step s t Kf N ^ 2 * ((CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2)
        * (2 * xMom d N 4 + 2 * xMom d N 2 ^ 2)
      ≤ step s t Kf N ^ 2 * ((CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2) * QPP d N :=
        mul_le_mul_of_nonneg_left hQ h0
    _ = step s t Kf N ^ 2 * ((CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2 * QPP d N) := by ring

theorem wPP_le (d : Dims) (κ E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N : ℕ) :
    wPP d κ E s t Kf N ≤ step s t Kf N ^ 4 * PPP d κ E t N ^ 2 := by
  unfold wPP PPP
  have hQ1 := QPP_ge_one d N
  have hQ : 8 * (xMom d N 8 + xMom d N 2 ^ 4) ≤ QPP d N ^ 2 := by
    have h1 : 8 * (xMom d N 8 + xMom d N 2 ^ 4) ≤ QPP d N := by
      unfold QPP
      have := xMom_nonneg d N 4; have := xMom_nonneg d N 2
      nlinarith [sq_nonneg (xMom d N 2)]
    nlinarith
  have e : (CU κ ^ 2 * ((C2pp d E t N / 2) * step s t Kf N)) ^ 4
      = step s t Kf N ^ 4 * ((CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2) ^ 2 := by ring
  rw [e]
  have h0 : 0 ≤ step s t Kf N ^ 4 * ((CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2) ^ 2 := by positivity
  calc step s t Kf N ^ 4 * ((CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2) ^ 2
        * (8 * (xMom d N 8 + xMom d N 2 ^ 4))
      ≤ step s t Kf N ^ 4 * ((CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2) ^ 2 * QPP d N ^ 2 :=
        mul_le_mul_of_nonneg_left hQ h0
    _ = step s t Kf N ^ 4 * ((CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2 * QPP d N) ^ 2 := by ring

/-- The moments of `‖X‖` are polynomial: `m₂ ≤ N`, `m₄ ≤ C₄ N`, `m₈ ≤ C₈ N` eventually (the
trace moments `traceMomentBound_gauss`). -/
theorem ev_moments (d : Dims) : ∃ C₄ C₈ : ℝ, 0 ≤ C₄ ∧ 0 ≤ C₈ ∧ ∀ᶠ N : ℕ in atTop,
    xMom d N 4 ≤ C₄ * N ∧ xMom d N 8 ≤ C₈ * N ∧ xMom d N 2 ≤ N := by
  obtain ⟨C₄, hC₄, h4⟩ := traceMomentBound_gauss d 2
  obtain ⟨C₈, hC₈, h8⟩ := traceMomentBound_gauss d 4
  refine ⟨C₄, C₈, hC₄.le, hC₈.le, ?_⟩
  filter_upwards [h4, h8, d.dim] with N hN4 hN8 hdim
  refine ⟨?_, ?_, ?_⟩
  · have h := integral_norm_Xmat_pow_le (d := d) N 1
    norm_num at h
    exact h.trans hN4
  · have h := integral_norm_Xmat_pow_le (d := d) N 2
    norm_num at h
    exact h.trans hN8
  · have h := integral_norm_Xmat_pow_le (d := d) N 0
    norm_num at h
    rw [show (fun ω => frobSq (Xmat d N ω)) = fun ω => frobSq (Xmat d N ω ^ 1) by simp] at h
    refine h.trans ?_
    rw [integral_frobSq_Xmat_one]
    have : ((d.L N * d.W N : ℕ) : ℝ) ≤ N := by
      have : d.L N * d.W N ≤ N := by rw [Nat.mul_comm]; exact hdim.1
      exact_mod_cast this
    exact this

theorem PPP_le (d : Dims) (κ E : ℝ) {t : ℕ → ℝ} {N : ℕ} {C₄ C₈ : ℝ} (hC₄ : 0 ≤ C₄)
    (hC₈ : 0 ≤ C₈) (hN1 : (1 : ℝ) ≤ N) (hWL : (d.W N : ℝ) * d.L N ≤ N)
    (hηt0 : 0 < etaT E (t N)) (hηt : (etaT E (t N))⁻¹ ≤ N)
    (hm4 : xMom d N 4 ≤ C₄ * N) (hm8 : xMom d N 8 ≤ C₈ * N) (hm2 : xMom d N 2 ≤ N) :
    PPP d κ E t N ≤ (CU κ ^ 2) ^ 2 * 262144 * (2 * C₄ + 8 * C₈ + 11) * (N : ℝ) ^ 18 := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N := by
    have h1 : Fintype.card (d.Idx N) = d.L N * d.W N := by simp [ZMod.card]
    rw [h1]; push_cast; linarith
  have hi0 : 0 ≤ (etaT E (t N))⁻¹ := inv_nonneg.2 hηt0.le
  have h1η : 1 + (etaT E (t N))⁻¹ ≤ 2 * N := by linarith
  have hC2 : C2pp d E t N ≤ 1024 * (N : ℝ) ^ 7 := by
    unfold C2pp
    have h3 : (1 + (etaT E (t N))⁻¹) ^ 3 ≤ (2 * N) ^ 3 := pow_le_pow_left₀ (by positivity) h1η 3
    have h6 : (2 * (1 + (etaT E (t N))⁻¹) ^ 3) ^ 2 ≤ (2 * (2 * N) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc (Fintype.card (d.Idx N) : ℝ) * (((2 : ℕ) : ℝ) ^ 2 * (2 * (1 + (etaT E (t N))⁻¹) ^ 3) ^ 2)
        ≤ (N : ℝ) * (((2 : ℕ) : ℝ) ^ 2 * (2 * (2 * N) ^ 3) ^ 2) := by gcongr
      _ = 1024 * (N : ℝ) ^ 7 := by push_cast; ring
  have hC20 := C2pp_nonneg d E t N
  have hC2sq : (C2pp d E t N / 2) ^ 2 ≤ 262144 * (N : ℝ) ^ 14 := by
    have := pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hC2 (by norm_num : (0:ℝ) ≤ 2)) 2
    calc (C2pp d E t N / 2) ^ 2 ≤ (1024 * (N : ℝ) ^ 7 / 2) ^ 2 := this
      _ = 262144 * (N : ℝ) ^ 14 := by ring
  have hm20 := xMom_nonneg d N 2
  have hQ : QPP d N ≤ (2 * C₄ + 8 * C₈ + 11) * (N : ℝ) ^ 4 := by
    unfold QPP
    have hN4 : (N : ℝ) ≤ (N : ℝ) ^ 4 := le_self_pow₀ hN1 (by norm_num)
    have hN2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    have h1N : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hN1
    have hm22 : xMom d N 2 ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hm20 hm2 2
    have hm24 : xMom d N 2 ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ hm20 hm2 4
    have h4' : C₄ * N ≤ C₄ * (N : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hN4 hC₄
    have h8' : C₈ * N ≤ C₈ * (N : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hN4 hC₈
    nlinarith
  have hQ0 : 0 ≤ QPP d N := le_trans zero_le_one (QPP_ge_one d N)
  unfold PPP
  have hCC : 0 ≤ (CU κ ^ 2) ^ 2 := by positivity
  calc (CU κ ^ 2) ^ 2 * (C2pp d E t N / 2) ^ 2 * QPP d N
      ≤ (CU κ ^ 2) ^ 2 * (262144 * (N : ℝ) ^ 14) * ((2 * C₄ + 8 * C₈ + 11) * (N : ℝ) ^ 4) := by
        gcongr
    _ = (CU κ ^ 2) ^ 2 * 262144 * (2 * C₄ + 8 * C₈ + 11) * (N : ℝ) ^ 18 := by ring

/-! #### The numeric smallness facts at a fixed `N`, from pure asymptotics -/

theorem rpow_neg_nat_eq {N : ℝ} (hN : 0 < N) (k : ℕ) : N ^ (-(k : ℝ)) = (N ^ k)⁻¹ := by
  rw [Real.rpow_neg hN.le, Real.rpow_natCast]

theorem hX2_of {C Bk W L N : ℝ} (hC : 0 ≤ C) (hBk : 0 ≤ Bk) (hN1 : 1 ≤ N) (hW1 : 1 ≤ W)
    (hL0 : 0 ≤ L) (hWL : W * L ≤ N) (hLN : L ≤ N) (hW20 : W ^ (-(20 : ℝ)) ≤ N ^ (-(10 : ℝ)))
    (hG : C * 6 * Real.exp 1 * (1 + Bk) * N ^ 6 ≤ N ^ 10) :
    C * (6 * Real.exp 1 * W * L ^ 2 * W ^ (-(20 : ℝ)) * (N ^ 2 * (N ^ 2 + Bk))) ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have he := (Real.exp_pos 1).le
  have hWL2 : W * L ^ 2 ≤ N ^ 2 := by
    calc W * L ^ 2 = (W * L) * L := by ring
      _ ≤ N * N := mul_le_mul hWL hLN hL0 hN0.le
      _ = N ^ 2 := by ring
  have hNB : N ^ 2 + Bk ≤ (1 + Bk) * N ^ 2 := by
    have : 1 ≤ N ^ 2 := one_le_pow₀ hN1
    nlinarith
  have hW20' : 0 ≤ W ^ (-(20 : ℝ)) := Real.rpow_nonneg (by linarith) _
  rw [Real.rpow_neg hN0.le, show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hW20
  have hN10 : 0 < N ^ 10 := by positivity
  calc C * (6 * Real.exp 1 * W * L ^ 2 * W ^ (-(20 : ℝ)) * (N ^ 2 * (N ^ 2 + Bk)))
      = C * 6 * Real.exp 1 * (W * L ^ 2) * W ^ (-(20 : ℝ)) * (N ^ 2 * (N ^ 2 + Bk)) := by ring
    _ ≤ C * 6 * Real.exp 1 * N ^ 2 * (N ^ 10)⁻¹ * (N ^ 2 * ((1 + Bk) * N ^ 2)) := by
        gcongr
    _ = (C * 6 * Real.exp 1 * (1 + Bk) * N ^ 6) * (N ^ 10)⁻¹ := by ring
    _ ≤ N ^ 10 * (N ^ 10)⁻¹ := by gcongr
    _ = 1 := by field_simp

theorem hX4_of {C W L N nε : ℝ} (hC : 0 ≤ C) (hN1 : 1 ≤ N) (hW0 : 0 ≤ W) (hL0 : 0 ≤ L)
    (hWL : W * L ≤ N) (hnε0 : 0 ≤ nε) (hnε : nε ≤ N)
    (hW20 : W ^ (-(20 : ℝ)) ≤ N ^ (-(10 : ℝ))) (hG : C * 12 * Real.exp 1 * N ^ 3 ≤ N ^ 10) :
    C * (12 * Real.exp 1 * W * L * nε * W ^ (-(20 : ℝ)) * N) ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have he := (Real.exp_pos 1).le
  have hW20' : 0 ≤ W ^ (-(20 : ℝ)) := Real.rpow_nonneg hW0 _
  rw [Real.rpow_neg hN0.le, show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hW20
  have hN10 : 0 < N ^ 10 := by positivity
  calc C * (12 * Real.exp 1 * W * L * nε * W ^ (-(20 : ℝ)) * N)
      = C * 12 * Real.exp 1 * (W * L) * nε * W ^ (-(20 : ℝ)) * N := by ring
    _ ≤ C * 12 * Real.exp 1 * N * N * (N ^ 10)⁻¹ * N := by gcongr
    _ = (C * 12 * Real.exp 1 * N ^ 3) * (N ^ 10)⁻¹ := by ring
    _ ≤ N ^ 10 * (N ^ 10)⁻¹ := by gcongr
    _ = 1 := by field_simp

theorem hqvtail_of {C W L N : ℝ} (hC : 0 ≤ C) (hN1 : 1 ≤ N) (hW0 : 0 ≤ W) (hL0 : 0 ≤ L)
    (hWL : W * L ≤ N) (hW19 : W ^ (-(19 : ℝ)) ≤ N ^ (-(9 : ℝ)))
    (hG : C ^ 2 * 4 * N ^ 5 ≤ N ^ 9) :
    C ^ 2 * (4 * W * L * W ^ (-(19 : ℝ))) * N ^ 4 ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have hW19' : 0 ≤ W ^ (-(19 : ℝ)) := Real.rpow_nonneg hW0 _
  rw [Real.rpow_neg hN0.le, show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hW19
  have hN9 : 0 < N ^ 9 := by positivity
  calc C ^ 2 * (4 * W * L * W ^ (-(19 : ℝ))) * N ^ 4
      = C ^ 2 * 4 * (W * L) * W ^ (-(19 : ℝ)) * N ^ 4 := by ring
    _ ≤ C ^ 2 * 4 * N * (N ^ 9)⁻¹ * N ^ 4 := by gcongr
    _ = (C ^ 2 * 4 * N ^ 5) * (N ^ 9)⁻¹ := by ring
    _ ≤ N ^ 9 * (N ^ 9)⁻¹ := by gcongr
    _ = 1 := by field_simp

theorem hRt_of {Bk N Δ D₁ : ℝ} (hBk : 0 ≤ Bk) (hN1 : 1 ≤ N) (hD₁ : 0 ≤ D₁) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ N ^ (-(D₁ + 100))) (hG : 2 ^ 19 * (1 + Bk) ^ 4 * N ^ 19 ≤ N ^ 50) :
    N ^ 2 * (1 + N) ^ 2 * (2 ^ 17 * N ^ 15 * (1 + Bk) ^ 4) * Δ ^ (1 / 2 : ℝ) ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have hΔh : Δ ^ (1 / 2 : ℝ) ≤ (N ^ 50)⁻¹ := by
    calc Δ ^ (1 / 2 : ℝ) ≤ (N ^ (-(D₁ + 100))) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hΔ0 hΔ (by norm_num)
      _ = N ^ (-(D₁ + 100) / 2) := by rw [← Real.rpow_mul hN0.le]; ring_nf
      _ ≤ N ^ (-(50 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = (N ^ 50)⁻¹ := rpow_neg_nat_eq hN0 50
  have h1N : (1 + N) ^ 2 ≤ 4 * N ^ 2 := by nlinarith
  have hΔh0 : 0 ≤ Δ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hΔ0 _
  have hN50 : 0 < N ^ 50 := by positivity
  calc N ^ 2 * (1 + N) ^ 2 * (2 ^ 17 * N ^ 15 * (1 + Bk) ^ 4) * Δ ^ (1 / 2 : ℝ)
      ≤ N ^ 2 * (4 * N ^ 2) * (2 ^ 17 * N ^ 15 * (1 + Bk) ^ 4) * (N ^ 50)⁻¹ := by gcongr
    _ = (2 ^ 19 * (1 + Bk) ^ 4 * N ^ 19) * (N ^ 50)⁻¹ := by ring
    _ ≤ N ^ 50 * (N ^ 50)⁻¹ := by gcongr
    _ = 1 := by field_simp

/-- The O2 loop modulus is `≤ 6 N⁹ Δ`. -/
theorem deltaShift_le (d : Dims) {E : ℝ} {s t : ℕ → ℝ} {Kf : ℕ → ℕ} {N : ℕ} (hE : |E| < 2)
    (hst : s N ≤ t N) (ht1 : t N < 1) (hWL : (d.W N : ℝ) * d.L N ≤ N)
    (hηt : (etaT E (t N))⁻¹ ≤ N) :
    deltaShift d E s t Kf N ≤ 6 * (N : ℝ) ^ 9 * step s t Kf N := by
  have hηt0 : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE ht1
  have hi0 : 0 ≤ (etaT E (t N))⁻¹ := inv_nonneg.2 hηt0.le
  have hΔ0 := step_nonneg' s t Kf N hst
  have hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N := by linarith
  unfold deltaShift
  calc (d.L N : ℝ) * (d.W N : ℝ) * 6 * (etaT E (t N))⁻¹ ^ 6
        * ((etaT E (t N))⁻¹ * step s t Kf N * (etaT E (t N))⁻¹)
      ≤ (N : ℝ) * 6 * (N : ℝ) ^ 6 * ((N : ℝ) * step s t Kf N * N) := by gcongr
    _ = 6 * (N : ℝ) ^ 9 * step s t Kf N := by ring

theorem hsmall_of (d : Dims) {E : ℝ} {s t : ℕ → ℝ} {Kf : ℕ → ℕ} {N : ℕ} {D₁ : ℝ} (hE : |E| < 2)
    (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1) (hN1 : (1 : ℝ) ≤ N) (hD₁ : 0 ≤ D₁)
    (hWL : (d.W N : ℝ) * d.L N ≤ N) (hηt : (etaT E (t N))⁻¹ ≤ N)
    (hΔ : step s t Kf N ≤ (N : ℝ) ^ (-(D₁ + 100))) (hG : 6 * (N : ℝ) ^ 14 ≤ (N : ℝ) ^ 100) :
    (band d).scale E N (s N) ^ 5 * deltaShift d E s t Kf N ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hA0 : 0 < (band d).scale E N (s N) := (band d).scale_pos' hE N hs0 (hst.trans_lt ht1)
  have hAN : (band d).scale E N (s N) ≤ N := scale_le_N_pp hE hWL hs0 (hst.trans_lt ht1)
  have hδ := deltaShift_le (Kf := Kf) d hE hst ht1 hWL hηt
  have hΔ0 := step_nonneg' s t Kf N hst
  have hΔ' : step s t Kf N ≤ ((N : ℝ) ^ 100)⁻¹ := by
    refine hΔ.trans ?_
    rw [← rpow_neg_nat_eq hN0 100]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hδ0 : 0 ≤ deltaShift d E s t Kf N := by
    have := inv_nonneg.2 (etaT_pos_of_lt_one' hE ht1).le
    unfold deltaShift; positivity
  have hN100 : 0 < (N : ℝ) ^ 100 := by positivity
  calc (band d).scale E N (s N) ^ 5 * deltaShift d E s t Kf N
      ≤ (N : ℝ) ^ 5 * (6 * (N : ℝ) ^ 9 * ((N : ℝ) ^ 100)⁻¹) := by
        gcongr
        exact hδ.trans (by gcongr)
    _ = (6 * (N : ℝ) ^ 14) * ((N : ℝ) ^ 100)⁻¹ := by ring
    _ ≤ (N : ℝ) ^ 100 * ((N : ℝ) ^ 100)⁻¹ := by gcongr
    _ = 1 := by field_simp

theorem htail_of (d : Dims) {E : ℝ} {s t : ℕ → ℝ} {Kf : ℕ → ℕ} {N : ℕ} {D₁ : ℝ} (hE : |E| < 2)
    (hst : s N ≤ t N) (ht1 : t N < 1) (hN1 : (1 : ℝ) ≤ N) (hD₁ : 0 ≤ D₁)
    (hWL : (d.W N : ℝ) * d.L N ≤ N) (hWN : (d.W N : ℝ) ≤ N) (hW2 : (2 : ℝ) ≤ d.W N)
    (hηt : (etaT E (t N))⁻¹ ≤ N)
    (hΔ : step s t Kf N ≤ (N : ℝ) ^ (-(D₁ + 100))) (hG : 6 * (N : ℝ) ^ 29 ≤ (N : ℝ) ^ 100) :
    (d.W N : ℝ) ^ (-(20 : ℝ)) + deltaShift d E s t Kf N ≤ (d.W N : ℝ) ^ (-(19 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hW0 : (0 : ℝ) < d.W N := by linarith
  have hδ := deltaShift_le (Kf := Kf) d hE hst ht1 hWL hηt
  have hΔ' : step s t Kf N ≤ ((N : ℝ) ^ 100)⁻¹ := by
    refine hΔ.trans ?_
    rw [← rpow_neg_nat_eq hN0 100]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hN100 : 0 < (N : ℝ) ^ 100 := by positivity
  have hδ' : deltaShift d E s t Kf N ≤ ((N : ℝ) ^ 20)⁻¹ := by
    refine hδ.trans ?_
    calc 6 * (N : ℝ) ^ 9 * step s t Kf N ≤ 6 * (N : ℝ) ^ 9 * ((N : ℝ) ^ 100)⁻¹ := by gcongr
      _ = (6 * (N : ℝ) ^ 29) * ((N : ℝ) ^ 100)⁻¹ * ((N : ℝ) ^ 20)⁻¹ := by field_simp
      _ ≤ (N : ℝ) ^ 100 * ((N : ℝ) ^ 100)⁻¹ * ((N : ℝ) ^ 20)⁻¹ := by gcongr
      _ = ((N : ℝ) ^ 20)⁻¹ := by field_simp
  have hWN20 : ((N : ℝ) ^ 20)⁻¹ ≤ (d.W N : ℝ) ^ (-(20 : ℝ)) := by
    rw [← rpow_neg_nat_eq hN0 20]
    exact Real.rpow_le_rpow_of_nonpos hW0 hWN (by norm_num)
  have h19 : (d.W N : ℝ) ^ (-(19 : ℝ)) = (d.W N : ℝ) * (d.W N : ℝ) ^ (-(20 : ℝ)) := by
    rw [show (-(19 : ℝ)) = 1 + (-(20 : ℝ)) by norm_num, Real.rpow_add hW0, Real.rpow_one]
  have hW20 : 0 ≤ (d.W N : ℝ) ^ (-(20 : ℝ)) := Real.rpow_nonneg hW0.le _
  rw [h19]
  nlinarith

theorem sq_rpow_five_halves {x : ℝ} (hx : 0 ≤ x) : (x ^ (5 / 2 : ℝ)) ^ 2 = x ^ 5 := by
  rw [← Real.rpow_natCast (x ^ (5 / 2 : ℝ)) 2, ← Real.rpow_mul hx]
  norm_num

/-- On a degenerate grid (`s_N = t_N`, `Δ = 0`) the grid path is frozen. -/
theorem H_eq_zero_of_step {s t : ℕ → ℝ} {Kf : ℕ → ℕ} {N : ℕ} (h : s N = t N) (k : ℕ)
    (ω : Ωg d) : H d s t Kf N k ω = H d s t Kf N 0 ω ∧ time s t Kf N k = time s t Kf N 0 := by
  have hstep : step s t Kf N = 0 := by unfold step; rw [h, sub_self, zero_div]
  refine ⟨?_, ?_⟩
  · unfold H; rw [hstep]; simp
  · unfold time; rw [hstep]; simp

theorem measure_le_ofReal_of_real {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    [IsFiniteMeasure μ] {S : Set Ω'} {x : ℝ} (h : μ.real S ≤ x) : μ S ≤ ENNReal.ofReal x := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ S)]
  exact ENNReal.ofReal_le_ofReal h

/-! #### Signature checks: the gained declarations have the binders and conclusions stated
below. -/

end RealPP

end RBM.Gauss.Grid

end

