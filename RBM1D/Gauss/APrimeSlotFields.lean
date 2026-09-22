/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeModel
import RBM1D.Flow.FirstCell

/-!
# The deterministic fields of `RBM.APrimeModel.APrimeSlot` at `J = jSnorm` (T274)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.29)/(5.43)/(5.46)/(5.47).
-/

namespace RBM

namespace APrimeSlotFields

open MeasureTheory Filter Set Real Gauss Step2FarMart Step2Bootstrap MomentDuhamelCut

open scoped Matrix.Norms.L2Operator

/-! ### 1. Measurability of `J*_{u,D}` and of its normalization -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`J*_{u,D}` is measurable in `ω`** — verbatim `RBM.measurable_jSfarSm` with the far weight
`χ` removed. -/
theorem measurable_jS (X : Sample B) (E D : ℝ) (N : ℕ) (u : ℝ) :
    Measurable fun ω => Step2.jS X E D N u ω := by
  have h : ∀ ω : Ω, Step2.jS X E D N u ω
      = (Finset.univ.sup' Finset.univ_nonempty
          (fun (a : LoopArg (B.L N) 2) (ω' : Ω) =>
            ‖Step2.lk X E N u ω' a‖ / tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D
              (zdist (B.L N) (a 0 - a 1)))) ω + 1 := by
    intro ω; rw [Finset.sup'_apply]; rfl
  simp only [h]
  exact (Finset.measurable_sup' _ fun a _ =>
    (measurable_lk X E N u a).norm.div measurable_const).add measurable_const

/-- **The `meas` field of `RBM.Step2Bootstrap.APrimeHypOn` at `J = jSnorm`.** -/
theorem measurable_jSnorm (X : Sample B) (E D : ℝ) (s : ℕ → ℝ) (N : ℕ) (u : ℝ) :
    Measurable fun ω => Step2Moment.jSnorm X E D s N u ω :=
  (measurable_jS X E D N u).div measurable_const

end Meas

/-! ### 2. The modulus transfer for the **unweighted** `J*` -/

section Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Modulus transfer for `J*_{u,D}`** — `RBM.Step2FarMart.abs_jSfarSm_sub_le` for the
unweighted functional.  `J*` is a `Finset.sup'` plus `1`, so a uniform bound on the pointwise
differences of the ratios bounds the difference of the maxima. -/
theorem abs_jS_sub_le (X : Sample B) {E D : ℝ} {N : ℕ} {ω : Ω} {v w M : ℝ}
    (h : ∀ x : LoopArg (B.L N) 2,
      |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
            (zdist (B.L N) (x 0 - x 1))
        - ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
            (zdist (B.L N) (x 0 - x 1))| ≤ M) :
    |Step2.jS X E D N v ω - Step2.jS X E D N w ω| ≤ M := by
  set F : LoopArg (B.L N) 2 → ℝ := fun x =>
    ‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
      (zdist (B.L N) (x 0 - x 1)) with hF
  set G : LoopArg (B.L N) 2 → ℝ := fun x =>
    ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
      (zdist (B.L N) (x 0 - x 1)) with hG
  have key : ∀ (F G : LoopArg (B.L N) 2 → ℝ), (∀ x, F x ≤ G x + M) →
      Finset.univ.sup' Finset.univ_nonempty F
        ≤ Finset.univ.sup' Finset.univ_nonempty G + M := by
    intro F G hFG
    refine Finset.sup'_le _ _ fun x _ => (hFG x).trans ?_
    have := Finset.le_sup' G (Finset.mem_univ x)
    linarith
  have h1 : Finset.univ.sup' Finset.univ_nonempty F
      ≤ Finset.univ.sup' Finset.univ_nonempty G + M :=
    key F G fun x => by have := abs_le.1 (h x); linarith [this.2]
  have h2 : Finset.univ.sup' Finset.univ_nonempty G
      ≤ Finset.univ.sup' Finset.univ_nonempty F + M :=
    key G F fun x => by have := abs_le.1 (h x); linarith [this.1]
  simp only [Step2.jS, Step2.jStar, ← hF, ← hG]
  rw [abs_le]
  constructor <;> linarith

end Transfer

/-! ### 3. The `jS` modulus from any loop modulus, and its event instance -/

section JSModulus

open Real Gauss Step2FarMart

/-- **The `J*_{u,D}` modulus from *any* modulus of the loop error** — `RBM.abs_jSfarSm_sub_le_of_lk`
transcribed to the *unweighted* functional.  The far weight `χ` of `jSfarSm` only ever
*contributed* a term (`RBM.Step2FarMart.abs_lkFarSm_ratio_sub_le` splits the difference into a
weight term plus the unweighted ratio term), and that term is non-negative, so the very same
constant `jSfarSmLip + Λ W^D` serves here. -/
theorem abs_jS_sub_le_of_lk (d : Dims) (N : ℕ) (ω : Ω d) {E D t₀ v w Λ γ : ℝ}
    (hE : |E| < 2) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hlen : |v - w| ≤ 1)
    (hv0 : 0 ≤ v) (hw0 : 0 ≤ w) (hv : v ≤ t₀) (hw : w ≤ t₀) (ht₀ : t₀ < 1)
    (hlogW : (1 : ℝ) ≤ Real.log (d.W N : ℝ)) (hΛ0 : 0 ≤ Λ)
    (hlk : ∀ x : LoopArg (d.L N) 2,
      ‖Step2.lk (sample d) E N v ω x - Step2.lk (sample d) E N w ω x‖ ≤ |v - w| ^ γ * Λ) :
    |Step2.jS (sample d) E D N v ω - Step2.jS (sample d) E D N w ω|
      ≤ |v - w| ^ γ * (jSfarSmLip d N E D t₀ + Λ * (d.W N : ℝ) ^ D) := by
  refine abs_jS_sub_le (sample d) (fun x => ?_)
  simp only [Band.ell, band_W, band_L]
  have hstep := ratio_step_le d N (E := E) (D := D) (t₀ := t₀) (Λ := Λ) (γ := γ)
    (ℓ := ((zdist (d.L N) (x 0 - x 1) : ℕ) : ℝ))
    (nv := ‖Step2.lk (sample d) E N v ω x‖) (nw := ‖Step2.lk (sample d) E N w ω x‖)
    hE hγ0 hγ1 hlen hv0 hw0 hv hw ht₀ hlogW hΛ0
    (Nat.cast_nonneg _) (zdist_le_half _) (norm_nonneg _) (norm_nonneg _)
    (norm_lk_le_crude d N ω hE hv0 hv ht₀ x) (norm_lk_le_crude d N ω hE hw0 hw ht₀ x)
    ((abs_norm_sub_norm_le _ _).trans (hlk x))
  have hweight0 : (0:ℝ) ≤ 15 / 8 * |((zdist (d.L N) (x 0 - x 1) : ℕ) : ℝ)
        / (6 * ellStar (d.W N : ℝ) (ellHat (d.L N) (v : ℂ)))
      - ((zdist (d.L N) (x 0 - x 1) : ℕ) : ℝ)
        / (6 * ellStar (d.W N : ℝ) (ellHat (d.L N) (w : ℂ)))|
      * |‖Step2.lk (sample d) E N v ω x‖
          / tailT (d.W N : ℝ) (ellHat (d.L N) (v : ℂ)) (etaT E v) D
            ((zdist (d.L N) (x 0 - x 1) : ℕ) : ℝ)| := by positivity
  exact le_trans (le_add_of_nonneg_left hweight0) hstep

/-- **The `γ = 1/2` producer for `J*_{u,D}` on the event `{‖X‖ ≤ N}`** — the exact analogue of
`RBM.abs_jSfarSm_sub_le_event`.  `v = w = 0` is allowed, which is D17's first cell. -/
theorem abs_jS_sub_le_event (d : Dims) (N : ℕ) (ω : Ω d) {E D t₀ v w : ℝ}
    (hE : |E| < 2) (hv0 : 0 ≤ v) (hw0 : 0 ≤ w) (hv : v ≤ t₀) (hw : w ≤ t₀) (ht₀ : t₀ < 1)
    (ht₀0 : 0 ≤ t₀) (hlen : |v - w| ≤ 1) (hlogW : (1 : ℝ) ≤ Real.log (d.W N : ℝ))
    (hX : ‖Xmat d N ω‖ ≤ (N : ℝ)) :
    |Step2.jS (sample d) E D N v ω - Step2.jS (sample d) E D N w ω|
      ≤ |v - w| ^ ((1:ℝ) / 2)
        * (jSfarSmLip d N E D t₀ + lkLipEv d N E t₀ * (d.W N : ℝ) ^ D) :=
  abs_jS_sub_le_of_lk d N ω (D := D) (Λ := lkLipEv d N E t₀) (γ := (1:ℝ) / 2)
    hE (by norm_num) (by norm_num) hlen hv0 hw0 hv hw ht₀ hlogW
    (lkLipEv_nonneg d N hE ht₀)
    (fun x => norm_lk_sub_le_event d N ω hE hv0 hw0 hv hw ht₀ ht₀0 hlen hX x)

end JSModulus

/-! ### 4. From `J*` to its normalization `J*/R⁴` -/

section Normalized

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `|a⁴ - b⁴| ≤ 4|a - b|` on `[0,1]`. -/
theorem abs_pow4_sub_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |a ^ 4 - b ^ 4| ≤ 4 * |a - b| := by
  have hid : a ^ 4 - b ^ 4 = (a - b) * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) := by ring
  have hfac : |a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3| ≤ 4 := by
    rw [abs_le]
    constructor <;> nlinarith [pow_le_one₀ ha0 ha1 (n := 3), pow_le_one₀ hb0 hb1 (n := 3),
      pow_nonneg ha0 3, pow_nonneg hb0 3, mul_nonneg (pow_nonneg ha0 2) hb0,
      mul_nonneg ha0 (pow_nonneg hb0 2), mul_nonneg ha0 hb0, sq_nonneg (a - b),
      sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
  rw [hid, abs_mul]
  calc |a - b| * |a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3| ≤ |a - b| * 4 :=
        mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
    _ = 4 * |a - b| := by ring

/-- **The reciprocal weight of (5.43)**, `R_u^{-4} = ((1-u)/(1-s_N))⁴`. -/
noncomputable def rhoS (s : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ := ((1 - u) / (1 - s N)) ^ 4

/-- `J*_{u,D}/R_u⁴ = J*_{u,D}·ρ_u`. -/
theorem jSnorm_eq_mul (X : Sample B) {E D : ℝ} {s : ℕ → ℝ} (hE : |E| < 2) {N : ℕ}
    (hs1 : s N < 1) {u : ℝ} (hu1 : u < 1) (ω : Ω) :
    Step2Moment.jSnorm X E D s N u ω = Step2.jS X E D N u ω * rhoS s N u := by
  have hs0 : (0:ℝ) < 1 - s N := by linarith
  have hu0 : (0:ℝ) < 1 - u := by linarith
  rw [Step2Moment.jSnorm, Step2Moment.ratR, Step2.etaT_ratio hE, rhoS, div_pow, div_pow]
  field_simp

theorem rhoS_nonneg {s : ℕ → ℝ} {N : ℕ} {u : ℝ} (hs1 : s N < 1) (hu1 : u ≤ 1) :
    0 ≤ rhoS s N u := by
  have hs0 : (0:ℝ) < 1 - s N := by linarith
  have : (0:ℝ) ≤ 1 - u := by linarith
  unfold rhoS; positivity

theorem rhoS_le_one {s : ℕ → ℝ} {N : ℕ} {u : ℝ} (hs1 : s N < 1) (hsu : s N ≤ u) (hu1 : u ≤ 1) :
    rhoS s N u ≤ 1 := by
  have hs0 : (0:ℝ) < 1 - s N := by linarith
  have hb : (1 - u) / (1 - s N) ≤ 1 := by
    rw [div_le_one hs0]; linarith
  have hb0 : (0:ℝ) ≤ (1 - u) / (1 - s N) := by
    apply div_nonneg (by linarith) hs0.le
  calc rhoS s N u = ((1 - u) / (1 - s N)) ^ 4 := rfl
    _ ≤ 1 ^ 4 := pow_le_pow_left₀ hb0 hb 4
    _ = 1 := one_pow 4

/-- **The Lipschitz modulus of the reciprocal weight**: `|ρ_v - ρ_w| ≤ 4(1-t₀)⁻¹|v-w|`. -/
theorem abs_rhoS_sub_le {s : ℕ → ℝ} {N : ℕ} {t₀ v w : ℝ} (ht₀ : t₀ < 1) (hst : s N ≤ t₀)
    (hsv : s N ≤ v) (hsw : s N ≤ w) (hv : v ≤ t₀) (hw : w ≤ t₀) :
    |rhoS s N v - rhoS s N w| ≤ 4 * (1 - t₀)⁻¹ * |v - w| := by
  have ht0 : (0:ℝ) < 1 - t₀ := by linarith
  have hs0 : (0:ℝ) < 1 - s N := by linarith
  have ha0 : (0:ℝ) ≤ (1 - v) / (1 - s N) := div_nonneg (by linarith) hs0.le
  have hb0 : (0:ℝ) ≤ (1 - w) / (1 - s N) := div_nonneg (by linarith) hs0.le
  have ha1 : (1 - v) / (1 - s N) ≤ 1 := by rw [div_le_one hs0]; linarith
  have hb1 : (1 - w) / (1 - s N) ≤ 1 := by rw [div_le_one hs0]; linarith
  have h4 := abs_pow4_sub_le ha0 ha1 hb0 hb1
  have hdiff : (1 - v) / (1 - s N) - (1 - w) / (1 - s N) = (w - v) / (1 - s N) := by
    field_simp; ring
  have habs : |(1 - v) / (1 - s N) - (1 - w) / (1 - s N)| = |v - w| / (1 - s N) := by
    rw [hdiff, abs_div, abs_of_pos hs0, abs_sub_comm]
  have hle : |v - w| / (1 - s N) ≤ (1 - t₀)⁻¹ * |v - w| := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ ht0 (by linarith)) (abs_nonneg _)
  calc |rhoS s N v - rhoS s N w| ≤ 4 * |(1 - v) / (1 - s N) - (1 - w) / (1 - s N)| := h4
    _ = 4 * (|v - w| / (1 - s N)) := by rw [habs]
    _ ≤ 4 * ((1 - t₀)⁻¹ * |v - w|) := by
        exact mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = 4 * (1 - t₀)⁻¹ * |v - w| := by ring

end Normalized

section CrudeSize

open Gauss

/-- `J*_{u,D} ≤ crudeLk·W^D + 1` on `[0, t₀]`, for every `ω` — the crude size of `J*`. -/
theorem jS_le_crude (d : Dims) (N : ℕ) (ω : Ω d) {E D t₀ u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu : u ≤ t₀) (ht₀ : t₀ < 1) :
    Step2.jS (sample d) E D N u ω ≤ (d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1 := by
  refine jS_le_of_bdd (sample d) E D N u ω (crudeLk_nonneg d N hE ht₀) (fun a => ?_)
  rw [Step2.idx_sigPM, ← Step2.norm_lk_eq]
  exact norm_lk_le_crude d N ω hE hu0 hu ht₀ a

end CrudeSize

/-! ### 5. The `modulus` field for `J*/R⁴` on the event `{‖X‖ ≤ N}` -/

section NormModulus

open Real Gauss Step2FarMart

/-- **The whole modulus constant of `J*_{u,D}/R_u⁴` on the event.**  The first two summands are
`RBM.abs_jS_sub_le_event`'s; the third pays for the time dependence of the weight `R_u^{-4}`. -/
noncomputable def jTotNormEv (d : Dims) (N : ℕ) (E D t₀ : ℝ) : ℝ :=
  jSfarSmLip d N E D t₀ + lkLipEv d N E t₀ * (d.W N : ℝ) ^ D
    + 4 * (1 - t₀)⁻¹ * ((d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1)

/-- **⭐ The `γ = 1/2` modulus of `J*_{u,D}/R_u⁴` on `{‖X‖ ≤ N}`**, with `v = w = s_N = 0`
allowed.  This is `RBM.abs_jSfarSm_sub_le_event` carried across the two differences between the
two functionals: the far weight `χ` is dropped (`abs_jS_sub_le_of_lk`), and the *time-dependent*
normalization `R_u^{-4}` of (5.43) is put back (`abs_rhoS_sub_le`, `jS_le_crude`). -/
theorem abs_jSnorm_sub_le_event (d : Dims) (N : ℕ) (ω : Ω d) {E D t₀ v w : ℝ} {s : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hsw : s N ≤ w) (hv : v ≤ t₀) (hw : w ≤ t₀)
    (ht₀ : t₀ < 1) (ht₀0 : 0 ≤ t₀) (hlen : |v - w| ≤ 1) (hlogW : (1 : ℝ) ≤ Real.log (d.W N : ℝ))
    (hX : ‖Xmat d N ω‖ ≤ (N : ℝ)) :
    |Step2Moment.jSnorm (sample d) E D s N v ω - Step2Moment.jSnorm (sample d) E D s N w ω|
      ≤ |v - w| ^ ((1:ℝ) / 2) * jTotNormEv d N E D t₀ := by
  have hv0 : (0:ℝ) ≤ v := le_trans hs0 hsv
  have hw0 : (0:ℝ) ≤ w := le_trans hs0 hsw
  have hst : s N ≤ t₀ := le_trans hsv hv
  have hs1 : s N < 1 := lt_of_le_of_lt hst ht₀
  have hv1 : v < 1 := lt_of_le_of_lt hv ht₀
  have hw1 : w < 1 := lt_of_le_of_lt hw ht₀
  have ht0 : (0:ℝ) < 1 - t₀ := by linarith
  have hpow0 : (0:ℝ) ≤ |v - w| ^ ((1:ℝ) / 2) := Real.rpow_nonneg (abs_nonneg _) _
  have hlin : |v - w| ≤ |v - w| ^ ((1:ℝ) / 2) :=
    self_le_rpow_of_le_one (abs_nonneg _) hlen (by norm_num) (by norm_num)
  set A := Step2.jS (sample d) E D N v ω with hA
  set Bq := Step2.jS (sample d) E D N w ω with hB
  have hA0 : (0:ℝ) ≤ A := le_trans zero_le_one (Step2Moment.one_le_jS (sample d) N v ω)
  have hB0 : (0:ℝ) ≤ Bq := le_trans zero_le_one (Step2Moment.one_le_jS (sample d) N w ω)
  have hρv0 : 0 ≤ rhoS s N v := rhoS_nonneg hs1 (by linarith)
  have hρv1 : rhoS s N v ≤ 1 := rhoS_le_one hs1 hsv (by linarith)
  have hsplit : Step2Moment.jSnorm (sample d) E D s N v ω
      - Step2Moment.jSnorm (sample d) E D s N w ω
      = (A - Bq) * rhoS s N v + Bq * (rhoS s N v - rhoS s N w) := by
    rw [jSnorm_eq_mul (sample d) hE hs1 hv1, jSnorm_eq_mul (sample d) hE hs1 hw1, ← hA, ← hB]
    ring
  have hJ := abs_jS_sub_le_event d N ω (D := D) (t₀ := t₀) hE hv0 hw0 hv hw ht₀ ht₀0 hlen
    hlogW hX
  have hρ := abs_rhoS_sub_le (s := s) (N := N) ht₀ hst hsv hsw hv hw
  have hsize := jS_le_crude d N ω (D := D) (t₀ := t₀) hE hw0 hw ht₀
  have hcr0 : (0:ℝ) ≤ (d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1 := by
    have hW0 : (0:ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
    have := crudeLk_nonneg d N hE ht₀
    have : (0:ℝ) ≤ (d.W N : ℝ) ^ D := (Real.rpow_pos_of_pos hW0 D).le
    positivity
  have hterm1 : |A - Bq| * rhoS s N v
      ≤ |v - w| ^ ((1:ℝ) / 2) * (jSfarSmLip d N E D t₀ + lkLipEv d N E t₀ * (d.W N : ℝ) ^ D) := by
    calc |A - Bq| * rhoS s N v ≤ |A - Bq| * 1 :=
          mul_le_mul_of_nonneg_left hρv1 (abs_nonneg _)
      _ = |A - Bq| := mul_one _
      _ ≤ _ := hJ
  have hterm2 : Bq * |rhoS s N v - rhoS s N w|
      ≤ |v - w| ^ ((1:ℝ) / 2) * (4 * (1 - t₀)⁻¹ * ((d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1)) := by
    calc Bq * |rhoS s N v - rhoS s N w|
        ≤ ((d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1) * (4 * (1 - t₀)⁻¹ * |v - w|) :=
          mul_le_mul hsize hρ (abs_nonneg _) hcr0
      _ ≤ ((d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1)
            * (4 * (1 - t₀)⁻¹ * |v - w| ^ ((1:ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcr0
          exact mul_le_mul_of_nonneg_left hlin (by positivity)
      _ = |v - w| ^ ((1:ℝ) / 2) * (4 * (1 - t₀)⁻¹ * ((d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1)) := by
          ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hρv0, abs_of_nonneg hB0]
  rw [jTotNormEv]
  nlinarith [hterm1, hterm2]

end NormModulus

/-! ### 6. The constant is `N^{2+2D}`, and the `modulus` field -/

section Size

open Real Gauss Step2FarMart Filter

/-- **The modulus constant of `J*/R⁴` is `N^{1+2D}` times an `(E,t₀)`-constant** — `D ≥ 1`, as
in `RBM.exists_const_jTotEv`, which this extends by the weight term. -/
theorem exists_const_jTotNormEv (d : Dims) {E D t₀ : ℝ} (hE : |E| < 2) (hD : 1 ≤ D)
    (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1) :
    ∃ K > (0 : ℝ), ∀ N : ℕ, (1 : ℝ) ≤ (N : ℝ) → (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) →
      jTotNormEv d N E D t₀ ≤ K * (N : ℝ) ^ (1 + 2 * D) := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_const_jTotEv d hE hD ht₀0 ht₀
  have h1t : (0 : ℝ) < 1 - t₀ := by linarith
  have hq0 : (0 : ℝ) < (etaT E t₀)⁻¹ := inv_pos.2 (etaT_pos_of_lt_one' hE ht₀)
  set q : ℝ := (etaT E t₀)⁻¹ with hqdef
  set r : ℝ := (1 - t₀)⁻¹ with hrdef
  have hr0 : (0:ℝ) < r := inv_pos.2 h1t
  refine ⟨K₀ + 4 * r * (q * q + r + 1), by positivity, ?_⟩
  intro N hN1 hWL
  have hWr1 : (1 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hLr1 : (1 : ℝ) ≤ (d.L N : ℝ) := by
    have := d.three_le_L N; exact_mod_cast (by omega : 1 ≤ d.L N)
  have hWr0 : (0 : ℝ) < (d.W N : ℝ) := by linarith
  have hWinv1 : ((d.W N : ℝ))⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; exact Or.inr hWr1
  have hWinv0 : (0:ℝ) < ((d.W N : ℝ))⁻¹ := inv_pos.2 hWr0
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hWN : (d.W N : ℝ) ≤ (N : ℝ) := by nlinarith
  have hWD : (d.W N : ℝ) ^ D ≤ (N : ℝ) ^ D := Real.rpow_le_rpow (by linarith) hWN (by linarith)
  have hWD0 : (0 : ℝ) < (d.W N : ℝ) ^ D := Real.rpow_pos_of_pos hWr0 _
  have hA0 : (0 : ℝ) < (N : ℝ) ^ (1 + 2 * D) := Real.rpow_pos_of_pos hN0 _
  have hA1 : (1:ℝ) ≤ (N : ℝ) ^ (1 + 2 * D) := Real.one_le_rpow hN1 (by linarith)
  have hfac4 : ((d.W N : ℝ))⁻¹ * (d.W N : ℝ) ^ D ≤ (N : ℝ) ^ (1 + 2 * D) := by
    calc ((d.W N : ℝ))⁻¹ * (d.W N : ℝ) ^ D ≤ 1 * (N : ℝ) ^ D :=
          mul_le_mul hWinv1 hWD hWD0.le (by norm_num)
      _ = (N : ℝ) ^ D := one_mul _
      _ ≤ (N : ℝ) ^ (1 + 2 * D) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hcr : (d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1 ≤ (q * q + r + 1) * (N : ℝ) ^ (1 + 2 * D) := by
    have hrw : (d.W N : ℝ) ^ D * crudeLk d N E t₀
        = (q * q + r) * (((d.W N : ℝ))⁻¹ * (d.W N : ℝ) ^ D) := by
      rw [crudeLk, hqdef, hrdef]; ring
    have h1 : (d.W N : ℝ) ^ D * crudeLk d N E t₀ ≤ (q * q + r) * (N : ℝ) ^ (1 + 2 * D) := by
      rw [hrw]; exact mul_le_mul_of_nonneg_left hfac4 (by positivity)
    nlinarith
  have hlast : 4 * r * ((d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1)
      ≤ 4 * r * (q * q + r + 1) * (N : ℝ) ^ (1 + 2 * D) := by
    have := mul_le_mul_of_nonneg_left hcr (by positivity : (0:ℝ) ≤ 4 * r)
    calc 4 * r * ((d.W N : ℝ) ^ D * crudeLk d N E t₀ + 1)
        ≤ 4 * r * ((q * q + r + 1) * (N : ℝ) ^ (1 + 2 * D)) := this
      _ = 4 * r * (q * q + r + 1) * (N : ℝ) ^ (1 + 2 * D) := by ring
  have h0 := hK₀ N hN1 hWL
  rw [jTotNormEv]
  nlinarith [h0, hlast]

/-- **⭐⭐ The `modulus` field of `RBM.Step2Bootstrap.APrimeHypOn` at `J = jSnorm`**, with
`Kmod = 2 + 2D`, `γ = 1/2`, on **any** event contained in `{‖X‖ ≤ N}`.

This is the statement `RBM.APrimeModel` §8 says is missing: T257's data assembled for the
*complete* `J*/R⁴`, not only for the far half.  The window is allowed to start at `s_N = 0`
(only `0 ≤ s N` is asked), which is D17's first cell. -/
theorem eventually_modulus_jSnorm_event (d : Dims) {E D t₀ : ℝ} {s t : ℕ → ℝ}
    {Good : ℕ → Set (Ω d)} (hE : |E| < 2) (hD : 1 ≤ D) (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hs0 : ∀ N, 0 ≤ s N) (htt : ∀ N, t N ≤ t₀)
    (hsub : ∀ N, Good N ⊆ {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)}) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Good N, ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      |Step2Moment.jSnorm (sample d) E D s N v ω - Step2Moment.jSnorm (sample d) E D s N w ω|
        ≤ (N : ℝ) ^ (2 + 2 * D) * |v - w| ^ ((1 : ℝ) / 2) := by
  obtain ⟨K, hK0, hK⟩ := exists_const_jTotNormEv d hE hD ht₀0 ht₀
  have hbig : ∀ᶠ N : ℕ in atTop, max 1 K ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [d.dim, hbig, eventually_one_le_log_W d] with N hdimN hbigN hlogW
  intro ω hω v hv w hw
  have hX : ‖Xmat d N ω‖ ≤ (N : ℝ) := hsub N hω
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_left _ _) hbigN
  have hKN : K ≤ (N : ℝ) := le_trans (le_max_right _ _) hbigN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by
    have := hdimN.1
    exact_mod_cast (by exact_mod_cast this : ((d.W N * d.L N : ℕ) : ℝ) ≤ (N : ℝ))
  have hvt : v ≤ t₀ := hv.2.trans (htt N)
  have hwt : w ≤ t₀ := hw.2.trans (htt N)
  have hlen : |v - w| ≤ 1 := by
    have h1 : s N ≤ v := hv.1
    have h2 : s N ≤ w := hw.1
    have h3 : (0:ℝ) ≤ s N := hs0 N
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h1 := abs_jSnorm_sub_le_event d N ω (D := D) (t₀ := t₀) (s := s) hE (hs0 N) hv.1 hw.1
    hvt hwt ht₀ ht₀0 hlen hlogW hX
  have h2 := hK N hN1 hWL
  have hp0 : (0 : ℝ) ≤ |v - w| ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (abs_nonneg _) _
  have hA0 : (0 : ℝ) < (N : ℝ) ^ (1 + 2 * D) := Real.rpow_pos_of_pos hN0 _
  have hpow : (N : ℝ) ^ (2 + 2 * D) = (N : ℝ) * (N : ℝ) ^ (1 + 2 * D) := by
    rw [show (2 : ℝ) + 2 * D = 1 + (1 + 2 * D) by ring, Real.rpow_add hN0, Real.rpow_one]
  calc |Step2Moment.jSnorm (sample d) E D s N v ω - Step2Moment.jSnorm (sample d) E D s N w ω|
      ≤ |v - w| ^ ((1 : ℝ) / 2) * jTotNormEv d N E D t₀ := h1
    _ ≤ |v - w| ^ ((1 : ℝ) / 2) * (K * (N : ℝ) ^ (1 + 2 * D)) :=
        mul_le_mul_of_nonneg_left h2 hp0
    _ ≤ |v - w| ^ ((1 : ℝ) / 2) * ((N : ℝ) * (N : ℝ) ^ (1 + 2 * D)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKN hA0.le) hp0
    _ = (N : ℝ) ^ (2 + 2 * D) * |v - w| ^ ((1 : ℝ) / 2) := by rw [hpow]; ring

end Size

/-! ### 7. ⭐⭐ The `APrimeHypOn` bundle: every field but `weightedMoment` -/

section Bundle

open Real Gauss Step2FarMart Filter MeasureTheory Step2Bootstrap

/-- The `levpoly` field at `lev ≡ 1`, `Θ ≡ 1`: it says `2 ≤ N`. -/
theorem eventually_levpoly_one {s t mesh : ℕ → ℝ} :
    ∀ᶠ N : ℕ in atTop, ∀ _ws ∈ MomentDuhamelCut.netFinset s t mesh N,
      2 * (1 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) * (1 : ℝ) := by
  filter_upwards [eventually_ge_atTop 2] with N hN _ws _
  have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [Real.rpow_one]; linarith

/-- **⭐⭐ Route (A′)'s interface for the complete `J*_{u,D}/R⁴`, all deterministic fields
discharged.**  `lev ≡ 1`, `Θ ≡ 1`, `Kmod = 2 + 2D`, `γ = 1/2`, `Clev = 1`, and the event may be
**any** sub-event of `{‖X‖ ≤ N}` — which is what lets the caller intersect it with the (S3)
event of `RBM.EarlyQVRateEv` and with Step 1's event without touching the modulus.

Only `weightedMoment` (and the weight `W` itself) is a parameter: that is the one field of
`RBM.Step2Bootstrap.APrimeHypOn` which is *not* deterministic, and it is
`RBM.APrimeModel.aprimeHypOn_of_stepBound''`'s job.

⚠ This is `APrimeHypOn`, never `RBM.Step2Bootstrap.APrimeHyp`: the latter's `modulus` is
quantified over **every** `ω` and is false for `J = jSnorm` (T249's compiled witness
`RBM.t249_witness_norm_gt` leaves every `{‖X‖ ≤ N}`). -/
noncomputable def aprimeHypOn_jSnorm_event (d : Dims) {E D t₀ : ℝ} {s t : ℕ → ℝ}
    {Good : ℕ → Set (Ω d)}
    (hE : |E| < 2) (hD : 1 ≤ D) (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hs0 : ∀ N, 0 ≤ s N) (htt : ∀ N, t N ≤ t₀) (hwindow : ∀ N, s N ≤ t N)
    (hsub : ∀ N, Good N ⊆ {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)})
    (hGmeas : ∀ N, MeasurableSet (Good N))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (mesh : ℕ → ℝ) (hmesh : ∀ N, 0 < mesh N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 + 2 * D) * (1 / mesh N) ^ ((1 : ℝ) / 2) ≤ 1)
    (Ccard : ℝ) (hcard : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard)
    (Wt : ℝ → ℕ → ℕ → Ω d → ℝ)
    (hWmeas : ∀ (δ : ℝ) (N k : ℕ), AEStronglyMeasurable (fun ω => Wt δ N k ω) (band d).P)
    (hW0 : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω d), 0 ≤ Wt δ N k ω)
    (hW1 : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω d), Wt δ N k ω ≤ 1)
    (hWdom : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω d),
      ω ∈ prefNet (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω) s mesh
        (fun N _u => (N : ℝ) ^ (2 * δ) * (1 : ℝ)) N k → 1 ≤ Wt δ N k ω)
    (hmom : WeightedMoment (band d).P
      (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω) s t mesh
      (fun _ _ => (1 : ℝ)) (fun _ => 1) δ₀ Wt) :
    APrimeHypOn (band d).P (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω) s t
      (fun _ _ => (1 : ℝ)) (fun _ => 1) Good where
  window := hwindow
  δ₀ := δ₀
  δ₀_pos := hδ₀
  Θ_pos := fun _ => one_pos
  lev_ge := fun _ _ _ => le_rfl
  J_nonneg := fun N u ω => by
    have h1 : (0:ℝ) ≤ Step2.jS (sample d) E D N u ω :=
      le_trans zero_le_one (Step2Moment.one_le_jS (sample d) N u ω)
    have h2 : (0:ℝ) ≤ Step2Moment.ratR E s N u ^ 4 := by positivity
    exact div_nonneg h1 h2
  meas := fun N u => measurable_jSnorm (sample d) E D s N u
  good_meas := hGmeas
  mesh := mesh
  mesh_pos := hmesh
  Kmod := 2 + 2 * D
  γ := (1 : ℝ) / 2
  γ_pos := by norm_num
  modulus := eventually_modulus_jSnorm_event d hE hD ht₀0 ht₀ hs0 htt hsub
  mesh_fine := hfine
  Ccard := Ccard
  card_le := hcard
  Clev := 1
  Clev_nonneg := zero_le_one
  levpoly := eventually_levpoly_one
  W := Wt
  W_meas := hWmeas
  W_nonneg := hW0
  W_le_one := hW1
  W_dom := hWdom
  weightedMoment := hmom

/-- ⭐ **The bundle's own exponents are `(2 + 2D, 1/2)`**, by `rfl` on the object just built —
not a statement about an abstract pair (the lesson T261 records). -/
theorem aprimeHypOn_jSnorm_event_Kmod (d : Dims) {E D t₀ : ℝ} {s t : ℕ → ℝ}
    {Good : ℕ → Set (Ω d)}
    (hE : |E| < 2) (hD : 1 ≤ D) (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hs0 : ∀ N, 0 ≤ s N) (htt : ∀ N, t N ≤ t₀) (hwindow : ∀ N, s N ≤ t N)
    (hsub : ∀ N, Good N ⊆ {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)})
    (hGmeas : ∀ N, MeasurableSet (Good N))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (mesh : ℕ → ℝ) (hmesh : ∀ N, 0 < mesh N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 + 2 * D) * (1 / mesh N) ^ ((1 : ℝ) / 2) ≤ 1)
    (Ccard : ℝ) (hcard : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard)
    (Wt : ℝ → ℕ → ℕ → Ω d → ℝ)
    (hWmeas : ∀ (δ : ℝ) (N k : ℕ), AEStronglyMeasurable (fun ω => Wt δ N k ω) (band d).P)
    (hW0 : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω d), 0 ≤ Wt δ N k ω)
    (hW1 : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω d), Wt δ N k ω ≤ 1)
    (hWdom : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω d),
      ω ∈ prefNet (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω) s mesh
        (fun N _u => (N : ℝ) ^ (2 * δ) * (1 : ℝ)) N k → 1 ≤ Wt δ N k ω)
    (hmom : WeightedMoment (band d).P
      (fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω) s t mesh
      (fun _ _ => (1 : ℝ)) (fun _ => 1) δ₀ Wt) :
    (aprimeHypOn_jSnorm_event d hE hD ht₀0 ht₀ hs0 htt hwindow hsub hGmeas δ₀ hδ₀ mesh hmesh
        hfine Ccard hcard Wt hWmeas hW0 hW1 hWdom hmom).Kmod = 2 + 2 * D ∧
      (aprimeHypOn_jSnorm_event d hE hD ht₀0 ht₀ hs0 htt hwindow hsub hGmeas δ₀ hδ₀ mesh hmesh
        hfine Ccard hcard Wt hWmeas hW0 hW1 hWdom hmom).γ = (1 : ℝ) / 2 :=
  ⟨rfl, rfl⟩

end Bundle

/-! ### 8. ⭐ `init` is structurally redundant — (2.69) is already in scope -/

section Init

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(2.69) gives `J*_{s,D} ≺ 1` at the left endpoint** — `RBM.stochDom_jSfarSm_init_of_boundsCore`
(T241) for the *unweighted* functional.  The far weight was never used there beyond
`lkFarSm ≤ |(L-K)|`, so dropping it costs nothing. -/
theorem stochDom_jS_init_of_boundsCore (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hB : BoundsCore X E s) (D : ℝ) (hD : 0 < D) :
    StochDom B.P (fun N (_ : Unit) ω => Step2.jS X E D N (s N) ω)
      (fun _ _ _ => (1 : ℝ)) := by
  refine StochDom.of_subset_union (hB.decay D hD) (hB.decay D hD)
    fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [Step1.eventually_one_le_scale_s (B := B) (s := s) (t := t) hE hst ht1 hc,
    eventually_le_rpow (2 : ℝ) (half_pos hτ)] with N hA1 hN2
  intro ω hω
  obtain ⟨u0, hbig0⟩ := hω
  have hbig : (N : ℝ) ^ τ < Step2.jS X E D N (s N) ω := by simpa using hbig0
  by_contra hno
  simp only [Set.mem_union, badSet, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨hno, -⟩ := hno
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hτ0 : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hkey : ∀ a : LoopArg (B.L N) 2,
      ‖Step2.lk X E N (s N) ω a‖
        ≤ (N : ℝ) ^ (τ / 2) *
          tailT (B.W N : ℝ) (B.ell N (s N)) (etaT E (s N)) D
            (zdist (B.L N) (a 0 - a 1)) := by
    intro a
    rw [Step2.norm_lk_eq]
    refine (hno (a 0, a 1)).trans ?_
    exact mul_le_mul_of_nonneg_left (inv_sq_mul_decayProf_le_tT hA1 (a 0) (a 1)) hτ0
  have hJ : Step2.jS X E D N (s N) ω ≤ (N : ℝ) ^ (τ / 2) + 1 := Step2.jStar_le hW0 hkey
  have hsq : (2 : ℝ) * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ := by
    rw [← UnifDetDom.rpow_half_mul_rpow_half N hτ]
    exact mul_le_mul_of_nonneg_right hN2 hτ0
  linarith

/-- **⭐⭐ `RBM.APrimeModel.APrimeSlot.init` has a producer.**  At `u = s_N` the normalization
`R_{s_N} = 1`, so the field is literally `J*_{s,D} ≺ 1`, i.e. (2.69) — which is the field
`RBM.BoundsCore.decay` of the hypothesis `hB` that
`RBM.APrimeModel.boundsCore_step_of_inputs_mergedOn_aprime` already has in scope.

This is the fifth instance of the T241/T242/T243 pattern: a datum listed as an independent slot
only because the assembly did not pass down a hypothesis it already held. -/
theorem stochDom_jSnorm_init_of_boundsCore (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hB : BoundsCore X E s) (D : ℝ) (hD : 0 < D) :
    StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
      (fun _ _ _ => (1 : ℝ)) := by
  have hrw : ∀ (N : ℕ) (ω : Ω),
      Step2Moment.jSnorm X E D s N (s N) ω = Step2.jS X E D N (s N) ω := by
    intro N ω
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have : Step2Moment.ratR E s N (s N) = 1 := div_self (Step2.etaT_pos' hE hs1).ne'
    rw [Step2Moment.jSnorm, this]
    norm_num
  have h := stochDom_jS_init_of_boundsCore X hE hst ht1 hc hB D hD
  refine StochDom.of_subset h fun τ hτ => ⟨τ, hτ, ?_⟩
  refine Filter.Eventually.of_forall fun N ω hω => ?_
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  have hu' : (N : ℝ) ^ τ * 1 < Step2Moment.jSnorm X E D s N (s N) ω := hu
  change (N : ℝ) ^ τ * 1 < Step2.jS X E D N (s N) ω
  rwa [hrw N ω] at hu'

end Init

/-! ### 9. `APrimeSlot` with `init` deleted, and the migrated assembly -/

section Slot'

open MeasureTheory Filter Step2Bootstrap APrimeModel

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **`RBM.APrimeModel.APrimeSlot` with the field `init` deleted** — the two data of route (A′)
that really are open.  `init` is produced by `stochDom_jSnorm_init_of_boundsCore` out of the
`RBM.BoundsCore X E s` the assembly already carries. -/
structure APrimeSlot' (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D : ℝ) where
  /-- The high-probability event carrying the time modulus (in the application `{‖X‖ ≤ N}`). -/
  Good : ℕ → Set Ω
  /-- T249's event-restricted interface of route (A′). -/
  hyp : APrimeHypOn B.P (fun N u ω => Step2Moment.jSnorm X E D s N u ω) s t
    (fun _ _ => (1 : ℝ)) (fun _ => 1) Good
  /-- The event is of high probability. -/
  good : HighProb B.P Good

/-- The forgetful map: every `APrimeSlot` gives an `APrimeSlot'`, so the new table is nowhere
harder to satisfy. -/
def APrimeSlot.toPrime {X : Sample B} {D : ℝ} (S : APrimeSlot X E s t D) :
    APrimeSlot' X E s t D :=
  ⟨S.Good, S.hyp, S.good⟩

/-- **⭐ `APrimeSlot'` + (2.69) = `APrimeSlot`.** -/
def aprimeSlot_of_aprimeSlot' {X : Sample B} {D : ℝ} (S : APrimeSlot' X E s t D)
    (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hB : BoundsCore X E s) (hD : 0 < D) : APrimeSlot X E s t D :=
  ⟨S.Good, S.hyp, S.good, stochDom_jSnorm_init_of_boundsCore X hE hst ht1 hc hB D hD⟩

/-- **⭐⭐ Slot 2, produced from `APrimeSlot'`.** -/
theorem jsNormDom_of_aprimeSlot' {X : Sample B} {D : ℝ} (S : APrimeSlot' X E s t D)
    (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hB : BoundsCore X E s) (hD : 0 < D) : JSNormDom X E s t D :=
  jsNormDom_of_aprimeSlot (aprimeSlot_of_aprimeSlot' S hE hst ht1 hc hB hD)

/-- **One step of the p. 24 grid with slot 2 = `APrimeSlot'`** — `init` gone. -/
theorem boundsCore_step_of_inputs_mergedOn_aprime' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore X E s) (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → APrimeSlot' X E s t D)
    (hcut : CutHypEvOnSlot X E s t)
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45i : Eq45FlowInputs X E s t) (H : Eq548EntryDataEvOn' X E s t) :
    BoundsCore X E t := by
  have hE : |E| < 2 := by linarith
  exact boundsCore_step_of_inputs_mergedOn_aprime X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1
    (fun D hD => jsNormDom_of_aprimeSlot' (Hy D hD) hE hst ht1 hreg.1 hB (by linarith))
    hcut h514 h45i H

/-- **⭐⭐⭐ The merged assembly with slot 2 = `APrimeSlot'`.**

Verbatim `RBM.APrimeModel.thm221NoEL_of_inputs_mergedOnAll_aprime` with the field `init` of the
slot deleted: (2.69) is now produced inside the step from the `RBM.BoundsCore X E s` that
`RBM.Thm221NoEL.step` hands over.  The conclusion is unchanged, `RBM.Thm221NoEL X κ`, on every
window `0 ≤ s ≤ t < 1` including p. 24's first cell. -/
theorem thm221NoEL_of_inputs_mergedOnAll_aprime' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 60 ≤ D → APrimeSlot' X E s t D)
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      BoundsCore X E s → CutHypEvOnSlot X E s t)
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45i : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Eq45FlowInputs X E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      Eq548EntryDataEvOn' X E s t) :
    Thm221NoEL X κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_mergedOn_aprime' X hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (h1 E hE s t hs0 hst ht1 c hc0 hreg)
      (Hy E hE s t hs0 hst ht1 c hc0 hreg)
      (hcut E hE s t hs0 hst ht1 c hc0 hreg hB) (h514 E hE s t hs0 hst ht1 c hc0 hreg)
      (h45i E hE s t hs0 hst ht1 c hc0 hreg) (h548e E hE s t hs0 hst ht1 c hc0 hreg)

end Slot'

/-! ### 10. The good event: `{‖X‖ ≤ N}` ∩ anything else of high probability -/

section GoodEvent

open Real Gauss Filter MeasureTheory

/-- **The slot's good event.**  The modulus of §6 only needs `Good N ⊆ {‖X‖ ≤ N}`, so the
caller is free to intersect in the (S3) event of `RBM.EarlyQVRateEv.stochDom_quadVar_grid`
(T267/T273) and Step 1's event, which is what the `weightedMoment` field will want. -/
def goodEv (d : Dims) (Ξ : ℕ → Set (Ω d)) (N : ℕ) : Set (Ω d) :=
  {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)} ∩ Ξ N

theorem goodEv_subset (d : Dims) (Ξ : ℕ → Set (Ω d)) (N : ℕ) :
    goodEv d Ξ N ⊆ {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)} := Set.inter_subset_left

theorem measurableSet_goodEv (d : Dims) {Ξ : ℕ → Set (Ω d)}
    (hΞ : ∀ N, MeasurableSet (Ξ N)) (N : ℕ) : MeasurableSet (goodEv d Ξ N) :=
  (Gauss.measurableSet_normX_le d N).inter (hΞ N)

/-- **The good event has high probability.**  `RBM.Gauss.highProb_normX_le` (T100) meets any
further `RBM.HighProb` family through `RBM.HighProb.inter`, so the intersection of the D17
event with (S3) and with Step 1's event is again of high probability. -/
theorem highProb_goodEv (d : Dims) (hTM : TraceMomentBound d) {Ξ : ℕ → Set (Ω d)}
    (hΞ : HighProb (band d).P Ξ) : HighProb (band d).P (goodEv d Ξ) :=
  (Gauss.highProb_normX_le d hTM).inter hΞ

/-- **The (S3)-style route, compiled**: any `≺` statement on the model — in the application
`RBM.EarlyQVRateEv.stochDom_quadVar_grid` — becomes, at any level `τ > 0`, a high-probability
event that may be intersected into `Good`. -/
theorem highProb_goodEv_of_stochDom (d : Dims) (hTM : TraceMomentBound d) {U : ℕ → Type*}
    {ξ ζ : ∀ N, U N → Ω d → ℝ} (h : StochDom (band d).P ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProb (band d).P
      (goodEv d (fun N => {ω | ∀ u, ξ N u ω ≤ (N : ℝ) ^ τ * ζ N u ω})) :=
  highProb_goodEv d hTM (h.highProb hτ)

/-- The good event is **eventually non-empty** — the anti-vacuity certificate: the `modulus`
field of the bundle of §7 is not a statement about `∅`. -/
theorem eventually_nonempty_goodEv (d : Dims) (hTM : TraceMomentBound d) {Ξ : ℕ → Set (Ω d)}
    (hΞ : HighProb (band d).P Ξ) : ∀ᶠ N : ℕ in atTop, (goodEv d Ξ N).Nonempty :=
  (highProb_goodEv d hTM hΞ).nonempty (band d).isProbabilityMeasure.measure_univ

end GoodEvent

/-! ### 11. Satisfiability at the **first cell** of the grid of p. 24 -/

section Witness

open Real Gauss Step2FarMart Filter MeasureTheory Step2Bootstrap

/-- The modulus constant of §5 is **strictly positive** at `exampleGrow`, so
`modulus_jSnorm_exampleGrow_zero` is not the vacuous `≤ 0`. -/
theorem jTotNormEv_pos_exampleGrow (N : ℕ) :
    0 < jTotNormEv Dims.exampleGrow N 0 1 (1 / 2) := by
  have hE : |(0 : ℝ)| < 2 := by norm_num
  have hlip : 0 ≤ jSfarSmLip Dims.exampleGrow N 0 1 (1 / 2) :=
    jSfarSmLip_nonneg Dims.exampleGrow N (D := 1) hE (by norm_num)
  have hlk : 0 < lkLipEv Dims.exampleGrow N 0 (1 / 2) := lkLipEv_pos_exampleGrow N
  have hW : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ) := by exact_mod_cast Dims.exampleGrow.W_pos N
  have hWD : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ) ^ (1 : ℝ) := Real.rpow_pos_of_pos hW _
  have hcr : 0 ≤ crudeLk Dims.exampleGrow N 0 (1 / 2) :=
    crudeLk_nonneg Dims.exampleGrow N hE (by norm_num)
  have h1t : (0 : ℝ) < 1 - (1 / 2 : ℝ) := by norm_num
  unfold jTotNormEv
  positivity

/-- ⭐ **The compiled witness for the `modulus` field of `RBM.Step2Bootstrap.APrimeHypOn` at
`J = jSnorm`**, at `d = exampleGrow`, `E = 0`, `D = 1`, window `[0, 1/2]` — **left endpoint
exactly `0`**, D17's first cell.  `Kmod = 2 + 2·1 = 4`, `γ = 1/2`. -/
theorem modulus_jSnorm_exampleGrow_zero :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ {ω : Ω Dims.exampleGrow | ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)},
      ∀ v ∈ Set.Icc ((fun _ : ℕ => (0 : ℝ)) N) ((fun _ : ℕ => (1 / 2 : ℝ)) N),
      ∀ w ∈ Set.Icc ((fun _ : ℕ => (0 : ℝ)) N) ((fun _ : ℕ => (1 / 2 : ℝ)) N),
      |Step2Moment.jSnorm (sample Dims.exampleGrow) 0 1 (fun _ => (0 : ℝ)) N v ω
          - Step2Moment.jSnorm (sample Dims.exampleGrow) 0 1 (fun _ => (0 : ℝ)) N w ω|
        ≤ (N : ℝ) ^ (2 + 2 * (1 : ℝ)) * |v - w| ^ ((1 : ℝ) / 2) :=
  eventually_modulus_jSnorm_event Dims.exampleGrow (t₀ := 1 / 2) (by norm_num) le_rfl
    (by norm_num) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => subset_rfl)

/-- ⭐⭐ **The `APrimeHypOn` bundle with every parameter pinned but the weight and the
`weightedMoment` field**, on p. 24's first cell: `d = exampleGrow`, `E = 0`, `D = 1`,
`s ≡ 0`, `t ≡ 1/2`, `Θ ≡ 1`, `lev ≡ 1`, `mesh = RBM.meshK 4 (1/2) = (N+1)^8`, `Ccard = 9`,
`Good N = {‖X_N‖ ≤ N}`, `Kmod = 4`, `γ = 1/2`, `Clev = 1`.

`mesh_fine` and `card_le` are discharged by `RBM.sat_mesh_pair_event` — the two fields that
pull against each other are jointly satisfiable at *these* exponents — so no deterministic
field of the interface can make it unsatisfiable on the first cell. -/
noncomputable def aprimeHypOn_jSnorm_exampleGrow
    (Wt : ℝ → ℕ → ℕ → Ω Dims.exampleGrow → ℝ)
    (hWmeas : ∀ (δ : ℝ) (N k : ℕ),
      AEStronglyMeasurable (fun ω => Wt δ N k ω) (band Dims.exampleGrow).P)
    (hW0 : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω Dims.exampleGrow), 0 ≤ Wt δ N k ω)
    (hW1 : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω Dims.exampleGrow), Wt δ N k ω ≤ 1)
    (hWdom : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω Dims.exampleGrow),
      ω ∈ prefNet
        (fun N u ω => Step2Moment.jSnorm (sample Dims.exampleGrow) 0 1 (fun _ => (0 : ℝ)) N u ω)
        (fun _ => (0 : ℝ)) (meshK (2 + 2 * (1 : ℝ)) (1 / 2))
        (fun N _u => (N : ℝ) ^ (2 * δ) * (1 : ℝ)) N k → 1 ≤ Wt δ N k ω)
    (hmom : WeightedMoment (band Dims.exampleGrow).P
      (fun N u ω => Step2Moment.jSnorm (sample Dims.exampleGrow) 0 1 (fun _ => (0 : ℝ)) N u ω)
      (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (meshK (2 + 2 * (1 : ℝ)) (1 / 2))
      (fun _ _ => (1 : ℝ)) (fun _ => 1) 1 Wt) :
    APrimeHypOn (band Dims.exampleGrow).P
      (fun N u ω => Step2Moment.jSnorm (sample Dims.exampleGrow) 0 1 (fun _ => (0 : ℝ)) N u ω)
      (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ)) (fun _ => 1)
      (fun N => {ω : Ω Dims.exampleGrow | ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)}) :=
  aprimeHypOn_jSnorm_event Dims.exampleGrow (E := 0) (D := 1) (t₀ := 1 / 2)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => subset_rfl)
    (fun N => Gauss.measurableSet_normX_le Dims.exampleGrow N) 1 one_pos
    (meshK (2 + 2 * (1 : ℝ)) (1 / 2)) (meshK_pos _ _)
    ((sat_mesh_pair_event (D := 1) (s := fun _ => (0 : ℝ)) (t := fun _ => (1 / 2 : ℝ))
      le_rfl (fun _ => le_rfl) (fun _ => by norm_num)).2.1)
    ((2 + 2 * (1 : ℝ)) / ((1 : ℝ) / 2) + 1)
    ((sat_mesh_pair_event (D := 1) (s := fun _ => (0 : ℝ)) (t := fun _ => (1 / 2 : ℝ))
      le_rfl (fun _ => le_rfl) (fun _ => by norm_num)).2.2)
    Wt hWmeas hW0 hW1 hWdom hmom


/-- **An explicit point of the good event, at every `N`**: `ω = 0` has `X = 0`
(`RBM.Gauss.Xmat_zero`), so `‖X‖ = 0 ≤ N`.  Unlike `eventually_nonempty_first_cell` this needs
no trace-moment hypothesis and no `∀ᶠ N`: the event of the witness is **never** empty. -/
theorem zero_mem_normX_le (d : Dims) (N : ℕ) :
    (0 : Ω d) ∈ {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)} := by
  have hz : Xmat d N (0 : Ω d) = 0 := by ext i j; simp [Xmat, Xentry]
  have h : ‖Xmat d N (0 : Ω d)‖ = 0 := by rw [hz, norm_zero]
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  change ‖Xmat d N (0 : Ω d)‖ ≤ (N : ℝ)
  rw [h]; exact hN

/-- **The window `[0, 1/2]` of the witness is non-degenerate** — it contains `0` and is not a
point, so the modulus really constrains a difference. -/
theorem window_first_cell_nondegenerate :
    (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
      (0 : ℝ) < 1 / 2 := ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The bundle's pair `(Kmod, γ) = (4, 1/2)` is outside T258's refutation range**
`Kmod ≤ 2γ`. -/
theorem first_cell_pair_outside_refutation : ¬ ((2 + 2 * (1 : ℝ)) ≤ 2 * ((1 : ℝ) / 2)) := by
  norm_num

/-- **The good event of the witness is eventually non-empty**, granted the trace moments —
so the `modulus` field of `aprimeHypOn_jSnorm_exampleGrow` is not vacuously true. -/
theorem eventually_nonempty_first_cell (hTM : TraceMomentBound Dims.exampleGrow) :
    ∀ᶠ N : ℕ in atTop,
      {ω : Ω Dims.exampleGrow | ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)}.Nonempty :=
  Gauss.eventually_nonempty_normX_le Dims.exampleGrow hTM

end Witness

end APrimeSlotFields

end RBM
