/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeDuhamelModel
import RBM1D.Gauss.Lemma514Q716

/-!
# Bad-event estimates for the weighted A-prime Duhamel step

The auxiliary event in the estimates may depend on the moment order and on the
small exponent.  It is used only inside the full-space weighted norm.  The
weight itself is never multiplied by an event indicator, so its differentiability
is unchanged.  The evolved (5.42) envelope remains a conditional input.
-/

namespace RBM.APrimeBadSplit

open MeasureTheory RBM.MomentDuhamel RBM.APrimeDuhamelModel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The weighted moment is the ordinary moment of the root-scaled variable. -/
theorem momNorm_root_eq {q : ℕ} (hq : q ≠ 0) {W Z : Ω → ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω) :
    momNorm P q (fun ω => W ω ^ ((1 : ℝ) / q) * Z ω) =
      (∫ ω, W ω * |Z ω| ^ q ∂P) ^ ((1 : ℝ) / q) := by
  rw [momNorm]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hW0 ω) _), mul_pow]
  have he : ((1 : ℝ) / q) * q = 1 := by
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    field_simp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hW0 ω), he, Real.rpow_one]

/-- A weighted norm split over an auxiliary event.  The event can be chosen
separately for each `q`, `δ`, and `N`; there is no event restriction on the weight. -/
theorem weighted_norm_le_of_event {q : ℕ} (hq : q ≠ 0) {W Z : Ω → ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1)
    (hZi : Integrable (fun ω => W ω * |Z ω| ^ q) P)
    {E : Set Ω} (hE : MeasurableSet E) {good Env pr : ℝ}
    (hgood : 0 ≤ good) (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hZgood : ∀ ω ∈ E, |Z ω| ≤ good)
    (hZall : ∀ ω, |Z ω| ≤ Env)
    (hP : (P Eᶜ).toReal ≤ pr) :
    (∫ ω, W ω * |Z ω| ^ q ∂P) ^ ((1 : ℝ) / q)
      ≤ good + Env * pr ^ ((1 : ℝ) / q) := by
  let Zr : Ω → ℝ := fun ω => W ω ^ ((1 : ℝ) / q) * Z ω
  have hZi' : Integrable (fun ω => |Zr ω| ^ q) P := by
    apply hZi.congr
    filter_upwards [] with ω
    dsimp [Zr]
    symm
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hW0 ω) _), mul_pow]
    have he : ((1 : ℝ) / q) * q = 1 := by
      have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      field_simp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hW0 ω), he, Real.rpow_one]
  have hroot : ∀ ω, W ω ^ ((1 : ℝ) / q) ≤ 1 := by
    intro ω
    calc W ω ^ ((1 : ℝ) / q) ≤ (1 : ℝ) ^ ((1 : ℝ) / q) :=
      Real.rpow_le_rpow (hW0 ω) (hW1 ω) (by positivity)
      _ = 1 := by simp
  have hZrgood : ∀ ω ∈ E, |Zr ω| ≤ good := by
    intro ω hω
    dsimp [Zr]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hW0 ω) _)]
    calc W ω ^ ((1 : ℝ) / q) * |Z ω| ≤ 1 * |Z ω| :=
          mul_le_mul_of_nonneg_right (hroot ω) (abs_nonneg _)
      _ = |Z ω| := one_mul _
      _ ≤ good := hZgood ω hω
  have hZrall : ∀ ω, |Zr ω| ≤ Env := by
    intro ω
    dsimp [Zr]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hW0 ω) _)]
    calc W ω ^ ((1 : ℝ) / q) * |Z ω| ≤ 1 * |Z ω| :=
          mul_le_mul_of_nonneg_right (hroot ω) (abs_nonneg _)
      _ = |Z ω| := one_mul _
      _ ≤ Env := hZall ω
  have hbase := RBM.Gauss.momNorm_le_affine_on_event (P := P) hq
    (Y := fun _ => (0 : ℝ)) (Z := Zr) (Ξ := E)
    (c := 0) (d := good) (Env := Env) (pr := pr)
    (by simp) (by simp) hZi' hE (by simp) hgood hEnv hpr
    (by intro ω hω; simpa using hZrgood ω hω) hZrall hP
  simp only [zero_mul, zero_add] at hbase
  exact (momNorm_root_eq (P := P) hq hW0).symm.le.trans hbase

/-- `hdrift`: the auxiliary good event supplies the drift envelope. -/
theorem drift_norm_le_of_event {p : ℕ} (hp : 1 ≤ p) {W G : Ω → ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1)
    (hGi : Integrable (fun ω => W ω * |G ω| ^ (2 * p)) P)
    {E : Set Ω} (hE : MeasurableSet E) {A Env pr : ℝ}
    (hA : 0 ≤ A) (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hGgood : ∀ ω ∈ E, |G ω| ≤ A) (hGall : ∀ ω, |G ω| ≤ Env)
    (hP : (P Eᶜ).toReal ≤ pr) :
    momNormW P W p G ≤ A + Env * pr ^ ((1 : ℝ) / (2 * p)) := by
  have hq : 2 * p ≠ 0 := by omega
  simpa [momNormW, Nat.cast_mul] using
    weighted_norm_le_of_event (P := P) hq hW0 hW1 hGi hE hA hEnv hpr
      hGgood hGall hP

/-- `hqv`: the evolved rate enters through its event-restricted (5.42) bound.
A global polynomial envelope pays for the complement. -/
theorem evolved_qv_norm_le_of_event {d : RBM.Gauss.Dims} {N p : ℕ} (hp : 1 ≤ p)
    {Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {u : ℝ}
    {W : RBM.Gauss.Ω d → ℝ} (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1)
    (hQi : Integrable (fun ω => W ω *
      |qvRateEvolved d N Ψ₁ u ω| ^ p) (RBM.Gauss.P d))
    {E : Set (RBM.Gauss.Ω d)} (hE : MeasurableSet E)
    {Qev Env pr : ℝ} (hQev : 0 ≤ Qev) (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hEv : EvolvedQVBound d N Ψ₁ E u Qev)
    (hQall : ∀ ω, qvRateEvolved d N Ψ₁ u ω ≤ Env)
    (hP : ((RBM.Gauss.P d) Eᶜ).toReal ≤ pr) :
    RBM.APrimeModel.rateNormW (RBM.Gauss.P d) W p (qvRateEvolved d N Ψ₁ u)
      ≤ Qev + Env * pr ^ ((1 : ℝ) / p) := by
  have hp' : p ≠ 0 := by omega
  exact weighted_norm_le_of_event (P := RBM.Gauss.P d) hp' hW0 hW1 hQi
    hE hQev hEnv hpr
    (by intro ω hω; rw [abs_of_nonneg (qvRateEvolved_nonneg d N Ψ₁ u ω)]; exact hEv ω hω)
    (by intro ω; rw [abs_of_nonneg (qvRateEvolved_nonneg d N Ψ₁ u ω)]; exact hQall ω)
    hP

/-! The cross term is an `L¹` bad-event split.  The pointwise (S5) estimate
is applied to every sample; only the evolved rate envelope uses `E`. -/

noncomputable def crossAbsSum (d : RBM.Gauss.Dims) (N : ℕ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (wD : (d.Idx N × d.Idx N × Bool) → RBM.Gauss.Ω d → ℝ)
    (u : ℝ) (ω : RBM.Gauss.Ω d) : ℝ :=
  ∑ q ∈ RBM.Gauss.usedCoord d N,
    (RBM.Gauss.gvar d (RBM.Gauss.crd d N q) : ℝ) *
      (|wD q ω| * ‖RBM.Gauss.coordD1 d N (Ψ u) (RBM.Gauss.Hflow d N u ω) q‖)

theorem crossAbsSum_nonneg (d : RBM.Gauss.Dims) (N : ℕ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (wD : (d.Idx N × d.Idx N × Bool) → RBM.Gauss.Ω d → ℝ)
    (u : ℝ) (ω : RBM.Gauss.Ω d) :
    0 ≤ crossAbsSum d N Ψ wD u ω := by
  unfold crossAbsSum
  exact Finset.sum_nonneg fun q _ => mul_nonneg
    (RBM.Gauss.gvar d (RBM.Gauss.crd d N q)).2
    (mul_nonneg (abs_nonneg _) (norm_nonneg _))

/-- The `crossPart` application.  `hS5` is pointwise on the whole sample
space; its rate factor has the conditional evolved (5.42) bound on `E`.
The polynomial envelope `hAll` alone is used outside `E`.  No derivative
vanishing assumption outside the event is present. -/
theorem crossPart_le_of_event {d : RBM.Gauss.Dims} {N : ℕ}
    {T : Set ℝ} {Ψ Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {w : RBM.Gauss.Ω d → ℝ}
    {wD : (d.Idx N × d.Idx N × Bool) → RBM.Gauss.Ω d → ℝ}
    (h : RBM.Gauss.TestFunT₁ d N T Ψ) (hw : RBM.Gauss.WeightC1 d N w wD)
    {u : ℝ} (hu : u ∈ T) (hu0 : 0 < u)
    {E : Set (RBM.Gauss.Ω d)} (hE : MeasurableSet E)
    {A : RBM.Gauss.Ω d → ℝ} {Cs Amax Qev Env pr : ℝ}
    (hCs : 0 ≤ Cs) (hA0 : ∀ ω, 0 ≤ A ω) (hAmax : 0 ≤ Amax)
    (hQev : 0 ≤ Qev) (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hS5 : ∀ ω, crossAbsSum d N Ψ wD u ω ≤
      Cs * (A ω * √(qvRateEvolved d N Ψ₁ u ω)))
    (hEv : EvolvedQVBound d N Ψ₁ E u Qev)
    (hAgood : ∀ ω ∈ E, A ω ≤ Amax)
    (hAll : ∀ ω, crossAbsSum d N Ψ wD u ω ≤ Env)
    (hP : ((RBM.Gauss.P d) Eᶜ).toReal ≤ pr) :
    crossPart d N Ψ wD u ≤
      (1 / (2 * √u)) * (Cs * (Amax * √Qev) + Env * pr) := by
  let Z := crossAbsSum d N Ψ wD u
  have hZi : Integrable Z (RBM.Gauss.P d) :=
    APrimeDuhamelModel.integrable_crossSum h hw hu
  have hZ0 : ∀ ω, 0 ≤ Z ω := crossAbsSum_nonneg d N Ψ wD u
  have hZgood : ∀ ω ∈ E, |Z ω| ≤ Cs * (Amax * √Qev) := by
    intro ω hω
    rw [abs_of_nonneg (hZ0 ω)]
    have hq : √(qvRateEvolved d N Ψ₁ u ω) ≤ √Qev :=
      Real.sqrt_le_sqrt (hEv ω hω)
    calc Z ω ≤ Cs * (A ω * √(qvRateEvolved d N Ψ₁ u ω)) := hS5 ω
      _ ≤ Cs * (Amax * √Qev) := by
        apply mul_le_mul_of_nonneg_left _ hCs
        exact mul_le_mul (hAgood ω hω) hq (Real.sqrt_nonneg _) hAmax
  have hZall : ∀ ω, |Z ω| ≤ Env := by
    intro ω
    rw [abs_of_nonneg (hZ0 ω)]
    exact hAll ω
  have hZabs : Integrable (fun ω => |Z ω| ^ (1 : ℕ)) (RBM.Gauss.P d) := by
    have heq : (fun ω => |Z ω| ^ (1 : ℕ)) = Z := by
      funext ω
      simp [abs_of_nonneg (hZ0 ω)]
    rwa [heq]
  have hnorm := RBM.Gauss.momNorm_le_affine_on_event
    (P := RBM.Gauss.P d) (q := 1) (by decide)
    (Y := fun _ => (0 : ℝ)) (Z := Z) (Ξ := E)
    (c := 0) (d := Cs * (Amax * √Qev)) (Env := Env) (pr := pr)
    (by simp) (by simp) hZabs hE (by simp) (by positivity) hEnv hpr
    (by intro ω hω; simpa using hZgood ω hω) hZall hP
  have hint : (∫ ω, Z ω ∂(RBM.Gauss.P d)) ≤
      Cs * (Amax * √Qev) + Env * pr := by
    simp only [momNorm, Nat.cast_one, div_one, Real.rpow_one, pow_one,
      zero_mul, zero_add, Real.rpow_one] at hnorm
    have heq : (fun ω => |Z ω|) = Z := by
      funext ω
      exact abs_of_nonneg (hZ0 ω)
    rwa [heq] at hnorm
  calc crossPart d N Ψ wD u
      ≤ (1 / (2 * √u)) * ∫ ω, Z ω ∂(RBM.Gauss.P d) :=
        APrimeDuhamelModel.crossPart_le_integral h hw hu hu0
    _ ≤ (1 / (2 * √u)) * (Cs * (Amax * √Qev) + Env * pr) :=
        mul_le_mul_of_nonneg_left hint (by positivity)

/-- The Hölder version used by `momFlowDeriv_le`: the event error stays in
the `L^{2p}` rate norm and therefore multiplies the same moment power as the
main (S5) term.  `hS5` is global; (5.42) is used only on `E`. -/
theorem crossPart_le_of_S5_event {d : RBM.Gauss.Dims} {N p : ℕ} (hp : 1 ≤ p)
    {T : Set ℝ} {Ψ Ψ₁ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {w : RBM.Gauss.Ω d → ℝ}
    {wD : (d.Idx N × d.Idx N × Bool) → RBM.Gauss.Ω d → ℝ}
    (h : RBM.Gauss.TestFunT₁ d N T Ψ) (hw : RBM.Gauss.WeightC1 d N w wD)
    {u : ℝ} (hu : u ∈ T) (hu0 : 0 < u)
    {E : Set (RBM.Gauss.Ω d)} (hE : MeasurableSet E)
    {Cs Qev Env pr : ℝ} (hCs : 0 ≤ Cs) (hQev : 0 ≤ Qev)
    (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hS5 : ∀ ω, crossAbsSum d N Ψ wD u ω ≤
      √u * Cs * (|wscale w p (flowY d N Ψ₁ u) ω| ^ (2 * p - 1) *
        √(qvRateEvolved d N Ψ₁ u ω)))
    (hEv : EvolvedQVBound d N Ψ₁ E u Qev)
    (hQall : ∀ ω, qvRateEvolved d N Ψ₁ u ω ≤ Env)
    (hP : ((RBM.Gauss.P d) Eᶜ).toReal ≤ pr)
    (hYm : AEStronglyMeasurable (wscale w p (flowY d N Ψ₁ u)) (RBM.Gauss.P d))
    (hQm : AEStronglyMeasurable (fun ω => √(qvRateEvolved d N Ψ₁ u ω))
      (RBM.Gauss.P d))
    (hYi : Integrable (fun ω => |wscale w p (flowY d N Ψ₁ u) ω| ^ (2 * p))
      (RBM.Gauss.P d))
    (hQi : Integrable (fun ω => |√(qvRateEvolved d N Ψ₁ u ω)| ^ (2 * p))
      (RBM.Gauss.P d))
    (hProdInt : Integrable (fun ω => √u * Cs *
      (|wscale w p (flowY d N Ψ₁ u) ω| ^ (2 * p - 1) *
        √(qvRateEvolved d N Ψ₁ u ω))) (RBM.Gauss.P d)) :
    crossPart d N Ψ wD u ≤
      (1 / 2 : ℝ) * Cs *
        (∫ ω, |wscale w p (flowY d N Ψ₁ u) ω| ^ (2 * p) ∂(RBM.Gauss.P d)) ^
          ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
        (√Qev + √Env * pr ^ ((1 : ℝ) / (2 * p))) := by
  let Q : RBM.Gauss.Ω d → ℝ := fun ω => qvRateEvolved d N Ψ₁ u ω
  let Y : RBM.Gauss.Ω d → ℝ := wscale w p (flowY d N Ψ₁ u)
  have hq : 2 * p ≠ 0 := by omega
  have hrate : momNorm (RBM.Gauss.P d) (2 * p) (fun ω => √(Q ω)) ≤
      √Qev + √Env * pr ^ ((1 : ℝ) / (2 * p)) := by
    have hh := weighted_norm_le_of_event (P := RBM.Gauss.P d) hq
      (W := fun _ => (1 : ℝ)) (Z := fun ω => √(Q ω))
      (by simp) (by simp) (by simpa using hQi) hE
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hpr
      (by
        intro ω hω
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (hEv ω hω))
      (by
        intro ω
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (hQall ω)) hP
    simpa [momNorm, Nat.cast_mul] using hh
  have hholder := MomentDuhamel.integral_pow_sub_one_mul_le
    (P := RBM.Gauss.P d) hp hYm hQm hYi hQi
  have hmono : (∫ ω, crossAbsSum d N Ψ wD u ω ∂(RBM.Gauss.P d)) ≤
      ∫ ω, √u * Cs * (|Y ω| ^ (2 * p - 1) * √(Q ω)) ∂(RBM.Gauss.P d) :=
    integral_mono (APrimeDuhamelModel.integrable_crossSum h hw hu) hProdInt hS5
  have hstep : crossPart d N Ψ wD u ≤
      (1 / (2 * √u)) * (√u * Cs *
        ((∫ ω, |Y ω| ^ (2 * p) ∂(RBM.Gauss.P d)) ^
          ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
          momNorm (RBM.Gauss.P d) (2 * p) (fun ω => √(Q ω)))) := by
    calc crossPart d N Ψ wD u
        ≤ (1 / (2 * √u)) * ∫ ω, crossAbsSum d N Ψ wD u ω ∂(RBM.Gauss.P d) :=
          APrimeDuhamelModel.crossPart_le_integral h hw hu hu0
      _ ≤ (1 / (2 * √u)) *
          ∫ ω, √u * Cs * (|Y ω| ^ (2 * p - 1) * √(Q ω)) ∂(RBM.Gauss.P d) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (1 / (2 * √u)) * (√u * Cs *
          ∫ ω, |Y ω| ^ (2 * p - 1) * √(Q ω) ∂(RBM.Gauss.P d)) := by
          rw [integral_const_mul]
      _ ≤ (1 / (2 * √u)) * (√u * Cs *
          ((∫ ω, |Y ω| ^ (2 * p) ∂(RBM.Gauss.P d)) ^
            ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
            momNorm (RBM.Gauss.P d) (2 * p) (fun ω => √(Q ω)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (by simpa [Y, Q, abs_of_nonneg (Real.sqrt_nonneg _)]
            using hholder) (by positivity)
  have hsqrt : √u ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu0)
  have hdiv : (1 / (2 * √u)) * (√u * Cs *
        ((∫ ω, |Y ω| ^ (2 * p) ∂(RBM.Gauss.P d)) ^
          ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
          momNorm (RBM.Gauss.P d) (2 * p) (fun ω => √(Q ω)))) =
      (1 / 2 : ℝ) * Cs *
        (∫ ω, |Y ω| ^ (2 * p) ∂(RBM.Gauss.P d)) ^
          ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
        momNorm (RBM.Gauss.P d) (2 * p) (fun ω => √(Q ω)) := by
    field_simp
  rw [hdiv] at hstep
  exact hstep.trans (by
    apply mul_le_mul_of_nonneg_left hrate
    positivity)

/-- Algebraic bridge from the preceding event estimate to the `hcross`
argument of `APrimeDuhamelModel.momFlowDeriv_le`. -/
theorem crossPart_budget_of_event_bound {d : RBM.Gauss.Dims} {N p : ℕ}
    (hp : 1 ≤ p)
    {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {wD : (d.Idx N × d.Idx N × Bool) → RBM.Gauss.Ω d → ℝ}
    {u Cs Rbd φa : ℝ}
    (hbound : crossPart d N Ψ wD u ≤ (1 / 2 : ℝ) * Cs * φa * Rbd) :
    crossPart d N Ψ wD u ≤
      2 * (p : ℝ) * φa * ((Cs * Rbd) / (4 * (p : ℝ))) := by
  apply APrimeDuhamelModel.crossPart_le_budget hp
  convert hbound using 1 <;> ring

/-! A satisfiability check with a nonconstant smooth weight and nonzero
observable.  The universal auxiliary event is enough to test the joint shape
of all the hypotheses without imposing an artificial vanishing condition. -/

theorem drift_event_nontrivial_witness (d : RBM.Gauss.Dims) (N : ℕ)
    (e : RBM.Gauss.Coord d) :
    APrimeDuhamelModel.cosW d e (fun _ => 0) ≠
      APrimeDuhamelModel.cosW d e (fun _ => Real.pi) ∧
    (1 : ℝ) ≠ 0 ∧
    momNormW (RBM.Gauss.P d) (APrimeDuhamelModel.cosW d e) 1 (fun _ => 1) ≤ 1 := by
  refine ⟨APrimeDuhamelModel.cosW_ne d e, one_ne_zero, ?_⟩
  let W := APrimeDuhamelModel.cosW d e
  have hwi : Integrable W (RBM.Gauss.P d) :=
    RBM.Gauss.integrable_of_continuous_of_bound
      (APrimeDuhamelModel.weightC1_cosW d N e).cont (by
        intro ω
        rw [Real.norm_eq_abs, abs_of_nonneg (APrimeDuhamelModel.cosW_nonneg d e ω)]
        exact APrimeDuhamelModel.cosW_le_one d e ω)
  have hGi : Integrable (fun ω => W ω * |(1 : ℝ)| ^ (2 * 1))
      (RBM.Gauss.P d) := by simpa using hwi
  have hmain := drift_norm_le_of_event (P := RBM.Gauss.P d) (p := 1) (by omega)
    (W := W) (G := fun _ => 1)
    (APrimeDuhamelModel.cosW_nonneg d e)
    (APrimeDuhamelModel.cosW_le_one d e)
    hGi (E := Set.univ) MeasurableSet.univ
    (A := 1) (Env := 1) (pr := 0)
    (by positivity) (by positivity) (by positivity)
    (by intro ω _; simp) (by intro ω; simp) (by simp)
  simpa [W] using hmain

end RBM.APrimeBadSplit
