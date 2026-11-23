/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

module

public import RBM1D.MainDefs
public import RBM1D.Flow.OUCommonCarrier
public import RBM1D.Flow.EnergyUniform
public import RBM1D.Gauss.DistEq

@[expose] public section

/-!
# The Step 1 interface of Theorem 2.6: the OU marginal, the GUE matrix and [51, Theorem 2.2]

This file fixes the statements through which Step 1 (2.21) and the final combination
(2.24) + (2.21) ⇒ (2.18) of the proof of Theorem 2.6 are formalized.

* `ouPairing`, `gueMatPairing`, `bandPairing`: `∫ O(α) ρ^{(k)}(E + α/M) dα` for the OU marginal
  `H_t` of (2.19) (one-time law, `ouMatrix` on `ouProductMeasure`), for the GUE matrix `H_∞`,
  and for the band matrix `H = H_0`.  Here `M = L W` is the matrix size (`msize`).
* `BulkUniversalityMat` is (2.18) with the GUE matrix model; `Step1Target` is (2.21) for
  `τ_* ∈ (0,1)`; `Step2Output` is (2.24) at some `τ_U ∈ (0,1)`; `theorem2_6_mat_of_steps` is the
  final combination in the proof of Theorem 2.6 (§2.3).
* The only external input is `LSY22'` (`Flow/DBMInputNorm.lean`): [51, Theorem 2.2]
  (Landon–Sosoe–Yau) read for the complex
  Hermitian case (GOE → GUE, `docs/PAPER-VS-LEAN.md` §4.4), with the premises of Def 2.1, (2.5),
  (2.6), (2.8), required only eventually, and the rate `C N^{-κ}` weakened to `→ 0`.
* `OUFlowLaw` is a law-carrying OU flow (the fixed-time law is part of the structure), with the
  witness `ouCommonFlowLaw`.
* `BandTracialLocalLaw` (the averaged part of Theorem 2.3 for the Gaussian band matrix) and
  `GUELocalLaw` are the local-law inputs of Step 1.
-/

open MeasureTheory Filter Matrix Topology

namespace RBM.Gauss

variable (d : Dims)

/-- `∫ O(α) ρ^{(k)}_{H_t}(E + α/M) dα` for the fixed-time OU marginal
`H_t = e^{-t/2} H + √(1 - e^{-t}) H_GUE` of (2.19). -/
noncomputable def ouPairing (N : ℕ) (t : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ) : ℝ :=
  RBM.corrPairing (ouProductMeasure d N) (ouMatrix d N t) (ouMatrix_isHermitian d N t) k O E

/-- **Step 1, (2.21)**, for `τ_* ∈ (0,1)`, `t_* = M^{-1+τ_*}`. -/
def Step1Target (κ : ℝ) : Prop :=
  ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ k : ℕ,
    ∀ O : (Fin k → ℝ) → ℝ, RBM.IsTestFun O →
      Tendsto (fun N => ouPairing d N ((Gauss.band d).tPow τs N) k O E -
        gueMatPairing d N k O E) atTop (𝓝 0)

/-- **Step 2's output, (2.24)**: for every bulk `E` and `k` there is `τ_U ∈ (0,1)` such that
the correlation functions of `H_0` and `H_{t_U}`, `t_U = M^{-1+τ_U}`, have the same limit. -/
def Step2Output (κ : ℝ) : Prop :=
  ∀ E : ℝ, |E| ≤ 2 - κ → ∀ k : ℕ, ∃ τU : ℝ, 0 < τU ∧ τU < 1 ∧
    ∀ O : (Fin k → ℝ) → ℝ, RBM.IsTestFun O →
      Tendsto (fun N => bandPairing d N k O E -
        ouPairing d N ((Gauss.band d).tPow τU N) k O E) atTop (𝓝 0)

/-- **Theorem 2.6 from Steps 1 and 2**: (2.24) and (2.21) with `t_* = t_U` give (2.18). -/
theorem theorem2_6_mat_of_steps (κ : ℝ) (h1 : Step1Target d κ) (h2 : Step2Output d κ) :
    BulkUniversalityMat d κ := by
  intro E hE k O hO
  obtain ⟨τU, h0, h1', h224⟩ := h2 E hE k
  have h := (h224 O hO).add (h1 τU h0 h1' E hE k O hO)
  rw [add_zero] at h
  refine h.congr fun N => ?_
  ring

/-- `∫ O(α) p^{(k)}(E + α/(Mρ)) dα`, written as `ρ^k · ∫ O(ρβ) p^{(k)}(E + β/M) dβ`
(change of variables `α = ρβ`; valid for `ρ > 0`). -/
noncomputable def scaledPairing {Ω' : Type*} [MeasurableSpace Ω'] {n : Type*} [Fintype n]
    [DecidableEq n] (Pm : Measure Ω') (Hm : Ω' → Matrix n n ℂ) (hH : ∀ ω, (Hm ω).IsHermitian)
    (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E ρ : ℝ) : ℝ :=
  ρ ^ k * RBM.corrPairing Pm Hm hH k (fun β => O (fun j => ρ * β j)) E

/-- **The OU flow (2.19) through its one-time laws**: a Hermitian matrix path whose law at each
fixed time `t ≥ 0` is that of `e^{-t/2} H + √(1 - e^{-t}) H_GUE`. -/
structure OUFlowLaw {Ω' : Type*} [MeasurableSpace Ω'] (Pm : Measure Ω') where
  Ht : ∀ N, ℝ → Ω' → Matrix (d.Idx N) (d.Idx N) ℂ
  measurable : ∀ N t, Measurable (Ht N t)
  hermitian : ∀ N t ω, (Ht N t ω).IsHermitian
  law : ∀ N t, 0 ≤ t → Pm.map (Ht N t) = (ouProductMeasure d N).map (ouMatrix d N t)

/-- The witness of `OUFlowLaw` on the common carrier (all sizes, all times on one space). -/
noncomputable def ouCommonFlowLaw : OUFlowLaw d (ouCommonMeasure d) where
  Ht N t ω := ouMatrix d N t (ouCommonProjection d N ω)
  measurable N t := by
    have h : Measurable (ouMatrix d N t) := by
      rw [show ouMatrix d N t = ouInterpolatedMatrix d N t from
        funext (ouMatrix_eq_interpolatedMatrix d N t)]
      apply measurable_pi_iff.mpr; intro i
      apply measurable_pi_iff.mpr; intro j
      have hs : Measurable (ouInterpolatedSample d N t) := by
        apply measurable_pi_iff.mpr; intro c
        simp only [ouInterpolatedSample]; fun_prop
      exact (measurable_Xentry d N i j).comp hs
    exact h.comp (ouCommonProjection_measurable d N)
  hermitian N t ω := ouMatrix_isHermitian d N t _
  law N t _ := by
    have h : Measurable (ouMatrix d N t) := by
      rw [show ouMatrix d N t = ouInterpolatedMatrix d N t from
        funext (ouMatrix_eq_interpolatedMatrix d N t)]
      apply measurable_pi_iff.mpr; intro i
      apply measurable_pi_iff.mpr; intro j
      have hs : Measurable (ouInterpolatedSample d N t) := by
        apply measurable_pi_iff.mpr; intro c
        simp only [ouInterpolatedSample]; fun_prop
      exact (measurable_Xentry d N i j).comp hs
    change (ouCommonMeasure d).map ((ouMatrix d N t) ∘ ouCommonProjection d N) = _
    rw [← Measure.map_map h (ouCommonProjection_measurable d N), ouCommonProjection_map]

/-- `ρ_sc(E) = Im m^{(E)} / π` on `[-2, 2]`. -/
theorem rhoSc_eq_mE_im {E : ℝ} (hE : |E| ≤ 2) : rhoSc E = (mE E).im / Real.pi := by
  simp only [rhoSc, hE, ↓reduceIte, mE_im]
  field_simp

/-- **The averaged local law for the Gaussian band matrix**: the third conjunct of
`RBM.localSemicircleLaw_of_boundsCoreN_of_z` for `B = Gauss.band d`, `Hband = Xmat d N`, with the
domain hypotheses on `z` exactly as there. -/
def BandTracialLocalLaw (κ : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ z : ℕ → ℂ, (∀ N, 0 < (z N).im) → (∀ N, (z N).im ≤ 1) →
    (∀ N, |(z N).re| ≤ 2 - κ) → (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) →
    ∀ τ' : ℝ, 0 < τ' → ∀ D : ℝ, 0 < D →
      ∀ᶠ N : ℕ in atTop, (Gauss.band d).P {ω | ∃ _u : Unit,
        ((Gauss.band d).W N : ℝ) ^ τ' * ((Gauss.band d).zScale N (z N))⁻¹ <
          ‖(((Gauss.band d).L N * (Gauss.band d).W N : ℕ) : ℂ)⁻¹ *
              (green (Xmat d N ω) (z N)).trace - msc (z N)‖}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- **The averaged GUE local law** in the bulk, down to `Im z ≥ N^{-1+τ}`. -/
def GUELocalLaw : Prop :=
  ∀ κ > (0 : ℝ), ∀ τ > (0 : ℝ), ∀ z : ℕ → ℂ, (∀ N, 0 < (z N).im) → (∀ N, (z N).im ≤ 1) →
    (∀ N, |(z N).re| ≤ 2 - κ) → (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) →
    ∀ τ' > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      gueMeasure d N {ω | (N : ℝ) ^ τ' * (msize d N * (z N).im)⁻¹ <
        ‖RBM.stieltjes (Xmat d N ω) (z N) - msc (z N)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))

/-! ### Check: `Step1Target` is (2.21) with `ρ_{H_∞}` the GUE matrix -/

end RBM.Gauss
