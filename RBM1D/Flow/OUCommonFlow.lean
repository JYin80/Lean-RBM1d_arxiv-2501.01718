/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.OUCommonCarrier
import RBM1D.Flow.Universality

/-!
# The `OUFlow` instance carried by the common carrier

The interface `RBM.OUFlow` of
`Flow/Universality.lean` instantiated on the common carrier `ouCommonBand d` of
`Flow/OUCommonCarrier.lean`, its measurability, and the two single-scale output interfaces
`FlowLocalLaw` ((2.26) at the paper's scale `η = N^{-1+2τ_U}`) and `FlowEq747` ((7.47) for
`H_{t_N}` along every admissible time sequence).  This module states the flow's plumbing only;
it does not assume or discharge `FlowLocalLaw`/`FlowEq747` themselves.

Also proves a small purely-filter uniformization lemma used to turn a family of eventual bounds
indexed by admissible time sequences into one eventual bound uniform over the admissible window.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal ComplexConjugate

namespace RBM.Gauss

/-- `H_0` on the common carrier: the actual band matrix, read off the band coordinate of the
common sample. -/
noncomputable def ouCommonH (d : Dims) :
    ∀ N, ouCommonOmega d → Matrix ((ouCommonBand d).Idx N) ((ouCommonBand d).Idx N) ℂ :=
  fun N ω => ouBandMatrix d N (ouCommonProjection d N ω)

/-- Measurability of the fixed-time OU matrix `ouMatrix d N t`, as a function on the plain
product carrier `Ω d × Ω d`.  File-local helper. -/
private theorem ouCommonFlow_ouMatrix_measurable (d : Dims) (N : ℕ) (t : ℝ) :
    Measurable (ouMatrix d N t) := by
  rw [show ouMatrix d N t = ouInterpolatedMatrix d N t from
    funext (ouMatrix_eq_interpolatedMatrix d N t)]
  apply measurable_pi_iff.mpr; intro i
  apply measurable_pi_iff.mpr; intro j
  have hs : Measurable (ouInterpolatedSample d N t) := by
    apply measurable_pi_iff.mpr; intro c
    simp only [ouInterpolatedSample]; fun_prop
  exact (measurable_Xentry d N i j).comp hs

/-- The OU flow (2.19) instantiated on the common carrier: `H_t` is `ouMatrix d N t` read off the
band/GUE coordinates of the common sample, starting at `ouCommonH d`. -/
noncomputable def ouCommonFlow (d : Dims) : RBM.OUFlow (ouCommonBand d) (ouCommonH d) where
  Ht N t ω := ouMatrix d N t (ouCommonProjection d N ω)
  hermitian N t _ := ouMatrix_isHermitian d N t _
  start N _ := ouMatrix_start d N _

theorem ouCommonFlow_measurable (d : Dims) (N : ℕ) (t : ℝ) :
    Measurable ((ouCommonFlow d).Ht N t) :=
  (ouCommonFlow_ouMatrix_measurable d N t).comp (ouCommonProjection_measurable d N)

/-- (2.26) at the single scale `Im z = N^{-1+2τ_U}`, uniformly over `|Re z| ≤ 2 - κ/2`,
`t ∈ [0, t_U]` and `x`, moment form. -/
def FlowLocalLaw (d : Dims) (κ τU : ℝ) : Prop :=
  ∀ δ > (0 : ℝ), ∀ p : ℕ, ∀ᶠ N : ℕ in atTop,
    ∀ t ∈ Set.Icc (0 : ℝ) ((ouCommonBand d).tPow τU N), ∀ E : ℝ, |E| ≤ 2 - κ / 2 →
      ∀ x : d.Idx N,
        ∫ ω, ‖RBM.green ((ouCommonFlow d).Ht N t ω)
            ((E : ℂ) + ((((ouCommonBand d).size N : ℝ) ^ (-1 + 2 * τU) : ℝ) : ℂ) * Complex.I)
            x x‖ ^ (2 * p) ∂(ouCommonMeasure d) ≤
          ((ouCommonBand d).size N : ℝ) ^ δ

/-- (7.47) for `H_{t_N}`, for every time sequence in `(0, t_U]`, at `τ* = c/3`. -/
def FlowEq747 (d : Dims) (κ τU : ℝ) : Prop :=
  ∀ E : ℝ, |E| ≤ 2 - κ → ∀ t : ℕ → ℝ,
    (∀ N, 0 < t N ∧ t N ≤ (ouCommonBand d).tPow τU N) →
    RBM.Eq747 (ouCommonFlow d) t ((ouCommonBand d).c / 3) (fun _ => E) (fun N => ouZeta (t N))

end RBM.Gauss

namespace RBM

/-- Uniformization over admissible time (or parameter) sequences: if an eventual property holds
along every sequence selecting one point from `T N` at each `N`, it holds eventually uniformly
over all of `T N`.  Used to combine per-sequence forms of (2.26)/(7.47) into the single-scale
window form above. Pure filter combinatorics; no dependence on the RBM1D model. -/
theorem eventually_forall_mem_of_forall_seq {α : Type*} {T : ℕ → Set α}
    (hT : ∀ N, (T N).Nonempty) {P : ℕ → α → Prop}
    (h : ∀ s : ℕ → α, (∀ N, s N ∈ T N) → ∀ᶠ N in atTop, P N (s N)) :
    ∀ᶠ N in atTop, ∀ a ∈ T N, P N a := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hcon' : ∃ᶠ N in atTop, ∃ a, a ∈ T N ∧ ¬ P N a := by
    refine hcon.mono ?_
    intro N hN
    push_neg at hN
    exact hN
  set g : ℕ → α := fun N =>
    if hN : ∃ a, a ∈ T N ∧ ¬ P N a then hN.choose else (hT N).choose with hg
  have hgmem : ∀ N, g N ∈ T N := by
    intro N
    by_cases hN : ∃ a, a ∈ T N ∧ ¬ P N a
    · simp only [hg, dif_pos hN]
      exact hN.choose_spec.1
    · simp only [hg, dif_neg hN]
      exact (hT N).choose_spec
  have hbad : ∀ N, (∃ a, a ∈ T N ∧ ¬ P N a) → ¬ P N (g N) := by
    intro N hN
    have hgN : g N = hN.choose := by simp only [hg, dif_pos hN]
    rw [hgN]
    exact hN.choose_spec.2
  have heven : ∀ᶠ N in atTop, P N (g N) := h g hgmem
  obtain ⟨N, hN1, hN2⟩ := (hcon'.and_eventually heven).exists
  exact hbad N hN1 hN2

end RBM
