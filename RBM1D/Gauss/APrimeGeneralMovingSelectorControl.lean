/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSingletonLocalLaw
import RBM1D.Gauss.APrimeGeneralMovingControlExtension

/-!
# T514: exact identification of the moving selector control

The sharp singleton control from T495 is exactly the clamped global control
from T504 at every deterministic selector in the original moving window.
-/

namespace RBM.APrimeGeneralMovingSelectorControl

open Filter MeasureTheory Set Gauss

noncomputable section

noncomputable abbrev d : Dims := Dims.exampleGrow
noncomputable abbrev B : Band (Ω d) := band d

/-- On the original moving window, the T495 selector control is exactly the
T504 global extension. -/
theorem selectorQ_eq_qExt {E : ℝ} {s t u : ℕ → ℝ}
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    APrimeGeneralMovingSingletonLocalLaw.selectorQ E s u N =
      APrimeGeneralMovingControlExtension.qExt E s t N (u N) := by
  rw [APrimeGeneralMovingControlExtension.qExt_eq_q (hu N)]
  simp only [APrimeGeneralMovingSingletonLocalLaw.selectorQ,
    APrimeGeneralMovingControlExtension.q, div_eq_mul_inv]

/-- Multiplication by the centered-trace factor two preserves the exact
selector-control identification. -/
theorem two_mul_selectorQ_eq_two_mul_qExt {E : ℝ} {s t u : ℕ → ℝ}
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    2 * APrimeGeneralMovingSingletonLocalLaw.selectorQ E s u N =
      2 * APrimeGeneralMovingControlExtension.qExt E s t N (u N) := by
  rw [selectorQ_eq_qExt hu N]

/-- The exact same positive-length parameter tuple supplied by T495 supports
the selector-control identification at the concrete right-endpoint selector.
-/
theorem positive_length_same_parameter_selector_control_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (sample d) 0 s ∧ Step1.Hyp (sample d) 0 s t ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      (∀ N, APrimeGeneralMovingSingletonLocalLaw.selectorQ 0 s t N =
        APrimeGeneralMovingControlExtension.qExt 0 s t N (t N)) ∧
      ∀ N, 2 * APrimeGeneralMovingSingletonLocalLaw.selectorQ 0 s t N =
        2 * APrimeGeneralMovingControlExtension.qExt 0 s t N (t N) := by
  obtain ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    hpos, _hll⟩ :=
    APrimeGeneralMovingSingletonLocalLaw.positive_length_same_parameter_witness
  have hu : ∀ N, t N ∈ Icc (s N) (t N) := fun N => ⟨hst N, le_rfl⟩
  exact ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    hpos, selectorQ_eq_qExt hu, two_mul_selectorQ_eq_two_mul_qExt hu⟩

#print axioms selectorQ_eq_qExt
#print axioms two_mul_selectorQ_eq_two_mul_qExt
#print axioms positive_length_same_parameter_selector_control_witness

end
end RBM.APrimeGeneralMovingSelectorControl
