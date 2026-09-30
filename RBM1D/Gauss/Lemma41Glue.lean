/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDEQuadDom
import RBM1D.Hierarchy.Step1

/-!
# The interface between `Green/EntryBound.lean` and `Hierarchy/Step1.lean`

Step 1 (`RBM1D/Hierarchy/Step1.lean`) states Lemma 4.1 in the language of `RBM.Sample`
(`Lval`, `llErr`, `llMax`, `goodEv`), while (4.2) and (4.3) are stated in the language of
`RBM1D/Green/EntryBound.lean` (`Lre`, `GoodEvent`, `goodSet`).  The two match; this file writes
the dictionary.

It also isolates what is *not* an interface question: Step 1 quantifies over
`u ∈ [s_N, t_N]` **inside** the index set of `≺`, while (4.2) and (4.3) for the Gaussian model
are statements at one fixed `u`.  Bridging that needs a Hölder
modulus in `u` valid uniformly in `ω`, whose constant is `η^{-2}‖X‖` (see
`RBM1D/Gauss/DominationHolder.lean`).  Nothing in this file touches that.

## Main statements

* `RBM.norm_gloop_pm_eq_Lre` : `‖L_{(+,-),(a,b)}‖ = L^{re}_{(+,-),(a,b)}` — the `2`-loop is a
  nonnegative real
* `RBM.Sample.llErr_eq`      : `llErr` is the entrywise quantity of `RBM.GoodEvent`
* `RBM.Step1.goodEv_eq_setOf_goodEvent` : `goodEv` is `RBM.GoodEvent` at a fixed time
* `RBM.Gauss.sample_Lval_pm` : the Gaussian sample's `2`-loop is `Lre` of the flow
-/

namespace RBM

open MeasureTheory Filter Finset

/-! ### The `(+,-)` two-loop is a nonnegative real -/

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `‖L_{(+,-),(a,b)}‖ = L^{re}_{(+,-),(a,b)}`: the two-loop of `RBM.pmLoop` equals
`W⁻²∑_{β,α}|G_{(b,β),(a,α)}|²`, a nonnegative real, so its norm is its real part. -/
theorem norm_gloop_pm_eq_Lre {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (a b : ZMod L) :
    ‖gloop L W H z ⟨[true, false], [a, b]⟩‖ = Lre H z a b := by
  have hval : gloop L W H z ⟨[true, false], [a, b]⟩
      = (((((W : ℝ)⁻¹) ^ 2 * ∑ β : Fin W, ∑ α : Fin W,
          ‖green H z (b, β) (a, α)‖ ^ 2 : ℝ)) : ℂ) := by
    rw [gloop_two_plus_minus_blocks hH]
    push_cast
    simp_rw [Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg, Lre_eq hH]
  have : (0 : ℝ) ≤ ∑ β : Fin W, ∑ α : Fin W, ‖green H z (b, β) (a, α)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

namespace Sample

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

/-- `llErr` is exactly the entrywise quantity of `RBM.GoodEvent`. -/
theorem llErr_eq (N : ℕ) (t : ℝ) (ω : Ω) (ij : B.Idx N × B.Idx N) :
    X.llErr E N t ω ij
      = ‖X.G E N t ω ij.1 ij.2 - (if ij.1 = ij.2 then mE E else 0)‖ := by
  show ‖(X.G E N t ω - mE E • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖ = _
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

end Sample

namespace Step1

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

/-- `goodEv` is `RBM.GoodEvent` at the threshold `(Wℓ_uη_u)^{-1/6}`. -/
theorem goodEv_eq_setOf_goodEvent (N : ℕ) (u : ℝ) :
    goodEv X E N u
      = {ω | GoodEvent (X.G E N u ω) (mE E) ((B.scale E N u)⁻¹ ^ ((1 : ℝ) / 6))} := by
  ext ω
  simp only [goodEv, GoodEvent, Set.mem_ofPred_eq]
  constructor
  · intro h x y
    rw [← X.llErr_eq N u ω (x, y)]
    exact le_trans (llErr_le_llMax X N u ω (x, y)) h
  · intro h
    refine llMax_le X ?_
    intro ij
    rw [X.llErr_eq N u ω ij]
    exact h ij.1 ij.2

end Step1

namespace StochDom

/-! ### Chaining through an indicator

(4.2) and (4.3) conclude `1_Ω ξ ≺ ζ` where the **control `ζ` carries no indicator**, while
Step 1 supplies `1_Ω ζ ≺ χ`.  The two chain anyway: on the failure event of the conclusion the
left-hand side is positive, so `ω ∈ Ω` and the indicator on the control is free. -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- Weakening the control. -/
theorem control_mono {ξ ζ ζ' : ∀ N, U N → Ω → ℝ} (h : StochDom P ξ ζ)
    (hle : ∀ N u ω, ζ N u ω ≤ ζ' N u ω) : StochDom P ξ ζ' := by
  refine StochDom.of_subset h fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards with N
  intro ω hω
  obtain ⟨v, hv⟩ := hω
  refine ⟨v, lt_of_le_of_lt ?_ hv⟩
  exact mul_le_mul_of_nonneg_left (hle N v ω) (Real.rpow_nonneg (Nat.cast_nonneg N) τ)

end StochDom

namespace Gauss

variable {d : Dims}

/-- **The Gaussian sample's `2`-loop is `Lre` of the flow.** -/
theorem sample_Lval_pm (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω d) (a b : ZMod (d.L N)) :
    ‖(sample d).Lval E N u ω (pmLoop a b)‖
      = Lre (Hflow d N u ω) (zt E u) a b :=
  norm_gloop_pm_eq_Lre (Hflow_isHermitian d N u ω) a b

/-- **`goodEv` of the Gaussian sample is `RBM.goodSet` of the flow**, at a fixed time `u`
and with `δ_N = (Wℓ_uη_u)^{-1/6}`.  This is the event `Ω(t,c)` of (4.1) in both languages. -/
theorem goodEv_eq_goodSet (E : ℝ) (N : ℕ) (u : ℝ) :
    Step1.goodEv (sample d) E N u
      = goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N u ω) (zt E u) (mE E)
          (fun N => ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 6)) N :=
  Step1.goodEv_eq_setOf_goodEvent (sample d) N u

/-! ### Transferring the random controls of (4.2) and (4.3) to the deterministic `Φ`

Step 1 supplies `1_Ω‖L_{(+,-),(a,b)}‖ ≺ Φ` with `Φ` deterministic.  The controls of (4.2) and
(4.3) are built from the same two-loops, so they too are `≺ Φ` (up to a constant, which `N^τ`
absorbs). -/

variable {d : Dims} {E u : ℝ} {Φ : ℕ → ℝ}

/-- `#{0, 1, -1} ≤ 3`. -/
theorem card_sbSupport_le (L : ℕ) : (sbSupport L).card ≤ 3 := by
  unfold sbSupport
  calc ({0, 1, -1} : Finset (ZMod L)).card ≤ ({1, -1} : Finset (ZMod L)).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ (({-1} : Finset (ZMod L)).card + 1) + 1 := by
        have := Finset.card_insert_le (1 : ZMod L) ({-1} : Finset (ZMod L))
        omega
    _ = 3 := by simp

/-- The double sum of two-loops in the control of (4.2) is at most `9 L^max`. -/
theorem sum_sum_Lre_le (d : Dims) (N : ℕ) (E u : ℝ) (ω : Ω d) (a₀ b₀ : ZMod (d.L N)) :
    (∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
        Lre (Hflow d N u ω) (zt E u) (b₀ + b) (a₀ + a))
      ≤ 9 * Lmax (Hflow d N u ω) (zt E u) := by
  have hH := Hflow_isHermitian d N u ω
  have hM : 0 ≤ Lmax (Hflow d N u ω) (zt E u) := Lmax_nonneg hH
  have hc : ((sbSupport (d.L N)).card : ℝ) ≤ 3 := by
    exact_mod_cast card_sbSupport_le (d.L N)
  have hc0 : (0 : ℝ) ≤ ((sbSupport (d.L N)).card : ℝ) := Nat.cast_nonneg _
  have hinner : ∀ a : ZMod (d.L N),
      (∑ b ∈ sbSupport (d.L N), Lre (Hflow d N u ω) (zt E u) (b₀ + b) (a₀ + a))
        ≤ ((sbSupport (d.L N)).card : ℝ) * Lmax (Hflow d N u ω) (zt E u) := by
    intro a
    calc (∑ b ∈ sbSupport (d.L N), Lre (Hflow d N u ω) (zt E u) (b₀ + b) (a₀ + a))
        ≤ ∑ _b ∈ sbSupport (d.L N), Lmax (Hflow d N u ω) (zt E u) :=
          Finset.sum_le_sum fun b _ => Lre_le_Lmax _ _
      _ = ((sbSupport (d.L N)).card : ℝ) * Lmax (Hflow d N u ω) (zt E u) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc (∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
        Lre (Hflow d N u ω) (zt E u) (b₀ + b) (a₀ + a))
      ≤ ∑ _a ∈ sbSupport (d.L N),
          ((sbSupport (d.L N)).card : ℝ) * Lmax (Hflow d N u ω) (zt E u) :=
        Finset.sum_le_sum fun a _ => hinner a
    _ = ((sbSupport (d.L N)).card : ℝ) *
          (((sbSupport (d.L N)).card : ℝ) * Lmax (Hflow d N u ω) (zt E u)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 9 * Lmax (Hflow d N u ω) (zt E u) := by
        have hsq : ((sbSupport (d.L N)).card : ℝ) * ((sbSupport (d.L N)).card : ℝ) ≤ 9 := by
          nlinarith [hc, hc0]
        nlinarith [hsq, hM]

end Gauss

end RBM
