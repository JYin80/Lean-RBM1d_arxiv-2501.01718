/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingControlExtension
import RBM1D.Gauss.APrimeGeneralMovingSingletonLocalLaw

/-!
# T513: control inputs for the general moving time net

The exact deterministic control is `2 * qExt`, independent of the block
index and sample. It is globally nonnegative, has the polynomial lower
bound `N^(-1)` on the moving window, and varies by at most `N^ε` at
distance `N^(-16)` for each fixed positive ε.
-/

namespace RBM.APrimeGeneralMovingNetControl

open Filter Set Gauss APrimeGeneralMovingControlExtension

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The control in the exact time-net consumer; block and sample arguments
are present to match its interface. -/
def control (E : ℝ) (s t : ℕ → ℝ) (N : ℕ) (u : ℝ)
    (_b : ZMod (d.L N)) (_ω : Ω d) : ℝ :=
  2 * qExt E s t N u

theorem control_nonneg {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (N : ℕ) (u : ℝ) (b : ZMod (d.L N)) (ω : Ω d) :
    0 ≤ control E s t N u b ω := by
  exact mul_nonneg (by norm_num) (qExt_nonneg hE hs0 hst ht1 N u)

theorem control_eq_two_q {E : ℝ} {s t : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hu : u ∈ Icc (s N) (t N)) (b : ZMod (d.L N)) (ω : Ω d) :
    control E s t N u b ω = 2 * q E s N u := by
  rw [control, qExt_eq_q hu]

/-- Exact compatibility with the fixed-selector control of T495. -/
theorem control_eq_two_selectorQ {E : ℝ} {s t v : ℕ → ℝ}
    (hv : ∀ N, v N ∈ Icc (s N) (t N)) (N : ℕ) (b : ZMod (d.L N)) (ω : Ω d) :
    control E s t N (v N) b ω =
      2 * APrimeGeneralMovingSingletonLocalLaw.selectorQ E s v N := by
  rw [control_eq_two_q (hv N)]
  simp only [q, APrimeGeneralMovingSingletonLocalLaw.selectorQ, div_eq_mul_inv]

/-- The underlying Step-1 inequalities apply at every window time directly;
no selector-dependent eventual threshold occurs in this lower bound. -/
theorem W_inv_le_q {E : ℝ} {s t : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (ht1 : t N < 1)
    (hu : u ∈ Icc (s N) (t N)) : (d.W N : ℝ)⁻¹ ≤ q E s N u := by
  have hu0 : 0 ≤ u := hs0.trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt ht1
  have hbase := Step1.inv_W_le_inv_scale (B := B) hE N hu0 hu1
  have hr : 1 ≤ B.ell N u / B.ell N (s N) :=
    Step1.one_le_ell_div (B := B) hu.1 hu1
  have hAi : 0 ≤ (B.scale E N u)⁻¹ :=
    inv_nonneg.mpr (B.scale_pos' hE N hu0 hu1).le
  calc
    (d.W N : ℝ)⁻¹ ≤ (B.scale E N u)⁻¹ := hbase
    _ ≤ (B.ell N u / B.ell N (s N)) * (B.scale E N u)⁻¹ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hr hAi
    _ = q E s N u := by simp only [q, div_eq_mul_inv]

/-- The model's `W_N ≤ N` gives a threshold uniform in every real window
time. No `Cond272Reg` is needed for this lower bound. -/
theorem eventually_inv_le_q {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Icc (s N) (t N), (N : ℝ)⁻¹ ≤ q E s N u := by
  filter_upwards [Gauss.W_le_self d] with N hWN u hu
  have hW : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hinv : (N : ℝ)⁻¹ ≤ (d.W N : ℝ)⁻¹ :=
    inv_anti₀ hW (by exact_mod_cast hWN)
  exact hinv.trans (W_inv_le_q hE (hs0 N) (ht1 N) hu)

/-- The consumer's `B = 1` control floor, valid for every sample and block. -/
theorem eventually_control_lower {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Ω d, ∀ b : ZMod (d.L N),
      ∀ u ∈ Icc (s N) (t N), (N : ℝ) ^ (-1 : ℝ) ≤ control E s t N u b ω := by
  filter_upwards [eventually_inv_le_q hE hs0 ht1] with N hfloor ω b u hu
  rw [Real.rpow_neg_one, control_eq_two_q hu]
  have hq0 := (q_pos hE (hs0 N) (hst N) (ht1 N) hu).le
  exact (hfloor u hu).trans (by linarith)

/-- For each fixed ε, one eventual threshold works for both arbitrary
window times, every block, and every sample. -/
theorem control_slow {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c) (hreg : Cond272Reg B E s t c) :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ω : Ω d, ∀ b : ZMod (d.L N),
      ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N),
        |u - v| ≤ (N : ℝ) ^ (-16 : ℝ) →
        control E s t N v b ω ≤ (N : ℝ) ^ ε * control E s t N u b ω := by
  intro ε hε
  have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [eventually_qExt_short_time_comparable hE hs0 hst ht1 hc hreg,
    hlarge] with N hcomparison hlargeN ω b u hu v hv hdist
  have hq := (hcomparison u hu v hv hdist).2
  have htwo : control E s t N v b ω ≤ 2 * control E s t N u b ω := by
    exact mul_le_mul_of_nonneg_left hq (by norm_num)
  exact htwo.trans
    (mul_le_mul_of_nonneg_right hlargeN (control_nonneg hE hs0 hst ht1 N u b ω))

/-- The three control fields are stronger than the event-restricted
consumer fields, since the floor and slow variation hold for all samples. -/
structure ControlFields (E : ℝ) (s t : ℕ → ℝ) : Prop where
  nonneg : ∀ N u b ω, 0 ≤ control E s t N u b ω
  lower : ∀ᶠ N : ℕ in atTop, ∀ ω : Ω d, ∀ b : ZMod (d.L N),
    ∀ u ∈ Icc (s N) (t N), (N : ℝ) ^ (-1 : ℝ) ≤ control E s t N u b ω
  slow : ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ω : Ω d, ∀ b : ZMod (d.L N),
    ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N),
      |u - v| ≤ (N : ℝ) ^ (-16 : ℝ) →
      control E s t N v b ω ≤ (N : ℝ) ^ ε * control E s t N u b ω

theorem controlFields {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c) (hreg : Cond272Reg B E s t c) :
    ControlFields E s t :=
  { nonneg := control_nonneg hE hs0 hst ht1
    lower := eventually_control_lower hE hs0 hst ht1
    slow := control_slow hE hs0 hst ht1 hc hreg }

/-- One application of T495's witness supplies the original Step-1 inputs,
positive window length, and this control package on the same parameters. -/
theorem positive_length_same_parameter_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg B 0 s t c ∧
      BoundsCore (sample d) 0 s ∧ Step1.Hyp (sample d) 0 s t ∧
      ControlFields 0 s t ∧ ∀ᶠ N : ℕ in atTop, s N < t N := by
  obtain ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, hlength, _hll⟩ :=
    APrimeGeneralMovingSingletonLocalLaw.positive_length_same_parameter_witness
  exact ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    controlFields (by norm_num) hs0 hst ht1 hc hreg, hlength⟩

#print axioms control_nonneg
#print axioms control_eq_two_q
#print axioms control_eq_two_selectorQ
#print axioms W_inv_le_q
#print axioms eventually_inv_le_q
#print axioms eventually_control_lower
#print axioms control_slow
#print axioms controlFields
#print axioms positive_length_same_parameter_witness

end
end RBM.APrimeGeneralMovingNetControl
