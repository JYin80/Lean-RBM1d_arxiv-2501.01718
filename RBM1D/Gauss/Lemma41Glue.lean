/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.EntryBoundGauss
import RBM1D.Hierarchy.Step1

/-!
# The interface between `Green/EntryBound.lean` and `Hierarchy/Step1.lean` — T102

`RBM.Lemma41Flow` of `RBM1D/Hierarchy/Step1.lean` is stated in the language of
`RBM.Sample` (`Lval`, `llErr`, `llMax`, `goodEv`), while `RBM.entry_bound_stochDom` and
`RBM.diag_bound_stochDom` are stated in the language of `RBM1D/Green/EntryBound.lean`
(`Lre`, `GoodEvent`, `goodSet`).  The two match; this file writes the dictionary.

It also isolates what is *not* an interface question: `Lemma41Flow` quantifies over
`u ∈ [s_N, t_N]` **inside** the index set of `≺`, while `RBM.Gauss.entry_bound_gauss` and
`RBM.Gauss.diag_bound_gauss` are statements at one fixed `u`.  Bridging that needs a Hölder
modulus in `u` valid uniformly in `ω`, whose constant is `η^{-2}‖X‖` — see `docs/STATUS.md`
(T99) and tickets T100/T101.  Nothing in this file touches that.

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

`RBM.entry_bound_stochDom` and `RBM.diag_bound_stochDom` conclude
`1_Ω ξ ≺ ζ` where the **control `ζ` carries no indicator**, while `RBM.Lemma41Flow` supplies
`1_Ω ζ ≺ χ`.  The two chain anyway: on the failure event of the conclusion the left-hand side
is positive, so `ω ∈ Ω` and the indicator on the control is free. -/

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

/-- **Transitivity through an indicator.**  If `1_A f ≺ g` (control without indicator) and
`1_A g ≺ h` (control `h ≥ 0`), then `1_A f ≺ h`. -/
theorem trans_indicator {A : ℕ → Set Ω} {f g h : ∀ N, U N → Ω → ℝ}
    (h₁ : StochDom P (fun N u ω => (A N).indicator (f N u) ω) g)
    (h₂ : StochDom P (fun N u ω => (A N).indicator (g N u) ω) h)
    (hh : ∀ N u ω, 0 ≤ h N u ω) :
    StochDom P (fun N u ω => (A N).indicator (f N u) ω) h := by
  refine StochDom.of_subset_union h₁ h₂ fun τ hτ => ⟨τ / 2, by linarith, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
  intro ω hω
  obtain ⟨u, hu0'⟩ := hω
  have hu : (N : ℝ) ^ τ * h N u ω < (A N).indicator (f N u) ω := hu0'
  by_contra hcon
  rw [Set.mem_union] at hcon
  push Not at hcon
  obtain ⟨hb1, hb2⟩ := hcon
  simp only [badSet, Set.mem_ofPred_eq, not_exists, not_lt] at hb1 hb2
  replace hb1 : ∀ v, (A N).indicator (f N v) ω ≤ (N : ℝ) ^ (τ / 2) * g N v ω := hb1
  replace hb2 : ∀ v, (A N).indicator (g N v) ω ≤ (N : ℝ) ^ (τ / 2) * h N v ω := hb2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hp : (0 : ℝ) < (N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hN0 _
  -- the failure event forces `ω ∈ A N`
  have hmem : ω ∈ A N := by
    by_contra hnot
    rw [Set.indicator_of_notMem hnot] at hu
    exact absurd hu (not_lt.2
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) τ) (hh N u ω)))
  have e1 : (A N).indicator (f N u) ω ≤ (N : ℝ) ^ (τ / 2) * g N u ω := hb1 u
  have e2 : g N u ω ≤ (N : ℝ) ^ (τ / 2) * h N u ω := by
    have := hb2 u
    rwa [Set.indicator_of_mem hmem] at this
  have hchain : (A N).indicator (f N u) ω
      ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * h N u ω) := by
    refine e1.trans ?_
    exact mul_le_mul_of_nonneg_left e2 hp.le
  have hpow : (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * h N u ω)
      = (N : ℝ) ^ τ * h N u ω := by
    rw [← mul_assoc, ← Real.rpow_add hN0]
    congr 2
    ring
  rw [hpow] at hchain
  exact absurd hu (not_lt.2 hchain)

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

`RBM.Lemma41Flow` supplies `1_Ω‖L_{(+,-),(a,b)}‖ ≺ Φ` with `Φ` deterministic.  The controls of
`RBM.entry_bound_stochDom` and `RBM.diag_bound_stochDom` are built from the same two-loops, so
they too are `≺ Φ` (up to a constant, which `N^τ` absorbs). -/

variable {d : Dims} {E u : ℝ} {Φ : ℕ → ℝ}

/-- The hypothesis of `RBM.Lemma41Flow` at a fixed time, restated with `RBM.Lre`. -/
abbrev LoopHyp (d : Dims) (E u : ℝ) (Φ : ℕ → ℝ) : Prop :=
  StochDom (P d)
    (fun N (ab : ZMod (d.L N) × ZMod (d.L N)) ω =>
      (Step1.goodEv (sample d) E N u).indicator
        (fun ω => Lre (Hflow d N u ω) (zt E u) ab.1 ab.2) ω)
    (fun N _ _ => Φ N)

/-- `RBM.Gauss.LoopHyp` is exactly the hypothesis of `RBM.Lemma41Flow` at a fixed time. -/
theorem loopHyp_iff :
    LoopHyp d E u Φ ↔ StochDom (P d)
      (fun N (ab : ZMod (d.L N) × ZMod (d.L N)) ω =>
        (Step1.goodEv (sample d) E N u).indicator
          (fun ω => ‖(sample d).Lval E N u ω (pmLoop ab.1 ab.2)‖) ω)
      (fun N _ _ => Φ N) := by
  have h : ∀ (N : ℕ) (ab : ZMod (d.L N) × ZMod (d.L N)) (ω : Ω d),
      ‖(sample d).Lval E N u ω (pmLoop ab.1 ab.2)‖
        = Lre (Hflow d N u ω) (zt E u) ab.1 ab.2 := fun N ab ω =>
    sample_Lval_pm E N u ω ab.1 ab.2
  constructor <;> intro hh <;>
    simpa only [h] using hh

/-- **`1_Ω L^{max} ≺ Φ`**: the maximum over the (finitely many) block pairs is attained. -/
theorem stochDom_indicator_Lmax {V : ℕ → Type*} (hΦ0 : ∀ N, 0 ≤ Φ N) (hΦ : LoopHyp d E u Φ) :
    StochDom (P d)
      (fun N (_ : V N) ω =>
        (Step1.goodEv (sample d) E N u).indicator
          (fun ω => Lmax (Hflow d N u ω) (zt E u)) ω)
      (fun N _ _ => Φ N) := by
  unfold LoopHyp at hΦ
  refine StochDom.of_subset_union hΦ hΦ fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards with N
  intro ω hω
  refine Set.mem_union_left _ ?_
  simp only [badSet, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨-, hlt⟩ := hω
  by_cases hmem : ω ∈ Step1.goodEv (sample d) E N u
  · rw [Set.indicator_of_mem hmem] at hlt
    obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty)
      (fun p : ZMod (d.L N) × ZMod (d.L N) => Lre (Hflow d N u ω) (zt E u) p.1 p.2)
    unfold Lmax at hlt
    rw [hp] at hlt
    exact ⟨p, by rw [Set.indicator_of_mem hmem]; exact hlt⟩
  · rw [Set.indicator_of_notMem hmem] at hlt
    exact absurd hlt (not_lt.2
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) τ) (hΦ0 N)))

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

/-- **The control of (4.2) is `≺ Φ + W⁻¹`.**  Each of the at most nine two-loops is at most
`L^max`, and the `W⁻¹` term is absorbed by the `W⁻¹` of the target. -/
theorem stochDom_indicator_entryControl (hΦ0 : ∀ N, 0 ≤ Φ N) (hΦ : LoopHyp d E u Φ) :
    StochDom (P d)
      (fun N (p : OffPair d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N u).indicator
          (fun ω => (∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
              Lre (Hflow d N u ω) (zt E u) (p.1.2.1 + b) (p.1.1.1 + a))
            + if p.1.1.1 - p.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0) ω)
      (fun N _ _ => Φ N + ((d.W N : ℕ) : ℝ)⁻¹) := by
  unfold LoopHyp at hΦ
  refine StochDom.of_subset_union hΦ hΦ fun τ hτ => ⟨τ / 2, by linarith, ?_⟩
  filter_upwards [eventually_le_rpow 9 (show (0:ℝ) < τ / 2 by linarith),
    Filter.eventually_ge_atTop 1] with N h9 hN1
  intro ω hω
  refine Set.mem_union_left _ ?_
  simp only [badSet, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨p, hlt⟩ := hω
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hW : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  have hτ1 : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1' hτ.le
  have hτ2 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' (by linarith)
  by_cases hmem : ω ∈ Step1.goodEv (sample d) E N u
  · rw [Set.indicator_of_mem hmem] at hlt
    -- drop the `W⁻¹` term
    have hite : (if p.1.1.1 - p.1.2.1 ∈ sbSupport (d.L N) then ((d.W N : ℕ) : ℝ)⁻¹ else 0)
        ≤ (N : ℝ) ^ τ * ((d.W N : ℕ) : ℝ)⁻¹ := by
      split_ifs
      · nlinarith [hW, hτ1]
      · positivity
    have hsum : (N : ℝ) ^ τ * Φ N
        < ∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
            Lre (Hflow d N u ω) (zt E u) (p.1.2.1 + b) (p.1.1.1 + a) := by
      nlinarith [hlt, hite]
    have h9M := sum_sum_Lre_le d N E u ω p.1.1.1 p.1.2.1
    have hM : 0 ≤ Lmax (Hflow d N u ω) (zt E u) := Lmax_nonneg (Hflow_isHermitian d N u ω)
    have hkey : (N : ℝ) ^ (τ / 2) * Φ N < Lmax (Hflow d N u ω) (zt E u) := by
      have hsplit : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
        rw [← Real.rpow_add hN0]; congr 1; ring
      nlinarith [hsum, h9M, h9, hΦ0 N, hτ2]
    obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty)
      (fun q : ZMod (d.L N) × ZMod (d.L N) => Lre (Hflow d N u ω) (zt E u) q.1 q.2)
    unfold Lmax at hkey
    rw [hq] at hkey
    exact ⟨q, by rw [Set.indicator_of_mem hmem]; exact hkey⟩
  · rw [Set.indicator_of_notMem hmem] at hlt
    exfalso
    have : (0 : ℝ) ≤ (N : ℝ) ^ τ * (Φ N + ((d.W N : ℕ) : ℝ)⁻¹) := by
      have h1 : (0 : ℝ) ≤ Φ N + ((d.W N : ℕ) : ℝ)⁻¹ := by linarith [hΦ0 N, hW]
      positivity
    linarith [hlt]

/-- **The diagonal half of Lemma 4.1 at a fixed time**: `1_Ω|G_{ii} − m|² ≺ Φ + W⁻¹`. -/
theorem stochDom_indicator_diag (hG : GaussIBP d) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ0 : ∀ N, 0 ≤ ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 6))
    (hδ : ∀ᶠ N : ℕ in Filter.atTop,
      ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 6) ≤ (N : ℝ) ^ (-c₀))
    (hΦ0 : ∀ N, 0 ≤ Φ N) (hΦ : LoopHyp d E u Φ) :
    StochDom (P d)
      (fun N (i : BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N u).indicator
          (fun ω => ‖green (Hflow d N u ω) (zt E u) i i - mE E‖ ^ 2) ω)
      (fun N _ _ => Φ N + ((d.W N : ℕ) : ℝ)⁻¹) := by
  have hset : ∀ N : ℕ, Step1.goodEv (sample d) E N u
      = goodSet (L := d.L) (W := d.W) (fun N ω => Hflow d N u ω) (zt E u) (mE E)
          (fun N => ((band d).scale E N u)⁻¹ ^ ((1 : ℝ) / 6)) N :=
    fun N => goodEv_eq_goodSet E N u
  have h1 : StochDom (P d)
      (fun N (i : BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N u).indicator
          (fun ω => ‖green (Hflow d N u ω) (zt E u) i i - mE E‖ ^ 2) ω)
      (fun N _ ω => Lmax (Hflow d N u ω) (zt E u)) := by
    simp only [hset]
    exact diag_bound_gauss hG hκ0 hκ1 hE hu0 hu1 hδ0 hc₀ hδ
  have h2 : StochDom (P d)
      (fun N (_ : BIdx d.L d.W N) ω =>
        (Step1.goodEv (sample d) E N u).indicator
          (fun ω => Lmax (Hflow d N u ω) (zt E u)) ω)
      (fun N _ _ => Φ N + ((d.W N : ℕ) : ℝ)⁻¹) :=
    StochDom.control_mono
      (stochDom_indicator_Lmax (V := fun N => BIdx d.L d.W N) hΦ0 hΦ)
      (fun N _ _ => by
        have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
        linarith)
  refine StochDom.trans_indicator h1 h2 (fun N _ _ => ?_)
  have hw : (0 : ℝ) ≤ ((d.W N : ℕ) : ℝ)⁻¹ := by positivity
  linarith [hΦ0 N]

end Gauss

end RBM
