/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Holder

set_option maxHeartbeats 4000000

/-!
# The net lift of (2.76) uniformly in `u ∈ [s_N, t_N]` — T1511

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*.

The grid stopping argument, together with the single-time transfer `map_H_eq`, gives the (2.76)
bound at one fixed time `u(N)` for each sequence `u`.  This file lifts that to the whole window
`u ∈ [s_N, t_N]`, uniformly, in the `√u·X` Gaussian model `sample d`.  The lift is deterministic
(a Hölder-1/2 modulus on `{‖X‖ ≤ N}`) and goes entirely through the abstract net lemma
`RBM.Gauss.netLift_of_relaxed` (`RBM1D/Gauss/Step1Hyp.lean`).

## Main results

* `RBM.Gauss.Grid.etaT_inv_le_of_hreg` — (T1) `η_{t_N}^{-1} ≤ N` from `hreg`.
* `RBM.Gauss.Grid.h276_of_pointwise` — (T2) the net lift itself; its conclusion is literally the
  second conjunct of `RBM.Step2.step2`.
-/

namespace RBM
namespace Gauss
namespace Grid

open Filter MeasureTheory
open scoped Matrix.Norms.L2Operator

/-! ### A generic exponent-comparison helper -/

/-- `C N^p ≤ κ N^q` eventually, for any fixed `C`, `κ > 0` and `p < q`. -/
theorem eventually_mul_rpow_le_mul_rpow (C κ : ℝ) (hκ : 0 < κ) {p q : ℝ} (hpq : p < q) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ p ≤ κ * (N : ℝ) ^ q := by
  filter_upwards [eventually_const_mul_rpow_le_rpow (C / κ) hpq] with N hN
  have h2 : κ * ((C / κ) * (N : ℝ) ^ p) ≤ κ * (N : ℝ) ^ q :=
    mul_le_mul_of_nonneg_left hN hκ.le
  have h3 : κ * (C / κ) = C := by field_simp
  rwa [← mul_assoc, h3] at h2

/-- `√|u - u'| ≤ N^{-A/2}` from `|u - u'| ≤ N^{-A}`. -/
theorem sqrt_abs_sub_le_rpow {N : ℕ} {u u' A : ℝ} (h : |u - u'| ≤ (N : ℝ) ^ (-A)) :
    Real.sqrt |u - u'| ≤ (N : ℝ) ^ (-A / 2) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have h1 : Real.sqrt |u - u'| ≤ Real.sqrt ((N : ℝ) ^ (-A)) := Real.sqrt_le_sqrt h
  have h2 : Real.sqrt ((N : ℝ) ^ (-A)) = (N : ℝ) ^ (-A / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0]
    ring_nf
  rwa [h2] at h1

/-- `|exp(-x) - exp(-y)| ≤ |x - y|` for `x, y ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  rcases le_total x y with hxy | hxy
  · -- `x ≤ y`: `exp(-x) ≥ exp(-y)` and `|x - y| = y - x`.
    have hex : Real.exp (-x) * ((x - y) + 1) ≤ Real.exp (-x) * Real.exp (x - y) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
    rw [← Real.exp_add, show -x + (x - y) = -y from by ring] at hex
    have hex1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hd1 : Real.exp (-x) - Real.exp (-y) ≤ y - x := by nlinarith [hex, hex1]
    have hd2 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    have hxy2 : |x - y| = y - x := by rw [abs_of_nonpos (by linarith : x - y ≤ 0)]; ring
    rw [hxy2, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (-x) - Real.exp (-y))]
    exact hd1
  · -- `y ≤ x`: symmetric.
    have hey : Real.exp (-y) * ((y - x) + 1) ≤ Real.exp (-y) * Real.exp (y - x) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
    rw [← Real.exp_add, show -y + (y - x) = -x from by ring] at hey
    have hey1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hd1 : Real.exp (-y) - Real.exp (-x) ≤ x - y := by nlinarith [hey, hey1]
    have hd2 : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
    have hxy2 : |x - y| = x - y := abs_of_nonneg (by linarith)
    rw [hxy2, abs_of_nonpos (by linarith : Real.exp (-x) - Real.exp (-y) ≤ 0)]
    linarith [hd1]

/-! ### (T1) -/

/-- **(T1)**: from `hreg` (step2's regularity gain `N^c(η_s/η_t)^{30} ≤ scale(t)`) and
`W ℓ_t η_t ≤ WLη_t ≤ Nη_t` (`(band d).dim`), conclude `η_{t_N}^{-1} ≤ N`. -/
theorem etaT_inv_le_of_hreg (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N)) :
    ∀ᶠ N : ℕ in atTop, (etaT E (t N))⁻¹ ≤ (N : ℝ) := by
  filter_upwards [hreg, (band d).dim, eventually_ge_atTop 1] with N hregN hdimN hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hηt : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
  have hηs_ge : etaT E (t N) ≤ etaT E (s N) := etaT_le_of_le hE (hst N)
  have hratio1 : (1 : ℝ) ≤ etaT E (s N) / etaT E (t N) := (one_le_div₀ hηt).mpr hηs_ge
  have hratio30 : (1 : ℝ) ≤ (etaT E (s N) / etaT E (t N)) ^ 30 := one_le_pow₀ hratio1
  have hNc_le : (N : ℝ) ^ c ≤ (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 :=
    le_mul_of_one_le_right (Real.rpow_nonneg (Nat.cast_nonneg N) c) hratio30
  have hellle : (band d).ell N (t N) ≤ ((band d).L N : ℝ) := min_le_right _ _
  have hW0 : (0 : ℝ) ≤ ((band d).W N : ℝ) := Nat.cast_nonneg _
  have hscale_le :
      (band d).scale E N (t N) ≤ ((band d).W N : ℝ) * ((band d).L N : ℝ) * etaT E (t N) := by
    show ((band d).W N : ℝ) * (band d).ell N (t N) * etaT E (t N) ≤ _
    have h1 : ((band d).W N : ℝ) * (band d).ell N (t N)
        ≤ ((band d).W N : ℝ) * ((band d).L N : ℝ) := mul_le_mul_of_nonneg_left hellle hW0
    exact mul_le_mul_of_nonneg_right h1 hηt.le
  have hWLN : ((band d).W N : ℝ) * ((band d).L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdimN.1
  have hchain : (N : ℝ) ^ c ≤ (N : ℝ) * etaT E (t N) :=
    calc (N : ℝ) ^ c ≤ (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 := hNc_le
      _ ≤ (band d).scale E N (t N) := hregN
      _ ≤ ((band d).W N : ℝ) * ((band d).L N : ℝ) * etaT E (t N) := hscale_le
      _ ≤ (N : ℝ) * etaT E (t N) := mul_le_mul_of_nonneg_right hWLN hηt.le
  have h1c : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0.le
  have hbig : (1 : ℝ) ≤ (N : ℝ) * etaT E (t N) := h1c.trans hchain
  have h := mul_le_mul_of_nonneg_right hbig (inv_nonneg.2 hηt.le)
  rwa [one_mul, mul_assoc, mul_inv_cancel₀ hηt.ne', mul_one] at h

/-! ### More generic helpers, for (T2) -/

/-- `√(N^e) = N^{e/2}`. -/
theorem sqrt_rpow_eq (N : ℕ) (e : ℝ) : Real.sqrt ((N : ℝ) ^ e) = (N : ℝ) ^ (e / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
  ring_nf

/-- `b⁻¹ ≤ κ a⁻¹` from `a ≤ κ b` (positive `a, b`). -/
theorem inv_le_const_mul_inv_of_le_const_mul {a b κ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ≤ κ * b) : b⁻¹ ≤ κ * a⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hb ha]
  nlinarith [h]

/-- The charge vector `(+, -)` and the bridge to `pmLoop`. -/
theorem idx_mySig {L : ℕ} (a b : ZMod L) :
    LoopData.idx ((![true, false] : Fin 2 → Bool), (![a, b] : LoopArg L 2)) = pmLoop a b := by
  simp [LoopData.idx, pmLoop, List.ofFn_succ]

/-- `lkErr` at the `2`-loop `pmLoop a b` is the norm of `SumZeroDyn.lkT` at charges `(+, -)`. -/
theorem lkErr_eq_norm_lkT {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) (E : ℝ)
    (N : ℕ) (u : ℝ) (ω : Ω) (a b : ZMod (B.L N)) :
    X.lkErr E N u ω (pmLoop a b) =
      ‖SumZeroDyn.lkT X E N u ω (![true, false]) (![a, b] : LoopArg (B.L N) 2)‖ := by
  rw [SumZeroDyn.norm_lkT, idx_mySig]

/-! ### (T2) -/

/-- **(T2)**: the net lift of (2.76), uniformly in `u ∈ [s_N, t_N]`, from the pointwise (along
every time sequence) bound `hpt`.  The conclusion is literally the second conjunct of
`RBM.Step2.step2`. -/
theorem h276_of_pointwise (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (hpt : ∀ D : ℝ, 0 < D → ∀ u : ∀ N, RBM.TimeIcc s t N, StochDom (P d)
      (fun N (p : ZMod ((band d).L N) × ZMod ((band d).L N)) ω =>
        (sample d).lkErr E N (u N) ω (pmLoop p.1 p.2))
      (fun N p _ => (etaT E (s N) / etaT E (u N)) ^ 4 *
        ((band d).scale E N (u N))⁻¹ ^ 2 * (band d).decayProf N (u N) D p.1 p.2)) :
    ∀ D : ℝ, 0 < D → StochDom (P d)
      (fun N (p : RBM.TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * ((band d).scale E N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) := by
  intro D hD0
  -- the net spacing exponent, fixed once `D` is fixed
  set A : ℝ := 4 * D + 40 with hA_def
  have hApos : (0 : ℝ) ≤ A := by rw [hA_def]; linarith
  have hlen : ∀ N, t N - s N ≤ (1 : ℝ) := fun N => by linarith [hs0 N, ht1 N]
  -- `T1`, in the two forms used below
  have hreg1 : ∀ᶠ N : ℕ in atTop, (etaT E (t N))⁻¹ ≤ (N : ℝ) :=
    etaT_inv_le_of_hreg d hE hs0 hst ht1 hc0 hreg
  have hreg1' : ∀ᶠ N : ℕ in atTop, (etaT E (t N))⁻¹ ≤ (N : ℝ) ^ (1 : ℝ) := by
    filter_upwards [hreg1] with N hN; rwa [Real.rpow_one]
  -- the envelope on `K` at loop length `2`, from (2.59)
  have hKb2raw := hKb_flow (band d) hE ht1 (zero_le_one) (2 : ℕ) hreg1'
  have he3 : (1 : ℝ) * ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
  have hKb2 : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (t N),
      ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF → 2 ≤ J.length → J.length ≤ 2 →
        ‖(band d).Kval E N w J‖ ≤ (N : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hKb2raw] with N hN w hw J hJ h2 h2'
    have := hN w hw J hJ h2 h2'
    rwa [he3] at this
  -- the four exponent gaps, one per factor of `bnd`, all fixed once `D` is fixed
  have hEtaGap : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) * (N : ℝ) ^ (-A) ≤ (1 / 10) * (N : ℝ) ^ (-1 : ℝ) :=
    eventually_mul_rpow_le_mul_rpow 1 (1 / 10) (by norm_num) (by rw [hA_def]; linarith)
  have hScaleGap : ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) * (N : ℝ) ^ (2 - A / 2) ≤ (1 / 10) * (N : ℝ) ^ (-1 : ℝ) :=
    eventually_mul_rpow_le_mul_rpow 2 (1 / 10) (by norm_num) (by rw [hA_def]; linarith)
  have hDecayGap : ∀ᶠ N : ℕ in atTop,
      Real.sqrt (1 / 2) * (N : ℝ) ^ (1 - A / 4) ≤ (1 / 10) * (N : ℝ) ^ (-D) :=
    eventually_mul_rpow_le_mul_rpow (Real.sqrt (1 / 2)) (1 / 10) (by norm_num)
      (by rw [hA_def]; linarith)
  have hLkGap : ∀ᶠ N : ℕ in atTop,
      (8 : ℝ) * (N : ℝ) ^ (8 - A / 2) ≤ (1 : ℝ) * (N : ℝ) ^ (-(D + 4)) :=
    eventually_mul_rpow_le_mul_rpow 8 1 (by norm_num) (by rw [hA_def]; linarith)
  have hNinv_eq : ∀ N : ℕ, (N : ℝ) ^ (-1 : ℝ) = (N : ℝ)⁻¹ := fun N => by
    rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_one]
  have hκ7 : (11 / 10 : ℝ) ^ 7 ≤ 2 := by norm_num
  -- `hlow`
  have hlow : ∀ᶠ N : ℕ in atTop, ∀ (p : RBM.TimeIcc s t N × (ZMod ((band d).L N) ×
      ZMod ((band d).L N))) (ω : Ω d), (N : ℝ) ^ (-(D + 2)) ≤
        (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 4 * ((band d).scale E N (p.1 : ℝ))⁻¹ ^ 2 *
          (band d).decayProf N (p.1 : ℝ) D p.2.1 p.2.2 := by
    filter_upwards [(band d).dim, eventually_ge_atTop 1] with N hdimN hN1 p ω
    obtain ⟨u, a, b⟩ := p
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hu_lo : s N ≤ (u : ℝ) := u.2.1
    have hu_hi : (u : ℝ) ≤ t N := u.2.2
    have hu_lo0 : (0 : ℝ) ≤ (u : ℝ) := le_trans (hs0 N) hu_lo
    have hu_lt1 : (u : ℝ) < 1 := lt_of_le_of_lt hu_hi (ht1 N)
    have hηu : 0 < etaT E (u : ℝ) := etaT_pos_of_lt_one' hE hu_lt1
    have hηs_ge : etaT E (u : ℝ) ≤ etaT E (s N) := etaT_le_of_le hE hu_lo
    have hratio1 : (1 : ℝ) ≤ etaT E (s N) / etaT E (u : ℝ) := (one_le_div₀ hηu).mpr hηs_ge
    have hratio4 : (1 : ℝ) ≤ (etaT E (s N) / etaT E (u : ℝ)) ^ 4 := one_le_pow₀ hratio1
    have hscale_pos : 0 < (band d).scale E N (u : ℝ) := (band d).scale_pos' hE N hu_lo0 hu_lt1
    have hellle : (band d).ell N (u : ℝ) ≤ ((band d).L N : ℝ) := min_le_right _ _
    have hW0 : (0 : ℝ) ≤ ((band d).W N : ℝ) := Nat.cast_nonneg _
    have hscale_le :
        (band d).scale E N (u : ℝ) ≤ ((band d).W N : ℝ) * ((band d).L N : ℝ) * etaT E (u : ℝ) := by
      show ((band d).W N : ℝ) * (band d).ell N (u : ℝ) * etaT E (u : ℝ) ≤ _
      have h1 : ((band d).W N : ℝ) * (band d).ell N (u : ℝ)
          ≤ ((band d).W N : ℝ) * ((band d).L N : ℝ) := mul_le_mul_of_nonneg_left hellle hW0
      exact mul_le_mul_of_nonneg_right h1 hηu.le
    have hWLN : ((band d).W N : ℝ) * ((band d).L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdimN.1
    have hscale_leN : (band d).scale E N (u : ℝ) ≤ (N : ℝ) := by
      refine hscale_le.trans ?_
      calc ((band d).W N : ℝ) * ((band d).L N : ℝ) * etaT E (u : ℝ)
          ≤ (N : ℝ) * etaT E (u : ℝ) := mul_le_mul_of_nonneg_right hWLN hηu.le
        _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left (etaT_le_one hE hu_lo0) hN0.le
        _ = (N : ℝ) := mul_one _
    have hscaleinv_ge : (N : ℝ)⁻¹ ≤ ((band d).scale E N (u : ℝ))⁻¹ :=
      inv_anti₀ hscale_pos hscale_leN
    have hscaleinv2 : (N : ℝ)⁻¹ ^ 2 ≤ ((band d).scale E N (u : ℝ))⁻¹ ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.2 (Nat.cast_nonneg N)) hscaleinv_ge 2
    have hWNpos : (0 : ℝ) < ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
    have hWleN : ((band d).W N : ℝ) ≤ (N : ℝ) := by
      have h3 : (band d).three_le_L N = (band d).three_le_L N := rfl
      have hL1 : 1 ≤ (band d).L N := by have := (band d).three_le_L N; omega
      have : (band d).W N ≤ N :=
        le_trans (Nat.le_mul_of_pos_right _ hL1) hdimN.1
      exact_mod_cast this
    have hWD_le : (N : ℝ) ^ (-D) ≤ ((band d).W N : ℝ) ^ (-D) := by
      have hpow_le : ((band d).W N : ℝ) ^ D ≤ (N : ℝ) ^ D :=
        Real.rpow_le_rpow hWNpos.le hWleN hD0.le
      have hpow_pos : (0 : ℝ) < ((band d).W N : ℝ) ^ D := Real.rpow_pos_of_pos hWNpos D
      have := inv_anti₀ hpow_pos hpow_le
      rwa [← Real.rpow_neg hWNpos.le, ← Real.rpow_neg (Nat.cast_nonneg N)] at this
    have hdecay_ge : (N : ℝ) ^ (-D) ≤ (band d).decayProf N (u : ℝ) D a b := by
      have h1 : (0 : ℝ) ≤
          Real.exp (-(((zdist ((band d).L N) (a - b) : ℝ)) / (band d).ell N (u : ℝ)) ^
            ((1 : ℝ) / 2)) := (Real.exp_pos _).le
      show (N : ℝ) ^ (-D) ≤ _ + ((band d).W N : ℝ) ^ (-D)
      linarith [hWD_le]
    have hbase_nonneg : (0 : ℝ) ≤ (etaT E (s N) / etaT E (u : ℝ)) ^ 4 * (N : ℝ)⁻¹ ^ 2 := by
      positivity
    calc (N : ℝ) ^ (-(D + 2))
        = (N : ℝ) ^ (-(2 : ℝ)) * (N : ℝ) ^ (-D) := by
          rw [← Real.rpow_add hN0]; ring_nf
      _ = (N : ℝ)⁻¹ ^ 2 * (N : ℝ) ^ (-D) := by
          rw [show (-(2:ℝ)) = ((-1:ℝ) * 2 : ℝ) from by ring, Real.rpow_mul (Nat.cast_nonneg N),
            hNinv_eq]
          norm_num
      _ ≤ (etaT E (s N) / etaT E (u : ℝ)) ^ 4 * ((band d).scale E N (u : ℝ))⁻¹ ^ 2
            * (band d).decayProf N (u : ℝ) D a b := by
          have h1 : (N:ℝ)⁻¹ ^ 2 * (N:ℝ)^(-D) ≤
              (etaT E (s N)/etaT E (u:ℝ))^4 * (N:ℝ)⁻¹^2 * (N:ℝ)^(-D) := by
            have hX0 : (0:ℝ) ≤ (N:ℝ)⁻¹^2 * (N:ℝ)^(-D) := by positivity
            calc (N:ℝ)⁻¹^2 * (N:ℝ)^(-D) = 1 * ((N:ℝ)⁻¹^2 * (N:ℝ)^(-D)) := (one_mul _).symm
              _ ≤ (etaT E (s N)/etaT E (u:ℝ))^4 * ((N:ℝ)⁻¹^2 * (N:ℝ)^(-D)) :=
                  mul_le_mul_of_nonneg_right hratio4 hX0
              _ = (etaT E (s N)/etaT E (u:ℝ))^4 * (N:ℝ)⁻¹^2 * (N:ℝ)^(-D) := by ring
          refine h1.trans ?_
          have h2 : (etaT E (s N)/etaT E (u:ℝ))^4 * (N:ℝ)⁻¹^2 * (N:ℝ)^(-D)
              ≤ (etaT E (s N)/etaT E (u:ℝ))^4 * ((band d).scale E N (u:ℝ))⁻¹^2 * (N:ℝ)^(-D) := by
            have hnn : (0:ℝ) ≤ (etaT E (s N)/etaT E (u:ℝ))^4 := by positivity
            have := mul_le_mul_of_nonneg_left hscaleinv2 hnn
            exact mul_le_mul_of_nonneg_right this (by positivity)
          refine h2.trans ?_
          have hnn2 : (0:ℝ) ≤ (etaT E (s N)/etaT E (u:ℝ))^4 *
              ((band d).scale E N (u:ℝ))⁻¹^2 := by positivity
          exact mul_le_mul_of_nonneg_left hdecay_ge hnn2
  -- `hclose`
  have hclose : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)},
      ∀ u u' : RBM.TimeIcc s t N, |(u : ℝ) - (u' : ℝ)| ≤ (N : ℝ) ^ (-A) →
      ∀ v : ZMod ((band d).L N) × ZMod ((band d).L N),
        (sample d).lkErr E N (u : ℝ) ω (pmLoop v.1 v.2) ≤
          (sample d).lkErr E N (u' : ℝ) ω (pmLoop v.1 v.2) + (N : ℝ) ^ (-((D + 2) + 2)) ∧
        (etaT E (s N) / etaT E (u' : ℝ)) ^ 4 * ((band d).scale E N (u' : ℝ))⁻¹ ^ 2 *
            (band d).decayProf N (u' : ℝ) D v.1 v.2 ≤
          2 * ((etaT E (s N) / etaT E (u : ℝ)) ^ 4 * ((band d).scale E N (u : ℝ))⁻¹ ^ 2 *
            (band d).decayProf N (u : ℝ) D v.1 v.2) := by
    filter_upwards [hreg1, hKb2, (band d).dim, eventually_ge_atTop 1,
        hEtaGap, hScaleGap, hDecayGap, hLkGap] with
      N hreg1N hKb2N hdimN hN1 hEtaGapN hScaleGapN hDecayGapN hLkGapN ω hωΞ u u' huu' v
    obtain ⟨a, b⟩ := v
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hu_lo : s N ≤ (u : ℝ) := u.2.1
    have hu_hi : (u : ℝ) ≤ t N := u.2.2
    have hu'_lo : s N ≤ (u' : ℝ) := u'.2.1
    have hu'_hi : (u' : ℝ) ≤ t N := u'.2.2
    have hu_lo0 : (0 : ℝ) ≤ (u : ℝ) := le_trans (hs0 N) hu_lo
    have hu'_lo0 : (0 : ℝ) ≤ (u' : ℝ) := le_trans (hs0 N) hu'_lo
    have hu_lt1 : (u : ℝ) < 1 := lt_of_le_of_lt hu_hi (ht1 N)
    have hu'_lt1 : (u' : ℝ) < 1 := lt_of_le_of_lt hu'_hi (ht1 N)
    have hu_Icc0T : (u : ℝ) ∈ Set.Icc (0 : ℝ) (t N) := ⟨hu_lo0, hu_hi⟩
    have hu'_Icc0T : (u' : ℝ) ∈ Set.Icc (0 : ℝ) (t N) := ⟨hu'_lo0, hu'_hi⟩
    have hηt : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
    have hηu : 0 < etaT E (u : ℝ) := etaT_pos_of_lt_one' hE hu_lt1
    have hηu' : 0 < etaT E (u' : ℝ) := etaT_pos_of_lt_one' hE hu'_lt1
    have hηtlow : (N : ℝ)⁻¹ ≤ etaT E (t N) := by
      have := inv_anti₀ (inv_pos.2 hηt) hreg1N
      rwa [inv_inv] at this
    have hηu_ge_ηt : etaT E (t N) ≤ etaT E (u : ℝ) := etaT_le_of_le hE hu_hi
    have hηu'_ge_ηt : etaT E (t N) ≤ etaT E (u' : ℝ) := etaT_le_of_le hE hu'_hi
    have hηu_ge : (N : ℝ)⁻¹ ≤ etaT E (u : ℝ) := hηtlow.trans hηu_ge_ηt
    have hηu'_ge : (N : ℝ)⁻¹ ≤ etaT E (u' : ℝ) := hηtlow.trans hηu'_ge_ηt
    have h1t : (0 : ℝ) < 1 - t N := by linarith [ht1 N]
    have hTinv : (1 - t N)⁻¹ ≤ (N : ℝ) := by
      have hle : etaT E (t N) ≤ 1 - t N := etaT_le hE.le (ht1 N).le
      exact (inv_anti₀ hηt hle).trans hreg1N
    have hWNpos : (0 : ℝ) < ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
    have hLpos1 : 1 ≤ (band d).L N := by have := (band d).three_le_L N; omega
    have hWleN : ((band d).W N : ℝ) ≤ (N : ℝ) := by
      have hle : (band d).W N ≤ N := le_trans (Nat.le_mul_of_pos_right _ hLpos1) hdimN.1
      exact_mod_cast hle
    have hLleN : ((band d).L N : ℝ) ≤ (N : ℝ) := by
      have hle : (band d).L N ≤ N :=
        le_trans (Nat.le_mul_of_pos_left _ ((band d).W_pos N)) hdimN.1
      exact_mod_cast hle
    have hsqrt_le : Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ (N : ℝ) ^ (-A / 2) :=
      sqrt_abs_sub_le_rpow huu'
    -- generic rpow-combination helpers, at this fixed `N`
    have hpow_add1 : ∀ e : ℝ, (N : ℝ) * (N : ℝ) ^ e = (N : ℝ) ^ (1 + e) := fun e => by
      have h1 : (N : ℝ) ^ (1 + e) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ e := Real.rpow_add hN0 1 e
      rw [h1, Real.rpow_one]
    have hpow_add2 : ∀ e : ℝ, (N : ℝ) * ((N : ℝ) * (N : ℝ) ^ e) = (N : ℝ) ^ (2 + e) := fun e => by
      have h1 : (N : ℝ) ^ (1 + (1 + e)) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 + e) :=
        Real.rpow_add hN0 1 (1 + e)
      rw [show (2 + e : ℝ) = 1 + (1 + e) from by ring, h1, Real.rpow_one, hpow_add1 e]
    have hpow_nat_rpow : ∀ (k : ℕ) (e : ℝ), (N : ℝ) ^ k * (N : ℝ) ^ e = (N : ℝ) ^ ((k : ℝ) + e) :=
      fun k e => by rw [← Real.rpow_natCast (N : ℝ) k, ← Real.rpow_add hN0]
    ------------------------------------------------------------------
    -- (a) the η factor
    ------------------------------------------------------------------
    have hη_close : |etaT E (u : ℝ) - etaT E (u' : ℝ)| ≤ (N : ℝ) ^ (-A) :=
      (abs_etaT_sub_le hE.le _ _).trans huu'
    have hη_ratio : etaT E (u : ℝ) ≤ (11 / 10) * etaT E (u' : ℝ) := by
      have h1 := (abs_le.mp hη_close).2
      have h2 : (N : ℝ) ^ (-A) ≤ (1 / 10) * (N : ℝ) ⁻¹ := by
        rw [← hNinv_eq]
        have := hEtaGapN
        linarith [this]
      linarith [h1, h2, hηu'_ge]
    ------------------------------------------------------------------
    -- (b) the scale factor
    ------------------------------------------------------------------
    have hscale_pos : 0 < (band d).scale E N (u : ℝ) := (band d).scale_pos' hE N hu_lo0 hu_lt1
    have hscale'_pos : 0 < (band d).scale E N (u' : ℝ) := (band d).scale_pos' hE N hu'_lo0 hu'_lt1
    have hscale_ge_eta : etaT E (u' : ℝ) ≤ (band d).scale E N (u' : ℝ) := by
      have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
      have hell1 : (1 : ℝ) ≤ (band d).ell N (u' : ℝ) :=
        one_le_ellHat _ ((band d).three_le_L N) hu'_lo0 hu'_lt1
      show etaT E (u' : ℝ) ≤ ((band d).W N : ℝ) * (band d).ell N (u' : ℝ) * etaT E (u' : ℝ)
      have hη0 : (0:ℝ) ≤ etaT E (u' : ℝ) := hηu'.le
      calc etaT E (u' : ℝ) = 1 * 1 * etaT E (u' : ℝ) := by ring
        _ ≤ ((band d).W N : ℝ) * (band d).ell N (u' : ℝ) * etaT E (u' : ℝ) := by gcongr
    have hscale'_ge : (N : ℝ)⁻¹ ≤ (band d).scale E N (u' : ℝ) := hηu'_ge.trans hscale_ge_eta
    have hscale_close : |(band d).scale E N (u : ℝ) - (band d).scale E N (u' : ℝ)| ≤
        ((band d).W N : ℝ) * ((1 - t N)⁻¹ + ((band d).L N : ℝ)) * Real.sqrt |(u : ℝ) - (u' : ℝ)| :=
      abs_scale_sub_le hE N (ht1 N) hu_Icc0T hu'_Icc0T
    have hscale_close' : |(band d).scale E N (u : ℝ) - (band d).scale E N (u' : ℝ)| ≤
        (2 : ℝ) * (N : ℝ) ^ (2 - A / 2) := by
      have hpoly : ((band d).W N : ℝ) * ((1 - t N)⁻¹ + ((band d).L N : ℝ)) ≤
          (N : ℝ) * (2 * (N : ℝ)) := by
        have h2 : (1 - t N)⁻¹ + ((band d).L N : ℝ) ≤ 2 * (N : ℝ) := by linarith [hTinv, hLleN]
        have hnn : (0:ℝ) ≤ (1 - t N)⁻¹ + ((band d).L N : ℝ) :=
          add_nonneg (inv_pos.2 h1t).le (Nat.cast_nonneg _)
        exact mul_le_mul hWleN h2 hnn hN0.le
      calc |(band d).scale E N (u : ℝ) - (band d).scale E N (u' : ℝ)|
          ≤ ((band d).W N : ℝ) * ((1 - t N)⁻¹ + ((band d).L N : ℝ))
              * Real.sqrt |(u : ℝ) - (u' : ℝ)| := hscale_close
        _ ≤ (N:ℝ) * (2 * (N:ℝ)) * Real.sqrt |(u : ℝ) - (u' : ℝ)| :=
            mul_le_mul_of_nonneg_right hpoly (Real.sqrt_nonneg _)
        _ ≤ (N:ℝ) * (2 * (N:ℝ)) * (N : ℝ) ^ (-A / 2) :=
            mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
        _ = 2 * (N:ℝ) ^ (2 - A / 2) := by
            rw [show (N:ℝ) * (2 * (N:ℝ)) * (N : ℝ) ^ (-A / 2)
                  = 2 * ((N:ℝ) * ((N:ℝ) * (N : ℝ) ^ (-A / 2))) from by ring,
              hpow_add2 (-A / 2)]
            congr 2
            ring
    have hscale_ratio : (band d).scale E N (u : ℝ) ≤ (11 / 10) * (band d).scale E N (u' : ℝ) := by
      have h1 := (abs_le.mp hscale_close').2
      have h2 : (2 : ℝ) * (N:ℝ) ^ (2 - A / 2) ≤ (1 / 10) * (N : ℝ)⁻¹ := by
        rw [← hNinv_eq]; exact hScaleGapN
      linarith [h1, h2, hscale'_ge]
    have hscaleinv_ratio :
        ((band d).scale E N (u' : ℝ))⁻¹ ≤ (11 / 10) * ((band d).scale E N (u : ℝ))⁻¹ :=
      inv_le_const_mul_inv_of_le_const_mul hscale_pos hscale'_pos hscale_ratio
    have hscaleinv2 : ((band d).scale E N (u' : ℝ))⁻¹ ^ 2 ≤
        (11 / 10) ^ 2 * ((band d).scale E N (u : ℝ))⁻¹ ^ 2 := by
      have h1 := pow_le_pow_left₀ (inv_nonneg.2 hscale'_pos.le) hscaleinv_ratio 2
      calc ((band d).scale E N (u' : ℝ))⁻¹ ^ 2
          ≤ ((11 / 10) * ((band d).scale E N (u : ℝ))⁻¹) ^ 2 := h1
        _ = (11 / 10) ^ 2 * ((band d).scale E N (u : ℝ))⁻¹ ^ 2 := by ring
    ------------------------------------------------------------------
    -- (c) the η ratio to the 4th power
    ------------------------------------------------------------------
    have hηs_pos : 0 < etaT E (s N) := lt_of_lt_of_le hηu (etaT_le_of_le hE hu_lo)
    have hη4 : (etaT E (s N) / etaT E (u' : ℝ)) ^ 4 ≤
        (11 / 10) ^ 4 * (etaT E (s N) / etaT E (u : ℝ)) ^ 4 := by
      have heq : etaT E (s N) / etaT E (u' : ℝ) =
          (etaT E (s N) / etaT E (u : ℝ)) * (etaT E (u : ℝ) / etaT E (u' : ℝ)) := by
        field_simp
      rw [heq, mul_pow]
      have hratio_le : etaT E (u : ℝ) / etaT E (u' : ℝ) ≤ 11 / 10 := by
        rw [div_le_iff₀ hηu']; linarith [hη_ratio]
      have hratio_nn : (0 : ℝ) ≤ etaT E (u : ℝ) / etaT E (u' : ℝ) := by positivity
      have hpow_le : (etaT E (u : ℝ) / etaT E (u' : ℝ)) ^ 4 ≤ (11 / 10) ^ 4 :=
        pow_le_pow_left₀ hratio_nn hratio_le 4
      have hbase_nn : (0 : ℝ) ≤ (etaT E (s N) / etaT E (u : ℝ)) ^ 4 := by positivity
      calc (etaT E (s N) / etaT E (u : ℝ)) ^ 4 * (etaT E (u : ℝ) / etaT E (u' : ℝ)) ^ 4
          ≤ (etaT E (s N) / etaT E (u : ℝ)) ^ 4 * (11 / 10) ^ 4 :=
            mul_le_mul_of_nonneg_left hpow_le hbase_nn
        _ = (11 / 10) ^ 4 * (etaT E (s N) / etaT E (u : ℝ)) ^ 4 := by ring
    ------------------------------------------------------------------
    -- (d) the decayProf ratio
    ------------------------------------------------------------------
    set z : ℝ := (zdist ((band d).L N) (a - b) : ℝ) with hz_def
    have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg _
    have hzLe : 2 * z ≤ ((band d).L N : ℝ) := by
      rw [hz_def]
      exact_mod_cast two_mul_zdist_le ((band d).L N) (a - b)
    have hellu1 : (1 : ℝ) ≤ (band d).ell N (u : ℝ) :=
      one_le_ellHat _ ((band d).three_le_L N) hu_lo0 hu_lt1
    have hellu'1 : (1 : ℝ) ≤ (band d).ell N (u' : ℝ) :=
      one_le_ellHat _ ((band d).three_le_L N) hu'_lo0 hu'_lt1
    have hellclose : |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)| ≤
        (1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)| := by
      show |ellHat ((band d).L N) ((u : ℝ) : ℂ) - ellHat ((band d).L N) ((u' : ℝ) : ℂ)| ≤ _
      exact abs_ellHat_sub_le _ (ht1 N) hu_Icc0T hu'_Icc0T
    have hprod_le : z * |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)| ≤
        (1 / 2) * (N : ℝ) ^ (2 - A / 2) := by
      have h1 : z * |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)| ≤
          (((band d).L N : ℝ) / 2) * ((1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)|) := by
        calc z * |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)|
            ≤ z * ((1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)|) :=
              mul_le_mul_of_nonneg_left hellclose hz0
          _ ≤ (((band d).L N : ℝ) / 2) * ((1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)|) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith [hzLe]
      refine h1.trans ?_
      have h2 : (((band d).L N : ℝ) / 2) * ((1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)|) ≤
          ((N : ℝ) / 2) * ((N : ℝ) * (N : ℝ) ^ (-A / 2)) := by
        have h3 : (1 - t N)⁻¹ * Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ (N : ℝ) * (N : ℝ) ^ (-A / 2) :=
          mul_le_mul hTinv hsqrt_le (Real.sqrt_nonneg _) hN0.le
        exact mul_le_mul (by linarith [hLleN]) h3 (by positivity) (by positivity)
      refine h2.trans (le_of_eq ?_)
      rw [show (N : ℝ) / 2 * ((N : ℝ) * (N : ℝ) ^ (-A / 2))
            = (1 / 2) * ((N : ℝ) * ((N : ℝ) * (N : ℝ) ^ (-A / 2))) from by ring,
        hpow_add2 (-A / 2)]
      congr 2
      ring
    have hg_diff : |Real.sqrt (z / (band d).ell N (u : ℝ)) -
        Real.sqrt (z / (band d).ell N (u' : ℝ))| ≤ Real.sqrt (1 / 2) * (N : ℝ) ^ (1 - A / 4) := by
      have hstep1 : |Real.sqrt (z / (band d).ell N (u : ℝ)) -
          Real.sqrt (z / (band d).ell N (u' : ℝ))| =
          Real.sqrt z * |1 / Real.sqrt ((band d).ell N (u : ℝ)) -
            1 / Real.sqrt ((band d).ell N (u' : ℝ))| := by
        have heq : Real.sqrt (z / (band d).ell N (u : ℝ)) -
            Real.sqrt (z / (band d).ell N (u' : ℝ)) =
            Real.sqrt z * (1 / Real.sqrt ((band d).ell N (u : ℝ)) -
              1 / Real.sqrt ((band d).ell N (u' : ℝ))) := by
          rw [Real.sqrt_div hz0, Real.sqrt_div hz0, mul_sub, mul_one_div, mul_one_div]
        rw [heq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg z)]
      have hden1 : (1 : ℝ) ≤ Real.sqrt ((band d).ell N (u : ℝ)) :=
        Real.one_le_sqrt.2 (by linarith [hellu1])
      have hden2 : (1 : ℝ) ≤ Real.sqrt ((band d).ell N (u' : ℝ)) :=
        Real.one_le_sqrt.2 (by linarith [hellu'1])
      have hstep2 : |1 / Real.sqrt ((band d).ell N (u : ℝ)) -
          1 / Real.sqrt ((band d).ell N (u' : ℝ))| ≤
          |Real.sqrt ((band d).ell N (u' : ℝ)) - Real.sqrt ((band d).ell N (u : ℝ))| := by
        have heq : (1:ℝ) / Real.sqrt ((band d).ell N (u : ℝ)) -
            1 / Real.sqrt ((band d).ell N (u' : ℝ)) =
            (Real.sqrt ((band d).ell N (u' : ℝ)) - Real.sqrt ((band d).ell N (u : ℝ))) /
              (Real.sqrt ((band d).ell N (u : ℝ)) * Real.sqrt ((band d).ell N (u' : ℝ))) := by
          field_simp
        rw [heq, abs_div]
        have hd1 : (1:ℝ) ≤ Real.sqrt ((band d).ell N (u : ℝ)) * Real.sqrt ((band d).ell N (u' : ℝ)) := by
          nlinarith [hden1, hden2]
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt ((band d).ell N (u : ℝ)) *
          Real.sqrt ((band d).ell N (u' : ℝ)))]
        rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.sqrt ((band d).ell N (u : ℝ)) *
          Real.sqrt ((band d).ell N (u' : ℝ)))]
        nlinarith [abs_nonneg (Real.sqrt ((band d).ell N (u' : ℝ)) -
          Real.sqrt ((band d).ell N (u : ℝ))), hd1]
      have hstep3 : |Real.sqrt ((band d).ell N (u' : ℝ)) - Real.sqrt ((band d).ell N (u : ℝ))| ≤
          Real.sqrt |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)| := by
        have := abs_sqrt_sub_sqrt_le ((band d).ell N (u' : ℝ)) ((band d).ell N (u : ℝ))
        rwa [abs_sub_comm ((band d).ell N (u' : ℝ)) ((band d).ell N (u : ℝ))] at this
      have hstep4 : Real.sqrt z * |1 / Real.sqrt ((band d).ell N (u : ℝ)) -
          1 / Real.sqrt ((band d).ell N (u' : ℝ))| ≤
          Real.sqrt z * Real.sqrt |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)| :=
        mul_le_mul_of_nonneg_left (hstep2.trans hstep3) (Real.sqrt_nonneg _)
      refine hstep1.le.trans (hstep4.trans ?_)
      rw [← Real.sqrt_mul hz0]
      calc Real.sqrt (z * |(band d).ell N (u : ℝ) - (band d).ell N (u' : ℝ)|)
          ≤ Real.sqrt ((1 / 2) * (N : ℝ) ^ (2 - A / 2)) := Real.sqrt_le_sqrt hprod_le
        _ = Real.sqrt (1 / 2) * (N : ℝ) ^ (1 - A / 4) := by
            rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/2)]
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
            congr 1
            ring
    have hdecay_ratio : (band d).decayProf N (u' : ℝ) D a b ≤
        (11 / 10) * (band d).decayProf N (u : ℝ) D a b := by
      have hWD_le : (N : ℝ) ^ (-D) ≤ ((band d).W N : ℝ) ^ (-D) := by
        have hpow_le : ((band d).W N : ℝ) ^ D ≤ (N : ℝ) ^ D :=
          Real.rpow_le_rpow hWNpos.le hWleN hD0.le
        have hpow_pos : (0 : ℝ) < ((band d).W N : ℝ) ^ D := Real.rpow_pos_of_pos hWNpos D
        have := inv_anti₀ hpow_pos hpow_le
        rwa [← Real.rpow_neg hWNpos.le, ← Real.rpow_neg (Nat.cast_nonneg N)] at this
      have hgap := hDecayGapN
      have hexp_diff : Real.exp (-(Real.sqrt (z / (band d).ell N (u' : ℝ)))) ≤
          Real.exp (-(Real.sqrt (z / (band d).ell N (u : ℝ)))) +
            Real.sqrt (1 / 2) * (N : ℝ) ^ (1 - A / 4) := by
        have hexpb : |Real.exp (-(Real.sqrt (z / (band d).ell N (u : ℝ)))) -
            Real.exp (-(Real.sqrt (z / (band d).ell N (u' : ℝ))))| ≤
            Real.sqrt (1 / 2) * (N : ℝ) ^ (1 - A / 4) :=
          (abs_exp_neg_sub_exp_neg_le (Real.sqrt_nonneg (z / (band d).ell N (u : ℝ)))
            (Real.sqrt_nonneg (z / (band d).ell N (u' : ℝ)))).trans hg_diff
        have := (abs_le.mp hexpb).1
        linarith [this]
      have hexp_nonneg : (0:ℝ) ≤ Real.exp (-(Real.sqrt (z / (band d).ell N (u : ℝ)))) :=
        (Real.exp_pos _).le
      have hWD_nonneg : (0:ℝ) ≤ ((band d).W N : ℝ) ^ (-D) := by positivity
      show Real.exp (-(z / (band d).ell N (u' : ℝ)) ^ ((1:ℝ)/2)) + ((band d).W N : ℝ) ^ (-D) ≤
        (11/10) * (Real.exp (-(z / (band d).ell N (u : ℝ)) ^ ((1:ℝ)/2))
          + ((band d).W N : ℝ) ^ (-D))
      rw [show (z / (band d).ell N (u' : ℝ)) ^ ((1:ℝ)/2) = Real.sqrt (z / (band d).ell N (u' : ℝ))
            from (Real.sqrt_eq_rpow _).symm,
          show (z / (band d).ell N (u : ℝ)) ^ ((1:ℝ)/2) = Real.sqrt (z / (band d).ell N (u : ℝ))
            from (Real.sqrt_eq_rpow _).symm]
      nlinarith [hexp_diff, hgap, hWD_le, hexp_nonneg, hWD_nonneg]
    ------------------------------------------------------------------
    -- (e) the lkErr additive bound
    ------------------------------------------------------------------
    have hlk_bound : (sample d).lkErr E N (u : ℝ) ω (pmLoop a b) ≤
        (sample d).lkErr E N (u' : ℝ) ω (pmLoop a b) + (N : ℝ) ^ (-((D + 2) + 2)) := by
      rw [lkErr_eq_norm_lkT, lkErr_eq_norm_lkT]
      have hKbBk : ∀ w ∈ Set.Icc (0 : ℝ) (t N), ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
          2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval E N w J‖ ≤ (N : ℝ) ^ (3 : ℝ) := hKb2N
      have hmod := norm_lkT_flow_sub_le d N hE (ht1 N) hu_Icc0T hu'_Icc0T ω
        (n := 2) (by norm_num) (![true, false], (![a, b] : LoopArg ((band d).L N) 2))
        (Bk := (N : ℝ) ^ (3 : ℝ)) (by positivity) hKbBk
      have hnormsub := norm_sub_norm_le
        (SumZeroDyn.lkT (sample d) E N (u : ℝ) ω (![true, false])
          (![a, b] : LoopArg ((band d).L N) 2))
        (SumZeroDyn.lkT (sample d) E N (u' : ℝ) ω (![true, false])
          (![a, b] : LoopArg ((band d).L N) 2))
      have hXle : ‖Xmat d N ω‖ + 1 ≤ 2 * (N : ℝ) := by linarith [hωΞ]
      have hηTinv_pos : (0:ℝ) ≤ (etaT E (t N))⁻¹ := by positivity
      have hConst_le : (2 : ℝ) * ((etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ * (‖Xmat d N ω‖ + 1) *
            (etaT E (t N))⁻¹ ^ (2 - 1)) +
          ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * ((N : ℝ) ^ (3 : ℝ)) ^ 2 ≤
          (8 : ℝ) * (N : ℝ) ^ (8 : ℕ) := by
        have e1 : (etaT E (t N))⁻¹ ^ (2 - 1) = (etaT E (t N))⁻¹ := by norm_num
        have e3 : ((N:ℝ) ^ (3 : ℝ)) ^ 2 = (N:ℝ) ^ (6 : ℕ) := by
          rw [← Real.rpow_natCast ((N:ℝ) ^ (3:ℝ)) 2, ← Real.rpow_mul hN0.le]
          norm_num
        rw [e1, e3]
        have h1 : (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ * (‖Xmat d N ω‖ + 1) * (etaT E (t N))⁻¹
            ≤ (N:ℝ) ^ (4:ℕ) * 2 := by
          have hh : (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ * (‖Xmat d N ω‖ + 1) * (etaT E (t N))⁻¹
              ≤ (N:ℝ) * (N:ℝ) * (2*(N:ℝ)) * (N:ℝ) :=
            mul_le_mul (mul_le_mul (mul_le_mul hreg1N hreg1N hηTinv_pos hN0.le) hXle
              (by positivity) (by positivity)) hreg1N hηTinv_pos (by positivity)
          refine hh.trans (le_of_eq ?_)
          ring
        have h2 : ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * (N:ℝ) ^ (6:ℕ) ≤
            (N:ℝ) ^ (8:ℕ) * 4 := by
          have hh : ((band d).W N : ℝ) * ((band d).L N : ℝ) ≤ (N:ℝ) * (N:ℝ) :=
            mul_le_mul hWleN hLleN (Nat.cast_nonneg _) hN0.le
          have hnn : (0:ℝ) ≤ (2:ℝ)^2 * (N:ℝ)^(6:ℕ) := by positivity
          have hstep : ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * (N:ℝ)^(6:ℕ)
              ≤ ((N:ℝ)*(N:ℝ)) * ((2:ℝ)^2 * (N:ℝ)^(6:ℕ)) := by
            calc ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * (N:ℝ)^(6:ℕ)
                = (((band d).W N : ℝ) * ((band d).L N:ℝ)) * ((2:ℝ)^2 * (N:ℝ)^(6:ℕ)) := by ring
              _ ≤ ((N:ℝ)*(N:ℝ)) * ((2:ℝ)^2 * (N:ℝ)^(6:ℕ)) := mul_le_mul_of_nonneg_right hh hnn
          refine hstep.trans (le_of_eq ?_)
          ring
        have h5 : (N:ℝ) ^ (4:ℕ) ≤ (N:ℝ) ^ (8:ℕ) := by
          have h2' : (1:ℝ) ≤ (N:ℝ)^(4:ℕ) := one_le_pow₀ (by linarith [hN1'] : (1:ℝ) ≤ (N:ℝ))
          have heq : (N:ℝ)^(8:ℕ) = (N:ℝ)^(4:ℕ) * (N:ℝ)^(4:ℕ) := by ring
          rw [heq]
          calc (N:ℝ)^(4:ℕ) = (N:ℝ)^(4:ℕ) * 1 := (mul_one _).symm
            _ ≤ (N:ℝ)^(4:ℕ) * (N:ℝ)^(4:ℕ) := mul_le_mul_of_nonneg_left h2' (by positivity)
        nlinarith [h1, h2, h5]
      have hmod' : ‖SumZeroDyn.lkT (sample d) E N (u : ℝ) ω (![true, false])
            (![a, b] : LoopArg ((band d).L N) 2) -
          SumZeroDyn.lkT (sample d) E N (u' : ℝ) ω (![true, false])
            (![a, b] : LoopArg ((band d).L N) 2)‖ ≤
          (8 : ℝ) * (N : ℝ) ^ (8 : ℕ) * Real.sqrt |(u : ℝ) - (u' : ℝ)| :=
        hmod.trans (mul_le_mul_of_nonneg_right hConst_le (Real.sqrt_nonneg _))
      have hfinal : (8 : ℝ) * (N : ℝ) ^ (8 : ℕ) * Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤
          (N : ℝ) ^ (-((D + 2) + 2)) := by
        refine (mul_le_mul_of_nonneg_left hsqrt_le (by positivity)).trans ?_
        rw [mul_assoc, hpow_nat_rpow 8 (-A / 2)]
        have := hLkGapN
        have heq : (8:ℝ) - A/2 = ((8:ℕ):ℝ) + (-A/2) := by push_cast; ring
        rw [← heq]
        have heq2 : -((D + 2) + 2) = -(D + 4) := by ring
        rw [heq2]
        linarith [this]
      linarith [hnormsub, hmod', hfinal]
    have hbnd_nonneg : (0:ℝ) ≤ (etaT E (s N)/etaT E (u:ℝ))^4 *
        ((band d).scale E N (u:ℝ))⁻¹^2 * (band d).decayProf N (u:ℝ) D a b := by
      have h3 : (0:ℝ) ≤ (band d).decayProf N (u:ℝ) D a b := by
        unfold Band.decayProf; positivity
      positivity
    have hstep1 : (etaT E (s N)/etaT E (u':ℝ))^4 * ((band d).scale E N (u':ℝ))⁻¹^2 ≤
        ((11/10)^4 * (etaT E (s N)/etaT E (u:ℝ))^4) *
          ((11/10)^2 * ((band d).scale E N (u:ℝ))⁻¹^2) := by
      have hB_nn : (0:ℝ) ≤ (11/10)^4 * (etaT E (s N)/etaT E (u:ℝ))^4 := by positivity
      exact mul_le_mul hη4 hscaleinv2 (by positivity) hB_nn
    have hstep2 : (etaT E (s N)/etaT E (u':ℝ))^4 * ((band d).scale E N (u':ℝ))⁻¹^2 *
        (band d).decayProf N (u':ℝ) D a b ≤
        (((11/10)^4 * (etaT E (s N)/etaT E (u:ℝ))^4) *
            ((11/10)^2 * ((band d).scale E N (u:ℝ))⁻¹^2)) *
          ((11/10) * (band d).decayProf N (u:ℝ) D a b) := by
      have hC_nn : (0:ℝ) ≤ (band d).decayProf N (u':ℝ) D a b := by
        unfold Band.decayProf; positivity
      have hD_nn : (0:ℝ) ≤ ((11/10)^4 * (etaT E (s N)/etaT E (u:ℝ))^4) *
          ((11/10)^2 * ((band d).scale E N (u:ℝ))⁻¹^2) := by positivity
      exact mul_le_mul hstep1 hdecay_ratio hC_nn hD_nn
    have heq : (((11/10)^4 * (etaT E (s N)/etaT E (u:ℝ))^4) *
          ((11/10)^2 * ((band d).scale E N (u:ℝ))⁻¹^2)) *
        ((11/10) * (band d).decayProf N (u:ℝ) D a b)
      = (11/10)^7 * ((etaT E (s N)/etaT E (u:ℝ))^4 * ((band d).scale E N (u:ℝ))⁻¹^2 *
          (band d).decayProf N (u:ℝ) D a b) := by ring
    refine ⟨hlk_bound, hstep2.trans (le_of_eq heq |>.trans ?_)⟩
    exact mul_le_mul_of_nonneg_right hκ7 hbnd_nonneg
  exact netLift_of_relaxed
    (ξ := fun N (p : RBM.TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
      (sample d).lkErr E N (p.1 : ℝ) ω (pmLoop p.2.1 p.2.2))
    (ζ := fun N p (_ : Ω d) => (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 4 *
      ((band d).scale E N (p.1 : ℝ))⁻¹ ^ 2 * (band d).decayProf N (p.1 : ℝ) D p.2.1 p.2.2)
    (ξ' := fun N (p : RBM.TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
      (sample d).lkErr E N (p.1 : ℝ) ω (pmLoop p.2.1 p.2.2))
    (ζ' := fun N p (_ : Ω d) => (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 4 *
      ((band d).scale E N (p.1 : ℝ))⁻¹ ^ 2 * (band d).decayProf N (p.1 : ℝ) D p.2.1 p.2.2)
    hst one_pos hlen hApos (hpt D hD0) (highProb_norm_Xmat_le d) hlow hclose (hpt D hD0)

end Grid
end Gauss
end RBM
