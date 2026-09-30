/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridBootstrap
import RBM1D.Gauss.GridNetLift
import RBM1D.Gauss.LoopLipschitz
import RBM1D.Gauss.Step1Hyp
import RBM1D.Gauss.Step2Plain
import RBM1D.Hierarchy.Step2FarMart
import RBM1D.Hierarchy.Step2MomentStep

/-!
# The time-uniform far lift: the left net point and the far bad-set transfer

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, pass 2 of the far-field argument (the second pass after (5.48)).

This file contains:

* `Grid.stochDom_of_forall_seq_left` — the abstract net argument with the net point chosen to
  the **left** of `u` (so that a family whose modulus is only one-sided, such as the far
  indicator `1(d > 6ℓ*_u)`, can still be lifted from "along every sequence" to the full window).
* `Grid.lkErr_modulus_plain` — the modulus of `lkErr` in the time, `8 N^8 √|u-u'|`, independent
  of `D`.
* `Grid.FarLift.exists_netTime_le_close` — the left net point.
* `Grid.FarLift.pg_bad_far_eq_flow` — the transfer of a bad-set probability from the grid to the
  flow, with a far side condition on the label.

## Route

`∀ D` is fixed first; `A(D) = 4D+44`, `B = D+2`. The modulus of `lkErr` in the time is
`8 N^8 √|u-u'|`, independent of `D`; since `T ≥ W^{-D} ≥ N^{-D}`, the normalised exponent is
`8 + D`. The left net point `u' ≤ u` comes from `FarLift.exists_netTime_le_close`; on it,
`ℓ_{u'} ≤ ℓ_u` (`ellStar_mono_time`) turns "far at `u`" into "far at `u'`" (`far_mono_time`), so
the indicator only ever *shrinks* going right-to-left, which is the one direction the
net-closeness hypothesis needs. `FarLift.pg_bad_far_eq_flow` generalises `pg_bad_eq_flow`
(`GridBootstrap.lean`) to a bad-set predicate carrying the far side condition.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped Matrix.Norms.L2Operator

variable (d : Dims)

/-! ### `pg_bad_eq_flow` (GridBootstrap.lean), generalised to carry a far side condition -/

/-- **The per-`N` transfer of a bad-set probability, with an extra side condition on the label
that does not depend on the matrix.** Exactly `pg_bad_eq_flow` with an extra conjunct `far p`
threaded through both sides; the measurability argument is unchanged (`far p` splits the union
over `p` into the known piece or the empty set). -/
theorem FarLift.pg_bad_far_eq_flow {E δ : ℝ} {s uR : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (hs0 : 0 ≤ s N)
    (hsu : s N ≤ uR N) (hK : K N ≠ 0) (far : ZMod (d.L N) × ZMod (d.L N) → Prop)
    (ζ : ZMod (d.L N) × ZMod (d.L N) → ℝ) :
    Pg d {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N), far p ∧
        (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) (H d s uR K N (K N) ω) (pmLoop p.1 p.2)}
      = RBM.Gauss.P d {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N), far p ∧
        (N : ℝ) ^ δ * ζ p < (sample d).lkErr E N (uR N) ω (pmLoop p.1 p.2)} := by
  classical
  set S : Set (Matrix (d.Idx N) (d.Idx N) ℂ) := {M | ∃ p : ZMod (d.L N) × ZMod (d.L N),
    far p ∧ (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) M (pmLoop p.1 p.2)} with hSdef
  have hS : MeasurableSet S := by
    have heq : S = ⋃ p : ZMod (d.L N) × ZMod (d.L N),
        if far p then {M | (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) M (pmLoop p.1 p.2)}
        else (∅ : Set (Matrix (d.Idx N) (d.Idx N) ℂ)) := by
      ext M
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨p, hp, hlt⟩
        exact ⟨p, by rw [if_pos hp]; exact hlt⟩
      · rintro ⟨p, hp⟩
        by_cases hfp : far p
        · rw [if_pos hfp] at hp; exact ⟨p, hfp, hp⟩
        · rw [if_neg hfp] at hp; exact hp.elim
    rw [heq]
    refine MeasurableSet.iUnion fun p => ?_
    split_ifs with hfp
    · exact measurableSet_lt measurable_const (measurable_lkErrMat d E N (uR N) (pmLoop p.1 p.2))
    · exact MeasurableSet.empty
  have hmap : (Pg d).map (H d s uR K N (K N)) = (RBM.Gauss.P d).map (Hflow d N (uR N)) := by
    have h := map_H_eq (d := d) s uR K N (K N) hs0 hsu hK
    rwa [time_last s uR K N hK] at h
  have hHm : Measurable (H d s uR K N (K N)) :=
    (H_measurable_filt d s uR K N (K N)).mono ((filt d).le (K N)) le_rfl
  have hFm : Measurable (Hflow d N (uR N)) := RBM.measurable_H (sample d) N (uR N)
  have e1 : {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N), far p ∧
      (N : ℝ) ^ δ * ζ p < lkErrMat d E N (uR N) (H d s uR K N (K N) ω) (pmLoop p.1 p.2)}
      = H d s uR K N (K N) ⁻¹' S := rfl
  have e2 : {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N), far p ∧
      (N : ℝ) ^ δ * ζ p < (sample d).lkErr E N (uR N) ω (pmLoop p.1 p.2)}
      = Hflow d N (uR N) ⁻¹' S := rfl
  rw [e1, e2, ← Measure.map_apply hHm hS, ← Measure.map_apply hFm hS, hmap]

/-! ### The Hölder modulus of `lkErr` in the time -/

/-- **The `1/2`-Hölder modulus in time of `lkErr` at a `2`-loop**, independent of `D`, on the
event `‖X‖ + 1 ≤ 2N`. -/
theorem lkErr_modulus_plain (d : Dims) {E : ℝ} (hE : |E| < 2) (N : ℕ) {t0 : ℝ} (ht0 : t0 < 1)
    {u u' : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) t0) (hu' : u' ∈ Set.Icc (0 : ℝ) t0)
    {ω : Ω d} (hX : ‖Xmat d N ω‖ + 1 ≤ 2 * (N : ℝ))
    (hKb : ∀ w ∈ Set.Icc (0 : ℝ) t0, ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval E N w J‖ ≤ (N : ℝ) ^ (3 : ℝ))
    (hreg1 : (etaT E t0)⁻¹ ≤ (N : ℝ)) (hWleN : ((band d).W N : ℝ) ≤ (N : ℝ))
    (hLleN : ((band d).L N : ℝ) ≤ (N : ℝ)) (hN1 : (1 : ℝ) ≤ N) (a b : ZMod ((band d).L N)) :
    (sample d).lkErr E N u ω (pmLoop a b) ≤
      (sample d).lkErr E N u' ω (pmLoop a b) + 8 * (N : ℝ) ^ (8 : ℕ) * Real.sqrt |u - u'| := by
  rw [lkErr_eq_norm_lkT, lkErr_eq_norm_lkT]
  have hN0 : (0 : ℝ) < N := by linarith
  have hηt0 : 0 < etaT E t0 := etaT_pos_of_lt_one' hE ht0
  have hηTinv_pos : (0 : ℝ) ≤ (etaT E t0)⁻¹ := (inv_pos.2 hηt0).le
  have hmod := norm_lkT_flow_sub_le d N hE ht0 hu hu' ω (n := 2) (by norm_num)
      (![true, false], (![a, b] : LoopArg ((band d).L N) 2)) (Bk := (N : ℝ) ^ (3 : ℝ))
      (by positivity) hKb
  have hnormsub := norm_sub_norm_le
    (SumZeroDyn.lkT (sample d) E N u ω (![true, false]) (![a, b] : LoopArg ((band d).L N) 2))
    (SumZeroDyn.lkT (sample d) E N u' ω (![true, false]) (![a, b] : LoopArg ((band d).L N) 2))
  have hConst_le : (2 : ℝ) * ((etaT E t0)⁻¹ * (etaT E t0)⁻¹ * (‖Xmat d N ω‖ + 1) *
        (etaT E t0)⁻¹ ^ (2 - 1)) +
      ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * ((N : ℝ) ^ (3 : ℝ)) ^ 2 ≤
      (8 : ℝ) * (N : ℝ) ^ (8 : ℕ) := by
    have e1 : (etaT E t0)⁻¹ ^ (2 - 1) = (etaT E t0)⁻¹ := by norm_num
    have e3 : ((N : ℝ) ^ (3 : ℝ)) ^ 2 = (N : ℝ) ^ (6 : ℕ) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ (3 : ℝ)) 2, ← Real.rpow_mul hN0.le]
      norm_num
    rw [e1, e3]
    have h1 : (etaT E t0)⁻¹ * (etaT E t0)⁻¹ * (‖Xmat d N ω‖ + 1) * (etaT E t0)⁻¹
        ≤ (N : ℝ) ^ (4 : ℕ) * 2 := by
      have hh : (etaT E t0)⁻¹ * (etaT E t0)⁻¹ * (‖Xmat d N ω‖ + 1) * (etaT E t0)⁻¹
          ≤ (N : ℝ) * (N : ℝ) * (2 * (N : ℝ)) * (N : ℝ) :=
        mul_le_mul (mul_le_mul (mul_le_mul hreg1 hreg1 hηTinv_pos hN0.le) hX
          (by positivity) (by positivity)) hreg1 hηTinv_pos (by positivity)
      refine hh.trans (le_of_eq ?_)
      ring
    have h2 : ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * (N : ℝ) ^ (6 : ℕ) ≤
        (N : ℝ) ^ (8 : ℕ) * 4 := by
      have hh : ((band d).W N : ℝ) * ((band d).L N : ℝ) ≤ (N : ℝ) * (N : ℝ) :=
        mul_le_mul hWleN hLleN (Nat.cast_nonneg _) hN0.le
      have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ 2 * (N : ℝ) ^ (6 : ℕ) := by positivity
      have hstep : ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * (N : ℝ) ^ (6 : ℕ)
          ≤ ((N : ℝ) * (N : ℝ)) * ((2 : ℝ) ^ 2 * (N : ℝ) ^ (6 : ℕ)) := by
        calc ((band d).W N : ℝ) * (2 : ℝ) ^ 2 * ((band d).L N : ℝ) * (N : ℝ) ^ (6 : ℕ)
            = (((band d).W N : ℝ) * ((band d).L N : ℝ)) * ((2 : ℝ) ^ 2 * (N : ℝ) ^ (6 : ℕ)) := by
              ring
          _ ≤ ((N : ℝ) * (N : ℝ)) * ((2 : ℝ) ^ 2 * (N : ℝ) ^ (6 : ℕ)) :=
            mul_le_mul_of_nonneg_right hh hnn
      refine hstep.trans (le_of_eq ?_)
      ring
    have h5 : (N : ℝ) ^ (4 : ℕ) ≤ (N : ℝ) ^ (8 : ℕ) := by
      have h2' : (1 : ℝ) ≤ (N : ℝ) ^ (4 : ℕ) := one_le_pow₀ (by linarith [hN1] : (1 : ℝ) ≤ (N : ℝ))
      have heq : (N : ℝ) ^ (8 : ℕ) = (N : ℝ) ^ (4 : ℕ) * (N : ℝ) ^ (4 : ℕ) := by ring
      rw [heq]
      calc (N : ℝ) ^ (4 : ℕ) = (N : ℝ) ^ (4 : ℕ) * 1 := (mul_one _).symm
        _ ≤ (N : ℝ) ^ (4 : ℕ) * (N : ℝ) ^ (4 : ℕ) := mul_le_mul_of_nonneg_left h2' (by positivity)
    nlinarith [h1, h2, h5]
  have hmod' : ‖SumZeroDyn.lkT (sample d) E N u ω (![true, false])
        (![a, b] : LoopArg ((band d).L N) 2) -
      SumZeroDyn.lkT (sample d) E N u' ω (![true, false])
        (![a, b] : LoopArg ((band d).L N) 2)‖ ≤
      (8 : ℝ) * (N : ℝ) ^ (8 : ℕ) * Real.sqrt |u - u'| :=
    hmod.trans (mul_le_mul_of_nonneg_right hConst_le (Real.sqrt_nonneg _))
  linarith [hnormsub, hmod']

/-! ### (T1) the generic net argument with the net point chosen to the LEFT of `u` -/

section Left

variable {Ωb : Type*} [MeasurableSpace Ωb] {P : Measure Ωb} {s t : ℕ → ℝ}

/-- **Left net point, floor index**: for `u ∈ [s_N, t_N]` there is a net point of spacing
`T / netSize A N` that lies to the LEFT of `u`: the "floor index" of the floor construction of
`Gauss.exists_netPt_close`. -/
theorem FarLift.exists_netTime_le_close {T : ℝ} (hT : 0 < T) (hlen : ∀ N, t N - s N ≤ T)
    (A : ℝ) (N : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (s N) (t N)) :
    ∃ k : Fin (netSize A N + 1), s N + netPt T A N k ≤ u ∧
      u - (s N + netPt T A N k) ≤ T / (netSize A N : ℝ) := by
  have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
  have hw0 : (0 : ℝ) ≤ u - s N := by linarith [hu.1]
  have hwT : u - s N ≤ T := by linarith [hu.2, hlen N]
  set x : ℝ := (u - s N) * (netSize A N : ℝ) / T with hx_def
  have hxT : x * T = (u - s N) * (netSize A N : ℝ) := by
    rw [hx_def]; exact div_mul_cancel₀ _ hT.ne'
  have hx0 : 0 ≤ x := div_nonneg (mul_nonneg hw0 hm.le) hT.le
  have hxm : x ≤ (netSize A N : ℝ) := by
    rw [hx_def, div_le_iff₀ hT]; nlinarith [hwT, hm.le]
  have hkm : ⌊x⌋₊ ≤ netSize A N := Nat.floor_le_of_le hxm
  have hfl : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  have hfu : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨⟨⌊x⌋₊, Nat.lt_succ_of_le hkm⟩, ?_, ?_⟩
  · have hnet : netPt T A N ⟨⌊x⌋₊, Nat.lt_succ_of_le hkm⟩
        = ((⌊x⌋₊ : ℕ) : ℝ) * T / (netSize A N : ℝ) := rfl
    rw [hnet]
    have hstep1 : ((⌊x⌋₊ : ℕ) : ℝ) * T ≤ (u - s N) * (netSize A N : ℝ) :=
      calc ((⌊x⌋₊ : ℕ) : ℝ) * T ≤ x * T := mul_le_mul_of_nonneg_right hfl hT.le
        _ = (u - s N) * (netSize A N : ℝ) := hxT
    have hdiv := (div_le_iff₀ hm).mpr hstep1
    linarith [hdiv]
  · have hnet : netPt T A N ⟨⌊x⌋₊, Nat.lt_succ_of_le hkm⟩
        = ((⌊x⌋₊ : ℕ) : ℝ) * T / (netSize A N : ℝ) := rfl
    rw [hnet]
    have hstep2 : (u - s N) * (netSize A N : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) * T + T := by
      have h1 : x * T < (((⌊x⌋₊ : ℕ) : ℝ) + 1) * T := mul_lt_mul_of_pos_right hfu hT
      rw [hxT] at h1
      nlinarith [h1]
    have hdiv2 := (le_div_iff₀ hm).mpr hstep2
    have heq : (((⌊x⌋₊ : ℕ) : ℝ) * T + T) / (netSize A N : ℝ)
        = ((⌊x⌋₊ : ℕ) : ℝ) * T / (netSize A N : ℝ) + T / (netSize A N : ℝ) := by
      rw [add_div]
    rw [heq] at hdiv2
    linarith [hdiv2]

/-- **`stochDom_of_forall_seq_left`**: the net argument with the
net point chosen to the LEFT of `u`. A `≺`-bound along every time sequence, together with a
one-sided "close in, close out" modulus valid on a high-probability event `Ξ` **only for
`u' ≤ u`**, already gives the full window statement — no two-sided modulus or continuity in `u`
is needed. -/
theorem stochDom_of_forall_seq_left {V : ℕ → Type*}
    {ξ ζ : ∀ N, RBM.TimeIcc s t N × V N → Ωb → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ}
    (hT : 0 < T) (hlen : ∀ N, t N - s N ≤ T) {A B : ℝ} (hA : 0 ≤ A)
    (hseq : ∀ u : ∀ N, RBM.TimeIcc s t N,
      StochDom P (fun N v ω => ξ N (u N, v) ω) (fun N v ω => ζ N (u N, v) ω))
    {Ξ : ℕ → Set Ωb} (hΞ : HighProb P Ξ)
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ (p : RBM.TimeIcc s t N × V N) (ω : Ωb),
      (N : ℝ) ^ (-B) ≤ ζ N p ω)
    (hclose : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ u u' : RBM.TimeIcc s t N, (u' : ℝ) ≤ u →
      (u : ℝ) - u' ≤ (N : ℝ) ^ (-A) → ∀ v : V N,
        ξ N (u, v) ω ≤ ξ N (u', v) ω + (N : ℝ) ^ (-(B + 2)) ∧
        ζ N (u', v) ω ≤ 2 * ζ N (u, v) ω) :
    StochDom P ξ ζ := by
  have hA1 : (0 : ℝ) ≤ A + 1 := by linarith
  have hnet := stochDom_reindex_of_forall_seq (V := V)
    (W := fun N => Fin (netSize (A + 1) N + 1)) hst hseq
    (fun N k => netTimeIcc (s := s) (t := t) hst hT.le (A + 1) N k)
    (C := A + 1 + 1) (by linarith) (card_net_le hA1)
  refine stochDom_of_subset_highProb hnet hΞ fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [hclose, hlow, eventually_ge_atTop 2, eventually_le_rpow T one_pos,
    eventually_le_rpow 3 hτ2] with N hcloseN hlowN hN2 hTN hN3
  rintro ω ⟨⟨⟨u, v⟩, hbad⟩, hωΞ⟩
  have hNpos : (0 : ℝ) < N := by positivity
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNpos' : (0 : ℝ) < (N : ℝ) := by linarith
  rw [Real.rpow_one] at hTN
  have hmpos : (0 : ℝ) < (netSize (A + 1) N : ℝ) := by exact_mod_cast netSize_pos (A + 1) N
  have hmge : (N : ℝ) ^ (A + 1) ≤ (netSize (A + 1) N : ℝ) := rpow_le_netSize _ _
  have hNA1 : (0 : ℝ) < (N : ℝ) ^ (A + 1) := Real.rpow_pos_of_pos hNpos' _
  obtain ⟨k, hk_le, hk_close⟩ := FarLift.exists_netTime_le_close (s := s) (t := t) hT hlen (A + 1) N u.2
  have hnetEq : (netTimeIcc (s := s) (t := t) hst hT.le (A + 1) N k : ℝ)
      = s N + netPt T (A + 1) N k := by
    show netTime s t T (A + 1) N k = _
    unfold netTime
    exact min_eq_right (hk_le.trans u.2.2)
  have hdist_le : (netTimeIcc (s := s) (t := t) hst hT.le (A + 1) N k : ℝ) ≤ (u : ℝ) := by
    rw [hnetEq]; exact hk_le
  have hdist : (u : ℝ) - (netTimeIcc (s := s) (t := t) hst hT.le (A + 1) N k : ℝ) ≤ (N : ℝ) ^ (-A) := by
    rw [hnetEq]
    refine hk_close.trans ?_
    have h1 : T / (netSize (A + 1) N : ℝ) ≤ T / (N : ℝ) ^ (A + 1) := by gcongr
    refine h1.trans ?_
    rw [div_le_iff₀ hNA1]
    have hmul : (N : ℝ) ^ (-A) * (N : ℝ) ^ (A + 1) = (N : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hNpos']; ring_nf
    rw [hmul, Real.rpow_one]
    exact hTN
  obtain ⟨hξ, hζ⟩ := hcloseN ω hωΞ u _ hdist_le hdist v
  set z : ℝ := ζ N (u, v) ω with hz_def
  set z' : ℝ := ζ N (netTimeIcc (s := s) (t := t) hst hT.le (A + 1) N k, v) ω with hz'_def
  set x : ℝ := ξ N (u, v) ω with hx_def
  set x' : ℝ := ξ N (netTimeIcc (s := s) (t := t) hst hT.le (A + 1) N k, v) ω with hx'_def
  have hzlow : (N : ℝ) ^ (-B) ≤ z := hlowN (u, v) ω
  have hz0 : (0 : ℝ) ≤ z := le_trans (Real.rpow_nonneg hNpos'.le _) hzlow
  have hBB : (N : ℝ) ^ (-(B + 2)) < (N : ℝ) ^ (-B) := by
    refine Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  have hhalf : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos']; ring_nf
  have hbig : (1 : ℝ) ≤ (N : ℝ) ^ τ - 2 * (N : ℝ) ^ (τ / 2) := by
    nlinarith [hhalf, hN3]
  have hprod : (0 : ℝ) ≤ ((N : ℝ) ^ τ - 2 * (N : ℝ) ^ (τ / 2) - 1) * z :=
    mul_nonneg (by linarith) hz0
  have hhalf0 : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg hNpos'.le _
  have hz'le : (N : ℝ) ^ (τ / 2) * z' ≤ (N : ℝ) ^ (τ / 2) * (2 * z) :=
    mul_le_mul_of_nonneg_left hζ hhalf0
  refine ⟨(k, v), ?_⟩
  show (N : ℝ) ^ (τ / 2) * z' < x'
  nlinarith [hbad, hξ, hprod, hzlow, hBB, hz'le]

end Left

end RBM.Gauss.Grid
