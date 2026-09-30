/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Holder
import RBM1D.EnergyN.Unif.Gauss.Lemma514Holder

/-!
# Hölder continuity in time and the kernel bound along the flow, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`: the time-Hölder bound on
`(W ℓ_u η_u)^m ‖lkT‖` (`RBM.Gauss.hHol_flowN`) and the polynomial bound on the kernels `K_J` of
lengths `2 ≤ |J| ≤ m` (`RBM.Gauss.hKb_flowN`).

## The external `κ` (`hKb_flowN` only)

`hHol_flowN` fixes no energy-dependent constant: its hypotheses `hreg`/`hXΞ`/`hKb` are already
`∀ᶠ N`, so no constant is fixed before them.

A spectral gap derived from `E` itself, `k := min 1 (2 - |E|)` as in
`RBM.Gauss.exists_gap_of_abs_lt_two`, is a genuine function of the specific `E`, and the constant
of `RBM.Gauss.exists_norm_Kval_le_upto` is chosen after it. So `hKb_flowN` takes the spectral gap
`κ` externally (`hEκ : ∀ N, |E N| ≤ 2 - κ`) and calls `RBM.Gauss.exists_norm_Kval_le_upto_unif`,
whose constant is chosen before `E`, as for `Step3.flow_xiL_leN`.
-/

namespace RBM.Gauss

open MeasureTheory Filter

open scoped Matrix.Norms.L2Operator

/-- **Time-Hölder bound**: eventually, on `Ξ`, for `u, v ∈ [s, t]`,
`|(W ℓ_u η_u)^m ‖lkT_u‖ - (W ℓ_v η_v)^m ‖lkT_v‖| ≤ N^{c(3m+4)+1} |u - v|^{1/2}`, given
`η_t⁻¹ ≤ N^c`, `‖X‖ + 1 ≤ N^c` on `Ξ`, and the kernel bound `hKb`. No energy-dependent constant is
fixed here. -/
theorem hHol_flowN (d : Dims) {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {Ξ : ℕ → Set (Ω d)} {c : ℝ} (hc1 : 1 ≤ c) {m : ℕ} (hm : 1 ≤ m)
    (hreg : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ c)
    (hXΞ : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ‖Xmat d N ω‖ + 1 ≤ (N : ℝ) ^ c)
    (hKb : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (t N),
      ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF → 2 ≤ J.length → J.length ≤ m →
        ‖(band d).Kval (E N) N w J‖ ≤ (N : ℝ) ^ c) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : LoopData ((band d).L N) m,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |(band d).scale (E N) N u ^ m * ‖SumZeroDyn.lkT (sample d) (E N) N u ω q.1 q.2‖
            - (band d).scale (E N) N v ^ m * ‖SumZeroDyn.lkT (sample d) (E N) N v ω q.1 q.2‖|
          ≤ (N : ℝ) ^ (c * (3 * (m : ℝ) + 4) + 1) * |u - v| ^ ((1 : ℝ) / 2) := by
  have hlt : c * (3 * (m : ℝ) + 4) < c * (3 * (m : ℝ) + 4) + 1 := by linarith
  filter_upwards [hreg, hXΞ, hKb, (band d).dim, eventually_ge_atTop 1,
    eventually_const_mul_rpow_le_rpow ((m : ℝ) ^ 2 + 5 * m) hlt]
    with N hregN hXN hKbN hdimN hN1 hnumN
  intro ω hω q u hu v hv
  have hT : t N < 1 := ht1 N
  have hu' : u ∈ Set.Icc (0 : ℝ) (t N) := ⟨le_trans (hs0 N) hu.1, hu.2⟩
  have hv' : v ∈ Set.Icc (0 : ℝ) (t N) := ⟨le_trans (hs0 N) hv.1, hv.2⟩
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hR1 : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' (by linarith)
  have hNc : (N : ℝ) ≤ (N : ℝ) ^ c := by
    have h := Real.rpow_le_rpow_of_exponent_le hN1' hc1
    rwa [Real.rpow_one] at h
  have hηT : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE N) hT
  have hT0 : (0 : ℝ) < 1 - t N := by linarith
  -- `W ≤ N ≤ N^c` and `L ≤ N ≤ N^c`
  have hLpos : 0 < (band d).L N := by have := (band d).three_le_L N; omega
  have hWle : (((band d).W N : ℕ) : ℝ) ≤ (N : ℝ) ^ c := by
    have : (band d).W N ≤ N := le_trans (Nat.le_mul_of_pos_right _ hLpos) hdimN.1
    exact le_trans (by exact_mod_cast this) hNc
  have hLle : (((band d).L N : ℕ) : ℝ) ≤ (N : ℝ) ^ c := by
    have : (band d).L N ≤ N :=
      le_trans (Nat.le_mul_of_pos_left _ ((band d).W_pos N)) hdimN.1
    exact le_trans (by exact_mod_cast this) hNc
  -- `(1-t)^{-1} ≤ η_t^{-1} ≤ N^c`, because `η_t = (1-t) Im m ≤ 1-t`
  have hηle : etaT (E N) (t N) ≤ 1 - t N := by
    show (1 - t N) * (mE (E N)).im ≤ 1 - t N
    have him : (mE (E N)).im ≤ 1 := le_trans (le_abs_self _)
      (by have := Complex.abs_im_le_norm (mE (E N)); rwa [norm_mE (hE N).le] at this)
    nlinarith
  have hTinv : (1 - t N)⁻¹ ≤ (N : ℝ) ^ c := le_trans (inv_anti₀ hηT hηle) hregN
  -- the explicit estimate, and then its constant
  refine (abs_scaleLK_sub_le d N (hE N) hT hu' hv' ω hm q hR1
    (fun w hw J hJ h2 hle => hKbN w hw J hJ h2 hle)).trans ?_
  have hconst := scaleLK_const_le (R := (N : ℝ) ^ c) (W := (((band d).W N : ℕ) : ℝ))
    (L := (((band d).L N : ℕ) : ℝ)) (Tinv := (1 - t N)⁻¹) (eta := (etaT (E N) (t N))⁻¹)
    (Bk := (N : ℝ) ^ c) (X := ‖Xmat d N ω‖ + 1) hm hR1
    (Nat.cast_nonneg _) hWle (Nat.cast_nonneg _) hLle
    (le_of_lt (inv_pos.2 hT0)) hTinv (le_of_lt (inv_pos.2 hηT)) hregN
    (by linarith) le_rfl (by positivity) (hXN ω hω)
  have hpow : ((N : ℝ) ^ c) ^ (3 * m + 4) = (N : ℝ) ^ (c * (3 * (m : ℝ) + 4)) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ c) (3 * m + 4),
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    push_cast
    ring_nf
  have hfinal : ((m : ℝ) * ((((band d).W N : ℕ) : ℝ) * (((band d).L N : ℕ) : ℝ)) ^ (m - 1)
          * ((((band d).W N : ℕ) : ℝ) * ((1 - t N)⁻¹ + (((band d).L N : ℕ) : ℝ))))
        * ((etaT (E N) (t N))⁻¹ ^ m + (N : ℝ) ^ c)
      + ((((band d).W N : ℕ) : ℝ) * (((band d).L N : ℕ) : ℝ)) ^ m
        * ((m : ℝ) * ((etaT (E N) (t N))⁻¹ * (etaT (E N) (t N))⁻¹ * (‖Xmat d N ω‖ + 1)
              * (etaT (E N) (t N))⁻¹ ^ (m - 1))
            + (((band d).W N : ℕ) : ℝ) * (m : ℝ) ^ 2 * (((band d).L N : ℕ) : ℝ)
              * ((N : ℝ) ^ c) ^ 2)
      ≤ (N : ℝ) ^ (c * (3 * (m : ℝ) + 4) + 1) := by
    refine hconst.trans ?_
    rw [hpow]
    exact hnumN
  rw [Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_right hfinal (Real.rpow_nonneg (abs_nonneg _) _)

variable {Ωb : Type*} [MeasurableSpace Ωb]

/-- **The kernel bound `‖K_J‖ ≤ N^{cm+1}`** for `2 ≤ |J| ≤ m` at all times `w ∈ [0, t]`,
eventually, when `η_t⁻¹ ≤ N^c` eventually. The spectral gap `κ` is external and is fed to
`RBM.Gauss.exists_norm_Kval_le_upto_unif` (see the module docstring). -/
theorem hKb_flowN (B : Band Ωb) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {t : ℕ → ℝ} (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c) (m : ℕ)
    (hreg : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ c) :
    ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (t N),
      ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ m →
        ‖B.Kval (E N) N w J‖ ≤ (N : ℝ) ^ (c * (m : ℝ) + 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_Kval_le_upto_unif B hκ0 hκ1 m
  have hlt : c * (m : ℝ) < c * (m : ℝ) + 1 := by linarith
  filter_upwards [hreg, eventually_ge_atTop 1, eventually_const_mul_rpow_le_rpow C hlt]
    with N hregN hN1 hnumN w hw J hJ hJ2 hJm
  have hE : |E N| < 2 := by have := hEκ N; linarith
  have hw0 : (0 : ℝ) ≤ w := hw.1
  have hw1 : w < 1 := lt_of_le_of_lt hw.2 (ht1 N)
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hRc : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0
  have hηw : 0 < etaT (E N) w := etaT_pos_of_lt_one' hE hw1
  have hηt : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' hE (ht1 N)
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hell : (1 : ℝ) ≤ B.ell N w := one_le_ellHat (B.L N) (B.three_le_L N) hw0 hw1
  -- `η_w ≤ W ℓ_w η_w`
  have hge : etaT (E N) w ≤ B.scale (E N) N w := by
    have h : (1 : ℝ) * 1 * etaT (E N) w ≤ (B.W N : ℝ) * B.ell N w * etaT (E N) w :=
      mul_le_mul_of_nonneg_right (mul_le_mul hW1 hell zero_le_one (by linarith)) hηw.le
    simpa [Band.scale] using h
  -- `(W ℓ_w η_w)^{-1} ≤ η_w^{-1} ≤ η_{t_N}^{-1} ≤ N^c`
  have hinv : (B.scale (E N) N w)⁻¹ ≤ (N : ℝ) ^ c :=
    le_trans (inv_anti₀ hηw hge) (le_trans (inv_anti₀ hηt (etaT_le_of_le hE hw.2)) hregN)
  have hbig : (B.scale (E N) N w)⁻¹ ^ (J.length - 1) ≤ ((N : ℝ) ^ c) ^ m := by
    calc (B.scale (E N) N w)⁻¹ ^ (J.length - 1)
        ≤ ((N : ℝ) ^ c) ^ (J.length - 1) :=
          pow_le_pow_left₀ (inv_nonneg.2 (B.scale_pos' hE N hw0 hw1).le) hinv _
      _ ≤ ((N : ℝ) ^ c) ^ m := pow_le_pow_right₀ hRc (by omega)
  have hpow : ((N : ℝ) ^ c) ^ m = (N : ℝ) ^ (c * (m : ℝ)) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ c) m, ← Real.rpow_mul (Nat.cast_nonneg N)]
  calc ‖B.Kval (E N) N w J‖ ≤ C * (B.scale (E N) N w)⁻¹ ^ (J.length - 1) :=
        hC (E N) (hEκ N) N w hw0 hw1 J hJ hJ2 hJm
    _ ≤ C * ((N : ℝ) ^ c) ^ m := mul_le_mul_of_nonneg_left hbig hC0
    _ = C * (N : ℝ) ^ (c * (m : ℝ)) := by rw [hpow]
    _ ≤ (N : ℝ) ^ (c * (m : ℝ) + 1) := hnumN

end RBM.Gauss

section Compat

open RBM RBM.Gauss MeasureTheory Filter

open scoped Matrix.Norms.L2Operator

end Compat
