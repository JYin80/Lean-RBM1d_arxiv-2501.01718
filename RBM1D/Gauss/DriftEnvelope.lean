/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.DriftDef
import RBM1D.Gauss.Lemma514Holder
import RBM1D.Hierarchy.Decay

/-!
# The pointwise deterministic envelope of the drift `F` of (5.15) (T238)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (5.13), (5.14), (5.15), (2.47).

## The gap this closes

Two places in the repository took *the same* statement as a named hypothesis:

* `RBM.Gauss.exists_bdd_uker_Qop_driftF` (and its three continuity/integrability consumers) in
  `RBM1D/Gauss/MomentDuhamelQInt.lean`, as `hFb`;
* `RBM.FastDecayFlow.hGd_Qop_driftF` in `RBM1D/Gauss/FastDecayFlow.lean`, as `hAM`.

Both need a **pointwise deterministic** bound `‖F_{u,σ,b}‖ ≤ c_F` valid for every loop argument
`b`, not a bound on the single composite `(U ∘ F_u)_a`: `Q_u` reads `F_u` through `RBM.Psum` at
`L^{n+1}` different loop arguments, so the identity `RBM.Gauss.uker_driftF_eq` of T212 — which
rewrites `(U ∘ F)_a` and never bounds `F` itself — does not transfer.

The route taken here is deliberately **crude**.  `RBM.Decay.norm_couplingLen_le`,
`RBM.Decay.norm_primBil_sub_le` and `RBM.Decay.norm_eG_le` are the *sharp* estimates of Lemma
5.10: they carry the decay parameters `(A, ℓ, δ, Φ)` and need `LoopDecay` hypotheses, none of
which an envelope may assume.  What the envelope needs instead is the trivial counting bound
`‖W ∑_{k<l} ∑_{a,b} F · S^{(B)}_{ab} · G‖ ≤ W n² L · sup‖F‖ · sup‖G‖`, obtained from
`∑_b ‖S^{(B)}_{ab}‖ = 1` (`RBM.sum_norm_SB_row`); the two sup's are then

* `RBM.Gauss.norm_gloop_le_win` — the flow envelope `η_v^{-m}` of every loop of length `≤ m`,
  from T77's `RBM.Gauss.norm_gloop_le_det`, uniform on a window `[0, v]`, `v < 1`;
* `RBM.Gauss.exists_norm_Kval_le_win` — (2.59)/(2.60) uniform in the length, from
  `RBM.Gauss.exists_norm_Kval_le_upto` and `η_u ≤ W ℓ_u η_u`.

Note which quantifiers appear.  The envelope is a **deterministic** inequality: it holds for
every Hermitian matrix, hence for every sample point, with no exceptional set — this is the
`RBM.Gauss.jS_le_rpow` shape, not a stochastic inequality in disguise.  The time quantifier is
`u ∈ [s, v]` with `v < 1` and nothing more: `η_v` may be arbitrarily small, and the envelope is
*not* asserted for `u` outside the window (where `z_u` leaves the upper half plane and the
statement would be false).  `RBM.Gauss.driftF_envelope_critical` is the satisfiability witness:
the window `[0, 1 - N⁻¹]`, whose `η` tends to `0`, still has a finite envelope.

## Main results

* `RBM.Gauss.norm_primBil_le_crude`, `norm_couplingLen_le_crude` — (5.13)/(5.14) counted.
* `RBM.Gauss.norm_eGterm_le_crude` — (2.47) counted.
* `RBM.Gauss.norm_driftF_le_crude` — the three blocks of `RBM.DriftDef.driftF` together.
* `RBM.Gauss.exists_driftF_envelope` — **the envelope**: one constant for the whole window,
  every Hermitian matrix, every charge pattern and every loop argument.
* `RBM.Gauss.exists_driftF_envelope_at` — its one-time form, the shape
  `RBM.FastDecayFlow.hGd_Qop_driftF` consumes.
* `RBM.Gauss.driftF_envelope_critical` — the non-vacuity witness at critical scaling.
-/

open Finset Matrix

namespace RBM.Gauss

/-! ### The counting bound for one cut -/

section Crude

variable {L : ℕ} [NeZero L]

/-- **One cut `(k, l)`, counted.**  No decay is used: the `b`-sum is one row of `S^{(B)}`, which
has norm-sum `1` (`RBM.sum_norm_SB_row`), and the `a`-sum contributes `L`. -/
theorem norm_glueTerm_le_crude (hL : 3 ≤ L) (F G : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) (k l : ℕ) {MF MG : ℝ} (hMF : 0 ≤ MF) (_hMG : 0 ≤ MG)
    (hF : ∀ a : ZMod L, ‖F (I.cutGlueL k l a)‖ ≤ MF)
    (hG : ∀ b : ZMod L, ‖G (I.cutGlueR k l b)‖ ≤ MG) :
    ‖Decay.glueTerm L F G I k l‖ ≤ (L : ℝ) * (MF * MG) := by
  have key : ‖Decay.glueTerm L F G I k l‖
      ≤ ∑ a : ZMod L, ∑ b : ZMod L,
          ‖F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
  refine key.trans ?_
  calc ∑ a : ZMod L, ∑ b : ZMod L, ‖F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)‖
      ≤ ∑ _a : ZMod L, ∑ b : ZMod L, MF * MG * ‖SB L _a b‖ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_mul]
        calc ‖F (I.cutGlueL k l a)‖ * ‖SB L a b‖ * ‖G (I.cutGlueR k l b)‖
            ≤ MF * ‖SB L a b‖ * MG :=
              mul_le_mul (mul_le_mul_of_nonneg_right (hF a) (norm_nonneg _)) (hG b)
                (norm_nonneg _) (by positivity)
          _ = MF * MG * ‖SB L a b‖ := by ring
    _ = ∑ _a : ZMod L, MF * MG := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, sum_norm_SB_row hL a, mul_one]
    _ = (L : ℝ) * (MF * MG) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

omit [NeZero L] in
/-- The two cut loops of `(k, l)` are well formed, of length between `2` and `I.length`;
this packages the four side conditions the crude bounds need. -/
theorem cut_bounds_of_mem {F : LoopIdx (ZMod L) → ℂ} {I : LoopIdx (ZMod L)} (hI : I.WF)
    {MF : ℝ} (hF : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖F J‖ ≤ MF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (∀ a : ZMod L, ‖F (I.cutGlueL k l a)‖ ≤ MF) ∧
      (∀ b : ZMod L, ‖F (I.cutGlueR k l b)‖ ≤ MF) :=
  ⟨fun a => hF _ (LoopIdx.WF.cutGlueL a hI hk hkl hl)
      (LoopIdx.two_le_length_cutGlueL I a hk hkl hl)
      (LoopIdx.length_cutGlueL_le I a hk hkl hl),
   fun b => hF _ (LoopIdx.WF.cutGlueR b hI hk hkl hl)
      (LoopIdx.two_le_length_cutGlueR I b hk hkl hl)
      (LoopIdx.length_cutGlueR_le I b hk hkl hl)⟩

/-- **(5.13) counted**: `‖E^{(F × G)}_{σ,a}‖ ≤ W n² L · sup‖F‖ · sup‖G‖`.

This is `RBM.Gauss.norm_primRhs_le` with independent left and right factors. -/
theorem norm_primBil_le_crude (hL : 3 ≤ L) (W : ℕ) (F G : LoopIdx (ZMod L) → ℂ)
    {I : LoopIdx (ZMod L)} (hI : I.WF) {MF MG : ℝ} (hMF : 0 ≤ MF) (hMG : 0 ≤ MG)
    (hF : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖F J‖ ≤ MF)
    (hG : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖G J‖ ≤ MG) :
    ‖primBil L W F G I‖ ≤ (W : ℝ) * (I.length : ℝ) ^ 2 * ((L : ℝ) * (MF * MG)) := by
  have hrw : primBil L W F G I
      = (W : ℂ) * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length,
          Decay.glueTerm L F G I k l := rfl
  rw [hrw]
  refine Decay.norm_W_sum_le W I.length _ (by positivity) fun k hk l hl => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  exact norm_glueTerm_le_crude hL F G I k l hMF hMG
    (cut_bounds_of_mem hI hF hk.1 hl.1 hl.2).1
    (cut_bounds_of_mem hI hG hk.1 hl.1 hl.2).2

/-- **(5.14), left half, counted.** -/
theorem norm_primBilLen_le_crude (hL : 3 ≤ L) (W lK : ℕ) (F G : LoopIdx (ZMod L) → ℂ)
    {I : LoopIdx (ZMod L)} (hI : I.WF) {MF MG : ℝ} (hMF : 0 ≤ MF) (hMG : 0 ≤ MG)
    (hF : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖F J‖ ≤ MF)
    (hG : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖G J‖ ≤ MG) :
    ‖primBilLen L W lK F G I‖ ≤ (W : ℝ) * (I.length : ℝ) ^ 2 * ((L : ℝ) * (MF * MG)) := by
  have hT : (0 : ℝ) ≤ (L : ℝ) * (MF * MG) := by positivity
  have hrw : primBilLen L W lK F G I
      = (W : ℂ) * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length,
          ∑ a : ZMod L, ∑ b : ZMod L,
            (if (I.cutGlueL k l a).length = lK then
              F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b) else 0) := rfl
  rw [hrw]
  refine Decay.norm_W_sum_le W I.length _ hT fun k hk l hl => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  rw [Decay.primBilLen_summand L F G I hk.1 hl.1 hl.2 lK]
  split_ifs with h
  · exact norm_glueTerm_le_crude hL F G I k l hMF hMG
      (cut_bounds_of_mem hI hF hk.1 hl.1 hl.2).1
      (cut_bounds_of_mem hI hG hk.1 hl.1 hl.2).2
  · simpa using hT

/-- **(5.14), right half, counted.** -/
theorem norm_primBilLenR_le_crude (hL : 3 ≤ L) (W lK : ℕ) (F G : LoopIdx (ZMod L) → ℂ)
    {I : LoopIdx (ZMod L)} (hI : I.WF) {MF MG : ℝ} (hMF : 0 ≤ MF) (hMG : 0 ≤ MG)
    (hF : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖F J‖ ≤ MF)
    (hG : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖G J‖ ≤ MG) :
    ‖Decay.primBilLenR L W lK F G I‖
      ≤ (W : ℝ) * (I.length : ℝ) ^ 2 * ((L : ℝ) * (MF * MG)) := by
  have hT : (0 : ℝ) ≤ (L : ℝ) * (MF * MG) := by positivity
  have hrw : Decay.primBilLenR L W lK F G I
      = (W : ℂ) * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length,
          ∑ a : ZMod L, ∑ b : ZMod L,
            (if (I.cutGlueR k l b).length = lK then
              F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b) else 0) := rfl
  rw [hrw]
  refine Decay.norm_W_sum_le W I.length _ hT fun k hk l hl => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  rw [Decay.primBilLenR_summand L F G I hk.1 hl.1 hl.2 lK]
  split_ifs with h
  · exact norm_glueTerm_le_crude hL F G I k l hMF hMG
      (cut_bounds_of_mem hI hF hk.1 hl.1 hl.2).1
      (cut_bounds_of_mem hI hG hk.1 hl.1 hl.2).2
  · simpa using hT

/-- **(5.14) counted**, both orientations. -/
theorem norm_couplingLen_le_crude (hL : 3 ≤ L) (W lK : ℕ) (K D : LoopIdx (ZMod L) → ℂ)
    {I : LoopIdx (ZMod L)} (hI : I.WF) {MK MD : ℝ} (hMK : 0 ≤ MK) (hMD : 0 ≤ MD)
    (hK : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K J‖ ≤ MK)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖D J‖ ≤ MD) :
    ‖Decay.couplingLen L W lK K D I‖
      ≤ 2 * ((W : ℝ) * (I.length : ℝ) ^ 2 * ((L : ℝ) * (MK * MD))) := by
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_primBilLen_le_crude hL W lK K D hI hMK hMD hK hD
  have h2 := norm_primBilLenR_le_crude hL W lK D K hI hMD hMK hD hK
  have h2' : ‖Decay.primBilLenR L W lK D K I‖
      ≤ (W : ℝ) * (I.length : ℝ) ^ 2 * ((L : ℝ) * (MK * MD)) := by
    refine h2.trans (le_of_eq ?_); ring
  linarith

end Crude

/-! ### The two sup's: the loop envelope and (2.59) on a window -/

section Sups

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **The deterministic loop envelope on a window.**  Every loop of length `1 ≤ m' ≤ m` of every
Hermitian matrix satisfies `|L_{u,σ,a}| ≤ η_v^{-m}` for `0 ≤ u ≤ v < 1`.

Two crudenesses on top of T77's `RBM.Gauss.norm_gloop_le_det`: the `W^{-m'+1}` is discarded
(`W ≥ 1`) and the length-dependent exponent is raised to `m` (`η_v ≤ 1`).  What is kept is that
the bound is uniform over the window — `η` is monotone decreasing in `u`. -/
theorem norm_gloop_le_win {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hM : M.IsHermitian)
    {E : ℝ} (hE : |E| < 2) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1) (m : ℕ)
    (J : LoopIdx (ZMod L)) (hJ : J.WF) (h1 : 1 ≤ J.length) (hm : J.length ≤ m) :
    ‖gloop L W M (zt E u) J‖ ≤ (etaT E v)⁻¹ ^ m := by
  have hu1 : u < 1 := lt_of_le_of_lt huv hv1
  have hv0 : (0 : ℝ) ≤ v := hu0.trans huv
  have hηv : 0 < etaT E v := etaT_pos_of_lt_one hE hv1
  have hinv1 : (1 : ℝ) ≤ (etaT E v)⁻¹ := one_le_inv_etaT hE hv0 hv1
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one hE hu1
  have hηu' : (0 : ℝ) ≤ (etaT E u)⁻¹ := inv_nonneg.2 hηu.le
  have hmono : (etaT E u)⁻¹ ≤ (etaT E v)⁻¹ := inv_anti₀ hηv (etaT_le_of_le hE huv)
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := by
    have : 0 < W := Nat.pos_of_ne_zero (NeZero.ne W)
    exact_mod_cast this
  have hd := norm_gloop_le_det hM hE hu1 J hJ h1
  refine hd.trans ?_
  have hWp : ((W : ℝ))⁻¹ ^ (J.a.length - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
  calc (etaT E u)⁻¹ ^ J.a.length * ((W : ℝ))⁻¹ ^ (J.a.length - 1)
      ≤ (etaT E u)⁻¹ ^ J.a.length * 1 := by
        exact mul_le_mul_of_nonneg_left hWp (pow_nonneg hηu' _)
    _ = (etaT E u)⁻¹ ^ J.a.length := mul_one _
    _ ≤ (etaT E v)⁻¹ ^ J.a.length := by
        exact pow_le_pow_left₀ hηu' hmono _
    _ ≤ (etaT E v)⁻¹ ^ m := pow_le_pow_right₀ hinv1 hm

end Sups

section KvalWin

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(2.59)/(2.60) as a window envelope.**  One constant, every length `2 … m`, every time of
`[0, v]` with `v < 1`: `|K_{u,σ,a}| ≤ C_K η_v^{-m}`.

`RBM.Gauss.exists_norm_Kval_le_upto` gives the sharp `(W ℓ_u η_u)^{-(len-1)}`; here that scale
is thrown away down to `η_v⁻¹` (using `W ≥ 1`, `ℓ_u ≥ 1` and the monotonicity of `η`), which is
all an envelope may ask for. -/
theorem exists_norm_Kval_le_win (B : Band Ω) {E : ℝ} (hE : |E| < 2) (m : ℕ) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (N : ℕ) (u v : ℝ), 0 ≤ u → u ≤ v → v < 1 →
      ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ m →
        ‖B.Kval E N u J‖ ≤ CK * (etaT E v)⁻¹ ^ m := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_Kval_le_upto B hE m
  refine ⟨C, hC0, fun N u v hu0 huv hv1 J hJ hJ2 hJm => ?_⟩
  have hu1 : u < 1 := lt_of_le_of_lt huv hv1
  have hv0 : (0 : ℝ) ≤ v := hu0.trans huv
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one hE hu1
  have hηv : 0 < etaT E v := etaT_pos_of_lt_one hE hv1
  have hinv1 : (1 : ℝ) ≤ (etaT E v)⁻¹ := one_le_inv_etaT hE hv0 hv1
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hell : (1 : ℝ) ≤ B.ell N u := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
  -- `η_u ≤ W ℓ_u η_u`
  have hge : etaT E u ≤ B.scale E N u := by
    have h : (1 : ℝ) * 1 * etaT E u ≤ (B.W N : ℝ) * B.ell N u * etaT E u :=
      mul_le_mul_of_nonneg_right (mul_le_mul hW1 hell zero_le_one (by linarith)) hηu.le
    simpa [Band.scale] using h
  have hinv : (B.scale E N u)⁻¹ ≤ (etaT E v)⁻¹ :=
    le_trans (inv_anti₀ hηu hge) (inv_anti₀ hηv (etaT_le_of_le hE huv))
  have hscale0 : (0 : ℝ) ≤ (B.scale E N u)⁻¹ := inv_nonneg.2 (B.scale_pos' hE N hu0 hu1).le
  refine (hC N u hu0 hu1 J hJ hJ2 hJm).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC0
  calc (B.scale E N u)⁻¹ ^ (J.length - 1) ≤ (etaT E v)⁻¹ ^ (J.length - 1) :=
        pow_le_pow_left₀ hscale0 hinv _
    _ ≤ (etaT E v)⁻¹ ^ m := pow_le_pow_right₀ hinv1 (by omega)

end KvalWin

/-! ### (2.47) counted -/

section EGCrude

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **(2.47) counted**: `‖Ẽ_{σ,a}‖ ≤ W n L · (M₁ + 1) · M₂` where `M₁` bounds the one-loop
`|L_{(s),(a)}|`, the `+1` is `|m(s)| ≤ 1`, and `M₂` bounds the `(n+1)`-loop the cut-and-glue
produces (`RBM.LoopIdx.length_cutGlue`).

The one-loop factor is `⟨(G(s) - m(s))E_a⟩ = (L - K)_{(s),(a)}`
(`RBM.DriftDef.trace_sub_eq_gloop_sub_Kgen`, `RBM.Kgen_one`). -/
theorem norm_eGterm_le_crude (hL : 3 ≤ L)
    {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {E : ℝ} (hE : |E| < 2) {u : ℝ}
    {I : LoopIdx (ZMod L)} (_hI : I.WF) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (_hM₂ : 0 ≤ M₂)
    (h1 : ∀ (s : Bool) (a : ZMod L), ‖gloop L W M (zt E u) ⟨[s], [a]⟩‖ ≤ M₁)
    (h2 : ∀ (k : ℕ), 1 ≤ k → k ≤ I.length → ∀ b : ZMod L,
      ‖gloop L W M (zt E u) (I.cutGlue k b)‖ ≤ M₂) :
    ‖eGterm L W (mSigma E) M (zt E u) I‖
      ≤ (W : ℝ) * (I.length : ℝ) * ((L : ℝ) * ((M₁ + 1) * M₂)) := by
  have hrw : eGterm L W (mSigma E) M (zt E u) I
      = (W : ℂ) * ∑ k ∈ Icc 1 I.length, ∑ a : ZMod L, ∑ b : ZMod L,
          Matrix.trace ((Gsig M (zt E u) (I.σ.getD (k - 1) true)
              - mSigma E (I.σ.getD (k - 1) true) •
                (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
            * Eblk L W a) * SB L a b * gloop L W M (zt E u) (I.cutGlue k b) := rfl
  rw [hrw]
  refine Decay.norm_W_sum_le' W I.length _ fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  set s : Bool := I.σ.getD (k - 1) true with hs
  -- the one-loop factor
  have hone : ∀ a : ZMod L,
      ‖Matrix.trace ((Gsig M (zt E u) s
          - mSigma E s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W a)‖
        ≤ M₁ + 1 := by
    intro a
    rw [DriftDef.trace_sub_eq_gloop_sub_Kgen (mSigma E) u M (zt E u) s a, Pi.sub_apply,
      Kgen_one W (mSigma E) u s a]
    exact (norm_sub_le _ _).trans (add_le_add (h1 s a) (norm_mSigma_le_one hE s))
  have hglue : ∀ b : ZMod L, ‖gloop L W M (zt E u) (I.cutGlue k b)‖ ≤ M₂ :=
    h2 k hk.1 hk.2
  calc ‖∑ a : ZMod L, ∑ b : ZMod L,
          Matrix.trace ((Gsig M (zt E u) s
              - mSigma E s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
            * Eblk L W a) * SB L a b * gloop L W M (zt E u) (I.cutGlue k b)‖
      ≤ ∑ a : ZMod L, ∑ b : ZMod L,
          ‖Matrix.trace ((Gsig M (zt E u) s
              - mSigma E s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
            * Eblk L W a) * SB L a b * gloop L W M (zt E u) (I.cutGlue k b)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a : ZMod L, ∑ b : ZMod L, (M₁ + 1) * M₂ * ‖SB L _a b‖ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_mul]
        calc ‖Matrix.trace ((Gsig M (zt E u) s
                - mSigma E s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
              * Eblk L W a)‖ * ‖SB L a b‖
              * ‖gloop L W M (zt E u) (I.cutGlue k b)‖
            ≤ (M₁ + 1) * ‖SB L a b‖ * M₂ :=
              mul_le_mul (mul_le_mul_of_nonneg_right (hone a) (norm_nonneg _)) (hglue b)
                (norm_nonneg _) (by positivity)
          _ = (M₁ + 1) * M₂ * ‖SB L a b‖ := by ring
    _ = ∑ _a : ZMod L, (M₁ + 1) * M₂ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, sum_norm_SB_row hL a, mul_one]
    _ = (L : ℝ) * ((M₁ + 1) * M₂) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

end EGCrude

/-! ### The drift, counted, and the envelope -/

section Envelope

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The three blocks of `RBM.DriftDef.driftF`, counted.**

`MG` bounds every loop of length `≤ n + 3`, `MK` every `K` of length `2 … n + 2`, and
`MD := MG + MK` therefore bounds `L - K` there. -/
theorem norm_driftF_le_crude (B : Band Ω) (E : ℝ) (N : ℕ) (hE : |E| < 2) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (B.L N) (n + 2)) {MG MK : ℝ} (hMG : 0 ≤ MG) (hMK : 0 ≤ MK)
    (hG : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 1 ≤ J.length → J.length ≤ n + 3 →
      ‖gloop (B.L N) (B.W N) M (zt E u) J‖ ≤ MG)
    (hK : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ n + 2 →
      ‖B.Kval E N u J‖ ≤ MK) :
    ‖DriftDef.driftF B E N u M σ a‖
      ≤ (B.W N : ℝ) * ((n : ℝ) + 2) * ((B.L N : ℝ) * ((MG + 1) * MG))
        + ((n : ℝ) + 2) * (2 * ((B.W N : ℝ) * ((n : ℝ) + 2) ^ 2
            * ((B.L N : ℝ) * (MK * (MG + MK)))))
        + (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2
            * ((B.L N : ℝ) * ((MG + MK) * (MG + MK))) := by
  classical
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  set I : LoopIdx (ZMod (B.L N)) := LoopData.idx (σ, a) with hIdef
  have hIWF : I.WF := LoopData.idx_wf (σ, a)
  have hIlen : I.length = n + 2 := LoopData.idx_length (σ, a)
  set D : LoopIdx (ZMod (B.L N)) → ℂ :=
    gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u with hDdef
  have hMD : (0 : ℝ) ≤ MG + MK := by linarith
  have hDb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖D J‖ ≤ MG + MK := by
    intro J hJ hJ2 hJle
    rw [hIlen] at hJle
    exact (norm_sub_le _ _).trans
      (add_le_add (hG J hJ (by omega) (by omega)) (hK J hJ hJ2 hJle))
  have hKb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖B.Kval E N u J‖ ≤ MK := by
    intro J hJ hJ2 hJle
    rw [hIlen] at hJle
    exact hK J hJ hJ2 hJle
  -- block 1: (2.47)
  have hEG : ‖eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) I‖
      ≤ (B.W N : ℝ) * ((n : ℝ) + 2) * ((B.L N : ℝ) * ((MG + 1) * MG)) := by
    have h := norm_eGterm_le_crude (L := B.L N) (W := B.W N) hL3 (M := M) hE (u := u)
      hIWF hMG hMG
      (fun s b => hG _ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length]) (by simp [LoopIdx.length]))
      (fun k hk1 hk2 b => hG _ (LoopIdx.WF.cutGlue b hIWF hk1 hk2)
        (by have := LoopIdx.length_cutGlue I b hk2; omega)
        (by have := LoopIdx.length_cutGlue I b hk2; omega))
    refine h.trans (le_of_eq ?_)
    rw [hIlen]
    push_cast
    ring
  -- block 2: the coupling sum over `l_K ≥ 3`
  have hcpl : ∀ lK : ℕ, ‖Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D I‖
      ≤ 2 * ((B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * ((B.L N : ℝ) * (MK * (MG + MK)))) := by
    intro lK
    have h := norm_couplingLen_le_crude hL3 (B.W N) lK (B.Kval E N u) D hIWF hMK hMD hKb hDb
    refine h.trans (le_of_eq ?_)
    rw [hIlen]
    push_cast
    ring
  have hsum : ‖∑ lK ∈ Finset.Icc 3 (n + 2),
        Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D I‖
      ≤ ((n : ℝ) + 2) * (2 * ((B.W N : ℝ) * ((n : ℝ) + 2) ^ 2
          * ((B.L N : ℝ) * (MK * (MG + MK))))) := by
    set T : ℝ := 2 * ((B.W N : ℝ) * ((n : ℝ) + 2) ^ 2
      * ((B.L N : ℝ) * (MK * (MG + MK)))) with hT
    have hT0 : 0 ≤ T := by rw [hT]; positivity
    calc ‖∑ lK ∈ Finset.Icc 3 (n + 2),
            Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D I‖
        ≤ ∑ lK ∈ Finset.Icc 3 (n + 2), T :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun lK _ => hcpl lK)
      _ = ((n + 2 + 1 - 3 : ℕ) : ℝ) * T := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      _ ≤ ((n : ℝ) + 2) * T := by
          refine mul_le_mul_of_nonneg_right ?_ hT0
          push_cast
          linarith
  -- block 3: (5.13)
  have hquad : ‖primBil (B.L N) (B.W N) D D I‖
      ≤ (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * ((B.L N : ℝ) * ((MG + MK) * (MG + MK))) := by
    have h := norm_primBil_le_crude hL3 (B.W N) D D hIWF hMD hMD hDb hDb
    refine h.trans (le_of_eq ?_)
    rw [hIlen]
    push_cast
    ring
  have hsplit : ‖DriftDef.driftF B E N u M σ a‖
      ≤ ‖eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) I‖
        + ‖∑ lK ∈ Finset.Icc 3 (n + 2),
            Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D I‖
        + ‖primBil (B.L N) (B.W N) D D I‖ := by
    have e : DriftDef.driftF B E N u M σ a
        = eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) I
          + (∑ lK ∈ Finset.Icc 3 (n + 2),
              Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D I)
          + primBil (B.L N) (B.W N) D D I := rfl
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  refine hsplit.trans ?_
  exact add_le_add (add_le_add hEG hsum) hquad

/-- **The envelope of the drift `F` of (5.15), pointwise and deterministic.**

One constant for the whole window `[s, v]`, `0 ≤ s`, `v < 1`, for **every** Hermitian matrix
(hence every sample point, with no exceptional set), every charge pattern and every loop
argument.  This is what `RBM.Gauss.exists_bdd_uker_Qop_driftF` asks for as `hFb` and what
`RBM.FastDecayFlow.hGd_Qop_driftF` asks for as `hAM`.

The window is not decoration: the bound is `η_v^{-O(n)}`, and outside `[0, 1)` there is no
bound at all. -/
theorem exists_driftF_envelope (B : Band Ω) {E : ℝ} (hE : |E| < 2) (n N : ℕ) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) :
    ∃ cF : ℝ, 0 ≤ cF ∧ ∀ u ∈ Set.Icc s v, ∀ M : Matrix (B.Idx N) (B.Idx N) ℂ, M.IsHermitian →
      ∀ (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) (n + 2)),
        ‖DriftDef.driftF B E N u M σ b‖ ≤ cF := by
  classical
  obtain ⟨CK, hCK0, hCK⟩ := exists_norm_Kval_le_win B hE (n + 2)
  set MG : ℝ := (etaT E v)⁻¹ ^ (n + 3) with hMGdef
  set MK : ℝ := CK * (etaT E v)⁻¹ ^ (n + 2) with hMKdef
  have hηv : 0 < etaT E v := etaT_pos_of_lt_one hE hv1
  have hMG0 : 0 ≤ MG := by rw [hMGdef]; positivity
  have hMK0 : 0 ≤ MK := by rw [hMKdef]; positivity
  refine ⟨(B.W N : ℝ) * ((n : ℝ) + 2) * ((B.L N : ℝ) * ((MG + 1) * MG))
      + ((n : ℝ) + 2) * (2 * ((B.W N : ℝ) * ((n : ℝ) + 2) ^ 2
          * ((B.L N : ℝ) * (MK * (MG + MK)))))
      + (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2
          * ((B.L N : ℝ) * ((MG + MK) * (MG + MK))), by positivity, ?_⟩
  intro u hu M hM σ b
  have hu0 : (0 : ℝ) ≤ u := hs0.trans hu.1
  refine norm_driftF_le_crude B E N hE u M σ b hMG0 hMK0 ?_ ?_
  · intro J hJ hJ1 hJle
    exact norm_gloop_le_win hM hE hu0 hu.2 hv1 (n + 3) J hJ hJ1 hJle
  · intro J hJ hJ2 hJle
    exact hCK N u v hu0 hu.2 hv1 J hJ hJ2 hJle

/-- **The envelope at a single time**, the shape `RBM.FastDecayFlow.hGd_Qop_driftF` consumes:
its `hAM` quantifies over `ω ∈ Ξ` at one `u`, and the envelope covers every `ω` at once. -/
theorem exists_driftF_envelope_at (B : Band Ω) {E : ℝ} (hE : |E| < 2) (n N : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ cF : ℝ, 0 ≤ cF ∧ ∀ M : Matrix (B.Idx N) (B.Idx N) ℂ, M.IsHermitian →
      ∀ (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) (n + 2)),
        ‖DriftDef.driftF B E N u M σ b‖ ≤ cF := by
  obtain ⟨cF, hcF0, hcF⟩ := exists_driftF_envelope B hE n N (s := u) (v := u) hu0 hu1
  exact ⟨cF, hcF0, fun M hM σ b => hcF u ⟨le_rfl, le_rfl⟩ M hM σ b⟩

/-- **Non-vacuity at critical scaling.**  The envelope is not an empty statement obtained by
letting the window collapse or `η` stay bounded away from `0`: on `[0, 1 - (N+1)⁻¹]`, whose
right endpoint tends to `1` and whose `η_v = (1 - v) Im m^{(E)}` tends to `0`, the envelope
still holds with a finite constant, for every `N` and every loop length.

`Set.Icc 0 (1 - (N+1)⁻¹)` is nondegenerate for every `N` (it contains `0` and its right
endpoint is `> 0` for `N ≥ 1`), and the matrix is arbitrary Hermitian — in particular `M = 0`
(the sample point `ω = 0` of the Gaussian model) is covered, which is the degenerate point the
project's satisfiability discipline asks about. -/
theorem driftF_envelope_critical (B : Band Ω) {E : ℝ} (hE : |E| < 2) (n N : ℕ) :
    ∃ cF : ℝ, 0 ≤ cF ∧ ∀ u ∈ Set.Icc (0 : ℝ) (1 - ((N : ℝ) + 1)⁻¹),
      ∀ M : Matrix (B.Idx N) (B.Idx N) ℂ, M.IsHermitian →
        ∀ (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) (n + 2)),
          ‖DriftDef.driftF B E N u M σ b‖ ≤ cF := by
  have hpos : (0 : ℝ) < ((N : ℝ) + 1)⁻¹ := by positivity
  exact exists_driftF_envelope B hE n N le_rfl (by linarith)

/-- The witness really is attained at a matrix: `M = 0` (i.e. `H = 0`, the sample point `ω = 0`)
is Hermitian, so the envelope of `driftF_envelope_critical` has content at it. -/
theorem driftF_envelope_critical_zero (B : Band Ω) {E : ℝ} (hE : |E| < 2) (n N : ℕ) :
    ∃ cF : ℝ, 0 ≤ cF ∧ ∀ u ∈ Set.Icc (0 : ℝ) (1 - ((N : ℝ) + 1)⁻¹),
      ∀ (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) (n + 2)),
        ‖DriftDef.driftF B E N u 0 σ b‖ ≤ cF := by
  obtain ⟨cF, hcF0, hcF⟩ := driftF_envelope_critical B hE n N
  exact ⟨cF, hcF0, fun u hu σ b => hcF u hu 0 (Matrix.isHermitian_zero) σ b⟩

end Envelope

end RBM.Gauss
