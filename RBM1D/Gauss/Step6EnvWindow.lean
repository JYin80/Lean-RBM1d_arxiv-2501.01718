/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6Sample
import RBM1D.Hierarchy.Step45
import RBM1D.Hierarchy.LKDecayQuant

/-!
# Step 6's envelope hypotheses, quantified over the window

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8, (5.126)–(5.136), and §2.7, (2.71), (2.80).

A single real number `Env N` dominating `‖E^{(G)}(L-K, L)_{v,σ,a}(ω)‖` for **every** `v : ℝ`
does not exist — at `E = 0`, `ω = 0`, `v = 1 - w` the value is `2(w⁻¹-1)w^{-3}/W`, unbounded as
`w ↓ 0` — so Step 6's envelope has to be read **only at window times** `v ∈ [s_N, t_N]`.  This
file builds that window envelope and the Gaussian producers of the window slots.

## What is here

* §1 — two crude counting bounds, `RBM.norm_eG_le_crude` and `RBM.norm_primBil_le_crude`:
  `|E^{(G)}| ≤ W n L M_X M_Y` and `|primBil| ≤ W n² L M M'`.  Both are the trivial triangle
  inequality with `∑_b ‖S^{(B)}_{ab}‖ = 1` (`RBM.sum_norm_SB_apply_row`); they are the shape in
  which the window envelope is checked.
* §3 — **the envelope exists on the window**: `RBM.exists_env_window` builds it explicitly, for
  an arbitrary `RBM.Sample`, out of `RBM.envFloor E t N = max(1, η_{t_N}^{-1})`, the
  deterministic loop bound `RBM.norm_gloop_flow_le_envFloor` and (2.59)
  (`RBM.exists_norm_Kval_le_envFloor`).  The only side condition is
  `hη : ∀ᶠ N, N^{-c} ≤ η_{t_N}`, and it is used **only** for the polynomial bound
  `Env N ≤ N^{Kenv}`, not for the envelope itself.
* §4b — the same envelope at a single interior time: `RBM.exists_norm_drift_le_at`.
* §6 — the Gaussian producers for the window slots: `RBM.Gauss.hmeasQ_window`,
  `RBM.Gauss.hmeasG_window`, `RBM.Gauss.hmeasLK_window`, `RBM.Gauss.hintL1_window`, and (from
  §4b) `RBM.Gauss.hintQ_gauss`, `RBM.Gauss.hintG_gauss`.
* §9 — `RBM.cor35Rate_mul_ell_mul`, the rate of Corollary 3.5 at the radius `ℓ_v N^τ`.
* §10 — `RBM.lkPath_nil`: `(L-K)` at loop length `0`.
* §11 — `RBM.integral_lkPath_eq_lkT`: `∫ (L - K) = E L - K`.

No hypothesis of this file is an `ω`-quantified pointwise inequality, and the envelope, which
does not exist in its `ℝ`-quantified form, is discharged here on the window.
-/

open MeasureTheory Filter

namespace RBM

/-! ### §1  Crude counting bounds for the two drift tensors

These are the `O(1)`-free versions of `RBM.Decay.norm_eG_le` and
`RBM.Decay.norm_primBil_sub_le`: no decay, no scale, just the triangle inequality and the fact
that each row of `S^{(B)}` has total mass `1`.  They are what turns a *pointwise* loop envelope
into an envelope for the drift tensors. -/

section Crude

open Finset

variable {L : ℕ} [NeZero L]

/-- **A crude bound for `E^{(G)}`**: `|E^{(G)}_{σ,a}| ≤ W n L M_X M_Y`, where `M_X` bounds the
`1`-loops of the left argument and `M_Y` the `(n+1)`-loops of the right one.  The `L` is the
`a`-sum; the `b`-sum is free because `∑_b ‖S^{(B)}_{ab}‖ = 1`. -/
theorem norm_eG_le_crude (hL : 3 ≤ L) (W : ℕ) {X Y : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {MX MY : ℝ} (hMX0 : 0 ≤ MX)
    (hX : ∀ (b : Bool) (a : ZMod L), ‖X ⟨[b], [a]⟩‖ ≤ MX)
    (hY : ∀ J : LoopIdx (ZMod L), J.WF → J.length = I.length + 1 → ‖Y J‖ ≤ MY) :
    ‖Decay.eG L W X Y I‖ ≤ (W : ℝ) * I.length * ((L : ℝ) * (MX * MY)) := by
  rw [Decay.eG]
  refine Decay.norm_W_sum_le' W I.length _ fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  have hYk : ∀ b : ZMod L, ‖Y (I.cutGlue k b)‖ ≤ MY := fun b =>
    hY _ (hI.cutGlue b hk.1 hk.2) (LoopIdx.length_cutGlue I b hk.2)
  calc ‖∑ a : ZMod L, ∑ b : ZMod L,
        X ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b * Y (I.cutGlue k b)‖
      ≤ ∑ a : ZMod L, ∑ b : ZMod L,
        ‖X ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b * Y (I.cutGlue k b)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a : ZMod L, ∑ b : ZMod L, MX * MY * ‖SB L _a b‖ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_mul]
        calc ‖X ⟨[I.σ.getD (k - 1) true], [a]⟩‖ * ‖SB L a b‖ * ‖Y (I.cutGlue k b)‖
            ≤ MX * ‖SB L a b‖ * MY := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right (hX _ a) (norm_nonneg _))
                (hYk b) (norm_nonneg _) (by positivity)
          _ = MX * MY * ‖SB L a b‖ := by ring
    _ = (L : ℝ) * (MX * MY) := by
        have hrow : ∀ a : ZMod L, (∑ b : ZMod L, MX * MY * ‖SB L a b‖) = MX * MY := by
          intro a
          rw [← Finset.mul_sum, sum_norm_SB_apply_row L hL a, mul_one]
        rw [Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_const, Finset.card_univ,
          ZMod.card, nsmul_eq_mul]

/-- **A crude bound for `primBil`**: `|primBil(K, K')_{σ,a}| ≤ W n² L M M'`, where `M`, `M'`
bound the arguments on well-formed loops of length between `2` and `n`.  Both glued loops have
their length in that range (`RBM.LoopIdx.two_le_length_cutGlueL`,
`RBM.LoopIdx.length_cutGlueL_le` and the right-hand pair). -/
theorem norm_primBil_le_crude (hL : 3 ≤ L) (W : ℕ) {K K' : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {M M' : ℝ} (hM0 : 0 ≤ M) (hM'0 : 0 ≤ M')
    (hK : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K J‖ ≤ M)
    (hK' : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K' J‖ ≤ M') :
    ‖primBil L W K K' I‖ ≤ (W : ℝ) * I.length ^ 2 * ((L : ℝ) * (M * M')) := by
  rw [primBil]
  refine Decay.norm_W_sum_le W I.length _ (by positivity) fun k hk l hl => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have hKL : ∀ a : ZMod L, ‖K (I.cutGlueL k l a)‖ ≤ M := fun a =>
    hK _ (LoopIdx.WF.cutGlueL a hI hk.1 hl.1 hl.2)
      (LoopIdx.two_le_length_cutGlueL I a hk.1 hl.1 hl.2)
      (LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2)
  have hKR : ∀ b : ZMod L, ‖K' (I.cutGlueR k l b)‖ ≤ M' := fun b =>
    hK' _ (LoopIdx.WF.cutGlueR b hI hk.1 hl.1 hl.2)
      (LoopIdx.two_le_length_cutGlueR I b hk.1 hl.1 hl.2)
      (LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2)
  calc ‖∑ a : ZMod L, ∑ b : ZMod L,
        K (I.cutGlueL k l a) * SB L a b * K' (I.cutGlueR k l b)‖
      ≤ ∑ a : ZMod L, ∑ b : ZMod L,
        ‖K (I.cutGlueL k l a) * SB L a b * K' (I.cutGlueR k l b)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a : ZMod L, ∑ b : ZMod L, M * M' * ‖SB L _a b‖ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_mul]
        calc ‖K (I.cutGlueL k l a)‖ * ‖SB L a b‖ * ‖K' (I.cutGlueR k l b)‖
            ≤ M * ‖SB L a b‖ * M' := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right (hKL a) (norm_nonneg _))
                (hKR b) (norm_nonneg _) (by positivity)
          _ = M * M' * ‖SB L a b‖ := by ring
    _ = (L : ℝ) * (M * M') := by
        have hrow : ∀ a : ZMod L, (∑ b : ZMod L, M * M' * ‖SB L a b‖) = M * M' := by
          intro a
          rw [← Finset.mul_sum, sum_norm_SB_apply_row L hL a, mul_one]
        rw [Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_const, Finset.card_univ,
          ZMod.card, nsmul_eq_mul]

end Crude


section Window

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

end Window

/-! ### §3  The window envelope, and that it exists

`R_N = max(1, η_{t_N}^{-1})` is the only scale a loop of length `≤ 3` can reach on the window:
`|L_J| ≤ R_N^{|J|}` for every `ω` (`RBM.Gauss.norm_gloop_le_det`, which is deterministic), and
`|K_J| ≤ C R_N^3` by (2.59).  So `|L - K| ≤ (1+C) R_N^3`, and the two drift tensors, being
`W · (at most 4 cuts) · (an `S^{(B)}`-row, mass `1`) · (two such loops)`, are bounded by
`4 W L ((1+C) R_N^3)^2`.  Off the window this fails — and not by a constant. -/

section EnvWindow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `η` is antitone in the time: `η_t ≤ η_v` for `v ≤ t`. -/
theorem etaT_le_of_le_window {E : ℝ} (hE : |E| < 2) {u w : ℝ} (huw : u ≤ w) :
    etaT E w ≤ etaT E u := by
  show (1 - w) * (mE E).im ≤ (1 - u) * (mE E).im
  exact mul_le_mul_of_nonneg_right (by linarith) (mE_im_pos hE).le

/-- The window floor `R_N = max(1, η_{t_N}^{-1})`. -/
noncomputable def envFloor (E : ℝ) (t : ℕ → ℝ) (N : ℕ) : ℝ :=
  max 1 (etaT E (t N))⁻¹

theorem one_le_envFloor (E : ℝ) (t : ℕ → ℝ) (N : ℕ) :
    1 ≤ envFloor E t N := le_max_left _ _

theorem envFloor_nonneg (E : ℝ) (t : ℕ → ℝ) (N : ℕ) :
    0 ≤ envFloor E t N := le_trans zero_le_one (one_le_envFloor E t N)

/-- Every loop of length `1 ≤ n ≤ 3` of the flow is bounded by `R_N^3` on the window. -/
theorem norm_gloop_flow_le_envFloor (X : Sample B) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (ht1 : ∀ N, t N < 1) (N : ℕ) (v : TimeIcc s t N) (ω : Ω)
    (J : LoopIdx (ZMod (B.L N))) (hJ : J.WF) (hn : 1 ≤ J.length) (h3 : J.length ≤ 3) :
    ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)) J‖ ≤ envFloor E t N ^ 3 := by
  have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
  have hηt : 0 < etaT E (t N) := etaT_pos hE (ht1 N)
  have hηv : 0 < etaT E (v : ℝ) := etaT_pos hE hv1
  have hmono : etaT E (t N) ≤ etaT E (v : ℝ) := etaT_le_of_le_window hE v.2.2
  have hR : (etaT E (v : ℝ))⁻¹ ≤ envFloor E t N :=
    le_trans (inv_anti₀ hηt hmono) (le_max_right _ _)
  have hR0 : 0 ≤ (etaT E (v : ℝ))⁻¹ := inv_nonneg.2 hηv.le
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hbase := Gauss.norm_gloop_le_det (X.hermitian N (v : ℝ) ω) hE hv1 J hJ hn
  refine hbase.trans ?_
  have hWle : ((B.W N : ℝ))⁻¹ ^ (J.length - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
  have h1 : (etaT E (v : ℝ))⁻¹ ^ J.length ≤ envFloor E t N ^ J.length :=
    pow_le_pow_left₀ hR0 hR _
  have h2 : envFloor E t N ^ J.length ≤ envFloor E t N ^ 3 :=
    pow_le_pow_right₀ (one_le_envFloor E t N) h3
  calc (etaT E (v : ℝ))⁻¹ ^ J.length * ((B.W N : ℝ))⁻¹ ^ (J.length - 1)
      ≤ (etaT E (v : ℝ))⁻¹ ^ J.length * 1 :=
        mul_le_mul_of_nonneg_left hWle (by positivity)
    _ = (etaT E (v : ℝ))⁻¹ ^ J.length := mul_one _
    _ ≤ envFloor E t N ^ 3 := h1.trans h2

/-- `K` at loop lengths `1, 2, 3` is bounded by `C R_N^3` on the window, with one constant. -/
theorem exists_norm_Kval_le_envFloor (B : Band Ω) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (v : TimeIcc s t N) (J : LoopIdx (ZMod (B.L N))),
      J.WF → 1 ≤ J.length → J.length ≤ 3 →
        ‖B.Kval E N (v : ℝ) J‖ ≤ C * envFloor E t N ^ 3 := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  obtain ⟨C1, hC10, hC1⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 1) le_rfl
  obtain ⟨C2, hC20, hC2⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 2) (by norm_num)
  obtain ⟨C3, hC30, hC3⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 3) (by norm_num)
  refine ⟨max C1 (max C2 C3), le_max_of_le_left hC10, fun N v J hJ hn h3 => ?_⟩
  have hv0 : 0 ≤ (v : ℝ) := (hs0 N).trans v.2.1
  have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
  have hηt : 0 < etaT E (t N) := etaT_pos hE (ht1 N)
  have hmono : etaT E (t N) ≤ etaT E (v : ℝ) := etaT_le_of_le_window hE v.2.2
  -- `η_v ≤ W ℓ_v η_v` because `W ≥ 1` and `ℓ_v ≥ 1`
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hell : (1 : ℝ) ≤ B.ell N (v : ℝ) := one_le_ellHat (B.L N) (B.three_le_L N) hv0 hv1
  have hηv : 0 < etaT E (v : ℝ) := etaT_pos hE hv1
  have hWl : (1 : ℝ) ≤ (B.W N : ℝ) * B.ell N (v : ℝ) := by nlinarith
  have hscale : etaT E (v : ℝ) ≤ B.scale E N (v : ℝ) := by
    show etaT E (v : ℝ) ≤ (B.W N : ℝ) * B.ell N (v : ℝ) * etaT E (v : ℝ)
    calc etaT E (v : ℝ) = 1 * etaT E (v : ℝ) := (one_mul _).symm
      _ ≤ ((B.W N : ℝ) * B.ell N (v : ℝ)) * etaT E (v : ℝ) :=
          mul_le_mul_of_nonneg_right hWl hηv.le
  have hscale0 : 0 < B.scale E N (v : ℝ) := lt_of_lt_of_le hηv hscale
  have hinv : (B.scale E N (v : ℝ))⁻¹ ≤ envFloor E t N :=
    le_trans (le_trans (inv_anti₀ hηv hscale) (inv_anti₀ hηt hmono))
      (le_max_right _ _)
  have hinv0 : (0 : ℝ) ≤ (B.scale E N (v : ℝ))⁻¹ := inv_nonneg.2 hscale0.le
  have hpow : ∀ n : ℕ, n ≤ 3 → (B.scale E N (v : ℝ))⁻¹ ^ n ≤ envFloor E t N ^ 3 := by
    intro n hn3
    exact (pow_le_pow_left₀ hinv0 hinv n).trans
      (pow_le_pow_right₀ (one_le_envFloor E t N) hn3)
  have hCmax : ∀ (c : ℝ) (n : ℕ), 0 ≤ c → c ≤ max C1 (max C2 C3) → n ≤ 4 →
      ‖B.Kval E N (v : ℝ) J‖ ≤ c * (B.scale E N (v : ℝ))⁻¹ ^ (n - 1) →
      ‖B.Kval E N (v : ℝ) J‖ ≤ max C1 (max C2 C3) * envFloor E t N ^ 3 := by
    intro c n hc0 hcle hn4 hb
    refine hb.trans ?_
    have h1 : c * (B.scale E N (v : ℝ))⁻¹ ^ (n - 1) ≤ c * envFloor E t N ^ 3 :=
      mul_le_mul_of_nonneg_left (hpow _ (by omega)) hc0
    exact h1.trans (mul_le_mul_of_nonneg_right hcle (pow_nonneg (envFloor_nonneg E t N) 3))
  have hcases : J.length = 1 ∨ J.length = 2 ∨ J.length = 3 := by omega
  rcases hcases with h | h | h
  · exact hCmax C1 1 hC10 (le_max_left _ _) (by norm_num) (hC1 N (v : ℝ) hv0 hv1 J hJ h)
  · exact hCmax C2 2 hC20 (le_max_of_le_right (le_max_left _ _)) (by norm_num)
      (hC2 N (v : ℝ) hv0 hv1 J hJ h)
  · exact hCmax C3 3 hC30 (le_max_of_le_right (le_max_right _ _)) (by norm_num)
      (hC3 N (v : ℝ) hv0 hv1 J hJ h)

theorem exists_env_window (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT E (t N)) :
    ∃ (Env : ℕ → ℝ) (Kenv : ℝ), 0 ≤ Kenv ∧ (∀ N, 0 ≤ Env N) ∧
      (∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv) ∧
      (∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖primBil (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
          (LoopData.idx (σ, a))‖ ≤ Env N) ∧
      (∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω)
          (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)))
          (LoopData.idx (σ, a))‖ ≤ Env N) ∧
      (∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X E N (v : ℝ) ω) (lkPath X E N (v : ℝ) ω)
          (LoopData.idx (σ, a))‖ ≤ Env N) := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  obtain ⟨C, hC0, hC⟩ := exists_norm_Kval_le_envFloor B hκ0 hκ1 hEκ hs0 ht1
  -- the pointwise loop envelope `M N = (1 + C) R_N^3`
  have hM0 : ∀ N : ℕ, 0 ≤ (1 + C) * envFloor E t N ^ 3 := fun N => by
    have := pow_nonneg (envFloor_nonneg E t N) 3; nlinarith
  have hgl : ∀ (N : ℕ) (v : TimeIcc s t N) (ω : Ω) (J : LoopIdx (ZMod (B.L N))),
      J.WF → 1 ≤ J.length → J.length ≤ 3 →
      ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)) J‖
        ≤ (1 + C) * envFloor E t N ^ 3 := by
    intro N v ω J hJ hn h3
    refine (norm_gloop_flow_le_envFloor X hE ht1 N v ω J hJ hn h3).trans ?_
    have := pow_nonneg (envFloor_nonneg E t N) 3
    nlinarith
  have hlk : ∀ (N : ℕ) (v : TimeIcc s t N) (ω : Ω) (J : LoopIdx (ZMod (B.L N))),
      J.WF → 1 ≤ J.length → J.length ≤ 3 →
      ‖lkPath X E N (v : ℝ) ω J‖ ≤ (1 + C) * envFloor E t N ^ 3 := by
    intro N v ω J hJ hn h3
    have h1 := norm_gloop_flow_le_envFloor X hE ht1 N v ω J hJ hn h3
    have h2 := hC N v J hJ hn h3
    calc ‖lkPath X E N (v : ℝ) ω J‖
        = ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)) J
            - B.Kval E N (v : ℝ) J‖ := rfl
      _ ≤ ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)) J‖
            + ‖B.Kval E N (v : ℝ) J‖ := norm_sub_le _ _
      _ ≤ envFloor E t N ^ 3 + C * envFloor E t N ^ 3 := add_le_add h1 h2
      _ = (1 + C) * envFloor E t N ^ 3 := by ring
  refine ⟨fun N => 4 * (B.W N : ℝ) * (B.L N : ℝ) * ((1 + C) * envFloor E t N ^ 3) ^ 2,
    2 + 6 * c, by linarith, fun N => ?_, ?_, ?_, ?_, ?_⟩
  · have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have := hM0 N
    positivity
  · -- the polynomial bound
    filter_upwards [hη, B.dim, eventually_ge_atTop 1,
      SumZeroDyn.eventually_const_mul_rpow_le (4 * (1 + C) ^ 2)
        (show 1 + 6 * c < 2 + 6 * c by linarith)] with N hηN hdimN hN1 hfinN
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    set A : ℝ := (N : ℝ) ^ c with hAdef
    have hA1 : (1 : ℝ) ≤ A := Real.one_le_rpow hN1' hc0
    have hηt : 0 < etaT E (t N) := etaT_pos hE (ht1 N)
    have hRA : envFloor E t N ≤ A := by
      refine max_le hA1 ?_
      have hpos : (0 : ℝ) < (N : ℝ) ^ (-c) := Real.rpow_pos_of_pos hN0 _
      have := inv_anti₀ hpos hηN
      rwa [Real.rpow_neg hN0.le, inv_inv] at this
    have hR0 : 0 ≤ envFloor E t N := envFloor_nonneg E t N
    have hA0 : (0 : ℝ) ≤ A := by linarith
    have h3 : envFloor E t N ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ hR0 hRA 3
    have hA30 : (0 : ℝ) ≤ A ^ 3 := by positivity
    have hMA : (1 + C) * envFloor E t N ^ 3 ≤ (1 + C) * A ^ 3 := by nlinarith
    have hMsq : ((1 + C) * envFloor E t N ^ 3) ^ 2 ≤ ((1 + C) * A ^ 3) ^ 2 :=
      pow_le_pow_left₀ (hM0 N) hMA 2
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by
      have : ((B.W N * B.L N : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hdimN.1
      push_cast at this; linarith
    have hA6 : A ^ 6 = (N : ℝ) ^ (6 * c) := by
      rw [hAdef, ← Real.rpow_natCast ((N : ℝ) ^ c) 6, ← Real.rpow_mul hN0.le]
      norm_num [mul_comm]
    have hstep : 4 * (B.W N : ℝ) * (B.L N : ℝ) * ((1 + C) * envFloor E t N ^ 3) ^ 2
        ≤ 4 * (1 + C) ^ 2 * ((N : ℝ) * A ^ 6) := by
      have hWL0 : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) :=
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hsq0 : (0 : ℝ) ≤ ((1 + C) * A ^ 3) ^ 2 := by positivity
      calc 4 * (B.W N : ℝ) * (B.L N : ℝ) * ((1 + C) * envFloor E t N ^ 3) ^ 2
          = 4 * ((B.W N : ℝ) * (B.L N : ℝ)) * ((1 + C) * envFloor E t N ^ 3) ^ 2 := by ring
        _ ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ)) * ((1 + C) * A ^ 3) ^ 2 := by nlinarith
        _ ≤ 4 * (N : ℝ) * ((1 + C) * A ^ 3) ^ 2 := by nlinarith
        _ = 4 * (1 + C) ^ 2 * ((N : ℝ) * A ^ 6) := by ring
    refine hstep.trans ?_
    have hprod : (N : ℝ) * A ^ 6 = (N : ℝ) ^ (1 + 6 * c) := by
      rw [hA6, Real.rpow_add hN0, Real.rpow_one]
    rw [hprod]
    exact hfinN
  · -- the envelope of `primBil(L-K, L-K)`
    intro N v σ a ω
    have hlen2 : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length = 2 := by
      show (List.ofFn a).length = 2
      rw [List.length_ofFn]
    have hK : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length →
        J.length ≤ (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length →
        ‖lkPath X E N (v : ℝ) ω J‖ ≤ (1 + C) * envFloor E t N ^ 3 := by
      intro J hJ h2 hle
      rw [hlen2] at hle
      exact hlk N v ω J hJ (by omega) (by omega)
    have hbound := norm_primBil_le_crude (B.three_le_L N) (B.W N)
      (I := LoopData.idx (σ, a)) (LoopData.idx_wf _) (hM0 N) (hM0 N) hK hK
    rw [hlen2] at hbound
    refine hbound.trans ?_
    push_cast
    have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have := hM0 N
    nlinarith [mul_nonneg (mul_nonneg hW0 hL0) (mul_nonneg this this)]
  · -- the envelope of `E^{(G)}(L-K, L)`
    intro N v σ a ω
    have hlen2 : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length = 2 := by
      show (List.ofFn a).length = 2
      rw [List.length_ofFn]
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖lkPath X E N (v : ℝ) ω ⟨[b], [x]⟩‖ ≤ (1 + C) * envFloor E t N ^ 3 :=
      fun b x => hlk N v ω ⟨[b], [x]⟩ rfl le_rfl (by show (1 : ℕ) ≤ 3; norm_num)
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
        J.length = (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length + 1 →
        ‖gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)) J‖
          ≤ (1 + C) * envFloor E t N ^ 3 := by
      intro J hJ hJlen
      rw [hlen2] at hJlen
      exact hgl N v ω J hJ (by omega) (by omega)
    have hbound := norm_eG_le_crude (B.three_le_L N) (B.W N)
      (I := LoopData.idx (σ, a)) (LoopData.idx_wf _) (hM0 N) hX hY
    rw [hlen2] at hbound
    refine hbound.trans ?_
    push_cast
    have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have := hM0 N
    nlinarith [mul_nonneg (mul_nonneg hW0 hL0) (mul_nonneg this this)]
  · -- the envelope of `E^{(G)}(L-K, L-K)`
    intro N v σ a ω
    have hlen2 : (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length = 2 := by
      show (List.ofFn a).length = 2
      rw [List.length_ofFn]
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖lkPath X E N (v : ℝ) ω ⟨[b], [x]⟩‖ ≤ (1 + C) * envFloor E t N ^ 3 :=
      fun b x => hlk N v ω ⟨[b], [x]⟩ rfl le_rfl (by show (1 : ℕ) ≤ 3; norm_num)
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
        J.length = (LoopData.idx (σ, a) : LoopIdx (ZMod (B.L N))).length + 1 →
        ‖lkPath X E N (v : ℝ) ω J‖ ≤ (1 + C) * envFloor E t N ^ 3 := by
      intro J hJ hJlen
      rw [hlen2] at hJlen
      exact hlk N v ω J hJ (by omega) (by omega)
    have hbound := norm_eG_le_crude (B.three_le_L N) (B.W N)
      (I := LoopData.idx (σ, a)) (LoopData.idx_wf _) (hM0 N) hX hY
    rw [hlen2] at hbound
    refine hbound.trans ?_
    push_cast
    have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have := hM0 N
    nlinarith [mul_nonneg (mul_nonneg hW0 hL0) (mul_nonneg this this)]

end EnvWindow

section GridWitness

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

end GridWitness


/-! ### §4b  The same envelope at a single interior time

Instantiating §3 at the degenerate window `s = t = v` gives the pointwise bound in the shape the
*integrability* slots of Step 6 want — those are quantified over `0 < v < 1`, not over the
window, so the window issue does not arise for them; §1 + §3 supply the bound. -/

section PointTime

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `N^{-1} ≤ η` for large `N`, for any fixed `η > 0`. -/
theorem eventually_rpow_neg_one_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ η := by
  obtain ⟨k, hk⟩ := exists_nat_gt η⁻¹
  filter_upwards [eventually_ge_atTop (max k 1)] with N hN
  have hNk : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_left k 1) hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_right k 1) hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [Real.rpow_neg hN0.le, Real.rpow_one]
  have h1 : η⁻¹ ≤ (N : ℝ) := le_trans hk.le hNk
  have := inv_anti₀ (inv_pos.2 hη) h1
  rwa [inv_inv] at this

/-- **The drift tensors are bounded at a single interior time**, uniformly in `ω`. -/
theorem exists_norm_drift_le_at (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
          (LoopData.idx (σ, a))‖ ≤ M) ∧
      (∀ (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
          (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))‖ ≤ M) ∧
      (∀ (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
        ‖Decay.eG (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
          (LoopData.idx (σ, a))‖ ≤ M) := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  obtain ⟨Env, Kenv, -, hEnv0, -, hQ, hG, hLK⟩ :=
    exists_env_window X hκ0 hκ1 hEκ (s := fun _ => v) (t := fun _ => v)
      (fun _ => hv0) (fun _ => hv1) (c := 1) zero_le_one
      (eventually_rpow_neg_one_le (etaT_pos hE hv1))
  refine ⟨Env N, hEnv0 N, fun σ a ω => hQ N ⟨v, le_rfl, le_rfl⟩ σ a ω,
    fun σ a ω => hG N ⟨v, le_rfl, le_rfl⟩ σ a ω, fun σ a ω => hLK N ⟨v, le_rfl, le_rfl⟩ σ a ω⟩

end PointTime

section Step

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

end Step

end RBM

/-! ### §6  The Gaussian producers for the window slots -/

namespace RBM.Gauss

open RBM Finset


theorem continuous_lkPath_gauss (d : Dims) (N : ℕ) {E v : ℝ} (hE : |E| < 2) (hv : v < 1)
    (I : LoopIdx (ZMod ((band d).L N))) :
    Continuous fun ω : Ω d => lkPath (sample d) E N v ω I :=
  (continuous_gloop_Hflow d N v (zt_im_ne_zero_of_lt_one hE hv) I).sub continuous_const

theorem continuous_gloop_flow_gauss (d : Dims) (N : ℕ) {E v : ℝ} (hE : |E| < 2) (hv : v < 1)
    (I : LoopIdx (ZMod ((band d).L N))) :
    Continuous fun ω : Ω d =>
      gloop ((band d).L N) ((band d).W N) ((sample d).H N v ω) (zt E v) I :=
  continuous_gloop_Hflow d N v (zt_im_ne_zero_of_lt_one hE hv) I

theorem continuous_primBil_lkPath_gauss (d : Dims) (N : ℕ) {E v : ℝ} (hE : |E| < 2) (hv : v < 1)
    (I : LoopIdx (ZMod ((band d).L N))) :
    Continuous fun ω : Ω d => primBil ((band d).L N) ((band d).W N)
      (lkPath (sample d) E N v ω) (lkPath (sample d) E N v ω) I := by
  refine continuous_const.mul (continuous_finsetSum _ fun k _ => continuous_finsetSum _
    fun l _ => continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_)
  exact ((continuous_lkPath_gauss d N hE hv _).mul continuous_const).mul
    (continuous_lkPath_gauss d N hE hv _)

theorem continuous_eG_lkPath_gloop_gauss (d : Dims) (N : ℕ) {E v : ℝ} (hE : |E| < 2) (hv : v < 1)
    (I : LoopIdx (ZMod ((band d).L N))) :
    Continuous fun ω : Ω d => Decay.eG ((band d).L N) ((band d).W N)
      (lkPath (sample d) E N v ω)
      (gloop ((band d).L N) ((band d).W N) ((sample d).H N v ω) (zt E v)) I := by
  refine continuous_const.mul (continuous_finsetSum _ fun k _ => continuous_finsetSum _
    fun a _ => continuous_finsetSum _ fun b _ => ?_)
  exact ((continuous_lkPath_gauss d N hE hv _).mul continuous_const).mul
    (continuous_gloop_flow_gauss d N hE hv _)

theorem continuous_eG_lkPath_gauss (d : Dims) (N : ℕ) {E v : ℝ} (hE : |E| < 2) (hv : v < 1)
    (I : LoopIdx (ZMod ((band d).L N))) :
    Continuous fun ω : Ω d => Decay.eG ((band d).L N) ((band d).W N)
      (lkPath (sample d) E N v ω) (lkPath (sample d) E N v ω) I := by
  refine continuous_const.mul (continuous_finsetSum _ fun k _ => continuous_finsetSum _
    fun a _ => continuous_finsetSum _ fun b _ => ?_)
  exact ((continuous_lkPath_gauss d N hE hv _).mul continuous_const).mul
    (continuous_lkPath_gauss d N hE hv _)

/-- The measurability of the quadratic drift integrand `primBil(L-K, L-K)` on the window, for the
Gaussian model. -/
theorem hmeasQ_window (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) :
    ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      AEStronglyMeasurable (fun ω => primBil ((band d).L N) ((band d).W N)
        (lkPath (sample d) E N (v : ℝ) ω) (lkPath (sample d) E N (v : ℝ) ω)
        (LoopData.idx (σ, a))) (band d).P :=
  fun N v σ a => (continuous_primBil_lkPath_gauss d N hE (v.2.2.trans_lt (ht1 N))
    (LoopData.idx (σ, a))).aestronglyMeasurable

/-- The measurability of the drift integrand `E^{(G)}(L-K, L)` on the window, for the Gaussian
model. -/
theorem hmeasG_window (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) :
    ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG ((band d).L N) ((band d).W N)
        (lkPath (sample d) E N (v : ℝ) ω)
        (gloop ((band d).L N) ((band d).W N) ((sample d).H N (v : ℝ) ω) (zt E (v : ℝ)))
        (LoopData.idx (σ, a))) (band d).P :=
  fun N v σ a => (continuous_eG_lkPath_gloop_gauss d N hE (v.2.2.trans_lt (ht1 N))
    (LoopData.idx (σ, a))).aestronglyMeasurable

/-- The measurability of `E^{(G)}(L-K, L-K)` on the window, for the Gaussian model. -/
theorem hmeasLK_window (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) :
    ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG ((band d).L N) ((band d).W N)
        (lkPath (sample d) E N (v : ℝ) ω) (lkPath (sample d) E N (v : ℝ) ω)
        (LoopData.idx (σ, a))) (band d).P :=
  fun N v σ a => (continuous_eG_lkPath_gauss d N hE (v.2.2.trans_lt (ht1 N))
    (LoopData.idx (σ, a))).aestronglyMeasurable

/-- The integrability of the one-loop `L_{v,(b),(x)}` on the window, for the Gaussian model, at
both charges. -/
theorem hintL1_window (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) :
    ∀ (N : ℕ) (v : TimeIcc s t N) (b : Bool) (x : ZMod ((band d).L N)),
      Integrable (fun ω => (sample d).Lval E N (v : ℝ) ω ⟨[b], [x]⟩) (band d).P := by
  intro N v b x
  have hv1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 N)
  exact integrable_sample_Lval (etaT_pos_of_lt_one hE hv1) (abs_im_zt E hE hv1).ge
    ⟨[b], [x]⟩ rfl le_rfl

/-- **The integrability of `primBil(L-K, L-K)`, for the Gaussian model.**  The integrand is
continuous in `ω` and deterministically bounded at every interior time
(`RBM.exists_norm_drift_le_at`), on a probability space. -/
theorem hintQ_gauss (d : Dims) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) :
    ∀ (N : ℕ) (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      Integrable (fun ω => primBil ((band d).L N) ((band d).W N)
        (lkPath (sample d) E N v ω) (lkPath (sample d) E N v ω) (LoopData.idx (σ, b)))
        (band d).P := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  intro N v hv0 hv1 σ b
  obtain ⟨M, -, hQ, -, -⟩ := exists_norm_drift_le_at (sample d) hκ0 hκ1 hEκ hv0.le hv1 N
  exact integrable_of_continuous_of_bound
    (continuous_primBil_lkPath_gauss d N hE hv1 (LoopData.idx (σ, b))) (fun ω => hQ σ b ω)

/-- **The integrability of `E^{(G)}(L-K, L)`, for the Gaussian model.** -/
theorem hintG_gauss (d : Dims) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) :
    ∀ (N : ℕ) (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      Integrable (fun ω => Decay.eG ((band d).L N) ((band d).W N)
        (lkPath (sample d) E N v ω)
        (gloop ((band d).L N) ((band d).W N) ((sample d).H N v ω) (zt E v))
        (LoopData.idx (σ, b))) (band d).P := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  intro N v hv0 hv1 σ b
  obtain ⟨M, -, -, hG, -⟩ := exists_norm_drift_le_at (sample d) hκ0 hκ1 hEκ hv0.le hv1 N
  exact integrable_of_continuous_of_bound
    (continuous_eG_lkPath_gloop_gauss d N hE hv1 (LoopData.idx (σ, b))) (fun ω => hG σ b ω)

end RBM.Gauss

namespace RBM

open Real

/-! ### §9  The quantitative half of Lemma 5.9 on the `K` side

With a decay rate of `K` linear in `1 - v`, turning `δ = C_m(1-v) e^{-c(1-v) ℓ}` into `N^{-D}` at
the radius `ℓ_v N^τ` would need `c(1-v) · ℓ_v N^τ ≳ D log N`, which fails badly when
`1 - v ≍ N^{-1}` and `ℓ_v ≍ N^{1/2}`.

**The rate is not linear.**  The rate of Corollary 3.5 is `RBM.cor35Rate δ = c₀ √δ / 4`
(`RBM1D/Loop/Cor35.lean`) — it is *square-root* in the gap.  So the decay length of `K` is
`δ^{-1/2}`, which at `δ = 1 - v` is exactly `RBM.ellHat`'s first branch `ℓ̂_v = (1-v)^{-1/2}`;
this is the same sharpened decay length as (2.52).  Consequently

  `cor35Rate (1-v) · (ℓ_v · N^τ) = (c₀/4) · N^τ`   (`RBM.cor35Rate_mul_ell_mul`)

whenever the cut-off in `ℓ̂` is inactive (`1 ≤ L √(1-v)`), so the exponential is `e^{-cN^τ}`,
super-polynomially small — there is no `log N` threshold to beat.  In the complementary regime
`L √(1-v) < 1` one has `ℓ_v = L`, so the radius `ℓ_v N^τ` already exceeds the diameter `L/2` of
the ring and the decay statement is vacuous (`RBM.LKDecayQuant.loopDecay_of_half_lt`).

The arithmetic that turns `C_m(δ) e^{-c₀√δ ℓ/4}` into `N^{-D}` is
`RBM.LKDecayQuant.term2_le`; the only new ingredient is the identity
`RBM.cor35Rate_mul_ell_mul` and the case split on the two branches of `ℓ̂`. -/

section KQuant

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The rate of Corollary 3.5 is `c₀/4` per unit of `N^τ` on the radius `ℓ_v N^τ`.**

`cor35Rate δ = c₀ √δ / 4` and `ℓ̂_v √(1-v) = 1` in the regime where the cut-off in `ℓ̂` is
inactive, so `cor35Rate (1-v) * (ℓ̂_v * A) = (c₀/4) A` — the gap cancels exactly.  This is the
statement that `ℓ̂_v`, not `(1-v)^{-1}`, is the decay length of `K`. -/
theorem cor35Rate_mul_ell_mul (L : ℕ) {u : ℝ} (hu1 : u < 1)
    (h : 1 ≤ (L : ℝ) * Real.sqrt (1 - u)) (A : ℝ) :
    cor35Rate (1 - u) * (ellHat L (u : ℂ) * A) = cZero / 4 * A := by
  have he := LKDecayQuant.ellHat_mul_sqrt_eq_one L hu1 h
  have hid : cor35Rate (1 - u) * (ellHat L (u : ℂ) * A)
      = cZero / 4 * A * (ellHat L (u : ℂ) * Real.sqrt (1 - u)) := by
    unfold cor35Rate; ring
  rw [hid, he, mul_one]

end KQuant

end RBM

namespace RBM

open Real

/-! ### §10  `(L - K)` at loop length `0`

The good sets of Step 6 contain a deterministic clause bounding `|L - K|` at loop lengths `≤ 2`
on the window.  Loop length `0` has to be treated separately — `RBM.lkPath_nil` computes it
exactly, `(L-K)_∅ = L W` (the trace of the identity, since `RBM.Kgen` vanishes at length `0`),
which is `≤ N` by `RBM.Band.dim` — because the `1 ≤ |J|` hypothesis of
`RBM.norm_gloop_flow_le_envFloor` genuinely excludes it. -/

section GoodSets

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

theorem loopIdx_eq_nil {α : Type*} {J : LoopIdx α} (hJ : J.WF) (h : J.length = 0) :
    J = ⟨[], []⟩ := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.length, LoopIdx.WF] at hJ h
  have ha : a = [] := List.eq_nil_of_length_eq_zero h
  have hs : σ = [] := List.eq_nil_of_length_eq_zero (by rw [hJ, h])
  subst ha; subst hs; rfl

theorem lkPath_nil (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω) :
    lkPath X E N v ω ⟨[], []⟩ = ((B.L N * B.W N : ℕ) : ℂ) := by
  change gloop (B.L N) (B.W N) (X.H N v ω) (zt E v) ⟨[], []⟩ - B.Kval E N v ⟨[], []⟩ = _
  rw [show B.Kval E N v (⟨[], []⟩ : LoopIdx (ZMod (B.L N))) = 0 from rfl]
  change Matrix.trace (gloopProd (B.L N) (B.W N) (X.H N v ω) (zt E v) ⟨[], []⟩) - 0 = _
  rw [gloopProd_nil, Matrix.trace_one, sub_zero]
  simp

end GoodSets

end RBM

namespace RBM

open Real

/-! ### §11  Lemma 5.9 for the *expectation* `E(L - K)` at the initial time

The fast decay (7.13) of `E(L-K)_{s_N,σ,·}` is about an expectation, not a pathwise quantity,
so Lemma 5.9's high-probability conclusion has to be integrated.
`RBM.fastDecay_integral_of_highProb` is exactly that step, and it charges `Env · P(Gᶜ)` for
the complement; with a deterministic envelope `N^{2+3c}` and the good set taken at the error
exponent `D + KM + 1`, that charge is `N^{-(D+1)}`, so the total is
`2N^{-(D+1)} ≤ N^{-D} ≤ W^{-D}` (the last step because `W ≤ N` and the exponent is negative —
the paper's `W^{-D}` is the *weaker* of the two).

`RBM.integral_lkPath_eq_lkT` is the identification `∫ (L - K) = E L - K`, which needs only the
integrability of `L` (the `K` term is deterministic and `P` is a probability measure). -/

section LkExpect

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

theorem integral_lkPath_eq_lkT (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ)
    (σ : Fin 2 → Bool)
    (hint : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 1 ≤ J.length →
      Integrable (fun ω => X.Lval E N u ω J) B.P) :
    (fun b : LoopArg (B.L N) 2 => ∫ ω, lkPath X E N u ω (LoopData.idx (σ, b)) ∂B.P)
      = Step6.lkT X E N u σ := by
  have hP := B.isProbabilityMeasure
  funext b
  change ∫ ω, (X.Lval E N u ω (LoopData.idx (σ, b)) - B.Kval E N u (LoopData.idx (σ, b))) ∂B.P
      = X.ELval E N u (LoopData.idx (σ, b)) - B.Kval E N u (LoopData.idx (σ, b))
  rw [integral_sub (hint _ (LoopData.idx_wf _) (by simp)) (integrable_const _),
    integral_const, probReal_univ, one_smul]
  rfl

end LkExpect

end RBM

namespace RBM

section DriftDecay

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

end DriftDecay

end RBM

namespace RBM.Gauss

open RBM

section GaussProducers

end GaussProducers

section Witness

end Witness

end RBM.Gauss

namespace RBM

section Steps34

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

end Steps34

end RBM

namespace RBM.Gauss

open RBM

section StepsAssembly

end StepsAssembly

end RBM.Gauss

namespace RBM.Gauss

open RBM

section FdWitness

end FdWitness

end RBM.Gauss
