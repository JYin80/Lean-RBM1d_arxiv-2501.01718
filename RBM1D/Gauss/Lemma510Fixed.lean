/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LoopDecayFixed
import RBM1D.Gauss.OneLoopSharpGrid
import RBM1D.Gauss.GridHierarchyN
import RBM1D.Gauss.Step2Plain
import RBM1D.Hierarchy.DriftDef
import RBM1D.Hierarchy.LKDecayQuant

/-!
# Lemma 5.10 at a fixed time

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.4, Lemma 5.10 (5.76)-(5.80), for the Gaussian model of `RBM1D/Gauss/Model.lean`,
all deterministic per matrix `M` at a fixed time `v`, plus the fixed-time good set `goodSet514`.

`RBM1D/Hierarchy/Decay.lean` formalizes Lemma 5.10 in abstract, deterministic form:
`Decay.norm_couplingLen_le'` is (5.78), `Decay.norm_primBil_sub_le` is (5.79), `Decay.norm_eG_le`
(bridged via `RBM.DriftDef.eGterm_eq_eG`) is (5.80).  This file (a) defines
`Ξ_m(M)`/`Ξ^{(L)}_m(M)` of (5.76) at a bare matrix `M`, (b) instantiates the three bounds at the
Gauss/grid layer with the `ℓ_v` factor extracted explicitly, (c) defines `goodSet514` and proves
it measurable, (d) supplies the union bound and the sharp `Ξ₁` conversion for its grid
`HighProb`.

`norm_KsimLK_le` uses the paper's single `Ξ_{n-l_K+2}` (via `couplingLen_eq_restrict`), and `K`'s
decay constant is collapsed to the literal `W^{-D}` (`K_decay_rpow`) under the explicit,
eventually true regime hypothesis `KDecayRegime` (`eventually_kDecayRegime`).  The tails of the
three bounds are `C_n · W · L · W^{-D}` times the relevant `Ξ`.

## Main results

* `xiLM`, `lkMaxM`, `xiLKM` — (5.76) at a bare matrix `M`; measurability.
* `couplingLen_eq_restrict`, `KDecayRegime`, `eventually_kDecayRegime`, `K_decay_rpow`.
* `norm_KsimLK_le` — (5.78).
* `norm_primBil_le514` — (5.79).
* `norm_eGterm_le` — (5.80), with the sharp `Ξ₁` normalization.
* `goodSet514`, `measurableSet_goodSet514`, `goodSet514_decay`.
* `highProb_biInter_finset`, `xiLKM_one_le_of_forall` — the union bound, and the conversion
  to the sharp `Ξ₁`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-! ### (5.76) at a bare matrix `M` -/

section XiDefs

variable (E : ℝ) (N : ℕ) (v : ℝ)

/-- **`Ξ^{(L)}_m(M)`** (5.76), at a bare matrix `M`: `RBM.loopXi` of `Loop/Split.lean` already
takes the matrix directly, so this is a one-line specialisation of `Sample.xiL`
(`Flow/FlowFamiliesCore.lean`) with `M` in place of `X.H N t ω`. -/
def xiLM (M : Matrix (d.Idx N) (d.Idx N) ℂ) (m : ℕ) : ℝ :=
  loopXi (d.L N) (d.W N) M (zt E v) ((band d).scale E N v) m

/-- `max_{σ,a} |(L-K)_{v,σ,a}(M)|` over loops of length `m`, deterministic in `M` (mirrors
`Sample.lkMax`). -/
def lkMaxM (M : Matrix (d.Idx N) (d.Idx N) ℂ) (m : ℕ) : ℝ :=
  ⨆ u : LoopData (d.L N) m,
    ‖gloop (d.L N) (d.W N) M (zt E v) u.idx - (band d).Kval E N v u.idx‖

/-- **`Ξ^{(L-K)}_m(M)`** (5.76), `Ξ_m(M) := A_v^m · max_{σ,a} |(L-K)_{v,σ,a}(M)|`,
at a bare matrix `M` (mirrors `Sample.xiLK`). -/
def xiLKM (M : Matrix (d.Idx N) (d.Idx N) ℂ) (m : ℕ) : ℝ :=
  lkMaxM d E N v M m * ((band d).scale E N v) ^ m

theorem lkMaxM_nonneg (M : Matrix (d.Idx N) (d.Idx N) ℂ) (m : ℕ) : 0 ≤ lkMaxM d E N v M m :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem xiLKM_nonneg (hA : 0 ≤ (band d).scale E N v) (M : Matrix (d.Idx N) (d.Idx N) ℂ) (m : ℕ) :
    0 ≤ xiLKM d E N v M m := mul_nonneg (lkMaxM_nonneg d E N v M m) (pow_nonneg hA _)

/-- The `G`-loop of an arbitrary well-formed `J` of length `m` is `≤ lkMaxM d E N v M m` (mirrors
`RBM.norm_gloop_le_loopMax`). -/
theorem norm_sub_le_lkMaxM (M : Matrix (d.Idx N) (d.Idx N) ℂ) {m : ℕ}
    (J : LoopIdx (ZMod (d.L N))) (hJ : J.WF) (hlen : J.length = m) :
    ‖gloop (d.L N) (d.W N) M (zt E v) J - (band d).Kval E N v J‖ ≤ lkMaxM d E N v M m := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF, LoopIdx.length] at hJ hlen
  subst hlen
  have hσ' : List.ofFn (fun i : Fin a.length => σ.get (Fin.cast hJ.symm i)) = σ := by
    apply List.ext_get <;> simp [hJ]
  have ha' : List.ofFn (fun i : Fin a.length => a.get i) = a := List.ofFn_get a
  have h := le_ciSup (f := fun u : LoopData (d.L N) a.length =>
      ‖gloop (d.L N) (d.W N) M (zt E v) u.idx - (band d).Kval E N v u.idx‖)
    (Set.finite_range _).bddAbove
    ((fun i : Fin a.length => σ.get (Fin.cast hJ.symm i), fun i : Fin a.length => a.get i) :
      LoopData (d.L N) a.length)
  have hidx : LoopData.idx
      ((fun i : Fin a.length => σ.get (Fin.cast hJ.symm i), fun i : Fin a.length => a.get i)
        : LoopData (d.L N) a.length) = (⟨σ, a⟩ : LoopIdx (ZMod (d.L N))) := by
    simp only [LoopData.idx, hσ', ha']
  rw [hidx] at h
  simpa [lkMaxM] using h

end XiDefs

/-! ### Measurability of `xiLM`/`lkMaxM`/`xiLKM` in `M` -/

section XiMeasurable

variable (E : ℝ) (N : ℕ) (v : ℝ)

theorem measurable_loopMax_matrix (z : ℂ) (m : ℕ) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => loopMax (d.L N) (d.W N) M z m) := by
  have heq : (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => loopMax (d.L N) (d.W N) M z m)
      = Finset.univ.sup' Finset.univ_nonempty
          (fun (x : (Fin m → Bool) × (Fin m → ZMod (d.L N)))
            (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
              ‖gloop (d.L N) (d.W N) M z ⟨List.ofFn x.1, List.ofFn x.2⟩‖) := by
    funext M
    simp only [Finset.sup'_apply]
    exact (Finset.sup'_univ_eq_ciSup
      (fun x : (Fin m → Bool) × (Fin m → ZMod (d.L N)) =>
        ‖gloop (d.L N) (d.W N) M z ⟨List.ofFn x.1, List.ofFn x.2⟩‖)).symm
  rw [heq]
  exact Finset.measurable_sup' _ fun x _ => (measurable_gloop_matrix d N z _).norm

theorem measurable_xiLM (m : ℕ) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => xiLM d E N v M m) :=
  (measurable_loopMax_matrix d N (zt E v) m).mul_const _

theorem measurable_lkMaxM (m : ℕ) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => lkMaxM d E N v M m) := by
  have heq : (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => lkMaxM d E N v M m)
      = Finset.univ.sup' Finset.univ_nonempty
          (fun (u : LoopData (d.L N) m) (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
            ‖gloop (d.L N) (d.W N) M (zt E v) u.idx - (band d).Kval E N v u.idx‖) := by
    funext M
    simp only [Finset.sup'_apply]
    exact (Finset.sup'_univ_eq_ciSup
      (fun u : LoopData (d.L N) m =>
        ‖gloop (d.L N) (d.W N) M (zt E v) u.idx - (band d).Kval E N v u.idx‖)).symm
  rw [heq]
  exact Finset.measurable_sup' _
    fun u _ => ((measurable_gloop_matrix d N (zt E v) u.idx).sub measurable_const).norm

theorem measurable_xiLKM (m : ℕ) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => xiLKM d E N v M m) :=
  (measurable_lkMaxM d E N v m).mul_const _

end XiMeasurable

/-! ### An elementary estimate: extracting the `ℓ_v` factor -/

section EllExtract

/-- **The `ℓ_v`-extraction step used by (T1)-(T3):** `W(ℓ_v W^τ + 1)/A_v ≤ 2 W^τ η_v^{-1}`,
using `1 ≤ ℓ_v` (`RBM.one_le_ellHat`) and `1 ≤ W^τ` (`τ > 0`, `1 ≤ W`), and `A_v = W ℓ_v η_v`
(`RBM.Band.scale`). This is the paper's own remark ("the `ℓ_u` factor comes from the sum of the
index `a`... and cancels against `A`") made explicit. -/
theorem W_mul_ell_rpow_add_one_div_scale_le {E : ℝ} (hE : |E| < 2) (N : ℕ) {v τ : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hτ : 0 < τ) :
    (d.W N : ℝ) * ((band d).ell N v * (d.W N : ℝ) ^ τ + 1) * ((band d).scale E N v)⁻¹
      ≤ 2 * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹ := by
  have hW1 : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
  have hℓ1 : (1 : ℝ) ≤ (band d).ell N v :=
    one_le_ellHat (d.L N) (d.three_le_L N) hv0 hv1
  have hWτ1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ := Real.one_le_rpow hW1 hτ.le
  have hη0 : 0 < etaT E v := etaT_pos hE hv1
  have hℓ0 : 0 < (band d).ell N v := lt_of_lt_of_le one_pos hℓ1
  have hW0 : (0 : ℝ) < d.W N := by linarith
  have hAeq : (band d).scale E N v = (d.W N : ℝ) * (band d).ell N v * etaT E v := rfl
  have hA0 : (0 : ℝ) < (d.W N : ℝ) * (band d).ell N v * etaT E v := by positivity
  rw [hAeq, mul_inv_le_iff₀ hA0]
  have hexpand : 2 * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹
      * ((d.W N : ℝ) * (band d).ell N v * etaT E v)
      = 2 * (d.W N : ℝ) ^ τ * (d.W N : ℝ) * (band d).ell N v := by
    field_simp
  rw [hexpand]
  have h1 : (1 : ℝ) ≤ (band d).ell N v * (d.W N : ℝ) ^ τ := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hW0.le]

end EllExtract

/-! ### (T1) `norm_KsimLK_le`, (5.78) -/

section KsimLK

/-- **The graded coupling only sees loops of length `n - l_K + 2` of its second argument.** In
`primBilLen` the `K` factor sits on `cutGlueL`, of length `k + n - l + 1 = l_K`, which forces the
`D` factor on `cutGlueR` to have length `l - k + 1 = n - l_K + 2`; symmetrically in
`primBilLenR`. Hence `D` may be replaced by its restriction to that single length. This is what
lets (5.78) be stated with the single `Ξ_{n-l_K+2}` of the paper. -/
theorem couplingLen_eq_restrict {L : ℕ} [NeZero L] (W lK : ℕ) (K D : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) :
    Decay.couplingLen L W lK K D I
      = Decay.couplingLen L W lK K
          (fun J => if J.length = I.length - lK + 2 then D J else 0) I := by
  unfold Decay.couplingLen primBilLen Decay.primBilLenR
  have hL : (∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : ZMod L,
      ∑ b : ZMod L, (if (I.cutGlueL k l a).length = lK then
        K (I.cutGlueL k l a) * SB L a b * D (I.cutGlueR k l b) else 0))
      = ∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : ZMod L,
      ∑ b : ZMod L, (if (I.cutGlueL k l a).length = lK then
        K (I.cutGlueL k l a) * SB L a b
          * (if (I.cutGlueR k l b).length = I.length - lK + 2 then D (I.cutGlueR k l b) else 0)
        else 0) := by
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have h1 := LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2
    have h2 := LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2
    by_cases h : (I.cutGlueL k l a).length = lK
    · have h' : (I.cutGlueR k l b).length = I.length - lK + 2 := by omega
      rw [if_pos h, if_pos h, if_pos h']
    · rw [if_neg h, if_neg h]
  have hR : (∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : ZMod L,
      ∑ b : ZMod L, (if (I.cutGlueR k l b).length = lK then
        D (I.cutGlueL k l a) * SB L a b * K (I.cutGlueR k l b) else 0))
      = ∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : ZMod L,
      ∑ b : ZMod L, (if (I.cutGlueR k l b).length = lK then
        (if (I.cutGlueL k l a).length = I.length - lK + 2 then D (I.cutGlueL k l a) else 0)
          * SB L a b * K (I.cutGlueR k l b)
        else 0) := by
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have h1 := LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2
    have h2 := LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2
    by_cases h : (I.cutGlueR k l b).length = lK
    · have h' : (I.cutGlueL k l a).length = I.length - lK + 2 := by omega
      rw [if_pos h, if_pos h, if_pos h']
    · rw [if_neg h, if_neg h]
  rw [hL, hR]

/-- **The regime hypothesis collapsing `K`'s decay constant to `W^{-D}`** (the `K`-side
conditions of `mem_decaySets_of_lre`, at one `N`): `1 ≤ N`, `L ≤ N`, `W ≤ N`,
`N^{1/2} ≤ W` ((2.2)), `2 ≤ N^{τ/4}`, and the smallness of
`cKbound m₀ · N^{2 cKexp m₀ + D} · exp(-cZero/2 · N^{τ/4})`. It depends only on `(m₀, τ, D)` and
`N`, and holds for all large `N` (`eventually_kDecayRegime`). -/
def KDecayRegime (N m₀ : ℕ) (τ D : ℝ) : Prop :=
  1 ≤ N ∧ (d.L N : ℝ) ≤ N ∧ (d.W N : ℝ) ≤ N ∧ (N : ℝ) ^ ((1 : ℝ) / 2) ≤ d.W N ∧
    2 ≤ (N : ℝ) ^ (τ / 2 / 2) ∧
    2 * LKDecayQuant.cKbound m₀ * (N : ℝ) ^ (((2 * LKDecayQuant.cKexp m₀ : ℕ) : ℝ) + D)
        * Real.exp (-(cZero / 2 * (N : ℝ) ^ (τ / 2 / 2))) ≤ 1

/-- **Satisfiability witness for `KDecayRegime`:** for every fixed `m₀`, `τ > 0` and `D`, it holds
for all large `N`. -/
theorem eventually_kDecayRegime (m₀ : ℕ) {τ : ℝ} (hτ : 0 < τ) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, KDecayRegime d N m₀ τ D := by
  have hWN : ∀ᶠ N : ℕ in atTop, (d.W N : ℝ) ≤ N := by
    filter_upwards [(band d).dim] with N hN
    have h : d.W N ≤ d.W N * d.L N :=
      Nat.le_mul_of_pos_right _ (by have := d.three_le_L N; omega)
    exact_mod_cast h.trans hN.1
  have hWlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2) ≤ d.W N := by
    filter_upwards [(band d).bandwidth, eventually_ge_atTop 1] with N hN hN1
    refine le_trans ?_ hN
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
      (by linarith [(band d).c_pos])
  have h2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (τ / 2 / 2) := by
    filter_upwards [SumZeroDyn.eventually_const_mul_rpow_le 2
      (show (0 : ℝ) < τ / 2 / 2 by linarith)] with N hN
    simpa using hN
  have hexp := SumZeroDyn.eventually_exp_small (2 * LKDecayQuant.cKbound m₀)
    (((2 * LKDecayQuant.cKexp m₀ : ℕ) : ℝ) + D) (cZero / 2) (by have := cZero_pos; linarith)
    (show (0 : ℝ) < τ / 2 / 2 by linarith)
  filter_upwards [eventually_ge_atTop 1, LKDecayQuant.eventually_L_le (B := band d), hWN, hWlow,
    h2, hexp] with N hN1 hLN hWNN hWlowN h2N hexpN
  exact ⟨hN1, hLN, hWNN, hWlowN, h2N, hexpN⟩

/-- **(5.75), `K` side, with the literal `W^{-D}`:** under `KDecayRegime`, `K_{v,σ,a}` has
`(ℓ_v W^τ, W^{-D})` decay for every loop of length `≤ m₀`. This is `K_decay` with its
constant `cKdecay(1-v)·exp(-cor35Rate(1-v)·ℓ_v W^τ)` absorbed into `W^{-D}` by
`LKDecayQuant.term2_le` (non-cut-off case `1 ≤ L√(1-v)`); in the cut-off case `ℓ_v = L` the
radius exceeds the diameter `L/2` and the statement is vacuous. Same argument as the `K` half of
`mem_decaySets_of_lre`. -/
theorem K_decay_rpow {E : ℝ} (hE : |E| < 2) {N : ℕ} (m₀ : ℕ) {v τ D : ℝ}
    (hτ : 0 < τ) (hD : 0 ≤ D) (hv0 : 0 ≤ v) (hv1 : v < 1) (hreg : KDecayRegime d N m₀ τ D) :
    Decay.LoopDecay (d.L N) m₀ ((band d).ell N v * (d.W N : ℝ) ^ τ) ((d.W N : ℝ) ^ (-D))
      (fun I => (band d).Kval E N v I) := by
  obtain ⟨hN1, hLN, hWN, hWlow, h2, hexp⟩ := hreg
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hW1 : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
  have hL0 : (0 : ℝ) < d.L N := by exact_mod_cast (by have := d.three_le_L N; omega : 0 < d.L N)
  have hWτ1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ := Real.one_le_rpow hW1 hτ.le
  have hWD0 : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hρ0 : 0 < (band d).ell N v * (d.W N : ℝ) ^ τ := ell_mul_rpow_pos d N v hv0 hv1 τ
  by_cases hcut : 1 ≤ (d.L N : ℝ) * Real.sqrt (1 - v)
  · have hellsq : (band d).ell N v * Real.sqrt (1 - v) = 1 :=
      LKDecayQuant.ellHat_mul_sqrt_eq_one (d.L N) hv1 hcut
    have hv0' : (0 : ℝ) < 1 - v := by linarith
    have hv1' : (1 : ℝ) - v ≤ 1 := by linarith
    have hsqN : 1 / (N : ℝ) ≤ Real.sqrt (1 - v) := by
      rw [div_le_iff₀ hN0]; nlinarith [Real.sqrt_nonneg (1 - v)]
    have hvN : 1 / (1 - v) ≤ (N : ℝ) ^ 2 := by
      have hsq : Real.sqrt (1 - v) * Real.sqrt (1 - v) = 1 - v := Real.mul_self_sqrt (by linarith)
      have hm2 : 1 / (N : ℝ) * (1 / (N : ℝ)) ≤ 1 - v := by
        rw [← hsq]; exact mul_le_mul hsqN hsqN (by positivity) (Real.sqrt_nonneg _)
      rw [div_le_iff₀ hv0']
      calc (1 : ℝ) = (N : ℝ) ^ 2 * (1 / (N : ℝ) * (1 / (N : ℝ))) := by field_simp
        _ ≤ (N : ℝ) ^ 2 * (1 - v) := mul_le_mul_of_nonneg_left hm2 (by positivity)
    set A : ℝ := (N : ℝ) ^ (τ / 2 / 2) with hAdef
    have hA0 : 0 ≤ A := Real.rpow_nonneg hN0.le _
    have hNsplit : (N : ℝ) ^ (τ / 2) = A * A := by
      rw [hAdef, ← Real.rpow_add hN0]; ring_nf
    have hWτ : (N : ℝ) ^ (τ / 2) ≤ (d.W N : ℝ) ^ τ := by
      have h1 : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ τ ≤ (d.W N : ℝ) ^ τ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hWlow hτ.le
      have h2' : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ τ = (N : ℝ) ^ (τ / 2) := by
        rw [← Real.rpow_mul hN0.le]; ring_nf
      rw [h2'] at h1; exact h1
    have hexpo : cZero / 2 * (N : ℝ) ^ (τ / 2 / 2) ≤
        cor35Rate (1 - v) * ((band d).ell N v * (d.W N : ℝ) ^ τ) := by
      have hid : cor35Rate (1 - v) * ((band d).ell N v * (d.W N : ℝ) ^ τ)
          = cZero / 4 * (d.W N : ℝ) ^ τ * ((band d).ell N v * Real.sqrt (1 - v)) := by
        unfold cor35Rate; ring
      rw [hid, hellsq, mul_one]
      have hAA : 2 * A ≤ A * A := mul_le_mul_of_nonneg_right h2 hA0
      have h2A : 2 * A ≤ (d.W N : ℝ) ^ τ := hAA.trans (hNsplit ▸ hWτ)
      have hc0 : 0 ≤ cZero / 4 := by have := cZero_pos; positivity
      calc cZero / 2 * A = cZero / 4 * (2 * A) := by ring
        _ ≤ cZero / 4 * (d.W N : ℝ) ^ τ := mul_le_mul_of_nonneg_left h2A hc0
    have hWD : (N : ℝ) ^ (-D) ≤ (d.W N : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
    have hKerr : Decay.cKdecay m₀ (1 - v) *
        Real.exp (-(cor35Rate (1 - v) * ((band d).ell N v * (d.W N : ℝ) ^ τ))) ≤
          (d.W N : ℝ) ^ (-D) := by
      have h := LKDecayQuant.term2_le (m := m₀) (τ := τ / 2) hN0 hv0' hv1' hvN hexpo hexp
      have hN0' : (0 : ℝ) ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
      linarith
    exact (K_decay d E N m₀ v hv0 hv1 hE.le hρ0).mono (d.L N) le_rfl le_rfl hKerr
  · have hcut' : (d.L N : ℝ) * Real.sqrt (1 - v) < 1 := not_le.mp hcut
    have hellL : (band d).ell N v = (d.L N : ℝ) := LKDecayQuant.ellHat_eq_L (d.L N) hv1 hcut'
    have hhalf : (d.L N : ℝ) / 2 < (band d).ell N v * (d.W N : ℝ) ^ τ := by
      rw [hellL]; nlinarith
    exact LKDecayQuant.loopDecay_of_half_lt hhalf _

/-- **(T1)**: (5.78), `[K∼(L−K)]^{l_K}_{v,σ}(M)` for `3 ≤ l_K ≤ n`, at a fixed matrix `M` and
time `v`, bounded by the **single** `Ξ^{(L-K)}_{n-l_K+2}(M)` of the paper:
`‖·‖ ≤ 8e n² C_K W^τ η_v^{-1} Ξ_{n-l_K+2}(M) A_v^{-n} + 2n² W L W^{-D} Ξ_{n-l_K+2}(M)`.
Inputs: the K bound (2.59) with constant `CK`, and
the K decay with the literal `W^{-D}` (`K_decay_rpow`, under the explicit regime `KDecayRegime`,
eventually true by `eventually_kDecayRegime`). The `ℓ_v` factor (from the `a`-sum restricted by
the decay of `K`) is extracted by `W_mul_ell_rpow_add_one_div_scale_le`. Route:
`couplingLen_eq_restrict` + `Decay.norm_couplingLen_le'`. -/
theorem norm_KsimLK_le {E : ℝ} (hE : |E| < 2) (N : ℕ) {v τ D : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hτ : 0 < τ) (hD : 0 ≤ D) (hA1 : 1 ≤ (band d).scale E N v)
    {n lK : ℕ} (hlK : 3 ≤ lK) (hln : lK ≤ n) (hreg : KDecayRegime d N n τ D)
    {CK : ℝ} (hCK : 0 ≤ CK)
    (hK : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖(band d).Kval E N v J‖ ≤ CK * ((band d).scale E N v)⁻¹ ^ (J.length - 1))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I : LoopIdx (ZMod (d.L N))) (hI : I.WF) (hIlen : I.length = n) :
    ‖Decay.couplingLen (d.L N) (d.W N) lK ((band d).Kval E N v)
        (fun J => gloop (d.L N) (d.W N) M (zt E v) J - (band d).Kval E N v J) I‖
      ≤ 8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹
          * xiLKM d E N v M (n - lK + 2) * ((band d).scale E N v)⁻¹ ^ n
        + 2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D)
          * xiLKM d E N v M (n - lK + 2) := by
  have h3L : 3 ≤ d.L N := d.three_le_L N
  have hℓpos : 0 < (band d).ell N v * (d.W N : ℝ) ^ τ := ell_mul_rpow_pos d N v hv0 hv1 τ
  have hApos : 0 < (band d).scale E N v := lt_of_lt_of_le one_pos hA1
  set Φ : ℝ := xiLKM d E N v M (n - lK + 2) with hΦdef
  have hΦ : 0 ≤ Φ := xiLKM_nonneg d E N v hApos.le M _
  have hδ : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D) :=
    Real.rpow_nonneg (by exact_mod_cast (d.W_pos N).le) _
  have hKd := K_decay_rpow d hE n hτ hD hv0 hv1 hreg
  have hDbound : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length < I.length →
      ‖(fun J => if J.length = I.length - lK + 2 then
          gloop (d.L N) (d.W N) M (zt E v) J - (band d).Kval E N v J else 0) J‖
        ≤ Φ * ((band d).scale E N v)⁻¹ ^ J.length := by
    intro J hJ _hJlt
    by_cases h : J.length = I.length - lK + 2
    · simp only [if_pos h]
      have hlen : J.length = n - lK + 2 := by omega
      have hle := norm_sub_le_lkMaxM d E N v M J hJ hlen
      have heq : Φ * ((band d).scale E N v)⁻¹ ^ J.length = lkMaxM d E N v M (n - lK + 2) := by
        rw [hlen, hΦdef, xiLKM, mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hApos), one_pow,
          mul_one]
      rw [heq]; exact hle
    · simp only [if_neg h, norm_zero]
      positivity
  have hCoup := Decay.norm_couplingLen_le' (d.L N) h3L (d.W N) hlK (I := I) hI
    hA1 hℓpos hδ hCK hΦ
    (fun J hJ h2 hlen => hK J hJ h2 (by rw [hIlen] at hlen; exact hlen))
    (by rw [hIlen]; exact hKd)
    hDbound
  refine (le_of_eq (congrArg norm (couplingLen_eq_restrict (d.W N) lK ((band d).Kval E N v)
    (fun J => gloop (d.L N) (d.W N) M (zt E v) J - (band d).Kval E N v J) I))).trans ?_
  refine hCoup.trans ?_
  rw [hIlen]
  have hratio := W_mul_ell_rpow_add_one_div_scale_le d hE N hv0 hv1 hτ
  have hfactor_nonneg : (0 : ℝ) ≤ 4 * Real.exp 1 * (n : ℝ) ^ 2 * CK * Φ
      * ((band d).scale E N v)⁻¹ ^ n := by positivity
  refine add_le_add ?_ le_rfl
  calc 4 * Real.exp 1 * (n : ℝ) ^ 2 * CK * Φ
        * ((d.W N : ℝ) * ((band d).ell N v * (d.W N : ℝ) ^ τ + 1) / (band d).scale E N v)
        * ((band d).scale E N v)⁻¹ ^ n
      = (4 * Real.exp 1 * (n : ℝ) ^ 2 * CK * Φ * ((band d).scale E N v)⁻¹ ^ n)
          * ((d.W N : ℝ) * ((band d).ell N v * (d.W N : ℝ) ^ τ + 1)
            * ((band d).scale E N v)⁻¹) := by rw [div_eq_mul_inv]; ring
    _ ≤ (4 * Real.exp 1 * (n : ℝ) ^ 2 * CK * Φ * ((band d).scale E N v)⁻¹ ^ n)
          * (2 * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹) :=
        mul_le_mul_of_nonneg_left hratio hfactor_nonneg
    _ = 8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹ * Φ
          * ((band d).scale E N v)⁻¹ ^ n := by ring

end KsimLK

/-! ### (T2) `norm_primBil_le514`, (5.79) -/

section PrimBil

/-- **`norm_primBil_le514`**: (5.79), `E^{((L-K)×(L-K))}_{v,σ}(M) = primBil(L-K,L-K)_v(M)` at a
fixed matrix `M` and time `v`, from `lkDecaySet` (the `L-K` half of Lemma 5.9's (5.75), which
supplies both the decay hypothesis and the literal `δ = W^{-D}`) and the hypotheses `hΞprod`/`hΞm`.
Taking `X := Ξ^{(L-K)}_m(M)` literally (not an external bound) makes `Decay.norm_primBil_sub_le`'s
pointwise `hD` hypothesis automatic (`norm_sub_le_lkMaxM`). -/
theorem norm_primBil_le514 {E : ℝ} (hE : |E| < 2) (N : ℕ) {v τ : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hτ : 0 < τ) (hA1 : 1 ≤ (band d).scale E N v)
    {n : ℕ} (hn : 2 ≤ n) {D : ℝ}
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hM : M ∈ lkDecaySet d E N n v τ D)
    {Φ B : ℝ} (hΦ : 0 ≤ Φ) (hB : 0 ≤ B)
    (hΞprod : ∀ m, 2 ≤ m → m ≤ n →
      xiLKM d E N v M m * xiLKM d E N v M (n - m + 2) * ((band d).scale E N v)⁻¹ ≤ Φ)
    (hΞm : ∀ m, 2 ≤ m → m ≤ n → xiLKM d E N v M m ≤ B)
    (I : LoopIdx (ZMod (d.L N))) (hI : I.WF) (hIlen : I.length = n) :
    ‖primBil (d.L N) (d.W N)
        (fun J => gloop (d.L N) (d.W N) M (zt E v) J - (band d).Kval E N v J)
        (fun J => gloop (d.L N) (d.W N) M (zt E v) J - (band d).Kval E N v J) I‖
      ≤ 4 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹ * Φ
          * ((band d).scale E N v)⁻¹ ^ n
        + (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D) * B := by
  have h3L := d.three_le_L N
  have hℓpos := ell_mul_rpow_pos d N v hv0 hv1 τ
  have hApos : 0 < (band d).scale E N v := lt_of_lt_of_le one_pos hA1
  have hDfun : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖gloop (d.L N) (d.W N) M (zt E v) J - (band d).Kval E N v J‖
        ≤ xiLKM d E N v M J.length * ((band d).scale E N v)⁻¹ ^ J.length := by
    intro J hJ _h2 _hlen
    have hle := norm_sub_le_lkMaxM d E N v M J hJ rfl
    have heq : xiLKM d E N v M J.length * ((band d).scale E N v)⁻¹ ^ J.length
        = lkMaxM d E N v M J.length := by
      rw [xiLKM, mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hApos), one_pow, mul_one]
    rw [heq]; exact hle
  have hDd : Decay.LoopDecay (d.L N) n ((band d).ell N v * (d.W N : ℝ) ^ τ) ((d.W N : ℝ) ^ (-D))
      (fun J => gloop (d.L N) (d.W N) M (zt E v) J - (band d).Kval E N v J) := hM
  have hPrim := Decay.norm_primBil_sub_le (d.L N) h3L (d.W N) (I := I) hI
    (A := (band d).scale E N v) (ℓ := (band d).ell N v * (d.W N : ℝ) ^ τ)
    (δ := (d.W N : ℝ) ^ (-D)) (Φ := Φ) (B := B)
    (X := fun m => xiLKM d E N v M m) hA1 hℓpos (by positivity) hΦ hB
    (fun J hJ h2 hlen => hDfun J hJ h2 (by rw [hIlen] at hlen; exact hlen))
    (fun m h2 hm => by rw [hIlen]; exact hΞprod m h2 (by rw [hIlen] at hm; exact hm))
    (fun m h2 hm => hΞm m h2 (by rw [hIlen] at hm; exact hm))
    (by rw [hIlen]; exact hDd)
  rw [hIlen] at hPrim
  refine hPrim.trans ?_
  have hratio := W_mul_ell_rpow_add_one_div_scale_le d hE N hv0 hv1 hτ
  have hfactor_nonneg : (0 : ℝ) ≤ 2 * Real.exp 1 * (n : ℝ) ^ 2 * Φ
      * ((band d).scale E N v)⁻¹ ^ n := by positivity
  refine add_le_add ?_ le_rfl
  calc 2 * Real.exp 1 * (n : ℝ) ^ 2 * Φ
        * ((d.W N : ℝ) * ((band d).ell N v * (d.W N : ℝ) ^ τ + 1) / (band d).scale E N v)
        * ((band d).scale E N v)⁻¹ ^ n
      = (2 * Real.exp 1 * (n : ℝ) ^ 2 * Φ * ((band d).scale E N v)⁻¹ ^ n)
          * ((d.W N : ℝ) * ((band d).ell N v * (d.W N : ℝ) ^ τ + 1)
            * ((band d).scale E N v)⁻¹) := by rw [div_eq_mul_inv]; ring
    _ ≤ (2 * Real.exp 1 * (n : ℝ) ^ 2 * Φ * ((band d).scale E N v)⁻¹ ^ n)
          * (2 * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹) :=
        mul_le_mul_of_nonneg_left hratio hfactor_nonneg
    _ = 4 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹ * Φ
          * ((band d).scale E N v)⁻¹ ^ n := by ring

end PrimBil

/-! ### (T3) `norm_eGterm_le`, (5.80) -/

section EGTerm

/-- **`norm_eGterm_le`**: (5.80), `eGterm_v,σ(M)` at a fixed matrix `M` and time `v`, from
`decaySet` (the `L` half of (5.75), which supplies both the decay hypothesis for the `Y`-factor
and the literal `δ = W^{-D}`), the sharp `Ξ₁(M)` bound and `Ξ^{(L)}_{n+1}(M)`.  Bridged via
`RBM.DriftDef.eGterm_eq_eG` (`Gauss.eGterm` **is** `Decay.eG` with `X = L - K`, `Y = L`). -/
theorem norm_eGterm_le {E : ℝ} (hE : |E| < 2) (N : ℕ) {v τ : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hτ : 0 < τ) (hA1 : 1 ≤ (band d).scale E N v)
    {n : ℕ} {D : ℝ}
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hM : M ∈ decaySet d E N (n + 1) v τ D)
    {Ξ1 Φ : ℝ} (hΞ1_0 : 0 ≤ Ξ1) (hΦ0 : 0 ≤ Φ)
    (hΞ1 : xiLKM d E N v M 1 ≤ Ξ1)
    (hΦ : xiLM d E N v M (n + 1) ≤ Φ)
    (I : LoopIdx (ZMod (d.L N))) (hI : I.WF) (hIlen : I.length = n) :
    ‖eGterm (d.L N) (d.W N) (mSigma E) M (zt E v) I‖
      ≤ 4 * Real.exp 1 * (n : ℝ) * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹ * Ξ1 * Φ
          * ((band d).scale E N v)⁻¹ ^ n
        + (n : ℝ) * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D) * Ξ1 := by
  have h3L := d.three_le_L N
  have hℓpos := ell_mul_rpow_pos d N v hv0 hv1 τ
  have hApos : 0 < (band d).scale E N v := lt_of_lt_of_le one_pos hA1
  have hbridge : eGterm (d.L N) (d.W N) (mSigma E) M (zt E v) I
      = Decay.eG (d.L N) (d.W N)
          (fun J => gloop (d.L N) (d.W N) M (zt E v) J - (band d).Kval E N v J)
          (gloop (d.L N) (d.W N) M (zt E v)) I :=
    DriftDef.eGterm_eq_eG (mSigma E) v M (zt E v) I
  rw [hbridge]
  have hX : ∀ (s : Bool) (a : ZMod (d.L N)),
      ‖gloop (d.L N) (d.W N) M (zt E v) (⟨[s], [a]⟩ : LoopIdx (ZMod (d.L N)))
          - (band d).Kval E N v (⟨[s], [a]⟩ : LoopIdx (ZMod (d.L N)))‖
        ≤ Ξ1 * ((band d).scale E N v)⁻¹ := by
    intro s a
    have hle := norm_sub_le_lkMaxM d E N v M (⟨[s], [a]⟩ : LoopIdx (ZMod (d.L N))) rfl rfl
    have heq : xiLKM d E N v M 1 = lkMaxM d E N v M 1 * (band d).scale E N v := by
      rw [xiLKM]; ring
    have hxi1 : lkMaxM d E N v M 1 * (band d).scale E N v ≤ Ξ1 := by rw [← heq]; exact hΞ1
    have hfin : lkMaxM d E N v M 1 ≤ Ξ1 * ((band d).scale E N v)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hApos).2 hxi1
    exact hle.trans hfin
  have hY : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length = n + 1 →
      ‖gloop (d.L N) (d.W N) M (zt E v) J‖ ≤ Φ * ((band d).scale E N v)⁻¹ ^ n := by
    intro J hJ hlen
    have haeq : J.a.length = n + 1 := hlen
    have hσeq : J.σ.length = n + 1 := (show J.σ.length = J.a.length from hJ).trans haeq
    have hlm := norm_gloop_le_loopMax (L := d.L N) (W := d.W N) (H := M) (z := zt E v)
      J hσeq haeq
    have hxiM : xiLM d E N v M (n + 1)
        = loopMax (d.L N) (d.W N) M (zt E v) (n + 1) * (band d).scale E N v ^ n := by
      rw [xiLM, loopXi, Nat.add_sub_cancel]
    have hxin : loopMax (d.L N) (d.W N) M (zt E v) (n + 1) * (band d).scale E N v ^ n ≤ Φ := by
      rw [← hxiM]; exact hΦ
    have hloopbound : loopMax (d.L N) (d.W N) M (zt E v) (n + 1)
        ≤ Φ * ((band d).scale E N v)⁻¹ ^ n := by
      rw [inv_pow, ← div_eq_mul_inv]
      exact (le_div_iff₀ (by positivity : (0 : ℝ) < (band d).scale E N v ^ n)).2 hxin
    exact hlm.trans hloopbound
  have hYd : Decay.LoopDecay (d.L N) (n + 1) ((band d).ell N v * (d.W N : ℝ) ^ τ)
      ((d.W N : ℝ) ^ (-D)) (gloop (d.L N) (d.W N) M (zt E v)) := hM
  have hEG := Decay.norm_eG_le (d.L N) h3L (d.W N) (I := I) hI
    (X := fun J => gloop (d.L N) (d.W N) M (zt E v) J - (band d).Kval E N v J)
    (Y := gloop (d.L N) (d.W N) M (zt E v))
    (A := (band d).scale E N v) (ℓ := (band d).ell N v * (d.W N : ℝ) ^ τ)
    (δ := (d.W N : ℝ) ^ (-D)) (Ξ₂ := Ξ1) (Φ := Φ)
    hA1 hℓpos (by positivity) hΞ1_0
    hX
    (fun J hJ hlen => by rw [hIlen]; exact hY J hJ (by rw [hIlen] at hlen; exact hlen))
    (by rw [hIlen]; exact hYd)
  rw [hIlen] at hEG
  refine hEG.trans ?_
  have hratio := W_mul_ell_rpow_add_one_div_scale_le d hE N hv0 hv1 hτ
  have hfactor_nonneg : (0 : ℝ) ≤ 2 * Real.exp 1 * (n : ℝ) * Ξ1 * Φ
      * ((band d).scale E N v)⁻¹ ^ n := by positivity
  refine add_le_add ?_ le_rfl
  calc 2 * Real.exp 1 * (n : ℝ) * Ξ1 * Φ
        * ((d.W N : ℝ) * ((band d).ell N v * (d.W N : ℝ) ^ τ + 1) / (band d).scale E N v)
        * ((band d).scale E N v)⁻¹ ^ n
      = (2 * Real.exp 1 * (n : ℝ) * Ξ1 * Φ * ((band d).scale E N v)⁻¹ ^ n)
          * ((d.W N : ℝ) * ((band d).ell N v * (d.W N : ℝ) ^ τ + 1)
            * ((band d).scale E N v)⁻¹) := by rw [div_eq_mul_inv]; ring
    _ ≤ (2 * Real.exp 1 * (n : ℝ) * Ξ1 * Φ * ((band d).scale E N v)⁻¹ ^ n)
          * (2 * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹) :=
        mul_le_mul_of_nonneg_left hratio hfactor_nonneg
    _ = 4 * Real.exp 1 * (n : ℝ) * (d.W N : ℝ) ^ τ * (etaT E v)⁻¹ * Ξ1 * Φ
          * ((band d).scale E N v)⁻¹ ^ n := by ring

end EGTerm

/-! ### (T4) `goodSet514` -/

section GoodSet

variable (E : ℝ) (N : ℕ) (v : ℝ) (n : ℕ) (ε Λ Φ τ D ℓs : ℝ)

/-- A generic countable-guarded intersection is measurable (mirrors `measurableSet_decaySet`'s
`⋂ (if …) …` technique, here over the countable index `ℕ` instead of `LoopIdx`). -/
theorem measurableSet_forall_le {N : ℕ} (f : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ)
    (hf : ∀ m, Measurable (f m)) (p : ℕ → Prop) [DecidablePred p] (g : ℕ → ℝ) :
    MeasurableSet {M : Matrix (d.Idx N) (d.Idx N) ℂ | ∀ m, p m → f m M ≤ g m} := by
  have heq : {M : Matrix (d.Idx N) (d.Idx N) ℂ | ∀ m, p m → f m M ≤ g m}
      = ⋂ m : ℕ, if p m then {M : Matrix (d.Idx N) (d.Idx N) ℂ | f m M ≤ g m} else Set.univ := by
    ext M
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h m
      by_cases hpm : p m
      · rw [if_pos hpm]; exact h m hpm
      · rw [if_neg hpm]; trivial
    · intro h m hpm
      have := h m
      rwa [if_pos hpm] at this
  rw [heq]
  refine MeasurableSet.iInter fun m => ?_
  split_ifs
  · exact measurableSet_le (hf m) measurable_const
  · exact MeasurableSet.univ

/-- **`goodSet514`**: the fixed-time matrix set of the conditions of Lemma 5.14, all at the
single time `v`: the intersection of
`Ξ^{(L)}_{2n+2} ≤ N^εΛ`; `Ξ_m ≤ N^εΦ` for `1 ≤ m < n` (the range of `Step3.Lemma514`);
`Ξ_m Ξ_{n-m+2}/A_v ≤ N^εΦ` for `2 ≤ m ≤ n`; `Ξ^{(L)}_{n+1} ≤ N^εΦ`; the sharp `Ξ₁ ≤ N^ε`;
`decaySet` **and** `lkDecaySet` (both halves of (5.75), needed by `norm_eGterm_le` and
`norm_primBil_le514` respectively); `eq557Set`, `eq273Set`.  The decay/(2.73) loop-length cap is
fixed to `2n+2`, the largest length occurring among the other conditions. -/
def goodSet514 : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | xiLM d E N v M (2 * n + 2) ≤ (N : ℝ) ^ ε * Λ}
    ∩ {M | ∀ m, 1 ≤ m → m < n → xiLKM d E N v M m ≤ (N : ℝ) ^ ε * Φ}
    ∩ {M | ∀ m, 2 ≤ m → m ≤ n →
        xiLKM d E N v M m * xiLKM d E N v M (n - m + 2) / (band d).scale E N v
          ≤ (N : ℝ) ^ ε * Φ}
    ∩ {M | xiLM d E N v M (n + 1) ≤ (N : ℝ) ^ ε * Φ}
    ∩ {M | xiLKM d E N v M 1 ≤ (N : ℝ) ^ ε}
    ∩ decaySet d E N (2 * n + 2) v τ D
    ∩ lkDecaySet d E N (2 * n + 2) v τ D
    ∩ eq557Set d E N v ℓs τ
    ∩ eq273Set d E N (2 * n + 2) v ℓs τ

theorem measurableSet_goodSet514 : MeasurableSet (goodSet514 d E N v n ε Λ Φ τ D ℓs) := by
  classical
  refine (((((((MeasurableSet.inter ?_ ?_).inter ?_).inter ?_).inter ?_).inter ?_).inter ?_).inter
    ?_) |>.inter ?_
  · exact measurableSet_le (measurable_xiLM d E N v (2 * n + 2)) measurable_const
  · exact measurableSet_forall_le d (fun m M => xiLKM d E N v M m)
      (fun m => measurable_xiLKM d E N v m) (fun m => 1 ≤ m ∧ m < n) (fun _ => (N : ℝ) ^ ε * Φ)
      |>.congr (by ext M; simp [and_imp])
  · exact measurableSet_forall_le d
      (fun m M => xiLKM d E N v M m * xiLKM d E N v M (n - m + 2) / (band d).scale E N v)
      (fun m => ((measurable_xiLKM d E N v m).mul (measurable_xiLKM d E N v (n - m + 2))).div_const
        _)
      (fun m => 2 ≤ m ∧ m ≤ n) (fun _ => (N : ℝ) ^ ε * Φ)
      |>.congr (by ext M; simp [and_imp])
  · exact measurableSet_le (measurable_xiLM d E N v (n + 1)) measurable_const
  · exact measurableSet_le (measurable_xiLKM d E N v 1) measurable_const
  · exact measurableSet_decaySet d E N (2 * n + 2) v τ D
  · exact measurableSet_lkDecaySet d E N (2 * n + 2) v τ D
  · exact measurableSet_eq557Set d E N v ℓs τ
  · exact measurableSet_eq273Set d E N (2 * n + 2) v ℓs τ

/-- **`goodSet514` supplies the decay inputs of (T2) and (T3):** membership gives
`decaySet (n+1)` (the input of `norm_eGterm_le`) and `lkDecaySet n` (the input of
`norm_primBil_le514`), by monotonicity of `LoopDecay` in the length cap. -/
theorem goodSet514_decay {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M ∈ goodSet514 d E N v n ε Λ Φ τ D ℓs) :
    M ∈ decaySet d E N (n + 1) v τ D ∧ M ∈ lkDecaySet d E N n v τ D := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hdec⟩, hlk⟩, _⟩, _⟩ := hM
  exact ⟨Decay.LoopDecay.mono (d.L N) hdec (by omega) le_rfl le_rfl,
    Decay.LoopDecay.mono (d.L N) hlk (by omega) le_rfl le_rfl⟩

end GoodSet

/-! ### (T5) The grid `HighProb` of `goodSet514`: the union bound and the `Ξ₁` conversion -/

section HighProbGoodSet

/-- **Finitely many `HighProb` events, indexed by a `Finset`, hold simultaneously w.h.p.**
(the finite case of `HighProb.biInter`/`HighProb.inter`, by `Finset` induction). Used to combine
the `∀ m, … → StochDom …` premises (finitely many `m`, since `n` is fixed) into a single
`HighProb`. -/
theorem highProb_biInter_finset {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : Finset ι) (Ξ : ι → ℕ → Set Ω) (h : ∀ i ∈ F, HighProb P (Ξ i)) :
    HighProb P (fun N => ⋂ i ∈ F, Ξ i N) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have heq : (fun N => ⋂ i ∈ (∅ : Finset ι), Ξ i N) = fun _ => Set.univ := by
      funext N; simp
    rw [heq]
    exact HighProb.of_eventually_univ (Filter.Eventually.of_forall fun _ ω => Set.mem_univ ω)
  | insert a s ha ih =>
    have heq : (fun N => ⋂ i ∈ insert a s, Ξ i N) = fun N => Ξ a N ∩ ⋂ i ∈ s, Ξ i N := by
      funext N; rw [Finset.set_biInter_insert]
    rw [heq]
    exact HighProb.inter (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Conversion of the output to the sharp `Ξ₁` of (5.76):** if `A_v · |(L-K)_{v,σ,a}(M)|`
is `≤ b` for every length-one loop `(σ, a)`, then
`Ξ^{(L-K)}_1(M) = A_v · max_{σ,a} |(L-K)_{v,σ,a}(M)| ≤ b`. -/
theorem xiLKM_one_le_of_forall {E : ℝ} {N : ℕ} {v : ℝ} (hv1 : v ≤ 1)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ u : LoopData (d.L N) 1, (band d).scale E N v * lkErrMat d E N v M u.idx ≤ b) :
    xiLKM d E N v M 1 ≤ b := by
  have hA := (band d).scale_nonneg E N hv1
  rw [xiLKM, pow_one, lkMaxM, Real.iSup_mul_of_nonneg hA]
  refine Real.iSup_le (fun u => ?_) hb
  rw [mul_comm]
  exact h u

end HighProbGoodSet

end RBM.Gauss.Grid

end

