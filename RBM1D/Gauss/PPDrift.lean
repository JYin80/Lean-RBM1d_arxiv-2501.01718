/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Kernel
import RBM1D.Hierarchy.KernelDecay
import RBM1D.Hierarchy.Dynamics
import RBM1D.Gauss.Hierarchy
import RBM1D.Propagator.Edges
import RBM1D.Loop.Split
import RBM1D.Gauss.LoopLipschitz

/-!
# The deterministic `n = 2`, `σ = (+,+)` drift and kernel bounds

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (2.47), (2.52), (5.13)-(5.20) and Lemma 5.10, (5.79)-(5.80)
, all specialized to a `2`-loop of constant charge `σ_pp = (+,+)`.

Route: both edges of `σ_pp` are the *short* edge
`ξ = m²`, so the evolution kernel `U_{u,v,σ_pp}` is bounded in `max→max` norm by a constant
`C_U(κ)` depending only on the spectral gap `κ` (`|E| ≤ 2 - κ`), uniformly for `0 ≤ u ≤ v < 1`
(`RBM.edgeKer_pp_row_le`, via `RBM.sum_norm_edgeKer_sub_one_le_short`, `KernelDecay.lean`,
and the short-edge gap `RBM.sqrt_le_norm_one_sub_short`). The `n = 2` drift terms of (5.15) --
the quadratic gluing term `primBil(A,A)` of (5.13) and the `Ẽ`-term `eGterm` of (2.47) -- are
bounded by unfolding `RBM.primBil`/`RBM.Gauss.eGterm` at loop length `2` (the only surviving
cut is `(k,l) = (1,2)`, `RBM.primBil_pp_eq`/`RBM.Gauss.eGterm_pp_eq`) and combining the
row-stochastic kernel `S^{(B)}` (`RBM.sum_norm_SB_row`, nearest-neighbour support) with a
window/tail split of the decaying tensor (`RBM.winInd`, `RBM.sum_winInd_le`,
`RBM.norm_le_winInd_add`, `RBM.norm_sum_SB_decayLeft`).

## Main results

* `RBM.CU`, `RBM.edgeKer_pp_row_le`   : the short-edge row bound, depending on `κ` only
* `RBM.sum_norm_Uker_pp_le` (sum form) : `Σ_b ‖U_{u,v,σ_pp}(a,b)‖ ≤ C_U(κ)²`
* `RBM.norm_Uker_pp_apply_le` (max→max form)
* `RBM.norm_primBil_pp_le` ((5.79) at `n = 2`)
* `RBM.Gauss.norm_eGterm_pp_le` ((5.80) at `n = 2`)
* compiled nondegenerate witnesses for `norm_primBil_pp_le`/`norm_eGterm_pp_le`, at the end of
  the file

## Deviations

* The edge parameter is written `(mE E) ^ 2` (both edges of `σ_pp`); `RBM.xiOf_pp_eq` records
  that this is literally `xiOf (mSigma E) ![true,true] i` for every `i`, so the kernel bounds are
  given in the paper's `xiOf` form and reduced internally.
* `Wℓ_v = A_v / η_v` (the paper's `scale`, `RBM1D/Flow/Hypotheses.lean`) is carried as an
  explicit hypothesis `hWℓ`, since the two drift bounds are stated deterministically, at a fixed
  matrix `M` and without reference to a `Band`.
-/

noncomputable section

namespace RBM

open Matrix Finset

/-! ### `σ_pp = (+,+)`: both edges are the short edge `m²` -/

section XiPP

/-- **The edge parameter of `σ_pp = (+,+)` is literally `m²` at every position.** -/
theorem xiOf_pp_eq (E : ℝ) (i : Fin 2) :
    xiOf (mSigma E) (![true, true] : Fin 2 → Bool) i = (mE E) ^ 2 := by
  fin_cases i <;> simp [xiOf, mSigma, sq]

end XiPP

/-! ### (T1, PP-4) : the bounded short-edge kernel -/

section PPKernel

/-- **The short-edge row-bound constant, depending on `κ` only.** -/
def CU (κ : ℝ) : ℝ := 1 + 2 * cTwo52 * (1 / cZero + 2) / Real.sqrt κ

/-- **The row bound of the `(+,+)` edge kernel, uniform in `u`, `v`, `L`; depends on `κ`
only.** Route: `sum_norm_edgeKer_sub_one_le_short` (`KernelDecay.lean`) plus the short-edge
gap `|1 - t m²| ≥ √κ` (`sqrt_le_norm_one_sub_short`). -/
theorem edgeKer_pp_row_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {E κ u v : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1) (x : ZMod L) :
    ∑ c : ZMod L, ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) x c‖ ≤ CU κ := by
  have hv0 : (0 : ℝ) ≤ v := hu0.trans huv
  have hE2 : |E| ≤ 2 := hE.trans (by linarith)
  have hξ1 : ‖(mE E) ^ 2‖ ≤ 1 := by rw [norm_pow, norm_mE hE2]; norm_num
  have hκ' : Real.sqrt κ ≤ ‖1 - (v : ℂ) * (mE E) ^ 2‖ :=
    sqrt_le_norm_one_sub_short hκ0 hκ1 hE hv0 hv1.le
  have hΞ := sum_norm_edgeKer_sub_one_le_short L hL huv hv0 hv1 hξ1 (Real.sqrt_pos.mpr hκ0) hκ' x
  have hident : ∀ c, edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) x c
      = (1 : Matrix (ZMod L) (ZMod L) ℂ) x c
        + (edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) - 1) x c := by
    intro c; rw [Matrix.sub_apply]; ring
  have hstep : ∑ c : ZMod L, ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) x c‖
      ≤ ∑ c : ZMod L, ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) x c‖
        + ∑ c : ZMod L, ‖(edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) - 1) x c‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [hident c]
    exact norm_add_le _ _
  rw [sum_norm_one_apply] at hstep
  refine hstep.trans ?_
  have hcSnn : (0 : ℝ) ≤ 2 * cTwo52 * (1 / cZero + 2) / Real.sqrt κ := by
    have := cTwo52_pos; have := cZero_pos
    positivity
  have hle1 : (v - u) ≤ 1 := by linarith
  have hbound : (v - u) * (2 * cTwo52 * (1 / cZero + 2) / Real.sqrt κ)
      ≤ 1 * (2 * cTwo52 * (1 / cZero + 2) / Real.sqrt κ) :=
    mul_le_mul_of_nonneg_right hle1 hcSnn
  unfold CU
  nlinarith [hΞ.trans hbound]

/-- **Sum form**: `Σ_b ‖U_{u,v,σ_pp}(a,b)‖ ≤ C_U(κ)²`, for `0 ≤ u ≤ v < 1` and
`|E| ≤ 2 - κ`. Route: `sum_norm_edgeKer_sub_one_le_short` plus the short-edge gap, then the
product-sum interchange `sum_prod_pi`. Constants depend on `κ` only. -/
theorem sum_norm_Uker_pp_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {E κ u v : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (a : LoopArg L 2) :
    ∑ b : LoopArg L 2,
      ‖∏ i : Fin 2, edgeKer L (xiOf (mSigma E) (![true, true] : Fin 2 → Bool) i)
          (u : ℂ) (v : ℂ) (a i) (b i)‖
      ≤ CU κ ^ 2 := by
  simp_rw [xiOf_pp_eq]
  have hrow : ∀ i : Fin 2, ∑ c : ZMod L, ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) c‖
      ≤ CU κ := fun i => edgeKer_pp_row_le hL hκ0 hκ1 hE hu0 huv hv1 (a i)
  calc ∑ b : LoopArg L 2, ‖∏ i : Fin 2, edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) (b i)‖
      = ∑ b : LoopArg L 2, ∏ i : Fin 2, ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) (b i)‖ := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [norm_prod]
    _ = ∏ i : Fin 2, ∑ c : ZMod L, ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) c‖ :=
        sum_prod_pi L (fun i c => ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) c‖)
    _ ≤ ∏ _i : Fin 2, CU κ :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (fun i _ => hrow i)
    _ = CU κ ^ 2 := by simp

/-- **(T1, PP-4, max→max form)**: `‖U_{u,v,σ_pp} X‖_max ≤ C_U(κ) ‖X‖_max`. Same row bound as
`sum_norm_Uker_pp_le`, threaded through `Uker` exactly as in `RBM.norm_Uker_apply_le`
(`Kernel.lean`), with the sharp short-edge row bound in place of the crude one. -/
theorem norm_Uker_pp_apply_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {E κ u v : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1) {M : ℝ}
    (hM0 : 0 ≤ M) {A : LoopArg L 2 → ℂ} (hA : ∀ b, ‖A b‖ ≤ M) (a : LoopArg L 2) :
    ‖Uker L (xiOf (mSigma E) (![true, true] : Fin 2 → Bool)) (u : ℂ) (v : ℂ) A a‖
      ≤ CU κ ^ 2 * M := by
  have hrow : ∀ i : Fin 2, ∑ c : ZMod L, ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) c‖
      ≤ CU κ := fun i => edgeKer_pp_row_le hL hκ0 hκ1 hE hu0 huv hv1 (a i)
  have hstep : (∑ b : LoopArg L 2,
      ∏ i : Fin 2, ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) (b i)‖) ≤ CU κ ^ 2 := by
    rw [sum_prod_pi L (fun i c => ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) c‖)]
    calc (∏ i : Fin 2, ∑ c : ZMod L, ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) c‖)
        ≤ ∏ _i : Fin 2, CU κ :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (fun i _ => hrow i)
      _ = CU κ ^ 2 := by simp
  have hgoal : ‖Uker L (fun i : Fin 2 => (mE E) ^ 2) (u : ℂ) (v : ℂ) A a‖ ≤ CU κ ^ 2 * M := by
    calc ‖Uker L (fun _ : Fin 2 => (mE E) ^ 2) (u : ℂ) (v : ℂ) A a‖
        = ‖∑ b : LoopArg L 2,
            (∏ i : Fin 2, edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) (b i)) * A b‖ := by
          rw [Uker_apply]
      _ ≤ ∑ b : LoopArg L 2,
          ‖(∏ i : Fin 2, edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) (b i)) * A b‖ :=
          norm_sum_le _ _
      _ ≤ ∑ b : LoopArg L 2,
          (∏ i : Fin 2, ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) (b i)‖) * M := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, norm_prod]
          exact mul_le_mul_of_nonneg_left (hA b) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = (∑ b : LoopArg L 2,
          ∏ i : Fin 2, ‖edgeKer L ((mE E) ^ 2) (u : ℂ) (v : ℂ) (a i) (b i)‖) * M := by
          rw [← Finset.sum_mul]
      _ ≤ CU κ ^ 2 * M := mul_le_mul_of_nonneg_right hstep hM0
  have hξeq : (xiOf (mSigma E) (![true, true] : Fin 2 → Bool)) = fun _ : Fin 2 => (mE E) ^ 2 := by
    funext i; exact xiOf_pp_eq E i
  rwa [hξeq]

end PPKernel

/-! ### A window/tail split of a decaying scalar function -/

section WindowSplit

variable {L : ℕ} [NeZero L]

/-- **The pointwise window/tail split**: a function bounded by `B` everywhere and by `δ` outside
a window of radius `ℓ'` around `p` is bounded by `winInd L ℓ' (c - p) * B + δ` everywhere. -/
theorem norm_le_winInd_add {ℓ' δ B : ℝ} (hδ0 : 0 ≤ δ) {f : ZMod L → ℂ} {p : ZMod L}
    (hflat : ∀ c, ‖f c‖ ≤ B) (hdecay : ∀ c, ℓ' ≤ (zdist L (c - p) : ℝ) → ‖f c‖ ≤ δ) (c : ZMod L) :
    ‖f c‖ ≤ winInd L ℓ' (c - p) * B + δ := by
  unfold winInd
  split_ifs with h
  · nlinarith [hflat c]
  · push Not at h
    nlinarith [hdecay c h]

/-- **The core two-index estimate behind (5.79)/(5.80).** `f` is `(ℓ', δ)`-decaying around the
anchor `p` and bounded by `Bf` everywhere; `g` is bounded by `Bg` everywhere. The `S^{(B)}`-sum
is row- and column-stochastic (`sum_norm_SB_row`, `SB_transpose`), so it costs nothing; the
`x`-sum is confined to the window by the decay of `f` (`norm_le_winInd_add`, `sum_winInd_le`).
This is the abstract shape of both (5.79) (`f = g = ` the length-2 `L-K` tensor) and (5.80)
(`f = ` the length-3 `L`-loop, `g = ` the length-1 `L-K` trace factor, after `Finset.sum_comm`). -/
theorem norm_sum_SB_decayLeft (hL : 3 ≤ L) {ℓ' δ Bf Bg : ℝ} (hℓ'0 : 0 < ℓ') (hℓ'1 : 1 ≤ 2 * ℓ')
    (hδ0 : 0 ≤ δ) (hBg0 : 0 ≤ Bg) {f g : ZMod L → ℂ} {p : ZMod L} (hfflat : ∀ x, ‖f x‖ ≤ Bf)
    (hfdecay : ∀ x, ℓ' ≤ (zdist L (x - p) : ℝ) → ‖f x‖ ≤ δ) (hgflat : ∀ y, ‖g y‖ ≤ Bg) :
    ‖∑ x : ZMod L, ∑ y : ZMod L, f x * SB L x y * g y‖
      ≤ Bg * (Bf * (6 * Real.exp 1 * ℓ') + (L : ℝ) * δ) := by
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hfflat p)
  have hfbound : ∀ x, ‖f x‖ ≤ winInd L ℓ' (x - p) * Bf + δ :=
    fun x => norm_le_winInd_add hδ0 hfflat hfdecay x
  have hinner : ∀ x : ZMod L, ‖∑ y : ZMod L, f x * SB L x y * g y‖ ≤ ‖f x‖ * Bg := by
    intro x
    calc ‖∑ y : ZMod L, f x * SB L x y * g y‖
        ≤ ∑ y : ZMod L, ‖f x * SB L x y * g y‖ := norm_sum_le _ _
      _ = ‖f x‖ * ∑ y : ZMod L, ‖SB L x y‖ * ‖g y‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [norm_mul, norm_mul, mul_assoc]
      _ ≤ ‖f x‖ * ∑ y : ZMod L, ‖SB L x y‖ * Bg :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hgflat y) (norm_nonneg _))
            (norm_nonneg _)
      _ = ‖f x‖ * ((∑ y : ZMod L, ‖SB L x y‖) * Bg) := by rw [Finset.sum_mul]
      _ = ‖f x‖ * Bg := by rw [sum_norm_SB_row hL x]; ring
  have houter : ‖∑ x : ZMod L, ∑ y : ZMod L, f x * SB L x y * g y‖ ≤ ∑ x : ZMod L, ‖f x‖ * Bg :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => hinner x)
  refine houter.trans ?_
  have hwin : 2 * Real.exp 1 * (ℓ' + 1) ≤ 6 * Real.exp 1 * ℓ' := by
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    nlinarith [mul_nonneg he.le (by linarith [hℓ'1] : (0 : ℝ) ≤ 4 * ℓ' - 2)]
  have hsumf : ∑ x : ZMod L, ‖f x‖ ≤ Bf * (6 * Real.exp 1 * ℓ') + (L : ℝ) * δ := by
    have hwinsum := sum_winInd_le L hℓ'0 p
    calc ∑ x : ZMod L, ‖f x‖
        ≤ ∑ x : ZMod L, (winInd L ℓ' (x - p) * Bf + δ) :=
          Finset.sum_le_sum fun x _ => hfbound x
      _ = (∑ x : ZMod L, winInd L ℓ' (x - p)) * Bf + (L : ℝ) * δ := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, Finset.card_univ,
            ZMod.card, nsmul_eq_mul]
      _ ≤ (2 * Real.exp 1 * (ℓ' + 1)) * Bf + (L : ℝ) * δ := by
          linarith [mul_le_mul_of_nonneg_right hwinsum hBf0]
      _ ≤ (6 * Real.exp 1 * ℓ') * Bf + (L : ℝ) * δ := by
          linarith [mul_le_mul_of_nonneg_right hwin hBf0]
      _ = Bf * (6 * Real.exp 1 * ℓ') + (L : ℝ) * δ := by ring
  calc ∑ x : ZMod L, ‖f x‖ * Bg = (∑ x : ZMod L, ‖f x‖) * Bg := by rw [Finset.sum_mul]
    _ ≤ (Bf * (6 * Real.exp 1 * ℓ') + (L : ℝ) * δ) * Bg :=
        mul_le_mul_of_nonneg_right hsumf hBg0
    _ = Bg * (Bf * (6 * Real.exp 1 * ℓ') + (L : ℝ) * δ) := by ring

end WindowSplit

/-! ### Bridging `List.ofFn` of explicit `2`- and `3`-vectors -/

section OfFnBridge

theorem ofFn_pp2 {L : ℕ} (x y : ZMod L) :
    List.ofFn (![x, y] : LoopArg L 2) = [x, y] := by
  simp [List.ofFn_succ]

theorem ofFn_pp3 {L : ℕ} (x y w : ZMod L) :
    List.ofFn (![x, y, w] : LoopArg L 3) = [x, y, w] := by
  simp [List.ofFn_succ]

end OfFnBridge

/-! ### (T2) : `norm_primBil_pp_le`, (5.79) at `n = 2` -/

section PrimBilPP

variable {L : ℕ} [NeZero L]

/-- `primBil` at the constant `2`-loop `(σ_pp, (a1,a2))`: the only surviving cut is `(k,l) =
(1,2)` (Def. 2.10, `LoopIdx.cutGlueL/cutGlueR`), so the double sum over `k,l` collapses. -/
theorem primBil_pp_eq (W : ℕ) (F G : LoopIdx (ZMod L) → ℂ) (a1 a2 : ZMod L) :
    primBil L W F G ⟨[true, true], [a1, a2]⟩
      = (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L,
          F ⟨[true, true], [x, a2]⟩ * SB L x y * G ⟨[true, true], [a1, y]⟩ := by
  have hlen : (⟨[true, true], [a1, a2]⟩ : LoopIdx (ZMod L)).length = 2 := rfl
  simp only [primBil, hlen, show Finset.Icc (1 : ℕ) 2 = ({1, 2} : Finset ℕ) from by decide]
  rw [Finset.sum_insert (by decide)]
  simp [show Finset.Ioc (1 : ℕ) 2 = ({2} : Finset ℕ) from by decide,
    show Finset.Ioc (2 : ℕ) 2 = (∅ : Finset ℕ) from by decide,
    LoopIdx.cutGlueL, LoopIdx.cutGlueR, List.take, List.drop]

/-- **(T2)**: (5.79) at `n = 2`. `A` (standing for `gloop - Kval` at `σ_pp`) is bounded by
`θ A_v^{-2}` everywhere and `(ℓ_v Kd, δ)`-fast-decaying; then `‖primBil(A,A)(I)‖ ≤ C Kd θ² A_v^{-3}
η_v^{-1} + C W L² δ θ A_v^{-2}`, `C = 6e`. Route: `primBil_pp_eq`, `norm_sum_SB_decayLeft`
(nearest-neighbour `S^{(B)}`, window/tail split), `Wℓ_v = A_v/η_v`. -/
theorem norm_primBil_pp_le (hL : 3 ≤ L) (W : ℕ) (A : LoopIdx (ZMod L) → ℂ) (a1 a2 : ZMod L)
    {ℓ Kd δ θ Av ηv : ℝ} (hKd1 : 1 ≤ Kd) (hℓ2 : (1 : ℝ) / 2 ≤ ℓ) (hδ0 : 0 ≤ δ) (hθ0 : 0 ≤ θ)
    (hAv0 : 0 < Av) (hηv0 : 0 < ηv) (hWℓ : (W : ℝ) * ℓ = Av / ηv)
    (hAdecay : FastDecay L (ℓ * Kd) δ (fun v : LoopArg L 2 => A ⟨[true, true], List.ofFn v⟩))
    (hAbound : ∀ v : LoopArg L 2, ‖A ⟨[true, true], List.ofFn v⟩‖ ≤ θ * Av⁻¹ ^ 2) :
    ‖primBil L W A A ⟨[true, true], [a1, a2]⟩‖
      ≤ 6 * Real.exp 1 * Kd * θ ^ 2 * Av⁻¹ ^ 3 * ηv⁻¹
        + 6 * Real.exp 1 * (W : ℝ) * (L : ℝ) ^ 2 * δ * θ * Av⁻¹ ^ 2 := by
  rw [primBil_pp_eq]
  have hℓKd0 : (0 : ℝ) < ℓ * Kd := by positivity
  have hℓKd1 : 1 ≤ 2 * (ℓ * Kd) := by
    nlinarith [mul_le_mul_of_nonneg_left hKd1 (show (0 : ℝ) ≤ ℓ by linarith), hℓ2]
  have hFflat : ∀ x : ZMod L, ‖A ⟨[true, true], [x, a2]⟩‖ ≤ θ * Av⁻¹ ^ 2 := by
    intro x
    have h := hAbound (![x, a2] : LoopArg L 2)
    simpa only [ofFn_pp2] using h
  have hFdecay : ∀ x : ZMod L, ℓ * Kd ≤ (zdist L (x - a2) : ℝ) →
      ‖A ⟨[true, true], [x, a2]⟩‖ ≤ δ := by
    intro x hx
    have h := hAdecay (a := (![x, a2] : LoopArg L 2)) ⟨0, 1, by simpa using hx⟩
    simpa only [ofFn_pp2] using h
  have hGflat : ∀ y : ZMod L, ‖A ⟨[true, true], [a1, y]⟩‖ ≤ θ * Av⁻¹ ^ 2 := by
    intro y
    have h := hAbound (![a1, y] : LoopArg L 2)
    simpa only [ofFn_pp2] using h
  have hcore := norm_sum_SB_decayLeft (L := L) hL hℓKd0 hℓKd1 hδ0
    (by positivity : (0:ℝ) ≤ θ * Av⁻¹ ^ 2) hFflat hFdecay hGflat
  have hWnn : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg W
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL.trans' (by norm_num)
  have h6e1 : (1 : ℝ) ≤ 6 * Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  calc ‖(W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L,
        A ⟨[true, true], [x, a2]⟩ * SB L x y * A ⟨[true, true], [a1, y]⟩‖
      = (W : ℝ) * ‖∑ x : ZMod L, ∑ y : ZMod L,
          A ⟨[true, true], [x, a2]⟩ * SB L x y * A ⟨[true, true], [a1, y]⟩‖ := by
        rw [norm_mul, Complex.norm_natCast]
    _ ≤ (W : ℝ) * (θ * Av⁻¹ ^ 2 * (θ * Av⁻¹ ^ 2 * (6 * Real.exp 1 * (ℓ * Kd))
          + (L : ℝ) * δ)) := mul_le_mul_of_nonneg_left hcore hWnn
    _ = 6 * Real.exp 1 * (W * ℓ) * Kd * θ ^ 2 * Av⁻¹ ^ 4
          + (W : ℝ) * (L : ℝ) * δ * θ * Av⁻¹ ^ 2 := by ring
    _ = 6 * Real.exp 1 * Kd * θ ^ 2 * Av⁻¹ ^ 3 * ηv⁻¹
          + (W : ℝ) * (L : ℝ) * δ * θ * Av⁻¹ ^ 2 := by
        have hAvpow : Av * Av⁻¹ ^ 4 = Av⁻¹ ^ 3 := by
          rw [show Av⁻¹ ^ 4 = Av⁻¹ ^ 3 * Av⁻¹ from by ring, ← mul_assoc,
            mul_comm Av (Av⁻¹ ^ 3), mul_assoc, mul_inv_cancel₀ hAv0.ne', mul_one]
        rw [hWℓ, div_eq_mul_inv,
          show 6 * Real.exp 1 * (Av * ηv⁻¹) * Kd * θ ^ 2 * Av⁻¹ ^ 4
            = (Av * Av⁻¹ ^ 4) * (6 * Real.exp 1 * Kd * θ ^ 2 * ηv⁻¹) from by ring,
          hAvpow]
        ring
    _ ≤ 6 * Real.exp 1 * Kd * θ ^ 2 * Av⁻¹ ^ 3 * ηv⁻¹
          + 6 * Real.exp 1 * (W : ℝ) * (L : ℝ) ^ 2 * δ * θ * Av⁻¹ ^ 2 := by
        have hstep1 : (W:ℝ) * (L:ℝ) * δ * θ * Av⁻¹^2 ≤ (W:ℝ) * (L:ℝ)^2 * δ * θ * Av⁻¹^2 := by
          have h0 : (0:ℝ) ≤ (W:ℝ) * δ * θ * Av⁻¹^2 := by positivity
          have hLL : (L:ℝ) ≤ (L:ℝ)^2 := by nlinarith [hL1]
          nlinarith [mul_le_mul_of_nonneg_left hLL h0]
        have hstep2 : (W:ℝ) * (L:ℝ)^2 * δ * θ * Av⁻¹^2
            ≤ 6 * Real.exp 1 * (W:ℝ) * (L:ℝ)^2 * δ * θ * Av⁻¹^2 := by
          have h0 : (0:ℝ) ≤ (W:ℝ) * (L:ℝ)^2 * δ * θ * Av⁻¹^2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right h6e1 h0]
        linarith [hstep1, hstep2]

end PrimBilPP

end RBM

namespace RBM.Gauss

open RBM

/-! ### (T3) : `norm_eGterm_pp_le`, (5.80) at `n = 2` -/

section EGtermPP

variable {L W : ℕ} [NeZero L] [NeZero W]

open scoped Matrix.Norms.L2Operator

/-- `eGterm` at the constant `2`-loop `(σ_pp,(a1,a2))`: both `k = 1, 2` terms use the same
charge `true` (`I.σ.getD (k-1) true = true` since `I.σ = [true,true]`), and cutting at `k` puts
the summed index `b` at position `k` of a `3`-loop of constant charge `true`. -/
theorem eGterm_pp_eq (m : Bool → ℂ) (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (a1 a2 : ZMod L) :
    eGterm L W m M z ⟨[true, true], [a1, a2]⟩
      = (W : ℂ) * ((∑ x : ZMod L, ∑ y : ZMod L,
            Matrix.trace ((Gsig M z true
                - m true • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W x)
              * SB L x y * gloop L W M z ⟨[true, true, true], [y, a1, a2]⟩)
        + (∑ x : ZMod L, ∑ y : ZMod L,
            Matrix.trace ((Gsig M z true
                - m true • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W x)
              * SB L x y * gloop L W M z ⟨[true, true, true], [a1, y, a2]⟩)) := by
  have hlen : (⟨[true, true], [a1, a2]⟩ : LoopIdx (ZMod L)).length = 2 := rfl
  simp only [eGterm, hlen, show Finset.Icc (1 : ℕ) 2 = ({1, 2} : Finset ℕ) from by decide]
  rw [Finset.sum_insert (by decide)]
  simp [LoopIdx.cutGlue, List.getD, List.take, List.drop]

/-- **(T3)**: (5.80) at `n = 2`. `Ξ₁(M) ≤ φ₁` (sharp, both charges, only `s = true` is used at
`σ_pp`), `max|L₃(M)| ≤ φ₃ A_v^{-2}` and the `3`-loops of charge `(+,+,+)` are `(ℓ_v Kd,
δ)`-fast-decaying; then `‖eGterm(M)(I)‖ ≤ C Kd φ₁ φ₃ A_v^{-2} η_v^{-1} + C W L φ₁ δ A_v^{-1}`,
`C = 12e`. Route: `eGterm_pp_eq`, `norm_sum_SB_decayLeft` twice (with `Finset.sum_comm` and the
symmetry of `S^{(B)}` for the second `k`-term, since the decaying tensor there is the *second*
index of the pair), `Wℓ_v = A_v/η_v`. -/
theorem norm_eGterm_pp_le (hL : 3 ≤ L) (m : Bool → ℂ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (a1 a2 : ZMod L)
    {ℓ Kd δ φ1 φ3 Av ηv : ℝ} (hKd1 : 1 ≤ Kd) (hℓ2 : (1 : ℝ) / 2 ≤ ℓ) (hδ0 : 0 ≤ δ)
    (hφ1_0 : 0 ≤ φ1) (hφ3_0 : 0 ≤ φ3) (hAv0 : 0 < Av) (hηv0 : 0 < ηv)
    (hWℓ : (W : ℝ) * ℓ = Av / ηv)
    (hXi1 : ∀ s : Bool, ∀ x : ZMod L, ‖Matrix.trace ((Gsig M z s
        - m s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W x)‖ ≤ φ1 * Av⁻¹)
    (hL3bound : ∀ v : LoopArg L 3,
      ‖gloop L W M z ⟨[true, true, true], List.ofFn v⟩‖ ≤ φ3 * Av⁻¹ ^ 2)
    (hL3decay : FastDecay L (ℓ * Kd) δ
      (fun v : LoopArg L 3 => gloop L W M z ⟨[true, true, true], List.ofFn v⟩)) :
    ‖eGterm L W m M z ⟨[true, true], [a1, a2]⟩‖
      ≤ 12 * Real.exp 1 * Kd * φ1 * φ3 * Av⁻¹ ^ 2 * ηv⁻¹
        + 12 * Real.exp 1 * (W : ℝ) * (L : ℝ) * φ1 * δ * Av⁻¹ := by
  rw [eGterm_pp_eq]
  set T : ZMod L → ℂ := fun x => Matrix.trace ((Gsig M z true
      - m true • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W x) with hTdef
  have hTflat : ∀ x, ‖T x‖ ≤ φ1 * Av⁻¹ := fun x => hXi1 true x
  have hℓKd0 : (0 : ℝ) < ℓ * Kd := by positivity
  have hℓKd1 : 1 ≤ 2 * (ℓ * Kd) := by
    nlinarith [mul_le_mul_of_nonneg_left hKd1 (show (0 : ℝ) ≤ ℓ by linarith), hℓ2]
  have hsymm : ∀ x y : ZMod L, SB L x y = SB L y x := by
    intro x y
    conv_rhs => rw [← SB_transpose]
    rw [Matrix.transpose_apply]
  -- (k = 1) term: the decaying variable `y` sits at position `0` of `(y, a1, a2)`.
  have hterm1 :
      ‖∑ x : ZMod L, ∑ y : ZMod L,
          T x * SB L x y * gloop L W M z ⟨[true, true, true], [y, a1, a2]⟩‖
        ≤ φ1 * Av⁻¹ * (φ3 * Av⁻¹ ^ 2 * (6 * Real.exp 1 * (ℓ * Kd)) + (L : ℝ) * δ) := by
    have hcomm : (∑ x : ZMod L, ∑ y : ZMod L,
          T x * SB L x y * gloop L W M z ⟨[true, true, true], [y, a1, a2]⟩)
        = ∑ y : ZMod L, ∑ x : ZMod L,
            gloop L W M z ⟨[true, true, true], [y, a1, a2]⟩ * SB L y x * T x := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      rw [hsymm x y]; ring
    rw [hcomm]
    refine norm_sum_SB_decayLeft hL hℓKd0 hℓKd1 hδ0 (by positivity : (0:ℝ) ≤ φ1 * Av⁻¹)
      (f := fun y => gloop L W M z ⟨[true, true, true], [y, a1, a2]⟩) (p := a1) ?_ ?_ hTflat
    · intro y
      have h := hL3bound (![y, a1, a2] : LoopArg L 3)
      simpa only [ofFn_pp3] using h
    · intro y hy
      have h := hL3decay (a := (![y, a1, a2] : LoopArg L 3)) ⟨0, 1, by simpa using hy⟩
      simpa only [ofFn_pp3] using h
  -- (k = 2) term: the decaying variable `y` sits at position `1` of `(a1, y, a2)`.
  have hterm2 :
      ‖∑ x : ZMod L, ∑ y : ZMod L,
          T x * SB L x y * gloop L W M z ⟨[true, true, true], [a1, y, a2]⟩‖
        ≤ φ1 * Av⁻¹ * (φ3 * Av⁻¹ ^ 2 * (6 * Real.exp 1 * (ℓ * Kd)) + (L : ℝ) * δ) := by
    have hcomm : (∑ x : ZMod L, ∑ y : ZMod L,
          T x * SB L x y * gloop L W M z ⟨[true, true, true], [a1, y, a2]⟩)
        = ∑ y : ZMod L, ∑ x : ZMod L,
            gloop L W M z ⟨[true, true, true], [a1, y, a2]⟩ * SB L y x * T x := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      rw [hsymm x y]; ring
    rw [hcomm]
    refine norm_sum_SB_decayLeft hL hℓKd0 hℓKd1 hδ0 (by positivity : (0:ℝ) ≤ φ1 * Av⁻¹)
      (f := fun y => gloop L W M z ⟨[true, true, true], [a1, y, a2]⟩) (p := a1) ?_ ?_ hTflat
    · intro y
      have h := hL3bound (![a1, y, a2] : LoopArg L 3)
      simpa only [ofFn_pp3] using h
    · intro y hy
      have h := hL3decay (a := (![a1, y, a2] : LoopArg L 3)) ⟨1, 0, by simpa using hy⟩
      simpa only [ofFn_pp3] using h
  have hWnn : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg W
  have hcore : ‖∑ x : ZMod L, ∑ y : ZMod L,
        T x * SB L x y * gloop L W M z ⟨[true, true, true], [y, a1, a2]⟩
      + ∑ x : ZMod L, ∑ y : ZMod L,
        T x * SB L x y * gloop L W M z ⟨[true, true, true], [a1, y, a2]⟩‖
      ≤ 2 * (φ1 * Av⁻¹ * (φ3 * Av⁻¹ ^ 2 * (6 * Real.exp 1 * (ℓ * Kd)) + (L : ℝ) * δ)) := by
    refine (norm_add_le _ _).trans ?_
    linarith [hterm1, hterm2]
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL.trans' (by norm_num)
  have h12e2 : (2 : ℝ) ≤ 12 * Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  calc ‖(W : ℂ) * (∑ x : ZMod L, ∑ y : ZMod L,
        T x * SB L x y * gloop L W M z ⟨[true, true, true], [y, a1, a2]⟩
      + ∑ x : ZMod L, ∑ y : ZMod L,
        T x * SB L x y * gloop L W M z ⟨[true, true, true], [a1, y, a2]⟩)‖
      = (W : ℝ) * ‖∑ x : ZMod L, ∑ y : ZMod L,
          T x * SB L x y * gloop L W M z ⟨[true, true, true], [y, a1, a2]⟩
        + ∑ x : ZMod L, ∑ y : ZMod L,
          T x * SB L x y * gloop L W M z ⟨[true, true, true], [a1, y, a2]⟩‖ := by
        rw [norm_mul, Complex.norm_natCast]
    _ ≤ (W : ℝ) * (2 * (φ1 * Av⁻¹ * (φ3 * Av⁻¹ ^ 2 * (6 * Real.exp 1 * (ℓ * Kd))
          + (L : ℝ) * δ))) := mul_le_mul_of_nonneg_left hcore hWnn
    _ = 12 * Real.exp 1 * (W * ℓ) * Kd * φ1 * φ3 * Av⁻¹ ^ 3
          + 2 * (W : ℝ) * (L : ℝ) * φ1 * δ * Av⁻¹ := by ring
    _ = 12 * Real.exp 1 * Kd * φ1 * φ3 * Av⁻¹ ^ 2 * ηv⁻¹
          + 2 * (W : ℝ) * (L : ℝ) * φ1 * δ * Av⁻¹ := by
        have hAvpow : Av * Av⁻¹ ^ 3 = Av⁻¹ ^ 2 := by
          rw [show Av⁻¹ ^ 3 = Av⁻¹ ^ 2 * Av⁻¹ from by ring, ← mul_assoc,
            mul_comm Av (Av⁻¹ ^ 2), mul_assoc, mul_inv_cancel₀ hAv0.ne', mul_one]
        rw [hWℓ, div_eq_mul_inv,
          show 12 * Real.exp 1 * (Av * ηv⁻¹) * Kd * φ1 * φ3 * Av⁻¹ ^ 3
            = (Av * Av⁻¹ ^ 3) * (12 * Real.exp 1 * Kd * φ1 * φ3 * ηv⁻¹) from by ring,
          hAvpow]
        ring
    _ ≤ 12 * Real.exp 1 * Kd * φ1 * φ3 * Av⁻¹ ^ 2 * ηv⁻¹
          + 12 * Real.exp 1 * (W : ℝ) * (L : ℝ) * φ1 * δ * Av⁻¹ := by
        have h0 : (0:ℝ) ≤ (W:ℝ) * (L:ℝ) * φ1 * δ * Av⁻¹ := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h12e2 h0]

end EGtermPP

end RBM.Gauss

namespace RBM

/-! ### (T4) : compiled nondegenerate witnesses -/

section Witness

open scoped Matrix.Norms.L2Operator

end Witness

end RBM
