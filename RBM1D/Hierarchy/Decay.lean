/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Dynamics
import RBM1D.Hierarchy.KernelDecay
import RBM1D.Loop.Cor35
import RBM1D.Green.EntryBound
import RBM1D.Loop.Split

/-!
# Section 5.4: the fast decay property and the bounds on the `E`-terms

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, §5.4 (pp. 63–65): Definition 5.8 (5.74), Lemma 5.9 (5.75), the notation
(5.76), Lemma 5.10 (5.77)–(5.81) and Lemma 5.11 (5.83)–(5.86).

Everything is **deterministic**: `≺` is replaced by explicit inequalities with explicit
constants, `W^τ` by a free decay radius `ℓ` (or `K ≥ 1`), and `O(W^{-D})` by an explicit
`δ ≥ 0`.  The random inputs (the event of Lemma 4.1, the decay (2.76) of `L_{(+,-)}`, the
integrated hierarchy (5.20), the martingale bound of Lemma 5.5) enter as hypotheses of the
theorems, never as axioms.

## Notation

`A = W ℓ_u η_u ≥ 1` is the scale of (5.76).  Loop functions are `LoopIdx (ZMod L) → ℂ`
(`K`, `D = L - K`, the `G`-loops `L`), as in `Loop/Primitive.lean` and
`Hierarchy/Dynamics.lean`.  `Ξ^{(L-K)}_{u,m} ≤ Φ` is written `|D_{σ,a}| ≤ Φ A^{-m}` for loops of
length `m`, `Ξ^{(L)}_{u,m} ≤ Φ` is `|L_{σ,a}| ≤ Φ A^{-(m-1)}` (T53's `Sample.xiL`, `xiLK`
are exactly the smallest such `Φ`).

## Definition 5.8

* `RBM.Decay.LoopDecay L N ℓ δ F` — **(5.74)** for all loops of length `≤ N` at once;
  `LoopDecay.fastDecay` relates it to T51's `RBM.FastDecay` (7.13) of the tensor `a ↦ F_{σ,a}`.

## Lemma 5.10, (5.77): THE FOUR POWER COUNTS (for T60)

Each `E`-term is bounded by `M⋆ · A^{-n} + err`, `M⋆ = C_n · Ψ · W(ℓ+1)/A`, where
`W(ℓ+1)/A = (ℓ+1)/(ℓ_u η_u)` is the paper's `W^τ/η_u` for `ℓ = ℓ_u W^τ`, and `err = O(W^{-D})`:

* `norm_couplingLen_le` — `[K ∼ (L-K)]^{l_K}`, `l_K ≥ 3` (`couplingLen`, both orientations of
  (5.14)): for `I` of length `n`,
  `‖couplingLen L W lK K D I‖ ≤ 4e n² C_K Φ (W(ℓ+1)/A) A^{-n} + 2n² W L δ Φ`
  if `‖K J‖ ≤ C_K A^{-(|J|-1)}` ((2.59)), `K` has `(ℓ,δ)` decay on lengths `≤ n`, and
  `‖D J‖ ≤ Φ A^{-|J|}` for `|J| < n` (i.e. `max_{k<n} Ξ^{(L-K)}_{u,k} ≤ Φ`).
* `norm_primBil_sub_le` — `E^{((L-K)×(L-K))} = primBil D D` ((5.13)):
  `≤ 2e n² Φ (W(ℓ+1)/A) A^{-n} + n² W L δ B` if `‖D J‖ ≤ X_{|J|} A^{-|J|}` (`2 ≤ |J| ≤ n`),
  `X_m X_{n-m+2} A^{-1} ≤ Φ`, `X_m ≤ B` and `D` decays.
* `norm_eG_le` — `E^{(G)}` ((2.47), defined here as `eG`):
  `≤ 2e n Ξ₂ Φ (W(ℓ+1)/A) A^{-n} + n W L δ Ξ₂` if the one-loops satisfy `‖(L-K)_{(s),(a)}‖ ≤ Ξ₂ A^{-1}`,
  `‖L J‖ ≤ Φ A^{-n}` for `|J| = n+1` and `L` decays.
* `norm_eTens_le` — `E ⊗ E` ((5.22), `eTens`, for an abstract gluing `J k b b'` of (5.23)):
  `≤ 2e n Φ (W(ℓ+1)/A) A^{-2n} + n W L δ` if `‖L J‖ ≤ Φ A^{-(2n+1)}` for `|J| = 2n+2`.

Tensor forms (`loopTensor L F σ b = F_{σ,b}`, the shape consumed by `Uker`/`Qop`):
`norm_loopTensor_couplingLen_le`, `norm_loopTensor_primBil_le`, `norm_loopTensor_eG_le`.

"All these `E`-terms have the `(u,τ,D)` decay property": `norm_couplingLen_le_of_far`,
`norm_primBil_le_of_far`, `norm_eG_le_of_far`, `norm_eTens_le_of_far`, and the `FastDecay`
forms `fastDecay_couplingLen`, `fastDecay_primBil`, `fastDecay_eG` (radius `2ℓ + 1`; for
`E^{(G)}` radius `ℓ`).

The mechanism is `norm_sum_SB_le_left`: `|∑_{a,b} S^(B)_{ab} F_{ab}| ≤ 2e(ℓ+1) M + Lδ` when `F`
decays in `a` around an anchor — the `b` sum is free (`S^(B)` stochastic) and the `a` sum is
confined to a window.  The anchors are labels that survive cutting (`exists_anchor_cutGlueL`,
`exists_anchor_cutGlueR`, `mem_cutGlue_of_mem`).

## Lemma 5.11

* `pow_mul_norm_Uker_le_of_eq` — the integrand of (5.84)/(5.86): Case 1 of (7.16) (T51's
  `norm_Uker_fastDecay_le_of_eq`) applied to a tensor of size `M⋆ A_u^{-n} + err`:
  `A_t^n |(U_{u,t,σ} ∘ E)_a| ≤ C_{n,κ} K^n c_r^n (M⋆ + A_u^n err) + A_t^n ((1-u)/(1-t))^n δ`.
* `pow_mul_norm_Uker_couplingLen_le` — the same, fully assembled for `[K ∼ (L-K)]^{l_K}`.
* `mul_add_one_div_le` — `W(ℓ_u K + 1)/(W ℓ_u η_u) ≤ (K+2)/η_u`.
* `integral_inv_one_sub`, `lemma511_assembly` — (5.84) ⟹ (5.83): from the integrated
  hierarchy (as an inequality) and an integrand bound `Ψ/η_u + ε`,
  `A_t^n |(L-K)_{t,σ,a}| ≤ I₀ + Ψ log((1-s)/(1-t)) + ε(t-s) + M`.

## Lemma 5.9

* `norm_Kgen_le_exp` — Corollary 3.5 for **every** `σ` (gap `δ ≤ |1 - t m(s)m(s')|`, e.g.
  `δ = 1 - t`, `one_sub_le_norm_one_sub`), via the tree representation `Kgen_eq` and (2.52);
  `loopDecay_Kgen` — `K` decays: `LoopDecay N ℓ (C_N(δ) e^{-c(δ) ℓ})`.
* `norm_sq_green_le_of_far` — (4.2) + decay of `L_{(+,-)}` ⟹ `|G_{ij}|² ≤ 729 Φ² δ₂` for
  `‖[i]-[j]‖ ≥ ℓ + 2`.
* `norm_gloop_le_of_far`, `loopDecay_gloop` — decaying entries of `G` ⟹ every `G`-loop
  decays (a far pair forces a far *consecutive* pair, `exists_consecutive_far`; rotate it to
  the ends, `gloop_rotate_eq`; `norm_trace_far_le`).
* `loopDecay_gloop_of_event`, `lemma59` — **(5.75)** on the event of Lemma 4.1: `L` and
  `L - K` both decay.

## Deviations from the paper

* **Deterministic, explicit constants** instead of `≺`; `W^τ` is a free radius `ℓ` and
  `O(W^{-D})` an explicit `δ`.  The factor `W(ℓ+1)/A` stands for the paper's `1/η_u` (it is
  `≤ (W^τ + 2)/η_u`, `mul_add_one_div_le`).
* `LoopDecay` carries a cap `N` on the loop length (the constants of Lemma 5.9 depend on it).
* (5.77) is stated with the inputs `max_{k<n} Ξ_k ≤ Φ` etc. as hypotheses, in the
  "bound-transfer" style of T53's `Step3.Lemma514`, and for `A ≥ 1`.  The error terms are
  kept separately (`2n²WLδΦ`, …).  For `E^{(G)}` the factor `Ξ^{(L)}_{u,2}` is kept (`Ξ₂`), the
  paper bounds it by `1` using (2.76).
* `E⊗E` (Definition 5.4) is not yet defined in `Dynamics.lean` (T58); `eTens` takes the
  gluing `J k b b'` of (5.23) as a parameter and only uses: `J k b b'` is well formed, has
  length `2n+2`, contains `b` and a label `c_k` independent of `b, b'`.
* `E^{(G)}` is defined here (`eG`), with the one-loop `⟨(G(σ_k) - m) E_a⟩` supplied as a loop
  function `X` evaluated at `((σ_k),(a))` (for `X = L - K` this is (2.47), since `K = m` on
  one-loops).  `[K ∼ (L - K)]^{l_K}` is `couplingLen = primBilLen K D + primBilLenR D K`
  (`primBilLenR` grades by the length of the right factor; `sum_couplingLen` checks that the
  grading exhausts `primBil K D + primBil D K`).
* Lemma 5.11 is proved as (i) the kernel bound on each `E`-term (the integrands of (5.84) and,
  with `n ↦ 2n`, `σ ↦ (σ,σ)`, of (5.86)) and (ii) the integration step `lemma511_assembly`;
  the integrated hierarchy (5.20) (triangle inequality applied) and the martingale bound
  (Lemma 5.5 + BDG) are hypotheses.  The time scale is `η_u = 1 - u` as in T51
  (`KernelDecay.lean`); a general normalization `A_u` enters through
  `(1-u)ℓ_u/((1-t)ℓ_t) ≤ c_r A_u/A_t`.
* Lemma 5.9 is proved on the event of Lemma 4.1 (the hypotheses of `norm_sq_green_le_blk`)
  with the decay (2.76) of `L_{(+,-)}` as a hypothesis; the passage to "with probability
  `1 - O(W^{-D'})`" is the high-probability statement of that event (`entry_bound_stochDom`).
  The decay radius grows from `ℓ` to `2N(ℓ + 2)` (the paper absorbs such factors into `W^τ`).
  For `K`, Corollary 3.5 is re-proved for all `σ` with the gap `1 - t`, so the rate is
  `c √(1-t) = c/ℓ_t` (when `ℓ_t < L`).
-/

namespace RBM

open Finset Real

namespace Decay

/-! ### Definition 5.8 for loop functions -/

section Def58

variable (L : ℕ)

/-- **Definition 5.8, (5.74)**, for all loops of length `≤ N` at once: `F` has `(ℓ, δ)` decay
if `‖F_{σ,a}‖ ≤ δ` as soon as two labels of `a` are at distance `≥ ℓ`.  The paper's
`(u, τ, D)` decay is `ℓ = ℓ_u W^τ`, `δ = W^{-D}` (its `O(W^{-D})` is absorbed into `δ`).
Only well-formed loops (`σ` and `a` of the same length) are constrained; the cap `N` on the
length is there because the constants of Lemma 5.9 depend on the length. -/
def LoopDecay (N : ℕ) (ℓ δ : ℝ) (F : LoopIdx (ZMod L) → ℂ) : Prop :=
  ∀ J : LoopIdx (ZMod L), J.WF → J.length ≤ N → ∀ x ∈ J.a, ∀ y ∈ J.a,
    ℓ ≤ (zdist L (x - y) : ℝ) → ‖F J‖ ≤ δ

/-- `LoopDecay` restricted to the loops with charges `σ` is T51's `FastDecay` (7.13) of the
tensor `a ↦ F_{σ,a}`. -/
theorem LoopDecay.fastDecay {n : ℕ} {ℓ δ : ℝ} {F : LoopIdx (ZMod L) → ℂ}
    (h : LoopDecay L n ℓ δ F) (σ : List Bool) (hσ : σ.length = n) :
    FastDecay L ℓ δ (fun a : LoopArg L n => F ⟨σ, List.ofFn a⟩) := by
  rintro a ⟨i, j, hij⟩
  refine h _ ?_ (by simp [LoopIdx.length]) (a i) (List.mem_ofFn.2 ⟨i, rfl⟩) (a j)
    (List.mem_ofFn.2 ⟨j, rfl⟩) hij
  simp [LoopIdx.WF, hσ]

theorem LoopDecay.mono {N N' : ℕ} {ℓ ℓ' δ δ' : ℝ} {F : LoopIdx (ZMod L) → ℂ}
    (h : LoopDecay L N ℓ δ F) (hN : N' ≤ N) (hℓ : ℓ ≤ ℓ') (hδ : δ ≤ δ') :
    LoopDecay L N' ℓ' δ' F :=
  fun J hJ hJN x hx y hy hxy => (h J hJ (hJN.trans hN) x hx y hy (hℓ.trans hxy)).trans hδ

/-- The difference of two decaying loop functions decays (used for `L - K`, Lemma 5.9). -/
theorem LoopDecay.sub {N : ℕ} {ℓ δ δ' : ℝ} {F G : LoopIdx (ZMod L) → ℂ}
    (hF : LoopDecay L N ℓ δ F) (hG : LoopDecay L N ℓ δ' G) :
    LoopDecay L N ℓ (δ + δ') (F - G) := fun J hJ hJN x hx y hy hxy =>
  (norm_sub_le _ _).trans (add_le_add (hF J hJ hJN x hx y hy hxy) (hG J hJ hJN x hx y hy hxy))

theorem LoopDecay.add {N : ℕ} {ℓ δ δ' : ℝ} {F G : LoopIdx (ZMod L) → ℂ}
    (hF : LoopDecay L N ℓ δ F) (hG : LoopDecay L N ℓ δ' G) :
    LoopDecay L N ℓ (δ + δ') (F + G) := fun J hJ hJN x hx y hy hxy =>
  (norm_add_le _ _).trans (add_le_add (hF J hJ hJN x hx y hy hxy) (hG J hJ hJN x hx y hy hxy))

end Def58

variable (L : ℕ) [NeZero L]

/-! ### The window sum -/

/-- **The source of every factor `ℓ_u` in Lemma 5.10.**  If `F_{ab}` is bounded by `M`, and
by `δ` once `a` is at distance `≥ ℓ` from an anchor `c`, then
`|∑_{a,b} S^(B)_{ab} F_{ab}| ≤ 2e(ℓ + 1) M + L δ`: the `b`-sum costs nothing (`S^(B)` is
stochastic) and the `a`-sum is confined to a window of `O(ℓ)` sites. -/
theorem norm_sum_SB_le_left (hL : 3 ≤ L) {ℓ M δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (c : ZMod L)
    (F : ZMod L → ZMod L → ℂ) (hF : ∀ a b, ‖F a b‖ ≤ M)
    (hFd : ∀ a b, ℓ ≤ (zdist L (a - c) : ℝ) → ‖F a b‖ ≤ δ) :
    ‖∑ a : ZMod L, ∑ b : ZMod L, SB L a b * F a b‖ ≤ 2 * exp 1 * (ℓ + 1) * M + L * δ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF 0 0)
  have hrow : ∀ a, ∑ b : ZMod L, ‖SB L a b * F a b‖ ≤ winInd L ℓ (a - c) * M + δ := by
    intro a
    by_cases h : (zdist L (a - c) : ℝ) < ℓ
    · have hw : winInd L ℓ (a - c) = 1 := by simp [winInd, h]
      calc ∑ b : ZMod L, ‖SB L a b * F a b‖ ≤ ∑ b : ZMod L, ‖SB L a b‖ * M :=
            sum_le_sum fun b _ => by
              rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hF a b) (norm_nonneg _)
        _ = M := by rw [← sum_mul, sum_norm_SB_apply_row L hL, one_mul]
        _ ≤ winInd L ℓ (a - c) * M + δ := by rw [hw]; linarith
    · have hw : winInd L ℓ (a - c) = 0 := by simp [winInd, h]
      push Not at h
      calc ∑ b : ZMod L, ‖SB L a b * F a b‖ ≤ ∑ b : ZMod L, ‖SB L a b‖ * δ :=
            sum_le_sum fun b _ => by
              rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hFd a b h) (norm_nonneg _)
        _ = δ := by rw [← sum_mul, sum_norm_SB_apply_row L hL, one_mul]
        _ = winInd L ℓ (a - c) * M + δ := by rw [hw]; ring
  calc ‖∑ a : ZMod L, ∑ b : ZMod L, SB L a b * F a b‖
      ≤ ∑ a : ZMod L, ∑ b : ZMod L, ‖SB L a b * F a b‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a : ZMod L, (winInd L ℓ (a - c) * M + δ) := sum_le_sum fun a _ => hrow a
    _ = (∑ a : ZMod L, winInd L ℓ (a - c)) * M + L * δ := by
        rw [sum_add_distrib, ← sum_mul, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    _ ≤ 2 * exp 1 * (ℓ + 1) * M + L * δ := by
        gcongr
        exact sum_winInd_le L hℓ c

/-- `norm_sum_SB_le_left` with the decay in the second variable (by the symmetry of `S^(B)`). -/
theorem norm_sum_SB_le_right (hL : 3 ≤ L) {ℓ M δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (c : ZMod L)
    (F : ZMod L → ZMod L → ℂ) (hF : ∀ a b, ‖F a b‖ ≤ M)
    (hFd : ∀ a b, ℓ ≤ (zdist L (b - c) : ℝ) → ‖F a b‖ ≤ δ) :
    ‖∑ a : ZMod L, ∑ b : ZMod L, SB L a b * F a b‖ ≤ 2 * exp 1 * (ℓ + 1) * M + L * δ := by
  have e : ∑ a : ZMod L, ∑ b : ZMod L, SB L a b * F a b
      = ∑ b : ZMod L, ∑ a : ZMod L, SB L b a * F a b := by
    rw [sum_comm]
    refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
    rw [show SB L a b = SB L b a from congrFun (congrFun (SB_transpose L) b) a]
  rw [e]
  exact norm_sum_SB_le_left L hL hℓ hδ c (fun b a => F a b) (fun b a => hF a b)
    (fun b a h => hFd a b h)

/-! ### Anchors: labels that survive cutting and gluing -/

section Anchor

variable {α : Type*} (x : LoopIdx α) (b : α) {k l : ℕ}

theorem mem_cutGlueL (k l : ℕ) : b ∈ (x.cutGlueL k l b).a := by
  simp [LoopIdx.cutGlueL]

theorem mem_cutGlueR (k l : ℕ) : b ∈ (x.cutGlueR k l b).a := by
  simp [LoopIdx.cutGlueR]

theorem mem_cutGlue (k : ℕ) : b ∈ (x.cutGlue k b).a := by
  simp [LoopIdx.cutGlue]

/-- Every label of the loop survives `cutGlue` (the new label is only inserted). -/
theorem mem_cutGlue_of_mem (k : ℕ) {c : α} (hc : c ∈ x.a) : c ∈ (x.cutGlue k b).a := by
  simp only [LoopIdx.cutGlue, List.mem_append, List.mem_cons]
  rw [← List.take_append_drop (k - 1) x.a, List.mem_append] at hc
  tauto

/-- The left loop of the cut `(k, l)` keeps the label `a_l`, whatever the glued label is. -/
theorem exists_anchor_cutGlueL (hl1 : 1 ≤ l) (hl : l ≤ x.length) :
    ∃ c : α, ∀ b : α, c ∈ (x.cutGlueL k l b).a := by
  have h : 0 < (x.a.drop (l - 1)).length := by
    simp only [List.length_drop]; simp only [LoopIdx.length] at hl; omega
  refine ⟨(x.a.drop (l - 1))[0], fun b => ?_⟩
  simp only [LoopIdx.cutGlueL, List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr (List.getElem_mem h))

/-- The right loop of the cut `(k, l)` keeps the label `a_k`. -/
theorem exists_anchor_cutGlueR (hk1 : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    ∃ c : α, ∀ b : α, c ∈ (x.cutGlueR k l b).a := by
  have h : 0 < ((x.a.drop (k - 1)).take (l - k)).length := by
    simp only [List.length_take, List.length_drop]; simp only [LoopIdx.length] at hl; omega
  refine ⟨((x.a.drop (k - 1)).take (l - k))[0], fun b => ?_⟩
  simp only [LoopIdx.cutGlueR, List.mem_append]
  exact Or.inl (List.getElem_mem h)

/-- Every label of the loop goes to the left or to the right loop of the cut `(k, l)`. -/
theorem mem_cutGlueL_or_mem_cutGlueR (hk : 1 ≤ k) (hkl : k < l) {c : α} (hc : c ∈ x.a) :
    (∀ b, c ∈ (x.cutGlueL k l b).a) ∨ (∀ b, c ∈ (x.cutGlueR k l b).a) := by
  rw [← List.take_append_drop (k - 1) x.a, List.mem_append,
    ← List.take_append_drop (l - k) (x.a.drop (k - 1)), List.mem_append, List.drop_drop] at hc
  have e : k - 1 + (l - k) = l - 1 := by omega
  rw [e] at hc
  rcases hc with h | h | h
  · left; intro b; simp [LoopIdx.cutGlueL, h]
  · right; intro b; simp [LoopIdx.cutGlueR, h]
  · left; intro b; simp [LoopIdx.cutGlueL, h]

end Anchor

/-! ### One cut `(k, l)` -/

section Glue

/-- `W ∑_{1≤k<l≤n} f(k, l)` has at most `n²` terms. -/
theorem norm_W_sum_le (W n : ℕ) (f : ℕ → ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ k ∈ Icc 1 n, ∀ l ∈ Ioc k n, ‖f k l‖ ≤ T) :
    ‖(W : ℂ) * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, f k l‖ ≤ W * n ^ 2 * T := by
  rw [norm_mul, Complex.norm_natCast, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc ‖∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, f k l‖
      ≤ ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ‖f k l‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun k _ => norm_sum_le _ _)
    _ ≤ ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, T :=
        sum_le_sum fun k hk => sum_le_sum fun l hl => hf k hk l hl
    _ ≤ ∑ k ∈ Icc 1 n, (n : ℝ) * T := by
        refine sum_le_sum fun k _ => ?_
        rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
        gcongr
        exact_mod_cast Nat.sub_le n k
    _ = n ^ 2 * T := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]; ring

/-- `W ∑_{1≤k≤n} f(k)` has `n` terms. -/
theorem norm_W_sum_le' (W n : ℕ) (f : ℕ → ℂ) {T : ℝ}
    (hf : ∀ k ∈ Icc 1 n, ‖f k‖ ≤ T) :
    ‖(W : ℂ) * ∑ k ∈ Icc 1 n, f k‖ ≤ W * n * T := by
  rw [norm_mul, Complex.norm_natCast, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc ‖∑ k ∈ Icc 1 n, f k‖ ≤ ∑ k ∈ Icc 1 n, ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Icc 1 n, T := sum_le_sum hf
    _ = n * T := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]

/-- The `(k, l)` summand of (2.48)/(5.13)/(5.14):
`∑_{a,b} F(G^{(a),L}_{k,l}(σ,a)) S^(B)_{ab} G(G^{(b),R}_{k,l}(σ,a))`. -/
noncomputable def glueTerm (F G : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) (k l : ℕ) : ℂ :=
  ∑ a : ZMod L, ∑ b : ZMod L, F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)

theorem glueTerm_eq (F G : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) (k l : ℕ) :
    glueTerm L F G I k l
      = ∑ a : ZMod L, ∑ b : ZMod L, SB L a b * (F (I.cutGlueL k l a) * G (I.cutGlueR k l b)) :=
  sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- One cut, the **left** loop decaying: the glued label `a` is confined to a window around
the label `a_l` that the left loop keeps. -/
theorem norm_glueTerm_le_left (hL : 3 ≤ L) {F G : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length)
    {ℓ δ MF MG : ℝ} (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hFd : LoopDecay L I.length ℓ δ F)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG) :
    ‖glueTerm L F G I k l‖ ≤ 2 * exp 1 * (ℓ + 1) * (MF * MG) + L * (δ * MG) := by
  have hMG : 0 ≤ MG := (norm_nonneg _).trans (hG 0)
  obtain ⟨c, hc⟩ := exists_anchor_cutGlueL I (k := k) (by omega) hl
  rw [glueTerm_eq]
  refine norm_sum_SB_le_left L hL hℓ (mul_nonneg hδ hMG) c _ (fun a b => ?_) (fun a b h => ?_)
  · rw [norm_mul]; exact mul_le_mul (hF a) (hG b) (norm_nonneg _)
      ((norm_nonneg _).trans (hF a))
  · rw [norm_mul]
    refine mul_le_mul ?_ (hG b) (norm_nonneg _) hδ
    exact hFd _ (hI.cutGlueL a hk hkl hl) (LoopIdx.length_cutGlueL_le I a hk hkl hl) a (mem_cutGlueL I a k l) c (hc a) h

/-- One cut, the **right** loop decaying. -/
theorem norm_glueTerm_le_right (hL : 3 ≤ L) {F G : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length)
    {ℓ δ MF MG : ℝ} (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hGd : LoopDecay L I.length ℓ δ G)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG) :
    ‖glueTerm L F G I k l‖ ≤ 2 * exp 1 * (ℓ + 1) * (MF * MG) + L * (MF * δ) := by
  have hMF : 0 ≤ MF := (norm_nonneg _).trans (hF 0)
  obtain ⟨c, hc⟩ := exists_anchor_cutGlueR I hk hkl hl
  rw [glueTerm_eq]
  refine norm_sum_SB_le_right L hL hℓ (mul_nonneg hMF hδ) c _ (fun a b => ?_) (fun a b h => ?_)
  · rw [norm_mul]; exact mul_le_mul (hF a) (hG b) (norm_nonneg _) hMF
  · rw [norm_mul]
    refine mul_le_mul (hF a) ?_ (norm_nonneg _) hMF
    exact hGd _ (hI.cutGlueR b hk hkl hl) (LoopIdx.length_cutGlueR_le I b hk hkl hl) b (mem_cutGlueR I b k l) c (hc b) h

/-- Two labels `x` in the left and `y` in the right loop, at distance `≥ 2ℓ + 1`: for
`|a - b| ≤ 1` one of the two loops has its glued label at distance `≥ ℓ` from `x`, resp. `y`. -/
theorem norm_mul_le_of_far_aux {F G : LoopIdx (ZMod L) → ℂ} {I : LoopIdx (ZMod L)} (hI : I.WF)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) {ℓ δ MF MG : ℝ} (hδ : 0 ≤ δ)
    (hFd : LoopDecay L I.length ℓ δ F) (hGd : LoopDecay L I.length ℓ δ G)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG)
    {x y : ZMod L} (hx : ∀ a, x ∈ (I.cutGlueL k l a).a) (hy : ∀ b, y ∈ (I.cutGlueR k l b).a)
    (hxy : 2 * ℓ + 1 ≤ (zdist L (x - y) : ℝ)) {a b : ZMod L} (hab : zdist L (a - b) ≤ 1) :
    ‖F (I.cutGlueL k l a) * G (I.cutGlueR k l b)‖ ≤ δ * MG + MF * δ := by
  have hMF : 0 ≤ MF := (norm_nonneg _).trans (hF 0)
  have hMG : 0 ≤ MG := (norm_nonneg _).trans (hG 0)
  rw [norm_mul]
  by_cases h1 : ℓ ≤ (zdist L (x - a) : ℝ)
  · have := hFd _ (hI.cutGlueL a hk hkl hl) (LoopIdx.length_cutGlueL_le I a hk hkl hl) x (hx a) a (mem_cutGlueL I a k l) h1
    nlinarith [norm_nonneg (F (I.cutGlueL k l a)), norm_nonneg (G (I.cutGlueR k l b)), hG b]
  by_cases h2 : ℓ ≤ (zdist L (b - y) : ℝ)
  · have := hGd _ (hI.cutGlueR b hk hkl hl) (LoopIdx.length_cutGlueR_le I b hk hkl hl) b (mem_cutGlueR I b k l) y (hy b) h2
    nlinarith [norm_nonneg (F (I.cutGlueL k l a)), norm_nonneg (G (I.cutGlueR k l b)), hF a]
  exfalso
  push Not at h1 h2
  have t1 := zdist_add_le L (x - a) (a - b)
  have t2 := zdist_add_le L (x - a + (a - b)) (b - y)
  have e : x - a + (a - b) + (b - y) = x - y := by ring
  rw [e] at t2
  have : (zdist L (x - y) : ℝ) ≤ zdist L (x - a) + zdist L (a - b) + zdist L (b - y) := by
    exact_mod_cast t2.trans (Nat.add_le_add_right t1 _)
  have hab' : (zdist L (a - b) : ℝ) ≤ 1 := by exact_mod_cast hab
  linarith

/-- **Decay of one cut**: if two labels of the loop are at distance `≥ 2ℓ + 1` and both
factors have `(ℓ, δ)` decay, the `(k, l)` summand is `≤ L δ (M_F + M_G)`. -/
theorem norm_glueTerm_le_of_far (hL : 3 ≤ L) {F G : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length)
    {ℓ δ MF MG : ℝ} (hδ : 0 ≤ δ) (hFd : LoopDecay L I.length ℓ δ F) (hGd : LoopDecay L I.length ℓ δ G)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG)
    {x y : ZMod L} (hx : x ∈ I.a) (hy : y ∈ I.a) (hxy : 2 * ℓ + 1 ≤ (zdist L (x - y) : ℝ)) :
    ‖glueTerm L F G I k l‖ ≤ L * (δ * MG + MF * δ) := by
  have hMF : 0 ≤ MF := (norm_nonneg _).trans (hF 0)
  have hMG : 0 ≤ MG := (norm_nonneg _).trans (hG 0)
  -- the pointwise bound on the support of `S^(B)`
  have hpt : ∀ a b, zdist L (a - b) ≤ 1 →
      ‖F (I.cutGlueL k l a) * G (I.cutGlueR k l b)‖ ≤ δ * MG + MF * δ := by
    intro a b hab
    rcases mem_cutGlueL_or_mem_cutGlueR I hk hkl hx with hxL | hxR <;>
      rcases mem_cutGlueL_or_mem_cutGlueR I hk hkl hy with hyL | hyR
    · have := hFd _ (hI.cutGlueL a hk hkl hl) (LoopIdx.length_cutGlueL_le I a hk hkl hl) x (hxL a) y (hyL a) (by linarith [hxy])
      rw [norm_mul]
      nlinarith [norm_nonneg (F (I.cutGlueL k l a)), norm_nonneg (G (I.cutGlueR k l b)), hG b]
    · exact norm_mul_le_of_far_aux L hI hk hkl hl hδ hFd hGd hF hG hxL hyR hxy hab
    · have hyx : 2 * ℓ + 1 ≤ (zdist L (y - x) : ℝ) := by
        rwa [← zdist_neg L (y - x), neg_sub]
      exact norm_mul_le_of_far_aux L hI hk hkl hl hδ hFd hGd hF hG hyL hxR hyx hab
    · have := hGd _ (hI.cutGlueR b hk hkl hl) (LoopIdx.length_cutGlueR_le I b hk hkl hl) x (hxR b) y (hyR b) (by linarith [hxy])
      rw [norm_mul]
      nlinarith [norm_nonneg (F (I.cutGlueL k l a)), norm_nonneg (G (I.cutGlueR k l b)), hF a]
  rw [glueTerm_eq]
  calc ‖∑ a : ZMod L, ∑ b : ZMod L, SB L a b * (F (I.cutGlueL k l a) * G (I.cutGlueR k l b))‖
      ≤ ∑ a : ZMod L, ∑ b : ZMod L,
          ‖SB L a b * (F (I.cutGlueL k l a) * G (I.cutGlueR k l b))‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a : ZMod L, ∑ b : ZMod L, ‖SB L a b‖ * (δ * MG + MF * δ) := by
        refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
        rw [norm_mul]
        by_cases hab : zdist L (a - b) ≤ 1
        · exact mul_le_mul_of_nonneg_left (hpt a b hab) (norm_nonneg _)
        · rw [SB_apply_eq_zero L hL (by omega)]; simp
    _ = L * (δ * MG + MF * δ) := by
        simp only [← sum_mul, sum_norm_SB_apply_row L hL, one_mul, sum_const, card_univ,
          ZMod.card, nsmul_eq_mul]

end Glue

/-! ### The graded coupling `[K ∼ (L - K)]^{l_K}` (5.14) -/

section Coupling

/-- The coupling `primBil F G` graded by the length of the **right** factor (T58's `primBilLen`
grades by the left one).  In `primBil (L - K) K` the `K` factor is on the right, so this is
the second half `(K ⇔ L - K)` of (5.14). -/
noncomputable def primBilLenR (W : ℕ) (lK : ℕ) (F G : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) : ℂ :=
  (W : ℂ) * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
    (if (I.cutGlueR k l b).length = lK then F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)
      else 0)

/-- **(5.14)** `[K ∼ (L - K)]^{l_K}_{t,σ,a}`: both orientations, graded by the length `l_K` of
the `K` loop (`D = L - K`). -/
noncomputable def couplingLen (W : ℕ) (lK : ℕ) (K D : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) : ℂ :=
  primBilLen L W lK K D I + primBilLenR L W lK D K I

theorem sum_primBilLenR (W : ℕ) (F G : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, primBilLenR L W lK F G I = primBil L W F G I := by
  simp only [primBilLenR, primBil, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have hlen : (I.cutGlueR k l b).length < N := by
    rw [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2]; omega
  rw [Finset.sum_ite_eq (Finset.range N) ((I.cutGlueR k l b).length)
    (fun _ => F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)),
    ite_eq_left_iff.2 (fun h => absurd (Finset.mem_range.mpr hlen) h)]

/-- Summing (5.14) over every `l_K` gives the whole first line of (5.12):
`∑_{l_K} [K ∼ (L - K)]^{l_K} = primBil K D + primBil D K`. -/
theorem sum_couplingLen (W : ℕ) (K D : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, couplingLen L W lK K D I = primBil L W K D I + primBil L W D K I := by
  simp only [couplingLen, Finset.sum_add_distrib]
  rw [sum_primBilLen L W K D I hN, sum_primBilLenR L W D K I hN]

theorem primBilLen_summand (F G : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) (lK : ℕ) :
    (∑ a : ZMod L, ∑ b : ZMod L, (if (I.cutGlueL k l a).length = lK then
      F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b) else 0))
      = if k + I.length - l + 1 = lK then glueTerm L F G I k l else 0 := by
  simp only [fun a => LoopIdx.length_cutGlueL I a hk hkl hl]
  split_ifs <;> simp [glueTerm]

theorem primBilLenR_summand (F G : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) (lK : ℕ) :
    (∑ a : ZMod L, ∑ b : ZMod L, (if (I.cutGlueR k l b).length = lK then
      F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b) else 0))
      = if l - k + 1 = lK then glueTerm L F G I k l else 0 := by
  simp only [fun b => LoopIdx.length_cutGlueR I b hk hkl hl]
  split_ifs <;> simp [glueTerm]

theorem pow_inv_le_one {A : ℝ} (hA : 1 ≤ A) (m : ℕ) : A⁻¹ ^ m ≤ 1 :=
  pow_le_one₀ (inv_nonneg.2 (by linarith)) (inv_le_one_of_one_le₀ hA)

/-- **Lemma 5.10, (5.77), first line**: `[K ∼ (L - K)]^{l_K}` for `l_K ≥ 3`.

With `A = W ℓ_u η_u ≥ 1`, `|K_{σ,a}| ≤ C_K A^{-(m-1)}` for loops of length `m` ((2.59)),
`K` having `(ℓ, δ)` decay, and `|(L - K)_{σ,a}| ≤ Φ A^{-m}` for loops of length `m < n`
(i.e. `Ξ^{(L-K)}_{u,m} ≤ Φ` for `m < n`, (5.76)):
`|[K ∼ (L - K)]^{l_K}_{σ,a}| ≤ 4e n² C_K Φ (W(ℓ+1)/A) A^{-n} + 2n² W L δ Φ`.
The paper's `max_{k<n} Ξ^{(L-K)}_{u,k} (W ℓ_u η_u)^{-n} η_u^{-1}` is the first term:
`W(ℓ+1)/A = (ℓ+1)/(ℓ_u η_u)` is `W^τ/η_u` for `ℓ = ℓ_u W^τ`; the second is `O(W^{-D})`. -/
theorem norm_couplingLen_le (hL : 3 ≤ L) (W : ℕ) {lK : ℕ} (hlK : 3 ≤ lK)
    {K D : LoopIdx (ZMod L) → ℂ} {I : LoopIdx (ZMod L)} (hI : I.WF) {A ℓ δ CK Φ : ℝ}
    (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hCK : 0 ≤ CK) (hΦ : 0 ≤ Φ)
    (hK : ∀ J : LoopIdx (ZMod L), J.WF → ‖K J‖ ≤ CK * A⁻¹ ^ (J.length - 1))
    (hKd : LoopDecay L I.length ℓ δ K)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → J.length < I.length → ‖D J‖ ≤ Φ * A⁻¹ ^ J.length) :
    ‖couplingLen L W lK K D I‖
      ≤ 4 * exp 1 * I.length ^ 2 * CK * Φ * ((W : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ I.length
        + 2 * I.length ^ 2 * W * L * δ * Φ := by
  set n := I.length with hn
  have hA0 : 0 < A := by linarith
  set T : ℝ := 2 * exp 1 * (ℓ + 1) * (CK * Φ * A⁻¹ ^ (n + 1)) + L * (δ * Φ) with hT
  have hT0 : 0 ≤ T := by positivity
  have hleft : ‖primBilLen L W lK K D I‖ ≤ W * n ^ 2 * T := by
    refine norm_W_sum_le W n _ hT0 fun k hk l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    rw [primBilLen_summand L K D I hk.1 hl.1 hl.2]
    split_ifs with h
    · have hF : ∀ a, ‖K (I.cutGlueL k l a)‖ ≤ CK * A⁻¹ ^ (lK - 1) := fun a => by
        have := hK _ (hI.cutGlueL a hk.1 hl.1 hl.2)
        rwa [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2, h] at this
      have hG : ∀ b, ‖D (I.cutGlueR k l b)‖ ≤ Φ * A⁻¹ ^ (l - k + 1) := fun b => by
        have := hD _ (hI.cutGlueR b hk.1 hl.1 hl.2)
          (by rw [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2]; omega)
        rwa [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2] at this
      refine (norm_glueTerm_le_left L hL hI hk.1 hl.1 hl.2 hℓ hδ hKd hF hG).trans ?_
      have e : CK * A⁻¹ ^ (lK - 1) * (Φ * A⁻¹ ^ (l - k + 1)) = CK * Φ * A⁻¹ ^ (n + 1) := by
        rw [mul_mul_mul_comm, ← pow_add]; congr 2; omega
      rw [e, hT]
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
      calc δ * (Φ * A⁻¹ ^ (l - k + 1)) ≤ δ * (Φ * 1) := by
            gcongr; exact pow_inv_le_one hA _
        _ = δ * Φ := by ring
    · simpa using hT0
  have hright : ‖primBilLenR L W lK D K I‖ ≤ W * n ^ 2 * T := by
    refine norm_W_sum_le W n _ hT0 fun k hk l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    rw [primBilLenR_summand L D K I hk.1 hl.1 hl.2]
    split_ifs with h
    · have hG : ∀ b, ‖K (I.cutGlueR k l b)‖ ≤ CK * A⁻¹ ^ (lK - 1) := fun b => by
        have := hK _ (hI.cutGlueR b hk.1 hl.1 hl.2)
        rwa [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2, h] at this
      have hF : ∀ a, ‖D (I.cutGlueL k l a)‖ ≤ Φ * A⁻¹ ^ (k + n - l + 1) := fun a => by
        have := hD _ (hI.cutGlueL a hk.1 hl.1 hl.2)
          (by rw [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2]; omega)
        rwa [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2] at this
      refine (norm_glueTerm_le_right L hL hI hk.1 hl.1 hl.2 hℓ hδ hKd hF hG).trans ?_
      have e : Φ * A⁻¹ ^ (k + n - l + 1) * (CK * A⁻¹ ^ (lK - 1)) = CK * Φ * A⁻¹ ^ (n + 1) := by
        rw [mul_mul_mul_comm, ← pow_add, mul_comm Φ CK]; congr 2; omega
      rw [e, hT]
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
      calc Φ * A⁻¹ ^ (k + n - l + 1) * δ ≤ Φ * 1 * δ := by
            gcongr; exact pow_inv_le_one hA _
        _ = δ * Φ := by ring
    · simpa using hT0
  calc ‖couplingLen L W lK K D I‖ ≤ ‖primBilLen L W lK K D I‖ + ‖primBilLenR L W lK D K I‖ :=
        norm_add_le _ _
    _ ≤ W * n ^ 2 * T + W * n ^ 2 * T := add_le_add hleft hright
    _ = _ := by
        rw [hT, pow_succ, div_eq_mul_inv]
        ring

/-- The first line of (5.77) with the exact cut-and-glue length range `2 ≤ |J| ≤ |I|`. -/
theorem norm_couplingLen_le' (hL : 3 ≤ L) (W : ℕ) {lK : ℕ} (hlK : 3 ≤ lK)
    {K D : LoopIdx (ZMod L) → ℂ} {I : LoopIdx (ZMod L)} (hI : I.WF) {A ℓ δ CK Φ : ℝ}
    (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hCK : 0 ≤ CK) (hΦ : 0 ≤ Φ)
    (hK : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K J‖ ≤ CK * A⁻¹ ^ (J.length - 1))
    (hKd : LoopDecay L I.length ℓ δ K)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → J.length < I.length → ‖D J‖ ≤ Φ * A⁻¹ ^ J.length) :
    ‖couplingLen L W lK K D I‖
      ≤ 4 * exp 1 * I.length ^ 2 * CK * Φ * ((W : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ I.length
        + 2 * I.length ^ 2 * W * L * δ * Φ := by
  set n := I.length with hn
  have hA0 : 0 < A := by linarith
  set T : ℝ := 2 * exp 1 * (ℓ + 1) * (CK * Φ * A⁻¹ ^ (n + 1)) + L * (δ * Φ) with hT
  have hT0 : 0 ≤ T := by positivity
  have hleft : ‖primBilLen L W lK K D I‖ ≤ W * n ^ 2 * T := by
    refine norm_W_sum_le W n _ hT0 fun k hk l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    rw [primBilLen_summand L K D I hk.1 hl.1 hl.2]
    split_ifs with h
    · have hF : ∀ a, ‖K (I.cutGlueL k l a)‖ ≤ CK * A⁻¹ ^ (lK - 1) := fun a => by
        have := hK _ (hI.cutGlueL a hk.1 hl.1 hl.2)
          (LoopIdx.two_le_length_cutGlueL I a hk.1 hl.1 hl.2)
          (LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2)
        rwa [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2, h] at this
      have hG : ∀ b, ‖D (I.cutGlueR k l b)‖ ≤ Φ * A⁻¹ ^ (l - k + 1) := fun b => by
        have := hD _ (hI.cutGlueR b hk.1 hl.1 hl.2)
          (by rw [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2]; omega)
        rwa [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2] at this
      refine (norm_glueTerm_le_left L hL hI hk.1 hl.1 hl.2 hℓ hδ hKd hF hG).trans ?_
      have e : CK * A⁻¹ ^ (lK - 1) * (Φ * A⁻¹ ^ (l - k + 1)) = CK * Φ * A⁻¹ ^ (n + 1) := by
        rw [mul_mul_mul_comm, ← pow_add]; congr 2; omega
      rw [e, hT]
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
      calc δ * (Φ * A⁻¹ ^ (l - k + 1)) ≤ δ * (Φ * 1) := by
            gcongr; exact pow_inv_le_one hA _
        _ = δ * Φ := by ring
    · simpa using hT0
  have hright : ‖primBilLenR L W lK D K I‖ ≤ W * n ^ 2 * T := by
    refine norm_W_sum_le W n _ hT0 fun k hk l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    rw [primBilLenR_summand L D K I hk.1 hl.1 hl.2]
    split_ifs with h
    · have hG : ∀ b, ‖K (I.cutGlueR k l b)‖ ≤ CK * A⁻¹ ^ (lK - 1) := fun b => by
        have := hK _ (hI.cutGlueR b hk.1 hl.1 hl.2)
          (LoopIdx.two_le_length_cutGlueR I b hk.1 hl.1 hl.2)
          (LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2)
        rwa [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2, h] at this
      have hF : ∀ a, ‖D (I.cutGlueL k l a)‖ ≤ Φ * A⁻¹ ^ (k + n - l + 1) := fun a => by
        have := hD _ (hI.cutGlueL a hk.1 hl.1 hl.2)
          (by rw [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2]; omega)
        rwa [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2] at this
      refine (norm_glueTerm_le_right L hL hI hk.1 hl.1 hl.2 hℓ hδ hKd hF hG).trans ?_
      have e : Φ * A⁻¹ ^ (k + n - l + 1) * (CK * A⁻¹ ^ (lK - 1)) = CK * Φ * A⁻¹ ^ (n + 1) := by
        rw [mul_mul_mul_comm, ← pow_add, mul_comm Φ CK]; congr 2; omega
      rw [e, hT]
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
      calc Φ * A⁻¹ ^ (k + n - l + 1) * δ ≤ Φ * 1 * δ := by
            gcongr; exact pow_inv_le_one hA _
        _ = δ * Φ := by ring
    · simpa using hT0
  calc ‖couplingLen L W lK K D I‖ ≤ ‖primBilLen L W lK K D I‖ + ‖primBilLenR L W lK D K I‖ :=
        norm_add_le _ _
    _ ≤ W * n ^ 2 * T + W * n ^ 2 * T := add_le_add hleft hright
    _ = _ := by
        rw [hT, pow_succ, div_eq_mul_inv]
        ring

/-- **Lemma 5.10, (5.77), second line**: `E^{((L-K)×(L-K))} = primBil D D` ((5.13), `D = L - K`).

With `|D_{σ,a}| ≤ X_m A^{-m}` for loops of length `2 ≤ m ≤ n` (i.e. `X_m = Ξ^{(L-K)}_{u,m}`),
`X_m X_{n-m+2} A^{-1} ≤ Φ` for `2 ≤ m ≤ n`, `X_m ≤ B`, and `D` having `(ℓ, δ)` decay:
`|E^{((L-K)×(L-K))}_{σ,a}| ≤ 2e n² Φ (W(ℓ+1)/A) A^{-n} + n² W L δ B`.
The paper's bound is `max_{2≤k≤n} Ξ_k Ξ_{n-k+2} (Wℓη)^{-1} · (Wℓη)^{-n} η^{-1}`. -/
theorem norm_primBil_sub_le (hL : 3 ≤ L) (W : ℕ) {D : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {A ℓ δ Φ B : ℝ} (X : ℕ → ℝ)
    (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hΦ : 0 ≤ Φ) (hB : 0 ≤ B)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖D J‖ ≤ X J.length * A⁻¹ ^ J.length)
    (hX : ∀ m, 2 ≤ m → m ≤ I.length → X m * X (I.length - m + 2) * A⁻¹ ≤ Φ)
    (hXB : ∀ m, 2 ≤ m → m ≤ I.length → X m ≤ B)
    (hDd : LoopDecay L I.length ℓ δ D) :
    ‖primBil L W D D I‖
      ≤ 2 * exp 1 * I.length ^ 2 * Φ * ((W : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ I.length
        + I.length ^ 2 * W * L * δ * B := by
  set n := I.length with hn
  have hA0 : 0 < A := by linarith
  set T : ℝ := 2 * exp 1 * (ℓ + 1) * (Φ * A⁻¹ ^ (n + 1)) + L * (δ * B) with hT
  have hT0 : 0 ≤ T := by positivity
  have key : ‖primBil L W D D I‖ ≤ W * n ^ 2 * T := by
    refine norm_W_sum_le W n (glueTerm L D D I) hT0 fun k hk l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    set p := k + n - l + 1 with hp
    set q := l - k + 1 with hq
    have hpq : q = n - p + 2 := by omega
    have hF : ∀ a, ‖D (I.cutGlueL k l a)‖ ≤ X p * A⁻¹ ^ p := fun a => by
      have := hD _ (hI.cutGlueL a hk.1 hl.1 hl.2)
        (by rw [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2]; omega)
        (by rw [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2]; omega)
      rwa [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2] at this
    have hG : ∀ b, ‖D (I.cutGlueR k l b)‖ ≤ X q * A⁻¹ ^ q := fun b => by
      have := hD _ (hI.cutGlueR b hk.1 hl.1 hl.2)
        (by rw [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2]; omega)
        (by rw [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2]; omega)
      rwa [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2] at this
    refine (norm_glueTerm_le_left L hL hI hk.1 hl.1 hl.2 hℓ hδ hDd hF hG).trans ?_
    have hXX : X p * X q * A⁻¹ ≤ Φ := by rw [hpq]; exact hX p (by omega) (by omega)
    have e : X p * A⁻¹ ^ p * (X q * A⁻¹ ^ q) = X p * X q * A⁻¹ * A⁻¹ ^ (n + 1) := by
      rw [mul_mul_mul_comm, mul_assoc (X p * X q), ← pow_succ', ← pow_add]; congr 2; omega
    rw [e, hT]
    refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    · gcongr
    · calc δ * (X q * A⁻¹ ^ q) ≤ δ * (B * 1) := by
            gcongr
            · exact hXB q (by omega) (by omega)
            · exact pow_inv_le_one hA _
        _ = δ * B := by ring
  refine key.trans (le_of_eq ?_)
  rw [hT, pow_succ, div_eq_mul_inv]
  ring

/-! #### The `E`-terms decay ("Furthermore" of Lemma 5.10) -/

omit [NeZero L] in
theorem mem_ofFn_of_fastDecay {n : ℕ} {a : LoopArg L n} {ℓ : ℝ}
    (h : ∃ i j, ℓ ≤ (zdist L (a i - a j) : ℝ)) :
    ∃ x ∈ List.ofFn a, ∃ y ∈ List.ofFn a, ℓ ≤ (zdist L (x - y) : ℝ) := by
  obtain ⟨i, j, hij⟩ := h
  exact ⟨a i, List.mem_ofFn.2 ⟨i, rfl⟩, a j, List.mem_ofFn.2 ⟨j, rfl⟩, hij⟩

omit [NeZero L] in
theorem wf_ofFn {n : ℕ} {σ : List Bool} (hσ : σ.length = n) (a : LoopArg L n) :
    (⟨σ, List.ofFn a⟩ : LoopIdx (ZMod L)).WF := by
  simp [LoopIdx.WF, hσ]

/-- **(5.14) decays**: if `K` and `D = L - K` have `(ℓ, δ)` decay and are bounded by `M_K`,
`M_D` on loops of length `≤ n`, then `[K ∼ (L - K)]^{l_K}_{σ,a}` is `≤ 2Wn²Lδ(M_K + M_D)` as
soon as two labels of `a` are at distance `≥ 2ℓ + 1`. -/
theorem norm_couplingLen_le_of_far (hL : 3 ≤ L) (W lK : ℕ) {K D : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {ℓ δ MK MD : ℝ} (hδ : 0 ≤ δ) (hMK : 0 ≤ MK)
    (hMD : 0 ≤ MD) (hKd : LoopDecay L I.length ℓ δ K) (hDd : LoopDecay L I.length ℓ δ D)
    (hK : ∀ J : LoopIdx (ZMod L), J.WF → J.length ≤ I.length → ‖K J‖ ≤ MK)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → J.length ≤ I.length → ‖D J‖ ≤ MD)
    {x y : ZMod L} (hx : x ∈ I.a) (hy : y ∈ I.a) (hxy : 2 * ℓ + 1 ≤ (zdist L (x - y) : ℝ)) :
    ‖couplingLen L W lK K D I‖ ≤ 2 * W * I.length ^ 2 * L * δ * (MK + MD) := by
  set n := I.length with hn
  have hT0 : 0 ≤ (L : ℝ) * δ * (MK + MD) := by positivity
  have hleft : ‖primBilLen L W lK K D I‖ ≤ W * n ^ 2 * (L * δ * (MK + MD)) := by
    refine norm_W_sum_le W n _ hT0 fun k hk l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    rw [primBilLen_summand L K D I hk.1 hl.1 hl.2]
    split_ifs
    · refine (norm_glueTerm_le_of_far L hL hI hk.1 hl.1 hl.2 hδ hKd hDd
        (fun a => hK _ (hI.cutGlueL a hk.1 hl.1 hl.2)
          (LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2))
        (fun b => hD _ (hI.cutGlueR b hk.1 hl.1 hl.2)
          (LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2)) hx hy hxy).trans (le_of_eq ?_)
      ring
    · simpa using hT0
  have hright : ‖primBilLenR L W lK D K I‖ ≤ W * n ^ 2 * (L * δ * (MK + MD)) := by
    refine norm_W_sum_le W n _ hT0 fun k hk l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    rw [primBilLenR_summand L D K I hk.1 hl.1 hl.2]
    split_ifs
    · refine (norm_glueTerm_le_of_far L hL hI hk.1 hl.1 hl.2 hδ hDd hKd
        (fun a => hD _ (hI.cutGlueL a hk.1 hl.1 hl.2)
          (LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2))
        (fun b => hK _ (hI.cutGlueR b hk.1 hl.1 hl.2)
          (LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2)) hx hy hxy).trans (le_of_eq ?_)
      ring
    · simpa using hT0
  calc ‖couplingLen L W lK K D I‖ ≤ ‖primBilLen L W lK K D I‖ + ‖primBilLenR L W lK D K I‖ :=
        norm_add_le _ _
    _ ≤ _ := add_le_add hleft hright
    _ = _ := by ring

/-- `[K ∼ (L - K)]^{l_K}_{t,σ}` is a fast-decaying tensor ((7.13), T51's `FastDecay`) with
`ℓ' = 2ℓ + 1`, `δ' = 2Wn²Lδ(M_K + M_D)`. -/
theorem fastDecay_couplingLen (hL : 3 ≤ L) (W lK : ℕ) {K D : LoopIdx (ZMod L) → ℂ} {n : ℕ}
    {σ : List Bool} (hσ : σ.length = n) {ℓ δ MK MD : ℝ} (hδ : 0 ≤ δ) (hMK : 0 ≤ MK)
    (hMD : 0 ≤ MD) (hKd : LoopDecay L n ℓ δ K) (hDd : LoopDecay L n ℓ δ D)
    (hK : ∀ J : LoopIdx (ZMod L), J.WF → J.length ≤ n → ‖K J‖ ≤ MK)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → J.length ≤ n → ‖D J‖ ≤ MD) :
    FastDecay L (2 * ℓ + 1) (2 * W * n ^ 2 * L * δ * (MK + MD))
      (fun a : LoopArg L n => couplingLen L W lK K D ⟨σ, List.ofFn a⟩) := by
  intro a ha
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_ofFn_of_fastDecay L ha
  have hlen : (⟨σ, List.ofFn a⟩ : LoopIdx (ZMod L)).length = n := by simp [LoopIdx.length]
  have := norm_couplingLen_le_of_far L hL W lK (wf_ofFn L hσ a) hδ hMK hMD
    (by rw [hlen]; exact hKd) (by rw [hlen]; exact hDd)
    (fun J hJ h => hK J hJ (h.trans hlen.le)) (fun J hJ h => hD J hJ (h.trans hlen.le))
    hx hy hxy
  rwa [hlen] at this

/-- **(5.13) decays**: `E^{((L-K)×(L-K))}_{σ,a} ≤ 2Wn²Lδ M_D` once two labels are
`≥ 2ℓ + 1` apart. -/
theorem norm_primBil_le_of_far (hL : 3 ≤ L) (W : ℕ) {D : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {ℓ δ MD : ℝ} (hδ : 0 ≤ δ) (hMD : 0 ≤ MD)
    (hDd : LoopDecay L I.length ℓ δ D)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → J.length ≤ I.length → ‖D J‖ ≤ MD)
    {x y : ZMod L} (hx : x ∈ I.a) (hy : y ∈ I.a) (hxy : 2 * ℓ + 1 ≤ (zdist L (x - y) : ℝ)) :
    ‖primBil L W D D I‖ ≤ 2 * W * I.length ^ 2 * L * δ * MD := by
  have hT0 : 0 ≤ (L : ℝ) * (δ * MD + MD * δ) := by positivity
  refine (norm_W_sum_le W I.length (glueTerm L D D I) hT0 fun k hk l hl => ?_).trans
    (le_of_eq (by ring))
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  exact norm_glueTerm_le_of_far L hL hI hk.1 hl.1 hl.2 hδ hDd hDd
    (fun a => hD _ (hI.cutGlueL a hk.1 hl.1 hl.2) (LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2))
    (fun b => hD _ (hI.cutGlueR b hk.1 hl.1 hl.2) (LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2))
    hx hy hxy

theorem fastDecay_primBil (hL : 3 ≤ L) (W : ℕ) {D : LoopIdx (ZMod L) → ℂ} {n : ℕ}
    {σ : List Bool} (hσ : σ.length = n) {ℓ δ MD : ℝ} (hδ : 0 ≤ δ) (hMD : 0 ≤ MD)
    (hDd : LoopDecay L n ℓ δ D)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → J.length ≤ n → ‖D J‖ ≤ MD) :
    FastDecay L (2 * ℓ + 1) (2 * W * n ^ 2 * L * δ * MD)
      (fun a : LoopArg L n => primBil L W D D ⟨σ, List.ofFn a⟩) := by
  intro a ha
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_ofFn_of_fastDecay L ha
  have hlen : (⟨σ, List.ofFn a⟩ : LoopIdx (ZMod L)).length = n := by simp [LoopIdx.length]
  have := norm_primBil_le_of_far L hL W (wf_ofFn L hσ a) hδ hMD (by rw [hlen]; exact hDd)
    (fun J hJ h => hD J hJ (h.trans hlen.le)) hx hy hxy
  rwa [hlen] at this

end Coupling

/-! ### The Itô correction `E^{(G)}` (2.47) -/

section EG

/-- **(2.47)** `E^{(G)}_{t,σ,a} = W ∑_{k} ∑_{a,b} ⟨(G_t(σ_k) - m(σ_k)) E_a⟩ S^(B)_{ab}
(G^{(b)}_k ∘ L_{t,σ,a})`, with the one-loop `⟨(G(σ_k) - m) E_a⟩ = (L - K)_{(σ_k),(a)}`
supplied as `X` (evaluated at the one-edge loop `((σ_k), (a))`) and the loops as `Y`. -/
noncomputable def eG (W : ℕ) (X Y : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) : ℂ :=
  (W : ℂ) * ∑ k ∈ Icc 1 I.length, ∑ a : ZMod L, ∑ b : ZMod L,
    X ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b * Y (I.cutGlue k b)

/-- **Lemma 5.10, (5.77), third line**: `E^{(G)}`.

With `|(L - K)_{(s),(a)}| ≤ Ξ₂ A^{-1}` for the one-loops (the paper's
`Ξ^{(L)}_{u,2} (Wℓ_uη_u)^{-1}`, from (4.5)), `|L_{σ,a}| ≤ Φ A^{-n}` for loops of length
`n + 1` (`Ξ^{(L)}_{u,n+1} ≤ Φ`), and `L` having `(ℓ, δ)` decay:
`|E^{(G)}_{σ,a}| ≤ 2e n Ξ₂ Φ (W(ℓ+1)/A) A^{-n} + n W L δ Ξ₂`.
The paper states `Ξ^{(L)}_{u,n+1} (Wℓη)^{-n} η^{-1}`, having used `Ξ^{(L)}_{u,2} ≺ 1`. -/
theorem norm_eG_le (hL : 3 ≤ L) (W : ℕ) {X Y : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {A ℓ δ Ξ₂ Φ : ℝ}
    (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hΞ₂ : 0 ≤ Ξ₂)
    (hX : ∀ (s : Bool) (a : ZMod L), ‖X ⟨[s], [a]⟩‖ ≤ Ξ₂ * A⁻¹)
    (hY : ∀ J : LoopIdx (ZMod L), J.WF → J.length = I.length + 1 →
      ‖Y J‖ ≤ Φ * A⁻¹ ^ I.length)
    (hYd : LoopDecay L (I.length + 1) ℓ δ Y) :
    ‖eG L W X Y I‖
      ≤ 2 * exp 1 * I.length * Ξ₂ * Φ * ((W : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ I.length
        + I.length * W * L * δ * Ξ₂ := by
  set n := I.length with hn
  have hA0 : 0 < A := by linarith
  have hAi : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  set T : ℝ := 2 * exp 1 * (ℓ + 1) * (Ξ₂ * Φ * A⁻¹ ^ (n + 1)) + L * (Ξ₂ * δ) with hT
  have key : ‖eG L W X Y I‖ ≤ W * n * T := by
    refine norm_W_sum_le' W n _ fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hn0 : 0 < I.a.length := by simp only [hn, LoopIdx.length] at hk; omega
    have hcm : ∀ b, I.a[0] ∈ (I.cutGlue k b).a := fun b =>
      mem_cutGlue_of_mem I b k (List.getElem_mem hn0)
    have hYk : ∀ b, ‖Y (I.cutGlue k b)‖ ≤ Φ * A⁻¹ ^ n := fun b =>
      hY _ (hI.cutGlue b hk.1 hk.2) (LoopIdx.length_cutGlue I b hk.2)
    have e : ∑ a : ZMod L, ∑ b : ZMod L,
        X ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b * Y (I.cutGlue k b)
        = ∑ a : ZMod L, ∑ b : ZMod L,
          SB L a b * (X ⟨[I.σ.getD (k - 1) true], [a]⟩ * Y (I.cutGlue k b)) :=
      sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    rw [e]
    have hAi0 : 0 ≤ A⁻¹ := inv_nonneg.2 hA0.le
    refine (norm_sum_SB_le_right L hL hℓ (M := Ξ₂ * A⁻¹ * (Φ * A⁻¹ ^ n))
      (δ := Ξ₂ * A⁻¹ * δ) (by positivity) I.a[0] _ (fun a b => ?_)
      (fun a b h => ?_)).trans ?_
    · rw [norm_mul]; exact mul_le_mul (hX _ a) (hYk b) (norm_nonneg _) (by positivity)
    · rw [norm_mul]
      refine mul_le_mul (hX _ a) ?_ (norm_nonneg _) (by positivity)
      exact hYd _ (hI.cutGlue b hk.1 hk.2) (LoopIdx.length_cutGlue I b hk.2).le b
        (mem_cutGlue I b k) _ (hcm b) h
    · rw [hT]
      have e2 : Ξ₂ * A⁻¹ * (Φ * A⁻¹ ^ n) = Ξ₂ * Φ * A⁻¹ ^ (n + 1) := by rw [pow_succ]; ring
      rw [e2]
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
      calc Ξ₂ * A⁻¹ * δ ≤ Ξ₂ * 1 * δ := by gcongr
        _ = Ξ₂ * δ := by ring
  refine key.trans (le_of_eq ?_)
  rw [hT, pow_succ, div_eq_mul_inv]
  ring

/-- **(2.47) decays**: every label of `a` survives in `G^{(b)}_k(σ, a)`, so `E^{(G)}_{σ,a}` is
`≤ WnL M_X δ` once two labels are `≥ ℓ` apart. -/
theorem norm_eG_le_of_far (W : ℕ) (hL : 3 ≤ L) {X Y : LoopIdx (ZMod L) → ℂ}
    {I : LoopIdx (ZMod L)} (hI : I.WF) {ℓ δ MX : ℝ}
    (hX : ∀ (s : Bool) (a : ZMod L), ‖X ⟨[s], [a]⟩‖ ≤ MX) (hYd : LoopDecay L (I.length + 1) ℓ δ Y)
    {x y : ZMod L} (hx : x ∈ I.a) (hy : y ∈ I.a) (hxy : ℓ ≤ (zdist L (x - y) : ℝ)) :
    ‖eG L W X Y I‖ ≤ W * I.length * (L * (MX * δ)) := by
  have hMX : 0 ≤ MX := (norm_nonneg _).trans (hX true 0)
  refine norm_W_sum_le' W I.length _ fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  calc ‖∑ a : ZMod L, ∑ b : ZMod L,
        X ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b * Y (I.cutGlue k b)‖
      ≤ ∑ a : ZMod L, ∑ b : ZMod L,
          ‖X ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b * Y (I.cutGlue k b)‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a : ZMod L, ∑ b : ZMod L, ‖SB L a b‖ * (MX * δ) := by
        refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
        have hY := hYd _ (hI.cutGlue b hk.1 hk.2) (LoopIdx.length_cutGlue I b hk.2).le x
          (mem_cutGlue_of_mem I b k hx) y
          (mem_cutGlue_of_mem I b k hy) hxy
        rw [norm_mul, norm_mul]
        have := hX (I.σ.getD (k - 1) true) a
        have h0 := norm_nonneg (SB L a b)
        nlinarith [norm_nonneg (X ⟨[I.σ.getD (k - 1) true], [a]⟩),
          norm_nonneg (Y (I.cutGlue k b)), mul_le_mul this hY (norm_nonneg _) hMX]
    _ = L * (MX * δ) := by
        simp only [← sum_mul, sum_norm_SB_apply_row L hL, one_mul, sum_const, card_univ,
          ZMod.card, nsmul_eq_mul]
        ring

theorem fastDecay_eG (W : ℕ) (hL : 3 ≤ L) {X Y : LoopIdx (ZMod L) → ℂ} {n : ℕ}
    {σ : List Bool} (hσ : σ.length = n) {ℓ δ MX : ℝ}
    (hX : ∀ (s : Bool) (a : ZMod L), ‖X ⟨[s], [a]⟩‖ ≤ MX) (hYd : LoopDecay L (n + 1) ℓ δ Y) :
    FastDecay L ℓ (W * n * (L * (MX * δ)))
      (fun a : LoopArg L n => eG L W X Y ⟨σ, List.ofFn a⟩) := by
  intro a ha
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_ofFn_of_fastDecay L ha
  have hlen : (⟨σ, List.ofFn a⟩ : LoopIdx (ZMod L)).length = n := by simp [LoopIdx.length]
  have := norm_eG_le_of_far L W hL (wf_ofFn L hσ a) hX (by rw [hlen]; exact hYd) hx hy hxy
  rwa [hlen] at this

end EG

/-! ### `E ⊗ E` (Definition 5.4), abstractly -/

section ETens

/-- **(5.22)** `(E⊗E)_{t,σ,a,a'} = W ∑_{k=1}^n ∑_{b,b'} S^(B)_{bb'} L_{t,σ^{(k)},a^{(k)}}`, for an
arbitrary gluing `J k b b' = (σ^{(k)}, a^{(k)})` (the loop (5.23) obtained by cutting the
`k`-th edge of `L_{σ,a}` and of its conjugate `L_{σ,a'}` and gluing with `E_b`, `E_{b'}`;
the pair `a, a'` is fixed and built into `J`).  Only the properties of (5.23) used in
Lemma 5.10 are assumed of `J`: `J k b b'` is a well-formed loop of length `2n + 2` that
contains `b` and a label `c_k` not depending on `b, b'` (in (5.23): `a_k`). -/
noncomputable def eTens (W : ℕ) (Y : LoopIdx (ZMod L) → ℂ) (n : ℕ)
    (J : ℕ → ZMod L → ZMod L → LoopIdx (ZMod L)) : ℂ :=
  (W : ℂ) * ∑ k ∈ Icc 1 n, ∑ b : ZMod L, ∑ b' : ZMod L, SB L b b' * Y (J k b b')

/-- **Lemma 5.10, (5.77), fourth line**: `E ⊗ E`.

With `|L_{σ,a}| ≤ Φ A^{-(2n+1)}` for loops of length `2n + 2` (`Ξ^{(L)}_{u,2n+2} ≤ Φ`) and `L`
having `(ℓ, δ)` decay:
`|(E⊗E)| ≤ 2e n Φ (W(ℓ+1)/A) A^{-2n} + n W L δ`, the paper's
`Ξ^{(L)}_{u,2n+2} (Wℓη)^{-2n} η^{-1}` ((5.81)). -/
theorem norm_eTens_le (hL : 3 ≤ L) (W : ℕ) {Y : LoopIdx (ZMod L) → ℂ} (n : ℕ)
    {J : ℕ → ZMod L → ZMod L → LoopIdx (ZMod L)} {A ℓ δ Φ : ℝ}
    (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ)
    (hJ : ∀ k b b', (J k b b').WF ∧ (J k b b').length = 2 * n + 2)
    (hJb : ∀ k b b', b ∈ (J k b b').a) (hJc : ∀ k, ∃ c, ∀ b b', c ∈ (J k b b').a)
    (hY : ∀ J' : LoopIdx (ZMod L), J'.WF → J'.length = 2 * n + 2 →
      ‖Y J'‖ ≤ Φ * A⁻¹ ^ (2 * n + 1))
    (hYd : LoopDecay L (2 * n + 2) ℓ δ Y) :
    ‖eTens L W Y n J‖ ≤ 2 * exp 1 * n * Φ * ((W : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ (2 * n)
        + n * W * L * δ := by
  have hA0 : 0 < A := by linarith
  have key : ‖eTens L W Y n J‖ ≤ W * n * (2 * exp 1 * (ℓ + 1) * (Φ * A⁻¹ ^ (2 * n + 1))
      + L * δ) := by
    refine norm_W_sum_le' W n _ fun k _ => ?_
    obtain ⟨c, hc⟩ := hJc k
    exact norm_sum_SB_le_left L hL hℓ hδ c _ (fun b b' => hY _ (hJ k b b').1 (hJ k b b').2)
      (fun b b' h => hYd _ (hJ k b b').1 (hJ k b b').2.le b (hJb k b b') c (hc b b') h)
  refine key.trans (le_of_eq ?_)
  rw [pow_succ, div_eq_mul_inv]
  ring

/-- **(5.22) decays**: if every glued loop `J k b b'` has two labels `≥ ℓ` apart (for (5.23):
two labels of `a` or of `a'`), then `|(E⊗E)| ≤ WnLδ`. -/
theorem norm_eTens_le_of_far (hL : 3 ≤ L) (W : ℕ) {Y : LoopIdx (ZMod L) → ℂ} (n : ℕ)
    {J : ℕ → ZMod L → ZMod L → LoopIdx (ZMod L)} {ℓ δ : ℝ}
    (hJ : ∀ k b b', (J k b b').WF ∧ (J k b b').length = 2 * n + 2) (hYd : LoopDecay L (2 * n + 2) ℓ δ Y)
    (hfar : ∀ k b b', ∃ x ∈ (J k b b').a, ∃ y ∈ (J k b b').a, ℓ ≤ (zdist L (x - y) : ℝ)) :
    ‖eTens L W Y n J‖ ≤ W * n * (L * δ) := by
  refine norm_W_sum_le' W n _ fun k _ => ?_
  calc ‖∑ b : ZMod L, ∑ b' : ZMod L, SB L b b' * Y (J k b b')‖
      ≤ ∑ b : ZMod L, ∑ b' : ZMod L, ‖SB L b b' * Y (J k b b')‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ b : ZMod L, ∑ b' : ZMod L, ‖SB L b b'‖ * δ := by
        refine sum_le_sum fun b _ => sum_le_sum fun b' _ => ?_
        obtain ⟨x, hx, y, hy, hxy⟩ := hfar k b b'
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hYd _ (hJ k b b').1 (hJ k b b').2.le x hx y hy hxy) (norm_nonneg _)
    _ = L * δ := by
        simp only [← sum_mul, sum_norm_SB_apply_row L hL, one_mul, sum_const, card_univ,
          ZMod.card, nsmul_eq_mul]

end ETens

/-! ### (5.77) in tensor form (the shape consumed by `Uker`, `Qop`) -/

section Tensor

/-- A loop function at fixed charges `σ`, as a tensor `a ↦ F_{σ,a}` on `ℤ_L^n`. -/
noncomputable def loopTensor {n : ℕ} (F : LoopIdx (ZMod L) → ℂ) (σ : Fin n → Bool) :
    LoopArg L n → ℂ :=
  fun b => F ⟨List.ofFn σ, List.ofFn b⟩

omit [NeZero L] in
theorem wf_loopTensor {n : ℕ} (σ : Fin n → Bool) (b : LoopArg L n) :
    (⟨List.ofFn σ, List.ofFn b⟩ : LoopIdx (ZMod L)).WF := by
  simp [LoopIdx.WF]

omit [NeZero L] in
@[simp] theorem length_loopTensor {n : ℕ} (σ : Fin n → Bool) (b : LoopArg L n) :
    (⟨List.ofFn σ, List.ofFn b⟩ : LoopIdx (ZMod L)).length = n := by
  simp [LoopIdx.length]

/-- **(5.77), first line, tensor form**: `‖[K ∼ (L-K)]^{l_K}_{σ,b}‖ ≤ M⋆ A^{-n} + err`. -/
theorem norm_loopTensor_couplingLen_le (hL : 3 ≤ L) (W : ℕ) {n lK : ℕ} (hlK : 3 ≤ lK)
    {K D : LoopIdx (ZMod L) → ℂ} (σ : Fin n → Bool) {A ℓ δ CK Φ : ℝ}
    (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hCK : 0 ≤ CK) (hΦ : 0 ≤ Φ)
    (hK : ∀ J : LoopIdx (ZMod L), J.WF → ‖K J‖ ≤ CK * A⁻¹ ^ (J.length - 1))
    (hKd : LoopDecay L n ℓ δ K)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → J.length < n → ‖D J‖ ≤ Φ * A⁻¹ ^ J.length)
    (b : LoopArg L n) :
    ‖loopTensor L (couplingLen L W lK K D) σ b‖
      ≤ 4 * exp 1 * n ^ 2 * CK * Φ * ((W : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ n
        + 2 * n ^ 2 * W * L * δ * Φ := by
  have := norm_couplingLen_le L hL W hlK (wf_loopTensor L σ b) hA hℓ hδ hCK hΦ hK
    (by rw [length_loopTensor]; exact hKd) (by rw [length_loopTensor]; exact hD)
  rwa [length_loopTensor] at this

/-- Tensor form of the bounded-length first line of (5.77). -/
theorem norm_loopTensor_couplingLen_le' (hL : 3 ≤ L) (W : ℕ) {n lK : ℕ} (hlK : 3 ≤ lK)
    {K D : LoopIdx (ZMod L) → ℂ} (σ : Fin n → Bool) {A ℓ δ CK Φ : ℝ}
    (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hCK : 0 ≤ CK) (hΦ : 0 ≤ Φ)
    (hK : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖K J‖ ≤ CK * A⁻¹ ^ (J.length - 1))
    (hKd : LoopDecay L n ℓ δ K)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → J.length < n → ‖D J‖ ≤ Φ * A⁻¹ ^ J.length)
    (b : LoopArg L n) :
    ‖loopTensor L (couplingLen L W lK K D) σ b‖
      ≤ 4 * exp 1 * n ^ 2 * CK * Φ * ((W : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ n
        + 2 * n ^ 2 * W * L * δ * Φ := by
  have := norm_couplingLen_le' L hL W hlK (wf_loopTensor L σ b) hA hℓ hδ hCK hΦ
    (fun J hJ hJ2 hJn => hK J hJ hJ2 (by rw [length_loopTensor] at hJn; exact hJn))
    (by rw [length_loopTensor]; exact hKd) (by rw [length_loopTensor]; exact hD)
  rwa [length_loopTensor] at this

/-- **(5.77), second line, tensor form**. -/
theorem norm_loopTensor_primBil_le (hL : 3 ≤ L) (W : ℕ) {n : ℕ} {D : LoopIdx (ZMod L) → ℂ}
    (σ : Fin n → Bool) {A ℓ δ Φ B : ℝ} (X : ℕ → ℝ)
    (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hΦ : 0 ≤ Φ) (hB : 0 ≤ B)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖D J‖ ≤ X J.length * A⁻¹ ^ J.length)
    (hX : ∀ m, 2 ≤ m → m ≤ n → X m * X (n - m + 2) * A⁻¹ ≤ Φ)
    (hXB : ∀ m, 2 ≤ m → m ≤ n → X m ≤ B)
    (hDd : LoopDecay L n ℓ δ D) (b : LoopArg L n) :
    ‖loopTensor L (primBil L W D D) σ b‖
      ≤ 2 * exp 1 * n ^ 2 * Φ * ((W : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ n + n ^ 2 * W * L * δ * B := by
  have := norm_primBil_sub_le L hL W (wf_loopTensor L σ b) X hA hℓ hδ hΦ hB
    (by rw [length_loopTensor]; exact hD) (by rw [length_loopTensor]; exact hX)
    (by rw [length_loopTensor]; exact hXB) (by rw [length_loopTensor]; exact hDd)
  rwa [length_loopTensor] at this

/-- **(5.77), third line, tensor form**. -/
theorem norm_loopTensor_eG_le (hL : 3 ≤ L) (W : ℕ) {n : ℕ} {X Y : LoopIdx (ZMod L) → ℂ}
    (σ : Fin n → Bool) {A ℓ δ Ξ₂ Φ : ℝ}
    (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hΞ₂ : 0 ≤ Ξ₂)
    (hX : ∀ (s : Bool) (a : ZMod L), ‖X ⟨[s], [a]⟩‖ ≤ Ξ₂ * A⁻¹)
    (hY : ∀ J : LoopIdx (ZMod L), J.WF → J.length = n + 1 → ‖Y J‖ ≤ Φ * A⁻¹ ^ n)
    (hYd : LoopDecay L (n + 1) ℓ δ Y) (b : LoopArg L n) :
    ‖loopTensor L (eG L W X Y) σ b‖
      ≤ 2 * exp 1 * n * Ξ₂ * Φ * ((W : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ n + n * W * L * δ * Ξ₂ := by
  have := norm_eG_le L hL W (wf_loopTensor L σ b) hA hℓ hδ hΞ₂ hX
    (by rw [length_loopTensor]; exact hY) (by rw [length_loopTensor]; exact hYd)
  rwa [length_loopTensor] at this

end Tensor

/-! ### Lemma 5.11: the kernel on the `E`-terms for non-alternating `σ` -/

section Lemma511

theorem cKerShort_nonneg (n : ℕ) {κ : ℝ} (hκ : 0 < κ) : 0 ≤ cKerShort n κ := by
  unfold cKerShort
  have := cWin_nonneg
  have := cShort_nonneg
  positivity

/-- **The integrand of (5.84) and (5.86).**  Case 1 of (7.16) (`σ_k = σ_{k+1}`, T51's
`norm_Uker_fastDecay_le_of_eq`) applied to a tensor of the size given by (5.77),
`|E_b| ≤ M⋆ A_u^{-n} + err`, fast-decaying at scale `ℓ_u K`:
`A_t^n |(U_{u,t,σ} ∘ E)_a| ≤ C_{n,κ} K^n c_r^n (M⋆ + A_u^n err) + A_t^n ((1-u)/(1-t))^n δ`.

Here `A_u`, `A_t` are the paper's `W ℓ_u η_u`, `W ℓ_t η_t` in any normalization with
`(1-u) ℓ_u / ((1-t) ℓ_t) ≤ c_r A_u/A_t` (`c_r = 1` for `η_u = 1 - u`).  With `M⋆` from (5.77),
`M⋆ ∝ Ξ · W(ℓ+1)/A_u`, this is the paper's `Ξ/η_u` integrand. -/
theorem pow_mul_norm_Uker_le_of_eq (hL : 3 ≤ L) {n : ℕ} [NeZero n] {E κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) {σ : Fin n → Bool} {k : Fin n} (hk : σ k = σ (k + 1))
    {u t : ℝ} (hu0 : 0 ≤ u) (hut : u ≤ t) (ht1 : t < 1) {K Au At cr Mst err δ : ℝ}
    (hK : 1 ≤ K) (hAu : 0 < Au) (hAt : 0 < At)
    (hR : (1 - u) * ellHat L (u : ℂ) / ((1 - t) * ellHat L (t : ℂ)) ≤ cr * (Au / At))
    (hMst : 0 ≤ Mst) (herr : 0 ≤ err) (hδ : 0 ≤ δ) {A : LoopArg L n → ℂ}
    (hAM : ∀ b, ‖A b‖ ≤ Mst * Au⁻¹ ^ n + err)
    (hAd : FastDecay L (ellHat L (u : ℂ) * K) δ A) (a : LoopArg L n) :
    At ^ n * ‖Uker L (xiOf (mSigma E) σ) u t A a‖
      ≤ cKerShort n √κ * K ^ n * cr ^ n * (Mst + Au ^ n * err)
        + At ^ n * ((1 - u) / (1 - t)) ^ n * δ := by
  have hM0 : 0 ≤ Mst * Au⁻¹ ^ n + err := by positivity
  have h := norm_Uker_fastDecay_le_of_eq L hL hκ0 hκ1 hE hk hu0 hut ht1 hK hM0 hδ hAM hAd a
  have hℓu := ellHat_real_pos L hL hu0 (hut.trans_lt ht1)
  have hℓt := ellHat_real_pos L hL (hu0.trans hut) ht1
  have hR0 : 0 ≤ (1 - u) * ellHat L (u : ℂ) / ((1 - t) * ellHat L (t : ℂ)) := by
    have : 0 ≤ 1 - u := by linarith
    have : 0 ≤ 1 - t := by linarith
    positivity
  have hc := cKerShort_nonneg n (Real.sqrt_pos.2 hκ0)
  have hRn : ((1 - u) * ellHat L (u : ℂ) / ((1 - t) * ellHat L (t : ℂ))) ^ n
      ≤ (cr * (Au / At)) ^ n := pow_le_pow_left₀ hR0 hR n
  have hAtn : 0 < At ^ n := pow_pos hAt n
  calc At ^ n * ‖Uker L (xiOf (mSigma E) σ) u t A a‖
      ≤ At ^ n * (cKerShort n √κ * K ^ n
          * ((1 - u) * ellHat L (u : ℂ) / ((1 - t) * ellHat L (t : ℂ))) ^ n
          * (Mst * Au⁻¹ ^ n + err) + ((1 - u) / (1 - t)) ^ n * δ) :=
        mul_le_mul_of_nonneg_left h hAtn.le
    _ ≤ At ^ n * (cKerShort n √κ * K ^ n * (cr * (Au / At)) ^ n
          * (Mst * Au⁻¹ ^ n + err) + ((1 - u) / (1 - t)) ^ n * δ) := by
        gcongr
    _ = cKerShort n √κ * K ^ n * cr ^ n * (Mst + Au ^ n * err)
          + At ^ n * ((1 - u) / (1 - t)) ^ n * δ := by
        rw [mul_pow, div_pow, inv_pow]
        field_simp

/-- **(5.84), the `[K ∼ (L - K)]^{l_K}` integrand, assembled**: (5.77) (`norm_couplingLen_le`)
and the decay of the `E`-term (`fastDecay_couplingLen`) plugged into Case 1 of (7.16).
The decay radius `2ℓ + 1` of the `E`-term is written `ℓ_u K`. -/
theorem pow_mul_norm_Uker_couplingLen_le (hL : 3 ≤ L) (W : ℕ) {n : ℕ} [NeZero n] {lK : ℕ}
    (hlK : 3 ≤ lK) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    {σ : Fin n → Bool} {k : Fin n} (hk : σ k = σ (k + 1))
    {u t : ℝ} (hu0 : 0 ≤ u) (hut : u ≤ t) (ht1 : t < 1)
    {K D : LoopIdx (ZMod L) → ℂ} {Au At cr ℓ δ CK Φ MD Kw : ℝ}
    (hAu : 1 ≤ Au) (hAt : 0 < At)
    (hR : (1 - u) * ellHat L (u : ℂ) / ((1 - t) * ellHat L (t : ℂ)) ≤ cr * (Au / At))
    (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hCK : 0 ≤ CK) (hΦ : 0 ≤ Φ) (hMD : 0 ≤ MD)
    (hKw : 1 ≤ Kw) (hℓK : 2 * ℓ + 1 = ellHat L (u : ℂ) * Kw)
    (hK : ∀ J : LoopIdx (ZMod L), J.WF → ‖K J‖ ≤ CK * Au⁻¹ ^ (J.length - 1))
    (hKd : LoopDecay L n ℓ δ K) (hDd : LoopDecay L n ℓ δ D)
    (hD : ∀ J : LoopIdx (ZMod L), J.WF → J.length < n → ‖D J‖ ≤ Φ * Au⁻¹ ^ J.length)
    (hDM : ∀ J : LoopIdx (ZMod L), J.WF → J.length ≤ n → ‖D J‖ ≤ MD)
    (a : LoopArg L n) :
    At ^ n * ‖Uker L (xiOf (mSigma E) σ) u t
        (fun b : LoopArg L n => couplingLen L W lK K D ⟨List.ofFn σ, List.ofFn b⟩) a‖
      ≤ cKerShort n √κ * Kw ^ n * cr ^ n
          * (4 * exp 1 * n ^ 2 * CK * Φ * ((W : ℝ) * (ℓ + 1) / Au)
            + Au ^ n * (2 * n ^ 2 * W * L * δ * Φ))
        + At ^ n * ((1 - u) / (1 - t)) ^ n * (2 * W * n ^ 2 * L * δ * (CK + MD)) := by
  have hσ : (List.ofFn σ).length = n := List.length_ofFn
  have hAu0 : 0 < Au := by linarith
  have hlen : ∀ b : LoopArg L n, (⟨List.ofFn σ, List.ofFn b⟩ : LoopIdx (ZMod L)).length = n :=
    fun b => by simp [LoopIdx.length]
  have hKM : ∀ J : LoopIdx (ZMod L), J.WF → J.length ≤ n → ‖K J‖ ≤ CK := fun J hJ _ =>
    (hK J hJ).trans (by
      calc CK * Au⁻¹ ^ (J.length - 1) ≤ CK * 1 := by gcongr; exact pow_inv_le_one hAu _
        _ = CK := mul_one _)
  have hdec := fastDecay_couplingLen L hL W lK hσ hδ hCK hMD hKd hDd hKM hDM
  rw [hℓK] at hdec
  refine pow_mul_norm_Uker_le_of_eq L hL hκ0 hκ1 hE hk hu0 hut ht1 hKw hAu0 hAt hR
    (by positivity) (by positivity) (by positivity) (fun b => ?_) hdec a
  have := norm_couplingLen_le L hL W hlK (wf_ofFn L hσ b) hAu hℓ hδ hCK hΦ hK
    (by rw [hlen b]; exact hKd)
    (fun J hJ h => hD J hJ (by rw [hlen b] at h; exact h))
  rwa [hlen b] at this

/-- `(ℓK + 1)/ℓ ≤ K + 2` for `ℓ ≥ 1/2`: the factor `W(ℓ_u W^τ + 1)/(W ℓ_u η_u)` of (5.77) is
`≤ (W^τ + 2)/η_u`. -/
theorem mul_add_one_div_le {W ℓ η K : ℝ} (hW : 0 < W) (hℓ : 1 / 2 ≤ ℓ) (hη : 0 < η) :
    W * (ℓ * K + 1) / (W * ℓ * η) ≤ (K + 2) / η := by
  have hℓ0 : 0 < ℓ := by linarith
  rw [div_le_div_iff₀ (by positivity) hη]
  have : W * (ℓ * K + 1) * η ≤ (K + 2) * (W * ℓ * η) := by
    have h1 : 1 ≤ 2 * ℓ := by linarith
    have : W * η * 1 ≤ W * η * (2 * ℓ) := mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  linarith

/-- `∫_s^t du/η_u = log((1-s)/(1-t))` with `η_u = 1 - u`: the only loss in (5.84), a
`log W` that `≺` absorbs. -/
theorem integral_inv_one_sub {s t : ℝ} (hst : s ≤ t) (ht1 : t < 1) :
    ∫ u in s..t, (1 - u)⁻¹ = Real.log ((1 - s) / (1 - t)) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => x⁻¹) 1,
    integral_inv_of_pos (by linarith) (by linarith)]

/-- **Lemma 5.11, (5.84) → (5.83), the deterministic assembly.**  Write `x = A_t^n |(L-K)_{t,σ,a}|`
and suppose the integrated hierarchy (5.20), after the triangle inequality, gives
`x ≤ I₀ + ∫_s^t f(u) du + M`, where `I₀ = A_t^n |U_{s,t,σ} ∘ (L-K)_s|` (the initial term),
`f(u) = A_t^n |(U_{u,t,σ} ∘ (drift E-terms)_u)_a|` and `M` the martingale term.  If the drift
integrand is `≤ Ψ/η_u + ε` (this is `pow_mul_norm_Uker_le_of_eq` + (5.77)), then
`x ≤ I₀ + Ψ log((1-s)/(1-t)) + ε(t - s) + M`. -/
theorem lemma511_assembly {s t : ℝ} (hst : s ≤ t) (ht1 : t < 1) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume s t) {x I₀ M Ψ ε : ℝ}
    (hier : x ≤ I₀ + (∫ u in s..t, f u) + M)
    (hfu : ∀ u ∈ Set.Icc s t, f u ≤ Ψ * (1 - u)⁻¹ + ε) :
    x ≤ I₀ + Ψ * Real.log ((1 - s) / (1 - t)) + ε * (t - s) + M := by
  have hc : ContinuousOn (fun u : ℝ => Ψ * (1 - u)⁻¹ + ε) (Set.uIcc s t) := by
    refine ContinuousOn.add (ContinuousOn.mul continuousOn_const ?_) continuousOn_const
    refine ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun u hu => ?_
    rw [Set.uIcc_of_le hst] at hu
    have := hu.2
    linarith
  have hg : IntervalIntegrable (fun u : ℝ => (1 - u)⁻¹) MeasureTheory.volume s t := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun u hu => ?_
    rw [Set.uIcc_of_le hst] at hu
    have := hu.2
    linarith
  have hmono := intervalIntegral.integral_mono_on hst hf hc.intervalIntegrable hfu
  rw [intervalIntegral.integral_add (hg.const_mul Ψ) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_inv_one_sub hst ht1,
    intervalIntegral.integral_const, smul_eq_mul] at hmono
  linarith

end Lemma511

/-! ### Lemma 5.9, the `K` side: the tree representation decays for every `σ` -/

section KDecay

/-- The gap `1 - t ≤ |1 - t m(s) m(s')|` for `|m| ≤ 1`: every edge of every tree of `K` is a
`Θ_ξ` with `|1 - ξ| ≥ 1 - t = η_t`. -/
theorem one_sub_le_norm_one_sub {m : Bool → ℂ} (hm1 : ∀ s, ‖m s‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t)
    (s s' : Bool) : 1 - t ≤ ‖1 - (t : ℂ) * (m s * m s')‖ := by
  have hξ : ‖(t : ℂ) * (m s * m s')‖ ≤ t := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    have := mul_le_mul (hm1 s) (hm1 s') (norm_nonneg _) zero_le_one
    nlinarith
  have := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * (m s * m s'))
  rw [norm_one] at this
  linarith

/-- `Cor35.norm_thetaEdge_le` for an arbitrary pair of charges. -/
theorem norm_thetaEdge_le_gen (hL : 3 ≤ L) {m : Bool → ℂ} (hm1 : ∀ s, ‖m s‖ ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) {δ : ℝ} (hδ : 0 < δ) (s s' : Bool)
    (hgap : δ ≤ ‖1 - (t : ℂ) * (m s * m s')‖) (x y : ZMod L) :
    ‖thetaEdge L m t s s' x y‖ ≤
        (2 * cTwo52 / δ + 1) * exp (-(cZero * Real.sqrt δ * zdist L (x - y))) ∧
      ‖(thetaEdge L m t s s' - 1) x y‖ ≤
        (2 * cTwo52 / δ + 1) * exp (-(cZero * Real.sqrt δ * zdist L (x - y))) := by
  have hξ : ‖(t : ℂ) * (m s * m s')‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    have := mul_le_mul (hm1 s) (hm1 s') (norm_nonneg _) zero_le_one
    nlinarith
  have h := Cor35.norm_Theta_apply_le_of_gap hL hξ hδ hgap x y
  have h1 := Cor35.norm_one_apply_le (L := L) (cZero * Real.sqrt δ) x y
  have he : 0 ≤ exp (-(cZero * Real.sqrt δ * zdist L (x - y))) := (exp_pos _).le
  unfold thetaEdge
  refine ⟨by linarith, ?_⟩
  rw [Matrix.sub_apply]
  calc _ ≤ ‖Theta L (t * (m s * m s')) x y‖ + ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) x y‖ :=
        norm_sub_le _ _
    _ ≤ _ := by linarith

/-- **Corollary 3.5 for every `σ`** (the input of Lemma 5.9 on the `K` side): for `n ≥ 3`,
`|K_{t,σ,a}| ≤ C_n(δ) e^{-c(δ) ‖a_i - a_j‖}` with `δ = 1 - t` (or any `δ` below every gap
`|1 - t m(s)m(s')|`).  Same proof as `RBM.cor35`, via the tree representation `Kgen_eq` and
(2.52); the pure-charge assumption of (3.6) is only used there to get a gap, and `δ = 1 - t`
always is one.  With `δ = η_t`, `c(δ) ‖a_i - a_j‖ = (c/4)‖a_i - a_j‖/η_t^{-1/2}`, which is
`≥ (c/4) W^τ` for `‖a_i - a_j‖ ≥ ℓ_t W^τ`, `ℓ_t = η_t^{-1/2} < L`. -/
theorem norm_Kgen_le_exp (hL : 3 ≤ L) (W : ℕ) [NeZero W] {m : Bool → ℂ}
    (hm1 : ∀ s, ‖m s‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ s s', δ ≤ ‖1 - (t : ℂ) * (m s * m s')‖) (I : LoopIdx (ZMod L)) {n : ℕ}
    (hn : 3 ≤ n) (hlen : I.length = n) {i j : ℕ} (hi : i < n) (hj : j < n) :
    ‖Kgen L W m t I‖
      ≤ cor35Const n δ * exp (-(cor35Rate δ * zdist L (I.a.getD i 0 - I.a.getD j 0))) := by
  have : NeZero n := ⟨by omega⟩
  rw [Kgen_eq W m t hn I hlen, Kn]
  have hκ : 0 < cZero * Real.sqrt δ := mul_pos cZero_pos (Real.sqrt_pos.2 hδ)
  have hB : 1 ≤ 2 * cTwo52 / δ + 1 := by
    have := cTwo52_pos
    have : 0 ≤ 2 * cTwo52 / δ := by positivity
    linarith
  set X := (2 * cTwo52 / δ + 1) ^ (n + n * n) *
    (2 / (1 - exp (-(cZero * Real.sqrt δ / (2 * ((n * n : ℕ) : ℝ)))))) ^ (n * n) *
    exp (-(cZero * Real.sqrt δ / 4 * zdist L (I.a.getD i 0 - I.a.getD j 0)))
  have htree : ∀ F ∈ TSP n,
      ‖treeValG L m t (fun k => I.σ.getD k false) (fun k => I.a.getD k 0) F‖ ≤ X := by
    intro F hF
    refine Cor35.norm_treeValW_le (isTSP_of_mem_TSP hF) (by omega) _ _ _ hB hκ
      (fun v x y => ?_) (fun d x y => ?_) ⟨i, hi⟩ ⟨j, hj⟩
    · exact (norm_thetaEdge_le_gen L hL hm1 ht0 ht1 hδ _ _ (hgap _ _) x y).1
    · exact (norm_thetaEdge_le_gen L hL hm1 ht0 ht1 hδ _ _ (hgap _ _) x y).2
  have hprod : ‖∏ k : Fin n, m (I.σ.getD k false)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun k _ => hm1 _)
  have hW : ‖(W : ℂ)⁻¹ ^ (n - 1)‖ ≤ 1 := by
    rw [norm_pow, norm_inv, Complex.norm_natCast]
    have : (1 : ℝ) ≤ W := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ this)
  have hX : 0 ≤ X := by
    have := Cor35.one_le_two_div
      (lam := cZero * Real.sqrt δ / (2 * ((n * n : ℕ) : ℝ)))
      (by have : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by positivity
          positivity)
    positivity
  have hsum : ‖∑ F ∈ TSP n,
      treeValG L m t (fun k => I.σ.getD k false) (fun k => I.a.getD k 0) F‖
      ≤ (TSP n).card * X := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum htree).trans ?_
    rw [sum_const, nsmul_eq_mul]
  rw [norm_mul, norm_mul]
  calc _ ≤ 1 * 1 * ((TSP n).card * X) := by
        gcongr
    _ = cor35Const n δ * exp (-(cor35Rate δ * zdist L (I.a.getD i 0 - I.a.getD j 0))) := by
        simp only [X, cor35Const, cor35Rate]
        ring

/-- The constant of `loopDecay_Kgen`: it covers every length `≤ N`. -/
noncomputable def cKdecay (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), cor35Const n δ + 2 * cTwo52 / δ

theorem cor35Const_nonneg (n : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 ≤ cor35Const n δ := by
  unfold cor35Const
  by_cases hn : n = 0
  · subst hn; simp
  have : 0 < n := Nat.pos_of_ne_zero hn
  have h2 := Cor35.one_le_two_div (lam := cZero * Real.sqrt δ / (2 * ((n * n : ℕ) : ℝ)))
    (by have : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by positivity
        have := cZero_pos
        have := Real.sqrt_pos.2 hδ
        positivity)
  have := cTwo52_pos
  have : 0 ≤ (2 * cTwo52 / δ + 1) := by positivity
  positivity

theorem cor35Const_le_cKdecay {n N : ℕ} (hnN : n ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    cor35Const n δ ≤ cKdecay N δ := by
  unfold cKdecay
  have h1 : cor35Const n δ ≤ ∑ k ∈ Finset.range (N + 1), cor35Const k δ :=
    Finset.single_le_sum (f := fun k => cor35Const k δ) (fun k _ => cor35Const_nonneg k hδ)
      (Finset.mem_range.2 (by omega))
  have := cTwo52_pos
  have : 0 ≤ 2 * cTwo52 / δ := by positivity
  linarith

theorem exp_le_exp_rate {δ ℓ z c : ℝ} (hδ : 0 < δ) (hc : cor35Rate δ ≤ c) (hℓ : 0 ≤ ℓ)
    (hz : ℓ ≤ z) : exp (-(c * z)) ≤ exp (-(cor35Rate δ * ℓ)) := by
  apply exp_le_exp.2
  have h0 : 0 ≤ cor35Rate δ := by
    unfold cor35Rate; have := cZero_pos; have := Real.sqrt_nonneg δ; positivity
  have : cor35Rate δ * ℓ ≤ c * z := mul_le_mul hc hz hℓ (h0.trans hc)
  linarith

/-- **Lemma 5.9, `K` side**: `K` (the tree representation `Kgen`, Definition 2.12) has
`(ℓ, C_N(δ) e^{-c(δ) ℓ})` decay on loops of length `≤ N`, for every `ℓ > 0`, where `δ` is any
lower bound on the gaps `|1 - t m(s)m(s')|` (e.g. `δ = 1 - t`, `one_sub_le_norm_one_sub`). -/
theorem loopDecay_Kgen (hL : 3 ≤ L) (W : ℕ) [NeZero W] {m : Bool → ℂ}
    (hm1 : ∀ s, ‖m s‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ s s', δ ≤ ‖1 - (t : ℂ) * (m s * m s')‖) (N : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    LoopDecay L N ℓ (cKdecay N δ * exp (-(cor35Rate δ * ℓ))) (Kgen L W m t) := by
  intro J hJ hJN x hx y hy hxy
  have hxy0 : x ≠ y := by
    rintro rfl
    rw [sub_self, zdist_zero] at hxy
    push_cast at hxy
    linarith
  have hc0 := cTwo52_pos
  obtain ⟨σ, a⟩ := J
  have hWF : σ.length = a.length := hJ
  simp only [LoopIdx.length] at hJN
  match a, σ, hWF, hx, hy, hJN with
  | [], _, _, hx, _, _ => simp at hx
  | [c], _, _, hx, hy, _ =>
    simp only [List.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy0
  | [a₁, a₂], [s₁, s₂], _, hx, hy, hJN =>
    rw [Kgen_two, kTwo]
    have hξ : ‖(t : ℂ) * (m s₁ * m s₂)‖ < 1 := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      have := mul_le_mul (hm1 s₁) (hm1 s₂) (norm_nonneg _) zero_le_one
      nlinarith
    have hΘ := Cor35.norm_Theta_apply_le_of_gap hL hξ hδ (hgap s₁ s₂) a₁ a₂
    have hz : ℓ ≤ (zdist L (a₁ - a₂) : ℝ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy0
      · exact hxy
      · rwa [← zdist_neg L, neg_sub]
      · exact absurd rfl hxy0
    have hrate : cor35Rate δ ≤ cZero * Real.sqrt δ := by
      unfold cor35Rate; have := cZero_pos; have := Real.sqrt_nonneg δ; nlinarith
    have hW1 : ‖(W : ℂ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_natCast]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W))
    have hm : ‖m s₁ * m s₂‖ ≤ 1 := by
      rw [norm_mul]
      simpa using mul_le_mul (hm1 s₁) (hm1 s₂) (norm_nonneg _) zero_le_one
    have hC : 2 * cTwo52 / δ ≤ cKdecay N δ := by
      unfold cKdecay
      have := Finset.sum_nonneg (s := Finset.range (N + 1)) (f := fun k => cor35Const k δ)
        (fun k _ => cor35Const_nonneg k hδ)
      linarith
    rw [norm_mul, norm_mul]
    calc ‖(W : ℂ)⁻¹‖ * ‖m s₁ * m s₂‖ * ‖Theta L (t * (m s₁ * m s₂)) a₁ a₂‖
        ≤ 1 * 1 * (2 * cTwo52 / δ * exp (-(cZero * Real.sqrt δ * zdist L (a₁ - a₂)))) := by
          gcongr
      _ ≤ cKdecay N δ * exp (-(cor35Rate δ * ℓ)) := by
          rw [one_mul, one_mul]
          exact mul_le_mul hC (exp_le_exp_rate hδ hrate hℓ.le hz) (exp_pos _).le
            ((by positivity : (0 : ℝ) ≤ 2 * cTwo52 / δ).trans hC)
  | a₁ :: a₂ :: a₃ :: as, σ, hWF, hx, hy, hJN =>
    set I : LoopIdx (ZMod L) := ⟨σ, a₁ :: a₂ :: a₃ :: as⟩
    have hlen : I.length = as.length + 3 := by simp [I, LoopIdx.length]
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
    have h := norm_Kgen_le_exp L hL W hm1 ht0 ht1 hδ hgap I (by omega) hlen
      (i := i) (j := j) (by simp only [I, List.length_cons] at hi; omega)
      (by simp only [I, List.length_cons] at hj; omega)
    have ei : I.a.getD i 0 = (a₁ :: a₂ :: a₃ :: as)[i] := List.getD_eq_getElem _ _ hi
    have ej : I.a.getD j 0 = (a₁ :: a₂ :: a₃ :: as)[j] := List.getD_eq_getElem _ _ hj
    rw [ei, ej] at h
    refine h.trans ?_
    exact mul_le_mul (cor35Const_le_cKdecay (by simp at hJN; omega) hδ)
      (exp_le_exp_rate hδ le_rfl hℓ.le hxy) (exp_pos _).le
      ((cor35Const_nonneg _ hδ).trans (cor35Const_le_cKdecay (by simp at hJN; omega) hδ))
  | [_, _], [], hWF, _, _, _ => simp at hWF
  | [_, _], [_], hWF, _, _, _ => simp at hWF
  | [_, _], _ :: _ :: _ :: _, hWF, _, _, _ => simp at hWF

end KDecay

/-! ### Lemma 5.9, the `G` side: (4.2) turns decay of `L_{(+,-)}` into decay of `G_{ij}` -/

section GDecay

variable {W : ℕ} [NeZero W]

/-- `‖u‖ ≤ ‖u + v - w‖ + 2` for `v, w ∈ {0, ±1}`. -/
theorem zdist_le_add_two (hL : 3 ≤ L) {u v w : ZMod L} (hv : v ∈ sbSupport L)
    (hw : w ∈ sbSupport L) : zdist L u ≤ zdist L (u + v - w) + 2 := by
  have hv1 := zdist_le_one_of_mem_sbSupport L hL hv
  have hw1 := zdist_le_one_of_mem_sbSupport L hL ((neg_mem_sbSupport L).2 hw)
  have e : u = (u + v - w) + (-v) + w := by ring
  have h1 := zdist_add_le L ((u + v - w) + (-v)) w
  have h2 := zdist_add_le L (u + v - w) (-v)
  rw [← e] at h1
  rw [zdist_neg] at h2
  have hw1' : zdist L w ≤ 1 := by rwa [zdist_neg] at hw1
  omega

/-- **Lemma 5.9, first step**: on the event of (4.2) (`norm_sq_green_le_blk`), if the
`(+,-)` `2`-loops decay, `L_{(+,-),(a,b)} ≤ δ₂` for `‖a - b‖ ≥ ℓ`, then the entries of `G`
decay: `|G_{ij}|² ≤ 729 Φ² δ₂` for `‖[i] - [j]‖ ≥ ℓ + 2`. -/
theorem norm_sq_green_le_of_far (hL : 3 ≤ L)
    {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} (hH : H.IsHermitian)
    (hz : z.im ≠ 0) {m : ℂ} (hm : ‖m‖ = 1) {δ : ℝ} (hΩ : GoodEvent (green H z) m δ)
    (hδ : δ ≤ 1 / 2) {Φ : ℝ} (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow H (green H z) (Sblk L W) Φ) (hLcol : LDECol H (green H z) (Sblk L W) Φ)
    {ℓ δ₂ : ℝ} (hℓ : 0 ≤ ℓ)
    (hdec : ∀ a b : ZMod L, ℓ ≤ (zdist L (a - b) : ℝ) → Lre H z a b ≤ δ₂)
    {i j : ZMod L × Fin W} (hij : ℓ + 2 ≤ (zdist L (i.1 - j.1) : ℝ)) :
    ‖green H z i j‖ ^ 2 ≤ 729 * Φ ^ 2 * δ₂ := by
  have hne : i ≠ j := by
    rintro rfl
    rw [sub_self, zdist_zero] at hij
    push_cast at hij
    linarith
  have h := norm_sq_green_le_blk hL hH hz hm hΩ hδ hΦ1 hΦδ hLrow hLcol hne
  have hind : (if i.1 - j.1 ∈ sbSupport L then (W : ℝ)⁻¹ else 0) = 0 := by
    rw [ite_eq_right_iff]
    intro hmem
    have := zdist_le_one_of_mem_sbSupport L hL hmem
    have : (zdist L (i.1 - j.1) : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  have hsum : ∑ u ∈ sbSupport L, ∑ v ∈ sbSupport L, Lre H z (j.1 + v) (i.1 + u) ≤ 9 * δ₂ := by
    have hterm : ∀ u ∈ sbSupport L, ∀ v ∈ sbSupport L, Lre H z (j.1 + v) (i.1 + u) ≤ δ₂ := by
      intro u hu v hv
      refine hdec _ _ ?_
      have h1 := zdist_le_add_two L hL (u := j.1 - i.1) hv hu
      have e : j.1 - i.1 + v - u = j.1 + v - (i.1 + u) := by ring
      rw [e] at h1
      have h2 : zdist L (i.1 - j.1) = zdist L (j.1 - i.1) := by rw [← zdist_neg L, neg_sub]
      have : (zdist L (i.1 - j.1) : ℝ) ≤ zdist L (j.1 + v - (i.1 + u)) + 2 := by
        rw [h2]; exact_mod_cast h1
      linarith
    calc ∑ u ∈ sbSupport L, ∑ v ∈ sbSupport L, Lre H z (j.1 + v) (i.1 + u)
        ≤ ∑ u ∈ sbSupport L, ∑ v ∈ sbSupport L, δ₂ :=
          sum_le_sum fun u hu => sum_le_sum fun v hv => hterm u hu v hv
      _ = 9 * δ₂ := by
          simp only [sum_const, card_sbSupport L hL, nsmul_eq_mul]; ring
  rw [hind, add_zero] at h
  calc ‖green H z i j‖ ^ 2 ≤ 81 * Φ ^ 2 * (∑ u ∈ sbSupport L, ∑ v ∈ sbSupport L,
        Lre H z (j.1 + v) (i.1 + u)) := h
    _ ≤ 81 * Φ ^ 2 * (9 * δ₂) := by gcongr
    _ = 729 * Φ ^ 2 * δ₂ := by ring

end GDecay

/-! ### Lemma 5.9, the loop side: decaying entries of `G` make every `G`-loop decay -/

section LoopFromEntries

open scoped Matrix.Norms.L2Operator

variable {W : ℕ} [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

/-- One far edge in a trace: `|Tr(G E_{a₁} R E_b)| ≤ δ_G ‖R‖` if `|G_{xy}| ≤ δ_G` for
`x ∈ I_b`, `y ∈ I_{a₁}`. -/
theorem norm_trace_far_le (G R : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (a₁ b : ZMod L)
    {δG : ℝ} (hG : ∀ x y : ZMod L × Fin W, x.1 = b → y.1 = a₁ → ‖G x y‖ ≤ δG) :
    ‖Matrix.trace (G * Eblk L W a₁ * R * Eblk L W b)‖ ≤ δG * ‖R‖ := by
  have hR := norm_nonneg R
  have hδ : 0 ≤ δG := by
    obtain ⟨y⟩ : Nonempty (Fin W) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne W)⟩⟩
    exact (norm_nonneg _).trans (hG (b, y) (a₁, y) rfl rfl)
  have e : Matrix.trace (G * Eblk L W a₁ * R * Eblk L W b)
      = ∑ x, (∑ y, G x y * ((bw a₁ y : ℝ) : ℂ) * R y x) * ((bw b x : ℝ) : ℂ) := by
    rw [Eblk_eq_diagonal_bw, Eblk_eq_diagonal_bw, Matrix.trace]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_diagonal, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.mul_diagonal]
  rw [e]
  have hpt : ∀ x y : ZMod L × Fin W,
      ‖G x y * ((bw a₁ y : ℝ) : ℂ) * R y x * ((bw b x : ℝ) : ℂ)‖
        ≤ δG * ‖R‖ * (bw a₁ y * bw b x) := by
    intro x y
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (bw_nonneg a₁ y), Real.norm_of_nonneg (bw_nonneg b x)]
    by_cases hy : y.1 = a₁
    · by_cases hx : x.1 = b
      · have h1 := hG x y hx hy
        have h2 := norm_apply_le_l2_opNorm R y x
        have := bw_nonneg a₁ y
        have := bw_nonneg b x
        calc ‖G x y‖ * bw a₁ y * ‖R y x‖ * bw b x = (‖G x y‖ * ‖R y x‖) * (bw a₁ y * bw b x) := by
              ring
          _ ≤ (δG * ‖R‖) * (bw a₁ y * bw b x) := by gcongr
      · have : bw (W := W) b x = 0 := by simp [bw, hx]
        simp [this]
    · have : bw (W := W) a₁ y = 0 := by simp [bw, hy]
      simp [this]
  calc ‖∑ x, (∑ y, G x y * ((bw a₁ y : ℝ) : ℂ) * R y x) * ((bw b x : ℝ) : ℂ)‖
      ≤ ∑ x, ∑ y, ‖G x y * ((bw a₁ y : ℝ) : ℂ) * R y x * ((bw b x : ℝ) : ℂ)‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
        rw [Finset.sum_mul]
        exact norm_sum_le _ _
    _ ≤ ∑ x, ∑ y, δG * ‖R‖ * (bw a₁ y * bw b x) :=
        sum_le_sum fun x _ => sum_le_sum fun y _ => hpt x y
    _ = δG * ‖R‖ * ((∑ x, bw (W := W) b x) * (∑ y, bw (W := W) a₁ y)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun y _ => ?_
        ring
    _ = δG * ‖R‖ := by rw [sum_bw, sum_bw, mul_one, mul_one]

/-- A loop whose **last and first** labels are far: `|L_{s::τ, a₁::a'++[b]}| ≤
δ_G |Im z|^{-|τ|} W^{-|a'|}`, if `|G(s)_{xy}| ≤ δ_G` for `x ∈ I_b`, `y ∈ I_{a₁}`. -/
theorem norm_gloop_le_of_far_ends (hH : H.IsHermitian) (hz : z.im ≠ 0) {s : Bool}
    {τ : List Bool} {a₁ b : ZMod L} {a' : List (ZMod L)} (h : τ.length = a'.length + 1)
    {δG : ℝ} (hG : ∀ x y : ZMod L × Fin W, x.1 = b → y.1 = a₁ → ‖Gsig H z s x y‖ ≤ δG) :
    ‖gloop L W H z ⟨s :: τ, a₁ :: (a' ++ [b])⟩‖
      ≤ δG * (|z.im|⁻¹ ^ τ.length * (W : ℝ)⁻¹ ^ a'.length) := by
  have hδ : 0 ≤ δG := by
    obtain ⟨y⟩ : Nonempty (Fin W) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne W)⟩⟩
    exact (norm_nonneg _).trans (hG (b, y) (a₁, y) rfl rfl)
  have h' : (s :: τ).length = (a₁ :: a').length + 1 := by simpa using h
  rw [← List.cons_append, ← trace_gchain_mul_Eblk h' b, gchain_cons]
  refine (norm_trace_far_le L _ _ a₁ b hG).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_gchain_le hH hz h) hδ

/-- The `G`-loop is invariant under every rotation of its index data. -/
theorem gloop_rotate_eq {σ : List Bool} {a : List (ZMod L)} (h : σ.length = a.length) (k : ℕ) :
    gloop L W H z ⟨σ.rotate k, a.rotate k⟩ = gloop L W H z ⟨σ, a⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← List.rotate_rotate σ k 1, ← List.rotate_rotate a k 1, ← ih]
    have hk : (σ.rotate k).length = (a.rotate k).length := by
      simp [List.length_rotate, h]
    generalize σ.rotate k = σ' at hk ⊢
    generalize a.rotate k = a' at hk ⊢
    cases σ' with
    | nil =>
      have : a' = [] := List.eq_nil_of_length_eq_zero (by simpa using hk.symm)
      subst this; simp
    | cons s σ'' =>
      cases a' with
      | nil => simp at hk
      | cons c a'' =>
        have hk' : σ''.length = a''.length := by simpa using hk
        rw [List.rotate_cons_succ, List.rotate_cons_succ, List.rotate_zero, List.rotate_zero,
          gloop_rotate s c hk']

/-- If two labels are `≥ 2nR` apart, two **consecutive** labels are `≥ R` apart. -/
theorem exists_consecutive_far {a : List (ZMod L)} {R : ℝ} (hR : 0 < R) {x y : ZMod L}
    (hx : x ∈ a) (hy : y ∈ a) (hxy : 2 * a.length * R ≤ (zdist L (x - y) : ℝ)) :
    ∃ k, ∃ hk : k + 1 < a.length, R ≤ (zdist L (a[k] - a[k + 1]) : ℝ) := by
  by_contra hno
  push Not at hno
  have hpos : 0 < a.length := List.length_pos_of_mem hx
  -- distance from the first label
  have hchain : ∀ i (hi : i < a.length),
      (zdist L (a[0] - a[i]) : ℝ) ≤ i * R := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hno i hi
      have t := zdist_add_le L (a[0] - a[i]) (a[i] - a[i + 1])
      rw [sub_add_sub_cancel] at t
      have t' : (zdist L (a[0] - a[i + 1]) : ℝ) ≤ zdist L (a[0] - a[i]) + zdist L (a[i] - a[i + 1]) := by
        exact_mod_cast t
      push_cast
      linarith
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
  have h1 := hchain i hi
  have h2 := hchain j hj
  have t := zdist_add_le L (a[i] - a[0]) (a[0] - a[j])
  rw [sub_add_sub_cancel] at t
  have hsym : zdist L (a[i] - a[0]) = zdist L (a[0] - a[i]) := by
    rw [← zdist_neg L, neg_sub]
  rw [hsym] at t
  have t' : (zdist L (a[i] - a[j]) : ℝ) ≤ zdist L (a[0] - a[i]) + zdist L (a[0] - a[j]) := by
    exact_mod_cast t
  have hi' : (i : ℝ) < a.length := by exact_mod_cast hi
  have hj' : (j : ℝ) < a.length := by exact_mod_cast hj
  nlinarith

/-- `norm_gloop_le_of_far_ends` with the first and last labels read off by `getD`. -/
theorem norm_gloop_le_of_far_getD (hH : H.IsHermitian) (hz : z.im ≠ 0) {R δG : ℝ}
    (hG : ∀ (s : Bool) (x y : ZMod L × Fin W), R ≤ (zdist L (x.1 - y.1) : ℝ) →
      ‖Gsig H z s x y‖ ≤ δG)
    {σ₀ : List Bool} {a₀ : List (ZMod L)} {n : ℕ} (hn : 2 ≤ n) (hlσ : σ₀.length = n)
    (hla : a₀.length = n) (hfar : R ≤ (zdist L (a₀.getD (n - 1) 0 - a₀.getD 0 0) : ℝ)) :
    ‖gloop L W H z ⟨σ₀, a₀⟩‖ ≤ δG * (|z.im|⁻¹ ^ (n - 1) * (W : ℝ)⁻¹ ^ (n - 2)) := by
  obtain ⟨a₁, rest, rfl⟩ : ∃ a₁ rest, a₀ = a₁ :: rest := by
    cases a₀ with
    | nil => simp at hla; omega
    | cons c r => exact ⟨c, r, rfl⟩
  obtain ⟨s, τ, rfl⟩ : ∃ s τ, σ₀ = s :: τ := by
    cases σ₀ with
    | nil => simp at hlσ; omega
    | cons c r => exact ⟨c, r, rfl⟩
  have hlen_rest : rest.length = n - 1 := by simp at hla; omega
  have hlτ : τ.length = n - 1 := by simp at hlσ; omega
  have hrest_ne : rest ≠ [] := by
    rintro rfl; simp at hlen_rest; omega
  have hrest' : rest = rest.dropLast ++ [rest.getLast hrest_ne] :=
    (List.dropLast_append_getLast hrest_ne).symm
  have hla' : rest.dropLast.length = n - 2 := by
    rw [List.length_dropLast, hlen_rest]; omega
  have hτa' : τ.length = rest.dropLast.length + 1 := by omega
  have hbk : rest.getLast hrest_ne = (a₁ :: rest).getD (n - 1) 0 := by
    rw [List.getLast_eq_getElem, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_cons]
    simp only [show ¬(n - 1 = 0) by omega, ↓reduceDIte]
    congr 1
    omega
  have key := norm_gloop_le_of_far_ends L hH hz (s := s) (a₁ := a₁)
    (b := rest.getLast hrest_ne) hτa' (δG := δG)
    (fun p q hp hq => hG s p q (by rw [hp, hq, hbk]; simpa using hfar))
  rw [← hrest', hlτ, hla'] at key
  exact key

/-- **Lemma 5.9, the loop side** ("by definition `L = ⟨∏ G E_{a_i}⟩` has the decay property"):
if every entry of `G(z)`, `G(z̄)` between blocks at distance `≥ R` is at most `δ_G`, then every
loop of length `n ≥ 2` whose labels are `≥ 2nR` apart satisfies
`|L_{σ,a}| ≤ δ_G |Im z|^{-(n-1)} W^{-(n-2)}`. -/
theorem norm_gloop_le_of_far (hH : H.IsHermitian) (hz : z.im ≠ 0) {R δG : ℝ} (hR : 0 < R)
    (hG : ∀ (s : Bool) (x y : ZMod L × Fin W), R ≤ (zdist L (x.1 - y.1) : ℝ) →
      ‖Gsig H z s x y‖ ≤ δG)
    (I : LoopIdx (ZMod L)) (hI : I.WF) (hn : 2 ≤ I.length) {x y : ZMod L} (hx : x ∈ I.a)
    (hy : y ∈ I.a) (hxy : 2 * I.length * R ≤ (zdist L (x - y) : ℝ)) :
    ‖gloop L W H z I‖ ≤ δG * (|z.im|⁻¹ ^ (I.length - 1) * (W : ℝ)⁻¹ ^ (I.length - 2)) := by
  obtain ⟨σ, a⟩ := I
  have hσa : σ.length = a.length := hI
  simp only [LoopIdx.length] at hn hxy hx hy ⊢
  obtain ⟨k, hk, hfar⟩ := exists_consecutive_far L hR hx hy hxy
  rw [← gloop_rotate_eq L hσa (k + 1)]
  refine norm_gloop_le_of_far_getD L hH hz hG hn (by rw [List.length_rotate, hσa])
    (List.length_rotate _ _) ?_
  have hlen : (a.rotate (k + 1)).length = a.length := List.length_rotate _ _
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
    List.getElem_rotate, List.getElem_rotate]
  have e1 : (a.length - 1 + (k + 1)) % a.length = k := by
    rw [show a.length - 1 + (k + 1) = k + a.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have e2 : (0 + (k + 1)) % a.length = k + 1 := by
    rw [zero_add, Nat.mod_eq_of_lt hk]
  simp only [e1, e2]
  exact hfar

omit [NeZero W] in
/-- `|G(z̄)_{xy}| = |G(z)_{yx}|`: entry decay of `G(z)` in both orders gives it for both charges. -/
theorem norm_Gsig_apply_le (hH : H.IsHermitian) {R δG : ℝ}
    (hG : ∀ x y : ZMod L × Fin W, R ≤ (zdist L (x.1 - y.1) : ℝ) → ‖green H z x y‖ ≤ δG)
    (s : Bool) (x y : ZMod L × Fin W) (hxy : R ≤ (zdist L (x.1 - y.1) : ℝ)) :
    ‖Gsig H z s x y‖ ≤ δG := by
  cases s
  · have e : Gsig H z false = Matrix.conjTranspose (Gsig H z true) := by
      rw [Gsig_conjTranspose hH]; rfl
    rw [e, Matrix.conjTranspose_apply, norm_star, Gsig_true]
    refine hG y x ?_
    rwa [← zdist_neg L, neg_sub]
  · exact hG x y hxy

/-- **Lemma 5.9, loop side, as Definition 5.8**: every `G`-loop of length `≤ N` has
`(2NR, δ_G max(1, |Im z|⁻¹)^N)` decay. -/
theorem loopDecay_gloop (hH : H.IsHermitian) (hz : z.im ≠ 0) {R δG : ℝ} (hR : 0 < R)
    (hδG : 0 ≤ δG)
    (hG : ∀ (s : Bool) (x y : ZMod L × Fin W), R ≤ (zdist L (x.1 - y.1) : ℝ) →
      ‖Gsig H z s x y‖ ≤ δG) (N : ℕ) :
    LoopDecay L N (2 * N * R) (δG * max 1 |z.im|⁻¹ ^ N) (gloop L W H z) := by
  intro J hJ hJN x hx y hy hxy
  have hC : 1 ≤ max 1 |z.im|⁻¹ := le_max_left _ _
  by_cases hn : 2 ≤ J.length
  · have hxy' : 2 * J.length * R ≤ (zdist L (x - y) : ℝ) := by
      have : (J.length : ℝ) ≤ N := by exact_mod_cast hJN
      nlinarith
    refine (norm_gloop_le_of_far L hH hz hR hG J hJ hn hx hy hxy').trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hδG
    have hW : (W : ℝ)⁻¹ ^ (J.length - 2) ≤ 1 :=
      pow_le_one₀ (by positivity)
        (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W)))
    have hZ : |z.im|⁻¹ ^ (J.length - 1) ≤ max 1 |z.im|⁻¹ ^ N :=
      (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ hC (by omega))
    calc |z.im|⁻¹ ^ (J.length - 1) * (W : ℝ)⁻¹ ^ (J.length - 2)
        ≤ max 1 |z.im|⁻¹ ^ N * 1 := mul_le_mul hZ hW (by positivity) (by positivity)
      _ = _ := mul_one _
  · exfalso
    have hlen : J.a.length ≤ 1 := by simp only [LoopIdx.length] at hn; omega
    have hxy0 : x = y := by
      match h : J.a, hlen with
      | [], _ => rw [h] at hx; simp at hx
      | [c], _ => rw [h] at hx hy; simp at hx hy; rw [hx, hy]
    rw [hxy0, sub_self, zdist_zero] at hxy
    have hN : 1 ≤ N := by
      have : 0 < J.length := List.length_pos_of_mem hx
      omega
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at hxy
    nlinarith

end LoopFromEntries

/-! ### Lemma 5.9, assembled (on the event of (4.2)) -/

section Lemma59

variable {W : ℕ} [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

/-- **Lemma 5.9, (5.75), deterministic core.**  On the event of Lemma 4.1 (the hypotheses of
`norm_sq_green_le_blk`: the weak local law `‖G - m‖_max ≤ δ` and the large-deviation bounds
with factor `Φ`), if the `(+,-)` `2`-loops decay ((2.76): `L_{(+,-),(a,b)} ≤ δ₂` for
`‖a - b‖ ≥ ℓ`), then every `G`-loop of length `≤ N` decays:
`LoopDecay N (2N(ℓ + 2)) (27 Φ √δ₂ max(1, |Im z|⁻¹)^N)`.  Together with `loopDecay_Kgen`
(the `K` side) and `LoopDecay.sub`, `L - K` decays. -/
theorem loopDecay_gloop_of_event (hL : 3 ≤ L) (hH : H.IsHermitian) (hz : z.im ≠ 0) {m : ℂ}
    (hm : ‖m‖ = 1) {δ : ℝ} (hΩ : GoodEvent (green H z) m δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ}
    (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow H (green H z) (Sblk L W) Φ) (hLcol : LDECol H (green H z) (Sblk L W) Φ)
    {ℓ δ₂ : ℝ} (hℓ : 0 ≤ ℓ) (hδ₂ : 0 ≤ δ₂)
    (hdec : ∀ a b : ZMod L, ℓ ≤ (zdist L (a - b) : ℝ) → Lre H z a b ≤ δ₂) (N : ℕ) :
    LoopDecay L N (2 * N * (ℓ + 2)) (27 * Φ * Real.sqrt δ₂ * max 1 |z.im|⁻¹ ^ N)
      (gloop L W H z) := by
  have hG : ∀ x y : ZMod L × Fin W, ℓ + 2 ≤ (zdist L (x.1 - y.1) : ℝ) →
      ‖green H z x y‖ ≤ 27 * Φ * Real.sqrt δ₂ := by
    intro x y hxy
    have h := norm_sq_green_le_of_far L hL hH hz hm hΩ hδ hΦ1 hΦδ hLrow hLcol hℓ hdec hxy
    have h0 : 0 ≤ 27 * Φ * Real.sqrt δ₂ := by positivity
    have e : (27 * Φ * Real.sqrt δ₂) ^ 2 = 729 * Φ ^ 2 * δ₂ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hδ₂]; ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).1 (by rw [e]; exact h)
  exact loopDecay_gloop L hH hz (by linarith) (by positivity)
    (norm_Gsig_apply_le L hH hG) N

/-- **Lemma 5.9, (5.75)**, deterministic form: on the event of Lemma 4.1 and under the
decay (2.76) of `L_{(+,-)}`, both `L` and `L - K` have `(u, τ, D)` decay on loops of length
`≤ N`, with radius `ℓ' = 2N(ℓ + 2)` and error
`δ_L + δ_K = 27Φ√δ₂ max(1,|Im z|⁻¹)^N + C_N(1-t) e^{-c(1-t) ℓ'}`.
(`K = Kgen L W m t` is the tree representation of Definition 2.12, `|m| ≤ 1`, `0 ≤ t < 1`.) -/
theorem lemma59 (hL : 3 ≤ L) (hH : H.IsHermitian) (hz : z.im ≠ 0) {m₀ : ℂ} (hm₀ : ‖m₀‖ = 1)
    {δ : ℝ} (hΩ : GoodEvent (green H z) m₀ δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ} (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow H (green H z) (Sblk L W) Φ) (hLcol : LDECol H (green H z) (Sblk L W) Φ)
    {ℓ δ₂ : ℝ} (hℓ : 0 ≤ ℓ) (hδ₂ : 0 ≤ δ₂)
    (hdec : ∀ a b : ZMod L, ℓ ≤ (zdist L (a - b) : ℝ) → Lre H z a b ≤ δ₂)
    {m : Bool → ℂ} (hm1 : ∀ s, ‖m s‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {N : ℕ}
    (hN : 1 ≤ N) :
    LoopDecay L N (2 * N * (ℓ + 2)) (27 * Φ * Real.sqrt δ₂ * max 1 |z.im|⁻¹ ^ N)
        (gloop L W H z) ∧
      LoopDecay L N (2 * N * (ℓ + 2))
        (27 * Φ * Real.sqrt δ₂ * max 1 |z.im|⁻¹ ^ N
          + cKdecay N (1 - t) * exp (-(cor35Rate (1 - t) * (2 * N * (ℓ + 2)))))
        (gloop L W H z - Kgen L W m t) := by
  have hGL := loopDecay_gloop_of_event L hL hH hz hm₀ hΩ hδ hΦ1 hΦδ hLrow hLcol hℓ hδ₂ hdec N
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK := loopDecay_Kgen L hL W hm1 ht0 ht1 (δ := 1 - t) (by linarith)
    (one_sub_le_norm_one_sub hm1 ht0) N (ℓ := 2 * N * (ℓ + 2)) (by positivity)
  exact ⟨hGL, hGL.sub L hK⟩

end Lemma59

end Decay

end RBM
