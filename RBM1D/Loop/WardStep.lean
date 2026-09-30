/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.WardInd
import RBM1D.Loop.Primitive

/-!
# The derivative identity behind Ward's identity at general `n`

Toward (3.18).  Fix `K : LoopIdx (ZMod L) → ℂ` (the primitive loop at a fixed time) and write
`N = |a'| = n - 1`.  This file rearranges `∑_x (2.48)(fullLoop μ a' x)` according to the cuts,
using the index identities of `RBM1D.Loop.WardInd`.

## Main results

* `RBM.sum_primRhs_fullLoop` : the `x`-summed (2.48), split into cuts `l ≤ N` and `(k, N + 1)`
* `RBM.cut_inner` (W1), `RBM.cut_last` (W2), `RBM.cut_one_last` (W3) : the three kinds of cut
* **`RBM.ward_rhs_identity`** : given cyclic invariance and Ward at shorter lengths,
  `∑_x (2.48)(+,μ,-;a',x) - κ ((2.48)(σ⁺) - (2.48)(σ⁻))
    = W (∑_k wD(adjacent cut) S K₂ + wD(cut (N,N+1)) S K₂ + c ∑_x K)`;
  with `∂_t κ = κ/(1-t)` and `W c = (1-t)⁻¹` this is (3.18).

Compared with the paper's Steps 3–4, the cuts `(1, m)` and `(m, n)` cancel for every
`2 ≤ m ≤ n - 1` at once (`hcancel` in the proof): the right chain of `σ^±` at `(1, m)` is the
`σ^±` of the left chain of the full loop at `(m, n)`, and cyclic invariance matches the other
factor.  No special corner cuts and no `3`-loop identity are needed.
-/

namespace RBM

open Finset LoopIdx

variable (L : ℕ) [NeZero L]

/-- `∑_x K_{(+,μ,-),(a',x)}`: the left-hand side of (3.13). -/
noncomputable def wStar (K : LoopIdx (ZMod L) → ℂ) (μ : List Bool) (a' : List (ZMod L)) : ℂ :=
  ∑ x : ZMod L, K (fullLoop μ a' x)

/-- The difference of the two sides of (3.13), with `κ = (2 W i η_t)⁻¹`. -/
noncomputable def wD (K : LoopIdx (ZMod L) → ℂ) (κ : ℂ) (μ : List Bool) (a' : List (ZMod L)) :
    ℂ :=
  wStar L K μ a' - κ * (K (pmLoop true μ a') - K (pmLoop false μ a'))

/-- The `x`-summed right-hand side of (2.48) at `fullLoop μ a' x`, split into the cuts with
`l ≤ N` and the cuts `(k, N + 1)`; the right chains do not depend on `x`. -/
theorem sum_primRhs_fullLoop (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (μ : List Bool)
    (a' : List (ZMod L)) (hμ : μ.length + 1 = a'.length) :
    ∑ x : ZMod L, primRhs L W K (fullLoop μ a' x) = (W : ℂ) *
      (∑ k ∈ Icc 1 a'.length, ∑ l ∈ Ioc k a'.length, ∑ a : ZMod L, ∑ b : ZMod L,
          (∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
            K ((fullLoop μ a' 0).cutGlueR k l b)
        + ∑ k ∈ Icc 1 a'.length, ∑ a : ZMod L, ∑ b : ZMod L,
          (∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k (a'.length + 1) a)) * SB L a b *
            K ((fullLoop μ a' 0).cutGlueR k (a'.length + 1) b)) := by
  have hlen : ∀ x : ZMod L, (fullLoop μ a' x).length = a'.length + 1 := fun x => by
    simp [fullLoop, LoopIdx.length]
  -- the right chain does not depend on `x`
  have hR : ∀ x : ZMod L, ∀ k l, 1 ≤ k → k < l → l ≤ a'.length + 1 → ∀ b : ZMod L,
      (fullLoop μ a' x).cutGlueR k l b = (fullLoop μ a' 0).cutGlueR k l b :=
    fun x k l hk hkl hl b => cutGlueR_fullLoop_indep μ a' x b 0 hk hkl hl
  -- split each `primRhs`
  have hsplit : ∀ x : ZMod L, primRhs L W K (fullLoop μ a' x) = (W : ℂ) *
      (∑ k ∈ Icc 1 a'.length, ∑ l ∈ Ioc k a'.length, ∑ a : ZMod L, ∑ b : ZMod L,
          K ((fullLoop μ a' x).cutGlueL k l a) * SB L a b *
            K ((fullLoop μ a' 0).cutGlueR k l b)
        + ∑ k ∈ Icc 1 a'.length, ∑ a : ZMod L, ∑ b : ZMod L,
          K ((fullLoop μ a' x).cutGlueL k (a'.length + 1) a) * SB L a b *
            K ((fullLoop μ a' 0).cutGlueR k (a'.length + 1) b)) := by
    intro x
    rw [primRhs, hlen, sum_Icc_succ_top (by omega), Ioc_self, sum_empty, add_zero,
      ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Icc] at hk
    rw [sum_Ioc_succ_top hk.2]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      rw [mem_Ioc] at hl
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hR x k l hk.1 hl.1 (by omega) b]
    · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hR x k (a'.length + 1) hk.1 (by omega) le_rfl b]
  simp only [hsplit, ← Finset.mul_sum, sum_add_distrib]
  congr 2
  · rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
  · rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]

section Cuts

variable (K : LoopIdx (ZMod L) → ℂ) (κ : ℂ) (μ : List Bool) (a' : List (ZMod L))

theorem wStar_eq (μ' : List Bool) (a'' : List (ZMod L)) :
    wStar L K μ' a'' = wD L K κ μ' a''
      + κ * (K (pmLoop true μ' a'') - K (pmLoop false μ' a'')) := by
  rw [wD]
  ring

/-- **W1**: a cut `(k, l)` with `l ≤ N`.  The `x`-summed left chain is `wD` one level down plus
`κ (K(L⁺) - K(L⁻))`, which cancels against the `σ^±` terms except for a remainder at `k = 1`. -/
theorem cut_inner (hμ : μ.length + 1 = a'.length) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l)
    (hl : l ≤ a'.length) (a b : ZMod L) :
    (∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
        K ((fullLoop μ a' 0).cutGlueR k l b)
      - κ * (K ((pmLoop true μ a').cutGlueL k l a) * SB L a b *
            K ((pmLoop true μ a').cutGlueR k l b)
          - K ((pmLoop false μ a').cutGlueL k l a) * SB L a b *
            K ((pmLoop false μ a').cutGlueR k l b))
      = wD L K κ (cutMu k l μ) (cutA k l a a') * SB L a b *
          K ((pmLoop true μ a').cutGlueR k l b)
        + κ * K ((pmLoop false μ a').cutGlueL k l a) * SB L a b *
          (K ((pmLoop false μ a').cutGlueR k l b) - K ((pmLoop true μ a').cutGlueR k l b)) := by
  have hL : ∀ x, (fullLoop μ a' x).cutGlueL k l a = fullLoop (cutMu k l μ) (cutA k l a a') x :=
    fun x => cutGlueL_fullLoop μ a' x a hμ hk hkl hl
  have hR : (fullLoop μ a' 0).cutGlueR k l b = (pmLoop true μ a').cutGlueR k l b := by
    rcases hk.lt_or_eq with hk2 | rfl
    · exact cutGlueR_fullLoop μ a' 0 b true hμ hk2 hkl hl
    · exact cutGlueR_fullLoop_one μ a' 0 b hμ hkl hl
  simp only [hL, hR, cutGlueL_pmLoop μ a' a true hμ hk hkl hl,
    cutGlueL_pmLoop μ a' a false hμ hk hkl hl]
  rw [show ∑ x : ZMod L, K (fullLoop (cutMu k l μ) (cutA k l a a') x)
      = wStar L K (cutMu k l μ) (cutA k l a a') from rfl, wStar_eq L K κ]
  ring

omit [NeZero L] in
/-- For `k ≥ 2` the remainder of W1 vanishes: the right chain does not see the first
charge. -/
theorem cutGlueR_pmLoop_indep (hμ : μ.length + 1 = a'.length) {k l : ℕ} (hk : 2 ≤ k)
    (hkl : k < l) (hl : l ≤ a'.length) (b : ZMod L) :
    (pmLoop false μ a').cutGlueR k l b = (pmLoop true μ a').cutGlueR k l b := by
  rw [← cutGlueR_fullLoop μ a' (0 : ZMod L) b false hμ hk hkl hl,
    cutGlueR_fullLoop μ a' (0 : ZMod L) b true hμ hk hkl hl]

/-- **W2**: a cut `(k, N + 1)` with `2 ≤ k ≤ N`.  The left chain sums to `wD` one level down
plus `κ (K(R₁ₖ⁺) - K(R₁ₖ⁻))`, and by cyclic invariance the right chain is `L₁ₖ(σ⁻)`. -/
theorem cut_last (hμ : μ.length + 1 = a'.length) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ a'.length)
    (hcyc : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → K J.rot = K J) (a b : ZMod L) :
    (∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k (a'.length + 1) a)) * SB L a b *
        K ((fullLoop μ a' 0).cutGlueR k (a'.length + 1) b)
      = (wD L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a])
          + κ * (K ((pmLoop true μ a').cutGlueR 1 k a)
            - K ((pmLoop false μ a').cutGlueR 1 k a))) * SB L a b *
          K ((pmLoop false μ a').cutGlueL 1 k b) := by
  have hL : ∀ x, (fullLoop μ a' x).cutGlueL k (a'.length + 1) a
      = fullLoop (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) x :=
    fun x => cutGlueL_fullLoop_last μ a' x a hμ (by omega) hkN
  have hWF : ((pmLoop false μ a').cutGlueL 1 k b).WF := by
    refine LoopIdx.WF.cutGlueL b ?_ le_rfl (by omega) ?_
    · simp [WF, pmLoop, hμ]
    · simp [LoopIdx.length, pmLoop]; omega
  have hlen : 2 ≤ ((pmLoop false μ a').cutGlueL 1 k b).length := by
    refine LoopIdx.two_le_length_cutGlueL _ b le_rfl (by omega) ?_
    simp [LoopIdx.length, pmLoop]; omega
  simp only [hL, cutGlueR_fullLoop_last μ a' 0 b hμ hk hkN, hcyc _ hWF hlen,
    cutGlueR_pmLoop_one μ a' a true (by omega : 1 < k),
    cutGlueR_pmLoop_one μ a' a false (by omega : 1 < k)]
  rw [show ∑ x : ZMod L, K (fullLoop (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) x)
      = wStar L K (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) from rfl, wStar_eq L K κ]

/-- **W3**: the cut `(1, N + 1)`.  The left chain is a `2`-loop `(+,-;a,x)`, whose `x`-sum is
`c` by the `2`-loop Ward identity; the right chain is the whole loop with last label `b`, and
the column sums of `S^(B)` are `1`. -/
theorem cut_one_last (hL : 3 ≤ L) (hμ : μ.length + 1 = a'.length) (c : ℂ)
    (h2 : ∀ a : ZMod L, wStar L K [] [a] = c) :
    ∑ a : ZMod L, ∑ b : ZMod L,
        (∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL 1 (a'.length + 1) a)) * SB L a b *
          K ((fullLoop μ a' 0).cutGlueR 1 (a'.length + 1) b)
      = c * wStar L K μ a' := by
  have hL1 : ∀ x a, (fullLoop μ a' x).cutGlueL 1 (a'.length + 1) a = fullLoop [] [a] x := by
    intro x a
    rw [cutGlueL_fullLoop_last μ a' x a hμ le_rfl (by omega)]
    simp
  simp only [hL1, cutGlueR_fullLoop_last_one μ a' 0 _ hμ]
  simp only [show ∀ a, ∑ x : ZMod L, K (fullLoop [] [a] x) = wStar L K [] [a] from fun _ => rfl,
    h2]
  rw [Finset.sum_comm, wStar, Finset.mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hcol : ∑ a : ZMod L, SB L a b = 1 := by
    rw [← sum_SB_row L hL b]
    exact sum_congr rfl fun a _ => congrFun (congrFun (SB_transpose L) b) a
  rw [hcol, mul_one]

/-- A double sum over `1 ≤ k < l ≤ N` of a function vanishing unless `l = k + 1`. -/
theorem sum_Icc_Ioc_adjacent {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → ℕ → M)
    (hf : ∀ k ∈ Icc 1 N, ∀ l ∈ Ioc k N, k + 1 < l → f k l = 0) :
    ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, f k l = ∑ k ∈ Icc 1 (N - 1), f k (k + 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [sum_Icc_succ_top (by omega), Ioc_self, sum_empty, add_zero, Nat.add_sub_cancel]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_Icc] at hk
  rw [Finset.sum_eq_single_of_mem (k + 1) (by rw [mem_Ioc]; omega)]
  intro l hl hne
  refine hf k (by rw [mem_Icc]; omega) l hl ?_
  rw [mem_Ioc] at hl
  omega

/-- **The right-hand side of the derivative of (3.13)**, at a fixed time.  Given cyclic
invariance, Ward at all shorter lengths (`hlow`) and the `2`-loop value `c` (`h2`), the
`x`-summed right-hand side of (2.48) at `(+,μ,-;a',x)` minus `κ` times that at `σ^±` is
`W` times: `wD` at the adjacent cuts `(k, k+1)` of length `n`, `wD` at the cut `(N, N+1)`, and
`c ∑_x K`. -/
theorem ward_rhs_identity (hL : 3 ≤ L) (W : ℕ) (c : ℂ) (hμ : μ.length + 1 = a'.length)
    (hN : 2 ≤ a'.length)
    (hcyc : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → K J.rot = K J)
    (h2 : ∀ a : ZMod L, wStar L K [] [a] = c)
    (hlow : ∀ (μ'' : List Bool) (a'' : List (ZMod L)), μ''.length + 1 = a''.length →
      a''.length < a'.length → wD L K κ μ'' a'' = 0) :
    ∑ x : ZMod L, primRhs L W K (fullLoop μ a' x)
      - κ * (primRhs L W K (pmLoop true μ a') - primRhs L W K (pmLoop false μ a'))
      = (W : ℂ) *
        (∑ k ∈ Icc 1 (a'.length - 1), ∑ a : ZMod L, ∑ b : ZMod L,
            wD L K κ (cutMu k (k + 1) μ) (cutA k (k + 1) a a') * SB L a b *
              K ((pmLoop true μ a').cutGlueR k (k + 1) b)
          + ∑ a : ZMod L, ∑ b : ZMod L,
            wD L K κ (μ.take (a'.length - 1)) (a'.take (a'.length - 1) ++ [a]) * SB L a b *
              K ((pmLoop false μ a').cutGlueL 1 a'.length b)
          + c * wStar L K μ a') := by
  set N := a'.length with hNdef
  have hpmlen : ∀ s, (pmLoop s μ a').length = N := fun s => by
    simp [LoopIdx.length, pmLoop, hNdef]
  -- the `σ^±` sums
  have hpm : ∀ s, primRhs L W K (pmLoop s μ a') = (W : ℂ) *
      ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : ZMod L, ∑ b : ZMod L,
        K ((pmLoop s μ a').cutGlueL k l a) * SB L a b * K ((pmLoop s μ a').cutGlueR k l b) :=
    fun s => by rw [primRhs, hpmlen]
  rw [sum_primRhs_fullLoop L W K μ a' hμ, hpm, hpm]
  -- (i) the cuts with `l ≤ N`
  have hA : ∀ k ∈ Icc 1 N, ∀ l ∈ Ioc k N, ∀ a b : ZMod L,
      (∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
          K ((fullLoop μ a' 0).cutGlueR k l b)
        - κ * (K ((pmLoop true μ a').cutGlueL k l a) * SB L a b *
              K ((pmLoop true μ a').cutGlueR k l b)
            - K ((pmLoop false μ a').cutGlueL k l a) * SB L a b *
              K ((pmLoop false μ a').cutGlueR k l b))
        = wD L K κ (cutMu k l μ) (cutA k l a a') * SB L a b *
            K ((pmLoop true μ a').cutGlueR k l b)
          + (if k = 1 then κ * K ((pmLoop false μ a').cutGlueL 1 l a) * SB L a b *
              (K ((pmLoop false μ a').cutGlueR 1 l b)
                - K ((pmLoop true μ a').cutGlueR 1 l b)) else 0) := by
    intro k hk l hl a b
    rw [mem_Icc] at hk
    rw [mem_Ioc] at hl
    rw [cut_inner L K κ μ a' hμ hk.1 hl.1 hl.2]
    split_ifs with h1
    · subst h1
      rfl
    · rw [cutGlueR_pmLoop_indep L μ a' hμ (by omega) hl.1 hl.2, sub_self, mul_zero]
  -- (ii) the cuts `(k, N + 1)`
  have hB : ∀ k ∈ Icc 2 N, ∀ a b : ZMod L,
      (∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k (N + 1) a)) * SB L a b *
          K ((fullLoop μ a' 0).cutGlueR k (N + 1) b)
        = wD L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) * SB L a b *
            K ((pmLoop false μ a').cutGlueL 1 k b)
          + κ * (K ((pmLoop true μ a').cutGlueR 1 k a) - K ((pmLoop false μ a').cutGlueR 1 k a))
            * SB L a b * K ((pmLoop false μ a').cutGlueL 1 k b) := by
    intro k hk a b
    rw [mem_Icc] at hk
    rw [cut_last L K κ μ a' hμ hk.1 hk.2 hcyc]
    ring
  have hIcc : Icc 1 N = insert 1 (Icc 2 N) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  have hIoc : Ioc 1 N = Icc 2 N := by
    ext k
    simp only [mem_Icc, mem_Ioc]
    omega
  -- the level-`n` bookkeeping
  have hcutlen : ∀ k l, 1 ≤ k → k < l → l ≤ N → ∀ a : ZMod L,
      (cutMu k l μ).length + 1 = (cutA k l a a').length ∧
        (cutA k l a a').length = N + k - l + 1 := by
    intro k l hk hkl hl a
    simp only [cutMu, cutA, List.length_append, List.length_take, List.length_drop,
      List.length_cons]
    omega
  have hT1 : ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : ZMod L, ∑ b : ZMod L,
      wD L K κ (cutMu k l μ) (cutA k l a a') * SB L a b * K ((pmLoop true μ a').cutGlueR k l b)
      = ∑ k ∈ Icc 1 (N - 1), ∑ a : ZMod L, ∑ b : ZMod L,
          wD L K κ (cutMu k (k + 1) μ) (cutA k (k + 1) a a') * SB L a b *
            K ((pmLoop true μ a').cutGlueR k (k + 1) b) := by
    refine sum_Icc_Ioc_adjacent N (fun k l => ∑ a : ZMod L, ∑ b : ZMod L,
      wD L K κ (cutMu k l μ) (cutA k l a a') * SB L a b *
        K ((pmLoop true μ a').cutGlueR k l b)) ?_
    intro k hk l hl hkl
    rw [mem_Icc] at hk
    rw [mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    obtain ⟨h1, h2⟩ := hcutlen k l hk.1 hl.1 hl.2 a
    rw [hlow _ _ h1 (by omega), zero_mul, zero_mul]
  have hU2 : ∑ k ∈ Icc 2 N, ∑ a : ZMod L, ∑ b : ZMod L,
      wD L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) * SB L a b *
        K ((pmLoop false μ a').cutGlueL 1 k b)
      = ∑ a : ZMod L, ∑ b : ZMod L,
          wD L K κ (μ.take (N - 1)) (a'.take (N - 1) ++ [a]) * SB L a b *
            K ((pmLoop false μ a').cutGlueL 1 N b) := by
    rw [Finset.sum_eq_single_of_mem N (by rw [mem_Icc]; omega)]
    intro k hk hkN
    rw [mem_Icc] at hk
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [hlow _ _ (by simp only [List.length_take, List.length_append, List.length_singleton]; omega)
      (by simp only [List.length_append, List.length_take, List.length_singleton]; omega),
      zero_mul, zero_mul]
  have hcancel : (∑ l ∈ Ioc 1 N, ∑ a : ZMod L, ∑ b : ZMod L,
        κ * K ((pmLoop false μ a').cutGlueL 1 l a) * SB L a b *
          (K ((pmLoop false μ a').cutGlueR 1 l b) - K ((pmLoop true μ a').cutGlueR 1 l b)))
      + ∑ k ∈ Icc 2 N, ∑ a : ZMod L, ∑ b : ZMod L,
        κ * (K ((pmLoop true μ a').cutGlueR 1 k a) - K ((pmLoop false μ a').cutGlueR 1 k a))
          * SB L a b * K ((pmLoop false μ a').cutGlueL 1 k b) = 0 := by
    rw [hIoc, ← sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Finset.sum_comm (s := (univ : Finset (ZMod L))) (t := (univ : Finset (ZMod L)))
      (f := fun a b => κ * (K ((pmLoop true μ a').cutGlueR 1 k a)
        - K ((pmLoop false μ a').cutGlueR 1 k a)) * SB L a b *
          K ((pmLoop false μ a').cutGlueL 1 k b)), ← sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [show SB L b a = SB L a b from congrFun (congrFun (SB_transpose L) a) b]
    ring
  simp only [← hNdef]
  -- the Ward-bracket part
  have eA : (∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : ZMod L, ∑ b : ZMod L,
        (∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
          K ((fullLoop μ a' 0).cutGlueR k l b))
      - κ * ((∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : ZMod L, ∑ b : ZMod L,
          K ((pmLoop true μ a').cutGlueL k l a) * SB L a b *
            K ((pmLoop true μ a').cutGlueR k l b))
        - ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : ZMod L, ∑ b : ZMod L,
          K ((pmLoop false μ a').cutGlueL k l a) * SB L a b *
            K ((pmLoop false μ a').cutGlueR k l b))
      = (∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : ZMod L, ∑ b : ZMod L,
          wD L K κ (cutMu k l μ) (cutA k l a a') * SB L a b *
            K ((pmLoop true μ a').cutGlueR k l b))
        + ∑ l ∈ Ioc 1 N, ∑ a : ZMod L, ∑ b : ZMod L,
          κ * K ((pmLoop false μ a').cutGlueL 1 l a) * SB L a b *
            (K ((pmLoop false μ a').cutGlueR 1 l b) - K ((pmLoop true μ a').cutGlueR 1 l b)) := by
    have e1 : ∀ k ∈ Icc 1 N, ∀ l ∈ Ioc k N, ∀ a : ZMod L,
        ∑ b : ZMod L, ((∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
            K ((fullLoop μ a' 0).cutGlueR k l b)
          - κ * (K ((pmLoop true μ a').cutGlueL k l a) * SB L a b *
                K ((pmLoop true μ a').cutGlueR k l b)
              - K ((pmLoop false μ a').cutGlueL k l a) * SB L a b *
                K ((pmLoop false μ a').cutGlueR k l b)))
        = ∑ b : ZMod L, (wD L K κ (cutMu k l μ) (cutA k l a a') * SB L a b *
              K ((pmLoop true μ a').cutGlueR k l b)
            + (if k = 1 then κ * K ((pmLoop false μ a').cutGlueL 1 l a) * SB L a b *
                (K ((pmLoop false μ a').cutGlueR 1 l b)
                  - K ((pmLoop true μ a').cutGlueR 1 l b)) else 0)) :=
      fun k hk l hl a => sum_congr rfl fun b _ => hA k hk l hl a b
    calc _ = ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : ZMod L, ∑ b : ZMod L,
          ((∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k l a)) * SB L a b *
              K ((fullLoop μ a' 0).cutGlueR k l b)
            - κ * (K ((pmLoop true μ a').cutGlueL k l a) * SB L a b *
                  K ((pmLoop true μ a').cutGlueR k l b)
                - K ((pmLoop false μ a').cutGlueL k l a) * SB L a b *
                  K ((pmLoop false μ a').cutGlueR k l b))) := by
          simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      _ = ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : ZMod L, ∑ b : ZMod L,
          (wD L K κ (cutMu k l μ) (cutA k l a a') * SB L a b *
              K ((pmLoop true μ a').cutGlueR k l b)
            + (if k = 1 then κ * K ((pmLoop false μ a').cutGlueL 1 l a) * SB L a b *
                (K ((pmLoop false μ a').cutGlueR 1 l b)
                  - K ((pmLoop true μ a').cutGlueR 1 l b)) else 0)) :=
          sum_congr rfl fun k hk => sum_congr rfl fun l hl => sum_congr rfl fun a _ =>
            e1 k hk l hl a
      _ = _ := by
          simp only [Finset.sum_add_distrib]
          congr 1
          rw [hIcc, sum_insert (by simp)]
          simp only [ite_true]
          rw [Finset.sum_eq_zero (s := Icc 2 N) fun k hk => ?_, add_zero]
          rw [mem_Icc] at hk
          simp only [show k ≠ 1 by omega, ite_false, Finset.sum_const_zero]
  -- the cuts `(k, N + 1)`
  have eB : (∑ k ∈ Icc 1 N, ∑ a : ZMod L, ∑ b : ZMod L,
        (∑ x : ZMod L, K ((fullLoop μ a' x).cutGlueL k (N + 1) a)) * SB L a b *
          K ((fullLoop μ a' 0).cutGlueR k (N + 1) b))
      = c * wStar L K μ a'
        + (∑ k ∈ Icc 2 N, ∑ a : ZMod L, ∑ b : ZMod L,
            wD L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) * SB L a b *
              K ((pmLoop false μ a').cutGlueL 1 k b))
        + ∑ k ∈ Icc 2 N, ∑ a : ZMod L, ∑ b : ZMod L,
            κ * (K ((pmLoop true μ a').cutGlueR 1 k a) - K ((pmLoop false μ a').cutGlueR 1 k a))
              * SB L a b * K ((pmLoop false μ a').cutGlueL 1 k b) := by
    rw [hIcc, sum_insert (by simp), hNdef, cut_one_last L K μ a' hL hμ c h2, ← hNdef, add_assoc,
      ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun b _ => hB k hk a b
  rw [show ∀ A B P P' : ℂ, (W : ℂ) * (A + B) - κ * ((W : ℂ) * P - (W : ℂ) * P')
      = (W : ℂ) * ((A - κ * (P - P')) + B) from fun A B P P' => by ring, eA, eB, hT1, hU2]
  rw [show ∀ T1 T2 cw U2 U3 : ℂ, T1 + T2 + (cw + U2 + U3) = T1 + U2 + cw + (T2 + U3)
      from fun T1 T2 cw U2 U3 => by ring, hcancel, add_zero]

end Cuts

end RBM
