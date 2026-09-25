/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridAzuma
import RBM1D.Gauss.GridDuhamel
import RBM1D.Gauss.GridStop
import RBM1D.Hierarchy.UkerBackBound

/-!
# T1504: tail bounds for the stopped discrete Duhamel martingale

Ticket T1504 (`docs/tickets/T1504.md`) with amend-1 (`docs/tickets/T1504-amend-1.md`), pilot doc
`docs/claude-team/pilot-P4P5-paper.md` §4, §9. Pure probability plus linear algebra on
`V := LoopArg L n → ℂ`. We have a filtration `ℱ`, a stopping time `τ` (`{j < τ} ∈ ℱ j`), grid times
`u : ℕ → ℝ`, edge parameters `ξ`, and write `U j k := Uker L ξ (u j) (u k)`.

## Main declarations

* `RBM.Gauss.Grid.stopped_duhamel_azuma_tail_fixed` : (T1′), the label-weighted Azuma tail for a
  fixed target grid index `k` and label `a`, with deterministic constants `c k a j` that may
  depend on `(k, a)`. It applies `azuma_complex` directly to
  `Σ_{j<k} {j<τ}·(U (j+1) k Z_{j+1}) a`. No inverse kernel, no label union.
* `RBM.Gauss.Grid.stopped_duhamel_azuma_union` : (T1″), the union over `1 ≤ k ≤ K` and all labels
  with per-`(k,a)` thresholds. The event is over all `k ≤ K`; the `k = 0` event is empty because
  `x 0 a > 0`. See the docstring for why the `k = 0` summand is not on the right-hand side.
* `RBM.Gauss.Grid.stopped_duhamel_cheb_tail` : (T2), the sup-norm Chebyshev tail bound for the
  stopped martingale-difference remainder, via the backward kernel (repair (A), T1500).
* `RBM.Gauss.Grid.stopped_duhamel_det_bound` : (T3), the pointwise bound for the stopped sum of a
  guarded norm-bounded remainder (for the O(Δ^{3/2}) errors only, not for the drift), with the
  corollary `stopped_duhamel_det_bound_half` for `t ≤ 1/2` that needs no forward-kernel hypothesis.
* `RBM.Gauss.Grid.stopped_duhamel_azuma_tail` : the original (T1), a sup-norm bound. It does not
  suffice for (2.76) (supervisor 2026-09-25-2045 §1) and must not be consumed.

Every public hypothesis states the stopped increment `{ω' | j < τ ω'}.indicator (…) ω` inline;
`stoppedEdge` is a public abbreviation for it, with the unfolding lemma `stoppedEdge_apply`.
The `Witness` section compiles nonzero Gaussian instances of the hypotheses of (T1), (T1′), (T1″),
(T2) and a nondegenerate (`ξ ≠ 0`) instance of the forward-kernel hypothesis of (T3).
-/

namespace RBM.Gauss.Grid

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

section Setup

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ℱ : Filtration ℕ mΩ'}

/-- Prepend a dummy zero term to a family `f : ℕ → M`.  Used to align a `K`-term family
(the increments indexed `1, …, K`, each with a hypothesis conditional on the *previous* index)
with the Azuma API `azuma_complex`, which wants an *unconditional* base case at index `0`. -/
private def prependZero {M : Type*} [Zero M] (f : ℕ → M) : ℕ → M
  | 0 => 0
  | j + 1 => f j

@[simp] private lemma prependZero_zero {M : Type*} [Zero M] (f : ℕ → M) :
    prependZero f 0 = 0 := rfl

@[simp] private lemma prependZero_succ {M : Type*} [Zero M] (f : ℕ → M) (j : ℕ) :
    prependZero f (j + 1) = f j := rfl

private lemma sum_range_succ_prependZero {M : Type*} [AddCommMonoid M] (f : ℕ → M) (K : ℕ) :
    ∑ i ∈ range (K + 1), prependZero f i = ∑ j ∈ range K, f j := by
  rw [Finset.sum_range_succ' (prependZero f) K]
  simp

/-- A finite sum of `MemLp _ 2 μ` real-valued functions is again `MemLp _ 2 μ`. -/
private lemma memLp_finset_sum {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {ι : Type*} {s : Finset ι} (f : ι → α → ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) : MemLp (fun x => ∑ i ∈ s, f i x) 2 μ := by
  have h := Finset.sum_induction f (fun g : α → ℝ => MemLp g 2 μ)
    (fun _ _ ha hb => ha.add hb) (memLp_const (0 : ℝ)) hf
  have heq : (∑ x ∈ s, f x) = fun x => ∑ i ∈ s, f i x := by
    funext x; rw [Finset.sum_apply]
  rwa [← heq]

/-- `‖(r : ℂ) * ζ‖ < 1` once `0 ≤ r ≤ t < 1` and `‖ζ‖ ≤ 1`. -/
private lemma norm_real_mul_lt_one {r t' : ℝ} (hr0 : 0 ≤ r) (hrt : r ≤ t') (ht1 : t' < 1)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) : ‖(r : ℂ) * ζ‖ < 1 := by
  have heq : ‖(r : ℂ) * ζ‖ = r * ‖ζ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
  rw [heq]
  calc r * ‖ζ‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hζ hr0
    _ = r := mul_one r
    _ ≤ t' := hrt
    _ < 1 := ht1

/-- The backward factorisation of repair (A): for any real `s`, and `0 ≤ r ≤ t < 1`,
`Uker L ξ s r = Uker L ξ t r ∘ Uker L ξ s t` (from `Uker_comp`, content-equivalent to
`Uker_factor`). -/
private lemma back_factor_apply {n : ℕ} (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : Fin n → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {s t r : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hr0 : 0 ≤ r) (hrt : r ≤ t)
    (A : LoopArg L n → ℂ) :
    Uker L ξ (s : ℂ) (r : ℂ) A = Uker L ξ (t : ℂ) (r : ℂ) (Uker L ξ (s : ℂ) (t : ℂ) A) := by
  have ht' : ∀ i, ‖(t : ℂ) * ξ i‖ < 1 := fun i => norm_real_mul_lt_one ht0 le_rfl ht1 (hξ i)
  have hr' : ∀ i, ‖(r : ℂ) * ξ i‖ < 1 := fun i => norm_real_mul_lt_one hr0 hrt ht1 (hξ i)
  exact (Uker_comp L hL ht' hr' A).symm

/-- The backward factorisation applied to a finite sum: for `0 ≤ u 0 ≤ u 1 ≤ …`, `u K = t < 1`,
`k ≤ K` and any family `F : ℕ → V`,
`Σ_{j<k} U_{u_{j+1},u_k} (F j) = U_{t,u_k} (Σ_{j<k} U_{u_{j+1},t} (F j))`. -/
private lemma back_factor_sum_apply {n : ℕ} (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : Fin n → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {u : ℕ → ℝ} {t : ℝ} (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {K : ℕ} (hut : u K = t) (ht1 : t < 1) {k : ℕ} (hkK : k ≤ K)
    (F : ℕ → LoopArg L n → ℂ) (a : LoopArg L n) :
    (∑ j ∈ range k, Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (F j)) a
      = Uker L ξ (t : ℂ) (u k : ℂ)
          (∑ j ∈ range k, Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (F j)) a := by
  have hmono : Monotone u := monotone_nat_of_le_succ hu_succ
  have h0m : ∀ m, 0 ≤ u m := fun m => hu0.trans (hmono (Nat.zero_le m))
  have h0t : 0 ≤ t := hut ▸ h0m K
  have hle_t : ∀ m, m ≤ K → u m ≤ t := fun m hm => hut ▸ hmono hm
  have hstep : ∀ j < k, Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (F j)
      = Uker L ξ (t : ℂ) (u k : ℂ) (Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (F j)) :=
    fun j _ => back_factor_apply L hL hξ h0t ht1 (h0m k) (hle_t k hkK) (F j)
  have hsum_eq : (∑ j ∈ range k, Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (F j))
      = Uker L ξ (t : ℂ) (u k : ℂ) (∑ j ∈ range k, Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (F j)) := by
    calc (∑ j ∈ range k, Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (F j))
        = ∑ j ∈ range k,
            Uker L ξ (t : ℂ) (u k : ℂ) (Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (F j)) :=
          Finset.sum_congr rfl (fun j hj => hstep j (Finset.mem_range.mp hj))
      _ = ∑ j ∈ range k,
            UkerHom L ξ (t : ℂ) (u k : ℂ) (Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (F j)) := by
          simp [UkerHom_apply]
      _ = UkerHom L ξ (t : ℂ) (u k : ℂ)
            (∑ j ∈ range k, Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (F j)) :=
          (map_sum (UkerHom L ξ (t : ℂ) (u k : ℂ)) _ _).symm
      _ = Uker L ξ (t : ℂ) (u k : ℂ)
            (∑ j ∈ range k, Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (F j)) := by
          rw [UkerHom_apply]
  exact congrFun hsum_eq a

/-- Given the `2^n` back-kernel bound on `Uker L ξ t r V a` and a label `a` where the threshold
`2^n * x` is met, some label `b` meets the threshold `x` for `V`. -/
private lemma exists_label_of_back_bound {n : ℕ} (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {ξ : Fin n → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1) {t r : ℝ} (hr0 : 0 ≤ r) (hrt : r ≤ t) (ht1 : t < 1)
    (V : LoopArg L n → ℂ) {x : ℝ} {a : LoopArg L n}
    (ha : 2 ^ n * x ≤ ‖Uker L ξ (t : ℂ) (r : ℂ) V a‖) :
    ∃ b, x ≤ ‖V b‖ := by
  have : Nonempty (LoopArg L n) := ⟨fun _ => 0⟩
  have hA : ∀ b, ‖V b‖ ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖V b‖) :=
    fun b => Finset.le_sup' (fun b => ‖V b‖) (Finset.mem_univ b)
  have hM0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖V b‖) :=
    le_trans (norm_nonneg (V (Classical.arbitrary _))) (hA _)
  have hbound : ‖Uker L ξ (t : ℂ) (r : ℂ) V a‖
      ≤ 2 ^ n * Finset.univ.sup' Finset.univ_nonempty (fun b => ‖V b‖) :=
    norm_Uker_back_le L hL hξ hr0 hrt ht1 hM0 hA a
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hxM : x ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖V b‖) := by
    nlinarith [ha, hbound]
  obtain ⟨b, -, hb⟩ := (Finset.le_sup'_iff (H := Finset.univ_nonempty)).mp hxM
  exact ⟨b, hb⟩

private lemma card_loopArg_eq (L n : ℕ) [NeZero L] : Fintype.card (LoopArg L n) = L ^ n := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

end Setup

section StoppedEdge

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ℱ : Filtration ℕ mΩ'}

/-- The stopped, evaluated-at-one-label kernel image of an increment,
`{j < τ}.indicator (fun ω' => (Uker L ξ (u (j+1)) t' (Z (j+1) ω')) b)`, with target time `t'`
(`t' = u k` for (T1′)/(T1″), `t' = t = u K` for (T1)/(T2)). All public hypotheses state this
expression inline; `stoppedEdge_apply` unfolds the abbreviation. -/
noncomputable def stoppedEdge {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ) (u : ℕ → ℝ)
    (t' : ℝ) (τ : Ω' → ℕ) (Z : ℕ → Ω' → LoopArg L n → ℂ) (b : LoopArg L n) (j : ℕ) : Ω' → ℂ :=
  {ω' | j < τ ω'}.indicator (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Z (j + 1) ω') b)

/-- Unfolding lemma for `stoppedEdge`. -/
theorem stoppedEdge_apply {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ) (u : ℕ → ℝ) (t' : ℝ)
    (τ : Ω' → ℕ) (Z : ℕ → Ω' → LoopArg L n → ℂ) (b : LoopArg L n) (j : ℕ) (ω : Ω') :
    stoppedEdge L ξ u t' τ Z b j ω =
      {ω' | j < τ ω'}.indicator
        (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Z (j + 1) ω') b) ω := rfl

/-- `A ↦ (Uker L ξ s t A) b` is continuous, so it preserves strong measurability. -/
private lemma stronglyMeasurable_Uker_apply {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ) (s t : ℂ)
    {i : ℕ} {W : Ω' → LoopArg L n → ℂ} (hW : StronglyMeasurable[ℱ i] W) (b : LoopArg L n) :
    StronglyMeasurable[ℱ i] (fun ω => Uker L ξ s t (W ω) b) := by
  have hcont : Continuous (fun A : LoopArg L n → ℂ => Uker L ξ s t A b) := by
    have heq : (fun A : LoopArg L n → ℂ => Uker L ξ s t A b)
        = fun A => ∑ c : LoopArg L n, (∏ p, edgeKer L (ξ p) s t (b p) (c p)) * A c := by
      funext A; exact Uker_apply L ξ s t A b
    rw [heq]
    exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
  exact hcont.comp_stronglyMeasurable hW

/-- `stoppedEdge` is `ℱ (j+1)`-strongly measurable. -/
private lemma stronglyMeasurable_stoppedEdge {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ)
    (u : ℕ → ℝ) (t' : ℝ) {τ : Ω' → ℕ} {Z : ℕ → Ω' → LoopArg L n → ℂ}
    (hZ : ∀ i, StronglyMeasurable[ℱ i] (Z i)) (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    (b : LoopArg L n) (j : ℕ) :
    StronglyMeasurable[ℱ (j + 1)] (stoppedEdge L ξ u t' τ Z b j) := by
  have hset : MeasurableSet[ℱ (j + 1)] {ω | j < τ ω} := (ℱ.mono (Nat.le_succ j)) _ (hτmeas j)
  have hW : StronglyMeasurable[ℱ (j + 1)]
      (fun ω => Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Z (j + 1) ω) b) :=
    stronglyMeasurable_Uker_apply L ξ _ _ (hZ (j + 1)) b
  exact hW.indicator hset

private lemma stronglyMeasurable_stoppedEdge_re {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ)
    (u : ℕ → ℝ) (t' : ℝ) {τ : Ω' → ℕ} {Z : ℕ → Ω' → LoopArg L n → ℂ}
    (hZ : ∀ i, StronglyMeasurable[ℱ i] (Z i)) (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    (b : LoopArg L n) (j : ℕ) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω => (stoppedEdge L ξ u t' τ Z b j ω).re) :=
  Complex.continuous_re.comp_stronglyMeasurable
    (stronglyMeasurable_stoppedEdge L ξ u t' hZ hτmeas b j)

private lemma stronglyMeasurable_stoppedEdge_im {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ)
    (u : ℕ → ℝ) (t' : ℝ) {τ : Ω' → ℕ} {Z : ℕ → Ω' → LoopArg L n → ℂ}
    (hZ : ∀ i, StronglyMeasurable[ℱ i] (Z i)) (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    (b : LoopArg L n) (j : ℕ) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω => (stoppedEdge L ξ u t' τ Z b j ω).im) :=
  Complex.continuous_im.comp_stronglyMeasurable
    (stronglyMeasurable_stoppedEdge L ξ u t' hZ hτmeas b j)

/-- `sum_stopped` at one label: the sum up to `min k (τ ω)` is the `k`-horizon sum of
`stoppedEdge`. -/
private lemma stopped_sum_apply_eq {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ) (u : ℕ → ℝ)
    (t' : ℝ) (τ : Ω' → ℕ) (Z : ℕ → Ω' → LoopArg L n → ℂ) (k : ℕ) (ω : Ω') (b : LoopArg L n) :
    (∑ j ∈ range (min k (τ ω)), Uker L ξ (u (j + 1) : ℂ) (t' : ℂ) (Z (j + 1) ω)) b
      = ∑ j ∈ range k, stoppedEdge L ξ u t' τ Z b j ω := by
  rw [Finset.sum_apply]
  exact sum_stopped (Ω' := Ω') (M := ℂ)
    (fun j ω => Uker L ξ (u j : ℂ) (t' : ℂ) (Z j ω) b) τ k ω

/-- The `τ ≤ K` form of `stopped_sum_apply_eq`. -/
private lemma inner_sum_apply_eq {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ) (u : ℕ → ℝ) (t : ℝ)
    {K : ℕ} {τ : Ω' → ℕ} (hτK : ∀ ω, τ ω ≤ K) (Z : ℕ → Ω' → LoopArg L n → ℂ) (ω : Ω')
    (b : LoopArg L n) :
    (∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Z (j + 1) ω)) b
      = ∑ j ∈ range K, stoppedEdge L ξ u t τ Z b j ω := by
  have h := stopped_sum_apply_eq L ξ u t τ Z K ω b
  rwa [min_eq_right (hτK ω)] at h

end StoppedEdge

section Azuma

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] {μ : Measure Ω'}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'}

/-- The common Azuma step: for a fixed label `b`, target time `t'` and horizon `k`, conditional
sub-Gaussian stopped increments give the complex Azuma tail for their `k`-horizon sum. -/
private lemma azuma_stoppedEdge {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ) (u : ℕ → ℝ) (t' : ℝ)
    {τ : Ω' → ℕ} (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    {Z : ℕ → Ω' → LoopArg L n → ℂ} (hZ : ∀ i, StronglyMeasurable[ℱ i] (Z i))
    (b : LoopArg L n) (k : ℕ) {c : ℕ → ℝ≥0}
    (hsubG : ∀ j < k,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => (stoppedEdge L ξ u t' τ Z b j ω).re) (c j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => (stoppedEdge L ξ u t' τ Z b j ω).im) (c j) μ)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ‖∑ j ∈ range k, stoppedEdge L ξ u t' τ Z b j ω‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ range k, (c j : ℝ))) := by
  set Y : ℕ → Ω' → ℂ := prependZero (fun j => stoppedEdge L ξ u t' τ Z b j) with hYdef
  set cc : ℕ → ℝ≥0 := prependZero c with hccdef
  have hYR : StronglyAdapted ℱ (fun i ω => (Y i ω).re) := by
    intro i
    cases i with
    | zero => simpa [hYdef] using stronglyMeasurable_const
    | succ j => simpa [hYdef] using stronglyMeasurable_stoppedEdge_re L ξ u t' hZ hτmeas b j
  have hYI : StronglyAdapted ℱ (fun i ω => (Y i ω).im) := by
    intro i
    cases i with
    | zero => simpa [hYdef] using stronglyMeasurable_const
    | succ j => simpa [hYdef] using stronglyMeasurable_stoppedEdge_im L ξ u t' hZ hτmeas b j
  have h0R : HasSubgaussianMGF (fun ω => (Y 0 ω).re) (cc 0) μ := by
    simp [hYdef, hccdef]
  have h0I : HasSubgaussianMGF (fun ω => (Y 0 ω).im) (cc 0) μ := by
    simp [hYdef, hccdef]
  have hCR : ∀ i < k + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).re) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    simpa [hYdef, hccdef] using (hsubG i hi).1
  have hCI : ∀ i < k + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).im) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    simpa [hYdef, hccdef] using (hsubG i hi).2
  have hazuma := azuma_complex (Z := Y) (c := cc) hYR hYI (k + 1) h0R h0I hCR hCI hx
  rw [NNReal.coe_sum] at hazuma
  have hsum : ∀ ω, ∑ j ∈ range k, stoppedEdge L ξ u t' τ Z b j ω = ∑ i ∈ range (k + 1), Y i ω := by
    intro ω
    have h3 := congrFun
      (sum_range_succ_prependZero (fun j => stoppedEdge L ξ u t' τ Z b j) k) ω
    simp only [Finset.sum_apply] at h3
    rw [hYdef, h3]
  have hsumeq : ∑ i ∈ range (k + 1), (cc i : ℝ) = ∑ j ∈ range k, (c j : ℝ) := by
    have := sum_range_succ_prependZero (M := ℝ≥0) c k
    have hcast : ((∑ i ∈ range (k + 1), prependZero c i : ℝ≥0) : ℝ)
        = ((∑ j ∈ range k, c j : ℝ≥0) : ℝ) := by exact_mod_cast this
    simpa [hccdef] using hcast
  have hset : {ω | x ≤ ‖∑ j ∈ range k, stoppedEdge L ξ u t' τ Z b j ω‖}
      = {ω | x ≤ ‖∑ i ∈ range (k + 1), Y i ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hsum ω]
  rw [hset, ← hsumeq]
  exact hazuma

/-- **(T1′)** `stopped_duhamel_azuma_tail_fixed` (T1504 amend-1): the label-weighted Azuma tail
for a fixed target grid index `k` and a fixed label `a`. The constants `c k a j` are
deterministic and may depend on the target `(k, a)`. Route: `sum_stopped` rewrites
`(Σ_{j<min k τ} U (j+1) k Z_{j+1}) a` as `Σ_{j<k} {j<τ}·(U (j+1) k Z_{j+1}) a`, and `azuma_complex`
is applied to that sum. No inverse kernel `U⁻¹` and no union over labels.

No hypothesis on `u`, `ξ` or `k` is needed: `Uker` is a total function of its complex times. -/
theorem stopped_duhamel_azuma_tail_fixed (L : ℕ) [NeZero L] {n : ℕ} {ξ : Fin n → ℂ}
    {u : ℕ → ℝ} {τ : Ω' → ℕ} (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    {Z : ℕ → Ω' → LoopArg L n → ℂ} (hZ : ∀ i, StronglyMeasurable[ℱ i] (Z i))
    (k : ℕ) (a : LoopArg L n) {c : ℕ → LoopArg L n → ℕ → ℝ≥0}
    (hsubG : ∀ j < k,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).re) (c k a j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).im) (c k a j) μ)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ‖(∑ j ∈ range (min k (τ ω)),
        Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω)) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ range k, (c k a j : ℝ))) := by
  have hset : {ω | x ≤ ‖(∑ j ∈ range (min k (τ ω)),
        Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω)) a‖}
      = {ω | x ≤ ‖∑ j ∈ range k, stoppedEdge L ξ u (u k) τ Z a j ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, stopped_sum_apply_eq L ξ u (u k) τ Z k ω a]
  rw [hset]
  exact azuma_stoppedEdge L ξ u (u k) hτmeas hZ a k (c := c k a) hsubG hx

/-- **(T1″)** `stopped_duhamel_azuma_union` (T1504 amend-1): the union of the (T1′) events over
all target grid indices `k ≤ K` and all labels `a`, with a threshold `x k a` for each `(k, a)`. On
`{τ = k}` the `k`-th sum is the linear term of the stopped Duhamel expansion at `u_τ`.

**The `k = 0` summand.** The amend writes the right-hand side as `Σ_{k ≤ K} Σ_a …`. For `k = 0`
the inner constant sum is empty, so under Lean's `a / 0 = 0` that summand equals
`4 * exp 0 = 4`. The literal form is then trivially true: its RHS is `≥ 4`, while the LHS is a
probability. The witness section compiles this fact. In the paper's convention the `k = 0`
summand is `0` (for `x 0 a > 0`), and the `k = 0` event `{x 0 a ≤ ‖0‖}` is empty. So we keep the
event over all `k ≤ K`, assume `x 0 a > 0` (`hx0`), and sum the RHS over `k ∈ Icc 1 K` only.
This RHS is at most the literal one, so this statement implies the literal form. -/
theorem stopped_duhamel_azuma_union (L : ℕ) [NeZero L] {n : ℕ} {ξ : Fin n → ℂ}
    {u : ℕ → ℝ} {τ : Ω' → ℕ} (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω})
    {Z : ℕ → Ω' → LoopArg L n → ℂ} (hZ : ∀ i, StronglyMeasurable[ℱ i] (Z i))
    (K : ℕ) {c : ℕ → LoopArg L n → ℕ → ℝ≥0}
    (hsubG : ∀ k ≤ K, ∀ a : LoopArg L n, ∀ j < k,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).re) (c k a j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω') a) ω).im) (c k a j) μ)
    {x : ℕ → LoopArg L n → ℝ} (hx : ∀ k ≤ K, ∀ a, 0 ≤ x k a) (hx0 : ∀ a, 0 < x 0 a) :
    μ.real {ω | ∃ k ≤ K, ∃ a, x k a ≤ ‖(∑ j ∈ range (min k (τ ω)),
        Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω)) a‖} ≤
      ∑ k ∈ Finset.Icc 1 K, ∑ a : LoopArg L n,
        4 * Real.exp (-(x k a) ^ 2 / (4 * ∑ j ∈ range k, (c k a j : ℝ))) := by
  set E : ℕ → LoopArg L n → Set Ω' := fun k a => {ω | x k a ≤ ‖(∑ j ∈ range (min k (τ ω)),
        Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω)) a‖} with hEdef
  have hincl : {ω | ∃ k ≤ K, ∃ a, x k a ≤ ‖(∑ j ∈ range (min k (τ ω)),
        Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω)) a‖}
      ⊆ ⋃ k ∈ Finset.Icc 1 K, ⋃ a, E k a := by
    rintro ω ⟨k, hk, a, ha⟩
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exfalso
      have h0 : (∑ j ∈ range (min 0 (τ ω)),
          Uker L ξ (u (j + 1) : ℂ) (u 0 : ℂ) (Z (j + 1) ω)) a = 0 := by simp
      rw [h0, norm_zero] at ha
      exact absurd ha (not_le.mpr (hx0 a))
    · simp only [Set.mem_iUnion]
      exact ⟨k, Finset.mem_Icc.mpr ⟨hkpos, hk⟩, a, ha⟩
  calc μ.real {ω | ∃ k ≤ K, ∃ a, x k a ≤ ‖(∑ j ∈ range (min k (τ ω)),
        Uker L ξ (u (j + 1) : ℂ) (u k : ℂ) (Z (j + 1) ω)) a‖}
      ≤ μ.real (⋃ k ∈ Finset.Icc 1 K, ⋃ a, E k a) := measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.Icc 1 K, μ.real (⋃ a, E k a) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ∑ a : LoopArg L n, μ.real (E k a) :=
        Finset.sum_le_sum fun k _ => measureReal_iUnion_fintype_le _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ∑ a : LoopArg L n,
        4 * Real.exp (-(x k a) ^ 2 / (4 * ∑ j ∈ range k, (c k a j : ℝ))) := by
        refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ => ?_
        have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
        exact stopped_duhamel_azuma_tail_fixed L hτmeas hZ k a (hsubG k hkK a) (hx k hkK a)

/-- **(T1)**, original target of T1504 (before amend-1). **Sup-norm; does not suffice for
(2.76), see supervisor 2026-09-25-2045 §1.** No consumer may use it; use (T1′)/(T1″) instead.
It bounds the stopped martingale part uniformly over labels. Route: factor
`U (j+1) (τ ω) = (U (τ ω) K)⁻¹ ∘ U (j+1) K`, bound the inverse by `norm_Uker_back_le` (factor
`2^n`), apply `azuma_complex` per label, and take the union over the `L^n` labels. -/
theorem stopped_duhamel_azuma_tail (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {u : ℕ → ℝ} {t : ℝ} (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {K : ℕ} (hut : u K = t) (ht1 : t < 1) {τ : Ω' → ℕ} (hτK : ∀ ω, τ ω ≤ K)
    (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) {Z : ℕ → Ω' → LoopArg L n → ℂ}
    (hZ : ∀ i, StronglyMeasurable[ℱ i] (Z i)) {c : ℕ → ℝ≥0}
    (hsubG : ∀ b : LoopArg L n, ∀ j < K,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Z (j + 1) ω') b) ω).re) (c j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Z (j + 1) ω') b) ω).im) (c j) μ)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | ∃ a, 2 ^ n * x ≤
        ‖(∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (u (τ ω) : ℂ) (Z (j + 1) ω)) a‖} ≤
      4 * (L : ℝ) ^ n * Real.exp (-x ^ 2 / (4 * ∑ j ∈ range K, (c j : ℝ))) := by
  have hmono : Monotone u := monotone_nat_of_le_succ hu_succ
  have h0m : ∀ m, 0 ≤ u m := fun m => hu0.trans (hmono (Nat.zero_le m))
  have hincl : {ω | ∃ a, 2 ^ n * x ≤
      ‖(∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (u (τ ω) : ℂ) (Z (j + 1) ω)) a‖}
      ⊆ ⋃ b : LoopArg L n, {ω | x ≤ ‖∑ j ∈ range K, stoppedEdge L ξ u t τ Z b j ω‖} := by
    intro ω hω
    obtain ⟨a, ha⟩ := hω
    rw [back_factor_sum_apply L hL hξ hu0 hu_succ hut ht1 (hτK ω) (fun j => Z (j + 1) ω) a]
      at ha
    have hle_t : u (τ ω) ≤ t := hut ▸ hmono (hτK ω)
    obtain ⟨b, hb⟩ := exists_label_of_back_bound L hL hξ (h0m (τ ω)) hle_t ht1 _ ha
    rw [inner_sum_apply_eq L ξ u t hτK Z ω b] at hb
    exact Set.mem_iUnion.mpr ⟨b, hb⟩
  calc μ.real {ω | ∃ a, 2 ^ n * x ≤
        ‖(∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (u (τ ω) : ℂ) (Z (j + 1) ω)) a‖}
      ≤ μ.real (⋃ b : LoopArg L n, {ω | x ≤ ‖∑ j ∈ range K, stoppedEdge L ξ u t τ Z b j ω‖}) :=
        measureReal_mono hincl
    _ ≤ ∑ b : LoopArg L n, μ.real {ω | x ≤ ‖∑ j ∈ range K, stoppedEdge L ξ u t τ Z b j ω‖} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _b : LoopArg L n, 4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ range K, (c j : ℝ))) :=
        Finset.sum_le_sum fun b _ => azuma_stoppedEdge L ξ u t hτmeas hZ b K (hsubG b) hx
    _ = 4 * (L : ℝ) ^ n * Real.exp (-x ^ 2 / (4 * ∑ j ∈ range K, (c j : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, card_loopArg_eq, nsmul_eq_mul]
        push_cast
        ring

end Azuma

section Cheb

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ'}

/-- **(T2)**: the discrete Chebyshev tail bound for the stopped Duhamel martingale-difference
remainder, pilot doc §4/§9 repair (A) (sup-norm, via the backward kernel of T1500). Route:
backward factorisation, then per label the real/imaginary partial sums are martingales
(`martingale_of_condExp_sub_eq_zero_nat`), `martingale_sq_eq_sum`, and Chebyshev. `0 < x` is
needed: at `x = 0` the RHS is `0` under `a / 0 = 0`. -/
theorem stopped_duhamel_cheb_tail (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {u : ℕ → ℝ} {t : ℝ} (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {K : ℕ} (hut : u K = t) (ht1 : t < 1) {τ : Ω' → ℕ} (hτK : ∀ ω, τ ω ≤ K)
    (hτmeas : ∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) {Y : ℕ → Ω' → LoopArg L n → ℂ}
    (hY : ∀ i, StronglyMeasurable[ℱ i] (Y i)) {e : ℕ → ℝ}
    (hYmeanRe : ∀ b : LoopArg L n, ∀ j < K,
      μ[fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).re | ℱ j] =ᵐ[μ] 0)
    (hYmeanIm : ∀ b : LoopArg L n, ∀ j < K,
      μ[fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).im | ℱ j] =ᵐ[μ] 0)
    (hYmemLpRe : ∀ b : LoopArg L n, ∀ j < K,
      MemLp (fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).re) 2 μ)
    (hYmemLpIm : ∀ b : LoopArg L n, ∀ j < K,
      MemLp (fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).im) 2 μ)
    (hYbound : ∀ b : LoopArg L n, ∀ j < K,
      ∫ ω, ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).re ^ 2 ∂μ
        + ∫ ω, ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).im ^ 2 ∂μ ≤ e j)
    {x : ℝ} (hx : 0 < x) :
    μ.real {ω | ∃ a, 2 ^ n * x ≤
        ‖(∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (u (τ ω) : ℂ) (Y (j + 1) ω)) a‖} ≤
      (L : ℝ) ^ n * (∑ j ∈ range K, e j) / x ^ 2 := by
  set vector : Ω' → LoopArg L n → ℂ :=
    fun ω => ∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω) with hvecdef
  have hincl : {ω | ∃ a, 2 ^ n * x ≤
      ‖(∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (u (τ ω) : ℂ) (Y (j + 1) ω)) a‖}
      ⊆ ⋃ b : LoopArg L n, {ω | x ≤ ‖vector ω b‖} := by
    intro ω hω
    obtain ⟨a, ha⟩ := hω
    have hfact := back_factor_sum_apply L hL hξ hu0 hu_succ hut ht1 (hτK ω)
      (fun j => Y (j + 1) ω) a
    rw [hfact] at ha
    have hmono : Monotone u := monotone_nat_of_le_succ hu_succ
    have h0m : ∀ m, 0 ≤ u m := fun m => hu0.trans (hmono (Nat.zero_le m))
    have hle_t : u (τ ω) ≤ t := hut ▸ hmono (hτK ω)
    obtain ⟨b, hb⟩ := exists_label_of_back_bound L hL hξ (h0m (τ ω)) hle_t ht1 (vector ω) ha
    exact Set.mem_iUnion.mpr ⟨b, hb⟩
  calc μ.real {ω | ∃ a, 2 ^ n * x ≤
        ‖(∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (u (τ ω) : ℂ) (Y (j + 1) ω)) a‖}
      ≤ μ.real (⋃ b : LoopArg L n, {ω | x ≤ ‖vector ω b‖}) := measureReal_mono hincl
    _ ≤ ∑ b : LoopArg L n, μ.real {ω | x ≤ ‖vector ω b‖} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _b : LoopArg L n, (∑ j ∈ range K, e j) / x ^ 2 := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        set W : ℕ → Ω' → ℂ := stoppedEdge L ξ u t τ Y b with hWdef
        set Mre : ℕ → Ω' → ℝ := fun i ω => ∑ j ∈ range (min i K), (W j ω).re with hMredef
        set Mim : ℕ → Ω' → ℝ := fun i ω => ∑ j ∈ range (min i K), (W j ω).im with hMimdef
        have hWadaptRe : ∀ j, StronglyMeasurable[ℱ (j + 1)] (fun ω => (W j ω).re) :=
          fun j => stronglyMeasurable_stoppedEdge_re L ξ u t hY hτmeas b j
        have hWadaptIm : ∀ j, StronglyMeasurable[ℱ (j + 1)] (fun ω => (W j ω).im) :=
          fun j => stronglyMeasurable_stoppedEdge_im L ξ u t hY hτmeas b j
        have hadpRe : StronglyAdapted ℱ Mre := by
          intro i
          refine Finset.stronglyMeasurable_fun_sum (range (min i K))
            (fun j _ => (hWadaptRe j).mono (ℱ.mono ?_))
          have : j + 1 ≤ min i K := by
            have hj : j ∈ range (min i K) := ‹j ∈ range (min i K)›
            simp only [Finset.mem_range] at hj
            omega
          exact this.trans (min_le_left i K)
        have hadpIm : StronglyAdapted ℱ Mim := by
          intro i
          refine Finset.stronglyMeasurable_fun_sum (range (min i K))
            (fun j _ => (hWadaptIm j).mono (ℱ.mono ?_))
          have : j + 1 ≤ min i K := by
            have hj : j ∈ range (min i K) := ‹j ∈ range (min i K)›
            simp only [Finset.mem_range] at hj
            omega
          exact this.trans (min_le_left i K)
        have hMemLpRe : ∀ i, MemLp (Mre i) 2 μ := fun i =>
          memLp_finset_sum (fun j ω => (W j ω).re)
            (fun j hj => hYmemLpRe b j
              (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right i K)))
        have hMemLpIm : ∀ i, MemLp (Mim i) 2 μ := fun i =>
          memLp_finset_sum (fun j ω => (W j ω).im)
            (fun j hj => hYmemLpIm b j
              (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right i K)))
        have hintRe : ∀ i, Integrable (Mre i) μ := fun i => (hMemLpRe i).integrable (by norm_num)
        have hintIm : ∀ i, Integrable (Mim i) μ := fun i => (hMemLpIm i).integrable (by norm_num)
        have hM0Re : Mre 0 = 0 := by funext ω; simp [hMredef]
        have hM0Im : Mim 0 = 0 := by funext ω; simp [hMimdef]
        have hstepRe : ∀ i, μ[Mre (i + 1) - Mre i | ℱ i] =ᵐ[μ] 0 := by
          intro i
          by_cases hiK : i < K
          · have heq : Mre (i + 1) - Mre i = fun ω => (W i ω).re := by
              funext ω
              simp only [hMredef, Pi.sub_apply]
              have h1 : min (i + 1) K = i + 1 := by omega
              have h2 : min i K = i := by omega
              rw [h1, h2, Finset.sum_range_succ]
              ring
            rw [heq]
            exact hYmeanRe b i hiK
          · have heq : Mre (i + 1) - Mre i = 0 := by
              funext ω
              simp only [hMredef, Pi.sub_apply, Pi.zero_apply]
              have h1 : min (i + 1) K = K := by omega
              have h2 : min i K = K := by omega
              rw [h1, h2]; ring
            rw [heq, condExp_zero]
        have hstepIm : ∀ i, μ[Mim (i + 1) - Mim i | ℱ i] =ᵐ[μ] 0 := by
          intro i
          by_cases hiK : i < K
          · have heq : Mim (i + 1) - Mim i = fun ω => (W i ω).im := by
              funext ω
              simp only [hMimdef, Pi.sub_apply]
              have h1 : min (i + 1) K = i + 1 := by omega
              have h2 : min i K = i := by omega
              rw [h1, h2, Finset.sum_range_succ]
              ring
            rw [heq]
            exact hYmeanIm b i hiK
          · have heq : Mim (i + 1) - Mim i = 0 := by
              funext ω
              simp only [hMimdef, Pi.sub_apply, Pi.zero_apply]
              have h1 : min (i + 1) K = K := by omega
              have h2 : min i K = K := by omega
              rw [h1, h2]; ring
            rw [heq, condExp_zero]
        have hMartRe : Martingale Mre ℱ μ :=
          martingale_of_condExp_sub_eq_zero_nat hadpRe hintRe hstepRe
        have hMartIm : Martingale Mim ℱ μ :=
          martingale_of_condExp_sub_eq_zero_nat hadpIm hintIm hstepIm
        have hsqRe := martingale_sq_eq_sum hMartRe hM0Re hMemLpRe K
        have hsqIm := martingale_sq_eq_sum hMartIm hM0Im hMemLpIm K
        have hMreK : Mre K = fun ω => ∑ j ∈ range K, (W j ω).re := by
          simp [hMredef, min_self]
        have hMimK : Mim K = fun ω => ∑ j ∈ range K, (W j ω).im := by
          simp [hMimdef, min_self]
        have hΔRe : ∀ j < K, ∀ ω, Mre (j + 1) ω - Mre j ω = (W j ω).re := by
          intro j hj ω
          simp only [hMredef]
          have h1 : min (j + 1) K = j + 1 := by omega
          have h2 : min j K = j := by omega
          rw [h1, h2, Finset.sum_range_succ]
          ring
        have hΔIm : ∀ j < K, ∀ ω, Mim (j + 1) ω - Mim j ω = (W j ω).im := by
          intro j hj ω
          simp only [hMimdef]
          have h1 : min (j + 1) K = j + 1 := by omega
          have h2 : min j K = j := by omega
          rw [h1, h2, Finset.sum_range_succ]
          ring
        have hsumRe : ∫ ω, (Mre K ω) ^ 2 ∂μ = ∑ j ∈ range K, ∫ ω, (W j ω).re ^ 2 ∂μ := by
          rw [hsqRe]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
          funext ω
          rw [hΔRe j (Finset.mem_range.mp hj) ω]
        have hsumIm : ∫ ω, (Mim K ω) ^ 2 ∂μ = ∑ j ∈ range K, ∫ ω, (W j ω).im ^ 2 ∂μ := by
          rw [hsqIm]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
          funext ω
          rw [hΔIm j (Finset.mem_range.mp hj) ω]
        have hboundtot :
            ∫ ω, (Mre K ω) ^ 2 ∂μ + ∫ ω, (Mim K ω) ^ 2 ∂μ ≤ ∑ j ∈ range K, e j := by
          rw [hsumRe, hsumIm, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum (fun j hj => hYbound b j (Finset.mem_range.mp hj))
        have hveceq : ∀ ω, ‖vector ω b‖ ^ 2 = (Mre K ω) ^ 2 + (Mim K ω) ^ 2 := by
          intro ω
          have hv : vector ω b = ∑ j ∈ range K, W j ω := by
            rw [hvecdef]; exact inner_sum_apply_eq L ξ u t hτK Y ω b
          have hre : (vector ω b).re = Mre K ω := by rw [hv, hMreK]; simp [Complex.re_sum]
          have him : (vector ω b).im = Mim K ω := by rw [hv, hMimK]; simp [Complex.im_sum]
          have hns : ‖vector ω b‖ ^ 2 = (vector ω b).re ^ 2 + (vector ω b).im ^ 2 := by
            rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
          rw [hns, hre, him]
        have hintf : Integrable (fun ω => (Mre K ω) ^ 2 + (Mim K ω) ^ 2) μ :=
          ((hMemLpRe K).integrable_sq).add ((hMemLpIm K).integrable_sq)
        have hnn : 0 ≤ᵐ[μ] fun ω => (Mre K ω) ^ 2 + (Mim K ω) ^ 2 :=
          ae_of_all _ fun ω => by positivity
        have hmarkov := mul_meas_ge_le_integral_of_nonneg hnn hintf (x ^ 2)
        have hsetEq :
            {ω | x ≤ ‖vector ω b‖} = {ω | x ^ 2 ≤ (Mre K ω) ^ 2 + (Mim K ω) ^ 2} := by
          ext ω
          rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← hveceq ω]
          constructor
          · intro h; exact pow_le_pow_left₀ hx.le h 2
          · intro h
            exact (pow_le_pow_iff_left₀ hx.le (norm_nonneg _) two_ne_zero).mp h
        rw [hsetEq]
        rw [le_div_iff₀ (by positivity : (0:ℝ) < x ^ 2)]
        calc μ.real {ω | x ^ 2 ≤ (Mre K ω) ^ 2 + (Mim K ω) ^ 2} * x ^ 2
            = x ^ 2 * μ.real {ω | x ^ 2 ≤ (Mre K ω) ^ 2 + (Mim K ω) ^ 2} := by ring
          _ ≤ ∫ ω, (Mre K ω) ^ 2 + (Mim K ω) ^ 2 ∂μ := hmarkov
          _ = ∫ ω, (Mre K ω) ^ 2 ∂μ + ∫ ω, (Mim K ω) ^ 2 ∂μ :=
            integral_add (hMemLpRe K).integrable_sq (hMemLpIm K).integrable_sq
          _ ≤ ∑ j ∈ range K, e j := hboundtot
    _ = (L : ℝ) ^ n * (∑ j ∈ range K, e j) / x ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, card_loopArg_eq, nsmul_eq_mul]
        push_cast
        ring

end Cheb

section Det

variable {Ω' : Type*}

/-- **(T3)**: the pointwise bound for the stopped sum of a guarded norm-bounded remainder. It is
meant for the O(Δ^{3/2}) errors of the stopped Duhamel expansion only, **not for the drift**.
Pure linear algebra: backward factorisation, then T1500's `norm_Uker_back_le` (factor `2^n`).

`hR : ∀ j ω, j < τ ω → ∀ b, ‖R j ω b‖ ≤ r j` is the amend-1 hypothesis (guarded by `j < τ ω`).
`hFwd` is the forward-kernel bound on the same guarded range. It is a separate hypothesis because
the forward kernel `Uker L ξ (u (j+1)) t` has no uniform max-norm bound as `t‖ξ‖ → 1⁻` (row
bound `1 + (t-s)‖ξ‖(1-t‖ξ‖)⁻¹`). So `hR` does not imply `hFwd` for general `t < 1`, and the
proof uses only `hFwd` and `hr0`: (T3) is a conditional adapter. For `t ≤ 1/2` and any `ξ` with
`‖ξ i‖ ≤ 1`, `hFwd` follows from `hR` (`hFwd_of_le_half`), giving
`stopped_duhamel_det_bound_half`. -/
theorem stopped_duhamel_det_bound (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {u : ℕ → ℝ} {t : ℝ} (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {K : ℕ} (hut : u K = t) (ht1 : t < 1) {τ : Ω' → ℕ} (hτK : ∀ ω, τ ω ≤ K)
    (R : ℕ → Ω' → LoopArg L n → ℂ) {r : ℕ → ℝ} (hr0 : ∀ j, 0 ≤ r j)
    (hR : ∀ j ω, j < τ ω → ∀ b, ‖R j ω b‖ ≤ r j)
    (hFwd : ∀ j ω, j < τ ω → ∀ a, ‖Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (R j ω) a‖ ≤ 2 ^ n * r j)
    (ω : Ω') (a : LoopArg L n) :
    ‖(∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (u (τ ω) : ℂ) (R j ω)) a‖ ≤
      2 ^ n * (2 ^ n * ∑ j ∈ range K, r j) := by
  have hmono : Monotone u := monotone_nat_of_le_succ hu_succ
  have h0m : ∀ m, 0 ≤ u m := fun m => hu0.trans (hmono (Nat.zero_le m))
  have hle_t : u (τ ω) ≤ t := hut ▸ hmono (hτK ω)
  rw [back_factor_sum_apply L hL hξ hu0 hu_succ hut ht1 (hτK ω) (fun j => R j ω) a]
  have hM' : ∀ b, ‖(∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (R j ω)) b‖
      ≤ 2 ^ n * ∑ j ∈ range K, r j := by
    intro b
    calc ‖(∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (R j ω)) b‖
        = ‖∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (R j ω) b‖ := by
          rw [Finset.sum_apply]
      _ ≤ ∑ j ∈ range (τ ω), ‖Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (R j ω) b‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range (τ ω), 2 ^ n * r j :=
          Finset.sum_le_sum (fun j hj => hFwd j ω (Finset.mem_range.mp hj) b)
      _ = 2 ^ n * ∑ j ∈ range (τ ω), r j := by rw [Finset.mul_sum]
      _ ≤ 2 ^ n * ∑ j ∈ range K, r j := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (hτK ω))
              (fun j _ _ => hr0 j)) (by positivity)
  have hM0 : 0 ≤ 2 ^ n * ∑ j ∈ range K, r j :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hr0 j))
  exact norm_Uker_back_le L hL hξ (h0m (τ ω)) hle_t ht1 hM0 hM' a

/-- Forward-kernel bound for `t ≤ 1/2`: for `0 ≤ s ≤ t ≤ 1/2` and `‖ξ i‖ ≤ 1`,
`‖Uker L ξ s t A a‖ ≤ 2^n M` whenever `‖A b‖ ≤ M` for all `b`. Uses `norm_Uker_apply_le` with
`C = 2`: `1 + ‖(s-t)ξ‖(1-‖tξ‖)⁻¹ ≤ 1 + (t-s)/(1-t) ≤ 1 + (1/2)/(1/2) = 2`. -/
theorem norm_Uker_fwd_le_of_le_half (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 / 2)
    {A : LoopArg L n → ℂ} {M : ℝ} (hM0 : 0 ≤ M) (hA : ∀ b, ‖A b‖ ≤ M) (a : LoopArg L n) :
    ‖Uker L ξ (s : ℂ) (t : ℂ) A a‖ ≤ 2 ^ n * M := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hy : ∀ i, ‖(t : ℂ) * ξ i‖ ≤ t := fun i => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    nlinarith [hξ i, norm_nonneg (ξ i)]
  have hz : ∀ i, ‖((s : ℂ) - (t : ℂ)) * ξ i‖ ≤ t - s := fun i => by
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonpos (by linarith)]
    nlinarith [hξ i, norm_nonneg (ξ i)]
  have hlt : ∀ i, ‖(t : ℂ) * ξ i‖ < 1 := fun i => (hy i).trans_lt (by linarith)
  have hC : ∀ i, 1 + ‖((s : ℂ) - (t : ℂ)) * ξ i‖ * (1 - ‖(t : ℂ) * ξ i‖)⁻¹ ≤ 2 := by
    intro i
    have h1 : (1 / 2 : ℝ) ≤ 1 - ‖(t : ℂ) * ξ i‖ := by linarith [hy i]
    have hpos : (0 : ℝ) < 1 - ‖(t : ℂ) * ξ i‖ := by linarith
    have hinv : (1 - ‖(t : ℂ) * ξ i‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]; linarith
    have hz' : ‖((s : ℂ) - (t : ℂ)) * ξ i‖ ≤ 1 / 2 := (hz i).trans (by linarith)
    have hinv0 : 0 ≤ (1 - ‖(t : ℂ) * ξ i‖)⁻¹ := inv_nonneg.mpr hpos.le
    nlinarith [norm_nonneg (((s : ℂ) - (t : ℂ)) * ξ i)]
  exact norm_Uker_apply_le L hL hlt hM0 hC hA a

/-- Nondegenerate witness for (T3)'s `hFwd` (audit defect 3): for any `ξ` with `‖ξ i‖ ≤ 1`,
any grid `0 ≤ u 0 ≤ u 1 ≤ …` with `u K = t ≤ 1/2`, any `τ ≤ K`, and any remainder satisfying the
guarded `hR`, the guarded `hFwd` holds. -/
theorem hFwd_of_le_half (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {u : ℕ → ℝ} {t : ℝ} (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {K : ℕ} (hut : u K = t) (ht : t ≤ 1 / 2) {τ : Ω' → ℕ} (hτK : ∀ ω, τ ω ≤ K)
    (R : ℕ → Ω' → LoopArg L n → ℂ) {r : ℕ → ℝ} (hr0 : ∀ j, 0 ≤ r j)
    (hR : ∀ j ω, j < τ ω → ∀ b, ‖R j ω b‖ ≤ r j) :
    ∀ j ω, j < τ ω → ∀ a, ‖Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (R j ω) a‖ ≤ 2 ^ n * r j := by
  intro j ω hj a
  have hmono : Monotone u := monotone_nat_of_le_succ hu_succ
  have h0 : 0 ≤ u (j + 1) := hu0.trans (hmono (Nat.zero_le _))
  have hle : u (j + 1) ≤ t := hut ▸ hmono (by have := hτK ω; omega)
  exact norm_Uker_fwd_le_of_le_half L hL hξ h0 hle ht (hr0 j) (hR j ω hj) a

/-- (T3) for `t ≤ 1/2` without the forward-kernel hypothesis. -/
theorem stopped_duhamel_det_bound_half (L : ℕ) [NeZero L] (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {u : ℕ → ℝ} {t : ℝ} (hu0 : 0 ≤ u 0) (hu_succ : ∀ j, u j ≤ u (j + 1))
    {K : ℕ} (hut : u K = t) (ht : t ≤ 1 / 2) {τ : Ω' → ℕ} (hτK : ∀ ω, τ ω ≤ K)
    (R : ℕ → Ω' → LoopArg L n → ℂ) {r : ℕ → ℝ} (hr0 : ∀ j, 0 ≤ r j)
    (hR : ∀ j ω, j < τ ω → ∀ b, ‖R j ω b‖ ≤ r j) (ω : Ω') (a : LoopArg L n) :
    ‖(∑ j ∈ range (τ ω), Uker L ξ (u (j + 1) : ℂ) (u (τ ω) : ℂ) (R j ω)) a‖ ≤
      2 ^ n * (2 ^ n * ∑ j ∈ range K, r j) :=
  stopped_duhamel_det_bound L hL hξ hu0 hu_succ hut (by linarith) hτK R hr0 hR
    (hFwd_of_le_half L hL hξ hu0 hu_succ hut ht hτK R hr0 hR) ω a

end Det

section Witness

/-! ### Satisfiability witnesses

* `Z = 0` / `Y = 0`: all hypotheses of (T1), (T1′), (T1″), (T2) hold with constants `0`
  (all five (T2) hypotheses are covered).
* Nonzero Gaussian (audit defect 1): `Ω' = ℝ`, `μ = gaussianReal 0 1`, `ℱ 0 = ⊥`,
  `ℱ (i+1) = borel ℝ`, `n = 0` (one label, `Uker = id`), `τ ≡ 1`, `Z (i+1) ω = ω` (constant
  vector), `c ≡ 1`, `e ≡ 1`. Each example applies the target theorem and obtains a genuine
  Gaussian tail: `γ{x ≤ |ω|} ≤ 4 e^{-x²/4}` from (T1), (T1′), (T1″), and `≤ 1/x²` from (T2).
* (T3): nondegenerate `hFwd` for `ξ = 1`, `u 1 = 1/4 < t = 1/2` (audit defect 3); the general
  statement is `hFwd_of_le_half`.
* The literal amend form of (T1″) (RHS summed over all `k ≤ K`) is trivially true. -/

private lemma Uker_zero_vec {n : ℕ} (L : ℕ) [NeZero L] (ξ : Fin n → ℂ) (s t : ℂ) :
    Uker L ξ s t (0 : LoopArg L n → ℂ) = 0 := by
  rw [← UkerHom_apply]; exact map_zero _

/-- `Z = 0` witness for the (T1′)/(T1″) hypotheses (any target `(k, a)`, any `τ`, `c = 0`), and
hence, with target time `t`, for (T1). -/
example {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] {μ : Measure Ω'}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'} (L : ℕ) [NeZero L] {n : ℕ}
    (ξ : Fin n → ℂ) (u : ℕ → ℝ) (τ : Ω' → ℕ) (k : ℕ) (a : LoopArg L n) :
    (∀ j, MeasurableSet[ℱ j] {ω | j < τ ω}) →
    ∀ j < k,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ)
            ((fun _ _ => 0 : ℕ → Ω' → LoopArg L n → ℂ) (j + 1) ω') a) ω).re) (0 : ℝ≥0) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (u k : ℂ)
            ((fun _ _ => 0 : ℕ → Ω' → LoopArg L n → ℂ) (j + 1) ω') a) ω).im) (0 : ℝ≥0) μ := by
  intro _ j _
  simp [Uker_zero_vec, Set.indicator]

/-- `Y = 0` witness for all five (T2) hypotheses, with `e ≡ 0`. -/
example {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ'} (L : ℕ) [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (u : ℕ → ℝ) (t : ℝ)
    (K : ℕ) (τ : Ω' → ℕ) :
    let Y : ℕ → Ω' → LoopArg L n → ℂ := fun _ _ => 0
    (∀ b : LoopArg L n, ∀ j < K,
      μ[fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).re | ℱ j] =ᵐ[μ] 0) ∧
    (∀ b : LoopArg L n, ∀ j < K,
      μ[fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).im | ℱ j] =ᵐ[μ] 0) ∧
    (∀ b : LoopArg L n, ∀ j < K,
      MemLp (fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).re) 2 μ) ∧
    (∀ b : LoopArg L n, ∀ j < K,
      MemLp (fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).im) 2 μ) ∧
    (∀ b : LoopArg L n, ∀ j < K,
      ∫ ω, ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).re ^ 2 ∂μ
        + ∫ ω, ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).im ^ 2 ∂μ
        ≤ (fun _ => (0 : ℝ)) j) := by
  intro Y
  have hzero : ∀ b : LoopArg L n, ∀ j : ℕ, (fun ω => {ω' | j < τ ω'}.indicator
      (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω) = fun _ => (0 : ℂ) := by
    intro b j
    funext ω
    simp [Y, Uker_zero_vec, Set.indicator]
  refine ⟨fun b j _ => ?_, fun b j _ => ?_, fun b j _ => ?_, fun b j _ => ?_, fun b j _ => ?_⟩
  · have h : (fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).re) = 0 := by
      funext ω; simp [congrFun (hzero b j) ω]
    rw [h, condExp_zero]
  · have h : (fun ω => ({ω' | j < τ ω'}.indicator
        (fun ω' => Uker L ξ (u (j + 1) : ℂ) (t : ℂ) (Y (j + 1) ω') b) ω).im) = 0 := by
      funext ω; simp [congrFun (hzero b j) ω]
    rw [h, condExp_zero]
  · simp only [congrFun (hzero b j), Complex.zero_re]
    exact memLp_const 0
  · simp only [congrFun (hzero b j), Complex.zero_im]
    exact memLp_const 0
  · simp [congrFun (hzero b j)]

/-- For `n = 0` the label type `LoopArg L 0` is a singleton and `Uker` is the identity. -/
private lemma Uker_fin_zero (L : ℕ) [NeZero L] (ξ : Fin 0 → ℂ) (s t : ℂ) (A : LoopArg L 0 → ℂ)
    (a : LoopArg L 0) : Uker L ξ s t A a = A a := by
  rw [Uker_apply, Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  exact congrArg A (Subsingleton.elim _ _)

/-- An (unconditionally) sub-Gaussian variable is conditionally sub-Gaussian given `⊥`. -/
private lemma hasCondSubgaussianMGF_bot {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    [StandardBorelSpace Ω'] {μ : Measure Ω'} [IsProbabilityMeasure μ] {X : Ω' → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) :
    HasCondSubgaussianMGF ⊥ bot_le X c μ := by
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro t
    rw [condExpKernel_comp_trim]
    exact h.integrable_exp_mul t
  · intro q
    have hb := condExp_ae_eq_trim_integral_condExpKernel (μ := μ) (m := ⊥) bot_le
      (h.integrable_exp_mul q)
    filter_upwards [hb] with ω' hω'
    rw [mgf, ← hω', condExp_bot]
    exact h.mgf_le q

/-- The standard Gaussian is sub-Gaussian with parameter `1`. -/
private lemma hasSubgaussianMGF_id_gaussianReal :
    HasSubgaussianMGF (fun x : ℝ => x) 1 (gaussianReal 0 1) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
    rw [show (fun x : ℝ => x) = id from rfl, this]
    simp

private lemma hasSubgaussianMGF_zero_of_prob {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} [IsProbabilityMeasure μ] (c : ℝ≥0) :
    HasSubgaussianMGF (fun _ : Ω' => (0 : ℝ)) c μ where
  integrable_exp_mul t := by simp
  mgf_le t := by
    simp only [mgf, mul_zero, Real.exp_zero, integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact Real.one_le_exp (by positivity)

/-- Two-step filtration on `ℝ`: trivial at time `0`, Borel afterwards. -/
private def gaussFilt : Filtration ℕ (inferInstance : MeasurableSpace ℝ) where
  seq i := match i with
    | 0 => ⊥
    | _ + 1 => inferInstance
  mono' i j hij := by
    rcases i with _ | i
    · exact bot_le
    · rcases j with _ | j
      · omega
      · exact le_rfl
  le' i := by
    rcases i with _ | i
    · exact bot_le
    · exact le_rfl

/-- Gaussian increments: `Z 0 = 0`, `Z (i+1) ω = ω` (a constant vector over the one label). -/
private noncomputable def gaussZ (L : ℕ) : ℕ → ℝ → LoopArg L 0 → ℂ :=
  fun i ω _ => if i = 0 then 0 else (ω : ℂ)

private lemma gaussZ_meas (L : ℕ) : ∀ i, StronglyMeasurable[gaussFilt i] (gaussZ L i) := by
  intro i
  rcases i with _ | i
  · change StronglyMeasurable[gaussFilt 0] (fun (_ : ℝ) (_ : LoopArg L 0) => (0 : ℂ))
    exact stronglyMeasurable_const
  · change StronglyMeasurable[(inferInstance : MeasurableSpace ℝ)]
      (fun (ω : ℝ) (_ : LoopArg L 0) => (ω : ℂ))
    exact (by fun_prop : Measurable fun (ω : ℝ) (_ : LoopArg L 0) => (ω : ℂ)).stronglyMeasurable

private lemma gauss_edge (L : ℕ) [NeZero L] (ξ : Fin 0 → ℂ) (s t' : ℂ) (a : LoopArg L 0) (j : ℕ)
    (hj : j < 1) (ω : ℝ) :
    {_ω' : ℝ | j < 1}.indicator (fun ω' => Uker L ξ s t' (gaussZ L (j + 1) ω') a) ω
      = (ω : ℂ) := by
  simp [Set.indicator, hj, Uker_fin_zero, gaussZ]

/-- The Gaussian stopped increment (`τ ≡ 1`, `j = 0`) is conditionally sub-Gaussian given
`ℱ 0 = ⊥` with parameter `1` (real part: standard Gaussian; imaginary part: `0`). -/
private lemma gauss_hsubG (L : ℕ) [NeZero L] (ξ : Fin 0 → ℂ) (s t' : ℂ) (a : LoopArg L 0)
    (j : ℕ) (hj : j < 1) :
    HasCondSubgaussianMGF (gaussFilt j) (gaussFilt.le j)
        (fun ω => ({_ω' : ℝ | j < 1}.indicator
          (fun ω' => Uker L ξ s t' (gaussZ L (j + 1) ω') a) ω).re) 1 (gaussianReal 0 1) ∧
      HasCondSubgaussianMGF (gaussFilt j) (gaussFilt.le j)
        (fun ω => ({_ω' : ℝ | j < 1}.indicator
          (fun ω' => Uker L ξ s t' (gaussZ L (j + 1) ω') a) ω).im) 1 (gaussianReal 0 1) := by
  obtain rfl : j = 0 := by omega
  simp only [gauss_edge L ξ s t' a 0 hj, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨hasCondSubgaussianMGF_bot hasSubgaussianMGF_id_gaussianReal,
    hasCondSubgaussianMGF_bot (hasSubgaussianMGF_zero_of_prob 1)⟩

/-- Nonzero Gaussian witness for (T1′): its conclusion is the Gaussian tail
`γ{x ≤ |ω|} ≤ 4 e^{-x²/4}`. -/
example (x : ℝ) (hx : 0 ≤ x) :
    (gaussianReal 0 1).real {ω | x ≤ |ω|} ≤ 4 * Real.exp (-x ^ 2 / 4) := by
  have h := stopped_duhamel_azuma_tail_fixed (μ := gaussianReal 0 1) (ℱ := gaussFilt) 3
    (ξ := fun _ => 0) (u := fun _ => 0) (τ := fun _ => 1) (fun _ => MeasurableSet.const _)
    (gaussZ_meas 3) 1 (fun _ => 0) (c := fun _ _ _ => 1)
    (fun j hj => gauss_hsubG 3 _ _ _ _ j hj) hx
  simpa [Uker_fin_zero, gaussZ] using h

/-- Nonzero Gaussian witness for (T1″) with `K = 1`. -/
example (x : ℝ) (hx : 0 < x) :
    (gaussianReal 0 1).real {ω | x ≤ |ω|} ≤ 4 * Real.exp (-x ^ 2 / 4) := by
  have h := stopped_duhamel_azuma_union (μ := gaussianReal 0 1) (ℱ := gaussFilt) 3
    (ξ := fun _ => 0) (u := fun _ => 0) (τ := fun _ => 1) (fun _ => MeasurableSet.const _)
    (gaussZ_meas 3) 1 (c := fun _ _ _ => 1)
    (fun _ hk a j hj => gauss_hsubG 3 _ _ _ a j (by omega)) (x := fun _ _ => x)
    (fun _ _ _ => hx.le) (fun _ => hx)
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (le_trans h (le_of_eq ?_))
  · intro ω hω
    refine ⟨1, le_rfl, fun _ => 0, ?_⟩
    simpa [Uker_fin_zero, gaussZ] using hω
  · simp

/-- Nonzero Gaussian witness for the original sup-norm (T1). -/
example (x : ℝ) (hx : 0 ≤ x) :
    (gaussianReal 0 1).real {ω | x ≤ |ω|} ≤ 4 * Real.exp (-x ^ 2 / 4) := by
  have h := stopped_duhamel_azuma_tail (μ := gaussianReal 0 1) (ℱ := gaussFilt) 3 (by norm_num)
    (ξ := fun _ => 0) (fun i => i.elim0) (u := fun _ => 0) (t := 0) le_rfl (fun _ => le_rfl)
    (K := 1) rfl (by norm_num) (τ := fun _ => 1) (fun _ => le_rfl)
    (fun _ => MeasurableSet.const _) (gaussZ_meas 3) (c := fun _ => 1)
    (fun b j hj => gauss_hsubG 3 _ _ _ b j hj) hx
  simpa [Uker_fin_zero, gaussZ] using h

private lemma integral_sq_gaussianReal : ∫ ω, ω ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h1 := variance_eq_integral (μ := gaussianReal 0 1) (X := id) measurable_id.aemeasurable
  rw [variance_id_gaussianReal] at h1
  simp only [id, integral_id_gaussianReal, sub_zero, NNReal.coe_one] at h1
  exact h1.symm

/-- Nonzero Gaussian witness for (T2), all five hypotheses with `e ≡ 1`: its conclusion is the
Chebyshev bound `γ{x ≤ |ω|} ≤ 1/x²`. -/
example (x : ℝ) (hx : 0 < x) :
    (gaussianReal 0 1).real {ω | x ≤ |ω|} ≤ 1 / x ^ 2 := by
  have hmeanRe : ∀ b : LoopArg 3 0, ∀ j < 1,
      (gaussianReal 0 1)[fun ω => ({_ω' : ℝ | j < 1}.indicator
        (fun ω' => Uker 3 (fun _ => 0) (((fun _ => (0 : ℝ)) (j + 1) : ℝ) : ℂ) ((0 : ℝ) : ℂ)
          (gaussZ 3 (j + 1) ω') b) ω).re | gaussFilt j] =ᵐ[gaussianReal 0 1] 0 := by
    intro b j hj
    obtain rfl : j = 0 := by omega
    simp only [gauss_edge 3 _ _ _ b 0 hj, Complex.ofReal_re]
    change (gaussianReal 0 1)[fun ω => ω | ⊥] =ᵐ[gaussianReal 0 1] 0
    rw [condExp_bot, integral_id_gaussianReal]
    exact ae_of_all _ fun _ => rfl
  have hmeanIm : ∀ b : LoopArg 3 0, ∀ j < 1,
      (gaussianReal 0 1)[fun ω => ({_ω' : ℝ | j < 1}.indicator
        (fun ω' => Uker 3 (fun _ => 0) (((fun _ => (0 : ℝ)) (j + 1) : ℝ) : ℂ) ((0 : ℝ) : ℂ)
          (gaussZ 3 (j + 1) ω') b) ω).im | gaussFilt j] =ᵐ[gaussianReal 0 1] 0 := by
    intro b j hj
    simp only [gauss_edge 3 _ _ _ b j hj, Complex.ofReal_im]
    rw [show (fun _ : ℝ => (0 : ℝ)) = 0 from rfl, condExp_zero]
  have hmemRe : ∀ b : LoopArg 3 0, ∀ j < 1,
      MemLp (fun ω => ({_ω' : ℝ | j < 1}.indicator
        (fun ω' => Uker 3 (fun _ => 0) (((fun _ => (0 : ℝ)) (j + 1) : ℝ) : ℂ) ((0 : ℝ) : ℂ)
          (gaussZ 3 (j + 1) ω') b) ω).re) 2 (gaussianReal 0 1) := by
    intro b j hj
    simp only [gauss_edge 3 _ _ _ b j hj, Complex.ofReal_re]
    exact memLp_id_gaussianReal' 2 (by norm_num)
  have hmemIm : ∀ b : LoopArg 3 0, ∀ j < 1,
      MemLp (fun ω => ({_ω' : ℝ | j < 1}.indicator
        (fun ω' => Uker 3 (fun _ => 0) (((fun _ => (0 : ℝ)) (j + 1) : ℝ) : ℂ) ((0 : ℝ) : ℂ)
          (gaussZ 3 (j + 1) ω') b) ω).im) 2 (gaussianReal 0 1) := by
    intro b j hj
    simp only [gauss_edge 3 _ _ _ b j hj, Complex.ofReal_im]
    exact memLp_const 0
  have hbound : ∀ b : LoopArg 3 0, ∀ j < 1,
      ∫ ω, ({_ω' : ℝ | j < 1}.indicator
          (fun ω' => Uker 3 (fun _ => 0) (((fun _ => (0 : ℝ)) (j + 1) : ℝ) : ℂ) ((0 : ℝ) : ℂ)
            (gaussZ 3 (j + 1) ω') b) ω).re ^ 2 ∂(gaussianReal 0 1)
        + ∫ ω, ({_ω' : ℝ | j < 1}.indicator
          (fun ω' => Uker 3 (fun _ => 0) (((fun _ => (0 : ℝ)) (j + 1) : ℝ) : ℂ) ((0 : ℝ) : ℂ)
            (gaussZ 3 (j + 1) ω') b) ω).im ^ 2 ∂(gaussianReal 0 1) ≤ (fun _ => (1 : ℝ)) j := by
    intro b j hj
    simp only [gauss_edge 3 _ _ _ b j hj, Complex.ofReal_re, Complex.ofReal_im]
    simp [integral_sq_gaussianReal]
  have h := stopped_duhamel_cheb_tail (μ := gaussianReal 0 1) (ℱ := gaussFilt) 3 (by norm_num)
    (ξ := fun _ => 0) (fun i => i.elim0) (u := fun _ => 0) (t := 0) le_rfl (fun _ => le_rfl)
    (K := 1) rfl (by norm_num) (τ := fun _ => 1) (fun _ => le_rfl)
    (fun _ => MeasurableSet.const _) (gaussZ_meas 3) (e := fun _ => 1)
    hmeanRe hmeanIm hmemRe hmemIm hbound hx
  simpa [Uker_fin_zero, gaussZ] using h

/-- Nondegenerate witness for (T3)'s `hFwd` (audit defect 3): `n = 1`, `ξ = 1` (so `‖ξ‖ = 1` and
`Uker` is not the identity), grid `u j = min j 2 / 4` (`u 1 = 1/4 < u 2 = t = 1/2`), `K = 2`,
`τ ≡ 2`, `R ≡ 1`, `r ≡ 1`. -/
example : ∀ j (ω : Unit), j < (fun _ : Unit => 2) ω → ∀ a : LoopArg 3 1,
    ‖Uker 3 (fun _ => (1 : ℂ)) (((fun j : ℕ => min (j : ℝ) 2 / 4) (j + 1) : ℝ) : ℂ)
      ((1 / 2 : ℝ) : ℂ) ((fun _ _ _ => (1 : ℂ)) j ω) a‖ ≤ 2 ^ 1 * (fun _ => (1 : ℝ)) j :=
  hFwd_of_le_half 3 (by norm_num) (fun _ => by simp) (u := fun j : ℕ => min (j : ℝ) 2 / 4)
    (by simp) (fun j => by gcongr; exact_mod_cast Nat.le_succ j) (K := 2) (by norm_num)
    (by norm_num) (τ := fun _ : Unit => 2) (fun _ => le_rfl) (fun _ _ _ => (1 : ℂ))
    (fun _ => zero_le_one) (fun _ _ _ _ => by simp)

/-- The literal amend form of (T1″) (RHS summed over all `k ≤ K`, including `k = 0`) holds for
**every** set and every choice of data, because the `k = 0` summand equals `4` under
`a / 0 = 0`. This is why `stopped_duhamel_azuma_union` sums over `k ∈ Icc 1 K`. -/
example {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (μ : Measure Ω') [IsProbabilityMeasure μ]
    (S : Set Ω') (L : ℕ) [NeZero L] (n K : ℕ) (c : ℕ → LoopArg L n → ℕ → ℝ≥0)
    (x : ℕ → LoopArg L n → ℝ) :
    μ.real S ≤ ∑ k ∈ range (K + 1), ∑ a : LoopArg L n,
      4 * Real.exp (-(x k a) ^ 2 / (4 * ∑ j ∈ range k, (c k a j : ℝ))) := by
  rw [Finset.sum_range_succ']
  have h0 : ∑ a : LoopArg L n,
      4 * Real.exp (-(x 0 a) ^ 2 / (4 * ∑ j ∈ range 0, (c 0 a j : ℝ))) = 4 * (L : ℝ) ^ n := by
    simp only [Finset.sum_range_zero, mul_zero, div_zero, Real.exp_zero, mul_one,
      Finset.sum_const, Finset.card_univ, card_loopArg_eq, nsmul_eq_mul, Nat.cast_pow]
    ring
  have hrest : 0 ≤ ∑ k ∈ range K, ∑ a : LoopArg L n,
      4 * Real.exp (-(x (k + 1) a) ^ 2 / (4 * ∑ j ∈ range (k + 1), (c (k + 1) a j : ℝ))) := by
    positivity
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ n :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L))
  have hS : μ.real S ≤ 1 := measureReal_le_one
  rw [h0]
  linarith

end Witness

end RBM.Gauss.Grid

#print axioms RBM.Gauss.Grid.stoppedEdge_apply
#print axioms RBM.Gauss.Grid.stopped_duhamel_azuma_tail_fixed
#print axioms RBM.Gauss.Grid.stopped_duhamel_azuma_union
#print axioms RBM.Gauss.Grid.stopped_duhamel_azuma_tail
#print axioms RBM.Gauss.Grid.stopped_duhamel_cheb_tail
#print axioms RBM.Gauss.Grid.stopped_duhamel_det_bound
#print axioms RBM.Gauss.Grid.norm_Uker_fwd_le_of_le_half
#print axioms RBM.Gauss.Grid.hFwd_of_le_half
#print axioms RBM.Gauss.Grid.stopped_duhamel_det_bound_half
