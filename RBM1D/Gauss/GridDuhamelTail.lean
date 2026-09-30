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
# Tail bounds for the stopped discrete Duhamel martingale

Pure probability plus linear algebra on `V := LoopArg L n → ℂ`.  We have a filtration `ℱ`, a
stopping time `τ` (`{j < τ} ∈ ℱ j`), grid times `u : ℕ → ℝ`, edge parameters `ξ`, and write
`U j k := Uker L ξ (u j) (u k)`.

## Main declarations

* `RBM.Gauss.Grid.stopped_duhamel_azuma_tail_label` : the label-weighted Azuma tail for a
  fixed target grid index `k` and label `a`, with deterministic constants `c k a j` that may
  depend on `(k, a)`. It applies `azuma_complex` directly to
  `Σ_{j<k} {j<τ}·(U (j+1) k Z_{j+1}) a`. No inverse kernel, no label union.
* `RBM.Gauss.Grid.stopped_duhamel_azuma_union` : the union over `1 ≤ k ≤ K` and all labels
  with per-`(k,a)` thresholds. The event is over all `k ≤ K`; the `k = 0` event is empty because
  `x 0 a > 0`. See the docstring for why the `k = 0` summand is not on the right-hand side.
* `RBM.Gauss.Grid.stopped_duhamel_cheb_tail` : the sup-norm Chebyshev tail bound for the
  stopped martingale-difference remainder, via the backward kernel.
* `RBM.Gauss.Grid.stopped_duhamel_det_bound` : the pointwise bound for the stopped sum of a
  guarded norm-bounded remainder (for the O(Δ^{3/2}) errors only, not for the drift).

Every public hypothesis states the stopped increment `{ω' | j < τ ω'}.indicator (…) ω` inline;
`stoppedEdge` is a public abbreviation for it, with the unfolding lemma `stoppedEdge_apply`.
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

/-- The backward factorisation: for any real `s`, and `0 ≤ r ≤ t < 1`,
`Uker L ξ s r = Uker L ξ t r ∘ Uker L ξ s t` (from `Uker_comp`). -/
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
(`t' = u k` for `stopped_duhamel_azuma_tail_label`/`stopped_duhamel_azuma_union`, `t' = t = u K`
for `stopped_duhamel_cheb_tail`/`stopped_duhamel_det_bound`). All public hypotheses state this
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

/-- **`stopped_duhamel_azuma_tail_label`**: the label-weighted Azuma tail
for a fixed target grid index `k` and a fixed label `a`. The constants `c k a j` are
deterministic and may depend on the target `(k, a)`. Route: `sum_stopped` rewrites
`(Σ_{j<min k τ} U (j+1) k Z_{j+1}) a` as `Σ_{j<k} {j<τ}·(U (j+1) k Z_{j+1}) a`, and `azuma_complex`
is applied to that sum. No inverse kernel `U⁻¹` and no union over labels.

No hypothesis on `u`, `ξ` or `k` is needed: `Uker` is a total function of its complex times. -/
theorem stopped_duhamel_azuma_tail_label (L : ℕ) [NeZero L] {n : ℕ} {ξ : Fin n → ℂ}
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

/-- **`stopped_duhamel_azuma_union`**: the union of the `stopped_duhamel_azuma_tail_label` events
over
all target grid indices `k ≤ K` and all labels `a`, with a threshold `x k a` for each `(k, a)`. On
`{τ = k}` the `k`-th sum is the linear term of the stopped Duhamel expansion at `u_τ`.

**The `k = 0` summand.** Written as `Σ_{k ≤ K} Σ_a …`, the right-hand side has at `k = 0`
an empty inner constant sum, so under Lean's `a / 0 = 0` that summand equals
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
        exact stopped_duhamel_azuma_tail_label L hτmeas hZ k a (hsubG k hkK a) (hx k hkK a)

end Azuma

section Cheb

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ'}

/-- **`stopped_duhamel_cheb_tail`**: the discrete Chebyshev tail bound for the stopped Duhamel
martingale-difference remainder (sup-norm, via the backward kernel of
`RBM1D/Hierarchy/UkerBackBound.lean`). Route:
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

/-- **`stopped_duhamel_det_bound`**: the pointwise bound for the stopped sum of a guarded
norm-bounded remainder. It is
meant for the O(Δ^{3/2}) errors of the stopped Duhamel expansion only, **not for the drift**.
Pure linear algebra: backward factorisation, then `norm_Uker_back_le` (factor `2^n`).

`hR : ∀ j ω, j < τ ω → ∀ b, ‖R j ω b‖ ≤ r j` is the remainder hypothesis (guarded by `j < τ ω`).
`hFwd` is the forward-kernel bound on the same guarded range. It is a separate hypothesis because
the forward kernel `Uker L ξ (u (j+1)) t` has no uniform max-norm bound as `t‖ξ‖ → 1⁻` (row
bound `1 + (t-s)‖ξ‖(1-t‖ξ‖)⁻¹`). So `hR` does not imply `hFwd` for general `t < 1`, and the
proof uses only `hFwd` and `hr0`: this is a conditional statement. -/
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

end Det

section Witness

end Witness

end RBM.Gauss.Grid

