/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Moment

/-!
# Lemma 5.14 from time-sequence bounds, at an `N`-dependent energy

The premises of (5.92) as a predicate, `RBM.Gauss.Lemma514PremisesN`, and three statements at an
`N`-dependent energy `E : ℕ → ℝ`: `Ξ^{(L-K)}` from a bound on `(W ℓ η)^m ‖lkT‖`
(`RBM.Gauss.stochDom_xiLK_of_nonnegN`), `Ξ^{(L-K)}` from bounds along every time sequence and time
continuity (`RBM.Gauss.stochDom_flowXiLK_of_seqN`), and Lemma 5.14 from such bounds
(`RBM.Gauss.lemma514_of_seqN`).

None of the three fixes an energy-dependent constant: `B.scale_pos'` is used pointwise per fixed
`N` inside the tactic blocks, and the generic (`E`-free) engines `unifDomIcc_of_forall_stochDom`,
`unifDomIcc_mul_scale`, `stochDom_timeIcc_of_unifDom_const` are used unchanged.
`Step3.flowXiLK`/`.flowXiL`/`.flowA`/`.Lemma514` carry no fixed `E`-dependent constant either
(plain deterministic families/defs), so they are eta-expanded at `E N`.
-/

namespace RBM.Gauss

open MeasureTheory Filter MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### `Ξ^{(L-K)}` from the loop difference, at `0 ≤ s`, at an `N`-dependent energy -/

section XiLKN

variable {B : Band Ω} (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **`Ξ^{(L-K)}_{u,m} ≺ ζ_u`** from `(W ℓ_u η_u)^m ‖lkT_u‖ ≺ ζ_u`, uniformly in `u ∈ [s, t]`. No
energy-dependent constant is fixed here. -/
theorem stochDom_xiLK_of_nonnegN (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {m : ℕ} {ζ : ∀ N, RBM.TimeIcc s t N → ℝ}
    (h : StochDom B.P (fun N (p : RBM.TimeIcc s t N × LoopData (B.L N) m) ω =>
      B.scale (E N) N p.1 ^ m * ‖SumZeroDyn.lkT X (E N) N p.1 ω p.2.1 p.2.2‖)
      (fun N p _ => ζ N p.1)) :
    StochDom B.P (fun N u ω => Step3.flowXiLK X (E N) s t m N u ω) (fun N u _ => ζ N u) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine (measure_mono fun ω hω => ?_).trans hN
  obtain ⟨u, hu⟩ := hω
  have hA : 0 < B.scale (E N) N u ^ m :=
    pow_pos (B.scale_pos' (hE N) N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))) m
  have hu' : (N : ℝ) ^ τ * ζ N u / B.scale (E N) N u ^ m < X.lkMax (E N) N u ω m := by
    rw [div_lt_iff₀ hA]
    have : Step3.flowXiLK X (E N) s t m N u ω = X.lkMax (E N) N u ω m * B.scale (E N) N u ^ m :=
      rfl
    linarith
  obtain ⟨ld, hld⟩ := exists_lt_of_lt_ciSup hu'
  refine ⟨(u, ld), ?_⟩
  show (N : ℝ) ^ τ * ζ N u < B.scale (E N) N u ^ m * ‖SumZeroDyn.lkT X (E N) N u ω ld.1 ld.2‖
  rw [div_lt_iff₀ hA] at hld
  rw [SumZeroDyn.norm_lkT]
  linarith

end XiLKN

/-! ### The four steps composed, at an `N`-dependent energy -/

section ComposeN

variable {B : Band Ω} (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **`Ξ^{(L-K)}_{u,m} ≺ c`** uniformly in `u ∈ [s, t]`, from the bound
`‖lkT_v‖ ≺ c (W ℓ_v η_v)^{-m}` along every time sequence `v`, the time-Hölder bound `hHol` on a
high-probability event, and polynomially many loop indices. No energy-dependent constant is fixed
here. -/
theorem stochDom_flowXiLK_of_seqN (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {m : ℕ}
    {Cv : ℝ} (hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData (B.L N) m) : ℝ) ≤ (N : ℝ) ^ Cv)
    {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb B.P Ξ)
    {c : ℕ → ℝ} (hc0 : ∀ N, 0 ≤ c N) (hc1 : ∀ᶠ N : ℕ in atTop, 1 ≤ c N)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : LoopData (B.L N) m,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |B.scale (E N) N u ^ m * ‖SumZeroDyn.lkT X (E N) N u ω q.1 q.2‖
            - B.scale (E N) N v ^ m * ‖SumZeroDyn.lkT X (E N) N v ω q.1 q.2‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ γ)
    (hseq : ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
      StochDom B.P
        (fun N (q : LoopData (B.L N) m) ω => ‖SumZeroDyn.lkT X (E N) N (v N) ω q.1 q.2‖)
        (fun N _ _ => c N * (B.scale (E N) N (v N) ^ m)⁻¹)) :
    StochDom B.P (fun N u ω => Step3.flowXiLK X (E N) s t m N u ω) (fun N _ _ => c N) := by
  have hkpos : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), 0 < B.scale (E N) N u ^ m := fun N u hu =>
    pow_pos (B.scale_pos' (hE N) N ((hs0 N).trans hu.1) (hu.2.trans_lt (ht1 N))) m
  have h1 : UnifDomIcc B.P s t
      (fun N u (q : LoopData (B.L N) m) ω => ‖SumZeroDyn.lkT X (E N) N u ω q.1 q.2‖)
      (fun N u _ _ => c N * (B.scale (E N) N u ^ m)⁻¹) :=
    unifDomIcc_of_forall_stochDom hst hseq
  exact stochDom_xiLK_of_nonnegN X hE hs0 ht1 (ζ := fun N _ => c N)
    (stochDom_timeIcc_of_unifDom_const hcard hst
      (fun N => by have h1 := hs0 N; have h2 := ht1 N; linarith) hK hγ hc0 hc1 hΞ hHol
      (unifDomIcc_mul_scale hkpos h1))

end ComposeN

/-! ### `RBM.Step3.Lemma514`, on the moment route, at an `N`-dependent energy -/

section Lemma514N

variable {B : Band Ω} (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **The premises of (5.92)**: `Ξ^{(L)}_{2n+2} ≺ Λ`, and `Φ` bounds `Ξ^{(L-K)}_m` for `m < n`,
`Ξ^{(L-K)}_m Ξ^{(L-K)}_{n-m+2} (W ℓ η)^{-1}` for `2 ≤ m ≤ n`, and `Ξ^{(L)}_{n+1}`. No
energy-dependent constant is fixed here. -/
def Lemma514PremisesN (X : Sample B) (E : ℕ → ℝ) (s t : ℕ → ℝ) (n : ℕ) (Λ Φ : ℕ → ℝ) : Prop :=
  StochDom B.P (fun N u ω => Step3.flowXiL X (E N) s t (2 * n + 2) N u ω) (fun N _ _ => Λ N) ∧
  (∀ m, 1 ≤ m → m < n → StochDom B.P (fun N u ω => Step3.flowXiLK X (E N) s t m N u ω)
    fun N _ _ => Φ N) ∧
  (∀ m, 2 ≤ m → m ≤ n → StochDom B.P
    (fun N u ω => Step3.flowXiLK X (E N) s t m N u ω
      * Step3.flowXiLK X (E N) s t (n - m + 2) N u ω * (Step3.flowA B (E N) s t N u)⁻¹)
    fun N _ _ => Φ N) ∧
  StochDom B.P (fun N u ω => Step3.flowXiL X (E N) s t (n + 1) N u ω) (fun N _ _ => Φ N)

/-- **Lemma 5.14, (5.92), for the flow at loop length `n`**, from the endpoint estimate along every
time sequence, the time-Hölder bound `hHol` and polynomially many loop indices. No
energy-dependent constant is fixed here. -/
theorem lemma514_of_seqN (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {n : ℕ}
    {Cv : ℝ} (hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData (B.L N) n) : ℝ) ≤ (N : ℝ) ^ Cv)
    {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb B.P Ξ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : LoopData (B.L N) n,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |B.scale (E N) N u ^ n * ‖SumZeroDyn.lkT X (E N) N u ω q.1 q.2‖
            - B.scale (E N) N v ^ n * ‖SumZeroDyn.lkT X (E N) N v ω q.1 q.2‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ γ)
    (hseq : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
      Lemma514PremisesN X E s t n Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom B.P
          (fun N (q : LoopData (B.L N) n) ω => ‖SumZeroDyn.lkT X (E N) N (v N) ω q.1 q.2‖)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * (B.scale (E N) N (v N) ^ n)⁻¹)) :
    Step3.Lemma514 B.P (fun m N u ω => Step3.flowXiLK X (E N) s t m N u ω)
      (fun m N u ω => Step3.flowXiL X (E N) s t m N u ω) (fun N u => Step3.flowA B (E N) s t N u)
      n := by
  intro Λ Φ hΛ0 hΦ0 hΛ1 hY hX1 hX2 hY1
  refine stochDom_flowXiLK_of_seqN X hE hs0 hst ht1 hcard hK hγ hΞ
    (c := fun N => Λ N ^ ((1 : ℝ) / 2) + Φ N) (fun N => ?_) ?_ hHol
    (hseq Λ Φ hΛ0 hΦ0 hΛ1 ⟨hY, hX1, hX2, hY1⟩)
  · have h1 : (0 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (hΛ0 N) _
    have := hΦ0 N
    linarith
  · filter_upwards [hΛ1] with N hN
    have h1 : (1 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.one_le_rpow hN (by norm_num)
    have := hΦ0 N
    linarith

end Lemma514N

end RBM.Gauss
