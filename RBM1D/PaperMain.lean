/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.EnergyN.Gauss.Thm221Gauss
import RBM1D.EnergyN.Gauss.Theorems24And25Gauss
import RBM1D.Flow.Theorem26Gauss

/-!
# The paper's main results, Theorems 2.2–2.6, in final Lean form

Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band Matrices*
(`paper/YauYin_RBM1D_Lean_version.pdf`), Theorems 2.2–2.6, for the complex Gaussian block band
model `RBM.Gauss.sample d` (linked to the flow by `RBM.Gauss.transfer_gauss d`).

Each `RBM.Paper.theorem2_k` restates one terminal theorem of the library. Its binders and
conclusion are copied from the terminal, and its proof is the terminal applied to its own binders.
The compiled `rfl` checks below confirm that each statement is the terminal's, unchanged.

| Paper | Lean | Terminal |
|---|---|---|
| Thm 2.2 | `RBM.Paper.theorem2_2` | `RBM.Gauss.delocalization_gauss` |
| Thm 2.3, (2.3), (2.4), trace | `RBM.Paper.theorem2_3` | `localSemicircleLaw_gaussN_of_z` |
| Thm 2.4, (2.6)–(2.9) | `RBM.Paper.theorem2_4` | `RBM.Gauss.quantumDiffusion_gaussN_of_z` |
| Thm 2.5, (2.12)/(2.13) | `RBM.Paper.theorem2_5` | `RBM.Gauss.theorem2_5_gaussN` |
| Thm 2.6, (2.18) | `RBM.Paper.theorem2_6` | `RBM.Gauss.theorem2_6_gauss` |

Common deviations (`docs/PAPER-VS-LEAN.md` §1–§2):
* `d : Dims` carries `W, L` as functions of the Lean index `N`, with `W N * L N ≤ N ≤ 2 W N L N`
  eventually (§2.3), and `c > 0` with `N^{1/2+c} ≤ W N` eventually, which is (2.2).
* Probability bounds are stated for the failure event: `P(fail) ≤ N^{-D}` in place of
  `P(success) ≥ 1 - N^{-D}` (§2.4); the two are equivalent.
* The model is the complex Gaussian band model (§1).

## Hypothesis table

Classes: (S) size or exponent parameter, or its sign/order constraint; (V) the variable the
theorem quantifies over (a spectral-parameter or energy sequence); (Q) the paper's quantifier
domain for that variable; (H) any other hypothesis. The table is backed by the compiled command
`#paper_main_hypothesis_table` below, which classifies the elaborated binders mechanically.

| Theorem | (S) | (V) | (Q) | (H) |
|---|---|---|---|---|
| 2.2 | `d`, `κ`, `hκ`, `τ`, `D`, `hτ`, `hD` | — | — | none |
| 2.3 | `d κ τ hκ hτ τ' D hτ' hD` | `z` | `him_pos him_le_one habs_re him_ge` | none |
| 2.4 | `d κ τ hκ hτ τ' D hτ' hD` | `z` | `him_pos him_le_one habs_re him_ge` | none |
| 2.5 | `d`, `κ`, `τ`, `hκ`, `hτ0`, `hτ` (2.11) | `E` | `hE` | none |
| 2.6 | `d`, `κ`, `hκ` | — | — | `h51 : LSY22' d` |

The only (H) hypothesis is `LSY22' d` in Theorem 2.6: the complex-Hermitian [51, Theorem 2.2]
read at unit density, the sole external input (`docs/PAPER-VS-LEAN.md` §4).
-/

noncomputable section

namespace RBM.Paper

open MeasureTheory Filter Topology RBM RBM.Gauss
open scoped Matrix

/-! ### Theorem 2.2 -/

/-- **Theorem 2.2 (delocalization).** Paper: *fix `c > 0` with `W ≥ N^{1/2+c}` (2.2). For
small `κ, τ > 0` and large `D > 0` there is `N₀` such that for `N ≥ N₀`,
`P(max_k ‖ψ_k‖²_∞ · 1(λ_k ∈ [−2+κ, 2−κ]) ⩽ N^{−1+τ}) ≥ 1 − N^{−D}`.*

Lean form: the probability of the complementary event `∃ (k, x), N^{−1+τ} < |ψ_k(x)|²·1(…)` is
at most `N^{−D}`, eventually in `N`, for every `d`, `κ > 0`, `τ > 0`, `D > 0`.

Deviations (`docs/PAPER-VS-LEAN.md`): `P(fail) ≤ N^{−D}` for `P(success) ≥ 1 − N^{−D}` (§2.4);
`N` is the Lean index with `WL ≤ N ≤ 2WL` (§2.3); eigenvalue labels follow Mathlib (§2.2); the
proof-level differences (§5) change no statement. Unconditional. -/
theorem theorem2_2 (d : Dims) {κ : ℝ} (hκ : 0 < κ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      (band d).P {ω | ∃ p : (band d).Idx N × (band d).Idx N, (N : ℝ) ^ (-1 + τ) <
        ‖((transfer_gauss d).hermitian N ω).eigenvectorBasis p.1 p.2‖ ^ 2 *
          Set.indicator (Set.Icc (-2 + κ) (2 - κ)) (fun _ => (1 : ℝ))
            (((transfer_gauss d).hermitian N ω).eigenvalues p.1)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  RBM.Gauss.delocalization_gauss d hκ hτ hD

/-! ### Theorem 2.3 -/

/-- **Theorem 2.3 (local semicircle law), (2.3), (2.4) and the tracial law.** Paper: *assume
(2.2). For fixed `κ, τ > 0`, large `D`, and `z = E + iη` with `|E| ≤ 2 − κ`, `1 ≥ η ≥ N^{−1+τ}`,
there is `N₀` such that for `N ≥ N₀`:
`P(max_{x,y} |(G − m)_{xy}| ≤ W^τ/(Wℓη)^{1/2}) ≥ 1 − N^{−D}` (2.3),
`P(max_a |W^{−1}Σ_{x∈I_a} G_xx − m| ≤ W^τ/(Wℓη)) ≥ 1 − N^{−D}` (2.4), and
`P(|N^{−1} Tr G − m| ≤ W^τ/(Wℓη)) ≥ 1 − N^{−D}`.*

Lean form: three failure-probability bounds, each eventually in `N`, along any sequence `z` with
`0 < Im z N ≤ 1`, `|Re z N| ≤ 2 − κ` for all `N` and `N^{−1+τ} ≤ Im z N` eventually;
`zScale N z = W·ℓ(z)·Im z` is `Wℓη`.

Deviations (`docs/PAPER-VS-LEAN.md`): sequence form, equivalent to the uniform-in-`z` form by
`RBM.eventually_forall_of_forall_sequences` (§2.8); separate domain exponent `τ` and loss
exponent `τ'` (`τ' = τ` is the paper's form; §2.7); `P(fail) ≤ N^{−D}` (§2.4) and tracial
normalization by `L·W` (§2.3); `N` is the Lean index (§2.3). No energy-slice hypothesis. -/
theorem theorem2_3 (d : Dims) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ)
    {z : ℕ → ℂ} (him_pos : ∀ N, 0 < (z N).im) (him_le_one : ∀ N, (z N).im ≤ 1)
    (habs_re : ∀ N, |(z N).re| ≤ 2 - κ)
    (him_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ ij : (band d).Idx N × (band d).Idx N,
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2) <
        ‖(green ((transfer_gauss d).Hband N ω) (z N) -
            msc (z N) • (1 : Matrix ((band d).Idx N) ((band d).Idx N) ℂ)) ij.1 ij.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ a : ZMod ((band d).L N),
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ <
        ‖((band d).W N : ℂ)⁻¹ * ∑ x : Fin ((band d).W N),
            green ((transfer_gauss d).Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ _u : Unit,
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ <
        ‖(((band d).L N * (band d).W N : ℕ) : ℂ)⁻¹ *
            (green ((transfer_gauss d).Hband N ω) (z N)).trace - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) :=
  RBM.Gauss.localSemicircleLaw_gaussN_of_z d hκ hτ him_pos him_le_one habs_re him_ge hτ' hD

/-! ### Theorem 2.4 -/

/-- **Theorem 2.4 (quantum diffusion), (2.6)–(2.9).** Paper: *under the assumptions of Theorem 2.3,
with `ξ = |m|²` for `G E_a G† E_b` and `ξ = m²` for `G E_a G E_b`,
`P(max_{a,b} |Tr G E_a G^{(†)} E_b − W^{−1}(ξ/(1 − ξS^{(B)}))_{ab}| ≤ W^τ/(Wℓη)²) ≥ 1 − N^{−D}`
(2.6), (2.7), and `max_{a,b} |E Tr G E_a G^{(†)} E_b − W^{−1}(ξ/(1 − ξS^{(B)}))_{ab}| ≤
(Wℓη)^{−3}W^τ` (2.8), (2.9).*

Lean form: two failure-probability bounds with `W^{τ'}·zScale^{−2}` and two expectation bounds with
`W^{τ'}·zScale^{−3}`, each eventually in `N`, where `Θ_L(ξ) = (1 − ξS^{(B)})^{−1}`; the domain
hypotheses on `z` are exactly those of Theorem 2.3.

Deviations (`docs/PAPER-VS-LEAN.md`): sequence form (§2.8); separate `τ`/`τ'` (§2.7);
`P(fail) ≤ N^{−D}` (§2.4); `N` is the Lean index (§2.3). -/
theorem theorem2_4 (d : Dims) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ)
    {z : ℕ → ℂ} (him_pos : ∀ N, 0 < (z N).im) (him_le_one : ∀ N, (z N).im ≤ 1)
    (habs_re : ∀ N, |(z N).re| ≤ 2 - κ)
    (him_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 2 <
        ‖(green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.1 *
            (green ((transfer_gauss d).Hband N ω) (z N))ᴴ *
              Eblk ((band d).L N) ((band d).W N) ab.2).trace -
          ((band d).W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta ((band d).L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 2 <
        ‖(green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.1 *
            green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.2).trace -
          ((band d).W N : ℂ)⁻¹ * msc (z N) ^ 2 *
            Theta ((band d).L N) (msc (z N) ^ 2) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ‖(∫ ω, (green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.1 *
              (green ((transfer_gauss d).Hband N ω) (z N))ᴴ *
                Eblk ((band d).L N) ((band d).W N) ab.2).trace ∂(band d).P) -
          ((band d).W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta ((band d).L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖ ≤
        ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 3) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ‖(∫ ω, (green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.1 *
              green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.2).trace ∂(band d).P) -
          ((band d).W N : ℂ)⁻¹ * msc (z N) ^ 2 *
            Theta ((band d).L N) (msc (z N) ^ 2) ab.1 ab.2‖ ≤
        ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 3) :=
  RBM.Gauss.quantumDiffusion_gaussN_of_z d hκ hτ him_pos him_le_one habs_re him_ge hτ' hD

/-! ### Theorem 2.5 -/

/-- **Theorem 2.5 (generalized QUE), (2.12)/(2.13).** Paper: *assume (2.2) and `0 < τ* < c/2`
(2.11). For small `κ > 0` there is `N₀` such that for `N ≥ N₀`:
`max_{|E|<2−κ} max_a P(max_{λ_i,λ_j∈J_E} |N ψ_i^*(E_a − N^{−1})ψ_j|² ≥ N^{−τ*/6}) ≤ N^{−τ*/6}`
(2.12) and `max_{|E|<2−κ} max_{A⊂Z_L} P(max_{λ_k∈J_E} |Σ_{a∈A}Σ_{x∈I_a}|ψ_k(x)|² − |A|W/N| >
|A|W/N^{1+τ*/12}) ≤ N^{−τ*/6}` (2.13).*

Lean form: `τ` is the paper's `τ*`; for every energy sequence with `|E N| ≤ 2 − κ`, the events
`queEvent212`/`queEvent213` (window `J_E` of radius `queEtaN τ N`) have probability at most
`size^{−τ/6}` eventually in `N`, where `size N = L N · W N` is the paper's `N`.

Deviations (`docs/PAPER-VS-LEAN.md`): `max_{|E|<2−κ}` becomes every sequence with
`|E N| ≤ 2 − κ`, equivalent to the uniform form by `RBM.eventually_forall_of_forall_sequences`
(§2.8, §2.6); in (2.13) `A` is nonempty and the event uses `≥` for `>` (§2.5; the `A = ∅` event is
empty in the paper). -/
theorem theorem2_5 (d : Dims) {κ τ : ℝ} (hκ : 0 < κ) (hτ0 : 0 < τ)
    (hτ : τ < (band d).c / 2) (E : ℕ → ℝ) (hE : ∀ N, |E N| ≤ 2 - κ) :
    (∀ᶠ N : ℕ in atTop, ∀ a : ZMod ((band d).L N),
      (band d).P (queEvent212 ((transfer_gauss d).hermitian N) a (E N)
          ((band d).queEtaN τ N) (((band d).size N : ℝ) ^ (-(τ / 6)))) ≤
        ENNReal.ofReal ((((band d).size N : ℝ)) ^ (-(τ / 6)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset (ZMod ((band d).L N)), A.Nonempty →
      (band d).P (queEvent213 ((transfer_gauss d).hermitian N) A (E N)
          ((band d).queEtaN τ N) τ) ≤
        ENNReal.ofReal ((((band d).size N : ℝ)) ^ (-(τ / 6)))) :=
  RBM.Gauss.theorem2_5_gaussN d hκ hτ0 hτ E hE

/-! ### Theorem 2.6 -/

/-- **Theorem 2.6 (bulk universality), (2.18).** Paper: *for small fixed `κ > 0`, under the
assumptions of Theorem 2.2, for any fixed `k ∈ ℕ`, `|E| ≤ 2 − κ` and smooth compactly supported
`O`: `lim_{N→∞} ∫ dα O(α)(ρ_H^{(k)} − ρ_GUE^{(k)})(E + α/N) = 0`.*

Lean form: `BulkUniversalityMat d κ`, which unfolds (by `Iff.rfl`, checked below) to
`∀ E, |E| ≤ 2 − κ → ∀ k O, IsTestFun O → Tendsto (bandPairing − gueMatPairing) atTop (𝓝 0)`.

Deviations (`docs/PAPER-VS-LEAN.md`): the one extra hypothesis `h51 : LSY22' d` is
[51, Theorem 2.2] in complex-Hermitian (GUE) form at unit density (§4), the sole external input;
the correlation functions are paired without densities (§2.9) and `ρ_GUE` is that of the GUE
matrix (§2.10); Step 1 goes through the local law, rescaling and GUE translation (§5.7);
`WL ≤ N ≤ 2WL` with scaling `α/M` at `M = LW` (§2.3); the proof-level differences (§5) change no
statement. -/
theorem theorem2_6 (d : Dims) (h51 : LSY22' d) {κ : ℝ} (hκ : 0 < κ) :
    BulkUniversalityMat d κ :=
  RBM.Gauss.theorem2_6_gauss d h51 hκ

/-! ### Statement identity with the terminals (`rfl`) -/

example : @theorem2_2 = @RBM.Gauss.delocalization_gauss := rfl
example : @theorem2_3 = @RBM.Gauss.localSemicircleLaw_gaussN_of_z := rfl
example : @theorem2_4 = @RBM.Gauss.quantumDiffusion_gaussN_of_z := rfl
example : @theorem2_5 = @RBM.Gauss.theorem2_5_gaussN := rfl
example : @theorem2_6 = @RBM.Gauss.theorem2_6_gauss := rfl

/-- `BulkUniversalityMat` is the paper's (2.18) quantifier string, by `Iff.rfl`. -/
example (d : Dims) (κ : ℝ) : BulkUniversalityMat d κ ↔
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, RBM.IsTestFun O →
      Tendsto (fun N => bandPairing d N k O E - gueMatPairing d N k O E) atTop (𝓝 0) :=
  Iff.rfl

end RBM.Paper

/-! ### Nondegenerate instances

`d = Dims.exampleGrow` (`W ≈ N^{3/4}`, `L ≈ N^{1/4} → ∞`, `c = 1/8`). Theorem 2.3/2.4 use the
spectral parameter `zStar N = (−1)^N/4 + i·(max N 1)^{−1/4}`: non-constant real part, `Im → 0`,
and `N^{−1/2} ≤ Im zStar N` for `N ≥ 1` (exponent slack `1/4`). -/

namespace RBM.Paper.NonVacuity

open Filter Topology RBM RBM.Gauss

/-- `zStar N = (−1)^N/4 + i·(max N 1)^{−1/4}`. -/
noncomputable def zStar (N : ℕ) : ℂ := ⟨(-1 : ℝ) ^ N / 4, (max (N : ℝ) 1) ^ (-(1 / 4 : ℝ))⟩

theorem zStar_im_pos (N : ℕ) : 0 < (zStar N).im :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _

theorem zStar_im_le_one (N : ℕ) : (zStar N).im ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (le_max_right _ _) (by norm_num)

theorem zStar_abs_re (N : ℕ) : |(zStar N).re| ≤ 2 - (1 / 2 : ℝ) := by
  change |(-1 : ℝ) ^ N / 4| ≤ 2 - 1 / 2
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow]
  norm_num

theorem zStar_im_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + (1 / 2 : ℝ)) ≤ (zStar N).im := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  change (N : ℝ) ^ (-1 + (1 / 2 : ℝ)) ≤ (max (N : ℝ) 1) ^ (-(1 / 4 : ℝ))
  rw [max_eq_left hN']
  exact Real.rpow_le_rpow_of_exponent_le hN' (by norm_num)

theorem zStar_re_nonconst : (zStar 0).re ≠ (zStar 1).re := by
  change (-1 : ℝ) ^ 0 / 4 ≠ (-1 : ℝ) ^ 1 / 4
  norm_num

/-- The domain does not collapse: `Im zStar N → 0`. -/
theorem zStar_im_tendsto : Tendsto (fun N => (zStar N).im) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => max (N : ℝ) 1) atTop atTop :=
    tendsto_atTop_mono (fun N => le_max_left _ _) tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp h1

/-- Theorem 2.2 at `κ = 1`, `τ = 1/2`, `D = 1`. -/
example := RBM.Paper.theorem2_2 Dims.exampleGrow (κ := 1) one_pos (τ := 1 / 2) (D := 1)
  (by norm_num) one_pos

/-- Theorem 2.3 at `κ = τ = 1/2`, `τ' = 1/10`, `D = 5`, `z = zStar`. -/
example := RBM.Paper.theorem2_3 Dims.exampleGrow (κ := 1 / 2) (τ := 1 / 2) (by norm_num)
  (by norm_num) zStar_im_pos zStar_im_le_one zStar_abs_re zStar_im_ge (τ' := 1 / 10) (D := 5)
  (by norm_num) (by norm_num)

/-- Theorem 2.4 at `κ = τ = 1/2`, `τ' = D = 1`, `z = zStar`. -/
example := RBM.Paper.theorem2_4 Dims.exampleGrow (κ := 1 / 2) (τ := 1 / 2) (by norm_num)
  (by norm_num) zStar_im_pos zStar_im_le_one zStar_abs_re zStar_im_ge (τ' := 1) (D := 1)
  one_pos one_pos

/-- Theorem 2.5 at `κ = 1/2`, `τ = 1/32 < c/2 = 1/16`, `E N = (−1)^N/4`. -/
example := RBM.Paper.theorem2_5 Dims.exampleGrow (κ := 1 / 2) (by norm_num)
  RBM.Gauss.NonVacuity.tau_pos RBM.Gauss.NonVacuity.tau_lt_half_c RBM.Gauss.NonVacuity.energy
  RBM.Gauss.NonVacuity.abs_energy_le

section Thm26

variable (h51 : LSY22' Dims.exampleGrow)

include h51 in
/-- Theorem 2.6 at `κ = 1`, `E = 0`, `k = 1`, `O = RBM.Gauss.testBump` (`O 0 = 1`), conditional
on the authorized external input `h51`. -/
example : Tendsto (fun N => bandPairing Dims.exampleGrow N 1 (fun x => RBM.Gauss.testBump x) 0 -
      gueMatPairing Dims.exampleGrow N 1 (fun x => RBM.Gauss.testBump x) 0) atTop (𝓝 0) :=
  RBM.Paper.theorem2_6 Dims.exampleGrow h51 one_pos 0 (by norm_num) 1 _
    RBM.Gauss.testBump_isTestFun

end Thm26

end RBM.Paper.NonVacuity

/-! ### Hypothesis table, compiled

Each binder of the elaborated type is classified: (S) type `Dims` or `ℝ`, or an order relation
between real terms; (V) a sequence `ℕ → ℂ` or `ℕ → ℝ`; (Q) `∀ N : ℕ, r` or `∀ᶠ N in atTop, r`
with `r` an order relation between real terms; (H) anything else. The command fails unless the
(H) list is `[]` for Theorems 2.2–2.5 and `[h51]` for Theorem 2.6. -/

namespace RBM.Paper.HypothesisTable

open Lean Meta Elab Command

def isRealOrder (e : Expr) : Bool :=
  (e.isAppOfArity ``LT.lt 4 || e.isAppOfArity ``LE.le 4) && (e.getArg! 0).isConstOf ``Real

def isNat (e : Expr) : Bool := e.isConstOf ``Nat

def classify (t : Expr) : String :=
  if t.isConstOf ``RBM.Gauss.Dims || t.isConstOf ``Real || isRealOrder t then "S"
  else match t with
    | .forallE _ dom body _ =>
      if isNat dom && !body.hasLooseBVars &&
          (body.isConstOf ``Complex || body.isConstOf ``Real) then "V"
      else if isNat dom && isRealOrder body then "Q"
      else "H"
    | _ =>
      if t.isAppOfArity ``Filter.Eventually 3 then
        match t.getArg! 1 with
        | .lam _ dom body _ => if isNat dom && isRealOrder body then "Q" else "H"
        | _ => "H"
      else "H"

elab "#paper_main_hypothesis_table" : command => do
  let env ← getEnv
  let rows : List (Name × List Name) :=
    [(``RBM.Paper.theorem2_2, []), (``RBM.Paper.theorem2_3, []), (``RBM.Paper.theorem2_4, []),
      (``RBM.Paper.theorem2_5, []), (``RBM.Paper.theorem2_6, [`h51])]
  let mut out : MessageData := m!"Hypothesis table of Theorems 2.2–2.6 (classes S, V, Q, H):"
  for (n, expected) in rows do
    let some ci := env.find? n | throwError m!"{n} not found"
    let rec binders : Expr → List (Name × Expr)
      | .forallE b t body _ => (b, t) :: binders body
      | _ => []
    let bs := binders ci.type
    let cls := bs.map fun (b, t) => (b, classify t)
    let hs := (cls.filter fun p => p.2 == "H").map (·.1)
    let hTypes := (bs.filter fun p => classify p.2 == "H").map (·.2)
    unless hs == expected do
      throwError m!"hypothesis table mismatch at {n}: (H) binders {hs}, expected {expected}"
    out := out ++ m!"\n{n}: {cls}; (H): {hs} : {hTypes}"
  logInfo out

#paper_main_hypothesis_table

end RBM.Paper.HypothesisTable

/-! ### Axioms -/

#print axioms RBM.Paper.theorem2_2
#print axioms RBM.Paper.theorem2_3
#print axioms RBM.Paper.theorem2_4
#print axioms RBM.Paper.theorem2_5
#print axioms RBM.Paper.theorem2_6
#print axioms RBM.Paper.NonVacuity.zStar_im_ge
#print axioms RBM.Paper.NonVacuity.zStar_im_tendsto
