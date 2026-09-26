/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridJStar
import RBM1D.Gauss.Step2Close
import RBM1D.Hierarchy.Decay
import RBM1D.Hierarchy.LKDecayQuant
import Mathlib.Logic.Equiv.List

/-!
# T1530: Lemma 5.9 at a fixed time (G1c pilot P4a)

Prover model: claude-opus-5-5

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.4, Definition 5.8 (5.74) and Lemma 5.9 (5.75), for the Gaussian model of
`RBM1D/Gauss/Model.lean`.

**Step 0 finding (see `docs/reports/T1530-prove.md`).** The deterministic content of
Definition 5.8 and Lemma 5.9 is already proved and merged in `RBM1D/Hierarchy/Decay.lean` (T59),
for every sign vector `σ` and every loop length, and is reused here directly:
`RBM.Decay.LoopDecay` (Definition 5.8), `RBM.Decay.loopDecay_gloop` (entry decay ⟹ loop decay,
T2), `RBM.Decay.loopDecay_Kgen` (tree-representation decay of `K`, T3), `RBM.Decay.LoopDecay.sub`
(T4). T3 therefore covers every length `≤ m₀`, not only lengths `2, 3`.

**(T5).** High probability of (5.75) for the Gaussian model is **derived** from
`RBM.Gauss.steps12_gauss` (T1524), under its hypothesis list verbatim. The route is:
(2.76) (`Steps12.aprioriDecay`) → `RBM.LKDecayQuant.highProb_flowDec_of_aprioriDecay` (two-point
function `Lre` small beyond `ℓ_v N^{τ/4}`) → `RBM.Lre_eq` (entry bound on `G`) → (T2)/(T3). Both
halves of (5.75), `|L| ≤ W^{-D}` and `|L − K| ≤ W^{-D}`, hold uniformly in `v ∈ [s_N, t_N]`, for
every `m₀`, then every `τ > 0`, `D > 0`. There is also a fixed-time corollary and a grid transfer
on the window `[s, t]`. The paper's probability `1 − O(W^{-D'})` is rendered as `HighProb`
(`1 − O(N^{-D''})` for all `D''`), which is equivalent since `N^{1/2} ≤ W ≤ N` eventually.

## Main results

* `decaySet` — (T1) Definition 5.8, specialised to a matrix `M`'s own `G`-loop `Lval M`.
* `loop_decay_of_entry_decay` — (T2) (5.75), the `L` side, deterministic.
* `K_decay` — (T3) (5.75), the `K` side: every `σ`, every length.
* `lk_decay`, `lkDecaySet` — (T4) (5.75), `L − K`.
* `mem_decaySets_of_lre` — (T5) deterministic core: two-point bound ⟹ both sets.
* `highProb_flow_decaySet`, `highProb_fixedTime_decaySet`, `highProb_grid_decaySet` — (T5) for
  the Gaussian model, from `steps12_gauss`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-! ### (T1) `decaySet`, Definition 5.8 -/

section Decaying

variable (E : ℝ) (N m₀ : ℕ) (u τ D : ℝ)

/-- **(T1)** The fixed-time matrix set of Definition 5.8 (5.74): `M ∈ decaySet E N m₀ u τ D`
iff every `G`-loop of `M` of length `n ≤ m₀` (the paper's fixed `n`, quantified before `τ, D`)
with a pair of labels at cyclic distance `≥ ℓ_u W^τ` has `‖L_{σ,a}(M)‖ ≤ W^{-D}`. -/
def decaySet : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | Decay.LoopDecay (d.L N) m₀ ((band d).ell N u * (d.W N : ℝ) ^ τ) ((d.W N : ℝ) ^ (-D))
        (fun I => gloop (d.L N) (d.W N) M (zt E u) I)}

theorem mem_decaySet_iff (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    M ∈ decaySet d E N m₀ u τ D ↔
      Decay.LoopDecay (d.L N) m₀ ((band d).ell N u * (d.W N : ℝ) ^ τ) ((d.W N : ℝ) ^ (-D))
        (fun I => gloop (d.L N) (d.W N) M (zt E u) I) :=
  Iff.rfl

/-- `LoopIdx (ZMod L)` is countable (an injection into `List Bool × List (ZMod L)`, both
countable), which is all `MeasurableSet.iInter` below needs — no Fintype bound on the loop
length is required for measurability, unlike `RBM.Gauss.Grid.eq273Set`'s fixed-`n` shape. -/
instance instCountableLoopIdx (L : ℕ) [NeZero L] : Countable (LoopIdx (ZMod L)) :=
  Function.Injective.countable (f := fun J : LoopIdx (ZMod L) => (J.σ, J.a))
    (fun _J _J' h => LoopIdx.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- **(T1)** `decaySet` is measurable: rewrite `Decay.LoopDecay`'s `∀ J, WF → length ≤ m₀ →
∀ x ∈ J.a, ∀ y ∈ J.a, …` as an intersection over the countable type `J : LoopIdx (ZMod (d.L N))`
and the Fintype `x y : ZMod (d.L N)` (folding `J.WF`, `J.length ≤ m₀`, `x ∈ J.a`, `y ∈ J.a` and
the distance condition into `if`-conditions that do not depend on `M`), using
`measurable_gloop_matrix` (`GridJStar.lean`, already merged). -/
theorem measurableSet_decaySet : MeasurableSet (decaySet d E N m₀ u τ D) := by
  classical
  have heq : decaySet d E N m₀ u τ D =
      ⋂ J : LoopIdx (ZMod (d.L N)), if J.WF ∧ J.length ≤ m₀ then
        ⋂ x : ZMod (d.L N), ⋂ y : ZMod (d.L N),
          if x ∈ J.a ∧ y ∈ J.a ∧
              (band d).ell N u * (d.W N : ℝ) ^ τ ≤ (zdist (d.L N) (x - y) : ℝ) then
            {M : Matrix (d.Idx N) (d.Idx N) ℂ |
              ‖gloop (d.L N) (d.W N) M (zt E u) J‖ ≤ (d.W N : ℝ) ^ (-D)}
          else Set.univ
        else Set.univ := by
    apply Set.eq_of_subset_of_subset
    · intro M hM
      simp only [Set.mem_iInter]
      intro J
      by_cases hJcond : J.WF ∧ J.length ≤ m₀
      · rw [if_pos hJcond]
        simp only [Set.mem_iInter]
        intro x y
        by_cases hxy : x ∈ J.a ∧ y ∈ J.a ∧
            (band d).ell N u * (d.W N : ℝ) ^ τ ≤ (zdist (d.L N) (x - y) : ℝ)
        · rw [if_pos hxy]
          exact hM J hJcond.1 hJcond.2 x hxy.1 y hxy.2.1 hxy.2.2
        · rw [if_neg hxy]; trivial
      · rw [if_neg hJcond]; trivial
    · intro M hM J hJ hJlen x hx y hy hxy
      simp only [Set.mem_iInter] at hM
      have hh := hM J
      rw [if_pos (⟨hJ, hJlen⟩ : J.WF ∧ J.length ≤ m₀)] at hh
      simp only [Set.mem_iInter] at hh
      have hh2 := hh x y
      rwa [if_pos (⟨hx, hy, hxy⟩ :
        x ∈ J.a ∧ y ∈ J.a ∧ (band d).ell N u * (d.W N : ℝ) ^ τ ≤ (zdist (d.L N) (x - y) : ℝ))]
        at hh2
  rw [heq]
  refine MeasurableSet.iInter fun J => ?_
  split_ifs with hJcond
  · refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
    split_ifs with hxy
    · exact measurableSet_le (measurable_gloop_matrix d N (zt E u) J).norm measurable_const
    · exact MeasurableSet.univ
  · exact MeasurableSet.univ

end Decaying

/-! ### (T2) Entry decay of `G` ⟹ `decaySet` membership (deterministic) -/

section EntryDecay

variable (E : ℝ) (N m₀ : ℕ) (u τ D : ℝ)

/-- **(T2)**, `(5.75)` first part, deterministic (`RBM.Decay.loopDecay_gloop`). If `M` is
Hermitian, `Im z_u ≠ 0`, and the entries of `Gsig M z_u` decay at radius `R` (both charges,
the `(4.2)`-type hypothesis) with error `δG`, and the resulting radius/error
`(2 m₀ R, δG · max(1, |Im z_u|⁻¹)^{m₀})` of `Decay.loopDecay_gloop` is dominated by the target
`(ℓ_u W^τ, W^{-D})` of `decaySet`, then `M ∈ decaySet`.

The extra hypothesis `‖G‖_max ≤ N^C` anticipated by the ticket is unnecessary:
`Decay.loopDecay_gloop` already accounts for the other `n - 2` factors of the loop
deterministically (rotating the loop so the far pair sits at the ends,
`Decay.exists_consecutive_far`), so only the entry-decay hypothesis `hG` is needed; `hR'`,
`hδ'` are the honest rendering of the ticket's "`D' = D + C(m₀)`" bookkeeping (the caller
picks `δG =: W^{-D'}` and discharges these two inequalities). -/
theorem loop_decay_of_entry_decay (M : Matrix (d.Idx N) (d.Idx N) ℂ) (hH : M.IsHermitian)
    (hz : (zt E u).im ≠ 0) {R δG : ℝ} (hR : 0 < R) (hδG : 0 ≤ δG)
    (hG : ∀ (s : Bool) (x y : d.Idx N), R ≤ (zdist (d.L N) (x.1 - y.1) : ℝ) →
      ‖Gsig M (zt E u) s x y‖ ≤ δG)
    (hR' : 2 * (m₀ : ℝ) * R ≤ (band d).ell N u * (d.W N : ℝ) ^ τ)
    (hδ' : δG * max 1 |(zt E u).im|⁻¹ ^ m₀ ≤ (d.W N : ℝ) ^ (-D)) :
    M ∈ decaySet d E N m₀ u τ D :=
  (Decay.loopDecay_gloop (d.L N) hH hz hR hδG hG m₀).mono (d.L N) le_rfl hR' hδ'

end EntryDecay

/-! ### (T3) `K` has Definition 5.8 decay for every `σ` and every length (deterministic) -/

section KDecayT3

variable (E : ℝ) (N m₀ : ℕ) (u : ℝ)

/-- **(T3)**, `(5.75)` `K` part, full generality: `RBM.Band.Kval` (Definition 2.12, the tree
representation) has Definition 5.8 decay for **every** `σ` and **every** length `n ≤ m₀`, via
`RBM.Decay.loopDecay_Kgen` (Lemma 3.4/3.5, `(2.52)`), with gap `δ = 1 - u`
(`RBM.Decay.one_sub_le_norm_one_sub`, `RBM.norm_mSigma`). This resolves the ticket's flagged
risk completely: no restriction to pure `σ`, no restriction to lengths `2, 3`. -/
theorem K_decay (hu0 : 0 ≤ u) (hu1 : u < 1) (hE : |E| ≤ 2) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Decay.LoopDecay (d.L N) m₀ ℓ
      (Decay.cKdecay m₀ (1 - u) * Real.exp (-(cor35Rate (1 - u) * ℓ)))
      (fun I => (band d).Kval E N u I) :=
  Decay.loopDecay_Kgen (d.L N) (d.three_le_L N) (d.W N) (fun s => (norm_mSigma hE s).le) hu0 hu1
    (by linarith) (Decay.one_sub_le_norm_one_sub (fun s => (norm_mSigma hE s).le) hu0) m₀ hℓ

/-- The radius `ℓ_u W^τ` is positive (`ellHat ≥ 1/2`, `W > 0`, any real power of a positive
base is positive), the side condition `K_decay`/`lk_decay` need to instantiate `hℓ`. -/
theorem ell_mul_rpow_pos (hu0 : 0 ≤ u) (hu1 : u < 1) (τ : ℝ) :
    0 < (band d).ell N u * (d.W N : ℝ) ^ τ := by
  have hW : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hξ : ‖(u : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hu0]; exact hu1
  have hell : (1 : ℝ) / 2 ≤ (band d).ell N u := half_le_ellHat (d.L N) (d.three_le_L N) hξ
  have hWτ : (0 : ℝ) < (d.W N : ℝ) ^ τ := Real.rpow_pos_of_pos hW τ
  have hellpos : (0 : ℝ) < (band d).ell N u := by linarith
  exact mul_pos hellpos hWτ

end KDecayT3

/-! ### (T4) `L − K` decays: the combination of (T2) and (T3) -/

section LKDecayT4

variable (E : ℝ) (N m₀ : ℕ) (u τ D : ℝ)

/-- **(T4)**, `(5.75)` `L − K` part: combine (T2)'s raw `Decay.LoopDecay` (of `M`'s `gloop`,
same radius `ℓ_u W^τ`) with (T3) via `Decay.LoopDecay.sub`. -/
theorem lk_decay (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hL : Decay.LoopDecay (d.L N) m₀ ((band d).ell N u * (d.W N : ℝ) ^ τ) ((d.W N : ℝ) ^ (-D))
      (fun I => gloop (d.L N) (d.W N) M (zt E u) I))
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hE : |E| ≤ 2) :
    Decay.LoopDecay (d.L N) m₀ ((band d).ell N u * (d.W N : ℝ) ^ τ)
      ((d.W N : ℝ) ^ (-D) + Decay.cKdecay m₀ (1 - u) *
        Real.exp (-(cor35Rate (1 - u) * ((band d).ell N u * (d.W N : ℝ) ^ τ))))
      (fun I => gloop (d.L N) (d.W N) M (zt E u) I - (band d).Kval E N u I) :=
  hL.sub (d.L N) (K_decay d E N m₀ u hu0 hu1 hE (ell_mul_rpow_pos d N u hu0 hu1 τ))

end LKDecayT4

/-! ### (T5) `HighProb` of (5.75) for the Gaussian model, from `steps12_gauss`

Route (no Lemma 4.1 event is used; `GoodEvent`/`LDERow`/`LDECol` are not needed):
`steps12_gauss` (T1524) → its field `aprioriDecay` ((2.76)) →
`RBM.LKDecayQuant.highProb_flowDec_of_aprioriDecay` (T138: `Lre ≤ |L - K| + |K|` with
`K_decay` at length `2`, so w.h.p. `Lre(H_v, z_v, a, b) ≤ N^{-c}` beyond the radius
`ℓ_v N^{τ/4}`, at every `v ∈ [s_N, t_N]`) → `RBM.Lre_eq` (an entry bound on `G_v`) →
`RBM.Decay.norm_Gsig_apply_le` (both charges) → (T2) for `L` and (T3) for `K`, with the
`N`-dependent entry radius `R_v = ℓ_v N^{τ/4}` and entry error `δ_G = N^{-D'}`,
`D' = D + 2 m₀ + 1`. The factor `cKdecay · exp(…)` of (T3) is absorbed into `W^{-D}` through the
`ℓ̂` dichotomy (`RBM.LKDecayQuant.term2_le`). No lower bound on `1 - u` is assumed: in the
cut-off regime `L √(1 - v) < 1` the target radius exceeds the diameter `L/2` and both decay
statements are vacuous, and otherwise `1 / (1 - v) ≤ L² ≤ N²`. -/

section LKSet

variable (E : ℝ) (N m₀ : ℕ) (u τ D : ℝ)

/-- **(T4) as a fixed-time matrix set**, the `L − K` half of (5.75): every loop of length
`≤ m₀` with a pair of labels at cyclic distance `≥ ℓ_u W^τ` has
`‖L_{σ,a}(M) − K_{u,σ,a}‖ ≤ W^{-D}`. -/
def lkDecaySet : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | Decay.LoopDecay (d.L N) m₀ ((band d).ell N u * (d.W N : ℝ) ^ τ) ((d.W N : ℝ) ^ (-D))
        (fun I => gloop (d.L N) (d.W N) M (zt E u) I - (band d).Kval E N u I)}

/-- `lkDecaySet` is measurable (same argument as `measurableSet_decaySet`; `Kval` is
deterministic). -/
theorem measurableSet_lkDecaySet : MeasurableSet (lkDecaySet d E N m₀ u τ D) := by
  classical
  have heq : lkDecaySet d E N m₀ u τ D =
      ⋂ J : LoopIdx (ZMod (d.L N)), if J.WF ∧ J.length ≤ m₀ then
        ⋂ x : ZMod (d.L N), ⋂ y : ZMod (d.L N),
          if x ∈ J.a ∧ y ∈ J.a ∧
              (band d).ell N u * (d.W N : ℝ) ^ τ ≤ (zdist (d.L N) (x - y) : ℝ) then
            {M : Matrix (d.Idx N) (d.Idx N) ℂ |
              ‖gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J‖ ≤
                (d.W N : ℝ) ^ (-D)}
          else Set.univ
        else Set.univ := by
    apply Set.eq_of_subset_of_subset
    · intro M hM
      simp only [Set.mem_iInter]
      intro J
      by_cases hJcond : J.WF ∧ J.length ≤ m₀
      · rw [if_pos hJcond]
        simp only [Set.mem_iInter]
        intro x y
        by_cases hxy : x ∈ J.a ∧ y ∈ J.a ∧
            (band d).ell N u * (d.W N : ℝ) ^ τ ≤ (zdist (d.L N) (x - y) : ℝ)
        · rw [if_pos hxy]
          exact hM J hJcond.1 hJcond.2 x hxy.1 y hxy.2.1 hxy.2.2
        · rw [if_neg hxy]; trivial
      · rw [if_neg hJcond]; trivial
    · intro M hM J hJ hJlen x hx y hy hxy
      simp only [Set.mem_iInter] at hM
      have hh := hM J
      rw [if_pos (⟨hJ, hJlen⟩ : J.WF ∧ J.length ≤ m₀)] at hh
      simp only [Set.mem_iInter] at hh
      have hh2 := hh x y
      rwa [if_pos (⟨hx, hy, hxy⟩ :
        x ∈ J.a ∧ y ∈ J.a ∧ (band d).ell N u * (d.W N : ℝ) ^ τ ≤ (zdist (d.L N) (x - y) : ℝ))]
        at hh2
  rw [heq]
  refine MeasurableSet.iInter fun J => ?_
  split_ifs with hJcond
  · refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
    split_ifs with hxy
    · exact measurableSet_le
        ((measurable_gloop_matrix d N (zt E u) J).sub_const _).norm measurable_const
    · exact MeasurableSet.univ
  · exact MeasurableSet.univ

end LKSet

section EntryToLoop

open LKDecayQuant

/-- **(T5), deterministic core, at one `N` and one time `v`.** If the `(+,-)` two-point
function `Lre(M, z_v, a, b)` is at most `N^{-(2D' + 2)}` (`D' = D + 2 m₀ + 1`) beyond the
radius `ℓ_v N^{τ/4}`, then `M` lies in both `decaySet` and `lkDecaySet` at `(m₀, v, τ, D)`.
The remaining hypotheses are elementary facts about `N` that hold eventually: `L, W ≤ N`,
`N^{1/2} ≤ W` ((2.2)), and three explicit lower bounds on `N` that depend only on
`(m₀, τ, D, E)`. -/
theorem mem_decaySets_of_lre {E : ℝ} (hE : |E| < 2) {N : ℕ} (m₀ : ℕ) {v τ D : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (hH : M.IsHermitian)
    (hN1 : 1 ≤ N) (hLN : (d.L N : ℝ) ≤ N) (hWN : (d.W N : ℝ) ≤ N)
    (hWlow : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ d.W N)
    (h2m : 2 * (m₀ : ℝ) ≤ (N : ℝ) ^ (τ / 2 / 2)) (h2 : 2 ≤ (N : ℝ) ^ (τ / 2 / 2))
    (hCE : 2 * (max 1 ((mE E).im)⁻¹) ^ m₀ ≤ (N : ℝ))
    (hexp : 2 * cKbound m₀ * (N : ℝ) ^ (((2 * cKexp m₀ : ℕ) : ℝ) + D)
        * Real.exp (-(cZero / 2 * (N : ℝ) ^ (τ / 2 / 2))) ≤ 1)
    (hlre : ∀ a b : ZMod (d.L N),
      (band d).ell N v * (N : ℝ) ^ (τ / 2 / 2) ≤ (zdist (d.L N) (a - b) : ℝ) →
        Lre M (zt E v) a b ≤ (N : ℝ) ^ (-(2 * (D + 2 * (m₀ : ℝ) + 1) + 2))) :
    M ∈ decaySet d E N m₀ v τ D ∧ M ∈ lkDecaySet d E N m₀ v τ D := by
  obtain ⟨D', hD'⟩ : ∃ D' : ℝ, D' = D + 2 * (m₀ : ℝ) + 1 := ⟨_, rfl⟩
  rw [← hD'] at hlre
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hW1 : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
  have hL3 : 3 ≤ d.L N := d.three_le_L N
  have hL0 : (0 : ℝ) < d.L N := by exact_mod_cast (by omega : 0 < d.L N)
  have hWτ1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ := Real.one_le_rpow hW1 hτ.le
  have hell1 : (1 : ℝ) ≤ (band d).ell N v :=
    one_le_ellHat_of_nonneg (by omega : 1 ≤ d.L N) hv0 hv1
  have hell0 : 0 < (band d).ell N v := lt_of_lt_of_le one_pos hell1
  have hWD0 : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  by_cases hcut : 1 ≤ (d.L N : ℝ) * Real.sqrt (1 - v)
  · -- the cut-off in `ℓ̂` is inactive: `ℓ_v √(1 - v) = 1`, `1 / (1 - v) ≤ N²`
    have hellsq : (band d).ell N v * Real.sqrt (1 - v) = 1 :=
      ellHat_mul_sqrt_eq_one (d.L N) hv1 hcut
    have hsqrt0 : 0 < Real.sqrt (1 - v) := Real.sqrt_pos.2 (by linarith)
    have hv0' : (0 : ℝ) < 1 - v := by linarith
    have hv1' : (1 : ℝ) - v ≤ 1 := by linarith
    have hsqN : 1 / (N : ℝ) ≤ Real.sqrt (1 - v) := by
      rw [div_le_iff₀ hN0]; nlinarith
    have hvN : 1 / (1 - v) ≤ (N : ℝ) ^ 2 := by
      have hsq : Real.sqrt (1 - v) * Real.sqrt (1 - v) = 1 - v := Real.mul_self_sqrt (by linarith)
      have hm2 : 1 / (N : ℝ) * (1 / (N : ℝ)) ≤ 1 - v := by
        rw [← hsq]; exact mul_le_mul hsqN hsqN (by positivity) (Real.sqrt_nonneg _)
      rw [div_le_iff₀ hv0']
      calc (1 : ℝ) = (N : ℝ) ^ 2 * (1 / (N : ℝ) * (1 / (N : ℝ))) := by field_simp
        _ ≤ (N : ℝ) ^ 2 * (1 - v) := mul_le_mul_of_nonneg_left hm2 (by positivity)
    -- the spectral parameter
    have hmim : 0 < (mE E).im := mE_im_pos hE
    have hzim : (zt E v).im = (1 - v) * (mE E).im := zt_im E v
    have hz : (zt E v).im ≠ 0 := by rw [hzim]; positivity
    -- powers of `N`
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
    -- the entry bound, from `Lre_eq`
    have hR0 : 0 < (band d).ell N v * A := mul_pos hell0 (Real.rpow_pos_of_pos hN0 _)
    have hgreen : ∀ x y : d.Idx N,
        (band d).ell N v * A ≤ (zdist (d.L N) (x.1 - y.1) : ℝ) →
          ‖green M (zt E v) x y‖ ≤ (N : ℝ) ^ (-D') := by
      intro x y hxy
      have hfar : (band d).ell N v * A ≤ (zdist (d.L N) (y.1 - x.1) : ℝ) := by
        rwa [← zdist_neg, neg_sub]
      have hl := hlre y.1 x.1 hfar
      rw [Lre_eq hH] at hl
      have hterm : ‖green M (zt E v) x y‖ ^ 2 ≤
          ∑ β : Fin (d.W N), ∑ α : Fin (d.W N), ‖green M (zt E v) (x.1, β) (y.1, α)‖ ^ 2 := by
        have h1 : ‖green M (zt E v) x y‖ ^ 2 ≤
            ∑ α : Fin (d.W N), ‖green M (zt E v) (x.1, x.2) (y.1, α)‖ ^ 2 :=
          Finset.single_le_sum (f := fun α => ‖green M (zt E v) (x.1, x.2) (y.1, α)‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ y.2)
        have h2' : ∑ α : Fin (d.W N), ‖green M (zt E v) (x.1, x.2) (y.1, α)‖ ^ 2 ≤
            ∑ β : Fin (d.W N), ∑ α : Fin (d.W N), ‖green M (zt E v) (x.1, β) (y.1, α)‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun β => ∑ α : Fin (d.W N), ‖green M (zt E v) (x.1, β) (y.1, α)‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ x.2)
        exact h1.trans h2'
      have hW2 : (0 : ℝ) < (d.W N : ℝ) ^ 2 := by positivity
      have hS : ∑ β : Fin (d.W N), ∑ α : Fin (d.W N), ‖green M (zt E v) (x.1, β) (y.1, α)‖ ^ 2
          ≤ (d.W N : ℝ) ^ 2 * (N : ℝ) ^ (-(2 * D' + 2)) := by
        rw [inv_pow, ← div_eq_inv_mul, div_le_iff₀ hW2] at hl
        linarith
      have hWN2 : (d.W N : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hW0.le hWN 2
      have hkey : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(2 * D' + 2)) = ((N : ℝ) ^ (-D')) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hN0,
          ← Real.rpow_mul hN0.le]
        congr 1; push_cast; ring
      have hsq : ‖green M (zt E v) x y‖ ^ 2 ≤ ((N : ℝ) ^ (-D')) ^ 2 :=
        calc ‖green M (zt E v) x y‖ ^ 2
            ≤ ∑ β : Fin (d.W N), ∑ α : Fin (d.W N), ‖green M (zt E v) (x.1, β) (y.1, α)‖ ^ 2 :=
              hterm
          _ ≤ (d.W N : ℝ) ^ 2 * (N : ℝ) ^ (-(2 * D' + 2)) := hS
          _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(2 * D' + 2)) :=
              mul_le_mul_of_nonneg_right hWN2 (Real.rpow_nonneg hN0.le _)
          _ = ((N : ℝ) ^ (-D')) ^ 2 := hkey
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg hN0.le _)
        two_ne_zero).1 hsq
    have hG : ∀ (s : Bool) (x y : d.Idx N),
        (band d).ell N v * A ≤ (zdist (d.L N) (x.1 - y.1) : ℝ) →
          ‖Gsig M (zt E v) s x y‖ ≤ (N : ℝ) ^ (-D') :=
      fun s x y hxy => Decay.norm_Gsig_apply_le (d.L N) hH hgreen s x y hxy
    -- (T2): the `L` side
    have hLd := Decay.loopDecay_gloop (d.L N) hH hz hR0 (Real.rpow_nonneg hN0.le _) hG m₀
    have hrad : 2 * (m₀ : ℝ) * ((band d).ell N v * A) ≤
        (band d).ell N v * (d.W N : ℝ) ^ τ := by
      calc 2 * (m₀ : ℝ) * ((band d).ell N v * A) = (band d).ell N v * (2 * (m₀ : ℝ)) * A := by
            ring
        _ ≤ (band d).ell N v * A * A := by gcongr
        _ = (band d).ell N v * (N : ℝ) ^ (τ / 2) := by rw [hNsplit]; ring
        _ ≤ (band d).ell N v * (d.W N : ℝ) ^ τ := by gcongr
    set CE : ℝ := max 1 ((mE E).im)⁻¹ with hCEdef
    have hMC : max 1 |(zt E v).im|⁻¹ ≤ CE * (N : ℝ) ^ 2 := by
      refine max_le ?_ ?_
      · have hCE1 : (1 : ℝ) ≤ CE := le_max_left _ _
        have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hN1)
        nlinarith
      · have habs : |(zt E v).im| = (1 - v) * (mE E).im := by
          rw [hzim, abs_of_pos (by positivity)]
        rw [habs, mul_inv]
        have h1 : (1 - v)⁻¹ ≤ (N : ℝ) ^ 2 := by rw [← one_div]; exact hvN
        have h2' : ((mE E).im)⁻¹ ≤ CE := le_max_right _ _
        calc (1 - v)⁻¹ * ((mE E).im)⁻¹ ≤ (N : ℝ) ^ 2 * CE :=
              mul_le_mul h1 h2' (by positivity) (by positivity)
          _ = CE * (N : ℝ) ^ 2 := by ring
    have hmax0 : 0 ≤ max 1 |(zt E v).im|⁻¹ := le_trans zero_le_one (le_max_left _ _)
    have hpowm : (max 1 |(zt E v).im|⁻¹) ^ m₀ ≤ CE ^ m₀ * ((N : ℝ) ^ 2) ^ m₀ := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hmax0 hMC m₀
    have hNm : (N : ℝ) ^ (-D') * ((N : ℝ) ^ 2) ^ m₀ = (N : ℝ) ^ (-D) * (N : ℝ)⁻¹ := by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hN0, ← Real.rpow_neg_one,
        ← Real.rpow_add hN0, hD']
      congr 1; push_cast; ring
    have hWD : (N : ℝ) ^ (-D) ≤ (d.W N : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
    have hCEN : CE ^ m₀ * (N : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [mul_inv_le_iff₀ hN0]; linarith
    have herrL : (N : ℝ) ^ (-D') * (max 1 |(zt E v).im|⁻¹) ^ m₀ ≤
        1 / 2 * (d.W N : ℝ) ^ (-D) := by
      calc (N : ℝ) ^ (-D') * (max 1 |(zt E v).im|⁻¹) ^ m₀
          ≤ (N : ℝ) ^ (-D') * (CE ^ m₀ * ((N : ℝ) ^ 2) ^ m₀) :=
            mul_le_mul_of_nonneg_left hpowm (Real.rpow_nonneg hN0.le _)
        _ = CE ^ m₀ * ((N : ℝ) ^ (-D') * ((N : ℝ) ^ 2) ^ m₀) := by ring
        _ = CE ^ m₀ * (N : ℝ)⁻¹ * (N : ℝ) ^ (-D) := by rw [hNm]; ring
        _ ≤ 1 / 2 * (N : ℝ) ^ (-D) :=
            mul_le_mul_of_nonneg_right hCEN (Real.rpow_nonneg hN0.le _)
        _ ≤ 1 / 2 * (d.W N : ℝ) ^ (-D) := by gcongr
    have hLdec : Decay.LoopDecay (d.L N) m₀ ((band d).ell N v * (d.W N : ℝ) ^ τ)
        (1 / 2 * (d.W N : ℝ) ^ (-D)) (fun I => gloop (d.L N) (d.W N) M (zt E v) I) :=
      hLd.mono (d.L N) le_rfl hrad herrL
    -- (T3): the `K` side
    have hρ0 : 0 < (band d).ell N v * (d.W N : ℝ) ^ τ := ell_mul_rpow_pos d N v hv0 hv1 τ
    have hKd := K_decay d E N m₀ v hv0 hv1 hE.le hρ0
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
    have hKerr : Decay.cKdecay m₀ (1 - v) *
        Real.exp (-(cor35Rate (1 - v) * ((band d).ell N v * (d.W N : ℝ) ^ τ))) ≤
          1 / 2 * (d.W N : ℝ) ^ (-D) :=
      (term2_le (m := m₀) (τ := τ / 2) hN0 hv0' hv1' hvN hexpo hexp).trans (by gcongr)
    have hKdec := hKd.mono (d.L N) le_rfl le_rfl hKerr
    refine ⟨hLdec.mono (d.L N) le_rfl le_rfl (by linarith), ?_⟩
    exact (hLdec.sub (d.L N) hKdec).mono (d.L N) le_rfl le_rfl (by linarith)
  · -- the cut-off is active: `ℓ_v = L`, and the target radius exceeds the diameter `L/2`
    push Not at hcut
    have hellL : (band d).ell N v = (d.L N : ℝ) := ellHat_eq_L (d.L N) hv1 hcut
    have hhalf : (d.L N : ℝ) / 2 < (band d).ell N v * (d.W N : ℝ) ^ τ := by
      rw [hellL]; nlinarith
    exact ⟨loopDecay_of_half_lt hhalf _, loopDecay_of_half_lt hhalf _⟩

end EntryToLoop

section HighProbT5

open LKDecayQuant

/-- **(T5), flow level: Lemma 5.9 (5.75) for the Gaussian model, uniformly in the time.**
Under `RBM.Gauss.steps12_gauss`'s hypothesis list, verbatim, for every loop-length cap `m₀`
(the paper's `n`) and then every `τ > 0`, `D > 0`: with high probability, at **every**
`v ∈ [s_N, t_N]` the flow `H_v` lies in `decaySet` (`|L| ≤ W^{-D}` beyond `ℓ_v W^τ`) **and** in
`lkDecaySet` (`|L − K| ≤ W^{-D}` beyond `ℓ_v W^τ`), for all loops of length `≤ m₀`. -/
theorem highProb_flow_decaySet {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ}
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (m₀ : ℕ) {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D) :
    HighProb (P d) (fun N => {ω | ∀ v : TimeIcc s t N,
      Hflow d N (v : ℝ) ω ∈ decaySet d E N m₀ (v : ℝ) τ D ∧
        Hflow d N (v : ℝ) ω ∈ lkDecaySet d E N m₀ (v : ℝ) τ D}) := by
  have hE : |E| < 2 := by linarith
  have h12 : Steps12 (sample d) E s t := steps12_gauss d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg
  have hFD := highProb_flowDec_of_aprioriDecay (B := band d) (X := sample d) hE hs0 ht1
    (τ := τ / 2) (by linarith) (c := 2 * (D + 2 * (m₀ : ℝ) + 1) + 2) (by positivity)
    h12.aprioriDecay
  refine hFD.mono ?_
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
  have h2m : ∀ᶠ N : ℕ in atTop, 2 * (m₀ : ℝ) ≤ (N : ℝ) ^ (τ / 2 / 2) := by
    filter_upwards [SumZeroDyn.eventually_const_mul_rpow_le (2 * (m₀ : ℝ))
      (show (0 : ℝ) < τ / 2 / 2 by linarith)] with N hN
    simpa using hN
  have h2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (τ / 2 / 2) := by
    filter_upwards [SumZeroDyn.eventually_const_mul_rpow_le 2
      (show (0 : ℝ) < τ / 2 / 2 by linarith)] with N hN
    simpa using hN
  have hCE : ∀ᶠ N : ℕ in atTop, 2 * (max 1 ((mE E).im)⁻¹) ^ m₀ ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hexp := SumZeroDyn.eventually_exp_small (2 * cKbound m₀)
    (((2 * cKexp m₀ : ℕ) : ℝ) + D) (cZero / 2) (by have := cZero_pos; linarith)
    (show (0 : ℝ) < τ / 2 / 2 by linarith)
  filter_upwards [eventually_ge_atTop 1, eventually_L_le (B := band d), hWN, hWlow, h2m, h2,
    hCE, hexp] with N hN1 hLN hWNN hWlowN h2mN h2N hCEN hexpN
  intro ω hω v
  have hv0 : 0 ≤ (v : ℝ) := le_trans (hs0 N) v.2.1
  have hv1 : (v : ℝ) < 1 := lt_of_le_of_lt v.2.2 (ht1 N)
  exact mem_decaySets_of_lre d hE m₀ hτ hD hv0 hv1 (Hflow d N (v : ℝ) ω)
    ((sample d).hermitian N (v : ℝ) ω) hN1 hLN hWNN hWlowN h2mN h2N hCEN hexpN
    (fun a b hab => hω v a b hab)

/-- **(T5), at one deterministic time `u(N) ∈ [s_N, t_N]`** (the ticket's "fixed time"
form): a specialisation of `highProb_flow_decaySet`. -/
theorem highProb_fixedTime_decaySet {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ}
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (m₀ : ℕ) {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D)
    (u : ℕ → ℝ) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) :
    HighProb (P d) (fun N => {ω |
      Hflow d N (u N) ω ∈ decaySet d E N m₀ (u N) τ D ∧
        Hflow d N (u N) ω ∈ lkDecaySet d E N m₀ (u N) τ D}) :=
  (highProb_flow_decaySet d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg m₀ hτ hD).mono
    (Filter.Eventually.of_forall fun N _ω hω => hω ⟨u N, hsu N, hut N⟩)

/-- **(T5), grid level.** `highProb_flow_decaySet` transferred to the grid on the window
`[s, t]` by `RBM.Gauss.Grid.highProb_grid_of_flow` (T1488/T1507), for a grid with polynomially
many points (the transfer lemma's own hypotheses). -/
theorem highProb_grid_decaySet {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ}
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (m₀ : ℕ) {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D)
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) :
    HighProb (Pg d) (fun N => {ω | ∀ k : Fin (K N + 1),
      H d s t K N k ω ∈ decaySet d E N m₀ (time s t K N k) τ D ∧
        H d s t K N k ω ∈ lkDecaySet d E N m₀ (time s t K N k) τ D}) :=
  highProb_grid_of_flow d s t K hs0 hst hK0 hC0 hKcard
    (fun N v => decaySet d E N m₀ v τ D ∩ lkDecaySet d E N m₀ v τ D)
    (fun N v => (measurableSet_decaySet d E N m₀ v τ D).inter
      (measurableSet_lkDecaySet d E N m₀ v τ D))
    (highProb_flow_decaySet d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg m₀ hτ hD)

end HighProbT5

end RBM.Gauss.Grid

end
