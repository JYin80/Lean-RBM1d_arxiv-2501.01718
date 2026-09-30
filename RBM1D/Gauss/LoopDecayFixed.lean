/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridJStar
import RBM1D.Gauss.Step2Close
import RBM1D.Gauss.Step2Plain
import RBM1D.Hierarchy.Decay
import RBM1D.Hierarchy.LKDecayQuant
import Mathlib.Logic.Equiv.List

/-!
# Lemma 5.9 at a fixed time

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.4, Definition 5.8 (5.74) and Lemma 5.9 (5.75), for the Gaussian model of
`RBM1D/Gauss/Model.lean`.

The deterministic content of Definition 5.8 and Lemma 5.9 is in `RBM1D/Hierarchy/Decay.lean`, for
every sign vector `σ` and every loop length, and is reused here directly: `RBM.Decay.LoopDecay`
(Definition 5.8), `RBM.Decay.loopDecay_gloop` (entry decay ⟹ loop decay),
`RBM.Decay.loopDecay_Kgen` (tree-representation decay of `K`), `RBM.Decay.LoopDecay.sub`.  So
`K_decay` covers every length `≤ m₀`, not only lengths `2, 3`.

**The two-point route.**  The deterministic core `mem_decaySets_of_lre` feeds the high
probability of (5.75): a small `(+,-)` two-point function `Lre` beyond `ℓ_v N^{τ/4}` (the a
priori decay (2.76)) → `RBM.Lre_eq` (entry bound on `G`) → `RBM.Decay.loopDecay_gloop` for `L`
and `K_decay` for `K`.  Both halves of (5.75), `|L| ≤ W^{-D}` and `|L − K| ≤ W^{-D}`, follow at
the given `(m₀, v, τ, D)`.

## Main results

* `decaySet` — Definition 5.8, specialised to a matrix `M`'s own `G`-loop `Lval M`.
* `K_decay` — (5.75), the `K` side: every `σ`, every length.
* `lkDecaySet` — (5.75), `L − K`, as a fixed-time matrix set.
* `mem_decaySets_of_lre` — deterministic core: two-point bound ⟹ both sets.
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

/-- `LoopIdx (ZMod L)` is countable (an injection into `List Bool × List (ZMod L)`, both
countable), which is all `MeasurableSet.iInter` below needs — no Fintype bound on the loop
length is required for measurability, unlike `RBM.Gauss.Grid.eq273Set`'s fixed-`n` shape. -/
instance instCountableLoopIdx (L : ℕ) [NeZero L] : Countable (LoopIdx (ZMod L)) :=
  Function.Injective.countable (f := fun J : LoopIdx (ZMod L) => (J.σ, J.a))
    (fun _J _J' h => LoopIdx.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- `decaySet` is measurable: rewrite `Decay.LoopDecay`'s `∀ J, WF → length ≤ m₀ →
∀ x ∈ J.a, ∀ y ∈ J.a, …` as an intersection over the countable type `J : LoopIdx (ZMod (d.L N))`
and the Fintype `x y : ZMod (d.L N)` (folding `J.WF`, `J.length ≤ m₀`, `x ∈ J.a`, `y ∈ J.a` and
the distance condition into `if`-conditions that do not depend on `M`), using
`measurable_gloop_matrix` (`GridJStar.lean`). -/
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

end EntryDecay

/-! ### (T3) `K` has Definition 5.8 decay for every `σ` and every length (deterministic) -/

section KDecayT3

variable (E : ℝ) (N m₀ : ℕ) (u : ℝ)

/-- **`K_decay`**, `(5.75)` `K` part, full generality: `RBM.Band.Kval` (Definition 2.12, the tree
representation) has Definition 5.8 decay for **every** `σ` and **every** length `n ≤ m₀`, via
`RBM.Decay.loopDecay_Kgen` (Lemma 3.4/3.5, `(2.52)`), with gap `δ = 1 - u`
(`RBM.Decay.one_sub_le_norm_one_sub`, `RBM.norm_mSigma`).  There is no restriction to pure `σ`
and none to lengths `2, 3`. -/
theorem K_decay (hu0 : 0 ≤ u) (hu1 : u < 1) (hE : |E| ≤ 2) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Decay.LoopDecay (d.L N) m₀ ℓ
      (Decay.cKdecay m₀ (1 - u) * Real.exp (-(cor35Rate (1 - u) * ℓ)))
      (fun I => (band d).Kval E N u I) :=
  Decay.loopDecay_Kgen (d.L N) (d.three_le_L N) (d.W N) (fun s => (norm_mSigma hE s).le) hu0 hu1
    (by linarith) (Decay.one_sub_le_norm_one_sub (fun s => (norm_mSigma hE s).le) hu0) m₀ hℓ

/-- The radius `ℓ_u W^τ` is positive (`ellHat ≥ 1/2`, `W > 0`, any real power of a positive
base is positive), the side condition `K_decay` needs to instantiate `hℓ`. -/
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

end LKDecayT4

/-! ### The two-point route to (5.75)

No Lemma 4.1 event is used; `GoodEvent`/`LDERow`/`LDECol` are not needed.  A bound
`Lre(H_v, z_v, a, b) ≤ N^{-c}` beyond the radius `ℓ_v N^{τ/4}` (with `Lre ≤ |L - K| + |K|` and
`K_decay` at length `2`, this is what (2.76) gives) → `RBM.Lre_eq` (an entry bound on `G_v`) →
`RBM.Decay.norm_Gsig_apply_le` (both charges) → `RBM.Decay.loopDecay_gloop` for `L` and
`K_decay` for `K`, with the
`N`-dependent entry radius `R_v = ℓ_v N^{τ/4}` and entry error `δ_G = N^{-D'}`,
`D' = D + 2 m₀ + 1`. The factor `cKdecay · exp(…)` of `K_decay` is absorbed into `W^{-D}` through
the `ℓ̂` dichotomy (`RBM.LKDecayQuant.term2_le`). No lower bound on `1 - u` is assumed: in the
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

end HighProbT5

end RBM.Gauss.Grid

end

