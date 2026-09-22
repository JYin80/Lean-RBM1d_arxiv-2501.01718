/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeRatioBdd
import RBM1D.Gauss.DimsExample
import RBM1D.Hierarchy.Step2

/-!
# The `Sample`/`Hflow` bridge and `J*` vs the soft maximum (T259)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.26)–(5.29) — the two structural joints that stood between route (A′)'s
analytic side (`RBM1D/Gauss/APrimeRatioBdd.lean`, T255) and its moment field
`RBM.Step2Bootstrap.WeightedMoment`.

## 甲 The Ω-bridge: **it is definitional**

`RBM.Step2Bootstrap.WeightedMoment` is quantified over an abstract `(Ω, P)` with
`J : ℕ → ℝ → Ω → ℝ` coming from a `RBM.Sample`, while
`RBM.Gauss.hasDerivAt_integral_Phi` lives on `∫ ω, Φ (Hflow d N s ω) ∂(P d)`.  The two are
the *same* object on the Gaussian model: `RBM.Gauss.sample` is built with
`H := fun N u ω => Hflow d N u ω` and `RBM.Gauss.band` with `P := P d`, so

* `RBM.Gauss.sample_H : (sample d).H N u ω = Hflow d N u ω` is `rfl`,
* `RBM.Gauss.band_P : (band d).P = P d` is `rfl`,
* `RBM.Gauss.sample_Lval` is `rfl`.

Nothing has to be assumed, and no `√u` convention or type wrapper differs.  What was genuinely
missing is the *composite*: the identification of the flow functional `RBM.Step2.lk` — the
numerator of (5.29) — with the **matrix function** `RBM.Gauss.loopObs` that carries the
`RBM.Gauss.BddC2C` regularity, and the generator identity restated in `RBM.Sample` vocabulary.
Both are supplied here (`lk_eq_loopObs_sub`, `hasDerivAt_integral_Phi_sample`).

## 乙 `J*` vs the soft maximum, on the model's index set

`RBM.Step2.jS` is `RBM.Step2.jStar` — a `Finset.sup'` over *all* of `LoopArg L 2`, plus `1`.
`RBM.Step2Bootstrap.le_softMax` / `softMax_le` were only available abstractly.  Here the
comparison is made on the model's own index set, against exactly the ratio family of
`RBM.Gauss.testFun_softW_lkRatio`:

  `(J*_{u,D} − 1)/Θ_N ≤ softMax_{2r} ρ ≤ e · (J*_{u,D} − 1)/Θ_N`,

the right inequality at the calibration `2r ≥ A log N` of
`RBM.Step2Bootstrap.rpow_card_le_exp_one`, the family having `card (LoopArg L 2) = L²`
members.  **The point is the absent `card` factor**: the raw bound is
`card^{1/(2r)} = L^{1/r}`, and it is the logarithmic order alone that turns it into the
constant `e`.

## Main results

* `RBM.Gauss.lk_eq_loopObs_sub`, `RBM.Gauss.norm_lk_eq` — 甲, the composite bridge: the flow's
  `(L−K)_{u,(+,−),a}` is `loopObs − Kval` evaluated at `Hflow d N u ω`.
* `RBM.Gauss.hasDerivAt_integral_Phi_sample` — 甲, the generator identity in `RBM.Sample`
  vocabulary (`(sample d).H`, `(band d).P`).
* `RBM.Gauss.card_loopArg_two` — `card (LoopArg L 2) = L²`.
* `RBM.Gauss.jStar_le_softMax`, `RBM.Gauss.softMax_le_jStar`,
  `RBM.Gauss.softMax_le_exp_one_mul_jStar`, `RBM.Gauss.jStar_softMax_two_sided` — 乙, abstract
  in `f`, with the `card` factor calibrated away.
* `RBM.Gauss.jS_le_softMax_lkRatio`, `RBM.Gauss.softMax_lkRatio_le_exp_one_mul_jS` — 乙 on the
  Gaussian model's own `RBM.Step2.jS`.
* `RBM.Gauss.abs_cutTrunc_jS_pow_le` — the shape handoff: the integrand of
  `RBM.Step2Bootstrap.WeightedMoment` is pointwise dominated by the *smooth* soft-max object.
* `RBM.Gauss.testFun_softW_jS`, `RBM.Gauss.hasDerivAt_integral_softW_jS` — the two joined: the
  soft-max weight built on **the model's (5.29) family** is a `RBM.Gauss.TestFun`, and the
  generator identity holds for it on `(band d).P`.
* `RBM.Gauss.sat_testFun_softW_jS` — a compiled satisfiability witness on
  `RBM.Gauss.Dims.exampleGrow`.

## What this does **not** do

The seventh step of `RBM.Step2Bootstrap.weightedMoment_of_stepBound` — the near/far estimate of
(5.39)–(5.47) — is untouched.  T230 and T255 both declined to endorse its two exponents; this
file does not supply them and does not depend on them.
-/

namespace RBM

open Cutoff MomentDuhamelCut MeasureTheory Filter

open scoped Matrix.Norms.L2Operator

namespace Gauss

open Matrix Step2Bootstrap

/-! ### 1. 甲 — the Ω-bridge, as a composite -/

section Bridge

variable (d : Dims) (E : ℝ) (N : ℕ) (u : ℝ)

/-- **The `RBM.Sample` integral of the moment route *is* the Gaussian integral.**  Both sides
are literally the same term; the lemma exists so that downstream files can rewrite in the
direction they need without unfolding `RBM.Gauss.band`. -/
theorem integral_sample_H_eq (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) :
    ∫ ω, Φ ((sample d).H N u ω) ∂(band d).P = ∫ ω, Φ (Hflow d N u ω) ∂(P d) := rfl

/-- **⭐ The composite Ω-bridge.**  The numerator of (5.29) along the flow,
`(L − K)_{u,(+,−),a}`, is the *matrix function* `RBM.Gauss.loopObs` minus the deterministic
primitive `K`, evaluated at `H_u = Hflow d N u ω`.  This is the identification route (A′)
needs: the left side is what `RBM.Step2.jS` and hence
`RBM.Step2Bootstrap.WeightedMoment` are built from, the right side is what carries the
`RBM.Gauss.BddC2C` regularity of `RBM.Gauss.bddC2C_loopObs_sub`. -/
theorem lk_eq_loopObs_sub (ω : Ω d) (a : LoopArg (d.L N) 2) :
    Step2.lk (sample d) E N u ω a
      = loopObs d N (zt E u) (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))
            (Hflow d N u ω)
        - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) := by
  rw [loopObs_Hflow]; rfl

/-- The norm form of `RBM.Gauss.lk_eq_loopObs_sub`. -/
theorem norm_lk_eq (ω : Ω d) (a : LoopArg (d.L N) 2) :
    ‖Step2.lk (sample d) E N u ω a‖
      = ‖loopObs d N (zt E u) (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))
            (Hflow d N u ω)
          - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖ := by
  rw [lk_eq_loopObs_sub]

variable {d N u}

/-- **⭐ 甲, second deliverable: the generator identity in `RBM.Sample` vocabulary.**
`RBM.Gauss.hasDerivAt_integral_Phi` restated on `(sample d).H` and `(band d).P`, which is the
form `RBM.Step2Bootstrap.WeightedMoment` (quantified over an abstract `(Ω, P)` and a
`RBM.Sample`) can consume.  It is the same theorem: the bridge is definitional. -/
theorem hasDerivAt_integral_Phi_sample {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hst : MatrixStein d) (h : TestFun d N Φ) (hu : 0 < u) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ ((sample d).H N s ω) ∂(band d).P)
      ((1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
        ∫ ω, coordD2 d N Φ ((sample d).H N u ω) q ∂(band d).P) u :=
  hasDerivAt_integral_Phi hst h hu

end Bridge

/-! ### 2. 乙 — `J*` against the soft maximum, abstractly -/

section JStar

open Step2

variable {L : ℕ} [NeZero L] {f : LoopArg L 2 → ℝ} {W ℓu ηu D ΘN : ℝ} {r : ℕ}

/-- The model's index set has `L²` members.  This is the `card` that
`RBM.Step2Bootstrap.softMax_le` pays and `RBM.Step2Bootstrap.rpow_card_le_exp_one` removes. -/
theorem card_loopArg_two : (Finset.univ : Finset (LoopArg L 2)).card = L ^ 2 := by
  simp [LoopArg, ZMod.card]

/-- `J* − 1` is the `Finset.sup'` of (5.29). -/
theorem jStar_sub_one :
    jStar L f W ℓu ηu D - 1
      = Finset.univ.sup' Finset.univ_nonempty
          fun a => f a / tailT W ℓu ηu D (zdist L (a 0 - a 1)) := by
  rw [jStar]; ring

theorem jStar_sub_one_nonneg (hW : 0 < W) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ jStar L f W ℓu ηu D - 1 := by
  rw [jStar_sub_one]
  refine le_trans ?_ (Finset.le_sup'
    (fun a : LoopArg L 2 => f a / tailT W ℓu ηu D (zdist L (a 0 - a 1)))
    (Finset.mem_univ (0 : LoopArg L 2)))
  exact div_nonneg (hf _) (tailT_pos hW _).le

/-- **⭐ The soft maximum dominates `J*`, with no loss.**  `Θ_N · softMax_{2r} ρ + 1 ≥ J*`,
where `ρ` is the ratio family of `RBM.Gauss.testFun_softW_lkRatio` (denominator
`Θ_N · T_{u,D}`).  This is `RBM.Step2Bootstrap.le_softMax` transported to the model's index
set and through the `Θ_N` normalization. -/
theorem jStar_le_softMax (hW : 0 < W) (hΘN : 0 < ΘN) (hr : 1 ≤ r) :
    jStar L f W ℓu ηu D
      ≤ ΘN * softMax r (Finset.univ : Finset (LoopArg L 2))
          (fun a => f a / (ΘN * tailT W ℓu ηu D (zdist L (a 0 - a 1)))) + 1 := by
  have key : ∀ a : LoopArg L 2,
      f a / tailT W ℓu ηu D (zdist L (a 0 - a 1))
        ≤ ΘN * softMax r (Finset.univ : Finset (LoopArg L 2))
            (fun b => f b / (ΘN * tailT W ℓu ηu D (zdist L (b 0 - b 1)))) := by
    intro a
    have hT : (0 : ℝ) < tailT W ℓu ηu D (zdist L (a 0 - a 1)) := tailT_pos hW _
    have he : f a / tailT W ℓu ηu D (zdist L (a 0 - a 1))
        = ΘN * (f a / (ΘN * tailT W ℓu ηu D (zdist L (a 0 - a 1)))) := by
      field_simp
    rw [he]
    refine mul_le_mul_of_nonneg_left ?_ hΘN.le
    exact le_trans (le_abs_self _)
      (le_softMax (r := r) (S := (Finset.univ : Finset (LoopArg L 2)))
        (ρ := fun b => f b / (ΘN * tailT W ℓu ηu D (zdist L (b 0 - b 1))))
        hr (Finset.mem_univ a))
  have hsup : (Finset.univ.sup' Finset.univ_nonempty
      fun a => f a / tailT W ℓu ηu D (zdist L (a 0 - a 1)))
      ≤ ΘN * softMax r (Finset.univ : Finset (LoopArg L 2))
          (fun b => f b / (ΘN * tailT W ℓu ηu D (zdist L (b 0 - b 1)))) :=
    Finset.sup'_le _ _ fun a _ => key a
  have h2 : jStar L f W ℓu ηu D - 1
      ≤ ΘN * softMax r (Finset.univ : Finset (LoopArg L 2))
          (fun b => f b / (ΘN * tailT W ℓu ηu D (zdist L (b 0 - b 1)))) := by
    rw [jStar_sub_one]; exact hsup
  linarith

/-- **The soft maximum is `J*` up to `card^{1/(2r)} = L^{1/r}`.**  The honest, uncalibrated
direction; `RBM.Gauss.softMax_le_exp_one_mul_jStar` removes the factor. -/
theorem softMax_le_jStar (hW : 0 < W) (hΘN : 0 < ΘN) (hf : ∀ a, 0 ≤ f a) (hr : 1 ≤ r) :
    softMax r (Finset.univ : Finset (LoopArg L 2))
        (fun a => f a / (ΘN * tailT W ℓu ηu D (zdist L (a 0 - a 1))))
      ≤ ((L : ℝ) ^ 2) ^ ((1 : ℝ) / (2 * (r : ℝ)))
          * ((jStar L f W ℓu ηu D - 1) / ΘN) := by
  have hM0 : 0 ≤ (jStar L f W ℓu ηu D - 1) / ΘN :=
    div_nonneg (jStar_sub_one_nonneg hW hf) hΘN.le
  have hb : ∀ a ∈ (Finset.univ : Finset (LoopArg L 2)),
      |f a / (ΘN * tailT W ℓu ηu D (zdist L (a 0 - a 1)))|
        ≤ (jStar L f W ℓu ηu D - 1) / ΘN := by
    intro a _
    have hT : (0 : ℝ) < tailT W ℓu ηu D (zdist L (a 0 - a 1)) := tailT_pos hW _
    have hnn : 0 ≤ f a / (ΘN * tailT W ℓu ηu D (zdist L (a 0 - a 1))) :=
      div_nonneg (hf a) (by positivity)
    have hle : f a / tailT W ℓu ηu D (zdist L (a 0 - a 1)) ≤ jStar L f W ℓu ηu D - 1 := by
      rw [jStar_sub_one]
      exact Finset.le_sup' (fun b : LoopArg L 2 => f b / tailT W ℓu ηu D (zdist L (b 0 - b 1)))
        (Finset.mem_univ a)
    have heq : f a / (ΘN * tailT W ℓu ηu D (zdist L (a 0 - a 1)))
        = (f a / tailT W ℓu ηu D (zdist L (a 0 - a 1))) / ΘN := by
      rw [div_div, mul_comm]
    rw [abs_of_nonneg hnn, heq]
    gcongr
  have h := softMax_le (ι := LoopArg L 2) (r := r) hr (S := Finset.univ)
    (ρ := fun a => f a / (ΘN * tailT W ℓu ηu D (zdist L (a 0 - a 1)))) hM0 hb
  have hcard : (((Finset.univ : Finset (LoopArg L 2)).card : ℝ)) = (L : ℝ) ^ 2 := by
    rw [card_loopArg_two]; push_cast; ring
  rwa [hcard] at h

/-- **⭐⭐ The `card` factor is a constant at `2r ≍ log N`.**  With `L² ≤ N^A` and
`2r ≥ A log N`, `RBM.Step2Bootstrap.rpow_card_le_exp_one` turns `L^{1/r}` into `e`.  This is
why the soft maximum is used at all: what it buys is **not** a factor `Λ`, it is the *absence*
of `card`. -/
theorem softMax_le_exp_one_mul_jStar {A : ℝ} {n : ℕ} (hW : 0 < W) (hΘN : 0 < ΘN)
    (hf : ∀ a, 0 ≤ f a) (hr : 1 ≤ r) (hn : 2 ≤ n) (hA : 0 < A)
    (hcard : ((L : ℝ)) ^ 2 ≤ (n : ℝ) ^ A) (hq : A * Real.log n ≤ 2 * (r : ℝ)) :
    softMax r (Finset.univ : Finset (LoopArg L 2))
        (fun a => f a / (ΘN * tailT W ℓu ηu D (zdist L (a 0 - a 1))))
      ≤ Real.exp 1 * ((jStar L f W ℓu ηu D - 1) / ΘN) := by
  have hL0 : (0 : ℝ) < (L : ℝ) ^ 2 := by
    have : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
    positivity
  have hexp : ((L : ℝ) ^ 2) ^ ((1 : ℝ) / (2 * (r : ℝ))) ≤ Real.exp 1 :=
    rpow_card_le_exp_one hL0 hn hcard hA hq
  have hM0 : 0 ≤ (jStar L f W ℓu ηu D - 1) / ΘN :=
    div_nonneg (jStar_sub_one_nonneg hW hf) hΘN.le
  exact (softMax_le_jStar hW hΘN hf hr).trans (mul_le_mul_of_nonneg_right hexp hM0)

/-- **⭐⭐ 乙, the two-sided comparison on the model's index set.**  Both bounds at once:
the soft maximum of the `Θ_N`-normalized ratio family of (5.29) is `(J* − 1)/Θ_N` up to the
constant `e`. -/
theorem jStar_softMax_two_sided {A : ℝ} {n : ℕ} (hW : 0 < W) (hΘN : 0 < ΘN)
    (hf : ∀ a, 0 ≤ f a) (hr : 1 ≤ r) (hn : 2 ≤ n) (hA : 0 < A)
    (hcard : ((L : ℝ)) ^ 2 ≤ (n : ℝ) ^ A) (hq : A * Real.log n ≤ 2 * (r : ℝ)) :
    (jStar L f W ℓu ηu D - 1) / ΘN
        ≤ softMax r (Finset.univ : Finset (LoopArg L 2))
          (fun a => f a / (ΘN * tailT W ℓu ηu D (zdist L (a 0 - a 1)))) ∧
      softMax r (Finset.univ : Finset (LoopArg L 2))
          (fun a => f a / (ΘN * tailT W ℓu ηu D (zdist L (a 0 - a 1))))
        ≤ Real.exp 1 * ((jStar L f W ℓu ηu D - 1) / ΘN) := by
  refine ⟨?_, softMax_le_exp_one_mul_jStar hW hΘN hf hr hn hA hcard hq⟩
  have h := jStar_le_softMax (L := L) (f := f) (W := W) (ℓu := ℓu) (ηu := ηu) (D := D)
    (ΘN := ΘN) (r := r) hW hΘN hr
  rw [div_le_iff₀ hΘN]
  nlinarith [h]

end JStar

/-! ### 3. 乙 on the Gaussian model: `jS`, and the `TestFun` built on its own family -/

section Model

open Step2

variable {d : Dims} {N : ℕ} {E D u ΘN : ℝ} {r : ℕ}

/-- `RBM.Step2.jS` of the Gaussian sample, written out as a `RBM.Step2.jStar`. -/
theorem jS_eq (ω : Ω d) :
    jS (sample d) E D N u ω
      = jStar (d.L N) (fun a => ‖Step2.lk (sample d) E N u ω a‖)
          ((d.W N : ℝ)) ((band d).ell N u) (etaT E u) D := rfl

/-- **`RBM.Step2.jS` as a `RBM.Step2.jStar` of the *matrix function* family.**  The 甲 bridge
pushed inside (5.29): the numerator is `RBM.Gauss.loopObs − K` at `M = H_u`. -/
theorem jS_eq_loopObs (ω : Ω d) :
    jS (sample d) E D N u ω
      = jStar (d.L N)
          (fun a => ‖loopObs d N (zt E u)
                (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) (Hflow d N u ω)
              - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖)
          ((d.W N : ℝ)) ((band d).ell N u) (etaT E u) D := by
  have hfam : (fun a : LoopArg (d.L N) 2 => ‖Step2.lk (sample d) E N u ω a‖)
      = fun a : LoopArg (d.L N) 2 => ‖loopObs d N (zt E u)
            (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) (Hflow d N u ω)
          - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖ :=
    funext fun a => norm_lk_eq d E N u ω a
  rw [jS_eq, hfam]

/-- **⭐ 乙 on the model, upper half**: `J*_{u,D}` of (5.29) against the soft maximum of the
family `RBM.Gauss.testFun_softW_lkRatio` uses — numerator `RBM.Gauss.loopObs − K`, denominator
`Θ_N · T_{u,D}`. -/
theorem jS_le_softMax_lkRatio (ω : Ω d) (hΘN : 0 < ΘN) (hr : 1 ≤ r) :
    jS (sample d) E D N u ω
      ≤ ΘN * softMax r (Finset.univ : Finset (LoopArg (d.L N) 2))
          (fun a => ‖loopObs d N (zt E u)
                (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) (Hflow d N u ω)
              - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖
            / (ΘN * tailT ((d.W N : ℝ)) ((band d).ell N u) (etaT E u) D
                ((zdist (d.L N) (a 0 - a 1) : ℝ)))) + 1 := by
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have h := jStar_le_softMax (L := d.L N)
    (f := fun a => ‖loopObs d N (zt E u)
          (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) (Hflow d N u ω)
        - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖)
    (W := (d.W N : ℝ)) (ℓu := (band d).ell N u) (ηu := etaT E u) (D := D) (ΘN := ΘN) (r := r)
    hW hΘN hr
  rw [jS_eq_loopObs]
  exact h

/-- **⭐⭐ The integrand of `RBM.Step2Bootstrap.WeightedMoment` is dominated, pointwise in `ω`
and at every truncation level, by the *smooth* soft-max object.**

`WeightedMoment`'s integrand is `W · |χ(J/θ)·J|^{2p}` with `J = RBM.Step2.jS`, a
`Finset.sup'` — nothing the generator identity can be applied to.  Composing
`RBM.MomentDuhamelCut.cutTrunc_le_self` with `RBM.Gauss.jS_le_softMax_lkRatio` replaces it by
`(Θ_N · softMax_{2r} ρ + 1)^{2p}`, and *that* is a `RBM.Gauss.TestFun` factor
(`RBM.Gauss.testFun_softW_jS`).  This is the shape handoff route (A′) needed; what is left is
the estimate of (5.39)–(5.47), not the shape.

The inequality is a deterministic algebraic comparison of two functionals of the *same* `ω`
(a maximum against the `ℓ^{2r}` norm of the same family), not a bound of a random quantity by
a deterministic rate — which is why it may be, and is, stated for every `ω`. -/
theorem abs_cutTrunc_jS_pow_le (ω : Ω d) (hΘN : 0 < ΘN) (hr : 1 ≤ r) (θ : ℝ) (p : ℕ) :
    |cutTrunc θ (jS (sample d) E D N u ω)| ^ (2 * p)
      ≤ (ΘN * softMax r (Finset.univ : Finset (LoopArg (d.L N) 2))
          (fun a => ‖loopObs d N (zt E u)
                (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) (Hflow d N u ω)
              - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖
            / (ΘN * tailT ((d.W N : ℝ)) ((band d).ell N u) (etaT E u) D
                ((zdist (d.L N) (a 0 - a 1) : ℝ)))) + 1) ^ (2 * p) := by
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hJ1 : 0 ≤ jS (sample d) E D N u ω - 1 := by
    rw [jS_eq_loopObs]
    exact jStar_sub_one_nonneg hW fun a => norm_nonneg _
  have hJ0 : 0 ≤ jS (sample d) E D N u ω := by linarith
  have hcut : |cutTrunc θ (jS (sample d) E D N u ω)| ≤ jS (sample d) E D N u ω := by
    rw [abs_of_nonneg (cutTrunc_nonneg hJ0)]
    exact cutTrunc_le_self hJ0
  exact pow_le_pow_left₀ (abs_nonneg _)
    (hcut.trans (jS_le_softMax_lkRatio ω hΘN hr)) (2 * p)

/-- **⭐ 乙 on the model, lower half, calibrated**: the soft maximum of the model's ratio
family is `(J*_{u,D} − 1)/Θ_N` up to `e`, the `card = L²` factor having been absorbed at
`2r ≥ A log n`. -/
theorem softMax_lkRatio_le_exp_one_mul_jS {A : ℝ} {n : ℕ} (ω : Ω d) (hΘN : 0 < ΘN)
    (hr : 1 ≤ r) (hn : 2 ≤ n) (hA : 0 < A) (hcard : ((d.L N : ℝ)) ^ 2 ≤ (n : ℝ) ^ A)
    (hq : A * Real.log n ≤ 2 * (r : ℝ)) :
    softMax r (Finset.univ : Finset (LoopArg (d.L N) 2))
        (fun a => ‖loopObs d N (zt E u)
              (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) (Hflow d N u ω)
            - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖
          / (ΘN * tailT ((d.W N : ℝ)) ((band d).ell N u) (etaT E u) D
              ((zdist (d.L N) (a 0 - a 1) : ℝ))))
      ≤ Real.exp 1 * ((jS (sample d) E D N u ω - 1) / ΘN) := by
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have h := softMax_le_exp_one_mul_jStar (L := d.L N)
    (f := fun a => ‖loopObs d N (zt E u)
          (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) (Hflow d N u ω)
        - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖)
    (W := (d.W N : ℝ)) (ℓu := (band d).ell N u) (ηu := etaT E u) (D := D) (ΘN := ΘN) (r := r)
    (A := A) (n := n) hW hΘN (fun a => norm_nonneg _) hr hn hA hcard hq
  rw [jS_eq_loopObs]
  exact h

/-- **⭐⭐ The `RBM.Gauss.TestFun` of route (A′) on the model's own (5.29) family.**
`RBM.Gauss.testFun_softW_lkRatio` instantiated at the Step-2 charges `σ = (+,−)`, the index set
`LoopArg (L N) 2`, the primitive `K = RBM.Band.Kval` and the distance
`ℓ(a) = ‖a₁ − a₂‖`.  This is the `Φ` whose generator identity
`RBM.Gauss.hasDerivAt_integral_softW_jS` states, and whose restriction to `M = H_u` is the
weight of `RBM.Step2Bootstrap.WeightedMoment` built on `RBM.Step2.jS`. -/
theorem testFun_softW_jS {η Θ : ℝ} (hr : 1 ≤ r) (hΘ : 0 < Θ) (hΘN : 0 < ΘN)
    (hz : (zt E u).im ≠ 0) (hη : 0 < η) (hzη : η ≤ |(zt E u).im|)
    {Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {c₀ c₁ c₂ : ℝ} (hΨ : BddC2C Ψ c₀ c₁ c₂) :
    TestFun d N (fun M => ((softW r (Finset.univ : Finset (LoopArg (d.L N) 2))
        (fun a => ‖loopObs d N (zt E u)
              (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) M
            - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖
          / (ΘN * tailT ((d.W N : ℝ)) ((band d).ell N u) (etaT E u) D
              ((zdist (d.L N) (a 0 - a 1) : ℝ)))) Θ : ℝ) : ℂ) * Ψ M) := by
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  refine testFun_softW_lkRatio (n := 2)
    (Kb := ∑ b : LoopArg (d.L N) 2,
      ‖(band d).Kval E N u (LoopData.idx ((Step2.sigPM, b) : LoopData (d.L N) 2))‖)
    (I := fun a => LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))
    (K := fun a => (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)))
    (ℓ := fun a => ((zdist (d.L N) (a 0 - a 1) : ℝ)))
    hr hΘ hΘN hW hz hη hzη (fun a _ => LoopData.idx_wf _) (fun a _ => LoopData.idx_length _)
    (fun a ha => Finset.single_le_sum (f := fun b : LoopArg (d.L N) 2 =>
      ‖(band d).Kval E N u (LoopData.idx ((Step2.sigPM, b) : LoopData (d.L N) 2))‖)
      (fun b _ => norm_nonneg _) ha) hΨ

/-- **⭐⭐ Step 4 of the (A′) chain on the model's own functional, in `RBM.Sample` vocabulary.**
The generator identity for the soft-max weight built on the (5.29) family of
`RBM.Step2.jS`, written against `(sample d).H` and `(band d).P` — i.e. against exactly the
objects `RBM.Step2Bootstrap.WeightedMoment` is quantified over.  甲 and 乙 joined. -/
theorem hasDerivAt_integral_softW_jS {η Θ : ℝ} (hst : MatrixStein d) (hr : 1 ≤ r) (hΘ : 0 < Θ)
    (hΘN : 0 < ΘN) (hz : (zt E u).im ≠ 0) (hη : 0 < η) (hzη : η ≤ |(zt E u).im|)
    {Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {c₀ c₁ c₂ : ℝ} (hΨ : BddC2C Ψ c₀ c₁ c₂)
    {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun s : ℝ => ∫ ω, (fun M => ((softW r
          (Finset.univ : Finset (LoopArg (d.L N) 2))
          (fun a => ‖loopObs d N (zt E u)
                (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) M
              - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖
            / (ΘN * tailT ((d.W N : ℝ)) ((band d).ell N u) (etaT E u) D
                ((zdist (d.L N) (a 0 - a 1) : ℝ)))) Θ : ℝ) : ℂ) * Ψ M)
        ((sample d).H N s ω) ∂(band d).P)
      ((1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
        ∫ ω, coordD2 d N (fun M => ((softW r
            (Finset.univ : Finset (LoopArg (d.L N) 2))
            (fun a => ‖loopObs d N (zt E u)
                  (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) M
                - (band d).Kval E N u
                    (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖
              / (ΘN * tailT ((d.W N : ℝ)) ((band d).ell N u) (etaT E u) D
                  ((zdist (d.L N) (a 0 - a 1) : ℝ)))) Θ : ℝ) : ℂ) * Ψ M)
          ((sample d).H N v ω) q ∂(band d).P) v :=
  hasDerivAt_integral_Phi_sample hst
    (testFun_softW_jS hr hΘ hΘN hz hη hzη hΨ) hv

end Model

/-! ### 4. A compiled satisfiability witness -/

section Sat

open Step2

/-- Every hypothesis of `RBM.Gauss.testFun_softW_jS` is simultaneously satisfiable on the
concrete model `RBM.Gauss.Dims.exampleGrow`, at `E = 0`, `u = 1/2`, `D = 1`, `Θ_N = Θ = 1`,
`r = 1`, `Ψ ≡ 1`, with `η = η_u = Im z_u > 0`.  The numerator is the genuine `(+,−)` loop of
(5.17) and the index set is the full `LoopArg (L N) 2`, so the weight is not trivial. -/
theorem sat_testFun_softW_jS (N : ℕ) :
    TestFun Dims.exampleGrow N (fun M => ((softW 1
        (Finset.univ : Finset (LoopArg (Dims.exampleGrow.L N) 2))
        (fun a => ‖loopObs Dims.exampleGrow N (zt 0 (1 / 2))
              (LoopData.idx ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2)) M
            - (band Dims.exampleGrow).Kval 0 N (1 / 2)
                (LoopData.idx ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2))‖
          / (1 * tailT ((Dims.exampleGrow.W N : ℝ)) ((band Dims.exampleGrow).ell N (1 / 2))
              (etaT 0 (1 / 2)) 1 ((zdist (Dims.exampleGrow.L N) (a 0 - a 1) : ℝ)))) 1 : ℝ) : ℂ)
      * (1 : ℂ)) := by
  have hE : |(0 : ℝ)| < 2 := by norm_num
  have hη : (0 : ℝ) < etaT 0 (1 / 2) := etaT_pos' hE (by norm_num)
  have hz : (zt 0 (1 / 2 : ℝ)).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hη.ne'
  have hzη : etaT 0 (1 / 2) ≤ |(zt 0 (1 / 2 : ℝ)).im| := by
    rw [← etaT_eq_zt_im, abs_of_pos hη]
  exact testFun_softW_jS (r := 1) (ΘN := 1) (Θ := 1) le_rfl one_pos one_pos hz hη hzη
    (bddC2C_const (E := Matrix (Dims.exampleGrow.Idx N) (Dims.exampleGrow.Idx N) ℂ) (1 : ℂ))

/-- **The calibration hypotheses of `RBM.Gauss.softMax_le_exp_one_mul_jStar` are satisfiable on
the real model, not only in the abstract.**  At `A = 2`, `n = L N` and soft-max order
`2r = 2 · L N` the three conditions `2 ≤ n`, `L² ≤ n^A` and `A log n ≤ 2r` hold simultaneously
for **every** `RBM.Gauss.Dims` and every `N`, so the comparison
`softMax ≤ e · (J*_{u,D} − 1)` is a statement with content: the `card`-free bound really is
available on the model's own (5.29) family.  (The estimate of (5.39)–(5.47) is a separate
matter and is not touched here.) -/
theorem sat_softMax_lkRatio_le_exp_one_mul_jS (d : Dims) (N : ℕ) (E D u : ℝ) (ω : Ω d) :
    softMax (d.L N) (Finset.univ : Finset (LoopArg (d.L N) 2))
        (fun a => ‖loopObs d N (zt E u)
              (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) (Hflow d N u ω)
            - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖
          / (1 * tailT ((d.W N : ℝ)) ((band d).ell N u) (etaT E u) D
              ((zdist (d.L N) (a 0 - a 1) : ℝ))))
      ≤ Real.exp 1 * ((jS (sample d) E D N u ω - 1) / 1) := by
  have h3 : 3 ≤ d.L N := d.three_le_L N
  have hL0 : (0 : ℝ) < (d.L N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) h3
  have hq : (2 : ℝ) * Real.log ((d.L N : ℕ) : ℝ) ≤ 2 * ((d.L N : ℕ) : ℝ) := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have hcard : ((d.L N : ℝ)) ^ 2 ≤ ((d.L N : ℕ) : ℝ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact softMax_lkRatio_le_exp_one_mul_jS (A := 2) (n := d.L N) (r := d.L N) ω one_pos
    (by omega) (by omega) (by norm_num) hcard hq

end Sat

end Gauss

end RBM

/-!
## Deviations from the paper

**T259a** (§5.3, (5.29); the sentence defining `J*_{u,D}` and the soft-maximum device of the
display after (5.44)).

1. *The comparison `J* ↔ softMax` is stated with an explicit normalization `Θ_N`.*  The paper
   writes the soft maximum of the ratios of (5.29) and the maximum `J*_{u,D}` of the same
   ratios interchangeably.  In Lean the two families differ by the constant `Θ_N` in the
   denominator (`RBM.Gauss.testFun_softW_lkRatio` carries it, `RBM.Step2.jStar` does not), so
   the comparison is stated as `(J* − 1)/Θ_N ≤ softMax ≤ e·(J* − 1)/Θ_N`
   (`RBM.Gauss.jStar_softMax_two_sided`).  The `− 1` is the additive `+1` that (5.29) itself
   puts into `J*`.  No change to the paper is proposed; this only fixes the normalization.
   Affected: the sentence introducing (5.29) and the display after (5.44).  No renumbering.
2. *The calibration of `2r` is an explicit hypothesis, not an asymptotic convention.*  The
   paper takes the soft-maximum order `q ≍ log N` tacitly.  Here the hypotheses
   `L² ≤ n^A` and `A log n ≤ 2r` are written out
   (`RBM.Gauss.softMax_le_exp_one_mul_jStar`), so the constant is literally `e` and not `1 +
   o(1)`.  This is a strengthening of the bookkeeping only.  No change to the paper.  No
   renumbering.
-/
