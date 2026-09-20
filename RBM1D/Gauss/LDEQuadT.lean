/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDEQuad

/-!
# The positive chaos moment bound `E[T^p] ≤ C_p E[Vq^p]` — T93

`RBM1D/Gauss/LDEQuad.lean` (T82) closes the Hanson–Wright recursion at
`RBM.Gauss.RowChaos.mom_succ_le`:

`E|Q|^{2p} ≤ (2p−1)^p E[T^p]`,  `T = ∑_k σ_k(‖U_k‖² + ‖V_k‖²)`.

What is left to reach the paper's control `Vq = ∑_{k,l} σ_k‖B_{kl}‖²σ_l` is the *positive
chaos* moment bound `E[T^p] ≤ C_p E[Vq^p]`.  That is what this file does, by the
conditioning-free route sketched in the header of `LDEQuad.lean`: run the same Gaussian
integration by parts on `E[T^p]`, with the **Wirtinger derivation along the row entry**

`D_l = r(∂_{a_l} − ε_l i ∂_{b_l})`,   `a_l = co l tt`,  `b_l = co l ff`.

It satisfies

`D_l U_k = 0`,  `D_l \bar V_k = 0`,  `D_l \bar U_k = 2r² \bar B_{kl}`,  `D_l V_k = 2r² B_{lk}`,

which is why `T` — built from `U \bar U` and `V \bar V` — differentiates into something
controlled by `B` alone.

Nothing here touches `RBM1D/Gauss/LDEQuad.lean`.

## This file so far

* `RBM.Gauss.RowChaos.wirtVal`          : the derivation `D_l`, as a function of the two partials
* `RBM.Gauss.RowChaos.integral_conj_h_mul_gen` : **the master identity**
  `∫ \bar h_l Z = w_l ∫ D_l Z` for tame `Z`
* `wirtVal_U`, `wirtVal_V`, `wirtVal_conj_U`, `wirtVal_conj_V` : the four derivation values
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Finset

namespace RowChaos

variable {d : Dims} {κ : Type*} [Fintype κ] [DecidableEq κ] (C : RowChaos d κ)

/-! ### The Wirtinger derivation along the row -/

/-- `D_l Z = r(∂_{a_l}Z − ε_l i ∂_{b_l}Z)`, as a function of the two partials `a`, `b`. -/
noncomputable def wirtVal (l : κ) (a b : ℂ) : ℂ :=
  (C.r : ℂ) * (a - ((C.eps l : ℂ) * Complex.I) * b)

variable {C}

theorem wirtVal_zero (l : κ) : C.wirtVal l 0 0 = 0 := by simp [wirtVal]

theorem wirtVal_add (l : κ) (a b a' b' : ℂ) :
    C.wirtVal l (a + a') (b + b') = C.wirtVal l a b + C.wirtVal l a' b' := by
  simp only [wirtVal]; ring

theorem wirtVal_smul (l : κ) (z a b : ℂ) :
    C.wirtVal l (z * a) (z * b) = z * C.wirtVal l a b := by
  simp only [wirtVal]; ring

theorem wirtVal_sum {ι : Type*} (s : Finset ι) (l : κ) (A B : ι → ℂ) :
    C.wirtVal l (∑ j ∈ s, A j) (∑ j ∈ s, B j) = ∑ j ∈ s, C.wirtVal l (A j) (B j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [wirtVal]
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj,
        wirtVal_add, ih]

/-! #### The four derivation values -/

/-- `D_l U_k = 0`: the row enters `U_k` only through `\bar h`, which is anti-holomorphic. -/
theorem wirtVal_U (l m : κ) (ω : Ω d) :
    C.wirtVal l (C.B ω m l * (C.r : ℂ))
      (C.B ω m l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I))) = 0 := by
  have hq : ((C.eps l : ℂ) * Complex.I) ^ 2 = -1 := by
    rw [mul_pow, C.eps_sq_complex l, Complex.I_sq, one_mul]
  simp only [wirtVal]
  linear_combination ((C.r : ℂ) ^ 2 * C.B ω m l) * hq

/-- `D_l V_k = 2r² B_{lk}`. -/
theorem wirtVal_V (l m : κ) (ω : Ω d) :
    C.wirtVal l ((C.r : ℂ) * C.B ω l m)
      (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l m)
      = 2 * (C.r : ℂ) ^ 2 * C.B ω l m := by
  have hq : ((C.eps l : ℂ) * Complex.I) ^ 2 = -1 := by
    rw [mul_pow, C.eps_sq_complex l, Complex.I_sq, one_mul]
  simp only [wirtVal]
  linear_combination (-((C.r : ℂ) ^ 2 * C.B ω l m)) * hq

/-- `D_l \bar U_k = 2r² \bar B_{kl}`. -/
theorem wirtVal_conj_U (l m : κ) (ω : Ω d) :
    C.wirtVal l ((starRingEnd ℂ) (C.B ω m l * (C.r : ℂ)))
      ((starRingEnd ℂ) (C.B ω m l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I))))
      = 2 * (C.r : ℂ) ^ 2 * (starRingEnd ℂ) (C.B ω m l) := by
  have hq : ((C.eps l : ℂ) * Complex.I) ^ 2 = -1 := by
    rw [mul_pow, C.eps_sq_complex l, Complex.I_sq, one_mul]
  simp only [wirtVal, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  linear_combination (-((C.r : ℂ) ^ 2 * (starRingEnd ℂ) (C.B ω m l))) * hq

/-- `D_l \bar V_k = 0`. -/
theorem wirtVal_conj_V (l m : κ) (ω : Ω d) :
    C.wirtVal l ((starRingEnd ℂ) ((C.r : ℂ) * C.B ω l m))
      ((starRingEnd ℂ) (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l m)) = 0 := by
  have hq : ((C.eps l : ℂ) * Complex.I) ^ 2 = -1 := by
    rw [mul_pow, C.eps_sq_complex l, Complex.I_sq, one_mul]
  simp only [wirtVal, map_mul, Complex.conj_I, Complex.conj_ofReal]
  linear_combination ((C.r : ℂ) ^ 2 * (starRingEnd ℂ) (C.B ω l m)) * hq

/-! ### The master identity `∫ \bar h_l Z = w_l ∫ D_l Z` -/

variable (C)

/-- **Gaussian integration by parts along one row entry.**  For every tame `Z` whose partials
along the two coordinates of the index `l` are `ZA`, `ZB`,

`∫ \bar h_l · Z = w_l ∫ D_l Z`,  `D_l Z = r(ZA − ε_l i ZB)`.

This is `RBM.Gauss.GaussIBP.stein` applied once to each of the two coordinates, combined with
`\bar h_l = r(ω_{a_l} − ε_l i ω_{b_l})`.  It is the analogue of
`RBM.Gauss.RowChaos.integral_chaos_mul` for a single row entry rather than the whole chaos. -/
theorem integral_conj_h_mul_gen (hG : GaussIBP d) {Z ZA ZB : Ω d → ℂ} (l : κ)
    (hZ : Tame d Z) (hZA : Tame d ZA) (hZB : Tame d ZB)
    (hdA : ∀ ω, HasDerivAt (fun s : ℝ => Z (Function.update ω (C.co l true) s)) (ZA ω)
      (ω (C.co l true)))
    (hdB : ∀ ω, HasDerivAt (fun s : ℝ => Z (Function.update ω (C.co l false) s)) (ZB ω)
      (ω (C.co l false))) :
    ∫ ω, (starRingEnd ℂ) (C.h ω l) * Z ω ∂(P d)
      = (C.w l : ℂ) * ∫ ω, C.wirtVal l (ZA ω) (ZB ω) ∂(P d) := by
  have hA : ∫ ω, (ω (C.co l true) : ℂ) * Z ω ∂(P d) = (C.w l : ℂ) * ∫ ω, ZA ω ∂(P d) :=
    hG.stein (C.co l true) Z ZA hZ hZA hdA
  have hB : ∫ ω, (ω (C.co l false) : ℂ) * Z ω ∂(P d) = (C.w l : ℂ) * ∫ ω, ZB ω ∂(P d) := by
    have h := hG.stein (C.co l false) Z ZB hZ hZB hdB
    have hgv : ((gvar d (C.co l false) : ℝ) : ℂ) = ((C.w l : ℝ) : ℂ) := by
      rw [C.gvar_tag l]; rfl
    rw [h, hgv]
  have hi1 : Integrable (fun ω : Ω d => (ω (C.co l true) : ℂ) * Z ω) (P d) :=
    ((Tame.coord (C.co l true)).mul hZ).integrable hG
  have hi2 : Integrable (fun ω : Ω d => (ω (C.co l false) : ℂ) * Z ω) (P d) :=
    ((Tame.coord (C.co l false)).mul hZ).integrable hG
  have hiA : Integrable ZA (P d) := hZA.integrable hG
  have hiB : Integrable ZB (P d) := hZB.integrable hG
  calc ∫ ω, (starRingEnd ℂ) (C.h ω l) * Z ω ∂(P d)
      = ∫ ω, ((C.r : ℂ) * ((ω (C.co l true) : ℂ) * Z ω)
          - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) *
            ((ω (C.co l false) : ℂ) * Z ω)) ∂(P d) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        simp only [C.conj_h]; ring
    _ = (C.r : ℂ) * ∫ ω, (ω (C.co l true) : ℂ) * Z ω ∂(P d)
        - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) *
          ∫ ω, (ω (C.co l false) : ℂ) * Z ω ∂(P d) := by
        rw [integral_sub (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = (C.w l : ℂ) * ((C.r : ℂ) * ∫ ω, ZA ω ∂(P d)
          - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) * ∫ ω, ZB ω ∂(P d)) := by
        rw [hA, hB]; ring
    _ = (C.w l : ℂ) * ∫ ω, C.wirtVal l (ZA ω) (ZB ω) ∂(P d) := by
        congr 1
        rw [show (fun ω => C.wirtVal l (ZA ω) (ZB ω))
            = fun ω => (C.r : ℂ) * ZA ω
              - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) * ZB ω from by
          funext ω; simp only [wirtVal]; ring]
        rw [integral_sub (hiA.const_mul _) (hiB.const_mul _), integral_const_mul,
          integral_const_mul]

end RowChaos

end RBM.Gauss
