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

/-- Right-hand scalar: `D_l (a·z, b·z) = (D_l(a,b))·z`. -/
theorem wirtVal_mul_right (l : κ) (z a b : ℂ) :
    C.wirtVal l (a * z) (b * z) = C.wirtVal l a b * z := by
  simp only [wirtVal]; ring

/-! ### The partials of `T` along the row -/

/-- `∂T/∂a_l`, in complex form. -/
noncomputable def TA (l : κ) (ω : Ω d) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) *
    ((C.B ω k l * (C.r : ℂ)) * (starRingEnd ℂ) (C.U ω k)
      + C.U ω k * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
      + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
      + C.V ω k * (starRingEnd ℂ) ((C.r : ℂ) * C.B ω l k))

/-- `∂T/∂b_l`, in complex form. -/
noncomputable def TB (l : κ) (ω : Ω d) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) *
    ((C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I))) * (starRingEnd ℂ) (C.U ω k)
      + C.U ω k *
        (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
      + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
      + C.V ω k *
        (starRingEnd ℂ) (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k))

theorem tameTA (l : κ) : Tame d (C.TA l) :=
  Tame.sum _ fun k _ => (Tame.const (d := d) ((C.sg k : ℝ) : ℂ)).mul
    (((((C.tameB k l).mul (Tame.const (d := d) ((C.r : ℂ)))).mul (C.tameU k).conj).add
      ((C.tameU k).mul (((C.tameB k l).mul (Tame.const (d := d) ((C.r : ℂ)))).conj))).add
      (((Tame.const (d := d) ((C.r : ℂ))).mul (C.tameB l k)).mul (C.tameV k).conj) |>.add
      ((C.tameV k).mul (((Tame.const (d := d) ((C.r : ℂ))).mul (C.tameB l k)).conj)))

theorem tameTB (l : κ) : Tame d (C.TB l) :=
  Tame.sum _ fun k _ => (Tame.const (d := d) ((C.sg k : ℝ) : ℂ)).mul
    (((((C.tameB k l).mul (Tame.const (d := d)
        (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))).mul (C.tameU k).conj).add
      ((C.tameU k).mul (((C.tameB k l).mul (Tame.const (d := d)
        (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))).conj))).add
      (((Tame.const (d := d) ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)).mul
        (C.tameB l k)).mul (C.tameV k).conj) |>.add
      ((C.tameV k).mul (((Tame.const (d := d)
        ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)).mul (C.tameB l k)).conj)))

theorem hasDerivAt_Tq_true (l : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => ((C.Tq (Function.update ω (C.co l true) s) : ℝ) : ℂ))
      (C.TA l ω) (ω (C.co l true)) := by
  have hfun : (fun s : ℝ => ((C.Tq (Function.update ω (C.co l true) s) : ℝ) : ℂ))
      = fun s : ℝ => ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l true) s) k)
          + C.V (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l true) s) k)) := by
    funext s; exact C.Tq_complex _
  rw [hfun]
  have hself := Function.update_eq_self (C.co l true) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l true) s) k)
          + C.V (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l true) s) k)))
      (((C.sg k : ℝ) : ℂ) *
        ((C.B ω k l * (C.r : ℂ)) * (starRingEnd ℂ) (C.U ω k)
          + C.U ω k * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
          + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
          + C.V ω k * (starRingEnd ℂ) ((C.r : ℂ) * C.B ω l k)))
      (ω (C.co l true)) := by
    intro k
    have hU := C.hasDerivAt_U_true l k ω
    have hV := C.hasDerivAt_V_true l k ω
    have hUc := hasDerivAt_conj' hU
    have hVc := hasDerivAt_conj' hV
    have h1 := hU.fun_mul hUc
    have h2 := hV.fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    ring
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k
  exact hsum

theorem hasDerivAt_Tq_false (l : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => ((C.Tq (Function.update ω (C.co l false) s) : ℝ) : ℂ))
      (C.TB l ω) (ω (C.co l false)) := by
  have hfun : (fun s : ℝ => ((C.Tq (Function.update ω (C.co l false) s) : ℝ) : ℂ))
      = fun s : ℝ => ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l false) s) k)
          + C.V (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l false) s) k)) := by
    funext s; exact C.Tq_complex _
  rw [hfun]
  have hself := Function.update_eq_self (C.co l false) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l false) s) k)
          + C.V (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l false) s) k)))
      (((C.sg k : ℝ) : ℂ) *
        ((C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I))) * (starRingEnd ℂ) (C.U ω k)
          + C.U ω k *
            (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
          + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
          + C.V ω k *
            (starRingEnd ℂ) (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k)))
      (ω (C.co l false)) := by
    intro k
    have hU := C.hasDerivAt_U_false l k ω
    have hV := C.hasDerivAt_V_false l k ω
    have hUc := hasDerivAt_conj' hU
    have hVc := hasDerivAt_conj' hV
    have h1 := hU.fun_mul hUc
    have h2 := hV.fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    ring
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k
  exact hsum

variable {C}

/-- The `k`-th summand of `D_l T`: `D_l(U_k\bar U_k + V_k\bar V_k)
= 2r²(U_k\bar B_{kl} + B_{lk}\bar V_k)`. -/
theorem wirtVal_term (l k : κ) (ω : Ω d) :
    C.wirtVal l
      ((C.B ω k l * (C.r : ℂ)) * (starRingEnd ℂ) (C.U ω k)
        + C.U ω k * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
        + C.V ω k * (starRingEnd ℂ) ((C.r : ℂ) * C.B ω l k))
      ((C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I))) * (starRingEnd ℂ) (C.U ω k)
        + C.U ω k *
          (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
        + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
        + C.V ω k *
          (starRingEnd ℂ) (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k))
      = 2 * (C.r : ℂ) ^ 2 *
        (C.U ω k * (starRingEnd ℂ) (C.B ω k l) + C.B ω l k * (starRingEnd ℂ) (C.V ω k)) := by
  have hq : ((C.eps l : ℂ) * Complex.I) ^ 2 = -1 := by
    rw [mul_pow, C.eps_sq_complex l, Complex.I_sq, one_mul]
  simp only [wirtVal, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  linear_combination ((C.r : ℂ) ^ 2 *
    (C.B ω k l * (starRingEnd ℂ) (C.U ω k) - C.U ω k * (starRingEnd ℂ) (C.B ω k l)
      - C.B ω l k * (starRingEnd ℂ) (C.V ω k)
      + C.V ω k * (starRingEnd ℂ) (C.B ω l k))) * hq

/-- **`D_l T = 2r² ∑_k σ_k (U_k \bar B_{kl} + B_{lk} \bar V_k)`.**  Both `U` and `\bar V` are
killed by `D_l`, so only `B` survives — this is the whole point of the derivation. -/
theorem wirtVal_TA_TB (l : κ) (ω : Ω d) :
    C.wirtVal l (C.TA l ω) (C.TB l ω)
      = 2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.V ω k)) := by
  rw [TA, TB, wirtVal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wirtVal_smul, wirtVal_term]
  ring

/-! ### `T` as a linear form in the row: `T = ∑_l \bar h_l W_l` -/

variable (C)

/-- `W_l = ∑_k σ_k(B_{kl}\bar U_k + V_k \bar B_{lk})`, the coefficient of `\bar h_l` in `T`. -/
noncomputable def Wt (l : κ) (ω : Ω d) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.U ω k)
    + C.V ω k * (starRingEnd ℂ) (C.B ω l k))

theorem tameWt (l : κ) : Tame d (C.Wt l) :=
  Tame.sum _ fun k _ => (Tame.const (d := d) ((C.sg k : ℝ) : ℂ)).mul
    (((C.tameB k l).mul (C.tameU k).conj).add ((C.tameV k).mul (C.tameB l k).conj))

variable {C}

/-- **`T` is a linear form in the conjugated row.**  Both `U_k\bar U_k` and `V_k\bar V_k`
contain exactly one factor `\bar h`, so `T = ∑_l \bar h_l W_l`.  This is what makes the
integration by parts of `E[T^{q+1}]` possible. -/
theorem Tq_eq_sum_conj_h_mul (ω : Ω d) :
    ((C.Tq ω : ℝ) : ℂ) = ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Wt l ω := by
  have hU : ∀ k : κ, C.U ω k = ∑ l, C.B ω k l * (starRingEnd ℂ) (C.h ω l) := fun _ => rfl
  have hV : ∀ k : κ, (starRingEnd ℂ) (C.V ω k)
      = ∑ l, (starRingEnd ℂ) (C.h ω l) * (starRingEnd ℂ) (C.B ω l k) := by
    intro k
    show (starRingEnd ℂ) (∑ m, C.h ω m * C.B ω m k) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => map_mul _ _ _
  have hexp : (∑ l, (starRingEnd ℂ) (C.h ω l) * C.Wt l ω)
      = ∑ l, ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.h ω l) * (starRingEnd ℂ) (C.U ω k)
          + C.V ω k * ((starRingEnd ℂ) (C.h ω l) * (starRingEnd ℂ) (C.B ω l k))) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Wt, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [C.Tq_complex ω, hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  nth_rewrite 1 [hU k]
  rw [hV k, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- The `k`-th summand of `D_l W_l`. -/
theorem wirtVal_termW (l k : κ) (ω : Ω d) :
    C.wirtVal l
      (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k))
      (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
        + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) *
          (starRingEnd ℂ) (C.B ω l k))
      = 2 * (C.r : ℂ) ^ 2 * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
        + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)) := by
  have hq : ((C.eps l : ℂ) * Complex.I) ^ 2 = -1 := by
    rw [mul_pow, C.eps_sq_complex l, Complex.I_sq, one_mul]
  simp only [wirtVal, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  linear_combination (-((C.r : ℂ) ^ 2 *
    (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
      + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)))) * hq

/-- **`D_l W_l = 2r² ∑_k σ_k(‖B_{kl}‖² + ‖B_{lk}‖²)`.** -/
theorem wirtVal_Wt (l : κ) (ω : Ω d) :
    C.wirtVal l
      (∑ k, ((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k)))
      (∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l *
            (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
          + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) *
            (starRingEnd ℂ) (C.B ω l k)))
      = 2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)) := by
  rw [wirtVal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wirtVal_smul, wirtVal_termW]
  ring

/-! ### The partials of `W_l` -/

variable (C)

/-- `∂W_l/∂a_l`. -/
noncomputable def WA (l : κ) (ω : Ω d) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
    + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k))

/-- `∂W_l/∂b_l`. -/
noncomputable def WB (l : κ) (ω : Ω d) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) *
    (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
      + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k))

theorem tameWA (l : κ) : Tame d (C.WA l) :=
  Tame.sum _ fun k _ => (Tame.const (d := d) ((C.sg k : ℝ) : ℂ)).mul
    (((C.tameB k l).mul ((C.tameB k l).mul (Tame.const (d := d) ((C.r : ℂ)))).conj).add
      (((Tame.const (d := d) ((C.r : ℂ))).mul (C.tameB l k)).mul (C.tameB l k).conj))

theorem tameWB (l : κ) : Tame d (C.WB l) :=
  Tame.sum _ fun k _ => (Tame.const (d := d) ((C.sg k : ℝ) : ℂ)).mul
    (((C.tameB k l).mul ((C.tameB k l).mul (Tame.const (d := d)
        (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))).conj).add
      (((Tame.const (d := d) ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)).mul
        (C.tameB l k)).mul (C.tameB l k).conj))

theorem hasDerivAt_Wt_true (l : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.Wt l (Function.update ω (C.co l true) s)) (C.WA l ω)
      (ω (C.co l true)) := by
  have hself := Function.update_eq_self (C.co l true) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.B (Function.update ω (C.co l true) s) k l *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l true) s) k)
          + C.V (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.B (Function.update ω (C.co l true) s) l k)))
      (((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k)))
      (ω (C.co l true)) := by
    intro k
    have hB1 := C.hasDerivAt_B_const l true k l ω
    have hB2 := C.hasDerivAt_B_const l true l k ω
    have hUc := hasDerivAt_conj' (C.hasDerivAt_U_true l k ω)
    have hVc := hasDerivAt_conj' hB2
    have h1 := hB1.fun_mul hUc
    have h2 := (C.hasDerivAt_V_true l k ω).fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    simp only [map_zero]
    ring
  exact HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k

theorem hasDerivAt_Wt_false (l : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.Wt l (Function.update ω (C.co l false) s)) (C.WB l ω)
      (ω (C.co l false)) := by
  have hself := Function.update_eq_self (C.co l false) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.B (Function.update ω (C.co l false) s) k l *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l false) s) k)
          + C.V (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.B (Function.update ω (C.co l false) s) l k)))
      (((C.sg k : ℝ) : ℂ) *
        (C.B ω k l *
            (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
          + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) *
            (starRingEnd ℂ) (C.B ω l k)))
      (ω (C.co l false)) := by
    intro k
    have hB1 := C.hasDerivAt_B_const l false k l ω
    have hB2 := C.hasDerivAt_B_const l false l k ω
    have hUc := hasDerivAt_conj' (C.hasDerivAt_U_false l k ω)
    have hVc := hasDerivAt_conj' hB2
    have h1 := hB1.fun_mul hUc
    have h2 := (C.hasDerivAt_V_false l k ω).fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    simp only [map_zero]
    ring
  exact HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k

variable {C}

/-- `D_l W_l = 2r² ∑_k σ_k(‖B_{kl}‖² + ‖B_{lk}‖²)`, in terms of `WA`/`WB`. -/
theorem wirtVal_WA_WB (l : κ) (ω : Ω d) :
    C.wirtVal l (C.WA l ω) (C.WB l ω)
      = 2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)) :=
  C.wirtVal_Wt l ω

/-! ### The integration by parts of `E[T^{q+1}]` -/

variable (C)

/-- `Z_{q,l} = W_l · T^q`, the coefficient of `\bar h_l` in `T^{q+1}`. -/
noncomputable def Zt (q : ℕ) (l : κ) (ω : Ω d) : ℂ :=
  C.Wt l ω * ((C.Tq ω : ℝ) : ℂ) ^ q

/-- `∂Z_{q,l}/∂a_l`. -/
noncomputable def ZA (q : ℕ) (l : κ) (ω : Ω d) : ℂ :=
  C.WA l ω * ((C.Tq ω : ℝ) : ℂ) ^ q
    + C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) * C.TA l ω)

/-- `∂Z_{q,l}/∂b_l`. -/
noncomputable def ZB (q : ℕ) (l : κ) (ω : Ω d) : ℂ :=
  C.WB l ω * ((C.Tq ω : ℝ) : ℂ) ^ q
    + C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) * C.TB l ω)

theorem tameZt (q : ℕ) (l : κ) : Tame d (C.Zt q l) :=
  (C.tameWt l).mul (C.tameTq.pow q)

theorem tameZA (q : ℕ) (l : κ) : Tame d (C.ZA q l) :=
  ((C.tameWA l).mul (C.tameTq.pow q)).add
    ((C.tameWt l).mul
      (((Tame.const (d := d) ((q : ℂ))).mul (C.tameTq.pow (q - 1))).mul (C.tameTA l)))

theorem tameZB (q : ℕ) (l : κ) : Tame d (C.ZB q l) :=
  ((C.tameWB l).mul (C.tameTq.pow q)).add
    ((C.tameWt l).mul
      (((Tame.const (d := d) ((q : ℂ))).mul (C.tameTq.pow (q - 1))).mul (C.tameTB l)))

variable {C}

theorem Tq_pow_succ_eq_sum (q : ℕ) (ω : Ω d) :
    ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) = ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω := by
  have h := Tq_eq_sum_conj_h_mul (C := C) ω
  calc ((C.Tq ω : ℝ) : ℂ) ^ (q + 1)
      = ((C.Tq ω : ℝ) : ℂ) ^ q * ((C.Tq ω : ℝ) : ℂ) := pow_succ _ _
    _ = ((C.Tq ω : ℝ) : ℂ) ^ q * ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Wt l ω := by rw [← h]
    _ = ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [Zt]; ring

variable (C)

theorem hasDerivAt_Zt_true (q : ℕ) (l : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.Zt q l (Function.update ω (C.co l true) s)) (C.ZA q l ω)
      (ω (C.co l true)) := by
  have hself := Function.update_eq_self (C.co l true) ω
  have hW := C.hasDerivAt_Wt_true l ω
  have hT := (C.hasDerivAt_Tq_true l ω).fun_pow q
  have hmul := hW.fun_mul hT
  simp only [hself] at hmul
  exact hmul

theorem hasDerivAt_Zt_false (q : ℕ) (l : κ) (ω : Ω d) :
    HasDerivAt (fun s : ℝ => C.Zt q l (Function.update ω (C.co l false) s)) (C.ZB q l ω)
      (ω (C.co l false)) := by
  have hself := Function.update_eq_self (C.co l false) ω
  have hW := C.hasDerivAt_Wt_false l ω
  have hT := (C.hasDerivAt_Tq_false l ω).fun_pow q
  have hmul := hW.fun_mul hT
  simp only [hself] at hmul
  exact hmul

variable {C}

/-- **`D_l Z_{q,l}`**: the diagonal term (which will sum to `2V_q T^q`) plus the cross term. -/
theorem wirtVal_ZA_ZB (q : ℕ) (l : κ) (ω : Ω d) :
    C.wirtVal l (C.ZA q l ω) (C.ZB q l ω)
      = (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
            (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
              + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))) * ((C.Tq ω : ℝ) : ℂ) ^ q
        + C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
            (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
              (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
                + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))) := by
  rw [ZA, ZB, wirtVal_add, wirtVal_mul_right, wirtVal_WA_WB, wirtVal_smul, wirtVal_smul,
    wirtVal_TA_TB]

/-- **The integration by parts of `E[T^{q+1}]`.**  `T^{q+1} = ∑_l \bar h_l Z_{q,l}`, and each
`\bar h_l` is integrated by parts against `Z_{q,l}`. -/
theorem integral_Tq_pow_succ (hG : GaussIBP d) (q : ℕ) :
    ∫ ω, ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) ∂(P d)
      = ∑ l, (C.w l : ℂ) * ∫ ω, C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(P d) := by
  have hint : ∀ l : κ, Integrable (fun ω => (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω) (P d) :=
    fun l => (((C.tameh l).conj).mul (C.tameZt q l)).integrable hG
  calc ∫ ω, ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) ∂(P d)
      = ∫ ω, ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω ∂(P d) :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => Tq_pow_succ_eq_sum q ω)
    _ = ∑ l, ∫ ω, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω ∂(P d) :=
        integral_finsetSum _ fun l _ => hint l
    _ = ∑ l, (C.w l : ℂ) * ∫ ω, C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(P d) :=
        Finset.sum_congr rfl fun l _ =>
          C.integral_conj_h_mul_gen hG l (C.tameZt q l) (C.tameZA q l) (C.tameZB q l)
            (C.hasDerivAt_Zt_true q l) (C.hasDerivAt_Zt_false q l)

/-! ### The diagonal term sums to `2 V_q` -/

/-- `∑_l σ_l ∑_k σ_k(‖B_{kl}‖² + ‖B_{lk}‖²) = 2V_q`: the two double sums are the same after
swapping the indices. -/
theorem sum_sg_mul_normSq (ω : Ω d) :
    ∑ l, C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) = 2 * C.Vq ω := by
  have e1 : ∑ l, C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)
      = (∑ l, ∑ k, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l)
        + ∑ l, ∑ k, C.sg l * ‖C.B ω l k‖ ^ 2 * C.sg k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : (∑ l, ∑ k, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l) = C.Vq ω := by
    rw [Vq, Finset.sum_comm]
  have e3 : (∑ l, ∑ k, C.sg l * ‖C.B ω l k‖ ^ 2 * C.sg k) = C.Vq ω := rfl
  rw [e1, e2, e3]; ring

/-- The diagonal part of `∑_l w_l D_l Z_{q,l}` is `2 V_q T^q`. -/
theorem sum_w_diag (q : ℕ) (ω : Ω d) :
    ∑ l, (C.w l : ℂ) * ((2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
          + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))) * ((C.Tq ω : ℝ) : ℂ) ^ q)
      = ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) := by
  have hterm : ∀ l : κ, (C.w l : ℂ) * ((2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
          + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))) * ((C.Tq ω : ℝ) : ℂ) ^ q)
      = ((C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) : ℝ) : ℂ)
        * ((C.Tq ω : ℝ) : ℂ) ^ q := by
    intro l
    have hk : ∀ k : κ, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
          + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))
        = ((C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) : ℝ) : ℂ) := by
      intro k
      rw [Complex.ofReal_mul, Complex.ofReal_add, ofReal_normSq, ofReal_normSq]
    rw [Finset.sum_congr rfl fun k _ => hk k, ← Complex.ofReal_sum, Complex.ofReal_mul,
      C.sg_complex l]
    ring
  rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.sum_mul, ← Complex.ofReal_sum,
    C.sum_sg_mul_normSq ω, ← Complex.ofReal_pow, ← Complex.ofReal_mul]

/-! ### The cross term -/

/-- Weighted Cauchy–Schwarz: `(∑ σ x y)² ≤ (∑ σ x²)(∑ σ y²)`. -/
theorem weighted_cauchy {ι : Type*} (s : Finset ι) (σ x y : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    (∑ i ∈ s, σ i * (x i * y i)) ^ 2
      ≤ (∑ i ∈ s, σ i * x i ^ 2) * ∑ i ∈ s, σ i * y i ^ 2 :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i _ => mul_nonneg (hσ i) (sq_nonneg _))
    (fun i _ => mul_nonneg (hσ i) (sq_nonneg _)) (fun i _ => le_of_eq (by ring))

/-- `q·x^{q-1}·x = q·x^q`, valid also at `q = 0`. -/
theorem nat_mul_pow_pred (x : ℝ) (q : ℕ) : (q : ℝ) * x ^ (q - 1) * x = (q : ℝ) * x ^ q := by
  cases q with
  | zero => simp
  | succ n => simp [pow_succ]; ring

variable (C)

/-- The common majorant of `‖W_l‖` and of `‖D_l T‖/(2r²)`. -/
noncomputable def Arow (l : κ) (ω : Ω d) : ℝ :=
  ∑ k, C.sg k * (‖C.B ω k l‖ * ‖C.U ω k‖ + ‖C.V ω k‖ * ‖C.B ω l k‖)

variable {C}

theorem Arow_nonneg (l : κ) (ω : Ω d) : 0 ≤ C.Arow l ω :=
  Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)

theorem norm_Wt_le (l : κ) (ω : Ω d) : ‖C.Wt l ω‖ ≤ C.Arow l ω := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.sg_nonneg k)]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (C.sg_nonneg k)
  rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]

theorem norm_sum_UV_le (l : κ) (ω : Ω d) :
    ‖∑ k, ((C.sg k : ℝ) : ℂ) * (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
      + C.B ω l k * (starRingEnd ℂ) (C.V ω k))‖ ≤ C.Arow l ω := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.sg_nonneg k)]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (C.sg_nonneg k)
  rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
  have h1 : ‖C.U ω k‖ * ‖C.B ω k l‖ = ‖C.B ω k l‖ * ‖C.U ω k‖ := mul_comm _ _
  have h2 : ‖C.B ω l k‖ * ‖C.V ω k‖ = ‖C.V ω k‖ * ‖C.B ω l k‖ := mul_comm _ _
  rw [h1, h2]

theorem sum_sg_normSq_U_le (ω : Ω d) : ∑ k, C.sg k * ‖C.U ω k‖ ^ 2 ≤ C.Tq ω := by
  refine Finset.sum_le_sum fun k _ => ?_
  have := mul_le_mul_of_nonneg_left
    (by nlinarith [sq_nonneg ‖C.V ω k‖] : ‖C.U ω k‖ ^ 2 ≤ ‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2)
    (C.sg_nonneg k)
  exact this

theorem sum_sg_normSq_V_le (ω : Ω d) : ∑ k, C.sg k * ‖C.V ω k‖ ^ 2 ≤ C.Tq ω := by
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left
    (by nlinarith [sq_nonneg ‖C.U ω k‖] : ‖C.V ω k‖ ^ 2 ≤ ‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2)
    (C.sg_nonneg k)

/-- `A_l² ≤ 2T(∑_kσ_k‖B_{kl}‖² + ∑_kσ_k‖B_{lk}‖²)`, by Cauchy–Schwarz in `k`. -/
theorem sq_Arow_le (l : κ) (ω : Ω d) :
    C.Arow l ω ^ 2
      ≤ 2 * C.Tq ω * ((∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) + ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2) := by
  set P : ℝ := ∑ k, C.sg k * (‖C.B ω k l‖ * ‖C.U ω k‖) with hP
  set Q : ℝ := ∑ k, C.sg k * (‖C.V ω k‖ * ‖C.B ω l k‖) with hQ
  have hsplit : C.Arow l ω = P + Q := by
    rw [hP, hQ, Arow, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hPc : P ^ 2 ≤ (∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) * ∑ k, C.sg k * ‖C.U ω k‖ ^ 2 :=
    weighted_cauchy _ _ _ _ (fun k => C.sg_nonneg k)
  have hQc : Q ^ 2 ≤ (∑ k, C.sg k * ‖C.V ω k‖ ^ 2) * ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2 :=
    weighted_cauchy _ _ _ _ (fun k => C.sg_nonneg k)
  have hB1 : (0 : ℝ) ≤ ∑ k, C.sg k * ‖C.B ω k l‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)
  have hB2 : (0 : ℝ) ≤ ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)
  have hU := C.sum_sg_normSq_U_le ω
  have hV := C.sum_sg_normSq_V_le ω
  have hP2 : P ^ 2 ≤ (∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) * C.Tq ω := by
    refine hPc.trans (mul_le_mul_of_nonneg_left hU hB1)
  have hQ2 : Q ^ 2 ≤ C.Tq ω * ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2 := by
    refine hQc.trans (mul_le_mul_of_nonneg_right hV hB2)
  rw [hsplit]
  nlinarith [sq_nonneg (P - Q)]

/-! ### The cross term, bounded -/

variable (C)

/-- The cross term of `∑_l w_l D_l Z_{q,l}`. -/
noncomputable def crossT (q : ℕ) (ω : Ω d) : ℂ :=
  ∑ l, (C.w l : ℂ) * (C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
    (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
      (C.U ω k * (starRingEnd ℂ) (C.B ω k l) + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))))

variable {C}

theorem Vq_nonneg (ω : Ω d) : 0 ≤ C.Vq ω :=
  Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (C.sg_nonneg k) (by positivity)) (C.sg_nonneg l)

/-- `∑_l w_l D_l Z_{q,l}` splits into the diagonal `2V_qT^q` and the cross term. -/
theorem sum_w_wirtVal_ZA_ZB (q : ℕ) (ω : Ω d) :
    ∑ l, (C.w l : ℂ) * C.wirtVal l (C.ZA q l ω) (C.ZB q l ω)
      = ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) + C.crossT q ω := by
  rw [← C.sum_w_diag q ω, crossT, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by rw [wirtVal_ZA_ZB]; ring

/-- **The cross term is `≤ 4q V_q T^q`.**  Two Cauchy–Schwarz steps: first in `k`
(`sq_Arow_le`), then the sum over `l` against `σ_l` is `2V_q` (`sum_sg_mul_normSq`). -/
theorem norm_crossT_le (q : ℕ) (ω : Ω d) :
    ‖C.crossT q ω‖ ≤ 4 * (q : ℝ) * C.Vq ω * C.Tq ω ^ q := by
  have hTn := C.Tq_nonneg ω
  have hTp : (0 : ℝ) ≤ C.Tq ω ^ (q - 1) := by positivity
  have hterm : ∀ l : κ, ‖(C.w l : ℂ) * (C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
        (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))))‖
      ≤ C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2) := by
    intro l
    have hw : ‖(C.w l : ℂ)‖ = C.w l := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.w_nonneg l)]
    have hqn : ‖(q : ℂ)‖ = (q : ℝ) := by simp
    have hT : ‖((C.Tq ω : ℝ) : ℂ) ^ (q - 1)‖ = C.Tq ω ^ (q - 1) := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hTn]
    have hr : ‖(2 : ℂ) * (C.r : ℂ) ^ 2‖ = 2 * C.r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      norm_num
    have hA := C.Arow_nonneg l ω
    have hr2 : (0 : ℝ) ≤ 2 * C.r ^ 2 := by positivity
    calc ‖(C.w l : ℂ) * (C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
          (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
            (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
              + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))))‖
        = C.w l * (‖C.Wt l ω‖ * ((q : ℝ) * C.Tq ω ^ (q - 1) *
            (2 * C.r ^ 2 * ‖∑ k, ((C.sg k : ℝ) : ℂ) *
              (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
                + C.B ω l k * (starRingEnd ℂ) (C.V ω k))‖))) := by
          simp only [norm_mul, hw, hqn, hT, hr]
      _ ≤ C.w l * (C.Arow l ω * ((q : ℝ) * C.Tq ω ^ (q - 1) *
            (2 * C.r ^ 2 * C.Arow l ω))) := by
          gcongr
          · exact C.w_nonneg l
          · exact norm_Wt_le l ω
          · exact norm_sum_UV_le l ω
      _ = C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2) := by
          show C.w l * _ = 2 * C.r ^ 2 * C.w l * _
          ring
  have hstep1 : ‖C.crossT q ω‖
      ≤ ∑ l, C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hterm l)
  have hstep2 : ∑ l, C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2)
      = (q : ℝ) * C.Tq ω ^ (q - 1) * ∑ l, C.sg l * C.Arow l ω ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hstep3 : ∑ l, C.sg l * C.Arow l ω ^ 2 ≤ 2 * C.Tq ω * (2 * C.Vq ω) := by
    have hbound : ∀ l : κ, C.sg l * C.Arow l ω ^ 2
        ≤ 2 * C.Tq ω * (C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := by
      intro l
      have h := C.sq_Arow_le l ω
      have hmerge : ((∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) + ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2)
          = ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hmerge] at h
      have := mul_le_mul_of_nonneg_left h (C.sg_nonneg l)
      calc C.sg l * C.Arow l ω ^ 2
          ≤ C.sg l * (2 * C.Tq ω *
              ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := this
        _ = 2 * C.Tq ω * (C.sg l * ∑ k, C.sg k *
              (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := by ring
    calc ∑ l, C.sg l * C.Arow l ω ^ 2
        ≤ ∑ l, 2 * C.Tq ω * (C.sg l * ∑ k, C.sg k *
            (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := Finset.sum_le_sum fun l _ => hbound l
      _ = 2 * C.Tq ω * ∑ l, C.sg l * ∑ k, C.sg k *
            (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) := by rw [Finset.mul_sum]
      _ = 2 * C.Tq ω * (2 * C.Vq ω) := by rw [C.sum_sg_mul_normSq ω]
  have hqT : (0 : ℝ) ≤ (q : ℝ) * C.Tq ω ^ (q - 1) := by positivity
  calc ‖C.crossT q ω‖
      ≤ (q : ℝ) * C.Tq ω ^ (q - 1) * ∑ l, C.sg l * C.Arow l ω ^ 2 := by
        rw [← hstep2]; exact hstep1
    _ ≤ (q : ℝ) * C.Tq ω ^ (q - 1) * (2 * C.Tq ω * (2 * C.Vq ω)) :=
        mul_le_mul_of_nonneg_left hstep3 hqT
    _ = 4 * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Tq ω) * C.Vq ω := by ring
    _ = 4 * (q : ℝ) * C.Vq ω * C.Tq ω ^ q := by
        rw [nat_mul_pow_pred (C.Tq ω) q]; ring

/-! ### `E[T^{q+1}] ≤ (4q+2) E[V_q T^q]` -/

variable (C)

theorem tameCrossT (q : ℕ) : Tame d (C.crossT q) :=
  Tame.sum _ fun l _ => (Tame.const (d := d) ((C.w l : ℂ))).mul
    ((C.tameWt l).mul (((Tame.const (d := d) ((q : ℂ))).mul (C.tameTq.pow (q - 1))).mul
      ((Tame.const (d := d) (2 * (C.r : ℂ) ^ 2)).mul
        (Tame.sum _ fun k _ => (Tame.const (d := d) ((C.sg k : ℝ) : ℂ)).mul
          (((C.tameU k).mul (C.tameB k l).conj).add
            ((C.tameB l k).mul (C.tameV k).conj))))))

theorem tameWirt (q : ℕ) (l : κ) :
    Tame d fun ω => C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) :=
  (Tame.const (d := d) ((C.r : ℂ))).mul
    ((C.tameZA q l).sub ((Tame.const (d := d) ((C.eps l : ℂ) * Complex.I)).mul (C.tameZB q l)))

/-- `V_q T^q` is integrable. -/
theorem integrable_Vq_mul_Tq_pow (hG : GaussIBP d) (q : ℕ) :
    Integrable (fun ω => C.Vq ω * C.Tq ω ^ q) (P d) := by
  refine integrable_of_tame_ofReal hG ?_
  have hfun : (fun ω : Ω d => ((C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ))
      = fun ω => ((C.Vq ω : ℝ) : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ q := by
    funext ω; rw [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [hfun]
  exact C.tame_ofReal_Vq.mul (C.tameTq.pow q)

/-- `V_q^q` is integrable. -/
theorem integrable_Vq_pow (hG : GaussIBP d) (q : ℕ) :
    Integrable (fun ω => C.Vq ω ^ q) (P d) := by
  refine integrable_of_tame_ofReal hG ?_
  have hfun : (fun ω : Ω d => ((C.Vq ω ^ q : ℝ) : ℂ))
      = fun ω => ((C.Vq ω : ℝ) : ℂ) ^ q := by funext ω; rw [Complex.ofReal_pow]
  rw [hfun]
  exact C.tame_ofReal_Vq.pow q

/-- `E[V_q^q]`. -/
noncomputable def momVpow (q : ℕ) : ℝ := ∫ ω, C.Vq ω ^ q ∂(P d)

theorem momVpow_nonneg (q : ℕ) : 0 ≤ C.momVpow q :=
  MeasureTheory.integral_nonneg fun ω => pow_nonneg (C.Vq_nonneg ω) q

variable {C}

/-- **The recursion for the positive chaos**: `E[T^{q+1}] ≤ (4q+2) E[V_q T^q]`.  The diagonal
term of the integration by parts is `2E[V_qT^q]`; the cross term is at most `4qE[V_qT^q]`. -/
theorem momTpow_succ_le (hG : GaussIBP d) (q : ℕ) :
    C.momTpow (q + 1) ≤ (4 * (q : ℝ) + 2) * ∫ ω, C.Vq ω * C.Tq ω ^ q ∂(P d) := by
  set I1 : ℝ := ∫ ω, C.Vq ω * C.Tq ω ^ q ∂(P d) with hI1
  have hiVT := C.integrable_Vq_mul_Tq_pow hG q
  have hiCross : Integrable (C.crossT q) (P d) := (C.tameCrossT q).integrable hG
  have hiW : ∀ l : κ, Integrable (fun ω => (C.w l : ℂ) *
      C.wirtVal l (C.ZA q l ω) (C.ZB q l ω)) (P d) :=
    fun l => ((Tame.const (d := d) ((C.w l : ℂ))).mul (C.tameWirt q l)).integrable hG
  have hiDiag : Integrable (fun ω : Ω d => ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ)) (P d) := by
    have : (fun ω : Ω d => ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ))
        = fun ω => ((2 * (C.Vq ω * C.Tq ω ^ q) : ℝ) : ℂ) := by
      funext ω; norm_num; ring_nf
    rw [this]
    exact (MeasureTheory.Integrable.ofReal (hiVT.const_mul 2))
  -- the complex identity
  have hId : ((C.momTpow (q + 1) : ℝ) : ℂ)
      = ((2 * I1 : ℝ) : ℂ) + ∫ ω, C.crossT q ω ∂(P d) := by
    have h1 : ((C.momTpow (q + 1) : ℝ) : ℂ) = ∫ ω, ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) ∂(P d) := by
      rw [momTpow, ← integral_ofReal']
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun ω => Complex.ofReal_pow _ _)
    have h2 : ∑ l, (C.w l : ℂ) * ∫ ω, C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(P d)
        = ∫ ω, ∑ l, (C.w l : ℂ) * C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(P d) := by
      rw [MeasureTheory.integral_finsetSum _ fun l _ => hiW l]
      exact Finset.sum_congr rfl fun l _ => (MeasureTheory.integral_const_mul _ _).symm
    have h3 : ∫ ω, ∑ l, (C.w l : ℂ) * C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(P d)
        = ∫ ω, (((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) + C.crossT q ω) ∂(P d) :=
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun ω => sum_w_wirtVal_ZA_ZB q ω)
    have h4 : ∫ ω, (((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) + C.crossT q ω) ∂(P d)
        = ((2 * I1 : ℝ) : ℂ) + ∫ ω, C.crossT q ω ∂(P d) := by
      rw [MeasureTheory.integral_add hiDiag hiCross]
      congr 1
      rw [integral_ofReal']
      congr 1
      rw [hI1, ← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [h1, integral_Tq_pow_succ hG, h2, h3, h4]
  -- the cross term is small
  have hcross : ‖∫ ω, C.crossT q ω ∂(P d)‖ ≤ 4 * (q : ℝ) * I1 := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    calc ∫ ω, ‖C.crossT q ω‖ ∂(P d)
        ≤ ∫ ω, 4 * (q : ℝ) * (C.Vq ω * C.Tq ω ^ q) ∂(P d) :=
          MeasureTheory.integral_mono hiCross.norm (hiVT.const_mul (4 * (q : ℝ)))
            (fun ω => (norm_crossT_le (C := C) q ω).trans_eq (by ring))
      _ = 4 * (q : ℝ) * I1 := by
          rw [hI1, MeasureTheory.integral_const_mul]
  have hsub : ((C.momTpow (q + 1) - 2 * I1 : ℝ) : ℂ) = ∫ ω, C.crossT q ω ∂(P d) := by
    rw [Complex.ofReal_sub, hId]; ring
  have habs : |C.momTpow (q + 1) - 2 * I1| ≤ 4 * (q : ℝ) * I1 := by
    have := hcross
    rw [← hsub, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have := (abs_le.1 habs).2
  linarith

end RowChaos

end RBM.Gauss
