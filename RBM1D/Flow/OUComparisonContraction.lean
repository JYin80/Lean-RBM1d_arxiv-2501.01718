/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.OUComparisonHessian

/-!
# Centered Hessian contraction for the Green comparison

This file records deterministic pointwise contractions only.  It makes no assertion about an
OU expectation, a time integral, or a Brownian path.
-/

namespace RBM

open Matrix
open scoped ComplexConjugate

noncomputable def paperK1Contraction {d : Gauss.Dims} (N : ℕ)
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) (z : ℂ) (σ τ : Bool) : ℂ :=
  (Fintype.card (d.Idx N) : ℂ)⁻¹ *
    ∑ a : d.Idx N, ∑ b : d.Idx N,
      ((signedGreen H z σ * signedGreen H z σ) a a) *
        (centeredVarianceEntry d N a b : ℂ) * (signedGreen H z τ) b b

noncomputable def paperK2Contraction {d : Gauss.Dims} (N : ℕ)
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) (z₁ z₂ : ℂ) (σ τ : Bool) : ℂ :=
  (Fintype.card (d.Idx N) : ℂ)⁻¹ * (Fintype.card (d.Idx N) : ℂ)⁻¹ *
    ∑ a : d.Idx N, ∑ b : d.Idx N,
      ((signedGreen H z₁ σ * signedGreen H z₁ σ) a b) *
        (centeredVarianceEntry d N a b : ℂ) *
          ((signedGreen H z₂ τ * signedGreen H z₂ τ) b a)

theorem centeredVariance_single_contraction_eq {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    (∑ a : d.Idx N, ∑ b : d.Idx N,
      (centeredVarianceEntry d N a b : ℂ) *
        Gauss.wirtSecond d N (fun K => (stieltjes K z).im) H a b) =
      ((2 * (paperK1Contraction N H z true true).im : ℝ) : ℂ) := by
  -- The second resolvent term agrees with the first after a simultaneous index swap.
  have hswap : (∑ a : d.Idx N, ∑ b : d.Idx N,
      (centeredVarianceEntry d N a b : ℂ) *
        ((green H z * green H z) b b * (green H z) a a)) =
      ∑ a : d.Idx N, ∑ b : d.Idx N,
        (centeredVarianceEntry d N a b : ℂ) *
          ((green H z * green H z) a a * (green H z) b b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [centeredVarianceEntry_symm]
  have hsum : (∑ a : d.Idx N, ∑ b : d.Idx N,
      (centeredVarianceEntry d N a b : ℂ) *
        ((green H z * green H z) a a * (green H z) b b +
          (green H z * green H z) b b * (green H z) a a)) =
      2 * ∑ a : d.Idx N, ∑ b : d.Idx N,
        (centeredVarianceEntry d N a b : ℂ) *
          ((green H z * green H z) a a * (green H z) b b) := by
    calc
      _ = ∑ a : d.Idx N,
          ((∑ b : d.Idx N, (centeredVarianceEntry d N a b : ℂ) *
              ((green H z * green H z) a a * (green H z) b b)) +
            ∑ b : d.Idx N, (centeredVarianceEntry d N a b : ℂ) *
              ((green H z * green H z) b b * (green H z) a a)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = (∑ a : d.Idx N, ∑ b : d.Idx N,
            (centeredVarianceEntry d N a b : ℂ) *
              ((green H z * green H z) a a * (green H z) b b)) +
          ∑ a : d.Idx N, ∑ b : d.Idx N,
            (centeredVarianceEntry d N a b : ℂ) *
              ((green H z * green H z) b b * (green H z) a a) := by
            rw [Finset.sum_add_distrib]
      _ = _ := by rw [hswap]; ring
  have hcomplex :
      ∑ a : d.Idx N, ∑ b : d.Idx N,
        (centeredVarianceEntry d N a b : ℂ) *
          ((Fintype.card (d.Idx N) : ℂ)⁻¹ *
            ((green H z * green H z) a a * (green H z) b b +
              (green H z * green H z) b b * (green H z) a a)) =
      2 * paperK1Contraction N H z true true := by
    dsimp [paperK1Contraction, signedGreen]
    have hXY : (∑ a : d.Idx N, ∑ b : d.Idx N,
        (centeredVarianceEntry d N a b : ℂ) *
          ((green H z * green H z) a a * (green H z) b b)) =
      ∑ a : d.Idx N, ∑ b : d.Idx N,
        (green H z * green H z) a a *
          (centeredVarianceEntry d N a b : ℂ) * (green H z) b b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    calc
      ∑ a : d.Idx N, ∑ b : d.Idx N,
          (centeredVarianceEntry d N a b : ℂ) *
            ((Fintype.card (d.Idx N) : ℂ)⁻¹ *
              ((green H z * green H z) a a * (green H z) b b +
                (green H z * green H z) b b * (green H z) a a))
          = (Fintype.card (d.Idx N) : ℂ)⁻¹ *
              ∑ a : d.Idx N, ∑ b : d.Idx N,
                (centeredVarianceEntry d N a b : ℂ) *
                  ((green H z * green H z) a a * (green H z) b b +
                    (green H z * green H z) b b * (green H z) a a) := by
              calc
                _ = ∑ a : d.Idx N,
                    ((Fintype.card (d.Idx N) : ℂ)⁻¹ *
                      ∑ b : d.Idx N, (centeredVarianceEntry d N a b : ℂ) *
                        ((green H z * green H z) a a * (green H z) b b +
                          (green H z * green H z) b b * (green H z) a a)) := by
                      apply Finset.sum_congr rfl
                      intro a _
                      calc
                        _ = ∑ b : d.Idx N, (Fintype.card (d.Idx N) : ℂ)⁻¹ *
                            ((centeredVarianceEntry d N a b : ℂ) *
                              ((green H z * green H z) a a * (green H z) b b +
                                (green H z * green H z) b b * (green H z) a a)) := by
                              apply Finset.sum_congr rfl
                              intro b _
                              ring
                        _ = _ := (Finset.mul_sum _ _ _).symm
                _ = _ := (Finset.mul_sum _ _ _).symm
      _ = (Fintype.card (d.Idx N) : ℂ)⁻¹ *
            (2 * ∑ a : d.Idx N, ∑ b : d.Idx N,
              (centeredVarianceEntry d N a b : ℂ) *
                ((green H z * green H z) a a * (green H z) b b)) := by rw [hsum]
      _ = 2 * ((Fintype.card (d.Idx N) : ℂ)⁻¹ *
            ∑ a : d.Idx N, ∑ b : d.Idx N,
              (green H z * green H z) a a *
                (centeredVarianceEntry d N a b : ℂ) * (green H z) b b) := by
              calc
                _ = 2 * ((Fintype.card (d.Idx N) : ℂ)⁻¹ *
                      ∑ a : d.Idx N, ∑ b : d.Idx N,
                        (centeredVarianceEntry d N a b : ℂ) *
                          ((green H z * green H z) a a * (green H z) b b)) := by ring
                _ = _ := congrArg
                  (fun w : ℂ => 2 * ((Fintype.card (d.Idx N) : ℂ)⁻¹ * w)) hXY
  have him := congrArg Complex.im hcomplex
  have hpoint (a b : d.Idx N) :
      (centeredVarianceEntry d N a b : ℂ) *
          Gauss.wirtSecond d N (fun K => (stieltjes K z).im) H a b =
        (((centeredVarianceEntry d N a b : ℂ) *
          ((Fintype.card (d.Idx N) : ℂ)⁻¹ *
            ((green H z * green H z) a a * (green H z) b b +
              (green H z * green H z) b b * (green H z) a a))).im : ℂ) := by
    rw [wirtSecond_stieltjesIm_entry_formula hH z hz]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  calc
    _ = ∑ a : d.Idx N, ∑ b : d.Idx N,
          (((centeredVarianceEntry d N a b : ℂ) *
            ((Fintype.card (d.Idx N) : ℂ)⁻¹ *
              ((green H z * green H z) a a * (green H z) b b +
                (green H z * green H z) b b * (green H z) a a))).im : ℂ) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            exact hpoint a b
    _ = ((∑ a : d.Idx N, ∑ b : d.Idx N,
          (centeredVarianceEntry d N a b : ℂ) *
            ((Fintype.card (d.Idx N) : ℂ)⁻¹ *
              ((green H z * green H z) a a * (green H z) b b +
                (green H z * green H z) b b * (green H z) a a))).im : ℝ) := by
          simp [Complex.im_sum]
    _ = ((2 * (paperK1Contraction N H z true true).im : ℝ) : ℂ) := by
          simpa [Complex.mul_im] using congrArg (fun x : ℝ => (x : ℂ)) him

theorem centeredVariance_wirtingerFirst_product_eq {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z₁ z₂ : ℂ) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) :
    (∑ a : d.Idx N, ∑ b : d.Idx N,
      (centeredVarianceEntry d N a b : ℂ) *
        stieltjesImWirtingerFirst H z₁ a b * stieltjesImWirtingerFirst H z₂ b a) =
      -(1 / 4 : ℂ) *
        (paperK2Contraction N H z₁ z₂ true true -
          paperK2Contraction N H z₁ z₂ true false -
          paperK2Contraction N H z₁ z₂ false true +
          paperK2Contraction N H z₁ z₂ false false) := by
  let q : ℂ := (Fintype.card (d.Idx N) : ℂ)⁻¹
  let c : ℂ := Complex.I * q / 2
  let A : d.Idx N → d.Idx N → ℂ := fun a b =>
    (green H z₁ * green H z₁) b a -
      (green H ((starRingEnd ℂ) z₁) * green H ((starRingEnd ℂ) z₁)) b a
  let B : d.Idx N → d.Idx N → ℂ := fun a b =>
    (green H z₂ * green H z₂) a b -
      (green H ((starRingEnd ℂ) z₂) * green H ((starRingEnd ℂ) z₂)) a b
  have hswap : (∑ a : d.Idx N, ∑ b : d.Idx N,
      (centeredVarianceEntry d N a b : ℂ) * A a b * B a b) =
      ∑ a : d.Idx N, ∑ b : d.Idx N,
        (centeredVarianceEntry d N a b : ℂ) * A b a * B b a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [centeredVarianceEntry_symm]
  have hfour :
      (∑ a : d.Idx N, ∑ b : d.Idx N,
        (centeredVarianceEntry d N a b : ℂ) * A b a * B b a) =
        (∑ a : d.Idx N, ∑ b : d.Idx N,
          (green H z₁ * green H z₁) a b *
            (centeredVarianceEntry d N a b : ℂ) *
              (green H z₂ * green H z₂) b a) -
        (∑ a : d.Idx N, ∑ b : d.Idx N,
          (green H z₁ * green H z₁) a b *
            (centeredVarianceEntry d N a b : ℂ) *
              (green H ((starRingEnd ℂ) z₂) * green H ((starRingEnd ℂ) z₂)) b a) -
        (∑ a : d.Idx N, ∑ b : d.Idx N,
          (green H ((starRingEnd ℂ) z₁) * green H ((starRingEnd ℂ) z₁)) a b *
            (centeredVarianceEntry d N a b : ℂ) *
              (green H z₂ * green H z₂) b a) +
        ∑ a : d.Idx N, ∑ b : d.Idx N,
          (green H ((starRingEnd ℂ) z₁) * green H ((starRingEnd ℂ) z₁)) a b *
            (centeredVarianceEntry d N a b : ℂ) *
              (green H ((starRingEnd ℂ) z₂) * green H ((starRingEnd ℂ) z₂)) b a := by
    have hsumEq (f : d.Idx N → d.Idx N → ℂ) :
        (∑ a : d.Idx N, ∑ b : d.Idx N, f a b) =
          ∑ p : d.Idx N × d.Idx N, f p.1 p.2 :=
      (Fintype.sum_prod_type (fun p : d.Idx N × d.Idx N => f p.1 p.2)).symm
    calc
      _ = ∑ a : d.Idx N, ∑ b : d.Idx N,
          (centeredVarianceEntry d N a b : ℂ) *
            ((green H z₁ * green H z₁) a b -
              (green H ((starRingEnd ℂ) z₁) * green H ((starRingEnd ℂ) z₁)) a b) *
            ((green H z₂ * green H z₂) b a -
              (green H ((starRingEnd ℂ) z₂) * green H ((starRingEnd ℂ) z₂)) b a) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            simp [A, B]
      _ = ∑ a : d.Idx N, ∑ b : d.Idx N,
          ((green H z₁ * green H z₁) a b *
              (centeredVarianceEntry d N a b : ℂ) *
                (green H z₂ * green H z₂) b a -
            (green H z₁ * green H z₁) a b *
              (centeredVarianceEntry d N a b : ℂ) *
                (green H ((starRingEnd ℂ) z₂) * green H ((starRingEnd ℂ) z₂)) b a -
            (green H ((starRingEnd ℂ) z₁) * green H ((starRingEnd ℂ) z₁)) a b *
              (centeredVarianceEntry d N a b : ℂ) *
                (green H z₂ * green H z₂) b a +
            (green H ((starRingEnd ℂ) z₁) * green H ((starRingEnd ℂ) z₁)) a b *
              (centeredVarianceEntry d N a b : ℂ) *
                (green H ((starRingEnd ℂ) z₂) * green H ((starRingEnd ℂ) z₂)) b a) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ∑ p : d.Idx N × d.Idx N,
          ((green H z₁ * green H z₁) p.1 p.2 *
              (centeredVarianceEntry d N p.1 p.2 : ℂ) *
                (green H z₂ * green H z₂) p.2 p.1 -
            (green H z₁ * green H z₁) p.1 p.2 *
              (centeredVarianceEntry d N p.1 p.2 : ℂ) *
                (green H ((starRingEnd ℂ) z₂) * green H ((starRingEnd ℂ) z₂)) p.2 p.1 -
            (green H ((starRingEnd ℂ) z₁) * green H ((starRingEnd ℂ) z₁)) p.1 p.2 *
              (centeredVarianceEntry d N p.1 p.2 : ℂ) *
                (green H z₂ * green H z₂) p.2 p.1 +
            (green H ((starRingEnd ℂ) z₁) * green H ((starRingEnd ℂ) z₁)) p.1 p.2 *
              (centeredVarianceEntry d N p.1 p.2 : ℂ) *
                (green H ((starRingEnd ℂ) z₂) * green H ((starRingEnd ℂ) z₂)) p.2 p.1) := by
            rw [hsumEq]
      _ = _ := by
        rw [hsumEq (fun a b => (green H z₁ * green H z₁) a b *
            (centeredVarianceEntry d N a b : ℂ) * (green H z₂ * green H z₂) b a),
          hsumEq (fun a b => (green H z₁ * green H z₁) a b *
            (centeredVarianceEntry d N a b : ℂ) *
              (green H ((starRingEnd ℂ) z₂) * green H ((starRingEnd ℂ) z₂)) b a),
          hsumEq (fun a b => (green H ((starRingEnd ℂ) z₁) *
            green H ((starRingEnd ℂ) z₁)) a b *
              (centeredVarianceEntry d N a b : ℂ) * (green H z₂ * green H z₂) b a),
          hsumEq (fun a b => (green H ((starRingEnd ℂ) z₁) *
            green H ((starRingEnd ℂ) z₁)) a b *
              (centeredVarianceEntry d N a b : ℂ) *
                (green H ((starRingEnd ℂ) z₂) * green H ((starRingEnd ℂ) z₂)) b a)]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hfactor :
      (∑ a : d.Idx N, ∑ b : d.Idx N,
        (centeredVarianceEntry d N a b : ℂ) * (c * A a b) * (c * B a b)) =
      (c * c) * ∑ a : d.Idx N, ∑ b : d.Idx N,
        (centeredVarianceEntry d N a b : ℂ) * A a b * B a b := by
    calc
      _ = ∑ a : d.Idx N, ∑ b : d.Idx N,
          (c * c) * ((centeredVarianceEntry d N a b : ℂ) * A a b * B a b) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = ∑ a : d.Idx N,
          ((c * c) * ∑ b : d.Idx N,
            (centeredVarianceEntry d N a b : ℂ) * A a b * B a b) := by
            apply Finset.sum_congr rfl
            intro a _
            exact (Finset.mul_sum _ _ _).symm
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hc : c * c = -(q * q / 4) := by
    calc
      c * c = (Complex.I * Complex.I) * (q * q) / 4 := by dsimp [c]; ring
      _ = -(q * q / 4) := by rw [Complex.I_mul_I]; ring
  rw [show (∑ a : d.Idx N, ∑ b : d.Idx N,
      (centeredVarianceEntry d N a b : ℂ) *
        stieltjesImWirtingerFirst H z₁ a b * stieltjesImWirtingerFirst H z₂ b a) =
      ∑ a : d.Idx N, ∑ b : d.Idx N,
        (centeredVarianceEntry d N a b : ℂ) * (c * A a b) * (c * B a b) from by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [stieltjesImWirtingerFirst_adjoint_formula hH z₁ hz₁,
          stieltjesImWirtingerFirst_adjoint_formula hH z₂ hz₂]
        ]
  rw [hfactor, hc, hswap, hfour]
  simp only [paperK2Contraction, signedGreen, ↓reduceIte]
  dsimp [q]
  ring

end RBM
