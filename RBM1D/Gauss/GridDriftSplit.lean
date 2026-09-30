/-
Copyright (c) 2026. All rights reserved.

The unmerged and split drift bound on the goodSet.
-/
import RBM1D.Gauss.Step2Plain

/-!
# Unmerged and split drift from the goodSet

`drift_of_goodSet'` (Step2Plain) bounds the grid drift `D_j` by a single merged coefficient,
whose far part `A^{-3/7} thr³` is hard-wired to the Step 2 threshold `thr`. For Step 5
((2.79), two passes at the stopping levels `thr` and `thrFar = N^δ (η_s/η_u)^{13/4}`) the three
pieces of the paper's (5.35) + (5.34)/(5.50) are kept apart:

* `drNear`: the near field `η_u⁻¹ c_near r³` of (5.35), carried by the near indicator
  `1(d ≤ ℓ*_u)`;
* `drRes ρ`: the (5.54) residue `r (ℓ_u η_u)⁻¹ L ρ`, rescaled to `T_{u,D}` on `d ≤ ℓ*_u`
  (`A_u⁻² ≤ e^{(log W)^{3/4}} T_{u,D}`), also carried by the near indicator;
* `drFar Λ`: the unmerged far field of (5.35) at the jG-level `N^{2ε} Λ` plus the quadratic
  (5.34)/(5.50) term at `thr`.

Here `r = 4 N^ζ ℓ_u/ℓ_s`, `A_u = scale = W ℓ_u η_u`, and `Λ` is any level with
`jS ≤ Λ ≤ thr`. The merged coefficient of `drift_of_goodSet'` is not used.
-/

namespace RBM.Gauss.Grid

open Real Finset RBM RBM.Step2FarInputs

section Defs

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- near part of (5.35) (supported on d ≤ ℓ*_u) -/
noncomputable def drNear (B : Band Ω') (E : ℝ) (s : ℕ → ℝ) (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (etaT E u)⁻¹ * Lemma57.cNear (B.W N : ℝ) (B.ell N u) *
    (4 * (N : ℝ) ^ ζ * B.ell N u / B.ell N (s N)) ^ 3

/-- the ρ-residue of `rhs535'`, rescaled to T (also supported on d ≤ ℓ*_u) -/
noncomputable def drRes (B : Band Ω') (E : ℝ) (s : ℕ → ℝ) (ζ : ℝ) (N : ℕ) (u ρ : ℝ) : ℝ :=
  4 * (N : ℝ) ^ ζ * B.ell N u / B.ell N (s N) * (B.ell N u * etaT E u)⁻¹ * (B.L N : ℝ) * ρ *
    (Real.exp (Real.log (B.W N : ℝ) ^ ((3 : ℝ) / 4)) * B.scale E N u ^ 2)

/-- far part: unmerged (5.35) at jG-level `N^{2ε}Λ`, plus (5.34)/(5.50) at `thr` -/
noncomputable def drFar (B : Band Ω') (E : ℝ) (s : ℕ → ℝ) (δ ε ζ D Λ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (etaT E u)⁻¹ * (Lemma57.cFar (B.W N : ℝ) (B.ell N u) *
      (4 * (N : ℝ) ^ ζ * B.ell N u / B.ell N (s N)) ^ ((3 : ℝ) / 2) *
        (√(B.scale E N u))⁻¹ * ((N : ℝ) ^ (2 * ε) * Λ)
    + 169 * (4 * (N : ℝ) ^ ζ * B.ell N u / B.ell N (s N)) * (B.scale E N u)⁻¹ *
        ((N : ℝ) ^ (2 * ε) * Λ) ^ ((3 : ℝ) / 2))
  + Real.exp 1 * Step2.thr E s δ N u ^ 2 *
      (36 * ((etaT E u)⁻¹ * (B.scale E N u)⁻¹) + (B.W N : ℝ) * B.L N * (B.W N : ℝ) ^ (-D))

namespace DrSplit

/-- `x^{3/2} = x √x` for `x ≥ 0`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * √x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- `4 N^ζ ℓ_u / ℓ_s = ℓ_u / (ℓ_s / (4 N^ζ))` (valid in any field). -/
theorem ratio_eq (g a b : ℝ) : g * a / b = a / (b / g) := by
  rw [div_div_eq_mul_div, mul_comm g a]

end DrSplit

end Defs

/-! ### `thrFar ≤ thr` -/

/-! ### (T2) the split drift bound on the goodSet -/

section Split

open MeasureTheory ProbabilityTheory Filter Matrix RBM DrSplit DriftPt

variable (d : Dims)

set_option linter.unusedVariables false in
/-- **`drift_of_goodSet_split`.** The hypotheses of `drift_of_goodSet'` with `hjS` split
through a level `Λ` (`jS ≤ Λ ≤ thr`). The drift is bounded by the near part `drNear` and the
residue `drRes ρ₀` (`ρ₀ = 2 η_u⁻¹ N^{2ε}Λ W^{-D}`), both on the near band `d ≤ ℓ*_u`, plus the
unmerged far part `drFar` at the jG-level `N^{2ε}Λ` (quadratic term at `thr`). -/
theorem drift_of_goodSet_split {E : ℝ} (hE : |E| < 2) {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ}
    {ω : Ωg d} {δ ε ζ D τ₁ Λ : ℝ}
    (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N) (hsv : s N ≤ time s u K N j)
    (hv1 : time s u K N j < 1)
    (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ) (hζ0 : 0 ≤ ζ) (hD : 8 + 2 * ζ ≤ D)
    (hW8 : 8 ≤ ((band d).W N : ℝ)) (hLW : ((band d).L N : ℝ) ≤ (band d).W N)
    (hNW : (N : ℝ) ≤ ((band d).W N : ℝ) ^ 2) (hlog : 2 * D ^ 2 ≤ Real.log ((band d).W N : ℝ))
    (hJA : (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N (time s u K N j) ≤
      (band d).scale E N (time s u K N j))
    (hDreg : ((band d).L N : ℝ) * √(((band d).W N : ℝ) ^ (-D)) ≤
      (band d).ell N (time s u K N j) * ((band d).scale E N (time s u K N j))⁻¹)
    (hG : H d s u K N j ω ∈
      goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζ ζ (ζ / 2) D)
    (hR : H d s u K N j ω ∈ rowSet d E N (time s u K N j) ((band d).ell N (s N)) (ζ / 2))
    (hjS : jSMat d E D N (time s u K N j) (H d s u K N j ω) ≤ Λ)
    (hΛ : Λ ≤ Step2.thr E s δ N (time s u K N j)) :
    ∀ b : LoopArg ((band d).L N) 2, ‖Dgrid (band d) E s u K N j ω b‖ ≤
      ((drNear (band d) E s ζ N (time s u K N j)
          + drRes (band d) E s ζ N (time s u K N j)
              (2 * (etaT E (time s u K N j))⁻¹ * ((N : ℝ) ^ (2 * ε) * Λ)
                * ((band d).W N : ℝ) ^ (-D)))
          * (if (zdist ((band d).L N) (b 0 - b 1) : ℝ)
                ≤ ellStar ((band d).W N : ℝ) ((band d).ell N (time s u K N j)) then 1 else 0)
        + drFar (band d) E s δ ε ζ D Λ N (time s u K N j)) *
      Step2.tT (band d) E N D (time s u K N j) (zdist ((band d).L N) (b 0 - b 1)) := by
  intro b
  have hofn : List.ofFn b = [b 0, b 1] := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]; rfl
  set v := time s u K N j with hv
  set M := H d s u K N j ω with hMdef
  have hM : M.IsHermitian := H_isHermitian d s u K N j ω
  obtain ⟨⟨⟨⟨⟨_hqv, hjg⟩, hh554⟩, hone⟩, h273⟩, h557⟩ := hG
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hℓs1 : 1 ≤ (band d).ell N (s N) := one_le_ellHat_of_nonneg ((band d).one_le_L N) hs0 hs1
  have hℓs0 : 0 < (band d).ell N (s N) := by linarith
  have hℓv1 : 1 ≤ (band d).ell N v := one_le_ellHat_of_nonneg ((band d).one_le_L N) hv0 hv1
  have hA0 : 0 < (band d).scale E N v := (band d).scale_pos' hE N hv0 hv1
  have hNz : 1 ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hN1 hζ0
  set g := 4 * (N : ℝ) ^ ζ with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have e : (band d).ell N v / ((band d).ell N (s N) / g)
      = g * ((band d).ell N v / (band d).ell N (s N)) := by
    field_simp
  have hrat0 : 0 ≤ (band d).ell N v / (band d).ell N (s N) := by positivity
  -- `h273`
  have h273' : ∀ x y c : ZMod ((band d).L N),
      ‖gloop ((band d).L N) ((band d).W N) M (zt E v) ⟨[false, true, true], [y, c, x]⟩‖
        ≤ ((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹ := by
    intro x y c
    have h := h273 ((![false, true, true], ![y, c, x]) : LoopData (d.L N) 3)
    have hidx : LoopData.idx ((![false, true, true], ![y, c, x]) : LoopData (d.L N) 3)
        = ⟨[false, true, true], [y, c, x]⟩ := by
      simp [LoopData.idx, List.ofFn_succ]
    rw [hidx] at h
    refine h.trans ?_
    rw [← hg, e, mul_pow, inv_pow]
    have hNg : (N : ℝ) ^ ζ ≤ g ^ 2 := by rw [hg]; nlinarith
    have h0 : 0 ≤ ((band d).ell N v / (band d).ell N (s N)) ^ 2 * (((band d).scale E N v) ^ 2)⁻¹ :=
      by positivity
    calc (N : ℝ) ^ ζ * ((band d).ell N v / (band d).ell N (s N)) ^ (3 - 1) *
          (((band d).scale E N v) ^ (3 - 1))⁻¹
        = (N : ℝ) ^ ζ * (((band d).ell N v / (band d).ell N (s N)) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹) := by norm_num; ring
      _ ≤ g ^ 2 * (((band d).ell N v / (band d).ell N (s N)) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹) := mul_le_mul_of_nonneg_right hNg h0
      _ = g ^ 2 * ((band d).ell N v / (band d).ell N (s N)) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹ := by ring
  -- `N^{ζ/2} √(ℓ_v/ℓ_s) ≤ √(ℓ_v/ℓ_s')`
  have hsq : (N : ℝ) ^ (ζ / 2) ≤ Real.sqrt g := by
    have e2 : (N : ℝ) ^ (ζ / 2) = Real.sqrt ((N : ℝ) ^ ζ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]; ring_nf
    rw [e2]
    exact Real.sqrt_le_sqrt (by rw [hg]; linarith)
  have hkey : (N : ℝ) ^ (ζ / 2) * Real.sqrt ((band d).ell N v / (band d).ell N (s N)) ≤
      Real.sqrt ((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) := by
    rw [← hg, e, Real.sqrt_mul hg0.le]
    exact mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
  have hisq0 : 0 ≤ (Real.sqrt ((band d).scale E N v))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have h557C : ∀ (x y : ZMod ((band d).L N)) (p : (band d).Idx N), p.1 = y →
      ∑ r : (band d).Idx N, Lemma57.blkW ((band d).L N) ((band d).W N) r x *
          ‖green M (zt E v) r p‖ ≤
        √((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) *
          (√((band d).scale E N v))⁻¹ := by
    intro x y p hp
    exact (h557 x y p hp).trans (mul_le_mul_of_nonneg_right hkey hisq0)
  have h557R : ∀ (x y : ZMod ((band d).L N)) (r : (band d).Idx N), r.1 = x →
      ∑ p : (band d).Idx N, Lemma57.blkW ((band d).L N) ((band d).W N) p y *
          ‖green M (zt E v) r p‖ ≤
        √((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) *
          (√((band d).scale E N v))⁻¹ := by
    intro x y r hr
    exact (hR x y r hr).trans (mul_le_mul_of_nonneg_right hkey hisq0)
  -- `hone`, `hκ`
  have hone' : ∀ (σ : Bool) (b' : ZMod (d.L N)), ‖Matrix.trace ((Gsig M (zt E v) σ
        - mSigma E σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b')‖
      ≤ ((N : ℝ) ^ ζ * (2 * ((band d).ell N v / (band d).ell N (s N)))) *
        ((band d).scale E N v)⁻¹ := by
    intro σ b'
    exact (hone σ b').trans (le_of_eq (by ring))
  have hκ : 2 * ((N : ℝ) ^ ζ * (2 * ((band d).ell N v / (band d).ell N (s N)))) ≤
      (band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ)) := by
    rw [← hg, e, hg]; apply le_of_eq; ring
  -- scalar facts
  have hW0 : (0 : ℝ) < ((band d).W N : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by linarith
  have hL3 : 3 ≤ (band d).L N := (band d).three_le_L N
  have hη0 : 0 < etaT E v := etaT_pos_of_lt_one' hE hv1
  have hℓv0 : 0 < (band d).ell N v := by linarith
  have hℓs'0 : 0 < (band d).ell N (s N) / (4 * (N : ℝ) ^ ζ) := div_pos hℓs0 (by linarith)
  have hr01 : 1 ≤ (band d).ell N v / (band d).ell N (s N) := by
    have hℓsv : (band d).ell N (s N) ≤ (band d).ell N v := Step3.ellHat_mono hsv hv1
    rw [le_div_iff₀ hℓs0]; linarith
  have hr : 1 ≤ (band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ)) := by
    rw [← hg, e]; exact one_le_mul_of_one_le_of_one_le (by rw [hg]; linarith) hr01
  -- the level `J = N^{2ε} Λ`
  have hjS1 : 1 ≤ jSMat d E D N v M := by
    unfold jSMat; exact Step2.one_le_jStar hW0 (fun a => norm_nonneg _)
  have hΛ1 : 1 ≤ Λ := hjS1.trans hjS
  have hy1 : 1 ≤ (N : ℝ) ^ (2 * ε) := Real.one_le_rpow hN1 (by linarith)
  have hy0 : 0 ≤ (N : ℝ) ^ (2 * ε) := by linarith
  have hJ1 : 1 ≤ (N : ℝ) ^ (2 * ε) * Λ := one_le_mul_of_one_le_of_one_le hy1 hΛ1
  have hJ0 : 0 ≤ (N : ℝ) ^ (2 * ε) * Λ := by linarith
  have hJthr : (N : ℝ) ^ (2 * ε) * Λ ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N v :=
    mul_le_mul_of_nonneg_left hΛ hy0
  have hA : 1 ≤ ((band d).W N : ℝ) * (band d).ell N v * etaT E v :=
    (hJ1.trans hJthr).trans hJA
  have hjG : jGMat (band d).toDims E N v ((band d).ell N v) (etaT E v) D M
      ≤ (N : ℝ) ^ (2 * ε) * Λ :=
    hjg.trans (mul_le_mul_of_nonneg_left hjS hy0)
  -- `h531`, `h42` at level `J`
  have h531 : ∀ x y : ZMod ((band d).L N),
      ellStar ((band d).W N : ℝ) ((band d).ell N v) / 2 ≤ (zdist ((band d).L N) (x - y) : ℝ) →
        (gloop ((band d).L N) ((band d).W N) M (zt E v) ⟨[true, false], [x, y]⟩).re ≤
          ((N : ℝ) ^ (2 * ε) * Λ) *
            tailT ((band d).W N : ℝ) ((band d).ell N v) (etaT E v) D
              (zdist ((band d).L N) (x - y)) := by
    intro x y hxy
    exact (two_loop_re_le_jGMat (B := band d) (ηu := etaT E v) (D := D) hM x y hxy).trans
      (mul_le_mul_of_nonneg_right hjG (tailT_nonneg hW0.le _))
  have h42 : ∀ x y : ZMod ((band d).L N),
      ellStar ((band d).W N : ℝ) ((band d).ell N v) / 2 ≤ (zdist ((band d).L N) (x - y) : ℝ) →
        gmBlkM (band d) N M (zt E v) x y ≤ √((N : ℝ) ^ (2 * ε) * Λ) *
          √(tailT ((band d).W N : ℝ) ((band d).ell N v) (etaT E v) D
            (zdist ((band d).L N) (x - y))) := by
    intro x y hxy
    refine (gmBlkM_le_sqrt_jGMat (B := band d) (ηu := etaT E v) (D := D) hM x y hxy).trans ?_
    rw [← Real.sqrt_mul hJ0]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hjG (tailT_nonneg hW0.le _))
  -- `ρ = ρ(jG) ≤ ρ₀`
  set ρ := rho554 d E N v D (jGMat d E N v ((band d).ell N v) (etaT E v) D M) with hρdef
  set ρ₀ := 2 * (etaT E v)⁻¹ * ((N : ℝ) ^ (2 * ε) * Λ) * ((band d).W N : ℝ) ^ (-D) with hρ₀def
  have hjG1 : 1 ≤ jGMat d E N v ((band d).ell N v) (etaT E v) D M :=
    one_le_jGMat' (B := band d) E N v M
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]; unfold rho554
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hη0.le) (by linarith)) (Real.sqrt_nonneg _)
  have hρρ₀ : ρ ≤ ρ₀ :=
    (rho554_mono d E N v D hη0 hjG).trans (rho554_le_two_mul_rpow d E N hη0 hℓv0 hA hlog hJ0)
  -- EG part: `rhs535'` with the indicator kept on the near term and the residue
  set x := b 0 with hx
  set y := b 1 with hy
  set ℓs' := (band d).ell N (s N) / (4 * (N : ℝ) ^ ζ) with hℓs'def
  set T := tailT ((band d).W N : ℝ) ((band d).ell N v) (etaT E v) D
    (zdist ((band d).L N) (x - y)) with hTdef
  have hT0 : 0 ≤ T := tailT_nonneg hW0.le _
  set χ : ℝ := if (zdist ((band d).L N) (x - y) : ℝ)
    ≤ ellStar ((band d).W N : ℝ) ((band d).ell N v) then 1 else 0 with hχdef
  have hχ0 : 0 ≤ χ := by rw [hχdef]; split_ifs <;> norm_num
  -- quadratic part (`primBil`), at `thr` through `jS ≤ Λ ≤ thr` (as in `drift_point_le'`)
  have hjSthr : Step2.jStar ((band d).L N)
      (fun a : LoopArg ((band d).L N) 2 =>
        ‖gloop ((band d).L N) ((band d).W N) M (zt E v) (LoopData.idx (Step2.sigPM, a))
          - (band d).Kval E N v (LoopData.idx (Step2.sigPM, a))‖)
      ((band d).W N) ((band d).ell N v) (etaT E v) D ≤ Step2.thr E s δ N v := hjS.trans hΛ
  have hquadEq := quadGlue_pm_eq_eLL_mat (B := band d) E N v M x y
  have hquad := Step2.norm_eLL_le hL3 hW0 hℓv1 hη0 D
    (fun a : LoopArg ((band d).L N) 2 =>
      gloop ((band d).L N) ((band d).W N) M (zt E v) (LoopData.idx (Step2.sigPM, a))
        - (band d).Kval E N v (LoopData.idx (Step2.sigPM, a))) ![x, y]
  have hJstarNonneg : 0 ≤ Step2.jStar ((band d).L N)
      (fun a : LoopArg ((band d).L N) 2 => ‖gloop ((band d).L N) ((band d).W N) M (zt E v)
          (LoopData.idx (Step2.sigPM, a)) - (band d).Kval E N v (LoopData.idx (Step2.sigPM, a))‖)
      ((band d).W N) ((band d).ell N v) (etaT E v) D :=
    (Step2.one_le_jStar hW0 (fun a => norm_nonneg _)).trans' (by norm_num)
  have hjSsq : Step2.jStar ((band d).L N)
      (fun a : LoopArg ((band d).L N) 2 => ‖gloop ((band d).L N) ((band d).W N) M (zt E v)
          (LoopData.idx (Step2.sigPM, a)) - (band d).Kval E N v (LoopData.idx (Step2.sigPM, a))‖)
      ((band d).W N) ((band d).ell N v) (etaT E v) D ^ 2 ≤ Step2.thr E s δ N v ^ 2 :=
    pow_le_pow_left₀ hJstarNonneg hjSthr 2
  have hxy01 : (![x, y] : LoopArg ((band d).L N) 2) 0 - (![x, y] : LoopArg ((band d).L N) 2) 1
      = x - y := by simp
  have hquadfinal : ‖primBil ((band d).L N) ((band d).W N)
      (gloop ((band d).L N) ((band d).W N) M (zt E v) - (band d).Kval E N v)
      (gloop ((band d).L N) ((band d).W N) M (zt E v) - (band d).Kval E N v)
      ⟨[true, false], [x, y]⟩‖ ≤
      exp 1 * Step2.thr E s δ N v ^ 2 *
          (36 * ((etaT E v)⁻¹ * (((band d).W N : ℝ) * (band d).ell N v * etaT E v)⁻¹)
            + ((band d).W N : ℝ) * ((band d).L N : ℝ) * ((band d).W N : ℝ) ^ (-D)) * T := by
    rw [hquadEq]
    refine hquad.trans ?_
    rw [hxy01]
    have he0 : (0 : ℝ) ≤ exp 1 := (exp_pos 1).le
    have hbrak0 : (0 : ℝ) ≤ 36 * ((etaT E v)⁻¹ * (((band d).W N : ℝ) * (band d).ell N v
        * etaT E v)⁻¹) + ((band d).W N : ℝ) * ((band d).L N : ℝ) * ((band d).W N : ℝ) ^ (-D) := by
      positivity
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjSsq hbrak0) hT0
    rw [← hTdef]
    linarith [mul_le_mul_of_nonneg_left this he0]
  have hEG := eGpm_le_rhs535_of_jG_mat' (B := band d) (D' := D) (ℓs := ℓs') hM hL3 hW1 hℓv1
    hℓs'0 hη0 hA hr hDreg x y hJ1 hρ0 (h273' x y) (fun c h => hh554 hM x y c h) h531 h42
    h557C h557R hone' hκ
  have hEGmul := rhs535'_le_mul_tailT_near (Wr := ((band d).W N : ℝ))
    (Lr := ((band d).L N : ℝ)) (ℓu := (band d).ell N v) (ℓs := ℓs') (ηu := etaT E v) (D := D)
    (J := (N : ℝ) ^ (2 * ε) * Λ) (ρ := ρ) (d := (zdist ((band d).L N) (x - y) : ℝ))
    hW1 hℓv0 hℓs'0 hη0 hρ0 (Nat.cast_nonneg _)
  set r := (band d).ell N v / ℓs' with hrdef
  set Asc := ((band d).W N : ℝ) * (band d).ell N v * etaT E v with hAscdef
  set ex := exp (log ((band d).W N : ℝ) ^ (3 / 4 : ℝ)) with hexdef
  have hr0 : 0 ≤ r := by linarith
  have hres : r * ((band d).ell N v * etaT E v)⁻¹ * ((band d).L N : ℝ) * ρ * (ex * Asc ^ 2) * χ
      ≤ r * ((band d).ell N v * etaT E v)⁻¹ * ((band d).L N : ℝ) * ρ₀ * (ex * Asc ^ 2) * χ := by
    have hc : 0 ≤ r * ((band d).ell N v * etaT E v)⁻¹ * ((band d).L N : ℝ) :=
      mul_nonneg (mul_nonneg hr0 (inv_nonneg.2 (mul_nonneg hℓv0.le hη0.le))) (Nat.cast_nonneg _)
    have hX : 0 ≤ ex * Asc ^ 2 := mul_nonneg (exp_pos _).le (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρρ₀ hc) hX) hχ0
  have hEGterm : RBM.Gauss.eGterm ((band d).L N) ((band d).W N) (mSigma E) M (zt E v)
      ⟨[true, false], [x, y]⟩
        = EGDef.eGpm ((band d).L N) ((band d).W N) (mSigma E) M (zt E v) x y :=
    eGterm_eq_eGpm (mSigma E) M (zt E v) x y
  have hEGfinal : ‖RBM.Gauss.eGterm ((band d).L N) ((band d).W N) (mSigma E) M (zt E v)
      ⟨[true, false], [x, y]⟩‖ ≤
      ((etaT E v)⁻¹ * (Lemma57.cNear ((band d).W N : ℝ) ((band d).ell N v) * r ^ 3 * χ
            + Lemma57.cFar ((band d).W N : ℝ) ((band d).ell N v) *
                (r * √r * (√Asc)⁻¹ * ((N : ℝ) ^ (2 * ε) * Λ))
            + 169 * (r * Asc⁻¹ * (((N : ℝ) ^ (2 * ε) * Λ) * √((N : ℝ) ^ (2 * ε) * Λ))))
          + r * ((band d).ell N v * etaT E v)⁻¹ * ((band d).L N : ℝ) * ρ₀ * (ex * Asc ^ 2) * χ)
        * T := by
    rw [hEGterm]
    refine (hEG.trans hEGmul).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith [hres]) hT0
  -- assemble
  change ‖RBM.Gauss.eGterm ((band d).L N) ((band d).W N) (mSigma E) M (zt E v)
        (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod ((band d).L N)))
      + primBil ((band d).L N) ((band d).W N)
          (gloop ((band d).L N) ((band d).W N) M (zt E v) - (band d).Kval E N v)
          (gloop ((band d).L N) ((band d).W N) M (zt E v) - (band d).Kval E N v)
          (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod ((band d).L N)))‖ ≤ _
  rw [hofn]
  have htT : Step2.tT (band d) E N D v (zdist ((band d).L N) (x - y)) = T := rfl
  have hr4 : 4 * (N : ℝ) ^ ζ * (band d).ell N v / (band d).ell N (s N) = r := by
    rw [hrdef, hℓs'def]; exact ratio_eq _ _ _
  have hsc : (band d).scale E N v = Asc := rfl
  have hRHS : ((drNear (band d) E s ζ N v + drRes (band d) E s ζ N v ρ₀) * χ
        + drFar (band d) E s δ ε ζ D Λ N v) * T
      = ((etaT E v)⁻¹ * (Lemma57.cNear ((band d).W N : ℝ) ((band d).ell N v) * r ^ 3 * χ
            + Lemma57.cFar ((band d).W N : ℝ) ((band d).ell N v) *
                (r * √r * (√Asc)⁻¹ * ((N : ℝ) ^ (2 * ε) * Λ))
            + 169 * (r * Asc⁻¹ * (((N : ℝ) ^ (2 * ε) * Λ) * √((N : ℝ) ^ (2 * ε) * Λ))))
          + r * ((band d).ell N v * etaT E v)⁻¹ * ((band d).L N : ℝ) * ρ₀ * (ex * Asc ^ 2) * χ)
        * T
      + exp 1 * Step2.thr E s δ N v ^ 2 *
          (36 * ((etaT E v)⁻¹ * Asc⁻¹)
            + ((band d).W N : ℝ) * ((band d).L N : ℝ) * ((band d).W N : ℝ) ^ (-D)) * T := by
    unfold drNear drRes drFar
    rw [hr4, hsc, rpow_three_halves hr0, rpow_three_halves hJ0, hexdef]
    ring
  rw [htT, hRHS]
  exact (norm_add_le _ _).trans (add_le_add hEGfinal hquadfinal)

set_option linter.unusedVariables false in
/-- **`drift_of_goodSet_unmerged`.** Same hypotheses as `drift_of_goodSet_split`; the near
indicator is replaced by `1`. -/
theorem drift_of_goodSet_unmerged {E : ℝ} (hE : |E| < 2) {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ}
    {ω : Ωg d} {δ ε ζ D τ₁ Λ : ℝ}
    (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N) (hsv : s N ≤ time s u K N j)
    (hv1 : time s u K N j < 1)
    (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ) (hζ0 : 0 ≤ ζ) (hD : 8 + 2 * ζ ≤ D)
    (hW8 : 8 ≤ ((band d).W N : ℝ)) (hLW : ((band d).L N : ℝ) ≤ (band d).W N)
    (hNW : (N : ℝ) ≤ ((band d).W N : ℝ) ^ 2) (hlog : 2 * D ^ 2 ≤ Real.log ((band d).W N : ℝ))
    (hJA : (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N (time s u K N j) ≤
      (band d).scale E N (time s u K N j))
    (hDreg : ((band d).L N : ℝ) * √(((band d).W N : ℝ) ^ (-D)) ≤
      (band d).ell N (time s u K N j) * ((band d).scale E N (time s u K N j))⁻¹)
    (hG : H d s u K N j ω ∈
      goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζ ζ (ζ / 2) D)
    (hR : H d s u K N j ω ∈ rowSet d E N (time s u K N j) ((band d).ell N (s N)) (ζ / 2))
    (hjS : jSMat d E D N (time s u K N j) (H d s u K N j ω) ≤ Λ)
    (hΛ : Λ ≤ Step2.thr E s δ N (time s u K N j)) :
    ∀ b : LoopArg ((band d).L N) 2, ‖Dgrid (band d) E s u K N j ω b‖ ≤
      ((drNear (band d) E s ζ N (time s u K N j)
          + drRes (band d) E s ζ N (time s u K N j)
              (2 * (etaT E (time s u K N j))⁻¹ * ((N : ℝ) ^ (2 * ε) * Λ)
                * ((band d).W N : ℝ) ^ (-D)))
          * 1
        + drFar (band d) E s δ ε ζ D Λ N (time s u K N j)) *
      Step2.tT (band d) E N D (time s u K N j) (zdist ((band d).L N) (b 0 - b 1)) := by
  intro b
  set v := time s u K N j with hv
  have h := drift_of_goodSet_split d hE hN1 hs0 hsv hv1 hδ0 hε0 hεδ hζ0 hD hW8 hLW hNW hlog hJA
    hDreg hG hR hjS hΛ b
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (tailT_nonneg (Nat.cast_nonneg _) _))
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hη0 : 0 < etaT E v := etaT_pos_of_lt_one' hE hv1
  have hℓs1 : 1 ≤ (band d).ell N (s N) := one_le_ellHat_of_nonneg ((band d).one_le_L N) hs0 hs1
  have hℓv1 : 1 ≤ (band d).ell N v := one_le_ellHat_of_nonneg ((band d).one_le_L N) hv0 hv1
  have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by linarith
  have hNz : 0 ≤ (N : ℝ) ^ ζ := Real.rpow_nonneg (Nat.cast_nonneg N) ζ
  have hNe : 0 ≤ (N : ℝ) ^ (2 * ε) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hW0 : (0 : ℝ) < ((band d).W N : ℝ) := by linarith
  have hjS1 : 1 ≤ jSMat d E D N v (H d s u K N j ω) := by
    unfold jSMat; exact Step2.one_le_jStar hW0 (fun a => norm_nonneg _)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hWD : 0 ≤ ((band d).W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hA0 : 0 ≤ (band d).scale E N v := ((band d).scale_pos' hE N hv0 hv1).le
  have hcN := Lemma57.cNear_nonneg hW1 (by linarith : (0 : ℝ) < (band d).ell N v)
  have hℓv0 : (0 : ℝ) < (band d).ell N v := by linarith
  have hℓs0 : (0 : ℝ) < (band d).ell N (s N) := by linarith
  have h0 : 0 ≤ drNear (band d) E s ζ N v + drRes (band d) E s ζ N v
      (2 * (etaT E v)⁻¹ * ((N : ℝ) ^ (2 * ε) * Λ) * ((band d).W N : ℝ) ^ (-D)) := by
    unfold drNear drRes
    have := (exp_pos (Real.log ((band d).W N : ℝ) ^ ((3 : ℝ) / 4))).le
    positivity
  have hχ : (if (zdist ((band d).L N) (b 0 - b 1) : ℝ)
      ≤ ellStar ((band d).W N : ℝ) ((band d).ell N v) then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  linarith [mul_le_mul_of_nonneg_left hχ h0]

end Split

/-! ### Acceptance checks: both stopping levels instantiate `hΛ` -/

end RBM.Gauss.Grid
