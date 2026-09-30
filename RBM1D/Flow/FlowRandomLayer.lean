/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GUEPhaseBounds
import RBM1D.Flow.GUEPhase729
import RBM1D.Flow.OUCommonFlow
import RBM1D.Flow.EnergyUniformReg

/-!
# The §7.2 random layer: `FlowLocalLaw` and `FlowEq747` from the Step 1–5 inputs

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §7.2. The two outputs `flowLocalLaw_of_steps` ((2.26) at `η = N^{-1+2τ_U}`, moment
form, uniform in `t ∈ [0, t_U]`, `|E| ≤ 2 - κ/2`) and `flowEq747_of_steps` ((7.47) for `H_{t_N}`
at `τ* = c/3`), with their random inputs made explicit as the Props
`BoundsCoreNInput d (κ/2)` / `BoundsNInput d κ` (Lemmas 2.18–2.20, resp. with (2.71), at
`N`-dependent energies).

Route:
* `τ0 = min (c/12) (1/100)`; per sequence, Lemma 2.8 at `z_N` gives `E' = lemE z_N`,
  `t₀ = lemT z_N`, and `t₁ = (1 - ζ(t_N)) t₀`;
* the size conditions (`frl_rows`, `frl_rowsLL`, `frl_rowsQ`) discharge the deterministic
  hypotheses of `GUEGrid.gueGrid_pathBounds` and `GUEGrid.gueGrid_eq729` at exponent
  `τU/2`, with primitive loops from `GUEGrid.gueK_exists`;
* `FlowLocalLaw`: the `localLaw` of `GUEGrid.gueGrid_pathBounds` at the last grid step,
  uniformized by
  `RBM.eventually_forall_mem_of_forall_seq`;
* `FlowEq747`: `GUEPhase.Eq747Inputs` for `GUEGrid.gueFlowCommon d t` is constructed (not assumed)
  from `GUEGrid.law726_gueFlowCommon`, the transferred bound of `GUEGrid.gueGrid_eq729` and
  boundedness, then
  `GUEPhase.eq747_of_inputs` is applied.

The only carrier crossing is the one-time law `GUEGrid.map_ouCommonFlow_smul_eq_gueH_last`
(`frl_integral_transfer`); no pathwise OU/GUE identity is used.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace RBM.Gauss

/-! ### Measurability of resolvent functionals in the matrix (private restatements of
the pattern of `Gauss/GridJStar.lean`, which this file does not import) -/

section FrlMeasurable

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem frl_measurable_green (z : ℂ) (i j : n) :
    Measurable fun M : Matrix n n ℂ => green M z i j :=
  measurable_matrix_inv_apply (continuous_id.sub continuous_const).measurable i j

private theorem frl_measurable_Gsig (z : ℂ) (σ : Bool) (i j : n) :
    Measurable fun M : Matrix n n ℂ => Gsig M z σ i j := by
  cases σ
  · simpa [Gsig] using frl_measurable_green ((starRingEnd ℂ) z) i j
  · simpa [Gsig] using frl_measurable_green z i j

private theorem frl_measurable_mul {ι : Type*} [Fintype ι]
    {Θ : Type*} [MeasurableSpace Θ] {A C : Θ → Matrix ι ι ℂ}
    (hA : ∀ i j, Measurable fun x => A x i j) (hC : ∀ i j, Measurable fun x => C x i j)
    (i j : ι) : Measurable fun x => (A x * C x) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hC k j)

private theorem frl_measurable_gloop {L W : ℕ} [NeZero L] [NeZero W] (z : ℂ)
    (I : LoopIdx (ZMod L)) :
    Measurable fun M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ => gloop L W M z I := by
  have hprod : ∀ i j : ZMod L × Fin W,
      Measurable fun M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ => gloopProd L W M z I i j := by
    suffices h : ∀ l : List (Bool × ZMod L), ∀ i j : ZMod L × Fin W,
        Measurable fun M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ => (l.foldr
          (fun (p : Bool × ZMod L) (Acc : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) =>
            Gsig M z p.1 * Eblk L W p.2 * Acc)
          (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) i j by
      simpa [gloopProd] using h (I.σ.zip I.a)
    intro l
    induction l with
    | nil => intro i j; simp
    | cons p l ih =>
        intro i j
        simp only [List.foldr_cons]
        refine frl_measurable_mul ?_ (fun a b => ih a b) i j
        intro a b
        exact frl_measurable_mul (fun c e => frl_measurable_Gsig z p.1 c e)
          (C := fun _ => Eblk L W p.2) (fun _ _ => measurable_const) a b
  have h : ∀ M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ, gloop L W M z I
      = ∑ i : ZMod L × Fin W, gloopProd L W M z I i i := fun _ => rfl
  simp only [h]
  exact Finset.measurable_sum _ fun i _ => hprod i i

end FrlMeasurable

/-! ### The one-time law, integrated (the only carrier crossing of this file) -/

/-- Integrals of a measurable matrix functional of `√t₀ · H_{τ_N}` on the common carrier equal
the integrals of the same functional of the last GUE-phase grid matrix, by
`GUEGrid.map_ouCommonFlow_smul_eq_gueH_last` (a one-time law at step `K`). -/
private theorem frl_integral_transfer (d : Dims) (t0 τ : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (ht0 : 0 ≤ t0 N) (hτ : 0 ≤ τ N) (hK : K N ≠ 0) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (f : Matrix (d.Idx N) (d.Idx N) ℂ → F) (hf : Measurable f) :
    ∫ ω, f (((Real.sqrt (t0 N) : ℝ) : ℂ) • (ouCommonFlow d).Ht N (τ N) ω) ∂(ouCommonMeasure d) =
      ∫ ω, f (GUEGrid.gueH d (fun N => (1 - ouZeta (τ N)) * t0 N) t0 K N (K N) ω)
        ∂(GUEGrid.Pgue d) := by
  have h1 : Measurable fun ω => ((Real.sqrt (t0 N) : ℝ) : ℂ) • (ouCommonFlow d).Ht N (τ N) ω :=
    (ouCommonFlow_measurable d N (τ N)).const_smul (((Real.sqrt (t0 N) : ℝ) : ℂ))
  have h2 := GUEGrid.gueH_measurable d (fun N => (1 - ouZeta (τ N)) * t0 N) t0 K N (K N)
  rw [← integral_map h1.aemeasurable hf.aestronglyMeasurable,
    GUEGrid.map_ouCommonFlow_smul_eq_gueH_last d t0 τ K N ht0 hτ hK]
  exact integral_map h2.aemeasurable hf.aestronglyMeasurable


/-! ### Deterministic facts: `ζ(t) = 1 - e^{-t}`, Lemma 2.8 at `z = e + iη` -/

private theorem frl_ouZeta_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ouZeta t := by
  unfold ouZeta
  have := Real.exp_le_one_iff.2 (neg_nonpos.2 ht)
  linarith

private theorem frl_ouZeta_le_one (t : ℝ) : ouZeta t ≤ 1 := by
  unfold ouZeta
  have := (Real.exp_pos (-t)).le
  linarith

private theorem frl_ouZeta_le (t : ℝ) : ouZeta t ≤ t := by
  unfold ouZeta
  have := Real.add_one_le_exp (-t)
  linarith

/-- Lemma 2.8 at `z = e + iη`, `|e| ≤ 2 - k`, `0 < η ≤ 1` (the bounds on
`η_{t₀} = etaT E' t₀ = √t₀ η` and `1 - t₀` used by the size conditions). -/
private theorem frl_lem28 {k e η : ℝ} (hk : 0 < k) (he : |e| ≤ 2 - k) (hη0 : 0 < η)
    (hη1 : η ≤ 1) {z : ℂ} (hz : z = (e : ℂ) + (η : ℂ) * Complex.I) :
    0 < z.im ∧ |lemE z| ≤ 2 - k ∧ 1 / 16 ≤ lemT z ∧ lemT z < 1 ∧
      η / 4 ≤ etaT (lemE z) (lemT z) ∧ etaT (lemE z) (lemT z) ≤ η ∧
      η / 4 ≤ 1 - lemT z ∧ 1 - lemT z ≤ η / (Real.sqrt (2 * k) / 2) := by
  have hre : z.re = e := by simp [hz]
  have him : z.im = η := by simp [hz]
  have hzim : 0 < z.im := him ▸ hη0
  obtain ⟨hE', ht16, -, -⟩ := lemma28_quant hk hzim (him ▸ hη1) (hre ▸ he)
  have ht1 := lemT_lt_one hzim
  have heta : etaT (lemE z) (lemT z) = Real.sqrt (lemT z) * η := by
    rw [etaT_eq_zt_im, zt_im_lemma28 hzim, him]
  have hs4 : (1 / 4 : ℝ) ≤ Real.sqrt (lemT z) := by
    rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht16
  have hs1 : Real.sqrt (lemT z) ≤ 1 := Real.sqrt_le_one.mpr ht1.le
  have hk2 : k ≤ 2 := by linarith [abs_nonneg e]
  have hm : Real.sqrt (2 * k) / 2 ≤ (mE (lemE z)).im := mE_im_ge hk hk2 hE'
  have hm1 : (mE (lemE z)).im ≤ 1 := mE_im_le_one (by linarith [hE'])
  have hc : 0 < Real.sqrt (2 * k) / 2 := by positivity
  have heta' : etaT (lemE z) (lemT z) = (1 - lemT z) * (mE (lemE z)).im := rfl
  have hA : η / 4 ≤ etaT (lemE z) (lemT z) := by rw [heta]; nlinarith
  have hB : etaT (lemE z) (lemT z) ≤ η := by rw [heta]; nlinarith
  refine ⟨hzim, hE', ht16, ht1, hA, hB, ?_, ?_⟩
  · have h1t : 0 < 1 - lemT z := by linarith
    rw [heta'] at hA
    nlinarith
  · rw [le_div_iff₀ hc]
    rw [heta'] at hB
    have h1t : 0 < 1 - lemT z := by linarith
    nlinarith

/-- `X ≤ N^{-τ} Y` from `2^τ X ≤ S^{-τ} Y` and `N ≤ 2S`. -/
private theorem frl_Npow {N S τD X Y : ℝ} (hS : 0 < S) (hN0 : 0 < N) (hN : N ≤ 2 * S)
    (hτD : 0 ≤ τD) (hY : 0 ≤ Y) (h : (2 : ℝ) ^ τD * X ≤ S ^ (-τD) * Y) :
    X ≤ N ^ (-τD) * Y := by
  have e : (2 * S) ^ (-τD) = (2 : ℝ) ^ (-τD) * S ^ (-τD) := Real.mul_rpow (by norm_num) hS.le
  have hN' : (2 * S) ^ (-τD) ≤ N ^ (-τD) := Real.rpow_le_rpow_of_nonpos hN0 hN (by linarith)
  have h2 : (2 : ℝ) ^ (-τD) * (2 : ℝ) ^ τD = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have h2p : 0 ≤ (2 : ℝ) ^ (-τD) := by positivity
  calc X = (2 : ℝ) ^ (-τD) * ((2 : ℝ) ^ τD * X) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ (2 : ℝ) ^ (-τD) * (S ^ (-τD) * Y) := mul_le_mul_of_nonneg_left h h2p
    _ = (2 * S) ^ (-τD) * Y := by rw [e]; ring
    _ ≤ N ^ (-τD) * Y := mul_le_mul_of_nonneg_right hN' hY

/-- **The size conditions** for the sequence `z_N = e_N + iη_N`,
`t₀ = lemT z_N`, `t₁ = (1 - ζ(t_N)) t₀`, from size-level conditions `r1`–`r5`: exactly the
deterministic hypotheses of `GUEGrid.gueGrid_pathBounds` / `GUEGrid.gueGrid_eq729` at the
exponent `τD`, and the range condition of `BoundsCoreNInput` / `BoundsNInput` at `τ`. -/
private theorem frl_rows (d : Dims) {k τD τ : ℝ} (hk : 0 < k) (hτD : 0 < τD) (hτ1 : τ ≤ 1)
    {e η t : ℕ → ℝ} (z : ℕ → ℂ) (hz : ∀ N, z N = (e N : ℂ) + (η N : ℂ) * Complex.I)
    (he : ∀ N, |e N| ≤ 2 - k) (hη0 : ∀ N, 0 < η N) (hη1 : ∀ N, η N ≤ 1) (ht : ∀ N, 0 ≤ t N)
    (r1 : ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ^ τD * t N ≤ ((d.L N * d.W N : ℕ) : ℝ) ^ (-τD) * (η N / 4))
    (r2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ τD * (4 * (((d.L N * d.W N : ℕ) : ℝ) * η N)⁻¹) ≤
      ((d.L N * d.W N : ℕ) : ℝ) ^ (-τD))
    (r3 : ∀ᶠ N : ℕ in atTop, (d.L N : ℝ) ^ 2 * (η N / (Real.sqrt (2 * k) / 2) + t N) ≤ 1)
    (r5 : ∀ᶠ N : ℕ in atTop, ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + τ) ≤ η N / 4) :
    (∀ N, |lemE (z N)| ≤ 2 - k) ∧ (∀ N, 0 ≤ (1 - ouZeta (t N)) * lemT (z N)) ∧
      (∀ N, (1 - ouZeta (t N)) * lemT (z N) ≤ lemT (z N)) ∧ (∀ N, lemT (z N) < 1) ∧
      (∀ᶠ N : ℕ in atTop, lemT (z N) - (1 - ouZeta (t N)) * lemT (z N) ≤
        (N : ℝ) ^ (-τD) * etaT (lemE (z N)) (lemT (z N))) ∧
      (∀ᶠ N : ℕ in atTop,
        (GUEGrid.gueScale d (fun N => lemE (z N)) N (lemT (z N)))⁻¹ ≤ (N : ℝ) ^ (-τD)) ∧
      (∀ᶠ N : ℕ in atTop, (d.L N : ℝ) ^ 2 * (1 - (1 - ouZeta (t N)) * lemT (z N)) ≤ 1) ∧
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - (1 - ouZeta (t N)) * lemT (z N)) := by
  have L28 := fun N => frl_lem28 hk (he N) (hη0 N) (hη1 N) (hz N)
  have hSpos : ∀ N, (0 : ℝ) < ((d.L N * d.W N : ℕ) : ℝ) := fun N =>
    Nat.cast_pos.2 (Nat.mul_pos (by have := d.three_le_L N; omega) (d.W_pos N))
  have hdim : ∀ᶠ N : ℕ in atTop, ((d.L N * d.W N : ℕ) : ℝ) ≤ N ∧
      (N : ℝ) ≤ 2 * ((d.L N * d.W N : ℕ) : ℝ) := by
    filter_upwards [d.dim] with N hN
    rw [Nat.mul_comm (d.L N)]
    exact ⟨by exact_mod_cast hN.1, by exact_mod_cast hN.2⟩
  have hζ0 : ∀ N, 0 ≤ ouZeta (t N) := fun N => frl_ouZeta_nonneg (ht N)
  have hζ1 : ∀ N, ouZeta (t N) ≤ 1 := fun N => frl_ouZeta_le_one (t N)
  have hζt : ∀ N, ouZeta (t N) ≤ t N := fun N => frl_ouZeta_le (t N)
  have ht0pos : ∀ N, 0 ≤ lemT (z N) := fun N => by linarith [(L28 N).2.2.1]
  have hdiff : ∀ N, lemT (z N) - (1 - ouZeta (t N)) * lemT (z N) ≤ t N := fun N => by
    have h1 := (L28 N).2.2.2.1
    nlinarith [hζ0 N, hζt N, ht0pos N]
  refine ⟨fun N => (L28 N).2.1, fun N => mul_nonneg (by linarith [hζ1 N]) (ht0pos N),
    fun N => by nlinarith [hζ0 N, ht0pos N], fun N => (L28 N).2.2.2.1, ?_, ?_, ?_, ?_⟩
  · filter_upwards [r1, hdim, eventually_ge_atTop 1] with N hN hd hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hX := frl_Npow (hSpos N) hN0 hd.2 hτD.le (by linarith [hη0 N]) hN
    calc _ ≤ t N := hdiff N
      _ ≤ (N : ℝ) ^ (-τD) * (η N / 4) := hX
      _ ≤ (N : ℝ) ^ (-τD) * etaT (lemE (z N)) (lemT (z N)) :=
          mul_le_mul_of_nonneg_left (L28 N).2.2.2.2.1 (by positivity)
  · filter_upwards [r2, hdim, eventually_ge_atTop 1] with N hN hd hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hX := frl_Npow (X := 4 * (((d.L N * d.W N : ℕ) : ℝ) * η N)⁻¹) (Y := 1)
      (hSpos N) hN0 hd.2 hτD.le zero_le_one (by rw [mul_one]; exact hN)
    rw [mul_one] at hX
    refine le_trans ?_ hX
    unfold GUEGrid.gueScale
    have hη4 := (L28 N).2.2.2.2.1
    have hSη : 0 < ((d.L N * d.W N : ℕ) : ℝ) * (η N / 4) := mul_pos (hSpos N) (by linarith [hη0 N])
    calc (((d.L N * d.W N : ℕ) : ℝ) * etaT (lemE (z N)) (lemT (z N)))⁻¹
        ≤ (((d.L N * d.W N : ℕ) : ℝ) * (η N / 4))⁻¹ :=
          inv_anti₀ hSη (mul_le_mul_of_nonneg_left hη4 (hSpos N).le)
      _ = 4 * (((d.L N * d.W N : ℕ) : ℝ) * η N)⁻¹ := by
          have := hη0 N; have := hSpos N; field_simp
  · filter_upwards [r3] with N hN
    refine le_trans ?_ hN
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := (L28 N).2.2.2.2.2.2.2
    have h2 : ouZeta (t N) * lemT (z N) ≤ ouZeta (t N) * 1 :=
      mul_le_mul_of_nonneg_left (L28 N).2.2.2.1.le (hζ0 N)
    nlinarith [hζt N]
  · filter_upwards [r5, hdim, eventually_ge_atTop 1] with N hN hd hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have h1 : (N : ℝ) ^ (-1 + τ) ≤ ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_nonpos (hSpos N) hd.1 (by linarith)
    have h2 := (L28 N).2.2.2.2.2.2.1
    have h3 : (1 - ouZeta (t N)) * lemT (z N) ≤ lemT (z N) := by nlinarith [hζ0 N, ht0pos N]
    linarith


/-! ### Size conditions at the two scales `η = S^{-1+2τU}` and `η = η_Q` -/

private theorem frl_rpow_mul_eq {x a b c e : ℝ} (hx : 0 < x) (h : a + b = c + e) :
    x ^ a * x ^ b = x ^ c * x ^ e := by
  rw [← Real.rpow_add hx, ← Real.rpow_add hx, h]

/-- Lift a property holding for all large reals to the matrix size `S = L W`. -/
private theorem frl_eventually_size (d : Dims) {P : ℝ → Prop} (h : ∀ᶠ x : ℝ in atTop, P x) :
    ∀ᶠ N : ℕ in atTop, P ((d.L N * d.W N : ℕ) : ℝ) :=
  (tendsto_natCast_atTop_atTop.comp (ouCommonBand d).tendsto_size).eventually h

private theorem frl_eventually_rpow_ge (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, C ≤ x ^ a :=
  (tendsto_rpow_atTop ha).eventually_ge_atTop C

/-- `L² ≤ S^{1-2c}` from (2.2) in the form `W² ≥ S^{1+2c}`. -/
private theorem frl_L_sq_le (d : Dims) (N : ℕ)
    (hW : ((d.L N * d.W N : ℕ) : ℝ) ^ (1 + 2 * d.c) ≤ (d.W N : ℝ) ^ 2) :
    (d.L N : ℝ) ^ 2 ≤ ((d.L N * d.W N : ℕ) : ℝ) ^ (1 - 2 * d.c) := by
  set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ) with hSdef
  have hS : 0 < S := Nat.cast_pos.2 (Nat.mul_pos (by have := d.three_le_L N; omega) (d.W_pos N))
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hSLW : S = (d.L N : ℝ) * d.W N := by rw [hSdef]; push_cast; ring
  have e : S ^ (1 - 2 * d.c) * S ^ (1 + 2 * d.c) = S ^ 2 := by
    rw [← Real.rpow_add hS, show 1 - 2 * d.c + (1 + 2 * d.c) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have h1 : (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ 2 ≤ S ^ (1 - 2 * d.c) * (d.W N : ℝ) ^ 2 := by
    calc (d.L N : ℝ) ^ 2 * (d.W N : ℝ) ^ 2 = S ^ 2 := by rw [hSLW]; ring
      _ = S ^ (1 - 2 * d.c) * S ^ (1 + 2 * d.c) := e.symm
      _ ≤ S ^ (1 - 2 * d.c) * (d.W N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hW (by positivity)
  exact le_of_mul_le_mul_right h1 (by positivity)

/-- The size conditions at `η = S^{-1+2τU}` (the scale of `FlowLocalLaw`), `τD = τU/2`, `τ = τU`,
for any `0 ≤ t_N ≤ S^{-1+τU}`. -/
private theorem frl_rowsLL (d : Dims) {k τU : ℝ} (hk : 0 < k) (hτU : 0 < τU)
    (hτUc : τU ≤ d.c / 12) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ N, t N ≤ ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + τU)) :
    (∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ (τU / 2) * t N ≤ ((d.L N * d.W N : ℕ) : ℝ) ^ (-(τU / 2)) *
      (((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + 2 * τU) / 4)) ∧
    (∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ (τU / 2) * (4 * (((d.L N * d.W N : ℕ) : ℝ) *
      ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + 2 * τU))⁻¹) ≤ ((d.L N * d.W N : ℕ) : ℝ) ^ (-(τU / 2))) ∧
    (∀ᶠ N : ℕ in atTop, (d.L N : ℝ) ^ 2 *
      (((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + 2 * τU) / (Real.sqrt (2 * k) / 2) + t N) ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop, ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + τU) ≤
      ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + 2 * τU) / 4) := by
  have hc := d.c_pos
  have hck : 0 < Real.sqrt (2 * k) / 2 := by positivity
  set C : ℝ := 1 / (Real.sqrt (2 * k) / 2) + 1 with hC
  have hC0 : 0 < C := by positivity
  have hev := frl_eventually_size d ((((((eventually_ge_atTop (1 : ℝ)).and
    (frl_eventually_rpow_ge (4 * (2 : ℝ) ^ (τU / 2)) (by positivity : 0 < τU / 2))).and
    (frl_eventually_rpow_ge (4 * (2 : ℝ) ^ (τU / 2)) (by positivity : 0 < 3 * τU / 2))).and
    (frl_eventually_rpow_ge C (by linarith : 0 < 2 * d.c - 2 * τU))).and
    (frl_eventually_rpow_ge 4 hτU)))
  have hW := (ouCommonBand d).eventually_size_rpow_le_W_sq
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hev] with N hN
    obtain ⟨⟨⟨⟨hS1, h1⟩, -⟩, -⟩, -⟩ := hN
    set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ)
    have hS : 0 < S := by linarith
    have e := frl_rpow_mul_eq (a := -(τU / 2)) (b := -1 + 2 * τU) (c := -1 + τU) (e := τU / 2) hS
      (by ring)
    have hp : 0 < S ^ (-1 + τU) := Real.rpow_pos_of_pos hS _
    have h2 : 0 < (2 : ℝ) ^ (τU / 2) := by positivity
    calc (2 : ℝ) ^ (τU / 2) * t N ≤ (2 : ℝ) ^ (τU / 2) * S ^ (-1 + τU) :=
          mul_le_mul_of_nonneg_left (ht N) h2.le
      _ ≤ S ^ (-1 + τU) * S ^ (τU / 2) / 4 := by nlinarith
      _ = S ^ (-(τU / 2)) * (S ^ (-1 + 2 * τU) / 4) := by rw [← e]; ring
  · filter_upwards [hev] with N hN
    obtain ⟨⟨⟨⟨hS1, -⟩, h1⟩, -⟩, -⟩ := hN
    set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ)
    have hS : 0 < S := by linarith
    have e1 : S * S ^ (-1 + 2 * τU) = S ^ (2 * τU) := by
      rw [mul_comm, ← Real.rpow_add_one hS.ne']; ring_nf
    have e2 : S ^ (-(τU / 2)) = (S ^ (2 * τU))⁻¹ * S ^ (3 * τU / 2) := by
      rw [← Real.rpow_neg hS.le, ← Real.rpow_add hS]; ring_nf
    rw [e1, e2]
    have hp : 0 < (S ^ (2 * τU))⁻¹ := by positivity
    nlinarith
  · filter_upwards [hev, hW] with N hN hWN
    obtain ⟨⟨⟨⟨hS1, -⟩, -⟩, h1⟩, -⟩ := hN
    set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ) with hSdef
    have hS : 0 < S := by linarith
    have hL := frl_L_sq_le d N hWN
    have htt : t N ≤ S ^ (-1 + 2 * τU) :=
      (ht N).trans (Real.rpow_le_rpow_of_exponent_le hS1 (by linarith))
    have hX : S ^ (-1 + 2 * τU) / (Real.sqrt (2 * k) / 2) + t N ≤ C * S ^ (-1 + 2 * τU) := by
      rw [hC, add_mul, one_mul, div_eq_mul_one_div, mul_comm]; linarith
    have e : S ^ (1 - 2 * d.c) * S ^ (-1 + 2 * τU) = (S ^ (2 * d.c - 2 * τU))⁻¹ := by
      rw [← Real.rpow_add hS, ← Real.rpow_neg hS.le]; ring_nf
    have hX0 : 0 ≤ S ^ (-1 + 2 * τU) / (Real.sqrt (2 * k) / 2) + t N := by
      have := ht0 N; positivity
    calc (d.L N : ℝ) ^ 2 * (S ^ (-1 + 2 * τU) / (Real.sqrt (2 * k) / 2) + t N)
        ≤ S ^ (1 - 2 * d.c) * (C * S ^ (-1 + 2 * τU)) :=
          mul_le_mul hL hX hX0 (by positivity)
      _ = C * (S ^ (2 * d.c - 2 * τU))⁻¹ := by rw [← e]; ring
      _ ≤ 1 := by
          have hp : 0 < S ^ (2 * d.c - 2 * τU) := by positivity
          rw [← div_eq_mul_inv, div_le_one hp]; exact h1
  · filter_upwards [hev] with N hN
    obtain ⟨⟨⟨⟨hS1, -⟩, -⟩, -⟩, h1⟩ := hN
    set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ)
    have hS : 0 < S := by linarith
    have e : S ^ (-1 + 2 * τU) = S ^ (-1 + τU) * S ^ τU := by
      rw [← Real.rpow_add hS]; ring_nf
    have hp : 0 < S ^ (-1 + τU) := by positivity
    rw [e]; nlinarith


/-- `(L² η_Q)³ ≤ S^{-5c}` at `η_Q = queEta S W (c/3)`, from `W² ≥ S^{1+2c}`. -/
private theorem frl_L_sq_queEta_cube_le (d : Dims) (N : ℕ)
    (hW : ((d.L N * d.W N : ℕ) : ℝ) ^ (1 + 2 * d.c) ≤ (d.W N : ℝ) ^ 2) :
    ((d.L N : ℝ) ^ 2 * queEta ((d.L N * d.W N : ℕ) : ℝ) (d.W N : ℝ) (d.c / 3)) ^ 3 ≤
      ((d.L N * d.W N : ℕ) : ℝ) ^ (-(5 * d.c)) := by
  set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ) with hSdef
  have hS : 0 < S := Nat.cast_pos.2 (Nat.mul_pos (by have := d.three_le_L N; omega) (d.W_pos N))
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hLW : (d.L N : ℝ) = S / d.W N := by
    rw [hSdef]; push_cast; field_simp
  have h5 : S ^ (5 : ℕ) = S ^ ((5 : ℕ) : ℝ) := (Real.rpow_natCast S 5).symm
  have key : ((d.L N : ℝ) ^ 2 * queEta S (d.W N : ℝ) (d.c / 3)) ^ 3 =
      S ^ (2 - d.c) / (d.W N : ℝ) ^ 4 := by
    rw [mul_pow, queEta_cube hS hW0, hLW]
    have e : S ^ (-3 - 3 * (d.c / 3)) * S ^ (5 : ℕ) = S ^ (2 - d.c) := by
      rw [h5, ← Real.rpow_add hS]; congr 1; push_cast; ring
    rw [← e]
    field_simp
  have hW4 : S ^ (2 + 4 * d.c) ≤ (d.W N : ℝ) ^ 4 := by
    have e : S ^ (2 + 4 * d.c) = (S ^ (1 + 2 * d.c)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS.le]; congr 1; push_cast; ring
    rw [e, show (d.W N : ℝ) ^ 4 = ((d.W N : ℝ) ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) hW 2
  rw [key]
  have e2 : S ^ (-(5 * d.c)) = S ^ (2 - d.c) / S ^ (2 + 4 * d.c) := by
    rw [← Real.rpow_sub hS]; ring_nf
  rw [e2]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hW4

/-- The size conditions at `η_Q = queEta S W (c/3)` (the scale of `FlowEq747`), `τD = τU/2`,
`τ = min (c/6) (1/2)`, for any `0 ≤ t_N ≤ S^{-1+τU}`. -/
private theorem frl_rowsQ (d : Dims) {k τU : ℝ} (hk : 0 < k) (hτU : 0 < τU)
    (hτUc : τU ≤ d.c / 12) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ N, t N ≤ ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + τU)) :
    (∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ (τU / 2) * t N ≤ ((d.L N * d.W N : ℕ) : ℝ) ^ (-(τU / 2)) *
      (queEta ((d.L N * d.W N : ℕ) : ℝ) (d.W N : ℝ) (d.c / 3) / 4)) ∧
    (∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ (τU / 2) * (4 * (((d.L N * d.W N : ℕ) : ℝ) *
      queEta ((d.L N * d.W N : ℕ) : ℝ) (d.W N : ℝ) (d.c / 3))⁻¹) ≤
        ((d.L N * d.W N : ℕ) : ℝ) ^ (-(τU / 2))) ∧
    (∀ᶠ N : ℕ in atTop, (d.L N : ℝ) ^ 2 *
      (queEta ((d.L N * d.W N : ℕ) : ℝ) (d.W N : ℝ) (d.c / 3) / (Real.sqrt (2 * k) / 2) + t N)
        ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop, ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + min (d.c / 6) (1 / 2)) ≤
      queEta ((d.L N * d.W N : ℕ) : ℝ) (d.W N : ℝ) (d.c / 3) / 4) := by
  have hc := d.c_pos
  set ck : ℝ := Real.sqrt (2 * k) / 2 with hck
  have hck0 : 0 < ck := by positivity
  have hev := frl_eventually_size d ((((((eventually_ge_atTop (1 : ℝ)).and
    (frl_eventually_rpow_ge (4 * (2 : ℝ) ^ (τU / 2)) (by linarith : 0 < d.c / 3 - 3 * τU / 2))).and
    (frl_eventually_rpow_ge (4 * (2 : ℝ) ^ (τU / 2)) (by linarith : 0 < d.c / 3 - τU / 2))).and
    (frl_eventually_rpow_ge 2 (by linarith : 0 < 2 * d.c - τU))).and
    (frl_eventually_rpow_ge (((ck / 2) ^ 3)⁻¹) (by linarith : 0 < 5 * d.c))).and
    (frl_eventually_rpow_ge 4 (by linarith : 0 < d.c / 6)))
  have hW := (ouCommonBand d).eventually_size_rpow_le_W_sq
  have hlow : ∀ N, ((d.L N * d.W N : ℕ) : ℝ) ^ (1 + 2 * d.c) ≤ (d.W N : ℝ) ^ 2 →
      1 ≤ ((d.L N * d.W N : ℕ) : ℝ) →
      ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + d.c / 3) ≤
        queEta ((d.L N * d.W N : ℕ) : ℝ) (d.W N : ℝ) (d.c / 3) := fun N hWN hS1 => by
    have h := rpow_le_queEta (τ := d.c / 3) hS1 (by exact_mod_cast d.W_pos N) hWN
    have e : -1 - d.c / 3 + 2 * d.c / 3 = -1 + d.c / 3 := by ring
    rwa [e] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hev, hW] with N hN hWN
    obtain ⟨⟨⟨⟨⟨hS1, h1⟩, -⟩, -⟩, -⟩, -⟩ := hN
    set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ)
    have hS : 0 < S := by linarith
    have hη := hlow N hWN hS1
    have e := frl_rpow_mul_eq (a := -(τU / 2)) (b := -1 + d.c / 3) (c := -1 + τU)
      (e := d.c / 3 - 3 * τU / 2) hS (by ring)
    have hp : 0 < S ^ (-1 + τU) := Real.rpow_pos_of_pos hS _
    have h2 : 0 < (2 : ℝ) ^ (τU / 2) := by positivity
    calc (2 : ℝ) ^ (τU / 2) * t N ≤ (2 : ℝ) ^ (τU / 2) * S ^ (-1 + τU) :=
          mul_le_mul_of_nonneg_left (ht N) h2.le
      _ ≤ S ^ (-1 + τU) * S ^ (d.c / 3 - 3 * τU / 2) / 4 := by nlinarith
      _ = S ^ (-(τU / 2)) * (S ^ (-1 + d.c / 3) / 4) := by rw [← e]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · filter_upwards [hev, hW] with N hN hWN
    obtain ⟨⟨⟨⟨⟨hS1, -⟩, h1⟩, -⟩, -⟩, -⟩ := hN
    set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ)
    have hS : 0 < S := by linarith
    have hinv : (S * queEta S (d.W N : ℝ) (d.c / 3))⁻¹ ≤ S ^ (d.c / 3 - 2 * d.c / 3) :=
      inv_mul_queEta_le (τ := d.c / 3) hS1 (by exact_mod_cast d.W_pos N) hWN
    have e2 : S ^ (-(τU / 2)) = S ^ (d.c / 3 - 2 * d.c / 3) * S ^ (d.c / 3 - τU / 2) := by
      rw [← Real.rpow_add hS]; ring_nf
    rw [e2]
    have hp : 0 < S ^ (d.c / 3 - 2 * d.c / 3) := by positivity
    have h2 : 0 < (2 : ℝ) ^ (τU / 2) := by positivity
    have hq : 0 ≤ (S * queEta S (d.W N : ℝ) (d.c / 3))⁻¹ := by
      have := queEta_pos (τ := d.c / 3) hS (by exact_mod_cast d.W_pos N : (0 : ℝ) < d.W N)
      positivity
    calc (2 : ℝ) ^ (τU / 2) * (4 * (S * queEta S (d.W N : ℝ) (d.c / 3))⁻¹)
        = (4 * (2 : ℝ) ^ (τU / 2)) * (S * queEta S (d.W N : ℝ) (d.c / 3))⁻¹ := by ring
      _ ≤ S ^ (d.c / 3 - τU / 2) * S ^ (d.c / 3 - 2 * d.c / 3) :=
          mul_le_mul h1 hinv hq (by positivity)
      _ = _ := by ring
  · filter_upwards [hev, hW] with N hN hWN
    obtain ⟨⟨⟨⟨⟨hS1, -⟩, -⟩, h1⟩, h2⟩, -⟩ := hN
    set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ)
    have hS : 0 < S := by linarith
    have hL := frl_L_sq_le d N hWN
    have hcube := frl_L_sq_queEta_cube_le d N hWN
    set η : ℝ := queEta S (d.W N : ℝ) (d.c / 3)
    have hη0 : 0 < η := queEta_pos hS (by exact_mod_cast d.W_pos N)
    -- `L² η ≤ ck / 2`
    have hA : (d.L N : ℝ) ^ 2 * η ≤ ck / 2 := by
      have h5 : S ^ (-(5 * d.c)) ≤ (ck / 2) ^ 3 := by
        rw [Real.rpow_neg hS.le]
        have hp : 0 < S ^ (5 * d.c) := by positivity
        rw [inv_le_comm₀ hp (by positivity)]; exact h2
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).1
        (hcube.trans h5)
    -- `L² t ≤ 1/2`
    have hB : (d.L N : ℝ) ^ 2 * t N ≤ 1 / 2 := by
      have e : S ^ (1 - 2 * d.c) * S ^ (-1 + τU) = (S ^ (2 * d.c - τU))⁻¹ := by
        rw [← Real.rpow_add hS, ← Real.rpow_neg hS.le]; ring_nf
      calc (d.L N : ℝ) ^ 2 * t N ≤ S ^ (1 - 2 * d.c) * S ^ (-1 + τU) :=
            mul_le_mul hL (ht N) (ht0 N) (by positivity)
        _ = (S ^ (2 * d.c - τU))⁻¹ := e
        _ ≤ 1 / 2 := by
            rw [one_div]; exact inv_anti₀ (by norm_num) h1
    have e : (d.L N : ℝ) ^ 2 * (η / ck + t N) =
        (d.L N : ℝ) ^ 2 * η / ck + (d.L N : ℝ) ^ 2 * t N := by
      ring
    rw [e]
    have : (d.L N : ℝ) ^ 2 * η / ck ≤ 1 / 2 := by
      rw [div_le_iff₀ hck0]; linarith
    linarith
  · filter_upwards [hev, hW] with N hN hWN
    obtain ⟨⟨⟨⟨⟨hS1, -⟩, -⟩, -⟩, -⟩, h1⟩ := hN
    set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ)
    have hS : 0 < S := by linarith
    have hη := hlow N hWN hS1
    have hm : S ^ (-1 + min (d.c / 6) (1 / 2)) ≤ S ^ (-1 + d.c / 6) :=
      Real.rpow_le_rpow_of_exponent_le hS1 (by linarith [min_le_left (d.c / 6) (1 / 2)])
    have e : S ^ (-1 + d.c / 3) = S ^ (-1 + d.c / 6) * S ^ (d.c / 6) := by
      rw [← Real.rpow_add hS]; ring_nf
    have hp : 0 < S ^ (-1 + d.c / 6) := by positivity
    rw [e] at hη
    nlinarith


/-- Loops of `H_{t_N}` on the common carrier are integrable (bounded by `(Im z)^{-n}`). -/
private theorem frl_integrable_gloop (d : Dims) (t : ℕ → ℝ) (N : ℕ) {z : ℂ} (hz : 0 < z.im)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.σ.length = I.a.length) (hn : 1 ≤ I.a.length) :
    Integrable (fun ω => gloop (d.L N) (d.W N) ((ouCommonFlow d).Ht N (t N) ω) z I)
      (ouCommonMeasure d) := by
  have := ouCommonMeasure_isProbabilityMeasure d
  have hη : 0 < |z.im| := abs_pos.2 hz.ne'
  refine Integrable.of_bound
    ((frl_measurable_gloop z I).comp (ouCommonFlow_measurable d N (t N))).aestronglyMeasurable
    (|z.im|⁻¹ ^ I.a.length * ((d.W N : ℝ))⁻¹ ^ (I.a.length - 1)) (ae_of_all _ fun ω => ?_)
  exact norm_gloop_le_of_le_abs_im ((ouCommonFlow d).hermitian N (t N) ω) hη le_rfl I hwf hn


/-- U-dependent input (`N`-dependent energy): Lemmas 2.18–2.20 without (2.71) on
`1 - t ≥ N^{-1+τ}`. -/
def BoundsCoreNInput (d : Dims) (κ : ℝ) : Prop :=
  ∀ E : ℕ → ℝ, (∀ N, |E N| ≤ 2 - κ) → ∀ τ : ℝ, 0 < τ → ∀ t : ℕ → ℝ, (∀ N, 0 ≤ t N) →
    (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) → BoundsCoreN (sample d) E t

/-- U-dependent input (Step 6, `N`-dependent energy): Lemmas 2.18–2.20 with (2.71). -/
def BoundsNInput (d : Dims) (κ : ℝ) : Prop :=
  ∀ E : ℕ → ℝ, (∀ N, |E N| ≤ 2 - κ) → ∀ τ : ℝ, 0 < τ → ∀ t : ℕ → ℝ, (∀ N, 0 ≤ t N) →
    (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) → BoundsN (sample d) E t

theorem boundsCoreNInput_of_Thm221NoELNReg (d : Dims) {κ : ℝ} (hκ : 0 < κ)
    (hT : Thm221NoELNReg (sample d) κ) : BoundsCoreNInput d κ :=
  fun _E hE _τ hτ _t ht0 ht => BoundsCoreN_of_Thm221NoELNReg hκ hT hE hτ ht0 ht

/-- **Row L1 along one admissible sequence** `(t_N, e_N)`: the per-sequence form of
`FlowLocalLaw`, via `gueK_exists` (lengths `≤ 8`), `gueGrid_pathBounds` (`n₀ = 2`,
exponent `τU/2`, energy margin `κ/2`), its `localLaw` field at the last grid step, and the
one-time law `frl_integral_transfer`. -/
private theorem frl_localLaw_seq (d : Dims) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hτUc : τU ≤ d.c / 12) (hτU1 : τU ≤ 1 / 100) (hG2 : BoundsCoreNInput d (κ / 2))
    {t e : ℕ → ℝ} (ht0' : ∀ N, 0 ≤ t N)
    (htP : ∀ N, t N ≤ ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + τU))
    (he : ∀ N, |e N| ≤ 2 - κ / 2) {δ : ℝ} (hδ : 0 < δ) (p : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ x : d.Idx N,
      ∫ ω, ‖RBM.green ((ouCommonFlow d).Ht N (t N) ω)
          ((e N : ℂ) + ((((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + 2 * τU) : ℝ) : ℂ) * Complex.I) x x‖ ^
            (2 * p) ∂(ouCommonMeasure d) ≤ ((d.L N * d.W N : ℕ) : ℝ) ^ δ := by
  have hk : 0 < κ / 2 := by positivity
  set η : ℕ → ℝ := fun N => ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + 2 * τU) with hηdef
  set z : ℕ → ℂ := fun N => (e N : ℂ) + (η N : ℂ) * Complex.I with hzdef
  have hSpos : ∀ N, (0 : ℝ) < ((d.L N * d.W N : ℕ) : ℝ) := fun N =>
    Nat.cast_pos.2 (Nat.mul_pos (by have := d.three_le_L N; omega) (d.W_pos N))
  have hS1 : ∀ N, (1 : ℝ) ≤ ((d.L N * d.W N : ℕ) : ℝ) := fun N => by
    exact_mod_cast (ouCommonBand d).one_le_size N
  have hη0 : ∀ N, 0 < η N := fun N => Real.rpow_pos_of_pos (hSpos N) _
  have hη1 : ∀ N, η N ≤ 1 := fun N => Real.rpow_le_one_of_one_le_of_nonpos (hS1 N) (by linarith)
  obtain ⟨r1, r2, r3, r5⟩ := frl_rowsLL d hk hτU hτUc ht0' htP
  obtain ⟨hE', ht1, ht10, ht0, h730, hscale, hell, hrange⟩ :=
    frl_rows d (k := κ / 2) (τD := τU / 2) (τ := τU) hk (by positivity) (by linarith)
      (e := e) (η := η) z (fun N => rfl) he hη0 hη1 ht0' r1 r2 r3 r5
  set E' : ℕ → ℝ := fun N => lemE (z N) with hE'def
  set t0 : ℕ → ℝ := fun N => lemT (z N) with ht0def
  set t1 : ℕ → ℝ := fun N => (1 - ouZeta (t N)) * t0 N with ht1def
  have hB : BoundsCoreN (sample d) E' t1 := hG2 E' hE' τU hτU t1 ht1 hrange
  have hE'2 : ∀ N, |E' N| < 2 := fun N => by have := hE' N; linarith
  choose Kt hKinit hK hK2 using fun N =>
    GUEGrid.gueK_exists (d.L N) (d.W N) (d.three_le_L N) (hE'2 N) (ht1 N) (ht10 N) (ht0 N) (4 * 2)
  have hP := GUEGrid.gueGrid_pathBounds d (κ := κ / 2) hk (τU := τU / 2) (by positivity) 2
    le_rfl hE' ht1 ht10 ht0 h730 hscale hell Kt hKinit hK hB
  have hbad := hP.localLaw (τU / 4) (by positivity) ((2 * p + 1 : ℕ) : ℝ) (by positivity)
  set C : ℝ := (2 : ℝ) ^ (2 * p) + (4 : ℝ) ^ (2 * p) with hCdef
  filter_upwards [hbad, hscale, d.dim, eventually_ge_atTop 1,
    frl_eventually_size d (frl_eventually_rpow_ge C hδ)] with N hbadN hscN hdimN hN1 hCN x
  change ∫ ω, ‖RBM.green ((ouCommonFlow d).Ht N (t N) ω) (z N) x x‖ ^ (2 * p)
    ∂(ouCommonMeasure d) ≤ _
  have L28 := frl_lem28 hk (he N) (hη0 N) (hη1 N) (hzdef ▸ rfl : z N = _)
  obtain ⟨hzim, -, ht16, -, hetaL, -, -, -⟩ := L28
  set S : ℝ := ((d.L N * d.W N : ℕ) : ℝ) with hSdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hSN : S ≤ N := by
    rw [hSdef, Nat.mul_comm]; exact_mod_cast hdimN.1
  -- the pointwise scaling `G(H, z) = √t₀ G(√t₀ H, z_{t₀}^{(E')})`
  set c : ℂ := ((Real.sqrt (t0 N) : ℝ) : ℂ) with hcdef
  have hs : 0 < Real.sqrt (t0 N) := Real.sqrt_pos.2 (by linarith)
  have hs1 : Real.sqrt (t0 N) ≤ 1 := Real.sqrt_le_one.mpr (lemT_lt_one hzim).le
  have hc : c ≠ 0 := sqrt_lemT_ne_zero hzim
  have hpt : ∀ ω, ‖RBM.green ((ouCommonFlow d).Ht N (t N) ω) (z N) x x‖ ^ (2 * p) =
      Real.sqrt (t0 N) ^ (2 * p) *
        ‖RBM.green (c • (ouCommonFlow d).Ht N (t N) ω) (zt (E' N) (t0 N)) x x‖ ^ (2 * p) := by
    intro ω
    have hg : RBM.green (c • (ouCommonFlow d).Ht N (t N) ω) (zt (E' N) (t0 N)) x x =
        c⁻¹ * RBM.green ((ouCommonFlow d).Ht N (t N) ω) (z N) x x := by
      rw [show zt (E' N) (t0 N) = c * z N from zt_eq_sqrt_lemT_mul hzim, green_smul_mul hc]
      rfl
    rw [hg, norm_mul, norm_inv, hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
      mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs.ne', one_pow, one_mul]
  have hstep1 : ∫ ω, ‖RBM.green ((ouCommonFlow d).Ht N (t N) ω) (z N) x x‖ ^ (2 * p)
      ∂(ouCommonMeasure d) = Real.sqrt (t0 N) ^ (2 * p) *
        ∫ ω, ‖RBM.green (GUEGrid.gueH d t1 t0 (GUEGrid.gueGridK 2) N (GUEGrid.gueGridK 2 N) ω)
          (zt (E' N) (t0 N)) x x‖ ^ (2 * p) ∂(GUEGrid.Pgue d) := by
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    exact frl_integral_transfer d t0 t (GUEGrid.gueGridK 2) N (by linarith) (ht0' N)
      (GUEGrid.gueGridK_ne_zero 2 N)
      (fun M => ‖RBM.green M (zt (E' N) (t0 N)) x x‖ ^ (2 * p))
      ((frl_measurable_green _ x x).norm.pow_const _)
  -- the bound on the `Pgue` side (row L1)
  set K := GUEGrid.gueGridK 2
  set Bset := badSet (fun N (p : Fin (K N + 1) × (d.Idx N × d.Idx N)) ω =>
      ‖(green (GUEGrid.gueH d t1 t0 K N p.1 ω) (zt (E' N) (Grid.time t1 t0 K N p.1)) -
          mE (E' N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) p.2.1 p.2.2‖)
      (fun N p _ => (GUEGrid.gueScale d E' N (Grid.time t1 t0 K N p.1))⁻¹ ^ ((1 : ℝ) / 2))
      (τU / 4) N with hBset
  set Bm := toMeasurable (GUEGrid.Pgue d) Bset with hBm
  have hevery : ∀ ω, ‖RBM.green (GUEGrid.gueH d t1 t0 K N (K N) ω) (zt (E' N) (t0 N)) x x‖ ≤
      4 * N := by
    intro ω
    have h1 := le_trans (norm_apply_le_l2_opNorm _ x x)
      (norm_green_zt_le (GUEGrid.gueH_isHermitian d t1 t0 K N (K N) ω) (hE'2 N) (ht0 N))
    refine h1.trans ?_
    have hηS : S⁻¹ ≤ η N := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (hS1 N) (by linarith)
    have hSη : 0 < η N / 4 := by linarith [hη0 N]
    calc (etaT (E' N) (t0 N))⁻¹ ≤ (η N / 4)⁻¹ := inv_anti₀ hSη hetaL
      _ = 4 * (η N)⁻¹ := by field_simp
      _ ≤ 4 * S := by
          have := inv_anti₀ (inv_pos.2 (hSpos N)) hηS
          rw [inv_inv] at this; linarith
      _ ≤ 4 * N := by linarith
  have hgood : ∀ ω, ω ∉ Bm →
      ‖RBM.green (GUEGrid.gueH d t1 t0 K N (K N) ω) (zt (E' N) (t0 N)) x x‖ ≤ 2 := by
    intro ω hω
    have hω' : ω ∉ Bset := fun h => hω (subset_toMeasurable _ _ h)
    simp only [hBset, badSet, Set.mem_ofPred_eq, not_exists, not_lt] at hω'
    have hu := hω' (Fin.last (K N), (x, x))
    simp only [Fin.val_last, Grid.time_last t1 t0 K N (GUEGrid.gueGridK_ne_zero 2 N)] at hu
    have hsc0 : 0 < GUEGrid.gueScale d E' N (t0 N) := by
      unfold GUEGrid.gueScale
      exact mul_pos (hSpos N) (by linarith [hη0 N])
    have hsc : ((GUEGrid.gueScale d E' N (t0 N))⁻¹) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (-(τU / 4)) := by
      calc ((GUEGrid.gueScale d E' N (t0 N))⁻¹) ^ ((1 : ℝ) / 2)
          ≤ ((N : ℝ) ^ (-(τU / 2))) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow (by positivity) hscN (by norm_num)
        _ = (N : ℝ) ^ (-(τU / 4)) := by
            rw [← Real.rpow_mul hN0.le]; ring_nf
    have hone : (N : ℝ) ^ (τU / 4) * (N : ℝ) ^ (-(τU / 4)) = 1 := by
      rw [← Real.rpow_add hN0]; simp
    have hdev : ‖(green (GUEGrid.gueH d t1 t0 K N (K N) ω) (zt (E' N) (t0 N)) -
        mE (E' N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) x x‖ ≤ 1 := by
      exact hu.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left hsc (by positivity)) hone)
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hdev
    have hm : ‖mE (E' N)‖ = 1 := norm_mE (hE'2 N).le
    calc _ = ‖(green (GUEGrid.gueH d t1 t0 K N (K N) ω) (zt (E' N) (t0 N)) x x - mE (E' N)) +
          mE (E' N)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ 2 := by rw [hm]; linarith
  have hPr := GUEGrid.Pgue_isProbabilityMeasure d
  have hfmeas : Measurable fun ω =>
      ‖RBM.green (GUEGrid.gueH d t1 t0 K N (K N) ω) (zt (E' N) (t0 N)) x x‖ ^ (2 * p) :=
    ((frl_measurable_green _ x x).norm.pow_const _).comp (GUEGrid.gueH_measurable d t1 t0 K N (K N))
  have hfint : Integrable (fun ω =>
      ‖RBM.green (GUEGrid.gueH d t1 t0 K N (K N) ω) (zt (E' N) (t0 N)) x x‖ ^ (2 * p))
      (GUEGrid.Pgue d) := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable ((4 * N) ^ (2 * p))
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hevery ω) _
  have hBmm : MeasurableSet Bm := measurableSet_toMeasurable _ _
  have hgint : Integrable (fun ω => (2 : ℝ) ^ (2 * p) +
      Bm.indicator (fun _ => ((4 : ℝ) * N) ^ (2 * p)) ω) (GUEGrid.Pgue d) :=
    (integrable_const _).add ((integrable_const _).indicator hBmm)
  have hptw : ∀ ω, ‖RBM.green (GUEGrid.gueH d t1 t0 K N (K N) ω) (zt (E' N) (t0 N)) x x‖ ^ (2 * p) ≤
      (2 : ℝ) ^ (2 * p) + Bm.indicator (fun _ => ((4 : ℝ) * N) ^ (2 * p)) ω := by
    intro ω
    by_cases hω : ω ∈ Bm
    · rw [Set.indicator_of_mem hω]
      have := pow_le_pow_left₀ (norm_nonneg _) (hevery ω) (2 * p)
      have : (0 : ℝ) ≤ 2 ^ (2 * p) := by positivity
      linarith
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact pow_le_pow_left₀ (norm_nonneg _) (hgood ω hω) _
  have hPB : (GUEGrid.Pgue d).real Bm ≤ (N : ℝ) ^ (-((2 * p + 1 : ℕ) : ℝ)) := by
    rw [measureReal_def, hBm, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbadN
  have hint : ∫ ω, ‖RBM.green (GUEGrid.gueH d t1 t0 K N (K N) ω) (zt (E' N) (t0 N)) x x‖ ^ (2 * p)
      ∂(GUEGrid.Pgue d) ≤ C := by
    refine (integral_mono hfint hgint hptw).trans ?_
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hBmm), integral_const,
      integral_indicator_const _ hBmm, probReal_univ, one_smul, smul_eq_mul, hCdef]
    have hNp : ((4 : ℝ) * N) ^ (2 * p) * (N : ℝ) ^ (-((2 * p + 1 : ℕ) : ℝ)) ≤
        (4 : ℝ) ^ (2 * p) := by
      rw [Real.rpow_neg hN0.le, Real.rpow_natCast, ← div_eq_mul_inv,
        div_le_iff₀ (by positivity), mul_pow, pow_succ]
      have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      have : (0 : ℝ) ≤ (4 : ℝ) ^ (2 * p) * (N : ℝ) ^ (2 * p) := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_left hPB (by positivity : (0 : ℝ) ≤ ((4 : ℝ) * N) ^ (2 * p))
    linarith
  rw [hstep1]
  have hI0 : 0 ≤ ∫ ω, ‖RBM.green (GUEGrid.gueH d t1 t0 K N (K N) ω) (zt (E' N) (t0 N)) x x‖ ^
      (2 * p) ∂(GUEGrid.Pgue d) := integral_nonneg fun _ => by positivity
  have hsp : Real.sqrt (t0 N) ^ (2 * p) ≤ 1 := pow_le_one₀ hs.le hs1
  calc _ ≤ 1 * C := mul_le_mul hsp hint hI0 zero_le_one
    _ = C := one_mul C
    _ ≤ S ^ δ := hCN

/-- **`FlowLocalLaw` from the Step 1–5 inputs.** -/
theorem flowLocalLaw_of_steps (d : Dims) {κ : ℝ} (hκ : 0 < κ)
    (hG2 : BoundsCoreNInput d (κ / 2)) :
    ∃ τ0 > (0 : ℝ), ∀ τU, 0 < τU → τU ≤ τ0 → FlowLocalLaw d κ τU := by
  have hc := d.c_pos
  refine ⟨min (d.c / 12) (1 / 100), by positivity, fun τU hτU hτU0 => ?_⟩
  have hτUc : τU ≤ d.c / 12 := hτU0.trans (min_le_left _ _)
  have hτU1 : τU ≤ 1 / 100 := hτU0.trans (min_le_right _ _)
  intro δ hδ p
  by_cases hκ4 : 4 < κ
  · exact Eventually.of_forall fun N t _ E hE => absurd hE (by have := abs_nonneg E; linarith)
  push Not at hκ4
  have hT : ∀ N, (Set.Icc (0 : ℝ) ((ouCommonBand d).tPow τU N) ×ˢ
      {E : ℝ | |E| ≤ 2 - κ / 2}).Nonempty := fun N =>
    ⟨(0, 0), ⟨Set.left_mem_Icc.2 (Real.rpow_nonneg (Nat.cast_nonneg _) _), by
      simp only [Set.mem_ofPred_eq, abs_zero]; linarith⟩⟩
  have key := RBM.eventually_forall_mem_of_forall_seq hT
    (P := fun N (a : ℝ × ℝ) => ∀ x : d.Idx N,
      ∫ ω, ‖RBM.green ((ouCommonFlow d).Ht N a.1 ω)
          ((a.2 : ℂ) + ((((ouCommonBand d).size N : ℝ) ^ (-1 + 2 * τU) : ℝ) : ℂ) * Complex.I) x x‖ ^
            (2 * p) ∂(ouCommonMeasure d) ≤ ((ouCommonBand d).size N : ℝ) ^ δ)
    (fun s hs => frl_localLaw_seq d hκ hτU hτUc hτU1 hG2 (t := fun N => (s N).1)
      (e := fun N => (s N).2) (fun N => (hs N).1.1) (fun N => (hs N).1.2) (fun N => (hs N).2) hδ p)
  filter_upwards [key] with N hN t ht E hE x
  exact hN (t, E) ⟨ht, hE⟩ x

/-- **`FlowEq747` from the Step 1–5 inputs.** -/
theorem flowEq747_of_steps (d : Dims) {κ : ℝ} (hκ : 0 < κ) (hG2 : BoundsNInput d κ) :
    ∃ τ0 > (0 : ℝ), ∀ τU, 0 < τU → τU ≤ τ0 → FlowEq747 d κ τU := by
  have hc := d.c_pos
  refine ⟨min (d.c / 12) (1 / 100), by positivity, fun τU hτU hτU0 => ?_⟩
  have hτUc : τU ≤ d.c / 12 := hτU0.trans (min_le_left _ _)
  intro E hE t ht
  set z : ℕ → ℂ := (ouCommonBand d).queZ ((ouCommonBand d).c / 3) (fun _ => E) with hzdef
  have hSpos : ∀ N, (0 : ℝ) < ((d.L N * d.W N : ℕ) : ℝ) := fun N =>
    Nat.cast_pos.2 (Nat.mul_pos (by have := d.three_le_L N; omega) (d.W_pos N))
  have hS1 : ∀ N, (1 : ℝ) ≤ ((d.L N * d.W N : ℕ) : ℝ) := fun N => by
    exact_mod_cast (ouCommonBand d).one_le_size N
  have hW0 : ∀ N, (0 : ℝ) < (d.W N : ℝ) := fun N => by exact_mod_cast d.W_pos N
  have hWS : ∀ N, (d.W N : ℝ) ≤ ((d.L N * d.W N : ℕ) : ℝ) := fun N => by
    have : d.W N ≤ d.L N * d.W N := Nat.le_mul_of_pos_left _ (by have := d.three_le_L N; omega)
    exact_mod_cast this
  have ht0' : ∀ N, 0 ≤ t N := fun N => (ht N).1.le
  have htP : ∀ N, t N ≤ ((d.L N * d.W N : ℕ) : ℝ) ^ (-1 + τU) := fun N => (ht N).2
  obtain ⟨r1, r2, r3, r5⟩ := frl_rowsQ d (k := κ) hκ hτU hτUc ht0' htP
  have hτ : 0 < min (d.c / 6) (1 / 2) := by positivity
  obtain ⟨hE', ht1, ht10, ht0, h730, hscale, hell, hrange⟩ :=
    frl_rows d (k := κ) (τD := τU / 2) (τ := min (d.c / 6) (1 / 2)) hκ (by positivity)
      ((min_le_right _ _).trans (by norm_num))
      (e := fun _ => E) (η := fun N => queEta ((d.L N * d.W N : ℕ) : ℝ) (d.W N : ℝ) (d.c / 3))
      z (fun N => rfl) (fun _ => hE) (fun N => queEta_pos (hSpos N) (hW0 N))
      (fun N => queEta_le_one (hS1 N) (hW0 N) (hWS N) (by positivity)) ht0' r1 r2 r3 r5
  set E' : ℕ → ℝ := fun N => lemE (z N) with hE'def
  set t0 : ℕ → ℝ := fun N => lemT (z N) with ht0def
  set t1 : ℕ → ℝ := fun N => (1 - ouZeta (t N)) * t0 N with ht1def
  have hB : BoundsN (sample d) E' t1 := hG2 E' hE' _ hτ t1 ht1 hrange
  have hE'2 : ∀ N, |E' N| < 2 := fun N => by have := hE' N; linarith
  choose Kt hKinit hK hK2 using fun N =>
    GUEGrid.gueK_exists (d.L N) (d.W N) (d.three_le_L N) (hE'2 N) (ht1 N) (ht10 N) (ht0 N) (4 * 3)
  have hP := GUEGrid.gueGrid_pathBounds d (κ := κ) hκ (τU := τU / 2) (by positivity) 3
    (by norm_num) hE' ht1 ht10 ht0 h730 hscale hell Kt hKinit hK hB.toBoundsCoreN
  have h729 := GUEGrid.gueGrid_eq729 d (κ := κ) hκ (τU := τU / 2) (by positivity) 3
    (by norm_num) hE' ht1 ht10 ht0 h730 hscale hell Kt hKinit hK hK2 hB hP
  have hzim : ∀ N, 0 < (z N).im := fun N => by
    rw [hzdef, Band.queZ_im]; exact queEta_pos (hSpos N) (hW0 N)
  refine GUEPhase.eq747_of_inputs (ouCommonFlow d) t (by positivity) (fun _ => E)
    (fun N => ouZeta (t N)) (fun _ => by have := abs_nonneg E; linarith)
    (Eventually.of_forall fun N => ⟨frl_ouZeta_nonneg (ht0' N), frl_ouZeta_le_one _⟩)
    (GUEGrid.gueFlowCommon d t) ⟨GUEGrid.law726_gueFlowCommon d t _ _, ?_, ?_, ?_⟩
  · intro δ hδ
    filter_upwards [h729 δ hδ] with N hN σ₂ a b
    have htr := frl_integral_transfer d t0 t (GUEGrid.gueGridK 3) N (by linarith [ht10 N, ht1 N])
      (ht0' N) (GUEGrid.gueGridK_ne_zero 3 N)
      (fun M => gloop (d.L N) (d.W N) M (zt (E' N) (t0 N)) ⟨[true, σ₂], [a, b]⟩)
      (frl_measurable_gloop _ _)
    have htr' : (∫ ω, GUEPhase.loopG (GUEGrid.gueFlowCommon d t) N (E' N) (t0 N) ω σ₂ a b
        ∂(ouCommonBand d).P) = ∫ ω, gloop (d.L N) (d.W N)
          (GUEGrid.gueH d t1 t0 (GUEGrid.gueGridK 3) N (GUEGrid.gueGridK 3 N) ω)
          (zt (E' N) (t0 N)) ⟨[true, σ₂], [a, b]⟩ ∂(GUEGrid.Pgue d) := htr
    rw [htr']
    exact hN σ₂ a b
  · intro N x y
    have e : (fun ω => trGG ((ouCommonFlow d).Ht N (t N) ω) (z N) x y) =
        fun ω => gloop (d.L N) (d.W N) ((ouCommonFlow d).Ht N (t N) ω) (z N)
          ⟨[true, true], [x, y]⟩ :=
      funext fun ω => (gloop_pp_eq _ _ _ _).symm
    rw [e]
    exact frl_integrable_gloop d t N (hzim N) _ rfl (Nat.le_succ 1)
  · intro N x y
    have e : (fun ω => trGGs ((ouCommonFlow d).Ht N (t N) ω) (z N) x y) =
        fun ω => gloop (d.L N) (d.W N) ((ouCommonFlow d).Ht N (t N) ω) (z N)
          ⟨[true, false], [x, y]⟩ :=
      funext fun ω => (gloop_pm_eq ((ouCommonFlow d).hermitian N (t N) ω) _ _ _).symm
    rw [e]
    exact frl_integrable_gloop d t N (hzim N) _ rfl (Nat.le_succ 1)

end RBM.Gauss

