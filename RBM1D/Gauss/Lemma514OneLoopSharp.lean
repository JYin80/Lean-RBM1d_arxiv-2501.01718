/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossGaussianStep2
import RBM1D.Gauss.DetAvgIBPFlow
import RBM1D.Gauss.Lemma514Holder
import RBM1D.Gauss.OpNorm

/-!
# Sharp actual Gaussian length-one input for Lemma 5.14 (T1385)

The moving-window entry local law from T1337 gives the sharp one-loop block-trace estimate by
T335. The existing Hölder modulus and sequence-to-uniform theorem then give the length-one
`XiLK` bound consumed by the all-order Lemma 5.14 route.
-/

namespace RBM.Gauss.Lemma514OneLoopSharp

open Filter MeasureTheory
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow

private theorem scale_le_W {E : ℝ} (hE : |E| ≤ 2) {N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) : (band d).scale E N u ≤ (band d).W N := by
  have hηℓ := etaT_mul_ellHat_le (L := (band d).L N)
    ((band d).three_le_L N) hE hu0 hu1
  have hW : 0 ≤ ((band d).W N : ℝ) := Nat.cast_nonneg _
  calc
    (band d).scale E N u = (band d).W N *
        (etaT E u * ellHat ((band d).L N) (u : ℂ)) := by
          simp [Band.scale, Band.ell]
          ring
    _ ≤ (band d).W N * 1 := mul_le_mul_of_nonneg_left hηℓ hW
    _ = (band d).W N := mul_one _

private theorem ell_le_L {N : ℕ} {u : ℝ} (hu1 : u < 1) :
    (band d).ell N u ≤ (band d).L N := by
  rw [Band.ell, ellHat_ofReal _ hu1]
  exact min_le_right _ _

private theorem scale_le_N_eta {E : ℝ} {N : ℕ} {u : ℝ}
    (hE : |E| < 2) (hu1 : u < 1)
    (hWL : ((band d).W N : ℝ) * (band d).L N ≤ (N : ℝ)) :
    (band d).scale E N u ≤ (N : ℝ) * etaT E u := by
  have hη : 0 ≤ etaT E u := (etaT_pos_of_lt_one' hE hu1).le
  have hℓ := ell_le_L (N := N) hu1
  calc
    (band d).scale E N u =
        ((band d).W N : ℝ) * (band d).ell N u * etaT E u := rfl
    _ ≤ ((band d).W N : ℝ) * (band d).L N * etaT E u := by gcongr
    _ ≤ (N : ℝ) * etaT E u := by gcongr

private theorem scale_antitone {E : ℝ} {N : ℕ} {u v : ℝ}
    (huv : u ≤ v) (hv1 : v ≤ 1) :
    (band d).scale E N v ≤ (band d).scale E N u := by
  change flowScale ((band d).W N : ℝ) ((band d).L N) E v ≤
    flowScale ((band d).W N : ℝ) ((band d).L N) E u
  exact flowScale_antitoneOn (Nat.cast_nonneg _) _ _
    (Set.mem_Iic.mpr (le_trans huv hv1)) (Set.mem_Iic.mpr hv1) huv

/-- The actual Gaussian moving-window bound for the one-loop `L-K` maximum, at the sharp
control required as the length-one input to the all-order Lemma 5.14 consumer. -/
theorem stochDom_flowXiLK_one_of_gaussian_hypotheses
    {κ E c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s) :
    StochDom (band d).P
      (Step3.flowXiLK (sample d) E s t 1)
      (fun _ _ _ => (1 : ℝ)) := by
  have hE : |E| < 2 := by linarith
  have hstep2 := APrimeFreeLossGaussianStep2.step2_of_gaussian_hypotheses
    hκ0 hκ1 hEκ hs0 hst ht1 hc hreg hB
  let Ξ : ℕ → Set (Ω d) := fun N =>
    {ω | ‖Xmat d N ω‖ + 1 ≤ (N : ℝ) ^ (2 : ℝ)}
  have hΞ : HighProb (band d).P Ξ := by
    apply HighProb.mono (highProb_norm_Xmat_le d)
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN ω hω
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [Ξ]
    have hN2 : (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((N : ℝ) - 2)]
    calc
      ‖Xmat d N ω‖ + 1 ≤ (N : ℝ) + 1 := add_le_add hω le_rfl
      _ ≤ (N : ℝ) ^ (2 : ℝ) := by simpa using hN2
  have hregHol : ∀ᶠ N : ℕ in atTop,
      (etaT E (t N))⁻¹ ≤ (N : ℝ) ^ (2 : ℝ) := by
    filter_upwards [hreg.2, (band d).dim, eventually_ge_atTop (1 : ℕ)]
      with N hscale hdim hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNc : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1 (by linarith)
    have hWL : ((band d).W N : ℝ) * (band d).L N ≤ (N : ℝ) := by
      exact_mod_cast hdim.1
    have hScaleEta := scale_le_N_eta (hE := hE) (ht1 N) hWL
    have hNeta : 1 ≤ (N : ℝ) * etaT E (t N) :=
      hNc.trans (hscale.trans hScaleEta)
    have hηpos : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
    have hηinv : (etaT E (t N))⁻¹ ≤ (N : ℝ) := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hηpos).2 (by nlinarith [hNeta])
    calc
      (etaT E (t N))⁻¹ ≤ (N : ℝ) := hηinv
      _ ≤ (N : ℝ) ^ (2 : ℝ) := by
        calc
          (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ ≤ (N : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hXΞ : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N,
      ‖Xmat d N ω‖ + 1 ≤ (N : ℝ) ^ (2 : ℝ) := Eventually.of_forall fun N ω hω => hω
  have hKb : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (t N),
      ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF → 2 ≤ J.length → J.length ≤ 1 →
        ‖(band d).Kval E N w J‖ ≤ (N : ℝ) ^ (2 : ℝ) := by
    apply Eventually.of_forall
    intro N w hw J hJ hJ2 hJ1
    omega
  have hHol := hHol_flow d hE hs0 ht1 (Ξ := Ξ) (c := (2 : ℝ))
    (by norm_num) (m := 1) (by norm_num) hregHol hXΞ hKb
  have hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData ((band d).L N) 1) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    convert (card_loopData_le (B := band d) 1) using 1
    norm_num
  have hseq : ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
      StochDom (band d).P
        (fun N (q : LoopData ((band d).L N) 1) ω =>
          ‖SumZeroDyn.lkT (sample d) E N (v N) ω q.1 q.2‖)
        (fun N _ _ => ((band d).scale E N (v N))⁻¹) := by
    intro v hv
    let Ψ : ℕ → ℝ := fun N =>
      (((band d).scale E N (v N))⁻¹) ^ ((1 : ℝ) / 2)
    have hv0 : ∀ N, 0 ≤ v N := fun N => (hs0 N).trans (hv N).1
    have hv1 : ∀ N, v N < 1 := fun N => (hv N).2.trans_lt (ht1 N)
    have hll : LocalLawUnifIcc d E v v Ψ := by
      intro τ hτ D hD
      have hDom := hstep2.1 τ hτ D hD
      filter_upwards [hDom] with N hDomN
      intro u hu ij
      have huEq : u = v N := le_antisymm hu.2 hu.1
      subst u
      have huST : v N ∈ Set.Icc (s N) (t N) := hv N
      let pu : TimeIcc s t N := ⟨v N, huST⟩
      have hsubset :
          {ω | (N : ℝ) ^ τ * Ψ N <
              ‖green (Hflow d N (v N) ω) (zt E (v N)) ij.1 ij.2 -
                if ij.1 = ij.2 then mE E else 0‖} ⊆
            badSet
              (fun N (p : TimeIcc s t N × ((band d).Idx N × (band d).Idx N)) ω =>
                (sample d).llErr E N (p.1 : ℝ) ω p.2)
              (fun N (p : TimeIcc s t N × ((band d).Idx N × (band d).Idx N)) _ =>
                ((band d).scale E N (p.1 : ℝ))⁻¹ ^ ((1 : ℝ) / 2)) τ N := by
        intro ω hω
        refine ⟨(pu, ij), ?_⟩
        simp only [Sample.llErr, Sample.G, sample_H, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
          Ψ, pu, Set.mem_ofPred_eq] at hω ⊢
        exact hω
      exact (measure_mono hsubset).trans hDomN
    have hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E (v N) := by
      filter_upwards [hreg.2, (band d).dim, eventually_ge_atTop (1 : ℕ)]
        with N hscale hdim hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNc : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1 (by linarith)
      have hScaleT : (N : ℝ) ^ c ≤ (band d).scale E N (t N) := hscale
      have hScaleV : (band d).scale E N (t N) ≤ (band d).scale E N (v N) :=
        scale_antitone ((hv N).2) (le_of_lt (ht1 N))
      have hWL : ((band d).W N : ℝ) * (band d).L N ≤ (N : ℝ) := by
        exact_mod_cast hdim.1
      have hScaleEta := scale_le_N_eta hE (hv1 N) hWL
      have hNeta : 1 ≤ (N : ℝ) * etaT E (v N) :=
        hNc.trans (hScaleT.trans (hScaleV.trans hScaleEta))
      have hNpos : 0 < (N : ℝ) := by positivity
      have hηlower : (1 : ℝ) / N ≤ etaT E (v N) :=
        (div_le_iff₀ hNpos).2 (by nlinarith [hNeta])
      rw [Real.rpow_neg_one]
      simpa [one_div] using hηlower
    have hΨlo : ∀ᶠ N : ℕ in atTop,
        ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N := by
      filter_upwards [Eventually.of_forall fun N => True.intro] with N _
      have hW : 0 < (d.W N : ℝ) := by exact_mod_cast (band d).W_pos N
      have hscale : 0 < (band d).scale E N (v N) :=
        (band d).scale_pos' hE N (hv0 N) (hv1 N)
      have hscaleW := scale_le_W (N := N) (by linarith) (hv0 N) (hv1 N)
      have hInv : ((d.W N : ℝ))⁻¹ ≤ ((band d).scale E N (v N))⁻¹ :=
        inv_anti₀ hscale hscaleW
      have hpow := Real.rpow_le_rpow (inv_nonneg.mpr (le_of_lt hW)) hInv
        (by norm_num : 0 ≤ (1 : ℝ) / 2)
      have hWrootSq : ((((d.W N : ℝ))⁻¹) ^ ((1 : ℝ) / 2)) ^ 2 =
          ((d.W N : ℝ))⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hW.le)]
        norm_num
      have hWsq : (((d.W N : ℝ)) ^ (-(1 : ℝ) / 2)) ^ 2 = ((d.W N : ℝ))⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hW)]
        norm_num [Real.rpow_neg_one]
      have hΨsq : Ψ N * Ψ N = ((band d).scale E N (v N))⁻¹ := by
        dsimp [Ψ]
        rw [← pow_two, ← Real.rpow_natCast,
          ← Real.rpow_mul (inv_nonneg.mpr hscale.le)]
        norm_num
      have hleft : 0 ≤ (d.W N : ℝ) ^ (-(1 : ℝ) / 2) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hroot0 : 0 ≤ (((d.W N : ℝ))⁻¹) ^ ((1 : ℝ) / 2) :=
        Real.rpow_nonneg (inv_nonneg.mpr hW.le) _
      have hright : 0 ≤ Ψ N := Real.rpow_nonneg (inv_nonneg.mpr hscale.le) _
      have hrootEq : ((d.W N : ℝ) ^ (-(1 : ℝ) / 2)) =
          (((d.W N : ℝ))⁻¹) ^ ((1 : ℝ) / 2) := by
        nlinarith [hWrootSq, hWsq]
      calc
        (d.W N : ℝ) ^ (-(1 : ℝ) / 2) =
            ((d.W N : ℝ)⁻¹) ^ ((1 : ℝ) / 2) := hrootEq
        _ ≤ ((band d).scale E N (v N))⁻¹ ^ ((1 : ℝ) / 2) := hpow
        _ = Ψ N := rfl
    have hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-(c / 2)) := by
      filter_upwards [hreg.2, eventually_ge_atTop (1 : ℕ)] with N hscale hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNpos : 0 < (N : ℝ) := by linarith
      have hNpow : 0 < (N : ℝ) ^ c := Real.rpow_pos_of_pos hNpos c
      have hScaleT : (N : ℝ) ^ c ≤ (band d).scale E N (t N) := hscale
      have hScaleV : (band d).scale E N (t N) ≤ (band d).scale E N (v N) :=
        scale_antitone ((hv N).2) (le_of_lt (ht1 N))
      have hInv : ((band d).scale E N (v N))⁻¹ ≤ ((N : ℝ) ^ c)⁻¹ :=
        inv_anti₀ hNpow (hScaleT.trans hScaleV)
      have hΨsq : Ψ N * Ψ N = ((band d).scale E N (v N))⁻¹ := by
        dsimp [Ψ]
        rw [← pow_two, ← Real.rpow_natCast, ← Real.rpow_mul
          (inv_nonneg.mpr ((band d).scale_pos' hE N (hv0 N) (hv1 N)).le)]
        norm_num
      have hNtargetSq : ((N : ℝ) ^ (-(c / 2))) ^ 2 = (N : ℝ) ^ (-c) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
        congr 1
        norm_num
      have hInvPow : ((N : ℝ) ^ c)⁻¹ = (N : ℝ) ^ (-c) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_mul (le_of_lt hNpos)]
        congr 1
        ring
      have hΨ0 : 0 ≤ Ψ N := Real.rpow_nonneg
        (inv_nonneg.mpr ((band d).scale_pos' hE N (hv0 N) (hv1 N)).le) _
      have hNtarget0 : 0 ≤ (N : ℝ) ^ (-(c / 2)) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      nlinarith [hInv, hInvPow, hΨsq, hNtargetSq]
    have htrace := detAvgIBP_stochDom_of_localLaw_complete d
      hκ0 hκ1 hEκ hv0 hv1 (by linarith : 0 < c / 2) (by norm_num : 0 ≤ (1 : ℝ))
      hη hΨlo hΨhi hll
    have htraceLoop := htrace.precomp_param
      (fun N (q : LoopData ((band d).L N) 1) => q.2 0)
    have hΨsq : ∀ N, Ψ N * Ψ N = ((band d).scale E N (v N))⁻¹ := by
      intro N
      dsimp [Ψ]
      rw [← pow_two, ← Real.rpow_natCast,
        ← Real.rpow_mul
          (inv_nonneg.mpr ((band d).scale_pos' hE N (hv0 N) (hv1 N)).le)]
      norm_num
    have hpoint : ∀ N (q : LoopData ((band d).L N) 1) ω,
        ‖SumZeroDyn.lkT (sample d) E N (v N) ω q.1 q.2‖ =
          ‖Matrix.trace ((green (Hflow d N (v N) ω) (zt E (v N)) -
              mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) (q.2 0))‖ := by
      intro N q ω
      rw [SumZeroDyn.norm_lkT]
      exact lkErr_one_eq_norm_trace (sample d) q
    intro τ hτ D hD
    filter_upwards [htraceLoop τ hτ D hD] with N hN
    apply (measure_mono ?_).trans hN
    intro ω hω
    rcases hω with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    simpa [hΨsq N, hpoint N q ω] using hq
  have hHolSeq : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N,
      ∀ q : LoopData ((band d).L N) 1,
        ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
          |(band d).scale E N u ^ 1 *
                ‖SumZeroDyn.lkT (sample d) E N u ω q.1 q.2‖ -
              (band d).scale E N v ^ 1 *
                ‖SumZeroDyn.lkT (sample d) E N v ω q.1 q.2‖|
            ≤ (N : ℝ) ^ ((2 : ℝ) * (3 * (1 : ℝ) + 4) + 1) *
              |u - v| ^ ((1 : ℝ) / 2) := by
    simpa only [Nat.cast_one] using hHol
  have hresult := stochDom_flowXiLK_of_seq (sample d) hE hs0 hst ht1
    (m := 1) (Cv := (2 : ℝ)) hcard
    (K := (2 : ℝ) * (3 * (1 : ℝ) + 4) + 1) (γ := (1 : ℝ) / 2)
    (by norm_num) (by norm_num) hΞ (c := fun _ => (1 : ℝ))
    (by intro N; norm_num) (by exact Eventually.of_forall fun N => le_rfl)
    hHolSeq (by simpa only [pow_one, one_mul] using hseq)
  simpa [Step3.flowXiLK] using hresult

#print axioms stochDom_flowXiLK_one_of_gaussian_hypotheses

end RBM.Gauss.Lemma514OneLoopSharp
