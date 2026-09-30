/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.StepGlue
import RBM1D.EnergyN.Hierarchy.Step3
import RBM1D.EnergyN.Flow.Hypotheses
import RBM1D.Flow.EnergyUniform

/-!
# Flow inputs of Steps 3–5 at an `N`-dependent energy

The energy-dependent lemmas that connect the flow bounds with the abstract estimates of Step 3,
at an `N`-dependent energy `E : ℕ → ℝ`.

## The external `κ`

`RBM.StepGlue.flow_S_zero'N` takes its kernel constant `C` from the uniform
`RBM.Step3.exists_norm_Kval_le_unif` (which needs `κ ≤ 1`), obtained once before `N`, and
instantiates its `∀ E, |E| ≤ 2 - κ → …` at each `E N` via `hEκ N`.

## Eta-expansion of `Step3.flowXiLK`/`.flowAs`/`.flowA`/`.S`/`.Lemma514`

None of these combinators fixes an energy-dependent constant: each is a plain deterministic
family/def at a single `E : ℝ`, used at `E N` through the eta-expansion
`fun N u ω => Step3.flowXiLK X (E N) s t m N u ω` etc., as in
`Step3.flow_xiL_leN`/`.hyp_flowN`.
-/

namespace RBM

namespace StepGlue

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **`Ξ^{(L-K)}_{u,m} ≺ f_u (W ℓ_u η_u)^m`** from `|L - K| ≺ f_u` for the loops of length `m`.
No energy-dependent constant is fixed here. -/
theorem stochDom_flowXiLKN (X : Sample B) {m : ℕ} {f : ∀ N, TimeIcc s t N → ℝ}
    (hA : ∀ N (u : TimeIcc s t N), 0 ≤ B.scale (E N) N u)
    (h : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => X.lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => f N p.1)) :
    StochDom B.P (fun N u ω => Step3.flowXiLK X (E N) s t m N u ω)
      (fun N u _ => f N u * B.scale (E N) N u ^ m) := by
  refine StochDom.of_subset_union h h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨u, hu⟩
  by_cases h' : ∃ p : TimeIcc s t N × LoopData (B.L N) m,
      (N : ℝ) ^ τ * f N p.1 < X.lkErr (E N) N p.1 ω p.2.idx
  · exact Or.inl h'
  · exfalso
    have hall : ∀ v : LoopData (B.L N) m, X.lkErr (E N) N u ω v.idx ≤ (N : ℝ) ^ τ * f N u :=
      fun v => not_lt.1 fun hc => h' ⟨(u, v), hc⟩
    have hmax : X.lkMax (E N) N u ω m ≤ (N : ℝ) ^ τ * f N u := ciSup_le hall
    have hApow : (0 : ℝ) ≤ B.scale (E N) N u ^ m := pow_nonneg (hA N u) _
    have : Step3.flowXiLK X (E N) s t m N u ω ≤ (N : ℝ) ^ τ * (f N u * B.scale (E N) N u ^ m) := by
      show X.lkMax (E N) N u ω m * B.scale (E N) N u ^ m ≤ _
      calc X.lkMax (E N) N u ω m * B.scale (E N) N u ^ m
          ≤ ((N : ℝ) ^ τ * f N u) * B.scale (E N) N u ^ m :=
            mul_le_mul_of_nonneg_right hmax hApow
        _ = (N : ℝ) ^ τ * (f N u * B.scale (E N) N u ^ m) := by ring
    exact absurd hu (not_lt.2 this)

/-- **The estimate `S(m, 0)` of Step 3 for the flow**, from the a priori bound (2.73) and (2.72).
The kernel constant is the uniform one of `RBM.Step3.exists_norm_Kval_le_unif`. -/
theorem flow_S_zero'N (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272N B E s t) (hapriori : AprioriFlowN X E s t) (m : ℕ) (hm : 1 ≤ m) :
    Step3.S B.P (fun n N u ω => Step3.flowXiLK X (E N) s t n N u ω)
      (fun N => Step3.flowAs B (E N) s N) (Step3.flowR B s t)
      (fun N u => Step3.flowA B (E N) s t N u) m 0 := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale (E N) N u := fun N u =>
    B.scale_pos' (hE N) N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have sc := Step3.scales_flowN (E := E) (s := s) (t := t) hE hs0 hst ht1 hc
  obtain ⟨C, hC0, hC⟩ := Step3.exists_norm_Kval_le_unif (B := B) hκ0 hκ1 hs0 ht1 hm
  set R : ℕ → ℝ := Step3.flowR B s t with hRdef
  -- (2.73): the a priori loop bound
  have hL := hapriori m hm
  -- (2.59): the deterministic bound on `K`, uniform `C`
  have hKle : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) (_ : Ω) => ‖B.Kval (E N) N p.1 p.2.idx‖)
      (fun N p _ => C * (B.scale (E N) N p.1)⁻¹ ^ (m - 1)) :=
    StochDom.of_unifDetDom (UnifDetDom.of_eventually_le_const_mul
      (fun N p => mul_nonneg hC0 (pow_nonneg (inv_nonneg.2 (hA N p.1).le) _)) 1
      (Eventually.of_forall fun N p => by simpa using hC (E N) (hEκ N) N p.1 p.2))
  -- `|L - K| ≤ |L| + |K|`
  have hsum : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => X.lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (m - 1) * (B.scale (E N) N p.1)⁻¹ ^ (m - 1)
        + C * (B.scale (E N) N p.1)⁻¹ ^ (m - 1)) := by
    refine StochDom.of_le_left (fun N p ω => ?_) (hL.add hKle)
    exact norm_sub_le _ _
  -- collapse to `(1 + C) R^{m-1} (W ℓ_u η_u)^{-(m-1)}`
  have hcollapse : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => X.lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => R N ^ (m - 1) * (B.scale (E N) N p.1)⁻¹ ^ (m - 1)) := by
    refine Step3.stochDom_mono (fun N p _ => mul_nonneg (pow_nonneg (sc.R_nonneg N) _)
      (pow_nonneg (inv_nonneg.2 (hA N p.1).le) _)) (1 + C) ?_ hsum
    filter_upwards [sc.one_le_R] with N hR p _
    have hℓs : 0 < B.ell N (s N) :=
      Step3.ellHat_pos_of_lt_one (B.one_le_L N) ((hst N).trans_lt (ht1 N))
    have hℓu : B.ell N p.1 ≤ B.ell N (t N) := Step3.ellHat_mono p.1.2.2 (ht1 N)
    have hratio : B.ell N p.1 / B.ell N (s N) ≤ R N :=
      div_le_div_of_nonneg_right hℓu hℓs.le
    have hr0 : 0 ≤ B.ell N p.1 / B.ell N (s N) := by
      have := (Step3.ellHat_pos_of_lt_one (L := B.L N) (B.one_le_L N)
        (p.1.2.2.trans_lt (ht1 N))).le
      positivity
    have hpow : (B.ell N p.1 / B.ell N (s N)) ^ (m - 1) ≤ R N ^ (m - 1) :=
      pow_le_pow_left₀ hr0 hratio _
    have hR1 : (1 : ℝ) ≤ R N ^ (m - 1) := one_le_pow₀ hR
    have hinv : (0 : ℝ) ≤ (B.scale (E N) N p.1)⁻¹ ^ (m - 1) :=
      pow_nonneg (inv_nonneg.2 (hA N p.1).le) _
    have h1 := mul_le_mul_of_nonneg_right hpow hinv
    have h2 : C * (B.scale (E N) N p.1)⁻¹ ^ (m - 1)
        ≤ C * (R N ^ (m - 1) * (B.scale (E N) N p.1)⁻¹ ^ (m - 1)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hinv hR1) hC0
    nlinarith
  -- pass to `Ξ^{(L-K)}`
  have hXi := stochDom_flowXiLKN X (f := fun N (u : TimeIcc s t N) =>
    R N ^ (m - 1) * (B.scale (E N) N u)⁻¹ ^ (m - 1)) (fun N u => (hA N u).le) hcollapse
  -- and compare with `Ψ(m,0)`
  refine Step3.stochDom_mono (fun N u _ => Step3.psi_nonneg (sc.As_pos N).le (sc.R_nonneg N)
    (sc.A_pos N u).le) 1 ?_ hXi
  filter_upwards with N u _
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hAu : (0 : ℝ) < B.scale (E N) N u := hA N u
  have hkey : R N ^ (j + 1 - 1) * (B.scale (E N) N u)⁻¹ ^ (j + 1 - 1) * B.scale (E N) N u ^ (j + 1)
      = R N ^ j * B.scale (E N) N u := by
    simp only [Nat.add_sub_cancel]
    rw [inv_pow, pow_succ, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hAu.ne')]
  rw [hkey, one_mul, Step3.psi_zero]
  have : (0 : ℝ) ≤ Step3.flowAs B (E N) s N ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (sc.As_pos N).le _
  have hAs : Step3.flowAs B (E N) s N ^ ((1 : ℝ) / 2) +
      R N ^ (j + 1 - 1) * Step3.flowA B (E N) s t N u
      = Step3.flowAs B (E N) s N ^ ((1 : ℝ) / 2) + R N ^ j * B.scale (E N) N u := by
    simp [Step3.flowA]
  rw [hAs]
  linarith

/-- **`|L_{u,σ,a} - K_{u,σ,a}| ≺ (W ℓ_u η_u)^{-1/2}` for the loops of length 1**, from the local
law (2.75). No energy-dependent constant is fixed here. -/
theorem flow_lkErr_one_le'N (X : Sample B) (hll : LocalLawFlowN X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 1) ω => X.lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ ((1 : ℝ) / 2)) := by
  refine StochDom.of_subset_union hll hll
    fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨p, hp⟩
  by_cases h' : ∃ q : TimeIcc s t N × (B.Idx N × B.Idx N),
      (N : ℝ) ^ τ * (B.scale (E N) N q.1)⁻¹ ^ ((1 : ℝ) / 2) < X.llErr (E N) N q.1 ω q.2
  · exact Or.inl h'
  · exfalso
    have hall : ∀ ij : B.Idx N × B.Idx N,
        X.llErr (E N) N p.1 ω ij ≤ (N : ℝ) ^ τ * (B.scale (E N) N p.1)⁻¹ ^ ((1 : ℝ) / 2) :=
      fun ij => not_lt.1 fun hcon => h' ⟨(p.1, ij), hcon⟩
    exact absurd hp (not_lt.2 (norm_lkErr_one_le X p.2 hall))

/-- **The estimate `S(1, l)` of Step 3 for the flow**, from the local law (2.75) and (2.72). No
energy-dependent constant is fixed here. -/
theorem flow_S_one'N (X : Sample B) (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t)
    (hll : LocalLawFlowN X E s t) (l : ℕ) :
    Step3.S B.P (fun n N u ω => Step3.flowXiLK X (E N) s t n N u ω)
      (fun N => Step3.flowAs B (E N) s N) (Step3.flowR B s t)
      (fun N u => Step3.flowA B (E N) s t N u) 1 l := by
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale (E N) N u := fun N u =>
    B.scale_pos' (hE N) N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have sc := Step3.scales_flowN (E := E) (s := s) (t := t) hE hs0 hst ht1 hc
  have hXi := stochDom_flowXiLKN X (f := fun N (u : TimeIcc s t N) =>
    (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 2)) (fun N u => (hA N u).le) (flow_lkErr_one_le'N X hll)
  refine Step3.stochDom_mono (fun N u _ => Step3.psi_nonneg (sc.As_pos N).le (sc.R_nonneg N)
    (sc.A_pos N u).le) 1 ?_ hXi
  filter_upwards [sc.A_le_As] with N hle u _
  have hA0 : 0 < B.scale (E N) N u := hA N u
  have hsq : B.scale (E N) N u ^ ((1 : ℝ) / 2) * B.scale (E N) N u ^ ((1 : ℝ) / 2)
      = B.scale (E N) N u := by
    rw [← Real.rpow_add hA0]; norm_num
  have hval : (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 2) * B.scale (E N) N u ^ 1
      = B.scale (E N) N u ^ ((1 : ℝ) / 2) := by
    rw [Real.inv_rpow hA0.le, pow_one,
      inv_mul_eq_iff_eq_mul₀ (Real.rpow_pos_of_pos hA0 _).ne']
    exact hsq.symm
  rw [hval, one_mul]
  refine le_trans ?_ (rpow_half_le_psi (sc.As_pos N).le (sc.R_nonneg N) (sc.A_pos N u).le 1 l)
  exact Real.rpow_le_rpow hA0.le (hle u) (by norm_num)

/-- **`|L_{u,(+,-),a} - K_{u,(+,-),a}| ≺ (η_s/η_u)^4 (W ℓ_u η_u)^{-2}`**, from (2.76) at `D = 1`.
No energy-dependent constant is fixed here. -/
theorem aprioriDecay_pm'N (X : Sample B) (ht1 : ∀ N, t N < 1)
    (hdecay : AprioriDecayFlowN X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT (E N) (s N) / etaT (E N) p.1) ^ 4 * (B.scale (E N) N p.1)⁻¹ ^ 2) := by
  refine Step3.stochDom_mono (fun N p _ => by positivity) 2
    (Eventually.of_forall fun N p _ => ?_) (hdecay 1 one_pos)
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hℓ : 0 < B.ell N p.1 := Step3.ellHat_pos_of_lt_one (B.one_le_L N) hu1
  have hdecay : B.decayProf N p.1 1 p.2.1 p.2.2 ≤ 2 := by
    have h1 : Real.exp (-(((zdist (B.L N) (p.2.1 - p.2.2) : ℝ) / B.ell N p.1) ^
        ((1 : ℝ) / 2))) ≤ 1 := by
      refine Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg ?_ _))
      positivity
    have h2 : (B.W N : ℝ) ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
    rw [Band.decayProf]
    linarith
  have hpre : (0 : ℝ) ≤ (etaT (E N) (s N) / etaT (E N) p.1) ^ 4 * (B.scale (E N) N p.1)⁻¹ ^ 2 := by
    positivity
  nlinarith

/-- Under (2.72) and `N^c ≤ W ℓ_t η_t` eventually: eventually, for all `u ∈ [s, t]`,
`(η_s/η_u)^4 ≤ W ℓ_u η_u` and `N^c ≤ W ℓ_u η_u`. No energy-dependent constant is fixed here. -/
theorem eventually_R4_le_scale_of_cond272N (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hcond : Cond272N B E s t)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N)) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT (E N) (s N) / etaT (E N) u) ^ 4 ≤ B.scale (E N) N u ∧
        (N : ℝ) ^ c ≤ B.scale (E N) N u := by
  filter_upwards [hcond, hreg] with N hN hNc u
  have hW0 : (0 : ℝ) ≤ B.W N := by positivity
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have h1s : 0 < 1 - s N := by linarith
  have hAt0 : 0 < B.scale (E N) N (t N) :=
    B.scale_pos' (hE N) N ((hs0 N).trans (hst N)) (ht1 N)
  have hAv : B.scale (E N) N (t N) ≤ B.scale (E N) N u := flowScale_antitoneOn hW0 (B.L N) (E N)
    (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 (ht1 N).le) u.2.2
  -- (2.72), inverted
  have hQ30 : ((1 - s N) / (1 - t N)) ^ 30 ≤ B.scale (E N) N (t N) := by
    have hinv := inv_anti₀ (inv_pos.2 hAt0) hN
    rw [inv_inv] at hinv
    have heq : ((1 - s N) / (1 - t N)) ^ 30 = (((1 - t N) / (1 - s N)) ^ 30)⁻¹ := by
      rw [← inv_pow, inv_div]
    rw [heq]; exact hinv
  have hR1 : 1 ≤ etaT (E N) (s N) / etaT (E N) u := by
    rw [Step2.etaT_ratio (hE N), le_div_iff₀ h1u]; linarith [u.2.1]
  have hRt : etaT (E N) (s N) / etaT (E N) u ≤ (1 - s N) / (1 - t N) := by
    rw [Step2.etaT_ratio (hE N)]
    exact div_le_div_of_nonneg_left h1s.le h1t (by linarith [u.2.2])
  refine ⟨?_, hNc.trans hAv⟩
  calc (etaT (E N) (s N) / etaT (E N) u) ^ 4 ≤ ((1 - s N) / (1 - t N)) ^ 4 :=
        pow_le_pow_left₀ (by linarith) hRt 4
    _ ≤ ((1 - s N) / (1 - t N)) ^ 30 :=
        pow_le_pow_right₀ (hR1.trans hRt) (by norm_num)
    _ ≤ B.scale (E N) N (t N) := hQ30
    _ ≤ B.scale (E N) N u := hAv

end StepGlue

end RBM
