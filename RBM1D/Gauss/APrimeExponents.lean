/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSlotArith

/-!
# T280d: scale interpolation for the first-pass A-prime slots

`Cond272Reg` consists of the printed (2.72), which gives `R^30 ≤ A_t`,
and a separate regime bound `N^c ≤ A_t`.  D20/§9 tried to multiply
these two lower bounds.  The implication fails even eventually in `N`.
The corrected calculation uses `Cond272Reg.margin` at each exponent below 30.
-/

namespace RBM.APrimeExponents

open Filter

/-- An eventual counterexample to the scale multiplication used in
`docs/CODEX-TICKETS.md` §9(7).  Both separate lower bounds hold with equality,
but their product is strictly larger than the same scale for all `N ≥ 2`.
Here `c = 30`, `R_N = N`, and `A_N = N^30`. -/
theorem not_eventually_product_scale_of_separate :
    ¬ (∀ (R A : ℕ → ℝ),
      (∀ᶠ N : ℕ in atTop, R N ^ 30 ≤ A N) →
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ 30 ≤ A N) →
      ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ 30 * R N ^ 30 ≤ A N) := by
  intro h
  have hprod := h (fun N => (N : ℝ)) (fun N => (N : ℝ) ^ 30)
    (Filter.Eventually.of_forall fun _ => le_rfl)
    (Filter.Eventually.of_forall fun _ => le_rfl)
  obtain ⟨N, hN⟩ := (hprod.and (eventually_ge_atTop 2)).exists
  rcases hN with ⟨hbad, hN2⟩
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hpow : (2 : ℝ) ^ 30 ≤ (N : ℝ) ^ 30 :=
    pow_le_pow_left₀ (by norm_num) hNr 30
  norm_num at hpow
  nlinarith

end RBM.APrimeExponents

namespace RBM.APrimeExponents

open Filter

/-! The corrected T280d margin account.  Exponents here refer only to monomials
`N^(a*δ) R^b / A`; the coefficients and the other factors in `QBd` require their
own model estimates. -/

/-- The four scale-sensitive exponent tests in the first-pass arithmetic.  The
last row is the `Λ³` far-field term of §11 and gives the smallest threshold. -/
theorem exponent_budget {c δ : ℝ} (hc : 0 < c) (_hδ : 0 ≤ δ) (hsmall : δ < c / 10) :
    (33 / 8 : ℝ) * δ < c * (1 - 10 / 30) ∧
    4 * δ < c * (1 - (11 / 2) / 30) ∧
    3 * δ < c * (1 - (9 / 2) / 30) ∧
    6 * δ < c * (1 - 12 / 30) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith

/-- A closed threshold usable with the outer `δ ≤ δ₀` quantifier.  The strict
margin inequality is retained even at `δ = δ₀`. -/
theorem delta_lt_c_div_ten_of_le_delta0 {c δ : ℝ} (hc : 0 < c)
    (hδ : δ ≤ c / 11) : δ < c / 10 := by
  linarith

/-- A reusable `a=1` consequence of `Cond272Reg.margin`.  The inequality is
uniform in `u`, so finitely many rows can be intersected under the same
regime and the same `N`. -/
theorem eventually_monomial_margin {Ω : Type*} [MeasurableSpace Ω]
    {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ} (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c δ a b : ℝ} (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hb0 : 0 ≤ b) (hb30 : b ≤ 30)
    (hbudget : a * δ ≤ c * (1 - b / 30)) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (N : ℝ) ^ (a * δ) * (etaT E (s N) / etaT E u) ^ b
        ≤ B.scale E N u := by
  have he : 0 ≤ c * (1 - b / 30) := mul_nonneg hc.le (by linarith)
  have hsum : (c * (1 - b / 30)) / c + b / 30 ≤ 1 := by
    have hc0 : c ≠ 0 := ne_of_gt hc
    field_simp [hc0]
    norm_num
  filter_upwards [hreg.margin hE hst ht1 hc he hb0 hsum,
    eventually_ge_atTop 1] with N hm hN1 u
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hpow : (N : ℝ) ^ (a * δ) ≤ (N : ℝ) ^ (c * (1 - b / 30)) :=
    Real.rpow_le_rpow_of_exponent_le hN1' hbudget
  have hR0 : 0 ≤ (etaT E (s N) / etaT E u) ^ b := by
    have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
    have hs1 : s N < 1 := lt_of_le_of_lt (hst N) (ht1 N)
    exact Real.rpow_nonneg (div_nonneg (etaT_pos hE hs1).le (etaT_pos hE hu1).le) _
  exact (mul_le_mul_of_nonneg_right hpow hR0).trans (by simpa only [Real.rpow_one] using hm u)

/-- All four scale rows share one regime and one eventual tail of `N`.
The second and third rows are the squared linear far coefficient and the
`3/2` far coefficient in `StepSide''`; the last is the cubic far term. -/
theorem eventually_first_pass_margin_rows {Ω : Type*} [MeasurableSpace Ω]
    {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ} (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (hsmall : δ < c / 10)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      ((N : ℝ) ^ ((33 / 8 : ℝ) * δ) *
            (etaT E (s N) / etaT E u) ^ (10 : ℝ) ≤ B.scale E N u) ∧
      ((N : ℝ) ^ (4 * δ) *
            (etaT E (s N) / etaT E u) ^ ((11 / 2 : ℝ)) ≤ B.scale E N u) ∧
      ((N : ℝ) ^ (3 * δ) *
            (etaT E (s N) / etaT E u) ^ ((9 / 2 : ℝ)) ≤ B.scale E N u) ∧
      ((N : ℝ) ^ (6 * δ) *
            (etaT E (s N) / etaT E u) ^ (12 : ℝ) ≤ B.scale E N u) := by
  obtain ⟨h1, h2, h3, h4⟩ := exponent_budget hc hδ hsmall
  have H1 := eventually_monomial_margin hE hst ht1 hc hreg
    (a := 33 / 8) (b := 10) (δ := δ) (by norm_num) (by norm_num) h1.le
  have H2 := eventually_monomial_margin hE hst ht1 hc hreg
    (a := 4) (b := 11 / 2) (δ := δ) (by norm_num) (by norm_num) h2.le
  have H3 := eventually_monomial_margin hE hst ht1 hc hreg
    (a := 3) (b := 9 / 2) (δ := δ) (by norm_num) (by norm_num) h3.le
  have H4 := eventually_monomial_margin hE hst ht1 hc hreg
    (a := 6) (b := 12) (δ := δ) (by norm_num) (by norm_num) h4.le
  filter_upwards [H1, H2, H3, H4] with N h1N h2N h3N h4N u
  exact ⟨h1N u, h2N u, h3N u, h4N u⟩

/-- The exact `b = 12` interpolation supplied by `Cond272Reg.margin`.
It holds uniformly at every time in the window. -/
theorem eventually_far_twelve_margin {Ω : Type*} [MeasurableSpace Ω]
    {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ} (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc : 0 < c) (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (N : ℝ) ^ (3 * c / 5) * (etaT E (s N) / etaT E u) ^ (12 : ℝ)
        ≤ B.scale E N u := by
  have hsum : (3 * c / 5) / c + (12 : ℝ) / 30 ≤ 1 := by
    have hc0 : c ≠ 0 := ne_of_gt hc
    field_simp [hc0]
    norm_num
  simpa only [Real.rpow_one] using
    (hreg.margin hE hst ht1 hc (by linarith) (by norm_num) hsum)

/-- The endpoint form required when the a priori level uses the full-window
ratio `R = η_s/η_t`, while a QV envelope is evaluated at an earlier time. -/
theorem eventually_endpoint_far_twelve_margin {Ω : Type*} [MeasurableSpace Ω]
    {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ} (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc : 0 < c) (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (3 * c / 5) * (etaT E (s N) / etaT E (t N)) ^ (12 : ℝ)
        ≤ B.scale E N (t N) := by
  filter_upwards [eventually_far_twelve_margin hE hst ht1 hc hreg] with N hN
  exact hN ⟨t N, hst N, le_rfl⟩

/-- The far-field quotient has a negative power of `N` when `δ < c/10`.
This is the arithmetic implication from §11; obtaining the far-field term
itself from `QBd` is a separate model estimate. -/
theorem eventually_far_twelve_quotient {Ω : Type*} [MeasurableSpace Ω]
    {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ} (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c δ : ℝ} (hc : 0 < c) (_hδ : 0 ≤ δ) (hsmall : δ < c / 10)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (N : ℝ) ^ (6 * δ) * (etaT E (s N) / etaT E u) ^ (12 : ℝ)
          / B.scale E N u
        ≤ (N : ℝ) ^ (6 * δ - 3 * c / 5) := by
  have _hneg : 6 * δ - 3 * c / 5 < 0 := by linarith
  filter_upwards [eventually_far_twelve_margin hE hst ht1 hc hreg,
    eventually_ge_atTop 1] with N hmargin hN1 u
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hR : 0 < etaT E (s N) / etaT E u := by
    have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
    have hs1 : s N < 1 := lt_of_le_of_lt (hst N) (ht1 N)
    have hηs : 0 < etaT E (s N) := etaT_pos hE hs1
    have hηu : 0 < etaT E u := etaT_pos hE hu1
    positivity
  have hA : 0 < B.scale E N u :=
    lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hR _))
      (hmargin u)
  rw [div_le_iff₀ hA]
  have hpow : (N : ℝ) ^ (6 * δ) =
      (N : ℝ) ^ (6 * δ - 3 * c / 5) * (N : ℝ) ^ (3 * c / 5) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  rw [hpow]
  nlinarith [mul_le_mul_of_nonneg_left (hmargin u)
    (Real.rpow_nonneg hN.le (6 * δ - 3 * c / 5))]

/-- At the right endpoint, the full-window ratio in the cubic a priori level
is controlled by the endpoint scale itself. -/
theorem eventually_endpoint_far_twelve_quotient {Ω : Type*} [MeasurableSpace Ω]
    {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ} (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (hsmall : δ < c / 10)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (6 * δ) * (etaT E (s N) / etaT E (t N)) ^ (12 : ℝ)
          / B.scale E N (t N)
        ≤ (N : ℝ) ^ (6 * δ - 3 * c / 5) := by
  filter_upwards [eventually_far_twelve_quotient hE hst ht1 hc hδ hsmall hreg]
    with N hN
  exact hN ⟨t N, hst N, le_rfl⟩

/-! §14 proposed using the same `β` row for the quadratic far-field summand of
`QBd`.  After `Λ² = N^(4δ) R^8` cancels the endpoint normalization `R^8`,
`sMax ≤ N^τ r³ A_u^(-3)` leaves `N^(4δ) r^(3/2) A_u^(-1/2)`.
Even granting the favorable logarithmic time integral, multiplication by the
`4R^4` required by `eventually_slot_arith_of_detDom` gives the square budget
`N^(8δ) R^(19/2) / A_t` (`r² ≤ R`).  Thus its margin threshold is
`δ < 41c/480`, strictly below the proposed closed threshold `c/11`.
This calculation omits the nonnegative `N^τ` loss and all coefficients. -/

/-- The quadratic far-field exponent row exceeds the available
`Cond272Reg.margin` exponent at `δ = c/11`. -/
theorem quadratic_far_margin_excess_at_delta0 {c : ℝ} (hc : 0 < c) :
    0 < 8 * (c / 11) - c * (1 - ((19 / 2 : ℝ) / 30)) := by
  norm_num
  linarith

/-- The §14 claim that the quadratic far row fits the previous `δ₀=c/11`
budget is false, even with the optimistic logarithmic time integration. -/
theorem not_quadratic_far_margin_budget_at_delta0 {c : ℝ} (hc : 0 < c) :
    ¬ 8 * (c / 11) ≤ c * (1 - ((19 / 2 : ℝ) / 30)) := by
  linarith [quadratic_far_margin_excess_at_delta0 hc]

/-- The actual `G=(t-s)·QBd` envelope can cost one more `R` than an
integrated rate.  Squaring gives `b=23/2` and a still smaller threshold. -/
theorem not_quadratic_far_sup_margin_budget_at_delta0 {c : ℝ} (hc : 0 < c) :
    ¬ 8 * (c / 11) ≤ c * (1 - ((23 / 2 : ℝ) / 30)) := by
  norm_num
  linarith

/-! §15 allows shrinking `δ₀`; this fixes the preceding quadratic row.
The additive `(2.73)` remainder is different: the `QBd` numerator contains
`W L ρ`, while its endpoint normalization contains `T_t²`.  At distance zero,
`ρ=A_u^(-5)` and the principal part of `T_t` is `A_t^(-2)`.
Even at `R=1`, `r=1`, and `A_u=A_t=W`, those powers leave the growing factor
`L`, independently of `δ`. -/

/-- Exact algebraic obstruction in the `ρfar` summand of `QBd`: at the
near-distance principal tail scale `T_t=W^(-2)`, the term is `L`.
This uses the actual `EarlyQVRateEv.rho0` formula at `ℓ=η=r=1`. -/
theorem rho_row_eq_length_at_principal_tail {W L : ℝ} (hW : 0 < W) :
    W * L * EarlyQVRateEv.rho0 W 1 1 1 / (W ^ (-2 : ℝ)) ^ 2 = L := by
  have hW0 : W ≠ 0 := ne_of_gt hW
  unfold EarlyQVRateEv.rho0
  simp only [mul_one, Real.rpow_neg hW.le]
  field_simp
  simp only [Real.rpow_two]
  ring

/-- Consequently the bare `QBd` parameter interface cannot bound the
`ρfar` summand uniformly in the length parameter without another spatial
estimate.  This certificate uses the principal near-distance tail scale;
it is not a counterexample for a far-pair model with extra information. -/
theorem no_uniform_rho_row_at_principal_tail {W : ℝ} (hW : 0 < W) :
    ¬ ∃ C : ℝ, ∀ L : ℝ, 0 ≤ L →
      W * L * EarlyQVRateEv.rho0 W 1 1 1 / (W ^ (-2 : ℝ)) ^ 2 ≤ C := by
  rintro ⟨C, hC⟩
  have hL0 : 0 ≤ max C 0 + 1 := by linarith [le_max_right C 0]
  have h := hC (max C 0 + 1) hL0
  rw [rho_row_eq_length_at_principal_tail hW] at h
  linarith [le_max_left C 0]

/-- Shrinking to the selectable `δ₀=c/20` repairs both inverse-scale
far-field exponent rows before the independent `ρfar` obstruction. -/
theorem far_rows_budget_at_c_div_twenty {c δ : ℝ} (hc : 0 < c)
    (hδ : δ ≤ c / 20) :
    8 * δ < c * (1 - ((23 / 2 : ℝ) / 30)) ∧
      6 * δ < c * (1 - (9 : ℝ) / 30) := by
  constructor <;> norm_num <;> linarith

/-! §17 replaces the `ρfar` slot of the new envelope by zero and carries
the near remainder as a separate `ε·T_u²` row.  The `ε` producer is not in
this module: the inequality below assumes only `0 ≤ ε`. -/

/-- `T_{u,D}(d) ≤ T_{t,D}(d)` on one flow window.  The length monotonicity
and the scale antitonicity are exactly the premises of `Cutoff.tailT_le_tailT_of_flow`. -/
theorem tailT_le_endpoint {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
    {E : ℝ} {s t : ℕ → ℝ} (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1) {N : ℕ} (u : TimeIcc s t N) {D d : ℝ}
    (hd : 0 ≤ d) :
    tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D d ≤
      tailT (B.W N : ℝ) (B.ell N (t N)) (etaT E (t N)) D d := by
  have hL : 1 ≤ B.L N := B.one_le_L N
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hℓu : 0 < B.ell N u := Step3.ellHat_pos_of_lt_one hL hu1
  have hℓ : B.ell N u ≤ B.ell N (t N) :=
    Step3.ellHat_mono u.2.2 (ht1 N)
  have hℓt : 0 < B.ell N (t N) := Step3.ellHat_pos_of_lt_one hL (ht1 N)
  have hAt : 0 < (B.W N : ℝ) * B.ell N (t N) * etaT E (t N) := by
    exact mul_pos (mul_pos hW hℓt) (etaT_pos hE (ht1 N))
  have hAle : B.scale E N (t N) ≤ B.scale E N u := by
    rw [B.scale_eq_flowScale, B.scale_eq_flowScale]
    exact flowScale_antitoneOn hW.le (B.L N) E
      (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 (ht1 N).le) u.2.2
  exact Cutoff.tailT_le_tailT_of_flow hd hℓu hℓ hAt hAle

/-- The §17 near remainder has no inverse endpoint tail factor after
time comparison and `R≥1`. -/
theorem epsilon_tail_row_le {ε Tu Tt R : ℝ} (hε : 0 ≤ ε)
    (hTu : 0 ≤ Tu) (hTt : 0 < Tt) (hT : Tu ≤ Tt) (hR : 1 ≤ R) :
    2 * ε * Tu ^ 2 / (Tt * R ^ 4) ^ 2 ≤ 2 * ε := by
  have hR4 : 1 ≤ R ^ 4 := one_le_pow₀ hR
  have hden : 0 < (Tt * R ^ 4) ^ 2 := by positivity
  have hnum : Tu ^ 2 ≤ Tt ^ 2 := pow_le_pow_left₀ hTu hT 2
  have hmul : Tt ≤ Tt * R ^ 4 := by
    nlinarith [mul_nonneg hTt.le (sub_nonneg.mpr hR4)]
  have hden2 : Tt ^ 2 ≤ (Tt * R ^ 4) ^ 2 :=
    pow_le_pow_left₀ hTt.le hmul 2
  have hratio : Tu ^ 2 / (Tt * R ^ 4) ^ 2 ≤ 1 :=
    (div_le_one hden).2 (hnum.trans hden2)
  calc
    2 * ε * Tu ^ 2 / (Tt * R ^ 4) ^ 2 = (2 * ε) * (Tu ^ 2 / (Tt * R ^ 4) ^ 2) := by ring
    _ ≤ (2 * ε) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 2 * ε := by ring

/-- The `W^{-D}` summand keeps its explicit small bandwidth factor after the
same time comparison.  `N≥W L` is the dimension bound of `Band.dim`. -/
theorem bandwidth_tail_row_le {W L N D Λ Tu Tt R : ℝ}
    (hW : 0 < W) (hL : 0 ≤ L) (hWL : W * L ≤ N) (hΛ : 0 ≤ Λ)
    (hTu : 0 ≤ Tu) (hTt : 0 < Tt) (hT : Tu ≤ Tt) (hR : 1 ≤ R) :
    16 * W * L * W ^ (-D) * StepSideAPrime.cWt ^ 3 * Λ ^ 3 * Tu ^ 2 /
        (Tt * R ^ 4) ^ 2
      ≤ 16 * N * W ^ (-D) * StepSideAPrime.cWt ^ 3 * Λ ^ 3 := by
  have hratio : Tu ^ 2 / (Tt * R ^ 4) ^ 2 ≤ 1 := by
    simpa using epsilon_tail_row_le (ε := (1 : ℝ) / 2) (Tu := Tu) (Tt := Tt)
      (R := R) (by norm_num) hTu hTt hT hR
  have hcWt : 0 < StepSideAPrime.cWt := StepSideAPrime.cWt_pos
  have hcoef : 0 ≤ 16 * W * L * W ^ (-D) * StepSideAPrime.cWt ^ 3 * Λ ^ 3 := by
    positivity
  calc
    16 * W * L * W ^ (-D) * StepSideAPrime.cWt ^ 3 * Λ ^ 3 * Tu ^ 2 /
        (Tt * R ^ 4) ^ 2
      = (16 * W * L * W ^ (-D) * StepSideAPrime.cWt ^ 3 * Λ ^ 3) *
          (Tu ^ 2 / (Tt * R ^ 4) ^ 2) := by ring
    _ ≤ 16 * W * L * W ^ (-D) * StepSideAPrime.cWt ^ 3 * Λ ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hratio hcoef]
    _ ≤ 16 * N * W ^ (-D) * StepSideAPrime.cWt ^ 3 * Λ ^ 3 := by
      have hfac : 0 ≤ 16 * W ^ (-D) * StepSideAPrime.cWt ^ 3 * Λ ^ 3 := by
        positivity
      nlinarith [mul_le_mul_of_nonneg_right hWL hfac]

/-- The corrected T280g-shaped deterministic envelope.  The old additive
`ρfar` slot is set to zero; the near-only residual is carried separately as
`2 ε T_u²/(T_t R⁴)²`.  Its model producer remains a named input. -/
noncomputable def QBdNearRem (Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε : ℝ) : ℝ :=
  APrimePrior.QBd Wr ℓu ℓs ηu D Λ Smax 0 Lr Tu Tt R +
    2 * ε * Tu ^ 2 / (Tt * R ^ 4) ^ 2

/-- The near remainder contributes at most `2ε` to the corrected envelope. -/
theorem QBdNearRem_le_of_tail {Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε : ℝ}
    (hε : 0 ≤ ε) (hTu : 0 ≤ Tu) (hTt : 0 < Tt) (hT : Tu ≤ Tt)
    (hR : 1 ≤ R) :
    QBdNearRem Wr ℓu ℓs ηu D Λ Smax Lr Tu Tt R ε ≤
      APrimePrior.QBd Wr ℓu ℓs ηu D Λ Smax 0 Lr Tu Tt R + 2 * ε := by
  unfold QBdNearRem
  gcongr
  exact epsilon_tail_row_le hε hTu hTt hT hR

/-- T268's integral estimates do not constrain the independent constant
drift envelope `Qb` in `fitLhs`.  Even with `Qm=0`, a polynomial `Qb`
makes `fitLhs` fail `≺1`.  This is a statement about the open arithmetic
interface, not a counterexample to the model drift estimate. -/
theorem not_fitLhs_detDom_for_arbitrary_Qb :
    ¬ ∀ Qb : ℕ → ℝ,
      (fun N => APrimeSlotArith.fitLhs 0 (N : ℝ) (1 / 4) (Qb N) 0 0 (1 / 20))
        ≺ (fun _ => 1) := by
  intro h
  have hdom := h (fun N => (N : ℝ) ^ 2)
  have htail := (detDom_iff.1 hdom) 1 (by norm_num)
  obtain ⟨N, hN⟩ := (htail.and (eventually_ge_atTop 3)).exists
  rcases hN with ⟨hfit, hN3⟩
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have heq : APrimeSlotArith.fitLhs 0 (N : ℝ) (1 / 4) ((N : ℝ) ^ 2)
      0 0 (1 / 20) = (N : ℝ) ^ 2 / 2 := by
    simp [APrimeSlotArith.fitLhs]
    ring
  rw [heq, Real.rpow_one, mul_one] at hfit
  nlinarith

end RBM.APrimeExponents
