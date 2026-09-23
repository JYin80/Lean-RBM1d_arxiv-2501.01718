/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.StochDomMono
import RBM1D.Flow.FlowFamiliesCore
import RBM1D.Flow.Iteration

/-!
# Step 3 of the proof of Theorem 2.21: the sharp loop bound (2.77)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.6 (pp. 69–72): the quantities
(5.76), the relations (5.107), the control parameter (5.108), the double induction (5.109)
and its consequence (2.77), with (5.111), (5.119), (5.120).

**Given Lemma 5.14 (5.92) as a hypothesis, Step 3 is deterministic**: everything here is
`≺`-calculus plus real inequalities between the scales.  Nothing is an `axiom`.

## The abstract formulation (for Steps 4–6, T55/T56)

Notation: `A_u = W ℓ_u η_u`, `A_s = W ℓ_s η_s`, `R = ℓ_t/ℓ_s`.  The step is stated over

* a parameter type `U : ℕ → Type*` (the times `u ∈ [s,t]` at index `N`),
* `X Y : ℕ → ∀ N, U N → Ω → ℝ` — the families `X n = Ξ^{(L-K)}_{·,n}`, `Y n = Ξ^{(L)}_{·,n}`,
* deterministic scales `A : ∀ N, U N → ℝ` (`A_u`), `As R : ℕ → ℝ` (`A_s`, `ℓ_t/ℓ_s`).

`≺` is `RBM.StochDom P` (Definition 2.1 (i)), **uniform in the time `u ∈ U N`**; this is the
paper's `max_{u ∈ [s,t]} … ≺ …`.  Deterministic `≺` is the special case `Ω = Unit`,
`P = Measure.dirac ()`.

* `RBM.Step3.Psi As R n k`, `RBM.Step3.psi As R Au n k` — **(5.108)** `Ψ(n,k,s,u,t)`.
* `RBM.Step3.S P X As R A n k` — the estimate **`S(n,k,s,u,t)`**: `X n ≺ Ψ(n,k)`.
* `RBM.Step3.Scales As R A` — the scale conditions (positivity; eventually `1 ≤ A_s`, `1 ≤ R`,
  `A_u ≤ A_s`, `R² A_s^{3/4} ≤ A_u`).  These are what "(2.72)" contributes to Step 3;
  `RBM.Step3.scale_facts_of_cond272` / `RBM.Step3.scales_flow` derive them from (2.72).
* `RBM.Step3.Lemma514 P X Y A n` — **Lemma 5.14 (5.92)** in the form used in (5.112).
* `RBM.Step3.Hyp P X Y As R A` — the bundle: `Scales`, non-negativity, (5.107) (first half,
  `n ≥ 3`), (5.118) (pointwise, any split), and `Lemma514` for `n ≥ 3`.

## Main results (abstract)

* `xiL_5119` — **(5.119)**; `rhs5119_le` — **(5.120)** (deterministic, constant `4`);
  `xiL_two_mul_add_two` — **(5.111)** `Ξ^{(L)}_{u,2n+2} ≺ Ψ(n,k)²`.
* `S_of_S` — **(5.109)**: `S(m,k)` for `m ≤ n-1` and `S(m,k-1)` for `m ≤ n+2` (and `S(2,3)`)
  give `S(n,k)`, for `n ≥ 3`, `k ≥ 1`.  Proof = (5.111)–(5.113).
* `S_all` — the double induction: `S(n,k)` for all `n ≥ 1`, `k`, from `S(m,0)` (`m ≥ 1`) and
  `S(m,l)` (`m ≤ 2`).
* `xiLK_le` — `Ξ^{(L-K)}_{u,n} ≺ (W ℓ_s η_s)^{1/2}` (take `k = n + 1`).
* `xiL_le_one`, `xiL_le_one_of` — **(2.77)** `Ξ^{(L)}_{u,n} ≺ 1`, via (5.107).

## The flow (concrete)

* `RBM.Sample.xiL`, `RBM.Sample.xiLK` — **(5.76)** `Ξ^{(L)}_{t,m}`, `Ξ^{(L-K)}_{t,m}`
  (`xiL` is `RBM.loopXi` of `Loop/Split.lean` at `H = H_t`, `z = z_t`).
* `RBM.Sample.xiL_le_add`, `RBM.Sample.xiLK_le_mul` — **(5.107)**, pointwise, from a bound
  `|K| ≤ C (W ℓ_t η_t)^{-m+1}` (2.59).
* `flowXiL`, `flowXiLK`, `flowA`, `flowAs`, `flowR` — the families on `u ∈ [s,t]`
  (`RBM.TimeIcc s t N`); `scales_flow` (from (2.72)); `flow_xiL_le` ((5.107) from
  `RBM.Band.norm_Kval_le`, every `n ≥ 1`), `flow_xiL_le_one_len` (`n = 1`); `hyp_flow` (the
  bundle, given `Lemma514`).
* `flow_sharpLoop` — **(2.77)** for every `n ≥ 1` in exactly the shape of the field
  `RBM.Steps.sharpLoop` of `Flow/Hypotheses.lean`.

## Deviations from the paper

* (5.92) is taken in the "bound-transfer" form `Lemma514`: if `max_u Ξ^{(L)}_{u,2n+2} ≺ Λ` and
  each term in the maximum on the right of (5.92) is `≺ Φ` uniformly in the time, then
  `Ξ^{(L-K)}_{u,n} ≺ Λ^{1/2} + Φ` (`Λ, Φ` deterministic, `Λ ≥ 1` eventually).  It is a
  consequence of (5.92), so the hypothesis is weaker.  The maximum over `v ∈ [s,t']` in (5.112)
  is taken over all of `[s,t]`; for `k ≥ 1`, `Ψ(n,k,s,v,t)` does not depend on `v`, and
  `Ψ(n,k,s,v,t') ≤ Ψ(n,k,s,v,t)`, so nothing is lost.
* (5.109) additionally assumes `S(2,3)`.  For `k = 1` the quadratic term `Ξ_2 Ξ_n A^{-1}` of
  (5.92) with `Ξ_n` bounded only at level `k - 1 = 0` loses a factor `R` against `Ψ(n,1)` unless
  `Ξ_2 ≺ A_s^{1/2}`; the paper has `S(2,l)` for every `l` from (2.76) ("`S(m,l)` holds for any
  `l` and `m ≤ 2`"), which `S_all` assumes anyway.
* "By condition (2.72)" is made explicit as `Scales`: `R² A_s^{3/4} ≤ A_u` (with
  `R ≤ ((1-s)/(1-t))^{1/2}`, `A_s ≤ ((1-s)/(1-t)) A_u`, `((1-s)/(1-t))^{30} ≤ A_t`).  It gives
  `R ≤ A_s^{1/4}`, so `k = n + 1` works in "for fixed `n` there is a large enough `k`".
* (5.107), first half, is proved for the flow for every `n ≥ 1` from
  `|K_{u,σ,a}| ≤ C (W ℓ_u η_u)^{-n+1}` (`RBM.Band.norm_Kval_le`: (2.59) for `n ≥ 3`, direct for
  `n = 1, 2`); the induction itself only uses lengths `≥ 4`.
* (5.107), second half, is `Ξ^{(L-K)} ≤ A_u (Ξ^{(L)} + C)` instead of the paper's
  `A_u Ξ^{(L)} + 1`: `|K| ≲ A_u^{-m+1}` only gives the additive term `C A_u`.  It is not used
  in Step 3.
* (5.120) holds with the constant `4` (absorbed in `≺`).
* Inputs taken as hypotheses (random layer, as in the paper): Lemma 5.14 (5.92), `S(m,0)` (from
  (2.73), (3.46)), `S(m,l)` for `m ≤ 2` (from (2.75), (2.76)).
-/

namespace RBM

open MeasureTheory Filter

namespace Step3

/-! ### Real inequalities between the scales -/

section Real

/-- The scale kit: `b = a^{1/4}` with `a^{1/2} = b²`, `a^{3/4} = b³`, `a = b⁴`. -/
theorem rpow_quarter {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    a ^ ((j : ℝ) / 4) = (a ^ ((1 : ℝ) / 4)) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  ring_nf

theorem rpow_half_eq {a : ℝ} (ha : 0 ≤ a) : a ^ ((1 : ℝ) / 2) = (a ^ ((1 : ℝ) / 4)) ^ 2 := by
  rw [← rpow_quarter ha]; norm_num

theorem rpow_three_quarter_eq {a : ℝ} (ha : 0 ≤ a) :
    a ^ ((3 : ℝ) / 4) = (a ^ ((1 : ℝ) / 4)) ^ 3 := by
  rw [← rpow_quarter ha]; norm_num

theorem self_eq_rpow_quarter_pow {a : ℝ} (ha : 0 ≤ a) : a = (a ^ ((1 : ℝ) / 4)) ^ 4 := by
  rw [← rpow_quarter ha]; norm_num

/-- `a^{1-(k-1)/4} = a^{1/4} a^{1-k/4}` for `k ≥ 1`. -/
theorem rpow_pred_eq {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    a ^ (1 - ((k - 1 : ℕ) : ℝ) / 4) = a ^ ((1 : ℝ) / 4) * a ^ (1 - (k : ℝ) / 4) := by
  rw [← Real.rpow_add ha]
  congr 1
  rw [Nat.cast_sub hk]
  ring

/-- `a^{1-k/4} ≤ a^{3/4}` for `k ≥ 1`, `a ≥ 1`. -/
theorem rpow_one_sub_le {a : ℝ} (ha : 1 ≤ a) {k : ℕ} (hk : 1 ≤ k) :
    a ^ (1 - (k : ℝ) / 4) ≤ (a ^ ((1 : ℝ) / 4)) ^ 3 := by
  rw [← rpow_three_quarter_eq (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le ha
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-! The polynomial inequalities.  Throughout, `b = (W ℓ_s η_s)^{1/4} ≥ 1`, `R = ℓ_t/ℓ_s ≥ 1`,
`v = W ℓ_u η_u` with `R² b³ ≤ v ≤ b⁴`, and `e = (W ℓ_s η_s)^{1-k/4} ≤ b³` (`k ≥ 1`). -/

variable {b R v e : ℝ}

theorem scale_facts (hb : 1 ≤ b) (hR : 1 ≤ R) (hv : v ≤ b ^ 4) (hRv : R ^ 2 * b ^ 3 ≤ v) :
    0 < v ∧ R ^ 2 ≤ b ∧ b ^ 2 ≤ v ∧ b ^ 3 ≤ v ∧ R * b ≤ v ∧ R ≤ b := by
  have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hb3v : b ^ 3 ≤ v := by nlinarith
  have hR2b : R ^ 2 ≤ b := by
    have h : R ^ 2 * b ^ 3 ≤ b * b ^ 3 := by nlinarith
    exact le_of_mul_le_mul_right h (by positivity)
  have hRb : R ≤ b := by nlinarith
  refine ⟨by linarith, hR2b, by nlinarith, hb3v, ?_, hRb⟩
  have : R * b ≤ R ^ 2 * b ^ 3 :=
    mul_le_mul (by nlinarith) (by simpa using pow_le_pow_right₀ hb (show 1 ≤ 3 by norm_num))
      (by linarith) (by positivity)
  linarith

/-- The deterministic part of **(5.119) ⟹ (5.120)**. -/
theorem ineq_5120 (hb : 1 ≤ b) (hR : 1 ≤ R) (hv : v ≤ b ^ 4) (hRv : R ^ 2 * b ^ 3 ≤ v)
    (he : 0 ≤ e) {n α β : ℕ} (hn : 1 ≤ n) (hαβ : α + β = 2 * n) (hα : α ≤ n + 1)
    (hβ : β ≤ n + 1) {p₁ p₂ : ℝ} (hp₁0 : 0 ≤ p₁) (hp₂0 : 0 ≤ p₂)
    (hp₁ : p₁ ≤ b ^ 2 + R ^ α * (b * e)) (hp₂ : p₂ ≤ b ^ 2 + R ^ β * (b * e)) :
    (1 + v⁻¹ * p₁) * (1 + v⁻¹ * p₂) * v ≤ 4 * (b ^ 2 + R ^ (n - 1) * e) ^ 2 := by
  obtain ⟨hv0, hR2b, hb2v, hb3v, -, -⟩ := scale_facts hb hR hv hRv
  set r := R ^ (n - 1) with hr
  have hr0 : 0 ≤ r := by positivity
  have hb0 : 0 ≤ b := by linarith
  have hsplit : R ^ (n + 1) = r * R ^ 2 := by rw [hr, ← pow_add]; congr 1; omega
  have hRα : R ^ α ≤ r * b :=
    (pow_le_pow_right₀ hR hα).trans (by rw [hsplit]; exact mul_le_mul_of_nonneg_left hR2b hr0)
  have hRβ : R ^ β ≤ r * b :=
    (pow_le_pow_right₀ hR hβ).trans (by rw [hsplit]; exact mul_le_mul_of_nonneg_left hR2b hr0)
  have hRαβ : R ^ α * R ^ β = r ^ 2 * R ^ 2 := by
    rw [← pow_add, hαβ, hr, ← pow_mul, ← pow_add]; congr 1; omega
  set x := R ^ α * (b * e) with hx
  set y := R ^ β * (b * e) with hy
  have hbe : 0 ≤ b * e := mul_nonneg hb0 he
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hxle : x ≤ r * b ^ 2 * e := by
    calc x ≤ r * b * (b * e) := mul_le_mul_of_nonneg_right hRα hbe
      _ = r * b ^ 2 * e := by ring
  have hyle : y ≤ r * b ^ 2 * e := by
    calc y ≤ r * b * (b * e) := mul_le_mul_of_nonneg_right hRβ hbe
      _ = r * b ^ 2 * e := by ring
  have hR2b2 : R ^ 2 * b ^ 2 ≤ v := by
    have : R ^ 2 * b ^ 2 ≤ R ^ 2 * b ^ 3 := by
      have : b ^ 2 ≤ b ^ 3 := pow_le_pow_right₀ hb (by norm_num)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hxy : x * y ≤ r ^ 2 * e ^ 2 * v := by
    have : x * y = r ^ 2 * e ^ 2 * (R ^ 2 * b ^ 2) := by
      rw [hx, hy]
      calc R ^ α * (b * e) * (R ^ β * (b * e)) = (R ^ α * R ^ β) * (b ^ 2 * e ^ 2) := by ring
        _ = _ := by rw [hRαβ]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hR2b2 (by positivity)
  -- the numerator
  have hnum : (v + p₁) * (v + p₂) ≤ 4 * v * (b ^ 2 + r * e) ^ 2 := by
    have h1 : v + p₁ ≤ v + b ^ 2 + x := by linarith
    have h2 : v + p₂ ≤ v + b ^ 2 + y := by linarith
    have h12 : (v + p₁) * (v + p₂) ≤ (v + b ^ 2 + x) * (v + b ^ 2 + y) :=
      mul_le_mul h1 h2 (by linarith) (by positivity)
    have h3 : (v + b ^ 2) * (x + y) ≤ (2 * v) * (2 * (r * b ^ 2 * e)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have h4 : (v + b ^ 2) ^ 2 ≤ 4 * v * b ^ 4 := by
      have : (v + b ^ 2) ^ 2 ≤ (2 * v) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      nlinarith
    have hre : 0 ≤ r * b ^ 2 * e := by positivity
    have h5 : 0 ≤ v * (r ^ 2 * e ^ 2) := by positivity
    nlinarith
  have hlhs : (1 + v⁻¹ * p₁) * (1 + v⁻¹ * p₂) * v = (v + p₁) * (v + p₂) * v⁻¹ := by
    field_simp
  rw [hlhs, mul_inv_le_iff₀ hv0]
  nlinarith

/-- The quadratic term of (5.112) for `3 ≤ p, q ≤ n - 1` (both factors at level `k`). -/
theorem ineq_quad (hb : 1 ≤ b) (hR : 1 ≤ R) (hv : v ≤ b ^ 4) (hRv : R ^ 2 * b ^ 3 ≤ v)
    (he : 0 ≤ e) (he3 : e ≤ b ^ 3) {n p q : ℕ} (hpq : p + q = n + 2) (hp : p ≤ n) (hq : q ≤ n) :
    (b ^ 2 + R ^ (p - 1) * e) * (b ^ 2 + R ^ (q - 1) * e) * v⁻¹
      ≤ 4 * (b ^ 2 + R ^ (n - 1) * e) := by
  obtain ⟨hv0, -, hb2v, hb3v, -, -⟩ := scale_facts hb hR hv hRv
  set r := R ^ (n - 1) with hr
  have hr0 : 0 ≤ r := by positivity
  have hRp : R ^ (p - 1) ≤ r := pow_le_pow_right₀ hR (by omega)
  have hRq : R ^ (q - 1) ≤ r := pow_le_pow_right₀ hR (by omega)
  have hRpq : R ^ (p - 1) * R ^ (q - 1) = r * R := by
    rw [← pow_add, hr, ← pow_succ]; congr 1; omega
  have hRe : R * e ≤ v := by
    have : R * e ≤ R ^ 2 * b ^ 3 := by
      have : R ≤ R ^ 2 := by nlinarith
      calc R * e ≤ R * b ^ 3 := mul_le_mul_of_nonneg_left he3 (by linarith)
        _ ≤ R ^ 2 * b ^ 3 := mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  rw [mul_inv_le_iff₀ hv0]
  have hexp : (b ^ 2 + R ^ (p - 1) * e) * (b ^ 2 + R ^ (q - 1) * e)
      = b ^ 2 * b ^ 2 + b ^ 2 * (R ^ (p - 1) * e + R ^ (q - 1) * e) + r * e * (R * e) := by
    rw [show r * e * (R * e) = (R ^ (p - 1) * R ^ (q - 1)) * e ^ 2 by rw [hRpq]; ring]
    ring
  rw [hexp]
  have h1 : b ^ 2 * b ^ 2 ≤ b ^ 2 * v := mul_le_mul_of_nonneg_left hb2v (by positivity)
  have h2 : b ^ 2 * (R ^ (p - 1) * e + R ^ (q - 1) * e) ≤ v * (2 * (r * e)) :=
    mul_le_mul hb2v (by nlinarith) (by positivity) (by linarith)
  have h3 : r * e * (R * e) ≤ r * e * v := mul_le_mul_of_nonneg_left hRe (by positivity)
  have h4 : 0 ≤ r * e * v := by positivity
  nlinarith

/-- The quadratic term of (5.112) with a `2`-loop factor: `Ξ_2 ≺ b²`, `Ξ_n ≺ b² + R^{n-1} b e`. -/
theorem ineq_quad_two (hb : 1 ≤ b) (hR : 1 ≤ R) (hv : v ≤ b ^ 4) (hRv : R ^ 2 * b ^ 3 ≤ v)
    (he : 0 ≤ e) (n : ℕ) :
    b ^ 2 * (b ^ 2 + R ^ (n - 1) * (b * e)) * v⁻¹ ≤ 2 * (b ^ 2 + R ^ (n - 1) * e) := by
  obtain ⟨hv0, -, hb2v, hb3v, -, -⟩ := scale_facts hb hR hv hRv
  have hr0 : 0 ≤ R ^ (n - 1) := by positivity
  rw [mul_inv_le_iff₀ hv0]
  have h1 : b ^ 2 * b ^ 2 ≤ b ^ 2 * v := mul_le_mul_of_nonneg_left hb2v (by positivity)
  have h2 : b ^ 3 * (R ^ (n - 1) * e) ≤ v * (R ^ (n - 1) * e) :=
    mul_le_mul_of_nonneg_right hb3v (by positivity)
  have h3 : b ^ 2 * (b ^ 2 + R ^ (n - 1) * (b * e))
      = b ^ 2 * b ^ 2 + b ^ 3 * (R ^ (n - 1) * e) := by ring
  rw [h3]
  have h4 : 0 ≤ R ^ (n - 1) * e * v := by positivity
  nlinarith

/-- The long-loop term of (5.112): `Ξ^{(L)}_{n+1} ≺ 1 + v⁻¹ (b² + R^n b e)`. -/
theorem ineq_long (hb : 1 ≤ b) (hR : 1 ≤ R) (hv : v ≤ b ^ 4) (hRv : R ^ 2 * b ^ 3 ≤ v)
    (he : 0 ≤ e) {n : ℕ} (hn : 1 ≤ n) :
    1 + v⁻¹ * (b ^ 2 + R ^ n * (b * e)) ≤ 3 * (b ^ 2 + R ^ (n - 1) * e) := by
  obtain ⟨hv0, -, hb2v, -, hRbv, -⟩ := scale_facts hb hR hv hRv
  have hr0 : 0 ≤ R ^ (n - 1) := by positivity
  have hRn : R ^ n = R ^ (n - 1) * R := by rw [← pow_succ]; congr 1; omega
  have h1 : (1 : ℝ) ≤ b ^ 2 := one_le_pow₀ hb
  have h2 : v⁻¹ * b ^ 2 ≤ 1 := by rw [inv_mul_le_iff₀ hv0]; linarith
  have h3 : v⁻¹ * (R ^ n * (b * e)) ≤ R ^ (n - 1) * e := by
    rw [inv_mul_le_iff₀ hv0, hRn]
    have : R ^ (n - 1) * e * (R * b) ≤ R ^ (n - 1) * e * v :=
      mul_le_mul_of_nonneg_left hRbv (by positivity)
    nlinarith
  have h4 : 0 ≤ R ^ (n - 1) * e := by positivity
  nlinarith

end Real

/-! ### The control parameter `Ψ` (5.108) and the estimate `S(n,k)` -/

section Psi

/-- **(5.108)** for `k ≥ 1`:
`Ψ(n,k,s,u,t) = (W ℓ_s η_s)^{1/2} + (ℓ_t/ℓ_s)^{n-1} (W ℓ_s η_s)^{1-k/4}`, with `As = W ℓ_s η_s` and `R = ℓ_t/ℓ_s`.  It does not depend on `u`. -/
noncomputable def Psi (As R : ℝ) (n k : ℕ) : ℝ :=
  As ^ ((1 : ℝ) / 2) + R ^ (n - 1) * As ^ (1 - (k : ℝ) / 4)

/-- **(5.108)** `Ψ(n,k,s,u,t)`, with `Au = W ℓ_u η_u`: for `k = 0` the last factor is
`W ℓ_u η_u`, for `k ≥ 1` it is `(W ℓ_s η_s)^{1-k/4}` (`RBM.Step3.Psi`). -/
noncomputable def psi (As R Au : ℝ) (n k : ℕ) : ℝ :=
  if k = 0 then As ^ ((1 : ℝ) / 2) + R ^ (n - 1) * Au else Psi As R n k

variable {As R Au : ℝ} {n k : ℕ}

theorem psi_of_ne_zero (hk : k ≠ 0) : psi As R Au n k = Psi As R n k := by simp [psi, hk]

theorem psi_zero : psi As R Au n 0 = As ^ ((1 : ℝ) / 2) + R ^ (n - 1) * Au := by simp [psi]

theorem Psi_nonneg (hAs : 0 ≤ As) (hR : 0 ≤ R) : 0 ≤ Psi As R n k := by
  unfold Psi; positivity

theorem psi_nonneg (hAs : 0 ≤ As) (hR : 0 ≤ R) (hAu : 0 ≤ Au) : 0 ≤ psi As R Au n k := by
  unfold psi; split_ifs
  · positivity
  · exact Psi_nonneg hAs hR

/-- `Ψ(n,k)` in the variables `b = As^{1/4}`, `e = As^{1-k/4}`. -/
theorem Psi_eq (hAs : 0 ≤ As) :
    Psi As R n k = (As ^ ((1 : ℝ) / 4)) ^ 2 + R ^ (n - 1) * As ^ (1 - (k : ℝ) / 4) := by
  rw [Psi, rpow_half_eq hAs]

/-- The level-`(k-1)` bound in the level-`k` variables: `Ψ(m,k-1,u) ≤ b² + R^{m-1} b e`
(for `k = 1` this uses `W ℓ_u η_u ≤ W ℓ_s η_s`). -/
theorem psi_pred_le (hAs : 0 < As) (hR : 0 ≤ R) (hAu : Au ≤ As) (hk : 1 ≤ k) (m : ℕ) :
    psi As R Au m (k - 1) ≤ (As ^ ((1 : ℝ) / 4)) ^ 2
      + R ^ (m - 1) * (As ^ ((1 : ℝ) / 4) * As ^ (1 - (k : ℝ) / 4)) := by
  rw [← rpow_pred_eq hAs hk, ← rpow_half_eq hAs.le]
  unfold psi
  split_ifs with h0
  · have hk1 : k - 1 = 0 := h0
    rw [hk1]
    simp only [CharP.cast_eq_zero, zero_div, sub_zero, Real.rpow_one]
    gcongr
  · exact le_of_eq (by rw [Psi])

/-- `Ψ(n,k)` is non-decreasing in `n` (for `R ≥ 1`). -/
theorem Psi_mono (hAs : 0 ≤ As) (hR : 1 ≤ R) {m : ℕ} (hmn : m ≤ n) :
    Psi As R m k ≤ Psi As R n k := by
  unfold Psi
  gcongr

end Psi

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- `ξ ≺ ζ` gives `1 + A⁻¹ ξ ≺ 1 + A⁻¹ ζ` for a deterministic `A > 0`. -/
theorem stochDom_one_add_inv_mul {A : ∀ N, U N → ℝ} (hA : ∀ N u, 0 < A N u)
    {ξ ζ : ∀ N, U N → Ω → ℝ} (hξ : ∀ N u ω, 0 ≤ ξ N u ω) (h : StochDom P ξ ζ) :
    StochDom P (fun N u ω => 1 + (A N u)⁻¹ * ξ N u ω)
      (fun N u ω => 1 + (A N u)⁻¹ * ζ N u ω) := by
  have h1 : StochDom P (fun N (_ : U N) (_ : Ω) => (1 : ℝ)) (fun _ _ _ => 1) :=
    StochDom.refl fun _ _ _ => zero_le_one
  have hA' : ∀ N u (_ : Ω), 0 ≤ (A N u)⁻¹ := fun N u _ => (inv_pos.2 (hA N u)).le
  have h2 : StochDom P (fun N u (_ : Ω) => (A N u)⁻¹) (fun N u _ => (A N u)⁻¹) :=
    StochDom.refl hA'
  exact h1.add (StochDom.mul hξ hA' h2 h)

/-- **The scales of Step 3.**  `As N = W ℓ_s η_s`, `R N = ℓ_t/ℓ_s`, `A N u = W ℓ_u η_u` for
`u ∈ U N` (the times `u ∈ [s, t]`).  The eventual inequalities are consequences of (2.72) for
the flow (`RBM.Step3.scales_of_cond272`). -/
structure Scales (As R : ℕ → ℝ) (A : ∀ N, U N → ℝ) : Prop where
  As_pos : ∀ N, 0 < As N
  R_nonneg : ∀ N, 0 ≤ R N
  A_pos : ∀ N u, 0 < A N u
  one_le_As : ∀ᶠ N : ℕ in atTop, 1 ≤ As N
  one_le_R : ∀ᶠ N : ℕ in atTop, 1 ≤ R N
  A_le_As : ∀ᶠ N : ℕ in atTop, ∀ u, A N u ≤ As N
  le_A : ∀ᶠ N : ℕ in atTop, ∀ u, R N ^ 2 * As N ^ ((3 : ℝ) / 4) ≤ A N u

/-- The scale facts in the variable `b = As^{1/4}`. -/
theorem Scales.kit {As R : ℕ → ℝ} {A : ∀ N, U N → ℝ} (h : Scales As R A) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ As N ∧ 1 ≤ As N ^ ((1 : ℝ) / 4) ∧ 1 ≤ R N ∧
      ∀ u, A N u ≤ As N ∧ A N u ≤ (As N ^ ((1 : ℝ) / 4)) ^ 4 ∧
        R N ^ 2 * (As N ^ ((1 : ℝ) / 4)) ^ 3 ≤ A N u := by
  filter_upwards [h.one_le_As, h.one_le_R, h.A_le_As, h.le_A] with N h1 h2 h3 h4
  have ha : 0 ≤ As N := by linarith
  refine ⟨h1, Real.one_le_rpow h1 (by norm_num), h2, fun u => ⟨h3 u, ?_, ?_⟩⟩
  · rw [← self_eq_rpow_quarter_pow ha]; exact h3 u
  · rw [← rpow_three_quarter_eq ha]; exact h4 u

variable (P) in
/-- **The estimate `S(n,k,s,u,t)`** (p. 70): `Ξ^{(L-K)}_{u,n} ≺ Ψ(n,k,s,u,t)`, uniformly in the
times `u ∈ U N`. -/
def S (X : ℕ → ∀ N, U N → Ω → ℝ) (As R : ℕ → ℝ) (A : ∀ N, U N → ℝ) (n k : ℕ) : Prop :=
  StochDom P (X n) fun N u _ => psi (As N) (R N) (A N u) n k

variable (P) in
/-- **Lemma 5.14, (5.92)**, in the form in which it is used in (5.112): if
`max_u Ξ^{(L)}_{u,2n+2} ≺ Λ` (`Λ ≥ 1` deterministic), and every term in the maximum on the
right of (5.92) is `≺ Φ` uniformly in the time (`Φ` deterministic), then
`Ξ^{(L-K)}_{u,n} ≺ Λ^{1/2} + Φ`.  This is implied by (5.92) (the maximum over `v ∈ [s,t]` of
quantities that are uniformly `≺ Φ` is `≺ Φ`), so taking it as a hypothesis is weaker than
taking (5.92). -/
def Lemma514 (X Y : ℕ → ∀ N, U N → Ω → ℝ) (A : ∀ N, U N → ℝ) (n : ℕ) : Prop :=
  ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
    StochDom P (Y (2 * n + 2)) (fun N _ _ => Λ N) →
    (∀ m, 1 ≤ m → m < n → StochDom P (X m) fun N _ _ => Φ N) →
    (∀ m, 2 ≤ m → m ≤ n → StochDom P (fun N u ω => X m N u ω * X (n - m + 2) N u ω * (A N u)⁻¹)
      fun N _ _ => Φ N) →
    StochDom P (Y (n + 1)) (fun N _ _ => Φ N) →
    StochDom P (X n) fun N _ _ => Λ N ^ ((1 : ℝ) / 2) + Φ N

variable (P) in
/-- **The inputs of Step 3.**  `X n N u ω = Ξ^{(L-K)}_{u,n}`, `Y n N u ω = Ξ^{(L)}_{u,n}` (5.76),
`A N u = W ℓ_u η_u`, `As N = W ℓ_s η_s`, `R N = ℓ_t/ℓ_s`. -/
structure Hyp (X Y : ℕ → ∀ N, U N → Ω → ℝ) (As R : ℕ → ℝ) (A : ∀ N, U N → ℝ) : Prop where
  scales : Scales As R A
  X_nonneg : ∀ n N u ω, 0 ≤ X n N u ω
  Y_nonneg : ∀ n N u ω, 0 ≤ Y n N u ω
  /-- **(5.107)**, first half: `Ξ^{(L)}_{u,n} ≺ 1 + (W ℓ_u η_u)^{-1} Ξ^{(L-K)}_{u,n}` (`n ≥ 3`). -/
  xiL_le : ∀ n, 3 ≤ n → StochDom P (Y n) fun N u ω => 1 + (A N u)⁻¹ * X n N u ω
  /-- **(5.118)**: `Ξ^{(L)}_{u,2n+2} ≤ Ξ^{(L)}_{u,2l₁} Ξ^{(L)}_{u,2l₂} (W ℓ_u η_u)` for
  `l₁ + l₂ = n + 1` (a deterministic inequality, `RBM.loopXi_le`). -/
  xiL_split : ∀ n l₁ l₂, 1 ≤ l₁ → 1 ≤ l₂ → l₁ + l₂ = n + 1 → ∀ N u ω,
    Y (2 * n + 2) N u ω ≤ Y (2 * l₁) N u ω * Y (2 * l₂) N u ω * A N u
  /-- **Lemma 5.14 (5.92)** for `n ≥ 3`. -/
  lemma514 : ∀ n, 3 ≤ n → Lemma514 P X Y A n

variable {X Y : ℕ → ∀ N, U N → Ω → ℝ} {As R : ℕ → ℝ} {A : ∀ N, U N → ℝ}

/-- The right side of (5.119): `W ℓ_u η_u · ∏_{m=1,2} (1 + (W ℓ_u η_u)^{-1} Ψ(2l_m, k-1, s, u, t))`,
with `l₁ = ⌊(n+1)/2⌋`, `l₂ = n + 1 - l₁`. -/
noncomputable def rhs5119 (As R : ℕ → ℝ) (A : ∀ N, U N → ℝ) (n k : ℕ) (N : ℕ) (u : U N) : ℝ :=
  (1 + (A N u)⁻¹ * psi (As N) (R N) (A N u) (2 * ((n + 1) / 2)) (k - 1)) *
    (1 + (A N u)⁻¹ * psi (As N) (R N) (A N u) (2 * (n + 1 - (n + 1) / 2)) (k - 1)) * A N u

/-- **(5.119)**: by (5.118), (5.107) and `S(2l_m, k-1)` (`2l_m ≤ n + 2`),
`Ξ^{(L)}_{u,2n+2} ≺ W ℓ_u η_u ∏_{m=1,2} (1 + (W ℓ_u η_u)^{-1} Ψ(2l_m, k-1, s, u, t))`. -/
theorem xiL_5119 (h : Hyp P X Y As R A) {n k : ℕ} (hn : 3 ≤ n)
    (hS : ∀ m, 1 ≤ m → m ≤ n + 2 → S P X As R A m (k - 1)) :
    StochDom P (Y (2 * n + 2)) fun N u _ => rhs5119 As R A n k N u := by
  have sc := h.scales
  set l₁ := (n + 1) / 2 with hl₁def
  set l₂ := n + 1 - l₁ with hl₂def
  have hl₁ : 2 ≤ l₁ := by omega
  have hl₂ : 2 ≤ l₂ := by omega
  have hbd0 : ∀ l N (u : U N) (_ : Ω),
      0 ≤ 1 + (A N u)⁻¹ * psi (As N) (R N) (A N u) (2 * l) (k - 1) := fun l N u _ => by
    have := psi_nonneg (sc.As_pos N).le (sc.R_nonneg N) (sc.A_pos N u).le
      (n := 2 * l) (k := k - 1)
    have := (inv_pos.2 (sc.A_pos N u)).le
    positivity
  -- (5.107) and `S(2l, k-1)`
  have hY : ∀ l, 2 ≤ l → 2 * l ≤ n + 2 → StochDom P (Y (2 * l))
      (fun N u _ => 1 + (A N u)⁻¹ * psi (As N) (R N) (A N u) (2 * l) (k - 1)) :=
    fun l hl hl' => (h.xiL_le (2 * l) (by omega)).trans
      (stochDom_one_add_inv_mul sc.A_pos (h.X_nonneg _) (hS (2 * l) (by omega) hl'))
  have h12 := StochDom.mul (h.Y_nonneg _) (hbd0 l₁) (hY l₁ hl₁ (by omega)) (hY l₂ hl₂ (by omega))
  have hA : StochDom P (fun N u (_ : Ω) => A N u) (fun N u _ => A N u) :=
    StochDom.refl fun N u _ => (sc.A_pos N u).le
  have h3 := StochDom.mul (fun N u _ => (sc.A_pos N u).le)
    (fun N u ω => mul_nonneg (hbd0 l₁ N u ω) (hbd0 l₂ N u ω)) h12 hA
  -- (5.118), pointwise
  exact StochDom.of_le_left (fun N u ω => h.xiL_split n l₁ l₂ (by omega) (by omega) (by omega)
    N u ω) h3

/-- **(5.120)** (deterministic): `W ℓ_u η_u ∏_{m=1,2} (1 + (W ℓ_u η_u)^{-1} Ψ(2l_m, k-1)) ≤
4 Ψ(n,k)²` for `k ≥ 1` (eventually in `N`, uniformly in `u`). -/
theorem rhs5119_le (sc : Scales As R A) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∀ᶠ N : ℕ in atTop, ∀ u, rhs5119 As R A n k N u ≤ 4 * Psi (As N) (R N) n k ^ 2 := by
  filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u
  obtain ⟨hAs, hv, hRv⟩ := hu u
  have ha0 : 0 < As N := sc.As_pos N
  rw [Psi_eq ha0.le, rhs5119]
  refine ineq_5120 (α := 2 * ((n + 1) / 2) - 1) (β := 2 * (n + 1 - (n + 1) / 2) - 1) hb hR hv
    hRv (Real.rpow_nonneg ha0.le _) hn (by omega) (by omega) (by omega)
    (psi_nonneg ha0.le (sc.R_nonneg N) (sc.A_pos N u).le)
    (psi_nonneg ha0.le (sc.R_nonneg N) (sc.A_pos N u).le) ?_ ?_
  · exact psi_pred_le ha0 (sc.R_nonneg N) hAs hk _
  · exact psi_pred_le ha0 (sc.R_nonneg N) hAs hk _

/-- **(5.111)**: under `S(m, k-1)` for `m ≤ n + 2` (`k ≥ 1`),
`Ξ^{(L)}_{u,2n+2} ≺ Ψ(n,k,s,u,t)²`.  (5.119) followed by (5.120). -/
theorem xiL_two_mul_add_two (h : Hyp P X Y As R A) {n k : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hS : ∀ m, 1 ≤ m → m ≤ n + 2 → S P X As R A m (k - 1)) :
    StochDom P (Y (2 * n + 2)) fun N _ _ => Psi (As N) (R N) n k ^ 2 :=
  stochDom_mono (fun N _ _ => sq_nonneg _) 4
    ((rhs5119_le h.scales (by omega) hk).mono fun _ hN u _ => hN u) (xiL_5119 h hn hS)

/-- `S(2,3)` gives `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_s η_s)^{1/2}`. -/
theorem xiLK_two_le (h : Hyp P X Y As R A) (hS2 : S P X As R A 2 3) :
    StochDom P (X 2) fun N _ _ => As N ^ ((1 : ℝ) / 2) := by
  have sc := h.scales
  refine stochDom_mono (fun N _ _ => Real.rpow_nonneg (sc.As_pos N).le _) 2 ?_ hS2
  filter_upwards [sc.kit] with N ⟨h1, hb, hR, hu⟩ u ω
  obtain ⟨-, hv, hRv⟩ := hu u
  obtain ⟨-, -, -, -, -, hRb⟩ := scale_facts hb hR hv hRv
  have ha0 := (sc.As_pos N).le
  rw [psi_of_ne_zero (by norm_num), Psi, rpow_half_eq ha0,
    show (1 : ℝ) - ((3 : ℕ) : ℝ) / 4 = 1 / 4 by norm_num]
  have hb0 : 0 ≤ As N ^ ((1 : ℝ) / 4) := by linarith
  simp only [show 2 - 1 = 1 from rfl, pow_one]
  nlinarith

/-- A product bound for the quadratic term of (5.92). -/
theorem quad_of {p q : ℕ} {ζp ζq : ∀ N, U N → ℝ} {Φ : ℕ → ℝ} (h : Hyp P X Y As R A)
    (hζp : ∀ N u, 0 ≤ ζp N u) (hζq : ∀ N u, 0 ≤ ζq N u) (hΦ : ∀ N, 0 ≤ Φ N)
    (hp : StochDom P (X p) fun N u _ => ζp N u) (hq : StochDom P (X q) fun N u _ => ζq N u)
    (C : ℝ) (hle : ∀ᶠ N : ℕ in atTop, ∀ u, ζp N u * ζq N u * (A N u)⁻¹ ≤ C * Φ N) :
    StochDom P (fun N u ω => X p N u ω * X q N u ω * (A N u)⁻¹) fun N _ _ => Φ N := by
  have hA' : ∀ N u (_ : Ω), 0 ≤ (A N u)⁻¹ := fun N u _ => (inv_pos.2 (h.scales.A_pos N u)).le
  have h12 := StochDom.mul (h.X_nonneg q) (fun N u _ => hζp N u) hp hq
  have h3 := StochDom.mul hA' (fun N u _ => mul_nonneg (hζp N u) (hζq N u)) h12
    (StochDom.refl hA')
  exact stochDom_mono (fun N _ _ => hΦ N) C (hle.mono fun N hN u _ => hN u) h3

/-- **(5.109), the induction step.**  For `n ≥ 3`, `k ≥ 1`: if `S(m,k)` holds for `m ≤ n - 1`
and `S(m,k-1)` for `m ≤ n + 2`, then `S(n,k)` holds.  (Also uses `S(2,3)`, which the paper
has from (2.76) for every level; it is needed for the `m = 2` quadratic term when `k = 1`.) -/
theorem S_of_S (h : Hyp P X Y As R A) {n k : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hSk : ∀ m, 1 ≤ m → m ≤ n - 1 → S P X As R A m k)
    (hSk1 : ∀ m, 1 ≤ m → m ≤ n + 2 → S P X As R A m (k - 1))
    (hS2 : S P X As R A 2 3) : S P X As R A n k := by
  have sc := h.scales
  have hk0 : k ≠ 0 := by omega
  have ha0 : ∀ N, 0 < As N := sc.As_pos
  set Ψ : ℕ → ℝ := fun N => Psi (As N) (R N) n k with hΨdef
  have hΨ0 : ∀ N, 0 ≤ Ψ N := fun N => Psi_nonneg (ha0 N).le (sc.R_nonneg N)
  have hS' : ∀ m, S P X As R A m k ↔
      StochDom P (X m) fun N _ _ => Psi (As N) (R N) m k := fun m => by
    unfold S; simp only [psi_of_ne_zero hk0]
  -- the long loop `Ξ^{(L)}_{2n+2}`: (5.111)
  have hlongloop := xiL_two_mul_add_two h hn hk hSk1
  -- the short loops `m < n`
  have hsmall : ∀ m, 1 ≤ m → m < n → StochDom P (X m) fun N _ _ => Ψ N := by
    intro m hm1 hmn
    refine stochDom_mono (fun N _ _ => hΨ0 N) 1 ?_ ((hS' m).1 (hSk m hm1 (by omega)))
    filter_upwards [sc.one_le_R] with N hR u ω
    rw [one_mul]
    exact Psi_mono (ha0 N).le hR hmn.le
  -- `Ξ^{(L-K)}_2 ≺ b²` and `Ξ^{(L-K)}_n ≺ Ψ(n, k-1)`
  have hX2 := xiLK_two_le h hS2
  have hXn := hSk1 n (by omega) (by omega)
  have hpsi0 : ∀ m N (u : U N), 0 ≤ psi (As N) (R N) (A N u) m (k - 1) := fun m N u =>
    psi_nonneg (ha0 N).le (sc.R_nonneg N) (sc.A_pos N u).le
  have hquad2 : ∀ᶠ N : ℕ in atTop, ∀ u, As N ^ ((1 : ℝ) / 2) *
      psi (As N) (R N) (A N u) n (k - 1) * (A N u)⁻¹ ≤ 2 * Ψ N := by
    filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u
    obtain ⟨hAs, hv, hRv⟩ := hu u
    obtain ⟨hv0, -⟩ := scale_facts hb hR hv hRv
    show _ ≤ 2 * Psi (As N) (R N) n k
    rw [Psi_eq (ha0 N).le, rpow_half_eq (ha0 N).le]
    refine le_trans ?_ (ineq_quad_two hb hR hv hRv (Real.rpow_nonneg (ha0 N).le _) n)
    gcongr
    exact psi_pred_le (ha0 N) (sc.R_nonneg N) hAs hk n
  have hquad : ∀ m, 2 ≤ m → m ≤ n → StochDom P
      (fun N u ω => X m N u ω * X (n - m + 2) N u ω * (A N u)⁻¹) fun N _ _ => Ψ N := by
    intro m hm2 hmn
    rcases (show m = 2 ∨ m = n ∨ (3 ≤ m ∧ m ≤ n - 1) by omega) with rfl | rfl | ⟨hm3, hm⟩
    · rw [show n - 2 + 2 = n by omega]
      exact quad_of h (fun N _ => Real.rpow_nonneg (ha0 N).le _) (hpsi0 n) hΨ0 hX2 hXn 2 hquad2
    · rw [show m - m + 2 = 2 by omega]
      refine quad_of h (hpsi0 m) (fun N _ => Real.rpow_nonneg (ha0 N).le _) hΨ0 hXn hX2 2 ?_
      filter_upwards [hquad2] with N hN u
      rw [mul_comm (psi _ _ _ _ _)]
      exact hN u
    · refine quad_of h (fun N _ => Psi_nonneg (ha0 N).le (sc.R_nonneg N))
        (fun N _ => Psi_nonneg (ha0 N).le (sc.R_nonneg N)) hΨ0
        ((hS' m).1 (hSk m (by omega) hm)) ((hS' (n - m + 2)).1 (hSk _ (by omega) (by omega)))
        4 ?_
      filter_upwards [sc.kit] with N ⟨h1, hb, hR, hu⟩ u
      obtain ⟨_, hv, hRv⟩ := hu u
      show _ ≤ 4 * Psi (As N) (R N) n k
      simp only [Psi_eq (ha0 N).le]
      exact ineq_quad hb hR hv hRv (Real.rpow_nonneg (ha0 N).le _)
        (rpow_one_sub_le h1 hk) (by omega) (by omega) (by omega)
  -- the `(n+1)`-loop `Ξ^{(L)}_{n+1}`, via (5.107)
  have hlong : StochDom P (Y (n + 1)) fun N _ _ => Ψ N := by
    have h1 := (h.xiL_le (n + 1) (by omega)).trans
      (stochDom_one_add_inv_mul sc.A_pos (h.X_nonneg _) (hSk1 (n + 1) (by omega) (by omega)))
    refine stochDom_mono (fun N _ _ => hΨ0 N) 3 ?_ h1
    filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u ω
    obtain ⟨hAs, hv, hRv⟩ := hu u
    obtain ⟨hv0, -⟩ := scale_facts hb hR hv hRv
    show _ ≤ 3 * Psi (As N) (R N) n k
    rw [Psi_eq (ha0 N).le]
    refine le_trans ?_ (ineq_long hb hR hv hRv (Real.rpow_nonneg (ha0 N).le _) (by omega : 1 ≤ n))
    gcongr
    have := psi_pred_le (ha0 N) (sc.R_nonneg N) hAs hk (n + 1)
    simpa using this
  -- (5.112) ⟹ (5.113)
  have hΛ : ∀ᶠ N : ℕ in atTop, 1 ≤ Ψ N ^ 2 := by
    filter_upwards [sc.one_le_As] with N h1
    have : 1 ≤ Ψ N := by
      have h2 : 1 ≤ As N ^ ((1 : ℝ) / 2) := Real.one_le_rpow h1 (by norm_num)
      have h3 : 0 ≤ R N ^ (n - 1) * As N ^ (1 - (k : ℝ) / 4) := by
        have := sc.R_nonneg N; have := ha0 N; positivity
      simp only [hΨdef, Psi]; linarith
    nlinarith
  have key := h.lemma514 n hn (fun N => Ψ N ^ 2) Ψ (fun N => sq_nonneg _) hΨ0 hΛ hlongloop
    hsmall hquad hlong
  rw [hS']
  refine stochDom_mono (fun N _ _ => hΨ0 N) 2 (Eventually.of_forall fun N u ω => ?_) key
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hΨ0 N)]
  norm_num
  show Ψ N + Ψ N ≤ 2 * Ψ N
  linarith

/-- **The double induction** (proof of (2.77), p. 70): from `S(m,0)` for all `m ≥ 1` (by (2.73)
and (3.46)) and `S(m,l)` for all `l` and `m ≤ 2` (by (2.75), (2.76)), the step (5.109) gives
`S(n,k)` for all `n ≥ 1` and all `k`: first `(3,1), (4,1), …`, then `(3,2), (4,2), …`, etc. -/
theorem S_all (h : Hyp P X Y As R A) (h0 : ∀ m, 1 ≤ m → S P X As R A m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → S P X As R A m l) :
    ∀ k n, 1 ≤ n → S P X As R A n k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro hn
      rcases (show n ≤ 2 ∨ 3 ≤ n by omega) with hn2 | hn3
      · exact h12 n (k + 1) hn hn2
      · exact S_of_S h hn3 (by omega) (fun m hm1 hm => ihn m (by omega) hm1)
          (fun m hm1 _ => by simpa using ih m hm1) (h12 2 3 (by norm_num) le_rfl)

/-- `Ψ(n, n+1) ≤ 2 (W ℓ_s η_s)^{1/2}` (for `R ≤ (W ℓ_s η_s)^{1/4}`): the choice of `k` on p. 70
("for any fixed `n` there is a large enough `k`"). -/
theorem Psi_succ_le {a r : ℝ} (ha : 0 < a) (hr0 : 0 ≤ r) (hr : r ≤ a ^ ((1 : ℝ) / 4)) {n : ℕ}
    (hn : 1 ≤ n) : Psi a r n (n + 1) ≤ 2 * a ^ ((1 : ℝ) / 2) := by
  have h1 : r ^ (n - 1) ≤ a ^ (((n - 1 : ℕ) : ℝ) / 4) := by
    rw [rpow_quarter ha.le]; exact pow_le_pow_left₀ hr0 hr _
  have h2 : a ^ (((n - 1 : ℕ) : ℝ) / 4) * a ^ (1 - ((n + 1 : ℕ) : ℝ) / 4) = a ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add ha]; congr 1; rw [Nat.cast_sub hn]; push_cast; ring
  unfold Psi
  have h3 : r ^ (n - 1) * a ^ (1 - ((n + 1 : ℕ) : ℝ) / 4) ≤ a ^ ((1 : ℝ) / 2) := by
    rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ha.le _)
  linarith

/-- **The conclusion of the induction** (p. 70): `Ξ^{(L-K)}_{u,n} ≺ (W ℓ_s η_s)^{1/2}` for every
`n ≥ 1`, uniformly in `u ∈ [s,t]`. -/
theorem xiLK_le (h : Hyp P X Y As R A) (h0 : ∀ m, 1 ≤ m → S P X As R A m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → S P X As R A m l) {n : ℕ} (hn : 1 ≤ n) :
    StochDom P (X n) fun N _ _ => As N ^ ((1 : ℝ) / 2) := by
  have sc := h.scales
  refine stochDom_mono (fun N _ _ => Real.rpow_nonneg (sc.As_pos N).le _) 2 ?_
    (S_all h h0 h12 (n + 1) n hn)
  filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u ω
  obtain ⟨_, hv, hRv⟩ := hu u
  obtain ⟨-, -, -, -, -, hRb⟩ := scale_facts hb hR hv hRv
  rw [psi_of_ne_zero (by omega)]
  exact Psi_succ_le (sc.As_pos N) (sc.R_nonneg N) hRb hn

/-- **(2.77) from (5.107)** at a given length `n`: if `Ξ^{(L)}_{u,n} ≺ 1 + (W ℓ_u η_u)^{-1}
Ξ^{(L-K)}_{u,n}`, then `Ξ^{(L)}_{u,n} ≺ 1`. -/
theorem xiL_le_one_of (h : Hyp P X Y As R A) (h0 : ∀ m, 1 ≤ m → S P X As R A m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → S P X As R A m l) {n : ℕ} (hn : 1 ≤ n)
    (h107 : StochDom P (Y n) fun N u ω => 1 + (A N u)⁻¹ * X n N u ω) :
    StochDom P (Y n) fun _ _ _ => 1 := by
  have sc := h.scales
  refine stochDom_mono (fun _ _ _ => zero_le_one) 2 ?_ (h107.trans
    (stochDom_one_add_inv_mul sc.A_pos (h.X_nonneg n) (xiLK_le h h0 h12 hn)))
  filter_upwards [sc.kit] with N ⟨_, hb, hR, hu⟩ u ω
  obtain ⟨_, hv, hRv⟩ := hu u
  obtain ⟨hv0, -, hb2v, -⟩ := scale_facts hb hR hv hRv
  rw [rpow_half_eq (sc.As_pos N).le, mul_one]
  have : (A N u)⁻¹ * (As N ^ ((1 : ℝ) / 4)) ^ 2 ≤ 1 := by
    rw [inv_mul_le_iff₀ hv0]; linarith
  linarith

/-- **(2.77)** (Step 3): `Ξ^{(L)}_{u,n} ≺ 1`, i.e. `max_{σ,a} |L_{u,σ,a}| ≺ (W ℓ_u η_u)^{-n+1}`,
for every `n ≥ 3`, uniformly in `u ∈ [s,t]`. -/
theorem xiL_le_one (h : Hyp P X Y As R A) (h0 : ∀ m, 1 ≤ m → S P X As R A m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → S P X As R A m l) {n : ℕ} (hn : 3 ≤ n) :
    StochDom P (Y n) fun _ _ _ => 1 :=
  xiL_le_one_of h h0 h12 (by omega) (h.xiL_le n hn)

end Abstract

/-! ### The scales of the flow satisfy `Step3.Scales` under (2.72) -/

section Flow

variable {W : ℝ} {L : ℕ} {E s u t : ℝ}

/-- `ℓ_t ≤ ((1-s)/(1-t))^{1/2} ℓ_s`. -/
theorem ellHat_le_sqrt_mul (hst : s ≤ t) (ht1 : t < 1) :
    ellHat L (t : ℂ) ≤ Real.sqrt ((1 - s) / (1 - t)) * ellHat L (s : ℂ) := by
  have hs1 : s < 1 := hst.trans_lt ht1
  have h1t : 0 < 1 - t := by linarith
  have h1s : 0 < 1 - s := by linarith
  have hQ : 1 ≤ (1 - s) / (1 - t) := by rw [le_div_iff₀ h1t]; linarith
  have hsq : 1 ≤ Real.sqrt ((1 - s) / (1 - t)) := Real.one_le_sqrt.2 hQ
  rw [ellHat_ofReal L ht1, ellHat_ofReal L hs1, mul_min_of_nonneg _ _ (by linarith)]
  refine le_min (min_le_left _ _ |>.trans (le_of_eq ?_)) (min_le_right _ _ |>.trans ?_)
  · rw [Real.sqrt_div h1s.le]
    have : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.2 h1s
    have : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1t
    field_simp
  · have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith

/-- `W ℓ_s η_s ≤ ((1-s)/(1-u)) W ℓ_u η_u` for `s ≤ u < 1`. -/
theorem flowScale_le_mul (hW : 0 ≤ W) (hsu : s ≤ u) (hu1 : u < 1) :
    flowScale W L E s ≤ (1 - s) / (1 - u) * flowScale W L E u := by
  have h1u : 0 < 1 - u := by linarith
  set Q := (1 - s) / (1 - u) with hQdef
  have hQ : 1 ≤ Q := by rw [hQdef, le_div_iff₀ h1u]; linarith
  have hs : 1 - s = Q * (1 - u) := by rw [hQdef]; field_simp
  rw [flowScale_eq W L E (by linarith), flowScale_eq W L E hu1.le, hs]
  have hc : 0 ≤ W * (mE E).im := mul_nonneg hW (mE_im_nonneg E)
  rw [show Q * (W * (mE E).im * min (Real.sqrt (1 - u)) (L * (1 - u)))
      = W * (mE E).im * (Q * min (Real.sqrt (1 - u)) (L * (1 - u))) by ring]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [mul_min_of_nonneg _ _ (by linarith)]
  refine min_le_min ?_ (le_of_eq (by ring))
  rw [Real.sqrt_mul (by linarith)]
  have : Real.sqrt Q ≤ Q := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)

/-- **The scale inequalities of Step 3 from (2.72)**: for `0 < W`, `|E| < 2`,
`s ≤ u ≤ t < 1` with `(W ℓ_t η_t)^{-1} ≤ ((1-t)/(1-s))^{30}`:
`1 ≤ W ℓ_s η_s`, `W ℓ_u η_u ≤ W ℓ_s η_s`, `1 ≤ ℓ_t/ℓ_s` and
`(ℓ_t/ℓ_s)² (W ℓ_s η_s)^{3/4} ≤ W ℓ_u η_u`. -/
theorem scale_facts_of_cond272 (hW : 0 < W) (hL : 1 ≤ L) (hE : |E| < 2) (hsu : s ≤ u)
    (hut : u ≤ t) (ht1 : t < 1)
    (hc : (flowScale W L E t)⁻¹ ≤ ((1 - t) / (1 - s)) ^ 30) :
    1 ≤ flowScale W L E s ∧ flowScale W L E u ≤ flowScale W L E s ∧
      1 ≤ ellHat L (t : ℂ) / ellHat L (s : ℂ) ∧
      (ellHat L (t : ℂ) / ellHat L (s : ℂ)) ^ 2 * flowScale W L E s ^ ((3 : ℝ) / 4)
        ≤ flowScale W L E u := by
  have hu1 : u < 1 := hut.trans_lt ht1
  have hs1 : s < 1 := hsu.trans_lt hu1
  have h1t : 0 < 1 - t := by linarith
  have h1s : 0 < 1 - s := by linarith
  set Q := (1 - s) / (1 - t) with hQdef
  have hQ : 1 ≤ Q := by rw [hQdef, le_div_iff₀ h1t]; linarith
  have hQ0 : 0 < Q := by linarith
  have hAt : 0 < flowScale W L E t := flowScale_pos hW hL hE ht1
  have hAu : 0 < flowScale W L E u := flowScale_pos hW hL hE hu1
  have hAs : 0 < flowScale W L E s := flowScale_pos hW hL hE hs1
  have hanti := flowScale_antitoneOn hW.le L E
  have hut' : flowScale W L E t ≤ flowScale W L E u :=
    hanti (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 ht1.le) hut
  have hsu' : flowScale W L E u ≤ flowScale W L E s :=
    hanti (Set.mem_Iic.2 hs1.le) (Set.mem_Iic.2 hu1.le) hsu
  -- `Q^30 ≤ A_t`
  have hQ30 : Q ^ 30 ≤ flowScale W L E t := by
    have : ((1 - t) / (1 - s)) ^ 30 = (Q ^ 30)⁻¹ := by rw [hQdef, ← inv_pow, inv_div]
    rw [this] at hc
    exact (inv_le_inv₀ hAt (by positivity)).1 hc
  have hAt1 : 1 ≤ flowScale W L E t := (one_le_pow₀ hQ).trans hQ30
  -- `R² ≤ Q`
  have hℓs := ellHat_pos_of_lt_one (L := L) hL hs1
  have hℓt := ellHat_pos_of_lt_one (L := L) hL ht1
  have hR : ellHat L (t : ℂ) / ellHat L (s : ℂ) ≤ Real.sqrt Q := by
    rw [div_le_iff₀ hℓs]; exact ellHat_le_sqrt_mul (hsu.trans hut) ht1
  have hR1 : 1 ≤ ellHat L (t : ℂ) / ellHat L (s : ℂ) := by
    rw [le_div_iff₀ hℓs, one_mul]; exact ellHat_mono (hsu.trans hut) ht1
  have hR2 : (ellHat L (t : ℂ) / ellHat L (s : ℂ)) ^ 2 ≤ Q := by
    calc _ ≤ Real.sqrt Q ^ 2 := pow_le_pow_left₀ (by linarith) hR 2
      _ = Q := Real.sq_sqrt hQ0.le
  -- `A_s ≤ Q A_u`
  have hAsQ : flowScale W L E s ≤ Q * flowScale W L E u := by
    refine (flowScale_le_mul hW.le hsu hu1).trans (mul_le_mul_of_nonneg_right ?_ hAu.le)
    exact div_le_div_of_nonneg_left h1s.le h1t (by linarith)
  refine ⟨hAt1.trans (hut'.trans hsu'), hsu', hR1, ?_⟩
  -- `Q (Q A_u)^{3/4} ≤ A_u`, since `Q^7 ≤ A_u`
  set Au := flowScale W L E u
  have hQ7 : Q ^ 7 ≤ Au := (pow_le_pow_right₀ hQ (by norm_num)).trans (hQ30.trans hut')
  have h74 : Q ^ ((7 : ℝ) / 4) ≤ Au ^ ((1 : ℝ) / 4) := by
    rw [show (7 : ℝ) / 4 = ((7 : ℕ) : ℝ) * (1 / 4) by norm_num, Real.rpow_mul hQ0.le,
      Real.rpow_natCast]
    exact Real.rpow_le_rpow (by positivity) hQ7 (by norm_num)
  calc (ellHat L (t : ℂ) / ellHat L (s : ℂ)) ^ 2 * flowScale W L E s ^ ((3 : ℝ) / 4)
      ≤ Q * (Q * Au) ^ ((3 : ℝ) / 4) :=
        mul_le_mul hR2 (Real.rpow_le_rpow hAs.le hAsQ (by norm_num)) (by positivity) hQ0.le
    _ = Q ^ ((7 : ℝ) / 4) * Au ^ ((3 : ℝ) / 4) := by
        rw [Real.mul_rpow hQ0.le hAu.le, ← mul_assoc]
        congr 1
        rw [show (7 : ℝ) / 4 = 1 + 3 / 4 by norm_num, Real.rpow_add hQ0, Real.rpow_one]
    _ ≤ Au ^ ((1 : ℝ) / 4) * Au ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right h74 (by positivity)
    _ = Au := by rw [← Real.rpow_add hAu]; norm_num

end Flow

end Step3

/-! ### The quantities (5.76) for the flow -/

namespace Sample

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B)

/-- `max_{σ,a} |L_{t,σ,a} - K_{t,σ,a}|` over loops of length `m`. -/
noncomputable def lkMax (E : ℝ) (N : ℕ) (t : ℝ) (ω : Ω) (m : ℕ) : ℝ :=
  ⨆ u : LoopData (B.L N) m, X.lkErr E N t ω u.idx

/-- **(5.76)** `Ξ^{(L-K)}_{t,m} = max_{σ,a} |(L - K)_{t,σ,a}| · (W ℓ_t η_t)^m`. -/
noncomputable def xiLK (E : ℝ) (N : ℕ) (t : ℝ) (ω : Ω) (m : ℕ) : ℝ :=
  X.lkMax E N t ω m * B.scale E N t ^ m

variable {E : ℝ} {N : ℕ} {t : ℝ} {ω : Ω} {m : ℕ}

theorem lkMax_nonneg : 0 ≤ X.lkMax E N t ω m :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem lkErr_le_lkMax (u : LoopData (B.L N) m) : X.lkErr E N t ω u.idx ≤ X.lkMax E N t ω m :=
  le_ciSup (f := fun u : LoopData (B.L N) m => X.lkErr E N t ω u.idx)
    (Set.finite_range _).bddAbove u

theorem norm_Lval_le_loopMax (u : LoopData (B.L N) m) :
    ‖X.Lval E N t ω u.idx‖ ≤ loopMax (B.L N) (B.W N) (X.H N t ω) (zt E t) m :=
  norm_gloop_le_loopMax _ (by simp [LoopData.idx]) (by simp [LoopData.idx])

theorem xiL_nonneg (hA : 0 ≤ B.scale E N t) : 0 ≤ X.xiL E N t ω m :=
  mul_nonneg (loopMax_nonneg _) (pow_nonneg hA _)

theorem xiLK_nonneg (hA : 0 ≤ B.scale E N t) : 0 ≤ X.xiLK E N t ω m :=
  mul_nonneg (X.lkMax_nonneg) (pow_nonneg hA _)

/-- **(5.107), first half, pointwise**: if `|K_{t,σ,a}| ≤ C (W ℓ_t η_t)^{-m+1}` for all loops of
length `m` (this is (2.59)), then `Ξ^{(L)}_{t,m} ≤ C + (W ℓ_t η_t)^{-1} Ξ^{(L-K)}_{t,m}`. -/
theorem xiL_le_add {C : ℝ} (hA : 0 < B.scale E N t) (hm : 1 ≤ m)
    (hK : ∀ u : LoopData (B.L N) m, ‖B.Kval E N t u.idx‖ ≤ C * (B.scale E N t)⁻¹ ^ (m - 1)) :
    X.xiL E N t ω m ≤ C + (B.scale E N t)⁻¹ * X.xiLK E N t ω m := by
  set A := B.scale E N t with hAdef
  have hmax : loopMax (B.L N) (B.W N) (X.H N t ω) (zt E t) m
      ≤ X.lkMax E N t ω m + C * A⁻¹ ^ (m - 1) := by
    refine ciSup_le fun u => ?_
    have h1 := norm_le_norm_sub_add (X.Lval E N t ω (LoopData.idx u))
      (B.Kval E N t (LoopData.idx u))
    have h2 := X.lkErr_le_lkMax (E := E) (t := t) (ω := ω) u
    have h3 := hK u
    simp only [Sample.lkErr] at h2
    exact h1.trans (add_le_add h2 h3)
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  calc X.xiL E N t ω (j + 1)
        = loopMax (B.L N) (B.W N) (X.H N t ω) (zt E t) (j + 1) * A ^ (j + 1 - 1) := rfl
    _ ≤ (X.lkMax E N t ω (j + 1) + C * A⁻¹ ^ (j + 1 - 1)) * A ^ (j + 1 - 1) :=
        mul_le_mul_of_nonneg_right hmax (pow_nonneg hA.le _)
    _ = C + A⁻¹ * X.xiLK E N t ω (j + 1) := by
        rw [xiLK, Nat.add_sub_cancel, ← hAdef, inv_pow]
        field_simp
        ring

/-- **(5.107), second half, pointwise**: under the same bound on `K`,
`Ξ^{(L-K)}_{t,m} ≤ W ℓ_t η_t · (Ξ^{(L)}_{t,m} + C)`.  (The paper writes
`(W ℓ_u η_u) Ξ^{(L)} + 1`; see the module docstring.) -/
theorem xiLK_le_mul {C : ℝ} (hA : 0 < B.scale E N t) (hm : 1 ≤ m)
    (hK : ∀ u : LoopData (B.L N) m, ‖B.Kval E N t u.idx‖ ≤ C * (B.scale E N t)⁻¹ ^ (m - 1)) :
    X.xiLK E N t ω m ≤ B.scale E N t * (X.xiL E N t ω m + C) := by
  set A := B.scale E N t with hAdef
  have hmax : X.lkMax E N t ω m
      ≤ loopMax (B.L N) (B.W N) (X.H N t ω) (zt E t) m + C * A⁻¹ ^ (m - 1) := by
    refine ciSup_le fun u => ?_
    have h1 := norm_sub_le (X.Lval E N t ω u.idx) (B.Kval E N t u.idx)
    exact h1.trans (add_le_add (X.norm_Lval_le_loopMax u) (hK u))
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  calc X.xiLK E N t ω (j + 1) = X.lkMax E N t ω (j + 1) * A ^ (j + 1) := rfl
    _ ≤ (loopMax (B.L N) (B.W N) (X.H N t ω) (zt E t) (j + 1) + C * A⁻¹ ^ (j + 1 - 1))
          * A ^ (j + 1) :=
        mul_le_mul_of_nonneg_right hmax (pow_nonneg hA.le _)
    _ = A * (X.xiL E N t ω (j + 1) + C) := by
        rw [xiL, loopXi, Nat.add_sub_cancel, ← hAdef, inv_pow]
        field_simp
        ring

end Sample

namespace Step3

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

section FlowFamilies

/-- `Ξ^{(L-K)}_{u,n}` for `u ∈ [s,t]`, as the family `n ↦ (N, u, ω) ↦ Ξ^{(L-K)}_{u,n}`. -/
noncomputable def flowXiLK (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) :
    ℕ → ∀ N, TimeIcc s t N → Ω → ℝ :=
  fun n N u ω => X.xiLK E N u ω n

/-- `A N u = W ℓ_u η_u` for `u ∈ [s,t]`. -/
noncomputable def flowA (B : Band Ω) (E : ℝ) (s t : ℕ → ℝ) : ∀ N, TimeIcc s t N → ℝ :=
  fun N u => B.scale E N u

/-- `As N = W ℓ_s η_s`. -/
noncomputable def flowAs (B : Band Ω) (E : ℝ) (s : ℕ → ℝ) : ℕ → ℝ := fun N => B.scale E N (s N)

variable {E : ℝ} {s t : ℕ → ℝ}

theorem flowA_pos (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (N : ℕ)
    (u : TimeIcc s t N) : 0 < flowA B E s t N u :=
  B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))

/-- **(2.72) gives the scale conditions of Step 3** for `u ∈ [s,t]`. -/
theorem scales_flow (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) :
    Scales (flowAs B E s) (flowR B s t) (flowA B E s t) := by
  have hs1 : ∀ N, s N < 1 := fun N => (hst N).trans_lt (ht1 N)
  have hL : ∀ N, 1 ≤ B.L N := fun N => by have := B.three_le_L N; omega
  have hW : ∀ N, (0 : ℝ) < B.W N := fun N => by exact_mod_cast B.W_pos N
  have key : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      1 ≤ flowAs B E s N ∧ flowA B E s t N u ≤ flowAs B E s N ∧ 1 ≤ flowR B s t N ∧
        flowR B s t N ^ 2 * flowAs B E s N ^ ((3 : ℝ) / 4) ≤ flowA B E s t N u := by
    filter_upwards [hc] with N hN u
    exact scale_facts_of_cond272 (hW N) (hL N) hE u.2.1 u.2.2 (ht1 N) hN
  refine ⟨fun N => B.scale_pos' hE N (hs0 N) (hs1 N), fun N => ?_,
    flowA_pos hE hs0 ht1, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (ellHat_pos_of_lt_one (hL N) (ht1 N)).le
      (ellHat_pos_of_lt_one (hL N) (hs1 N)).le
  · filter_upwards [key] with N hN
    exact (hN ⟨s N, le_rfl, hst N⟩).1
  · filter_upwards [key] with N hN
    exact (hN ⟨s N, le_rfl, hst N⟩).2.2.1
  · filter_upwards [key] with N hN u
    exact (hN u).2.1
  · filter_upwards [key] with N hN u
    exact (hN u).2.2.2

/-- The bound (2.59) on `K`, at the times `u ∈ [s,t]`, in the form used by (5.107). -/
theorem exists_norm_Kval_le {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) n),
      ‖B.Kval E N u v.idx‖ ≤ C * (B.scale E N u)⁻¹ ^ (n - 1) := by
  obtain ⟨C, hC0, hC⟩ := B.norm_Kval_le hκ0 hκ1 hEκ hn
  refine ⟨C, hC0, fun N u v => ?_⟩
  exact hC N u ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N)) v.idx v.idx_wf (by simp)

variable (X : Sample B)

/-- **(5.107) for the flow** from a bound `|K_{u,σ,a}| ≤ C (W ℓ_u η_u)^{-n+1}` (this is (2.59)):
`Ξ^{(L)}_{u,n} ≺ 1 + (W ℓ_u η_u)^{-1} Ξ^{(L-K)}_{u,n}`, uniformly in `u ∈ [s,t]`. -/
theorem flow_xiL_le_of {C : ℝ} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hC : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) n),
      ‖B.Kval E N u v.idx‖ ≤ C * (B.scale E N u)⁻¹ ^ (n - 1)) :
    StochDom B.P (flowXiL X E s t n)
      fun N u ω => 1 + (flowA B E s t N u)⁻¹ * flowXiLK X E s t n N u ω := by
  have hA := flowA_pos (B := B) hE hs0 ht1
  have hζ : ∀ N u ω, 0 ≤ 1 + (flowA B E s t N u)⁻¹ * flowXiLK X E s t n N u ω :=
    fun N u ω => by
      have := (inv_pos.2 (hA N u)).le
      have := X.xiLK_nonneg (E := E) (N := N) (t := u) (ω := ω) (m := n) (hA N u).le
      unfold flowXiLK; positivity
  refine StochDom.of_le_left (ξ' := fun N u ω =>
    max C 1 * (1 + (flowA B E s t N u)⁻¹ * flowXiLK X E s t n N u ω)) (fun N u ω => ?_)
    (StochDom.const_mul_left (le_trans zero_le_one (le_max_right _ _)) hζ (StochDom.refl hζ))
  have h1 := X.xiL_le_add (ω := ω) (hA N u) hn (hC N u)
  have h2 : 0 ≤ (flowA B E s t N u)⁻¹ * flowXiLK X E s t n N u ω := by
    have := (inv_pos.2 (hA N u)).le
    have := X.xiLK_nonneg (E := E) (N := N) (t := u) (ω := ω) (m := n) (hA N u).le
    unfold flowXiLK; positivity
  have h3 : C ≤ max C 1 := le_max_left _ _
  have h4 : 1 ≤ max C 1 := le_max_right _ _
  unfold flowXiL
  unfold flowXiLK flowA at h2
  unfold flowXiLK flowA
  nlinarith

/-- **(5.107) for the flow** (`n ≥ 3`), from (2.59) (`RBM.norm_Kgen_le`). -/
theorem flow_xiL_le {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (flowXiL X E s t n)
      fun N u ω => 1 + (flowA B E s t N u)⁻¹ * flowXiLK X E s t n N u ω := by
  obtain ⟨C, -, hC⟩ := exists_norm_Kval_le (B := B) hκ0 hκ1 hEκ hs0 ht1 hn
  exact flow_xiL_le_of X (by linarith) hs0 ht1 hn hC

/-- **(5.107) for the flow at `n = 1`**: `K_{u,(σ),(a)} = m(σ)` has `|m(σ)| ≤ 1`. -/
theorem flow_xiL_le_one_len (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    StochDom B.P (flowXiL X E s t 1)
      fun N u ω => 1 + (flowA B E s t N u)⁻¹ * flowXiLK X E s t 1 N u ω := by
  refine flow_xiL_le_of X (C := 1) hE hs0 ht1 le_rfl fun N u v => ?_
  have hv : v.idx = ⟨[v.1 0], [v.2 0]⟩ := by simp [LoopData.idx]
  rw [hv, Band.Kval, Kgen_one]
  simpa using norm_mSigma_le_one hE (v.1 0)

/-- **The inputs of Step 3 for the flow**: under `|E| ≤ 2 - κ`, `0 < s ≤ t < 1`, (2.72) and
Lemma 5.14 (5.92) (the only random-layer input), the hypotheses `RBM.Step3.Hyp` hold for
`Ξ^{(L-K)}`, `Ξ^{(L)}` of (5.76) on `[s,t]`: (5.107) by (2.59), (5.118) by
`RBM.loopXi_le`, the scale conditions by (2.72). -/
theorem hyp_flow {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (h514 : ∀ n, 3 ≤ n → Lemma514 B.P (flowXiLK X E s t) (flowXiL X E s t) (flowA B E s t) n) :
    Hyp B.P (flowXiLK X E s t) (flowXiL X E s t) (flowAs B E s) (flowR B s t)
      (flowA B E s t) := by
  have hE : |E| < 2 := by linarith
  have hA := flowA_pos (B := B) hE hs0 ht1
  exact
    { scales := scales_flow hE hs0 hst ht1 hc
      X_nonneg := fun n N u ω => X.xiLK_nonneg (hA N u).le
      Y_nonneg := fun n N u ω => X.xiL_nonneg (hA N u).le
      xiL_le := fun n hn => flow_xiL_le X hκ0 hκ1 hEκ hs0 ht1 (by omega)
      xiL_split := fun n l₁ l₂ h₁ h₂ hl N u ω =>
        loopXi_le (X.hermitian N u ω) (hA N u).le h₁ h₂ hl
      lemma514 := h514 }

/-- **(2.77) for the flow, in the shape of `RBM.Steps.sharpLoop`**, at a length `n` for which
(5.107) is available: `max_{σ,a} |L_{u,σ,a}| ≺ (W ℓ_u η_u)^{-n+1}` uniformly in `u ∈ [s,t]`.
Inputs: `|E| ≤ 2 - κ`, `0 < s ≤ t < 1`, (2.72), Lemma 5.14 (5.92), `S(m,0)` for `m ≥ 1` (from
(2.73), (3.46)) and `S(m,l)` for `m ≤ 2` (from (2.75), (2.76)). -/
theorem flow_sharpLoop_of {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (h514 : ∀ n, 3 ≤ n → Lemma514 B.P (flowXiLK X E s t) (flowXiL X E s t) (flowA B E s t) n)
    (h0 : ∀ m, 1 ≤ m → S B.P (flowXiLK X E s t) (flowAs B E s) (flowR B s t) (flowA B E s t) m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 →
      S B.P (flowXiLK X E s t) (flowAs B E s) (flowR B s t) (flowA B E s t) m l)
    {n : ℕ} (hn : 1 ≤ n)
    (h107 : StochDom B.P (flowXiL X E s t n)
      fun N u ω => 1 + (flowA B E s t N u)⁻¹ * flowXiLK X E s t n N u ω) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) := by
  have hE : |E| < 2 := by linarith
  have hA := flowA_pos (B := B) hE hs0 ht1
  have H := hyp_flow X hκ0 hκ1 hEκ hs0 hst ht1 hc h514
  have hY := (xiL_le_one_of H h0 h12 hn h107).precomp_param
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) => p.1)
  have hinv : ∀ N (p : TimeIcc s t N × LoopData (B.L N) n) (_ : Ω),
      0 ≤ (B.scale E N p.1)⁻¹ ^ (n - 1) := fun N p _ => pow_nonneg (inv_pos.2 (hA N p.1)).le _
  have hprod := StochDom.mul hinv (fun _ _ _ => zero_le_one) hY (StochDom.refl hinv)
  refine StochDom.of_le_left (fun N p ω => ?_)
    (stochDom_mono hinv 1 (Eventually.of_forall fun N p ω => by simp) hprod)
  have h1 := X.norm_Lval_le_loopMax (E := E) (t := p.1) (ω := ω) p.2
  have hA' := hA N p.1
  simp only [Pi.mul_apply, flowXiL, Sample.xiL, loopXi]
  refine h1.trans (le_of_eq ?_)
  unfold flowA at hA'
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hA'.ne', one_pow, mul_one]

/-- **(2.77) for the flow** (`n = 1` and `n ≥ 3`), in the shape of `RBM.Steps.sharpLoop`.
(`n = 2` needs (5.107) at `n = 2`, i.e. `|K_{u,σ,a}| ≤ C (W ℓ_u η_u)^{-1}` for `2`-loops,
which is not used anywhere in the induction and not proved here.) -/
theorem flow_sharpLoop {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (h514 : ∀ n, 3 ≤ n → Lemma514 B.P (flowXiLK X E s t) (flowXiL X E s t) (flowA B E s t) n)
    (h0 : ∀ m, 1 ≤ m → S B.P (flowXiLK X E s t) (flowAs B E s) (flowR B s t) (flowA B E s t) m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 →
      S B.P (flowXiLK X E s t) (flowAs B E s) (flowR B s t) (flowA B E s t) m l)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) := by
  exact flow_sharpLoop_of X hκ0 hκ1 hEκ hs0 hst ht1 hc h514 h0 h12 hn
    (flow_xiL_le X hκ0 hκ1 hEκ hs0 ht1 hn)

end FlowFamilies

end Step3

end RBM
