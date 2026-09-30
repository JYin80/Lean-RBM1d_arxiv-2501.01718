/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.GUEPhase

/-!
# §7.2: the primed right sides of (7.45), (7.46), and the bootstrap `eq728G`

The bootstraps (7.45) ⟹ (7.27) and (7.46) ⟹ (7.28) when the E^{(G)} term of (7.41)/(7.42) is
available only in the weaker form given by Lemma 4.1 (4.3) together with (5.117)/(6.4), without
fluctuation averaging (4.5).

* **(7.45), primed** (`rhs745G`): the E^{(G)} term is `N L₂ L_n` instead of `N L₂^{3/2} L_n`.
* **(7.46), primed** (`rhs746G`): the E^{(G)} term is `N D₁ L_{n+1}` (the tracked `1`-loop)
  instead of `N L₂ L_{n+1}`, and the bootstrap now also covers length `n = 1` (where the
  quadratic sum of (7.46) is empty).
* `eq728G`: the `≺` statement (7.28) from the primed right side of (7.46).  (7.27) from the
  primed (7.45) is `eq727GE` of `Hierarchy/GUEPhaseGEven.lean`.  The smallness bookkeeping is
  `9qp³` for (7.45) and `3qp²` for (7.46), both `≤ ρ = (36(20n₀+48))⁻¹` for `p³q ≤ ρ`, so
  `τ' = min τ τU / 16` works.
-/

namespace RBM.GUEPhase

open Set Filter MeasureTheory

section LBootstrapG

variable (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ)

/-- (7.45) with the E^{(G)} term `N L₂ L_n` (from (4.3) + (5.117), no fluctuation averaging). -/
noncomputable def rhs745G (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
    + (N * η t)⁻¹ ^ n
    + N * (t - t1) * supOn (fun u => Lm 2 u * Lm n u) t1 t
    + Real.sqrt (t - t1) * supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm n u) t1 t

/-- (7.46) with the E^{(G)} term `N D₁ L_{n+1}` (the `1`-loop tracked in the bootstrap). -/
noncomputable def rhs746G (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
    + (N * η t)⁻¹ ^ n
    + N * (t - t1) * supOn (fun u => Dm 1 u * Lm (n + 1) u) t1 t
    + Real.sqrt (t - t1) * supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) *
        Real.sqrt (Lm (2 * n) u)) t1 t

private theorem rhs746G_self (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) :
    rhs746G N η t1 Lm Dm n t1 = (N * η t1)⁻¹ ^ n := by
  simp [rhs746G]

/-- **(7.46)G ⟹ (7.28), pathwise, for `1 ≤ n ≤ n₀`.** It covers length `n = 1` (where the
quadratic sum of (7.46) is empty), and the E^{(G)} term is `D₁ L_{n+1}` (the `1`-loop tracked
simultaneously in the same bootstrap). -/
private theorem eq728_pathG {Lm Dm : ℕ → ℝ → ℝ} {n0 : ℕ} {t0 M M' Φ ε δ : ℝ}
    (hN : 0 < N) (ht10 : t1 ≤ t0)
    (hη : ∀ t ∈ Icc t1 t0, 0 < η t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → η t ≤ η u)
    (hηc : ContinuousOn η (Icc t1 t0))
    (hδ : ∀ t ∈ Icc t1 t0, (N * η t)⁻¹ ≤ δ) (hδ1 : δ ≤ 1)
    (hsm : ∀ t ∈ Icc t1 t0, t - t1 ≤ ε * η t) (hε : 0 ≤ ε)
    (hDc : ∀ m ∈ Set.Icc 1 n0, ContinuousOn (Dm m) (Icc t1 t0))
    (hL0 : ∀ m t, 0 ≤ Lm m t) (hD0 : ∀ m t, 0 ≤ Dm m t)
    (hL : ∀ j, 2 ≤ j → j ≤ 2 * n0 → ∀ t ∈ Icc t1 t0, Lm j t ≤ M * (N * η t)⁻¹ ^ (j - 1))
    (h746 : ∀ m ∈ Set.Icc 1 n0, ∀ t ∈ Icc t1 t0, Dm m t ≤ Φ * rhs746G N η t1 Lm Dm m t)
    (hM : 0 ≤ M) (hM' : 0 ≤ M') (hΦ : 0 ≤ Φ)
    (hcond : Φ * (ε * n0 * ((1 + M') * M') + 1 + ε * (M' * M) + Real.sqrt (ε * M)) < M') :
    ∀ t ∈ Icc t1 t0, ∀ m ∈ Set.Icc 1 n0, Dm m t < M' * (N * η t)⁻¹ ^ m := by
  have hx0 : ∀ t ∈ Icc t1 t0, 0 < (N * η t)⁻¹ := fun t ht => inv_pos.2 (mul_pos hN (hη t ht))
  have hgc : ∀ m ∈ Set.Icc 1 n0, ContinuousOn (fun t => M' * (N * η t)⁻¹ ^ m) (Icc t1 t0) :=
    fun m _ => continuousOn_const.mul
      (((continuousOn_const.mul hηc).inv₀ fun t ht => (mul_pos hN (hη t ht)).ne').pow _)
  have hc1 : 0 ≤ ε * n0 * ((1 + M') * M') := by positivity
  have hc3 : 0 ≤ ε * (M' * M) := by positivity
  have hc4 : 0 ≤ Real.sqrt (ε * M) := Real.sqrt_nonneg _
  refine continuity_argument (Set.finite_Icc 1 n0) hDc hgc (fun m hm => ?_)
    (fun t ht hprev m hm => ?_)
  · have ht1 : t1 ∈ Icc t1 t0 := ⟨le_rfl, ht10⟩
    have hD := h746 m hm t1 ht1
    rw [rhs746G_self] at hD
    have hpos : 0 < (N * η t1)⁻¹ ^ m := pow_pos (hx0 t1 ht1) _
    show Dm m t1 < M' * (N * η t1)⁻¹ ^ m
    have : Φ < M' := by nlinarith
    nlinarith
  show Dm m t < M' * (N * η t)⁻¹ ^ m
  set x := (N * η t)⁻¹ with hx
  have hxp := hx0 t ht
  have hx1 : x ≤ 1 := (hδ t ht).trans hδ1
  have hηt := hη t ht
  have ht1t : t1 ≤ t := ht.1
  have hsub : Icc t1 t ⊆ Icc t1 t0 := Icc_subset_Icc_right ht.2
  obtain ⟨hm1, hmn⟩ := hm
  have hxu : ∀ u ∈ Icc t1 t, 0 ≤ (N * η u)⁻¹ ∧ (N * η u)⁻¹ ≤ x := by
    intro u hu
    have hu0 := hsub hu
    refine ⟨(hx0 u hu0).le, inv_anti₀ (mul_pos hN hηt) ?_⟩
    exact mul_le_mul_of_nonneg_left (hanti u hu0 t ht hu.2) hN.le
  have hLu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ 2 * n0 → Lm j u ≤ M * x ^ (j - 1) := by
    intro u hu j h2 hj
    refine (hL j h2 hj u (hsub hu)).trans ?_
    gcongr
    · exact (hxu u hu).1
    · exact (hxu u hu).2
  have hDu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ m → 0 ≤ Dm j u ∧
      Dm j u ≤ M' * x ^ (j - 1 + 1) := by
    intro u hu j h2 hj
    refine ⟨hD0 j u, (hprev u hu j ⟨by omega, hj.trans hmn⟩).trans ?_⟩
    have : j - 1 + 1 = j := by omega
    rw [this]
    gcongr
    · exact (hxu u hu).1
    · exact (hxu u hu).2
  have hD1u : ∀ u ∈ Icc t1 t, Dm 1 u ≤ M' * x := by
    intro u hu
    have h1n0 : (1 : ℕ) ∈ Set.Icc 1 n0 := ⟨le_rfl, by omega⟩
    have hprev1 := hprev u hu 1 h1n0
    calc Dm 1 u ≤ M' * (N * η u)⁻¹ ^ 1 := hprev1
      _ = M' * (N * η u)⁻¹ := by ring
      _ ≤ M' * x := mul_le_mul_of_nonneg_left (hxu u hu).2 hM'
  have hmx : x⁻¹ * x ^ (m + 1) = x ^ m := by
    rw [inv_mul_pow hxp.ne' (by omega)]; rfl
  have hm0 : (m : ℝ) ≤ n0 := by exact_mod_cast hmn
  have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN.le (by linarith)
  -- line 1
  have hl1 := supOn_line1_le N η t1 (n := m) 1 le_rfl ht1t hM' hxp.le hx1 hxu hDu
  have hline1 : N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (m - k + 2) u) t1 t
      ≤ ε * n0 * ((1 + M') * M') * x ^ m := by
    calc _ ≤ N * (t - t1) * (m * ((1 + M') * M' * x ^ (m + 1))) :=
          mul_le_mul_of_nonneg_left hl1 hNt
      _ ≤ ε * x⁻¹ * (m * ((1 + M') * M' * x ^ (m + 1))) :=
          mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
      _ = ε * m * ((1 + M') * M') * (x⁻¹ * x ^ (m + 1)) := by ring
      _ ≤ ε * n0 * ((1 + M') * M') * (x⁻¹ * x ^ (m + 1)) := by gcongr
      _ = _ := by rw [hmx]
  -- line 3 (E^{(G)} term `N D₁ L_{n+1}`, the tracked 1-loop)
  have hline3 : N * (t - t1) * supOn (fun u => Dm 1 u * Lm (m + 1) u) t1 t
      ≤ ε * (M' * M) * x ^ m := by
    have hsup : supOn (fun u => Dm 1 u * Lm (m + 1) u) t1 t ≤ M' * M * x ^ (m + 1) := by
      refine supOn_le ht1t fun u hu => ?_
      have h1 : Dm 1 u ≤ M' * x := hD1u u hu
      have h2 : Lm (m + 1) u ≤ M * x ^ m := by simpa using hLu u hu (m + 1) (by omega) (by omega)
      calc Dm 1 u * Lm (m + 1) u ≤ (M' * x) * (M * x ^ m) :=
            mul_le_mul h1 h2 (hL0 (m + 1) u) (by positivity)
        _ = M' * M * x ^ (m + 1) := by rw [pow_succ']; ring
    calc _ ≤ N * (t - t1) * (M' * M * x ^ (m + 1)) := mul_le_mul_of_nonneg_left hsup hNt
      _ ≤ ε * x⁻¹ * (M' * M * x ^ (m + 1)) :=
          mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
      _ = ε * (M' * M) * (x⁻¹ * x ^ (m + 1)) := by ring
      _ = _ := by rw [hmx]
  -- line 4 (unchanged martingale term of (7.46))
  have hline4 : Real.sqrt (t - t1) *
      supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Real.sqrt (Lm (2 * m) u)) t1 t
      ≤ Real.sqrt (ε * M) * x ^ m := by
    have hsup : supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Real.sqrt (Lm (2 * m) u)) t1 t
        ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) * Real.sqrt (M * x ^ (2 * m - 1)) := by
      refine supOn_le ht1t fun u hu => ?_
      have hu0 := hsub hu
      have hηu : (η u)⁻¹ ≤ (η t)⁻¹ := inv_anti₀ hηt (hanti u hu0 t ht hu.2)
      have hs : Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        have : 0 ≤ (η u)⁻¹ := (inv_pos.2 (hη u hu0)).le
        gcongr
      have hs2 : Real.sqrt (Lm (2 * m) u) ≤ Real.sqrt (M * x ^ (2 * m - 1)) :=
        Real.sqrt_le_sqrt (hLu u hu (2 * m) (by omega) (by omega))
      exact mul_le_mul hs hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq := sqrt_mul_sqrt_le N η t1 hN hηt ht1t (hsm t ht)
    have hfin :
        Real.sqrt (ε * x) * Real.sqrt (M * x ^ (2 * m - 1)) = Real.sqrt (ε * M) * x ^ m := by
      rw [← Real.sqrt_mul (by positivity)]
      have : ε * x * (M * x ^ (2 * m - 1)) = ε * M * (x ^ m) ^ 2 := by
        have h2m : 2 * m - 1 + 1 = m * 2 := by omega
        have hxx : x * x ^ (2 * m - 1) = (x ^ m) ^ 2 := by
          rw [← pow_succ', h2m, pow_mul]
        calc ε * x * (M * x ^ (2 * m - 1)) = ε * M * (x * x ^ (2 * m - 1)) := by ring
          _ = ε * M * (x ^ m) ^ 2 := by rw [hxx]
      rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc _ ≤ Real.sqrt (t - t1) * (Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) *
            Real.sqrt (M * x ^ (2 * m - 1))) :=
          mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
      _ = (Real.sqrt (t - t1) * Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2)) *
            Real.sqrt (M * x ^ (2 * m - 1)) := by ring
      _ ≤ Real.sqrt (ε * x) * Real.sqrt (M * x ^ (2 * m - 1)) :=
          mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
      _ = _ := hfin
  have hD := h746 m ⟨hm1, hmn⟩ t ht
  have hrhs : rhs746G N η t1 Lm Dm m t ≤ (ε * n0 * ((1 + M') * M') + 1
      + ε * (M' * M) + Real.sqrt (ε * M)) * x ^ m := by
    unfold rhs746G
    rw [← hx]
    nlinarith
  have hDt := hD.trans (mul_le_mul_of_nonneg_left hrhs hΦ)
  have hpos : 0 < x ^ m := pow_pos hxp _
  nlinarith

end LBootstrapG

section DominationG

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The smallness bookkeeping of (7.46)G: with `p = N^{τ'} ≥ 1`, `q = N^{-τ_U}`, `p³ q ≤ ρ`, the
condition of `eq728_pathG` holds with `Φ = M = p`, `M' = 3p`, `ε = q` (the E^{(G)} term
contributes `3qp²` before the outer `Φ`, since it is linear in the tracked `D₁ ≺ Λ`). -/
private theorem cond728G {p q : ℝ} (n0 : ℕ) (hp : 1 ≤ p) (hq : 0 ≤ q)
    (hr : p ^ 3 * q ≤ 1 / (36 * (20 * n0 + 48))) :
    p * (q * n0 * ((1 + 3 * p) * (3 * p)) + 1 + q * (3 * p * p) + Real.sqrt (q * p)) < 3 * p := by
  set r := p ^ 3 * q with hrdef
  have hn0 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg n0
  have hρ : 1 / (36 * (20 * (n0 : ℝ) + 48)) ≤ 1 / 36 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hp0 : 0 < p := by linarith
  have hp2 : p ^ 2 * q ≤ r := by
    rw [hrdef]; have : p ^ 2 ≤ p ^ 3 := pow_le_pow_right₀ hp (by norm_num)
    exact mul_le_mul_of_nonneg_right this hq
  have hp1 : q * p ≤ r := by
    rw [hrdef]; have : p ≤ p ^ 3 := by nlinarith
    nlinarith
  have hT1 : q * n0 * ((1 + 3 * p) * (3 * p)) ≤ 12 * n0 * r := by
    have h1 : (1 + 3 * p) * (3 * p) ≤ 12 * p ^ 2 := by nlinarith
    calc q * n0 * ((1 + 3 * p) * (3 * p)) ≤ q * n0 * (12 * p ^ 2) := by gcongr
      _ = 12 * n0 * (p ^ 2 * q) := by ring
      _ ≤ 12 * n0 * r := by gcongr
  have hsr : Real.sqrt (q * p) ≤ 1 / 6 := by
    rw [show (1 : ℝ) / 6 = Real.sqrt (1 / 36) by
      rw [show (1 : ℝ) / 36 = (1 / 6) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ((hp1.trans hr).trans hρ)
  have hsum : (20 * n0 + 48) * r ≤ 1 / 36 := by
    have h48 : (0 : ℝ) < 20 * n0 + 48 := by positivity
    calc (20 * n0 + 48) * r ≤ (20 * n0 + 48) * (1 / (36 * (20 * n0 + 48))) := by gcongr
      _ = 1 / 36 := by field_simp
  have hr0 : 0 ≤ r := by positivity
  have hqpp : q * (3 * p * p) ≤ 3 * r := by
    have heq : q * (3 * p * p) = 3 * (p ^ 2 * q) := by ring
    rw [heq]; nlinarith [hp2]
  have hS : q * n0 * ((1 + 3 * p) * (3 * p)) + 1 + q * (3 * p * p) + Real.sqrt (q * p) < 2 := by
    nlinarith
  nlinarith

/-- **(7.28)** for `1 ≤ n ≤ n₀` from (7.46) in the `rhs746G` form and (7.27) at lengths
`2 ≤ j ≤ 2n₀`. -/
theorem eq728G {n0 : ℕ} (Nf : ℕ → ℝ) (η : ℕ → ℝ → ℝ) (t1 t0 : ℕ → ℝ)
    (Lm Dm : ℕ → ℕ → ℝ → Ω → ℝ)
    (hN : ∀ N, 0 < Nf N) (ht10 : ∀ N, t1 N ≤ t0 N)
    (hη : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), 0 < η N t)
    (hanti : ∀ N, ∀ u ∈ Icc (t1 N) (t0 N), ∀ t ∈ Icc (t1 N) (t0 N), u ≤ t → η N t ≤ η N u)
    (hηc : ∀ N, ContinuousOn (η N) (Icc (t1 N) (t0 N)))
    {τU : ℝ} (hτU : 0 < τU)
    (h730 : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), t - t1 N ≤ (N : ℝ) ^ (-τU) * η N t)
    (hscale : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), (Nf N * η N t)⁻¹ ≤ (N : ℝ) ^ (-τU))
    (hL0 : ∀ N m t ω, 0 ≤ Lm N m t ω) (hD0 : ∀ N m t ω, 0 ≤ Dm N m t ω)
    (h727 : StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 (2 * n0)) ω => Lm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)))
    (hcont : HighProb P (fun N => {ω | ∀ m ∈ Set.Icc 1 n0,
      ContinuousOn (fun t => Dm N m t ω) (Icc (t1 N) (t0 N))}))
    (h746 : StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 1 n0) ω => Dm N p.2 p.1 ω)
      (fun N p ω => rhs746G (Nf N) (η N) (t1 N) (fun m t => Lm N m t ω) (fun m t => Dm N m t ω)
        p.2 p.1)) :
    StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 1 n0) ω => Dm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ (p.2 : ℕ)) := by
  refine stochDom_of_forall_highProb fun τ hτ => ?_
  set τ' := min τ τU / 16 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'τ : τ' < τ := by have := min_le_left τ τU; linarith
  have hτ'U : 3 * τ' - τU < 0 := by have := min_le_right τ τU; linarith
  have hρ : (0 : ℝ) < 1 / (36 * (20 * n0 + 48)) := by positivity
  refine (((h746.highProb hτ'0).inter hcont).inter (h727.highProb hτ'0)).mono ?_
  filter_upwards [h730, hscale, eventually_rpow_le_of_neg hτ'U hρ,
    eventually_le_rpow 3 (sub_pos.2 hτ'τ), eventually_ge_atTop 1]
    with N h730N hscN hrN h3N hN1
  rintro ω ⟨⟨h746ω, hcω⟩, hLω⟩
  simp only [Set.mem_ofPred_eq] at h746ω hcω hLω ⊢
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set p := (N : ℝ) ^ τ' with hpdef
  set q := (N : ℝ) ^ (-τU) with hqdef
  have hp1 : 1 ≤ p := Real.one_le_rpow (by exact_mod_cast hN1) hτ'0.le
  have hq0 : 0 ≤ q := Real.rpow_nonneg hN0.le _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
  have hr : p ^ 3 * q ≤ 1 / (36 * (20 * n0 + 48)) := by
    have : p ^ 3 * q = (N : ℝ) ^ (3 * τ' - τU) := by
      rw [hpdef, hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      push_cast; ring_nf
    rw [this]; exact hrN
  have key := eq728_pathG (Nf N) (η N) (t1 N) (Lm := fun m t => Lm N m t ω)
    (Dm := fun m t => Dm N m t ω) (n0 := n0) (M := p) (M' := 3 * p) (Φ := p)
    (ε := q) (δ := q) (hN N) (ht10 N) (hη N) (hanti N) (hηc N) hscN hq1 h730N hq0
    (fun m hm => hcω m hm) (fun m t => hL0 N m t ω) (fun m t => hD0 N m t ω)
    (fun j h2 hj t ht => by simpa using hLω (⟨t, ht⟩, ⟨j, h2, hj⟩))
    (fun m hm t ht => by simpa using h746ω (⟨t, ht⟩, ⟨m, hm⟩)) (by linarith) (by linarith)
    (by linarith) (cond728G n0 hp1 hq0 hr)
  rintro ⟨⟨t, ht⟩, ⟨m, hm⟩⟩
  have h1 := key t ht m hm
  have hx : 0 ≤ (Nf N * η N t)⁻¹ ^ m := by
    have := hη N t ht; have := hN N; positivity
  have h3 : 3 * p ≤ (N : ℝ) ^ τ := by
    have e : (N : ℝ) ^ τ = (N : ℝ) ^ (τ - τ') * p := by
      rw [hpdef, ← Real.rpow_add hN0]; ring_nf
    rw [e]; nlinarith
  show Dm N m t ω ≤ (N : ℝ) ^ τ * (Nf N * η N t)⁻¹ ^ m
  nlinarith

end DominationG

end RBM.GUEPhase
