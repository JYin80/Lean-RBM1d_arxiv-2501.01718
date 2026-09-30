/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.GUEPhaseG

/-!
# §7.2: `eq727GE`, the even-length primed bootstrap

The bootstrap (7.45) ⟹ (7.27) with the primed right side `rhs745G` of
`Hierarchy/GUEPhaseG.lean`: the continuity argument runs over the **even** lengths
`m ∈ [2, n₀]` only (`n₀` even).  At odd `m`, (6.4) (`loopMax_odd_sq_le`) and
(5.117) (`loopMax_two_mul_add_le`) bound the E^{(G)}/martingale terms of (7.45) only by
`L_{m±1}`, not by `L_m`, so `h745` is not available at odd `m`.  Odd lengths are recovered from
the even ones by the pathwise inequality `hodd : L_{2l+1} ≤ √(L_{2l} L_{2l+2})` ((6.4)), an
extra hypothesis satisfied by the GUE-grid loops (`gueLproc_odd`); see `docs/PAPER-VS-LEAN.md`
§5.5.

The private lemmas `eq727_pathGE`/`gEven_cond727G` are the pathwise bootstrap and its smallness
bookkeeping, with the continuity argument restricted to even lengths and `hLu` extended to odd
indices via `hodd`.
-/

namespace RBM.GUEPhase

open Set Filter MeasureTheory

section LBootstrapGEven

variable (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ)

/-- **Odd-length extension of an even-length bound via (6.4).** If `Lm` is bounded by
`M * s ^ (j - 1)` at every even `j ∈ [2, n₀]` (`hbd`), and `hodd` gives the pathwise inequality
`L_{2l+1} ≤ √(L_{2l} L_{2l+2})`, then the same bound holds at the odd `m` too. Generic in the time
argument `t` and the scale `s` so it can be applied both at a fixed time (final extension) and at a
running time `u ≤ t` inside the continuity argument. -/
private theorem gEven_oddBound {Lm : ℕ → ℝ → ℝ} {n0 : ℕ} (hn0 : Even n0)
    (hL0 : ∀ m t, 0 ≤ Lm m t) {M s : ℝ} (hM0 : 0 ≤ M) (hs0 : 0 ≤ s) {t : ℝ}
    (hodd : ∀ l : ℕ, 1 ≤ l → 2 * l + 2 ≤ n0 →
      Lm (2 * l + 1) t ≤ Real.sqrt (Lm (2 * l) t * Lm (2 * l + 2) t))
    {m : ℕ} (hm2 : 2 ≤ m) (hmn : m ≤ n0) (hmo : Odd m)
    (hbd : ∀ j, 2 ≤ j → j ≤ n0 → Even j → Lm j t ≤ M * s ^ (j - 1)) :
    Lm m t ≤ M * s ^ (m - 1) := by
  obtain ⟨l, hl⟩ := hmo
  have hl1 : 1 ≤ l := by omega
  have hl2 : 2 * l + 2 ≤ n0 := by
    obtain ⟨k, hk⟩ := hn0; omega
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have heL := hbd (2 * (k + 1)) (by omega) (by omega) ⟨k + 1, two_mul (k + 1)⟩
  have heL2 := hbd (2 * (k + 1) + 2) (by omega) hl2 ⟨k + 2, by ring⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) + 2 - 1 = 2 * k + 3 := by omega
  rw [e1] at heL
  rw [e2] at heL2
  have hoddt := hodd (k + 1) hl1 hl2
  have hprod : Lm (2 * (k + 1)) t * Lm (2 * (k + 1) + 2) t ≤
      (M * s ^ (2 * k + 1)) * (M * s ^ (2 * k + 3)) :=
    mul_le_mul heL heL2 (hL0 _ _) (by positivity)
  have hpoweq : s ^ (2 * k + 1) * s ^ (2 * k + 3) = s ^ (2 * k + 2) * s ^ (2 * k + 2) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  have heq : (M * s ^ (2 * k + 1)) * (M * s ^ (2 * k + 3)) = (M * s ^ (2 * k + 2)) ^ 2 := by
    calc (M * s ^ (2 * k + 1)) * (M * s ^ (2 * k + 3))
        = M * M * (s ^ (2 * k + 1) * s ^ (2 * k + 3)) := by ring
      _ = M * M * (s ^ (2 * k + 2) * s ^ (2 * k + 2)) := by rw [hpoweq]
      _ = (M * s ^ (2 * k + 2)) ^ 2 := by ring
  have hsq : Real.sqrt (Lm (2 * (k + 1)) t * Lm (2 * (k + 1) + 2) t) ≤ M * s ^ (2 * k + 2) := by
    calc Real.sqrt (Lm (2 * (k + 1)) t * Lm (2 * (k + 1) + 2) t)
        ≤ Real.sqrt ((M * s ^ (2 * k + 1)) * (M * s ^ (2 * k + 3))) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt ((M * s ^ (2 * k + 2)) ^ 2) := by rw [heq]
      _ = M * s ^ (2 * k + 2) := Real.sqrt_sq (by positivity)
  have hfin : Lm (2 * (k + 1) + 1) t ≤ M * s ^ (2 * k + 2) := hoddt.trans hsq
  have hm1 : m - 1 = 2 * k + 2 := by omega
  rw [hm1, hl]
  exact hfin

/-- **(7.27) from (7.45)G at even lengths only, pathwise.** The continuity argument runs over
`S = {m ∈ [2, n₀] | Even m}`; inside the step, `hLu` at odd `j`
comes from `hodd` (`gEven_oddBound`); the output is over **all** `m ∈ [2, n₀]` (odd via `hodd` at
the final time). -/
private theorem eq727_pathGE {Lm Dm Km : ℕ → ℝ → ℝ} {n0 : ℕ} (hn0 : Even n0)
    {t0 A M Φ ε δ : ℝ}
    (hN : 0 < N) (ht10 : t1 ≤ t0)
    (hη : ∀ t ∈ Icc t1 t0, 0 < η t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → η t ≤ η u)
    (hηc : ContinuousOn η (Icc t1 t0))
    (hδ : ∀ t ∈ Icc t1 t0, (N * η t)⁻¹ ≤ δ) (hδ1 : δ ≤ 1)
    (hsm : ∀ t ∈ Icc t1 t0, t - t1 ≤ ε * η t) (hε : 0 ≤ ε)
    (hLc : ∀ m ∈ Set.Icc 2 n0, Even m → ContinuousOn (Lm m) (Icc t1 t0))
    (hL0 : ∀ m t, 0 ≤ Lm m t) (hD0 : ∀ m t, 0 ≤ Dm m t)
    (hLDK : ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc t1 t0, Lm m t ≤ Dm m t + Km m t)
    (hDLK : ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc t1 t0, Dm m t ≤ Lm m t + Km m t)
    (hodd : ∀ l : ℕ, 1 ≤ l → 2 * l + 2 ≤ n0 → ∀ t ∈ Icc t1 t0,
      Lm (2 * l + 1) t ≤ Real.sqrt (Lm (2 * l) t * Lm (2 * l + 2) t))
    (hK : ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc t1 t0, Km m t ≤ A * (N * η t)⁻¹ ^ (m - 1))
    (h745 : ∀ m ∈ Set.Icc 2 n0, Even m → ∀ t ∈ Icc t1 t0,
      Dm m t ≤ Φ * rhs745G N η t1 Lm Dm m t)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hΦ : 0 ≤ Φ)
    (hcond : A + Φ * (ε * n0 * ((1 + (M + A)) * (M + A)) + δ + ε * (M * M)
      + Real.sqrt ε * M) < M) :
    ∀ t ∈ Icc t1 t0, ∀ m ∈ Set.Icc 2 n0, Lm m t ≤ M * (N * η t)⁻¹ ^ (m - 1) := by
  have hx0 : ∀ t ∈ Icc t1 t0, 0 < (N * η t)⁻¹ := fun t ht => inv_pos.2 (mul_pos hN (hη t ht))
  have hgc : ∀ m ∈ {m ∈ Set.Icc 2 n0 | Even m},
      ContinuousOn (fun t => M * (N * η t)⁻¹ ^ (m - 1)) (Icc t1 t0) :=
    fun m _ => continuousOn_const.mul
      (((continuousOn_const.mul hηc).inv₀ fun t ht => (mul_pos hN (hη t ht)).ne').pow _)
  have hc1 : 0 ≤ ε * n0 * ((1 + (M + A)) * (M + A)) := by positivity
  have hc3 : 0 ≤ ε * (M * M) := by positivity
  have hc4 : 0 ≤ Real.sqrt ε * M := by positivity
  have hS : Set.Finite {m ∈ Set.Icc 2 n0 | Even m} :=
    (Set.finite_Icc 2 n0).subset fun x hx => hx.1
  have heven : ∀ t ∈ Icc t1 t0, ∀ m ∈ {m ∈ Set.Icc 2 n0 | Even m},
      Lm m t < M * (N * η t)⁻¹ ^ (m - 1) := by
    refine continuity_argument hS (fun m hm => hLc m hm.1 hm.2) hgc (fun m hm => ?_)
      (fun t ht hprev m hm => ?_)
    · obtain ⟨hm2n0, hme⟩ := hm
      have ht1 : t1 ∈ Icc t1 t0 := ⟨le_rfl, ht10⟩
      set x := (N * η t1)⁻¹ with hx
      have hxp := hx0 t1 ht1
      have hD := h745 m hm2n0 hme t1 ht1
      have hself : rhs745G N η t1 Lm Dm m t1 = (N * η t1)⁻¹ ^ m := by simp [rhs745G]
      rw [hself] at hD
      have hxm : x ^ m ≤ δ * x ^ (m - 1) := by
        have : x ^ m = x * x ^ (m - 1) := by
          rw [← pow_succ']; congr 1; have := hm2n0.1; omega
        rw [this]
        exact mul_le_mul_of_nonneg_right (hδ t1 ht1) (by positivity)
      have hLt := hLDK m hm2n0 t1 ht1
      have hKt := hK m hm2n0 t1 ht1
      have hpos : 0 < x ^ (m - 1) := pow_pos hxp _
      show Lm m t1 < M * x ^ (m - 1)
      have hΦx : Φ * x ^ m ≤ Φ * δ * x ^ (m - 1) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hxm hΦ
      have hcond' : A + Φ * δ < M := by nlinarith
      nlinarith
    · obtain ⟨hm2n0, hme⟩ := hm
      obtain ⟨hm2, hmn⟩ := hm2n0
      show Lm m t < M * (N * η t)⁻¹ ^ (m - 1)
      set x := (N * η t)⁻¹ with hx
      have hxp := hx0 t ht
      have hx1 : x ≤ 1 := (hδ t ht).trans hδ1
      have hηt := hη t ht
      have ht1t : t1 ≤ t := ht.1
      have hsub : Icc t1 t ⊆ Icc t1 t0 := Icc_subset_Icc_right ht.2
      have hxu : ∀ u ∈ Icc t1 t, 0 ≤ (N * η u)⁻¹ ∧ (N * η u)⁻¹ ≤ x := by
        intro u hu
        have hu0 := hsub hu
        refine ⟨(hx0 u hu0).le, inv_anti₀ (mul_pos hN hηt) ?_⟩
        exact mul_le_mul_of_nonneg_left (hanti u hu0 t ht hu.2) hN.le
      have hLu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ n0 → Lm j u ≤ M * x ^ (j - 1) := by
        intro u hu j h2 hj
        rcases Nat.even_or_odd j with hje | hjo
        · have hprevj := hprev u hu j ⟨⟨h2, hj⟩, hje⟩
          refine hprevj.trans ?_
          gcongr
          · exact (hxu u hu).1
          · exact (hxu u hu).2
        · have hLj : Lm j u ≤ M * (N * η u)⁻¹ ^ (j - 1) :=
            gEven_oddBound hn0 hL0 hM (hx0 u (hsub hu)).le
              (fun l hl1 hl2 => hodd l hl1 hl2 u (hsub hu)) h2 hj hjo
              (fun k hk1 hk2 hke => hprev u hu k ⟨⟨hk1, hk2⟩, hke⟩)
          refine hLj.trans ?_
          gcongr
          · exact (hxu u hu).1
          · exact (hxu u hu).2
      have hDu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ m → 0 ≤ Dm j u ∧
          Dm j u ≤ (M + A) * x ^ (j - 1 + 0) := by
        intro u hu j h2 hj
        refine ⟨hD0 j u, ?_⟩
        have hjn : j ∈ Set.Icc 2 n0 := ⟨h2, hj.trans hmn⟩
        have h1 := hDLK j hjn u (hsub hu)
        have h2' := hK j hjn u (hsub hu)
        have h3 : A * (N * η u)⁻¹ ^ (j - 1) ≤ A * x ^ (j - 1) := by
          gcongr
          · exact (hxu u hu).1
          · exact (hxu u hu).2
        have h4 := hLu u hu j h2 (hj.trans hmn)
        rw [Nat.add_zero]
        nlinarith
      -- line 1
      have hl1 := supOn_line1_le N η t1 (n := m) 0 (by norm_num) ht1t (by positivity) hxp.le
        hx1 hxu hDu
      have hmx : x⁻¹ * x ^ m = x ^ (m - 1) := inv_mul_pow hxp.ne' (by omega)
      have hm0 : (m : ℝ) ≤ n0 := by exact_mod_cast hmn
      have hline1 : N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
          ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (m - k + 2) u) t1 t
          ≤ ε * n0 * ((1 + (M + A)) * (M + A)) * x ^ (m - 1) := by
        have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN.le (by linarith)
        calc _ ≤ N * (t - t1) * (m * ((1 + (M + A)) * (M + A) * x ^ (m + 0))) :=
              mul_le_mul_of_nonneg_left hl1 hNt
          _ ≤ ε * x⁻¹ * (m * ((1 + (M + A)) * (M + A) * x ^ (m + 0))) :=
              mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
          _ = ε * m * ((1 + (M + A)) * (M + A)) * (x⁻¹ * x ^ m) := by ring
          _ ≤ ε * n0 * ((1 + (M + A)) * (M + A)) * (x⁻¹ * x ^ m) := by gcongr
          _ = _ := by rw [hmx]
      -- line 2
      have hline2 : x ^ m ≤ δ * x ^ (m - 1) := by
        have : x ^ m = x * x ^ (m - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [this]
        exact mul_le_mul_of_nonneg_right (hδ t ht) (by positivity)
      -- line 3 (E^{(G)} term `N L₂ L_n`, no fluctuation averaging)
      have hline3 : N * (t - t1) * supOn (fun u => Lm 2 u * Lm m u) t1 t
          ≤ ε * (M * M) * x ^ (m - 1) := by
        have hsup : supOn (fun u => Lm 2 u * Lm m u) t1 t ≤ M * M * x ^ m := by
          refine supOn_le ht1t fun u hu => ?_
          have h2 : Lm 2 u ≤ M * x := by simpa using hLu u hu 2 le_rfl (by omega)
          have hm' : Lm m u ≤ M * x ^ (m - 1) := hLu u hu m hm2 hmn
          calc Lm 2 u * Lm m u ≤ (M * x) * (M * x ^ (m - 1)) :=
                mul_le_mul h2 hm' (hL0 m u) (by positivity)
            _ = M * M * (x * x ^ (m - 1)) := by ring
            _ = M * M * x ^ m := by rw [← pow_succ']; congr 2; omega
        have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN.le (by linarith)
        calc _ ≤ N * (t - t1) * (M * M * x ^ m) := mul_le_mul_of_nonneg_left hsup hNt
          _ ≤ ε * x⁻¹ * (M * M * x ^ m) :=
              mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
          _ = ε * (M * M) * (x⁻¹ * x ^ m) := by ring
          _ = _ := by rw [hmx]
      -- line 4
      have hline4 : Real.sqrt (t - t1) *
          supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm m u) t1 t
          ≤ Real.sqrt ε * M * x ^ (m - 1) := by
        have hsup : supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm m u) t1 t
            ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) * (M * x ^ (m - 1)) := by
          refine supOn_le ht1t fun u hu => ?_
          have hu0 := hsub hu
          have hηu : (η u)⁻¹ ≤ (η t)⁻¹ := inv_anti₀ hηt (hanti u hu0 t ht hu.2)
          have hs : Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) := by
            refine Real.sqrt_le_sqrt ?_
            have : 0 ≤ (η u)⁻¹ := (inv_pos.2 (hη u hu0)).le
            gcongr
          exact mul_le_mul hs (hLu u hu m hm2 hmn) (hL0 m u) (Real.sqrt_nonneg _)
        have hsq := sqrt_mul_sqrt_le N η t1 hN hηt ht1t (hsm t ht)
        have hsx : Real.sqrt (ε * (N * η t)⁻¹) ≤ Real.sqrt ε := by
          refine Real.sqrt_le_sqrt ?_
          calc ε * (N * η t)⁻¹ ≤ ε * 1 := mul_le_mul_of_nonneg_left hx1 hε
            _ = ε := mul_one ε
        have hpos : 0 ≤ M * x ^ (m - 1) := by positivity
        calc _ ≤ Real.sqrt (t - t1) * (Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) * (M * x ^ (m - 1))) :=
              mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
          _ = (Real.sqrt (t - t1) * Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2)) * (M * x ^ (m - 1)) := by ring
          _ ≤ Real.sqrt ε * (M * x ^ (m - 1)) :=
              mul_le_mul_of_nonneg_right (hsq.trans hsx) hpos
          _ = _ := by ring
      -- assemble
      have hD := h745 m ⟨hm2, hmn⟩ hme t ht
      have hrhs : rhs745G N η t1 Lm Dm m t ≤ (ε * n0 * ((1 + (M + A)) * (M + A)) + δ
          + ε * (M * M) + Real.sqrt ε * M) * x ^ (m - 1) := by
        unfold rhs745G
        rw [← hx]
        nlinarith
      have hDt : Dm m t ≤ Φ * ((ε * n0 * ((1 + (M + A)) * (M + A)) + δ
          + ε * (M * M) + Real.sqrt ε * M) * x ^ (m - 1)) :=
        hD.trans (mul_le_mul_of_nonneg_left hrhs hΦ)
      have hLt := hLDK m ⟨hm2, hmn⟩ t ht
      have hKt := hK m ⟨hm2, hmn⟩ t ht
      have hpos : 0 < x ^ (m - 1) := pow_pos hxp _
      nlinarith
  intro t ht m hm
  rcases Nat.even_or_odd m with hme | hmo
  · exact (heven t ht m ⟨hm, hme⟩).le
  · obtain ⟨hm2, hmn⟩ := hm
    exact gEven_oddBound hn0 hL0 hM (hx0 t ht).le
      (fun l hl1 hl2 => hodd l hl1 hl2 t ht) hm2 hmn hmo
      (fun k hk1 hk2 hke => (heven t ht k ⟨⟨hk1, hk2⟩, hke⟩).le)

end LBootstrapGEven

section DominationGE

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The smallness bookkeeping of (7.45)G, restricted to even lengths. -/
private theorem gEven_cond727G {p q : ℝ} (n0 : ℕ) (hp : 1 ≤ p) (hq : 0 ≤ q)
    (hr : p ^ 3 * q ≤ 1 / (36 * (20 * n0 + 48))) :
    p + p * (q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) + q
      + q * (3 * p * (3 * p)) + Real.sqrt q * (3 * p)) < 3 * p := by
  set r := p ^ 3 * q with hrdef
  have hn0 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg n0
  have hρ : 1 / (36 * (20 * (n0 : ℝ) + 48)) ≤ 1 / 36 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hp0 : 0 < p := by linarith
  have hp2 : p ^ 2 * q ≤ r := by
    rw [hrdef]; have : p ^ 2 ≤ p ^ 3 := pow_le_pow_right₀ hp (by norm_num)
    exact mul_le_mul_of_nonneg_right this hq
  have hq1 : q ≤ r := by
    rw [hrdef]; have : 1 ≤ p ^ 3 := one_le_pow₀ hp
    nlinarith
  have hT1 : q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) ≤ 20 * n0 * r := by
    have h1 : (1 + (3 * p + p)) * (3 * p + p) ≤ 20 * p ^ 2 := by nlinarith
    calc q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) ≤ q * n0 * (20 * p ^ 2) := by gcongr
      _ = 20 * n0 * (p ^ 2 * q) := by ring
      _ ≤ 20 * n0 * r := by gcongr
  have hT3 : q * (3 * p * (3 * p)) ≤ 9 * r := by
    have heq : q * (3 * p * (3 * p)) = 9 * (p ^ 2 * q) := by ring
    rw [heq]; nlinarith [hp2]
  have hT4 : Real.sqrt q * (3 * p) ≤ 3 * Real.sqrt r := by
    have : Real.sqrt q * p = Real.sqrt (p ^ 2 * q) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hp0.le]; ring
    have h2 : Real.sqrt (p ^ 2 * q) ≤ Real.sqrt r := Real.sqrt_le_sqrt hp2
    nlinarith
  have hsr : Real.sqrt r ≤ 1 / 6 := by
    rw [show (1 : ℝ) / 6 = Real.sqrt (1 / 36) by
      rw [show (1 : ℝ) / 36 = (1 / 6) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (hr.trans hρ)
  have hsum : (20 * n0 + 48) * r ≤ 1 / 36 := by
    have h48 : (0 : ℝ) < 20 * n0 + 48 := by positivity
    calc (20 * n0 + 48) * r ≤ (20 * n0 + 48) * (1 / (36 * (20 * n0 + 48))) := by gcongr
      _ = 1 / 36 := by field_simp
  have hr0 : 0 ≤ r := by positivity
  have hS : q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) + q
      + q * (3 * p * (3 * p)) + Real.sqrt q * (3 * p) < 2 := by nlinarith
  nlinarith

/-- **(7.27) from (7.45)G at even lengths only**: the continuity
argument runs over the even `m ∈ [2, n₀]`; odd lengths are controlled by (6.4) through `hodd`. -/
theorem eq727GE {n0 : ℕ} (hn0 : Even n0) (Nf : ℕ → ℝ) (η : ℕ → ℝ → ℝ) (t1 t0 : ℕ → ℝ)
    (Lm Dm : ℕ → ℕ → ℝ → Ω → ℝ) (Km : ℕ → ℕ → ℝ → ℝ)
    (hN : ∀ N, 0 < Nf N) (ht10 : ∀ N, t1 N ≤ t0 N)
    (hη : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), 0 < η N t)
    (hanti : ∀ N, ∀ u ∈ Icc (t1 N) (t0 N), ∀ t ∈ Icc (t1 N) (t0 N), u ≤ t → η N t ≤ η N u)
    (hηc : ∀ N, ContinuousOn (η N) (Icc (t1 N) (t0 N)))
    {τU : ℝ} (hτU : 0 < τU)
    (h730 : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), t - t1 N ≤ (N : ℝ) ^ (-τU) * η N t)
    (hscale : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), (Nf N * η N t)⁻¹ ≤ (N : ℝ) ^ (-τU))
    (hL0 : ∀ N m t ω, 0 ≤ Lm N m t ω) (hD0 : ∀ N m t ω, 0 ≤ Dm N m t ω)
    (hLDK : ∀ N ω, ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc (t1 N) (t0 N), Lm N m t ω ≤ Dm N m t ω + Km N m t)
    (hDLK : ∀ N ω, ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc (t1 N) (t0 N), Dm N m t ω ≤ Lm N m t ω + Km N m t)
    (hodd : ∀ N ω, ∀ l : ℕ, 1 ≤ l → 2 * l + 2 ≤ n0 → ∀ t ∈ Icc (t1 N) (t0 N),
      Lm N (2 * l + 1) t ω ≤ Real.sqrt (Lm N (2 * l) t ω * Lm N (2 * l + 2) t ω))
    (hK : UnifDetDom (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 n0) => Km N p.2 p.1)
      (fun N p => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)))
    (hcont : HighProb P (fun N => {ω | ∀ m ∈ Set.Icc 2 n0, Even m →
      ContinuousOn (fun t => Lm N m t ω) (Icc (t1 N) (t0 N))}))
    (h745 : StochDom P
      (fun N (p : TimeIcc t1 t0 N × {m : ℕ // m ∈ Set.Icc 2 n0 ∧ Even m}) ω => Dm N p.2.1 p.1 ω)
      (fun N p ω => rhs745G (Nf N) (η N) (t1 N) (fun m t => Lm N m t ω) (fun m t => Dm N m t ω)
        p.2.1 p.1)) :
    StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 n0) ω => Lm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) := by
  refine stochDom_of_forall_highProb fun τ hτ => ?_
  set τ' := min τ τU / 16 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'τ : τ' < τ := by have := min_le_left τ τU; linarith
  have hτ'U : 3 * τ' - τU < 0 := by have := min_le_right τ τU; linarith
  have hρ : (0 : ℝ) < 1 / (36 * (20 * n0 + 48)) := by positivity
  refine ((h745.highProb hτ'0).inter hcont).mono ?_
  filter_upwards [hK τ' hτ'0, h730, hscale, eventually_rpow_le_of_neg hτ'U hρ,
    eventually_le_rpow 3 (sub_pos.2 hτ'τ), eventually_ge_atTop 1]
    with N hKN h730N hscN hrN h3N hN1
  rintro ω ⟨h745ω, hcω⟩
  simp only [Set.mem_ofPred_eq] at h745ω hcω ⊢
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
  have key := eq727_pathGE (Nf N) (η N) (t1 N) hn0 (Lm := fun m t => Lm N m t ω)
    (Dm := fun m t => Dm N m t ω) (Km := Km N) (n0 := n0) (A := p) (M := 3 * p) (Φ := p)
    (ε := q) (δ := q) (hN N) (ht10 N) (hη N) (hanti N) (hηc N) hscN hq1 h730N hq0
    (fun m hm hme => hcω m hm hme) (fun m t => hL0 N m t ω) (fun m t => hD0 N m t ω) (hLDK N ω)
    (hDLK N ω) (fun l hl1 hl2 t ht => hodd N ω l hl1 hl2 t ht)
    (fun m hm t ht => by simpa using hKN (⟨t, ht⟩, ⟨m, hm⟩))
    (fun m hm hme t ht => by simpa using h745ω (⟨t, ht⟩, ⟨m, hm, hme⟩)) (by linarith) (by linarith)
    (by linarith) (gEven_cond727G n0 hp1 hq0 hr)
  rintro ⟨⟨t, ht⟩, ⟨m, hm⟩⟩
  have h1 := key t ht m hm
  have hx : 0 ≤ (Nf N * η N t)⁻¹ ^ (m - 1) := by
    have := hη N t ht; have := hN N; positivity
  have h3 : 3 * p ≤ (N : ℝ) ^ τ := by
    have e : (N : ℝ) ^ τ = (N : ℝ) ^ (τ - τ') * p := by
      rw [hpdef, ← Real.rpow_add hN0]; ring_nf
    rw [e]; nlinarith
  show Lm N m t ω ≤ (N : ℝ) ^ τ * (Nf N * η N t)⁻¹ ^ (m - 1)
  nlinarith

end DominationGE

end RBM.GUEPhase
