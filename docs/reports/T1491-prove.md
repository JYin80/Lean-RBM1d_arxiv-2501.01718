Prover model: claude-sonnet-5

# T1491 — (5.36) in the proof-exponent shape: math preflight and proof

## 0. Step 0 (read-only checks)

Read `RBM1D/Hierarchy/Lemma57.lean` (worktree `T1491`), section `EE` (lines 1506–1950).

- `RBM.Lemma57.ee_le` (:1818–1863) is the abstract master. Its conclusion keeps the far-field
  bracket unmerged: `cFar2 W ℓu * (J ^ 2 * ((W * ℓu * ηu) * μ)) + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹`,
  with `μ` a free nonnegative parameter (`hμ : 0 ≤ μ`), entering only through the hypotheses
  `h566`/`hsym` (both stated with a literal `μ` in the same two places).
- `RBM.Lemma57.ee_le_paper` (:1874–1948) **is** proved from `ee_le` (confirmed): its proof
  (lines 1912–1948) calls `ee_le` with
  `μ := ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹)`,
  rewrites `(W * ℓu * ηu) * μ = ℓu/ℓs * √(ℓu/ℓs) * (√(W*ℓu*ηu))⁻¹` (`hAμ`, by `field_simp`,
  using `hℓs : 0 < ℓs`, `hA0 : 0 < W*ℓu*ηu`, `hsA : 0 < √(W*ℓu*ηu)` — all available from
  `ee_le_paper`'s hypotheses `hW hℓu hℓs hηu hA`), and only **then** merges
  `cFar2 * (J^2 * ν) + 72*J^3*(Wℓuηu)⁻¹ ≤ (cFar2+72)*ν*J^3` using `J^2 ≤ J^3` (from `hJ`) and
  `(Wℓuηu)⁻¹ ≤ ν` (from `hr`, `hA`, monotonicity of `Real.sqrt` and of `x ↦ x⁻¹`).
- So `ee_le_paper`'s hypotheses do imply `ee_le`'s hypotheses for this `μ`: the gap the ticket
  asks to check does not occur. Ticket (T1)'s stated route ("`ee_le` with this `μ`, then the
  identity") is exactly the first half of `ee_le_paper`'s existing proof, stopped **before**
  the merge step. Ticket (T2) is exactly that merge step, stated as a standalone comparison of
  the two right-hand sides (not routed through `EE`/`Gsq`/`L6`).
- Consequence for the new file: no new hypothesis, no new nonlinear fact is needed anywhere;
  every inequality used (`Real.one_le_sqrt`, `Real.sq_sqrt`, `inv_anti₀`, `pow_le_pow_right₀`,
  `mul_le_mul_of_nonneg_left/right`) is already used, in the same role, inside the already
  ‑committed `ee_le_paper` proof.

## 1. Math preflight

### Target (T1) `RBM.Lemma57.ee_le_reduced`

- **Statement vs paper/route.** Hypotheses: copied verbatim, same names and order, from
  `ee_le_paper` (:1874–1892): `hW hℓu hℓs hηu hJ hA hr a₁ a₂ {Gsq L6 ρ EE} hρ hL6 hGsq h273 h564
  h42sq h566 h572 hsym hEE`. Conclusion: `ee_le`'s conclusion with `μ` instantiated to the same
  `ν := ℓu/ℓs * √(ℓu/ℓs) * ((√(Wℓuηu))⁻¹*(Wℓuηu)⁻¹)` as `ee_le_paper` uses, and the identity
  `(Wℓuηu)*μ = ℓu/ℓs*√(ℓu/ℓs)*(√(Wℓuηu))⁻¹` applied — i.e. `ee_le`'s two far-field summands
  `cFar2*(J²*(Aμ))` and `72*J³*A⁻¹` rewritten as `cFar2*(ℓu/ℓs*√(ℓu/ℓs)*(√(Wℓuηu))⁻¹)*J²` and
  `72*J³*A⁻¹`, kept **apart** (no merge). This is exactly (5.71)+(5.72) as displayed by
  `ee_far_le` (:1793–1794) after substituting `A*μ = ν` — i.e. the proof-exponent shape the
  ticket asks for, and it is strictly sharper than `ee_le_paper`'s merged bracket (verified as
  (T2) below).
- **Hypotheses.** Identical to `ee_le_paper`'s, already accepted; no new hypothesis is added
  (satisfies acceptance criterion 3 verbatim).
- **Quantifier order.** Unchanged from `ee_le_paper`: `L` outer (section variable), then
  `W ℓu ℓs ηu D J` (section-implicit reals), then the explicit numeric hypotheses, then
  `a₁ a₂ : ZMod L`, then the implicit functions/reals `Gsq L6 ρ EE`, then the ∀-inside-hypothesis
  quantifiers over `b`/`x y`. Same order as `ee_le_paper`, hence the same order as the paper's
  own (5.36) (fixed parameters `W, ℓ_u, ℓ_s, η_u, J*, A_u` before the per-pair statement).
- **Dependencies.** `RBM.Lemma57.ee_le` — already committed, used only as a black box via
  `hmain := ee_le L hW hℓu hℓs hηu hJ a₁ a₂ hμ hρ hL6 hGsq h273 h564 h42sq h566 h572 hsym hEE`.
  No other dependency.
- **Boundary cases.** `ηu⁻¹`, `(Wℓuηu)⁻¹`, `(√(Wℓuηu))⁻¹`, `ℓu/ℓs` are all well-defined and
  finite because `hηu : 0 < ηu`, `hA : 1 ≤ Wℓuηu` (so `Wℓuηu > 0`, `√(Wℓuηu) > 0`), `hℓs : 0 <
  ℓs`. The `if … then 1 else 0` indicator is decidable on `ℝ` via `Classical`/`LinearOrder`,
  already used unchanged from `ee_le`. No division by zero, no `N = 0`/empty-index-set case:
  `L` is any `ℕ` with `[NeZero L]` (inherited section hypothesis, unconstrained by this ticket),
  `a₁ a₂ : ZMod L` arbitrary (no forced distinctness).
- **Simultaneous satisfiability.** Inherited unchanged from `ee_le_paper`, which the repository
  already treats as accepted (T1488 audit D4, dependency of downstream EESym files that are
  committed and build). No new hypothesis is introduced, so no new satisfiability question
  arises. (Sanity witness, not required to re-derive: `W=ℓu=ℓs=ηu=J=1`, `D` arbitrary, `L=1`,
  `Gsq ≡ L6 ≡ 0`, `ρ = EE = 0` discharges every hypothesis of `ee_le_paper` non-vacuously.)
- **Verdict: PASS.**

### Target (T2) `RBM.Lemma57.ee_le_paper_of_reduced`

- **Statement vs paper/route.** A pointwise comparison, independent of `EE`/`Gsq`/`L6`, of the
  two right-hand sides: `ee_le_paper`'s RHS ≥ `ee_le_reduced`'s RHS, under `hW hℓu hℓs hηu hJ hA
  hr` (the same positivity/normalization hypotheses `ee_le_paper` needs to run its own merge
  step — `hJ` for `J² ≤ J³`, `hA`/`hr` for `(Wℓuηu)⁻¹ ≤ ν`), plus the shared real parameter `ρ`
  (only needed because it is textually present in both sides' identical remainder term
  `W*L*ρ + 2*W*L*W^(-D)*J³*tailT…²`, and cancels). This is precisely the algebraic content of
  `ee_le_paper`'s own proof lines 1934–1948 (`hJ23`, `hbr`, `hbr'`, `hstep`), extracted as a
  standalone lemma — the "sanity check that (T1) is the sharper statement" the ticket asks for.
- **Hypotheses.** `hW hℓu hℓs hηu hJ hA hr`: a subset of `ee_le_paper`'s hypotheses (no `EE`,
  `Gsq`, `L6`, `ρ`-nonnegativity needed: `ρ` is universally quantified and cancels identically,
  so no `hρ` hypothesis is required or added). No new hypothesis beyond what `ee_le_paper`
  already assumes.
- **Quantifier order.** `L` outer, then `W ℓu ℓs ηu D J` implicit, then the seven numeric
  hypotheses in the same left-to-right order as `ee_le_paper`, then `a₁ a₂ : ZMod L`, then `ρ :
  ℝ`. No `∀ᶠ N` / asymptotic parameter is involved (this is finite algebra on real numbers, not
  a stochastic-domination statement), so there is no ordering-with-`N` issue.
- **Boundary cases.** Same as (T1): `ηu > 0`, `Wℓuηu ≥ 1 > 0` so `√(Wℓuηu) > 0`, `ℓs > 0`.
  `J ≥ 1 ≥ 0` so `J² ≤ J³` (`pow_le_pow_right₀`). `ℓu/ℓs ≥ 1` and `√(ℓu/ℓs) ≥ 1` (`Real.
  one_le_sqrt`) give `ℓu/ℓs·√(ℓu/ℓs) ≥ 1`; combined with `√(Wℓuηu) ≤ Wℓuηu` (from `Wℓuηu ≥ 1`)
  this gives `(Wℓuηu)⁻¹ ≤ ν`. No degenerate/empty case.
- **Simultaneous satisfiability.** `W = ℓu = ℓs = ηu = J = 1`, `D`, `a₁ a₂`, `ρ` arbitrary
  discharges every hypothesis non-vacuously (all seven inequalities become `1 ≤ 1`/`0 < 1`).
- **Verdict: PASS.**

## 2. Proof (after PASS)

New file `RBM1D/Hierarchy/Lemma57Reduced.lean`, `import RBM1D.Hierarchy.Lemma57`, namespace
`RBM.Lemma57`, section variables `(L : ℕ) [NeZero L]` and `{W ℓu ℓs ηu D J : ℝ}` (identical to
the `EE` section of `Lemma57.lean`).

- `ee_le_reduced`: `have hmain := ee_le L hW hℓu hℓs hηu hJ a₁ a₂ hμ hρ hL6 hGsq h273 h564 h42sq
  h566 h572 hsym hEE` with `hμ` the positivity of `ν`, then `refine hmain.trans (le_of_eq ?_)`,
  the identity `hAμ` (verbatim from `ee_le_paper`'s proof, closed by `field_simp`), `rw [hAμ]`,
  `ring` (pure commutativity of the already-rewritten term; `ring` treats `√(·)`, `tailT …`,
  `(·)^(-D)` etc. as atoms, which is all that's needed here).
- `ee_le_paper_of_reduced`: the `hJ23`/`hone`/`hinvA`/`hbr` chain copied from `ee_le_paper`'s
  proof (lines 1908–1941), assembled with `set`, `mul_le_mul_of_nonneg_left/right`,
  `Real.one_le_sqrt`, `Real.sq_sqrt`, `inv_anti₀`, `pow_le_pow_right₀`, finished by `linarith`
  (which ring-normalizes the atoms `cFar2 W ℓu`, `ν`, `J^2`, `J^3`, `(Wℓuηu)⁻¹` consistently, as
  it already does inside `ee_le_paper`'s own proof).

## 3. Build

```
lake build RBM1D.Hierarchy.Lemma57Reduced
```

Result: **succeeded** — `Build completed successfully (2956 jobs)`, ending with
`Built RBM1D.Hierarchy.Lemma57Reduced`. Only pre-existing style-linter warnings (long lines in
`Lemma57.lean`, unused-variable/section-var hints in the new file) appear; no error. `grep -n
"sorry\|admit\|^axiom\| axiom "` on the new file returns nothing. Commit `e8ec942` on branch
`t/T1491` (main worktree unaffected; only `RBM1D/Hierarchy/Lemma57Reduced.lean` staged/committed
in the ticket's worktree).

## 4. Axioms

```
#print axioms RBM.Lemma57.ee_le_reduced
#print axioms RBM.Lemma57.ee_le_paper_of_reduced
```

Both print only `propext`, `Classical.choice`, `Quot.sound`.

## 5. Key lemmas used

`RBM.Lemma57.ee_le` (master, unmerged), `RBM.Lemma57.cFar2_nonneg`, `RBM.Lemma57.tailT_nonneg`,
`Real.sqrt_pos`, `Real.one_le_sqrt`, `Real.sq_sqrt`, `Real.sqrt_nonneg`, `inv_anti₀`,
`pow_le_pow_right₀`, `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`, `field_simp`,
`ring`, `linarith`, `positivity`.

## 6. Open issues

None. No paper-delta candidate: this ticket only re-derives, in Lean, the two exponent shapes
that pilot §9 (B) already flags as the correct ones (the proof's (5.71)/(5.72) exponents, not
the displayed (5.35)/(5.36) ones); that delta is already recorded (candidate (ii) of pilot §9,
`docs/paper-deltas.md`) and this ticket adds no new one.
