Prover model: claude-sonnet-5[1m]

# T1496: absorbing the `≺` loss into the reduced (5.35) shape (inventory target M3)

2026-09-25T19:41Z.

## (a) Math preflight

Sources read: `CLAUDE.md` §3; `docs/reports/T1488-prove.md` §2 (row (5.35)/B2), §3 (target M3)
and "Open issues" #2; `RBM1D/Hierarchy/Step2FarInputs.lean` (definitions of `rhs535`, `mGF`,
`mGN`, `mgfBeta`, `mgfGamma`, and the statements of `eGpm_le_rhs535`, `eGpm_le_rhs535_of_jS`,
`h535_of_jS`); `RBM1D/Analysis/StretchedExp.lean` (`tailT`, `ellStar`, `tailT_nonneg`);
`RBM1D/Hierarchy/Lemma57.lean` (`cNear`, `cFar`, `cNear_nonneg`, `cFar_nonneg`).

### Step 0 (read-only checks)

- `RBM.Step2FarInputs.rhs535 Wr Lr ℓu ℓs ηu D J ρ d` (Step2FarInputs.lean:994) is
  ```
  ηu⁻¹ * (cNear Wr ℓu * (ℓu/ℓs)^3 * (if d ≤ ellStar Wr ℓu then 1 else 0)
        + cFar Wr ℓu * (ℓu/ℓs * √(ℓu/ℓs) * (√(Wr*ℓu*ηu))⁻¹ * J)
        + 169 * (ℓu/ℓs * (Wr*ℓu*ηu)⁻¹ * (J*√J))) * tailT Wr ℓu ηu D d
    + ℓu/ℓs * (ℓu*ηu)⁻¹ * Lr * ρ
  ```
  `ℓs` occurs only through `r := ℓu/ℓs`, four literal copies of the same subterm; there is no
  other occurrence of `ℓs`. Confirmed against the definition.
- Degree of `rhs535` in `r`: the near-field term `cNear · r³ · 1(near)` has degree `3`; the
  far-field terms have degree `3/2` (`cFar·r·√r·A^{-1/2}·J`) and `1`
  (`169·r·A⁻¹·J^{3/2}`, and the additive `r·(ℓuηu)⁻¹·Lr·ρ` residue); `A = Wℓuηu` does not
  depend on `ℓs`. Maximum degree is `3`. The ticket's `c³` is therefore the *sharp* (not an
  under- or over-estimate of the) power needed: for `c ≥ 1`, `c^{3/2} ≤ c³` and `c ≤ c³`, so a
  single factor `c³` dominates every term, and no smaller power works uniformly (it must match
  the degree-3 term with equality when the indicator is `1`).
- `RBM.Step2FarInputs.eGpm_le_rhs535_of_jS` (Step2FarInputs.lean:2224) has `ℓs` as a free
  explicit-implicit real parameter with hypotheses `hℓs : 0 < ℓs` and `hr : 1 ≤ B.ell N u / ℓs`
  only (lines 2226–2227); no other constraint on `ℓs`. Confirmed against the statement, exactly
  as the ticket's Step 0 anticipates.
- `h560` **is** among the hypotheses of `eGpm_le_rhs535_of_jS` (Step2FarInputs.lean:2248–2250):
  ```
  (h560 : ∀ b, ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      ⟨[false, true, true], [a₂, b, a₁]⟩‖
    ≤ gmOfJS X E D' N u ω a₂ b * gmOfJS X E D' N u ω a₁ b * gmOfJS X E D' N u ω a₂ a₁)
  ```
  and likewise in `h535_of_jS` (:2298–2301, universally quantified over `u`, `b`, `c`). `h560`
  does **not** mention `ℓs` in any form — its two sides are built only from `gloop` and
  `gmOfJS` (which depends on `X`, `E`, `D'`, `N`, `u`, `ω`, points, not on `ℓs`). Hence the
  `ℓs → ℓs/c` rescaling of T1 neither creates nor removes the difficulty `docs/reports/
  T1488-prove.md` "Open issues" #2 flags: `h560` would have to hold verbatim, unchanged, to run
  T2. Per the ticket's Step 0 instruction, this blocks (T2); (T1) proceeds since it is a
  standalone fact about `rhs535` and does not touch `eGpm_le_rhs535_of_jS` at all.

### Verdict, target by target

**(T1) `RBM.rhs535_div_le` — PASS.**
Statement checked against the paper route: this is a pure scaling lemma about the Lean
constant `rhs535` (the RHS of the (2.73)-reduced (5.35), `RBM.EGDef.eGpm_le_reduced`'s
conclusion read through `rhs535`), not a new paper citation; the paper content it serves
(absorbing an `N^τ` loss from Step 1 into the `ℓ_s` slot) is exactly `docs/reports/
T1488-prove.md` §3 M3.
- Hypotheses: `1 ≤ c`, `1 ≤ Wr`, `0 < ℓu`, `0 < ℓs`, `0 < ηu`, `0 ≤ J`, `0 ≤ ρ`, `0 ≤ Lr`,
  `0 ≤ d`. These are exactly "the nonnegativity hypotheses `rhs535` needs" (matching the
  hypothesis lists of the already-committed `rhs535_far_le`/`rhs535_le_const` in the same
  file, plus `0 < ℓs` in place of the weaker `0 ≤ ℓu/ℓs` since T1 needs `ℓs` itself, not just
  the ratio, to form `ℓs/c`).
- Quantifier order: `∀ Wr Lr ℓu ℓs ηu D J ρ d c` (all fixed reals), matching the paper's
  parameter order (no `N` here; `rhs535` is a real-valued arithmetic function, not indexed by
  `N`).
- Dependency: only `RBM.Step2FarInputs.rhs535`'s definition and `RBM.Lemma57.cNear_nonneg`/
  `cFar_nonneg`/`RBM.tailT_nonneg` (already-committed, `main`).
- Boundary case `c = 1`: both sides equal `rhs535 Wr Lr ℓu ℓs ηu D J ρ d` up to the (true)
  inequality `≤ 1³·(...)`; not vacuous, holds with room since `c^{3/2}, c ≤ c³` are equalities
  only at `c = 1`.
- Simultaneous satisfiability: compiled witness below (§ (b)), non-degenerate (no zero
  arguments, no astronomically large values): `Wr=5, Lr=3, ℓu=2, ℓs=1, ηu=1/2, D=4, J=7, ρ=6,
  d=1, c=3`.

**(T2) `RBM.eGpm_le_rhs535_of_jS_scaled` — BLOCKED, not written.**
Per Step 0: `h560` is a hypothesis of `RBM.Step2FarInputs.eGpm_le_rhs535_of_jS`, and it is
unaffected by the `ℓs`-rescaling (it does not mention `ℓs`). `docs/reports/T1488-prove.md`
"Open issues" #2 gives a precise, uncompiled heuristic that `h560` is generically **false**:
at `b = a₁`, `h560`'s right side is `jS^{3/2}·T(|a₁-a₂|)·(A⁻² + W^{-D})^{1/2}`
(since `gmOfJS X E D' N u ω a₂ a₁ = √(jS·tailT(|a₂-a₁|))`, `gmOfJS X E D' N u ω a₁ a₁` is
`√(jS·tailT(0))`, and `tailT(0) = A⁻² + W^{-D}`), while the left side is `‖m‖·|L_{(−,+),(a₂,
a₁,a₁)}|`-type data whose typical size is `≈ jS·T(|a₁-a₂|)` (one power of `jS` too many
relative to the right side's `jS^{3/2}·(\text{small})^{1/2}` once `jS < A²`). I did not attempt
to compile a counterexample or a proof of `h560` myself; the ticket's Step 0 explicitly directs
"report ... rather than working around it", and this is a judgement about the *statistics of
the Gaussian model* (whether `h560` holds with high probability for a specific choice of
`gmOfJS`), not an arithmetic fact about `rhs535` in the scope of this "arithmetic" ticket. The
only new information this ticket adds to T1488's open issue is: the `ℓs`-rescaling route does
not sidestep it, so (T2) cannot be discharged by T1 alone. Per the ticket's acceptance
criteria, this satisfies "a precise `h560` report as described in Step 0" and (T2) is
correctly omitted.

## (b) Declarations added, build, axioms

Sole writable file: `RBM1D/Hierarchy/Rhs535Scale.lean` (new module).

- `RBM.rhs535_div_le {Wr Lr ℓu ℓs ηu D J ρ d c : ℝ} (hc : 1 ≤ c) (hW : 1 ≤ Wr) (hℓu : 0 < ℓu)
  (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ0 : 0 ≤ J) (hρ0 : 0 ≤ ρ) (hLr0 : 0 ≤ Lr) (_hd0 : 0 ≤ d) :
  Step2FarInputs.rhs535 Wr Lr ℓu (ℓs / c) ηu D J ρ d ≤ c ^ 3 * Step2FarInputs.rhs535 Wr Lr ℓu
  ℓs ηu D J ρ d` (T1, as requested).

Build:
```
$ lake build RBM1D.Hierarchy.Rhs535Scale
✔ [3770/3770] Built RBM1D.Hierarchy.Rhs535Scale
Build completed successfully (3770 jobs).
```
No `sorry`/`admit`/`axiom`, no warnings in the new file (one earlier unused-hypothesis lint on
`hd0` was silenced by renaming it `_hd0`; `d`'s nonnegativity is part of "the nonnegativity
hypotheses `rhs535` needs" per the ticket, even though this particular proof happens not to
need it — `ellStar Wr ℓu` and `tailT`'s nonnegativity do not require `0 ≤ d`).

Axioms (`lake env lean` on a scratch file `import RBM1D.Hierarchy.Rhs535Scale`):
```
'RBM.rhs535_div_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Satisfiability witness (compiled, `lake env lean`, rc 0):
```
example : True := by
  have h := @RBM.rhs535_div_le 5 3 2 1 (1/2 : ℝ) 4 7 6 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  trivial
```

## (c) Key lemmas used

`RBM.Step2FarInputs.rhs535` (def), `RBM.Lemma57.cNear_nonneg`, `RBM.Lemma57.cFar_nonneg`,
`RBM.tailT_nonneg`, `Real.sqrt_le_left`, `Real.sqrt_mul`, `mul_le_mul_of_nonneg_left/right`,
`add_le_add`, `LE.le.trans_eq`.

Proof shape: write `r := ℓu/ℓs`; the substitution `ℓs → ℓs/c` turns every occurrence of `r`
inside `rhs535` into `c*r` (since `ℓu/(ℓs/c) = c*(ℓu/ℓs)` for `c, ℓs ≠ 0`); the near-field term
scales by exactly `c³` (equality, via `ring`); the `β`-term (`cFar` piece) scales by `c·√c` via
`√(c*r) = √c*√r`; the `γ`-term (169 piece) and the (5.54) tail-remainder term each scale by
`c`. Since `c ≥ 1` gives `c ≤ c² ≤ c³` and `√c ≤ c` (hence `c·√c ≤ c·c ≤ c³`), each scaled term
is `≤ c³` times the corresponding original term, termwise, using only nonnegativity of the
individual factors (`cNear, cFar ≥ 0`, `r, J, A⁻¹, √r, √J, (√A)⁻¹, ℓu, ηu, Lr, ρ ≥ 0`,
`tailT ≥ 0`, `ηu⁻¹ ≥ 0`). Summing termwise inequalities and multiplying through by the (also
nonnegative) `ηu⁻¹ · tailT` factor, then adding the residue-term bound, gives the stated
inequality; the final step is a `ring` identity distributing `c³` back over the sum.

## (d) Open issues

1. (T2) `eGpm_le_rhs535_of_jS_scaled` remains unproved, blocked on `h560`'s satisfiability
   exactly as `docs/reports/T1488-prove.md` "Open issues" #2 already flagged (`T1488a`/`b` are
   the paper-delta candidates from that report; this ticket adds no new paper-delta, only
   confirms the same obstruction survives the `ℓs`-rescaling unchanged). Whoever resolves M3's
   downstream use (feeding M4, per the ticket's "Upstream / downstream" line) must either
   (i) find a genuine bound on `h560` (likely requires abandoning `gmOfJS := √(jS·tailT)` in
   favor of the APrime route's `gmBlk`/`jG`, which `docs/reports/T1488-prove.md` row A3 already
   notes "avoids the issue"), or (ii) restate M4 directly off `eGpm_le_rhs535` with the APrime
   `κ₁, κ₂` (as M4 in T1488 already does) rather than through `eGpm_le_rhs535_of_jS`/`h535_of_jS`.
2. `rhs535_div_le`'s hypothesis `0 < ℓs` (rather than the weaker `0 ≤ ℓu/ℓs` used by
   `eGpm_le_rhs535_of_jS`'s own `hr`) is required because T1 must form `ℓs/c` itself; this is a
   strictly stronger requirement than `eGpm_le_rhs535_of_jS`'s `hℓs : 0 < ℓs`, so it composes
   with it without weakening anything downstream.
