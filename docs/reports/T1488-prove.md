Prover model: claude-opus-5-5[1m]

# T1488: read-only inventory of the inputs of the discrete Step 2 (σ = (+,−))

Revision 3 (2026-09-25T18:13Z). Revision 2 (2026-09-25T17:46Z) answered the first RETURN (D1–D6). Revision 3 answers the re-audit in `docs/reports/T1488-audit.md`, which found two remaining defects: D7 (row A3) and D8 (target M7). Nothing else was changed. The ticket is report-only: no Lean was written, no worktree was used, and no module was built.

## 0. Method and verification

- Sources read: `CLAUDE.md` §3; `docs/claude-team/pilot-P4P5-paper.md` §1–§9; the audit report; the paper `paper/250520-YinJun-v2.pdf` pp. 48, 56–63, text extracted with `pypdf` to check (4.1)–(4.3), (5.33)–(5.36), (5.53)–(5.61); and the statements (not the proofs) of the Lean files cited below.
- Every declaration cited in this revision was `#check`-ed with `lake env lean` in the main worktree, using scratch files outside the repository that import the cited modules. There were 54 + 5 + 1 new checks. All returned rc 0, with no error, no `sorry` and no unknown identifier. The audit had already checked the 34 citations of revision 1.
- Revision 3: each declaration newly cited for D7/D8 was located with `grep -n` and `#check`-ed under `import RBM1D`. That is 18 declarations: the four named in D7, `stochDom_ldeRow_flow`/`_ldeCol_flow`, `tailT_sub_le`, `tailT_antitone`, `ellStar`, `ee_le_EEpath_sym`, `EEpath`, `Gauss.eeTens`, `Gauss.eeEdge`, `eeArg_append`, `zdist_add_le`, `Step3.ellHat_mono` and `Step2FarMart.ellStar_mono_time`. The one unknown-identifier error was my own mistyped namespace (`EEBridge.eeTens`); the name is `RBM.Gauss.eeTens`, and it then checked cleanly. The statements quoted in row A3 and in M7 are copied from the `#check` output.
- File:line gives the line of the `theorem` / `def` / `structure` keyword on the current `main`. Every cited file is tracked and unmodified in git, and every cited module is in the committed root import closure.
- Column convention in both tables:
  - "Det / SD": the statement is either per-sample deterministic (a fixed matrix or ω, no probability) or a `StochDom` / `HighProb` statement.
  - "Unif. u": the statement holds jointly for all `u ∈ [s,t]` (index `TimeIcc s t N`, or `∀ u ∈ Set.Ico (s N) (t N)` inside one event).
  - "Dims": the statement is either stated for an abstract `Band` / `Sample` or Hermitian `M` (then it holds for every `Gauss.Dims` once its hypotheses are discharged), or stated for `Gauss.sample d` with arbitrary `d : Dims`, or only for `Dims.exampleGrow`.
- Scope caveat (CLAUDE.md §3.5): every `Gauss` statement below is about the flow `Hflow d N u ω` (= `√u·X`). The discrete route of the pilot uses these statements only through single-time laws at each grid time (pilot §5). Each event used is a function of `H_u` alone, so the transfer is legitimate, but it needs P1's transfer lemma once per event. That transfer lemma is not part of this inventory.

## (a) Preflight verdict

The ticket has no Lean target. Target of the ticket: a complete inventory with precise missing statements.

**PASS.** Both tables are complete. Every "missing" cell refers to a target M1–M7 in §3, and each target is stated in Lean shape (quantifiers, event, index ranges, exponents) with a ticket estimate.

What the audit asked for, and where it is answered:

| Audit | Where fixed |
|---|---|
| D1 | Table A rows A1, A2: `apriori`/`weakLaw` hold for **every** `d : Gauss.Dims` via `step1Hyp_gauss_of_scale''`; (4.2) row cites `entryBoundFlow_floor`/`diagBoundFlow_floor` |
| D2 | Row A3: `entry_bound_stochDom`'s real form (arbitrary Hermitian family `H`, hypotheses `hLrow`/`hLcol`) and where the floored versions are discharged |
| D3 | Row A3 + target M2: (5.57) at full strength, as a statement with its sources |
| D4 | Row B3: `ee_le_paper` merges the far bracket; the proof-level form lives in `ee_le`/`ee_le_sym`/`ee_le_EEpath_sym`; target M5 |
| D5 | Rows B2, B3 + targets M4, M6, M7; `eGpm_le_reduced`, `F_eq_eGpm_add_quadGlue`, `eeL6`, `norm_eeFun_le_W_sum` and the further existing wiring (Step2FarInputs, APrime*) are listed |
| D6 | Table B now has the columns "Det / SD", "Unif. u", "Dims" per row |
| D7 (rev. 3) | Row A3: the fixed-time unfloored (4.2)/(4.3) **are** discharged for the Gaussian flow, for every `d`, by `entry_bound_gauss`/`diag_bound_gauss` (inputs `stochDom_ldeRow`/`_ldeCol`). Only the time-uniform unfloored form remains conditional, on `LDENetClose` |
| D8 (rev. 3) | Target M7 restated in Lean terms. It has an explicit loss factor `exp(√(2C)·(log W)^{3/4})` coming from `tailT_sub_le`, a displacement parameter `C`, and a separate hypothesis-free Cauchy–Schwarz sub-lemma M7a |

Revision 1 also contained errors the audit did not list. They are corrected here:
- (i) `hsym` is **not** open. `Lemma57.ee_le_sym` / `ee_le_paper_sym` and `EEDef.ee_le_EEpath_sym` remove it (T190).
- (ii) Revision 1 said the wiring from Step 1 to per-ω Lemma 5.7 inputs was "not yet written". Much of it exists (`Step2FarInputs`, `EarlyQVRateEv`, `APrimeJG`, `APrimeFullQV`, `APrimeGeneralMovingDriftSourceGeneralDims`), and it is listed below.

## 1. Table A: inputs of the stopping time σ

**Row A1: (2.73), loops of length ≤ 6 (used in (5.64)); also n = 2, 3, 4 for (5.53), (5.57), (5.66).**
- Lean:
  - `RBM.Step1.apriori`, Hierarchy/Step1.lean:812: `∀ n ≥ 1, StochDom` of `‖L_{u,σ,a}‖` over `TimeIcc s t N × LoopData (L N) n`, with right side `(ℓ_u/ℓ_s)^{n-1}(Wℓ_uη_u)^{-(n-1)}`. It is conditional on `h : Step1.Hyp X E s t`.
  - Gaussian discharge of `Step1.Hyp`: `RBM.Gauss.step1Hyp_gauss_of_scale''`, Gauss/EntryBoundTime.lean:654. It holds for **every `d : Dims`**. Its hypotheses are exactly those of `apriori` minus `h`: `0<κ`, `|E| ≤ 2-κ`, `BoundsCore (sample d) E s`, `0 ≤ s`, `s ≤ t`, `t < 1`, `Cond272`, `0<c`, and `N^c ≤ Wℓ_tη_t`. Its field `lemma41` is supplied by `lemma41Flow_gauss` (:635), which is built from `entryBoundFlow_floor` (:155) and `diagBoundFlow_floor` (:535).
  - Older discharges keep extra hypotheses:
    - `step1Hyp_gauss_of_scale'` (:448) still assumes `DiagBoundFlow`.
    - `RBM.Gauss.step1Hyp_gauss_of_scale` (Gauss/Step1Hyp.lean:1196) assumes the unfloored `EntryBoundFlow` and `DiagBoundFlow`. The EntryBoundTime docstring records T148's finding that the unfloored time-uniform form is not what the large-deviation estimates give.
- Det / SD: SD.
- Unif. u: yes (index `TimeIcc`).
- Dims: abstract `Sample`; **for every `d : Gauss.Dims`** through `step1Hyp_gauss_of_scale''`, not only `exampleGrow`. The remaining input `BoundsCore (sample d) E s` is (2.68)–(2.70) at time `s`, i.e. the hypothesis of Theorem 2.21 (the induction input), exactly as in the paper.
- Exponents: literal (2.73).
- Missing: none.

**Row A2: (2.74) weak law.**
- Lean:
  - `RBM.Step1.weakLaw`, Step1.lean:791: `‖G_u − m‖_max ≺ (Wℓ_uη_u)^{-1/4}`.
  - Also the event (4.1) along the flow: `RBM.APrimeGeneralMovingGoodSetFlowActual.highProb_goodSetFlow` (Gauss/APrimeGeneralMovingGoodSetFlowActual.lean:105), i.e. `HighProb (goodSetFlow d E s t (flowDelta d E t))` with `flowDelta = (Wℓ_tη_t)^{-1/6}` (`RBM.Gauss.flowDelta`, Gauss/APrimeGeneralMovingCarrierCore.lean:63).
- Det / SD: SD.
- Unif. u: yes.
- Dims: every `d : Gauss.Dims`, by the same discharge `step1Hyp_gauss_of_scale''`.
- Exponents: literal (2.74).
- Missing: none.

**Row A3: (4.2)/(4.3), the resolvent-entry bounds, as used in (5.57), (5.61), (5.69)–(5.70).**
- Lean, fixed time:
  - `RBM.entry_bound_stochDom`, Green/EntryBound.lean:1512.
    - Stated for an **arbitrary Hermitian family** `H : ∀ N, Ω → Matrix (ZMod (L N) × Fin (W N)) …`, at one `z` with `z.im ≠ 0`, with `‖m‖ = 1` and a threshold `δ_N ≤ N^{-c₀}`.
    - It is conditional on two `StochDom` large-deviation hypotheses ([39, Lemma 3.3]) over off-diagonal pairs: `hLrow` (`ldeRowLHS ≺ ldeRowRHS`) and `hLcol` (`ldeColLHS ≺ ldeColRHS`).
    - Conclusion: `1_{goodSet}|G_{ij}|² ≺ Σ_{a,b∈sbSupport} Lre(j+b, i+a) + W^{-1}·1(|[i]−[j]| ≤ 1)`.
  - `RBM.diag_bound_stochDom` (:1566), i.e. (4.3), additionally takes `hLquad` and `hLdiag`.
- Where these hypotheses are discharged for the Gaussian model:
  - **Fixed time, unfloored: discharged, for every `d : Dims`.**
    - `RBM.Gauss.stochDom_ldeRow` and `RBM.Gauss.stochDom_ldeCol` (Gauss/LDEHyp.lean:221/246, from T91) prove exactly `hLrow`/`hLcol` for `H N ω := Hflow d N u ω`. The hypotheses are only `0 ≤ u`, `u ≤ 1` and `z.im ≠ 0`, for every `d`.
    - `RBM.Gauss.entry_bound_gauss` (Gauss/EntryBoundGauss.lean:42, from T97) is (4.2) for the Gaussian flow, with **no** large-deviation hypothesis. Its hypotheses are `0 ≤ u ≤ 1`, `z.im ≠ 0`, `‖m‖ = 1`, `0 ≤ δ_N` and `δ_N ≤ N^{-c₀}` eventually. It is `entry_bound_stochDom` applied to `stochDom_ldeRow`/`_ldeCol`.
    - `RBM.Gauss.diag_bound_gauss` (:61) is (4.3) at `z = zt E t` and `m = mE E`. Its hypotheses are `0 < κ ≤ 1`, `|E| ≤ 2−κ`, `0 ≤ t < 1` and the same `δ` conditions. It also uses `stochDom_ldeQuad` and `stochDom_normSq_Hflow_diag`.
    - The module is in the root imports (RBM1D.lean:144).
    - Scope: the time `u` (resp. `t`) is a single real constant, independent of `N`. These statements therefore do not directly cover an `N`-dependent grid time or a family of times. For grid use or time-uniform use, the floored flow forms below remain the right source.
  - **Time-uniform, unfloored: conditional.** `RBM.Gauss.stochDom_ldeRow_flow`/`stochDom_ldeCol_flow` (Gauss/LDEFlow.lean:421/442), indexed by `TimeIcc s t N × OffPair`, still assume `hclose : LDENetClose d E s t Ξ δ`, together with `HighProb Ξ`. Only this form is undischarged.
  - **Time-uniform, floored: discharged.** The floored, time-indexed versions are discharged: `RBM.entry_bound_stochDom_floor_idx` / `diag_bound_stochDom_floor_idx` (Green/EntryBoundFloor.lean:730/806) take the floored inputs `RBM.Gauss.stochDom_ldeRow_flow_floor`, `stochDom_ldeCol_flow_floor`, `stochDom_ldeQuad_flow_floor` (Gauss/LDENetClose.lean:747/827/1601). The results are `RBM.Gauss.entryBoundFlow_floor` (EntryBoundTime.lean:155) and `diagBoundFlow_floor` (:535). These are (4.2)/(4.3) along the flow with an additive floor `2N^{-B}` (resp. `N^{-B}`) for any `B ≥ 0`, and **no** large-deviation hypothesis.
- Per-ω consumers in blockwise form:
  - `RBM.APrimeJG.gmBlk`/`gsqBlk`/`jG` (definitions, Gauss/APrimeGeneralMovingCarrierCore.lean:138/145/153).
  - `RBM.APrimeJG.gsqBlk_le_jG_mul_tailT` (Gauss/APrimeJG.lean:98): `h42sq`/(5.61)/(5.69)–(5.70) with `J := jG`, deterministic.
  - `RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow` (APrimeJG.lean:569): `HighProb {ω | ∀ u ∈ TimeIcc, jG ≤ 1 + N^τ(9e^{√3}·jS + 2)}` for every `d : Dims`. This links the blockwise J to the paper's `J*_{u,D}` = `Step2.jS`.
- Det / SD: SD for (4.2)/(4.3) and for the jG link; the per-ω consequences (`gsqBlk_le_jG_mul_tailT`) are Det.
- Unif. u: fixed-time forms (`entry_bound_stochDom`, `diag_bound_stochDom`, `entry_bound_gauss`, `diag_bound_gauss`): no, since the time is one real constant independent of `N`. `*_floor_idx`, `entryBoundFlow_floor` and `highProb_jG_le…`: yes.
- Dims: `entry_bound_stochDom`/`diag_bound_stochDom` are stated for an abstract Hermitian `H`. Their Gaussian fixed-time instances `entry_bound_gauss`/`diag_bound_gauss` hold for every `d : Dims`, as do the floored flow forms and the jG link.
- Exponents: (4.2)/(4.3) literal, up to the floor. The floor `2N^{-B}` is harmless: take `B ≥ D` and it is `≤ W^{-D}` because `W ≤ N`.
- Missing: **(5.57) at full strength** (target M2). Only the weak form `κ₂ = flowDelta + W^{-1} = (Wℓ_tη_t)^{-1/6} + W^{-1}` exists per-ω, in `pointwise_source_package` (row B2). The paper's `W^{-1}max_y Σ_x|G_xy| ≺ (Wℓ_uη_u)^{-1/2}(1+J*(Wℓ_uη_u)^{-1})` does not. Nor does the (2.73)-reduced form `≤ N^τ(ℓ_u/ℓ_s)^{1/2}(Wℓ_uη_u)^{-1/2}` that `eG_le_reduced`/`eGpm_le_reduced` take as `h557C`/`h557R`.

**Row A4: Lemma 5.6, (5.30)–(5.32), deterministic.**
- Lean:
  - (5.30): `RBM.Step2.norm_Theta_le_of_ellStar` (Hierarchy/Step2.lean:1830), `norm_oneSub_mul_Theta_le` (:1843), and the flow form `eq530` (:1889).
  - (5.31): `eq531` (:1991).
  - (5.32): `RBM.tailT_sub_le` (Analysis/StretchedExp.lean:337) and `RBM.unifDetDom_tailT_sub` (:396).
- Det / SD: Det. `eq530`/`eq531` are `∀ᶠ N, ∀ ω u a b` with no probability.
- Unif. u: yes.
- Dims: abstract `Band`/`Sample`, so every `d`.
- Exponents: literal.
- Missing: none.

**Row A5: initial condition `J*_s ≺ 1`, from (2.68)/(2.69).**
- Lean: `RBM.BoundsCore.decay` (Flow/Hypotheses.lean:278, a `StochDom` field, i.e. (2.69)), then `RBM.Step2.decayProf_le_tT` (Step2.lean:1258), then the inline `hinit` in the proof of `RBM.Step2.jS_highProb` (:1293, lines 1320–1324).
- Det / SD: the source is SD; `hinit` is a per-ω bound on the good event.
- Unif. u: n/a (single time `s`).
- Dims: abstract `Sample`.
- Exponents: literal.
- Missing: the named statement **M1** (≈1 ticket, repackaging).

## 2. Table B: Lemma 5.7, (5.34)–(5.36); proven versus displayed exponents

Exponents in the paper:
- Displayed (5.35): `η_u^{-1}r²·1(near) + η_u^{-1}A_u^{-1/3}(J*)³`.
- Displayed (5.36): `η_u^{-1}r⁵·1(near) + η_t^{-1}A_u^{-1/2}(J*)³`.
- Proof-level forms, as they appear in Lean:
  - (5.35) near (5.55): `η_u^{-1}r²(1+(J*)²A^{-1})`.
  - (5.35) far (5.63) with abstract `κ₁` ((4.5)/(2.73) prefactor) and `κ₂` ((5.57)): `η_u^{-1}κ₁(c_far·J·κ₂ + J^{3/2}(168A^{-1} + L√(W^{-D})/ℓ_u))`.
  - (5.36) far (5.71)+(5.72): `η_u^{-1}(c_far2·J²·A·μ + 72·J³·A^{-1})` with `μ = (max L)^{1/2}`. For `μ ≤ r^{3/2}A^{-3/2}` this is `J²r^{3/2}A^{-1/2} + J³A^{-1}`.
- Notation: `r = ℓ_u/ℓ_s`, `A = A_u = Wℓ_uη_u`.
- Pilot §9 (B) requires the proof-level forms.

**Row B1: (5.34), `E^{((L−K)×(L−K))}`.** Displayed and proof-level exponents coincide.

| Lean (file:line) | Version | Det / SD | Unif. u | Dims |
|---|---|---|---|---|
| `RBM.Step2.eLL` (def, Step2.lean:222), `RBM.Step2.norm_eLL_le` (:250) | the only shape: `e(J*)²(36η_u^{-1}A^{-1} + WLW^{-D})T_{u,D}` | Det (any input function) | n/a | abstract |
| `RBM.Step2FarInputs.quadGlue_pm_eq_eLL` (Hierarchy/Step2FarInputs.lean:2337) | identifies the (5.49) gluing term of `L−K` with `eLL` | Det | any u | abstract `Sample` |
| `RBM.Step2FarInputs.quad_near_le_of_jS` / `quad_far_le_of_jS` (:2573 / :2460) | per-ω bound with `J := Step2.jS`, given `hJ : jS ≤ N^δ(η_s/η_u)²` and deterministic (2.72) facts | Det (per ω, on the hypotheses) | yes (`∀ u ∈ Ico`) | abstract `Sample` |

Consumed by `RBM.Step2.step_bound` (`h534`, Step2.lean:809), and by `egData_of_jS` (Step2FarInputs.lean:2810).

Missing: none for the per-ω bound. In the discrete route, `hJ` is exactly what σ's threshold gives before the stopping time.

**Row B2: (5.35), `E^{(G̃)}`.** In all cases below, J is abstract unless stated otherwise.

| Lean (file:line) | Version | Det / SD | Unif. u | Dims |
|---|---|---|---|---|
| `RBM.Lemma57.eG_le` (Hierarchy/Lemma57.lean:1116) | **proof-level** master: near `κ₁c_near r²`, far `κ₁(c_far Jκ₂ + J^{3/2}(…))`, abstract `κ₁, κ₂` | Det | fixed u | abstract reals |
| `RBM.Lemma57.eG_le_paper` (:1420) | **displayed** `A^{-1/3}J³`, with `κ₂ = A^{-1/2}(1+JA^{-1})`; needs `J ≤ A` | Det | fixed u | Hermitian `H` |
| `RBM.Lemma57.eG_le_reduced` (:1463), `eG_le_reduced_of_schwarz` (:1311) | **proof-level, (2.73)-reduced**: `κ₁ = r`, `κ₂ = r^{1/2}A^{-1/2}`; near `r³`, far `c_far r^{3/2}A^{-1/2}J + 169 rA^{-1}J^{3/2}` | Det | fixed u | Hermitian `H` |
| `RBM.EGDef.eGpm` (def, Hierarchy/EGDef.lean:86), `norm_eGpm_le` (:221, i.e. (5.52)), `RBM.EGDef.eGpm_le_reduced` (:262) | `eG_le_reduced` applied to the concrete `E^{(G̃)}` of (5.51) | Det | fixed u | Hermitian `M` |
| `RBM.EGDef.F_eq_eGpm_add_quadGlue` (:694) | drift `F = eGpm + (5.49) gluing`, conditional on `MomentDuhamel.Hyp X E s t 0` | Det | fixed u | abstract `Sample` |
| `RBM.Step2FarInputs.farDrift_eq_eGpm_add_quadGlue` (:163) | the same identity for the pinned drift `farDrift`, **with no hypothesis structure** | Det | fixed u | abstract `Sample` |
| `RBM.Step2FarInputs.rhs535` (def, :994), `eGpm_le_rhs535` (:1116), `eGpm_le_rhs535_of_jS` (:2224), `h535_of_jS` (:2267) | proof-level (2.73)-reduced shape; `_of_jS`: `J := Step2.jS` pinned, with `h531` proved and `h42` by definition of `gmOfJS` (:2184); `h535_of_jS`: `∀ u ∈ Ico`, with `ℓ_s := ℓ_{s_N}` pinned | Det | `h535_of_jS`: yes | abstract `Sample` |
| `RBM.APrimeGeneralMovingDriftSourceGeneralDims.highProb_commonEvent` (Gauss/APrimeGeneralMovingDriftSourceGeneralDims.lean:75); `pointwise_source_package` (:141); `pointwise_far_source_bound` (:362); `pointwise_near_source_bound` (:477) | `HighProb commonEvent` for every `d : Dims` (hypotheses: `|E|<2`, `60 ≤ D`, window, `Cond272Reg`, `BoundsCore`). On it, for all `u ∈ TimeIcc`, the **eG_le-type far bound** with `κ₁ = 4N^ζ r`, **`κ₂ = flowDelta + W^{-1}`**, `J := jG`, `Gm := gmBlk` | SD event + Det on it | yes | **every `d : Dims`** |

Exponents:
- `eG_le`, `eG_le_reduced` and `eGpm_le_reduced`/`rhs535` are proof-level, i.e. pilot §9 (B) compliant.
- `eG_le_paper` is the displayed shape.
- The APrime far bound is proof-level in structure, but its `κ₂ = (Wℓ_tη_t)^{-1/6} + W^{-1}` is **weaker** than (5.57)'s `A_u^{-1/2}`. Whether that suffices for σ must be checked in A5. A rough count with pilot §9's extreme case `η_s/η_t ≤ A^{1/30}` suggests it does. This is indicative only.
- `RBM.Step2.Hyp.eG` (Step2.lean:1237) is still an unproved structure field in the displayed shape, and is not the target.

Missing: **M4** (full-strength (5.35) on a high-probability event, 1–2 tickets after M2).

**Row B3: (5.36), `(E⊗E)`.**

| Lean (file:line) | Version | Det / SD | Unif. u | Dims |
|---|---|---|---|---|
| `RBM.Lemma57.ee_le` (:1818) | **proof-level** master, abstract `μ`: far `c_far2 J²Aμ + 72J³A^{-1}`; carries `hsym`, `h566` | Det | fixed u | abstract reals |
| `RBM.Lemma57.ee_le_paper` (:1874) | `μ := r^{3/2}A^{-3/2}` and the far bracket **merged** into `(c_far2+72) r^{3/2}A^{-1/2}J³`, a displayed-like shape that keeps `r^{3/2}` | Det | fixed u | abstract reals |
| `RBM.Lemma57.ee_le_sym` (:2661), `ee_le_paper_sym` (:2711) | the same two shapes **without `hsym`/`h566`** (T190) | Det | fixed u | abstract reals |
| `RBM.EEDef.eeL6` (def, Hierarchy/EEDef.lean:168), `norm_eeFun_le_W_sum` (:186), `norm_EEpath_le_W_sum` (:198) | concrete `L^{(1)}(b)` of (5.22) and `‖E⊗E‖ ≤ W Σ_b eeL6` | Det | fixed u | abstract `Sample` |
| `RBM.EEDef.ee_le_EEpath_sym` (:1294) | **proof-level** (5.36) for the concrete `EEpath`, `μ = 2√Smax` abstract, `J` with `h42sq`; only for **`a' = a`** (`hc0`, `hc1`) | Det | fixed u | abstract `Sample` |
| `RBM.EEDef.ee_le_paper_EEpath_sym` (:1359) | the same with `hμbd`, far bracket merged (displayed-like) | Det | fixed u | abstract `Sample` |
| `RBM.EarlyQVRate.quadVar_lkFun_le_ee_sym` (Gauss/EarlyQVRate.lean:295); `RBM.EarlyQVRateEv.stochDom_quadVar_grid` (Gauss/EarlyQVRateEv.lean:489), `stochDom_quadVar_grid_det` (:706) | quadVar of `(L−K)_{u,σ,a}` ≤ proof-level RHS; grid `StochDom` over `{j ≤ n_N} × σ × a`, conditional on `Step1.Hyp`, with **`J := jStar`** | SD | grid (yes) | abstract `Sample`; for every `d` via `step1Hyp_gauss_of_scale''` |
| `RBM.APrimeFullQV.sourceEvent_of_step1` (Gauss/APrimeFullQV.lean:37), `early_raw_full` (:55) | per-ω quadVar ≤ proof-level `diagShape'` with **`J := jG`** (blockwise), given the n = 4, 6 Step-1 source event | Det on the event | fixed u | abstract `Sample` |

Exponents:
- `ee_le`, `ee_le_sym`, `ee_le_EEpath_sym`, `s3Rhs` and `diagShape'` are proof-level (pilot §9 (B) compliant).
- `ee_le_paper(_sym)`/`ee_le_paper_EEpath_sym` merge the two far terms. They are therefore **not** the (5.71)/(5.72) shape pilot §9 requires. The audit's D4 is correct on this point.
- No named instance gives the proof-level bracket with `μ` already evaluated at `r^{3/2}A^{-3/2}`.

Defect found in `stochDom_quadVar_grid(_det)`: it cannot serve σ.
- Its `jStar` (EarlyQVRateEv.lean:146) is built from the **global** maximum `gMax = max_{σ,p,q}|G_σ(p,q)|` (:112), which includes the diagonal entries.
- Hence, whenever a far pair exists (`ℓ*_u/2 ≤ zdist`), `jStar ≥ 1 + gMax²/tailT(d) ≥ 1 + (1−δ_N)²/(A^{-2}+W^{-D})`. This uses `|G_pp − m| ≤ δ_N` on (4.1) and `|m| = 1`.
- So `jStar ≳ min(A², W^D)`, far above σ's threshold `N^δ(η_s/η_t)^4`.
- `early_raw_full`'s `jG` does not have this defect (row A3 links it to `jS`).

Missing: **M5** (proof-level named instance, ≈1 ticket), **M6** (grid/high-probability form with `J := jG`, 1–2 tickets), **M7** (the `a' ≠ a` case needed by (5.42), 1–2 tickets).

## 2b. (5.39)–(5.42): U-kernel estimates, Lemma 7.1, tail (7.2)

| Item | Lean (file:line) | Det / SD | Unif. u | Dims |
|---|---|---|---|---|
| Lemma 7.1, `‖U∘A‖ ≤ Cⁿ M` | `RBM.norm_Uker_apply_le`, Hierarchy/Kernel.lean:256 | Det | any u ≤ t | abstract |
| (7.2) far-field tail | `RBM.norm_Uker_tail_le_ellStar`, Hierarchy/KernelDecay.lean:2314 | Det | yes | abstract |
| (5.39)–(5.41) | `RBM.Step2.norm_Uker_le_of_tail`, Step2.lean:448; flow form `norm_Uker_flow` (:691) | Det | yes | abstract |
| semigroup law `U_{u,t}U_{s,u} = U_{s,t}` (pilot §3) | `RBM.Uker_comp`, Kernel.lean:306 | Det | — | abstract |
| (5.42) quadVar of the U-propagated observable versus `(U⊗U)(Q Q (E⊗E))` | `RBM.EEUker.quadVar_qUkerObsT_le_norm_QQ_eeFun'`, Gauss/MomentDuhamelQInt.lean:739 | Det (at `M = H_u`) | fixed u, v | abstract `Sample` |

Missing: bounding the right side of the last row by the (5.36) shape needs `(E⊗E)` at doubled arguments with `a' ≠ a`, because `U⊗U` mixes labels. That is **M7**.

## 3. Missing statements (ticket targets)

Common notation (Lean): `ℓ_u := (band d).ell N u`, `ℓ_s := (band d).ell N (s N)`, `η_u := etaT E u`, `A_u := (d.W N : ℝ) * ℓ_u * η_u`. "Step-1 hypotheses" means the hypothesis list of `RBM.Gauss.step1Hyp_gauss_of_scale''`: `0<κ`, `|E| ≤ 2-κ`, `BoundsCore (sample d) E s`, `∀N, 0 ≤ s N`, `∀N, s N ≤ t N`, `∀N, t N < 1`, `Cond272 (band d) E s t`, `0<c`, `∀ᶠ N, N^c ≤ (band d).scale E N (t N)`. These are simultaneously satisfiable in every earlier general-`Dims` ticket that used them, e.g. `eventually_commonEvent_nonempty` (APrimeGeneralMovingDriftSourceGeneralDims.lean:127) under the same list.

- **M1 (initial condition, ≈1 ticket, repackaging).** Under `BoundsCore X E s`, `|E| < 2`, `0 ≤ s`, `s < 1` and `∀ᶠ N, 1 ≤ B.scale E N (s N)`:
  `∀ D > 0, StochDom B.P (fun N (_ : Unit) ω => RBM.Step2.jS X E D N (s N) ω) (fun _ _ _ => 1)`.
  Sources: `BoundsCore.decay`, `decayProf_le_tT`, and the inline `hinit` of `jS_highProb`.

- **M2 ((4.2) implies (5.57) at (2.73)-reduced strength, 2–3 tickets).** For `d : Dims` under the Step-1 hypotheses, `∀ τ > 0`:
  `HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N, ∀ (x y : ZMod (d.L N)) (p : ZMod (d.L N) × Fin (d.W N)), p.1 = y → ∑ r, Lemma57.blkW (d.L N) (d.W N) r x * ‖green (Hflow d N u ω) (zt E u) r p‖ ≤ (N:ℝ)^τ * √(ℓ_u/ℓ_s) * (√A_u)⁻¹})`,
  together with the row form (`∀ r, r.1 = x → ∑ p, blkW p y * ‖green … r p‖ ≤ …`), on the same event.
  Sources:
  - `entryBoundFlow_floor` with `B ≥ 1`;
  - `Step1.apriori` at `n = 2` with `step1Hyp_gauss_of_scale''`, giving `L_{(+,-)} ≺ r A_u^{-1}`;
  - `highProb_goodSetFlow` for the indicator;
  - the diagonal entry `r = p` contributes `W^{-1}(1+δ_N) ≤ 2A_u^{-1/2}`, because `ℓ_uη_u ≤ 1`;
  - `W^{-1} ≤ A_u^{-1}` for the near-block term.

- **M3 (absorbing the ≺ loss into the reduced shape, ≈1 ticket, arithmetic).** `eGpm_le_rhs535_of_jS` takes `h273`/`h557C`/`h557R` with constant 1, while Step 1 gives them only up to `N^τ`.
  - Since `ℓs` is a free parameter there (only `0 < ℓs`, `1 ≤ ℓ_u/ℓs` are required), instantiate `ℓs := N^{-2τ}ℓ_s`.
  - This needs `rhs535 Wr Lr ℓu (ℓs / c) ηu D J ρ d ≤ c^3 * rhs535 Wr Lr ℓu ℓs ηu D J ρ d` for `c ≥ 1` and nonnegative data (the degree in `r` is ≤ 3).
  - `h535_of_jS`/`EGData` pin `ℓs := ℓ_{s_N}` and cannot absorb the loss. A consumer must therefore go through `eGpm_le_rhs535_of_jS` plus this lemma.

- **M4 ((5.35) proof-level shape at full `κ₂` on one event, 1–2 tickets after M2).** For `d : Dims`, under the hypotheses of `highProb_commonEvent`, `∀ ζ τ > 0`, on `commonEvent ∩ (M2 event)` (still `HighProb`):
  `∀ u : TimeIcc s t N, ∀ a₁ a₂, zdist (a₂−a₁) ≥ ℓ*_u → ‖EGDef.eGpm (d.L N) (d.W N) (mSigma E) (Hflow d N u ω) (zt E u) a₁ a₂‖ ≤ η_u⁻¹ κ₁ (cFar W ℓ_u · jG · κ₂ + jG√jG (168 A_u⁻¹ + L√(W^{-D})/ℓ_u)) · tailT W ℓ_u η_u D (zdist (a₂−a₁))`,
  with `κ₁ = 4N^ζ r` and `κ₂ = N^τ √r A_u^{-1/2}`. This is `pointwise_far_source_bound` with its `kappa2` replaced. The near branch is unchanged (`pointwise_near_source_bound`).

- **M5 ((5.36) proof-level named instance, ≈1 ticket).** `ee_le_reduced_EEpath_sym`: the hypotheses of `EEDef.ee_le_EEpath_sym` plus `hμbd` (as in `ee_le_paper_EEpath_sym`), with the conclusion **not merged**:
  `… ≤ η_u⁻¹(cNear2·r⁵·1(≤4ℓ*_u) + cFar2·(2J)²·r^{3/2}A_u^{-1/2} + 72(2J)³A_u⁻¹)·T² + (remainders)`.
  This is the (5.71)/(5.72) shape pilot §9 (B) requires. An abstract twin `ee_le_reduced_sym` from `Lemma57.ee_le_sym` is optional.

- **M6 ((5.36) on a high-probability event with the blockwise J, 1–2 tickets).** For `d : Dims` under the Step-1 hypotheses, `∀ τ > 0`:
  `HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N, ∀ a : LoopArg (d.L N) 2, quadVar (band d).toDims N (fun M' => MomentDuhamel.lkFun (band d) E N u M' Step2.sigPM a) (Hflow d N u ω) ≤ N^τ · APrimeQVEndpoint.diagShape' (band d) N ℓ_u ℓ_s η_u D (APrimeJG.jG (sample d) E N u ω ℓ_u η_u D) (EarlyQVRateEv.sDet (band d) E N u ℓ_s) (EEDef.nearEpsilon …) a})`.
  Sources: `sourceEvent_of_step1` and `early_raw_full` fed by `Step1.apriori` at n = 4, 6, plus `highProb_jG_le_of_entryBoundFlow` for `jG ≤ N` (`hJcap`). This replaces the `jStar` version, which cannot serve σ (row B3).

- **M7 ((5.36) off the diagonal `a' ≠ a`, 1–2 tickets: M7a ≈ ½–1, M7b ≈ 1).** This is needed to bound the right side of `quadVar_qUkerObsT_le_norm_QQ_eeFun'` (2b), because `U⊗U` mixes labels. Current Lean covers only `a' = a` (`hc0`/`hc1` of `ee_le_EEpath_sym`; paper-delta #113 ①).
  - **M7a (Cauchy–Schwarz, no hypothesis).** For `a a' : LoopArg (B.L N) (0+2)` and `σ : Fin (0+2) → Bool`:
    `‖EEpath X E 0 N u ω σ (Fin.append a a')‖ ^ 2 ≤ ‖EEpath X E 0 N u ω σ (Fin.append a a)‖ * ‖EEpath X E 0 N u ω σ (Fin.append a' a')‖`.
    - No positive-semidefiniteness hypothesis is needed. The kernel is a Gram kernel by definition.
    - `EEpath … c = eeArg … σ c`, and by `eeArg_append` this equals `Gauss.eeTens d N z M (toIdx σ a) (toIdx σ a')`.
    - `eeTens I I' = ∑_{k<I.length} ∑_{i,j} e_k(I)_{ij} · conj(e_k(I')_{ij})`, where `e_k = emartEdge` (Gauss/DischargeBDG.lean, `eeEdge`/`eeTens`). This is a finite inner product `⟨v(I), v(I')⟩`. The two loops `toIdx σ a` and `toIdx σ a'` have the same length, so the index sets agree.
    - So M7a is the Cauchy–Schwarz inequality for finite sums. The diagonal entries `eeTens I I = ∑|e|²` are real and nonnegative.
  - **M7b (the bound).** Take the notation of `ee_le_EEpath_sym`: `A := (B.W N : ℝ) * ℓu * ηu`, `Wr := (B.W N : ℝ)`, `Lr := (B.L N : ℝ)`, `dist := (zdist (B.L N) (a 0 − a 1) : ℝ)`, `T := tailT Wr ℓu ηu D dist`. The hypotheses are the following.
    - All hypotheses of `EEDef.ee_le_EEpath_sym` except `hc0`/`hc1`: `hℓu, hℓs, hηu, hJ, hρ, hGm0, hGm, hGsq0, hGsq2, hrow, hSmax, h42sq`. These do not depend on `c`.
    - `h273` and `h564` at **both** `c := Fin.append a a` and `c := Fin.append a' a'`, with one common `ρ`. For these two `c`, `hc0`/`hc1` hold by `leftArg_append`/`rightArg_append`.
    - `{C : ℝ} (hC : 0 ≤ C)` and `(hdisp : ∀ i, (zdist (B.L N) (a i − a' i) : ℝ) ≤ C * ellStar Wr ℓu)`.

    The conclusion is
    `‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a a')‖ ≤ Real.exp (√(2*C) * Real.log Wr ^ (3/4 : ℝ)) * ( ηu⁻¹ * (Lemma57.cNear2 Wr ℓu * (ℓu/ℓs)^5 * (if dist ≤ (4 + 2*C) * ellStar Wr ℓu then 1 else 0) + Lemma57.cFar2 Wr ℓu * ((2*J)^2 * (A * (2*√Smax))) + 72 * (2*J)^3 * A⁻¹) * T^2 + (Wr * Lr * ρ + 2 * Wr * Lr * Wr^(-D) * (2*J)^3 * T^2) )`.
  - Proof of M7b.
    - Write `R(c)` for the right side of `ee_le_EEpath_sym` at `c`, and `dist'` for the distance of `a'`.
    - `zdist_add_le` gives `dist' ≥ dist − 2C·ℓ*_u`.
    - `tailT_antitone` and `tailT_sub_le` with constant `2C` then give `tailT(dist') ≤ e^{λ}·tailT(dist)`, where `λ := √(2C)(log W)^{3/4}`.
    - The same distance bound gives `1(dist' ≤ 4ℓ*_u) ≤ 1(dist ≤ (4+2C)ℓ*_u)`, and trivially `1(dist ≤ 4ℓ*_u) ≤ 1(dist ≤ (4+2C)ℓ*_u)`.
    - Let `K̄ := ηu⁻¹(cNear2·r⁵·1(dist ≤ (4+2C)ℓ*_u) + cFar2·(2J)²·A·2√Smax + 72(2J)³A⁻¹) + 2·Wr·Lr·Wr^{-D}(2J)³`, where `r = ℓu/ℓs`.
    - Write `R(a,a) ≤ x + y` and `R(a',a') ≤ e^{2λ}x + y`, with `x = K̄·T²` and `y = Wr·Lr·ρ`. The second inequality uses `tailT ≥ 0`. Then `(x+y)(e^{2λ}x+y) ≤ e^{2λ}(x+y)²`, since `1 + e^{2λ} ≤ 2e^{2λ}`.
    - M7a then gives the conclusion, with loss factor exactly `e^{λ}`.
  - About the loss factor (not `1+o(1)`):
    - `e^{λ} = exp(√(2C)(log W)^{3/4})`. This is `W^{o(1)}` only if `C = o((log W)^{1/2})`.
    - The near-region indicator also widens from `4ℓ*_u` to `(4+2C)ℓ*_u`.
    - The value of `C` is fixed by the application, and this report does not decide it. The labels in (5.42) are displaced by the `U`-kernel tail (7.2). If that displacement is on the scale `ℓ*_v` of a later time `v ≥ u`, then `C = ℓ_v/ℓ_u ≥ 1`. That is because `ℓ` is non-decreasing in time: `Step3.ellHat_mono` and `Step2FarMart.ellStar_mono_time` give `ℓ*_u ≤ ℓ*_v`, so the re-audit's "`ℓ*_t ≤ ℓ*_u`" has the inequality reversed for `u ≤ t`.
    - Whether `ℓ_v/ℓ_u` is small enough for the loss to be harmless must be checked when σ's bookkeeping is assembled (A5).

Total for A5 on these inputs: about 9–12 tickets (M1 1, M2 2–3, M3 1, M4 1–2, M5 1, M6 1–2, M7 1–2). The P1 transfer lemmas and P4 are excluded.

## (b) Declarations added, build, axioms

None. The ticket is report-only, so no Lean file was touched, nothing was built with `lake build`, and there are no axioms to print. The only commands run were the `lake env lean` scratch checks of §0, all with rc 0.

## (c) Key existing lemmas the A5 assembly would use

`step1Hyp_gauss_of_scale''`, `Step1.apriori`, `entryBoundFlow_floor`, `highProb_goodSetFlow`, `highProb_jG_le_of_entryBoundFlow`, `gsqBlk_le_jG_mul_tailT`, `eq531`, `tailT_sub_le`, `norm_eLL_le` + `quad_{near,far}_le_of_jS`, `eG_le` / `eGpm_le_rhs535_of_jS` / `pointwise_{far,near}_source_bound`, `ee_le_EEpath_sym` / `early_raw_full`, `norm_Uker_le_of_tail`, `Uker_comp`, `quadVar_qUkerObsT_le_norm_QQ_eeFun'`.

## (d) Open issues

1. `EarlyQVRateEv.jStar` is not the paper's `J*_{u,D}`. As shown in row B3, it is at least of order `min(A_u², W^D)` whenever a far pair exists, so `stochDom_quadVar_grid(_det)` is a true but useless bound for σ. The module docstring's claim that "`jStar` is literally `J_{u,D}` of (5.28)" is inaccurate. This should be re-audited; paper-delta candidate `T1488a`.
2. Suspected unsatisfiable hypothesis. In `eGpm_le_rhs535_of_jS`/`h535_of_jS`, the hypothesis `h560` is required for **all** `b` with `Gm := gmOfJS = √(jS·T_{u,D}(d))`.
   - At `b = a₁`, the right side is `jS^{3/2}·T(|a₁−a₂|)·(A^{-2}+W^{-D})^{1/2}`.
   - The heuristic size of the left side there is `≈ |m|·L_{(−,+),(a₂,a₁)}`, which can be as large as `jS·T(|a₁−a₂|)`.
   - So `h560` looks false on typical samples whenever `jS < A²`. I did not compile this; it needs a satisfiability check.
   - The APrime route (`Gm := gmBlk`, `J := jG`) avoids the issue. This is why M4 is stated on that route.
3. The APrime far bound uses `κ₂ = (Wℓ_tη_t)^{-1/6} + W^{-1}`, weaker than (5.57). A5 must decide whether M2/M4 are needed or whether the weaker exponent closes σ's bookkeeping; the rough count says it does.
4. Pilot §9 quotes the proof exponents of (5.35) as `(Wℓη)^{-1/2}(J*)² + (Wℓη)^{-3/2}(J*)³`. Lean's `eG_le` carries `κ₁(c_far Jκ₂ + J^{3/2}·…)`. With the paper's `κ₁ = 1+JA^{-1}` and `κ₂ = A^{-1/2}(1+JA^{-1})`, the leading product is `JA^{-1/2} + 2J²A^{-3/2} + J³A^{-5/2}`, which for `J ≥ 1` is at most the pilot's expression. So Lean's form is at least as strong as the pilot's. Revision 1 called this a "discrepancy"; it is not one.
5. Paper-delta candidates, not written here because the sole writable file is this report:
   - `T1488a` (issue 1);
   - `T1488b`: `ee_le_paper*` merges the (5.71)/(5.72) terms, and σ must use the unmerged form (M5).
