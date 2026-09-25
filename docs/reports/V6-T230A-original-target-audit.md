# V6: whole-paper dependency plan and original T230/A′ target audit

Read-only mathematical audit, 2026-09-24. This report follows Jun's corrected priority: the objective is the whole paper, not T230/A′ itself. Only `paper/250520-YinJun-v2.pdf` is used as a mathematical source. Its formulas and main theorems were read directly from the local PDF text extraction. The source declarations cited below were personally inspected. Archive access was restricted to the T230 row. No Lean was edited, no task was dispatched, no build or new theorem is claimed.

## Verdict

There is an explicit **dependency roadmap**, but not yet an end-to-end proof-ready plan. Several first missing arrows are actual analytic estimates whose complete proofs have not been preflighted. Calling them implementation tasks would conceal the mathematical uncertainty.

The accepted radial Gaussian route is a legitimate alternative proof strategy for the paper's final **static Gaussian matrix** statements. Identifying it with a Brownian stopped process is neither true nor necessary. The exact transfer to the final matrix already exists in `Gauss/DistEq.lean`. Conversely, equality of one-time marginal laws cannot transfer a time-supremum or stopped-process identity.

The local T1337 result really does imply paper (2.75) and the literal RHS of (2.76), for `Dims.exampleGrow`, fixed energy, an incoming `BoundsCore`, and `Cond272Reg`. The placement of the `W^{-D}` floor is a small comparison still to formalize, not a missing analytic estimate. This local result does not propagate all fields of `BoundsCore`, cover all paper-allowed dimensions/energy sequences, prove the sharp (5.47)/(5.48), or discharge the universality branch.

## 1. The actual final objectives

Paper §2.1 is already a **Gaussian complex Hermitian block band model**, with `N=WL` and (2.2) `W >= N^(1/2+c)` for any fixed `c>0`. General non-Gaussian entry laws are not a new obligation of this paper.

| Paper conclusion | Mathematical input | Existing Lean consumer; remaining qualification |
|---|---|---|
| Theorem 2.3, (2.3)/(2.4), local and partial tracial laws | First five steps of Theorem 2.21, grid iteration, resolvent transfer | `Flow/EnergyUniform.lean:660,722`, `localSemicircleLaw_of_boundsCoreN`, `localSemicircleLaw_of_boundsCoreN_of_z`; need actual `BoundsCoreN`, not an assumed step theorem |
| Theorem 2.2, all bulk eigenvectors | Energy-uniform local law and spectral estimate (2.10) | `Flow/EnergyUniform.lean:1162`, `delocalization_of_Thm221N'`; its premise is **`Thm221NoELN'`**, not a fixed-energy `Thm221NoEL` |
| Theorem 2.4, high-probability (2.6)/(2.7) | Same first pass, length-two loops and transfer | `Flow/Consequences.lean:680,699,711`; fixed-energy assembled consumers also exist in `Flow/Thm221NoEL.lean:1073` |
| Theorem 2.4, expectation (2.8)/(2.9) | Step 6's extra cancellation, propagated (2.71) | `Flow/Consequences.lean:792,808,826`; need the full `Bounds.expect` field |
| Theorem 2.5, generalized QUE (2.12)/(2.13) | Expectation diffusion, oscillation of primitive kernel, spectral/Markov argument | `Flow/Universality.lean:1457`, `theorem2_5_of_QDExpect`; `Gauss/Thm25Gauss.lean:115` discharges loop integrability but still assumes `Thm221` and a **fixed-flow-energy `SpecSeq` slice** |
| Theorem 2.6, bulk universality (2.18) | Actual OU/GUE interpolation, local law/QUE on interpolation, comparison (2.23), DBM theorem | `Flow/Universality.lean:1675`, `theorem2_6_of_steps`, currently has three substantive hypothesis slots; see §7 |

The final theorem range must include arbitrary admissible dimension sequences and bulk energies. Proving one fixed-energy growing example is an important witness and intermediate theorem, but not any of these full main theorems.

## 2. End-to-end graph, with precise completion gates

```text
Actual Gaussian model, all admissible d; energy sequences E_N in a fixed bulk
  |
  +-- incoming BoundsCoreN at s + Cond272Reg/gained grid condition
  |      |
  |      +-- Step 1 producer [exists]
  |      +-- weak normalized J* / Step 2 [exampleGrow, fixed E: exists]
  |      +-- all-charge xiLK_2 cutoff moment [missing analytic localization]
  |      +-- all-n Lemma 5.14 [Q/nonalternating/moving decay gaps]
  |      +-- actual Eq. (4.5) random-scale input [missing fluctuation estimate]
  |      +-- Eq. (5.48) sharp near + far data [missing; quantifiers need repair]
  |      |
  |      +--> Steps 1--5 --> BoundsCoreN at t
  |                   --> grid from zero --> local laws / diffusion (2.6),(2.7)
  |                                      --> energy net --> delocalization
  |
  +-- preceding flow estimates + incoming Bounds.expect at s
  |      +--> existing Gaussian Step 6 analytic assembly
  |      +--> Bounds.expect at t --> full grid --> (2.8),(2.9) --> QUE
  |
  +-- actual OU/GUE interpolation law and mixed-covariance estimates
         +--> (7.26),(7.29) --> (7.47) --> weak QUE along interpolation
         +--> (2.23) + internal Green comparison
         +--> authorized external [51] --> bulk universality
```

**Milestone M1 — one honest local Gaussian induction step.** For `d=exampleGrow`, all fixed bulk `E`, and every deterministic `0<=s_N<=t_N<1` with `c>0`, `Cond272Reg`, prove

```lean
BoundsCore (Gauss.sample d) E s -> BoundsCore (Gauss.sample d) E t
```

using only incoming induction data. The exact current one-step consumer is `APrimeBoundsCoreStepAssembler.boundsCore_step_of_inputs_mergedOn_aprime_of_boundsCore` (line 28). Its four missing inputs are detailed in §3. Gate: a positive-length Gaussian window, the same `s,t`, all hypotheses jointly inhabited, and no Step 3/4/5 conclusion used to produce its own premise.

**M2 — full dimension and energy-sequence range.** Prove the same implication for every `d : Gauss.Dims` and arbitrary `E : N -> R` with `forall N, |E N|<=2-kappa`, with constants/thresholds in the necessary order. The exact grid consumer is `Thm221NoELN'.step`, `Flow/EnergyUniform.lean:199`. It takes `Cond272N'`, which the grid supplies; a sequence-energy `Cond272Reg` version is also a valid intermediate. Gate: a compiled actual producer, not `forall E fixed, ...` with an energy-dependent asymptotic threshold. Sequence-energy production is what permits the existing finite energy net and random eigenvalue argument.

**M3 — first-pass main theorems.** Use `BoundsCoreN_zero`, `boundsGrid_of_fields`, and `BoundsCoreN_of_Thm221NoELN'` (`EnergyUniform:288,432,493`), then `transfer_gauss`/`transferLoop1_gauss`. Assemble the full local law, high-probability diffusion and delocalization. Gate: final statements about `Xmat d`, all their requested spectral parameters, and only natural dimension/bulk assumptions left. The compiled grid and consequences must not be counted as producers of the missing induction step.

**M4 — expectation induction and QUE.** Feed M1/M2's actual flow conclusions to `Gauss.bounds_step_gauss_window_analytic`, `Gauss/FlowContInt.lean:412`, then iterate full `Bounds`/`BoundsN`. This source already discharges the often-repeated `hcont`, `hintU1`, `hintU2` gaps (lines 380,389,398). Do **not** open duplicate regularity tickets from stale comments in `Step6EnvWindow`. Remaining inputs are Steps 1–5's delivered estimates plus induction data. Gate: match those input quantifiers and retain arbitrary energy sequences; remove the fixed-flow-energy `SpecSeq` restriction in the actual QUE consequence through `QDExpect`, rather than assuming it away.

**M5 — the independent universality branch.** Construct/verify an actual interpolation law, prove its comparison estimate and the internal comparison-to-correlations implication, and apply the sole authorized external [51] theorem with checked hypotheses. Gate: none of `StepTwoClaim`, `GreenComparison`, or an unverified OU law may remain as disguised assumptions. This branch is not currently reduced to routine Lean work; §7 names the first missing propositions.

These gates permit real parallelism, but there is no evidence that eight independent positive analytic targets are presently ready. A full theorem being a future milestone is not a proof of the milestone's premises.

## 3. First missing arrows in Steps 1–5

The local one-step consumer (`APrimeBoundsCoreStepAssembler:28`) takes incoming `hB`, Step 1, A′ slot, and four further inputs. `Gauss.step1Hyp_slot` already supplies Step 1 using `hB`; T1335 supplies the A′ slot for exampleGrow. The universal wrapper at line 48 still states some other producers without an incoming `BoundsCore` argument. Use the actual one-step theorem when assembling an induction; do not infer that this unnecessarily stronger wrapper is an analytic obligation.

### 3a. All-charge cutoff

The exact target is `CutHypEvOnSlot X E s t`, `Flow/Step345Producer.lean:749`:

```lean
exists Good : N -> Set Omega,
  (forall N, MeasurableSet (Good N)) /\ HighProb B.P Good /\
  Nonempty (MomentDuhamelCut.CutHypEvOn B.P
    (fun N u omega => X.xiLK E N u omega 2) s t
    (fun N => Step3.flowAs B E s N ^ (1/2 : R)) Good)
```

The field is **all charges**, not just `(+,-)`. The initial row is already T608. The actual modulus and its consumer field repair are T1339/T1351 (the scheduler reports accepted T1351); QV T1341 is its own active target. These do not prove the cutoff moment.

Smallest unresolved analytic issue: localize the actual Gaussian time integral while retaining intermediate-time support and control the drift source `xiLK_1 * xiL_3`, in addition to `xiLK_2^2`. T596's present reduction removes the endpoint truncation before Duhamel and then asks for unrestricted drift moments. Endpoint truncation alone does not control the path between `s` and the endpoint. Restricting Stein to an indicator event is not legal integration by parts. A new actual smooth localization estimate, with its cross derivative and support proved, or another valid Gaussian proof is needed. No proof-ready positive theorem for this entire row has been established in this audit.

### 3b. Lemma 5.14

The exact consumer requires `forall n, 2<=n -> Step3.Lemma514 P flowXiLK flowXiL flowA n`. The source `Gauss/Lemma514QAssembly.lean:359,560` accepts nonnegative `s` and calls the Q/P-half/nonalternating moment rows. The narrow nonnegative-start P-half repair and the bounded CT decay seed are already active T1347/T1349; they are not new work. The CT seed is `E=0` and `u<=1/2`, not a first grid cell tending to 1. The unresolved obligations are actual Q/nonalternating budgets and adequate all-order moving decay under incoming data, with the lower-order hypotheses of `Lemma514Premises` and `QGood` retained. Do not replace them by the desired all-order conclusion.

### 3c. Eq. (4.5)

`Eq45FlowInputs`, `Flow/Step345Producer:181`, is exactly `exists x, IBPFlow ... x /\ FlucRowFlow ... x /\ FlucBlkFlow ... x`. The actual same-sample auxiliary `x` and random `Lmax_u(omega)` must be shared by all three.

`Gauss/Eq45FlowInputs` already contains the random-control net engine and slow-variation theorem. Thus another time-net constructor would duplicate work. The first missing mathematical estimate is the fixed-time **actual conditional fluctuation bound with the random `Lmax` control**, uniform in the deterministic time, followed by the conditional-expectation modulus. T1333 rejects only a canonical deterministic-majorant budget, not this claim or paper (4.5). No full positive proof route for that missing estimate was verified here.

### 3d. Eq. (5.48)

`Eq548EntryDataEvOnK`, `Flow/Thm221Assembly:1349`, asks for near `lkErr_pm ≺ R^2 tailT`, a modulus on one high-probability event, and all-order cutoff moments for the smooth far functional. Its fixed `Kmod` is outside `forall D`; a bound `Kmod=D-1` for each `D` does not fill that record. A valid primed consumer must move the modulus/net choice to its correct place before assembling the actual far estimate.

For near decay, T1345's accepted event makes the **same actual weight** equal to 1 for all active cells and all orders. T1343's sharper coordinate moment remains incomplete according to its current report/source (an import shell). Its mathematical target is still plausible from the already inspected raw initial/drift/QV inputs, but is not an accepted producer. Once proved, multiplying the coordinate by `R^2`, Markov and a polynomial union over coordinates/net points, then the Gaussian modulus, can yield `J*/R^2 ≺ 1`. Choose the free loss after the target stochastic exponent, and the fixed moment order after the desired tail exponent and net cardinality. This is a subsequent transfer, not a finished proof of (5.48)'s far component.

## 4. The exact original T230/A′ contract

The targeted archived row is `docs/archive/TASKS-done.md:28`. Its implementation acceptance explicitly says:

> `MomentHypCut.cut` / `MomentHypCut2.cut` are theorem-produced; the satisfiability witness has `R > 1`; axioms are clean.

It also forbids new free fields. The original request was first a read-only exploration of route B. Its particular good/bad iteration was rejected. Cowork/Jun explicitly authorized A′, replacing the prefix indicator by a smooth Gaussian-sample weight (subsequently an l^q soft maximum). This is an authorized alternative proof, not a request to reproduce a Brownian stopping-time construction. `paper-deltas.md` #118/#162/#170/#184 record that distinction; `HANDOVER.md:147` explicitly fixes the radial model and one-time law alignment.

The row is marked completed **structurally**, with `momentHypCutEv_of_aprime` and `momentHypCut2Ev_of_aprime`; actual weighted-moment discharge was deferred. The sharp second-pass consumer is `Gauss/Step2Bootstrap.lean:1490,1536,1557`:

```lean
MomentHypCut2Ev (Gauss.sample d) E s t D
-- whose cut is CutHypEv' for jSnorm2 = J*/R^2,
-- truncation level levSharp = R^2, output control 1.
```

Together with the blunt domination it yields `J* ≺ R^2`. Current T1335/T1337 provide the first pass `J*/R^4 ≺ 1`. They do not fill the second cut. A direct smooth-weight proof of sharp domination is sufficient for the final mathematical conclusion; if the old ticket is declared literally complete, produce the promised second-cut interface too, or explicitly approve the replacement acceptance statement. Neither contract requires stopped-process identity. Full Theorem 2.21 and the whole paper are broader objectives, not synonyms for this two-cut contract.

Paper (5.21)/(5.24) genuinely involve stopped martingale integrals. Paper (5.43) introduces the stop; (5.47) is sharp `R^2`; (5.48) separates near/far. These are intermediate proof statements. Paper Step 2's final (2.75)/(2.76) only needs the weaker `R^4` decay, explaining how T1337 reaches that local output without yet proving the sharp second pass.

## 5. One immediately proof-ready paper-alignment theorem

Write `A_u=W ell_u eta_u`, `R=eta_s/eta_u`, and `e_ab=exp(-sqrt(dist(a,b)/ell_u))`. The current T1337 RHS is

`R^4 A_u^-2 (e_ab + W^-D)`.

Paper (2.76) is

`R^4 A_u^-2 e_ab + W^-D`.

`StepGlue.eventually_R4_le_scale_of_cond272`, `Hierarchy/StepGlue.lean:785`, gives eventually and uniformly over `u : TimeIcc`, `R^4<=A_u` and `N^c<=A_u`. With `c>0,N>=1`, this gives `A_u>=1` and `R^4 A_u^-2<=1`. Therefore the first display is bounded by the second **for the same D**. No exponent reindexing or stochastic estimate is required.

Proposed theorem signature (new declaration, not claimed compiled): take exactly all hypotheses of `APrimeFreeLossGaussianStep2.step2_of_gaussian_hypotheses` and replace its second RHS by

```lean
(etaT E (s N) / etaT E p.1)^4 *
  ((Gauss.band d).scale E N p.1)⁻¹^2 *
    Real.exp (-(((zdist ((Gauss.band d).L N) (p.2.1-p.2.2) : R) /
      (Gauss.band d).ell N p.1) ^ (1/2 : R))) +
  (((Gauss.band d).W N : R) ^ (-D))
```

with `d=exampleGrow`, `forall D>0`, and the same full time/block-pair index. Prove the deterministic domination first for any band, then use `StochDom` monotonicity and T1337. Reuse its joint positive-window witness. This is a small exact final-statement alignment task, **not** the principal new analytic arrow toward M1.

## 6. Dimension range, energy uniformity, and false universalization

`Gauss/Model.lean:130` defines `Dims` with arbitrary sequences `W,L`, `WL<=N<=2WL` eventually, and `W>=N^(1/2+d.c)`, `d.c>0`. All current `APrimeFreeLoss...` final producers are specialized to `Dims.exampleGrow`. One actual arithmetic specialization is `APrimeFreeLossFarLinear.lean:244`: it assumes `W>=N^(5/8)` and gets the margin `N^(-13/24)`.

For a general `d`, the same calculation yields

`R^(5/2)/W <= N^(1/12)/N^(1/2+d.c) = N^(-5/12-d.c)`.

This remains a strong gain, so that particular row is not a mathematical obstruction to general dimensions. It does not prove the entire transitive chain is generic. Every actual producer, common event, mesh cardinality, floor and loss budget must be audited before replacing `exampleGrow` by `d`. In particular, estimates from other fronts using `L^2<=W` do not follow from paper (2.2) for arbitrary small bandwidth exponent. Do not import that extra restriction silently.

Fixed `E` must likewise be generalized with real uniformity, not by moving a quantifier through `eventually`. The existing `Thm221NoELN'` consumer is explicit about `E_N`; the final QUE slice is also visible in `theorem2_5_gauss`. These are independent range gates even after exampleGrow M1 is solved.

An arbitrary `Sample B` has only a Hermitian measurable path with `H_0=0`, not a Gaussian law or a hierarchy. Universal natural-hypothesis A′/Step-2 production for all such samples is false. For instance take `H_u=0` identically, `E=0`, `s=0`, `t=1/2`, a growing band. Initial `BoundsCore` is the zero-time identity and `Cond272Reg` holds eventually for a suitable positive `c`. Yet `G_t=2i I`, `m=i`, so the diagonal local-law error is 1 while `A_t^-1/2` tends polynomially to zero. This is a noncollapsed counterexample to the proposed universal implication, not to the Gaussian paper theorem.

## 7. Radial coupling and the separate universality branch

`Gauss/DistEq.lean` proves the needed static transfer exactly: `green_Hflow_lemT_eq`, `gloop_Hflow_lemT_eq`, `transfer_gauss`, `transferLoop1_gauss`, and `loopScaling_gauss`. Since `H_u=sqrt(u) X`, the resolvent scaling to `X` is pointwise. Thus the final Theorems 2.2–2.5 can be established through a completely radial proof without constructing Brownian motion. One-time equality cannot identify the joint path law, stops, martingale QV, or the probability of a supremum; use the actual radial estimates for those internal steps.

Theorem 2.6 has a different interpolation, (2.19). At `Flow/Universality.lean:1609`, `OUFlow` records only a Hermitian path and its start. Its comment explicitly says the **law is not formalized**. `theorem2_6_of_steps` assumes:

1. `DBMUniversality F kappa`, the authorized [51] input in already-applied form;
2. `GreenComparison F kappa`, currently another external hypothesis;
3. `StepTwoClaim F kappa`, the substantive model-dependent (2.23).

Under the handoff's rule that [51] is the sole external input, item 2 must be proved internally (or a changed external-input policy explicitly approved). The present conditional theorem is not whole-paper closure.

`Hierarchy/GUEPhase.lean:1390,1455` does implement the deterministic conversion `Eq747Inputs -> Eq747`. Its remaining actual inputs are precise: `law726` equates the OU endpoint loop expectation to the GUE-phase loop expectation; `eq729` gives all-small-loss expectation error `W^delta (N eta)^-3`, with `forall delta>0, eventually N, forall charges/blocks`; and the two integrability clauses. Algebraic primitive-kernel formulas are already proved. No actual OU/GUE producer of those two substantive fields, nor a producer of `StepTwoClaim` or `GreenComparison`, was found by the bounded source search.

The first universality milestone is therefore a law-correct model and actual producer specification for (7.26)/(7.29), plus a proof plan for (2.23), rather than instantiating the law-free `OUFlow` record. A full continuous Brownian construction may be avoidable with an explicit Gaussian interpolation/generator argument for static expectations, but that is a proposed research choice, not a proved bridge. The authorized [51] theorem must still apply to the chosen endpoint law with all its hypotheses checked. No external paper was consulted in this audit, so that final application is explicitly not preflighted here.

## 8. Scheduling conclusion

Keep the full-paper milestones visible and stop using local A′ acceptance as a proxy for them. The floor comparison is ready and small. The active sharp coordinate repair, accepted same-weight plateau, all-charge QV/modulus work and P-half seam each have concrete consumers, but their completion does not resolve the missing localization, Q/nonalternating, actual random-scale fluctuation, far-field, dimension/energy-uniformity or universality arrows.

The next substantial mathematical investigation should produce one complete actual estimate for one of §3's unresolved rows, with its common event, time support and quantifier order fixed. Until then the honest overall status is: **conditional upper-level architecture exists; several central analytic arrows remain unresolved; no fully preflighted end-to-end Lean proof plan yet**. This is a statement about present evidence, not a disproof of the paper or of the alternate Gaussian strategy.
