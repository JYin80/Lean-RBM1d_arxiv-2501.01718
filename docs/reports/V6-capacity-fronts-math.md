# V6 capacity follow-up: two real first-cell targets

Read-only mathematical preflight, 2026-09-24. No Lean source changed, no task dispatched, and no build claimed. This supplements, and does not change, `V6-next-fronts-math.md`. Mathematical references below are exclusively to `paper/250520-YinJun-v2.pdf`, read from its direct text extraction. Existing source signatures were personally inspected. Scheduler-owned T1339/T1341 remain disjoint.

## Recommendation

Two additional proof groups are justified, both on the first-cell Lemma 5.14 seam:

1. Extend the **actual Ward/P-half estimate** to `0 ≤ s`, retaining the `QGood` guard and proving the `PHalf514` consumer theorem.
2. Produce **actual all-order first-cell `LKDecay`** from the already proved Gaussian Combes--Thomas entry decay, with a common high-probability event and all-charge loop decay. This avoids the unresolved all-threshold hypothesis in `LKDecayQuant.flowInputs_of_inputs`.

These are independently provable in separate new files. Group 1's generic proof treats its existing `LKDecay` premise as an input; Group 2 produces that input on a genuine Gaussian first window. Group 1 need not wait for Group 2 to prove its core theorem. Their final composition is a small consumer check, not a third proof group. **Scheduling qualification:** Group 2 only covers `E=0, u≤1/2`; it is a bounded analytic seed and growing-model witness, not a producer on a full first grid cell whose endpoint tends to 1. If every new group must directly remove a general T230A-prime premise, release Group 1 and keep Group 2 optional.

I do **not** recommend dispatching a full actual all-charge nonlinear cutoff drift/moment claim yet. The precise missing support and linear-source issues are recorded below. Filling a count of eight is not evidence that six more proof-ready estimates exist.

## A. Nonnegative-start Ward/P-half

Suggested new source: `RBM1D/Gauss/Lemma514PHalfNonneg.lean`. Preserve existing frozen declarations. The exact main consumer signature is:

```lean
theorem pHalf514_of_wardP_nonneg
    (X : Sample B) {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hW : SumZeroDyn.WardP X E n)
    (hdec : SumZeroDyn.LKDecay X E s t) :
    PHalf514 X E s t n
```

Also export the stronger time-indexed analytic core, the nonnegative-start analogue of `SumZeroDyn.termP`:

```lean
theorem termP_nonneg
    (X : Sample B) {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hW : SumZeroDyn.WardP X E n)
    (hdec : SumZeroDyn.LKDecay X E s t)
    {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hX : StochDom B.P (Step3.flowXiLK X E s t (n + 1))
      (fun N _ _ => Φ N)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood p.2.1 then
          B.scale E N p.1 ^ (n + 2) *
            (‖Psum (B.L N) (SumZeroDyn.lkT X E N p.1 ω p.2.1)
                (p.2.2 0)‖ *
              ‖vartheta (B.L N) ((p.1 : ℝ) : ℂ) p.2.2‖)
        else 0)
      (fun N _ _ => 1 + Φ N)
```

`MeasurableSpace Ω`, `{B : Band Ω}` and namespace qualifications are the same as the original source. These are proposed signatures, not compiled declarations.

Source audit establishes a direct proof route:

- `Hierarchy/SumZeroDyn.lean:2918–3030` is the complete proof of `termP`. The strict-start input is used only to obtain `0 ≤ u` and to pass its weak form into `flow_crude`. `flow_crude` itself already accepts `0 ≤ s` at line 1381. Ward's identity `WardP` at line 1647 already includes time zero, as does `norm_Psum_lkT_le` at line 3209.
- Retain exactly the radius exponent `τ₁ = τ / (2*(n+2))` and decay exponent `D = 2*n+3+τ₁`. The main cost is `C_n N^(τ₁*(n+1)) Φ`; the error is `C'_n A_u^(n+1) L^n N^(τ₁-D)`. The existing `eventually_finish` argument absorbs both, since `A_u,L ≤ N` eventually. There is no division by `s` or by `u`.
- `Gauss/Lemma514QRoute.lean:675–718` only rescales this statement by `A_v^-(n+2)` and weakens `1+Φ` to `Λ^(1/2)+Φ`. Its scale positivity also has the existing nonnegative-time version `Band.scale_pos'`.
- `Gauss/Lemma514QAssembly.lean:293` defines `PHalf514`, and line 314 proves the current positive-start version. Its only use of `Lemma514Premises` is the lower-order slot `m=n+1`; no desired length-`n+2` conclusion is used. `SumZeroDyn.wardP_holds` at line 5409 discharges `hW` without a new hypothesis.
- Exact next consumer: `lemma514_of_momentDuhamelQ`, `Gauss/Lemma514QAssembly.lean:359–380`, already accepts `hs0 : ∀ N, 0 ≤ s N` and needs `hPhalf : PHalf514 ...`. The same input is required by the all-order Gaussian assembly at line 560. The new theorem closes precisely the current mismatch at `s=0`; it does not close the Q or nonalternating moment rows.

Paper basis: (5.96) and (5.87), used in (5.101). The mathematical formula is unchanged; only a surplus formal strict-start assumption is removed. Retain `QGood`: the unguarded estimate has a real `L^n` obstruction already proved in `Lemma514QRoute`.

Nondegeneracy must be checked jointly, not with an impossible `0<s=0` assumption. A simple independent witness is the actual Gaussian `Dims.example` (`L=3`, `W=max 1 (N/3)`) on `s=0,t=1/2,E=0`. `Cond272` holds eventually since `A_t→∞`; `LKDecay` holds because for each fixed `τ>0`, the radius eventually exceeds the fixed block diameter. This is a positive time interval with a nonconstant Gaussian sample. Choose positive deterministic polynomial envelopes `Λ,Φ` sufficiently large to dominate **all four** `Lemma514Premises` clauses, using the fixed spectral gap `η≥1/2` and primitive loop bounds; then invoke the new theorem at `v=1/4`. This witnesses both the new hypotheses and the actual conclusion, with `Λ,Φ` explicit in the delivered proof. Do not use `Φ=0` or an empty time window. Group B additionally permits a growing-dimension joint witness after composition.

## B. Actual first-cell all-charge loop decay from Combes--Thomas

Suggested new source: `RBM1D/Gauss/Lemma514FirstCellLKDecay.lean`. This is a genuinely analytic source-to-consumer estimate, not a generic constructor. Let `d = Dims.exampleGrow`. Exact target:

```lean
theorem lkDecay_first_half_exampleGrow :
    SumZeroDyn.LKDecay (Gauss.sample Dims.exampleGrow) 0
      (fun _ => 0) (fun _ => (1 / 2 : ℝ))
```

The stronger useful core should retain the existing actual common event `APrimeFirstCellJGAllTime.good`, and prove:

```lean
theorem eventually_loopDecay_pair_on_first_half_good
    (m : ℕ) (hm : 1 ≤ m)
    {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellJGAllTime.good N,
      ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
        Decay.LoopDecay ((Gauss.band d).L N) m
          ((Gauss.band d).ell N u * (N : ℝ)^τ)
          ((N : ℝ)^(-D))
          (gloop ((Gauss.band d).L N) ((Gauss.band d).W N)
            ((Gauss.sample d).H N u ω) (zt 0 u)) ∧
        Decay.LoopDecay ((Gauss.band d).L N) m
          ((Gauss.band d).ell N u * (N : ℝ)^τ)
          ((N : ℝ)^(-D))
          (gloop ((Gauss.band d).L N) ((Gauss.band d).W N)
            ((Gauss.sample d).H N u ω) (zt 0 u) -
            (Gauss.band d).Kval 0 N u)
```

The order is `∀ m,τ,D, eventually N, ∀ ω on one common event, ∀ u`; do not move `∀ m,D` inside a single eventual threshold. This supplies actual loop decay even at positive times, not just its zero initial value.

Verified producers and proof route:

- `Gauss/APrimeFirstCellCTDecay.lean:536` proves, **on precisely this event**, for both charges and all `0≤u≤1/2`,
  `‖Gsig ... σ (a,p) (b,q)‖ ≤ 4 exp(-α zdist(a-b))`, with `α=log(65/64)>0`.
- `Gauss/APrimeFirstCellJGActual.lean:124` already proves `HighProb (Gauss.P d) good`; event measurability is `APrimeFirstCellJGAllTime.measurableSet_good:179`. Do not assume a new entry-decay or local-law hypothesis.
- Apply `Decay.loopDecay_gloop`, `Hierarchy/Decay.lean:1685`, with entry radius `R=ell_u*N^τ/(2m)`. Its resulting radius is exactly `ell_u*N^τ`. Since `η_u≥1/2` and `ell_u≥1`, its error is at most `4*2^m*exp(-α*N^τ/(2m))`.
- Apply `Decay.loopDecay_Kgen`, line 1328, at the **constant gap** `δ=1/2`, justified by `u≤1/2` and `Decay.one_sub_le_norm_one_sub`. The primitive error is at most `cKdecay m (1/2)*exp(-cor35Rate (1/2)*N^τ)`. Both constants are independent of `N,u,ω`. Add the errors via `LoopDecay.sub`; absorb their sum into `N^-D` using exponential-over-polynomial decay. For the raw-loop half choose its error small enough for this same absorption.
- Pass to `lkErr * farInd` by the existing `LoopData`/`LoopDecay` bridge used in `LKDecayQuant.highProb_loopDecay_pair`; no LDE or good-diagonal division is needed. `HighProb` plus the pointwise eventual bound gives the stated stochastic domination.
- A bounded search found no current use of `Gsig_entry_decay_on_good` except its true-charge specialization in its own file, and no existing Gaussian consumer of `Decay.loopDecay_gloop`. Thus this is not already implemented by the CT work.

Exact consumers: the `hdec` field of target A, `FastDecayFlow.norm_Psum_lkT_le_of_mem_lkGood:779`, and the actual drift decay/localization work needing length-two `D` and length-three raw-loop decay. A restriction to any `0≤s_N≤t_N≤1/2` is immediate and may be included for convenience, but is not the analytic deliverable. The general moving window with `t↑1` remains open.

Nondegenerate joint certificate: retain the same actual event and use `APrimeFirstCellCTDecay.diagonalWitness` (line 599), its membership theorem (line 613), and `Xmat_diagonalWitness_ne_zero` (line 637), at `u=1/4`. Require `m=2`, strictly positive radius/error, and two **distinct** blocks inside the large growing circle with distance at least the radius, e.g. choose `τ=1/16`, `D=1`. Since `L_N~N^(1/4)` and `ell_(1/4)` is bounded, far pairs exist eventually. This prevents the certificate from relying on the far indicator being identically zero. A HighProb/nonempty certificate for the same event supplies the probabilistic side. The Gaussian is actual and the window length is `1/2`.

## Cutoff nonlinear drift: exact remaining obstacle

The current T596 estimate removes `cutTrunc` with `cutTrunc_le_self` (`XiLKTwoCutMoment.lean:191–197`) **before** the moment Duhamel estimate. Its drift term consequently contains unrestricted moments of `U driftF`. An endpoint cutoff does not give any bound on `xiLK_2` at intermediate times. `CutHypTheta.prefixEvent:1473`, conditional moment field at line 1661, and `moment_of_conditional:970` explicitly distinguish these issues. Restricting the probability measure to the prefix event does not preserve the Gaussian integration-by-parts identity: an actual smooth weight or a stopped-process proof is required.

At length two there is no coupling sum. Retaining the two terms separately gives, on a decay event with radius `ell_u*K` and tail `δdec`, writing `J=xiLK_2`, `X1=xiLK_1`, `Y3=xiL_3`, `A=A_u`,

`|F_u| ≤ 8e (K+2) η_u^-1 A^-3 J²
          + 4e (K+2) η_u^-1 A^-2 X1 Y3
          + W L δdec (4J+2X1)`.

This follows directly from `Decay.norm_loopTensor_primBil_le:1022`, `Decay.norm_loopTensor_eG_le:1040`, and the actual decomposition `DriftDef.driftF_eq_eG_add`. The bounds are already present term-by-term inside `DriftBound.norm_driftF_le:330–365`; exporting only this algebra would be too small and would not close a new consumer.

Two cautions govern any subsequent real drift ticket:

1. **Do not erase `X1`.** The source `DriftBound.lean:40–53` explicitly retains `X1*Y3`; the coarse theorem folds it into `cDrift(n,CK,C1)` assuming `X1≤C1`. T1337 supplies weak local law, not an order-one `xiLK_1` bound. The latter is connected with the separate (4.5) front. Setting `C1=1` from Step 2 is unsupported, and importing Step 3/4 would be circular. This affects the nonlinearity-free source term as well as the quadratic term.
2. **A useful localization target must preserve its support through the generator/moment identity.** On a prefix `J_u≤N^(2δ) A_s^(1/2)`, the quadratic term becomes linear with coefficient `N^(2δ) A_s^(1/2)/A_u`, before transport and the time integral. `Cond272Reg` leaves enough power for a small coefficient if the decay radius is chosen at a suitably small power of `N`; however that algebra is not an actual weighted Duhamel estimate. The currently accepted A-prime smooth weight controls normalized alternating `jSnorm`, not the all-charge `xiLK_2` maximum. An all-charge smooth support estimate plus its generator cross-term budget, or a route avoiding localization entirely, is still needed.

Thus the smallest honest next analytic obligations are (i) control the actual `X1*Y3` source at the final `A_s^(1/2)` scale with running time powers, and (ii) supply the same-weight all-charge generator identity/cross budget that carries the prefix quadratic contraction. I have not verified a complete proof route for either on general moving windows and do not label either dispatch-ready. Group B does discharge an actual spatial-decay prerequisite on the first half interval.

## Scheduler candidates and scope

The scheduler's two separately inspected near-(5.48) candidates are mathematically compatible and independent of A/B and T1339/T1341:

- Retaining `R^-2` in the exact accepted same-weight closed-cell Minkowski estimate is legitimate if the literal initial term is `N^(5λ/32)R^-2`, the raw drift is `O(N^(4λ/1000)R^-2)`, and QV is `O(N^(4λ/1000)R^-4)` before taking the square root. The square root only improves the stated loss. This is a sharper estimate of the same observable, not a new normalization inferred from its already weakened bound.
- Proving that the **identical** canonical smooth weight equals one on a common high-probability event, using accepted weak `JSNormDom` and the literal `widenedW_le_weight_canonical`, is independent of that sharper moment calculation. Quantify `λ` before the event, retain all active `k` and all `p`, and obtain all-`p` plateau from the common hard-prefix bound and the canonical calibration, not an infinite union of p-dependent events. `StochDom` already controls the existential bad event over the entire `TimeIcc`, so restriction to the finite target net costs no cardinality loss. This is the correct input for later deweighting.

I subsequently read the exact `docs/V6-SHARP-NEAR-TICKET-SPECS.md` T1343/T1345 specifications and personally checked `APrimeWeight.piecewiseW_dom_canonical:210`, `piecewiseW_le_widenedW:222`, and `APrimeSmoothWeightActual.widenedW_le_weight_canonical:1253`. The proposed finite-net threshold `N^(2λ)` matches the first theorem's literal `prefNet` threshold. The latter comparison has canonical cutoff parameter `2`, matching the specified actual weight. There is no mathematical objection to releasing these two bounded targets. This confirms the stated inputs and inspected comparisons; I did not repeat the scheduler's full Minkowski-source preflight. Eq45 actual conditional rows, the general moving LKDecay quantifier repair, Eq548 final assembly, and the Q/nonalternating Lemma 5.14 RHS remain separately held.
