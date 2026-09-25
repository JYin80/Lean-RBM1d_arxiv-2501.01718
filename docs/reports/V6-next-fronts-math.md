# V6 next mathematical fronts — bounded read-only investigation

Date: 2026-09-24. Scope: actual Gaussian `Dims.exampleGrow`, after the accepted
T1337/T1338 local Step-2 result. This is a mathematical preflight, not a Lean
proof or an acceptance certificate. No Lean source, shared scheduler document,
root import, or git state was changed. Only the prescribed
`paper/250520-YinJun-v2.pdf` was consulted; its text was extracted directly with
`pypdf` for this investigation.

## Recommendation

Select **one major front: the actual all-charge two-loop cutoff input**. Two
independent, bounded source targets are mathematically ready:

1. The actual finite-maximum `xiLK ... 2` time modulus on the Gaussian norm event,
   with the literal existing mesh exponent `Kmod=21`, `gamma=1/2`.
2. The literal all-charge QV row of T596, uniformly on the entire moving window,
   at the target `N^(epsilon/4) A_s^(1/2)` scale. A direct Step-1 length-six route
   works for `exampleGrow`; no `EEBridge` decay assumption or frozen all-time
   `hEEmom` envelope is needed.

These are two genuine estimates, not constructors. They can be assigned to two
file-disjoint workers. They do **not** close the remaining nonlinear drift or
`CutHypEvOnSlot`. Keep all four general assembly gaps on HOLD.

## Target 1: actual all-charge modulus

Suggested exclusive file: `RBM1D/Gauss/XiLKTwoCutModulus.lean`.

The exact main target can be stated for any `d : Dims` (or conservatively for
`exampleGrow`):

```lean
theorem xiLK_two_event_modulus
    (d : Gauss.Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω : Gauss.Ω d, ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ) →
      ∀ v ∈ Set.Icc (s N) (t N),
      ∀ w ∈ Set.Icc (s N) (t N),
        |(Gauss.sample d).xiLK E N v ω 2 -
          (Gauss.sample d).xiLK E N w ω 2| ≤
        (N : ℝ) ^ (21 : ℝ) * |v - w| ^ ((1 : ℝ) / 2)
```

Also deliver measurability of this exact `xiLK` for every fixed `N,u` and a
joint positive-window witness for the event, modulus, and existing
`meshK 21 (1/2)` mesh/cardinality inequalities. Do not assume the cutoff moment
in this file and do not manufacture a `CutHypEvOn` record missing its moment.

### Exact source path and absence of duplication

* `Gauss.hHol_flow`, `Gauss/Lemma514Holder.lean:721`, already controls every
  charge/label **coordinate** `A_u^m * ||lkT_u(sigma,a)||`. It does not control
  the finite maximum `Sample.xiLK`; that actual finite-maximum transfer is not
  present in the searched sources.
* Use its `c=2,m=2` specialization: `2*(3*2+4)+1=21`. The source permits
  `s=0`; its assumptions only require `0 <= s`.
* `Cond272Reg` gives the polynomial endpoint floor. The generic theorem
  `Gauss.rpow_neg_one_le_one_sub_of_scale_ge` used by
  `APrimeGeneralMovingWindowFloor.eventually_endpoint_floor` yields
  `(1-t_N)^(-1) <= N` eventually. Absorb the fixed bulk factor to obtain
  `eta_t^(-1) <= N^2`. On the event `||X|| <= N`, also `||X||+1 <= N^2`.
* `Gauss.norm_Kval_two_le_rpow`, `Lemma514Holder.lean:1074`, supplies the exact
  length-two K envelope on `[0,t_N]`. Weaken its exponent to 2, matching the
  two other inputs of `hHol_flow`.
* `Sample.lkMax` is the finite `iSup` over all `LoopData L 2`, and `xiLK` is
  that maximum times `scale^2` (`Hierarchy/Step3.lean:781–786`). Multiplication
  by the nonnegative `scale^2` commutes with this finite maximum. The inequality
  `|max_q a_q(v)-max_q a_q(w)| <= max_q |a_q(v)-a_q(w)|` costs **no cardinality**.
* `Flow/Eq548Producer.lean:192` has `measurable_Lval` for every real time;
  subtract deterministic K, take norms, and a finite maximum. Do not assume
  `Im z != 0` for this all-real-time measurability field.
* `Gauss.highProb_normX_le d (Gauss.traceMomentBound_gauss d)` supplies the
  explicit event. Existing `mesh_fine_at_meshK`, `card_le_at_meshK`, and
  `eventually_one_le_flowAs_rpow_half` fit `Kmod=21`, `gamma=1/2`, `Ccard=43`.

Named consumer: `MomentDuhamelCut.CutHypEvOn.modulus` and `.meas` inside
`CutHypEvOnSlot` (`Flow/Step345Producer.lean:749`). The moment field remains
independent and open.

## Target 2: the literal all-charge T596 QV row

Suggested exclusive file: `RBM1D/Gauss/XiLKTwoCutQV.lean`.
Let `d := Gauss.Dims.exampleGrow`. Suggested exact main signature:

```lean
theorem twoCoord_qv_momNorm_le_cut_scale
    {κ E c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    ∀ ε > (0 : ℝ), ∀ P : ℕ, 1 ≤ P →
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∀ v ∈ Set.Icc (s N) (t N),
        ∀ q : LoopData (d.L N) 2,
          (Gauss.band d).scale E N v ^ 2 *
            (MomentDuhamel.cMDval' P 0 *
              ∫ u in (s N)..v,
                MomentDuhamel.momNorm (Gauss.band d).P P (fun ω =>
                  ‖Uker (d.L N) (SumZeroDyn.xi2 E q.1)
                    ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (MomentDuhamel.eeFun (Gauss.band d) E N u
                      ((Gauss.sample d).H N u ω) q.1)
                    (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
            ≤ C * ((N : ℝ) ^ (ε / 4) *
              (Step3.flowAs (Gauss.band d) E s N ^ ((1 : ℝ) / 2)))
```

The namespace is exactly `RBM.MomentDuhamel.cMDval'`, verified in
`MomentDuhamelHypGauss.lean:2120`; its `cMDval'_of_one_le` at :2127 gives
`2*(2P-1)` for `P>=1`. This is the literal coefficient in
`XiLKTwoCutMoment.twoCoordDuhamelRhs`. No change of coefficient is allowed.

Require a net corollary with **exactly** `netFinset s t (meshK 21 (1/2))`, so
this is directly the third summand in T596. The whole-window theorem is useful
for avoiding a new endpoint-uniformity quantifier gap. Require actual
interval integrability, using
`Gauss.intervalIntegrable_momNorm_eeFun_gauss`
(`Gauss/MomentDuhamelHypGauss.lean:1862`); do not let a nonintegrable Bochner
integral disappear to zero. Include `v=s_N` (integral zero) and a joint
strict-positive-window witness.

### A complete mathematical estimate, without decay premises

Write
`A_u = W ell_u eta_u`, `mu=Im(mE E)>0`, and
`R_sv=(1-s_N)/(1-v)=eta_s/eta_v`.

1. Obtain `Step1.Hyp` from `Gauss.step1Hyp_slot`; apply
   `Step1.apriori` at length **6** (`Hierarchy/Step1.lean:812`). Its exact
   unweighted source is

   `||L_{u,charge,label}|| prec (ell_u/ell_s)^5 A_u^(-5)`.

   Use `Gauss.momNormDom_of_stochDom` on the index
   `TimeIcc s t N × LoopData L 6` to retain the running `u` in this scale.
   The scale is bounded below by `N^-5` eventually, because `ell_u/ell_s>=1`
   and `A_u<=N`; the deterministic resolvent envelope is polynomial since
   `eta_u^-1<=N^2`. Measurability and every fixed power's integrability follow
   from `continuous_gloop_Hflow` and the deterministic resolvent envelope.
   The reverse bridge gives even norms; apply Lyapunov to get the required
   order `P` norm, retaining the same running profile. Thus, for every fixed
   `a>0,P>=1`, uniformly in all `u` and all six-loop coordinates,

   `||L_u||_P <= C_(a,P) N^a (ell_u/ell_s)^5 A_u^(-5)`.

2. Apply the exact finite sum in
   `EEDef.norm_eeFun_le_W_sum` (`Hierarchy/EEDef.lean:189`) with `m=2`.
   Every glued loop has length 6; the SB row absolute sum is 1. Minkowski
   therefore yields, for every charge `sigma` and all four output labels,

   `||eeFun_u(sigma)||_P <= 2 W L C_(a,P) N^a (ell_u/ell_s)^5 A_u^(-5)`.

   The explicit factor `L` is retained. No fast-decay hypothesis and no
   `EEBridge.stochDom_norm_eeField` invocation is necessary.

3. Apply `Gauss.momNorm_Uker_apply_le`
   (`Gauss/MomentDuhamelRhs.lean:265`) at tensor length **4**, order `P`, and
   `xi=SumZeroDyn.xi2 E sigma`. Each coordinate phase has norm at most 1.
   The kernel row mass costs exactly `R_uv^4`. Do **not** use the sum bound
   `APrimeQVEndpoint.norm_Uker_eeFun_le_ratio` literally: that version retains
   an extra sum over all four output indices. Minkowski with the kernel mass
   avoids an unnecessary `L^4` cost.

4. There is an exact cancellation **before integration**:

   `A_v^4 R_uv^4 W L (ell_u/ell_s)^5 A_u^(-5)`
   `= (L/ell_s) (ell_v/ell_s)^4 eta_u^(-1)`.

   Thus the square of the normalized QV row is at most

   `2 cMDval'(P,0) C_(a,P) N^a`
   `  * (L/ell_s) (ell_v/ell_s)^4 log(R_sv)/mu`.

   `integral_etaT_inv_eq` in `Gauss/Lemma514NonAlt.lean:1346` verifies the
   logarithmic integral. This scalar identity also follows directly from
   `eta_u=mu*(1-u)` and has no Step-3 dependence.

5. The `exampleGrow` arithmetic gives `L^3<=W` eventually: for `N>=81`,
   `L^4<=N` and `W=floor(N/L)` by `Dims.growL_pow_le` and `Dims.growW_eq`
   (`Gauss/DimsExample.lean:133,151`). In particular `L^2<=W`.
   The piecewise formula `ell_s=min((1-s)^(-1/2),L)` gives

   `L/ell_s <= mu^(-1/2) A_s^(1/2)`

   eventually. In the unsaturated case,
   `A_s=mu W/ell_s` and `mu*(L/ell_s)^2<=A_s` uses `L^2<=W` and
   `ell_s>=1`. In the saturated case `L/ell_s=1`, and `A_s>=1`, `mu<=1`
   suffice. This is the only special-dimension estimate in the route.

6. From (2.72), `R_sv^30<=A_v<=A_s`. Also `ell_v/ell_s<=R_sv`, and
   `0<=log R_sv<=R_sv` since `R_sv>=1`. Taking square roots bounds the row by

   `C_(E,a,P) N^(a/2) A_s^(1/4) R_sv^(5/2)`
   `<= C_(E,a,P) N^(a/2) A_s^(1/3)`
   `<= C_(E,a,P) N^(a/2) A_s^(1/2)`.

   Set `a=epsilon/2`. This is the exact requested loss `N^(epsilon/4)`.
   All constants and the moment order are fixed before `eventually N`; its
   threshold is uniform in the entire `v` and all charge/label families.

### Why this is not already proved and what it does not claim

T596 has the actual QV integrand but no absorption. T608 handles the transported
initial row only. Existing A-prime QV budget modules select `Step2.sigPM` and
use smooth weights; this target has all four charges, raw unweighted moments,
and exactly the `xi2` QV term of T596.

No cutoff support is needed to estimate this QV row. It does **not** solve the
raw drift obstruction: at length 2 the latter contains
`A_u^-1 * xiLK_u(2)^2`, and T596 discarded the cutoff before forming its raw
Duhamel RHS. Neither this QV estimate nor the new modulus supplies the missing
all-charge stopped/smooth-cutoff drift inequality.

The all-charge finite maximum later costs `4L^2` in the T596 family inequality.
The final moment assembly must choose higher order `P>=max(p,4/epsilon)`
before `eventually N` and use Lyapunov; it cannot absorb `4L^2` at the original
fixed order. That later assembly is not part of this ticket.

## Joint witnesses and file ownership

For both files, specialize the actual `exampleGrow` Gaussian sample to the
accepted positive first window already witnessed by
`APrimeFreeLossGaussianStep2.positive_window_joint_step2_witness` and its
`base` data (ultimately `positive_length_common_support_witness`). Retain the
same `s,t,c`, `Cond272Reg`, incoming `BoundsCore`, and eventual `s_N<t_N`.
Intersect its common event with `||Xmat||<=N` for the modulus if a combined
resident is desired; both are high probability for the same sample. This is a
witness for the **complete hypotheses actually used**, not a geometry-only
placeholder for a new moment assumption. Keep the modulus file and QV file
independent; each gets a separate report and independent final audit.

## Other fronts: reason to hold them

* **Random-scale later-cell (4.5):** productive as a future second main front,
  but no full fixed-time random-scale fluctuation proof was verified here.
  The net and slow-control pieces already exist:
  `Eq45FlowInputs.stochDom_timeIcc_of_unifDom` and
  `Lmax_flow_slow_of_net`; dispatching another net adapter duplicates them.
  The missing estimate is the actual same-sample `UnifDomIcc` bound for
  `sum_k S_ik (G_kk-condExpDiag_k)` and the block average with control
  `Lmax(H_u(omega),z_u)`, together with the actual IBP remainder.
  `CondStableInst.LmaxRowProxy` is fixed-time; its `W^-1` construction pays
  `eta^-2` when time moves. A row-minor random proxy would be useful, but is
  not a substitute for the missing fixed-time fluctuation moments. T1333
  rules out only the canonical deterministic-majorant route. Paper (4.5)
  uses random `Psi^2=Lmax`, as confirmed directly in the paragraph preceding
  (4.12).
* **All-order Lemma 5.14:** paper (5.92) removes the eta-ratio loss using
  nonalternating and sum-zero arguments. The exact accepted consumer
  `lemma514Q_forall_of_hHol_flow` (`Lemma514QAssembly.lean:560`) still needs
  actual Q and nonalternating RHS budgets and `PHalf514`. Its
  `pHalf514_of_wardP` source at :314 assumes `0<s_N`; it does not cover the
  first cell. The new two-loop modulus is not an all-order budget.
* **(5.48):** the paper has a near term with `R^2` and a far term with no R.
  `Eq548EntryDataEvOnK'` still places one `(Kmod,gamma)` outside its internal
  `forall D`. Choosing `Kmod=D-1` separately for each D does not instantiate
  this record. A correctly quantified new package and actual near/far moments
  would be needed; an adapter is not an analytic producer. The old swapped-
  sample no-go does not refute the actual Gaussian package universally.
* **High-q/general moving:** the accepted same-loss T1331 family already
  covers the exact moving family consumer; the old short/extended-range
  high-q transport theorems cover only their stated ranges. No independent
  unfilled downstream consumer was found that justifies extending those
  transports in parallel with the two actual cutoff targets.

The paper dependencies used are (2.72), (2.73), the Duhamel/QV formulas
(5.21), (5.22), (5.24), and the cutoff/net discussion (5.43)–(5.46). The
proposed estimates concern the actual Lean radial Gaussian flow, not a new
identification with the paper's Brownian stopped process.
