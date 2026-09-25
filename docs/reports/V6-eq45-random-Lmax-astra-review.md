# V6: independent review of the random-Lmax (4.12)/(4.5) route

## Verdict and release boundary

**Primary verdict: conditional on the uniform pre-(4.5) entry-law input.** The
random-normalization argument in the deferred appendix of T328 has a valid
internal mathematical implementation. Its essential higher-difference and
shared-minor arguments survive this independent audit. Sections 3-7 below give
the derivation, including a repair of the proxy's moment-order bookkeeping.
Neither [40] nor a new random-layer axiom is needed.

This is a mathematical proof of an implication with explicitly stated entry
inputs, not an accepted Lean producer for every later cell. In particular:

* T405/T406, T331's addendum, `fixedTimeFAStatement_proved`, and
  `detAvgIBP_stochDom_of_localLaw_complete` prove deterministic-scale results.
  They do not already prove the random-scale implication reviewed here.
* The corrected random-scale core is ready for **one bounded implementation
  target**, specified in section 10. Its hypotheses have a common, positive-time
  actual Gaussian witness. The theorem is quantified over arbitrary `Dims`;
  only the concrete witness uses `Dims.exampleGrow`.
* **HOLD full later-cell / `Eq45FlowInputs` acceptance.** The source of the entry
  hypotheses on each actual later cell and the frozen assembly's stronger
  unconditional `h45i` signature remain separate obligations. The present
  review supplies neither a compiled producer nor an unconditional later-cell
  good-event witness. A positive first-cell witness cannot replace those.

T1333's canonical-majorant obstruction and the historical failures recorded in
T852 remain valid. No historical report or verdict was edited. This report
does not certify A-prime, full Eq45, or full-paper closure.

## 1. Claim card and exact consumer

Use the actual `Gauss.P d`, `Gauss.Hflow d N u omega`, and row integration
`P_i = condRow`; set `Q_i = 1-P_i`. Here `d : Gauss.Dims` is arbitrary, the
matrix index is `ZMod (d.L N) x Fin (d.W N)`, and its cardinality `n_N=W_N L_N`
satisfies `n_N <= N <= 2 n_N` eventually. In particular `W_N <= N`, `L_N <= N`
eventually, and `W_N >= N^(1/2+d.c)`, with fixed `d.c>0`. No assertion uses
these eventual bounds at `N=0`.

Fix `0<kappa<=1`, `|E|<=2-kappa`, and deterministic sequences
`0<=s_N<=t_N<1`. Require `eta_(t_N)>=N^(-K)` eventually, with fixed `K>=0`.
For `u in [s_N,t_N]`, write

```text
G = green (Hflow d N u omega) (zt E u),
m = mE E,                 v_i = G_ii-m,
Gamma = Lmax(Hflow d N u omega, zt E u)
      = max_(a,b) W^(-2) sum_(x in I_a,y in I_b) |G_xy|^2,
Z_i = Q_i v_i,            x_i = P_i v_i.
```

The entry inputs used in this audit are, uniformly in deterministic `u`:

```text
(WLL) max_(i,j) |G_ij-m delta_ij| prec (N+2)^(-a),  a>0 fixed;
(REL) max_(i,j) |G_ij-m delta_ij|^2 prec Gamma.
```

The uniformity means `UnifDomIcc`: the eventual threshold comes before all
`u` and finite labels. Polynomial finite-label union bounds turn the component
version into the displayed maxima. These are hypotheses about the actual
Gaussian entries, not scalar profiles or prospective FA conclusions. (REL) is
the pre-averaging entry estimate (4.2)/(4.3), after removing the weak-law
indicator and absorbing its finite neighboring-block sum and `W^(-1)` term.
It must actually be supplied at a use site.

For deterministic weights `w`, possibly complex, with

```text
max_i |w_i| <= W^(-1),       sum_i |w_i| <= 1,
```

the proved analytic conclusion is

```text
sum_i w_i Z_i prec Gamma.                                     (RFA)
```

This covers both required real coefficient families:
`w_k=Sblk i k` and `w_k=blkCoef a k`. It does not put a samplewise supremum
over the entire weight class inside the probability.

The literal consumer is `Eq45FlowInputs` in
`Flow/Step345Producer.lean:181`. Its one auxiliary field must work in all three
conjuncts. With `x=condExpDiag`, `Eq45Flow.lean:153-180` requires:

```text
IBP:  |x_i-u m^2 sum_k S_ik v_k| prec Gamma;
row:  |sum_k S_ik (v_k-x_k)|     prec Gamma;
block:|sum_k blkCoef_a(k)(v_k-x_k)| prec Gamma.
```

Time belongs to the index of `StochDom`, hence all three eventually hold on
one sample simultaneously for every time. Section 8 checks that upgrade.
The final consumer `StepGlue.flow_hs1` only uses the alternating two-loop
restriction of its packaged length-two input; this agrees with V6 preflight
section 5. That observation does not itself produce these three inputs.

## 2. What the existing proofs establish

`DetFlucAvg.lean:33` and `DetFlucAvgComplete.fixedTimeFAStatement_proved` have
deterministic `Psi : Nat -> Real`, with

```text
W^(-1/2) <= Psi_N <= N^(-a),   eta_(u_N)>=N^(-K),
LocalLawUnifIcc d E u u Psi,
```

and conclude both averages at `Psi_N^2`. The finite budgets and order
`fixed p -> eventually N` are sound. This is a genuine general-`Dims`,
moving deterministic-time theorem; it is not restricted to fixed real time.
Its denominator, however, is deterministic. Allowing its parameters to depend
on time does not introduce correlation with a small realized `Gamma`.

`DetIBPWeighted.unifDomIcc_condExpDiag_weighted` retains the variance weight of
the diagonal exception and proves the residual at deterministic `Psi^2`.
`DetAvgIBPFlow.detAvgIBP_stochDom_of_localLaw_complete` assembles this with FA.
These valid results are narrower than the current random-scale target.

`CondStableInst.condStable_Lmax` uses the fixed-real-time sandwich

```text
(4W)^(-1) <= Gamma <= eta_t^(-2)/W
```

on the weak-law event. Its proof absorbs the fixed constant `eta_t^(-2)`.
It cannot be instantiated at `t=t_N` by silently treating that constant as
uniform. The proxy construction below avoids this loss.

T1333 formally rules out a different proposed conversion. On its actual
`exampleGrow` later cell with `alpha=1/480`, a deterministic majorant of
`(W ell_t eta_t)^(-1/2)` forces

```text
4 W Psi_N^2 >= 2 N^(5/3840)
```

eventually. This contradicts the literal all-positive-epsilon `hPsiW` premise
of `Eq45FlowGrid.eq45FlowInputs_of_localLaw_gain_budget'`. It does not refute
(RFA), the proxy below, or paper (4.5).

The authorized PDF states (4.12) at the random two-loop scale and cites [40].
That citation is not used as a proof input here. T328's deterministic main
verdict, T331's addendum, and the bounded deterministic averaging portions of
T405/T406 are kept distinct from T328's deferred random-control appendix.
The latter, not their earlier PASS labels, is the argument audited below.

## 3. Common entry event and the corrected smooth proxy

Fix a finite deletion/moment budget first. From (WLL)/(REL), for any small
fixed `b>0` there is a fixed-time event `E_N(u,b)` on which

```text
max_i |v_i|, max_(i!=j) |G_ij| <= N^b sqrt(Gamma),
max_(i,j) |G_ij-m delta_ij| <= (N+2)^(-a/2),
c/W <= Gamma <= N^(-a0),
```

eventually, where `c>0` and `a0>0` are fixed. Its failure probability is
smaller than any fixed inverse power of `N`, uniformly in `u`. The last
line follows from the second line: the diagonal contribution gives
`Gamma>=1/(4W)`, while
`Gamma <= (1+delta)^2/W+delta^2`, `delta=(N+2)^(-a/2)`.
Choose, for example, any `a0<min(a,1/2+d.c)` and absorb constants eventually.
The event definition is independent of the requested failure exponent.

For a deleted set `S`, use the actual principal-minor resolvent embedded by
zero in the original index set. Keep the original blocks and normalization:

```text
Gamma_ab^S = W^(-2) ||1_a G^S 1_b||_HS^2.
```

Fix once and for all a deterministic even integer function

```text
q_N = 2 ceil(2 log(N+2)) + 8,
lambda^S = [W^(-q_N) + sum_(a,b) (Gamma_ab^S)^(q_N)]^(1/q_N).
```

For all sufficiently large `N`, `q_N>=log(L_N^2+1)`, and for each fixed
budget `M`, eventually `q_N>=4M`. Thus

```text
max(W^(-1), max_ab Gamma_ab^S)
 <= lambda^S <= e max(W^(-1), max_ab Gamma_ab^S).             (P0)
```

This repairs a quantifier ambiguity in T328. There the suggested `q` depended
on the moment budget before the statement `S_w prec 1`; literally different
moments can then describe different `S_w`. The present choice defines the
same proxy family for all fixed moments, including when `L_N` is bounded.
Only the proof's eventual threshold depends on the moment budget. Alternatively
one could avoid asserting domination of a common auxiliary variable and
transfer each fixed-moment estimate separately. No repair of the main scale
or loss is required.

`lambda^S` is measurable, is row-i-free for every `i in S`, and has the
global lower bound `W^(-1)`. Every minor resolvent has norm at most `eta^(-1)`.
Consequently `lambda^S`, its inverse, all normalized variables below, and all
their fixed finite differences have polynomial envelopes, uniformly in `u`.
No inverse diagonal is bounded on the entire probability space.

## 4. Audit of the higher finite differences

Write `Delta_k F^S=F^S-F^(S union {k})`, with distinct fresh deletion labels.
All estimates below have a fixed finite total deletion budget; no all-orders
bound at one `N` is asserted. On `E_N(u,b)` put `A=N^b sqrt(Gamma)`.
Choose `b` sufficiently small after the budget so that all subsequent fixed
powers of `N^b` times `sqrt(Gamma)` tend to zero.

### 4.1 Embedded rank-one identity and boundary rows

The exact identity is

```text
Delta_k G^S = G^S_:k G^S_k: / G^S_kk.                         (R1)
```

It also holds on row or column `k`: the embedded later minor is zero there,
and the right side equals that original row or column. Thus the argument
does not discard the diagonal term when a deleted label lies in a block.
All surviving minor diagonals stay bounded and bounded away from zero by
iterating the scalar recursion `delta -> delta+2 delta^2`, for a fixed number
of steps. Surviving off-diagonal and centered diagonal entries have bound
`C_M N^(C_M b) sqrt(Gamma)`.

For every endpoint column and row,

```text
W^(-1) ||1_a G^S_:k||_2^2 <= C_M N^(C_M b) Gamma,
W^(-1) ||G^S_k: 1_b||_2^2 <= C_M N^(C_M b) Gamma.
```

The possible diagonal entry costs `C/W<=C Gamma`; the other entries use the
off-diagonal bound. Hence (R1) has normalized block HS norm at most
`C_M N^(C_M b) Gamma`, with no factor `W` left over.

### 4.2 Induction with fresh labels

For `T` disjoint from `S`, `r=|T|>=1`, repeated discrete product rules give

```text
W^(-1)||1_a Delta_T G^S 1_b||_HS
 <= C_M N^(C_M b) Gamma^((r+1)/2),                          (Rr)
|Delta_T G^S_ii|
 <= C_M N^(C_M b) Gamma^((r+1)/2),  i outside S union T.    (Dr)
```

Here is the degree invariant behind this induction. Each block term consists
of two endpoint vectors, internal off-diagonal entries between distinct
deletion vertices, and inverse surviving diagonals. The two normalized
endpoint norms each cost `sqrt(Gamma)`. A new difference of an endpoint
inserts a new endpoint and one internal off-diagonal entry. A difference of
an internal edge replaces it by two. Both gain `sqrt(Gamma)`. For inverse
diagonals the exact rule is

```text
Delta_k (1/G_jj^S)
 = -G_jk^S G_kj^S /
       (G_jj^S G_jj^(S+k) G_kk^S),                         (I1)
```

which gains `Gamma`, a stronger gain. The new `k` is distinct from earlier
internal vertices. Block-vector coordinates can equal `k`; (R1) already
handles those coordinates, so no false off-diagonal assertion is made about
an endpoint vector. For (Dr), the two scalar endpoints are off-diagonal
because `i` is not deleted. Shifted factors retain the same type of bounds.
There are only finitely many terms depending on `M`.

For `r=0`, the normalized block norm is `O(sqrt(Gamma))`: it follows first
for the full matrix by definition, then for minors by summing the first
differences. The centered scalar diagonal has the same bound. These
observations supply the base cases absent from a purely positive-order count.

### 4.3 Loop powers and the smooth-norm chain rule

Apply the discrete product rule to the HS inner product. For `1<=r<=M`,

```text
|Delta_T Gamma_ab^S|
 <= C_M N^(C_M b) Gamma^(1+r/2).                           (Lr)
```

Splitting the `r` labels between the two matrix factors gives exponent
`(1+r_1)/2+(1+r_2)/2=1+r/2`, also when one part is empty.
In particular all finite-minor maxima differ from the original `Gamma` by
`O_M(N^(C_M b) Gamma^(3/2))`. Together with (P0), this proves
`lambda^S comparable to Gamma` on the **same original sample's event**.

For positive vectors including the floor coordinate, the `j`th derivative
of `F(v)=||v||_q` obeys

```text
|D^j F(v)[h_1,...,h_j]|
 <= C_j q^(C_j) ||v||_q^(1-j) product_l ||h_l||_q,
|D^j F^(-1)(v)[h_1,...,h_j]|
 <= C_j q^(C_j) ||v||_q^(-1-j) product_l ||h_l||_q.
```

Differentiate `sum v_l^q` and its `1/q` power. Each multilinear sum is bounded
by Holder with total reciprocal exponent one; `q>=4M` suffices. The chain
rule has only finitely many partitions at fixed derivative order. The power
of `q` depends on that order, not on the number of blocks.

Use the multi-affine interpolation of the cube of loop vectors
`(Gamma_ab^(S union U))`, `U subset T`, including the constant floor
coordinate. A mixed derivative of this interpolation is a convex combination
of the corresponding exact differences in (Lr). Its q-norm therefore has
the stated bound, since `(L^2+1)^(1/q)<=e`. At any interpolation point at
least one vertex coefficient is at least `2^(-r)`; all coordinates are
nonnegative. The interpolated norm is thus bounded below by `2^(-r)` times
that vertex norm, and is comparable to `Gamma`. The multivariable fundamental
theorem of calculus and the preceding derivative bounds prove

```text
|Delta_T lambda^S| <= C_M q_N^(C_M) N^(C_M b) Gamma^(1+r/2),
|Delta_T (lambda^S)^(-1)|
 <= C_M q_N^(C_M) N^(C_M b) Gamma^(-1+r/2).                 (Pr)
```

This verifies T328's critical proxy lemma. The hard maximum would not suffice:
the mixed second difference of `max(1+h x,1+h y)` on a binary square is
`-h`, even though each branch has zero mixed second difference. This is a
counterexample to that shortcut, not to (Pr) or to the Gaussian theorem.

## 5. Exact centering, resampling, and normalized moments

For `i outside S`, define

```text
Y_i^S = (G_ii^S-m)/lambda^(S union {i}),
X_i = Q_i Y_i^empty = Z_i/lambda^{i}.
```

The equality is exact because the denominator is row-i-free. The deleted
set in every denominator includes `i`; reserve that label in the fixed
minor budget. In the `n=2p`-slot expansion all labels lie in the tuple's
distinct-label set `R`, so budget `n` suffices; using a larger fixed budget
does not affect any exponent.

Combining (Dr)/(Pr) by the discrete product rule gives, for distinct
`T` outside `S union {i}`,

```text
|Delta_T Y_i^S|
 <= C_M q_N^(C_M) N^(C_M b) Gamma^((|T|-1)/2).              (Yr)
```

In particular the costs for zero, one, and two extra differences are
`Gamma^(-1/2)`, `1`, and `Gamma^(1/2)`. Globally the original normalized
minor expression is bounded by `W(eta^(-1)+1)`; its finite difference by
`2^M` times this. These raw expressions, not their rational expansions, pay
the bad-event contribution.

The coordinate projections commute, including the coordinates shared by
two Hermitian rows: integrating the overlap twice is idempotent.
Deleted-row measurability and `P_i Q_i=0` are exact. They agree with the
internal identities in `CondRow`, `FlucIter`, and `FlucIterHigh`.

Expand the `n=2p` moment of `sum_i w_i X_i`. For each tuple, let `a` be its
number of singleton labels and `d0` its number of distinct labels. Pivot
each singleton `k`: leave its unique centered slot unchanged and insert
`P_k+Q_k` into all other slots. The all-`P_k` branch has zero expectation
over the full Gaussian space. Every surviving branch adds `Q_k` to another
slot. Earlier centers and extra Q letters persist by commutation. Thus if
`T_h` is the set of extra Q labels on slot `h`,

```text
d_extra = sum_h |T_h| >= a,      d0 <= (n+a)/2.
```

There is no repeated label counted as a fresh difference. Use the exact
identity `Q_T Y_i^empty = Q_T Delta_T Y_i^empty`: every nonempty deleted
term is annihilated by one of its deleted-row Q operators. Commute the other
projection letters outside it. This is the existing singleton-pivot
mechanism applied to different, row-normalized variables; the current
deterministic `FlucGainUpTo'` conclusion is not being instantiated with a
random scalar.

Expand Q as `1-P` and represent the remaining projections using independent
auxiliary Gaussian coordinate copies. There are at most `C_n` transformed
samples per branch. Every transformed full sample has the original Gaussian
law. All transformations resample only rows in the tuple's `R`, so the
**same** `G^R` and `lambda^R` are unchanged in all factors. On the joint good
event, (Yr) consequently bounds the entire product by

```text
C_n q_N^(C_n) N^(C_n b) (lambda^R)^((d_extra-n)/2)
 <= C_n q_N^(C_n) N^(C_n b) W^((n-a)/2).                   (J)
```

The last inequality uses both `W^(-1)<=lambda^R` and `lambda^R<=1`
eventually on that event. Positive and negative random powers are combined
before either bound is used. Applying separate global bounds to the factors
would lose this cancellation.

The joint bad-event probability is at most `C_n N^(-B)` by the original
marginals, without assuming independence among transformed samples. The
global polynomial envelope makes its expectation smaller than `N^(-A)` for
any prescribed fixed `A`, by choosing `B` after `n,K,A`. Good-event indicators
are inserted only at this estimation stage, after every exact cancellation.

For each equality partition the absolute coefficient mass is at most
`W^(-(n-d0))`, because
`|w_i|^r <= W^(-(r-1)) |w_i|` and `sum |w_i|<=1`. Since
`n-d0 >= (n-a)/2`, it cancels (J). This includes zero weights and all
collisions. For `n=4`, the five partition types give total bandwidth powers
`W^(-1), W^(-1/2), 1, 1, 1` for `4, 3+1, 2+2, 2+1+1, 1+1+1+1`, respectively.

There are finitely many partitions and branches for fixed `p`. Choosing `b`
after `p` and the requested loss, and absorbing the fixed power of
`q_N=O(log N)`, proves

```text
for every fixed p>=1 and epsilon>0, exists C>0, eventually N,
uniformly in u and each deterministic admissible w,
E |sum_i w_i X_i|^(2p) <= C N^epsilon.                     (M)
```

This proves the random-scale gain internally. It is not a renamed
deterministic-Psi theorem or a moment estimate against an independent copy
of `Gamma`.

## 6. Recovery of the original random denominator

The first-difference case of (Pr) gives

```text
|1/lambda^empty - 1/lambda^{i}| <= N^epsilon Gamma^(-1/2)
```

on the common good event, with arbitrary small fixed loss. To bound `Z_i`
without assuming conditional stability, use

```text
Z_i/sqrt(lambda^{i}) = Q_i[v_i/sqrt(lambda^{i})].
```

The right side has every fixed moment at arbitrary small polynomial loss:
use the entry event and same-sample proxy comparison for the input, its
polynomial envelope on the complement, then conditional Jensen. This is
legitimate because its denominator is row-free.

Set `R=Gamma+W^(-1)`. A useful stronger output than domination is

```text
E [ |sum_i w_i Z_i| / R ]^(2p) <= C_(p,epsilon) N^epsilon.  (RM)
```

Indeed write

```text
(sum_i w_i Z_i)/lambda^empty
 = sum_i w_i X_i
   + sum_i w_i [Z_i/sqrt(lambda^{i})]
       [sqrt(lambda^{i})(1/lambda^empty-1/lambda^{i})].
```

Each bracket in the second term has the required fixed moments: the first
by Jensen, the second by (Pr) and its global polynomial envelope. Holder at
twice the desired moment order and the coefficient l1 bound control this
error. Globally `lambda^empty/R<=e` eventually by (P0), proving (RM).
On the weak-law event `R<=5 Gamma`; Markov and the negligible complement
give the literal random control (RFA). The floor is a proof device only and
does not replace `Gamma` in the final conclusion.

## 7. IBP is a separate, verified analytic arrow

The first-order proxy comparison also proves conditional preservation. If
`F` has a polynomial global envelope and `|F| prec Gamma^r` for fixed
`r>=0`, then

```text
|P_i F| prec Gamma^r
```

uniformly over the required finite labels and deterministic times. Normalize
by `(lambda^{i})^r`, apply conditional Jensen, and transfer back using the
same-sample comparison. The floor supplies the polynomial inverse envelope.
This argument also proves the moving-time fixed-time bound
`P_i Gamma prec Gamma`. It uses no factor `eta_t^(-2)` as a multiplicative
loss and does not assert that `Gamma` is itself row-independent.

The actual complex Gaussian IBP identity is

```text
x_i = u m sum_k S_ik P_i[v_k G_ii]
    = u m^2 sum_k S_ik P_i v_k
      + u m sum_k S_ik P_i[v_k v_i].
```

The second sum is `O_prec(Gamma)` by (REL), conditional preservation, and
`sum_k S_ik=1`. For `k!=i`,

```text
G_kk-G_kk^{i}=G_ki G_ik/G_ii = O_prec(Gamma),
P_i v_k-v_k = O_prec(Gamma).
```

The latter follows because the minor term is row-i-free. Off the good
event use the raw difference's bound `2 eta^(-1)`, not a claimed global
bound for `1/G_ii`. For `k=i` the difference is `-Z_i`; do not apply a
minor identity to the deleted diagonal. Its coefficient is `S_ii<=W^(-1)`.
Since `Z_i prec sqrt(Gamma)` and `Gamma>=1/(4W)` with high probability,
`S_ii Z_i=O_prec(Gamma)`. Equivalently, the existing weighted two-regime
remainder argument only needs a size-one diagonal bound.

Therefore the literal `IBPFlow` residual at fixed time is `O_prec(Gamma)`.
This part does not use (RFA). Only afterwards use (RFA) with row weights to
replace `v` by `x` in the self-consistent equation, and the established
short-edge stability of `I-u m^2 S` to obtain `max_i |x_i| prec Gamma`.
Block (RFA) then proves (4.5). The stable inverse has a bulk-dependent
constant, not `(1-u)^(-1)`.

This analytic IBP proof is a new use of the row-minor proxy. It is **not**
already the conclusion of `CondStableInst.condStable_Lmax` or
`DetIBPWeighted`. Its formal implementation must remain separately visible
from the two fluctuation estimates.

## 8. Time window, quantifiers, and one event

The moment estimates above are uniform in deterministic `u`: their inputs
use one eventual threshold for the whole interval, and their envelopes use
`eta_(t_N)>=N^(-K)`. Constants depend on fixed parameters and moment orders,
not on `u` or on a chosen good sample.

The existing `Eq45FlowInputs.stochDom_timeIcc_Lmax_of_unifDom'` and its three
wrappers (`ibpFlow_of_unifDom'`, `flucRowFlow_of_unifDom'`,
`flucBlkFlow_of_unifDom'`) accept precisely these random fixed-time controls.
They already separate event threshold `delta` from mesh spacing `mu` and
use the same `flowNetEvent=goodSetFlow intersect {||Xmat||<=N}`. Their
Hölder and `Lmax_flow_slow_of_net'` inputs do not need `hPsiW`.

For completeness, the analytic upgrade chooses a polynomial mesh after
fixing the model/window and tolerance. On the Gaussian norm event, the
resolvent identity gives a polynomial Hölder-1/2 modulus, including `u=0`.
Integrating the resampled-row modulus gives the same type of bound for
`P_i v_i`. Finite block sums give a polynomial modulus for `Gamma`. The
weak-law event gives `Gamma>=1/(4W)>=1/(4N)` eventually. A sufficiently fine
mesh makes interpolation errors smaller than the remaining tolerance times
this floor. The original observables and `Gamma`, not their smooth proof
proxies, are interpolated. The two weight families are time independent.

For a fixed tolerance `tau>0`, define the success event by the weak-law/norm
conditions and the required row, block, and IBP inequalities at the mesh
points with fixed thresholds. This event definition does not contain `D` or
`p`. For each `D>0`, prove its probability estimate by choosing `p` larger
than the net-plus-label exponent divided by a fixed fraction of `tau`.
Then choose small entry tolerances and large exceptional exponents, then
`N_0`. Finite unions and interpolation give one measurable common event
for the continuum. Equivalently, use the existing primed net engine once
its actual `goodSetFlow` source is supplied.

The legitimate order is

```text
d,E,kappa,s,t,a,K and the actual entry hypotheses;
q_N as a deterministic function, fixed independently of moments;
requested tolerance and time mesh / physical event definition;
requested failure exponent;
fixed moment / deletion budget;
small source tolerances and large exceptional exponents;
eventual N threshold;
all deterministic times / finite labels, then continuum interpolation.
```

The moment assertion itself has `p,epsilon` before `eventually N`.
No moment order grows with `N`. The harmless logarithmic smoothing order
`q_N` is not a probabilistic moment order. Positive cells, their endpoints,
and the zero-time endpoint are included. At `u=0`, `G=mI`, so all centered
fluctuations and the IBP residual are zero; the positive-time witness below
ensures the argument is not certified solely by that degenerate case.

The source `Hflow=sqrt(u)X` is the repository's actual Gaussian scaling
flow. Its fixed-time marginals agree with the manuscript flow; it is not a
Brownian path. This report verifies the literal scaling-flow consumer and
does not identify the two path laws.

## 9. Source applicability, witness, and the remaining assembly mismatch

The reconstructed proof applies to **every** `d : Dims` satisfying the
listed hypotheses, including bounded or growing `L`. It never uses the
numerics of `Dims.exampleGrow`. The polynomial eta floor is explicit; no
fixed `t0<1` is smuggled into a later window.

There is a nondegenerate same-event witness for all hypotheses of the bounded
core target. Take the actual first-cell source
`firstCell_localLawUnifIcc_of_step1` / `firstCell_step1_localLaw_witness`,
`d=Dims.exampleGrow`, `E=0`, and its positive `tau'`. Its interval
`[firstCellS tau', firstCellT tau']` starts at zero, has positive length
eventually, and has `eta>=1/2`. The enlarged deterministic scale is exactly
`2 firstCellPsi=W^(-1/2)`. The source gives the weak entry law uniformly,
with a fixed positive polynomial exponent (one may take `a=1/8` eventually).

On the same source weak-law event, `Gamma>=1/(4W)`. The deterministic entry
law at squared scale `1/W`, intersected with that event, therefore gives
(REL). For each fixed source tolerance, intersect these inequalities with
the existing Gaussian norm event. Their complement has arbitrarily small
polynomial probability, so this **one** intersection has positive measure
and is nonempty for all sufficiently large `N`. Every finite-minor/proxy
condition proved above holds for every sample in it; there is no selection
of different samples for different conditions. At any positive interior
time, diagonal variance `u/(3W)` is positive, as are the actual averaging
weights. If desired, intersect with `X_ii!=0` for a fixed diagonal coordinate;
its complement has Gaussian measure zero. This certifies a random source on
a positive interval, not a zero-matrix or zero-time test.

This is a **first-cell** witness. T1333's `k=1` later cell proves the domain
and the deterministic-majorant contradiction only. The inspected evidence
does not supply an unconditional high-probability source event on that
later cell. T328's phrase "on a later ... window under its initial
BoundsCore assumption" is a conditional statement, not such a witness.
It must not be promoted to one.

There is also a precise consumer mismatch. For example,
`Step345Producer.thm221NoEL_of_inputs_mergedOnAll_gauss` quantifies `h45i`
over all `E,s,t,c` satisfying its domain and `Cond272Reg`, **without** a
`BoundsCore(s)` argument. In contrast, the pre-(4.5) Step-1 weak-law route
uses `BoundsCore(s)` to produce its entry inputs. The enclosing step has
that datum, but the frozen `h45i` slot does not expose it. The proxy theorem
does not make the datum disappear. A separately reviewed primed assembly
which passes the existing induction datum, or an independent source of the
unconditional weak law, is needed; neither is written here. Do not use the
same-cell Eq45 conclusion to manufacture its entry hypotheses.

## 10. One bounded proof-ready analytic Lean target

Release only the following **new random-scale fixed-time core**, not another
deterministic FA theorem or an unconditional Eq45 assembly. Suggested
descriptive name: `randomLmax_flucAvg_moment_of_entry_inputs`.

The inputs are exactly arbitrary `d : Dims`, fixed bulk `E`, domain
`0<=s<=t<1`, an eventual polynomial lower bound for `eta_(t_N)`, and the two
actual entry hypotheses (WLL)/(REL) in section 1, in `UnifDomIcc` form.
Using `(N+2)^(-a)` avoids artificial zero-size control problems. Keep
`a>0`, `K>=0` fixed before every eventual quantifier. No assumed proxy,
normalized moment, `FlucGain`, `CondStable`, `Eq45`, or `hPsiW` field is an
allowed extra input.

The single requested conclusion is the explicit normalized moment family:

```text
forall p : Nat, 1 <= p -> forall epsilon : Real, 0 < epsilon ->
  exists C > 0, eventually N,
    forall u in Icc (s N) (t N),
    forall deterministic w : d.Idx N -> Real,
      (forall i, |w i| <= (d.W N : Real)^(-1)) ->
      (sum_i |w i| <= 1) ->
      Integrable (fun omega =>
        (norm (flucAvg d N u (zt E u) (mE E) w omega) /
          (Lmax (Hflow d N u omega) (zt E u)
            + (d.W N : Real)^(-1)))^(2*p)) (P d)
      and integral_of_that_function <= C * (N : Real)^epsilon.
```

The weights are quantified after the eventual threshold because the proof's
constants are uniform in every deterministic admissible vector. This is a
uniform bound for their separate expectations, not a moment of a samplewise
weight supremum. Restricting the theorem to real weights loses nothing for
the two exact consumers. Both `Sblk` and `blkCoef` satisfy the displayed
maximum and l1 conditions without an additional bandwidth loss.

Sections 3-6 prove precisely this target; section 9 preflights every source
hypothesis on one nondegenerate Gaussian event. Markov plus the weak-law
lower bound gives both random `UnifDomIcc` conclusions at literal `Lmax`.
The separate IBP theorem and existing time-net adapters remain downstream
work. Implementation must reuse the existing projection, minor identity,
and singleton counting proofs rather than reprove deterministic FA. It
must preserve finite budgets and prove its smooth-proxy estimates, not add
them as unproduced structure fields.

For the **full later-cell route**, the release decision remains HOLD until
the scheduler records the source weak/relative entry event for the intended
cell with its actual initial datum and resolves the stronger `h45i` slot.
This target alone is not a proof-ready claim of universal paper closure.

## 11. Direct-edge classification

| Direct edge | Classification | Exact boundary |
|---|---|---|
| Actual product Gaussian law, row projection commutation, minor identities | Proved internally | Read actual declarations; overlapping Hermitian edges are included |
| Deterministic entry law -> row and block FA at deterministic `Psi^2` | Proved, narrower | `DetFlucAvgComplete`; T405/T406 do not certify random `Lmax` |
| Deterministic local law -> weighted IBP / averaged law at `Psi^2` | Proved, narrower | `DetIBPWeighted`, `DetAvgIBPFlow` |
| Canonical later-cell deterministic majorant -> all-epsilon `hPsiW` | Contradicted | T1333; numerical no-go remains active |
| Fixed-real-time `W^(-1)` proxy -> moving-time random conditional stability by the same proof | Missing / invalid inference | `eta_t^(-2)` is no longer a constant; not a refutation of the desired stability |
| (WLL)/(REL) -> finite-minor common event and smooth proxy | Proved analytically here | Actual same-sample minors; not yet a compiled random-proxy module |
| Proxy -> mixed differences (Pr)/(Yr) | Proved analytically here | Finite budget; corrected moment-independent `q_N` |
| Normalized singleton expansion -> (RM) for both weights | Proved analytically here | Common fully deleted minor retained in products |
| (RM) -> literal fixed-time random FA | Proved analytically here | Floor removed on the same weak-law event |
| First-order proxy -> random conditional preservation -> IBP residual | Proved analytically here, separate | Diagonal variance weight retained; no FA used for this residual |
| Three random fixed-time estimates + actual flow event/moduli -> three flow fields | Proved conditional adapter | Existing primed net engine; source premises must be discharged |
| Three fields -> Eq45 -> one-loop bound | Proved internal transfer | `eq45Flow_of_eq45FlowInputs`, `stochDom_lkErr_one_Lmax` |
| All required source hypotheses on positive first cell | Proved / witnessed | `exampleGrow`, actual same event, positive Gaussian variance |
| Unconditional required source event on T1333 later cell | Missing in inspected evidence | Domain witness alone does not supply it |
| Step-1 inputs using initial BoundsCore -> frozen unconditional `h45i` | Blocked by mismatch | Must expose existing initial datum in a successor or prove a stronger source |

## 12. Verification, provenance, and ownership

This was a fresh independent review of existing source proofs and the T328
candidate, not a continuation of its author's session. Its historical
verdicts were not treated as premises. The corrected `q_N` bookkeeping and
the explicit normalized-moment statement are reconstructed in this report;
no separate independent Lean PASS is claimed for them.

The only manuscript source was `paper/250520-YinJun-v2.pdf`, inspected at
(4.1)-(4.12) and the IBP displays following (4.12); the complete relevant
formula sheet was also rendered and visually checked. No external paper was
fetched or accepted as a mathematical input. No simulation was used as proof.

Commands/checks included targeted `sed`/`rg` reads, local `pypdf` extraction,
`pdftoppm` rendering, SHA-256 checks, and a read-only research-state
`check --summary` (4 events, 2 recorded claims, 0 bookkeeping issues; not a
mathematical certificate for this route). Existing `.olean` artifacts were
present and newer than their sources for the inspected core modules,
including `Eq45Flow`, `Eq45FlowGrid`, `DetFlucAvg`, `DetFlucThreshold`,
`CondStableFlow`, `EntryBoundTime`, `Model`, `FirstCellStep1LocalLaw`,
`FlucIter`, `FlucIterHigh`, and `MinorDiffGain`. This is not a fresh build or
dependency-hash certificate. No new `lake build` or public axiom audit was
run, because no Lean theorem was added or changed.

Source SHA-256 snapshot:

```text
bd6f7e32bee30a28202e147742b28e88e85bdd6a691ae8fa89e3aedae22bbb43  paper/250520-YinJun-v2.pdf
acc1bb43f65cab6ade8c14553ea36294aa7dff2180703a3096876050515700b2  docs/reports/T328.md
2084b0f47d8ed510e09f07118cf777c048fcebee6b134c8a7d9efa33fd338649  docs/reports/T331.md
b5462698576a3d852472a44b324144aa8dc60a16804808edbfeb25ae547c8a20  docs/reports/T405.md
c974cb588c14ca6c908c02fd25381f261f8671096fe06748dbf89de28b004ed4  docs/reports/T406.md
2aa822089519f7b9e75baf13e884268eb9b112bce3a6df146220e88c061639b7  docs/reports/T852.md
c684d6ffba45dac3d0c487e3d34d983d34bf86fc5f90eb54ac4273d2f8581fe3  docs/reports/T1333.md
0f0446780aa69fca612c2016c3bde7088d65b932cadec64ffa66c0271c605c43  docs/reports/V6-full-paper-cutoff-localization-preflight.md
7fb29e5a4338f36cd93efaab8518ae0242f3676e355a6318cf5e9a63fa545b43  RBM1D/Flow/Step345Producer.lean
09c349a4a41eb4a49fe4caa8c6389deac419b0c0988537f0b8a08c0a80e05e29  RBM1D/Gauss/DetFlucAvgComplete.lean
4ce1644a458ff091083ea2807176819b7b2868a90c1473cdcb5bbe62d8c49ae7  RBM1D/Gauss/CondStableInst.lean
d3adcfed24ac8ac0dd8e609a41a521ce27b46c60cec07d25d061708ae64a1ead  RBM1D/Gauss/DetAvgIBPFlow.lean
a7de3860833a742c38e75c68544f467209d27ba417446b4ee939c7677260328d  RBM1D/Gauss/MinorDiffCond.lean
f1c27830cbd31aa584dc2c18798bcb47e7e973a643713324ec4f53632423f995  RBM1D/Gauss/Eq45FlowInputs.lean
7b82a7540602a2ab352a3d9d9c50565fe7869be7c4bb70ac3953a5729cfa9391  RBM1D/Gauss/Eq45LaterCellCanonicalNoGo.lean
871dc097f48ab1305a78d48f3ae44e2dc09676d96eba426742a14f485cb5e149  RBM1D/Gauss/DetIBPWeighted.lean
```

Only `docs/reports/V6-eq45-random-Lmax-astra-review.md` was written in the
repository. No Lean source, root import, live TASKS/STATUS/PLAN, historical
report, ledger, automation, Git index, commit, or push was changed.
