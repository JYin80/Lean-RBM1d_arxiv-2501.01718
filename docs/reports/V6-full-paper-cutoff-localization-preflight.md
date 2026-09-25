# V6: all-charge cutoff localization preflight

Read-only mathematical preflight, 2026-09-24. Only `paper/250520-YinJun-v2.pdf` and direct relevant Lean sources were used. No Lean change, task dispatch, build, or new compiled theorem is claimed. This report examines the actual `CutHypEvOnSlot` arrow on the full-paper critical path.

## Conclusion

**Do not dispatch the complete all-charge smooth-localization estimate yet.** The quadratic term can be made small once genuine prefix support is retained. The mixed source `xiLK_1 * xiL_3` is a separate obstruction: the accepted Step-1 and Step-2 bounds alone do not make its available majorant fit the required scale. This failure survives the nonalternating short-edge kernel improvement. It is a failure of the proposed majorant argument, not a counterexample to the actual Gaussian estimate or the paper.

There is a concrete noncircular next check: produce the actual Eq. (4.5) fluctuation estimate, then use **only the alternating raw two-loop estimate already supplied by T1337** to obtain `xiLK_1 ≺ 1` before the all-charge cutoff. The existing `StepGlue.flow_hs1` is packaged with a Step-3 input, but its proof only uses that input's `(+,-)` restriction. Thus the stronger packaging is not a mathematical reason to wait for Step 3. Paper (5.80) explicitly invokes (4.5) for precisely this mixed source.

The all-charge smooth weight and its generator cross budget are also not supplied by the existing alternating A′ weight. Below is a fully specified candidate, a proof of its intermediate-time support mechanism, the exact target and the first unproved source inequality. It has a genuine positive-window Gaussian witness; nonvacuity is not the obstruction.

## 1. Exact consumer and available rows

`Flow/Step345Producer.lean:749` defines `CutHypEvOnSlot X E s t` as the existence of one measurable high-probability event `Good_N` and a `MomentDuhamelCut.CutHypEvOn` for

`J_N(u,omega) = X.xiLK E N u omega 2`, `Theta_N = A_s^(1/2)`, `A_u=W ell_u eta_u`.

At `Gauss/MomentDuhamelCut.lean:1500`, the moment field is **unconditional**, even though the modulus is restricted to `Good`:

```text
exists delta0>0, for every 0<delta<=delta0, epsilon>0, p in Nat,
exists C>0, eventually N, for every v in netFinset(s,t,mesh)_N,
 E |cutTrunc(N^(2delta) Theta_N, J_N(v))|^(2p)
 <= C N^(epsilon p) Theta_N^(2p).
```

The accepted T1339/T1351 source `XiLKTwoCutModulus` supplies the actual all-charge modulus on `Gnorm_N={||X_N||<=N}`, with `Kmod=21`, `gamma=1/2`, `mesh_N=(N+1)^42`, matching measurability, positivity, cardinality, and `mesh_fine <= Theta_N`. T608 supplies the initial row. T1341 is active: its all-charge QV target has the stronger normalized scale `A_s^(1/3)`. It is not treated as accepted in this report.

T596 (`XiLKTwoCutMoment:48,107,152`) has the exact all-charge, all-label coordinate Duhamel RHS, with the conjugated doubled charge `xi2` in the QV row. It bounds the cutoff maximum by a sum of `4 L_N^2` **unweighted** coordinate moments and first uses `cutTrunc_le_self`. Therefore it has discarded the information that would control the quadratic drift at intermediate times. Multiplying its final inequality by an endpoint cutoff does not restore a localized Gaussian identity.

The final moment quantifier `forall delta, forall epsilon` should not be replaced by a bound with loss proportional to that same fixed delta. The usual valid route is a weighted prefix improvement for every arbitrarily small localization loss, bootstrap to stochastic domination, and then the full cutoff-moment field by a polynomial-envelope reverse bridge. Constants/moment orders are fixed before the eventual N and must be uniform in the active cell.

## 2. A precise all-charge weight that really retains support

The following is a proposed mathematical construction, not an existing Lean declaration. Fix `d=Dims.exampleGrow`, bulk `E`, deterministic windows `0<=s_N<=t_N<1`, `c>0`, `Cond272Reg`, and incoming `BoundsCore (sample d) E s`. Set

`v_j=s_N+j/mesh_N`, `Q_N=LoopData(L_N,2)`, `Theta_N=sqrt(A_s)`.

For a base Gaussian matrix `X_N(omega)` define the **complex**, all-charge normalized coordinates

`Z_{j,q}(omega)=A_(v_j)^2 (L-K)_(v_j,q)(omega)/Theta_N`.

All preceding times use this same matrix through `H_(v_j)=sqrt(v_j) X_N`; they are not independent samples. For example take the integer soft-max order

`m_N=max(1,ceil(50 log(N+2)))`, `a_N=(N+2)^(-10)`

and, for each active cell k,

`S_(N,k)=(a_N^(2m_N)+sum_(j<k,q in Q_N) |Z_(j,q)|^(2m_N))^(1/(2m_N))`,

`chi_(lambda,N,k)=cutChi(S_(N,k)/N^(2lambda))`,

`w_(lambda,p,N,k)=chi_(lambda,N,k)^(2p)`.

The positive regularizer makes the root smooth; the coordinates are smooth resolvent functions off the real axis. The cutoff is a function of the base Gaussian matrix, constant in the running integration variable u. A rigorous implementation must use a smooth Hermitian-coordinate realization (or the existing smooth matrix extension), not claim that the resolvent is globally smooth on every complex matrix. The existing generic soft-max derivative estimates in `APrimeDuhamel` are applicable after that check, whereas the literal `APrimeSmoothWeightActual` definition is specialized to the alternating, tail-normalized observable.

There are eventually at most `N^50` summands: the mesh contributes 42 powers and the actual two-loop family has cardinality `4L_N^2`. Hence the soft-max cardinality factor is bounded by a numerical constant, uniformly in k. For every fixed `lambda>0`, eventually:

* If every preceding net value satisfies `J_N(v_j)<=N^lambda Theta_N`, then `chi=1`. One event works for all p.
* For `p>=1`, if `w>0`, then every preceding net value satisfies `J_N(v_j)<2N^(2lambda) Theta_N`.
* On **the same** `Gnorm_N`, T1351's modulus fills every interval from a preceding net point through the next endpoint. Thus, for `k>=1`,

```text
p>=1 and w_(lambda,p,N,k)(omega)>0 and omega in Gnorm_N
  => for every u in [s_N,v_k],
       J_N(u,omega) <= (2N^(2lambda)+1)Theta_N
                    <= 3N^(2lambda)Theta_N.
```

This includes `u=v_k`, although the smooth weight uses only `j<k`. The missing final mesh interval is covered by the modulus. For k=0 the time integral is zero and the initial moment row is used. The last admissible mesh point is still inside the window; no ceiling endpoint beyond t is allowed.

This support statement is substantive and correct; it does not imply that a full weighted Duhamel bound holds. Off `Gnorm_N`, one must use the actual polynomial envelopes and its arbitrarily small bad probability, in the full Gaussian measure. Conditioning Stein on `Gnorm_N` is not permitted.

## 3. The candidate analytic estimate and its exact quantifiers

With the above weight, one sufficient weighted prefix estimate would be:

```text
For every fixed natural Gaussian window as in §2,
there exists lambda0>0 such that for every 0<lambda<=lambda0
and every fixed p>=1 there exists C(E,c,s,t,lambda,p)>0,
eventually N, simultaneously for all active k,

 E [chi_(lambda,N,k) J_N(v_k)]^(2p)
   <= C N^(lambda p/2) Theta_N^(2p).
```

The weights for different p are powers of the **same** chi. The event on which chi=1 does not depend on p. The root budget is `N^(lambda/4) Theta_N`. At `p=0`, use the probability-space identity. For finite-max passage, first prove sufficiently high fixed coordinate moments and then lower the order; do not leave the factor `4L_N^2` in the desired p=1 estimate. The high fixed order may depend on lambda, requested p and the polynomial cardinality exponent, but not on N or k.

This statement would give a strict prefix improvement: Markov at `N^lambda Theta_N` gives a factor `N^(-3lambda p/2)`, allowing polynomial-net union bounds with arbitrarily high fixed p. The initial tail and `Gnorm_N` supply the remaining bootstrap inputs. It would ultimately yield the consumer in §1. **This full statement is not proved or refuted here.** The attempted derivation from existing majorants breaks at the mixed source identified below.

## 4. The quadratic term has room; the mixed source does not follow

Write `R_u=eta_s/eta_u`, `r_u=ell_u/ell_s`; then `A_u=A_s r_u/R_u`, `1<=r_u<=sqrt(R_u)`, and `R_v^30<=A_v<=A_s` under Cond272. Also `du/eta_u=(Im m)^(-1) d(log R_u)`.

At length two there is no lower-order coupling sum. The actual decomposition is `driftF=eG+primBil(D,D)`, and `DriftBound:330–365`/`Decay:1022,1040` retain separately

```text
|F_u| <= C (K+2) eta_u^(-1)
             [A_u^(-3) J_u^2 + A_u^(-2) X1_u Y3_u]
          + WL delta_decay (4J_u+2X1_u),
X1_u=xiLK_1,  Y3_u=xiL_3.
```

This display requires the actual spatial decay hypotheses. They must be produced or replaced by a separately checked crude-counting argument; they are not consequences of the cutoff alone. The comparison below even grants those favorable decay hypotheses.

The generic two-coordinate kernel gives `||U_(u,v)|| <= R_(u,v)^2`. On the support proved in §2, the main quadratic integral satisfies

```text
A_v^2 integral_s^v R_(u,v)^2 eta_u^(-1) A_u^(-3) J_u^2 du
 <= C_E N^(4lambda) r_v^2 integral_1^(R_v) [R/r_R^3] d(log R)
 <= C_E N^(4lambda) R_v^2
 <= C_E N^(4lambda) A_s^(1/15).
```

For `K=N^tau`, the radius cost adds at most `N^tau` up to a fixed constant. Relative to `Theta=sqrt(A_s)`, the bound is

`C_E N^(4lambda+tau) A_s^(-13/30) <= C_E N^(4lambda+tau-13c/30)`.

For example, `lambda<=c/1000`, `tau=lambda/10` leaves a factor at most `C_E N^(-c/3)`. Thus the quadratic term is genuinely perturbative once the all-time support is present. Its smallness is not the first unresolved exponent.

For the mixed source, the accepted inputs are only

`X1_u ≺ sqrt(A_u)` from the T1337 local law, and `Y3_u ≺ r_u^2` from Step 1.

Using the generic kernel gives the profile

`C_E sqrt(A_s) r_v^2 integral_1^(R_v) sqrt(r_R/R) d(log R)`,

which is of order `sqrt(A_s) R_v` in an unsaturated interval. Even replacing the kernel by the nonalternating **Case 1 of (7.16)** does not solve it. That favorable normalized kernel bound leaves the smaller profile

`integral_s^v eta_u^(-1) X1_u Y3_u du`.

On an unsaturated interval at E=0, `r_u=sqrt(R_u)`, so the permitted profiles give exactly

`sqrt(A_s) integral_1^(R_v) R^(3/4) d(log R)
 = (4/3) sqrt(A_s) (R_v^(3/4)-1)`.

The cutoff on J alone has not restricted this mixed source. In particular, setting `X1<=1` here from the local law would be a false inference.

### A decisive scalar-majorant obstruction on a real admissible window

Take the actual dimension sequence `exampleGrow`, E=0, `s_N=0`, and `t_N=1-(N+2)^(-1/100)`. Eventually the whole interval is unsaturated, `ell_t=(N+2)^(1/200)<<L_N`, `A_s=W_N`, and `R_t=(N+2)^(1/100)`. These are genuine positive windows with incoming `BoundsCore` at zero. `Cond272Reg` holds, for example with c=1/2: the source bound `W>=N^(5/8)` gives `A_t` a power strictly above 1/2 and well above `R_t^30`.

For nonnegative scalar profiles take `Y3=r^2`, `J=min(R_u-1,1)`, and `X1=sqrt(A_u) min(R_u-1,1)`. They obey the available upper bounds, the J cutoff, continuity and zero initial values for J and X1. For `R_u>=2`, the mixed-source integral is at least

`(4/3) Theta_N (R_t^(3/4)-2^(3/4))`.

It grows like `Theta_N N^(3/400)`. Therefore it cannot be bounded by `C N^(lambda/4) Theta_N` for every arbitrarily small lambda; choose, for example, `0<lambda<=1/1000`. No choice of a fixed C or a later N0 repairs that comparison.

These scalar profiles are **not asserted to be simultaneous values of actual Gaussian loops**. The result refutes exactly the deterministic implication from the currently available magnitude profiles to the requested source budget. It does not refute the actual weighted estimate in §3; additional cancellation or a stronger actual source estimate may prove it.

## 5. The earliest missing inequality, and the noncircular repair check

For the literal `eG` tensor and the same all-charge weight, the first unresolved analytic row is

```text
for every sufficiently small lambda>0 and every fixed p>=1,
exists C>0, eventually N, uniformly in active k and all q,

(A_v^2 / Theta_N) integral_s^v
  || chi_(lambda,N,k) U_(u,v) eG_u,q ||_(2p) du
 <= C N^(lambda/8),                    v=v_k.
```

The loss `lambda/8` leaves room inside the root budget `lambda/4`; other sufficiently small fixed fractions would serve. The measure is the **full actual Gaussian measure**, the same chi is retained inside the norm, and both time integrability and Gaussian integrability are required. No unrestricted all-real-time envelope is assumed.

A sufficient stronger actual input is `X1 ≺ 1` uniformly over `TimeIcc`, followed by a reverse moment bridge using its real polynomial envelope. With `Y3 ≺ r_u^2`, the generic-kernel mixed source then has the bound

`C_E N^a r_v^2 log R_v <= C_E N^(a+b) A_s^(1/30)`

for any fixed small a,b>0, which fits `Theta_N` with a large power margin. This is why (4.5) matters even though the quadratic J term itself is small.

`Hierarchy/StepGlue.lean:506–535` proves `flow_hs1` from `Eq45Flow` and a packaged all-charge raw length-two estimate. Inspecting its proof shows it uses **only**

```text
StochDom P (fun N (u,a,b) omega => |L_(u,+-,a,b)(omega)|)
           (fun N (u,a,b) _ => A_u^(-1)).
```

This input is already obtained from T1337's alternating `L-K` estimate, the primitive K bound and Cond272, exactly as paper (5.73). It does not require all-charge Step 3. Then Eq45 at `Phi_u=A_u^(-1)` supplies the one-loop error, and multiplication by A_u gives `X1 ≺ 1`. Producing an actual Eq45 input remains substantial; merely weakening the existing `flow_hs1` wrapper is not a new analytic ticket.

The decisive next mathematical check is therefore the actual fixed-time, same-sample fluctuation/conditional-expectation estimate behind `Eq45FlowInputs`, with its random Lmax control. Alternatively one must prove the displayed localized `eG` inequality directly by genuine cancellation. Repeating the present absolute-value profile estimates cannot do so.

## 6. The cross derivative is a separate required row

The correct Gaussian identity already exists generically. `APrimeDuhamelModel:49` defines its cross part as

`(2 sqrt(u))^(-1) sum_alpha gvar_alpha E[(partial_alpha w)(X) partial_alpha Psi(u,H_u)]`.

For `Psi=|A_v^2 U_(u,v)(L-K)_u / Theta_N|^(2p)`, `momFlowDeriv_le:638` needs an actual budget `Bc(u)` satisfying

`crossPart <= 2p phi(u)^((2p-1)/(2p)) Bc(u)`

and a sufficiently small `integral_s^v Bc(u) du`. Its Gaussian derivative, weighted Holder and closed-window machinery are available. Generic soft-max/covariation Cauchy–Schwarz in `APrimeDuhamel:1246` avoids a full cardinality loss.

What is not available is the literal all-charge prefix derivative/rate producer for §2's normalization, together with its uniform moving-window integral budget. Existing actual cross producers use `Step2.sigPM` and tail/R^4 normalization. They cannot simply be renamed. The `u^(-1/2)` factor is locally integrable at s=0, but its **moving time powers** and the prefix-time pullback factors must be retained; freezing a worst endpoint rate before integration can create a false obstruction. T1341's single coordinate time-integrated QV is not automatically a two-time prefix/current cross estimate.

The candidate may have enough room: the raw length-six rates suggest products of the prefix normalized gradient and current normalized QV. But a complete all-charge cross proof has not been established here, so no positive cross ticket is asserted. Even a successful cross estimate would leave the mixed-source row in §5.

## 7. Nondegeneracy of the proposed localization

A joint positive-window witness can be given without assuming the desired all-charge conclusion. Use the actual nonconstant `exampleGrow` Gaussian model, E=0, `s_N=0`, and

`t_N=(N+2)^(-83/2)`.

Take c=1/2. Initial `BoundsCore` is the exact zero-time theorem; Cond272Reg follows eventually from `W>=N^(5/8)`. The same high-probability event `Gnorm_N` used by T1351 has

`J_u <= N^21 sqrt(t_N) <= N^(1/4)` for all `0<=u<=t_N`,

because `J_0=0`. Meanwhile `Theta_N=sqrt(W_N)>=N^(5/16)`. Hence `J_u/Theta_N<=N^(-1/16)`, and the all-charge smooth weight above equals 1 on `Gnorm_N` for every fixed lambda>0, all active k and every p, eventually. The event has positive probability eventually. There are positive active mesh points: `t_N mesh_N` grows like `N^(1/2)`.

This is a positive-length window with R>1, a nonzero probability measure, a growing number of blocks, and the actual Gaussian observables. The observable is not defined to be zero: at the zero matrix sample and any positive small u the same-block constant-charge loop is `-1/[W(1-u)^2]`, whereas the primitive two-loop magnitude is at most `1/[W(1-u)]`; their difference is nonzero. Continuity gives an open Gaussian-positive region with this nonzero coordinate, still inside the norm event and the plateau for sufficiently large N. This argument is an analytic witness proposal, not a compiled witness certificate.

The witness verifies that the localization construction is meaningful. Its very short interval does not establish the sought estimate on the long moving windows where the scalar-majorant obstruction in §4 occurs. Both facts must be retained in any future ticket.

## 8. Paper comparison and release decision

Paper (5.21)/(5.24) are stopped-hierarchy/martingale statements. Paper (5.40)–(5.42) control the alternating tail-normalized nonlinear terms, and (5.43)–(5.47) retain the stop until the improvement is established. They motivate the need to preserve localization; they do not identify a radial Gaussian weighted moment with a stopped process.

The independent constant-charge sector is instead handled through Lemma 5.11/(7.16) Case 1, as correctly recorded in `Hierarchy/Step2PP`. For its actual drift, the factor removed in paper (5.80) is supplied through (4.5), not by weak entrywise local law alone. This is the first critical dependency exposed by this preflight.

**Release decision:** no complete all-charge localized moment ticket from the currently accepted inputs. Preserve the modulus, initial and QV work. Preflight the actual Eq45 fluctuation arrow next, or supply a new direct mixed-source cancellation proof. After that, the new all-charge same-weight generator/cross row and conditional quadratic budget have a credible assembly route; without it, a positive ticket would assume precisely the missing analytic estimate.
