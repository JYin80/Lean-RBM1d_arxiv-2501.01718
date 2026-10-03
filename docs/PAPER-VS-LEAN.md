# The paper and the Lean proof: detailed differences

**Paper.** H.-T. Yau and J. Yin, *Delocalization of one-dimensional random band matrices*,
`paper/YauYin_RBM1D_Lean_version.pdf` in this repository. Page, equation and theorem numbers below refer
to this PDF.

**Cited works.** [51] = B. Landon, P. Sosoe, H.-T. Yau, *Fixed energy universality of Dyson Brownian
motion*, Adv. Math. 346 (2019), in the form of arXiv:1609.09011v4. [37] = L. Erdős, H.-T. Yau, *A dynamical approach to
random matrix theory*, AMS 2017. [70] = C. Xu et al., *Bulk universality and quantum unique ergodicity
for random band matrices in high dimensions*, Ann. Probab. 52 (2024).

**Lean.** Every name below that starts with `RBM.` is a declaration of the library `RBM1D` and is used,
directly or indirectly, by the proofs of the five main theorems, except `RBM.Gauss.Dims.exampleGrow` and
`RBM.Paper.NonVacuity.zStar`, which are used by the compiled instances in `RBM1D/PaperMain.lean`. Other names (such as
`Matrix.IsHermitian.eigenvalues`) are from Mathlib.

Contents: §1 what is proved; §2 differences between the statements; §3 uniformity in (W, L); §4 the
external input [51]; §5 where the Lean proof takes a different route.

---

## 1. What is proved

**The model.** `RBM.Gauss.Dims` fixes, for every Lean index `N`, a block size `W N ≥ 1`, a number of
blocks `L N ≥ 3`, and a constant `c > 0`, with `W N · L N ≤ N ≤ 2 W N · L N` and `N^{1/2+c} ≤ W N` for
all large `N` (§2.3 explains the role of the index `N`). The matrix `RBM.Gauss.Xmat d N` is the band
matrix of the paper's §2.1 (p. 7): its rows and columns are indexed by pairs (block `a ∈ Z_L`,
offset `α ∈ {0, …, W−1}`), which is the paper's index `i = aW + α`; its entries are independent up to
Hermitian symmetry, complex Gaussian `N_C(0, S_ij)` off the diagonal and real Gaussian `N(0, S_ii)` on
the diagonal, with `S = S^{(B)} ⊗ S_W`, `S^{(B)}_{ab} = (1/3)·1(dist_{Z_L}(a,b) ≤ 1)`,
`(S_W)_{αβ} = 1/W` (the variances are `RBM.Gauss.gvar`). The probability measure is `RBM.Gauss.P d`,
and `RBM.Gauss.band d` packages the dimensions with this measure. The five theorems are stated for the
matrix `(RBM.Gauss.transfer_gauss d).Hband`, which is `Xmat` itself.

**The theorems.** They are in `RBM1D/PaperMain.lean`.

| Paper | Lean | Hypotheses other than parameters |
|---|---|---|
| Theorem 2.2 (delocalization) | `RBM.Paper.theorem2_2` | none |
| Theorem 2.3 (local semicircle law: (2.3), (2.4) and the tracial law) | `RBM.Paper.theorem2_3` | none |
| Theorem 2.4 (quantum diffusion: (2.6)–(2.9)) | `RBM.Paper.theorem2_4` | none |
| Theorem 2.5 (generalized QUE: (2.12), (2.13)) | `RBM.Paper.theorem2_5` | none |
| Theorem 2.6 (bulk universality: (2.18)) | `RBM.Paper.theorem2_6` | `h51 : RBM.Gauss.LSY22' d` |

"Parameters" are: the dimensions `d` (which carry (2.2)); the positive constants `κ, τ, D` (and `τ'`,
§2.7); the spectral parameter `z` of Theorems 2.3–2.4 with the paper's domain conditions; the energy
`E` of Theorem 2.5 with `|E| ≤ 2 − κ`; and `0 < τ* < c/2` (2.11) in Theorem 2.5. `PaperMain.lean`
contains a compiled command that classifies every binder of the five statements and fails unless the
only non-parameter hypothesis is `h51` in Theorem 2.6.

**The single external input.** Theorem 2.6 assumes `RBM.Gauss.LSY22' d`, which is [51, Theorem 2.2]
in the form of arXiv:1609.09011v4, for complex Hermitian matrices (§4). It is a hypothesis of the theorem, not an
axiom, so it does not appear in the axiom list below. Theorems 2.2–2.5 use no external input.

**Axioms.** The five theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. To check:

```
lake build RBM1D.PaperMain
```
prints, among its messages,
```
'RBM.Paper.theorem2_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Paper.theorem2_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Paper.theorem2_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Paper.theorem2_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Paper.theorem2_6' depends on axioms: [propext, Classical.choice, Quot.sound]
```
and `lake build RBM1D` runs the command `#assert_rbm_axioms` (file `RBM1D/Test/Axioms.lean`) on every
declaration in the namespace `RBM`; the build fails if any of them uses `sorryAx` or any axiom other than
these three.

**The statements are not vacuous.** `RBM.Gauss.Dims.exampleGrow` is a choice of dimensions with
`W ≈ N^{3/4}`, `L ≈ N^{1/4} → ∞` and `c = 1/8`. `PaperMain.lean` applies every theorem to it:
Theorem 2.2 at `κ = 1`, `τ = 1/2`, `D = 1`; Theorems 2.3 and 2.4 along the spectral parameter
`RBM.Paper.NonVacuity.zStar N = (−1)^N/4 + i·max(N,1)^{−1/4}` (real part not constant, imaginary part
tending to 0 and at least `N^{−1/2}`); Theorem 2.5 at `τ* = 1/32 < c/2` with the energies
`E_N = (−1)^N/4`; Theorem 2.6 at `E = 0`, `k = 1` and a smooth bump function, under `h51`. There is no
empty index set (`L ≥ 3`, `W ≥ 1`) and no collapsed spectral window.

---

## 2. Differences between the statements

Each entry gives the paper's wording, the Lean form, the reason for the difference, and how the two
statements relate. "Equivalent" means that each implies the other for the full family of parameters
(possibly after a change of the free constants such as `τ ↦ τ/2`, `D ↦ 2D`). "Lean stronger" means
that the Lean statement implies the paper's.

| | Item | Relation |
|---|---|---|
| 2.1 | `L ≥ 3` | identical (the paper states `L ≥ 3`, p. 7) |
| 2.2 | eigenvalue and eigenvector labels | equivalent |
| 2.3 | Lean index `N` versus matrix size `WL` | equivalent (with §3) |
| 2.4 | failure probability instead of success probability | equivalent |
| 2.5 | (2.13): the weak inequality and the event for `A = ∅` | Lean stronger (the Lean event uses `≥`; for `A = ∅` the paper's event is empty) |
| 2.6 | `≥` and `>`, `≤` and `<` | identical, except `|E| ≤ 2−κ` in Theorem 2.5 and `≥` in the event of (2.13) (Lean stronger) |
| 2.7 | separate exponent `τ'` for the error | Lean stronger |
| 2.8 | spectral parameters and energies as sequences | equivalent |
| 2.9 | correlation functions without densities | identical definition |
| 2.10 | the GUE side of (2.18) | identical |
| 2.11 | test functions | identical |
| 2.12 | one probability space for all `N` | equivalent |
| 2.13 | the index set `Z_L × {0, …, W−1}` | identical after relabeling |

### 2.1 `L ≥ 3`

- **Paper** (p. 7): "the number of blocks is denoted by `L ∈ ℕ` with `L ≥ 3`", and, after the
  definition of `S`, "Clearly, `S = S^T`, and it satisfies `Σ_j S_ij = 1`."
- **Lean.** `RBM.Gauss.Dims.three_le_L : ∀ N, 3 ≤ L N`. The row-sum identity is `RBM.sum_SB_row`, which
  assumes `3 ≤ L`.
- **Relation: identical.** `L` may stay bounded (for example `L ≡ 3`), as in the paper.

### 2.2 Eigenvalue and eigenvector labels

- **Paper** (p. 7): `λ_1 ≤ λ_2 ≤ … ≤ λ_N` with normalized eigenvectors `ψ_k`.
- **Lean.** Mathlib's `Matrix.IsHermitian.eigenvalues` and `Matrix.IsHermitian.eigenvectorBasis`:
  an orthonormal eigenbasis, paired with the eigenvalues by index, in no particular order.
- **Relation: equivalent.** Every statement takes a maximum over all labels (over `k` in Theorem 2.2
  and (2.13), over `i, j` in (2.12)), so the order does not matter. The eigenvector quantities
  `|ψ_k(x)|²`, `|ψ_i^*(E_a − N^{−1})ψ_j|²` and `Σ_{x∈I_a}|ψ_k(x)|²` do not change when an eigenvector is
  multiplied by a phase, so they do not depend on the choice of eigenbasis when the spectrum is simple.
  The spectrum is simple almost surely: the discriminant of the characteristic polynomial is a
  polynomial in the independent real coordinates of `H`; it is not identically zero, since the diagonal
  coordinates are free (`S_ii > 0`) and a diagonal matrix with distinct entries has a simple spectrum;
  and the coordinates have a nondegenerate Gaussian density, so the zero set of the discriminant has
  probability zero. (This almost-sure simplicity argument is not compiled.)

### 2.3 The Lean index `N` versus the matrix size `WL`

- **Paper** (pp. 7–8): `N = W·L` is the matrix size; (2.2) reads `W ≥ N^{1/2+c}`.
- **Lean.** `N` is an index. The matrix has size `M = W N · L N` (`RBM.Band.size`, `RBM.Gauss.msize`),
  and `RBM.Gauss.Dims.dim` requires only `M ≤ N ≤ 2M` for large `N`; `RBM.Gauss.Dims.bandwidth` is
  `N^{1/2+c} ≤ W N`. The reason: `N = W·L` with `L ≥ 3` is impossible for every `N` (for example for
  primes), while a Lean statement "for all large `N`" needs dimensions at every `N`.
- **Where the index appears.**
  - Theorem 2.2: the threshold `N^{−1+τ}` and the rate `N^{−D}`.
  - Theorems 2.3 and 2.4: the domain `N^{−1+τ} ≤ Im z` and the rate `N^{−D}`. The error terms do not
    involve `N`: they are `W^{τ'}` times powers of `(Wℓη)^{−1}` (`RBM.Band.zScale` is `W·ℓ(z)·Im z`,
    and `RBM.ellZ` is `ℓ(z)` of (2.1)); the tracial law divides the trace by `L·W`, the paper's `N`.
  - Theorems 2.5 and 2.6 use only the size `M`: the window `J_E` (`RBM.Band.queEtaN`), the threshold
    and the rate of (2.12)–(2.13), and the scaling `E + α/M` in (2.18).
- **Relation: equivalent** (for each fixed family of dimensions; the uniformity over `(W, L)` is §3).
  At an index with `N = M`, the Lean statement is the paper's statement. In general `M ≤ N ≤ 2M`, and
  the statements convert with explicit slack:
  - (R1) `N^{−1+τ} ≤ M^{−1+τ}` (since `N ≥ M`, `τ ≤ 1`), so the Lean failure event contains the
    paper's and the Lean domain of `z` contains the paper's; and `N^{−D} ≤ M^{−D}`. So the Lean
    statement at `(τ, D)` implies the paper's at `(τ, D)`. (For `τ > 1` both statements are trivial:
    `|ψ_k(x)|² ≤ 1 < N^{−1+τ}`, and the domain of `z` is empty.)
  - (R2) `M^{−2D} ≤ (N/2)^{−2D} = 2^{2D} N^{−2D} ≤ N^{−D}` once `N ≥ 4`.
  - (R3) `(2M)^{−1+τ} ≥ M^{−1+τ/2}` once `M^{τ/2} ≥ 2^{1−τ}`. So the paper's statement at `(τ/2, 2D)`
    implies the Lean statement at `(τ, D)` for large `N`.
  - The bandwidth condition converts in the same way: `N^{1/2+c} ≤ W` implies `M^{1/2+c} ≤ W`, and
    `M^{1/2+c} ≤ W` implies `N^{1/2+c/2} ≤ W` for large `N`.

### 2.4 Probability bounds for the failure event

- **Paper:** `P(success) ⩾ 1 − N^{−D}` in Theorems 2.2–2.4 (for example
  `P(max_k ‖ψ_k‖²_∞ · 1(λ_k ∈ [−2+κ, 2−κ]) ⩽ N^{−1+τ}) ⩾ 1 − N^{−D}`).
- **Lean:** `P(fail) ≤ N^{−D}`, where `fail` is exactly the complement of the paper's success event
  (for example `∃ (k, x), N^{−1+τ} < |ψ_k(x)|² · 1(λ_k ∈ [−2+κ, 2−κ])`).
- **Relation: equivalent.** For a measurable event `A`, `P(A) ≥ 1 − x` if and only if `P(Aᶜ) ≤ x`.
  Without measurability, Lean's `P` of a set is its outer measure, and `1 ≤ P(A) + P(Aᶜ)` still gives
  `P(A) ≥ 1 − N^{−D}` from the Lean bound.

### 2.5 (2.13): the weak inequality and the event for `A = ∅`

- **Paper** (2.13), p. 10: for any subset `A ⊂ Z_L`,
  `max_{|E|<2−κ} max_{A⊂Z_L} P(max_{λ_k∈J_E} |Σ_{a∈A} Σ_{x∈I_a} |ψ_k(x)|² − |A|W/N| > |A|W/N^{1+τ*/12}) ≤ N^{−τ*/6}`.
- **Lean.** `RBM.Paper.theorem2_5` states the bound for every nonempty `A`; the event is
  `RBM.queEvent213`, which has the weak inequality `≥` with the same threshold `|A|W/N^{1+τ*/12}`.
- **Relation: Lean stronger.** For every `A` the paper's statement follows from the Lean statement.
  - For `A ≠ ∅`: the paper's event (some `λ_k ∈ J_E` with `|…| > |A|W/N^{1+τ*/12}`) is contained in the
    Lean event (the same with `≥`), with the same threshold, so the Lean bound `N^{−τ*/6}` implies the
    paper's bound at the same rate.
  - For `A = ∅`: the paper's event reads `0 > 0`, so it is empty and its probability is `0 ≤ N^{−τ*/6}`.
    The paper's (2.13) holds trivially there, and the Lean statement omits this case.

### 2.6 Weak and strict inequalities

- **Paper.** Theorems 2.2–2.4 use `⩾ 1 − N^{−D}` for the success probabilities and `⩽` or `≤` inside
  the events; (2.12) uses `≥ N^{−τ*/6}` and (2.13) uses `> |A|W/N^{1+τ*/12}`; "for all `N ⩾ N_0`". The
  other strict inequality is the energy range `|E| < 2 − κ` of (2.12) and (2.13).
- **Lean.** The failure events of Theorems 2.2–2.4 use `<`, which is the exact complement of the paper's
  `≤` (§2.4). `RBM.queEvent212` uses `≤` in the same direction as the paper's `≥`, and
  `RBM.queEvent213` uses the weak inequality `≤` where (2.13) has `>`. "For all `N ⩾ N_0`" is
  `∀ᶠ N in atTop`. Theorem 2.5 allows every energy with `|E| ≤ 2 − κ`.
- **Relation.** Identical, except for the energy range of Theorem 2.5, where the Lean domain is larger
  (Lean stronger; since `κ` is arbitrary, the two are also equivalent), and the event of (2.13), where
  the Lean's weak inequality is stronger than the paper's strict one (§2.5).

### 2.7 A separate exponent `τ'` for the error in Theorems 2.3 and 2.4

- **Paper.** One `τ` bounds the domain (`η ≥ N^{−1+τ}`) and the error (`W^τ`).
- **Lean.** Two independent positive exponents: `τ` in `N^{−1+τ} ≤ Im z` and `τ'` in `W^{τ'}`.
- **Relation: Lean stronger.** Taking `τ' = τ` gives the paper's statement.

### 2.8 Spectral parameters and energies as sequences

- **Paper.** Theorem 2.3: for fixed `κ, τ, D` and `z = E + iη` with `|E| ≤ 2 − κ`,
  `1 ≥ η ≥ N^{−1+τ}`, there is `N_0` such that for `N ⩾ N_0` the bound holds. This is one probability
  bound for each `z` (the maximum in (2.3) is over `x, y` only). Theorem 2.4 is the same. Theorem 2.5
  takes `max_{E:|E|<2−κ}` of the probabilities, with one `N_0`.
- **Lean.** For every sequence `z N` with `0 < Im z N ≤ 1` and `|Re z N| ≤ 2 − κ` for all `N`, and
  `N^{−1+τ} ≤ Im z N` for large `N`, the bound holds for large `N`. Theorem 2.5: for every sequence
  `E N` with `|E N| ≤ 2 − κ`; the maxima over `a` and over `A` are inside "for large `N`". Theorem 2.6:
  a fixed energy, as in the paper.
- **Relation: equivalent.** The uniform statement implies the sequence statement. Conversely,
  `RBM.eventually_forall_of_forall_sequences` is a compiled diagonal argument: if the bound held along
  every admissible sequence but not uniformly, one could choose a bad point at infinitely many `N` and
  obtain one bad sequence. It gives one `N_0` for all `z` (respectively `E`) in the domain, that is, the
  paper's form. (The base sequence needed by the lemma is `z N = i`, admissible when `κ ≤ 2` and
  `τ ≤ 1`; otherwise the domain is empty.) Applying the lemma to the five theorems takes a few lines; the
  results are not stored as separate declarations.

### 2.9 Correlation functions without densities (Theorem 2.6)

- **Paper** (p. 11): `ρ^{(k)}_H` is the `k`-marginal of the joint density of the unordered
  eigenvalues, and (2.18) is about `∫ O(α) ρ^{(k)}_H(E + α/N) dα`.
- **Lean.** `RBM.corrPairing` defines this pairing directly as
  `M^k (M−k)!/M! · E Σ_{i_1,…,i_k distinct} O(M(λ_{i_1} − E), …, M(λ_{i_k} − E))`, with `M` the size.
  By symmetry of the joint density this equals the paper's integral whenever the density exists; the
  Lean definition does not need a density. (The equality with the density form is not compiled.)
- **Relation: identical** on the matrices the paper considers.

### 2.10 The GUE side of (2.18)

- **Paper.** `ρ^{(k)}_{GUE}`, with the GUE normalized as the invariant law `H_∞` of the
  Ornstein–Uhlenbeck flow (2.19).
- **Lean.** `RBM.Gauss.gueMatPairing` is `RBM.corrPairing` for the matrix `Xmat` under
  `RBM.Gauss.gueMeasure d N`: independent Gaussian coordinates with `E|h_ij|² = 1/M` (diagonal
  variance `1/M`, off-diagonal real and imaginary parts `1/(2M)` each), the law of `H_∞`. The Lean
  conclusion is `RBM.Gauss.BulkUniversalityMat d κ`: for all `|E| ≤ 2 − κ`, all `k` and all test
  functions `O`, `RBM.Gauss.bandPairing − RBM.Gauss.gueMatPairing → 0`.
- **Relation: identical.** The Lean compares with the GUE matrix, not with an explicit formula for the
  GUE eigenvalue density; both describe the same object.

### 2.11 Test functions

- **Paper:** "smooth test function `O` with compact support".
- **Lean:** `RBM.IsTestFun O` is `C^∞` with compact support. **Identical.**

### 2.12 One probability space for all `N`

- **Paper.** One probability space for each `N` (the dimension of `H` changes with `N`).
- **Lean.** `RBM.Gauss.P d` is a product measure over the coordinates of all indices `N`; the matrix at
  index `N` reads only the coordinates of level `N`.
- **Relation: equivalent.** Every statement concerns one index at a time, so only the law at level `N`
  matters, and it is the paper's law.

### 2.13 The index set

- **Paper.** Indices `i ∈ Z_N`, blocks `I_a = {aW, …, aW + W − 1}`.
- **Lean.** Indices `(a, α) ∈ Z_L × {0, …, W−1}`, with `E_a` of (2.5) as `RBM.Eblk`, `Θ_L(ξ) =
  (1 − ξS^{(B)})^{−1}` as `RBM.Theta`, `m_sc` as `RBM.msc`.
- **Relation: identical** under the bijection `i ↦ (⌊i/W⌋, i mod W)`.

---

## 3. Uniformity in (W, L)

**The two forms.** In the paper, `N_0` depends only on `(c, κ, τ, D)` (and on `τ*`, respectively on
`k, O, E` and the accuracy, for Theorems 2.5 and 2.6). It is uniform over all admissible pairs
`(W, L)`: `L ≥ 3`, `W ≥ N^{1/2+c}`, `N = WL`. The Lean statements have the form "for every
`d : RBM.Gauss.Dims`, for all large `N`". The two forms are equivalent. The argument below is a paper
argument; it is not compiled.

**Uniform ⇒ Lean.** Fix `d`. For large `N`, the pair `(W N, L N)` is admissible with the same `c` and
size `M = W N · L N ∈ [N/2, N]` (by §2.3, `N^{1/2+c} ≤ W N` gives `M^{1/2+c} ≤ W N`). The law of the
matrix at index `N` is the paper's law for this pair (§2.12). Apply the uniform statement at size `M`
and convert with (R1)–(R3) of §2.3.

**Lean ⇒ uniform.**
1. The probability of the event at index `N` depends only on `(W N, L N)` (and on `z N` or `E N`):
   `Xmat d N` reads only the level-`N` coordinates, their variances `RBM.Gauss.gvar` depend only on
   `S^{(B)}` and `W` at that level, and the eigen-decomposition is a function of the matrix.
2. Suppose the uniform statement fails for some constants. Then there are admissible pairs
   `(W_j, L_j)` (with spectral parameters `z_j` or energies `E_j`, if present) at infinitely many
   distinct sizes `M_j`, each violating the bound at size `M_j`.
3. Build one `d` with the same `c`: at `N = M_j` put `(W, L) = (W_j, L_j)`; at every other `N` put the
   filler `L = 3`, `W = max(1, ⌊N/3⌋)`. At `N = M_j` we have `WL = N` and `W_j ≥ N^{1/2+c}`, so the Lean
   event and threshold at index `N` are exactly the paper's at size `M_j`. The filler satisfies
   `W N ≥ 1` and `L N ≥ 3` for all `N`, `3⌊N/3⌋ ≤ N ≤ 6⌊N/3⌋` for `N ≥ 3`, and
   `max(1, ⌊N/3⌋) ≥ N/3 − 1 ≥ N^{1/2+c}` for large `N` whenever `c < 1/2` (row R4 below). For `c = 1/4`
   this filler is the compiled `RBM.Gauss.Dims.example`, with the bandwidth bound
   `RBM.Gauss.Dims.bandwidth_three`; it also covers every `c ≤ 1/4`.
4. The Lean theorem for this `d` (and the glued sequence `z` or `E`, equal to `z_j`, `E_j` at
   `N = M_j` and to `i`, `0` elsewhere) gives the bound for all large `N`, in particular at `N = M_j`
   for large `j`. Contradiction.
5. If `c ≥ 1/2`, no admissible pair exists (`W ≥ N^{1/2+c} ≥ N = WL ≥ 3W` is impossible), so the
   paper's statement holds vacuously; the Lean hypotheses on `d` are also contradictory for large `N`.
6. For Theorem 2.6 the same gluing applies to a subsequence on which the difference in (2.18) stays
   above some `ε > 0`. The glued `d` satisfies `LSY22' d`, since [51] holds along any sequence of sizes.

**Row R4.** `max(1, ⌊N/3⌋) ≥ N/3 − 1 ≥ N^{1/2+c}` for large `N` if and only if `1/2 + c < 1`; the slack
is `1/2 − c > 0`.

---

## 4. The external input [51]

The paper uses one result from the literature that the Lean proof does not prove: the fixed-energy
universality of Dyson Brownian motion, [51, Theorem 2.2], in Step 1 of the proof of Theorem 2.6
(p. 12, (2.21)). In Lean it is the hypothesis `h51 : RBM.Gauss.LSY22' d` of `RBM.Paper.theorem2_6`.

### 4.1 The statement in arXiv:1609.09011v4

[51] considers `H_t = V + √t W` with `V` a deterministic diagonal matrix and `W` a GOE matrix. Its
(2.7) defines `p^{(k)}_{H_t}(λ_1, …, λ_k) = ∫ p^{(N)}_{H_t}(λ_1, …, λ_N) dλ_{k+1} ⋯ dλ_N`, where
`p^{(N)}_{H_t}` is the symmetrized eigenvalue **probability** density. Theorem 2.2 of [51]: let `V` be
`(g, G)`-regular (Definition 2.1), `g N^σ ≤ t ≤ N^{−σ} G²` (2.8), `|E| ≤ qG`; then for every `k` and
`O ∈ C_c^∞(ℝ^k)`,

```
| ρ_{fc,t}(E)^{−k} ∫ O(α) p^{(k)}_{H_t}(E + α_1/(Nρ_{fc,t}(E)), …) dα
    − ρ_sc(E)^{−k} ∫ O(α) p^{(k)}_{GOE}(E + α_1/(Nρ_sc(E)), …) dα | ≤ C N^{−κ}.   (2.9)
```

The factors `ρ_{fc,t}(E)^{−k}` and `ρ_sc(E)^{−k}` are part of (2.9) in arXiv:1609.09011v4; earlier
versions printed (2.9) without them.

### 4.2 The form used in Lean

The change of variables `α = ρβ` gives, for any `ρ > 0`,

```
ρ^{−k} ∫ O(α) p^{(k)}(E + α/(Nρ)) dα = ∫ O(ρβ) p^{(k)}(E + β/N) dβ.
```

So (2.9) says that, after each side's test function is dilated by that side's density, `O ↦ O(ρ·)`,
with `ρ = ρ_{fc,t}(E)` on the first side and `ρ = ρ_sc(E)` on the second,

```
∫ O(ρ_{fc,t}(E) β) p^{(k)}_{H_t}(E + β/N) dβ − ∫ O(ρ_sc(E) β) p^{(k)}_{GUE}(E + β/N) dβ → 0.
```

- `RBM.Gauss.LSY22'` states exactly this, with the pairing `RBM.corrPairing` of §2.9, for
  `H_t = RBM.Gauss.dbmMatrix` (`V + √t · Xmat`, with `Xmat` under the GUE measure
  `RBM.Gauss.gueMeasure`) and with the GUE in place of the GOE (§4.4). The matrix size is
  `M = RBM.Gauss.msize d N`.
- The premises are those of [51], required for large `N`: Definition 2.1 of [51]
  (`M^δ/M ≤ g ≤ M^{−δ}`, `G ≤ M^{−δ}`, and `RBM.Gauss.IsRegular51`: (2.2) `c ≤ Im m_V(E + iη) ≤ C` for
  `|E| ≤ G`, `g ≤ η ≤ 10`, and (2.3) `|v_i| ≤ M^{C_V}`); the free-convolution equation (2.5)
  (`RBM.Gauss.IsFreeConv51`); the density `ρ_{fc,t}(E) = lim_{η↓0} Im m(E + iη)/π` (2.6); (2.8); and
  `|E| ≤ qG`. `ρ_sc` is `RBM.Gauss.rhoSc`.
- The rate `C N^{−κ}` is weakened to "tends to 0", and the premises are required only for large `N`.
  The sequence form rests on the standard reading that the constants of [51] depend only on the fixed
  parameters (`δ, σ, q, c, C, C_V, k, O`).
- `RBM.Gauss.scaledPairing_eq_pow_mul` records the identity between the two normalizations
  (`ρ^k` times the dilated pairing).

### 4.3 A consistency check of the normalization (`k = 1`)

For `k = 1`, `p^{(1)}` is `N^{−1}` times the mean eigenvalue density, so

```
ρ^{−1} ∫ O(α) p^{(1)}(E + α/(Nρ)) dα = E Σ_i O(Nρ(λ_i − E)).
```

Average this over `E` against `φ((E − E_0)/ℓ)/ℓ`, with `φ ≥ 0` smooth, `∫ φ = 1`, and a mesoscopic
scale `N^{−1} ≪ ℓ ≪ 1`. Since `O(Nρ(λ − E))` has width `1/(Nρ) ≪ ℓ` in `E`, the average is
`(Nρ)^{−1} ∫O · E Σ_i φ((λ_i − E_0)/ℓ)/ℓ` up to lower-order terms. By the local law at scale `ℓ`, this
tends to `(ρ_true(E_0)/ρ(E_0)) ∫O`, where `ρ_true` is the limiting density of the matrix (`ρ_{fc,t}` for
`H_t`, `ρ_sc` for the GOE or GUE). With `ρ = ρ_true`, as in (2.9) of arXiv:1609.09011v4, both averages
tend to `∫O` and their difference tends to 0, consistently with the bound `C N^{−κ}`, which is uniform in
`|E| ≤ qG`. (This check is a paper argument; it is not compiled.)

### 4.4 The complex Hermitian case

[51, Theorem 2.2] is stated for the real symmetric case (GOE). The band matrix of the paper is complex
Hermitian, and (2.21) compares with the GUE. The Remark following Theorem 2.2 in arXiv:1609.09011v4
states that the methods and results of [51] hold also for the complex Hermitian case, with essentially
only notational changes; the paper's footnote at Step 1 of the proof of Theorem 2.6 (p. 12) cites it in
this form.

### 4.5 What the Lean proves around the input

- **The GUE local law** (`RBM.Gauss.GUELocalLaw`) is proved inside Lean, by
  `RBM.Gauss.gueLocalLaw_of_band` (§5.7).
- **The premises of `LSY22'` hold with high probability** in the situation where Step 1 uses it:
  `RBM.Gauss.eventually_step1Good_gue` shows that the relevant diagonal matrix is `(g, G)`-regular
  and that its free-convolution density exists and is close to `ρ_sc`, with probability at least
  `1 − N^{−D}`. In particular `ρ_{fc,t}(E) > 0` there, which (2.9) presupposes.
- Applied to such a GUE-derived `V`, `LSY22'` gives `RBM.Gauss.gue_translation'`: bulk GUE statistics
  at unit density do not depend on the energy. This is a known property of the GUE, so this use of the
  hypothesis yields nothing false.

---

## 5. Where the Lean proof takes a different route

This section describes the places where the Lean proof argues differently from the paper. None of
them changes a statement of §1. For each item: the paper's step, the Lean replacement, and the main
declarations.

### 5.1 The Brownian flow (2.34)

- **Paper.** The characteristic flow uses a matrix Brownian motion `H_u`; the proofs of §5 use Itô's
  formula, the Burkholder–Davis–Gundy inequality (Lemma 5.5) and stopping times.
- **Lean.** Two models with the paper's one-time laws:
  - `RBM.Gauss.Grid.H` on the space `RBM.Gauss.Grid.Pg`: a discrete Gaussian random walk
    `H_{u_k} = √s X_0 + √Δ Σ_{i≤k} X_i` with independent copies `X_i` of the band matrix, on a time grid
    of polynomially small mesh `Δ`. The arguments that need the joint law at different times
    (stopping times and martingale bounds, §5.2) are run on this walk.
  - `RBM.Gauss.Hflow`: `H_u = √u · X`. It has the paper's law at each fixed time, but it is not a
    Brownian path. It is used for statements about the law at one time (for example, the identities
    in law (2.39) and (2.66) become pointwise identities in this model).
  - `RBM.Gauss.Grid.map_H_eq` proves that the walk at grid step `k` has the same law as `Hflow` at the
    grid time `u_k`.
- Only one-time laws enter the statements of §1.

### 5.2 Stopping times, martingales and Grönwall on the grid

- **Paper.** §5.3–§5.6 (e.g. (5.39)–(5.48)): Itô expansions of loop observables, BDG for the martingale
  terms, stopping times at thresholds, and continuity arguments in time.
- **Lean.** The same stopping arguments, on the discrete grid of §5.1:
  - one step of the loop hierarchy is a discrete Duhamel expansion with exact conditional
    expectations (`RBM.Gauss.Grid.discrete_hierarchy_step_n`);
  - stopping times are first hitting indices on the grid (`RBM.Gauss.Grid.firstHit`); the stopped
    expansion is assembled pathwise on one high-probability event, uniformly over all grid steps
    (`RBM.Gauss.Grid.grid_assembly_stopped_pathwise`);
  - the martingale terms are bounded by the Azuma–Hoeffding inequality
    (`RBM.Gauss.Grid.azuma_two_sided`, `RBM.Gauss.Grid.highProb_azuma_grid_plainN`) and by Chebyshev's
    inequality at the stopping index (`RBM.Gauss.Grid.cheb_grid_at_stop_plainN`), in place of BDG;
  - self-improving bounds use a discrete Bihari inequality (`RBM.Gauss.Grid.discrete_bihari`);
  - bounds at a fixed time are obtained from moment bounds (`RBM.Gauss.stochDom_of_momentDom`: all
    moments bounded relative to `Φ` imply `≺ Φ`).
- Main results of this part: `RBM.Gauss.step2_gauss_plainN`, `RBM.Gauss.step4_gauss_plainN`,
  `RBM.Gauss.step5_gauss_plainN`, and Theorem 2.21 for the Gaussian model along energy sequences,
  `RBM.Gauss.thm221NoELNReg_gauss` and `RBM.Gauss.thm221RegN_gauss`. Their step hypothesis is (2.72)
  together with `Wℓ_tη_t ≥ N^c` for some fixed `c > 0`; this is the condition `t ≤ 1 − N^{−1+τ}` for
  some fixed `τ > 0` of Theorem 2.21 (p. 24): since `η_t = (1 − t) Im m^{(E)}` and
  `ℓ_t = min((1 − t)^{−1/2}, L)`, each of the two conditions implies the other with another fixed
  exponent.

### 5.3 `N^{−C}` time nets

- **Paper.** Statements uniform in time follow from bounds at each time "by a standard continuity
  argument" or an `N^{−C}` net (Definition 2.1(i), (5.46), p. 51).
- **Lean.** Explicit nets: `RBM.Gauss.netTime` is the `k`-th net point on `[s_N, t_N]`,
  `RBM.Gauss.exists_netTime_close` says every time is close to a net point; a union bound over the
  polynomially many net points and a Lipschitz or Hölder bound in time give the uniform statement (for
  example `RBM.Gauss.unifDomIcc_ldeQuadN`). The mesh exponent is chosen explicitly.

### 5.4 The Ornstein–Uhlenbeck flow (2.19)

- **Paper.** `dH_t = −H_t dt/2 + N^{−1/2} dB_t`, `H_0 = H`.
- **Lean.** Only its one-time laws are used: `RBM.Gauss.ouMatrix` is
  `e^{−t/2} H + √(1 − e^{−t}) H_GUE` with an independent GUE matrix, and `RBM.Gauss.OUFlowLaw` (with the
  instance `RBM.Gauss.ouCommonFlowLaw`) is a family on one probability space with these laws. Steps
  1–3 of the proof of Theorem 2.6 and §7.2 need only these laws.

### 5.5 The GUE phase of §7.2 on a discrete grid

- **Paper** (§7.2, (7.25)–(7.47)): the matrices are driven by a GUE Brownian motion on `[t_1, t_0]`,
  and (7.37)–(7.38) use Itô's formula, BDG and a continuity argument.
- **Lean.** The GUE phase is a discrete Gaussian walk with `(N+1)^{32n_0+64}` steps. (7.37)/(7.38)
  become a discrete Duhamel expansion with a random quadratic-variation control, bounded by dyadic
  layered stopping times and Azuma's inequality in each layer
  (`RBM.Gauss.GUEGrid.gueGrid_loop_duhamel`; the grid process is frozen at the stopping index
  `RBM.Gauss.GUEGrid.gueStop`). The continuous-time quantities of the paper are piecewise-linear
  interpolations of grid values; for example `RBM.Gauss.GUEGrid.gueKproc` interpolates the running
  maximum of `K̃` that enters (7.27). The continuity argument is `RBM.GUEPhase.continuity_argument`.
  (7.27) is bootstrapped for even loop lengths only, and odd lengths follow from the loop bound (6.4).
  Only the law at time `t_0` enters the result (`RBM.Gauss.GUEGrid.gueFlowCommon`,
  `RBM.Gauss.GUEGrid.law726_gueFlowCommon` for (7.26)).

### 5.6 Internal proofs in place of [37] and [70]

The paper cites [37, Theorem 15.3] and [70, Proposition 4.17, Lemmas 4.18, 4.20] in Steps 2–3 of the
proof of Theorem 2.6 (pp. 12–15). The Lean proves each step internally:

| Paper step | Cited result | Lean |
|---|---|---|
| (2.23) ⇒ (2.24): Green's function comparison gives correlation-function comparison | [37, Theorem 15.3] with [70, Proposition 4.17] | `RBM.corrPairing_sub_le_of_claim223` (quantitative: the difference of the `k`-point pairings of `H_0` and `H_{t_U}` is `O(N^{−c′+Ckτ_U} + N^{−τ_U/2} + N^{−1/2})`), proved by decomposing the sum over distinct indices and Poisson smoothing at scale `N^{−τ_U}`; then `RBM.Gauss.step2Output_of_flow` for (2.24) |
| (2.23), the claim "analogous to [70, Proposition 4.17]" | [70, Proposition 4.17] | `RBM.Gauss.claim223_of_flow` |
| (2.25): the time derivative of `E ∏ Im m_t(z_i)` | [70, Lemma 4.18] | `RBM.Gauss.eq225` |
| (2.31): the eigen-decomposition bound | [70, Lemma 4.20] (the paper also says "or use the eigen-decomposition of `G`") | `RBM.norm_green_spectral_identity_blockM_le`, with `M_{y,α}` as `RBM.blockM_eq`; the kernel bounds (2.29)–(2.30) are `RBM.Gauss.expect_L1_weighted_le`, `RBM.Gauss.expect_L2_weighted_le` |

In (2.29)–(2.30) (p. 14), in the bad events `B_y` (p. 14) and `B̃_y` (p. 15) and in `c′` (p. 15), the
paper and the Lean both use `c/36`: (2.12) with `τ* = c/3` bounds `|N ψ^*(E_a − N^{−1})ψ|²` by
`N^{−c/18}`, which bounds `|M_{y,α}|` by `N^{−c/36}`. The probability of the bad event `B_y` is
`O(N^{−c/18})` (in the Lean, `3N^{−c/18}`). Any fixed positive exponent suffices for (2.23).

### 5.7 Step 1 of Theorem 2.6

- **Paper** (p. 12): (2.21) follows from the local law and [51, Theorem 2.2].
- **Lean.** (2.21) is `RBM.Gauss.step1Target_of`. It combines [51] (`LSY22'`) with the local law, the
  rescaling of correlation functions by the free-convolution density, and GUE energy translation:
  - `RBM.Gauss.step1_band'` compares `H_{t_*}` near `E` with the GUE near `0`: conditionally on the
    band matrix `H`, `H_{t_*}` is Dyson Brownian motion started from the diagonal matrix
    `e^{−t_*/2}λ(H) − E`, which is `(g, G)`-regular with high probability, and [51] applies at energy
    `0`; the free-convolution density `ρ_{fc}` tends to `ρ_sc(E)`, and this rescaling is removed
    with an explicit rate;
  - `RBM.Gauss.gue_translation'` compares the GUE near `E` with the GUE near `0`, by a second
    application of [51], to a diagonal matrix built from an independent GUE matrix;
  - the averaged GUE local law needed there is proved inside Lean from the local law of the band
    model itself: for `L ≡ 3` (`RBM.Gauss.dL3`) every pair of blocks is adjacent, so
    `S_ij = 1/(3W)` for all `i, j` and the band matrix is a GUE matrix of size `3W`; a GUE matrix of
    any other size `M` is, after rescaling by `√(M′/M)`, a principal `M × M` minor of one of size
    `M′ = 3⌈M/3⌉`, and Cauchy interlacing (`RBM.Gauss.eigenvalues₀_submatrix_interlace`) transfers the
    averaged local law (`RBM.Gauss.gueLocalLaw_of_band`).
- The paper explains (2.21) in the same way, in the sentence after (2.21) (p. 12), and takes
  `τ_* ∈ (0, 1)`, since [51] needs `t ≪ 1`.

### 5.8 The proof of Theorem 2.2

- **Paper** (p. 9): (2.10) and the local law (2.3) at `z = λ_k + iη`, `η = N^{−1+τ}`.
- **Lean.**
  - (2.3) is stated for deterministic `z`, while `λ_k` is random. The Lean uses an energy net on
    `[−2+κ, 2−κ]` with mesh `(N+1)^{−4}` (`RBM.bulkNet`), takes the union bound over the net inside the
    probability, and moves from a net point to `λ_k` by the Lipschitz bound
    `|Im G_xx(E + iη) − Im G_xx(E′ + iη)| ≤ |E − E′| η^{−2}` (`RBM.im_green_lipschitz_energy`).
  - It takes `η = N^{−1+θ}` with `θ = min(τ, c, 1)/2 < τ`, so the constant `C` in `|ψ_k(x)|² ≤ Cη` is
    absorbed by `N^{−τ/2}`; the paper uses the same `τ` for `η` and for the conclusion. The fact
    "`ℓ ∼ L`" is `RBM.Band.rpow_le_zScale`.

### 5.9 Other proof-level differences, by theme

These concern intermediate lemmas and change no statement of §1.

- **Explicit constants.** Many deterministic lemmas are proved with explicit constants and explicit
  error terms where the paper writes `O(·)`, `≍` or `≺` (for example the propagator bounds of
  Appendix B and Lemma 2.14, the estimates of Section 6 of the paper, and Lemmas 7.2–7.3).
- **Explicit side conditions.** Conditions the paper leaves implicit are hypotheses of the Lean
  lemmas, for example the bulk condition `|E| ≤ 2 − κ` and `|ξ| < 1` for `Θ_ξ`.
- **Proved where the paper asserts.** The uniqueness of the primitive loops `K` (Definition 2.12), the
  invariance of `K` under cyclic rotation (used in Lemma 3.6), and the translation invariance used in
  Corollary 3.7 are proved, with the needed two-loop bound as a hypothesis.
- **Alternative proofs.** Some lemmas are proved by a different argument with the same or a stronger
  conclusion; for example the bound (3.45) of Lemma 3.11 is proved without the logarithmic factor that
  summing (3.66) over `d_1` would produce.
- **Measurability and integrability.** Measurability of events and integrability of the random
  variables are proved or carried explicitly.

### 5.10 Paper results that the final Lean does not use

- **Definition 3.1 and Lemma 3.2** (canonical partitions and their classification). The Lean indexes
  the tree expansion of Lemma 3.4 directly by the sets of pairwise non-crossing diagonals of the
  polygon (`RBM.TSP`), which is the description Lemma 3.2 gives. So the geometric construction of
  Definition 3.1 and the bijection of Lemma 3.2 are not needed.
- **Appendix A, (A.5)–(A.27), with Lemma A.2** (bounds on `G`-chains). The paper states on p. 85 that
  these results are not used in the proof of the main theorem; the final Lean does not contain them.
- **The band-structure bound for `Θ` and the packaged decay-rate statement.** The Lean uses (2.52)
  directly, for complex `ξ` (`RBM.norm_Theta_apply_le_complex`), together with the two-sided bound
  `‖1 − ξ‖/8 ≤ (1 − ‖ρ(ξ)‖)² ≤ 3‖1 − ξ‖` (`RBM.sq_one_sub_norm_rho_le`, `RBM.norm_one_sub_xi_le`). A
  weaker bound from truncating the Neumann series of `Θ` at the band width, and a separate statement
  that `ℓ̂(ξ)` is the decay length up to constants, are not needed.
