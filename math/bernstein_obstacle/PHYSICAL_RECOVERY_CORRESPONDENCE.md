# Physical Bernstein recovery: scope, literature, and proof obligations

This contribution concerns the positive sampling operator in issue [#97](https://github.com/DomTheDeveloper/crl/issues/97). It does **not** certify completion of stages 5–8 or constitute the independent human faithfulness review required there.

## Exact sources and attribution

- Corrected analytical target: `f2bd41f19ff5afbcca8a23f9afdcdf084364dae4`.
- Implementation base for this contribution: `a1d194ddd892f10cf2598541286be39302c051a1`, branch `formal/bernstein-final-review-base`.
- Lean: `leanprover/lean4:v4.33.0-rc1`; mathlib: `4608056c77c52468b80773e8dcd585ef821c7c5e`.
- `SimplexRecovery.lean` already defines the positive finite-index sampler and proves its oriented-face identities. `SimplexPartition.lean` and `SimplexAffineReproduction.lean` already prove natural-index partition and first moments. These are upstream results, reused rather than claimed as new.
- The new work transports those identities to the bounded `MultiIndex` representation actually used by `simplexSamplingRecovery`, and supplies an actual map into a normed physical space, diameter bounds, and local pointwise estimates.

## Primary literature checked

1. [Kirby–Shapero, arXiv:2311.05880v2](https://arxiv.org/html/2311.05880v2), sections 3–4: the bounds-constrained polynomial set and the smaller coefficient-constrained Bernstein set are distinct. The paper explicitly leaves high accuracy of the smaller set unproved. Its general range-repair construction can also alter strongly imposed boundary conditions. Neither argument closes our physical recovery or clipping theorem.
2. [Guermond, local interpolation on affine meshes](https://people.tamu.edu/~guermond/M661_FALL_2025/chap11.pdf), Theorem 11.13 and Remark 11.19: the relevant ingredients are reproduction of the required low-degree polynomial space, reference-operator boundedness, and uniform affine-map shape control. The general approximation statement need not come from a nodal interpolation projector. For positive Bernstein sampling, reproduce `P1`; do not assume reproduction of all `Pr`.
3. [Hunter, PDE notes](https://math.ucdavis.edu/~hunter/pdes/pde_notes.pdf), Proposition 3.22 and section 3.6: positive-part weak derivatives and mollification justify the density route below. Pointwise truncation is a contraction in `L2`; this does not justify declaring it a contraction in the full `H1` norm. Compact support must remain inside the domain during smoothing.
4. [Bertot's bibliography](https://www-sop.inria.fr/members/Yves.Bertot/pubs.html) records Bertot–Guilhot–Mahboubi's 2011 formal Bernstein work. This contribution makes no claim to be the first formal treatment of Bernstein polynomials. Its preprint was not accessible through the archive in this check; its technical proofs are not used here.
5. [DeGiorgi at `4c1b3077d3782b24065184df4ba59501b2e56fc7`](https://github.com/scottnarmstrong/DeGiorgi/tree/4c1b3077d3782b24065184df4ba59501b2e56fc7): source inspection found `MemW1pWitness.weakGrad_ae_eq_zero_on_zeroSet`, positive-part construction, and supported smoothing. That checkout uses Lean `v4.29.0-rc6`; compatibility with this project's pins was **not** established by that inspection. The present patch adds no DeGiorgi dependency.

## Statement correspondence for the new Lean declarations

Let `d,n : Nat`, with `n > 0` whenever lattice samples are used. A `BarycentricPoint d` has `d+1` nonnegative coordinates summing to one. A `MultiIndex d n` has bounded natural entries summing to `n`. All sums below run over the entire index set, including indices whose basis value vanishes.

| Lean declaration | Mathematical content | Scope and assumptions |
| --- | --- | --- |
| `simplexBasis_eq_simplexBasisNat` | Exact equality of factorial and multinomial basis formulas | All `d,n`, including `n=0` |
| `simplexMultiIndex_sum_eq_piAntidiag` | Bijection of bounded and natural complete index sums | Any additive commutative monoid |
| `simplexBasis_sum_eq_one` | Partition of unity for the actual finite basis | All barycentric points, including faces |
| `simplexField_const`, lower/upper bounds | Constants and coefficient interval bounds pass to values | Nonnegative basis, complete partition |
| `simplexSamplingRecovery_const`, interval/subtraction/difference lemmas | Constant reproduction, range preservation, uniform contraction | Positive degree; actual upstream sampler |
| `simplexBasis_first_moment`, `simplexSamplingRecovery_coordinate`, `simplexSamplingRecovery_affine` | Coordinate and affine reproduction in the finite representation | Reuses upstream natural first moment; `n>0` for normalized samples |
| `physicalSimplexPoint`, subtraction/diameter/convexity lemmas | `F_v(lambda)=sum_i lambda_i v_i` and convex physical image | Any real normed space; no inverse map required |
| `physicalSamplingRecovery_nonneg`, constant/affine lemmas | Recovery preserves nonnegativity and physical affine functions | The affine part is an actual linear map |
| `physicalSamplingRecovery_abs_error_le` | Pointwise error at most `L h` | Lipschitz bound on the physical image; vertex diameter at most `h` |
| `physicalSamplingRecovery_taylor_error_le` | Pointwise error at most `M h^2` | Explicit quadratic Taylor remainder bound, not an assumed approximation theorem |
| `norm_taylor_remainder_le_of_lipschitz_fderiv` | Quadratic remainder from actual Fréchet derivatives | Convex set, differentiability at its points, derivative Lipschitz constant `M>=0` |
| `physicalSamplingRecovery_abs_error_le_of_lipschitz_fderiv` | Pointwise recovery error at most `M h^2` | Actual derivative hypotheses on the physical simplex; constant is `M`, not `M/2` |
| `curve_square_sampling_error`, `curve_square_sampling_midpoint_error` | Exact quadratic error and its nonzero midpoint value | Univariate regression guard; reuses Mathlib moments |

Degenerate vertex families are allowed by these `C0` results. They do **not** supply valid physical finite elements, inverse affine maps, volumes, or `H1` derivative estimates. Those require additional geometry. No theorem here identifies a formal polynomial partial derivative with a physical weak derivative.

## Analytical derivation of the remaining local gradient estimate

The following is a mathematical derivation, **not yet a Lean theorem**.

Take a nondegenerate physical simplex `T` with diameter `h_T`, barycentric functions `lambda_i`, and fixed degree `r>=1`. Write

\[
B_T^r w(z)=\sum_{|\alpha|=r}w(x_\alpha) B_\alpha^r(z),\qquad
x_\alpha=\sum_i(\alpha_i/r)v_i.
\]

Assume `w` is `C2` on a neighborhood of `T` and `M_T=sup_T ||D2 w||` uses the Euclidean operator norm. At a fixed evaluation point `x`, keep the affine function
`q_x(z)=w(x)+Dw(x)(z-x)` fixed while differentiating with respect to `z`. Its sampled Bernstein recovery equals `q_x`. Taylor's theorem gives
`|w(x_alpha)-q_x(x_alpha)| <= (M_T/2) h_T^2`.
Partition and positivity therefore give

\[
\|w-B_T^rw\|_{L^\infty(T)}\le (M_T/2)h_T^2.
\]

For the derivative, the factorial basis formula gives, with terms omitted when `alpha_i=0`,

\[
\nabla B_\alpha^r
=r\sum_{i:\alpha_i>0}B_{\alpha-e_i}^{r-1}\nabla\lambda_i.
\]

Reindexing each complete degree-`r-1` sum and using its nonnegative partition yields
`sum_alpha ||grad B_alpha^r(x)|| <= r sum_i ||grad lambda_i||`.
Since `Dw(x)=Dq_x(x)`, differentiating the recovered **fixed** remainder gives

\[
\|\nabla(w-B_T^rw)\|_{L^\infty(T)}
\le (rM_T/2)h_T^2\sum_i\|\nabla\lambda_i\|.
\]

Uniform shape regularity bounds `h_T sum_i ||grad lambda_i||` by a constant depending only on dimension and the shape bound. Thus the gradient error is `O(h_T M_T)`, with a constant also depending on the fixed degree. Multiplication by `|T|^(1/2)` gives the required local `L2` estimates. Squaring and summing over a conforming mesh, with `h=max_T h_T`, gives

\[
\|w-B_h^rw\|_{L^2(\Omega)}\le C h^2 |\Omega|^{1/2}\|D^2w\|_\infty,
\qquad
\|\nabla(w-B_h^rw)\|_{L^2(\Omega)}\le C h |\Omega|^{1/2}\|D^2w\|_\infty.
\]

No global quasi-uniformity is needed for this summation. The per-element shape bound is essential. Pointwise sampling is applied to smooth representatives, not to arbitrary `H1` equivalence classes.

### A concrete guard against an incorrect high-order claim

For fixed `r`, sampling does not reproduce quadratic functions. On `[a,a+h]`, apply the degree-`r` Bernstein sampler to `w(z)=z^2`. The elementary second-moment identity gives the exact error
`B_T^r w(z)-w(z)=(z-a)(a+h-z)/r`.
For a uniform mesh of `[0,1]`, its derivative error has global `L2` norm `h/(sqrt(3) r)`. Thus increasing the fixed polynomial degree does not turn this positive sampling construction into an `h^r` recovery. This example concerns the sampling operator, not the best approximation in the coefficient cone or the solution of the obstacle VI.
The sharp-rate branch must instead use the separate interpolation-plus-clipping argument and all its free-boundary and physical-boundary assumptions.

## Positive smooth density and the moving recovery sequence

This section is also an analytical argument whose formal instantiation remains open.

Let `v>=0` almost everywhere in `H_0^1(Omega)`. From the definition of `H_0^1`, choose `phi_m` in `C_c^infty(Omega)` with `phi_m -> v` in `H1`, and extract a subsequence converging almost everywhere. Put `p_m=phi_m^+`. The value error is bounded by that of `phi_m`. For gradients,

\[
\nabla p_m-\nabla v
=1_{\{\phi_m>0\}}(\nabla\phi_m-\nabla v)
-1_{\{\phi_m\le0\}}\nabla v.
\]

The first term tends to zero in `L2`. In the second, the indicator eventually vanishes where `v>0`; where `v=0`, `grad v=0` almost everywhere by the weak chain rule. Dominated convergence finishes the gradient argument. No full-`H1` nonexpansiveness assertion is used.

Each `p_m` is compactly supported inside `Omega`, but is generally not smooth. Extend it by zero and convolve with a nonnegative smooth mollifier of radius less than half its support distance from `Omega^c`. Choose the radius sufficiently small that the `H1` smoothing error is at most `1/m`. The resulting `w_m` is nonnegative and belongs to `C_c^infty(Omega)`, with `w_m -> v` in `H1`.

For a conforming simplicial mesh, the same physical lattice point on a shared face gives the same sampled coefficient in both elements, with the correct permutation. Boundary-face samples vanish because `w_m` vanishes there; for sufficiently fine meshes even the whole boundary elements avoid its support. Hence assembled recovery lies in `K_h^B`. The local gradient estimate above implies strong `H1` convergence for each fixed `w_m`. Choose monotone thresholds `N_m>=m`, ensuring feasibility and error at most `1/m` for every mesh index `k>=N_m`. Set `m(k)=max {m : N_m<=k}` after the initial indices. Then `m(k)->infinity` and the recovered `w_m(k)` converges strongly to `v`. This is the concrete input needed by the upstream scheduling and Mosco machinery.

The weak Mosco condition follows from `K_h^B subset K`, where the physical nonnegative `H_0^1` cone is norm closed and convex, and therefore weakly closed. It does not require nested meshes. For a continuous symmetric coercive bilinear energy with a bounded linear load, recovery, weak compactness, weak lower semicontinuity and uniqueness give convergence of discrete minimizers. Convergence of the energies and coercivity then upgrade weak convergence to strong convergence. The ambient `H_0^1` Hilbert-space realization and this transfer still need to be instantiated formally.

## Remaining formal obligations

1. A nondegenerate physical simplex/inverse coordinate construction with a uniform shape bound.
2. Actual physical derivatives of the finite Bernstein basis, including the degree-lowering identity and its complete-index sum.
3. Element/global integrals and assembled `H_0^1` membership from shared faces and boundary trace.
4. A concrete nonnegative smooth density construction and the ambient physical Hilbert-space bridge.
5. Instantiation of moving Mosco and minimizer theorems with that construction.
6. The distinct sharp-rate branch: local-size risky sets, one-ring grading, uniform broken regularity, tube measure, coefficient clipping and physical-boundary compatibility.
7. Independent qualified human faithfulness review. Kernel checking alone does not provide it.

## Reproduction

From `math/bernstein_obstacle/lean`, using the pinned toolchain:

```text
lake build BernsteinObstacle.PhysicalSimplexCalculus
lake build BernsteinObstacle.SamplingQuadraticGuard
lake env lean PhysicalRecoveryAudit.lean
```

The audit prints every new theorem's axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted here; neither `sorryAx` nor project-specific axioms are acceptable. A saved transcript documents an actual run, not the unformalized arguments above.

The focused run on 2026-10-02 Minsk time compiled both leaf targets and audited all 27 new theorems with exit 0 and no axioms outside that whitelist. The transcript is [PHYSICAL_RECOVERY_FOCUSED_AUDIT_2026-10-02.txt](audit_packets/PHYSICAL_RECOVERY_FOCUSED_AUDIT_2026-10-02.txt). The full upstream library was not rerun by this focused check.
