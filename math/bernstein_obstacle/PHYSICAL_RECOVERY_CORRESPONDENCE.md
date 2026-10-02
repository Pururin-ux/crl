# Physical Bernstein recovery: scope, literature, and proof obligations

This contribution concerns the positive sampling operator in issue [#97](https://github.com/DomTheDeveloper/crl/issues/97). It does **not** certify completion of stages 5–8 or constitute the independent human faithfulness review required there.

## Exact sources and attribution

- Corrected analytical target: `f2bd41f19ff5afbcca8a23f9afdcdf084364dae4`.
- Implementation base for this contribution: `a1d194ddd892f10cf2598541286be39302c051a1`, branch `formal/bernstein-final-review-base`.
- Lean: `leanprover/lean4:v4.33.0-rc1`; mathlib: `4608056c77c52468b80773e8dcd585ef821c7c5e`.
- `SimplexRecovery.lean` already defines the positive finite-index sampler and proves its oriented-face identities. `SimplexPartition.lean` and `SimplexAffineReproduction.lean` already prove natural-index partition and first moments. These are upstream results, reused rather than claimed as new.
- The new work transports those identities to the bounded `MultiIndex` representation actually used by `simplexSamplingRecovery`. It supplies actual physical estimates and nonnegative continuous conforming mesh recovery under explicit geometric assumptions. Global weak derivatives, interior-supported `H01` approximation and global error terms are proved. Concrete `H1` and `H01` Hilbert spaces are now constructed from actual `L2` classes and weak partials. The full nonnegative `H01` cone is proved weakly sequentially closed. Every fixed smooth interior test input has actual strong Hilbert recovery on a supplied changing family with uniform local shape control and shrinking maximum size.

## Primary literature checked

1. [Kirby–Shapero, arXiv:2311.05880v2](https://arxiv.org/html/2311.05880v2), sections 3–4: the bounds-constrained polynomial set and the smaller coefficient-constrained Bernstein set are distinct. The paper explicitly leaves high accuracy of the smaller set unproved. Its general range-repair construction can also alter strongly imposed boundary conditions. Neither argument closes our physical recovery or clipping theorem.
2. [Guermond, local interpolation on affine meshes](https://people.tamu.edu/~guermond/M661_FALL_2025/chap11.pdf), Theorem 11.13 and Remark 11.19: the relevant ingredients are reproduction of the required low-degree polynomial space, reference-operator boundedness, and uniform affine-map shape control. The general approximation statement need not come from a nodal interpolation projector. For positive Bernstein sampling, reproduce `P1`; do not assume reproduction of all `Pr`.
3. [Hunter, PDE notes](https://math.ucdavis.edu/~hunter/pdes/pde_notes.pdf), Proposition 3.22 and section 3.6: positive-part weak derivatives and mollification justify the density route below. Pointwise truncation is a contraction in `L2`; this does not justify declaring it a contraction in the full `H1` norm. Compact support must remain inside the domain during smoothing. Sections 3.A.1 and 4.C were checked for the Lipschitz-to-weak-derivative transfer, now formalized. Sections 3.5–3.6, Definition 3.43 and equation (4.13) were additionally checked for the Sobolev closure and the full function-plus-gradient Hilbert norm. Equivalence to a gradient-only energy norm still requires the separate Poincare/coercivity bridge.
4. [Bertot's bibliography](https://www-sop.inria.fr/members/Yves.Bertot/pubs.html) records Bertot–Guilhot–Mahboubi's 2011 formal Bernstein work. This contribution makes no claim to be the first formal treatment of Bernstein polynomials. Its preprint was not accessible through the archive in this check; its technical proofs are not used here.
5. [DeGiorgi at `4c1b3077d3782b24065184df4ba59501b2e56fc7`](https://github.com/scottnarmstrong/DeGiorgi/tree/4c1b3077d3782b24065184df4ba59501b2e56fc7): source inspection found `MemW1pWitness.weakGrad_ae_eq_zero_on_zeroSet`, positive-part construction, and supported smoothing. Its C1 integration-by-parts, reflected-test convolution derivative, shrinking-bump, support and weak-partial uniqueness arguments are adapted with Apache-2.0 attribution against the actual `SobolevH01Port` definition. The new joint-L2 weak-limit proof uses actual `Lp` inner products; uniqueness uses pinned Mathlib's distribution fundamental lemma. Bounded-function L2 smoothing uses the a.e. convolution limit and dominated convergence. The older checkout uses Lean `v4.29.0-rc6`; that package as a whole has not been compiled or adopted here. The present patch adds no DeGiorgi dependency.

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
| `hasFDerivAt_physicalPolynomial_eval`, `fderiv_physicalPolynomial_eval`, affine specialization | Actual chain rule for evaluation of multivariate polynomials | Arbitrary differentiable finite coordinate family; formal partials are proved to yield the Frechet derivative |
| `eval_simplexBasisPolynomial`, partial nonnegativity and complete partial sum | The polynomial is the original Bernstein basis; each formal partial is nonnegative and its complete mass is `n` | All barycentric points, including faces; partial mass includes `n=0` |
| `sum_norm_fderiv_affineSimplexBasis_le`, finite-index counterpart | Sum of norms of actual physical basis derivatives is at most `n sum_i ||ell_i||` | Actual affine coordinate maps; no shape bound assumed for this identity |
| `affineSimplexField_eq_simplexField`, actual field derivative and coefficient-difference bound | The original bounded-index field as a function on physical space; derivative error at most `delta n sum_i ||ell_i||` | Uniform coefficient differences; coordinate values at the evaluation point must be barycentric |
| Complete coordinate-hyperplane partition/first moment and `affineSimplexField_affineCoefficients` | Affine reproduction outside as well as inside the simplex | Real coordinates summing to one; no nonnegativity needed, so the identity can be differentiated in ambient space |
| `affinePhysicalSamplingRecovery_eq`, affine reproduction and derivative-error lemmas | Actual original sampler derivative error at most `M h^2 n sum_i ||ell_i||`, and at most `n M C h` under shape scaling | Genuine reconstruction of all physical points; differentiable `f` with `M`-Lipschitz derivative on the physical element |
| `affineBasisCoordinateConstant`, `affineBasisCoordinateDerivative`, reconstruction and inverse identities | The needed coordinates are constructed from an actual full affine basis | Finite-dimensional real normed space; nondegeneracy is encoded by `AffineBasis`, not a derivative oracle |
| `norm_fderiv_affineBasisPhysicalSamplingRecovery_error_le_of_shape` | First-order actual physical derivative estimate on an affine-basis element | Explicit per-element bound `h sum_i ||D lambda_i|| <= C`; a mesh-uniform constant remains to be supplied |
| Physical-element compactness, closedness, measurability and finite-measure lemmas | The actual element is its finite convex hull and has finite measure on measures finite on compacts | Ordinary Borel structure gives measurability; no asserted volume formula |
| The two original `eLpNorm` error estimates | Local value error at most `mu(T)^(1/2) M h^2`, derivative error at most `mu(T)^(1/2) n M C h` | Actual `L2` seminorm, with the measure and element measurability explicit |
| `norm_gradient_sub_eq_norm_fderiv_sub`, its `eLpNorm` version and the physical gradient-error estimates | Riesz identification gives exact equality of the classical gradient and Frechet-derivative difference norms, and the same local gradient bounds | Complete real inner-product space; actual Mathlib gradient, not a supplied gradient oracle |
| `contDiff_physicalPolynomial_eval`, affine polynomial/field/sampler specializations | Actual physical recovery polynomial is globally smooth | Every order `WithTop ENat`; input sampling values require no smoothness |
| `hasWeakPartialDeriv_of_contDiff`, `gradient_component_eq_fderiv_apply` | Integration by parts gives the project's integral-based weak partial derivative; the actual gradient component equals `Df(e_i)` | Global `C1` function, compactly supported smooth tests in an open physical domain; adapted proof attribution above |
| `hasWeakGrad_affineBasisPhysicalSamplingRecovery` | The physical recovery polynomial's classical gradient is its actual integral-based weak gradient | Any open physical domain; no assembled piecewise function is asserted |
| `memLp_continuous_restrict_compact`, `memH1_of_contDiff_of_subset_compact` | Actual scalar and derivative `L2` integrability from compact localization, followed by integral-based `H1` membership | Open domain contained in a compact physical set; no approximation witness assumed |
| `memH1_affineBasisPhysicalSamplingRecovery_interior` | The original positive recovery polynomial belongs to the project's physical `H1` space on the actual simplex interior | Genuine affine basis; no global `H01` or mesh assembly claim |
| `simplexField_lastFace_restrict`, permutation/oriented versions and `simplexSamplingRecovery_orientedLastFace` | The full ambient field restricts exactly to the complete face field; the actual sampler restricts to the actual face sampler | Arbitrary off-face coefficients, which vanish through the basis; extends the upstream special zero-extension identity |
| Physical permutation/facet identities and `physicalSamplingRecovery_subface` | Exact restriction in physical coordinates for faces of any codimension | A `SimplexSubface` is a chain of oriented facet embeddings; vertices and barycentric points are constructed recursively |
| `affineBasisPhysicalSamplingRecovery_sharedSubface`, zero-subface theorem | Equal ordered physical face vertices give equal actual recovered traces; zero input on the entire physical face gives zero trace | Genuine local polynomials; no recovered-value equality assumed |
| `physicalMeshRecovery_eq_on_element`, nonnegativity, finite-cover continuity and support theorems | An actual selected-element function is independent of element choice, nonnegative, continuous on the mesh and compactly supported | Finite affine-basis family with `physicalFacesMatch`, a geometric common-subface condition including edges and vertices |
| `physicalMeshRecovery_zero_frontier`, `continuous_physicalMeshRecovery` | Zero input on the physical boundary yields zero recovered trace and a continuous zero extension | `physicalBoundaryFaces` covers boundary points by whole physical subfaces contained in the boundary; it is independent of the input function |
| AE congruence, neighborhood equality, actual derivative/gradient and local `H1`/weak-gradient transfer | The assembled function has its local polynomial's actual derivatives and integral weak gradient on each element interior | The global interface integral is not asserted by these local statements |
| `memLp_physicalMeshRecovery` | Actual scalar `Lp` membership of the zero extension on the whole ambient physical space | Continuous zero boundary data, finite geometric conforming mesh, compact support |
| `lipschitzWith_of_local_norm_bound`, finite closed-cover pasting | Uniform local radial bounds imply global Lipschitz control, without differentiating at interfaces | Mathlib's one-sided slope fencing theorem along straight segments; finite closed sets exclude incompatible neighboring cells locally |
| `lipschitzWith_physicalMeshRecovery_of_bound`, its existence version | The actual zero-extended recovered mesh function is globally Lipschitz | Compact physical elements give finite bounds for continuous polynomial derivatives; the resulting constant is per mesh, not a uniform family estimate |
| Shrinking-step, difference-quotient bound and limit theorems | Positive steps tend to zero; actual Lipschitz difference quotients are uniformly bounded and tend to the actual derivative almost everywhere | Pinned Mathlib Rademacher; no derivative at every interface assumed |
| `tendsto_integral_physicalDifferenceQuotient_mul` | Integral convergence of the paired difference quotients | Dominated convergence with the explicit bound `C ||v|| ||phi||`; continuous compactly supported test |
| `integral_physicalDifferenceQuotient_mul`, `integral_fderiv_mul_of_lipschitz_hasCompactSupport` | Exact backwards test shift, then genuine global integration by parts | Translation-invariant volume; compactly supported Lipschitz function and `C1` compactly supported test |
| `hasWeakPartialDeriv_of_lipschitz_hasCompactSupport`, weak-gradient and `memH1` versions | Actual integral weak derivative and `H1` membership | Globally Lipschitz compactly supported scalar function; open physical domain, including the whole space |
| `hasWeakGrad_physicalMeshRecovery`, `memH1_physicalMeshRecovery`, `physicalMeshH1Witness` | Genuine global weak gradient and `H1` membership of the actual assembled zero extension, with a constructed explicit witness | Finite geometric conforming affine-basis mesh and zero input on its physical boundary; no weak-gradient witness or Sobolev membership is an input |
| Nonzero-sample and recovery support localization declarations | A nonzero recovery value requires a nonzero actual sample; recovered support lies in the input support thickened by the maximum element diameter | No input positivity assumed; one mesh-independent radius for compact input inside an open domain |
| `physicalShrinkingBump`, `physicalMollification`, support, bound and L2 limit declarations | Actual nonnegative normalized bumps shrink to zero; bounded measurable compactly supported functions converge in L2 under this convolution | A common compact support and global bound give the dominated-convergence majorant; discontinuous derivative components are included |
| Convolution weak-partial and `fderiv_physicalMollification_apply` declarations | Derivatives of the same actual mollification are convolutions with the actual weak partials | Reflected compact test functions, genuine integration by parts and the pinned convolution differentiation theorem |
| `lipschitzH1Witness`, `memH01_of_lipschitz_hasCompactSupport`, nonnegative approximation construction | Construct actual weak-gradient data and one smooth compact sequence converging in both function and every gradient component | Globally Lipschitz compactly supported function with topological support inside an open domain; H01 uses the port's existing `NeZero d` parameter |
| Physical H01, radius and changing-family membership declarations | Actual recovery has H01 and positive smooth approximation data; fixed interior-supported inputs give eventual H01 recovery on shrinking meshes | Finite geometric conformity and boundary-face data; common open domain for the family; no H01 approximation witness is assumed |
| `volume_frontier_physicalSimplex`, `ae_mem_physicalElement_interior` | Actual cell interfaces have zero volume and almost every mesh point lies in an element interior | Pinned finite-dimensional convex-set Haar theorem; no null-interface hypothesis is added |
| Global L2 value/gradient bounds and `tendsto_physicalMeshRecovery_H1_error` | Actual assembled value error is second order and actual gradient error first order; both L2 terms converge across a supplied changing family | Common finite-volume physical set, derivative Lipschitz bound, fixed degree, shrinking maximum size and family-uniform shape bound using local sizes; no quasi-uniformity or Hilbert quotient realization asserted |
| Actual L2 pairing, weak-limit and weak-partial uniqueness declarations | Joint strong L2 limits satisfy the genuine integral weak-derivative identity; weak partials are unique almost everywhere | Actual `Lp` inner products and the pinned distribution fundamental lemma; uniqueness uses an open domain |
| `physicalH1Submodule`, closedness, completeness, norm and function-injectivity declarations | The actual weak-derivative graph is a closed subspace of the L2 Hilbert product; the full Sobolev norm is identified and the function class determines its weak partial classes | Actual finite `PiLp 2` product; no separately postulated Hilbert realization; openness is required for uniqueness |
| `physicalH01Submodule`, test-range, membership equivalence and embedding declarations | Construct the closed Hilbert subspace generated by actual smooth interior test functions and prove equivalence to the port's `MemH01` approximation definition | Full function-plus-gradient H1 norm; the port's H01 bridge retains `NeZero d`; no trace characterization or gradient-only norm equivalence assumed |
| Full physical H01 cone, convexity, closedness and weak sequential closure | Almost-everywhere nonnegativity is a norm-closed convex condition on the actual represented L2 function, hence preserved under weak convergence | The full continuous cone is covered; full positive smooth density and discrete strong recovery are separate obligations |
| `tendsto_physicalMeshH1Element`, `tendsto_physicalMeshH01Element` | Actual mesh recoveries converge strongly in the constructed physical Hilbert spaces for every fixed smooth interior test input | A supplied common-set family, geometric conformity, uniform local shape bound and shrinking maximum diameter; the derivative Lipschitz bound is constructed from smooth compact support |
| `physicalSupportedMeshH01Recovery`, eventual support and strong-convergence declarations | Construct an H01 element at every mesh index: actual Bernstein recovery once support is inside the domain, zero beforehand; the zero branch disappears eventually | No recovered H01/support witness is supplied; nonnegative input gives actual full-cone membership at every index; no sampling of arbitrary H1 equivalence classes |

Degenerate vertex families remain allowed by the initial `C0` results. The later affine-basis specialization provides genuine nondegenerate physical coordinates. The chain rule identifies formal partials with actual **Frechet** derivatives. Trace compatibility is derived from physical common-face vertices. Global `MemH1`, interior-supported `MemH01`, actual Hilbert spaces, full-cone weak closure and strong smooth-input recovery on a supplied changing family are proved. A conventional geometric mesh-family construction, full positive H01 density and physical Mosco/minimizer instantiation remain open.

## Actual mesh construction and the interface obligation

`physicalMeshRecovery` selects an element containing a point and evaluates its actual affine-basis polynomial; outside the finite mesh union it returns zero. `physicalFacesMatch` describes the geometry of element overlaps, not equality of recovered values. The subface restriction theorem proves that choice does not affect the value, including at lower-dimensional intersections. Closed finite-cover pasting gives continuity. A separate geometric boundary-subface cover gives zero boundary trace from zero input data there, and hence a continuous compactly supported zero extension.

To obtain its global Lipschitz bound, each polynomial's continuous derivative is bounded on its compact convex element. Finitely many such bounds give one finite constant for that mesh. The closure of the mesh complement, where the recovered function is zero, completes a finite closed cover of the whole ambient space. Near a fixed point, any cell containing a sufficiently nearby point also contains the fixed point: cells excluding the fixed point can all be excluded by finitely many open complements. Thus the local radial increment bound pastes. A straight-line argument with Mathlib's one-sided slope fencing theorem proves the global bound, without asserting classical differentiability at interfaces.

The global integral weak-gradient transfer is now proved. Positive shrinking difference quotients of a Lipschitz function are bounded by `C ||v||` and converge almost everywhere to `Df(v)` by Rademacher. Pairing with a continuous compactly supported test permits dominated convergence. Translation invariance gives the exact identity pairing the function quotient in direction `v` with the test quotient in direction `-v`. Applying the same limit theorem to a `C1` compactly supported test gives integration by parts. Compact support and the actual measurable bounded derivative components give `L2` integrability. This constructs the global weak-gradient witness and `MemH1` of the assembled function without any assumed interface derivative or supplied Sobolev witness.

These are actual functions and proved properties under explicit geometric mesh assumptions. The Lipschitz constant obtained by compactness is per mesh. The global error theorem instead uses one uniform local-size coordinate shape bound, so it does not require this compactness-derived Lipschitz constant to be uniform. Constructing a family satisfying those geometric/shape data and the ambient normed physical-space realization remain separate obligations.

## Interior support and actual H01 approximation

The nonzero-sample lemma implies `tsupport B_h f` is contained in the closed thickening of `tsupport f` by the maximum diameter. Compact support inside an open domain has a positive distance margin in this precise thickening sense. All sufficiently fine actual recoveries therefore have support inside the domain.

For each compactly supported Lipschitz recovered function `u`, choose normalized nonnegative smooth bumps whose outer radii are `delta/(n+1)` and inner radii half as large. Their convolutions with `u` are smooth and supported in one compact thickening still inside the domain. Pinned Mathlib's Lebesgue differentiation theorem gives almost-everywhere convergence for bounded measurable derivative components. A common compact support and uniform convolution bound provide an integrable square-error majorant, giving actual L2 convergence by dominated convergence.

Reflecting the compact test function in the weak-derivative identity proves that the derivative of this same convolution is convolution with the actual weak derivative. Thus the sequence converges jointly in function and gradient, satisfying the port's actual H01 definition. Nonnegative input remains nonnegative under the same mollification. This constructs positive smooth approximation for the Lipschitz compactly supported subclass, not for every member of the nonnegative H01 cone. Zero trace alone is never substituted for the approximation definition.

## Local gradient estimate and the remaining Sobolev transfer

The local derivative estimate and the global L2 error terms are proved in Lean with actual derivative-Lipschitz hypotheses and the safe constant `M` in the quadratic remainder. Actual convex cell boundaries have zero volume, so almost-everywhere interior neighborhood equality transfers the local derivative bound to the assembled gradient. The derivation below explains the sharper analytical `C2` constant `M/2`; that sharper factor is not claimed as a formal result.

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
The Lean proof establishes this bound without needing the degree-lowering reindexing: it differentiates the upstream multinomial polynomial expansion, proves nonnegativity of the evaluated formal partials, and obtains complete partial mass exactly `r`. The actual polynomial chain rule then gives the same total operator-norm bound in physical coordinates.
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

The formal global gradient bound uses `h_T sum_i ||D lambda_i|| <= C` and `h_T <= H` separately. It does not replace `h_T` by the maximum diameter in the shape hypothesis or assume a ratio of minimum to maximum sizes. For a supplied common-domain changing mesh family with `H -> 0`, both actual L2 error terms tend to zero. The uniform shape constant is explicit; deriving it from a conventional geometric mesh-family definition remains open. Pointwise sampling is applied to smooth representatives, not to arbitrary `H1` equivalence classes.

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

The weak Mosco condition follows from `K_h^B subset K`, where the physical nonnegative `H_0^1` cone is norm closed and convex, and therefore weakly closed. Actual full-cone weak sequential closure is now proved; no nestedness is required. For a continuous symmetric coercive bilinear energy with a bounded linear load, recovery, weak compactness, weak lower semicontinuity and uniqueness give convergence of discrete minimizers. Convergence of the energies and coercivity then upgrade weak convergence to strong convergence. The specific physical energy/coercivity and minimizer transfer remain to be instantiated formally in the constructed Hilbert space.

## Actual Sobolev Hilbert realization and smooth recovery

The ambient space is `PiLp 2` of `d+1` actual scalar `L2` classes. Its first coordinate represents the function; the other coordinates represent the weak partials. Each compact smooth integration-by-parts condition is a continuous linear functional on this product. Their kernel intersection is the actual weak-derivative graph. It is closed and complete, with

`||z||^2 = ||u||_L2^2 + sum_i ||G_i||_L2^2`.

Weak-partial uniqueness proves that the represented function class determines the whole graph element. Actual witnesses embed independently of their chosen gradient data. The H01 space is the closure, inside that graph, of actual smooth compactly supported functions inside the open domain. A proved equivalence identifies this closure with the existing simultaneous function/weak-partial L2 approximation definition. No boundary-trace assertion is substituted for that equivalence.

The nonnegative cone is the preimage of the actual L2 nonnegative cone under the continuous function-coordinate map. L2 order closedness and pointwise convexity give norm closedness and convexity. The existing Hahn–Banach separation argument then proves weak sequential closure of this actual full H01 cone.

For each fixed smooth compact interior test input, its continuous compactly supported second derivative gives a finite bound and therefore a global Lipschitz bound for its first derivative. This constant depends on the input, not on the mesh. The proved global error terms consequently converge in the actual H1 product topology under local shape control and shrinking maximum size. The support margin gives eventual actual H01 membership. The constructed H01 recovery is zero at indices whose recovered support is not yet inside the domain, and actual Bernstein recovery at every subsequent sufficiently fine index. It converges strongly in H01 and preserves nonnegativity at every index. This proves the smooth-input stage of the proposed diagonal construction; it does not supply general positive H01 smooth density, a conventional geometric family, the energy/coercivity bridge or complete Mosco convergence.

## Remaining formal obligations

1. Instantiate a conforming physical mesh family and obtain one uniform bound for the actual coordinate norms from its stated shape-regularity assumptions. The affine-basis coordinates themselves are now constructed.
2. Connect the constructed full-H1-norm H01 Hilbert space to the specific coercive physical energy/minimizer formulation, including any required Poincare equivalence. The actual quotient graph, norm, zero-trace closure and smooth-input strong recovery are proved. General zero-trace H01 membership without interior support is not asserted.
3. Construct nonnegative smooth density for every element of the full H01 cone. The Lipschitz compactly supported subclass is covered by an actual constructed witness; positive-part weak chain rule and H1 continuity for the general cone remain open.
4. Instantiate the discrete coefficient-constrained physical family, diagonal full-cone strong recovery, moving Mosco and minimizer theorems. Actual full-cone weak sequential closure is proved; it does not replace strong recovery.
5. The distinct sharp-rate branch: local-size risky sets, one-ring grading, uniform broken regularity, tube measure, coefficient clipping and physical-boundary compatibility.
6. Independent qualified human faithfulness review. Kernel checking alone does not provide it.

## Reproduction

From `math/bernstein_obstacle/lean`, using the pinned toolchain:

```text
lake build BernsteinObstacle.PhysicalRecoveryHilbert
lake build BernsteinObstacle.SamplingQuadraticGuard
lake env lean PhysicalHilbertRecoveryAudit.lean
```

The audit prints every new theorem's axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted here; neither `sorryAx` nor project-specific axioms are acceptable. A saved transcript documents an actual run, not the unformalized arguments above.

The initial focused run on 2026-10-02 Minsk time audited the first 27 new theorems with exit 0 and no axioms outside that whitelist; its retained transcript is [PHYSICAL_RECOVERY_FOCUSED_AUDIT_2026-10-02.txt](audit_packets/PHYSICAL_RECOVERY_FOCUSED_AUDIT_2026-10-02.txt). The full upstream library was not rerun by that focused check.

The expanded focused run on the same Minsk date compiled the physical derivative, coordinate, geometry, and `L2` leaves and audited all 59 new theorems with exit 0 and no axioms outside that whitelist. Its actual output and SHA256 hashes of the seven additional source modules are in [PHYSICAL_GRADIENT_FOCUSED_AUDIT_2026-10-02.txt](audit_packets/PHYSICAL_GRADIENT_FOCUSED_AUDIT_2026-10-02.txt). This is a scoped check, not a claim that the full upstream library or the unformalized Sobolev arguments passed.

The subsequent focused run on the same Minsk date compiled the classical-gradient and local-Sobolev leaves with their dependencies and audited all 73 new declarations with exit 0 and no axioms outside that whitelist. Its actual output and SHA256 hashes of the four additional modules are in [PHYSICAL_SOBOLEV_FOCUSED_AUDIT_2026-10-02.txt](audit_packets/PHYSICAL_SOBOLEV_FOCUSED_AUDIT_2026-10-02.txt). This verifies the local weak-derivative and `H1` bridge; it does not verify mesh assembly, positive smooth density, Mosco convergence, the sharp clipping rate, or the full upstream library.

The assembly-focused run on the same Minsk date compiled physical subfaces, assembled local Sobolev transfer and global Lipschitz pasting, then audited all 111 new declarations with exit 0 and no axioms outside that whitelist. Its actual output and SHA256 hashes of the six additional modules are in [PHYSICAL_ASSEMBLY_FOCUSED_AUDIT_2026-10-02.txt](audit_packets/PHYSICAL_ASSEMBLY_FOCUSED_AUDIT_2026-10-02.txt). This verifies the described assembly and per-mesh Lipschitz properties, not global integral weak derivatives/`H01`, positive smooth density, Mosco, the sharp rate or the full upstream library.

The global-Sobolev focused run on the same Minsk date compiled the global `H1` leaf and its dependencies and audited all 126 new declarations, including the constructed `physicalMeshH1Witness`, with exit 0 and no axioms outside that whitelist. Its actual output and SHA256 hashes of the three additional modules are in [PHYSICAL_GLOBAL_SOBOLEV_FOCUSED_AUDIT_2026-10-02.txt](audit_packets/PHYSICAL_GLOBAL_SOBOLEV_FOCUSED_AUDIT_2026-10-02.txt). This verifies the integral-based global weak-gradient and `H1` bridge, not `H01`, the ambient Hilbert realization, a changing mesh family, positive smooth density, Mosco, the sharp rate or the full upstream library.

The H01/uniform-error focused run compiled the final `PhysicalGlobalError` leaf and dependencies (3527 jobs, exit 0) and audited all 159 new declarations, including the actual approximation constructions, with exit 0 and no axioms outside the whitelist. Actual output and SHA256 hashes of the six additional source modules are in [PHYSICAL_H01_UNIFORM_FOCUSED_AUDIT_2026-10-02.txt](audit_packets/PHYSICAL_H01_UNIFORM_FOCUSED_AUDIT_2026-10-02.txt). This verifies the interior-supported H01, bounded positive smoothing and actual changing-family error terms described above. It does not verify a constructed conventional mesh family, the ambient Hilbert quotient, full-cone positive density, Mosco, the sharp rate, independent human review or the full upstream library.

The Hilbert-recovery focused run compiled the final `PhysicalRecoveryHilbert` leaf and dependencies (3622 jobs, exit 0) and audited all 224 new declarations with exit 0 and no axioms outside the whitelist. Its actual output, timestamp and SHA256 hashes of the five additional source modules are in [PHYSICAL_HILBERT_RECOVERY_FOCUSED_AUDIT_2026-10-02.txt](audit_packets/PHYSICAL_HILBERT_RECOVERY_FOCUSED_AUDIT_2026-10-02.txt). It verifies the actual H1/H01 Hilbert realization, full-cone weak closure and fixed smooth interior-input strong recovery on a supplied changing family. Full-cone positive smooth density, a conventional geometric family, complete physical Mosco/minimizer instantiation, the sharp clipping rate, independent human review and the full upstream library remain outside this check.
