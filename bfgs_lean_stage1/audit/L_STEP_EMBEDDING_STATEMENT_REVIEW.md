# Literal Module L countably affine embedding

Main integrated scope: seven files, 76 explicit declarations and three exact target types. This tranche implements the literal step-ramp variant in Module L, including its actual multidimensional objective, countable affine residual, local geometry and exact scaled copies. It reuses the released common numerical data from `LEmbeddingObjective`: mu=1/4096, center=(2,-32), q_i=g_i-mu*center and b_i=q_i dot center. Their actual closed scalar parameter bounds are derived from the certified seed data. The original research source is unchanged.

## Actual objective and global geometry

`LStepEmbedding.residualBranch` consists of the three actual step scalar functions evaluated at q_i dot x, followed by x_2. The actual residual is their finite attained maximum. The objective adds the literal Euclidean quadratic mu*sqNorm(x)/2. Equality with the finite maximum of the four printed full branches is proved. Convexity and mu-strong convexity follow from the actual scalar convexity and quadratic, and the source lower bound, unique zero and compact sublevels are derived. No assumed smoothness is placed on the step branches.

The origin is proved nondifferentiable using two actual global lower supports, zero and x_2, with contact at zero: differentiability would force both zero derivative and the second-coordinate derivative. This argument does not use a total `fderiv` value at a nonsmooth point.

`CountableIndex` is explicitly Option(Fin 3 times Option Nat), with its countability proved. The corresponding continuous linear maps and constants are explicit: the fourth branch, each negative scalar branch, and every positive geometric affine line. The residual is proved the actual **attained maximum** of this countable affine family at every point. No global local-finiteness claim is made at zero, where scalar breakpoints accumulate.

## Derived local polyhedrality and the actual Hessian

The two printed vectors q_0 and q_1 have a proved trivial joint kernel, by their exact rational coordinates. Consequently the residual is strictly positive at every nonzero point. Any originally active scalar branch there has a nonzero scalar argument, because a zero argument gives scalar value zero. These facts are derived, not supplied as active-set or rank hypotheses.

Each such scalar branch is locally the maximum of two affine functions, by the checked scalar step construction and composition with its actual linear form. The fourth branch is affine. The existing inactive-gap theorem removes originally inactive pieces on an actual neighborhood, and a finite product enumeration gives an actual finite maximum of affine functions for the residual near every nonzero point.

The generic `FiniteAffineLocal.affine_of_differentiable` proves that an actual locally finite affine maximum is locally affine wherever differentiable. It derives agreement of active derivatives using local contact and Fermat's theorem, and combines that with the inactive-gap reduction. It assumes neither branch independence nor convexity as an extra premise. Applying it to the residual after subtracting the actual quadratic gives a local affine germ at every differentiability point of the full objective. Nonsmoothness at zero is used to exclude the sole accumulation point.

`AffineQuadraticGerm` differentiates the literal quadratic plus affine map twice, including actual derivative existence. Local equality then identifies the actual full derivative field and its actual derivative. Thus at **every differentiability point** of the objective, the second Frechet derivative exists and its literal `RadialHessian.matrix` is exactly mu*I. This strengthens the source's restriction to twice-differentiable points and does not infer anything merely from Lean's total derivative convention.

## Exact copies and nonstationary centers

The fixed open copy neighborhood is all y with abs(q_i dot y)<1/2 for every i and y_2<1; it contains zero. A helper accepts the root's smaller norm(y)<1 neighborhood with the same linear inequalities. The copy point is exactly a_n*center+a_n*y, with the source a_n=(1/128)^n and constant Cstar=1+mu*sqNorm(center)/2.

The complete closed scalar plateaus prove the exact first-three branch identities. The fourth residual is strictly negative on this neighborhood while the first scalar residual is nonnegative, so the fourth full branch is strictly below the first. Therefore the actual maximum satisfies F(copyPoint n y)=a_n^2*(Cstar+Q_mu(y)). The proof is valid for every n including zero; the source requires only n>=1. Function values at the copy centers are exactly a_n^2*Cstar and strictly positive.

Nonstationarity at each copy center is also derived. A zero supporting vector there would imply a global minimum of F. The actual local-copy identity would make zero a local minimum of the convex quadratic seed Q_mu, hence a global minimum, contradicting its checked actual nonstationarity. No active-gradient alphabet is presumed in this argument.

## Validation and remaining composition

`bash audit/verify_l_step_embedding.sh` freshly rebuilds the seven files with the pinned toolchain, prints all 76 explicit declarations' transitive axioms, checks three exact target types with strict `Meta.isDefEq`, and verifies frozen source hashes. Its Python checker only checks source/log integrity; it performs no mathematical computation. No proof placeholders, custom axioms or unchecked calculations are present.

Exact targets: `lStepEmbeddingGeometry`, `lStepEmbeddingPolyhedral`, and `lStepEmbeddingCopies`. The actual full-BFGS bad-run transfer and fixed identity-initialization transformation are separate parent-owned composition steps. This tranche supplies their literal objective and exact open local model; it does not substitute an assumed hierarchy, recurrence, trajectory, eligibility or convergence premise for those steps. The source's transformed fixed Hessian statement is likewise left for the shared affine-coordinate composition.

Main source integration preserves the frozen source modulo owned import prefixes. The delivered reproduction script, declaration inventory, both source manifests, axiom and exact-contract files are self-contained and require no scratch files. Independent peer review is recorded separately; scratch validation is not a substitute for main build evidence.

Independent source/proof review passed with no defects: audit/L_STEP_EMBEDDING_PEER_REVIEW.md. The reviewer read all seven files and 76 declarations, matched the frozen source hashes and all standard-axiom reports, and independently reran the three exact target contracts in audit/l_step_embedding_peer_contracts.log. The delivered main full build/axiom/contract/hash run also passed in audit/l_step_embedding_validation.log.
