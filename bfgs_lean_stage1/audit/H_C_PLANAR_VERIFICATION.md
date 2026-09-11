# Module H.C planar unbounded-below theorem

Status: 20 public theorems and two concrete definitions compile under the pinned
Lean toolchain and pass independent transitive axiom checks. Root integration
is a separate whole-project audit. Original `H.tex` is unchanged.

The completed source claim is Theorem H.C's **planar unbounded-below** dichotomy,
including the endpoint observation H.7.2 and H.7.3. The broader H.7.4 statement
for all finite-value planar runs, its recurrent-effective-dimension extension,
and H.8's relative-interior theorem remain separately tracked obligations.

## Exact final theorem

`AdmissibleBFGSRun.maxLinear_planar_unbounded_complete` takes:

- a finite nonempty actual slope set `A : Finset (Vec 2)`;
- an actual `AdmissibleBFGSRun 2 (Homogeneous.finiteMaxLinear A hA)`;
- `¬ BddBelow (Set.range (Homogeneous.finiteMaxLinear A hA))`.

It proves there is no stationary support vector zero at any point and exactly
one of the following alternatives (`Xor'`):

1. x_k→0, F(x_k)→0, every F(x_k)>0, and the entire value sequence is strictly
   decreasing;
2. F(x_k)→−∞ and the actual Euclidean norm of x_k→∞.

There is no assumed gradient alphabet, bounded iterate set, bounded displacement,
step-length bound, matrix convergence, eigenvalue bound, point convergence,
or independently supplied transition-rank condition. The slope membership is
proved from actual differentiability of the finite maximum. Norm escape uses
`euclideanVector` explicitly; the finite-Pi norm used by intermediate continuous
linear maps gives the same point topology and is not substituted for the
Euclidean norm in the escaping conclusion.

## Proof chain and source comparison

- The two exact endpoint pairings are g_k·x_(k+1)=F_k−d_k and
  g_(k+1)·x_(k+1)=F_(k+1). On the zero-value branch, Armijo derives summable d,
  hence both endpoint pairings tend to zero.
- `pairMatrix a b` is the actual matrix whose rows are a and b.
  `pairMatrix_det` identifies its actual determinant with the explicit 2×2
  determinant. The inverse estimate uses its actual nonsingular inverse and
  the operator norm of its continuous linear map. A finite double sum of these
  norms supplies the uniform coefficient for every independent slope pair.
  Dependent pairs may also occur in A; their inclusion in this finite total sum
  adds no inverse-nonsingularity assumption.
- `maxLinear_independent_anchors_tendsto_zero` proves the source anchor statement
  for every sequence of transition indices tending to infinity. It imposes no
  bound on anchor gaps and no advance bound on endpoints.
- A negative objective direction w is derived from global unboundedness below.
  All actual slopes pair negatively with w. A direct 2×2 identity shows that
  distinct positive-active slopes with this common negative direction have
  nonzero determinant. This is an algebraic proof of the source's exclusion of
  dependent transitions for this branch. Actual positive curvature already
  excludes unchanged gradients. No opposite-pair or independent-transition
  premise is retained in the final theorem.
- H.A supplies the actual value dichotomy. In the zero branch every transition
  is independent, giving endpoint and then full point convergence to zero. In
  the escaping branch, the proved finite-slope Euclidean bound |F(x)|≤C‖x‖₂
  gives norm escape. The two limit alternatives are formally proved exclusive.
- Global unboundedness below excludes a zero supporting vector anywhere;
  therefore the zero point limit in the first alternative is nonstationary.

## Reproduction and audit artifacts

```bash
cd bfgs_lean_stage1
source scripts/env.sh
lake build BfgsVerification.HomogeneousPlanarEscape
lake env lean audit/H_C_PlanarAxiomChecks.lean
```

Files: `HomogeneousPlanarAlgebra.lean`, `HomogeneousPlanarEndpoints.lean`,
`HomogeneousPlanarEscape.lean`. Logs:
`audit/homogeneous_planar_full_build.log`,
`audit/homogeneous_planar_axioms.log`.
All 22 transitive axiom closures are subsets of `propext`, `Classical.choice`,
and `Quot.sound`. No sorry/admit/custom mathematical axiom/native_decide/unsafe
computation is used. The algebra module allows 800,000 elaboration heartbeats;
this is a finite compiler resource limit, not an untrusted computation or proof
assumption.
