# Reconstructed four-piece objective: exact statement review

The construction resolves the numerical and supporting-plane assertions at
R.tex182–187 by an explicit new witness built from the verified D counterexample.
It does not identify the earlier unsupported attribution as an existing old
formula or claim that such an object never existed. The user has authorized
reconstruction from the report's mathematics. All original research files and
previous release evidence remain unchanged.

The literal model is `ReconstructedFourPiece.family : MaxAffine.Family 2 4`.
Its actual four branch formulas are exported by `literal_branches`, and
`objective_formula` proves the exact identity

    F_R(z) = a F_D(Tz) + a − 1,
    T(u,v) = (u,16v/5),
    a = (25/4)/(c−16d−1) > 0.

Here c,d are the actual certified algebraic D constants. The denominator is
proved positive from D's third supporting error. Using 16d−c instead would
produce a negative scale and is not the construction. No numerical experiment
or unverified algebraic-root approximation enters any proof.

`ReconstructedFourPieceFailureTarget` has no supplied objective, run, minimum,
active branch, curvature, hierarchy or convergence hypothesis. It identifies the
actual literal objective, convexity, every compact sublevel, the optimizer
(−1,5), minimum−1, unique minimization, branch values−1,−1,−29/4 and actual
nonstationarity of the limiting point0. For every original D parameter choice
0<c1≤1/3 and c1<c2<1 it refers to the explicitly constructed
`AdmissibleBFGSRun`. That structure proves positive initial matrix, positive
lengths, nonzero accepted gradients, actual accepted derivatives, both original
acceptance inequalities and the unmodified full inverse-BFGS update. Coordinate
covariance followed by positive objective-value scaling gives the exact point,
matrix and gradient formulas and preserves every accepted length. The target
then proves actual iterates→0, values→a−1>−1 and strict value decrease. These
limits are derived from the proved D orbit, not assumptions of the new run.

The domain change uses an actual invertible matrix. The value change divides
the inverse-Hessian matrices by a and multiplies the gradients by a; merely
scaling values while keeping those matrices fixed would not give this same
trajectory. Root's independent `ObjectiveValueScaling` helper proves that
algebra and has its own ordinary compiler/axiom/peer gate. The reconstruction
freshly rebuilds that frozen helper as a dependency.

`ReconstructedSupportingPlaneTarget` proves actual derivative existence at all
accepted points, actual strictly positive secant curvature, curvature→0, and the
exact recurring intercepts0,0,25/4 at indices3m+j. It then refutes the full SP
predicate on the actual initial sublevel. The proof fixes the positive band
eta=a before the proposed constant C. Successive phase1→2 accepted points have
intercept difference25/4 and decreasing values in that band. Their actual
curvatures tend to zero, contradicting the proposed C bound even if C is
negative. Compactness and the already checked same-domain RS/SP equivalence
also give failure of RS there. No artificial eligibility or small-step premise
is assumed.

This scope certifies the genuine infinite accepted full-BFGS run required by the
source interpretation. It does not assert identity with an old unpublished
execution transcript or add a universal line-search-existence theorem. It also
does not change any source condition or infer blanket nonsmooth convergence.

The two exact targets are checked by full target printing, actual type/axiom
reports for all53 owned declarations and strict Lean type equality. The five
sources and100 transitive main source dependencies are frozen. The fresh owner
run and separate independent review determine the final verification status;
this document is a statement review, not a substitute for those logs.
