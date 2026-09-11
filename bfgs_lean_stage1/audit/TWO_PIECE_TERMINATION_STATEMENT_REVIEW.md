# Actual two-piece termination: source and statement review

Scope: the pre-existing two-piece result cited at H.tex403–408, with the literal
objective `abs(x0)+x1`. Attribution remains [Xie–Wächter,
arXiv1712.08571v1](https://arxiv.org/html/1712.08571v1), SectionsII–IV.
The formalization also proves the no-infinite-continuation conclusion for the
actual arbitrary-dimensional independent-linear-form objective. It does not
claim finite termination for the report's general many-piece model.

Nine frozen Lean sources contain 68 explicit declarations and two exact targets.
`bash audit/verify_two_piece.sh` rebuilds each source in dependency order, prints every actual type
and transitive axiom report, checks both exact target types and validates hashes.
This is fourteenth-milestone work; the public reproduction uses delivered main files only.

## Actual scalar data and the finite proof

At a differentiable point, the actual gradient is `(sigma,1)` with sigma²=1 and
sigma*x0=abs(x0)>0. Actual weak-Wolfe curvature forces the sign to alternate.
Write the actual symmetric matrix entries as aa,bb,cc and define

- A=aa+2*sigma*bb+cc, the actual gradient energy;
- B=aa+sigma*bb, the signed first direction component;
- D=aa*cc-bb², the actual determinant;
- X=abs(x0).

A andD are positive by actual SPD; B is positive by actual weak Wolfe. The full
unmodified inverse-BFGS formula gives the exact recurrences used by the proof.
They are not scalar hypotheses in the final target. Both off-diagonal matrix
entries are retained. No iterate/metric limit, boundedness or matrix accuracy is
assumed.

The scalar potential is psi=B*X/D. Its exact change is
`psi-psi_next = 2*B²*(X-alpha*(B-A/2))/(A*D)`.
Full Armijo bounds this below by `c1*alpha*B²/D`. If two more transitions can
continue, their positive B values force `D<alpha*B²`. Thus the drop is strictly
greater than c1. A finite telescoping bound contradicts an infinite positive
potential sequence. The two-step look-ahead is derived from the supposed
infinite continuation; it is not imposed on a current line-search rule.

## Exact termination meaning

`twoPieceTermination` proves convexity and, for every valid fixed c1,c2, that the
reverse actual accepted-transition relation on differentiable SPD states is
well founded. The relation includes actual displacement, full update, Armijo,
weak Wolfe and the next actual derivative. This rules out every infinite choice
of accepted steps, not just a selected successful implementation. It additionally
constructs a finite reachable terminal state from every such initial state.

A terminal state has no actual differentiable acceptable step. The ray has at
most one point of nondifferentiability. If its asymptotic slope were nonnegative,
the proved actual finite-bad-ray step-existence theorem would construct another
accepted step and its SPD next state. Therefore that slope is negative. The
actual objective on the terminal search ray tends to minus infinity.
This describes mathematical termination through failure of an acceptable
length; it does not assert that every possible numerical line-search program
detects the unbounded direction after finitely many oracle calls.

`twoPieceLinearImage` proves no infinite actual full-BFGS run exists for F∘Q
when Q has full row rank, in arbitrary finite dimension, and for
`abs(dot u x)+dot v x` when u,v are linearly independent. The actual projected
matrix is Q H Qᵀ and its full update/derivative tests are proved by the existing
projection theorem. No off-plane components or derivative assumptions are
discarded. The arbitrary-dimensional target is explicitly no-infinite
continuation; the detailed terminal-ray target is the literal two-dimensional
model. The report's two-piece citation is thereby kept separate from its new
many-piece escape theorem.
