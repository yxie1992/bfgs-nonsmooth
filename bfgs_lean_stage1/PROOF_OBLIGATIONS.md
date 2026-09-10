# Source-to-formalization map and remaining obligations

Source: `BFGS_MASTER_REPORT.pdf`, Module M, printed pp. 9–10, physical PDF pp. 13–14.
This file is a status register. An item is not proved merely by being listed.

## 1. Exact target — M.1

For arbitrary finite dimension n, actual SPD H, alpha > 0, q = g^T H g > 0,
beta = -y^T H g / q > 0, and s = -alpha H g, prove for 1 <= j <= n:

    e_j(BFGS(H,s,y))
      <= ||y||^2/(beta^2 q) e_(j+1)(H) + (alpha/beta)e_j(H).

`Definitions.lean` defines e_j as sums of the actual j-by-j principal determinants.
No surrogate sequence is substituted in this end-to-end target.

### Matrix-side obligations not yet implemented

M1.1. From SPD H and independent columns Z, prove A = Z^T H Z is SPD/invertible.

M1.2. Relate the actual inverse-BFGS update to

    P H P^T + alpha/(beta q) (Hg)(Hg)^T,
    P = I - (Hg)y^T/kappa,   kappa = g^T H y = -beta q.

M1.3. Prove the rank-two compression determinant identity in arbitrary size:

    det(Z^T P H P^T Z)
      = det(A)/kappa^2 * ((kappa-w)^2 + u(r-zeta)),

with u=a^T A^-1 a, w=a^T A^-1 b, zeta=b^T A^-1 b, and r=y^T H y.
This must remain valid when the compressed projected matrix is singular.

M1.4. Prove both Schur-complement / Gram determinant identities and the
nonnegativity of the larger Gram determinant. No unjustified invertibility of
that larger Gram matrix is permitted.

M1.5. Prove the exact rank-one determinant increment and 0 <= u <= q.
The candidate scalar bounds in `CompressionAlgebra.lean` only finish the
arithmetic AFTER these matrix facts have been supplied.

M1.6. Prove the principal-sum/basis identities: orthogonal-conjugation invariance,
e_1=trace, e_n=determinant, e_(n+1)=0, and nonnegativity for SPD H.

M1.7. In an orthonormal eigenbasis, establish the combinatorial identity

    sum_{|I|=j} det Gram_H(y,E_I)
      = sum_{|J|=j+1} (product_{i in J} lambda_i) (sum_{i in J} y_i^2)
      <= ||y||^2 e_(j+1)(H).

M1.8. Assemble M1.1–M1.7 into an actual proof of `PrincipalMinorHierarchyTarget`.

**Critical warning:** passing M1.3, M1.4, or M1.7 as hypotheses proves only a
conditional assembly lemma. It is NOT end-to-end formalization of M.1.

## 2. Normalization bridge from M.1 to the scalar hierarchy

With c>0, beta_k>=c, and ||g_k||<=G, derive

    q_k e_j(H_(k+1))
      <= (4G^2/c^2)e_(j+1)(H_k) + (d_k/c)e_j(H_k),
    q_k <= G^2 e_1(H_k).

Also supply nonnegativity of the entries, positivity of e_1, and e_(n+1)=0.
For a nontrivial infinite run n>0. Show d_k/c has the `UpperNull` property from
Tendsto d 0, and assemble the actual run into `NormalizedHierarchy`.

These are not yet implemented. The scalar library intentionally makes this
interface explicit rather than concealing it as an axiom or a renamed theorem.

## 3. Implemented candidate proof scripts — weighted and qualitative growth stage

`ScalarHierarchy.lean`:

    V_eta(k) = sum_(j=1)^n (K/eta)^(j-1) E(k,j)
    q_k V_eta(k+1) <= (eta+delta_k)V_eta(k)
    E(k,1) <= V_eta(k).

The terminal term is included in `shift_identity` and is removed only with
E(k,n+1)=0. For any requested A>0, take eta=A/2 and select a single tail on
which delta_k<=eta. That gives q_k V(k+1)<=A V(k), q_k<=C V(k).

`ReciprocalGrowth.lean` then gives candidate proofs for:

    sum_(k=0)^(N-1) log q_k <= B_A + N log A      eventually,
    -(1/N) sum_(k<N) log q_k -> infinity,
    (product_(k<N) q_k^-1)^(1/N) -> infinity,
    (1/N) sum_(k<N) q_k^-1 -> infinity.

The finite prefix is explicitly retained and absorbed into B_A. The arithmetic
mean uses log(u)<=u-1 rather than AM–GM. This is a disclosed presentation change
of the source's qualitative scalar argument; it is not a new mathematical claim.

All these scripts are currently UNCOMPILED. Even after successful compilation,
the exported result `hierarchy_reciprocal_growth` is conditional on the explicit
hierarchy until the bridge in section 2 is checked.

## 4. M.3 — not yet implemented

Retain the source's explicit finite-horizon lower bound. Required steps:

* product bound over a fixed tail J;
* AM–GM for eta+d_k/c and for the positive reciprocals;
* choose eta=D_J/[c(m-1)] while keeping J fixed;
* bound V_eta(H_J) polynomially in m and prove its m-th root tends to one;
* deduce liminf S_N/N^2 >= c/(2D_J);
* only then let J increase, so D_J -> 0, obtaining S_N/N^2 -> infinity.

`SuperquadraticReciprocalTarget` freezes the end-to-end statement but has no proof.
The qualitative M.2 theorem does not imply M.3 without these additional steps.

## 5. Acceptance criteria for the next stage

A successful `lake build` and clean transitive axiom audit are necessary but not
sufficient to claim the full result: the exported theorem signatures must be
reviewed for unproved assumptions equivalent to the desired conclusion.

Do not introduce a matrix bound, convergence of H_k, convergence of x_k, positive
curvature beyond the BFGS conditions, or finite gradient alphabets. These are not
hypotheses of the source result.
