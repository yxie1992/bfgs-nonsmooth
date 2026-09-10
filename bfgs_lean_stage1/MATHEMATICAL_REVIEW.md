# Informal review accompanying the first Lean draft

This is a mathematical/readability review, NOT compiler feedback and NOT formal
verification. It records why the proposed stages correspond to the supplied proof.

## Source and scope

The requested targets are M.1, M.2, and the stronger M.3 in the consolidated
report. Their actual matrix assumptions are retained. In particular:

- alpha is positive; this is required when bounding the rank-one increment.
- q and beta are positive, so cancellation and logarithms are legitimate.
- the hierarchy ranges from j=1 through j=n; no j=0 claim is introduced.
- the terminal slot e_(n+1)=0 is used explicitly, not inferred from a name.
- q_k need not tend to zero pointwise; only the stated reciprocal means diverge.
- neither bounded matrices nor convergence of the matrices or iterates is assumed.

## Compression arithmetic

Put Delta=det(A). The three scalar identities in the source are

    kappa^2 D = Delta ((kappa-w)^2 + u(r-zeta)),
    Dy = Delta(r-zeta),
    Dgy = Delta((q-u)(r-zeta) - (kappa-w)^2).

Expanding gives

    kappa^2 D = q Dy - Dgy.

With kappa^2=beta^2 q^2 and Dgy>=0, q>0, beta>0:

    D <= Dy/(beta^2 q).

The rank-one addition is bounded using Delta>=0, alpha>=0, beta*q>0 and u<=q:

    alpha/(beta*q) Delta*u <= (alpha/beta) Delta.

The draft implements these scalar implications. It does NOT yet establish that
D, Dy, Dgy, Delta and u are the claimed determinants/Schur quantities of actual
matrices. That is the primary unfinished algebraic task.

## Weighted recurrence

Use an actual finite number n of slots, and r=K/eta. The exact shift identity is

    r sum_(j=0)^(n-1) r^j E_(j+2) + E_1
      = sum_(j=0)^(n-1) r^j E_(j+1) + r^n E_(n+1).

Only after inserting E_(n+1)=0 and E_1>=0 does it give

    K shiftedPotential <= eta weightedPotential.

Multiplying the normalized hierarchy by r^(j-1), summing, and using nonnegative
weights proves

    q_k V_eta(k+1) <= (eta+delta_k)V_eta(k).

The first coefficient is one, so V_eta(k)>=E_(k,1)>0.

## Qualitative reciprocal growth (M.2)

For each A>0 choose eta=A/2 and a fixed tail where delta_k<=eta. Then

    q_k V(k+1)<=A V(k),             q_k<=C V(k).

Logarithms telescope. For a tail starting at J and a block with m+1 terms,

    sum_(i=0)^m log(q_(J+i))
      <= log(C)+log(V(J))+m log(A).

Restoring the first J terms gives an explicit constant B_A with

    sum_(k=0)^(N-1) log(q_k) <= B_A + N log(A)

for every N>=J+1. Given any requested threshold T, take A=exp(-(T+1)); for
N large enough that B_A<=N, the negative logarithmic mean is at least T.

Thus the geometric reciprocal mean, which equals the exponential of that
logarithmic mean, tends to infinity. The arithmetic reciprocal mean dominates
the logarithmic mean since -log(q)=log(1/q)<=1/q-1. This establishes the same
qualitative conclusion as the source's root/AM–GM argument.

This logarithmic route is chosen to simplify formalization. It does not prove a
new rate, nor does it silently replace M.3. The stronger quadratic normalization
requires the separate finite-horizon argument.

## Explicit next checkpoint

Run the pinned compiler, repair elaboration/tactic errors, and inspect the axiom
reports. Only then can any implemented scalar declaration be called Lean-checked.
The principal-minor theorem remains open until the matrix identities,
nonnegativity, basis invariance, combinatorial summation and normalization bridge
are formally proved. A clean build of an implication with those facts as
hypotheses is not a substitute.
