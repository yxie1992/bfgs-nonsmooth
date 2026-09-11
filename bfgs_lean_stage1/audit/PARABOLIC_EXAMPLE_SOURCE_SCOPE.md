# Q explicit example: parameter scope and documented extension

The printed example in `report/chapters/Q.tex` uses
`z=(u,2u²-epsilon/2)` and the metric entry
`H22=4u²*A+3*epsilon/2`. Its predicted decrease is `3*epsilon/2`,
whereas its actual objective decrease is `epsilon`. Therefore Armijo is
equivalent to `c1 <= 2/3`; strict Armijo holds exactly for `c1 < 2/3`.
The source explicitly gives this strict-Armijo restriction. The printed
pair alone must not be cited as a witness for constants `c1 > 2/3`.

The formal development also uses the following explicit extension:

```
x = (u, 2u² + epsilon)
z = (u, 2u² - rho*epsilon)
H = [[A, -2u*A], [-2u*A, 4u²*A+(1+rho)*epsilon]].
```

For `A>0`, `rho>0`, `epsilon>0`, and `rho*epsilon<3u²`, both
endpoints lie strictly within their stated active cells. The gradients are
`(2u,1)` and `(6u,0)`. Completing the metric quadratic form gives
`A*(v0-2u*v1)²+(1+rho)*epsilon*v1²`, proving SPD. Its exact unit
BFGS step is `z-x`. Predicted decrease and secant curvature both equal
`(1+rho)*epsilon`; actual decrease is `epsilon`. Armijo holds exactly
when `c1*(1+rho)<=1`; weak Wolfe holds for every `c2>=0` and is strict
for `c2>0`.

For `0<c1<1`, selecting `rho=(1-c1)/(2*c1)>0` gives strict Armijo.
Thus the extended construction covers every ordinary choice
`0<c1<c2<1`. The radial numerator is `2u²+rho*epsilon`, and the
quotient diverges as `epsilon` decreases to zero for each fixed `u!=0`.
The transported direction numerator is `2*rho*epsilon`, giving a
vanishing transported correction. These are individual accepted first
steps with varying SPD metrics. No single infinite run with these
prescribed pairs or matrices is asserted.

This is a documented extension of the example, not a change to the
original research source. Formal coverage and compiler/axiom evidence
are recorded separately when the example modules are complete.
