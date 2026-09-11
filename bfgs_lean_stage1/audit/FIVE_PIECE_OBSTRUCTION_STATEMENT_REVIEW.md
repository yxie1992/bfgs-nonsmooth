# Five-piece obstruction statement review

Source: families.tex, final paragraph of the matrix/line-search section. The
original source is unchanged. Main module `FivePieceObstruction.lean` has 18
explicit theorems and five concrete definitions. `MaxAffineCalculus.lean`
adds five generic actual finite-max derivative theorems.

The actual finite maximum uses slopes (-1,0,0), (0,1,1), (0,-1,1),
(1/4,0,0), (0,0,-1), with zero intercepts. Its nonnegativity, unique zero
minimizer, compact sublevels, and coercivity are proved. No oracle values or
subgradient selection are hypotheses.

For every positive tau, the actual initial point is tau*(-2,0,1), the
initial SPD inverse matrix is tau*I, the actual gradient is (-1,0,0), and
the exact BFGS trial point is (tau*(alpha-2),0,tau). The source's three
ray-value regions are proved directly from the finite maximum. At every
alpha<1 the actual derivative equals the initial gradient. For 1<=alpha<=6,
two active slopes with different second coordinates contradict actual
Fréchet differentiability. For alpha>6 the literal Armijo inequality at
c1=1/4 is inconsistent. The early region contradicts c2=1/2 weak Wolfe.

`no_differentiable_armijo_wolfe` uses the actual BFGS step and ordinary
acceptance inequalities. `obstruction_in_every_neighborhood` constructs
tau before all positive trial lengths and all putative actual gradients.
It proves every neighborhood of the unique minimizer contains such an
initial point with its constructed SPD matrix and genuine derivative.
The source means failure to choose a differentiable accepted next point;
this is not a constructed infinite admissible run or a convergence counterexample.

Build and transitive axiom logs: `five_piece_obstruction_build.log`,
`five_piece_obstruction_axioms.log`, `max_affine_calculus_build.log`, and
`max_affine_calculus_axioms.log`. All explicit closures contain only
propext, Classical.choice and Quot.sound. Full release integration is separate.
