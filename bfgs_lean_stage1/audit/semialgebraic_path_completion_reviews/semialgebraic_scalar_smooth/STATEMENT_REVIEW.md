# Actual semialgebraic scalar smoothness and A's piecewise-C1 assertion

Five frozen proof files, 14 declarations, three exact targets and six strict source/wrapper checks. All initial pinned compiler calls passed; the fresh owner audit is reproduced by `bash audit/scratch/semialgebraic_scalar_smooth/verify.sh`. This scope depends only on the 149 frozen main sources listed in `dependency_hashes.json`. It does not depend on the new semialgebraic-path graph work or assume any decomposition theorem.

The literal source is `BFGS_MASTER_REPORT_LaTeX/report/chapters/affine_geometry.tex:66–75`: along a piecewise-C1 semialgebraic path, the continuous semialgebraic scalar composition is piecewise C1. This scope proves the one-variable regularity fact. The actual semialgebraicity of the chosen path and of its composition are separate graph-construction obligations and are not silently supplied by this theorem.

## Exact statements

`semialgebraic_scalar_smooth_except_finite` has only the genuine semialgebraicity of `{(t,y) | t∈D and y=f(t)}`, written in the established `Option (Fin 1)` coordinates. It derives an actual finite set E such that the actual total function f is C∞ at every t∈D\E. No continuity, differentiability, root choice, finite partition or generic regularity is a premise. In particular, the statement includes arbitrary domains D, whose definability follows from the supplied graph. Boundary or isolated domain points can be in E; it makes no false ambient smoothness assertion at every boundary point.

`continuous_semialgebraic_interval_piecewise_smooth` retains actual continuity on the entire closed interval, including both endpoints, and derives C∞ at every interior point outside a finite set. Empty and singleton intervals require no side condition. This proves the stated C1 consequence with stronger regularity. It does not demand endpoint derivatives or uniform derivative bounds.

The reusable `semialgebraic_function_finite_smooth_pieces` works in every finite parameter dimension, including zero: the actual domain is a finite union of actual semialgebraic pieces, and the actual function is `ContDiffOn ℝ ∞` on each piece. This is obtained from the existing ambient smooth ordered-root extension on fixed actual root-signature strata. It does not assert full-dimensional pieces, connected pieces, a disjoint partition, or global continuity across pieces.

## Proof chain and degenerate cases

1. A one-variable Boolean polynomial formula has constant truth on each actual root-free cut-profile cell. Those cells are open. Their actual finite root boundary therefore contains every point where domain membership fails to provide a neighborhood. Zero polynomials and empty root lists are covered by the existing actual formula/root semantics.
2. A singleton Boolean-polynomial fiber must contain a root of an atom whose whole fiber is nonzero. Otherwise each surviving atom has locally constant sign, every identically zero atom is constant, and the entire formula would hold in a neighborhood of the allegedly unique height. The contradiction uses a literal neighboring real point. Continuity of the unknown function is not used.
3. Split by actual zero-fiber patterns. The product of surviving atoms has a nonzero fiber. Its actual root signatures take finitely many values, with representatives drawn from their actual range. The graph's unique height is one of the actual ordered roots. No numerical root ordering or assumed root alphabet is introduced.
4. For each zero pattern, attained signature and valid root index, intersect the actual signature set with equality of the unknown function and that root. The equality set is semialgebraic by intersecting the two actual graphs and projecting one common height. The existing ordered-root smoothness theorem then transfers to the actual function on this piece.
5. There are finitely many such pieces. In one variable, union their derived finite boundaries. At every remaining domain point, some piece contains a neighborhood. Composing its actual vector-coordinate smoothness with the constant-coordinate map yields actual `ContDiffAt ℝ ∞ f` there.

The zero-dimensional, empty-domain, empty-atom, all-zero-fiber, constant-polynomial, duplicate-atom and multiple-root cases require no added rank or positivity assumptions. A hypothetical singleton fiber with no surviving root is excluded by the local-sign proof; it is not discarded by assumption.

## Audit scope

`source_hashes.json` freezes the five proof files; `declarations.json` lists all 14 names, including three target definitions. `Axioms.lean` prints actual types and transitive axioms. `Contracts.lean` compares each of the three underlying theorem types and each corresponding final wrapper with its complete target using strict definitional equality. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The Python scripts manage builds, text/hash checks and log validation only; they do not evaluate mathematical examples or supply proof facts.

The source remains unchanged. No convergence assertion or constant critical-value theorem is claimed merely from this scalar result; the existing actual A/C application is a separate audited chain.
