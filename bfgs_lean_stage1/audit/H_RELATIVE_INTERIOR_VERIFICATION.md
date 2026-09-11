# H.8 relative-interior convergence — compiled scope

The final import is `BfgsVerification.HomogeneousRelativeInteriorConvergence`.
Four new modules contain 29 public theorems and two concrete definitions:
`HomogeneousLowRankRestriction`, `HomogeneousRelativeInteriorGeometry`,
`HomogeneousRelativeInteriorBounds`, and `HomogeneousRelativeInteriorConvergence`.

`Homogeneous.RelativeInteriorZero A` means zero is in the interior of the actual
convex hull, regarded as a subset of the subspace `span ℝ (A : Set (Vec n))`.
This is exactly the source convention for relative interior in H.8. It is not
an assumed coercivity or ball-radius certificate. The proof derives strict
positivity on the nonzero slope span, an orthonormal coordinate representation,
and a uniform positive Euclidean constant `μ` satisfying
`μ * ‖euclideanVector (Uᵀ.mulVec x)‖ ≤ finiteMaxLinear A hA x` for every x.
The source zero fiber is also derived exactly: F(x)=0 iff Uᵀx=0.

`maxLinear_relativeInterior_complete` uses an actual admissible full-BFGS run
with the actual finite maximum and differentiable accepted points. It proves
F(x_k)→0 and x_k→P, where
`P = fiberPoint Uᵀ (R.H 0) (R.x 0) 0`
is definitionally x₀−H₀U(UᵀH₀U)⁻¹Uᵀx₀. It also proves F(P)=0 and that P is
the unique minimizer of the actual H₀⁻¹ quadratic metric distance over the
entire zero fiber. Since the expression uses only x₀,H₀ and the slope span,
the limit formula is independent of the admissible accepted lengths.
The coordinate-free `maxLinear_relativeInterior_has_limit` derives the
coordinate matrix instead of taking it as additional input.

`maxLinear_recurrent_relativeInterior_convergence` assumes relative interior
only for the actual recurrent gradient set. Finite-alphabet recurrence derives
an eventual tail consisting entirely of those slopes. The new restricted run
preserves x,H,g,α,c₁,c₂, every accepted objective value, and every actual
accepted derivative. Derivative preservation is proved from local equality:
at a differentiable finite maximum, any active slope equals the derivative,
and the finite strict inequalities give a neighborhood with the same linear
germ. Thus neither the restricted gradient alphabet nor actual differentiability
is assumed. The resulting full original iterate sequence converges to the
current-tail formula using H_J and x_J. Original objective values tend to zero,
and original F(P)=0 follows by continuity. The proof does not identify the
original objective globally with its recurrent restriction; that generally
would be false. A coordinate-free recurrent limit export is also provided.

No iterate/matrix convergence, bounded step lengths, bounded iterates, finite
length, or projected convergence is assumed. The original research files are
unchanged. H.7.4 general planar block stitching and the rank≤2 extension remain
separate obligations; this file does not claim they follow from H.8.

Reproduction from the project root after `source scripts/env.sh`:

```
lake build BfgsVerification.HomogeneousRelativeInteriorConvergence
lake env lean audit/H_RelativeInteriorAxiomChecks.lean
```

Actual logs are `audit/homogeneous_relative_interior_full_build.log` and
`audit/homogeneous_relative_interior_axioms.log`. All 31 transitive declaration
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
