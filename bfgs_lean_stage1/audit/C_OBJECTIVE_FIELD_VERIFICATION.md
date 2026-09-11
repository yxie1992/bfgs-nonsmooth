# C actual comparison-field tranche

The four main modules `PlanarSupportNeighborhoods`, `PlanarAmbientFrame`, `PlanarObjectiveField`, and `PlanarFieldRegularity` compile with pinned Lean 4.19.0. The exact import is `BfgsVerification.PlanarFieldRegularity`. All 37 explicit declarations (30 theorems and 7 definitions) passed declaration/type and transitive-axiom checks; the only dependencies are standard `propext`, `Classical.choice`, and `Quot.sound`. The recorded source hashes match. Reproduce with:

```bash
source scripts/env.sh
lake build BfgsVerification.PlanarFieldRegularity
lake env lean audit/C_ObjectiveFieldAxiomChecks.lean
```

Evidence is in `c_objective_field_build.log`, `c_objective_field_axioms.log`, `c_objective_field_declarations.json`, and `c_objective_field_validation.log`. Scratch backups and compiler histories remain under `audit/scratch`.

## Verified scope and source comparison

Finite convex subdifferentials have upper neighborhood control of all actual supports, derived from compact supporting-vector bounds and the closed actual graph. The normalized actual subdifferential at a two-active-branch corner equals the geometrically constructed normal sector. Thus a cutoff plateau containing the whole base sector also contains every normalized supporting vector at every sufficiently nearby point, including smooth branch points and nonsmooth switching points.

The angular comparison field is implemented intrinsically in plane coordinates. An ambient smooth cutoff's derivative in the rotated normal direction is proved equal to the actual angular derivative. For every Euclidean unit normal, the frame recovers the level velocity on a sector plateau and has exactly the prescribed positive normal pairing. No global angle choice, angle branch cut, or assumed derivative formula is used.

The actual objective field is globally defined using a chosen actual support. At every differentiable point the selected support equals the actual gradient. In each regular corner chart the field equals the corresponding level velocity composed with the actual objective on a full neighborhood. This identity removes any dependence on support selection there. Consequently actual C1 branch regularity gives C1 field regularity in smooth charts, while the actual C1 level velocity and finite convex objective give local Lipschitz regularity across corners, even when line segments cross switching sets infinitely often. The field pairs to one with all actual supports at a corner and has the exact gradient-length-times-height visibility formula at smooth points.

These theorems use actual local max representations and actual derivatives. The field lemmas accept the finite cutoff/velocity family; the preceding geometry tranche constructs such cutoffs from separated normal sectors. The remaining global assembly must select the actual finite corner family and apply both tranches together. The final planar affine-critical cluster theorem, endpoint transversality/log-transport and the actual secant quotient are not claimed by these modules. No branch-convexity hypothesis is discarded from those remaining endpoint obligations: it is simply unnecessary for the local field results proved here.

The original report source is preserved. Earlier corrections remain in force: the level velocity is C1 under C2 branches, while the angular cutoff is smooth; the oriented tangent/normal determinant has the previously documented sign.
