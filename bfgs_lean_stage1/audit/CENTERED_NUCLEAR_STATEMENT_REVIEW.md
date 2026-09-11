# Centered nuclear comparison (main after seventh milestone)

Source: R.tex lines 215–228 and the centered-at-zero contrast at line 296. This independently compiled main unit imports the frozen actual 2×2 spectral norm model. It does not alter that model or treat the shifted counterexample as a BFGS failure.

`nuclearCoords_homogeneous` derives positive degree-one homogeneity directly from the already checked max of a scalar absolute value and the Euclidean norm of an actual linear map. Convexity is inherited from the checked spectral formula. `nuclearCoords_unique_zero` derives positive definiteness from that formula, and `nuclearCoords_sublevel_compact` derives compactness from finite convexity and unique attainment.

`nuclearCoords_inward_error_zero` invokes the general degree-one theorem only after supplying actual convexity and homogeneity of this particular spectral definition. No derivative continuity is assumed. `centered_nuclear_inward` gives the literal IR constants M=0, theta=1/2 on every set. `centered_nuclear_radial` derives RS on each compact set. `centered_nuclear_convergence` proves objective and actual full-BFGS iterate convergence to zero for every AdmissibleBFGSRun of the centered objective; compactness/zero-sublevel boundedness is derived rather than assumed.

`minimizer_matrix_rank` also checks the shifted example's stated rank-one minimizer, using the actual matrix diagonal rank theorem. This additional fact does not change any counterexample hypotheses.

This unit is specifically for real symmetric 2×2 nuclear norms. General matrix dimensions, nonsymmetric matrices, and the spectral operator norm remain separate concrete-family instantiations. No new BFGS conclusion is asserted for the shifted nuclear objective.

Reproduction (scratch source and embedded audit):

- `source scripts/env.sh; lake env lean audit/scratch/nuclear_sym2/CenteredNuclear.lean`
- `source scripts/env.sh; lake env lean audit/scratch/nuclear_sym2/CenteredNuclearAudit.lean`

The source remained outside the main library during the seventh milestone freeze. Its ten theorems are not included in the two-file 101-declaration nuclear counterexample audit. Separate logs and validation are stored beside this file.

Main import `BfgsVerification.CenteredNuclear` and 10-name audit both passed; see `CenteredNuclearAudit.lean`, `centered_nuclear_build.log`, `centered_nuclear_axioms.log`, and `centered_nuclear_validation.log`. The scratch history is retained. These additions postdate seventh milestone f820c46 and await the next whole-project audit.
