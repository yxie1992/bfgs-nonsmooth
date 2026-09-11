# Independent review: actual ordered roots on signatures

All seven frozen source files were read in full, including the three complete
targets, actual ordered-root and signature definitions, and the invoked
multiplicity-chart interface. A fresh PeerAudit.lean checked29 actual declaration
types/transitive axioms and three strict target equalities, plus an independently
restated full actual ordered-fiber smoothness theorem. Seven source and ten
frozen dependency hashes match. Actual logs are peer_axioms_contracts.log and
peer_validation.log. No defects were found.

The signature records actual degree, distinct real-root count and total real-root
multiplicity. It does not contain continuity or smoothness. Distinct-root count
alone would be insufficient: disappearance and splitting in different clusters
can compensate. The proof correctly uses both actual counts and the local
multiplicity upper bounds. Equality of the total budget saturates every positive
base capacity; equality of the distinct counts forces one actual root in each
cluster. Disjoint equal-radius intervals then force increasing matching with the
actual orderEmbOfFin enumeration. The actual multiplicities are preserved, not
merely a chosen label or weight.

The cluster radius is chosen for each requested epsilon before its parameter
neighborhood. Restricting the neighborhood to the actual signature supplies the
degree/count equalities. The resulting branch continuity and local multiplicity
constancy are derived, including on lower-dimensional and multiple-root strata.
The value zero outside the valid root index is only a totalization convention;
every exported continuity/smoothness statement requires a valid actual index.

The ambient smooth extension comes from the actual (m-1)st derivative's
simple-root chart. Continuity keeps the chosen root inside the chart, and the
proved actual multiplicity equality places it in the proper stratum. The proof
therefore obtains equality with the smooth chart locally within the parameter
set; it does not assert persistence throughout an ambient parameter neighborhood.
ContDiffWithinAt follows with the actual base equality, and the global
ContDiffOn theorem re-centers the same signature at each of its points.

The actual root ordering and exhaustion lemmas correctly include zero/empty
families via valid-index and nonzero-polynomial hypotheses. Semialgebraicity of
signatures/graphs and the finite cylindrical-cover induction remain separate
obligations. This scope does not replace them by a decomposition premise.
