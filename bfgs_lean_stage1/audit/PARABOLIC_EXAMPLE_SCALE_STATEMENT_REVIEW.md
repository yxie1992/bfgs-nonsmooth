# Printed Q scale: continuation review

This module closes the printed-piecewise-scale obligation recorded in the
frozen fifth-milestone example review. It introduces no new assumptions.

`sourceScale_continuousOn` proves literal continuity of the defined printed
piecewise field on `F>0`. The proof derives each switching-interface value
from the actual closed middle cell and uses equality on the frontiers of
the two strict region predicates. No continuity at zero is claimed.

The actual generic calibration at the two interfaces yields
`k0=k1+1/3` and `k2=k1+1/6`. Thus the printed field equals the generic
selector-free field times `exp(-(k1+1/2))` at every positive-value point.
This factor is a single globally positive constant; no endpoint-dependent
normalization or additional branch selector is introduced.

The vector identity extends to zero because the objective's unique-zero
theorem forces the origin and both radial vectors vanish there. The
resulting constant matrix rescaling of the already derived general
certificate proves `exists_source_bandCertificate`, with its matrix field
equal to the literal printed `outer(theta*r)(theta*r)` at every point,
including the origin. Every compact set, positive band, and original
line-search constant pair is covered, with no assumed transport estimate.

All nine declarations are covered by the scoped axiom audit, and the three
exact type contracts expose continuity, a globally constant normalization,
and the actual printed-field certificate. The scratch copy was preserved during the fifth-milestone freeze; after
commit 137e073 it was copied into the main source tree for the next tranche.
