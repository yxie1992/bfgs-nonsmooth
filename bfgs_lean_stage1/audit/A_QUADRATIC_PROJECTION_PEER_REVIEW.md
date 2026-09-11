# Independent quadratic projection review

Reviewer: convex_gradient. Reviewed all five frozen source modules, the exact targets, their transitive axiom reports, and fresh independently run audit drivers. The five hashes match `source_hashes.json`; all 33 declarations use only the standard allowed axioms; all four strict contracts pass. See `peer_validation.log`, `peer_axioms.log`, and `peer_contracts.log`.

No mathematical or statement defect was found in the delivered scope. The scalar result uses the actual quadratic `a*t^2+b*t+c`, a proved completing-square identity, and actual real roots. Its existential zero, positive, and nonnegative criteria include quadratic, affine, constant, and identically zero cases. In particular, the negative-leading-coefficient inequalities use the actual vertex and the appropriate strict or weak discriminant test.

The semialgebraic results build the actual finite Boolean combinations of polynomial coefficient/discriminant conditions. The universal statements use complements of the correct existential conditions. The coordinate projection is the literal projection of the actual polynomial zero/positive/nonnegative locus, with a proved evaluation identity. The degree-two extension starts from an arbitrary actual polynomial with eliminated-coordinate degree at most two and derives its coefficient expansion; it does not assume a supplied quadratic representation or root oracle. Parameter dimension and parameter degrees remain arbitrary, including dimension zero.

The four target definitions retain all global quantifiers and the actual degree bound. The limitations are accurately stated: these results eliminate one quadratic atom at a time. They do not prove simultaneous multi-atom projection, where a common witness is required, and do not establish arbitrary-degree quantifier elimination, global path decomposition, or the outstanding full Module A theorem.

## Main integration correspondence

The frozen source snapshot above was copied to the five delivered main files listed in `a_quadratic_projection_declarations.json`. Only owned import qualification changed. `a_quadratic_projection_copy_validation.log` records the exact-body comparison. Fresh main compiler, transitive-dependency, strict-contract and hash evidence is recorded in `a_quadratic_projection_validation.log`; `verify_a_quadratic_projection.sh` uses delivered main files only. The original mathematical scope and limitations remain unchanged.
