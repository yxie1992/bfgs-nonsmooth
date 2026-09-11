# Exact translation, scaling, and finite-search transfer

Four main modules contain 16 explicit declarations plus four Data constructor/projections. The complete types and transitive axiom reports are recorded in translated_run_axioms.log. The delivered source hashes and declaration inventory are translated_run_declarations.json. The self-contained verify_translated_run.sh rebuilds main modules and verifies those reports without a scratch dependency or any external mathematical computation.

For an actual admissible full-BFGS run R on Q and nonzero scalar t, the transferred accepted point is p+t*R.x, the gradient is t*R.g, and the full matrix and accepted length are exactly R.H and R.alpha. Data contains convexity of the actual destination objective and its actual value/derivative at every accepted point. Simultaneous scaling of both actual secant vectors cancels in the original inverse-BFGS formula. Armijo and weak Wolfe follow by multiplication by t²>0. This is conditional transfer infrastructure, with Data discharged in each concrete local-copy application. It assumes no new iterate or matrix convergence.

The open-local-model lemma derives destination Frechet derivatives from the literal identity F(p+t*y)=A+t²Q(y) on an open set. It composes the actual Q derivative with the continuous inverse affine chart and proves local equality with F. It does not merely assign destination gradients. Nonzero t is sufficient; positivity is not required for the transfer theorem.

The general finite-search congruence theorem requires comparison equivalences only at lengths in the source search's actual finite history. Induction over the exact search recursion handles immediate acceptance, weak-Wolfe failure, Armijo rejection, and exhaustion. Both the result and the entire ordered query history are preserved. No oracle equality at unqueried points is assumed.

The concrete local-model search transfer obtains these comparison equivalences from the same open objective identity, actual differentiability at every queried point (including rejected queries), and actual Frechet derivatives at the accepted base. Directional products and function differences scale by t²; the source and destination use the actual coordinateGradient. The required containment and differentiability are explicit local-copy obligations, supplied by the source bad-orbit theorem in the final Module L construction.

Source research files are unchanged. This tranche alone does not prove a bad orbit exists or close Module L's global/local failure targets.
