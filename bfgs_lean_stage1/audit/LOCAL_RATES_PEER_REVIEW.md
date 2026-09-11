# Independent local-basin and rate review

Reviewed CompactSolutionBasin.lean, RateBudgets.lean, and ObjectiveRates.lean against Module T's local nonunique-minimizer paragraph and the first two rate paragraphs in Module F (`report/chapters/families.tex:92–108`). No mathematical defect was found.

The local basin assumes a neighborhood of **every** point attaining the minimum; compactness and the minimum outside its interior supply a strictly positive gap. The basin is chosen before the universal quantifier over actual admissible runs and initial SPD matrices. Certificates are restricted to the original K∩U, accepted containment is derived from Armijo, and solution-set distance is explicitly Euclidean. No unique-minimizer assumption is used for value/distance convergence; the optional uniqueness conclusion is separate.

The finite reference bound has the correct last-iterate index N and actual denominator S_N=∑_{k<N}1/q_k. The generic square-root lemma requires S>0, which is derived from the actual q_k positivity for N>0. Linear cumulative corrections remain an explicit assumption; this is correctly not advertised as a rate for arbitrary band certificates. The little-o statement is exactly sqrt(N)*gap(N)→0 and is derived from actual full-BFGS superquadratic reciprocal growth.

The homogeneous potential has exactly the source coefficient (1-c₁)/c₁. Its weighted-sum bound is telescoped from the actual potential step, and objective monotonicity converts it to the last-iterate square bound. The asymptotic theorem requires only a lower bound along the run, derives the zero-value limit and positivity, and obtains global gradient bounds from homogeneity. No compactness or iterate/matrix convergence is added. The coercive norm-rate wrapper derives its positive Euclidean lower constant; it does not assume that estimate separately.

Source-coverage note sent to root: the low-level `homogeneous_sqrt_bound` takes nonnegative values along the run. To expose the finite source theorem directly under only a run lower bound, add a wrapper deriving that nonnegativity by the same argument already used in `homogeneous_value_rate`. This is a statement-coverage refinement, not a defect in the proved implication.

Exact statements and transitive axiom checks for the reviewed declarations are recorded in `LOCAL_RATES_PEER_AUDIT.lean` and its compiler log. The later quadratic-plus-coercive-gauge rate is outside this review.

Independent audit result: all 19 reviewed declarations type-check; only propext, Classical.choice, and Quot.sound appear in their transitive dependencies.
