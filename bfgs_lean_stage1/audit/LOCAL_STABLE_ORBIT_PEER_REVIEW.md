# Independent review of constructive local stable orbits

Reviewed all six modules in `audit/local_stable_orbit_declarations.json`: StableSequenceTransform, StableSequenceEstimates, StableSequence, LocalStableOrbit, StablePositiveDirection, and StableOrbitTargets (25 explicit declarations). This is a review of the stated abstract dynamics infrastructure; applying it to Module L's concrete return map remains a separate obligation.

**Result: no mathematical or statement defect found.** The actual convergent sequence is constructed by a contraction on a complete sequence space. The final theorems assume a strict derivative and the explicit stable/inverse-unstable operator bounds; they do not assume an invariant manifold, an orbit, or orbit convergence.

## Fixed-point construction

The domain `C₀(ℕ,S×U)` is the Banach space of sequences converging to zero, with its actual supremum norm and the product maximum norm. It is nonempty (the zero sequence), and its closed radius ball is complete. Working in this space is not an assumption that the desired orbit exists: a self-map and contraction are proved before its fixed point is obtained.

The sequence transform sets the initial stable component to the freely prescribed a, uses `A s_n + N_s(w_n)` for the next stable component, and uses `B(u_{n+1}−N_u(w_n))` for the unstable component. Only continuity of N at zero and N(0)=0 are needed to prove the transform takes arbitrary C₀ sequences back into C₀; no global continuity extension of the local remainder is presumed. On the closed ball the derived Lipschitz remainder estimate supplies all quantitative bounds.

The stable expression contracts by `‖A‖+δ`, and the backward unstable expression by `‖B‖(1+δ)`. The proof uses the product maximum norm and the same sequence supremum norm throughout. A common K<1 bounds both factors. The boundary case radius zero is safe in the generic fixed-point theorem; positive local radius is established in its eventual application. The fixed-point identities are translated back to the actual forward recurrence using the actual inverse continuous linear equivalence L, rather than a one-sided inverse assumption.

## Strict derivative and quantifiers

`small_lipschitz_ball` derives an arbitrarily small positive ball with the requested δ-Lipschitz remainder from `HasStrictFDerivAt N 0 0`. The contraction constants are chosen from the actual bounds `‖A‖<1` and `‖L⁻¹‖<1`, before choosing the ball or initial stable coordinate. Subtracting the block derivative from T gives the actual remainder with zero strict derivative and zero value.

For every prescribed radius r>0, the theorem finds R>0 before **every** stable coordinate a with ‖a‖≤R. For each such a it constructs a complete forward T-orbit, entirely within the requested radius, converging to zero, and having exactly that initial stable component. All estimates are derived. The main criteria work in arbitrary complete normed stable/unstable spaces; the exact report-facing targets specialize to two stable and three unstable real coordinates. These targets impose explicit norm contraction, not merely a spectral-radius assertion; obtaining compatible coordinates/norms from the concrete L return-map derivative remains part of the application.

`positive_stable_direction` scales an actual vector e with positive linear functional λ(e), obtains a positive initial stable coordinate, and proves the initial full state is nonzero. Its conclusion is **initial** positivity and nontriviality. It does not claim λ(w_n)>0 or w_n≠0 for every later n. Preserving a positive scale for the actual L orbit will require the corresponding concrete recurrence/oracle argument; this is a scope distinction, not a defect in the stated theorem.

## Application boundary and audit

No actual BFGS update, deterministic line-search oracle, affine chart, derivative splitting of L's normalized return map, or persistence of positive scale is hidden in these six modules. Accordingly they do not yet prove L's source counterexample. The target-file comment correctly retains the derivative-splitting and oracle-agreement obligations.

Independent verification of all 25 actual declaration names, standard transitive axioms, six frozen source hashes, and the two strict exact-target checks is recorded below once the final scoped audit is available. This bounded review leaves the released whole-project metadata unchanged.

Independent validation completed: all 25 actual axiom reports match the frozen declaration list and use only `propext`, `Classical.choice`, and `Quot.sound`; all six source hashes match. Both strict `Meta.isDefEq` target checks passed in `audit/LOCAL_STABLE_ORBIT_PEER_CONTRACTS.lean` / `audit/local_stable_orbit_peer_contracts.log`.
