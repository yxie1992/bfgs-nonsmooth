# Independent review: translated run and finite search transfer

Result: PASS, no defects found in the four main files TranslatedRun,
TranslatedLocalModel, FiniteSearchTransfer, and TranslatedSearch, frozen by
`audit/translated_run_declarations.json` (16 explicit and 4 generated declarations).

I read all four files and the existing actual deterministic line-search and
simultaneous inverse-BFGS secant-scaling definitions they use. The transformation
is exactly x'=p+t*x, F(x')=A+t^2*Q(x), g'=t*g and H'=H, with t nonzero; it is
not a change to the BFGS algorithm. The actual point recurrence is proved,
both secants scale by t, and the full inverse-BFGS update therefore keeps the
same H sequence. Gradient nonzeroness and all initial SPD/accepted step-length
fields come from the original actual run. The value offset A cancels, and the
factor t^2 is positive for either sign of nonzero t, preserving the accepted
Armijo/weak-Wolfe inequalities.

`Data` explicitly contains actual objective convexity, accepted-point value
identities and actual Frechet derivatives. The later local-model wrapper
proves these fields from one exact objective identity on an open neighborhood.
It uses the actual inverse affine coordinate map to prove derivatives of F;
there is no unproved assertion that Lean's total coordinate gradient behaves
well at nondifferentiable points. Point/value-limit lemmas are ordinary
conditional transfer facts; this tranche does not purport to derive existence
or convergence of the source run.

The general `search_history_congr` theorem compares both strict predicates
only on the source search's actually visited finite history. Its induction
carries arbitrary lower/upper brackets and next trial. It handles immediate
acceptance, Wolfe-driven bracket changes, Armijo rejection, and exhausted fuel.
It proves equality of the whole result, including the accepted option and
ordered attempted-length list, not merely agreement on one successful trial.
No comparisons at unvisited points are required.

`translated_comparisons` preserves the exact strict source line-search
predicates by multiplication by positive t^2. `local_model_search` identifies
both actual base gradients, uses the actual full-BFGS search direction, and
derives each query gradient from the open local identity and the source's
actual differentiability at that query. The query premise includes all actual
source history points, including Armijo-rejected trials, matching the intended
source all-query regularity guarantee. It does not assert all-ray line-search
existence or assume the desired target search history.

The literal Module L local-copy application must still discharge the exact
model, source trajectory, and actual-query membership/differentiability data.
No iterate/matrix convergence, boundedness, line-search outcomes or final
counterexample conclusions are hidden in these generic transfer proofs.

Final validation: I independently checked all four main hashes, compared every proof body with the read scratch snapshot (only imports changed), and reran the full declaration/standard-transitive-axiom validator against the pinned main compiler logs. `audit/translated_run_peer_validation.log` records PASS. The delivered reproduction script `audit/verify_translated_run.sh` uses only main sources and delivered audit files; no scratch dependency remains.
