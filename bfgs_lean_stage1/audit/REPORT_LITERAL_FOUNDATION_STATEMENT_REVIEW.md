# Literal Module M closure and audit implementation review

This milestone adds three proof modules, 18 scoped declaration reports and two exact targets. The former principal-matrix and reciprocal-growth theorems already had complete checked proofs; the additional exports certify two literal intermediate assertions that those proofs had replaced by sufficient inequalities. Original research sources and all prior mathematical proof bodies remain unchanged.

## Actual eigenbasis Gram-sum equality

The exact insertion/erasure bijection matches j-element subsets missing a fixed coordinate with (j+1)-element subsets containing it. Product expansion and finite sum interchange prove the literal combinatorial equality, without sign assumptions on scalar factors. Existing actual diagonal Gram determinant identities transfer this to sums of actual determinants, and actual orthogonal coordinate changes give the formula in the original matrix coordinates.

The final PrincipalGramSumIdentityTarget assumes only an actual SPD matrix in arbitrary finite dimension. It constructs the orthogonal diagonalization and positive eigenvalue coordinates before quantifying over every vector and every degree. The summands are determinants of actual Gram matrices with columns [y,U E_I]. No chosen-basis, determinant-identity, matrix-convergence or scalar-hierarchy premise remains. Zero dimension, degree zero and degrees beyond the dimension are included. This verifies foundation94–99 literally while preserving the original hierarchy proof route.

## Sharp actual potential degree and root limit

The finite monomial sum is an actual real polynomial, its evaluation is the actual weighted principal potential, and its degree is at most n−1. The zero-dimensional polynomial is zero. With nonnegative coefficients and t≥1, the actual potential has the sharp constant-times-t^(n−1) bound. No degree or polynomial representation is assumed.

For the actual full-BFGS run, the tail is the actual infinite sum of predicted decreases. Summability and strict positivity prove that this tail is positive. The source's eta=D/[c(m−1)] gives the constructed polynomial evaluated at m−1 and the sharp fixed-tail bound. Actual PSD principal coefficients and positive trace supply the upper and lower bounds proving that the actual mth root tends to one. The polynomial and its fixed coefficient bound precede all horizons; there is no bound uniform over tail index J. The exact final target assumes neither a scalar hierarchy nor a matrix or potential limit. This verifies the degree/root-limit sentence at foundation151 and respects the fixed-tail order at153–155. Historical M149 labels in development comments refer to this same scope;151 is the actual prose line.

Both additions passed fresh owner and independent peer compilation, all18 standard transitive-axiom reports, and independent complete-contract restatements. The aggregate delivered scope must separately pass the ordinary Lean collector before central registration. Compilation and the complete frozen central result are recorded in actual logs, not inferred from this review.

## Shared dependency-graph audit

The revised first audit loop builds the exact outgoing dependency graph of Lean4.19's collectAxioms from the checked environment once. It uses the same constant-info cases and Expr.getUsedConstants traversal. Reverse reachability from every discovered axiom yields every theorem's exact transitive axiom set, including cycles. It does not stop upon finding the permitted axioms. Missing checked constants and checked/elaboration type mismatches fail the audit.

The independent review checks the algorithm case by case against the pinned implementation. Graph-cycle checks and exhaustive comparisons cover every complete milestone17 theorem's actual type and axiom set, plus all152 scoped declaration sets including definitions/fields. The existing ordinary #print axioms and complete target checks remain intact. The new three-module scope also receives ordinary collector checks independently of the shared graph. Exact target-type equality and full theorem enumeration are unchanged.

This is an audit implementation improvement, not a mathematical computation used in a proof. None of the library theorems can depend on this later audit-only namespace. Pinned toolchain, package revisions, original research sources and prior proof bodies are unchanged. The original ordinary complete audit and exhaustive comparison evidence are preserved. The performance result does not justify omitting any theorem or transitive dependency.

## Remaining source resolution

No further retained mathematical proof obligation was identified after the literal M supplement and the completed A/C/I source reviews. R182–187 still refers to an unidentified older four-piece objective. Its printed (-1,5), -29/4 and25/4 attribution is not proved by the separately verified current D objective. E's original19-job execution/archive facts are also absent; the remote has no alternate branch, tag, release asset or Actions artifact supplying them. Current universal Lean proofs cannot identify those missing inputs. The original whole-report flag therefore remains false pending explicit source resolution.

All earlier mathematical corrections and declared research questions remain visible. There is no new blanket BFGS convergence, arbitrary-ray step-existence, floating-point robustness or positive-measure failure assertion. The final status and delivery manifest are promoted only after the complete frozen gate and source/dependency checks succeed.

## Delivered evidence

The complete gate passed with 5,126 explicit theorems, 7,704 total theorem declarations and 251 exact targets. See the [full compiler transcript](report_literal_foundation_check.log), [status register](STATUS.json), [literal M source map](module_m_literal_source_map.json), [ordinary scoped audit](module_m_literal_completion_axioms_contracts.log), and [independent delivery review](module_m_delivery_reviews/MODULE_M_DELIVERY_INDEPENDENT_PEER_REVIEW.md).

The [source-kind validator](../scripts/validate_module_m_literal_source_map.py) checks the actual mapped declarations against the final inventory. The [audit implementation evidence and reproduction commands](cached_axiom_evidence/README.md) include the exhaustive ordinary-collector comparison and optional ordinary full-audit reproduction. These links supplement the reviewed statement analysis above; they change no mathematical claim.
