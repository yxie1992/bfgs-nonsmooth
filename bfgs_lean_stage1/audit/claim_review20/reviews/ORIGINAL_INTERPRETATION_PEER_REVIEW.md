# Original-claim interpretation: independent review

PASS for the final frozen 17-declaration `OriginalClaimInterpretation.lean` source with SHA256 `6f007e1c01f7b9c14f8594605d58abcb220f964c8fb8a967ca8c15b54c38d476`. The reviewer independently read the original 13 theorem bodies and authored three optimizer-completion lemmas and the general reference identity; root independently reviewed all four additions and returned PASS. The review read the actual definitions of homogeneity, optimizer intercept, and variable objective, and the original R setup/interpretation and U example paragraphs. No mathematical or statement defect was found.

The independent `PeerContracts.lean` embeds the owner source byte-for-byte, then restates nine complete propositions and checks definitional equality with the actual theorem types. It imports only the two existing main library modules imported by the owner; it does not trust an owner-built scratch object. A fresh pinned compiler run passed, with all 17 source declarations and nine review definitions receiving ordinary transitive-axiom reports. Every reported axiom is one of `propext`, `Classical.choice`, and `Quot.sound`. Owner source and metadata hashes remained unchanged. `peer_declarations.json` binds the independent driver, exact names and nine strict markers, both original chapters, the pinned configuration, and 134 main import dependency source hashes.

## R: degree-zero qualification and the compact setting

The original `R.tex` setup (lines 19–23) assumes a finite convex objective, an attained minimum, and a compact sublevel strictly above the minimum. Its later homogeneous intercept sentence (line 180) does not explicitly repeat a positive-degree convention. The review distinguishes the algebraic identity in isolation from that chapter-wide setting.

The actual `PositiveDegree p F` definition quantifies over nonnegative dilations, including zero. At degree zero, zero dilation has factor one, so every such function is constant. Its optimizer intercept at zero is zero. The positive constant function `F≡1` is genuinely nonnegative and convex, has a minimizer at zero and an actual zero derivative everywhere, but the unqualified formula `(p−1)F` is `−1`. Thus `unrestricted_zero_degree_formula_fails` correctly tests the displayed algebraic identity without a zero-minimum/positive-degree convention.

That constant example is **not a counterexample to the compact-sublevel theorem**. Every positive sublevel is the entire positive-dimensional space. The new `degree_zero_positive_sublevel_not_compact` proves this fact using the actual sublevel and actual noncompactness of Euclidean space.

More strongly, `compact_nonnegative_homogeneity_positive_degree` derives `p>0` from convexity, nonnegativity, homogeneity, and a compact sublevel with any strict witness `F(z)<b` in positive finite dimension. It does not assume positivity of the degree. For `p≤0`, homogeneity at dilation two and midpoint convexity imply `F(x)≤F(0)`; midpoint convexity at `x` and `−x` then implies equality everywhere. The strict witness then shows that the stipulated sublevel is all of space, contradicting compactness. This argument uses no continuity of gradients, differentiability, or unique-minimizer premise.

`compact_degree_intercept` then proves the source's literal `(p−1)F` formula under those compact-context hypotheses, with only the actual derivative at the evaluation point. The `Vec (n+1)` dimension restriction is essential to the noncompactness argument and accurately states positive dimension; it is not concealed. The theorem makes no assertion about zero-dimensional spaces. The new optimizer-completion lemmas remove any origin convention for an arbitrary optimizer, as follows.

`zero_value_eq_zero_of_compact_sublevel` proves that any zero-valued point of an actually homogeneous objective must be the origin if a sublevel at a nonnegative value is compact. Its entire nonnegative ray has value zero; choosing an explicit dilation larger than the compact set's norm bound contradicts boundedness unless the point is zero. No positive-degree premise is used in this ray lemma.

`compact_homogeneous_minimizer_eq_zero` derives positive degree from the strengthened strict-sublevel hypotheses, then derives `F(0)=0`. Nonnegativity and the actual optimizer inequality give `F(xStar)=0`; the ray lemma gives `xStar=0`. Finally, `compact_homogeneous_optimizer_intercept` proves the displayed formula for **any actual optimizer**, with `IsMinOn F univ xStar` and no assumed `p>0`, `F(0)=0`, or `xStar=0`. Taking the strict witness `z=xStar` recovers exactly the original `b>Fstar` context. Thus neither the level bound nor the origin convention is an added source premise. Root independently read these three added bodies and checked precisely this chain before returning PASS.

The final `degree_intercept_at_reference` also explicitly proves the unrestricted reference-point formula

`optimizerIntercept F xStar x g = (p−1)*F(x) + F(xStar) − dot g xStar`.

It needs only actual homogeneity and the actual derivative at `x`; the reference need not be an optimizer. The often-used `(p−1)F(x)+F(0)` formula is its specialization at reference zero. The new general theorem must not be paraphrased by dropping the `−dot g xStar` term at an arbitrary reference. Its proof expands the actual dot product and uses the existing proved Euler identity, followed by ring normalization. A ninth independent full-type comparison checks this exact formula.

The appropriate source disposition is therefore contextual: the unqualified identity needs its positive-degree/zero-minimum convention stated, while the compact positive-sublevel context already excludes the positive-constant obstruction and supplies a checked route to the original formula. The unrestricted constant example alone must not be described as refuting the chapter's convergence theorem.

## U: the allowed zero-coupling parameter

The original `U.tex` example (lines 399–415) permits `‖c‖<1`, which includes `c=0`. The actual `printedVariableObjective` is the printed formula after the documented coordinate ordering. At zero coupling its objective is exactly

`quadratic x + (sourcePrimitive (x 0) + |x 0|)`.

`zero_coupling_split` proves the algebraic equality for the actual objective. `quadratic_smooth` proves actual global smoothness of the quadratic term. `printed_zero_coupling_has_split` combines those facts with the actual norm restriction, exhibiting both functions in the decomposition. It is an actual global smooth-plus-univariate representation, so it certainly supplies such a local representation as well.

This qualifies the example's explanatory sentence that the jump magnitude changes with the tangential coordinate: that sentence requires nonzero coupling. It does **not** refute the existential heading “The objective need not split…”, nor the convergence or RS-failure claims for the family. Nonzero coupling remains the scope of the existing nonsplitting theorem. A release should not turn this zero-parameter edge case into a claim that no member of the family demonstrates the stated phenomenon.

## Evidence and reproduction

The exact public source and report inventories are in [owner metadata](../metadata/ORIGINAL_reviewed_declarations.json) and [peer metadata](../metadata/ORIGINAL_PEER_reviewed_declarations.json). The public reproduction command below uses these unchanged sources and records new execution evidence.

With coordinated ownership, the reviewer added three optimizer lemmas and the general reference identity to the scratch owner source; root independently reviewed all four additions. No public proof, root import, central audit, checker, or status register was changed. It does not certify interpretations of unrelated original claims.

## Public reproduction

The [owner source](../sources/OriginalClaimInterpretation.lean) and [independent literal contracts](../sources/PeerContracts.lean) are exact byte copies of the reviewed Lean files. The latter starts with the exact former source and intentionally repeats its 17 declarations before adding nine independent expected propositions. Repeated output occurrences are counted separately from new declarations.

Run `python3 scripts/verify_report_claim_review_20.py --run` from the Lean project for an incremental pinned build and all delivered fresh Lean audits. Existing delivered logs are preserved; another invocation automatically uses a unique UTC run directory. Without `--run`, the command validates the delivered default fresh evidence. Completed review-authoring logs are retained as [owner](../reviewed_logs/ORIGINAL.log) and [peer](../reviewed_logs/ORIGINAL_PEER.log), not relabeled as public executions.
