# Companion preservation and organization review

Reviewed independently against the sealed corrected chapter excerpts and their complete export lists. This is a source/contract-preservation review; it does not assert that the new companion has compiled or that every inherited proof was re-proved during this editorial turn.

The preservation check passed for all **172 source spans, 14 chapters and 3,087 distinct formal exports**. Every source marker occurs exactly once, the recorded marker line numbers and source hashes agree, the source and companion statement-label sets agree, and each ledger export list exactly equals its source span's complete list. Removing source markers and applying the generator's declared transformations gives the same mathematical body for every span. No source result was deleted or represented only by a sample declaration.

The checked transformations are: move attribution paragraphs to chapter-end notes; replace internal bibliography keys by chapter references; replace module-number prefixes in printed cross-references/tags; remove redundant manually printed section prefixes; and replace the unavailable historical program-execution sentence in the deterministic certificate with the disclosed formal-certificate/article-calculation explanation. Whitespace is ignored in this comparison. The last transformation is substantive evidence wording and is reviewed separately below; it is not treated as an automatic proof of the rational inequalities.

## Stronger and incomparable results

| Family | Retained location and scope checked |
|---|---|
| Reciprocal budgets | Chapter 2, source M.span.3: weaker bounded-gradient/vanishing-decrease geometric and arithmetic means, explicit finite-horizon inequality, and superquadratic reciprocal sum under summability all remain distinct. The fixed-tail-before-horizon limit is retained. |
| Transported and radial conditions | Chapters 3–5: potentially singular/unbounded PSD field, all eligible-pair quantifiers, exact nonexpansion normalization, radial/inward equivalence and certificate nonnecessity remain. No certificate obstruction is relabeled BFGS failure. |
| Concrete objectives and lifting | Chapter 6, especially F:lifting: centered and transformed-gauge conditions, initialization-dependent affine-fiber selection, conservative finite-horizon/asymptotic bounds and accepted-point existence limitations survive. |
| Noncompact homogeneity | Chapter 7: unconditional value dichotomy, many-piece affine-hull escape obstruction, planar/effective-rank iterate conclusions and the separate arbitrary-dimensional noncompact theorem remain; compact certificate convergence has not replaced them. |
| Planar geometry | Chapter 9, C:thm:cluster and C:cor:max: dimension, contour and nondegeneracy restrictions remain. Affine-critical cluster forcing is kept separate from convergence under no false affine criticality. The signed determinant and one-sided transport proof remain. |
| Flat parabolic contours | Chapter 10: arbitrary finite branch count and zero linear coefficients remain. Flat-contour coverage has not been removed as supposedly implied by the strict-contour planar theorem. |
| Fixed normal geometry | Chapter 11, U:one/U:parallel and its tangential-curvature subsection: arbitrary dimension, one versus parallel exceptional interfaces and weaker tangential curvature remain distinct. No rotating-normal generalization is inferred. |
| Deterministic upper-regularity failure | Chapter 12: fixed implementation, exact seed, all-query comparisons/containment and the one-objective local embedding remain. The local globally C^{2,1} convex-branch statement does not acquire a lower curvature assumption. |
| Positive lower-curvature failure | Chapter 13, L:thm:global and L:thm:local: global quadratic-branch failure, local finite C^{1,1} strongly convex branches and the countable constant-classical-Hessian variant remain separate. The text explicitly excludes a proved local finite C^2 uniformly strongly convex counterexample. |
| Open/evidence boundaries | Chapters 1 and 14 retain explicit open questions, finite detection versus infinite-run distinctions, historical audit scope and no publication-priority guarantee. |

## Findings sent to the assembling agent

1. **Numbering correction required:** the source macro overrides in `companion/chapters/04_R.tex` and `05_G.tex` still use `R.\arabic{section}.\arabic{theorem}` and `G.\arabic{section}.\arabic{theorem}`. The generic replacement misses a letter followed by a backslash, so these disagree with numeric chapters 4 and 5 and their converted equation tags. Replace these macro prefixes explicitly and log a typographic transformation.
2. **Self-contained certificate proof required:** the edited deterministic-root paragraph now directs the reader to the article appendix for its explicit polynomial/coefficient calculation. Include the corresponding calculation in the companion (with valid internal references), or another complete companion derivation. The ledger identifies correct formal evidence but is not a replacement for a human-readable proof in a purported complete companion.
3. **Directional attribution prose required:** moving notes to the end leaves “the theorem below,” “assertions below,” and similar descriptions incorrect. Examples occur in chapters 2, 5, 6 and 9. Rewrite them neutrally or use exact references; this is bibliographic prose, not an opportunity to alter theorem contracts.
4. **Organization polish recommended:** source phrases such as “This module,” “sources Chapters,” “the user's literal ... assumption,” and plural “Modules A and H” survive. Replace them with monograph language, retaining theorem/evidence boundaries. Fix physical numbering only with actual LaTeX cross-references; external-paper theorem numbers must remain untouched.

The chapter order is logically sound: common algebra, sufficient mechanisms, verifiable geometries, noncompact alternatives, independent geometric extensions, then deterministic negative results. Keeping all source mathematics is the right conservative starting point. Redundant inventory material should function as a navigation map, not another competing mathematical narrative.

## Snapshot and scope

No original corrected source, Lean proof, Git state or companion source was edited by this reviewer. The review inspected the generator rather than executing its writes. An independent read-only Python comparison checked all source excerpts against actual generated marker bodies, exact export lists, source hashes, labels and line positions. It returned no preservation mismatches. Later generator/assembly changes require a refreshed check; the findings above are open at this snapshot.

Snapshot UTC: 2026-09-12T08:56:47.923466+00:00

```json
{
  "editorial/generate_companion.py": "21c9cfd07bfa1b84644e777f8bacad3511db4b09191087322d2dbefe2a2648ca",
  "companion/SOURCE_CORRESPONDENCE.json": "5ac4d3329ab1b41d751373a0cea7d9121df714fe2287c7c0f60132fc5f586d68",
  "editorial/SUPERSESSION_LEDGER.json": "a307de4c5d8bc68a49d7fb82a0e72cfaa5253711451cd32b6fab6f85e6b842a4",
  "companion/chapters/01_I.tex": "fa92ea9b6625477007b5c79a5d2a8a6326eabedc85531ca5eb64ff0bb0a8c52b",
  "companion/chapters/02_M.tex": "801f4ef1d7973855389140bd4992b877fcb4333f23aa8a3043c143e6c1fb3c38",
  "companion/chapters/03_T.tex": "ddafa0125c6176ddf4d9780ae5098c1a010a597bab25385b46120d896f323d3b",
  "companion/chapters/04_R.tex": "ec0e8342f42d58c4a0c489c541a647f58ad6b14395e79620272d66f7d4d18bfb",
  "companion/chapters/05_G.tex": "6ed22642dcacff5b5e82701d0c8530501d557d1713df5cfc3fdbf3703a25fd07",
  "companion/chapters/06_F.tex": "93b02dd6f8a4da939f51f3272aa6e88b473be375a0419107b8324f1ad96799b0",
  "companion/chapters/07_H.tex": "809a5847fea7fdca565ae2ac3a452a449f0f7c81fb8773e1bed0fdedaee792f6",
  "companion/chapters/08_A.tex": "62728e02dff8d30ae125b1e40d0d526e47eb43b15c9edd79f0f600b096fcc69e",
  "companion/chapters/09_C.tex": "7b8b0af338184450a72ebc17a5f7f9d9c05f33954fe5fdca7bdd57ab2a91a4fc",
  "companion/chapters/10_Q.tex": "1069f33b0e4638d6dc47534ee3c87f9dd95f6b6c72e21be567fe365152b41446",
  "companion/chapters/11_U.tex": "a95de37e027db55b72d0bf79ae1147e13d744e2f03c24b601ce6e9c435169420",
  "companion/chapters/12_D.tex": "1d906724fc159186910c9d1997367da89c02e99e68faea0121ebbf143e526f1e",
  "companion/chapters/13_L.tex": "6a8be71332253b620945f06337427ffa001ab43aa1a435b3d532fd4924be88ea",
  "companion/chapters/14_E.tex": "379ae9c9e18961ab582a0595e6563a98ec84404860d9302eebe3ffc82e3eaa4e"
}
```

## Resolution and reproducibility follow-up

The three required findings above are now resolved. The generator explicitly converts the R/G theorem-macro prefixes, moves notes before all chapter-reference transformations, replaces their stale directional wording, and inserts the stable `comp:trial_table` label before recording correspondence. The inventory now describes ordinary chapter numbering. Original sealed sources remain untouched.

At the assembling author's request this reviewer modified the generator and regenerated its outputs. It now SHA256-guards the frozen claim index, declaration index and every source chapter before any write. `python3 editorial/generate_companion.py --check` regenerates all 17 managed outputs in memory and writes nothing; it checks missing/changed outputs and unexpected chapter files. The first check correctly reported the intentionally stale R/G files and ledger before regeneration; the final check passes for 14 chapters, 172 spans and 3,087 unique exports. These later authorized edits supersede the earlier read-only scope statement for the generator and generated companion only.

The complete finite certificate now appears in `companion/appendices/seed_certificate.tex`, generated from the canonical article appendix. An independent reproduction of the documented heading/reference transformations matches its entire byte content, and every appendix reference resolves within the companion. It no longer relies on the article for an essential proof. The source-span register and HTML correspondence view were included in this follow-up inspection; the HTML correctly distinguishes exact types/export lists from natural-language correspondence. Root-prose supplemental records are linked by the integrated ledger.

The remaining conversational source vocabulary noted above is a style recommendation, not a missing theorem or proof. No stronger/incomparable result was removed during these fixes. Integrated PDF build and visual checks remain the assembling author's release gates.

Follow-up UTC: 2026-09-12T09:14:16.800806+00:00

```json
{
  "editorial/generate_companion.py": "1f9eb9df5e0f96129816a24bb87e21903b5841648d32b000d93aebfe1a09817c",
  "editorial/prepare_shared_appendix.py": "271999bb8052f1486e975219d6a95e816a8ddb8ddadc2cfc017aa91c51898acb",
  "companion/SOURCE_CORRESPONDENCE.json": "20b2218d7d30bdea209ce779c963ee0f1dc61bfead5728ec920ccf19719bb4a9",
  "companion/PROOF_CORRESPONDENCE.html": "45ad9247c96c6de776ad8c08489cd363ed67119e95028b4ddf0799ff2d75a7f2",
  "companion/appendices/seed_certificate.tex": "b0345bf263ece7a3ea19ed4da8e35a2dee5bfa323ab552bde661fea3ee046b53"
}
```
