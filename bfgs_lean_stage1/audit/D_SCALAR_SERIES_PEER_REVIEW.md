# Independent review: Module D positive scalar series

Reviewed against `report/chapters/D.tex`, lines 246–357. No mathematical or theorem-statement defect was found in the seven-file, 80-declaration scope listed in `d_scalar_series_declarations.json`. I read all seven source files, the relevant ramp prerequisite statements, the literal report formulas, and the scoped audit. I independently checked all 80 transitive-axiom reports and all seven recorded source hashes.

The scale is literally `(1/16)^n`, starting at n=0. Positive-interval coverage is proved, with closed interval endpoints included in the source-identification theorems. The infinite ramp sum is an actual definition; summability of its values, first derivatives, and second derivatives is proved from geometric majorants. Differentiation under the sum uses these bounds, and continuity of the actual curvature sum establishes C² even at the accumulation point zero. No series convergence, derivative identity, or supplied interpolation datum is assumed.

Earlier terms vanish and the entire later tail is evaluated by exact geometric series. The resulting formula agrees with the displayed scalar on every closed geometric interval and with `1+x-b` for every x≥b. All node values and actual derivative sums have the printed cubic, square, and zero values. Disjoint ramp support gives the sharp `102/b` positive-side curvature bound; the proof does not replace it by a summed overlap bound.

The affine-plateau theorem covers the complete closed condition `|h|≤a_n/2` for every n≥0. The proof classifies every summand at the perturbed node using both independently derived strict plateau-length inequalities. The n=0 case is included by the same finite-prefix/tail argument. The uniformly proved interval `2≤b≤34` includes both report parameter values once the algebraic-root bound is used; this generalization does not hide a source assumption.

The two BFGS scaling lemmas concern the actual full update and actual step definition. Simultaneous nonzero secant scaling is valid even when the total inverse expression sees zero curvature; the source application with positive curvature is covered. Neither lemma supplies an assumed orbit or matrix limit.

Scope limits: negative extension and its joins, the complete scalar assembly, global second-derivative Lipschitz continuity, the two-dimensional objective, and the deterministic orbit are separate declarations or remaining integration work. This review does not promote the positive-part scope into a complete verification of those claims. No original research source was changed.

Frozen source hashes:

- `BfgsVerification/BFGSGradientScaling.lean`: `ecfb55cf045e46ca35ec0e4e504637bf4007d1a3700a1844b059d50418246e95`
- `BfgsVerification/DScalarGeometric.lean`: `60bb85caff85865b1cf9e646d07926b347ebbc98b0234443159576133d83c918`
- `BfgsVerification/DScalarSeries.lean`: `fef96ef81ef57c17339e0551ab5bf7baee8f7e81f16a2385a952530a87d8ce6e`
- `BfgsVerification/DScalarIntervals.lean`: `e9e192a2213c36df2bd044593a6aa9fa4177aa8c4056e99c4415cdb6f2391456`
- `BfgsVerification/DScalarCurvature.lean`: `1248ccef20aa3da4de92c2e86836e52fb1dcb75e3c2f9fd46a06418478a24d00`
- `BfgsVerification/DScalarJets.lean`: `4c61730b5d3a67869dd8fb479b047dc6a0ed925b9fad218ca4189e1f2b02d356`
- `BfgsVerification/DScalarPlateaus.lean`: `8644271a3338f2ce92655051b8f4e4a126adeb7aaef803206653123d4c23a572`
