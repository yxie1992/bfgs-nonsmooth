# Module L stable-manifold source map

This map concerns `BFGS_MASTER_REPORT_LaTeX/report/chapters/L.tex` lines 197–214. It records the newly delivered source closure; the central whole-project release audit remains the root integration step.

| Source assertion | Actual checked declaration / construction |
| --- | --- |
| Two stable directions of the actual five-dimensional derivative | `LReturnStableGraph.source_splitting` derives the actual coordinate equivalence and both contraction bounds from the actual block derivative and checked shape roots. `AnalyticStableGraph.stable_inclusion_range` identifies its stable inclusion with the actual derivative-power stable set. |
| Smooth local stable manifold through the actual seed | `LReturnStableGraph.lStableInvariantManifold : LStableInvariantManifoldTarget` constructs the actual graph `seed + E(a,h(a))`, smooth on one open two-dimensional parameter neighborhood. |
| Embedded dimension two | `chart_isEmbedding` proves the actual parameter restriction is a topological embedding with the explicit stable-projection inverse. `stable_inclusion_dimension` and the final target prove the actual derivative range has dimension two. |
| Tangency to the actual stable space | The final target contains `HasFDerivAt` for the actual chart and equality of its derivative range with `{v | (D returnMap(seed))^n v → 0}`. The unstable derivative vanishes by a derived bounded backward recurrence. |
| Local stable invariance | The same final target supplies open V0 containing zero, V0⊆V, and actual return-map images of graph points over V0 lie on the same graph over V. This follows from derived uniqueness of small actual convergent orbits. |
| Actual stable forward trajectories | Every point of the constructed graph has an actual forward return-map orbit that stays in any prescribed seed neighborhood and converges to seed. The implicit-function sequence is identified with the actual C0 contraction solution. |
| Transversality to zero physical scale and arbitrarily small positive scales | `source_splitting` gives `E z 4 = z.1 1`; `source_smooth_stable_graph` proves the chart scale is the second parameter. The final target includes a graph point with physical scale in `(0,eps)` for every eps>0. |
| Actual smooth local diffeomorphism | The previously delivered `LReturnLocalInverse.actual_local_inverse` independently proves this property. The new constructive stable graph does not assume a local inverse or an abstract stable-manifold theorem. |

The final source contract has no assumed analytic sequence lift, orbit selection, hierarchy, normal sequence, convergence, tangent space, local invariance or BFGS modification. The literal return map's analyticity is derived by the existing source formulas. Generic helper hypotheses stay conditional exactly where stated; the final source theorem discharges them. No mathematical correction to the original source was needed for this tranche.

Delivered scope: twenty main Lean files, ninety explicitly audited declarations (including the sequence abbreviation), and two exact source contracts. Reproduce with `bash audit/verify_l_stable_manifold.sh`. The final import is `BfgsVerification.LStableInvariantManifold`; exact target names are `BfgsVerification.LReturnStableGraph.lStableManifold` and `BfgsVerification.LReturnStableGraph.lStableInvariantManifold`.
