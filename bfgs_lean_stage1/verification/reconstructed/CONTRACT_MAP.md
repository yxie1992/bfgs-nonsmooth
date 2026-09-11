# Exact contract map

Each driver fixes complete literal proposition bodies independently of library target aliases. All jobs use the kernel-checked theorem-counterpart method.

## D-root

Source Module E lines [53, 56]. Driver: `jobs/Job01.lean`.

* Isolated algebraic seed existence/uniqueness in the specified box
* Every accepted and rejected trial
* SPD matrices
* Actual embedding constants

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.algebraicSeedRoot` | `EJob01.Contract01` |
| `BfgsVerification.algebraicSeedBounds` | `EJob01.Contract02` |
| `BfgsVerification.allSeedTrials` | `EJob01.Contract03` |
| `BfgsVerification.DEmbedding.objectiveGeometry` | `EJob01.Contract04` |
| `BfgsVerification.DBoxDenominators.sourceBoxDenominators` | `EJob01.Contract05` |
| `BfgsVerification.DEuclideanLocality.euclideanLocality` | `EJob01.Contract06` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## D-symbolic

Source Module E lines [57, 60]. Driver: `jobs/Job02.lean`.

* Independent inverse/Hessian update closure
* Actual secant identities

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.PlanarUpdate.inverse_formula` | `EJob02.Contract01` |
| `BfgsVerification.hessianUpdate` | `EJob02.Contract02` |
| `BfgsVerification.SeedCycle.source_cycle` | `EJob02.Contract03` |
| `BfgsVerification.inverseBFGS_det` | `EJob02.Contract04` |
| `BfgsVerification.inverseBFGS_posDef` | `EJob02.Contract05` |
| `BfgsVerification.EReconstruction.inverse_update_secant` | `EJob02.Contract06` |
| `BfgsVerification.EReconstruction.hessian_update_secant` | `EJob02.Contract07` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## D-full-oracle

Source Module E lines [61, 64]. Driver: `jobs/Job03.lean`.

* Actual full objective oracle, not a local branch assumption
* Actual deterministic accepted and rejected trials
* Shrinking identity-initialized starts

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.deterministicSeedFailure` | `EJob03.Contract01` |
| `BfgsVerification.allSeedTrials` | `EJob03.Contract02` |
| `BfgsVerification.DEmbedding.embeddingFailure` | `EJob03.Contract03` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## L-hyperbolicity

Source Module E lines [65, 68]. Driver: `jobs/Job04.lean`.

* Actual normalized Jacobian
* Exact characteristic-polynomial signs
* Stable/unstable eigenvalue separation
* Embedding bounds; actual analytic orbit mechanism remains separately checked

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.LReturnSpectrum.actual_spectral_contract` | `EJob04.Contract01` |
| `BfgsVerification.LGlobalTargets.spectrum` | `EJob04.Contract02` |
| `BfgsVerification.LReturnStableGraph.lStableManifold` | `EJob04.Contract03` |
| `BfgsVerification.LEmbedding.hessian` | `EJob04.Contract04` |
| `BfgsVerification.LShapePrecision.actualJacobianPrecision` | `EJob04.Contract05` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## L-embedding

Source Module E lines [69, 72]. Driver: `jobs/Job05.lean`.

* Actual scalar ramps and plateaus at all nodes
* Full local objective value and actual derivative identities

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.lScalarRamp` | `EJob05.Contract01` |
| `BfgsVerification.lScalarNodes` | `EJob05.Contract02` |
| `BfgsVerification.lScalarStepNodes` | `EJob05.Contract03` |
| `BfgsVerification.LEmbedding.localModel` | `EJob05.Contract04` |
| `BfgsVerification.LActualCopies.smoothFailure` | `EJob05.Contract05` |
| `BfgsVerification.LActualCopies.stepFailure` | `EJob05.Contract06` |
| `BfgsVerification.lScalarRegularity` | `EJob05.Contract07` |
| `BfgsVerification.lScalarPeaks` | `EJob05.Contract08` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## A-minors

Source Module E lines [73, 76]. Driver: `jobs/Job06.lean`.

* Actual update matrices
* Actual compressed determinants
* Arbitrary-dimensional principal-minor inequalities; A is a legacy job label

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.principalMinorHierarchy` | `EJob06.Contract01` |
| `BfgsVerification.CompressionAlgebra.gram_numerator_identity` | `EJob06.Contract02` |
| `BfgsVerification.principalGramSumIdentity` | `EJob06.Contract03` |
| `BfgsVerification.BFGSCompression.inverseBFGS_compression` | `EJob06.Contract04` |
| `BfgsVerification.CompressionDeterminant.compression_add_rank_one_det` | `EJob06.Contract05` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## H-lifting

Source Module E lines [77, 80]. Driver: `jobs/Job07.lean`.

* Projected actual full-BFGS update
* Actual invariant image/subspace and lift

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.AffineProjection.projected_update` | `EJob07.Contract01` |
| `BfgsVerification.AffineProjection.actualImageRange` | `EJob07.Contract02` |
| `BfgsVerification.linearImageLifting` | `EJob07.Contract03` |
| `BfgsVerification.AffineProjection.inverseBFGS_compress` | `EJob07.Contract04` |
| `BfgsVerification.AffineProjection.matrix_lift_invariant` | `EJob07.Contract05` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## M-mixed

Source Module E lines [81, 84]. Driver: `jobs/Job08.lean`.

* Actual accepted-step identities and principal hierarchy
* Weighted potential
* Compression identities
* Literal matrix-limit example

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.principalMinorHierarchy` | `EJob08.Contract01` |
| `BfgsVerification.sharpPrincipalPotential` | `EJob08.Contract02` |
| `BfgsVerification.CompressionAlgebra.gram_numerator_identity` | `EJob08.Contract03` |
| `BfgsVerification.UnexcitedMetric.literal_matrix_limit` | `EJob08.Contract04` |
| `BfgsVerification.fullBFGS_normalizedHierarchy` | `EJob08.Contract05` |
| `BfgsVerification.BFGSCompression.inverseBFGS_compression` | `EJob08.Contract06` |
| `BfgsVerification.reciprocalGrowth` | `EJob08.Contract07` |
| `BfgsVerification.superquadraticReciprocalGrowth` | `EJob08.Contract08` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## P-polyhedral

Source Module E lines [85, 88]. Driver: `jobs/Job09.lean`.

* Finite polyhedral/PLQ actual-objective convergence
* C1,1 smooth part without C2 premise
* Actual lifting; P is a legacy label

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.polyhedralBasin` | `EJob09.Contract01` |
| `BfgsVerification.smoothPLQBasin` | `EJob09.Contract02` |
| `BfgsVerification.linearImageLifting` | `EJob09.Contract03` |
| `BfgsVerification.lStepEmbeddingPolyhedral` | `EJob09.Contract04` |
| `BfgsVerification.lScalarRegularity` | `EJob09.Contract05` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

The positive P-family coverage comes from `polyhedralBasin` and `smoothPLQBasin`; the latter preserves local C¹,¹ rather than requiring C². The supplemental `lStepEmbeddingPolyhedral` check describes boundary geometry of the negative L example (countable maximum and local polyhedral germs away from zero), and does not place that objective in the positive P family. `lScalarRegularity` separately checks a C¹,¹/non-C² regularity distinction.

## R-secant

Source Module E lines [89, 92]. Driver: `jobs/Job10.lean`.

* Finite-max radial agreement hypotheses and bounds
* Finite sums and compositions
* Actual gauges and real powers including1<p<2
* Actual accepted-run consequences

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.finiteMaxRadialBasin` | `EJob10.Contract01` |
| `BfgsVerification.RadialPower.mixed_linear_powers_radial` | `EJob10.Contract02` |
| `BfgsVerification.RadialPower.mixed_powers_radial` | `EJob10.Contract03` |
| `BfgsVerification.AdmissibleBFGSRun.mixed_powers_convergence` | `EJob10.Contract04` |
| `BfgsVerification.RadialPower.sumObjective_inward` | `EJob10.Contract05` |
| `BfgsVerification.RadialPower.composed_gauge_homogeneous` | `EJob10.Contract06` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## R-interpretation

Source Module E lines [93, 96]. Driver: `jobs/Job11.lean`.

* Endpoint and inward Taylor equivalence
* Supporting-plane interpretation
* Boundary and strictness examples
* Reconstructed explicit R182–187 objective and actual infinite orbit

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.radialInwardEquivalence` | `EJob11.Contract01` |
| `BfgsVerification.radialInterceptEquivalence` | `EJob11.Contract02` |
| `BfgsVerification.parabolicRadialBoundary` | `EJob11.Contract03` |
| `BfgsVerification.InterceptExamples.quadratic_absolute_intercept` | `EJob11.Contract04` |
| `BfgsVerification.reconstructedFourPieceFailure` | `EJob11.Contract05` |
| `BfgsVerification.reconstructedSupportingPlane` | `EJob11.Contract06` |

Authored evidence change: Add the new exact reconstructed R objective/actual-orbit contract when independently reviewed.

## G-obstruction

Source Module E lines [97, 100]. Driver: `jobs/Job12.lean`.

* Common-target incoming-jump obstruction
* Actual SPD realization of an eligible pair
* Actual accumulating-kink example
* Exact pointwise rank-one/PSD feasibility

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.TransportedCertificate.incoming_jump_no_band_certificate` | `EJob12.Contract01` |
| `BfgsVerification.eligiblePairRealizability` | `EJob12.Contract02` |
| `BfgsVerification.AccumulatingKinks.every_neighborhood_no_certificates` | `EJob12.Contract03` |
| `BfgsVerification.PointwiseFeasibility.visibility_secant_iff_source_capacity` | `EJob12.Contract04` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## V-ridges

Source Module E lines [101, 104]. Driver: `jobs/Job13.lean`.

* Actual ridge objective and asymmetric slopes
* Allowed degeneracies and strict contours
* Matrix-frame identities
* Convergence supersession by planar theorem; V is legacy auxiliary label

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.RidgeSupersession.ridgeSupersession` | `EJob13.Contract01` |
| `BfgsVerification.RidgeSupersession.fullBFGS_convergence` | `EJob13.Contract02` |
| `BfgsVerification.AdmissibleBFGSRun.moving_frame_energy` | `EJob13.Contract03` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## T-certificate

Source Module E lines [105, 108]. Driver: `jobs/Job14.lean`.

* Projected PSD moving energy
* Actual accepted-step transported-certificate convergence
* Strictness/nonnecessity examples
* Logarithmic/value rescaling by exact real identities, not Decimal evidence

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.transportedCertificateConvergence` | `EJob14.Contract01` |
| `BfgsVerification.certificateNormalization` | `EJob14.Contract02` |
| `BfgsVerification.AdmissibleBFGSRun.normalized_frame_trace_recurrence` | `EJob14.Contract03` |
| `BfgsVerification.scalarGlobalCertificateNonnecessity` | `EJob14.Contract04` |
| `BfgsVerification.TransportedCertificate.projected_transport_trace` | `EJob14.Contract05` |
| `BfgsVerification.TransportedCertificate.projected_energy` | `EJob14.Contract06` |
| `BfgsVerification.TransportedCertificate.value_weight_transport` | `EJob14.Contract07` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## C-planar

Source Module E lines [109, 112]. Driver: `jobs/Job15.lean`.

* Angular/determinant identities
* Actual moving-energy recurrence
* Explicit quadratic barycentric coefficients and basin
* Three-dimensional field obstruction

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.PlanarAllPairs.sourceAllEndpointEstimates` | `EJob15.Contract01` |
| `BfgsVerification.planarQuadraticCoefficients` | `EJob15.Contract02` |
| `BfgsVerification.planarQuadraticBasin` | `EJob15.Contract03` |
| `BfgsVerification.spatialQuadraticRadial` | `EJob15.Contract04` |
| `BfgsVerification.spatialCanonicalWarning` | `EJob15.Contract05` |
| `BfgsVerification.PlanarTransport.angularFrame_hasDerivAt` | `EJob15.Contract06` |
| `BfgsVerification.PlanarTransport.triangular_determinant` | `EJob15.Contract07` |
| `BfgsVerification.AdmissibleBFGSRun.moving_frame_energy` | `EJob15.Contract08` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## U-multidimensional

Source Module E lines [113, 116]. Driver: `jobs/Job16.lean`.

* Actual residual-energy and cutoff transport
* Principal hierarchy and finite horizon
* Exact spike nodes and actual infinite-series oracle
* Fixed-normal qualifications and actual convergence

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.fixedNormalHyperplane` | `EJob16.Contract01` |
| `BfgsVerification.AdmissibleBFGSRun.residual_frames_on_tail_incompatible_source` | `EJob16.Contract02` |
| `BfgsVerification.finiteHorizon` | `EJob16.Contract03` |
| `BfgsVerification.NormalSpike.sourceSpikeProperties` | `EJob16.Contract04` |
| `BfgsVerification.NormalSpike.spikeObjectiveConvergence` | `EJob16.Contract05` |
| `BfgsVerification.FixedNormal.cutoffFrame_transport` | `EJob16.Contract06` |
| `BfgsVerification.NormalSpike.rationalSpikeOracle` | `EJob16.Contract07` |
| `BfgsVerification.NormalSpike.sourcePrimitive_second_derivative_peak` | `EJob16.Contract08` |
| `BfgsVerification.principalMinorHierarchy` | `EJob16.Contract09` |

Authored evidence change: Keep all listed mathematical roles; measure and report actual new job outcome/time and declaration counts.

## C-planar-numerical

Source Module E lines [117, 120]. Driver: `jobs/Job17.lean`.

* Actual full-BFGS convergence for the stated explicit planar class
* Numerical run/count/threshold observations require new actual execution if retained as empirical claims

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.planarQuadraticBasin` | `EJob17.Contract01` |
| `BfgsVerification.planarConvergence` | `EJob17.Contract02` |
| `BfgsVerification.EReconstruction.planar_eventual_printed_tolerance` | `EJob17.Contract03` |

Authored evidence change: Explicitly replace purported numerical run observations by universal convergence counterparts; do not assert measured runs/iterations/trials/precision/threshold observations.

## U-multidimensional-numerical

Source Module E lines [121, 124]. Driver: `jobs/Job18.lean`.

* Actual arbitrary-dimensional fixed-normal/spike objective and full-series oracle
* Numerical run/count/threshold observations require new actual execution if retained as empirical claims

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.fixedNormalHyperplane` | `EJob18.Contract01` |
| `BfgsVerification.NormalSpike.spikeObjectiveConvergence` | `EJob18.Contract02` |
| `BfgsVerification.NormalSpike.sourceSpikeProperties` | `EJob18.Contract03` |
| `BfgsVerification.NormalSpike.rationalSpikeOracle` | `EJob18.Contract04` |
| `BfgsVerification.EReconstruction.spike_eventual_printed_tolerance` | `EJob18.Contract05` |

Authored evidence change: Explicitly replace purported numerical run observations by universal convergence counterparts; do not assert measured runs/iterations/trials/precision/threshold observations.

## G-oscillatory-numerical

Source Module E lines [125, 128]. Driver: `jobs/Job19.lean`.

* Auxiliary incoming-pair geometry, not an actual bad BFGS trajectory
* Original oscillatory objective is undefined in the report; replace explicitly with its defined accumulating-kink family

| Actual theorem | Frozen literal contract |
|---|---|
| `BfgsVerification.AccumulatingKinks.crossing_eligible` | `EJob19.Contract01` |
| `BfgsVerification.AccumulatingKinks.crossing_curvature` | `EJob19.Contract02` |
| `BfgsVerification.AccumulatingKinks.crossing_quotient_tendsto` | `EJob19.Contract03` |
| `BfgsVerification.AccumulatingKinks.every_neighborhood_no_certificates` | `EJob19.Contract04` |

Authored evidence change: Explicit author-approved substitution of the undefined archived oscillatory objective by the defined accumulating-kink h.

