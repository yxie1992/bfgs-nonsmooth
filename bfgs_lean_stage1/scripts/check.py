#!/usr/bin/env python3
"""Fail-closed build/audit driver for the BFGS Lean project.

A static source scan is not a Lean verification. Missing executables, build
errors, missing axiom output, or unexpected axioms prevent a verified status.
A successful helper build alone is insufficient: exact target inhabitants and
compiled-environment axiom reports establish the matrix-run and objective-level status.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "audit"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_LEAN = "4.19.0"
EXPECTED_MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
TARGETS = {
    "end_to_end_principal_minor_hierarchy_verified":
        ("BfgsVerification.principalMinorHierarchy", "BfgsVerification.PrincipalMinorHierarchyTarget"),
    "end_to_end_bfgs_reciprocal_growth_verified":
        ("BfgsVerification.reciprocalGrowth", "BfgsVerification.ReciprocalGrowthTarget"),
    "superquadratic_growth_verified":
        ("BfgsVerification.superquadraticReciprocalGrowth", "BfgsVerification.SuperquadraticReciprocalTarget"),
}
OBJECTIVE_TARGETS = {
    "objective_reciprocal_growth_verified":
        ("BfgsVerification.objectiveReciprocalGrowth", "BfgsVerification.ObjectiveReciprocalGrowthTarget"),
    "objective_lower_bound_growth_verified":
        ("BfgsVerification.objectiveLowerBoundGrowth", "BfgsVerification.ObjectiveLowerBoundGrowthTarget"),
    "compact_objective_growth_verified":
        ("BfgsVerification.compactObjectiveGrowth", "BfgsVerification.CompactObjectiveGrowthTarget"),
    "compact_objective_finite_horizon_verified":
        ("BfgsVerification.compactObjectiveFiniteHorizon", "BfgsVerification.CompactObjectiveFiniteHorizonTarget"),
}
FOUNDATION_TARGETS = {
    "hessian_invariants_and_exact_determinant_verified":
        ("BfgsVerification.hessianInvariants", "BfgsVerification.HessianInvariantTarget"),
    "localization_verified":
        ("BfgsVerification.localization", "BfgsVerification.LocalizationTarget"),
    "strict_contour_steps_verified":
        ("BfgsVerification.strictContourSteps", "BfgsVerification.StrictContourTarget"),
    "reference_energy_verified":
        ("BfgsVerification.referenceEnergy", "BfgsVerification.ReferenceEnergyTarget"),
    "quadratic_correction_criterion_verified":
        ("BfgsVerification.quadraticCorrectionConvergence", "BfgsVerification.QuadraticCorrectionTarget"),
    "moving_frame_criterion_verified":
        ("BfgsVerification.movingFrameCriterion", "BfgsVerification.MovingFrameCriterionTarget"),
    "residual_frame_criterion_verified":
        ("BfgsVerification.residualFrameCriterion", "BfgsVerification.ResidualFrameCriterionTarget"),
}
REPORT_CORE_TARGETS = {
    "transported_certificate_primary_theorem_verified":
        ("BfgsVerification.transportedCertificateConvergence", "BfgsVerification.TransportedCertificateTarget"),
    "homogeneous_value_dichotomy_verified":
        ("BfgsVerification.homogeneousDichotomy", "BfgsVerification.HomogeneousDichotomyTarget"),
    "scalar_arbitrary_metric_convergence_verified":
        ("BfgsVerification.scalarMetricConvergence", "BfgsVerification.ScalarMetricConvergenceTarget"),
    "scalar_actual_bfgs_convergence_verified":
        ("BfgsVerification.scalarBFGSConvergence", "BfgsVerification.ScalarBFGSConvergenceTarget"),
    "radial_certificate_convergence_verified":
        ("BfgsVerification.radialCertificateConvergence", "BfgsVerification.RadialCertificateConvergenceTarget"),
}
REPORT_GEOMETRY_TARGETS = {
    "certificate_exact_normalization_verified":
        ("BfgsVerification.certificateNormalization", "BfgsVerification.CertificateNormalizationTarget"),
    "recurrent_affine_hull_verified":
        ("BfgsVerification.recurrentAffineHull", "BfgsVerification.RecurrentAffineHullTarget"),
    "max_linear_affine_escape_verified":
        ("BfgsVerification.maxLinearAffineEscape", "BfgsVerification.MaxLinearAffineEscapeTarget"),
    "radial_intercept_equivalence_verified":
        ("BfgsVerification.radialInterceptEquivalence", "BfgsVerification.RadialInterceptEquivalenceTarget"),
    "inward_certificate_convergence_verified":
        ("BfgsVerification.inwardCertificateConvergence", "BfgsVerification.InwardCertificateConvergenceTarget"),
    "incoming_jump_obstruction_verified":
        ("BfgsVerification.incomingJumpObstruction", "BfgsVerification.IncomingJumpObstructionTarget"),
    "scalar_certificate_characterization_verified":
        ("BfgsVerification.scalarCertificateCharacterization", "BfgsVerification.ScalarCertificateCharacterizationTarget"),
}
REPORT_CONTINUATION_TARGETS = {
    "radial_inward_equivalence_verified":
        ("BfgsVerification.radialInwardEquivalence", "BfgsVerification.RadialInwardEquivalenceTarget"),
    "local_radial_central_equivalence_verified":
        ("BfgsVerification.localRadialCentralEquivalence", "BfgsVerification.LocalRadialCentralEquivalenceTarget"),
    "actual_linear_image_lifting_verified":
        ("BfgsVerification.linearImageLifting", "BfgsVerification.LinearImageLiftingTarget"),
    "nonunique_solution_basin_verified":
        ("BfgsVerification.nonuniqueSolutionBasin", "BfgsVerification.NonuniqueSolutionBasinTarget"),
    "linear_correction_rate_verified":
        ("BfgsVerification.linearCorrectionRate", "BfgsVerification.LinearCorrectionRateTarget"),
    "homogeneous_rates_verified":
        ("BfgsVerification.homogeneousRates", "BfgsVerification.HomogeneousRatesTarget"),
    "scalar_global_certificate_nonnecessity_verified":
        ("BfgsVerification.scalarGlobalCertificateNonnecessity", "BfgsVerification.ScalarGlobalCertificateNonnecessityTarget"),
    "scalar_local_certificate_nonnecessity_verified":
        ("BfgsVerification.scalarLocalCertificateNonnecessity", "BfgsVerification.ScalarLocalCertificateNonnecessityTarget"),
    "eligible_pair_realizability_verified":
        ("BfgsVerification.eligiblePairRealizability", "BfgsVerification.EligiblePairRealizabilityTarget"),
    "finite_sample_feasibility_verified":
        ("BfgsVerification.finiteSampleFeasibility", "BfgsVerification.FiniteSampleFeasibilityTarget"),
}
REPORT_APPLICATION_TARGETS = {
    'affine_certificate_covariance_verified':
        ("BfgsVerification.affineCertificateCovariance", "BfgsVerification.AffineCertificateCovarianceTarget"),
    'centered_smooth_convergence_verified':
        ("BfgsVerification.centeredSmoothConvergence", "BfgsVerification.CenteredSmoothConvergenceTarget"),
    'centered_local_basin_verified':
        ("BfgsVerification.centeredLocalBasin", "BfgsVerification.CenteredLocalBasinTarget"),
    'quadratic_gauge_rates_verified':
        ("BfgsVerification.quadraticGaugeRates", "BfgsVerification.QuadraticGaugeRatesTarget"),
    'ellipsoid_certificate_geometry_verified':
        ("BfgsVerification.ellipsoidCertificateGeometry", "BfgsVerification.EllipsoidCertificateGeometryTarget"),
    'pointwise_certificate_capacity_verified':
        ("BfgsVerification.pointwiseCertificateCapacity", "BfgsVerification.PointwiseCertificateCapacityTarget"),
    'planar_homogeneous_escape_verified':
        ("BfgsVerification.planarHomogeneousEscape", "BfgsVerification.PlanarHomogeneousEscapeTarget"),
    'parabolic_denominator_verified':
        ("BfgsVerification.parabolicDenominator", "BfgsVerification.ParabolicDenominatorTarget"),
}
REPORT_FAMILY_TARGETS = {
    "accessible_active_objective_separation_verified":
        ("BfgsVerification.accessibleActiveSeparation", "BfgsVerification.AccessibleActiveSeparationTarget"),
    "parabolic_eligible_separation_verified":
        ("BfgsVerification.parabolicEligibleSeparation", "BfgsVerification.ParabolicEligibleSeparationTarget"),
    "parabolic_radial_nonnecessity_verified":
        ("BfgsVerification.parabolicNonnecessity", "BfgsVerification.ParabolicNonnecessityTarget"),
    "parabolic_certificate_verified":
        ("BfgsVerification.parabolicCertificate", "BfgsVerification.ParabolicCertificateTarget"),
    "parabolic_convergence_verified":
        ("BfgsVerification.parabolicConvergence", "BfgsVerification.ParabolicConvergenceTarget"),
    "transformed_gauge_convergence_verified":
        ("BfgsVerification.transformedGaugeConvergence", "BfgsVerification.TransformedGaugeConvergenceTarget"),
    "relative_interior_convergence_verified":
        ("BfgsVerification.relativeInteriorConvergence", "BfgsVerification.RelativeInteriorConvergenceTarget"),
    "recurrent_relative_interior_verified":
        ("BfgsVerification.recurrentRelativeInterior", "BfgsVerification.RecurrentRelativeInteriorTarget"),
}
REPORT_STRUCTURE_TARGETS = {
    "smooth_plq_basin_verified":
        ("BfgsVerification.smoothPLQBasin", "BfgsVerification.SmoothPLQBasinTarget"),
    "maxAffineThreshold_verified":
        ("BfgsVerification.maxAffineThreshold", "BfgsVerification.MaxAffineThresholdTarget"),
    "mixedLinearPowers_verified":
        ("BfgsVerification.mixedLinearPowers", "BfgsVerification.MixedLinearPowersTarget"),
    "recurrentLowRank_verified":
        ("BfgsVerification.recurrentLowRank", "BfgsVerification.RecurrentLowRankTarget"),
    "relativeInteriorClass_verified":
        ("BfgsVerification.relativeInteriorClass", "BfgsVerification.RelativeInteriorClassTarget"),
    "parabolicPruning_verified":
        ("BfgsVerification.parabolicPruning", "BfgsVerification.ParabolicPruningTarget"),
    "parabolicPrintedField_verified":
        ("BfgsVerification.parabolicPrintedField", "BfgsVerification.ParabolicPrintedFieldTarget"),
    "polyhedralBasin_verified":
        ("BfgsVerification.polyhedralBasin", "BfgsVerification.PolyhedralBasinTarget"),
    "fivePieceObstruction_verified":
        ("BfgsVerification.fivePieceObstruction", "BfgsVerification.FivePieceObstructionTarget"),
}
REPORT_ANALYTIC_TARGETS = {
    "actualFiniteMaxSubdifferential_verified":
        ("BfgsVerification.actualFiniteMaxSubdifferential", "BfgsVerification.ActualFiniteMaxSubdifferentialTarget"),
    "localAffineCorrectness_verified":
        ("BfgsVerification.localAffineCorrectness", "BfgsVerification.LocalAffineCorrectnessTarget"),
    "finiteMaxRadialBasin_verified":
        ("BfgsVerification.finiteMaxRadialBasin", "BfgsVerification.FiniteMaxRadialBasinTarget"),
    "euclideanResidualBasin_verified":
        ("BfgsVerification.euclideanResidualBasin", "BfgsVerification.EuclideanResidualBasinTarget"),
    "finiteRayStep_verified":
        ("BfgsVerification.finiteRayStep", "BfgsVerification.FiniteRayStepTarget"),
    "unexcitedMetric_verified":
        ("BfgsVerification.unexcitedMetric", "BfgsVerification.UnexcitedMetricTarget"),
    "parabolicRadialBoundary_verified":
        ("BfgsVerification.parabolicRadialBoundary", "BfgsVerification.ParabolicRadialBoundaryTarget"),
    "algebraicSeedRoot_verified":
        ("BfgsVerification.algebraicSeedRoot", "BfgsVerification.AlgebraicSeedRootTarget"),
    "algebraicSeedBounds_verified":
        ("BfgsVerification.algebraicSeedBounds", "BfgsVerification.AlgebraicSeedBoundsTarget"),
    "affineRankLoss_verified":
        ("BfgsVerification.affineRankLoss", "BfgsVerification.AffineRankLossTarget"),
    "algebraicJacobianCertificate_verified":
        ("BfgsVerification.algebraicJacobianCertificate", "BfgsVerification.AlgebraicJacobianCertificateTarget"),
    "nuclearBoundary_verified":
        ("BfgsVerification.nuclearBoundary", "BfgsVerification.NuclearBoundaryTarget"),
    "fixedNormalHyperplane_verified":
        ("BfgsVerification.fixedNormalHyperplane", "BfgsVerification.FixedNormalHyperplaneTarget"),
    "parallelInterfacesCluster_verified":
        ("BfgsVerification.parallelInterfacesCluster", "BfgsVerification.ParallelInterfacesClusterTarget"),
    "parallelInterfacesConvergence_verified":
        ("BfgsVerification.parallelInterfacesConvergence", "BfgsVerification.ParallelInterfacesConvergenceTarget"),
    "fixedNormalLocalBasin_verified":
        ("BfgsVerification.fixedNormalLocalBasin", "BfgsVerification.FixedNormalLocalBasinTarget"),
    "parallelInterfacesLocalBasin_verified":
        ("BfgsVerification.parallelInterfacesLocalBasin", "BfgsVerification.ParallelInterfacesLocalBasinTarget"),
}
REPORT_DYNAMICS_TARGETS = {
    "tangentialCompositeConvergence_verified":
        ("BfgsVerification.tangentialCompositeConvergence", "BfgsVerification.TangentialCompositeConvergenceTarget"),
    "tangentialCompositeLocalBasin_verified":
        ("BfgsVerification.tangentialCompositeLocalBasin", "BfgsVerification.TangentialCompositeLocalBasinTarget"),
    "strongCompositeConvergence_verified":
        ("BfgsVerification.strongCompositeConvergence", "BfgsVerification.StrongCompositeConvergenceTarget"),
    "strongCompositeLocalBasin_verified":
        ("BfgsVerification.strongCompositeLocalBasin", "BfgsVerification.StrongCompositeLocalBasinTarget"),
    "exactSeedCycle_verified":
        ("BfgsVerification.exactSeedCycle", "BfgsVerification.ExactSeedCycleTarget"),
    "deterministicSeedFailure_verified":
        ("BfgsVerification.deterministicSeedFailure", "BfgsVerification.DeterministicSeedFailureTarget"),
    "allSeedTrials_verified":
        ("BfgsVerification.allSeedTrials", "BfgsVerification.AllSeedTrialsTarget"),
}
REPORT_CONSTRUCTION_TARGETS = {
    'coerciveSeedFailure_verified':
        ('BfgsVerification.coerciveSeedFailure', 'BfgsVerification.CoerciveSeedFailureTarget'),
    'dScalarFunction_verified':
        ('BfgsVerification.dScalarFunction', 'BfgsVerification.DScalarFunctionTarget'),
    'centeredSpectralConvergence_verified':
        ('BfgsVerification.centeredSpectralConvergence', 'BfgsVerification.CenteredSpectralConvergenceTarget'),
    'singularCurvatureCounterexample_verified':
        ('BfgsVerification.singularCurvatureCounterexample', 'BfgsVerification.SingularCurvatureCounterexampleTarget'),
    'sourceSpikeProperties_verified':
        ('BfgsVerification.NormalSpike.sourceSpikeProperties', 'BfgsVerification.NormalSpike.SourceSpikePropertiesTarget'),
    'spikeObjectiveConvergence_verified':
        ('BfgsVerification.NormalSpike.spikeObjectiveConvergence', 'BfgsVerification.NormalSpike.SpikeObjectiveConvergenceTarget'),
    'spikeRadialSeparation_verified':
        ('BfgsVerification.NormalSpike.spikeRadialSeparation', 'BfgsVerification.NormalSpike.SpikeRadialSeparationTarget'),
    'spikeObjectiveGeometry_verified':
        ('BfgsVerification.NormalSpike.spikeObjectiveGeometry', 'BfgsVerification.NormalSpike.SpikeObjectiveGeometryTarget'),
    'spikeHessianPeaks_verified':
        ('BfgsVerification.NormalSpike.spikeHessianPeaks', 'BfgsVerification.NormalSpike.SpikeHessianPeakTarget'),
    'rationalSpikeOracle_verified':
        ('BfgsVerification.NormalSpike.rationalSpikeOracle', 'BfgsVerification.NormalSpike.RationalSpikeOracleTarget'),
}
REPORT_EMBEDDING_TARGETS = {
    'dEmbeddingObjective_verified':
        ('BfgsVerification.DEmbedding.objectiveGeometry', 'BfgsVerification.DEmbedding.ObjectiveGeometryTarget'),
    'dEmbeddingFailure_verified':
        ('BfgsVerification.DEmbedding.embeddingFailure', 'BfgsVerification.DEmbedding.EmbeddingFailureTarget'),
    'lQuadraticSeed_verified':
        ('BfgsVerification.LQuadraticSeed.quadraticSeed', 'BfgsVerification.LQuadraticSeed.QuadraticSeedTarget'),
    'planarAffineCriticalCluster_verified':
        ('BfgsVerification.planarAffineCriticalCluster', 'BfgsVerification.PlanarAffineCriticalClusterTarget'),
    'planarConvergence_verified':
        ('BfgsVerification.planarConvergence', 'BfgsVerification.PlanarConvergenceTarget'),
    'planarLocalBasin_verified':
        ('BfgsVerification.planarLocalBasin', 'BfgsVerification.PlanarLocalBasinTarget'),
    'variableSpikeConvergence_verified':
        ('BfgsVerification.NormalSpike.variableSpikeConvergence', 'BfgsVerification.NormalSpike.VariableSpikeConvergenceTarget'),
    'variableSpikeSeparation_verified':
        ('BfgsVerification.NormalSpike.variableSpikeSeparation', 'BfgsVerification.NormalSpike.VariableSpikeSeparationTarget'),
    'variableSpikeNonsplitting_verified':
        ('BfgsVerification.NormalSpike.variableSpikeNonsplitting', 'BfgsVerification.NormalSpike.VariableSpikeNonsplittingTarget'),
    'variableSpikeGeometry_verified':
        ('BfgsVerification.NormalSpike.variableSpikeGeometry', 'BfgsVerification.NormalSpike.VariableSpikeGeometryTarget'),
    'variableSpikeHessian_verified':
        ('BfgsVerification.NormalSpike.variableSpikeHessian', 'BfgsVerification.NormalSpike.VariableSpikeHessianTarget'),
}
REPORT_STRUCTURAL_CLOSURE_TARGETS = {
    "finiteC1MaxAffineGap_verified":
        ("BfgsVerification.finiteC1MaxAffineGap", "BfgsVerification.FiniteC1MaxAffineGapTarget"),
    "planarFiniteMaxLocalBasin_verified":
        ("BfgsVerification.planarFiniteMaxLocalBasin", "BfgsVerification.PlanarFiniteMaxLocalBasinTarget"),
    "planarFiniteMaxHessianBasin_verified":
        ("BfgsVerification.planarFiniteMaxHessianBasin", "BfgsVerification.PlanarFiniteMaxHessianBasinTarget"),
    "rectangularNuclearNorm_verified":
        ("BfgsVerification.rectangularNuclearNorm", "BfgsVerification.RectangularNuclearNormTarget"),
    "centeredRectangularNuclear_verified":
        ("BfgsVerification.centeredRectangularNuclear", "BfgsVerification.CenteredRectangularNuclearTarget"),
    "mixedNuclearPowers_verified":
        ("BfgsVerification.mixedNuclearPowers", "BfgsVerification.MixedNuclearPowersTarget"),
    "firstDifferenceBasin_verified":
        ("BfgsVerification.firstDifferenceBasin", "BfgsVerification.FirstDifferenceBasinTarget"),
    "planarQuadraticModel_verified":
        ("BfgsVerification.planarQuadraticModel", "BfgsVerification.PlanarQuadraticModelTarget"),
    "planarQuadraticCoefficients_verified":
        ("BfgsVerification.planarQuadraticCoefficients", "BfgsVerification.PlanarQuadraticCoefficientsTarget"),
    "planarQuadraticBasin_verified":
        ("BfgsVerification.planarQuadraticBasin", "BfgsVerification.PlanarQuadraticBasinTarget"),
    "planarQuadraticCurve_verified":
        ("BfgsVerification.planarQuadraticCurve", "BfgsVerification.PlanarQuadraticCurveTarget"),
    "planarQuadraticSeparation_verified":
        ("BfgsVerification.planarQuadraticSeparation", "BfgsVerification.PlanarQuadraticSeparationTarget"),
    "stableOrbitCriterion_verified":
        ("BfgsVerification.LocalStableOrbit.stableOrbit", "BfgsVerification.LocalStableOrbit.StableOrbitTarget"),
    "positiveStableOrbitCriterion_verified":
        ("BfgsVerification.LocalStableOrbit.positiveStableOrbit", "BfgsVerification.LocalStableOrbit.PositiveStableOrbitTarget"),
}
REPORT_L_FAILURE_TARGETS = {
    "spatialCanonicalWarning_verified":
        ("BfgsVerification.spatialCanonicalWarning", "BfgsVerification.SpatialCanonicalWarningTarget"),
    "spatialQuadraticRadial_verified":
        ("BfgsVerification.spatialQuadraticRadial", "BfgsVerification.SpatialQuadraticRadialTarget"),
    "finiteMaxTaylor_verified":
        ("BfgsVerification.finiteMaxTaylor", "BfgsVerification.FiniteMaxTaylorTarget"),
    "finiteMaxActualHessian_verified":
        ("BfgsVerification.finiteMaxActualHessian", "BfgsVerification.FiniteMaxActualHessianTarget"),
    "lScalarRamp_verified":
        ("BfgsVerification.lScalarRamp", "BfgsVerification.LScalarRampTarget"),
    "lScalarDefinition_verified":
        ("BfgsVerification.lScalarDefinition", "BfgsVerification.LScalarDefinitionTarget"),
    "lScalarRegularity_verified":
        ("BfgsVerification.lScalarRegularity", "BfgsVerification.LScalarRegularityTarget"),
    "lScalarNodes_verified":
        ("BfgsVerification.lScalarNodes", "BfgsVerification.LScalarNodeTarget"),
    "lScalarPeaks_verified":
        ("BfgsVerification.lScalarPeaks", "BfgsVerification.LScalarPeaksTarget"),
    "lScalarStepDefinition_verified":
        ("BfgsVerification.lScalarStepDefinition", "BfgsVerification.LScalarStepDefinitionTarget"),
    "lScalarStepGeometry_verified":
        ("BfgsVerification.lScalarStepGeometry", "BfgsVerification.LScalarStepGeometryTarget"),
    "lScalarStepNodes_verified":
        ("BfgsVerification.lScalarStepNodes", "BfgsVerification.LScalarStepNodeTarget"),
    "lScalarStepLocal_verified":
        ("BfgsVerification.lScalarStepLocal", "BfgsVerification.LScalarStepLocalTarget"),
    "lStepEmbeddingGeometry_verified":
        ("BfgsVerification.lStepEmbeddingGeometry", "BfgsVerification.LStepEmbeddingGeometryTarget"),
    "lStepEmbeddingPolyhedral_verified":
        ("BfgsVerification.lStepEmbeddingPolyhedral", "BfgsVerification.LStepEmbeddingPolyhedralTarget"),
    "lStepEmbeddingCopies_verified":
        ("BfgsVerification.lStepEmbeddingCopies", "BfgsVerification.LStepEmbeddingCopiesTarget"),
    "LEmbedding_regularity_verified":
        ("BfgsVerification.LEmbedding.regularity", "BfgsVerification.LEmbedding.RegularityTarget"),
    "LEmbedding_origin_verified":
        ("BfgsVerification.LEmbedding.origin", "BfgsVerification.LEmbedding.OriginTarget"),
    "LEmbedding_hessian_verified":
        ("BfgsVerification.LEmbedding.hessian", "BfgsVerification.LEmbedding.HessianTarget"),
    "LEmbedding_localModel_verified":
        ("BfgsVerification.LEmbedding.localModel", "BfgsVerification.LEmbedding.LocalModelTarget"),
    "LActualCopies_smoothFailure_verified":
        ("BfgsVerification.LActualCopies.smoothFailure", "BfgsVerification.LActualCopies.SmoothFailureTarget"),
    "LActualCopies_stepFailure_verified":
        ("BfgsVerification.LActualCopies.stepFailure", "BfgsVerification.LActualCopies.StepFailureTarget"),
    "LGlobalTargets_globalFailure_verified":
        ("BfgsVerification.LGlobalTargets.globalFailure", "BfgsVerification.LGlobalTargets.GlobalFailureTarget"),
    "LGlobalTargets_spectrum_verified":
        ("BfgsVerification.LGlobalTargets.spectrum", "BfgsVerification.LGlobalTargets.SpectrumTarget"),
    "LGlobalTargets_localInverse_verified":
        ("BfgsVerification.LGlobalTargets.localInverse", "BfgsVerification.LGlobalTargets.LocalInverseTarget"),
}
REPORT_SOURCE_CLOSURE_TARGETS = {
    "AffineRankLoss_rankLossCurvature_verified":
        ("BfgsVerification.AffineRankLoss.rankLossCurvature", "BfgsVerification.AffineRankLoss.RankLossCurvatureTarget"),
    "LWhitening_smoothIdentityFailure_verified":
        ("BfgsVerification.LWhitening.smoothIdentityFailure", "BfgsVerification.LWhitening.SmoothIdentityFailureTarget"),
    "LWhitening_stepIdentityFailure_verified":
        ("BfgsVerification.LWhitening.stepIdentityFailure", "BfgsVerification.LWhitening.StepIdentityFailureTarget"),
    "LWhitening_smoothLocalFailure_verified":
        ("BfgsVerification.LWhitening.smoothLocalFailure", "BfgsVerification.LWhitening.SmoothLocalFailureTarget"),
    "LWhitening_stepLocalFailure_verified":
        ("BfgsVerification.LWhitening.stepLocalFailure", "BfgsVerification.LWhitening.StepLocalFailureTarget"),
    "PlanarAllPairs_sourceAllPairTransport_verified":
        ("BfgsVerification.PlanarAllPairs.sourceAllPairTransport", "BfgsVerification.PlanarAllPairs.SourceAllPairTransportTarget"),
    "PlanarAllPairs_sourceAllEndpointEstimates_verified":
        ("BfgsVerification.PlanarAllPairs.sourceAllEndpointEstimates", "BfgsVerification.PlanarAllPairs.SourceAllEndpointEstimatesTarget"),
    "ComparisonEnergyWarning_comparisonEnergyWarning_verified":
        ("BfgsVerification.ComparisonEnergyWarning.comparisonEnergyWarning", "BfgsVerification.ComparisonEnergyWarning.ComparisonEnergyWarningTarget"),
    "AffineProjection_actualImageRange_verified":
        ("BfgsVerification.AffineProjection.actualImageRange", "BfgsVerification.AffineProjection.ActualImageRangeTarget"),
    "LReturnStableGraph_lStableManifold_verified":
        ("BfgsVerification.LReturnStableGraph.lStableManifold", "BfgsVerification.LReturnStableGraph.LStableManifoldTarget"),
    "LReturnStableGraph_lStableInvariantManifold_verified":
        ("BfgsVerification.LReturnStableGraph.lStableInvariantManifold", "BfgsVerification.LReturnStableGraph.LStableInvariantManifoldTarget"),
    "univariateSignBoundary_verified":
        ("BfgsVerification.univariateSignBoundary", "BfgsVerification.UnivariateSignBoundaryTarget"),
    "univariateConvexCover_verified":
        ("BfgsVerification.univariateConvexCover", "BfgsVerification.UnivariateConvexCoverTarget"),
    "univariateCellCover_verified":
        ("BfgsVerification.univariateCellCover", "BfgsVerification.UnivariateCellCoverTarget"),
    "polynomialFiberDerivative_verified":
        ("BfgsVerification.polynomialFiberDerivative", "BfgsVerification.PolynomialFiberDerivativeTarget"),
    "polynomialSimpleRootChart_verified":
        ("BfgsVerification.polynomialSimpleRootChart", "BfgsVerification.PolynomialSimpleRootChartTarget"),
    "polynomialSimpleRootProjection_verified":
        ("BfgsVerification.polynomialSimpleRootProjection", "BfgsVerification.PolynomialSimpleRootProjectionTarget"),
}
REPORT_GEOMETRY_COMPLETION_TARGETS = {
    "TwoPieceBudget_twoPieceTermination_verified":
        ("BfgsVerification.TwoPieceBudget.twoPieceTermination", "BfgsVerification.TwoPieceBudget.TwoPieceTerminationTarget"),
    "TwoPieceBudget_twoPieceLinearImage_verified":
        ("BfgsVerification.TwoPieceBudget.twoPieceLinearImage", "BfgsVerification.TwoPieceBudget.TwoPieceLinearImageTarget"),
    "LShapePrecision_actualJacobianPrecision_verified":
        ("BfgsVerification.LShapePrecision.actualJacobianPrecision", "BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget"),
    "ConstantRankFields_sourceConstantRank_verified":
        ("BfgsVerification.ConstantRankFields.sourceConstantRank", "BfgsVerification.ConstantRankFields.SourceConstantRankTarget"),
    "ConstantRankFields_sourceConstantRankEligible_verified":
        ("BfgsVerification.ConstantRankFields.sourceConstantRankEligible", "BfgsVerification.ConstantRankFields.SourceConstantRankEligibleTarget"),
    "polynomialDegreeStrata_verified":
        ("BfgsVerification.polynomialDegreeStrata", "BfgsVerification.PolynomialDegreeStrataTarget"),
    "polynomialDerivativeSpecialization_verified":
        ("BfgsVerification.polynomialDerivativeSpecialization", "BfgsVerification.PolynomialDerivativeSpecializationTarget"),
    "polynomialMultiplicityStrata_verified":
        ("BfgsVerification.polynomialMultiplicityStrata", "BfgsVerification.PolynomialMultiplicityStrataTarget"),
    "polynomialMultipleRootChart_verified":
        ("BfgsVerification.polynomialMultipleRootChart", "BfgsVerification.PolynomialMultipleRootChartTarget"),
    "realQuadraticElimination_verified":
        ("BfgsVerification.realQuadraticElimination", "BfgsVerification.RealQuadraticEliminationTarget"),
    "quadraticPolynomialProjection_verified":
        ("BfgsVerification.quadraticPolynomialProjection", "BfgsVerification.QuadraticPolynomialProjectionTarget"),
    "quadraticUniversalConditions_verified":
        ("BfgsVerification.quadraticUniversalConditions", "BfgsVerification.QuadraticUniversalConditionsTarget"),
    "actualDegreeTwoProjection_verified":
        ("BfgsVerification.actualDegreeTwoProjection", "BfgsVerification.ActualDegreeTwoProjectionTarget"),
    "positivePseudoDivision_verified":
        ("BfgsVerification.positivePseudoDivision", "BfgsVerification.PositivePseudoDivisionTarget"),
    "pseudoDivisionSpecialization_verified":
        ("BfgsVerification.pseudoDivisionSpecialization", "BfgsVerification.PseudoDivisionSpecializationTarget"),
    "finiteRootRemainders_verified":
        ("BfgsVerification.finiteRootRemainders", "BfgsVerification.FiniteRootRemaindersTarget"),
}
ALL_TARGETS = TARGETS | OBJECTIVE_TARGETS | FOUNDATION_TARGETS | REPORT_CORE_TARGETS | REPORT_GEOMETRY_TARGETS | REPORT_CONTINUATION_TARGETS | REPORT_APPLICATION_TARGETS | REPORT_FAMILY_TARGETS | REPORT_STRUCTURE_TARGETS | REPORT_ANALYTIC_TARGETS | REPORT_DYNAMICS_TARGETS | REPORT_CONSTRUCTION_TARGETS | REPORT_EMBEDDING_TARGETS | REPORT_STRUCTURAL_CLOSURE_TARGETS | REPORT_L_FAILURE_TARGETS | REPORT_SOURCE_CLOSURE_TARGETS | REPORT_GEOMETRY_COMPLETION_TARGETS


def theorem_names(code: str) -> list[str]:
    """Discover explicit declarations; compiled-environment enumeration audits
    these plus Lean-generated theorem declarations. Fail closed if one is absent.
    """
    scopes: list[tuple[str, str]] = []
    names: list[str] = []
    for line in code.splitlines():
        line = line.strip()
        namespace = re.match(r"namespace\s+(\S+)", line)
        section = re.match(r"(?:noncomputable\s+)?section(?:\s+(\S+))?$", line)
        ending = re.match(r"end(?:\s+(\S+))?$", line)
        if namespace:
            scopes.append(("namespace", namespace.group(1)))
        elif section:
            scopes.append(("section", section.group(1) or ""))
        elif ending and scopes:
            scopes.pop()
        theorem = re.search(r"\b(?:theorem|lemma)\s+([\w'.]+)", line)
        if theorem:
            name = theorem.group(1)
            prefix = ".".join(value for kind, value in scopes if kind == "namespace")
            names.append(name.removeprefix("_root_.") if name.startswith("_root_.")
                         else f"{prefix}.{name}" if prefix else name)
    return names


def lean_code_only(text: str) -> str:
    """Remove nested block comments, line comments and quoted strings."""
    out: list[str] = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(out)


def record(status: dict) -> None:
    AUDIT.mkdir(exist_ok=True)
    (AUDIT / "STATUS.json").write_text(json.dumps(status, indent=2) + "\n")


def run(command: list[str], logfile: str, timeout: int) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=timeout)
    (AUDIT / logfile).write_text(
        "$ " + " ".join(command) + "\n"
        + result.stdout + result.stderr + f"\nexit_code={result.returncode}\n"
    )
    return result


def dependency_inventory(manifest: dict, timeout: int) -> list[dict]:
    """Check every pinned Git dependency, including tracked worktree changes."""
    reports = []
    transcript = []
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise ValueError(f"Unpinned dependency kind: {package['name']}")
        directory = str(Path(manifest["packagesDir"]) / package["name"])
        results = []
        for git_args in (["rev-parse", "HEAD"],
                         ["status", "--porcelain", "--untracked-files=no"]):
            command = ["git", "-C", directory, *git_args]
            result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=timeout)
            transcript.append("$ " + " ".join(command) + "\n" + result.stdout + result.stderr
                              + f"exit_code={result.returncode}\n")
            results.append(result)
        revision, worktree = results
        reports.append({
            "package": package["name"], "expected_revision": package["rev"],
            "actual_revision": revision.stdout.strip(),
            "tracked_worktree_clean": worktree.returncode == 0 and not worktree.stdout.strip(),
            "verified": revision.returncode == 0 and revision.stdout.strip() == package["rev"]
                        and worktree.returncode == 0 and not worktree.stdout.strip(),
        })
    (AUDIT / "dependencies.log").write_text("\n".join(transcript))
    return reports


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--static-only", action="store_true")
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    local_elan = ROOT / ".toolchain" / "elan"
    if (local_elan / "bin" / "lake").is_file():
        os.environ["ELAN_HOME"] = str(local_elan)
        os.environ["PATH"] = str(local_elan / "bin") + os.pathsep + os.environ.get("PATH", "")
    os.environ["XDG_CACHE_HOME"] = str(ROOT / ".cache")
    os.environ["MATHLIB_CACHE_DIR"] = str(ROOT / ".cache" / "mathlib")
    AUDIT.mkdir(exist_ok=True)
    status: dict = {
        "timestamp_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "status": "NOT_CHECKED",
        "lean_typechecking_performed": False,
        **{flag: False for flag in ALL_TARGETS},
        "objective_level_model_formalized": False,
        "entire_report_verified": False,
        "verified_declarations": [],
        "warning": "Verification is pending for this invocation; success requires the complete build and axiom audit.",
    }
    lean_files = [ROOT / "BfgsVerification.lean", ROOT / "Audit.lean"] + sorted(
        (ROOT / "BfgsVerification").glob("*.lean")
    )
    forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b")
    problems = []
    theorem_count = 0
    declarations: dict[str, str] = {}
    sources = []
    for path in lean_files:
        content = path.read_text()
        code = lean_code_only(content)
        theorem_count += len(re.findall(r"\b(?:theorem|lemma)\s+", code))
        for name in theorem_names(code):
            declarations[name] = str(path.relative_to(ROOT))
        problems += [f"{path.relative_to(ROOT)}: forbidden token {m.group(0)}" for m in forbidden.finditer(code)]
        sources.append({"path": str(path.relative_to(ROOT)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    status["sources"] = sources
    status["explicit_theorem_declarations"] = theorem_count
    if len(declarations) != theorem_count:
        problems.append("Explicit theorem discovery mismatch; audit coverage cannot be certified")
    status["static_scan_passed"] = not problems
    status["static_scan_problems"] = problems
    if problems:
        status["status"] = "STATIC_SCAN_FAILED"
        record(status)
        print(json.dumps(status, indent=2))
        return 1
    if args.static_only:
        status["status"] = "STATIC_SCAN_ONLY_NOT_LEAN_VERIFIED"
        record(status)
        print(json.dumps(status, indent=2))
        return 0
    record(status)
    source_check = run([sys.executable, "scripts/report_inventory.py"], "report_source_check.log", args.timeout)
    status["report_sources_preserved"] = source_check.returncode == 0
    if source_check.returncode:
        status["status"] = "REPORT_SOURCE_COVERAGE_FAILED"
        record(status)
        return 1
    lake = shutil.which("lake")
    lean = shutil.which("lean")
    status["executables"] = {"lake": lake, "lean": lean}
    if lake is None or lean is None:
        status["status"] = "BLOCKED_NO_LEAN_TOOLCHAIN"
        record(status)
        print(json.dumps(status, indent=2))
        return 69
    try:
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
        revision = run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
                       "mathlib_revision.log", args.timeout)
        if mathlib["rev"] != EXPECTED_MATHLIB or revision.stdout.strip() != EXPECTED_MATHLIB:
            status["status"] = "DEPENDENCY_REVISION_FAILED"
            record(status)
            return 1
        status["mathlib_revision"] = EXPECTED_MATHLIB
        status["dependencies"] = dependency_inventory(manifest, args.timeout)
        if not all(package["verified"] for package in status["dependencies"]):
            status["status"] = "DEPENDENCY_CHECKOUT_FAILED"
            record(status)
            return 1
        version = run([lake, "env", "lean", "--version"], "lean_version.log", args.timeout)
        if version.returncode or not re.search(r"version " + re.escape(EXPECTED_LEAN) + r"(?:,|\s|\))", version.stdout):
            status["status"] = "TOOLCHAIN_VERSION_FAILED"
            record(status)
            return 1
        build = run([lake, "build"], "build.log", args.timeout)
        status["lean_typechecking_performed"] = True
        if build.returncode:
            status["status"] = "LEAN_BUILD_FAILED"
            record(status)
            return 1
        ax = run([lake, "env", "lean", "Audit.lean"], "axioms.log", args.timeout)
        if ax.returncode:
            status["status"] = "AXIOM_AUDIT_COMMAND_FAILED"
            record(status)
            return 1
        transcript = ax.stdout + ax.stderr
        reports = [json.loads(line.removeprefix("BFGS_AUDIT "))
                   for line in transcript.splitlines() if line.startswith("BFGS_AUDIT ")]
        counts = re.findall(r"^BFGS_AUDIT_COUNT (\d+)$", transcript, re.M)
        if len(counts) != 1 or int(counts[0]) != len(reports) or not reports:
            status["status"] = "AXIOM_INVENTORY_FAILED"
            record(status)
            return 1
        inventory = {item["theorem"]: item for item in reports}
        if len(inventory) != len(reports):
            status["status"] = "DUPLICATE_AXIOM_REPORT"
            record(status)
            return 1
        unexpected = []
        missing = []
        accepted = []
        missing = sorted(set(declarations) - set(inventory))
        for theorem, item in sorted(inventory.items()):
            axioms = set(item["axioms"])
            excess = sorted(axioms - ALLOWED_AXIOMS)
            if excess:
                unexpected.append({"theorem": theorem, "unexpected": excess})
            else:
                if theorem in declarations:
                    accepted.append({**item, "axioms": sorted(axioms), "source": declarations[theorem]})
        status["audited_declaration_count"] = len(inventory)
        (AUDIT / "declarations.json").write_text(json.dumps(reports, indent=2) + "\n")
        status["unexpected_axioms"] = unexpected
        status["missing_axiom_reports"] = missing
        if unexpected or missing:
            status["status"] = "AXIOM_AUDIT_FAILED"
            record(status)
            return 1
        for flag, (name, signature) in ALL_TARGETS.items():
            status[flag] = name in inventory and inventory[name]["signature"] == signature
        status["conditional_results"] = [
            {"theorem": name, "verified": name in inventory, "condition": "NormalizedHierarchy"}
            for name in [
                "BfgsVerification.ReciprocalGrowth.hierarchy_reciprocal_growth",
                "BfgsVerification.QuantitativeGrowth.hierarchy_finite_horizon_rpow",
                "BfgsVerification.QuantitativeGrowth.hierarchy_superquadratic_growth",
            ]
        ]
        status["conditional_results"] += [
            {"theorem": name, "verified": name in inventory, "condition": condition}
            for name, condition in [
                ("BfgsVerification.LocalStableOrbit.stableOrbit", "Actual strict derivative with contractive stable block and inverse-contracting unstable block; constructs a forward orbit without assuming one. The actual L spectral application and source orbit are now derived in LReturnStableOrbit/LGlobalFailure."),
                ("BfgsVerification.LocalStableOrbit.positiveStableOrbit", "Same actual derivative/contraction hypotheses plus a positive stable functional direction; proves positive initial scale. Actual L positive scale preservation is now derived from its return recurrence in source_oracle_orbit."),
                ("BfgsVerification.LBlockSplitting.positive_orbit_of_block", "Actual strict derivative, literal upper-block equations and two actual characteristic roots with stated ordering; all coordinates and the forward orbit are constructed. The actual L spectrum and global-run application are now discharged in LGlobalTargets."),
                ("BfgsVerification.SeedEmbedding.fromMetric_exact", "Conditional translated/scaled objective value and derivative interface; every field is discharged for the actual D objective in DEmbedding.actualOracleData and embeddingFailure"),
                ("BfgsVerification.AffineBarycentric.affine_critical_subfamily_eventually_full", "Continuous finite gradient data, affine independence and positive base weights; the actual finite-C1-max subdifferential bridge and original-family application are now discharged in localAffineCorrectness"),
                ("BfgsVerification.AdmissibleBFGSRun.compact_value_log_orders_of_correction_bound", "Actual pointwise correction bounded by C times next objective gap; discharged for the actual quadratic-gauge family in quadraticGaugeRates"),
                ("BfgsVerification.linearCorrectionRate", "Actual linear cumulative reference-correction budget; derived for centered smooth-plus-sublinear objectives"),
                ("BfgsVerification.linearImageLifting", "Explicit source premise: the projected actual run converges; full-space convergence and metric fiber selection are derived"),
                ("BfgsVerification.AccessibleJumpGeometry.visible_tangent_projection_ne_zero", "Full active-gradient tangent conclusion requires annihilation of all differences; accessible-span projection is proved separately"),
                ("BfgsVerification.EnergyBudget.energy_gap_tendsto_zero", "Scalar energy recurrence and negligible cumulative corrections"),
                ("BfgsVerification.ResidualBudget.residual_recurrence_incompatible", "Scalar residual recurrence; discharged in residualFrameCriterion"),
                ("BfgsVerification.quadraticCorrectionConvergence", "Actual cumulative reference-correction budget; not derived for every finite convex objective"),
                ("BfgsVerification.movingFrameCriterion", "Excludes exact frame certificates; constructing them from a given objective remains objective-specific"),
                ("BfgsVerification.residualFrameCriterion", "Excludes fixed-smooth-subspace residual certificates; constructing them remains objective-specific"),
            ]
        ]
        status["matrix_to_normalized_hierarchy_verified"] = "BfgsVerification.fullBFGS_normalizedHierarchy" in inventory
        status["finite_horizon_verified"] = "BfgsVerification.finiteHorizon" in inventory
        status["positive_definiteness_from_initial_matrix_verified"] = "BfgsVerification.fullBFGS_positive_invariants" in inventory
        status["armijo_summability_verified"] = "BfgsVerification.AdmissibleBFGSRun.summable_predicted_decreases_of_lower_bound" in inventory
        status["compact_gradient_bound_verified"] = "BfgsVerification.convex_gradient_bound_on_compact" in inventory
        status["objective_level_model_formalized"] = all(status[flag] for flag in OBJECTIVE_TARGETS)
        status["euclidean_operator_norm_bridge_verified"] = "BfgsVerification.FrameNorms.operatorSqBound_iff_opNorm_sq" in inventory
        status["arbitrary_subspace_basis_bridge_verified"] = "BfgsVerification.FrameNorms.orthonormal_matrix_for_subspace" in inventory
        status["outside_verified_scope"] = [
            "A general nonlinear Boolean semialgebraic projection/path/critical-value closure and the dependent C semialgebraic alternative; final source/synthesis/evidence reconciliation. Actual C arbitrary-dimensional constant-rank C1 field/secant theorem, L Jacobian precision, two-piece termination and arbitrary-dimensional no-infinite-continuation, and A multiplicity/quadratic-projection/positive-pseudo-division infrastructure are now checked. The finite polynomial fragments do not prove general quantifier elimination; see REPORT_STATUS.json",
            "Unconditional optimal-value convergence for arbitrary finite convex nonsmooth objectives",
            "Existence of admissible steps on every search ray",
        ]
        status["remaining_target_obligations"] = [name for flag, (name, _) in ALL_TARGETS.items()
                                                  if not status[flag]]
        complete = all(status[flag] for flag in ALL_TARGETS)
        matrix_complete = all(status[flag] for flag in TARGETS)
        objective_complete = matrix_complete and all(status[flag] for flag in OBJECTIVE_TARGETS)
        status["status"] = ("MODULE_M_AND_REPORT_GEOMETRY_COMPLETION_TARGETS_VERIFIED" if complete
                            else "MODULE_M_OBJECTIVE_AND_MATRIX_GROWTH_VERIFIED" if objective_complete
                            else "MODULE_M_MATRIX_AND_GROWTH_TARGETS_VERIFIED" if matrix_complete
                            else "STAGED_LEMMAS_CHECKED_MATRIX_TARGET_STILL_OPEN")
        status["warning"] = ("Claims concern the exact Module M and registered report-tranche targets printed in axioms.log. The entire report remains incomplete. "
                             "Energy convergence criteria retain explicit correction budgets; frame theorems exclude "
                             "certificates whose construction remains objective-specific. No unconditional BFGS "
                             "convergence or all-ray step-existence theorem is claimed.")
        status["verified_declarations"] = accepted
        record(status)
        print(json.dumps(status, indent=2))
        return 0 if complete else 1
    except subprocess.TimeoutExpired as exc:
        status["status"] = "COMMAND_TIMED_OUT"
        status["failed_command"] = exc.cmd
        record(status)
        return 124
    except OSError as exc:
        status["status"] = "EXECUTION_ERROR"
        status["error"] = str(exc)
        record(status)
        return 1
    except (ValueError, KeyError, StopIteration) as exc:
        status["status"] = "AUDIT_METADATA_ERROR"
        status["error"] = str(exc)
        record(status)
        return 1


if __name__ == "__main__":
    sys.exit(main())
