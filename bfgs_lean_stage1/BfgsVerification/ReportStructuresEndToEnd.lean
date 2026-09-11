import BfgsVerification.ReportStructuresTargets

noncomputable section
namespace BfgsVerification

theorem maxAffineThreshold : MaxAffineThresholdTarget :=
  @MaxAffine.Family.threshold_tail_convergence

theorem mixedLinearPowers : MixedLinearPowersTarget :=
  @RadialPower.local_mixed_linear_powers_basin

theorem recurrentLowRank : RecurrentLowRankTarget :=
  @AdmissibleBFGSRun.maxLinear_recurrent_span_le_two_finite_value

theorem relativeInteriorClass : RelativeInteriorClassTarget :=
  @Homogeneous.relativeInteriorZero_iff_nonneg_linear_zero_fiber

theorem parabolicPruning : ParabolicPruningTarget :=
  @Parabolic.Family.ordered_pruning_specification

theorem parabolicPrintedField : ParabolicPrintedFieldTarget :=
  @Parabolic.Example.exists_source_bandCertificate

theorem polyhedralBasin : PolyhedralBasinTarget :=
  @ConvexCellRadial.finite_polyhedral_basin

theorem fivePieceObstruction : FivePieceObstructionTarget :=
  @FivePieceObstruction.obstruction_in_every_neighborhood

theorem smoothPLQBasin : SmoothPLQBasinTarget :=
  @ConvexCellRadial.smooth_plus_piecewise_quadratic_basin

end BfgsVerification
