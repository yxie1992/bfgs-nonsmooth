import BfgsVerification
import BfgsVerification.EReconstructionFacts
import BfgsVerification.ReconstructedFourPieceTargets

/- Frozen literal propositions, authored from the checked research statements.
The runner never regenerates these expectations from the library aliases. -/
noncomputable section
open scoped BigOperators Topology
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def EJob15.Contract01 : Prop :=
∀ {F : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) → Real}
  (hF :
    @ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real.semiring
      Real.partialOrder
      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
      Real.instAddCommMonoid Real.partialOrder
      (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
        (@Algebra.id.{0} Real Real.instCommSemiring))
      (@Set.univ.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) F)
  {K : Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))} {ℓ : Real},
  @IsCompact.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
        @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      K →
    (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
        @Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
            (@Set.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) K x →
          @Eq.{1} Real (F x) ℓ) →
      (∀ (x y : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
          @HasSubset.Subset.{0} (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
              (@Set.instHasSubset.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
              (@segment.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.semiring
                Real.partialOrder
                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                  (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                    (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                    (@Algebra.id.{0} Real Real.instCommSemiring)))
                x y)
              (@frontier.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@setOf.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  fun (w : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                  @LE.le.{0} Real Real.instLE (F w) ℓ)) →
            @Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) x y) →
        (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
            @Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                (@Set.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) K x →
              Or
                (@ContDiffAt.{0, 0, 0} Real
                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                    (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.normedAddCommGroup)
                  (@Pi.normedSpace.{0, 0, 0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))
                    (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                    (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                      @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                    @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                  Real Real.normedAddCommGroup
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                  (@OfNat.ofNat.{0} (WithTop.{0} ENat) 2
                    (@instOfNatAtLeastTwo.{0} (WithTop.{0} ENat) 2
                      (@AddMonoidWithOne.toNatCast.{0} (WithTop.{0} ENat)
                        (@WithTop.addMonoidWithOne.{0} ENat
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENat
                            (@NonAssocSemiring.toAddCommMonoidWithOne.{0} ENat
                              (@Semiring.toNonAssocSemiring.{0} ENat
                                (@CommSemiring.toSemiring.{0} ENat instENatCommSemiring))))))
                      BfgsVerification.PlanarAllPairs.SourceAllEndpointEstimatesTarget._proof_1))
                  F x)
                (BfgsVerification.PlanarCornerCharts.ConvexTwoBranchRegularAt F x)) →
          (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
              @Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                  (@Set.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) K x →
                Not
                  (@BfgsVerification.AffineCriticalObjective.IsAffineCritical (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    F x)) →
            ∀ {c₁ c₂ : Real},
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) c₁ →
                @LT.lt.{0} Real Real.instLT c₂ (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) →
                  ∃ (m : Nat) (χ : Fin m → BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) → Real) (v :
                    Fin m → Real → BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                    And
                      (∀ (i : Fin m),
                        @ContDiff.{0, 0, 0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.normedAddCommGroup)
                          (@Pi.normedSpace.{0, 0, 0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))
                            (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                              @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                            @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                          Real Real.normedAddCommGroup
                          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                          (@WithTop.some.{0} ENat (@Top.top.{0} ENat instENatTop)) (χ i))
                      (∃ (U : Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (Q :
                        Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))),
                        And
                          (@IsOpen.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                              @UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                            U)
                          (And
                            (@HasSubset.Subset.{0}
                              (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                              (@Set.instHasSubset.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                              K U)
                            (And
                              (@HasSubset.Subset.{0}
                                (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                (@Set.instHasSubset.{0}
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                (@closure.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  U)
                                Q)
                              (And
                                (@IsCompact.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  Q)
                                (∃ (η : Real) (κ : Real) (δ : Real) (C : Real) (C' : Real) (C₀ : Real),
                                  And
                                    (@LT.lt.{0} Real Real.instLT
                                      (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) η)
                                    (And
                                      (@LT.lt.{0} Real Real.instLT
                                        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) κ)
                                      (And
                                        (@LT.lt.{0} Real Real.instLT
                                          (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) δ)
                                        (And
                                          (@LE.le.{0} Real Real.instLE
                                            (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) C)
                                          (And
                                            (@LE.le.{0} Real Real.instLE
                                              (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) C')
                                            (And
                                              (@LE.le.{0} Real Real.instLE
                                                (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) C₀)
                                              (And
                                                (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                                                  @Membership.mem.{0, 0}
                                                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                      (Set.{0}
                                                        (BfgsVerification.Vec
                                                          (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                      (@Set.instMembership.{0}
                                                        (BfgsVerification.Vec
                                                          (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                      Q x →
                                                    ∃ (L : NNReal) (V :
                                                      Set.{0}
                                                        (BfgsVerification.Vec
                                                          (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))),
                                                      And
                                                        (@Membership.mem.{0, 0}
                                                          (Set.{0}
                                                            (BfgsVerification.Vec
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                          (Filter.{0}
                                                            (BfgsVerification.Vec
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                          (@Filter.instMembership.{0}
                                                            (BfgsVerification.Vec
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                          (@nhds.{0}
                                                            (BfgsVerification.Vec
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                            (@Pi.topologicalSpace.{0, 0}
                                                              (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                              (fun
                                                                  (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                                                Real)
                                                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                                              @UniformSpace.toTopologicalSpace.{0} Real
                                                                (@PseudoMetricSpace.toUniformSpace.{0} Real
                                                                  Real.pseudoMetricSpace))
                                                            x)
                                                          V)
                                                        (@LipschitzOnWith.{0, 0}
                                                          (BfgsVerification.Vec
                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                          (BfgsVerification.Vec
                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                          (@pseudoEMetricSpacePi.{0, 0}
                                                            (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                                              Real)
                                                            (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                            fun (b : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                                            @EMetricSpace.toPseudoEMetricSpace.{0} Real
                                                              (@MetricSpace.toEMetricSpace.{0} Real Real.metricSpace))
                                                          (@pseudoEMetricSpacePi.{0, 0}
                                                            (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                                              Real)
                                                            (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                            fun (b : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                                            @EMetricSpace.toPseudoEMetricSpace.{0} Real
                                                              (@MetricSpace.toEMetricSpace.{0} Real Real.metricSpace))
                                                          L (@BfgsVerification.PlanarObjectiveField.field m F hF χ v)
                                                          V))
                                                (And
                                                  (∀
                                                    (x :
                                                      BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                                                    @Membership.mem.{0, 0}
                                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                        (Set.{0}
                                                          (BfgsVerification.Vec
                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                        (@Set.instMembership.{0}
                                                          (BfgsVerification.Vec
                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                        Q x →
                                                      ∀
                                                        (g :
                                                          BfgsVerification.Vec
                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                                                        @Membership.mem.{0, 0}
                                                            (BfgsVerification.Vec
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                            (Set.{0}
                                                              (BfgsVerification.Vec
                                                                (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                            (@Set.instMembership.{0}
                                                              (BfgsVerification.Vec
                                                                (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                            (@BfgsVerification.ConvexSubdifferential.subdifferential
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F x)
                                                            g →
                                                          @LE.le.{0} Real Real.instLE η
                                                            (@BfgsVerification.dot
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) g
                                                              (@BfgsVerification.PlanarObjectiveField.field m F hF χ v
                                                                x)))
                                                  (And
                                                    (∀
                                                      (x :
                                                        BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                                                      @Membership.mem.{0, 0}
                                                          (BfgsVerification.Vec
                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                          (Set.{0}
                                                            (BfgsVerification.Vec
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                          (@Set.instMembership.{0}
                                                            (BfgsVerification.Vec
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                          Q x →
                                                        ∀
                                                          (g :
                                                            BfgsVerification.Vec
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                                                          @Membership.mem.{0, 0}
                                                              (BfgsVerification.Vec
                                                                (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                              (Set.{0}
                                                                (BfgsVerification.Vec
                                                                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                              (@Set.instMembership.{0}
                                                                (BfgsVerification.Vec
                                                                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                              (@BfgsVerification.ConvexSubdifferential.subdifferential
                                                                (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F x)
                                                              g →
                                                            ∀
                                                              (h :
                                                                BfgsVerification.Vec
                                                                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                                                              @Membership.mem.{0, 0}
                                                                  (BfgsVerification.Vec
                                                                    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                                  (Set.{0}
                                                                    (BfgsVerification.Vec
                                                                      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                                  (@Set.instMembership.{0}
                                                                    (BfgsVerification.Vec
                                                                      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                                  (@BfgsVerification.ConvexSubdifferential.subdifferential
                                                                    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F x)
                                                                  h →
                                                                @Eq.{1} Real
                                                                  (@BfgsVerification.dot
                                                                    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) g
                                                                    (@BfgsVerification.PlanarObjectiveField.field m F hF
                                                                      χ v x))
                                                                  (@BfgsVerification.dot
                                                                    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) h
                                                                    (@BfgsVerification.PlanarObjectiveField.field m F hF
                                                                      χ v x)))
                                                    (∀
                                                      (x :
                                                        BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                                                      @Membership.mem.{0, 0}
                                                          (BfgsVerification.Vec
                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                          (Set.{0}
                                                            (BfgsVerification.Vec
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                          (@Set.instMembership.{0}
                                                            (BfgsVerification.Vec
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                          U x →
                                                        ∀
                                                          (z :
                                                            BfgsVerification.Vec
                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                                                          @Membership.mem.{0, 0}
                                                              (BfgsVerification.Vec
                                                                (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                              (Set.{0}
                                                                (BfgsVerification.Vec
                                                                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                              (@Set.instMembership.{0}
                                                                (BfgsVerification.Vec
                                                                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                              U z →
                                                            ∀
                                                              (g h :
                                                                BfgsVerification.Vec
                                                                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                                                              @BfgsVerification.TransportedCertificate.EligiblePair
                                                                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F c₁ c₂ x z
                                                                  g h →
                                                                @LT.lt.{0} Real Real.instLT
                                                                    (@Norm.norm.{0}
                                                                      (EuclideanSpace.{0, 0} Real
                                                                        (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                                                      (@PiLp.instNorm.{0, 0}
                                                                        (@OfNat.ofNat.{0} ENNReal 2
                                                                          (@instOfNatAtLeastTwo.{0} ENNReal 2
                                                                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                                                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0}
                                                                                ENNReal
                                                                                instENNRealAddCommMonoidWithOne))
                                                                            PiLp.innerProductSpace._proof_2))
                                                                        (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                                        (fun
                                                                            (x :
                                                                              Fin
                                                                                (@OfNat.ofNat.{0} Nat 2
                                                                                  (instOfNatNat 2))) =>
                                                                          Real)
                                                                        (Fin.fintype
                                                                          (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                                        fun
                                                                          (i :
                                                                            Fin
                                                                              (@OfNat.ofNat.{0} Nat 2
                                                                                (instOfNatNat 2))) =>
                                                                        Real.norm)
                                                                      (@BfgsVerification.euclideanVector
                                                                        (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                                                        (@HSub.hSub.{0, 0, 0}
                                                                          (BfgsVerification.Vec
                                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                                          (BfgsVerification.Vec
                                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                                          (BfgsVerification.Vec
                                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                                          (@instHSub.{0}
                                                                            (BfgsVerification.Vec
                                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                                            (@Pi.instSub.{0, 0}
                                                                              (Fin
                                                                                (@OfNat.ofNat.{0} Nat 2
                                                                                  (instOfNatNat 2)))
                                                                              (fun
                                                                                  (a :
                                                                                    Fin
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2))) =>
                                                                                Real)
                                                                              fun
                                                                                (i :
                                                                                  Fin
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2))) =>
                                                                              Real.instSub))
                                                                          z x)))
                                                                    δ →
                                                                  And
                                                                    (∀ (θ : Real),
                                                                      @Membership.mem.{0, 0} Real (Set.{0} Real)
                                                                          (@Set.instMembership.{0} Real)
                                                                          (@Set.Icc.{0} Real Real.instPreorder
                                                                            (@OfNat.ofNat.{0} Real 0
                                                                              (@Zero.toOfNat0.{0} Real Real.instZero))
                                                                            (@OfNat.ofNat.{0} Real 1
                                                                              (@One.toOfNat1.{0} Real Real.instOne)))
                                                                          θ →
                                                                        And
                                                                          (@Membership.mem.{0, 0}
                                                                            (BfgsVerification.Vec
                                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                                            (Set.{0}
                                                                              (BfgsVerification.Vec
                                                                                (@OfNat.ofNat.{0} Nat 2
                                                                                  (instOfNatNat 2))))
                                                                            (@Set.instMembership.{0}
                                                                              (BfgsVerification.Vec
                                                                                (@OfNat.ofNat.{0} Nat 2
                                                                                  (instOfNatNat 2))))
                                                                            Q
                                                                            (@HAdd.hAdd.{0, 0, 0}
                                                                              (BfgsVerification.Vec
                                                                                (@OfNat.ofNat.{0} Nat 2
                                                                                  (instOfNatNat 2)))
                                                                              (BfgsVerification.Vec
                                                                                (@OfNat.ofNat.{0} Nat 2
                                                                                  (instOfNatNat 2)))
                                                                              (BfgsVerification.Vec
                                                                                (@OfNat.ofNat.{0} Nat 2
                                                                                  (instOfNatNat 2)))
                                                                              (@instHAdd.{0}
                                                                                (BfgsVerification.Vec
                                                                                  (@OfNat.ofNat.{0} Nat 2
                                                                                    (instOfNatNat 2)))
                                                                                (@Pi.instAdd.{0, 0}
                                                                                  (Fin
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (fun
                                                                                      (a :
                                                                                        Fin
                                                                                          (@OfNat.ofNat.{0} Nat 2
                                                                                            (instOfNatNat 2))) =>
                                                                                    Real)
                                                                                  fun
                                                                                    (i :
                                                                                      Fin
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2))) =>
                                                                                  Real.instAdd))
                                                                              x
                                                                              (@HSMul.hSMul.{0, 0, 0} Real
                                                                                (BfgsVerification.Vec
                                                                                  (@OfNat.ofNat.{0} Nat 2
                                                                                    (instOfNatNat 2)))
                                                                                (BfgsVerification.Vec
                                                                                  (@OfNat.ofNat.{0} Nat 2
                                                                                    (instOfNatNat 2)))
                                                                                (@instHSMul.{0, 0} Real
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (@Function.hasSMul.{0, 0, 0}
                                                                                    (Fin
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    Real Real
                                                                                    (@Algebra.toSMul.{0, 0} Real Real
                                                                                      Real.instCommSemiring
                                                                                      (@CommSemiring.toSemiring.{0} Real
                                                                                        Real.instCommSemiring)
                                                                                      (@Algebra.id.{0} Real
                                                                                        Real.instCommSemiring))))
                                                                                θ
                                                                                (@HSub.hSub.{0, 0, 0}
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (@instHSub.{0}
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (@Pi.instSub.{0, 0}
                                                                                      (Fin
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2)))
                                                                                      (fun
                                                                                          (a :
                                                                                            Fin
                                                                                              (@OfNat.ofNat.{0} Nat 2
                                                                                                (instOfNatNat 2))) =>
                                                                                        Real)
                                                                                      fun
                                                                                        (i :
                                                                                          Fin
                                                                                            (@OfNat.ofNat.{0} Nat 2
                                                                                              (instOfNatNat 2))) =>
                                                                                      Real.instSub))
                                                                                  z x))))
                                                                          (@LE.le.{0} Real Real.instLE
                                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                              (@instHMul.{0} Real Real.instMul) κ
                                                                              (@Norm.norm.{0}
                                                                                (EuclideanSpace.{0, 0} Real
                                                                                  (Fin
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2))))
                                                                                (@PiLp.instNorm.{0, 0}
                                                                                  (@OfNat.ofNat.{0} ENNReal 2
                                                                                    (@instOfNatAtLeastTwo.{0} ENNReal 2
                                                                                      (@AddMonoidWithOne.toNatCast.{0}
                                                                                        ENNReal
                                                                                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0}
                                                                                          ENNReal
                                                                                          instENNRealAddCommMonoidWithOne))
                                                                                      PiLp.innerProductSpace._proof_2))
                                                                                  (Fin
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (fun
                                                                                      (x :
                                                                                        Fin
                                                                                          (@OfNat.ofNat.{0} Nat 2
                                                                                            (instOfNatNat 2))) =>
                                                                                    Real)
                                                                                  (Fin.fintype
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  fun
                                                                                    (i :
                                                                                      Fin
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2))) =>
                                                                                  Real.norm)
                                                                                (@BfgsVerification.euclideanVector
                                                                                  (@OfNat.ofNat.{0} Nat 2
                                                                                    (instOfNatNat 2))
                                                                                  (@HSub.hSub.{0, 0, 0}
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (@instHSub.{0}
                                                                                      (BfgsVerification.Vec
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2)))
                                                                                      (@Pi.instSub.{0, 0}
                                                                                        (Fin
                                                                                          (@OfNat.ofNat.{0} Nat 2
                                                                                            (instOfNatNat 2)))
                                                                                        (fun
                                                                                            (a :
                                                                                              Fin
                                                                                                (@OfNat.ofNat.{0} Nat 2
                                                                                                  (instOfNatNat 2))) =>
                                                                                          Real)
                                                                                        fun
                                                                                          (i :
                                                                                            Fin
                                                                                              (@OfNat.ofNat.{0} Nat 2
                                                                                                (instOfNatNat 2))) =>
                                                                                        Real.instSub))
                                                                                    z x))))
                                                                            (@abs.{0} Real Real.lattice
                                                                              Real.instAddGroup
                                                                              (BfgsVerification.HomogeneousPlanar.pairDet
                                                                                (@HSub.hSub.{0, 0, 0}
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (@instHSub.{0}
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (@Pi.instSub.{0, 0}
                                                                                      (Fin
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2)))
                                                                                      (fun
                                                                                          (a :
                                                                                            Fin
                                                                                              (@OfNat.ofNat.{0} Nat 2
                                                                                                (instOfNatNat 2))) =>
                                                                                        Real)
                                                                                      fun
                                                                                        (i :
                                                                                          Fin
                                                                                            (@OfNat.ofNat.{0} Nat 2
                                                                                              (instOfNatNat 2))) =>
                                                                                      Real.instSub))
                                                                                  z x)
                                                                                (@BfgsVerification.PlanarObjectiveField.field
                                                                                  m F hF χ v
                                                                                  (@HAdd.hAdd.{0, 0, 0}
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (@instHAdd.{0}
                                                                                      (BfgsVerification.Vec
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2)))
                                                                                      (@Pi.instAdd.{0, 0}
                                                                                        (Fin
                                                                                          (@OfNat.ofNat.{0} Nat 2
                                                                                            (instOfNatNat 2)))
                                                                                        (fun
                                                                                            (a :
                                                                                              Fin
                                                                                                (@OfNat.ofNat.{0} Nat 2
                                                                                                  (instOfNatNat 2))) =>
                                                                                          Real)
                                                                                        fun
                                                                                          (i :
                                                                                            Fin
                                                                                              (@OfNat.ofNat.{0} Nat 2
                                                                                                (instOfNatNat 2))) =>
                                                                                        Real.instAdd))
                                                                                    x
                                                                                    (@HSMul.hSMul.{0, 0, 0} Real
                                                                                      (BfgsVerification.Vec
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2)))
                                                                                      (BfgsVerification.Vec
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2)))
                                                                                      (@instHSMul.{0, 0} Real
                                                                                        (BfgsVerification.Vec
                                                                                          (@OfNat.ofNat.{0} Nat 2
                                                                                            (instOfNatNat 2)))
                                                                                        (@Function.hasSMul.{0, 0, 0}
                                                                                          (Fin
                                                                                            (@OfNat.ofNat.{0} Nat 2
                                                                                              (instOfNatNat 2)))
                                                                                          Real Real
                                                                                          (@Algebra.toSMul.{0, 0} Real
                                                                                            Real Real.instCommSemiring
                                                                                            (@CommSemiring.toSemiring.{0}
                                                                                              Real
                                                                                              Real.instCommSemiring)
                                                                                            (@Algebra.id.{0} Real
                                                                                              Real.instCommSemiring))))
                                                                                      θ
                                                                                      (@HSub.hSub.{0, 0, 0}
                                                                                        (BfgsVerification.Vec
                                                                                          (@OfNat.ofNat.{0} Nat 2
                                                                                            (instOfNatNat 2)))
                                                                                        (BfgsVerification.Vec
                                                                                          (@OfNat.ofNat.{0} Nat 2
                                                                                            (instOfNatNat 2)))
                                                                                        (BfgsVerification.Vec
                                                                                          (@OfNat.ofNat.{0} Nat 2
                                                                                            (instOfNatNat 2)))
                                                                                        (@instHSub.{0}
                                                                                          (BfgsVerification.Vec
                                                                                            (@OfNat.ofNat.{0} Nat 2
                                                                                              (instOfNatNat 2)))
                                                                                          (@Pi.instSub.{0, 0}
                                                                                            (Fin
                                                                                              (@OfNat.ofNat.{0} Nat 2
                                                                                                (instOfNatNat 2)))
                                                                                            (fun
                                                                                                (a :
                                                                                                  Fin
                                                                                                    (@OfNat.ofNat.{0}
                                                                                                      Nat 2
                                                                                                      (instOfNatNat
                                                                                                        2))) =>
                                                                                              Real)
                                                                                            fun
                                                                                              (i :
                                                                                                Fin
                                                                                                  (@OfNat.ofNat.{0} Nat
                                                                                                    2
                                                                                                    (instOfNatNat
                                                                                                      2))) =>
                                                                                            Real.instSub))
                                                                                        z x))))))))
                                                                    (And
                                                                      (@LE.le.{0} Real Real.instLE
                                                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                          (@instHDiv.{0} Real
                                                                            (@DivInvMonoid.toDiv.{0} Real
                                                                              Real.instDivInvMonoid))
                                                                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                                            (@instHPow.{0, 0} Real Nat
                                                                              (@Monoid.toNatPow.{0} Real
                                                                                Real.instMonoid))
                                                                            (@BfgsVerification.dot
                                                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                                                              (@HSub.hSub.{0, 0, 0}
                                                                                (BfgsVerification.Vec
                                                                                  (@OfNat.ofNat.{0} Nat 2
                                                                                    (instOfNatNat 2)))
                                                                                (BfgsVerification.Vec
                                                                                  (@OfNat.ofNat.{0} Nat 2
                                                                                    (instOfNatNat 2)))
                                                                                (BfgsVerification.Vec
                                                                                  (@OfNat.ofNat.{0} Nat 2
                                                                                    (instOfNatNat 2)))
                                                                                (@instHSub.{0}
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (@Pi.instSub.{0, 0}
                                                                                    (Fin
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (fun
                                                                                        (a :
                                                                                          Fin
                                                                                            (@OfNat.ofNat.{0} Nat 2
                                                                                              (instOfNatNat 2))) =>
                                                                                      Real)
                                                                                    fun
                                                                                      (i :
                                                                                        Fin
                                                                                          (@OfNat.ofNat.{0} Nat 2
                                                                                            (instOfNatNat 2))) =>
                                                                                    Real.instSub))
                                                                                h g)
                                                                              (@BfgsVerification.PlanarObjectiveField.field
                                                                                m F hF χ v z))
                                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                                          (@BfgsVerification.TransportedCertificate.pairCurvature
                                                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) x
                                                                            z g h))
                                                                        C₀)
                                                                      (∃ (lam : Real) (β : Real),
                                                                        And
                                                                          (@LT.lt.{0} Real Real.instLT
                                                                            (@OfNat.ofNat.{0} Real 0
                                                                              (@Zero.toOfNat0.{0} Real Real.instZero))
                                                                            lam)
                                                                          (And
                                                                            (@Eq.{1}
                                                                              (BfgsVerification.Vec
                                                                                (@OfNat.ofNat.{0} Nat 2
                                                                                  (instOfNatNat 2)))
                                                                              (@BfgsVerification.PlanarObjectiveField.field
                                                                                m F hF χ v z)
                                                                              (@HAdd.hAdd.{0, 0, 0}
                                                                                (BfgsVerification.Vec
                                                                                  (@OfNat.ofNat.{0} Nat 2
                                                                                    (instOfNatNat 2)))
                                                                                (BfgsVerification.Vec
                                                                                  (@OfNat.ofNat.{0} Nat 2
                                                                                    (instOfNatNat 2)))
                                                                                (BfgsVerification.Vec
                                                                                  (@OfNat.ofNat.{0} Nat 2
                                                                                    (instOfNatNat 2)))
                                                                                (@instHAdd.{0}
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (@Pi.instAdd.{0, 0}
                                                                                    (Fin
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (fun
                                                                                        (a :
                                                                                          Fin
                                                                                            (@OfNat.ofNat.{0} Nat 2
                                                                                              (instOfNatNat 2))) =>
                                                                                      Real)
                                                                                    fun
                                                                                      (i :
                                                                                        Fin
                                                                                          (@OfNat.ofNat.{0} Nat 2
                                                                                            (instOfNatNat 2))) =>
                                                                                    Real.instAdd))
                                                                                (@HSMul.hSMul.{0, 0, 0} Real
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (@instHSMul.{0, 0} Real
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (@Function.hasSMul.{0, 0, 0}
                                                                                      (Fin
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2)))
                                                                                      Real Real
                                                                                      (@Algebra.toSMul.{0, 0} Real Real
                                                                                        Real.instCommSemiring
                                                                                        (@CommSemiring.toSemiring.{0}
                                                                                          Real Real.instCommSemiring)
                                                                                        (@Algebra.id.{0} Real
                                                                                          Real.instCommSemiring))))
                                                                                  lam
                                                                                  (@BfgsVerification.PlanarObjectiveField.field
                                                                                    m F hF χ v x))
                                                                                (@HSMul.hSMul.{0, 0, 0} Real
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (BfgsVerification.Vec
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (@instHSMul.{0, 0} Real
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (@Function.hasSMul.{0, 0, 0}
                                                                                      (Fin
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2)))
                                                                                      Real Real
                                                                                      (@Algebra.toSMul.{0, 0} Real Real
                                                                                        Real.instCommSemiring
                                                                                        (@CommSemiring.toSemiring.{0}
                                                                                          Real Real.instCommSemiring)
                                                                                        (@Algebra.id.{0} Real
                                                                                          Real.instCommSemiring))))
                                                                                  β
                                                                                  (@HSub.hSub.{0, 0, 0}
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (BfgsVerification.Vec
                                                                                      (@OfNat.ofNat.{0} Nat 2
                                                                                        (instOfNatNat 2)))
                                                                                    (@instHSub.{0}
                                                                                      (BfgsVerification.Vec
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2)))
                                                                                      (@Pi.instSub.{0, 0}
                                                                                        (Fin
                                                                                          (@OfNat.ofNat.{0} Nat 2
                                                                                            (instOfNatNat 2)))
                                                                                        (fun
                                                                                            (a :
                                                                                              Fin
                                                                                                (@OfNat.ofNat.{0} Nat 2
                                                                                                  (instOfNatNat 2))) =>
                                                                                          Real)
                                                                                        fun
                                                                                          (i :
                                                                                            Fin
                                                                                              (@OfNat.ofNat.{0} Nat 2
                                                                                                (instOfNatNat 2))) =>
                                                                                        Real.instSub))
                                                                                    z x))))
                                                                            (And
                                                                              (@LE.le.{0} Real Real.instLE
                                                                                (@abs.{0} Real Real.lattice
                                                                                  Real.instAddGroup (Real.log lam))
                                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                  (@instHMul.{0} Real Real.instMul) C
                                                                                  (@BfgsVerification.TransportedCertificate.pairDecrease
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2))
                                                                                    x z g)))
                                                                              (@LE.le.{0} Real Real.instLE
                                                                                  (@BfgsVerification.TransportedCertificate.pairDecrease
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2))
                                                                                    x z g)
                                                                                  (@OfNat.ofNat.{0} Real 1
                                                                                    (@One.toOfNat1.{0} Real
                                                                                      Real.instOne)) →
                                                                                @LE.le.{0} Real Real.instLE
                                                                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                                                    (@instHPow.{0, 0} Real Nat
                                                                                      (@Monoid.toNatPow.{0} Real
                                                                                        Real.instMonoid))
                                                                                    lam
                                                                                    (@OfNat.ofNat.{0} Nat 2
                                                                                      (instOfNatNat 2)))
                                                                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                                    (@instHAdd.{0} Real Real.instAdd)
                                                                                    (@OfNat.ofNat.{0} Real 1
                                                                                      (@One.toOfNat1.{0} Real
                                                                                        Real.instOne))
                                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                      (@instHMul.{0} Real Real.instMul)
                                                                                      C'
                                                                                      (@BfgsVerification.TransportedCertificate.pairDecrease
                                                                                        (@OfNat.ofNat.{0} Nat 2
                                                                                          (instOfNatNat 2))
                                                                                        x z g))))))))))))))))))))))

def EJob15.Contract02 : Prop :=
∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
  @LE.le.{0} Real Real.instLE
      (@abs.{0} Real Real.lattice Real.instAddGroup
        (x
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_2 0))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 10
          (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast
            BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_3))) →
    @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (x
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_2 1))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real 10
            (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast
              BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_3))) →
      And
        (@LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real 267
              (@instOfNatAtLeastTwo.{0} Real 267 Real.instNatCast
                BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_4))
            (@OfNat.ofNat.{0} Real 100
              (@instOfNatAtLeastTwo.{0} Real 100 Real.instNatCast
                BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_5)))
          (BfgsVerification.PlanarQuadraticExample.denominator x))
        (And
          (@LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real 23
                (@instOfNatAtLeastTwo.{0} Real 23 Real.instNatCast
                  BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_6))
              (@OfNat.ofNat.{0} Real 100
                (@instOfNatAtLeastTwo.{0} Real 100 Real.instNatCast
                  BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_5)))
            (BfgsVerification.PlanarQuadraticExample.numerator x
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 0
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                  BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_7 0))))
          (And
            (@LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real 49
                  (@instOfNatAtLeastTwo.{0} Real 49 Real.instNatCast
                    BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_8))
                (@OfNat.ofNat.{0} Real 100
                  (@instOfNatAtLeastTwo.{0} Real 100 Real.instNatCast
                    BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_5)))
              (BfgsVerification.PlanarQuadraticExample.numerator x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 1
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                    BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_7 1))))
            (And
              (@LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real 45
                    (@instOfNatAtLeastTwo.{0} Real 45 Real.instNatCast
                      BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_9))
                  (@OfNat.ofNat.{0} Real 100
                    (@instOfNatAtLeastTwo.{0} Real 100 Real.instNatCast
                      BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_5)))
                (BfgsVerification.PlanarQuadraticExample.numerator x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 2
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                      BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_7 2))))
              (And
                (∀ (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))),
                  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                    (BfgsVerification.PlanarQuadraticExample.coefficients x i))
                (And
                  (@Eq.{1} Real
                    (∑ i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)),
                      BfgsVerification.PlanarQuadraticExample.coefficients x i)
                    (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
                  (And
                    (@Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (∑ i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)),
                        @HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (@instHSMul.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                              (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                (@Algebra.id.{0} Real Real.instCommSemiring))))
                          (BfgsVerification.PlanarQuadraticExample.coefficients x i)
                          (BfgsVerification.PlanarQuadraticExample.gradient i x))
                      (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                        (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))
                    (And
                      (@AffineIndependent.{0, 0, 0, 0} Real (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) → Real)
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.instRing
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                          (@Ring.toSemiring.{0} Real Real.instRing)
                          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                            (@NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Real
                              (@Semiring.toNonUnitalSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
                          (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                  (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                        (@Finset.instAddTorsorForall.{0, 0} Real Real.instRing
                          (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                        (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                        BfgsVerification.PlanarQuadraticExample.gradient i x)
                      (And
                        (@BfgsVerification.AffineCriticalObjective.AffineCorrectAt
                          (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) BfgsVerification.PlanarQuadraticExample.objective x)
                        (∀ (w : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))),
                          @Eq.{1} Real (∑ i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)), w i)
                              (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) →
                            @Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (∑ i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)),
                                  @HSMul.hSMul.{0, 0, 0} Real
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (@instHSMul.{0, 0} Real
                                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                        Real
                                        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                          (@Algebra.id.{0} Real Real.instCommSemiring))))
                                    (w i) (BfgsVerification.PlanarQuadraticExample.gradient i x))
                                (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                                  (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))) →
                              @Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) w
                                (BfgsVerification.PlanarQuadraticExample.coefficients x))))))))))

def EJob15.Contract03 : Prop :=
∀
  (R :
    BfgsVerification.AdmissibleBFGSRun (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
      BfgsVerification.PlanarQuadraticExample.objective),
  @LT.lt.{0} Real Real.instLT
      (BfgsVerification.PlanarQuadraticExample.objective
        (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
          BfgsVerification.PlanarQuadraticExample.objective R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 100
          (@instOfNatAtLeastTwo.{0} Real 100 Real.instNatCast
            BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_5))) →
    And
      (@Filter.Tendsto.{0, 0} Nat Real
        (fun (k : Nat) =>
          BfgsVerification.PlanarQuadraticExample.objective
            (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              BfgsVerification.PlanarQuadraticExample.objective R k))
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
      (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
          BfgsVerification.PlanarQuadraticExample.objective R)
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
            (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)))))

def EJob15.Contract04 : Prop :=
And
  (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))),
    @Eq.{1} Real
      (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
        (BfgsVerification.SpatialQuadraticWarning.gradient x) x)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real 2
          (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast BfgsVerification.SpatialCanonicalWarningTarget._proof_3))
        (BfgsVerification.SpatialQuadraticWarning.objective x)))
  (And
    (∀ (ε : Real),
      @Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
        (BfgsVerification.SpatialQuadraticWarning.next ε)
        (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
          (@instHAdd.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
            (@Pi.instAdd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAdd))
          BfgsVerification.SpatialQuadraticWarning.base (BfgsVerification.SpatialQuadraticWarning.step ε)))
    (And
      (∀ (b : Real),
        @BfgsVerification.RadialCertificate.HasRadialSecantBounds (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
          BfgsVerification.SpatialQuadraticWarning.objective
          (@setOf.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
            fun (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
            @LE.le.{0} Real Real.instLE (BfgsVerification.SpatialQuadraticWarning.objective x) b)
          (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 0
            (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
              (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instZero))))
      (∀
        (R :
          BfgsVerification.AdmissibleBFGSRun (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
            BfgsVerification.SpatialQuadraticWarning.objective),
        And
          (@Filter.Tendsto.{0, 0} Nat Real
            (fun (k : Nat) =>
              BfgsVerification.SpatialQuadraticWarning.objective
                (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                  BfgsVerification.SpatialQuadraticWarning.objective R k))
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (@nhds.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
          (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
            (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              BfgsVerification.SpatialQuadraticWarning.objective R)
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 0
                (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                  (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instZero))))))))

def EJob15.Contract05 : Prop :=
And
  (@Matrix.PosDef.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
    (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.commRing Real.partialOrder instStarRingReal
    BfgsVerification.SpatialQuadraticWarning.Q)
  (And
    (@ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real.semiring
      Real.partialOrder
      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
      Real.instAddCommMonoid Real.partialOrder
      (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
        (@Algebra.id.{0} Real Real.instCommSemiring))
      (@Set.univ.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))
      BfgsVerification.SpatialQuadraticWarning.objective)
    (And
      (∀ (N : WithTop.{0} ENat),
        @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
          (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
            (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.normedAddCommGroup)
          (@Pi.normedSpace.{0, 0, 0} Real
            (@NontriviallyNormedField.toNormedField.{0} Real
              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))
            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
            (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
            (fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
              @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
            @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          N BfgsVerification.SpatialQuadraticWarning.objective)
      (And
        (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))),
          @HasFDerivAt.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
            (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommGroup)
            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real Real.semiring
              Real.instAddCommMonoid
              (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                      (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                        (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            Real
            (@SeminormedAddCommGroup.toAddCommGroup.{0} Real
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))
            (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                      (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            BfgsVerification.SpatialQuadraticWarning.objective
            (@BfgsVerification.gradientFunctional (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (BfgsVerification.SpatialQuadraticWarning.gradient x))
            x)
        (∀ (ε : Real),
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
            @LT.lt.{0} Real Real.instLT ε
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                  (@OfNat.ofNat.{0} Real 10
                    (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast
                      BfgsVerification.SpatialCanonicalWarningTarget._proof_1))) →
              And
                (@BfgsVerification.TransportedCertificate.EligiblePair (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                  BfgsVerification.SpatialQuadraticWarning.objective
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real 4
                      (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                        BfgsVerification.SpatialCanonicalWarningTarget._proof_2)))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real 2
                      (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                        BfgsVerification.SpatialCanonicalWarningTarget._proof_3)))
                  BfgsVerification.SpatialQuadraticWarning.base (BfgsVerification.SpatialQuadraticWarning.next ε)
                  (BfgsVerification.SpatialQuadraticWarning.gradient BfgsVerification.SpatialQuadraticWarning.base)
                  (BfgsVerification.SpatialQuadraticWarning.gradient (BfgsVerification.SpatialQuadraticWarning.next ε)))
                (And
                  (@Eq.{1} Real
                    (@BfgsVerification.TransportedCertificate.pairDecrease (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                      BfgsVerification.SpatialQuadraticWarning.base (BfgsVerification.SpatialQuadraticWarning.next ε)
                      (BfgsVerification.SpatialQuadraticWarning.gradient BfgsVerification.SpatialQuadraticWarning.base))
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) ε
                      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                  (And
                    (@Eq.{1} Real
                      (@BfgsVerification.TransportedCertificate.pairCurvature (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                        BfgsVerification.SpatialQuadraticWarning.base (BfgsVerification.SpatialQuadraticWarning.next ε)
                        (BfgsVerification.SpatialQuadraticWarning.gradient
                          BfgsVerification.SpatialQuadraticWarning.base)
                        (BfgsVerification.SpatialQuadraticWarning.gradient
                          (BfgsVerification.SpatialQuadraticWarning.next ε)))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) ε
                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) ε
                                (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real 2
                                  (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                                    BfgsVerification.SpatialCanonicalWarningTarget._proof_3))
                                ε))
                            (@OfNat.ofNat.{0} Real 4
                              (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                                BfgsVerification.SpatialCanonicalWarningTarget._proof_2))))
                        (@OfNat.ofNat.{0} Real 3
                          (@instOfNatAtLeastTwo.{0} Real 3 Real.instNatCast
                            BfgsVerification.SpatialCanonicalWarningTarget._proof_4))))
                    (And
                      (@Eq.{1} Real
                        (@Matrix.det.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (instDecidableEqFin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real.commRing
                          (BfgsVerification.SpatialQuadraticWarning.tripleColumns
                            (BfgsVerification.SpatialQuadraticWarning.gradient
                              BfgsVerification.SpatialQuadraticWarning.base)
                            (BfgsVerification.SpatialQuadraticWarning.step ε)
                            (BfgsVerification.SpatialQuadraticWarning.change ε)))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@OfNat.ofNat.{0} Real 4
                                (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                                  BfgsVerification.SpatialCanonicalWarningTarget._proof_2))
                              (@OfNat.ofNat.{0} Real 3
                                (@instOfNatAtLeastTwo.{0} Real 3 Real.instNatCast
                                  BfgsVerification.SpatialCanonicalWarningTarget._proof_4)))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) ε
                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) ε)))
                      (And
                        (∃ (H : BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))),
                          And
                            (@Matrix.PosDef.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                              (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.commRing Real.partialOrder
                              instStarRingReal H)
                            (And
                              (@Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                (@BfgsVerification.bfgsStep (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) H
                                  (BfgsVerification.SpatialQuadraticWarning.gradient
                                    BfgsVerification.SpatialQuadraticWarning.base)
                                  (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
                                (BfgsVerification.SpatialQuadraticWarning.step ε))
                              (@Eq.{1} Real
                                (@BfgsVerification.metricEnergy (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) H
                                  (BfgsVerification.SpatialQuadraticWarning.gradient
                                    BfgsVerification.SpatialQuadraticWarning.base))
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) ε
                                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))
                        (And
                          (∀ (N : WithTop.{0} ENat),
                            And
                              (@ContDiffAt.{0, 0, 0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.normedAddCommGroup)
                                (@Pi.normedSpace.{0, 0, 0} Real
                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))
                                  (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                  @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.normedAddCommGroup)
                                (@Pi.normedSpace.{0, 0, 0} Real
                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))
                                  (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                  @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                                N BfgsVerification.SpatialQuadraticWarning.canonicalField
                                BfgsVerification.SpatialQuadraticWarning.base)
                              (@ContDiffAt.{0, 0, 0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.normedAddCommGroup)
                                (@Pi.normedSpace.{0, 0, 0} Real
                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))
                                  (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                  @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.normedAddCommGroup)
                                (@Pi.normedSpace.{0, 0, 0} Real
                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))
                                  (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                  @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                                N BfgsVerification.SpatialQuadraticWarning.canonicalField
                                (BfgsVerification.SpatialQuadraticWarning.next ε)))
                          (And
                            (And
                              (@Eq.{1} Real
                                (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                                  (BfgsVerification.SpatialQuadraticWarning.gradient
                                    BfgsVerification.SpatialQuadraticWarning.base)
                                  (BfgsVerification.SpatialQuadraticWarning.canonicalField
                                    BfgsVerification.SpatialQuadraticWarning.base))
                                (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
                              (@Eq.{1} Real
                                (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                                  (BfgsVerification.SpatialQuadraticWarning.gradient
                                    (BfgsVerification.SpatialQuadraticWarning.next ε))
                                  (BfgsVerification.SpatialQuadraticWarning.canonicalField
                                    (BfgsVerification.SpatialQuadraticWarning.next ε)))
                                (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))))
                            (And
                              (BfgsVerification.SpatialQuadraticWarning.canonicalField
                                  (BfgsVerification.SpatialQuadraticWarning.next ε) ∉
                                @Submodule.span.{0, 0} Real
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
                                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                              (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                                  (@Insert.insert.{0, 0}
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))
                                    (@Set.instInsert.{0}
                                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))
                                    (BfgsVerification.SpatialQuadraticWarning.canonicalField
                                      BfgsVerification.SpatialQuadraticWarning.base)
                                    (@Singleton.singleton.{0, 0}
                                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))
                                      (@Set.instSingletonSet.{0}
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))
                                      (BfgsVerification.SpatialQuadraticWarning.step ε))))
                              (∀ (a : Real),
                                Not
                                  (@Matrix.PosSemidef.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                    (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.commRing
                                    Real.partialOrder instStarRingReal
                                    (@HSub.hSub.{0, 0, 0}
                                      (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                        (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                      (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                        (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                      (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                        (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                      (@instHSub.{0}
                                        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                        (@Matrix.sub.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real.instSub))
                                      (@HSMul.hSMul.{0, 0, 0} Real
                                        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                        (@instHSMul.{0, 0} Real
                                          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                          (@Matrix.smul.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                                            (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                              (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                              (@Algebra.id.{0} Real Real.instCommSemiring))))
                                        a
                                        (@HMul.hMul.{0, 0, 0}
                                          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                          (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                            (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.instMul
                                            Real.instAddCommMonoid)
                                          (@HMul.hMul.{0, 0, 0}
                                            (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                            (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                              (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                              (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                              (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                              (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.instMul
                                              Real.instAddCommMonoid)
                                            (@BfgsVerification.TransportedCertificate.stepProjector
                                              (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                                              (BfgsVerification.SpatialQuadraticWarning.step ε))
                                            (@BfgsVerification.outer (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                                              (BfgsVerification.SpatialQuadraticWarning.canonicalField
                                                BfgsVerification.SpatialQuadraticWarning.base)
                                              (BfgsVerification.SpatialQuadraticWarning.canonicalField
                                                BfgsVerification.SpatialQuadraticWarning.base)))
                                          (@BfgsVerification.TransportedCertificate.stepProjector
                                            (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                                            (BfgsVerification.SpatialQuadraticWarning.step ε))))
                                      (@HMul.hMul.{0, 0, 0}
                                        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                        (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                          (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.instMul
                                          Real.instAddCommMonoid)
                                        (@HMul.hMul.{0, 0, 0}
                                          (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real)
                                          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                            (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                            (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.instMul
                                            Real.instAddCommMonoid)
                                          (@BfgsVerification.TransportedCertificate.stepProjector
                                            (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                                            (BfgsVerification.SpatialQuadraticWarning.step ε))
                                          (@BfgsVerification.outer (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                                            (BfgsVerification.SpatialQuadraticWarning.canonicalField
                                              (BfgsVerification.SpatialQuadraticWarning.next ε))
                                            (BfgsVerification.SpatialQuadraticWarning.canonicalField
                                              (BfgsVerification.SpatialQuadraticWarning.next ε))))
                                        (@BfgsVerification.TransportedCertificate.stepProjector
                                          (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                                          (BfgsVerification.SpatialQuadraticWarning.step ε)))))))))))))))))

def EJob15.Contract06 : Prop :=
∀ (h hθ : Real → Real) (θ h1 h2 : Real),
  @HasDerivAt.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.instAddCommGroup
      (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
              (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@IsModuleTopology.toContinuousSMul.{0, 0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real
            (@SeminormedRing.toPseudoMetricSpace.{0} Real
              (@SeminormedCommRing.toSeminormedRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real
                  (@NormedField.toNormedCommRing.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
        Real Real.instAdd
        (@SMulZeroClass.toSMul.{0, 0} Real Real
          (@AddZeroClass.toZero.{0} Real
            (@AddMonoid.toAddZeroClass.{0} Real
              (@SubNegMonoid.toAddMonoid.{0} Real
                (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup)))))
          (@DistribSMul.toSMulZeroClass.{0, 0} Real Real
            (@AddMonoid.toAddZeroClass.{0} Real
              (@SubNegMonoid.toAddMonoid.{0} Real
                (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))
            (@DistribMulAction.toDistribSMul.{0, 0} Real Real
              (@MonoidWithZero.toMonoid.{0} Real
                (@Semiring.toMonoidWithZero.{0} Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@NontriviallyNormedField.toNormedField.{0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
              (@SubNegMonoid.toAddMonoid.{0} Real
                (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup)))
              (@Module.toDistribMulAction.{0, 0} Real Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
                (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                        (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))))
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@IsTopologicalSemiring.toIsModuleTopology.{0} Real Real.semiring
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real
              (@SeminormedRing.toPseudoMetricSpace.{0} Real
                (@SeminormedCommRing.toSeminormedRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real
                    (@NormedField.toNormedCommRing.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
          (@IsTopologicalRing.toIsTopologicalSemiring.{0} Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real
                (@SeminormedRing.toPseudoMetricSpace.{0} Real
                  (@SeminormedCommRing.toSeminormedRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real
                      (@NormedField.toNormedCommRing.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Real
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                  (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing))))
            instIsTopologicalRingReal)))
      h h1 θ →
    @HasDerivAt.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.instAddCommGroup
        (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@IsModuleTopology.toContinuousSMul.{0, 0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real
              (@SeminormedRing.toPseudoMetricSpace.{0} Real
                (@SeminormedCommRing.toSeminormedRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real
                    (@NormedField.toNormedCommRing.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
          Real Real.instAdd
          (@SMulZeroClass.toSMul.{0, 0} Real Real
            (@AddZeroClass.toZero.{0} Real
              (@AddMonoid.toAddZeroClass.{0} Real
                (@SubNegMonoid.toAddMonoid.{0} Real
                  (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup)))))
            (@DistribSMul.toSMulZeroClass.{0, 0} Real Real
              (@AddMonoid.toAddZeroClass.{0} Real
                (@SubNegMonoid.toAddMonoid.{0} Real
                  (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))
              (@DistribMulAction.toDistribSMul.{0, 0} Real Real
                (@MonoidWithZero.toMonoid.{0} Real
                  (@Semiring.toMonoidWithZero.{0} Real
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
                (@SubNegMonoid.toAddMonoid.{0} Real
                  (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup)))
                (@Module.toDistribMulAction.{0, 0} Real Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@NontriviallyNormedField.toNormedField.{0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                  (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
                  (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))))
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@IsTopologicalSemiring.toIsModuleTopology.{0} Real Real.semiring
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real
                (@SeminormedRing.toPseudoMetricSpace.{0} Real
                  (@SeminormedCommRing.toSeminormedRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real
                      (@NormedField.toNormedCommRing.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            (@IsTopologicalRing.toIsTopologicalSemiring.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real
                  (@SeminormedRing.toPseudoMetricSpace.{0} Real
                    (@SeminormedCommRing.toSeminormedRing.{0} Real
                      (@NormedCommRing.toSeminormedCommRing.{0} Real
                        (@NormedField.toNormedCommRing.{0} Real
                          (@NontriviallyNormedField.toNormedField.{0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Real
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing))))
              instIsTopologicalRingReal)))
        hθ h2 θ →
      @Eq.{1} Real (hθ θ) h1 →
        @HasDerivAt.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
              (@NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Real
                (@Semiring.toNonUnitalSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
            (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                      (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@instContinuousSMulForall.{0, 0, 0} Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real
                (@SeminormedRing.toPseudoMetricSpace.{0} Real
                  (@SeminormedCommRing.toSeminormedRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real
                      (@NormedField.toNormedCommRing.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            (fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring Real.semiring
                (@Algebra.id.{0} Real Real.instCommSemiring))
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
            @IsModuleTopology.toContinuousSMul.{0, 0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real
                  (@SeminormedRing.toPseudoMetricSpace.{0} Real
                    (@SeminormedCommRing.toSeminormedRing.{0} Real
                      (@NormedCommRing.toSeminormedCommRing.{0} Real
                        (@NormedField.toNormedCommRing.{0} Real
                          (@NontriviallyNormedField.toNormedField.{0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
              Real Real.instAdd
              (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring Real.semiring
                (@Algebra.id.{0} Real Real.instCommSemiring))
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@IsTopologicalSemiring.toIsModuleTopology.{0} Real Real.semiring
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real
                    (@SeminormedRing.toPseudoMetricSpace.{0} Real
                      (@SeminormedCommRing.toSeminormedRing.{0} Real
                        (@NormedCommRing.toSeminormedCommRing.{0} Real
                          (@NormedField.toNormedCommRing.{0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
                (@IsTopologicalRing.toIsTopologicalSemiring.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real
                      (@SeminormedRing.toPseudoMetricSpace.{0} Real
                        (@SeminormedCommRing.toSeminormedRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real
                            (@NormedField.toNormedCommRing.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Real
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                      (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                        (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing))))
                  instIsTopologicalRingReal)))
          (BfgsVerification.PlanarTransport.angularFrame h hθ)
          (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@instHSMul.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                  (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                  (@Algebra.id.{0} Real Real.instCommSemiring))))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (h θ) h2)
            (BfgsVerification.PlanarTransport.tangent θ))
          θ

def EJob15.Contract07 : Prop :=
∀ (θ sT sn a b e : Real),
  @Eq.{1} Real
    (BfgsVerification.HomogeneousPlanar.pairDet
      (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@instHAdd.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Pi.instAdd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAdd))
        (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@instHSMul.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
              (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                (@Algebra.id.{0} Real Real.instCommSemiring))))
          sT (BfgsVerification.PlanarTransport.tangent θ))
        (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@instHSMul.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
              (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                (@Algebra.id.{0} Real Real.instCommSemiring))))
          sn (BfgsVerification.PlanarTransport.normal θ)))
      (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@instHAdd.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Pi.instAdd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAdd))
        (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@instHSMul.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
              (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                (@Algebra.id.{0} Real Real.instCommSemiring))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a sT)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b sn))
          (BfgsVerification.PlanarTransport.tangent θ))
        (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@instHSMul.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
              (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                (@Algebra.id.{0} Real Real.instCommSemiring))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) e sn)
          (BfgsVerification.PlanarTransport.normal θ))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) sn
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) a e) sT)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b sn)))

def EJob15.Contract08 : Prop :=
∀ {n : Nat} {F : BfgsVerification.Vec n → Real} (R : BfgsVerification.AdmissibleBFGSRun n F) {r : Nat} (k : Nat)
  (V W : Matrix.{0, 0, 0} (Fin n) (Fin r) Real) (T : BfgsVerification.Mat r) (b : BfgsVerification.Vec r),
  @Eq.{1} (Matrix.{0, 0, 0} (Fin n) (Fin r) Real) W
      (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin r) Real) (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
        (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
        (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
          (@Matrix.add.{0, 0, 0} (Fin n) (Fin r) Real Real.instAdd))
        (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin r) Real) (BfgsVerification.Mat r)
          (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin r) (Fin r) Real (Fin.fintype r)
            Real.instMul Real.instAddCommMonoid)
          V T)
        (@BfgsVerification.EnergyIdentities.rectOuter n r (@BfgsVerification.AdmissibleBFGSRun.displacement n F R k)
          b)) →
    @Eq.{1} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
      (@BfgsVerification.metricGram.{0} n (Fin r)
        (@BfgsVerification.AdmissibleBFGSRun.hessian n F R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
        W)
      (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real) (BfgsVerification.Mat r)
        (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
        (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
          (@Matrix.add.{0, 0, 0} (Fin r) (Fin r) Real Real.instAdd))
        (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real) (BfgsVerification.Mat r)
          (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin r) (Fin r) (Fin r) Real (Fin.fintype r)
            Real.instMul Real.instAddCommMonoid)
          (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real) (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
            (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin r) (Fin r) (Fin r) Real (Fin.fintype r)
              Real.instMul Real.instAddCommMonoid)
            (@Matrix.transpose.{0, 0, 0} (Fin r) (Fin r) Real T)
            (@HSub.hSub.{0, 0, 0} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real) (BfgsVerification.Mat r)
              (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
              (@instHSub.{0} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
                (@Matrix.sub.{0, 0, 0} (Fin r) (Fin r) Real Real.instSub))
              (@BfgsVerification.metricGram.{0} n (Fin r) (@BfgsVerification.AdmissibleBFGSRun.hessian n F R k) V)
              (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Mat r) (BfgsVerification.Mat r)
                (@instHSMul.{0, 0} Real (BfgsVerification.Mat r)
                  (@Matrix.smul.{0, 0, 0, 0} (Fin r) (Fin r) Real Real
                    (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                      (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                      (@Algebra.id.{0} Real Real.instCommSemiring))))
                (@Inv.inv.{0} Real Real.instInv (@BfgsVerification.AdmissibleBFGSRun.q n F R k))
                (@BfgsVerification.outer r
                  (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin r) Real V)
                    (@BfgsVerification.AdmissibleBFGSRun.g n F R k))
                  (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin r) Real V)
                    (@BfgsVerification.AdmissibleBFGSRun.g n F R k))))))
          T)
        (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Mat r) (BfgsVerification.Mat r)
          (@instHSMul.{0, 0} Real (BfgsVerification.Mat r)
            (@Matrix.smul.{0, 0, 0, 0} (Fin r) (Fin r) Real Real
              (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                (@Algebra.id.{0} Real Real.instCommSemiring))))
          (@Inv.inv.{0} Real Real.instInv (@BfgsVerification.AdmissibleBFGSRun.curvature n F R k))
          (@BfgsVerification.outer r
            (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
              (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                    (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                      (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
              (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin r) Real W)
              (@BfgsVerification.AdmissibleBFGSRun.gradientChange n F R k))
            (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
              (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                    (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                      (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
              (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin r) Real W)
              (@BfgsVerification.AdmissibleBFGSRun.gradientChange n F R k)))))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.PlanarAllPairs.sourceAllEndpointEstimates, ``EJob15.Contract01),
    (``BfgsVerification.planarQuadraticCoefficients, ``EJob15.Contract02),
    (``BfgsVerification.planarQuadraticBasin, ``EJob15.Contract03),
    (``BfgsVerification.spatialQuadraticRadial, ``EJob15.Contract04),
    (``BfgsVerification.spatialCanonicalWarning, ``EJob15.Contract05),
    (``BfgsVerification.PlanarTransport.angularFrame_hasDerivAt, ``EJob15.Contract06),
    (``BfgsVerification.PlanarTransport.triangular_determinant, ``EJob15.Contract07),
    (``BfgsVerification.AdmissibleBFGSRun.moving_frame_energy, ``EJob15.Contract08)]
  for (actual, contract) in pairs do
    let info ← getConstInfo actual
    unless info.isTheorem do throwError "not a theorem: {actual}"
    let some checked := (← getEnv).checked.get.find? actual
      | throwError "unchecked actual declaration: {actual}"
    unless info.type == checked.type do throwError "checked type mismatch: {actual}"
    let correct ← liftTermElabM do
      let proof ← Meta.mkConstWithFreshMVarLevels actual
      let expected ← Meta.mkConstWithFreshMVarLevels contract
      Meta.isDefEq (← Meta.inferType proof) expected
    unless correct do throwError "literal proposition mismatch: {actual} versus {contract}"
    let axioms ← Lean.collectAxioms actual
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "nonstandard axiom: {actual} uses {ax}"
    let signature ← liftTermElabM do pure (← Meta.ppExpr info.type).pretty
    logInfo m!"E19_CHECK {Json.compress <| Json.mkObj [
      ("theorem", toJson actual.toString), ("contract",toJson contract.toString),
      ("signature",toJson signature), ("axioms",toJson (axioms.map Name.toString)),
      ("strict_definitional_type_check",toJson true)]}"
  logInfo m!"E19_JOB_PASS {pairs.size}"
