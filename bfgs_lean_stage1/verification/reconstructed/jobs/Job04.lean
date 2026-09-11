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

def EJob04.Contract01 : Prop :=
∀ (μ : Real),
  ∃ (ls : Real) (lu : Real),
    And
      (And
        (@LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real 38
              (@instOfNatAtLeastTwo.{0} Real 38 Real.instNatCast
                (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 36 (instOfNatNat 36)))))
            (@OfNat.ofNat.{0} Real 1000
              (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
                (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 998 (instOfNatNat 998))))))
          ls)
        (@LT.lt.{0} Real Real.instLT ls
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real 39
              (@instOfNatAtLeastTwo.{0} Real 39 Real.instNatCast
                (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 37 (instOfNatNat 37)))))
            (@OfNat.ofNat.{0} Real 1000
              (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
                (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 998 (instOfNatNat 998))))))))
      (And
        (And
          (@LT.lt.{0} Real Real.instLT
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real 1564
                (@instOfNatAtLeastTwo.{0} Real 1564 Real.instNatCast
                  (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 1562 (instOfNatNat 1562)))))
              (@OfNat.ofNat.{0} Real 1000
                (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
                  (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 998 (instOfNatNat 998))))))
            lu)
          (@LT.lt.{0} Real Real.instLT lu
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real 1565
                (@instOfNatAtLeastTwo.{0} Real 1565 Real.instNatCast
                  (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 1563 (instOfNatNat 1563)))))
              (@OfNat.ofNat.{0} Real 1000
                (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
                  (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 998 (instOfNatNat 998))))))))
        (∃ (E :
          @ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
            (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
            BfgsVerification.LBlockSplitting.Coordinates
            (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
            (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
            BfgsVerification.LNormalizedReturn.State
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
            (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real Real.semiring
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
                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real Real.semiring
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
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))),
          And
            (∀ (w : BfgsVerification.LBlockSplitting.Coordinates),
              @Eq.{1} Real
                (@DFunLike.coe.{1, 1, 1}
                  (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                    (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                    BfgsVerification.LBlockSplitting.Coordinates
                    (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                    (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                    BfgsVerification.LNormalizedReturn.State
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                    (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                        Real.semiring Real.instAddCommMonoid
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
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                        Real.semiring Real.instAddCommMonoid
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                      Real.semiring Real.instAddCommMonoid
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
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                  BfgsVerification.LBlockSplitting.Coordinates
                  (fun (x : BfgsVerification.LBlockSplitting.Coordinates) => BfgsVerification.LNormalizedReturn.State)
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                      BfgsVerification.LBlockSplitting.Coordinates
                      (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                      (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                      (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                        Real.semiring Real.instAddCommMonoid
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                    BfgsVerification.LBlockSplitting.Coordinates BfgsVerification.LNormalizedReturn.State
                    (@ContinuousLinearEquiv.equivLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                      BfgsVerification.LBlockSplitting.Coordinates
                      (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                      (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                      (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                        Real.semiring Real.instAddCommMonoid
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))))
                  E w
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) 4
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) 4)))
                (@Prod.fst.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) w
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 1))))
            (And
              (∀ (w : BfgsVerification.LBlockSplitting.Coordinates),
                @Eq.{1} BfgsVerification.LNormalizedReturn.State
                  (@DFunLike.coe.{1, 1, 1}
                    (@ContinuousLinearMap.{0, 0, 0, 0} Real Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                      (@RingHom.id.{0} Real
                        (@Semiring.toNonAssocSemiring.{0} Real
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                      Real.denselyNormedField))))))))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                    BfgsVerification.LNormalizedReturn.State
                    (fun (x : BfgsVerification.LNormalizedReturn.State) => BfgsVerification.LNormalizedReturn.State)
                    (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                      (@RingHom.id.{0} Real
                        (@Semiring.toNonAssocSemiring.{0} Real
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                      Real.denselyNormedField))))))))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                    (@fderiv.{0, 0, 0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (BfgsVerification.LNormalizedReturn.returnMap μ) BfgsVerification.LNormalizedReturn.seed)
                    (@DFunLike.coe.{1, 1, 1}
                      (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                        BfgsVerification.LBlockSplitting.Coordinates
                        (@instTopologicalSpaceProd.{0, 0}
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                        (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                        BfgsVerification.LNormalizedReturn.State
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                        (@Prod.instModule.{0, 0, 0} Real
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                      BfgsVerification.LBlockSplitting.Coordinates
                      (fun (x : BfgsVerification.LBlockSplitting.Coordinates) =>
                        BfgsVerification.LNormalizedReturn.State)
                      (@EquivLike.toFunLike.{1, 1, 1}
                        (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                          BfgsVerification.LBlockSplitting.Coordinates
                          (@instTopologicalSpaceProd.{0, 0}
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                              @UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                              @UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                          (@Prod.instAddCommMonoid.{0, 0}
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                          BfgsVerification.LNormalizedReturn.State
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                          (@Prod.instModule.{0, 0, 0} Real
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                              Real.semiring Real.instAddCommMonoid
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
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                              Real.semiring Real.instAddCommMonoid
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
                                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                        BfgsVerification.LBlockSplitting.Coordinates BfgsVerification.LNormalizedReturn.State
                        (@ContinuousLinearEquiv.equivLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                          BfgsVerification.LBlockSplitting.Coordinates
                          (@instTopologicalSpaceProd.{0, 0}
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                              @UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                              @UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                          (@Prod.instAddCommMonoid.{0, 0}
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                          BfgsVerification.LNormalizedReturn.State
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                          (@Prod.instModule.{0, 0, 0} Real
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                              Real.semiring Real.instAddCommMonoid
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
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                              Real.semiring Real.instAddCommMonoid
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
                                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))))
                      E w))
                  (@DFunLike.coe.{1, 1, 1}
                    (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                      BfgsVerification.LBlockSplitting.Coordinates
                      (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                      (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                      (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                        Real.semiring Real.instAddCommMonoid
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                    BfgsVerification.LBlockSplitting.Coordinates
                    (fun (x : BfgsVerification.LBlockSplitting.Coordinates) => BfgsVerification.LNormalizedReturn.State)
                    (@EquivLike.toFunLike.{1, 1, 1}
                      (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                        BfgsVerification.LBlockSplitting.Coordinates
                        (@instTopologicalSpaceProd.{0, 0}
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                        (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                        BfgsVerification.LNormalizedReturn.State
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                        (@Prod.instModule.{0, 0, 0} Real
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                      BfgsVerification.LBlockSplitting.Coordinates BfgsVerification.LNormalizedReturn.State
                      (@ContinuousLinearEquiv.equivLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                        BfgsVerification.LBlockSplitting.Coordinates
                        (@instTopologicalSpaceProd.{0, 0}
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                        (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                        BfgsVerification.LNormalizedReturn.State
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                        (@Prod.instModule.{0, 0, 0} Real
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))))
                    E
                    (@Prod.mk.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                      (@DFunLike.coe.{1, 1, 1}
                        (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                          (@Pi.topologicalSpace.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            Real.instAddCommMonoid)
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                          (@Pi.topologicalSpace.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            Real Real Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                          (@Pi.Function.module.{0, 0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            Real Real Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                        (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                        (fun (x : BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                          BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                        (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                          (@Pi.topologicalSpace.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            Real.instAddCommMonoid)
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                          (@Pi.topologicalSpace.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            Real Real Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                          (@Pi.Function.module.{0, 0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            Real Real Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                        (@BfgsVerification.LBlockSplitting.diagonalMap
                          (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ
                          (@Matrix.vecCons.{0} Real (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) ls
                            (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
                              BfgsVerification.SeedOrbit.seedRatio (@Matrix.vecEmpty.{0} Real))))
                        (@Prod.fst.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) w))
                      (@DFunLike.coe.{1, 1, 1}
                        (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                          (@Pi.topologicalSpace.{0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            Real.instAddCommMonoid)
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                          (@Pi.topologicalSpace.{0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) Real Real Real.semiring
                            Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) Real Real Real.semiring
                            Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                        (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                        (fun
                            (x : BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                          BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                        (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                          (@Pi.topologicalSpace.{0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            Real.instAddCommMonoid)
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                          (@Pi.topologicalSpace.{0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) Real Real Real.semiring
                            Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) Real Real Real.semiring
                            Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                        (@BfgsVerification.LBlockSplitting.diagonalMap
                          (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ
                          (@Matrix.vecCons.{0} Real (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ
                            (@Inv.inv.{0} Real Real.instInv BfgsVerification.SeedOrbit.seedRatio)
                            (@Matrix.vecCons.{0} Real (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
                              (@Inv.inv.{0} Real Real.instInv BfgsVerification.SeedOrbit.seedRatio)
                              (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) lu
                                (@Matrix.vecEmpty.{0} Real)))))
                        (@Prod.snd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) w)))))
              (@Eq.{1}
                (@Polynomial.{0} Real
                  (@CommSemiring.toSemiring.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))
                (@LinearMap.charpoly.{0, 0} Real BfgsVerification.LNormalizedReturn.State Real.commRing
                  (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                  (@Module.Free.function.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                    (@CommSemiring.toSemiring.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))
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
                        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
                    (@Finite.of_fintype.{0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))))
                    (@Module.free_of_finite_type_torsion_free'.{0, 0} Real Real.commRing Real
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
                      Real.instIsDomain
                      (@instIsPrincipalIdealRingOfIsSemisimpleRing.{0} Real Real.instRing
                        (@IsSemisimpleRing.isSemisimpleModule.{0, 0} Real Real.instRing Real Real.instAddCommGroup
                          (@Semiring.toModule.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                          (@Submodule.complementedLattice.{0, 0} Real Real Real.instDivisionRing Real.instAddCommGroup
                            (@Semiring.toModule.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)))))
                      (@FiniteDimensional.rclike_to_real.{0} Real Real.instRCLike)
                      (@Module.instNoZeroSMulDivisorsOfIsDomain.{0, 0} Real Real Real.commRing
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
                        (@Module.instIsReflexiveOfFiniteOfProjective.{0, 0} Real Real Real.commRing
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
                          (@FiniteDimensional.rclike_to_real.{0} Real Real.instRCLike)
                          (@IsAzumaya.toProjective.{0, 0} Real Real Real.instCommSemiring Real.semiring
                            (@NormedAlgebra.toAlgebra.{0, 0} Real Real
                              (@DenselyNormedField.toNormedField.{0} Real
                                (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike))
                              (@SeminormedCommRing.toSeminormedRing.{0} Real
                                (@NormedCommRing.toSeminormedCommRing.{0} Real
                                  (@NormedField.toNormedCommRing.{0} Real
                                    (@DenselyNormedField.toNormedField.{0} Real
                                      (@RCLike.toDenselyNormedField.{0} Real Real.instRCLike)))))
                              (@RCLike.toNormedAlgebra.{0} Real Real.instRCLike))
                            (@IsAzumaya.id.{0} Real Real.instCommSemiring)))
                        Real.instIsDomain)))
                  (@FiniteDimensional.finiteDimensional_pi'.{0, 0, 0} Real Real.instDivisionRing
                    (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                    (@Finite.of_fintype.{0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                    (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                    (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                      @NormedSpace.toModule.{0, 0} Real Real Real.normedField
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
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                    @FiniteDimensional.rclike_to_real.{0} Real Real.instRCLike)
                  (@ContinuousLinearMap.toLinearMap.{0, 0, 0, 0} Real Real
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                    (@RingHom.id.{0} Real
                      (@Semiring.toNonAssocSemiring.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@NontriviallyNormedField.toNormedField.{0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                    Real.denselyNormedField))))))))
                    BfgsVerification.LNormalizedReturn.State
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                    BfgsVerification.LNormalizedReturn.State
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                    (@fderiv.{0, 0, 0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (BfgsVerification.LNormalizedReturn.returnMap μ) BfgsVerification.LNormalizedReturn.seed)))
                (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                  (@Polynomial.{0} Real
                    (@CommSemiring.toSemiring.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))
                  (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.mul'.{0} Real Real.semiring))
                  (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                    (@Polynomial.{0} Real Real.semiring)
                    (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.mul'.{0} Real Real.semiring))
                    (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                      (@Polynomial.{0} Real Real.semiring)
                      (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.mul'.{0} Real Real.semiring))
                      (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                        (@Polynomial.{0} Real Real.semiring)
                        (@instHPow.{0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                          (@Monoid.toNatPow.{0} (@Polynomial.{0} Real Real.semiring)
                            (@MonoidWithZero.toMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                              (@Semiring.toMonoidWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.semiring.{0} Real Real.semiring)))))
                        (@HSub.hSub.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.{0} Real Real.semiring)
                          (@instHSub.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.sub.{0} Real Real.instRing))
                          (@Polynomial.X.{0} Real Real.semiring)
                          (@DFunLike.coe.{1, 1, 1}
                            (@RingHom.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                              (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                              (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.semiring.{0} Real Real.semiring)))
                            Real (fun (x : Real) => @Polynomial.{0} Real Real.semiring)
                            (@RingHom.instFunLike.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                              (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                              (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.semiring.{0} Real Real.semiring)))
                            (@Polynomial.C.{0} Real Real.semiring)
                            (@Inv.inv.{0} Real Real.instInv BfgsVerification.SeedOrbit.seedRatio)))
                        (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@HSub.hSub.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                        (@Polynomial.{0} Real Real.semiring)
                        (@instHSub.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.sub.{0} Real Real.instRing))
                        (@Polynomial.X.{0} Real Real.semiring)
                        (@DFunLike.coe.{1, 1, 1}
                          (@RingHom.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                            (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                            (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.semiring.{0} Real Real.semiring)))
                          Real (fun (x : Real) => @Polynomial.{0} Real Real.semiring)
                          (@RingHom.instFunLike.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                            (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                            (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.semiring.{0} Real Real.semiring)))
                          (@Polynomial.C.{0} Real Real.semiring) ls)))
                    (@HSub.hSub.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                      (@Polynomial.{0} Real Real.semiring)
                      (@instHSub.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.sub.{0} Real Real.instRing))
                      (@Polynomial.X.{0} Real Real.semiring)
                      (@DFunLike.coe.{1, 1, 1}
                        (@RingHom.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                          (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                          (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.semiring.{0} Real Real.semiring)))
                        Real (fun (x : Real) => @Polynomial.{0} Real Real.semiring)
                        (@RingHom.instFunLike.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                          (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                          (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.semiring.{0} Real Real.semiring)))
                        (@Polynomial.C.{0} Real Real.semiring) lu)))
                  (@HSub.hSub.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                    (@Polynomial.{0} Real Real.semiring)
                    (@instHSub.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.sub.{0} Real Real.instRing))
                    (@Polynomial.X.{0} Real Real.semiring)
                    (@DFunLike.coe.{1, 1, 1}
                      (@RingHom.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.semiring.{0} Real Real.semiring)))
                      Real (fun (x : Real) => @Polynomial.{0} Real Real.semiring)
                      (@RingHom.instFunLike.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.semiring.{0} Real Real.semiring)))
                      (@Polynomial.C.{0} Real Real.semiring) BfgsVerification.SeedOrbit.seedRatio)))))))

def EJob04.Contract02 : Prop :=
∀ (μ : Real),
  ∃ (ls : Real) (lu : Real),
    And
      (And
        (@LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real 38
              (@instOfNatAtLeastTwo.{0} Real 38 Real.instNatCast
                BfgsVerification.LGlobalTargets.SpectrumTarget._proof_3))
            (@OfNat.ofNat.{0} Real 1000
              (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
                BfgsVerification.LGlobalTargets.SpectrumTarget._proof_4)))
          ls)
        (@LT.lt.{0} Real Real.instLT ls
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real 39
              (@instOfNatAtLeastTwo.{0} Real 39 Real.instNatCast
                BfgsVerification.LGlobalTargets.SpectrumTarget._proof_5))
            (@OfNat.ofNat.{0} Real 1000
              (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
                BfgsVerification.LGlobalTargets.SpectrumTarget._proof_4)))))
      (And
        (And
          (@LT.lt.{0} Real Real.instLT
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real 1564
                (@instOfNatAtLeastTwo.{0} Real 1564 Real.instNatCast
                  BfgsVerification.LGlobalTargets.SpectrumTarget._proof_6))
              (@OfNat.ofNat.{0} Real 1000
                (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
                  BfgsVerification.LGlobalTargets.SpectrumTarget._proof_4)))
            lu)
          (@LT.lt.{0} Real Real.instLT lu
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real 1565
                (@instOfNatAtLeastTwo.{0} Real 1565 Real.instNatCast
                  BfgsVerification.LGlobalTargets.SpectrumTarget._proof_7))
              (@OfNat.ofNat.{0} Real 1000
                (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
                  BfgsVerification.LGlobalTargets.SpectrumTarget._proof_4)))))
        (∃ (E :
          @ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
            (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
            BfgsVerification.LBlockSplitting.Coordinates
            (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
            (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
            BfgsVerification.LNormalizedReturn.State
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
            (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real Real.semiring
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
                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real Real.semiring
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
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))),
          And
            (∀ (w : BfgsVerification.LBlockSplitting.Coordinates),
              @Eq.{1} Real
                (@DFunLike.coe.{1, 1, 1}
                  (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                    (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                    BfgsVerification.LBlockSplitting.Coordinates
                    (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                    (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                    BfgsVerification.LNormalizedReturn.State
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                    (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                        Real.semiring Real.instAddCommMonoid
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
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                        Real.semiring Real.instAddCommMonoid
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                      Real.semiring Real.instAddCommMonoid
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
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                  BfgsVerification.LBlockSplitting.Coordinates
                  (fun (x : BfgsVerification.LBlockSplitting.Coordinates) => BfgsVerification.LNormalizedReturn.State)
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                      BfgsVerification.LBlockSplitting.Coordinates
                      (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                      (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                      (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                        Real.semiring Real.instAddCommMonoid
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                    BfgsVerification.LBlockSplitting.Coordinates BfgsVerification.LNormalizedReturn.State
                    (@ContinuousLinearEquiv.equivLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                      BfgsVerification.LBlockSplitting.Coordinates
                      (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                      (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                      (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                        Real.semiring Real.instAddCommMonoid
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))))
                  E w
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) 4
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))
                      BfgsVerification.LGlobalTargets.SpectrumTarget._proof_8 4)))
                (@Prod.fst.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) w
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.LGlobalTargets.SpectrumTarget._proof_9 1))))
            (And
              (∀ (w : BfgsVerification.LBlockSplitting.Coordinates),
                @Eq.{1} BfgsVerification.LNormalizedReturn.State
                  (@DFunLike.coe.{1, 1, 1}
                    (@ContinuousLinearMap.{0, 0, 0, 0} Real Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                      (@RingHom.id.{0} Real
                        (@Semiring.toNonAssocSemiring.{0} Real
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                      Real.denselyNormedField))))))))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                    BfgsVerification.LNormalizedReturn.State
                    (fun (x : BfgsVerification.LNormalizedReturn.State) => BfgsVerification.LNormalizedReturn.State)
                    (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                      (@RingHom.id.{0} Real
                        (@Semiring.toNonAssocSemiring.{0} Real
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                      Real.denselyNormedField))))))))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                    (@fderiv.{0, 0, 0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (BfgsVerification.LNormalizedReturn.returnMap μ) BfgsVerification.LNormalizedReturn.seed)
                    (@DFunLike.coe.{1, 1, 1}
                      (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                        BfgsVerification.LBlockSplitting.Coordinates
                        (@instTopologicalSpaceProd.{0, 0}
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                        (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                        BfgsVerification.LNormalizedReturn.State
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                        (@Prod.instModule.{0, 0, 0} Real
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                      BfgsVerification.LBlockSplitting.Coordinates
                      (fun (x : BfgsVerification.LBlockSplitting.Coordinates) =>
                        BfgsVerification.LNormalizedReturn.State)
                      (@EquivLike.toFunLike.{1, 1, 1}
                        (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                          BfgsVerification.LBlockSplitting.Coordinates
                          (@instTopologicalSpaceProd.{0, 0}
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                              @UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                              @UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                          (@Prod.instAddCommMonoid.{0, 0}
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                          BfgsVerification.LNormalizedReturn.State
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                          (@Prod.instModule.{0, 0, 0} Real
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                              Real.semiring Real.instAddCommMonoid
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
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                              Real.semiring Real.instAddCommMonoid
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
                                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                        BfgsVerification.LBlockSplitting.Coordinates BfgsVerification.LNormalizedReturn.State
                        (@ContinuousLinearEquiv.equivLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                          BfgsVerification.LBlockSplitting.Coordinates
                          (@instTopologicalSpaceProd.{0, 0}
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                              @UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                              @UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                          (@Prod.instAddCommMonoid.{0, 0}
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                          BfgsVerification.LNormalizedReturn.State
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                          (@Prod.instModule.{0, 0, 0} Real
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                              Real.semiring Real.instAddCommMonoid
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
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                              Real.semiring Real.instAddCommMonoid
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
                                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))))
                      E w))
                  (@DFunLike.coe.{1, 1, 1}
                    (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                      BfgsVerification.LBlockSplitting.Coordinates
                      (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                      (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                      (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                        Real.semiring Real.instAddCommMonoid
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                    BfgsVerification.LBlockSplitting.Coordinates
                    (fun (x : BfgsVerification.LBlockSplitting.Coordinates) => BfgsVerification.LNormalizedReturn.State)
                    (@EquivLike.toFunLike.{1, 1, 1}
                      (@ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                        BfgsVerification.LBlockSplitting.Coordinates
                        (@instTopologicalSpaceProd.{0, 0}
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                        (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                        BfgsVerification.LNormalizedReturn.State
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                        (@Prod.instModule.{0, 0, 0} Real
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                      BfgsVerification.LBlockSplitting.Coordinates BfgsVerification.LNormalizedReturn.State
                      (@ContinuousLinearEquiv.equivLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                        BfgsVerification.LBlockSplitting.Coordinates
                        (@instTopologicalSpaceProd.{0, 0}
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                        (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                        BfgsVerification.LNormalizedReturn.State
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                        (@Prod.instModule.{0, 0, 0} Real
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                            Real.semiring Real.instAddCommMonoid
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
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                          Real.semiring Real.instAddCommMonoid
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))))
                    E
                    (@Prod.mk.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                      (@DFunLike.coe.{1, 1, 1}
                        (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                          (@Pi.topologicalSpace.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            Real.instAddCommMonoid)
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                          (@Pi.topologicalSpace.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            Real Real Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                          (@Pi.Function.module.{0, 0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            Real Real Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                        (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                        (fun (x : BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                          BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                        (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                          (@Pi.topologicalSpace.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            Real.instAddCommMonoid)
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                          (@Pi.topologicalSpace.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ) =>
                            Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            Real Real Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                          (@Pi.Function.module.{0, 0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ)
                            Real Real Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                        (@BfgsVerification.LBlockSplitting.diagonalMap
                          (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ
                          (@Matrix.vecCons.{0} Real (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) ls
                            (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
                              BfgsVerification.SeedOrbit.seedRatio (@Matrix.vecEmpty.{0} Real))))
                        (@Prod.fst.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) w))
                      (@DFunLike.coe.{1, 1, 1}
                        (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                          (@Pi.topologicalSpace.{0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            Real.instAddCommMonoid)
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                          (@Pi.topologicalSpace.{0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) Real Real Real.semiring
                            Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) Real Real Real.semiring
                            Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                        (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                        (fun
                            (x : BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                          BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                        (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                          (@Pi.topologicalSpace.{0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            Real.instAddCommMonoid)
                          (BfgsVerification.Vec (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                          (@Pi.topologicalSpace.{0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.addCommMonoid.{0, 0} (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ)
                            (fun (a : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) => Real)
                            fun (i : Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) =>
                            Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) Real Real Real.semiring
                            Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ) Real Real Real.semiring
                            Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                        (@BfgsVerification.LBlockSplitting.diagonalMap
                          (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ.succ
                          (@Matrix.vecCons.{0} Real (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))).succ
                            (@Inv.inv.{0} Real Real.instInv BfgsVerification.SeedOrbit.seedRatio)
                            (@Matrix.vecCons.{0} Real (Nat.succ (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
                              (@Inv.inv.{0} Real Real.instInv BfgsVerification.SeedOrbit.seedRatio)
                              (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) lu
                                (@Matrix.vecEmpty.{0} Real)))))
                        (@Prod.snd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) w)))))
              (@Eq.{1}
                (@Polynomial.{0} Real
                  (@CommSemiring.toSemiring.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))
                (@LinearMap.charpoly.{0, 0} Real BfgsVerification.LNormalizedReturn.State Real.commRing
                  (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                  BfgsVerification.LGlobalTargets.SpectrumTarget._proof_10
                  BfgsVerification.LGlobalTargets.SpectrumTarget._proof_11
                  (@ContinuousLinearMap.toLinearMap.{0, 0, 0, 0} Real Real
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                    (@RingHom.id.{0} Real
                      (@Semiring.toNonAssocSemiring.{0} Real
                        (@DivisionSemiring.toSemiring.{0} Real
                          (@Semifield.toDivisionSemiring.{0} Real
                            (@Field.toSemifield.{0} Real
                              (@NormedField.toField.{0} Real
                                (@NontriviallyNormedField.toNormedField.{0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                    Real.denselyNormedField))))))))
                    BfgsVerification.LNormalizedReturn.State
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                    BfgsVerification.LNormalizedReturn.State
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@AddCommGroup.toAddCommMonoid.{0} BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup))
                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                    (@fderiv.{0, 0, 0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
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
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (BfgsVerification.LNormalizedReturn.returnMap μ) BfgsVerification.LNormalizedReturn.seed)))
                (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                  (@Polynomial.{0} Real
                    (@CommSemiring.toSemiring.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))
                  (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.mul'.{0} Real Real.semiring))
                  (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                    (@Polynomial.{0} Real Real.semiring)
                    (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.mul'.{0} Real Real.semiring))
                    (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                      (@Polynomial.{0} Real Real.semiring)
                      (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.mul'.{0} Real Real.semiring))
                      (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                        (@Polynomial.{0} Real Real.semiring)
                        (@instHPow.{0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                          (@Monoid.toNatPow.{0} (@Polynomial.{0} Real Real.semiring)
                            (@MonoidWithZero.toMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                              (@Semiring.toMonoidWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.semiring.{0} Real Real.semiring)))))
                        (@HSub.hSub.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.{0} Real Real.semiring)
                          (@instHSub.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.sub.{0} Real Real.instRing))
                          (@Polynomial.X.{0} Real Real.semiring)
                          (@DFunLike.coe.{1, 1, 1}
                            (@RingHom.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                              (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                              (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.semiring.{0} Real Real.semiring)))
                            Real (fun (x : Real) => @Polynomial.{0} Real Real.semiring)
                            (@RingHom.instFunLike.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                              (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                              (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.semiring.{0} Real Real.semiring)))
                            (@Polynomial.C.{0} Real Real.semiring)
                            (@Inv.inv.{0} Real Real.instInv BfgsVerification.SeedOrbit.seedRatio)))
                        (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@HSub.hSub.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                        (@Polynomial.{0} Real Real.semiring)
                        (@instHSub.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.sub.{0} Real Real.instRing))
                        (@Polynomial.X.{0} Real Real.semiring)
                        (@DFunLike.coe.{1, 1, 1}
                          (@RingHom.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                            (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                            (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.semiring.{0} Real Real.semiring)))
                          Real (fun (x : Real) => @Polynomial.{0} Real Real.semiring)
                          (@RingHom.instFunLike.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                            (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                            (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.semiring.{0} Real Real.semiring)))
                          (@Polynomial.C.{0} Real Real.semiring) ls)))
                    (@HSub.hSub.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                      (@Polynomial.{0} Real Real.semiring)
                      (@instHSub.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.sub.{0} Real Real.instRing))
                      (@Polynomial.X.{0} Real Real.semiring)
                      (@DFunLike.coe.{1, 1, 1}
                        (@RingHom.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                          (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                          (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.semiring.{0} Real Real.semiring)))
                        Real (fun (x : Real) => @Polynomial.{0} Real Real.semiring)
                        (@RingHom.instFunLike.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                          (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                          (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                            (@Polynomial.semiring.{0} Real Real.semiring)))
                        (@Polynomial.C.{0} Real Real.semiring) lu)))
                  (@HSub.hSub.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                    (@Polynomial.{0} Real Real.semiring)
                    (@instHSub.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.sub.{0} Real Real.instRing))
                    (@Polynomial.X.{0} Real Real.semiring)
                    (@DFunLike.coe.{1, 1, 1}
                      (@RingHom.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.semiring.{0} Real Real.semiring)))
                      Real (fun (x : Real) => @Polynomial.{0} Real Real.semiring)
                      (@RingHom.instFunLike.{0, 0} Real (@Polynomial.{0} Real Real.semiring)
                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)
                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.semiring.{0} Real Real.semiring)))
                      (@Polynomial.C.{0} Real Real.semiring) BfgsVerification.SeedOrbit.seedRatio)))))))

def EJob04.Contract03 : Prop :=
∀ (μ : Real) (W : Set.{0} BfgsVerification.LNormalizedReturn.State),
  @Membership.mem.{0, 0} (Set.{0} BfgsVerification.LNormalizedReturn.State)
      (Filter.{0} BfgsVerification.LNormalizedReturn.State)
      (@Filter.instMembership.{0} BfgsVerification.LNormalizedReturn.State)
      (@nhds.{0} BfgsVerification.LNormalizedReturn.State
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        BfgsVerification.LNormalizedReturn.seed)
      W →
    ∃ (E :
      @ContinuousLinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
        (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
        BfgsVerification.LBlockSplitting.Coordinates
        (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
        (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
        BfgsVerification.LNormalizedReturn.State
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
        (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real Real.semiring
            Real.instAddCommMonoid
            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real Real.semiring
            Real.instAddCommMonoid
            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real Real.semiring
          Real.instAddCommMonoid
          (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
            (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
              (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
      (h :
      BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) →
        BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
      (V : Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))),
      And
        (@IsOpen.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          V)
        (And
          (@Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
            (@Set.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) V
            (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
              (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))
          (And
            (@Eq.{1} BfgsVerification.LNormalizedReturn.State
              (@BfgsVerification.AnalyticStableGraph.chart.{0, 0, 0}
                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                BfgsVerification.LNormalizedReturn.State
                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.normedAddCommGroup)
                (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
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
                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                  (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.normedAddCommGroup)
                (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
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
                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                  (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.normedAddCommGroup)
                (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                  (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                  (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                    @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                  @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                BfgsVerification.LNormalizedReturn.seed E h
                (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                  (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))
              BfgsVerification.LNormalizedReturn.seed)
            (And
              (@ContDiffOn.{0, 0, 0} Real
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
                BfgsVerification.LNormalizedReturn.State
                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                  (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.normedAddCommGroup)
                (@Pi.normedSpace.{0, 0, 0} Real
                  (@NontriviallyNormedField.toNormedField.{0} Real
                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))
                  (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                  (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                  (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                    @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                  @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                (@WithTop.some.{0} ENat (@Top.top.{0} ENat instENatTop))
                (@BfgsVerification.AnalyticStableGraph.chart.{0, 0, 0}
                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                  BfgsVerification.LNormalizedReturn.State
                  (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                    (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.normedAddCommGroup)
                  (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
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
                  (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                    (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.normedAddCommGroup)
                  (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
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
                  (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                    (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.normedAddCommGroup)
                  (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                    (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                    (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                      @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                    @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                  BfgsVerification.LNormalizedReturn.seed E h)
                V)
              (And
                (@Topology.IsEmbedding.{0, 0}
                  (@Set.Elem.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) V)
                  BfgsVerification.LNormalizedReturn.State
                  (@instTopologicalSpaceSubtype.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                      @Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                        (@Set.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) V x)
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  fun (a : @Set.Elem.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) V) =>
                  @BfgsVerification.AnalyticStableGraph.chart.{0, 0, 0}
                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                    BfgsVerification.LNormalizedReturn.State
                    (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.normedAddCommGroup)
                    (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
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
                    (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                      (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.normedAddCommGroup)
                    (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
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
                    (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.normedAddCommGroup)
                    (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                              (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                      @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                              (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    BfgsVerification.LNormalizedReturn.seed E h
                    (@Subtype.val.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                          (@Set.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) V
                          x)
                      a))
                (And
                  (@HasFDerivAt.{0, 0, 0} Real
                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                      Real.semiring Real.instAddCommMonoid
                      (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                        (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                        (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                          (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    BfgsVerification.LNormalizedReturn.State
                    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommGroup)
                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                      Real.semiring Real.instAddCommMonoid
                      (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                        (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                        (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                          (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@BfgsVerification.AnalyticStableGraph.chart.{0, 0, 0}
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.normedAddCommGroup)
                      (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
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
                      (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                        (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.normedAddCommGroup)
                      (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
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
                      (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.normedAddCommGroup)
                      (@Pi.normedSpace.{0, 0, 0} Real Real.normedField (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                          @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                      BfgsVerification.LNormalizedReturn.seed E h)
                    (@ContinuousLinearMap.comp.{0, 0, 0, 0, 0, 0} Real Real Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                      Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (@RingHom.id.{0} Real
                        (@Semiring.toNonAssocSemiring.{0} Real
                          (@DivisionSemiring.toSemiring.{0} Real
                            (@Semifield.toDivisionSemiring.{0} Real
                              (@Field.toSemifield.{0} Real
                                (@NormedField.toField.{0} Real
                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                      Real.denselyNormedField))))))))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@AddCommGroup.toAddCommMonoid.{0}
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup))
                      BfgsVerification.LBlockSplitting.Coordinates
                      (@instTopologicalSpaceProd.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                      (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                      BfgsVerification.LNormalizedReturn.State
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                        Real.semiring Real.instAddCommMonoid
                        (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                          (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                          (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                            (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                      (@Prod.instModule.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                          Real.semiring Real.instAddCommMonoid
                          (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                            (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                            (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                              (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                          Real.semiring Real.instAddCommMonoid
                          (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                            (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                            (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                              (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                        Real.semiring Real.instAddCommMonoid
                        (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                          (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                          (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                            (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                      BfgsVerification.LReturnStableGraph.LStableManifoldTarget._proof_1
                      (@ContinuousLinearEquiv.toContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring)
                        BfgsVerification.LBlockSplitting.Coordinates
                        (@instTopologicalSpaceProd.{0, 0}
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                        (@Prod.instAddCommMonoid.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                        BfgsVerification.LNormalizedReturn.State
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                        (@Prod.instModule.{0, 0, 0} Real
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                            Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                            Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                          Real.semiring Real.instAddCommMonoid
                          (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                            (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                            (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                              (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                        E)
                      (@ContinuousLinearMap.inl.{0, 0, 0} Real Real.semiring
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                          Real.semiring Real.instAddCommMonoid
                          (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                            (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                            (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                              (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real Real
                          Real.semiring Real.instAddCommMonoid
                          (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                            (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                            (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                              (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))))
                    (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                      (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))
                  (And
                    (@Eq.{1} Nat
                      (@Module.finrank.{0, 0} Real
                        (↥(@LinearMap.range.{0, 0, 0, 0, 0} Real Real
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            BfgsVerification.LNormalizedReturn.State Real.semiring Real.semiring
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                              Real.semiring Real.instAddCommMonoid
                              (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                  (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                              Real.semiring Real.instAddCommMonoid
                              (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                  (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                            (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              BfgsVerification.LNormalizedReturn.State
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                            (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              BfgsVerification.LNormalizedReturn.State Real.semiring Real.semiring
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                            BfgsVerification.LReturnStableGraph.LStableManifoldTarget._proof_2
                            (@RingHomSurjective.ids.{0} Real Real.semiring)
                            (@ContinuousLinearMap.toLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                @UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              BfgsVerification.LNormalizedReturn.State
                              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                @UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@ContinuousLinearMap.comp.{0, 0, 0, 0, 0, 0} Real Real Real Real.semiring Real.semiring
                                Real.semiring
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                  @UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                BfgsVerification.LBlockSplitting.Coordinates
                                (@instTopologicalSpaceProd.{0, 0}
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                                (@Prod.instAddCommMonoid.{0, 0}
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                                BfgsVerification.LNormalizedReturn.State
                                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                  @UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                  Real.semiring Real.instAddCommMonoid
                                  (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                    (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                    (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                      (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                (@Prod.instModule.{0, 0, 0} Real
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                  Real.semiring Real.instAddCommMonoid
                                  (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                    (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                    (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                      (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                BfgsVerification.LReturnStableGraph.LStableManifoldTarget._proof_3
                                (@ContinuousLinearEquiv.toContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring
                                  Real.semiring
                                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                  (@RingHomInvPair.ids.{0} Real Real.semiring)
                                  (@RingHomInvPair.ids.{0} Real Real.semiring)
                                  BfgsVerification.LBlockSplitting.Coordinates
                                  (@instTopologicalSpaceProd.{0, 0}
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                      @UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                      @UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                                  (@Prod.instAddCommMonoid.{0, 0}
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                      Real.instAddCommMonoid))
                                  BfgsVerification.LNormalizedReturn.State
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                                  (@Prod.instModule.{0, 0, 0} Real
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                      Real Real.semiring Real.instAddCommMonoid
                                      (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                        (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                        (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                          (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                      Real Real.semiring Real.instAddCommMonoid
                                      (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                        (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                        (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                          (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  E)
                                (@ContinuousLinearMap.inl.{0, 0, 0} Real Real.semiring
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))))))
                        Real.semiring
                        (@Submodule.addCommMonoid.{0, 0} Real BfgsVerification.LNormalizedReturn.State Real.semiring
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                            Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                          (@LinearMap.range.{0, 0, 0, 0, 0} Real Real
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            BfgsVerification.LNormalizedReturn.State Real.semiring Real.semiring
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                              Real.semiring Real.instAddCommMonoid
                              (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                  (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                              Real.semiring Real.instAddCommMonoid
                              (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                  (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                            (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              BfgsVerification.LNormalizedReturn.State
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                            (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              BfgsVerification.LNormalizedReturn.State Real.semiring Real.semiring
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                            BfgsVerification.LReturnStableGraph.LStableManifoldTarget._proof_2
                            (@RingHomSurjective.ids.{0} Real Real.semiring)
                            (@ContinuousLinearMap.toLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                @UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              BfgsVerification.LNormalizedReturn.State
                              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                @UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@ContinuousLinearMap.comp.{0, 0, 0, 0, 0, 0} Real Real Real Real.semiring Real.semiring
                                Real.semiring
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                  @UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                BfgsVerification.LBlockSplitting.Coordinates
                                (@instTopologicalSpaceProd.{0, 0}
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                                (@Prod.instAddCommMonoid.{0, 0}
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                                BfgsVerification.LNormalizedReturn.State
                                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                  @UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                  Real.semiring Real.instAddCommMonoid
                                  (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                    (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                    (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                      (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                (@Prod.instModule.{0, 0, 0} Real
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                  Real.semiring Real.instAddCommMonoid
                                  (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                    (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                    (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                      (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                BfgsVerification.LReturnStableGraph.LStableManifoldTarget._proof_3
                                (@ContinuousLinearEquiv.toContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring
                                  Real.semiring
                                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                  (@RingHomInvPair.ids.{0} Real Real.semiring)
                                  (@RingHomInvPair.ids.{0} Real Real.semiring)
                                  BfgsVerification.LBlockSplitting.Coordinates
                                  (@instTopologicalSpaceProd.{0, 0}
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                      @UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                      @UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                                  (@Prod.instAddCommMonoid.{0, 0}
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                      Real.instAddCommMonoid))
                                  BfgsVerification.LNormalizedReturn.State
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                                  (@Prod.instModule.{0, 0, 0} Real
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                      Real Real.semiring Real.instAddCommMonoid
                                      (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                        (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                        (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                          (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                      Real Real.semiring Real.instAddCommMonoid
                                      (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                        (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                        (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                          (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  E)
                                (@ContinuousLinearMap.inl.{0, 0, 0} Real Real.semiring
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))))))
                        (@Submodule.module.{0, 0} Real BfgsVerification.LNormalizedReturn.State Real.semiring
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                            Real.semiring Real.instAddCommMonoid
                            (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                              (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                              (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                          (@LinearMap.range.{0, 0, 0, 0, 0} Real Real
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            BfgsVerification.LNormalizedReturn.State Real.semiring Real.semiring
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                              Real.semiring Real.instAddCommMonoid
                              (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                  (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                              Real.semiring Real.instAddCommMonoid
                              (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                  (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                            (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              BfgsVerification.LNormalizedReturn.State
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                            (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              BfgsVerification.LNormalizedReturn.State Real.semiring Real.semiring
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                            BfgsVerification.LReturnStableGraph.LStableManifoldTarget._proof_2
                            (@RingHomSurjective.ids.{0} Real Real.semiring)
                            (@ContinuousLinearMap.toLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                @UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              BfgsVerification.LNormalizedReturn.State
                              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                @UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@ContinuousLinearMap.comp.{0, 0, 0, 0, 0, 0} Real Real Real Real.semiring Real.semiring
                                Real.semiring
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                  @UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                BfgsVerification.LBlockSplitting.Coordinates
                                (@instTopologicalSpaceProd.{0, 0}
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                                (@Prod.instAddCommMonoid.{0, 0}
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                                BfgsVerification.LNormalizedReturn.State
                                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                  @UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                  Real.semiring Real.instAddCommMonoid
                                  (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                    (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                    (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                      (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                (@Prod.instModule.{0, 0, 0} Real
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                  Real.semiring Real.instAddCommMonoid
                                  (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                    (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                    (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                      (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                BfgsVerification.LReturnStableGraph.LStableManifoldTarget._proof_3
                                (@ContinuousLinearEquiv.toContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring
                                  Real.semiring
                                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                  (@RingHomInvPair.ids.{0} Real Real.semiring)
                                  (@RingHomInvPair.ids.{0} Real Real.semiring)
                                  BfgsVerification.LBlockSplitting.Coordinates
                                  (@instTopologicalSpaceProd.{0, 0}
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                      @UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                      @UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                                  (@Prod.instAddCommMonoid.{0, 0}
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                      Real.instAddCommMonoid))
                                  BfgsVerification.LNormalizedReturn.State
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                                  (@Prod.instModule.{0, 0, 0} Real
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                      Real Real.semiring Real.instAddCommMonoid
                                      (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                        (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                        (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                          (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                      Real Real.semiring Real.instAddCommMonoid
                                      (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                        (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                        (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                          (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  E)
                                (@ContinuousLinearMap.inl.{0, 0, 0} Real Real.semiring
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real
                                          (@CommRing.toCommSemiring.{0} Real Real.commRing)))))))))))
                      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (And
                      (@Eq.{1} (Set.{0} BfgsVerification.LNormalizedReturn.State)
                        (@SetLike.coe.{0, 0}
                          (@Submodule.{0, 0} Real BfgsVerification.LNormalizedReturn.State Real.semiring
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                              Real.semiring Real.instAddCommMonoid
                              (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                  (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                          BfgsVerification.LNormalizedReturn.State
                          (@Submodule.setLike.{0, 0} Real BfgsVerification.LNormalizedReturn.State Real.semiring
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                              Real.semiring Real.instAddCommMonoid
                              (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                  (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                          (@LinearMap.range.{0, 0, 0, 0, 0} Real Real
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            BfgsVerification.LNormalizedReturn.State Real.semiring Real.semiring
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                              Real.semiring Real.instAddCommMonoid
                              (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                  (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                              Real.semiring Real.instAddCommMonoid
                              (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                  (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                            (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              BfgsVerification.LNormalizedReturn.State
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                            (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              BfgsVerification.LNormalizedReturn.State Real.semiring Real.semiring
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                            BfgsVerification.LReturnStableGraph.LStableManifoldTarget._proof_2
                            (@RingHomSurjective.ids.{0} Real Real.semiring)
                            (@ContinuousLinearMap.toLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                @UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                              BfgsVerification.LNormalizedReturn.State
                              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                @UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                Real.semiring Real.instAddCommMonoid
                                (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                  (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                  (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                    (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                              (@ContinuousLinearMap.comp.{0, 0, 0, 0, 0, 0} Real Real Real Real.semiring Real.semiring
                                Real.semiring
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                  @UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                BfgsVerification.LBlockSplitting.Coordinates
                                (@instTopologicalSpaceProd.{0, 0}
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                                (@Prod.instAddCommMonoid.{0, 0}
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid))
                                BfgsVerification.LNormalizedReturn.State
                                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                  @UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                  Real.semiring Real.instAddCommMonoid
                                  (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                    (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                    (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                      (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                (@Prod.instModule.{0, 0, 0} Real
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real Real
                                  Real.semiring Real.instAddCommMonoid
                                  (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                    (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                    (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                      (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                BfgsVerification.LReturnStableGraph.LStableManifoldTarget._proof_3
                                (@ContinuousLinearEquiv.toContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring
                                  Real.semiring
                                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                  (@RingHomInvPair.ids.{0} Real Real.semiring)
                                  (@RingHomInvPair.ids.{0} Real Real.semiring)
                                  BfgsVerification.LBlockSplitting.Coordinates
                                  (@instTopologicalSpaceProd.{0, 0}
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                      @UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                      @UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
                                  (@Prod.instAddCommMonoid.{0, 0}
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                      Real.instAddCommMonoid))
                                  BfgsVerification.LNormalizedReturn.State
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.instAddCommMonoid)
                                  (@Prod.instModule.{0, 0, 0} Real
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real.semiring
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                      Real Real.semiring Real.instAddCommMonoid
                                      (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                        (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                        (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                          (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                      Real Real.semiring Real.instAddCommMonoid
                                      (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                        (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                        (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                          (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  E)
                                (@ContinuousLinearMap.inl.{0, 0, 0} Real Real.semiring
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing)))))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real.instAddCommMonoid)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) Real
                                    Real Real.semiring Real.instAddCommMonoid
                                    (@LieAlgebra.toModule.{0, 0} Real Real Real.commRing
                                      (@LieRing.ofAssociativeRing.{0} Real Real.instRing)
                                      (@LieAlgebra.ofAssociativeAlgebra.{0, 0} Real Real.instRing Real Real.commRing
                                        (@Algebra.id.{0} Real (@CommRing.toCommSemiring.{0} Real Real.commRing))))))))))
                        (@BfgsVerification.AnalyticStableGraph.linearStableSet.{0}
                          BfgsVerification.LNormalizedReturn.State
                          (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.normedAddCommGroup)
                          (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
                            (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                            (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                              @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                            @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                          (@fderiv.{0, 0, 0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                            BfgsVerification.LNormalizedReturn.State
                            (@SeminormedAddCommGroup.toAddCommGroup.{0} BfgsVerification.LNormalizedReturn.State
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} BfgsVerification.LNormalizedReturn.State
                                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.normedAddCommGroup)))
                            (@NormedSpace.toModule.{0, 0} Real BfgsVerification.LNormalizedReturn.State Real.normedField
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} BfgsVerification.LNormalizedReturn.State
                                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.normedAddCommGroup))
                              (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
                                (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                  @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                        (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                        (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
                            (@UniformSpace.toTopologicalSpace.{0} BfgsVerification.LNormalizedReturn.State
                              (@PseudoMetricSpace.toUniformSpace.{0} BfgsVerification.LNormalizedReturn.State
                                (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                                  BfgsVerification.LNormalizedReturn.State
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                                    BfgsVerification.LNormalizedReturn.State
                                    (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                      (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                      Real.normedAddCommGroup)))))
                            BfgsVerification.LNormalizedReturn.State
                            (@SeminormedAddCommGroup.toAddCommGroup.{0} BfgsVerification.LNormalizedReturn.State
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} BfgsVerification.LNormalizedReturn.State
                                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.normedAddCommGroup)))
                            (@NormedSpace.toModule.{0, 0} Real BfgsVerification.LNormalizedReturn.State Real.normedField
                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} BfgsVerification.LNormalizedReturn.State
                                (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                  (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real.normedAddCommGroup))
                              (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
                                (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                  @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                        (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                        (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
                            (@UniformSpace.toTopologicalSpace.{0} BfgsVerification.LNormalizedReturn.State
                              (@PseudoMetricSpace.toUniformSpace.{0} BfgsVerification.LNormalizedReturn.State
                                (@SeminormedAddCommGroup.toPseudoMetricSpace.{0}
                                  BfgsVerification.LNormalizedReturn.State
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0}
                                    BfgsVerification.LNormalizedReturn.State
                                    (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                      (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                      Real.normedAddCommGroup)))))
                            (BfgsVerification.LNormalizedReturn.returnMap μ) BfgsVerification.LNormalizedReturn.seed)))
                      (And
                        (∀ (eps : Real),
                          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                              eps →
                            ∃ (a : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                              And
                                (@Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                  (@Set.instMembership.{0}
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                  V a)
                                (And
                                  (@LT.lt.{0} Real Real.instLT
                                    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                                    (BfgsVerification.LNormalizedReturn.scale
                                      (@BfgsVerification.AnalyticStableGraph.chart.{0, 0, 0}
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                        BfgsVerification.LNormalizedReturn.State
                                        (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                          (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                          Real.normedAddCommGroup)
                                        (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
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
                                        (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                          (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                          Real.normedAddCommGroup)
                                        (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
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
                                        (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                          (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                          Real.normedAddCommGroup)
                                        (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
                                          (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                          (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                          (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                            @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                  (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                          @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                  (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                                        BfgsVerification.LNormalizedReturn.seed E h a)))
                                  (@LT.lt.{0} Real Real.instLT
                                    (BfgsVerification.LNormalizedReturn.scale
                                      (@BfgsVerification.AnalyticStableGraph.chart.{0, 0, 0}
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                        BfgsVerification.LNormalizedReturn.State
                                        (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                          (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                          Real.normedAddCommGroup)
                                        (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
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
                                        (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                          (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                          fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                          Real.normedAddCommGroup)
                                        (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
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
                                        (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                          (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                          Real.normedAddCommGroup)
                                        (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
                                          (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                          (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                          (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                            @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                  (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                          @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                  (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                                        BfgsVerification.LNormalizedReturn.seed E h a))
                                    eps)))
                        (∀ (a : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                          @Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                              (@Set.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                              V a →
                            ∃ (w : Nat → BfgsVerification.LNormalizedReturn.State),
                              And
                                (@Eq.{1} BfgsVerification.LNormalizedReturn.State
                                  (w (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
                                  (@BfgsVerification.AnalyticStableGraph.chart.{0, 0, 0}
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                    BfgsVerification.LNormalizedReturn.State
                                    (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                      Real.normedAddCommGroup)
                                    (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
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
                                    (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) => Real)
                                      (Fin.fintype (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) =>
                                      Real.normedAddCommGroup)
                                    (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
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
                                    (@Pi.normedAddCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                      (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                      Real.normedAddCommGroup)
                                    (@Pi.normedSpace.{0, 0, 0} Real Real.normedField
                                      (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                      (Fin.fintype (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                      (fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                        @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                              (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                      @InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                              (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                                        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                                    BfgsVerification.LNormalizedReturn.seed E h a))
                                (And
                                  (∀ (n : Nat),
                                    @Membership.mem.{0, 0} BfgsVerification.LNormalizedReturn.State
                                      (Set.{0} BfgsVerification.LNormalizedReturn.State)
                                      (@Set.instMembership.{0} BfgsVerification.LNormalizedReturn.State) W (w n))
                                  (And
                                    (@Filter.Tendsto.{0, 0} Nat BfgsVerification.LNormalizedReturn.State w
                                      (@Filter.atTop.{0} Nat Nat.instPreorder)
                                      (@nhds.{0} BfgsVerification.LNormalizedReturn.State
                                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) => Real)
                                          fun (i : Fin (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) =>
                                          @UniformSpace.toTopologicalSpace.{0} Real
                                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                        BfgsVerification.LNormalizedReturn.seed))
                                    (∀ (n : Nat),
                                      @Eq.{1} BfgsVerification.LNormalizedReturn.State
                                        (w
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                            (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
                                        (BfgsVerification.LNormalizedReturn.returnMap μ (w n))))))))))))))

def EJob04.Contract04 : Prop :=
And
  (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
    @Filter.Eventually.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (fun (z : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
          @DifferentiableAt.{0, 0, 0} Real
            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
            Real Real.instAddCommGroup
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
            BfgsVerification.LEmbedding.objective z)
        (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          x) →
      @DifferentiableAt.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
          (@ContinuousLinearMap.{0, 0, 0, 0} Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@AddCommGroup.toAddCommMonoid.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup))
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
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
          (@ContinuousLinearMap.addCommGroup.{0, 0, 0, 0} Real Real.instRing Real Real.instRing
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@SeminormedAddCommGroup.toAddCommGroup.{0} Real
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))
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
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            instIsTopologicalAddGroupReal)
          (@ContinuousLinearMap.module.{0, 0, 0, 0, 0} Real Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@AddCommGroup.toAddCommMonoid.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup))
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
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
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
            BfgsVerification.LEmbedding.HessianTarget._proof_12 BfgsVerification.LEmbedding.HessianTarget._proof_13
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            BfgsVerification.LEmbedding.HessianTarget._proof_14)
          (@ContinuousLinearMap.topologicalSpace.{0, 0, 0, 0} Real Real Real.normedField Real.normedField
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
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
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            instIsTopologicalAddGroupReal)
          (@fderiv.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
            Real Real.instAddCommGroup
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
            BfgsVerification.LEmbedding.objective)
          x →
        And
          (@Matrix.IsSymm.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@BfgsVerification.RadialHessian.matrix (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              BfgsVerification.LEmbedding.objective x))
          (∀ (v : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
            And
              (@LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) BfgsVerification.LEmbedding.mu
                  (@BfgsVerification.sqNorm (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) v))
                (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) v
                  (@Matrix.mulVec.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@BfgsVerification.RadialHessian.matrix (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.LEmbedding.objective x)
                    v)))
              (@LE.le.{0} Real Real.instLE
                (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) v
                  (@Matrix.mulVec.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@BfgsVerification.RadialHessian.matrix (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.LEmbedding.objective x)
                    v))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real 512
                    (@instOfNatAtLeastTwo.{0} Real 512 Real.instNatCast
                      BfgsVerification.LEmbedding.RegularityTarget._proof_5))
                  (@BfgsVerification.sqNorm (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) v)))))
  (And
    (∀ (x g : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
      @HasFDerivAt.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real Real.semiring
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
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
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
          BfgsVerification.LEmbedding.objective
          (@BfgsVerification.gradientFunctional (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) g) x →
        @Filter.Eventually.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (fun (z : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
            @LE.le.{0} Real Real.instLE (BfgsVerification.LEmbedding.objective z)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (BfgsVerification.LEmbedding.objective x)
                  (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) g
                    (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@instHSub.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.instSub.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instSub))
                      z x)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real 256
                    (@instOfNatAtLeastTwo.{0} Real 256 Real.instNatCast
                      BfgsVerification.LEmbedding.HessianTarget._proof_15))
                  (@BfgsVerification.sqNorm (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@instHSub.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.instSub.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instSub))
                      z x)))))
          (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            x))
    (∀ (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
      (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
      @DifferentiableAt.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
          (@ContinuousLinearMap.{0, 0, 0, 0} Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@AddCommGroup.toAddCommMonoid.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup))
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
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
          (@ContinuousLinearMap.addCommGroup.{0, 0, 0, 0} Real Real.instRing Real Real.instRing
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@SeminormedAddCommGroup.toAddCommGroup.{0} Real
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))
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
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            instIsTopologicalAddGroupReal)
          (@ContinuousLinearMap.module.{0, 0, 0, 0, 0} Real Real Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@AddCommGroup.toAddCommMonoid.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup))
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
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
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
            BfgsVerification.LEmbedding.HessianTarget._proof_12 BfgsVerification.LEmbedding.HessianTarget._proof_13
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            BfgsVerification.LEmbedding.HessianTarget._proof_14)
          (@ContinuousLinearMap.topologicalSpace.{0, 0, 0, 0} Real Real Real.normedField Real.normedField
            (@RingHom.id.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
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
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            instIsTopologicalAddGroupReal)
          (@fderiv.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
            Real Real.instAddCommGroup
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
            (BfgsVerification.LEmbedding.branch (@Fin.castSucc (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) i)))
          x →
        And
          (@Matrix.IsSymm.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@BfgsVerification.RadialHessian.matrix (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              (BfgsVerification.LEmbedding.branch (@Fin.castSucc (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) i)) x))
          (∀ (v : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
            And
              (@LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) BfgsVerification.LEmbedding.mu
                  (@BfgsVerification.sqNorm (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) v))
                (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) v
                  (@Matrix.mulVec.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@BfgsVerification.RadialHessian.matrix (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      (BfgsVerification.LEmbedding.branch (@Fin.castSucc (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) i))
                      x)
                    v)))
              (@LE.le.{0} Real Real.instLE
                (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) v
                  (@Matrix.mulVec.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@BfgsVerification.RadialHessian.matrix (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      (BfgsVerification.LEmbedding.branch (@Fin.castSucc (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) i))
                      x)
                    v))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (BfgsVerification.LEmbedding.gradientBound i)
                  (@BfgsVerification.sqNorm (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) v))))))

def EJob04.Contract05 : Prop :=
And
  (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
    @LE.le.{0} Real Real.instLE
        (@Norm.norm.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@NormedRing.toNorm.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.normedRing.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
              @NormedCommRing.toNormedRing.{0} Real Real.normedCommRing))
          (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@instHSub.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Pi.instSub.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instSub))
            x BfgsVerification.AlgebraicSeed.center))
        BfgsVerification.AlgebraicSeed.radius →
      ∀ (i j : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (BfgsVerification.LShapeDerivative.jacobian
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget._proof_11 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget._proof_11 1)))
                i j)
              (BfgsVerification.LShapePrecision.display20 i j)))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real 2
                (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                  BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget._proof_12))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@OfNat.ofNat.{0} Real 10
                  (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast
                    BfgsVerification.LShapePrecision.display20._proof_2))
                (@OfNat.ofNat.{0} Nat 20 (instOfNatNat 20))))))
  (And
    (∀ (i j : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (BfgsVerification.LShapePrecision.actualEntry i j) (BfgsVerification.LShapePrecision.display20 i j)))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real 2
              (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget._proof_12))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@OfNat.ofNat.{0} Real 10
                (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast BfgsVerification.LShapePrecision.display20._proof_2))
              (@OfNat.ofNat.{0} Nat 20 (instOfNatNat 20))))))
    (And
      (∀ (i j : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
        @LT.lt.{0} Real Real.instLT
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (BfgsVerification.LShapePrecision.actualEntry i j)
              (BfgsVerification.LShapePrecision.correctedDisplay15 i j)))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real 2
                (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                  BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget._proof_12))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@OfNat.ofNat.{0} Real 10
                  (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast
                    BfgsVerification.LShapePrecision.display20._proof_2))
                (@OfNat.ofNat.{0} Nat 15 (instOfNatNat 15))))))
      (And
        (∀ (i j : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
          @LT.lt.{0} Real Real.instLT
            (@abs.{0} Real Real.lattice Real.instAddGroup
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (BfgsVerification.LShapePrecision.actualEntry i j)
                (BfgsVerification.LShapePrecision.originalDisplay15 i j)))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@OfNat.ofNat.{0} Real 10
                  (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast
                    BfgsVerification.LShapePrecision.display20._proof_2))
                (@OfNat.ofNat.{0} Nat 15 (instOfNatNat 15)))))
        (@LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real 2
                (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                  BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget._proof_12))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@OfNat.ofNat.{0} Real 10
                  (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast
                    BfgsVerification.LShapePrecision.display20._proof_2))
                (@OfNat.ofNat.{0} Nat 15 (instOfNatNat 15)))))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (BfgsVerification.LShapePrecision.originalDisplay15
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                  BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget._proof_11 1))
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                  BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget._proof_11 0)))
            (BfgsVerification.LShapePrecision.actualEntry
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                  BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget._proof_11 1))
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                  BfgsVerification.LShapePrecision.ActualJacobianPrecisionTarget._proof_11 0))))))))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.LReturnSpectrum.actual_spectral_contract, ``EJob04.Contract01),
    (``BfgsVerification.LGlobalTargets.spectrum, ``EJob04.Contract02),
    (``BfgsVerification.LReturnStableGraph.lStableManifold, ``EJob04.Contract03),
    (``BfgsVerification.LEmbedding.hessian, ``EJob04.Contract04),
    (``BfgsVerification.LShapePrecision.actualJacobianPrecision, ``EJob04.Contract05)]
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
