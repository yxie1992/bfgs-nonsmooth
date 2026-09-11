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

def EJob13.Contract01 : Prop :=
∀ (a b : Real → Real),
  @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
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
                  (@Semiring.toNonAssocSemiring.{0} ENat (@CommSemiring.toSemiring.{0} ENat instENatCommSemiring))))))
          BfgsVerification.RidgeSupersession.RidgeSupersessionTarget._proof_1))
      a →
    @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
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
                    (@Semiring.toNonAssocSemiring.{0} ENat (@CommSemiring.toSemiring.{0} ENat instENatCommSemiring))))))
            BfgsVerification.RidgeSupersession.RidgeSupersessionTarget._proof_1))
        b →
      @ConvexOn.{0, 0, 0} Real Real Real Real.semiring Real.partialOrder Real.instAddCommMonoid Real.instAddCommMonoid
          Real.partialOrder
          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
          (@Set.univ.{0} Real) a →
        @ConvexOn.{0, 0, 0} Real Real Real Real.semiring Real.partialOrder Real.instAddCommMonoid Real.instAddCommMonoid
            Real.partialOrder
            (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
              (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
            (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
              (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
            (@Set.univ.{0} Real) b →
          ∀ (p q u : Real),
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) p →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) q →
                (∀ (t : Real),
                    @LE.le.{0} Real Real.instLE (BfgsVerification.RidgeSupersession.profile a b p q u)
                      (BfgsVerification.RidgeSupersession.profile a b p q t)) →
                  (∀ (t : Real),
                      @Eq.{1} Real (BfgsVerification.RidgeSupersession.profile a b p q t)
                          (BfgsVerification.RidgeSupersession.profile a b p q u) →
                        @Eq.{1} Real t u) →
                    (∀ (t : Real),
                        @Ne.{1} Real t u →
                          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                            (@deriv.{0, 0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
                              (@UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              (@deriv.{0, 0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
                                (@UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                a)
                              t)) →
                      (∀ (t : Real),
                          @Ne.{1} Real t u →
                            @LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@deriv.{0, 0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
                                (@UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (@deriv.{0, 0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
                                  (@UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  b)
                                t)) →
                        And
                          (∀
                            (R :
                              BfgsVerification.AdmissibleBFGSRun (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                (BfgsVerification.RidgeSupersession.objective a b p q)),
                            And
                              (@Filter.Tendsto.{0, 0} Nat Real
                                (fun (k : Nat) =>
                                  BfgsVerification.RidgeSupersession.objective a b p q
                                    (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                      (BfgsVerification.RidgeSupersession.objective a b p q) R k))
                                (@Filter.atTop.{0} Nat Nat.instPreorder)
                                (@nhds.{0} Real
                                  (@UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (BfgsVerification.RidgeSupersession.profile a b p q u)))
                              (@Filter.Tendsto.{0, 0} Nat
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                  (BfgsVerification.RidgeSupersession.objective a b p q) R)
                                (@Filter.atTop.{0} Nat Nat.instPreorder)
                                (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (BfgsVerification.RidgeSupersession.optimizer a b p q u))))
                          (∀ (U : Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))),
                            @Membership.mem.{0, 0}
                                (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                (Filter.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                (@Filter.instMembership.{0}
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (BfgsVerification.RidgeSupersession.optimizer a b p q u))
                                U →
                              ∃ (ε : Real),
                                And
                                  (@LT.lt.{0} Real Real.instLT
                                    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
                                  (∀
                                    (R :
                                      BfgsVerification.AdmissibleBFGSRun (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                        (BfgsVerification.RidgeSupersession.objective a b p q)),
                                    @LE.le.{0} Real Real.instLE
                                        (BfgsVerification.RidgeSupersession.objective a b p q
                                          (@BfgsVerification.AdmissibleBFGSRun.x
                                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                            (BfgsVerification.RidgeSupersession.objective a b p q) R
                                            (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                          (BfgsVerification.RidgeSupersession.profile a b p q u) ε) →
                                      And
                                        (∀ (k : Nat),
                                          @Membership.mem.{0, 0}
                                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                            (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                            (@Set.instMembership.{0}
                                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                                            U
                                            (@BfgsVerification.AdmissibleBFGSRun.x
                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                              (BfgsVerification.RidgeSupersession.objective a b p q) R k))
                                        (And
                                          (@Filter.Tendsto.{0, 0} Nat Real
                                            (fun (k : Nat) =>
                                              BfgsVerification.RidgeSupersession.objective a b p q
                                                (@BfgsVerification.AdmissibleBFGSRun.x
                                                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                                  (BfgsVerification.RidgeSupersession.objective a b p q) R k))
                                            (@Filter.atTop.{0} Nat Nat.instPreorder)
                                            (@nhds.{0} Real
                                              (@UniformSpace.toTopologicalSpace.{0} Real
                                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                              (BfgsVerification.RidgeSupersession.profile a b p q u)))
                                          (@Filter.Tendsto.{0, 0} Nat
                                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                            (@BfgsVerification.AdmissibleBFGSRun.x
                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                              (BfgsVerification.RidgeSupersession.objective a b p q) R)
                                            (@Filter.atTop.{0} Nat Nat.instPreorder)
                                            (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                              (@Pi.topologicalSpace.{0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                                @UniformSpace.toTopologicalSpace.{0} Real
                                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                              (BfgsVerification.RidgeSupersession.optimizer a b p q u))))))

def EJob13.Contract02 : Prop :=
∀ {a b : Real → Real},
  @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
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
                  (@Semiring.toNonAssocSemiring.{0} ENat (@CommSemiring.toSemiring.{0} ENat instENatCommSemiring))))))
          (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
      a →
    @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
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
                    (@Semiring.toNonAssocSemiring.{0} ENat (@CommSemiring.toSemiring.{0} ENat instENatCommSemiring))))))
            (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
        b →
      @ConvexOn.{0, 0, 0} Real Real Real Real.semiring Real.partialOrder Real.instAddCommMonoid Real.instAddCommMonoid
          Real.partialOrder
          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
          (@Set.univ.{0} Real) a →
        @ConvexOn.{0, 0, 0} Real Real Real Real.semiring Real.partialOrder Real.instAddCommMonoid Real.instAddCommMonoid
            Real.partialOrder
            (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
              (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
            (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
              (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
            (@Set.univ.{0} Real) b →
          ∀ {p q u : Real},
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) p →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) q →
                (∀ (t : Real),
                    @LE.le.{0} Real Real.instLE (BfgsVerification.RidgeSupersession.profile a b p q u)
                      (BfgsVerification.RidgeSupersession.profile a b p q t)) →
                  (∀ (t : Real),
                      @Eq.{1} Real (BfgsVerification.RidgeSupersession.profile a b p q t)
                          (BfgsVerification.RidgeSupersession.profile a b p q u) →
                        @Eq.{1} Real t u) →
                    (∀ (t : Real),
                        @Ne.{1} Real t u →
                          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                            (@deriv.{0, 0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
                              (@UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              (@deriv.{0, 0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
                                (@UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                a)
                              t)) →
                      (∀ (t : Real),
                          @Ne.{1} Real t u →
                            @LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@deriv.{0, 0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
                                (@UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (@deriv.{0, 0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
                                  (@UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  b)
                                t)) →
                        ∀
                          (R :
                            BfgsVerification.AdmissibleBFGSRun (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              (BfgsVerification.RidgeSupersession.objective a b p q)),
                          And
                            (@Filter.Tendsto.{0, 0} Nat Real
                              (fun (k : Nat) =>
                                BfgsVerification.RidgeSupersession.objective a b p q
                                  (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                    (BfgsVerification.RidgeSupersession.objective a b p q) R k))
                              (@Filter.atTop.{0} Nat Nat.instPreorder)
                              (@nhds.{0} Real
                                (@UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (BfgsVerification.RidgeSupersession.profile a b p q u)))
                            (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                (BfgsVerification.RidgeSupersession.objective a b p q) R)
                              (@Filter.atTop.{0} Nat Nat.instPreorder)
                              (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                  @UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (BfgsVerification.RidgeSupersession.optimizer a b p q u)))

def EJob13.Contract03 : Prop :=
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
    (``BfgsVerification.RidgeSupersession.ridgeSupersession, ``EJob13.Contract01),
    (``BfgsVerification.RidgeSupersession.fullBFGS_convergence, ``EJob13.Contract02),
    (``BfgsVerification.AdmissibleBFGSRun.moving_frame_energy, ``EJob13.Contract03)]
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
