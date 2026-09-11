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

def EJob18.Contract01 : Prop :=
∀ {n : Nat} {F : BfgsVerification.Vec n → Real} (R : BfgsVerification.AdmissibleBFGSRun n F)
  {Ω : Set.{0} (BfgsVerification.Vec n)},
  @IsOpen.{0} (BfgsVerification.Vec n)
      (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
        @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      Ω →
    @IsCompact.{0} (BfgsVerification.Vec n)
        (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@BfgsVerification.AdmissibleBFGSRun.initialSublevel n F R) →
      @HasSubset.Subset.{0} (Set.{0} (BfgsVerification.Vec n)) (@Set.instHasSubset.{0} (BfgsVerification.Vec n))
          (@BfgsVerification.AdmissibleBFGSRun.initialSublevel n F R) Ω →
        ∀ {μ : Real},
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) μ →
            @BfgsVerification.FixedNormal.EuclideanStrongConvexOn n Ω μ F →
              ∀ {a : BfgsVerification.Vec n},
                @Eq.{1} Real (@BfgsVerification.sqNorm n a)
                    (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) →
                  ∀ (b : Real) {A : BfgsVerification.Vec n → BfgsVerification.Vec n},
                    (∀ (x : BfgsVerification.Vec n),
                        @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                            (@Set.instMembership.{0} (BfgsVerification.Vec n)) Ω x →
                          ∀ (g : BfgsVerification.Vec n),
                            @BfgsVerification.Homogeneous.Supports n F x g →
                              @Eq.{1} (BfgsVerification.Vec n) (@BfgsVerification.FixedNormal.tangentProjection n a g)
                                (A x)) →
                      ∀ {L : NNReal},
                        @LipschitzOnWith.{0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n)
                            (@pseudoEMetricSpacePi.{0, 0} (Fin n) (fun (a : Fin n) => Real) (Fin.fintype n)
                              fun (b : Fin n) =>
                              @EMetricSpace.toPseudoEMetricSpace.{0} Real
                                (@MetricSpace.toEMetricSpace.{0} Real Real.metricSpace))
                            (@pseudoEMetricSpacePi.{0, 0} (Fin n) (fun (a : Fin n) => Real) (Fin.fintype n)
                              fun (b : Fin n) =>
                              @EMetricSpace.toPseudoEMetricSpace.{0} Real
                                (@MetricSpace.toEMetricSpace.{0} Real Real.metricSpace))
                            L A Ω →
                          @BfgsVerification.CenteredSmoothSublinear.LocallyC11On n
                              (@BfgsVerification.FixedNormal.regularRegion n Ω a b
                                (@Singleton.singleton.{0, 0} Real (Set.{0} Real) (@Set.instSingletonSet.{0} Real)
                                  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
                              F →
                            ∀ (star : BfgsVerification.Vec n),
                              (∀ (z : BfgsVerification.Vec n), @LE.le.{0} Real Real.instLE (F star) (F z)) →
                                (∀ (z : BfgsVerification.Vec n),
                                    @Eq.{1} Real (F z) (F star) → @Eq.{1} (BfgsVerification.Vec n) z star) →
                                  @Eq.{1} Real (@BfgsVerification.dot n a star) b →
                                    And
                                      (@Filter.Tendsto.{0, 0} Nat Real
                                        (fun (k : Nat) => F (@BfgsVerification.AdmissibleBFGSRun.x n F R k))
                                        (@Filter.atTop.{0} Nat Nat.instPreorder)
                                        (@nhds.{0} Real
                                          (@UniformSpace.toTopologicalSpace.{0} Real
                                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                          (F star)))
                                      (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec n)
                                        (@BfgsVerification.AdmissibleBFGSRun.x n F R)
                                        (@Filter.atTop.{0} Nat Nat.instPreorder)
                                        (@nhds.{0} (BfgsVerification.Vec n)
                                          (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                            fun (i : Fin n) =>
                                            @UniformSpace.toTopologicalSpace.{0} Real
                                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                          star))

def EJob18.Contract02 : Prop :=
∀ (n : Nat)
  (R :
    BfgsVerification.AdmissibleBFGSRun
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
      (@BfgsVerification.NormalSpike.objective
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (BfgsVerification.NormalSpike.normal n))),
  And
    (@Filter.Tendsto.{0, 0} Nat Real
      (fun (k : Nat) =>
        @BfgsVerification.NormalSpike.objective
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.NormalSpike.normal n)
          (@BfgsVerification.AdmissibleBFGSRun.x
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@BfgsVerification.NormalSpike.objective
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (BfgsVerification.NormalSpike.normal n))
            R k))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
    (@Filter.Tendsto.{0, 0} Nat
      (BfgsVerification.Vec
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
      (@BfgsVerification.AdmissibleBFGSRun.x
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@BfgsVerification.NormalSpike.objective
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.NormalSpike.normal n))
        R)
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0}
        (BfgsVerification.Vec
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
        (@Pi.topologicalSpace.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
          (fun
              (a :
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) =>
            Real)
          fun
            (i :
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0}
          (BfgsVerification.Vec
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
          0
          (@Zero.toOfNat0.{0}
            (BfgsVerification.Vec
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
            (@Pi.instZero.{0, 0}
              (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
              (fun
                  (a :
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) =>
                Real)
              fun
                (i :
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) =>
              Real.instZero)))))

def EJob18.Contract03 : Prop :=
And
  (@ConvexOn.{0, 0, 0} Real Real Real Real.semiring Real.partialOrder Real.instAddCommMonoid Real.instAddCommMonoid
    Real.partialOrder
    (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
      (@Algebra.id.{0} Real Real.instCommSemiring))
    (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
      (@Algebra.id.{0} Real Real.instCommSemiring))
    (@Set.univ.{0} Real) BfgsVerification.NormalSpike.sourcePrimitive)
  (And
    (@ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} (WithTop.{0} ENat) 1
        (@One.toOfNat1.{0} (WithTop.{0} ENat)
          (@WithTop.one.{0} ENat
            (@AddMonoidWithOne.toOne.{0} ENat
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENat
                (@NonAssocSemiring.toAddCommMonoidWithOne.{0} ENat
                  (@Semiring.toNonAssocSemiring.{0} ENat (@CommSemiring.toSemiring.{0} ENat instENatCommSemiring))))))))
      BfgsVerification.NormalSpike.sourcePrimitive)
    (And
      (@ContDiffOn.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@OfNat.ofNat.{0} (WithTop.{0} ENat) 3
          (@instOfNatAtLeastTwo.{0} (WithTop.{0} ENat) 3
            (@AddMonoidWithOne.toNatCast.{0} (WithTop.{0} ENat)
              (@WithTop.addMonoidWithOne.{0} ENat
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENat
                  (@NonAssocSemiring.toAddCommMonoidWithOne.{0} ENat
                    (@Semiring.toNonAssocSemiring.{0} ENat (@CommSemiring.toSemiring.{0} ENat instENatCommSemiring))))))
            BfgsVerification.NormalSpike.SourceSpikePropertiesTarget._proof_1))
        BfgsVerification.NormalSpike.sourcePrimitive
        (@HasCompl.compl.{0} (Set.{0} Real) (@Set.instHasCompl.{0} Real)
          (@Singleton.singleton.{0, 0} Real (Set.{0} Real) (@Set.instSingletonSet.{0} Real)
            (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))))
      (And
        (∀ (v : Real),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
            (BfgsVerification.NormalSpike.sourcePrimitive v))
        (And
          (∀ (v : Real),
            @LE.le.{0} Real Real.instLE v (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) →
              @Eq.{1} Real (BfgsVerification.NormalSpike.sourcePrimitive v)
                (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))
          (And
            (∀ (v : Real),
              @GE.ge.{0} Real Real.instLE v (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) →
                And
                  (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
                      BfgsVerification.NormalSpike.sourcePrimitive v))
                  (And
                    (@LE.le.{0} Real Real.instLE
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
                        BfgsVerification.NormalSpike.sourcePrimitive v)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real 6
                          (@instOfNatAtLeastTwo.{0} Real 6 Real.instNatCast
                            BfgsVerification.NormalSpike.SourceSpikePropertiesTarget._proof_2))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) v
                          (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
                    (@LE.le.{0} Real Real.instLE (BfgsVerification.NormalSpike.sourcePrimitive v)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real 6
                          (@instOfNatAtLeastTwo.{0} Real 6 Real.instNatCast
                            BfgsVerification.NormalSpike.SourceSpikePropertiesTarget._proof_2))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) v
                          (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))))))
            (And
              (@HasDerivAt.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
                BfgsVerification.NormalSpike.SourceSpikePropertiesTarget._proof_3
                (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
                  BfgsVerification.NormalSpike.sourcePrimitive)
                (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))
              (And
                (@Eq.{1} Real
                  (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
                    (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
                      BfgsVerification.NormalSpike.sourcePrimitive)
                    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))
                  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))
                (And
                  (∀ (N : Nat),
                    And
                      (@Eq.{1} Real
                        (BfgsVerification.NormalSpike.sourcePrimitive (BfgsVerification.NormalSpike.scale N))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@OfNat.ofNat.{0} Real 64
                                (@instOfNatAtLeastTwo.{0} Real 64 Real.instNatCast
                                  BfgsVerification.NormalSpike.SourceSpikePropertiesTarget._proof_4))
                              (@OfNat.ofNat.{0} Real 315
                                (@instOfNatAtLeastTwo.{0} Real 315 Real.instNatCast
                                  BfgsVerification.NormalSpike.SourceSpikePropertiesTarget._proof_5)))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                              (BfgsVerification.NormalSpike.scale N) (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                              (@OfNat.ofNat.{0} Real 6
                                (@instOfNatAtLeastTwo.{0} Real 6 Real.instNatCast
                                  BfgsVerification.NormalSpike.SourceSpikePropertiesTarget._proof_2)))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                              (BfgsVerification.NormalSpike.scale N) (@OfNat.ofNat.{0} Nat 7 (instOfNatNat 7))))))
                      (And
                        (@Eq.{1} Real
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
                            BfgsVerification.NormalSpike.sourcePrimitive (BfgsVerification.NormalSpike.scale N))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@OfNat.ofNat.{0} Real 8
                                (@instOfNatAtLeastTwo.{0} Real 8 Real.instNatCast
                                  BfgsVerification.NormalSpike.SourceSpikePropertiesTarget._proof_6))
                              (@OfNat.ofNat.{0} Real 9
                                (@instOfNatAtLeastTwo.{0} Real 9 Real.instNatCast
                                  BfgsVerification.NormalSpike.SourceSpikePropertiesTarget._proof_7)))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                              (BfgsVerification.NormalSpike.scale N) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
                        (@Eq.{1} Real
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
                              BfgsVerification.NormalSpike.sourcePrimitive)
                            (BfgsVerification.NormalSpike.scale N))
                          (@Inv.inv.{0} Real Real.instInv
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                              (BfgsVerification.NormalSpike.scale N) (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))))))
                  (And
                    (@Filter.Tendsto.{0, 0} Nat Real
                      (fun (N : Nat) =>
                        @deriv.{0, 0} Real
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
                            BfgsVerification.NormalSpike.sourcePrimitive)
                          (BfgsVerification.NormalSpike.scale N))
                      (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder))
                    (Not
                      (@ContinuousAt.{0, 0} Real Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
                            BfgsVerification.NormalSpike.sourcePrimitive))
                        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))))))))))))

def EJob18.Contract04 : Prop :=
∀ (v : Rat),
  And
    (@Eq.{1} Real (@Rat.cast.{0} Real Real.instRatCast (BfgsVerification.NormalSpike.rationalValueOracle v))
      (BfgsVerification.NormalSpike.sourcePrimitive (@Rat.cast.{0} Real Real.instRatCast v)))
    (And
      (@Eq.{1} Real (@Rat.cast.{0} Real Real.instRatCast (BfgsVerification.NormalSpike.rationalDerivativeOracle v))
        (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
          BfgsVerification.NormalSpike.sourcePrimitive (@Rat.cast.{0} Real Real.instRatCast v)))
      (@Eq.{1} Real
        (@Rat.cast.{0} Real Real.instRatCast (BfgsVerification.NormalSpike.rationalSecondDerivativeOracle v))
        (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
          (@deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
            BfgsVerification.NormalSpike.sourcePrimitive)
          (@Rat.cast.{0} Real Real.instRatCast v))))

def EJob18.Contract05 : Prop :=
∀ {n : Nat} (a : BfgsVerification.Vec n),
  @Eq.{1} Real (@BfgsVerification.sqNorm n a) (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) →
    ∀ (R : BfgsVerification.AdmissibleBFGSRun n (@BfgsVerification.NormalSpike.objective n a)),
      ∃ (N : Nat),
        ∀ (k : Nat),
          @GE.ge.{0} Nat instLENat k N →
            @LT.lt.{0} Real Real.instLT
              (@BfgsVerification.NormalSpike.objective n a
                (@BfgsVerification.AdmissibleBFGSRun.x n (@BfgsVerification.NormalSpike.objective n a) R k))
              (@HPow.hPow.{0, 0, 0} Real Int Real
                (@instHPow.{0, 0} Real Int (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real 10
                  (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast
                    (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 8 (instOfNatNat 8)))))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int 28 (@instOfNat 28))))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.fixedNormalHyperplane, ``EJob18.Contract01),
    (``BfgsVerification.NormalSpike.spikeObjectiveConvergence, ``EJob18.Contract02),
    (``BfgsVerification.NormalSpike.sourceSpikeProperties, ``EJob18.Contract03),
    (``BfgsVerification.NormalSpike.rationalSpikeOracle, ``EJob18.Contract04),
    (``BfgsVerification.EReconstruction.spike_eventual_printed_tolerance, ``EJob18.Contract05)]
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
