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

def EJob05.Contract01 : Prop :=
∀ (b : Real),
  @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 17
          (@instOfNatAtLeastTwo.{0} Real 17 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_1))
        (@OfNat.ofNat.{0} Real 10
          (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_2)))
      b →
    @LE.le.{0} Real Real.instLE b
        (@OfNat.ofNat.{0} Real 34
          (@instOfNatAtLeastTwo.{0} Real 34 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_3)) →
      And (@LT.lt.{0} Real Real.instLT BfgsVerification.LScalarRamp.epsilon (BfgsVerification.LScalarRamp.center b))
        (And
          (@LT.lt.{0} Real Real.instLT (BfgsVerification.LScalarRamp.center b)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) BfgsVerification.LScalarRamp.epsilon))
          (And
            (@Eq.{1} Real
              (@intervalIntegral.{0} Real Real.normedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                (fun (x : Real) => BfgsVerification.LScalarRamp.ramp b x)
                (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                (BfgsVerification.LScalarRamp.center b)))
            (And
              (∀ (x : Real),
                @Eq.{1} Real (BfgsVerification.LScalarRamp.primitive b x)
                  (@intervalIntegral.{0} Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    (fun (t : Real) => BfgsVerification.LScalarRamp.ramp b t)
                    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) x
                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
              (And
                (∀ (x : Real),
                  And
                    (@HasDerivAt.{0, 0} Real
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
                      BfgsVerification.LScalarRampTarget._proof_4 (BfgsVerification.LScalarRamp.ramp b)
                      (BfgsVerification.LScalarRamp.rampDerivative b x) x)
                    (And
                      (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                        (BfgsVerification.LScalarRamp.rampDerivative b x))
                      (@LE.le.{0} Real Real.instLE (BfgsVerification.LScalarRamp.rampDerivative b x)
                        (@OfNat.ofNat.{0} Real 768
                          (@instOfNatAtLeastTwo.{0} Real 768 Real.instNatCast
                            BfgsVerification.LScalarRampTarget._proof_5)))))
                (And
                  (@LT.lt.{0} Real Real.instLT
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                      (@OfNat.ofNat.{0} Real 2
                        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_6)))
                    (BfgsVerification.LScalarRamp.lowerLength b))
                  (@LT.lt.{0} Real Real.instLT
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                      (@OfNat.ofNat.{0} Real 2
                        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_6)))
                    (BfgsVerification.LScalarRamp.upperLength b)))))))

def EJob05.Contract02 : Prop :=
∀ (b : Real),
  @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 17
          (@instOfNatAtLeastTwo.{0} Real 17 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_1))
        (@OfNat.ofNat.{0} Real 10
          (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_2)))
      b →
    @LE.le.{0} Real Real.instLE b
        (@OfNat.ofNat.{0} Real 34
          (@instOfNatAtLeastTwo.{0} Real 34 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_3)) →
      ∀ (n : Nat),
        And
          (@Eq.{1} Real
            (BfgsVerification.LScalar.phi b
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
                (BfgsVerification.LScalarGeometric.scale n)))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (BfgsVerification.LScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
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
              BfgsVerification.LScalarRampTarget._proof_4 (BfgsVerification.LScalar.phi b)
              (BfgsVerification.LScalarGeometric.scale n)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
                (BfgsVerification.LScalarGeometric.scale n)))
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
                BfgsVerification.LScalarRampTarget._proof_4
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
                  (BfgsVerification.LScalar.phi b))
                (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
                  (BfgsVerification.LScalarGeometric.scale n)))
              (∀ (h : Real),
                @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup h)
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (BfgsVerification.LScalarGeometric.scale n)
                      (@OfNat.ofNat.{0} Real 2
                        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                          BfgsVerification.LScalarRampTarget._proof_6))) →
                  @Eq.{1} Real
                    (BfgsVerification.LScalar.phi b
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
                          (BfgsVerification.LScalarGeometric.scale n))
                        h))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                        (BfgsVerification.LScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (BfgsVerification.LScalarGeometric.scale n) h)))))

def EJob05.Contract03 : Prop :=
∀ (b : Real),
  @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 17
          (@instOfNatAtLeastTwo.{0} Real 17 Real.instNatCast BfgsVerification.LScalarStepDefinitionTarget._proof_1))
        (@OfNat.ofNat.{0} Real 10
          (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast BfgsVerification.LScalarStepDefinitionTarget._proof_2)))
      b →
    @LE.le.{0} Real Real.instLE b
        (@OfNat.ofNat.{0} Real 34
          (@instOfNatAtLeastTwo.{0} Real 34 Real.instNatCast BfgsVerification.LScalarStepDefinitionTarget._proof_3)) →
      ∀ (n : Nat),
        And
          (@Eq.{1} Real
            (BfgsVerification.LScalarStep.phi b
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
                (BfgsVerification.LScalarGeometric.scale n)))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (BfgsVerification.LScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
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
              BfgsVerification.LScalarStepNodeTarget._proof_4 (BfgsVerification.LScalarStep.phi b)
              (BfgsVerification.LScalarGeometric.scale n)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
                (BfgsVerification.LScalarGeometric.scale n)))
            (∀ (h : Real),
              @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup h)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (BfgsVerification.LScalarGeometric.scale n)
                    (@OfNat.ofNat.{0} Real 2
                      (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                        BfgsVerification.LScalarStepNodeTarget._proof_5))) →
                @Eq.{1} Real
                  (BfgsVerification.LScalarStep.phi b
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
                        (BfgsVerification.LScalarGeometric.scale n))
                      h))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                      (BfgsVerification.LScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (BfgsVerification.LScalarGeometric.scale n) h))))

def EJob05.Contract04 : Prop :=
And
  (@IsOpen.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
      @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    BfgsVerification.LEmbedding.localDomain)
  (And
    (@Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
      (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
      (@Set.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
      BfgsVerification.LEmbedding.localDomain
      (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
        (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))
    (And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
        BfgsVerification.LEmbedding.offset)
      (And
        (∀ (n : Nat) (y : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
          @Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
              (@Set.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
              BfgsVerification.LEmbedding.localDomain y →
            @Eq.{1} Real (BfgsVerification.LEmbedding.objective (BfgsVerification.LEmbedding.copyPoint n y))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                  (BfgsVerification.LScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  BfgsVerification.LEmbedding.offset
                  (BfgsVerification.LQuadraticSeed.objective BfgsVerification.LEmbedding.mu y))))
        (And
          (∀ (n : Nat),
            And
              (@Eq.{1} Real (BfgsVerification.LEmbedding.objective (BfgsVerification.LEmbedding.copyCenter n))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                    (BfgsVerification.LScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  BfgsVerification.LEmbedding.offset))
              (And
                (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                  (BfgsVerification.LEmbedding.objective (BfgsVerification.LEmbedding.copyCenter n)))
                (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)) ∉
                  @BfgsVerification.ConvexSubdifferential.subdifferential (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.LEmbedding.objective (BfgsVerification.LEmbedding.copyCenter n))))
          (And
            (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              BfgsVerification.LEmbedding.copyCenter (@Filter.atTop.{0} Nat Nat.instPreorder)
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
            (∀ (y : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
              @Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (n : Nat) => BfgsVerification.LEmbedding.copyPoint n y) (@Filter.atTop.{0} Nat Nat.instPreorder)
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
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))))))))

def EJob05.Contract05 : Prop :=
BfgsVerification.LActualCopies.FixedMetricFailureTarget BfgsVerification.LEmbedding.objective

def EJob05.Contract06 : Prop :=
BfgsVerification.LActualCopies.FixedMetricFailureTarget BfgsVerification.LStepEmbedding.objective

def EJob05.Contract07 : Prop :=
∀ (b : Real),
  @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 17
          (@instOfNatAtLeastTwo.{0} Real 17 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_1))
        (@OfNat.ofNat.{0} Real 10
          (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_2)))
      b →
    @LE.le.{0} Real Real.instLE b
        (@OfNat.ofNat.{0} Real 34
          (@instOfNatAtLeastTwo.{0} Real 34 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_3)) →
      And
        (@ConvexOn.{0, 0, 0} Real Real Real Real.semiring Real.partialOrder Real.instAddCommMonoid
          Real.instAddCommMonoid Real.partialOrder
          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
          (@Set.univ.{0} Real) (BfgsVerification.LScalar.phi b))
        (And
          (∀ (x : Real),
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
              (BfgsVerification.LScalar.phi b x))
          (And
            (@Filter.Tendsto.{0, 0} Real Real (BfgsVerification.LScalar.phi b)
              (@Filter.cocompact.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
              (@Filter.atTop.{0} Real Real.instPreorder))
            (And
              (And
                (∀ (x : Real),
                  @LE.le.{0} Real Real.instLE
                    (BfgsVerification.LScalar.phi b (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))
                    (BfgsVerification.LScalar.phi b x))
                (∀ (x : Real),
                  @Eq.{1} Real (BfgsVerification.LScalar.phi b x)
                      (BfgsVerification.LScalar.phi b
                        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))) →
                    @Eq.{1} Real x (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
              (And
                (@ContDiff.{0, 0, 0} Real
                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
                              (@Semiring.toNonAssocSemiring.{0} ENat
                                (@CommSemiring.toSemiring.{0} ENat instENatCommSemiring))))))))
                  (BfgsVerification.LScalar.phi b))
                (And
                  (∃ (K : NNReal),
                    @LipschitzWith.{0, 0} Real Real
                      (@EMetricSpace.toPseudoEMetricSpace.{0} Real
                        (@MetricSpace.toEMetricSpace.{0} Real Real.metricSpace))
                      (@EMetricSpace.toPseudoEMetricSpace.{0} Real
                        (@MetricSpace.toEMetricSpace.{0} Real Real.metricSpace))
                      K
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
                        (BfgsVerification.LScalar.phi b)))
                  (And
                    (∀ (x : Real),
                      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) x →
                        @ContDiffAt.{0, 0, 0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
                                      (@Semiring.toNonAssocSemiring.{0} ENat
                                        (@CommSemiring.toSemiring.{0} ENat instENatCommSemiring))))))
                              BfgsVerification.LScalarRampTarget._proof_6))
                          (BfgsVerification.LScalar.phi b) x)
                    (And
                      (∀ (x : Real),
                        @LT.lt.{0} Real Real.instLT x
                            (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) →
                          @ContDiffAt.{0, 0, 0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
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
                                        (@Semiring.toNonAssocSemiring.{0} ENat
                                          (@CommSemiring.toSemiring.{0} ENat instENatCommSemiring))))))
                                BfgsVerification.LScalarRampTarget._proof_6))
                            (BfgsVerification.LScalar.phi b) x)
                      (And
                        (Not
                          (@DifferentiableAt.{0, 0, 0} Real
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
                              (BfgsVerification.LScalar.phi b))
                            (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
                        (∀ (x a : Real),
                          @HasDerivAt.{0, 0} Real
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
                              BfgsVerification.LScalarRampTarget._proof_4
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
                                (BfgsVerification.LScalar.phi b))
                              a x →
                            And
                              (@LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) a)
                              (@LE.le.{0} Real Real.instLE a
                                (@Max.max.{0} Real Real.instMax
                                  (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@OfNat.ofNat.{0} Real 768
                                      (@instOfNatAtLeastTwo.{0} Real 768 Real.instNatCast
                                        BfgsVerification.LScalarRampTarget._proof_5))
                                    b))))))))))))

def EJob05.Contract08 : Prop :=
∀ (b : Real),
  @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 17
          (@instOfNatAtLeastTwo.{0} Real 17 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_1))
        (@OfNat.ofNat.{0} Real 10
          (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_2)))
      b →
    @LE.le.{0} Real Real.instLE b
        (@OfNat.ofNat.{0} Real 34
          (@instOfNatAtLeastTwo.{0} Real 34 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_3)) →
      And
        (@Filter.Tendsto.{0, 0} Nat Real (BfgsVerification.LScalar.peak b) (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@nhds.{0} Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
        (And
          (∀ (n : Nat),
            And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                (BfgsVerification.LScalar.peak b n))
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
                BfgsVerification.LScalarRampTarget._proof_4
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
                  (BfgsVerification.LScalar.phi b))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real 768
                    (@instOfNatAtLeastTwo.{0} Real 768 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_5))
                  b)
                (BfgsVerification.LScalar.peak b n)))
          (And
            (And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real 768
                    (@instOfNatAtLeastTwo.{0} Real 768 Real.instNatCast BfgsVerification.LScalarRampTarget._proof_5))
                  b))
              (Not
                (@Filter.Tendsto.{0, 0} Nat Real
                  (fun (n : Nat) =>
                    @deriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
                        (BfgsVerification.LScalar.phi b))
                      (BfgsVerification.LScalar.peak b n))
                  (@Filter.atTop.{0} Nat Nat.instPreorder)
                  (@nhds.{0} Real
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))))
            (∀ (n : Nat),
              And
                (@Eq.{1} Real
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
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
                      (BfgsVerification.LScalar.phi b)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
                        (BfgsVerification.LScalarGeometric.scale n)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
                      (BfgsVerification.LScalarGeometric.scale n)))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) b))
                (@Eq.{1} Real
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
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
                      (BfgsVerification.LScalar.phi b)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                            (@OfNat.ofNat.{0} Real 4
                              (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                                BfgsVerification.LScalarPeaksTarget._proof_7))))
                        (BfgsVerification.LScalarGeometric.scale n)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                          (@OfNat.ofNat.{0} Real 4
                            (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                              BfgsVerification.LScalarPeaksTarget._proof_7))))
                      (BfgsVerification.LScalarGeometric.scale n)))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                        (@OfNat.ofNat.{0} Real 4
                          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                            BfgsVerification.LScalarPeaksTarget._proof_7)))))))))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.lScalarRamp, ``EJob05.Contract01),
    (``BfgsVerification.lScalarNodes, ``EJob05.Contract02),
    (``BfgsVerification.lScalarStepNodes, ``EJob05.Contract03),
    (``BfgsVerification.LEmbedding.localModel, ``EJob05.Contract04),
    (``BfgsVerification.LActualCopies.smoothFailure, ``EJob05.Contract05),
    (``BfgsVerification.LActualCopies.stepFailure, ``EJob05.Contract06),
    (``BfgsVerification.lScalarRegularity, ``EJob05.Contract07),
    (``BfgsVerification.lScalarPeaks, ``EJob05.Contract08)]
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
