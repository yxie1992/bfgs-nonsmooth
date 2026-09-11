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

def EJob03.Contract01 : Prop :=
∀ (c₁ c₂ : Real)
  (hc₁ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) c₁)
  (hc₁' :
    @LE.le.{0} Real Real.instLE c₁
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 3
          (@instOfNatAtLeastTwo.{0} Real 3 Real.instNatCast BfgsVerification.DeterministicSeedFailureTarget._proof_4))))
  (hc : @LT.lt.{0} Real Real.instLT c₁ c₂)
  (hc₂ : @LT.lt.{0} Real Real.instLT c₂ (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))),
  let R := BfgsVerification.SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂;
  And
    (@Eq.{1} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
      (@BfgsVerification.AdmissibleBFGSRun.H (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
        (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC BfgsVerification.SeedOrbit.seedD) R
        (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
      (@OfNat.ofNat.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
        (@One.toOfNat1.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Matrix.one.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.instZero Real.instOne))))
    (And
      (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
          (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC BfgsVerification.SeedOrbit.seedD) R)
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
      (And
        (@Filter.Tendsto.{0, 0} Nat Real
          (fun (k : Nat) =>
            BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC BfgsVerification.SeedOrbit.seedD
              (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC BfgsVerification.SeedOrbit.seedD)
                R k))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@nhds.{0} Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
        (And
          (∀ (k : Nat),
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
              (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC BfgsVerification.SeedOrbit.seedD
                (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                  (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC
                    BfgsVerification.SeedOrbit.seedD)
                  R k)))
          (And
            (∀ (k : Nat),
              @LT.lt.{0} Real Real.instLT
                (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC BfgsVerification.SeedOrbit.seedD
                  (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC
                      BfgsVerification.SeedOrbit.seedD)
                    R
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
                (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC BfgsVerification.SeedOrbit.seedD
                  (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC
                      BfgsVerification.SeedOrbit.seedD)
                    R k)))
            (And
              (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                  (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)) ∉
                @BfgsVerification.ConvexSubdifferential.subdifferential (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                  (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC
                    BfgsVerification.SeedOrbit.seedD)
                  (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))
              (∀ (k : Nat),
                @Eq.{1} (Prod.{0, 0} (Option.{0} Real) (List.{0} Real))
                  (@BfgsVerification.DeterministicLineSearch.fromMetric (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC
                      BfgsVerification.SeedOrbit.seedD)
                    (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC
                        BfgsVerification.SeedOrbit.seedD)
                      R k)
                    (@BfgsVerification.AdmissibleBFGSRun.H (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC
                        BfgsVerification.SeedOrbit.seedD)
                      R k)
                    c₁ c₂ (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                  (@Prod.mk.{0, 0} (Option.{0} Real) (List.{0} Real)
                    (@Option.some.{0} Real
                      (@BfgsVerification.AdmissibleBFGSRun.α (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                        (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC
                          BfgsVerification.SeedOrbit.seedD)
                        R k))
                    (BfgsVerification.SeedOrbit.trialHistory (BfgsVerification.SeedOrbit.phase k)))))))))

def EJob03.Contract02 : Prop :=
∀ (k : Nat) (q : Fin (@OfNat.ofNat.{0} Nat 9 (instOfNatNat 9))),
  @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (BfgsVerification.SeedOrbit.trialPhase q)
      (BfgsVerification.SeedOrbit.phase k) →
    And
      (@DifferentiableAt.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (BfgsVerification.SeedOrbit.objective BfgsVerification.SeedOrbit.seedC BfgsVerification.SeedOrbit.seedD)
        (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@instHAdd.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.instAdd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAdd))
          (BfgsVerification.SeedOrbit.orbitPoint k)
          (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@instHSMul.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                  (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                  (@Algebra.id.{0} Real Real.instCommSemiring))))
            (BfgsVerification.SeedOrbit.trialLength q)
            (@BfgsVerification.bfgsStep (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              (BfgsVerification.SeedOrbit.orbitMetric k) (BfgsVerification.SeedOrbit.orbitGradient k)
              (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))))))
      (BfgsVerification.SeedOrbit.PointCertificate BfgsVerification.SeedOrbit.seedC BfgsVerification.SeedOrbit.seedD
        (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@instHAdd.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.instAdd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAdd))
          (BfgsVerification.SeedOrbit.orbitPoint k)
          (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@instHSMul.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                  (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                  (@Algebra.id.{0} Real Real.instCommSemiring))))
            (BfgsVerification.SeedOrbit.trialLength q)
            (@BfgsVerification.bfgsStep (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              (BfgsVerification.SeedOrbit.orbitMetric k) (BfgsVerification.SeedOrbit.orbitGradient k)
              (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))))
        (BfgsVerification.SeedOrbit.trialActive q))

def EJob03.Contract03 : Prop :=
And
  (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
    (fun (n : Nat) =>
      BfgsVerification.SeedEmbedding.point (BfgsVerification.DEmbedding.center n)
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
          (BfgsVerification.DScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
    (@Filter.atTop.{0} Nat Nat.instPreorder)
    (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
        @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
        (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)))))
  (And
    (@Filter.Tendsto.{0, 0} Nat Real
      (fun (n : Nat) =>
        BfgsVerification.DEmbedding.objective
          (BfgsVerification.SeedEmbedding.point (BfgsVerification.DEmbedding.center n)
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (BfgsVerification.DScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
    (And
      (∀ (n : Nat),
        And
          (@Ne.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (BfgsVerification.DEmbedding.center n)
            (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
              (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))
          (And
            (@Eq.{1} Real (BfgsVerification.DEmbedding.objective (BfgsVerification.DEmbedding.center n))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (BfgsVerification.DScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))
            (And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                (BfgsVerification.DEmbedding.objective (BfgsVerification.DEmbedding.center n)))
              (And
                (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)) ∉
                  @BfgsVerification.ConvexSubdifferential.subdifferential (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.DEmbedding.objective (BfgsVerification.DEmbedding.center n))
                (@Filter.Tendsto.{0, 0} Real Real
                  (fun (t : Real) =>
                    @HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (BfgsVerification.DEmbedding.objective
                          (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (@instHAdd.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@Pi.instAdd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAdd))
                            (BfgsVerification.DEmbedding.center n)
                            (@HSMul.hSMul.{0, 0, 0} Real
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@instHSMul.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                  (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                    (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                    (@Algebra.id.{0} Real Real.instCommSemiring))))
                              t BfgsVerification.DEmbedding.descentDirection)))
                        (BfgsVerification.DEmbedding.objective (BfgsVerification.DEmbedding.center n)))
                      t)
                  (@nhdsWithin.{0} Real
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@Set.Ioi.{0} Real Real.instPreorder
                      (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
                  (@nhds.{0} Real
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@Neg.neg.{0} Real Real.instNeg
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                        (BfgsVerification.DScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))))))
      (And
        (∀ (V : Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))),
          @Membership.mem.{0, 0} (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
              (Filter.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
              (@Filter.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
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
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))
              V →
            @Filter.Eventually.{0} Nat
              (fun (n : Nat) =>
                And
                  (∀ (k : Nat),
                    @Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                      (@Set.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) V
                      (BfgsVerification.SeedEmbedding.point (BfgsVerification.DEmbedding.center n)
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                          (BfgsVerification.DScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        k))
                  (∀ (k : Nat) (q : Fin (@OfNat.ofNat.{0} Nat 9 (instOfNatNat 9))),
                    @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (BfgsVerification.SeedOrbit.trialPhase q)
                        (BfgsVerification.SeedOrbit.phase k) →
                      @Membership.mem.{0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                        (@Set.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) V
                        (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (@instHAdd.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (@Pi.instAdd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAdd))
                          (BfgsVerification.DEmbedding.center n)
                          (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (@instHSMul.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                  (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                  (@Algebra.id.{0} Real Real.instCommSemiring))))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                              (BfgsVerification.DScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.SeedEmbedding.trialPoint k q)))))
              (@Filter.atTop.{0} Nat Nat.instPreorder))
        (∀ (c₁ c₂ : Real)
          (hc₁ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) c₁)
          (hc₁' :
            @LE.le.{0} Real Real.instLE c₁
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real 3
                  (@instOfNatAtLeastTwo.{0} Real 3 Real.instNatCast
                    BfgsVerification.DEmbedding.EmbeddingFailureTarget._proof_6))))
          (hc : @LT.lt.{0} Real Real.instLT c₁ c₂)
          (hc₂ : @LT.lt.{0} Real Real.instLT c₂ (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
          (n : Nat) (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) n),
          let R := @BfgsVerification.DEmbedding.run n hn c₁ c₂ hc₁ hc₁' hc hc₂;
          And
            (@Eq.{1} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@BfgsVerification.AdmissibleBFGSRun.H (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                BfgsVerification.DEmbedding.objective R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
              (@OfNat.ofNat.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                (@One.toOfNat1.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@Matrix.one.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                    (instDecidableEqFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.instZero Real.instOne))))
            (And
              (∀ (k : Nat),
                @Matrix.PosDef.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                  (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.commRing Real.partialOrder
                  instStarRingReal
                  (@BfgsVerification.AdmissibleBFGSRun.H (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.DEmbedding.objective R k))
              (And
                (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.DEmbedding.objective R)
                  (@Filter.atTop.{0} Nat Nat.instPreorder)
                  (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (BfgsVerification.DEmbedding.center n)))
                (And
                  (@Filter.Tendsto.{0, 0} Nat Real
                    (fun (k : Nat) =>
                      BfgsVerification.DEmbedding.objective
                        (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                          BfgsVerification.DEmbedding.objective R k))
                    (@Filter.atTop.{0} Nat Nat.instPreorder)
                    (@nhds.{0} Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (BfgsVerification.DEmbedding.objective (BfgsVerification.DEmbedding.center n))))
                  (And
                    (∀ (k : Nat),
                      @LT.lt.{0} Real Real.instLT
                        (BfgsVerification.DEmbedding.objective (BfgsVerification.DEmbedding.center n))
                        (BfgsVerification.DEmbedding.objective
                          (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                            BfgsVerification.DEmbedding.objective R k)))
                    (And
                      (∀ (k : Nat),
                        @LT.lt.{0} Real Real.instLT
                          (BfgsVerification.DEmbedding.objective
                            (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              BfgsVerification.DEmbedding.objective R
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
                          (BfgsVerification.DEmbedding.objective
                            (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              BfgsVerification.DEmbedding.objective R k)))
                      (And
                        (∀ (k : Nat),
                          @Eq.{1} (Prod.{0, 0} (Option.{0} Real) (List.{0} Real))
                            (@BfgsVerification.DeterministicLineSearch.fromMetric
                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) BfgsVerification.DEmbedding.objective
                              (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                BfgsVerification.DEmbedding.objective R k)
                              (@BfgsVerification.AdmissibleBFGSRun.H (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                BfgsVerification.DEmbedding.objective R k)
                              c₁ c₂ (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                            (@Prod.mk.{0, 0} (Option.{0} Real) (List.{0} Real)
                              (@Option.some.{0} Real
                                (@BfgsVerification.AdmissibleBFGSRun.α (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                  BfgsVerification.DEmbedding.objective R k))
                              (BfgsVerification.SeedOrbit.trialHistory (BfgsVerification.SeedOrbit.phase k))))
                        (And
                          (∀ (k : Nat),
                            @LE.le.{0} Nat instLENat
                              (@List.length.{0} Real
                                (BfgsVerification.SeedOrbit.trialHistory (BfgsVerification.SeedOrbit.phase k)))
                              (@OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))
                          (And
                            (∀ (k : Nat) (q : Fin (@OfNat.ofNat.{0} Nat 9 (instOfNatNat 9))),
                              @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))
                                  (BfgsVerification.SeedOrbit.trialPhase q) (BfgsVerification.SeedOrbit.phase k) →
                                @HasFDerivAt.{0, 0, 0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
                                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
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
                                  BfgsVerification.DEmbedding.objective
                                  (@BfgsVerification.gradientFunctional (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                    (@HSMul.hSMul.{0, 0, 0} Real
                                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (@instHSMul.{0, 0} Real
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                          Real Real
                                          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                            (@Algebra.id.{0} Real Real.instCommSemiring))))
                                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                        (BfgsVerification.DScalarGeometric.scale n)
                                        (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (BfgsVerification.SeedOrbit.gradient BfgsVerification.SeedOrbit.seedC
                                        BfgsVerification.SeedOrbit.seedD (BfgsVerification.SeedOrbit.trialActive q))))
                                  (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (@instHAdd.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (@Pi.instAdd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAdd))
                                    (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                      BfgsVerification.DEmbedding.objective R k)
                                    (@HSMul.hSMul.{0, 0, 0} Real
                                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (@instHSMul.{0, 0} Real
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                          Real Real
                                          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                            (@Algebra.id.{0} Real Real.instCommSemiring))))
                                      (BfgsVerification.SeedOrbit.trialLength q)
                                      (@BfgsVerification.bfgsStep (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                        (@BfgsVerification.AdmissibleBFGSRun.H (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                          BfgsVerification.DEmbedding.objective R k)
                                        (@BfgsVerification.AdmissibleBFGSRun.g (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                          BfgsVerification.DEmbedding.objective R k)
                                        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))))))
                            (∀ (m : Nat) (j : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))),
                              And
                                (@Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                    BfgsVerification.DEmbedding.objective R
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) m)
                                      (@Fin.val (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) j)))
                                  (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (@instHAdd.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (@Pi.instAdd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAdd))
                                    (BfgsVerification.DEmbedding.center n)
                                    (@HSMul.hSMul.{0, 0, 0} Real
                                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (@instHSMul.{0, 0} Real
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                          Real Real
                                          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                            (@Algebra.id.{0} Real Real.instCommSemiring))))
                                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                        (BfgsVerification.DScalarGeometric.scale n)
                                        (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (@HSMul.hSMul.{0, 0, 0} Real
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (@instHSMul.{0, 0} Real
                                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                          (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                            Real Real
                                            (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                              (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                              (@Algebra.id.{0} Real Real.instCommSemiring))))
                                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                          BfgsVerification.SeedOrbit.seedRatio m)
                                        (BfgsVerification.SeedOrbit.point BfgsVerification.SeedOrbit.seedC
                                          BfgsVerification.SeedOrbit.seedD BfgsVerification.SeedOrbit.seedRatio j)))))
                                (And
                                  (@Eq.{1} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (@BfgsVerification.AdmissibleBFGSRun.H (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                      BfgsVerification.DEmbedding.objective R
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) m)
                                        (@Fin.val (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) j)))
                                    (@HSMul.hSMul.{0, 0, 0} Real
                                      (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (@instHSMul.{0, 0} Real
                                        (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (@Matrix.smul.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                          (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                            (@Algebra.id.{0} Real Real.instCommSemiring))))
                                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                        BfgsVerification.SeedOrbit.seedRatio m)
                                      (BfgsVerification.SeedOrbit.metric BfgsVerification.SeedOrbit.seedC
                                        BfgsVerification.SeedOrbit.seedD j)))
                                  (And
                                    (@Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (@BfgsVerification.AdmissibleBFGSRun.g (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                        BfgsVerification.DEmbedding.objective R
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) m)
                                          (@Fin.val (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) j)))
                                      (@HSMul.hSMul.{0, 0, 0} Real
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (@instHSMul.{0, 0} Real
                                          (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                          (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                            Real Real
                                            (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                              (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                              (@Algebra.id.{0} Real Real.instCommSemiring))))
                                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                          (BfgsVerification.DScalarGeometric.scale n)
                                          (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (BfgsVerification.SeedOrbit.gradient BfgsVerification.SeedOrbit.seedC
                                          BfgsVerification.SeedOrbit.seedD j)))
                                    (@Eq.{1} Real
                                      (@BfgsVerification.AdmissibleBFGSRun.α (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                        BfgsVerification.DEmbedding.objective R
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) m)
                                          (@Fin.val (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) j)))
                                      (BfgsVerification.SeedOrbit.length j)))))))))))))))))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.deterministicSeedFailure, ``EJob03.Contract01),
    (``BfgsVerification.allSeedTrials, ``EJob03.Contract02),
    (``BfgsVerification.DEmbedding.embeddingFailure, ``EJob03.Contract03)]
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
