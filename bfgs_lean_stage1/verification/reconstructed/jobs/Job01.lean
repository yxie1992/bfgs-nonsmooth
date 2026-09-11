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

def EJob01.Contract01 : Prop :=
@ExistsUnique.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
  fun (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
  And
    (∀ (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (x i)
            (BfgsVerification.AlgebraicSeed.center i)))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (@OfNat.ofNat.{0} Real 10
              (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast BfgsVerification.AlgebraicSeedRootTarget._proof_3))
            (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30)))))
    (And
      (@Eq.{1} Real
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real 264192
                (@instOfNatAtLeastTwo.{0} Real 264192 Real.instNatCast
                  BfgsVerification.AlgebraicSeedRootTarget._proof_4))
              (BfgsVerification.AlgebraicSeed.R
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
            (BfgsVerification.AlgebraicSeed.K
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (BfgsVerification.AlgebraicSeed.U
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 1))))
              (BfgsVerification.AlgebraicSeed.V
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (BfgsVerification.AlgebraicSeed.U
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 1))))
              (@OfNat.ofNat.{0} Real 129
                (@instOfNatAtLeastTwo.{0} Real 129 Real.instNatCast
                  BfgsVerification.AlgebraicSeedRootTarget._proof_5)))))
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))
      (@Eq.{1} Real
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real 16
                  (@instOfNatAtLeastTwo.{0} Real 16 Real.instNatCast BfgsVerification.AlgebraicSeedRootTarget._proof_6))
                (BfgsVerification.AlgebraicSeed.V
                  (x
                    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                        BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                  (x
                    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                        BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
              (BfgsVerification.AlgebraicSeed.T
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
            (BfgsVerification.AlgebraicSeed.K
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (BfgsVerification.AlgebraicSeed.R
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 1))))
              (BfgsVerification.AlgebraicSeed.U
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
            (BfgsVerification.AlgebraicSeed.Y
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.UnexcitedMetricTarget._proof_2 1))))))
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))

def EJob01.Contract02 : Prop :=
∀ {x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))},
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
    And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
        (BfgsVerification.AlgebraicSeed.U
          (x
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) BfgsVerification.UnexcitedMetricTarget._proof_2
                0)))
          (x
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) BfgsVerification.UnexcitedMetricTarget._proof_2
                1)))))
      (And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
          (BfgsVerification.AlgebraicSeed.V
            (x
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                  BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
            (x
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                  BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
        (And
          (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
            (BfgsVerification.AlgebraicSeed.R
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
          (And
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
              (BfgsVerification.AlgebraicSeed.K
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
            (And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                (BfgsVerification.AlgebraicSeed.T
                  (x
                    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                        BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                  (x
                    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                        BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
              (And
                (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                  (BfgsVerification.AlgebraicSeed.Y
                    (x
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                          BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                    (x
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                          BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
                (And
                  (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (BfgsVerification.AlgebraicSeed.U
                        (x
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                        (x
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              BfgsVerification.UnexcitedMetricTarget._proof_2 1))))
                      (@OfNat.ofNat.{0} Real 129
                        (@instOfNatAtLeastTwo.{0} Real 129 Real.instNatCast
                          BfgsVerification.AlgebraicSeedRootTarget._proof_5))))
                  (And
                    (@LT.lt.{0} Real Real.instLT
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real 60
                          (@instOfNatAtLeastTwo.{0} Real 60 Real.instNatCast
                            BfgsVerification.AlgebraicSeedBoundsTarget._proof_7))
                        (@OfNat.ofNat.{0} Real 1000
                          (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
                            BfgsVerification.AlgebraicSeedBoundsTarget._proof_8)))
                      (BfgsVerification.AlgebraicSeed.ratio
                        (x
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                        (x
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              BfgsVerification.UnexcitedMetricTarget._proof_2 1)))))
                    (@LT.lt.{0} Real Real.instLT
                      (BfgsVerification.AlgebraicSeed.ratio
                        (x
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              BfgsVerification.UnexcitedMetricTarget._proof_2 0)))
                        (x
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              BfgsVerification.UnexcitedMetricTarget._proof_2 1))))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real 61
                          (@instOfNatAtLeastTwo.{0} Real 61 Real.instNatCast
                            BfgsVerification.AlgebraicSeedBoundsTarget._proof_9))
                        (@OfNat.ofNat.{0} Real 1000
                          (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
                            BfgsVerification.AlgebraicSeedBoundsTarget._proof_8)))))))))))

def EJob01.Contract03 : Prop :=
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

def EJob01.Contract04 : Prop :=
And
  (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
    @Eq.{1} Real (BfgsVerification.DEmbedding.objective x)
      (@Finset.sup'.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) Real.instSemilatticeSup
        (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)))
          (Fin.fintype (@OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))))
        BfgsVerification.DEmbedding.ObjectiveGeometryTarget._proof_1
        fun (i : Fin (@OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))) => BfgsVerification.DEmbedding.branch i x))
  (And
    (∀ (i : Fin (@OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))),
      And
        (@ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real.semiring
          Real.partialOrder
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
          Real.instAddCommMonoid Real.partialOrder
          (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
            (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
              (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
          (@Set.univ.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
          (BfgsVerification.DEmbedding.branch i))
        (@ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
              BfgsVerification.DEmbedding.ObjectiveGeometryTarget._proof_2))
          (BfgsVerification.DEmbedding.branch i)))
    (And
      (@ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real.semiring
        Real.partialOrder
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
        Real.instAddCommMonoid Real.partialOrder
        (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
        (@Set.univ.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
        BfgsVerification.DEmbedding.objective)
      (And
        (@Eq.{1} Real
          (BfgsVerification.DEmbedding.objective
            (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
              (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))
          (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))
        (And
          (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
              (BfgsVerification.DEmbedding.objective x))
          (And
            (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
              Iff
                (@Eq.{1} Real (BfgsVerification.DEmbedding.objective x)
                  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))
                (@Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) x
                  (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)))))
            (And
              (∀ (a : Real),
                @IsCompact.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@setOf.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    fun (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                    @LE.le.{0} Real Real.instLE (BfgsVerification.DEmbedding.objective x) a))
              (And
                (Not
                  (@DifferentiableAt.{0, 0, 0} Real
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
                    BfgsVerification.DEmbedding.objective
                    (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                      (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)))))
                (And
                  (∀ (h : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                    @Filter.Tendsto.{0, 0} Real Real
                      (fun (t : Real) =>
                        @HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (BfgsVerification.DEmbedding.objective
                              (@HSMul.hSMul.{0, 0, 0} Real
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@instHSMul.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                    (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                      (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                      (@Algebra.id.{0} Real Real.instCommSemiring))))
                                t h))
                            (BfgsVerification.DEmbedding.objective
                              (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                                (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)))))
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
                        (@Max.max.{0} Real Real.instMax
                          (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                          (h
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                BfgsVerification.DEmbedding.ObjectiveGeometryTarget._proof_3 1))))))
                  (And
                    (∀ (i : Fin (@OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)))
                      (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                      And
                        (@Matrix.PosSemidef.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                          (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.commRing Real.partialOrder
                          instStarRingReal
                          (@BfgsVerification.RadialHessian.matrix (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                            (BfgsVerification.DEmbedding.branch i) x))
                        (@Matrix.PosSemidef.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                          (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.commRing Real.partialOrder
                          instStarRingReal
                          (@HSub.hSub.{0, 0, 0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (@instHSub.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@Matrix.sub.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real.instSub))
                            (@HSMul.hSMul.{0, 0, 0} Real
                              (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@instHSMul.{0, 0} Real (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@Matrix.smul.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                  (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                    (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                    (@Algebra.id.{0} Real Real.instCommSemiring))))
                              (@OfNat.ofNat.{0} Real 64
                                (@instOfNatAtLeastTwo.{0} Real 64 Real.instNatCast
                                  BfgsVerification.DEmbedding.ObjectiveGeometryTarget._proof_4))
                              (@OfNat.ofNat.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                                (@One.toOfNat1.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Matrix.one.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                    (instDecidableEqFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.instZero
                                    Real.instOne))))
                            (@BfgsVerification.RadialHessian.matrix (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              (BfgsVerification.DEmbedding.branch i) x))))
                    (∀ (i : Fin (@OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)))
                      (x y : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                      @LE.le.{0} Real Real.instLE
                        (@BfgsVerification.FrameNorms.euclideanOpNorm (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                          (@HSub.hSub.{0, 0, 0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (@instHSub.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@Matrix.sub.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real.instSub))
                            (@BfgsVerification.RadialHessian.matrix (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              (BfgsVerification.DEmbedding.branch i) x)
                            (@BfgsVerification.RadialHessian.matrix (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              (BfgsVerification.DEmbedding.branch i) y)))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real 60000
                            (@instOfNatAtLeastTwo.{0} Real 60000 Real.instNatCast
                              BfgsVerification.DEmbedding.ObjectiveGeometryTarget._proof_5))
                          (@Norm.norm.{0} (EuclideanSpace.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                            (@PiLp.instNorm.{0, 0}
                              (@OfNat.ofNat.{0} ENNReal 2
                                (@instOfNatAtLeastTwo.{0} ENNReal 2
                                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                      instENNRealAddCommMonoidWithOne))
                                  PiLp.innerProductSpace._proof_2))
                              (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (x : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.norm)
                            (@BfgsVerification.euclideanVector (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@instHSub.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Pi.instSub.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instSub))
                                x y))))))))))))))

def EJob01.Contract05 : Prop :=
∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
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
    And
      (∀ (j : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))),
        And
          (@Matrix.PosDef.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
            (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.commRing Real.partialOrder instStarRingReal
            (BfgsVerification.SeedOrbit.metric
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 0)))
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 1)))
              j))
          (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
            (@BfgsVerification.metricEnergy (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              (BfgsVerification.SeedOrbit.metric
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 1)))
                j)
              (BfgsVerification.SeedOrbit.gradient
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 1)))
                j))))
      (And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
          (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
            (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@instHSub.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@Pi.instSub.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instSub))
              BfgsVerification.SeedCycle.g1 BfgsVerification.SeedCycle.g0)
            (@BfgsVerification.bfgsStep (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              (@OfNat.ofNat.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                (@One.toOfNat1.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@Matrix.one.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                    (instDecidableEqFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.instZero Real.instOne)))
              BfgsVerification.SeedCycle.g0 (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))))
        (And
          (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
            (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@instHSub.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@Pi.instSub.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instSub))
                (BfgsVerification.SeedCycle.g2
                  (x
                    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                        BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 0)))
                  (x
                    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                        BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 1))))
                BfgsVerification.SeedCycle.g1)
              (@BfgsVerification.bfgsStep (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) BfgsVerification.SeedCycle.M1
                BfgsVerification.SeedCycle.g1
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                  (@OfNat.ofNat.{0} Real 4
                    (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                      BfgsVerification.DBoxDenominators.lastCurvature._proof_1))))))
          (And
            (@LT.lt.{0} Real Real.instLT
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real 100
                  (@instOfNatAtLeastTwo.{0} Real 100 Real.instNatCast
                    BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_4)))
              (BfgsVerification.DBoxDenominators.lastCurvature
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 0)))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 1)))))
            (And
              (@Matrix.PosDef.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.commRing Real.partialOrder instStarRingReal
                (BfgsVerification.SeedCycle.update
                  (BfgsVerification.SeedOrbit.metric
                    (x
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                          BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 0)))
                    (x
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                          BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 1)))
                    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) 2
                      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
                        BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_5 2)))
                  (BfgsVerification.SeedCycle.g2
                    (x
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                          BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 0)))
                    (x
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                          BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 1))))
                  BfgsVerification.SeedCycle.g0
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real 16
                      (@instOfNatAtLeastTwo.{0} Real 16 Real.instNatCast
                        BfgsVerification.DBoxDenominators.lastCurvature._proof_2)))))
              (And
                (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                  (BfgsVerification.AlgebraicSeed.ratio
                    (x
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                          BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 0)))
                    (x
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                          BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 1)))))
                (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                    (BfgsVerification.AlgebraicSeed.ratio
                      (x
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                            BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 0)))
                      (x
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                            BfgsVerification.DBoxDenominators.SourceBoxDenominatorsTarget._proof_3 1)))))))))))

def EJob01.Contract06 : Prop :=
And
  (∀ (n k : Nat),
    @LE.le.{0} Real Real.instLE
      (@Norm.norm.{0} (EuclideanSpace.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
        (@PiLp.instNorm.{0, 0}
          (@OfNat.ofNat.{0} ENNReal 2
            (@instOfNatAtLeastTwo.{0} ENNReal 2
              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instENNRealAddCommMonoidWithOne))
              PiLp.innerProductSpace._proof_2))
          (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (fun (x : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
          (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.norm)
        (@BfgsVerification.euclideanVector (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
          (BfgsVerification.SeedEmbedding.point (BfgsVerification.DEmbedding.center n)
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (BfgsVerification.DScalarGeometric.scale n) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            k)))
      (BfgsVerification.DEuclideanLocality.sourceBound n))
  (And
    (∀ (n k : Nat) (q : Fin (@OfNat.ofNat.{0} Nat 9 (instOfNatNat 9))),
      @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) (BfgsVerification.SeedOrbit.trialPhase q)
          (BfgsVerification.SeedOrbit.phase k) →
        @LE.le.{0} Real Real.instLE
          (@Norm.norm.{0} (EuclideanSpace.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
            (@PiLp.instNorm.{0, 0}
              (@OfNat.ofNat.{0} ENNReal 2
                (@instOfNatAtLeastTwo.{0} ENNReal 2
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instENNRealAddCommMonoidWithOne))
                  PiLp.innerProductSpace._proof_2))
              (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (x : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.norm)
            (@BfgsVerification.euclideanVector (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
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
          (BfgsVerification.DEuclideanLocality.sourceBound n))
    (@Filter.Tendsto.{0, 0} Nat Real BfgsVerification.DEuclideanLocality.sourceBound
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.algebraicSeedRoot, ``EJob01.Contract01),
    (``BfgsVerification.algebraicSeedBounds, ``EJob01.Contract02),
    (``BfgsVerification.allSeedTrials, ``EJob01.Contract03),
    (``BfgsVerification.DEmbedding.objectiveGeometry, ``EJob01.Contract04),
    (``BfgsVerification.DBoxDenominators.sourceBoxDenominators, ``EJob01.Contract05),
    (``BfgsVerification.DEuclideanLocality.euclideanLocality, ``EJob01.Contract06)]
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
