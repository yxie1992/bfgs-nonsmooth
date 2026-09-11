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

def EJob08.Contract01 : Prop :=
∀ (n : Nat) (H : BfgsVerification.Mat n) (g y : BfgsVerification.Vec n) (α : Real),
  @Matrix.PosDef.{0, 0} (Fin n) Real (Fin.fintype n) Real.commRing Real.partialOrder instStarRingReal H →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) α →
      let q := @BfgsVerification.metricEnergy n H g;
      let β :=
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Neg.neg.{0} Real Real.instNeg
            (@BfgsVerification.dot n y
              (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
                (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                      (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                        (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                (Fin.fintype n) H g)))
          q;
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) q →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) β →
          ∀ (j : Nat),
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) j →
              @LE.le.{0} Nat instLENat j n →
                @LE.le.{0} Real Real.instLE
                  (@BfgsVerification.principalSum n
                    (@BfgsVerification.inverseBFGS n H (@BfgsVerification.bfgsStep n H g α) y) j)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@BfgsVerification.sqNorm n y)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) β
                            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          q))
                      (@BfgsVerification.principalSum n H
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) α β)
                      (@BfgsVerification.principalSum n H j)))

def EJob08.Contract02 : Prop :=
∀ (n : Nat) (R : BfgsVerification.FullBFGSRun n) (G c : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) c →
    @Summable.{0, 0} Real Nat Real.instAddCommMonoid
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@BfgsVerification.FullBFGSRun.d n R) →
      ∀ (J : Nat),
        let D :=
          @tsum.{0, 0} Real Real.instAddCommMonoid
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            Nat fun (i : Nat) =>
            @BfgsVerification.FullBFGSRun.d n R (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J i);
        let K :=
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real 4
                (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                  BfgsVerification.SharpPrincipalPotentialTarget._proof_1))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) G
                (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              c (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)));
        ∃ (p : @Polynomial.{0} Real Real.semiring),
          And
            (@LE.le.{0} Nat instLENat (@Polynomial.natDegree.{0} Real Real.semiring p)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            (And
              (∀ (m : Nat),
                @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) m →
                  And
                    (@Eq.{1} Real
                      (BfgsVerification.ScalarHierarchy.weightedPotential n
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) K
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) D
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                (@Nat.cast.{0} Real Real.instNatCast m)
                                (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))))))
                        (@BfgsVerification.principalSum n (@BfgsVerification.FullBFGSRun.H n R J)))
                      (@Polynomial.eval.{0} Real Real.semiring
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@Nat.cast.{0} Real Real.instNatCast m)
                          (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
                        p))
                    (@LE.le.{0} Real Real.instLE
                      (BfgsVerification.ScalarHierarchy.weightedPotential n
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) K
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) D
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                (@Nat.cast.{0} Real Real.instNatCast m)
                                (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))))))
                        (@BfgsVerification.principalSum n (@BfgsVerification.FullBFGSRun.H n R J)))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (BfgsVerification.ScalarHierarchy.weightedPotential n
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) K
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) D c))
                          (@BfgsVerification.principalSum n (@BfgsVerification.FullBFGSRun.H n R J)))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (@Nat.cast.{0} Real Real.instNatCast m)
                            (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                            (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
              (@Filter.Tendsto.{0, 0} Nat Real
                (fun (m : Nat) =>
                  @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                    (BfgsVerification.ScalarHierarchy.weightedPotential n
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) K
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) D
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (@Nat.cast.{0} Real Real.instNatCast m)
                              (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))))))
                      (@BfgsVerification.principalSum n (@BfgsVerification.FullBFGSRun.H n R J)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                      (@Nat.cast.{0} Real Real.instNatCast m)))
                (@Filter.atTop.{0} Nat Nat.instPreorder)
                (@nhds.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))))

def EJob08.Contract03 : Prop :=
∀ (Δ q u r z κ w : Real),
  @Eq.{1} Real
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) q
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Δ
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) r z)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Δ
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) q u)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) r z))
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) κ w)
            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Δ
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) κ w)
          (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) r z))))

def EJob08.Contract04 : Prop :=
∀ (A : Real) {ρ v₀ : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) ρ →
    @LT.lt.{0} Real Real.instLT ρ (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) →
      @Filter.Tendsto.{0, 0} Nat (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (fun (k : Nat) =>
          BfgsVerification.UnexcitedMetric.diagonal A
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) ρ)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real 2
                    (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                      (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
                  ρ))
              (BfgsVerification.UnexcitedMetric.radius ρ v₀ k)))
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@instTopologicalSpaceMatrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
          (BfgsVerification.UnexcitedMetric.diagonal A
            (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))

def EJob08.Contract05 : Prop :=
∀ {n : Nat} (R : BfgsVerification.FullBFGSRun n) (G c : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) G →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) c →
      (∀ (k : Nat),
          @LE.le.{0} Real Real.instLE (@BfgsVerification.sqNorm n (@BfgsVerification.FullBFGSRun.g n R k))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              G (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) →
        (∀ (k : Nat), @LE.le.{0} Real Real.instLE c (@BfgsVerification.FullBFGSRun.beta n R k)) →
          BfgsVerification.ScalarHierarchy.NormalizedHierarchy n
            (fun (k : Nat) => @BfgsVerification.principalSum n (@BfgsVerification.FullBFGSRun.H n R k))
            (@BfgsVerification.FullBFGSRun.q n R)
            (fun (k : Nat) =>
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@BfgsVerification.FullBFGSRun.d n R k) c)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real 4
                  (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                    (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) G
                  (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) c
                (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              G (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))

def EJob08.Contract06 : Prop :=
∀ {n m : Nat} (H : BfgsVerification.Mat n) (Z : Matrix.{0, 0, 0} (Fin n) (Fin m) Real) (g y : BfgsVerification.Vec n)
  (α : Real),
  @Matrix.IsSymm.{0, 0} Real (Fin n) H →
    @Ne.{1} Real α (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @Ne.{1} Real (@BfgsVerification.metricEnergy n H g)
          (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Ne.{1} Real
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Neg.neg.{0} Real Real.instNeg
                (@BfgsVerification.dot n y
                  (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) H g)))
              (@BfgsVerification.metricEnergy n H g))
            (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) →
          let q := @BfgsVerification.metricEnergy n H g;
          let β :=
            @HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Neg.neg.{0} Real Real.instNeg
                (@BfgsVerification.dot n y
                  (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) H g)))
              q;
          @Eq.{1} (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
            (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin m) (Fin n) Real) (Matrix.{0, 0, 0} (Fin n) (Fin m) Real)
              (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin m) (Fin n) (Fin m) Real (Fin.fintype n)
                Real.instMul Real.instAddCommMonoid)
              (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin m) (Fin n) Real) (BfgsVerification.Mat n)
                (Matrix.{0, 0, 0} (Fin m) (Fin n) Real)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin m) (Fin n) (Fin n) Real (Fin.fintype n)
                  Real.instMul Real.instAddCommMonoid)
                (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin m) Real Z)
                (@BfgsVerification.inverseBFGS n H (@BfgsVerification.bfgsStep n H g α) y))
              Z)
            (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Mat m) (BfgsVerification.Mat m) (BfgsVerification.Mat m)
              (@instHAdd.{0} (BfgsVerification.Mat m) (@Matrix.add.{0, 0, 0} (Fin m) (Fin m) Real Real.instAdd))
              (@BfgsVerification.CompressionDeterminant.compression m
                (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin m) (Fin n) Real) (Matrix.{0, 0, 0} (Fin n) (Fin m) Real)
                  (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin m) (Fin n) (Fin m) Real
                    (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                  (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin m) (Fin n) Real) (BfgsVerification.Mat n)
                    (Matrix.{0, 0, 0} (Fin m) (Fin n) Real)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin m) (Fin n) (Fin n) Real
                      (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                    (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin m) Real Z) H)
                  Z)
                (@Matrix.mulVec.{0, 0, 0} (Fin m) (Fin n) Real
                  (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                        (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                          (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                  (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin m) Real Z)
                  (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) H g))
                (@Matrix.mulVec.{0, 0, 0} (Fin m) (Fin n) Real
                  (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                        (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                          (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                  (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin m) Real Z)
                  (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) H y))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Neg.neg.{0} Real Real.instNeg β) q)
                (@BfgsVerification.dot n y
                  (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) H y)))
              (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Mat m) (BfgsVerification.Mat m)
                (@instHSMul.{0, 0} Real (BfgsVerification.Mat m)
                  (@Matrix.smul.{0, 0, 0, 0} (Fin m) (Fin m) Real Real
                    (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                      (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                      (@Algebra.id.{0} Real Real.instCommSemiring))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) α
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) β q))
                (@BfgsVerification.outer m
                  (@Matrix.mulVec.{0, 0, 0} (Fin m) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin m) Real Z)
                    (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
                      (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                            (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                              (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                      (Fin.fintype n) H g))
                  (@Matrix.mulVec.{0, 0, 0} (Fin m) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin m) Real Z)
                    (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
                      (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                            (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                              (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                      (Fin.fintype n) H g)))))

def EJob08.Contract07 : Prop :=
∀ (n : Nat) (R : BfgsVerification.FullBFGSRun n) (G c : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) G →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) c →
      (∀ (k : Nat),
          @LE.le.{0} Real Real.instLE (@BfgsVerification.sqNorm n (@BfgsVerification.FullBFGSRun.g n R k))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              G (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) →
        (∀ (k : Nat), @LE.le.{0} Real Real.instLE c (@BfgsVerification.FullBFGSRun.beta n R k)) →
          @Filter.Tendsto.{0, 0} Nat Real (@BfgsVerification.FullBFGSRun.d n R) (@Filter.atTop.{0} Nat Nat.instPreorder)
              (@nhds.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))) →
            And
              (@Filter.Tendsto.{0, 0} Nat Real
                (BfgsVerification.reciprocalGeometricMean (@BfgsVerification.FullBFGSRun.q n R))
                (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder))
              (@Filter.Tendsto.{0, 0} Nat Real (BfgsVerification.reciprocalMean (@BfgsVerification.FullBFGSRun.q n R))
                (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder))

def EJob08.Contract08 : Prop :=
∀ (n : Nat) (R : BfgsVerification.FullBFGSRun n) (G c : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) G →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) c →
      (∀ (k : Nat),
          @LE.le.{0} Real Real.instLE (@BfgsVerification.sqNorm n (@BfgsVerification.FullBFGSRun.g n R k))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              G (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) →
        (∀ (k : Nat), @LE.le.{0} Real Real.instLE c (@BfgsVerification.FullBFGSRun.beta n R k)) →
          @Summable.{0, 0} Real Nat Real.instAddCommMonoid
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@BfgsVerification.FullBFGSRun.d n R) →
            @Filter.Tendsto.{0, 0} Nat Real
              (fun (N : Nat) =>
                @HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (∑ k ∈ Finset.range N, @Inv.inv.{0} Real Real.instInv (@BfgsVerification.FullBFGSRun.q n R k))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N) (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
              (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder)

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.principalMinorHierarchy, ``EJob08.Contract01),
    (``BfgsVerification.sharpPrincipalPotential, ``EJob08.Contract02),
    (``BfgsVerification.CompressionAlgebra.gram_numerator_identity, ``EJob08.Contract03),
    (``BfgsVerification.UnexcitedMetric.literal_matrix_limit, ``EJob08.Contract04),
    (``BfgsVerification.fullBFGS_normalizedHierarchy, ``EJob08.Contract05),
    (``BfgsVerification.BFGSCompression.inverseBFGS_compression, ``EJob08.Contract06),
    (``BfgsVerification.reciprocalGrowth, ``EJob08.Contract07),
    (``BfgsVerification.superquadraticReciprocalGrowth, ``EJob08.Contract08)]
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
