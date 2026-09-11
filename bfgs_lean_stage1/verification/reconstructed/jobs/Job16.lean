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

def EJob16.Contract01 : Prop :=
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

def EJob16.Contract02 : Prop :=
∀ {n : Nat} {F : BfgsVerification.Vec n → Real} (R : BfgsVerification.AdmissibleBFGSRun n F) {r p : Nat} (J : Nat)
  (G : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) G →
    (∀ (k : Nat),
        @LE.le.{0} Real Real.instLE (@BfgsVerification.sqNorm n (@BfgsVerification.AdmissibleBFGSRun.g n F R k))
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) G
            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) →
      @Summable.{0, 0} Real Nat Real.instAddCommMonoid
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@BfgsVerification.AdmissibleBFGSRun.d n F R) →
        ∀ (U : Matrix.{0, 0, 0} (Fin n) (Fin r) Real),
          @Eq.{1} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
              (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin r) (Fin n) Real) (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
                (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin r) (Fin n) (Fin r) Real (Fin.fintype n)
                  Real.instMul Real.instAddCommMonoid)
                (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin r) Real U) U)
              (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real) 1
                (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
                  (@Matrix.one.{0, 0} (Fin r) Real (instDecidableEqFin r) Real.instZero Real.instOne))) →
            ∀ (L m C₀ C_T C_R : Real),
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) m →
                (∀ (k : Nat),
                    @LE.le.{0} Real Real.instLE
                      (@BfgsVerification.sqNorm r
                        (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                          (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                  (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                          (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin r) Real U)
                          (@BfgsVerification.AdmissibleBFGSRun.gradientChange n F
                            (@BfgsVerification.AdmissibleBFGSRun.shift n F R J) k)))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) L
                        (@BfgsVerification.AdmissibleBFGSRun.curvature n F
                          (@BfgsVerification.AdmissibleBFGSRun.shift n F R J) k))) →
                  ∀ (V Z : Nat → Matrix.{0, 0, 0} (Fin n) (Fin p) Real) (T : Nat → BfgsVerification.Mat p)
                    (b : Nat → BfgsVerification.Vec p),
                    (∀ (k : Nat),
                        @LE.le.{0} Real Real.instLE m
                          (@BfgsVerification.sqNorm p
                            (@Matrix.mulVec.{0, 0, 0} (Fin p) (Fin n) Real
                              (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                    (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                      (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                              (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin p) Real (V k))
                              (@BfgsVerification.AdmissibleBFGSRun.g n F
                                (@BfgsVerification.AdmissibleBFGSRun.shift n F R J) k)))) →
                      (∀ (k : Nat),
                          @LE.le.{0} Real Real.instLE
                            (@BfgsVerification.sqNorm p
                              (@Matrix.mulVec.{0, 0, 0} (Fin p) (Fin n) Real
                                (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                      (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                        (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                                (Fin.fintype n)
                                (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin p) Real
                                  (V
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
                                (@BfgsVerification.AdmissibleBFGSRun.gradientChange n F
                                  (@BfgsVerification.AdmissibleBFGSRun.shift n F R J) k)))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C₀
                              (@BfgsVerification.AdmissibleBFGSRun.curvature n F
                                (@BfgsVerification.AdmissibleBFGSRun.shift n F R J) k))) →
                        (∀ (k : Nat),
                            @Eq.{1} (Matrix.{0, 0, 0} (Fin n) (Fin p) Real)
                              (V
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                  (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
                              (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin p) Real)
                                (Matrix.{0, 0, 0} (Fin n) (Fin p) Real) (Matrix.{0, 0, 0} (Fin n) (Fin p) Real)
                                (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin n) (Fin p) Real)
                                  (@Matrix.add.{0, 0, 0} (Fin n) (Fin p) Real Real.instAdd))
                                (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin p) Real)
                                  (Matrix.{0, 0, 0} (Fin n) (Fin p) Real) (Matrix.{0, 0, 0} (Fin n) (Fin p) Real)
                                  (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin n) (Fin p) Real)
                                    (@Matrix.add.{0, 0, 0} (Fin n) (Fin p) Real Real.instAdd))
                                  (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin p) Real) (BfgsVerification.Mat p)
                                    (Matrix.{0, 0, 0} (Fin n) (Fin p) Real)
                                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin p) (Fin p)
                                      Real (Fin.fintype p) Real.instMul Real.instAddCommMonoid)
                                    (V k) (T k))
                                  (@BfgsVerification.EnergyIdentities.rectOuter n p
                                    (@BfgsVerification.AdmissibleBFGSRun.displacement n F
                                      (@BfgsVerification.AdmissibleBFGSRun.shift n F R J) k)
                                    (b k)))
                                (Z k))) →
                          (∀ (k : Nat),
                              @BfgsVerification.FrameBounds.OperatorSqBound p (T k)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C_T
                                    (@BfgsVerification.AdmissibleBFGSRun.d n F
                                      (@BfgsVerification.AdmissibleBFGSRun.shift n F R J) k)))) →
                            (∀ (k : Nat),
                                @Eq.{1} (Matrix.{0, 0, 0} (Fin n) (Fin p) Real)
                                  (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                                    (Matrix.{0, 0, 0} (Fin n) (Fin p) Real) (Matrix.{0, 0, 0} (Fin n) (Fin p) Real)
                                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin p)
                                      Real (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                                    (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
                                      (Matrix.{0, 0, 0} (Fin r) (Fin n) Real) (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                                      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin r)
                                        (Fin n) Real (Fin.fintype r) Real.instMul Real.instAddCommMonoid)
                                      U (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin r) Real U))
                                    (Z k))
                                  (Z k)) →
                              (∀ (k : Nat),
                                  @LE.le.{0} Real Real.instLE (@BfgsVerification.SmoothSubspace.frobSq n p (Z k))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C_R
                                      (@BfgsVerification.AdmissibleBFGSRun.d n F
                                        (@BfgsVerification.AdmissibleBFGSRun.shift n F R J) k))) →
                                False

def EJob16.Contract03 : Prop :=
∀ {n : Nat} (R : BfgsVerification.FullBFGSRun n) (G c : Real),
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
            ∀ (J m : Nat),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) m →
                ∀ (η : Real),
                  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) η →
                    let D :=
                      @tsum.{0, 0} Real Real.instAddCommMonoid
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        Nat fun (i : Nat) =>
                        @BfgsVerification.FullBFGSRun.d n R
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J i);
                    let V :=
                      BfgsVerification.ScalarHierarchy.weightedPotential n
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
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
                          η)
                        (@BfgsVerification.principalSum n (@BfgsVerification.FullBFGSRun.H n R J));
                    @LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
                          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) G
                                (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              V)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@Neg.neg.{0} Real Real.instNeg
                                (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
                              (@Nat.cast.{0} Real Real.instNatCast
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                  (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
                        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) η
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) D
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                                (@Nat.cast.{0} Real Real.instNatCast m))))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast m))
                            (@Nat.cast.{0} Real Real.instNatCast
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
                      (∑
                        i ∈
                          Finset.range
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))),
                        @Inv.inv.{0} Real Real.instInv
                          (@BfgsVerification.FullBFGSRun.q n R
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J i)))

def EJob16.Contract04 : Prop :=
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

def EJob16.Contract05 : Prop :=
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

def EJob16.Contract06 : Prop :=
∀ {n r : Nat} (U : Matrix.{0, 0, 0} (Fin n) (Fin r) Real) (a x z : BfgsVerification.Vec n) (b : Real) (τ : Real → Real),
  let β :=
    BfgsVerification.FixedNormal.cutoffSlope τ
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@BfgsVerification.dot n a x) b)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@BfgsVerification.dot n a z) b);
  @Eq.{1}
    (Matrix.{0, 0, 0} (Fin n)
      (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
      Real)
    (@BfgsVerification.FixedNormal.cutoffFrame n r U a
      (τ (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@BfgsVerification.dot n a z) b)))
    (@HAdd.hAdd.{0, 0, 0}
      (Matrix.{0, 0, 0} (Fin n)
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
        Real)
      (Matrix.{0, 0, 0} (Fin n)
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
        Real)
      (Matrix.{0, 0, 0} (Fin n)
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
        Real)
      (@instHAdd.{0}
        (Matrix.{0, 0, 0} (Fin n)
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
              (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
          Real)
        (@Matrix.add.{0, 0, 0} (Fin n)
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
              (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
          Real Real.instAdd))
      (@HAdd.hAdd.{0, 0, 0}
        (Matrix.{0, 0, 0} (Fin n)
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
              (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
          Real)
        (Matrix.{0, 0, 0} (Fin n)
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
              (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
          Real)
        (Matrix.{0, 0, 0} (Fin n)
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
              (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
          Real)
        (@instHAdd.{0}
          (Matrix.{0, 0, 0} (Fin n)
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            Real)
          (@Matrix.add.{0, 0, 0} (Fin n)
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            Real Real.instAdd))
        (@HMul.hMul.{0, 0, 0}
          (Matrix.{0, 0, 0} (Fin n)
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            Real)
          (BfgsVerification.Mat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
              (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
          (Matrix.{0, 0, 0} (Fin n)
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            Real)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n)
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            Real
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            Real.instMul Real.instAddCommMonoid)
          (@BfgsVerification.FixedNormal.cutoffFrame n r U a
            (τ (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@BfgsVerification.dot n a x) b)))
          (@OfNat.ofNat.{0}
            (BfgsVerification.Mat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            1
            (@One.toOfNat1.{0}
              (BfgsVerification.Mat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                  (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
              (@Matrix.one.{0, 0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
                Real
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
                Real.instZero Real.instOne))))
        (@BfgsVerification.EnergyIdentities.rectOuter n
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
          (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n) (BfgsVerification.Vec n)
            (@instHSub.{0} (BfgsVerification.Vec n)
              (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
            z x)
          (@BfgsVerification.FixedNormal.normalCoefficient r β)))
      (@BfgsVerification.FixedNormal.cutoffResidual n r a
        (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n) (BfgsVerification.Vec n)
          (@instHSub.{0} (BfgsVerification.Vec n)
            (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
          z x)
        β))

def EJob16.Contract07 : Prop :=
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

def EJob16.Contract08 : Prop :=
∀ (N : Nat),
  @Eq.{1} Real
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
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        BfgsVerification.NormalSpike.sourcePrimitive)
      (BfgsVerification.NormalSpike.scale N))
    (@Inv.inv.{0} Real Real.instInv
      (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
        (BfgsVerification.NormalSpike.scale N) (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))

def EJob16.Contract09 : Prop :=
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

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.fixedNormalHyperplane, ``EJob16.Contract01),
    (``BfgsVerification.AdmissibleBFGSRun.residual_frames_on_tail_incompatible_source, ``EJob16.Contract02),
    (``BfgsVerification.finiteHorizon, ``EJob16.Contract03),
    (``BfgsVerification.NormalSpike.sourceSpikeProperties, ``EJob16.Contract04),
    (``BfgsVerification.NormalSpike.spikeObjectiveConvergence, ``EJob16.Contract05),
    (``BfgsVerification.FixedNormal.cutoffFrame_transport, ``EJob16.Contract06),
    (``BfgsVerification.NormalSpike.rationalSpikeOracle, ``EJob16.Contract07),
    (``BfgsVerification.NormalSpike.sourcePrimitive_second_derivative_peak, ``EJob16.Contract08),
    (``BfgsVerification.principalMinorHierarchy, ``EJob16.Contract09)]
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
