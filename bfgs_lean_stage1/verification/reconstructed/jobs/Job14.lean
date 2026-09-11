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

def EJob14.Contract01 : Prop :=
∀ {n : Nat} {F : BfgsVerification.Vec n → Real} (R : BfgsVerification.AdmissibleBFGSRun n F) (b : Real),
  @IsCompact.{0} (BfgsVerification.Vec n)
      (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
        @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@setOf.{0} (BfgsVerification.Vec n) fun (x : BfgsVerification.Vec n) => @LE.le.{0} Real Real.instLE (F x) b) →
    ∀ (star : BfgsVerification.Vec n),
      (∀ (x : BfgsVerification.Vec n), @LE.le.{0} Real Real.instLE (F star) (F x)) →
        @LE.le.{0} Real Real.instLE
            (F (@BfgsVerification.AdmissibleBFGSRun.x n F R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) b →
          @BfgsVerification.TransportedCertificate.HasBandCertificates n F
              (@setOf.{0} (BfgsVerification.Vec n) fun (x : BfgsVerification.Vec n) =>
                @LE.le.{0} Real Real.instLE (F x) b)
              (F star) (@BfgsVerification.AdmissibleBFGSRun.c₁ n F R) (@BfgsVerification.AdmissibleBFGSRun.c₂ n F R) →
            And
              (@Filter.Tendsto.{0, 0} Nat Real (fun (k : Nat) => F (@BfgsVerification.AdmissibleBFGSRun.x n F R k))
                (@Filter.atTop.{0} Nat Nat.instPreorder)
                (@nhds.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (F star)))
              (And
                (@Filter.Tendsto.{0, 0} Nat Real
                  (fun (k : Nat) =>
                    @BfgsVerification.euclideanSolutionDistance n F (@BfgsVerification.AdmissibleBFGSRun.x n F R k))
                  (@Filter.atTop.{0} Nat Nat.instPreorder)
                  (@nhds.{0} Real
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
                ((∀ (x : BfgsVerification.Vec n),
                    @Eq.{1} Real (F x) (F star) → @Eq.{1} (BfgsVerification.Vec n) x star) →
                  @Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec n) (@BfgsVerification.AdmissibleBFGSRun.x n F R)
                    (@Filter.atTop.{0} Nat Nat.instPreorder)
                    (@nhds.{0} (BfgsVerification.Vec n)
                      (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      star)))

def EJob14.Contract02 : Prop :=
∀ {n : Nat} {F : BfgsVerification.Vec n → Real} {K : Set.{0} (BfgsVerification.Vec n)} {fstar c₁ c₂ : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) c₁ →
    @LT.lt.{0} Real Real.instLT c₂ (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) →
      ∀ (b : Real),
        (∀ (x : BfgsVerification.Vec n),
            @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                (@Set.instMembership.{0} (BfgsVerification.Vec n)) K x →
              @LE.le.{0} Real Real.instLE (F x) b) →
          Iff (@BfgsVerification.TransportedCertificate.HasBandCertificates n F K fstar c₁ c₂)
            (∀ (η : Real),
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) η →
                @Set.Nonempty.{0} (BfgsVerification.Vec n)
                    (@BfgsVerification.TransportedCertificate.positiveBand n F K fstar η) →
                  ∃ (C : @BfgsVerification.TransportedCertificate.BandCertificate n F K fstar c₁ c₂ η),
                    @Eq.{1} Real (@BfgsVerification.TransportedCertificate.BandCertificate.L n F K fstar c₁ c₂ η C)
                      (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))

def EJob14.Contract03 : Prop :=
∀ {n : Nat} {F : BfgsVerification.Vec n → Real} (R : BfgsVerification.AdmissibleBFGSRun n F) {r : Nat}
  (V : Nat → Matrix.{0, 0, 0} (Fin n) (Fin r) Real) (T P : Nat → BfgsVerification.Mat r)
  (b : Nat → BfgsVerification.Vec r),
  (∀ (k : Nat),
      @Ne.{1} Real (@Matrix.det.{0, 0} (Fin r) (instDecidableEqFin r) (Fin.fintype r) Real Real.commRing (P k))
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))) →
    (∀ (k : Nat),
        @Eq.{1} (BfgsVerification.Mat r)
          (P
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
          (@HMul.hMul.{0, 0, 0} (BfgsVerification.Mat r) (BfgsVerification.Mat r)
            (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin r) (Fin r) (Fin r) Real (Fin.fintype r)
              Real.instMul Real.instAddCommMonoid)
            (P k) (T k))) →
      (∀ (k : Nat),
          @Eq.{1} (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
            (V
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin r) Real) (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
              (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
              (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
                (@Matrix.add.{0, 0, 0} (Fin n) (Fin r) Real Real.instAdd))
              (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin r) Real) (BfgsVerification.Mat r)
                (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin r) (Fin r) Real (Fin.fintype r)
                  Real.instMul Real.instAddCommMonoid)
                (V k) (T k))
              (@BfgsVerification.EnergyIdentities.rectOuter n r
                (@BfgsVerification.AdmissibleBFGSRun.displacement n F R k) (b k)))) →
        ∀ (k : Nat),
          @Eq.{1} Real
            (@BfgsVerification.AdmissibleBFGSRun.normalizedFrameEnergy n F R r V P
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@BfgsVerification.AdmissibleBFGSRun.normalizedFrameEnergy n F R r V P k)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@BfgsVerification.sqNorm r
                    (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin r) Real
                      (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                            (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                              (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                      (Fin.fintype r)
                      (@Matrix.transpose.{0, 0, 0} (Fin r) (Fin r) Real
                        (@Inv.inv.{0} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
                          (@Matrix.inv.{0, 0} (Fin r) Real (Fin.fintype r) (instDecidableEqFin r) Real.commRing) (P k)))
                      (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                        (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                              (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                        (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin r) Real (V k))
                        (@BfgsVerification.AdmissibleBFGSRun.g n F R k))))
                  (@BfgsVerification.AdmissibleBFGSRun.q n F R k)))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@BfgsVerification.sqNorm r
                  (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin r) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype r)
                    (@Matrix.transpose.{0, 0, 0} (Fin r) (Fin r) Real
                      (@Inv.inv.{0} (Matrix.{0, 0, 0} (Fin r) (Fin r) Real)
                        (@Matrix.inv.{0, 0} (Fin r) Real (Fin.fintype r) (instDecidableEqFin r) Real.commRing)
                        (P
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))
                    (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                      (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                            (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                              (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                      (Fin.fintype n)
                      (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin r) Real
                        (V
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
                      (@BfgsVerification.AdmissibleBFGSRun.gradientChange n F R k))))
                (@BfgsVerification.AdmissibleBFGSRun.curvature n F R k)))

def EJob14.Contract04 : Prop :=
let f := BfgsVerification.ScalarCounterexamples.shiftedAbs;
let F := BfgsVerification.ScalarCounterexamples.shiftedObjective;
And
  (@StrongConvexOn.{0} Real Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@Set.univ.{0} Real) (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) f)
  (And
    (∀ (x : Real),
      @LE.le.{0} Real Real.instLE
        (f (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))) (f x))
    (And
      (∀ (x : Real),
        @Eq.{1} Real (f x)
            (f (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))) →
          @Eq.{1} Real x
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))))
      (And
        (Not
          (@BfgsVerification.TransportedCertificate.HasBandCertificates (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) F
            (@setOf.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
              fun (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) =>
              @LE.le.{0} Real Real.instLE (F x)
                (@OfNat.ofNat.{0} Real 3
                  (@instOfNatAtLeastTwo.{0} Real 3 Real.instNatCast
                    BfgsVerification.ScalarGlobalCertificateNonnecessityTarget._proof_1)))
            (F
              (@DFunLike.coe.{1, 1, 1}
                (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  Real.instAddCommMonoid (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real.instAddCommMonoid)
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
                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) Real Real Real.semiring
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
                Real (fun (x : Real) => BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  Real.instAddCommMonoid (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real.instAddCommMonoid)
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
                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) Real Real Real.semiring
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
                BfgsVerification.OneDimensional.embed
                (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real 4
                (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                  BfgsVerification.ScalarGlobalCertificateNonnecessityTarget._proof_2)))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real 2
                (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                  BfgsVerification.ScalarGlobalCertificateNonnecessityTarget._proof_3)))))
        (And
          (∀ (R : BfgsVerification.ScalarMetricRun f),
            And
              (@Filter.Tendsto.{0, 0} Nat Real (fun (k : Nat) => f (@BfgsVerification.ScalarMetricRun.x f R k))
                (@Filter.atTop.{0} Nat Nat.instPreorder)
                (@nhds.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real 3
                      (@instOfNatAtLeastTwo.{0} Real 3 Real.instNatCast
                        BfgsVerification.ScalarGlobalCertificateNonnecessityTarget._proof_1))
                    (@OfNat.ofNat.{0} Real 2
                      (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                        BfgsVerification.ScalarGlobalCertificateNonnecessityTarget._proof_3)))))
              (@Filter.Tendsto.{0, 0} Nat Real (@BfgsVerification.ScalarMetricRun.x f R)
                (@Filter.atTop.{0} Nat Nat.instPreorder)
                (@nhds.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))))))
          (∀ (R : BfgsVerification.AdmissibleBFGSRun (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) F),
            And
              (@Filter.Tendsto.{0, 0} Nat Real
                (fun (k : Nat) =>
                  F (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) F R k))
                (@Filter.atTop.{0} Nat Nat.instPreorder)
                (@nhds.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real 3
                      (@instOfNatAtLeastTwo.{0} Real 3 Real.instNatCast
                        BfgsVerification.ScalarGlobalCertificateNonnecessityTarget._proof_1))
                    (@OfNat.ofNat.{0} Real 2
                      (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
                        BfgsVerification.ScalarGlobalCertificateNonnecessityTarget._proof_3)))))
              (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) F R)
                (@Filter.atTop.{0} Nat Nat.instPreorder)
                (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@DFunLike.coe.{1, 1, 1}
                    (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      Real.instAddCommMonoid (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real.instAddCommMonoid)
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
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) Real Real
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
                    Real (fun (x : Real) => BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                    (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      Real.instAddCommMonoid (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real.instAddCommMonoid)
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
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) Real Real
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
                    BfgsVerification.OneDimensional.embed
                    (@Neg.neg.{0} Real Real.instNeg
                      (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))))))))))

def EJob14.Contract05 : Prop :=
∀ {n : Nat} (M : BfgsVerification.Mat n),
  @Matrix.PosSemidef.{0, 0} (Fin n) Real (Fin.fintype n) Real.commRing Real.partialOrder instStarRingReal M →
    ∀ (s : BfgsVerification.Vec n),
      @Eq.{1} (Fin n → Real)
          (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
            (Fin.fintype n) M s)
          (@OfNat.ofNat.{0} (Fin n → Real) 0
            (@Zero.toOfNat0.{0} (Fin n → Real)
              (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instZero))) →
        ∀ (W Z : BfgsVerification.Mat n) (a : Real),
          @Matrix.PosSemidef.{0, 0} (Fin n) Real (Fin.fintype n) Real.commRing Real.partialOrder instStarRingReal
              (@HSub.hSub.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real) (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                (@instHSub.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                  (@Matrix.sub.{0, 0, 0} (Fin n) (Fin n) Real Real.instSub))
                (@HSMul.hSMul.{0, 0, 0} Real (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                  (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                  (@instHSMul.{0, 0} Real (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                    (@Matrix.smul.{0, 0, 0, 0} (Fin n) (Fin n) Real Real
                      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                        (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                        (@Algebra.id.{0} Real Real.instCommSemiring))))
                  a
                  (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real) (BfgsVerification.Mat n)
                    (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real
                      (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                    (@HMul.hMul.{0, 0, 0} (BfgsVerification.Mat n) (BfgsVerification.Mat n)
                      (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real
                        (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                      (@BfgsVerification.TransportedCertificate.stepProjector n s) W)
                    (@BfgsVerification.TransportedCertificate.stepProjector n s)))
                (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real) (BfgsVerification.Mat n)
                  (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real
                    (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                  (@HMul.hMul.{0, 0, 0} (BfgsVerification.Mat n) (BfgsVerification.Mat n)
                    (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real
                      (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                    (@BfgsVerification.TransportedCertificate.stepProjector n s) Z)
                  (@BfgsVerification.TransportedCertificate.stepProjector n s))) →
            @LE.le.{0} Real Real.instLE
              (@Matrix.trace.{0, 0} (Fin n) Real (Fin.fintype n) Real.instAddCommMonoid
                (@HMul.hMul.{0, 0, 0} (BfgsVerification.Mat n) (BfgsVerification.Mat n)
                  (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real
                    (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                  M Z))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
                (@Matrix.trace.{0, 0} (Fin n) Real (Fin.fintype n) Real.instAddCommMonoid
                  (@HMul.hMul.{0, 0, 0} (BfgsVerification.Mat n) (BfgsVerification.Mat n)
                    (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real
                      (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                    M W)))

def EJob14.Contract06 : Prop :=
∀ {n : Nat} (W : BfgsVerification.Mat n) (s v : BfgsVerification.Vec n),
  @Eq.{1} Real
    (@BfgsVerification.metricEnergy n
      (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real) (BfgsVerification.Mat n)
        (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real (Fin.fintype n)
          Real.instMul Real.instAddCommMonoid)
        (@HMul.hMul.{0, 0, 0} (BfgsVerification.Mat n) (BfgsVerification.Mat n) (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real (Fin.fintype n)
            Real.instMul Real.instAddCommMonoid)
          (@BfgsVerification.TransportedCertificate.stepProjector n s) W)
        (@BfgsVerification.TransportedCertificate.stepProjector n s))
      v)
    (@BfgsVerification.metricEnergy n W
      (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
        (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
              (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
        (Fin.fintype n) (@BfgsVerification.TransportedCertificate.stepProjector n s) v))

def EJob14.Contract07 : Prop :=
∀ {L c₁ d fx fz fstar : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) L →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) c₁ →
      @LE.le.{0} Real Real.instLE (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c₁ d)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) fx fz) →
        @LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Real.exp
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) L c₁)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) fz fstar)))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) L d)))
          (Real.exp
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) L c₁)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) fx fstar)))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.transportedCertificateConvergence, ``EJob14.Contract01),
    (``BfgsVerification.certificateNormalization, ``EJob14.Contract02),
    (``BfgsVerification.AdmissibleBFGSRun.normalized_frame_trace_recurrence, ``EJob14.Contract03),
    (``BfgsVerification.scalarGlobalCertificateNonnecessity, ``EJob14.Contract04),
    (``BfgsVerification.TransportedCertificate.projected_transport_trace, ``EJob14.Contract05),
    (``BfgsVerification.TransportedCertificate.projected_energy, ``EJob14.Contract06),
    (``BfgsVerification.TransportedCertificate.value_weight_transport, ``EJob14.Contract07)]
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
