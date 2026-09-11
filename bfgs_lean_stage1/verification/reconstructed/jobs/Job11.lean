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

def EJob11.Contract01 : Prop :=
∀ {n : Nat} {F : BfgsVerification.Vec n → Real},
  @ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec n) Real Real.semiring Real.partialOrder
      (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommMonoid)
      Real.instAddCommMonoid Real.partialOrder
      (@Function.hasSMul.{0, 0, 0} (Fin n) Real Real
        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
        (@Algebra.id.{0} Real Real.instCommSemiring))
      (@Set.univ.{0} (BfgsVerification.Vec n)) F →
    ∀ (star : BfgsVerification.Vec n),
      (∀ (x : BfgsVerification.Vec n), @LE.le.{0} Real Real.instLE (F star) (F x)) →
        ∀ (b : Real),
          @LT.lt.{0} Real Real.instLT (F star) b →
            @IsCompact.{0} (BfgsVerification.Vec n)
                (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@setOf.{0} (BfgsVerification.Vec n) fun (x : BfgsVerification.Vec n) =>
                  @LE.le.{0} Real Real.instLE (F x) b) →
              Iff
                (@BfgsVerification.RadialCertificate.HasRadialSecantBounds n F
                  (@setOf.{0} (BfgsVerification.Vec n) fun (x : BfgsVerification.Vec n) =>
                    @LE.le.{0} Real Real.instLE (F x) b)
                  star)
                (@BfgsVerification.RadialCertificate.HasInwardTaylorBounds n F
                  (@setOf.{0} (BfgsVerification.Vec n) fun (x : BfgsVerification.Vec n) =>
                    @LE.le.{0} Real Real.instLE (F x) b)
                  star)

def EJob11.Contract02 : Prop :=
∀ {n : Nat} {F : BfgsVerification.Vec n → Real},
  @ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec n) Real Real.semiring Real.partialOrder
      (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommMonoid)
      Real.instAddCommMonoid Real.partialOrder
      (@Function.hasSMul.{0, 0, 0} (Fin n) Real Real
        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
        (@Algebra.id.{0} Real Real.instCommSemiring))
      (@Set.univ.{0} (BfgsVerification.Vec n)) F →
    ∀ {K : Set.{0} (BfgsVerification.Vec n)},
      @IsCompact.{0} (BfgsVerification.Vec n)
          (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          K →
        ∀ (star : BfgsVerification.Vec n),
          Iff (@BfgsVerification.RadialCertificate.HasRadialSecantBounds n F K star)
            (@BfgsVerification.RadialCertificate.HasInterceptBounds n F K star)

def EJob11.Contract03 : Prop :=
∀ {K : Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))},
  @Membership.mem.{0, 0} (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
      (Filter.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
      (@Filter.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
      (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
          (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))
      K →
    And
      (∀
        (R :
          BfgsVerification.AdmissibleBFGSRun (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
            BfgsVerification.ParabolicRadialBoundary.objective),
        And
          (@Filter.Tendsto.{0, 0} Nat Real
            (fun (k : Nat) =>
              BfgsVerification.ParabolicRadialBoundary.objective
                (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                  BfgsVerification.ParabolicRadialBoundary.objective R k))
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (@nhds.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
          (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              BfgsVerification.ParabolicRadialBoundary.objective R)
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
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))))
      (Not
        (@BfgsVerification.RadialCertificate.HasRadialSecantBounds (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
          BfgsVerification.ParabolicRadialBoundary.objective K
          (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
            (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)))))

def EJob11.Contract04 : Prop :=
∀ {x g : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))},
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
        @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      BfgsVerification.UnexcitedMetric.objective
      (@BfgsVerification.gradientFunctional (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) g) x →
    @Eq.{1} Real
      (@BfgsVerification.RadialCertificate.optimizerIntercept (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
        BfgsVerification.UnexcitedMetric.objective
        (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
          (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)))
        x g)
      (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
        (x
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0)))
        (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))

def EJob11.Contract05 : Prop :=
And
  (@ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real.semiring
    Real.partialOrder
    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
    Real.instAddCommMonoid Real.partialOrder
    (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
        (@Algebra.id.{0} Real Real.instCommSemiring)))
    (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
      (@Algebra.id.{0} Real Real.instCommSemiring))
    (@Set.univ.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
    BfgsVerification.ReconstructedFourPiece.objective)
  (And
    (∀ (b : Real),
      @IsCompact.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@setOf.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          fun (z : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
          @LE.le.{0} Real Real.instLE (BfgsVerification.ReconstructedFourPiece.objective z) b))
    (And
      (@Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        BfgsVerification.ReconstructedFourPiece.optimizer
        (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
          (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
            (@OfNat.ofNat.{0} Real 5
              (@instOfNatAtLeastTwo.{0} Real 5 Real.instNatCast
                BfgsVerification.ReconstructedFourPieceFailureTarget._proof_1))
            (@Matrix.vecEmpty.{0} Real))))
      (And
        (@Eq.{1} Real
          (BfgsVerification.ReconstructedFourPiece.objective BfgsVerification.ReconstructedFourPiece.optimizer)
          (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))))
        (And
          (∀ (z : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
            @LE.le.{0} Real Real.instLE
              (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
              (BfgsVerification.ReconstructedFourPiece.objective z))
          (And
            (∀ (z : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
              @Eq.{1} Real (BfgsVerification.ReconstructedFourPiece.objective z)
                  (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))) →
                @Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) z
                  BfgsVerification.ReconstructedFourPiece.optimizer)
            (And
              (∀ (i : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))),
                @Eq.{1} Real
                  (@BfgsVerification.MaxAffine.Family.branch (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    (@OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)) BfgsVerification.ReconstructedFourPiece.family
                    (@Fin.castSucc (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) i)
                    BfgsVerification.ReconstructedFourPiece.optimizer)
                  (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
                    (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
                      (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
                      (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@Neg.neg.{0} Real Real.instNeg
                            (@OfNat.ofNat.{0} Real 29
                              (@instOfNatAtLeastTwo.{0} Real 29 Real.instNatCast
                                BfgsVerification.ReconstructedFourPieceFailureTarget._proof_2)))
                          (@OfNat.ofNat.{0} Real 4
                            (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                              BfgsVerification.ReconstructedFourPieceFailureTarget._proof_3)))
                        (@Matrix.vecEmpty.{0} Real)))
                    i))
              (And
                (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                    (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)) ∉
                  @BfgsVerification.ConvexSubdifferential.subdifferential (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    BfgsVerification.ReconstructedFourPiece.objective
                    (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                      (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))))
                (∀ (c₁ c₂ : Real)
                  (hc₁ :
                    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) c₁)
                  (hc₁' :
                    @LE.le.{0} Real Real.instLE c₁
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
                        (@OfNat.ofNat.{0} Real 3
                          (@instOfNatAtLeastTwo.{0} Real 3 Real.instNatCast
                            BfgsVerification.ReconstructedFourPieceFailureTarget._proof_4))))
                  (hc : @LT.lt.{0} Real Real.instLT c₁ c₂)
                  (hc₂ :
                    @LT.lt.{0} Real Real.instLT c₂ (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))),
                  let R := @BfgsVerification.ReconstructedFourPiece.run c₁ c₂ hc₁ hc₁' hc hc₂;
                  And
                    (@Eq.{1} Real
                      (@BfgsVerification.AdmissibleBFGSRun.c₁ (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                        BfgsVerification.ReconstructedFourPiece.objective R)
                      c₁)
                    (And
                      (@Eq.{1} Real
                        (@BfgsVerification.AdmissibleBFGSRun.c₂ (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                          BfgsVerification.ReconstructedFourPiece.objective R)
                        c₂)
                      (And
                        (∀ (k : Nat),
                          @Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              BfgsVerification.ReconstructedFourPiece.objective R k)
                            (@BfgsVerification.AffineWhitening.point (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                              BfgsVerification.ReconstructedFourPiece.coordinate
                              (BfgsVerification.SeedOrbit.orbitPoint k)))
                        (And
                          (∀ (k : Nat),
                            @Eq.{1} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (@BfgsVerification.AdmissibleBFGSRun.H (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                BfgsVerification.ReconstructedFourPiece.objective R k)
                              (@HSMul.hSMul.{0, 0, 0} Real
                                (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@instHSMul.{0, 0} Real (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@Matrix.smul.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                                    (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                      (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                      (@Algebra.id.{0} Real Real.instCommSemiring))))
                                (@Inv.inv.{0} Real Real.instInv BfgsVerification.ReconstructedFourPiece.valueScale)
                                (@BfgsVerification.AffineWhitening.metric (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                  BfgsVerification.ReconstructedFourPiece.coordinate
                                  (BfgsVerification.SeedOrbit.orbitMetric k))))
                          (And
                            (∀ (k : Nat),
                              @Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                (@BfgsVerification.AdmissibleBFGSRun.g (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                  BfgsVerification.ReconstructedFourPiece.objective R k)
                                (@HSMul.hSMul.{0, 0, 0} Real
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@instHSMul.{0, 0} Real
                                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                                      Real
                                      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                        (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                        (@Algebra.id.{0} Real Real.instCommSemiring))))
                                  BfgsVerification.ReconstructedFourPiece.valueScale
                                  (@BfgsVerification.AffineWhitening.gradient (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                    BfgsVerification.ReconstructedFourPiece.coordinate
                                    (BfgsVerification.SeedOrbit.orbitGradient k))))
                            (And
                              (∀ (k : Nat),
                                @Eq.{1} Real
                                  (@BfgsVerification.AdmissibleBFGSRun.α (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                    BfgsVerification.ReconstructedFourPiece.objective R k)
                                  (BfgsVerification.SeedOrbit.orbitLength k))
                              (And
                                (@Filter.Tendsto.{0, 0} Nat
                                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                  (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                    BfgsVerification.ReconstructedFourPiece.objective R)
                                  (@Filter.atTop.{0} Nat Nat.instPreorder)
                                  (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                                      @UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                    (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
                                      (@Zero.toOfNat0.{0}
                                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                        (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero)))))
                                (And
                                  (@Filter.Tendsto.{0, 0} Nat Real
                                    (fun (k : Nat) =>
                                      BfgsVerification.ReconstructedFourPiece.objective
                                        (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                          BfgsVerification.ReconstructedFourPiece.objective R k))
                                    (@Filter.atTop.{0} Nat Nat.instPreorder)
                                    (@nhds.{0} Real
                                      (@UniformSpace.toTopologicalSpace.{0} Real
                                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                        BfgsVerification.ReconstructedFourPiece.valueScale
                                        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))))
                                  (And
                                    (@LT.lt.{0} Real Real.instLT
                                      (@Neg.neg.{0} Real Real.instNeg
                                        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
                                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                        BfgsVerification.ReconstructedFourPiece.valueScale
                                        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))))
                                    (And
                                      (∀ (k : Nat),
                                        @LT.lt.{0} Real Real.instLT
                                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                            BfgsVerification.ReconstructedFourPiece.valueScale
                                            (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
                                          (BfgsVerification.ReconstructedFourPiece.objective
                                            (@BfgsVerification.AdmissibleBFGSRun.x
                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                              BfgsVerification.ReconstructedFourPiece.objective R k)))
                                      (∀ (k : Nat),
                                        @LT.lt.{0} Real Real.instLT
                                          (BfgsVerification.ReconstructedFourPiece.objective
                                            (@BfgsVerification.AdmissibleBFGSRun.x
                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                              BfgsVerification.ReconstructedFourPiece.objective R
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
                                          (BfgsVerification.ReconstructedFourPiece.objective
                                            (@BfgsVerification.AdmissibleBFGSRun.x
                                              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                                              BfgsVerification.ReconstructedFourPiece.objective R k))))))))))))))))))))

def EJob11.Contract06 : Prop :=
And
  (∀ (m : Nat) (j : Fin (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))),
    @Eq.{1} Real
      (@BfgsVerification.RadialCertificate.optimizerIntercept (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
        BfgsVerification.ReconstructedFourPiece.objective BfgsVerification.ReconstructedFourPiece.optimizer
        (BfgsVerification.ReconstructedFourPiece.point
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              m)
            (@Fin.val (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) j)))
        (BfgsVerification.ReconstructedFourPiece.gradient
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              m)
            (@Fin.val (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) j))))
      (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
        (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
          (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real 25
                (@instOfNatAtLeastTwo.{0} Real 25 Real.instNatCast
                  BfgsVerification.ReconstructedSupportingPlaneTarget._proof_5))
              (@OfNat.ofNat.{0} Real 4
                (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
                  BfgsVerification.ReconstructedFourPieceFailureTarget._proof_3)))
            (@Matrix.vecEmpty.{0} Real)))
        j))
  (And
    (∀ (k : Nat),
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
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        BfgsVerification.ReconstructedFourPiece.objective
        (@BfgsVerification.gradientFunctional (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
          (BfgsVerification.ReconstructedFourPiece.gradient k))
        (BfgsVerification.ReconstructedFourPiece.point k))
    (And
      (∀ (k : Nat),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
          (@BfgsVerification.RadialCertificate.secantCurvature (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
            (BfgsVerification.ReconstructedFourPiece.point k)
            (BfgsVerification.ReconstructedFourPiece.point
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            (BfgsVerification.ReconstructedFourPiece.gradient k)
            (BfgsVerification.ReconstructedFourPiece.gradient
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))
      (And
        (@Filter.Tendsto.{0, 0} Nat Real
          (fun (k : Nat) =>
            @BfgsVerification.RadialCertificate.secantCurvature (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              (BfgsVerification.ReconstructedFourPiece.point k)
              (BfgsVerification.ReconstructedFourPiece.point
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
              (BfgsVerification.ReconstructedFourPiece.gradient k)
              (BfgsVerification.ReconstructedFourPiece.gradient
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@nhds.{0} Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
        (And
          (Not
            (@BfgsVerification.RadialCertificate.HasInterceptBounds (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              BfgsVerification.ReconstructedFourPiece.objective
              (@setOf.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                fun (z : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                @LE.le.{0} Real Real.instLE (BfgsVerification.ReconstructedFourPiece.objective z)
                  (BfgsVerification.ReconstructedFourPiece.objective
                    (BfgsVerification.ReconstructedFourPiece.point (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
              BfgsVerification.ReconstructedFourPiece.optimizer))
          (Not
            (@BfgsVerification.RadialCertificate.HasRadialSecantBounds (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              BfgsVerification.ReconstructedFourPiece.objective
              (@setOf.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                fun (z : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                @LE.le.{0} Real Real.instLE (BfgsVerification.ReconstructedFourPiece.objective z)
                  (BfgsVerification.ReconstructedFourPiece.objective
                    (BfgsVerification.ReconstructedFourPiece.point (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
              BfgsVerification.ReconstructedFourPiece.optimizer))))))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.radialInwardEquivalence, ``EJob11.Contract01),
    (``BfgsVerification.radialInterceptEquivalence, ``EJob11.Contract02),
    (``BfgsVerification.parabolicRadialBoundary, ``EJob11.Contract03),
    (``BfgsVerification.InterceptExamples.quadratic_absolute_intercept, ``EJob11.Contract04),
    (``BfgsVerification.reconstructedFourPieceFailure, ``EJob11.Contract05),
    (``BfgsVerification.reconstructedSupportingPlane, ``EJob11.Contract06)]
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
