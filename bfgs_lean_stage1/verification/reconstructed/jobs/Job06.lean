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

def EJob06.Contract01 : Prop :=
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

def EJob06.Contract02 : Prop :=
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

def EJob06.Contract03 : Prop :=
∀ {n : Nat} (H : BfgsVerification.Mat n),
  @Matrix.PosDef.{0, 0} (Fin n) Real (Fin.fintype n) Real.commRing Real.partialOrder instStarRingReal H →
    ∃ (U : BfgsVerification.Mat n) (lam : BfgsVerification.Vec n),
      And
        (@Eq.{1} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
          (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real) (BfgsVerification.Mat n)
            (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real (Fin.fintype n)
              Real.instMul Real.instAddCommMonoid)
            (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin n) Real U) U)
          (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real) 1
            (@One.toOfNat1.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
              (@Matrix.one.{0, 0} (Fin n) Real (instDecidableEqFin n) Real.instZero Real.instOne))))
        (And
          (@Eq.{1} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
            (@HMul.hMul.{0, 0, 0} (BfgsVerification.Mat n) (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
              (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real (Fin.fintype n)
                Real.instMul Real.instAddCommMonoid)
              U (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin n) Real U))
            (@OfNat.ofNat.{0} (BfgsVerification.Mat n) 1
              (@One.toOfNat1.{0} (BfgsVerification.Mat n)
                (@Matrix.one.{0, 0} (Fin n) Real (instDecidableEqFin n) Real.instZero Real.instOne))))
          (And
            (@Eq.{1} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
              (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real) (BfgsVerification.Mat n)
                (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real (Fin.fintype n)
                  Real.instMul Real.instAddCommMonoid)
                (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real) (BfgsVerification.Mat n)
                  (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin n) Real
                    (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                  (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin n) Real U) H)
                U)
              (@Matrix.diagonal.{0, 0} (Fin n) Real (instDecidableEqFin n) Real.instZero lam))
            (And
              (∀ (i : Fin n),
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) (lam i))
              (∀ (y : BfgsVerification.Vec n) (j : Nat),
                @Eq.{1} Real
                  (∑ I ∈ @Finset.powersetCard.{0} (Fin n) j (@Finset.univ.{0} (Fin n) (Fin.fintype n)),
                    @Matrix.det.{0, 0}
                      (Sum.{0, 0} Unit
                        (@Subtype.{1} (Fin n) fun (x : Fin n) =>
                          @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n)) I x))
                      (fun
                          (a b :
                            Sum.{0, 0} Unit
                              (@Subtype.{1} (Fin n) fun (x : Fin n) =>
                                @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n))
                                  I x)) =>
                        @Sum.instDecidableEq.{0, 0} Unit
                          (@Subtype.{1} (Fin n) fun (x : Fin n) =>
                            @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n)) I
                              x)
                          instDecidableEqPUnit.{1}
                          (fun
                              (a b :
                                @Subtype.{1} (Fin n) fun (x : Fin n) =>
                                  @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                                    (@Finset.instMembership.{0} (Fin n)) I x) =>
                            @Subtype.instDecidableEq.{0} (Fin n)
                              (@Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n))
                                I)
                              (instDecidableEqFin n) a b)
                          a b)
                      (@instFintypeSum.{0, 0} Unit
                        (@Subtype.{1} (Fin n) fun (x : Fin n) =>
                          @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n)) I x)
                        PUnit.fintype.{0} (@Finset.Subtype.fintype.{0} (Fin n) I))
                      Real Real.commRing
                      (@BfgsVerification.metricGram.{0} n
                        (Sum.{0, 0} Unit
                          (@Subtype.{1} (Fin n) fun (x : Fin n) =>
                            @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n)) I
                              x))
                        H
                        (@Matrix.fromCols.{0, 0, 0, 0} Real (Fin n) Unit
                          (@Subtype.{1} (Fin n) fun (x : Fin n) =>
                            @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n)) I
                              x)
                          (@Matrix.replicateCol.{0, 0, 0} (Fin n) Real Unit y)
                          (@HMul.hMul.{0, 0, 0} (BfgsVerification.Mat n)
                            (Matrix.{0, 0, 0} (Fin n)
                              (@Subtype.{1} (Fin n) fun (x : Fin n) =>
                                @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n))
                                  I x)
                              Real)
                            (Matrix.{0, 0, 0} (Fin n)
                              (@Subtype.{1} (Fin n) fun (x : Fin n) =>
                                @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n))
                                  I x)
                              Real)
                            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n)
                              (@Subtype.{1} (Fin n) fun (x : Fin n) =>
                                @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n))
                                  I x)
                              Real (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                            U (@BfgsVerification.coordinateMatrix n I)))))
                  (∑
                    J ∈
                      @Finset.powersetCard.{0} (Fin n)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
                        (@Finset.univ.{0} (Fin n) (Fin.fintype n)),
                    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (∏ i ∈ J, lam i)
                      (∑ k ∈ J,
                        @HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                          (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
                            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                            (Fin.fintype n) (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin n) Real U) y k)
                          (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))))

def EJob06.Contract04 : Prop :=
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

def EJob06.Contract05 : Prop :=
∀ {n : Nat} (A : BfgsVerification.Mat n) (a b : BfgsVerification.Vec n) (κ r ρ : Real),
  @IsUnit.{0} Real Real.instMonoid
      (@Matrix.det.{0, 0} (Fin n) (instDecidableEqFin n) (Fin.fintype n) Real Real.commRing A) →
    @Matrix.IsSymm.{0, 0} Real (Fin n) A →
      @Eq.{1} Real
        (@Matrix.det.{0, 0} (Fin n) (instDecidableEqFin n) (Fin.fintype n) Real Real.commRing
          (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Mat n) (BfgsVerification.Mat n) (BfgsVerification.Mat n)
            (@instHAdd.{0} (BfgsVerification.Mat n) (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
            (@BfgsVerification.CompressionDeterminant.compression n A a b κ r)
            (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Mat n) (BfgsVerification.Mat n)
              (@instHSMul.{0, 0} Real (BfgsVerification.Mat n)
                (@Matrix.smul.{0, 0, 0, 0} (Fin n) (Fin n) Real Real
                  (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                    (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                    (@Algebra.id.{0} Real Real.instCommSemiring))))
              ρ (@BfgsVerification.outer n a a))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@Matrix.det.{0, 0} (Fin n) (instDecidableEqFin n) (Fin.fintype n) Real Real.commRing
            (@BfgsVerification.CompressionDeterminant.compression n A a b κ r))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ρ
              (@Matrix.det.{0, 0} (Fin n) (instDecidableEqFin n) (Fin.fintype n) Real Real.commRing A))
            (@BfgsVerification.dot n a
              (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
                (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                      (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                        (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                (Fin.fintype n)
                (@Inv.inv.{0} (BfgsVerification.Mat n)
                  (@Matrix.inv.{0, 0} (Fin n) Real (Fin.fintype n) (instDecidableEqFin n) Real.commRing) A)
                a))))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.principalMinorHierarchy, ``EJob06.Contract01),
    (``BfgsVerification.CompressionAlgebra.gram_numerator_identity, ``EJob06.Contract02),
    (``BfgsVerification.principalGramSumIdentity, ``EJob06.Contract03),
    (``BfgsVerification.BFGSCompression.inverseBFGS_compression, ``EJob06.Contract04),
    (``BfgsVerification.CompressionDeterminant.compression_add_rank_one_det, ``EJob06.Contract05)]
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
