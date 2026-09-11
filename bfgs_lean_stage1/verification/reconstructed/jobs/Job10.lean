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

def EJob10.Contract01.{u_1} : Prop :=
∀ {n : Nat} {ι : Type u_1} [inst : Fintype.{u_1} ι] (hne : @Finset.Nonempty.{u_1} ι (@Finset.univ.{u_1} ι inst))
  {F : BfgsVerification.Vec n → Real},
  @ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec n) Real Real.semiring Real.partialOrder
      (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommMonoid)
      Real.instAddCommMonoid Real.partialOrder
      (@Function.hasSMul.{0, 0, 0} (Fin n) Real Real
        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
        (@Algebra.id.{0} Real Real.instCommSemiring))
      (@Set.univ.{0} (BfgsVerification.Vec n)) F →
    ∀ (f : ι → BfgsVerification.Vec n → Real) {U : Set.{0} (BfgsVerification.Vec n)},
      @IsOpen.{0} (BfgsVerification.Vec n)
          (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          U →
        (∀ (i : ι),
            @ContDiffOn.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
              (BfgsVerification.Vec n)
              (@Pi.normedAddCommGroup.{0, 0} (Fin n) (fun (a : Fin n) => Real) (Fin.fintype n) fun (i : Fin n) =>
                Real.normedAddCommGroup)
              (@Pi.normedSpace.{0, 0, 0} Real
                (@NontriviallyNormedField.toNormedField.{0} Real
                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))
                (Fin n) (fun (a : Fin n) => Real) (Fin.fintype n)
                (fun (i : Fin n) =>
                  @NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                        (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                fun (i : Fin n) =>
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
                  BfgsVerification.FiniteMaxRadialBasinTarget._proof_1))
              (f i) U) →
          ∀ {star : BfgsVerification.Vec n},
            @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                (@Set.instMembership.{0} (BfgsVerification.Vec n)) U star →
              (∀ (w : BfgsVerification.Vec n),
                  @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                      (@Set.instMembership.{0} (BfgsVerification.Vec n)) U w →
                    @Eq.{1} Real (F w)
                      (@Finset.sup'.{0, u_1} Real ι Real.instSemilatticeSup (@Finset.univ.{u_1} ι inst) hne
                        fun (i : ι) => f i w)) →
                (∀ (w : BfgsVerification.Vec n),
                    @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                        (@Set.instMembership.{0} (BfgsVerification.Vec n)) U w →
                      ∀ (i j : ι),
                        @Eq.{1} Real (f i w) (F w) →
                          @Eq.{1} Real (f j w) (F w) →
                            @Eq.{1} Real
                              (@DFunLike.coe.{1, 1, 1}
                                (@ContinuousLinearMap.{0, 0, 0, 0} Real Real
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@NontriviallyNormedField.toNormedField.{0} Real
                                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                              Real.denselyNormedField))))))
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@NontriviallyNormedField.toNormedField.{0} Real
                                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                              Real.denselyNormedField))))))
                                  (@RingHom.id.{0} Real
                                    (@Semiring.toNonAssocSemiring.{0} Real
                                      (@DivisionSemiring.toSemiring.{0} Real
                                        (@Semifield.toDivisionSemiring.{0} Real
                                          (@Field.toSemifield.{0} Real
                                            (@NormedField.toField.{0} Real
                                              (@NontriviallyNormedField.toNormedField.{0} Real
                                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                  Real.denselyNormedField))))))))
                                  (BfgsVerification.Vec n)
                                  (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@AddCommGroup.toAddCommMonoid.{0} (BfgsVerification.Vec n)
                                    (@Pi.addCommGroup.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instAddCommGroup))
                                  Real
                                  (@UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
                                  (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@NontriviallyNormedField.toNormedField.{0} Real
                                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                Real.denselyNormedField))))))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonUnitalSemiring.{0} Real
                                          (@Ring.toSemiring.{0} Real Real.instRing))))
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
                                (BfgsVerification.Vec n) (fun (x : BfgsVerification.Vec n) => Real)
                                (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@NontriviallyNormedField.toNormedField.{0} Real
                                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                              Real.denselyNormedField))))))
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@NontriviallyNormedField.toNormedField.{0} Real
                                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                              Real.denselyNormedField))))))
                                  (@RingHom.id.{0} Real
                                    (@Semiring.toNonAssocSemiring.{0} Real
                                      (@DivisionSemiring.toSemiring.{0} Real
                                        (@Semifield.toDivisionSemiring.{0} Real
                                          (@Field.toSemifield.{0} Real
                                            (@NormedField.toField.{0} Real
                                              (@NontriviallyNormedField.toNormedField.{0} Real
                                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                  Real.denselyNormedField))))))))
                                  (BfgsVerification.Vec n)
                                  (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@AddCommGroup.toAddCommMonoid.{0} (BfgsVerification.Vec n)
                                    (@Pi.addCommGroup.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instAddCommGroup))
                                  Real
                                  (@UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
                                  (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@NontriviallyNormedField.toNormedField.{0} Real
                                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                Real.denselyNormedField))))))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonUnitalSemiring.{0} Real
                                          (@Ring.toSemiring.{0} Real Real.instRing))))
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
                                (@fderiv.{0, 0, 0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                                  (BfgsVerification.Vec n)
                                  (@Pi.addCommGroup.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                    Real.instAddCommGroup)
                                  (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@NontriviallyNormedField.toNormedField.{0} Real
                                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                Real.denselyNormedField))))))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonUnitalSemiring.{0} Real
                                          (@Ring.toSemiring.{0} Real Real.instRing))))
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
                                  (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
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
                                  (f i) w)
                                (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n)
                                  (BfgsVerification.Vec n)
                                  (@instHSub.{0} (BfgsVerification.Vec n)
                                    (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instSub))
                                  w star))
                              (@DFunLike.coe.{1, 1, 1}
                                (@ContinuousLinearMap.{0, 0, 0, 0} Real Real
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@NontriviallyNormedField.toNormedField.{0} Real
                                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                              Real.denselyNormedField))))))
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@NontriviallyNormedField.toNormedField.{0} Real
                                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                              Real.denselyNormedField))))))
                                  (@RingHom.id.{0} Real
                                    (@Semiring.toNonAssocSemiring.{0} Real
                                      (@DivisionSemiring.toSemiring.{0} Real
                                        (@Semifield.toDivisionSemiring.{0} Real
                                          (@Field.toSemifield.{0} Real
                                            (@NormedField.toField.{0} Real
                                              (@NontriviallyNormedField.toNormedField.{0} Real
                                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                  Real.denselyNormedField))))))))
                                  (BfgsVerification.Vec n)
                                  (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@AddCommGroup.toAddCommMonoid.{0} (BfgsVerification.Vec n)
                                    (@Pi.addCommGroup.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instAddCommGroup))
                                  Real
                                  (@UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
                                  (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@NontriviallyNormedField.toNormedField.{0} Real
                                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                Real.denselyNormedField))))))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonUnitalSemiring.{0} Real
                                          (@Ring.toSemiring.{0} Real Real.instRing))))
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
                                (BfgsVerification.Vec n) (fun (x : BfgsVerification.Vec n) => Real)
                                (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@NontriviallyNormedField.toNormedField.{0} Real
                                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                              Real.denselyNormedField))))))
                                  (@DivisionSemiring.toSemiring.{0} Real
                                    (@Semifield.toDivisionSemiring.{0} Real
                                      (@Field.toSemifield.{0} Real
                                        (@NormedField.toField.{0} Real
                                          (@NontriviallyNormedField.toNormedField.{0} Real
                                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                              Real.denselyNormedField))))))
                                  (@RingHom.id.{0} Real
                                    (@Semiring.toNonAssocSemiring.{0} Real
                                      (@DivisionSemiring.toSemiring.{0} Real
                                        (@Semifield.toDivisionSemiring.{0} Real
                                          (@Field.toSemifield.{0} Real
                                            (@NormedField.toField.{0} Real
                                              (@NontriviallyNormedField.toNormedField.{0} Real
                                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                  Real.denselyNormedField))))))))
                                  (BfgsVerification.Vec n)
                                  (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                    @UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@AddCommGroup.toAddCommMonoid.{0} (BfgsVerification.Vec n)
                                    (@Pi.addCommGroup.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instAddCommGroup))
                                  Real
                                  (@UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
                                  (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@NontriviallyNormedField.toNormedField.{0} Real
                                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                Real.denselyNormedField))))))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonUnitalSemiring.{0} Real
                                          (@Ring.toSemiring.{0} Real Real.instRing))))
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
                                (@fderiv.{0, 0, 0} Real
                                  (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                                  (BfgsVerification.Vec n)
                                  (@Pi.addCommGroup.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                    Real.instAddCommGroup)
                                  (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real
                                    (@DivisionSemiring.toSemiring.{0} Real
                                      (@Semifield.toDivisionSemiring.{0} Real
                                        (@Field.toSemifield.{0} Real
                                          (@NormedField.toField.{0} Real
                                            (@NontriviallyNormedField.toNormedField.{0} Real
                                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                Real.denselyNormedField))))))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonUnitalSemiring.{0} Real
                                          (@Ring.toSemiring.{0} Real Real.instRing))))
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
                                  (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
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
                                  (f j) w)
                                (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n)
                                  (BfgsVerification.Vec n)
                                  (@instHSub.{0} (BfgsVerification.Vec n)
                                    (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instSub))
                                  w star))) →
                  (∀ (x : BfgsVerification.Vec n), @LE.le.{0} Real Real.instLE (F star) (F x)) →
                    (∀ (x : BfgsVerification.Vec n),
                        @Eq.{1} Real (F x) (F star) → @Eq.{1} (BfgsVerification.Vec n) x star) →
                      ∃ (δ : Real),
                        And
                          (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                            δ)
                          (∀ (R : BfgsVerification.AdmissibleBFGSRun n F),
                            @LE.le.{0} Real Real.instLE
                                (F
                                  (@BfgsVerification.AdmissibleBFGSRun.x n F R
                                    (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (F star) δ) →
                              And
                                (∀ (k : Nat),
                                  @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                                    (@Set.instMembership.{0} (BfgsVerification.Vec n)) U
                                    (@BfgsVerification.AdmissibleBFGSRun.x n F R k))
                                (And
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
                                      (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                        @UniformSpace.toTopologicalSpace.{0} Real
                                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                      star))))

def EJob10.Contract02.{u_1} : Prop :=
∀ {n : Nat} {ι : Type u_1} [inst : Fintype.{u_1} ι] {m : ι → Nat} {F ψ : BfgsVerification.Vec n → Real},
  @ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec n) Real Real.semiring Real.partialOrder
      (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommMonoid)
      Real.instAddCommMonoid Real.partialOrder
      (@Function.hasSMul.{0, 0, 0} (Fin n) Real Real
        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
        (@Algebra.id.{0} Real Real.instCommSemiring))
      (@Set.univ.{0} (BfgsVerification.Vec n)) F →
    ∀ (γ : (j : ι) → BfgsVerification.Vec (m j) → Real),
      (∀ (j : ι),
          @ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec (m j)) Real Real.semiring Real.partialOrder
            (@Pi.addCommMonoid.{0, 0} (Fin (m j)) (fun (a : Fin (m j)) => Real) fun (i : Fin (m j)) =>
              Real.instAddCommMonoid)
            Real.instAddCommMonoid Real.partialOrder
            (@Function.hasSMul.{0, 0, 0} (Fin (m j)) Real Real
              (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
            (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
              (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
            (@Set.univ.{0} (BfgsVerification.Vec (m j))) (γ j)) →
        (∀ (j : ι), @BfgsVerification.Homogeneous.PositiveDegreeOne (m j) (γ j)) →
          (∀ (j : ι) (x : BfgsVerification.Vec (m j)),
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) (γ j x)) →
            ∀
              (A :
                (j : ι) →
                  @LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                    (BfgsVerification.Vec n) (BfgsVerification.Vec (m j))
                    (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                      Real.instAddCommMonoid)
                    (@Pi.addCommMonoid.{0, 0} (Fin (m j)) (fun (a : Fin (m j)) => Real) fun (i : Fin (m j)) =>
                      Real.instAddCommMonoid)
                    (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real Real.semiring Real.instAddCommMonoid
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
                    (@Pi.Function.module.{0, 0, 0} (Fin (m j)) Real Real Real.semiring Real.instAddCommMonoid
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
              (p : ι → Real),
              (∀ (j : ι),
                  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) (p j)) →
                ∀ (star : BfgsVerification.Vec n) {U K : Set.{0} (BfgsVerification.Vec n)},
                  @IsOpen.{0} (BfgsVerification.Vec n)
                      (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      U →
                    @BfgsVerification.CenteredSmoothSublinear.LocallyC11On n U ψ →
                      @IsCompact.{0} (BfgsVerification.Vec n)
                          (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          K →
                        @HasSubset.Subset.{0} (Set.{0} (BfgsVerification.Vec n))
                            (@Set.instHasSubset.{0} (BfgsVerification.Vec n)) K U →
                          (∀ (x : BfgsVerification.Vec n),
                              @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                                  (@Set.instMembership.{0} (BfgsVerification.Vec n)) U x →
                                @Eq.{1} Real (F x)
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ψ x)
                                    (∑ j : ι,
                                      @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                                        (γ j
                                          (@DFunLike.coe.{1, 1, 1}
                                            (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                              (@RingHom.id.{0} Real
                                                (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                              (BfgsVerification.Vec n) (BfgsVerification.Vec (m j))
                                              (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                fun (i : Fin n) => Real.instAddCommMonoid)
                                              (@Pi.addCommMonoid.{0, 0} (Fin (m j)) (fun (a : Fin (m j)) => Real)
                                                fun (i : Fin (m j)) => Real.instAddCommMonoid)
                                              (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real Real.semiring
                                                Real.instAddCommMonoid
                                                (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
                                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                        (@NormedCommRing.toSeminormedCommRing.{0} Real
                                                          Real.normedCommRing))))
                                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                          (@NormedCommRing.toSeminormedCommRing.{0} Real
                                                            Real.normedCommRing))))
                                                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                                              (@Pi.Function.module.{0, 0, 0} (Fin (m j)) Real Real Real.semiring
                                                Real.instAddCommMonoid
                                                (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
                                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                        (@NormedCommRing.toSeminormedCommRing.{0} Real
                                                          Real.normedCommRing))))
                                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                          (@NormedCommRing.toSeminormedCommRing.{0} Real
                                                            Real.normedCommRing))))
                                                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))))
                                            (BfgsVerification.Vec n)
                                            (fun (x : BfgsVerification.Vec n) => BfgsVerification.Vec (m j))
                                            (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real (BfgsVerification.Vec n)
                                              (BfgsVerification.Vec (m j)) Real.semiring Real.semiring
                                              (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                fun (i : Fin n) => Real.instAddCommMonoid)
                                              (@Pi.addCommMonoid.{0, 0} (Fin (m j)) (fun (a : Fin (m j)) => Real)
                                                fun (i : Fin (m j)) => Real.instAddCommMonoid)
                                              (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real Real.semiring
                                                Real.instAddCommMonoid
                                                (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
                                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                        (@NormedCommRing.toSeminormedCommRing.{0} Real
                                                          Real.normedCommRing))))
                                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                          (@NormedCommRing.toSeminormedCommRing.{0} Real
                                                            Real.normedCommRing))))
                                                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                                              (@Pi.Function.module.{0, 0, 0} (Fin (m j)) Real Real Real.semiring
                                                Real.instAddCommMonoid
                                                (@NormedSpace.toModule.{0, 0} Real Real Real.normedField
                                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                        (@NormedCommRing.toSeminormedCommRing.{0} Real
                                                          Real.normedCommRing))))
                                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                                                          (@NormedCommRing.toSeminormedCommRing.{0} Real
                                                            Real.normedCommRing))))
                                                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                                              (@RingHom.id.{0} Real
                                                (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                            (A j)
                                            (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n)
                                              (BfgsVerification.Vec n)
                                              (@instHSub.{0} (BfgsVerification.Vec n)
                                                (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                                  Real.instSub))
                                              x star)))
                                        (p j)))) →
                            @BfgsVerification.RadialCertificate.HasRadialSecantBounds n F K star

def EJob10.Contract03.{u_1} : Prop :=
∀ {n : Nat} {ι : Type u_1} [inst : Fintype.{u_1} ι] {F ψ : BfgsVerification.Vec n → Real},
  @ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec n) Real Real.semiring Real.partialOrder
      (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommMonoid)
      Real.instAddCommMonoid Real.partialOrder
      (@Function.hasSMul.{0, 0, 0} (Fin n) Real Real
        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
        (@Algebra.id.{0} Real Real.instCommSemiring))
      (@Set.univ.{0} (BfgsVerification.Vec n)) F →
    ∀ {Γ : ι → BfgsVerification.Vec n → Real},
      (∀ (j : ι),
          @ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec n) Real Real.semiring Real.partialOrder
            (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommMonoid)
            Real.instAddCommMonoid Real.partialOrder
            (@Function.hasSMul.{0, 0, 0} (Fin n) Real Real
              (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
            (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
              (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
            (@Set.univ.{0} (BfgsVerification.Vec n)) (Γ j)) →
        (∀ (j : ι), @BfgsVerification.Homogeneous.PositiveDegreeOne n (Γ j)) →
          (∀ (j : ι) (x : BfgsVerification.Vec n),
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) (Γ j x)) →
            ∀ (p : ι → Real),
              (∀ (j : ι),
                  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) (p j)) →
                ∀ (star : BfgsVerification.Vec n) {U K : Set.{0} (BfgsVerification.Vec n)},
                  @IsOpen.{0} (BfgsVerification.Vec n)
                      (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      U →
                    @BfgsVerification.CenteredSmoothSublinear.LocallyC11On n U ψ →
                      @IsCompact.{0} (BfgsVerification.Vec n)
                          (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          K →
                        @HasSubset.Subset.{0} (Set.{0} (BfgsVerification.Vec n))
                            (@Set.instHasSubset.{0} (BfgsVerification.Vec n)) K U →
                          (∀ (x : BfgsVerification.Vec n),
                              @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                                  (@Set.instMembership.{0} (BfgsVerification.Vec n)) U x →
                                @Eq.{1} Real (F x)
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ψ x)
                                    (@BfgsVerification.RadialPower.sumObjective.{u_1} n ι inst Γ p star x))) →
                            @BfgsVerification.RadialCertificate.HasRadialSecantBounds n F K star

def EJob10.Contract04.{u_1} : Prop :=
∀ {n : Nat} {ι : Type u_1} [inst : Fintype.{u_1} ι] {F ψ : BfgsVerification.Vec n → Real}
  (R : BfgsVerification.AdmissibleBFGSRun n F) {Γ : ι → BfgsVerification.Vec n → Real},
  (∀ (j : ι),
      @ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec n) Real Real.semiring Real.partialOrder
        (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommMonoid)
        Real.instAddCommMonoid Real.partialOrder
        (@Function.hasSMul.{0, 0, 0} (Fin n) Real Real
          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))
        (@Set.univ.{0} (BfgsVerification.Vec n)) (Γ j)) →
    (∀ (j : ι), @BfgsVerification.Homogeneous.PositiveDegreeOne n (Γ j)) →
      (∀ (j : ι) (x : BfgsVerification.Vec n),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) (Γ j x)) →
        ∀ (p : ι → Real),
          (∀ (j : ι),
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) (p j)) →
            ∀ (star : BfgsVerification.Vec n),
              (∀ (x : BfgsVerification.Vec n), @LE.le.{0} Real Real.instLE (F star) (F x)) →
                ∀ {U : Set.{0} (BfgsVerification.Vec n)},
                  @IsOpen.{0} (BfgsVerification.Vec n)
                      (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      U →
                    @BfgsVerification.CenteredSmoothSublinear.LocallyC11On n U ψ →
                      @IsCompact.{0} (BfgsVerification.Vec n)
                          (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@BfgsVerification.AdmissibleBFGSRun.initialSublevel n F R) →
                        @HasSubset.Subset.{0} (Set.{0} (BfgsVerification.Vec n))
                            (@Set.instHasSubset.{0} (BfgsVerification.Vec n))
                            (@BfgsVerification.AdmissibleBFGSRun.initialSublevel n F R) U →
                          (∀ (x : BfgsVerification.Vec n),
                              @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                                  (@Set.instMembership.{0} (BfgsVerification.Vec n)) U x →
                                @Eq.{1} Real (F x)
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ψ x)
                                    (@BfgsVerification.RadialPower.sumObjective.{u_1} n ι inst Γ p star x))) →
                            And
                              (@Filter.Tendsto.{0, 0} Nat Real
                                (fun (k : Nat) => F (@BfgsVerification.AdmissibleBFGSRun.x n F R k))
                                (@Filter.atTop.{0} Nat Nat.instPreorder)
                                (@nhds.{0} Real
                                  (@UniformSpace.toTopologicalSpace.{0} Real
                                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                  (F star)))
                              (And
                                (@Filter.Tendsto.{0, 0} Nat Real
                                  (fun (k : Nat) =>
                                    @BfgsVerification.euclideanSolutionDistance n F
                                      (@BfgsVerification.AdmissibleBFGSRun.x n F R k))
                                  (@Filter.atTop.{0} Nat Nat.instPreorder)
                                  (@nhds.{0} Real
                                    (@UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
                                ((∀ (x : BfgsVerification.Vec n),
                                    @Eq.{1} Real (F x) (F star) → @Eq.{1} (BfgsVerification.Vec n) x star) →
                                  @Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec n)
                                    (@BfgsVerification.AdmissibleBFGSRun.x n F R)
                                    (@Filter.atTop.{0} Nat Nat.instPreorder)
                                    (@nhds.{0} (BfgsVerification.Vec n)
                                      (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                        @UniformSpace.toTopologicalSpace.{0} Real
                                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                      star)))

def EJob10.Contract05.{u_1} : Prop :=
∀ {n : Nat} {ι : Type u_1} [inst : Fintype.{u_1} ι] {Γ : ι → BfgsVerification.Vec n → Real},
  (∀ (j : ι), @BfgsVerification.Homogeneous.PositiveDegreeOne n (Γ j)) →
    (∀ (j : ι) (x : BfgsVerification.Vec n),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) (Γ j x)) →
      ∀ (p : ι → Real) (star x : BfgsVerification.Vec n) {t : Real},
        @LE.le.{0} Real Real.instLE t (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) →
          @Eq.{1} Real
            (@BfgsVerification.RadialPower.sumObjective.{u_1} n ι inst Γ p star
              (@BfgsVerification.RadialCertificate.inwardPoint n star x t))
            (∑ j : ι,
              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (BfgsVerification.RadialPower.profile (p j) t)
                (@BfgsVerification.RadialPower.powered n (Γ j) (p j)
                  (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n) (BfgsVerification.Vec n)
                    (@instHSub.{0} (BfgsVerification.Vec n)
                      (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
                    x star)))

def EJob10.Contract06 : Prop :=
∀ {n m : Nat} {γ : BfgsVerification.Vec m → Real},
  @BfgsVerification.Homogeneous.PositiveDegreeOne m γ →
    ∀
      (A :
        @LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (BfgsVerification.Vec n)
          (BfgsVerification.Vec m)
          (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommMonoid)
          (@Pi.addCommMonoid.{0, 0} (Fin m) (fun (a : Fin m) => Real) fun (i : Fin m) => Real.instAddCommMonoid)
          (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real Real.semiring Real.instAddCommMonoid
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
          (@Pi.Function.module.{0, 0, 0} (Fin m) Real Real Real.semiring Real.instAddCommMonoid
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
                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))),
      @BfgsVerification.Homogeneous.PositiveDegreeOne n
        (@Function.comp.{1, 1, 1} (BfgsVerification.Vec n) (BfgsVerification.Vec m) Real γ
          (@DFunLike.coe.{1, 1, 1}
            (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (BfgsVerification.Vec n)
              (BfgsVerification.Vec m)
              (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommMonoid)
              (@Pi.addCommMonoid.{0, 0} (Fin m) (fun (a : Fin m) => Real) fun (i : Fin m) => Real.instAddCommMonoid)
              (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real Real.semiring Real.instAddCommMonoid
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
              (@Pi.Function.module.{0, 0, 0} (Fin m) Real Real Real.semiring Real.instAddCommMonoid
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
            (BfgsVerification.Vec n) (fun (x : BfgsVerification.Vec n) => BfgsVerification.Vec m)
            (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real (BfgsVerification.Vec n) (BfgsVerification.Vec m)
              Real.semiring Real.semiring
              (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommMonoid)
              (@Pi.addCommMonoid.{0, 0} (Fin m) (fun (a : Fin m) => Real) fun (i : Fin m) => Real.instAddCommMonoid)
              (@Pi.Function.module.{0, 0, 0} (Fin n) Real Real Real.semiring Real.instAddCommMonoid
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
              (@Pi.Function.module.{0, 0, 0} (Fin m) Real Real Real.semiring Real.instAddCommMonoid
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
              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
            A))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.finiteMaxRadialBasin, ``EJob10.Contract01),
    (``BfgsVerification.RadialPower.mixed_linear_powers_radial, ``EJob10.Contract02),
    (``BfgsVerification.RadialPower.mixed_powers_radial, ``EJob10.Contract03),
    (``BfgsVerification.AdmissibleBFGSRun.mixed_powers_convergence, ``EJob10.Contract04),
    (``BfgsVerification.RadialPower.sumObjective_inward, ``EJob10.Contract05),
    (``BfgsVerification.RadialPower.composed_gauge_homogeneous, ``EJob10.Contract06)]
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
