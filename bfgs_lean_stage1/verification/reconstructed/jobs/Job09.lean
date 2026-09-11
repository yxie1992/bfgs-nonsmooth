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

def EJob09.Contract01.{u_1} : Prop :=
∀ {n : Nat} {ι : Type u_1} [inst : Fintype.{u_1} ι] {m : ι → Nat} {F : BfgsVerification.Vec n → Real},
  @ConvexOn.{0, 0, 0} Real (BfgsVerification.Vec n) Real Real.semiring Real.partialOrder
      (@Pi.addCommMonoid.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommMonoid)
      Real.instAddCommMonoid Real.partialOrder
      (@Function.hasSMul.{0, 0, 0} (Fin n) Real Real
        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring)))
      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
        (@Algebra.id.{0} Real Real.instCommSemiring))
      (@Set.univ.{0} (BfgsVerification.Vec n)) F →
    ∀ (a : (i : ι) → Fin (m i) → BfgsVerification.Vec n) (b : (i : ι) → Fin (m i) → Real)
      (V : ι → Set.{0} (BfgsVerification.Vec n)) (f : ι → BfgsVerification.Vec n → Real),
      (∀ (i : ι),
          @IsOpen.{0} (BfgsVerification.Vec n)
            (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (V i)) →
        (∀ (i : ι), @BfgsVerification.CenteredSmoothSublinear.LocallyC11On n (V i) (f i)) →
          ∀ {U : Set.{0} (BfgsVerification.Vec n)},
            @IsOpen.{0} (BfgsVerification.Vec n)
                (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                U →
              ∀ {star : BfgsVerification.Vec n},
                @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                    (@Set.instMembership.{0} (BfgsVerification.Vec n)) U star →
                  (∀ (i : ι),
                      @HasSubset.Subset.{0} (Set.{0} (BfgsVerification.Vec n))
                        (@Set.instHasSubset.{0} (BfgsVerification.Vec n))
                        (@Inter.inter.{0} (Set.{0} (BfgsVerification.Vec n))
                          (@Set.instInter.{0} (BfgsVerification.Vec n)) U
                          (@BfgsVerification.ConvexCellRadial.polyhedron n (m i) (a i) (b i)))
                        (V i)) →
                    (∀ (x : BfgsVerification.Vec n),
                        @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                            (@Set.instMembership.{0} (BfgsVerification.Vec n)) U x →
                          ∃ (i : ι),
                            @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                              (@Set.instMembership.{0} (BfgsVerification.Vec n))
                              (@BfgsVerification.ConvexCellRadial.polyhedron n (m i) (a i) (b i)) x) →
                      (∀ (i : ι) (x : BfgsVerification.Vec n),
                          @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                              (@Set.instMembership.{0} (BfgsVerification.Vec n)) U x →
                            @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                                (@Set.instMembership.{0} (BfgsVerification.Vec n))
                                (@BfgsVerification.ConvexCellRadial.polyhedron n (m i) (a i) (b i)) x →
                              @Eq.{1} Real (F x) (f i x)) →
                        (∀ (x : BfgsVerification.Vec n), @LE.le.{0} Real Real.instLE (F star) (F x)) →
                          (∀ (x : BfgsVerification.Vec n),
                              @Eq.{1} Real (F x) (F star) → @Eq.{1} (BfgsVerification.Vec n) x star) →
                            ∃ (δ : Real),
                              And
                                (@LT.lt.{0} Real Real.instLT
                                  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) δ)
                                (∀ (R : BfgsVerification.AdmissibleBFGSRun n F),
                                  @LE.le.{0} Real Real.instLE
                                      (F
                                        (@BfgsVerification.AdmissibleBFGSRun.x n F R
                                          (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (F star)
                                        δ) →
                                    And
                                      (∀ (k : Nat),
                                        @Membership.mem.{0, 0} (BfgsVerification.Vec n)
                                          (Set.{0} (BfgsVerification.Vec n))
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
                                            (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                              fun (i : Fin n) =>
                                              @UniformSpace.toTopologicalSpace.{0} Real
                                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                            star))))

def EJob09.Contract02.{u_1} : Prop :=
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
    ∀ (a : (i : ι) → Fin (m i) → BfgsVerification.Vec n) (b : (i : ι) → Fin (m i) → Real)
      (Q : ι → BfgsVerification.Mat n) (c : ι → BfgsVerification.Vec n) (d : ι → Real)
      {U : Set.{0} (BfgsVerification.Vec n)},
      @IsOpen.{0} (BfgsVerification.Vec n)
          (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          U →
        ∀ {star : BfgsVerification.Vec n},
          @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
              (@Set.instMembership.{0} (BfgsVerification.Vec n)) U star →
            @BfgsVerification.CenteredSmoothSublinear.LocallyC11On n U ψ →
              (∀ (x : BfgsVerification.Vec n),
                  @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                      (@Set.instMembership.{0} (BfgsVerification.Vec n)) U x →
                    ∃ (i : ι),
                      @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                        (@Set.instMembership.{0} (BfgsVerification.Vec n))
                        (@BfgsVerification.ConvexCellRadial.polyhedron n (m i) (a i) (b i)) x) →
                (∀ (i : ι) (x : BfgsVerification.Vec n),
                    @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                        (@Set.instMembership.{0} (BfgsVerification.Vec n)) U x →
                      @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
                          (@Set.instMembership.{0} (BfgsVerification.Vec n))
                          (@BfgsVerification.ConvexCellRadial.polyhedron n (m i) (a i) (b i)) x →
                        @Eq.{1} Real (F x)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ψ x)
                            (@BfgsVerification.ConvexCellRadial.quadratic n (Q i) (c i) (d i) x))) →
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

def EJob09.Contract03 : Prop :=
∀ {n r : Nat} (A : Matrix.{0, 0, 0} (Fin r) (Fin n) Real) (hA : @BfgsVerification.AffineProjection.FullRowRank n r A)
  (F : BfgsVerification.Vec r → Real)
  (R :
    BfgsVerification.AdmissibleBFGSRun n fun (x : BfgsVerification.Vec n) =>
      F
        (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
          (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                  (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
          (Fin.fintype n) A x))
  (zstar : BfgsVerification.Vec r),
  @Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec r)
      (@BfgsVerification.AdmissibleBFGSRun.x r F (@BfgsVerification.AffineProjection.projectRun n r A hA F R))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} (BfgsVerification.Vec r)
        (@Pi.topologicalSpace.{0, 0} (Fin r) (fun (a : Fin r) => Real) fun (i : Fin r) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        zstar) →
    And
      (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec n)
        (@BfgsVerification.AdmissibleBFGSRun.x n
          (fun (x : BfgsVerification.Vec n) =>
            F
              (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                      (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                        (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                (Fin.fintype n) A x))
          R)
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} (BfgsVerification.Vec n)
          (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@BfgsVerification.AffineProjection.fiberPoint n r A
            (@BfgsVerification.AdmissibleBFGSRun.H n
              (fun (x : BfgsVerification.Vec n) =>
                F
                  (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) A x))
              R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
            (@BfgsVerification.AdmissibleBFGSRun.x n
              (fun (x : BfgsVerification.Vec n) =>
                F
                  (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) A x))
              R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
            zstar)))
      (And
        (@Eq.{1} (Fin r → Real)
          (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
            (Fin.fintype n) A
            (@BfgsVerification.AffineProjection.fiberPoint n r A
              (@BfgsVerification.AdmissibleBFGSRun.H n
                (fun (x : BfgsVerification.Vec n) =>
                  F
                    (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                      (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                            (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                              (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                      (Fin.fintype n) A x))
                R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
              (@BfgsVerification.AdmissibleBFGSRun.x n
                (fun (x : BfgsVerification.Vec n) =>
                  F
                    (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                      (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                            (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                              (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                      (Fin.fintype n) A x))
                R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
              zstar))
          zstar)
        (∀ (x : BfgsVerification.Vec n),
          @Eq.{1} (Fin r → Real)
              (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                      (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                        (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                (Fin.fintype n) A x)
              zstar →
            And
              (@LE.le.{0} Real Real.instLE
                (@BfgsVerification.metricEnergy n
                  (@Inv.inv.{0} (BfgsVerification.Mat n)
                    (@Matrix.inv.{0, 0} (Fin n) Real (Fin.fintype n) (instDecidableEqFin n) Real.commRing)
                    (@BfgsVerification.AdmissibleBFGSRun.H n
                      (fun (x : BfgsVerification.Vec n) =>
                        F
                          (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                            (Fin.fintype n) A x))
                      R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
                  (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n) (BfgsVerification.Vec n)
                    (@instHSub.{0} (BfgsVerification.Vec n)
                      (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
                    (@BfgsVerification.AffineProjection.fiberPoint n r A
                      (@BfgsVerification.AdmissibleBFGSRun.H n
                        (fun (x : BfgsVerification.Vec n) =>
                          F
                            (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                              (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                    (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                      (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                              (Fin.fintype n) A x))
                        R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
                      (@BfgsVerification.AdmissibleBFGSRun.x n
                        (fun (x : BfgsVerification.Vec n) =>
                          F
                            (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                              (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                    (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                      (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                              (Fin.fintype n) A x))
                        R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
                      zstar)
                    (@BfgsVerification.AdmissibleBFGSRun.x n
                      (fun (x : BfgsVerification.Vec n) =>
                        F
                          (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                            (Fin.fintype n) A x))
                      R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
                (@BfgsVerification.metricEnergy n
                  (@Inv.inv.{0} (BfgsVerification.Mat n)
                    (@Matrix.inv.{0, 0} (Fin n) Real (Fin.fintype n) (instDecidableEqFin n) Real.commRing)
                    (@BfgsVerification.AdmissibleBFGSRun.H n
                      (fun (x : BfgsVerification.Vec n) =>
                        F
                          (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                            (Fin.fintype n) A x))
                      R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
                  (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n) (BfgsVerification.Vec n)
                    (@instHSub.{0} (BfgsVerification.Vec n)
                      (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
                    x
                    (@BfgsVerification.AdmissibleBFGSRun.x n
                      (fun (x : BfgsVerification.Vec n) =>
                        F
                          (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                            (Fin.fintype n) A x))
                      R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
              (Iff
                (@Eq.{1} Real
                  (@BfgsVerification.metricEnergy n
                    (@Inv.inv.{0} (BfgsVerification.Mat n)
                      (@Matrix.inv.{0, 0} (Fin n) Real (Fin.fintype n) (instDecidableEqFin n) Real.commRing)
                      (@BfgsVerification.AdmissibleBFGSRun.H n
                        (fun (x : BfgsVerification.Vec n) =>
                          F
                            (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                              (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                    (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                      (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                              (Fin.fintype n) A x))
                        R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
                    (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n) (BfgsVerification.Vec n)
                      (@instHSub.{0} (BfgsVerification.Vec n)
                        (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
                      x
                      (@BfgsVerification.AdmissibleBFGSRun.x n
                        (fun (x : BfgsVerification.Vec n) =>
                          F
                            (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                              (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                    (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                      (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                              (Fin.fintype n) A x))
                        R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
                  (@BfgsVerification.metricEnergy n
                    (@Inv.inv.{0} (BfgsVerification.Mat n)
                      (@Matrix.inv.{0, 0} (Fin n) Real (Fin.fintype n) (instDecidableEqFin n) Real.commRing)
                      (@BfgsVerification.AdmissibleBFGSRun.H n
                        (fun (x : BfgsVerification.Vec n) =>
                          F
                            (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                              (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                    (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                      (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                              (Fin.fintype n) A x))
                        R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
                    (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n) (BfgsVerification.Vec n)
                      (@instHSub.{0} (BfgsVerification.Vec n)
                        (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
                      (@BfgsVerification.AffineProjection.fiberPoint n r A
                        (@BfgsVerification.AdmissibleBFGSRun.H n
                          (fun (x : BfgsVerification.Vec n) =>
                            F
                              (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                                (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                      (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                        (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                                (Fin.fintype n) A x))
                          R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
                        (@BfgsVerification.AdmissibleBFGSRun.x n
                          (fun (x : BfgsVerification.Vec n) =>
                            F
                              (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                                (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                      (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                        (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                                (Fin.fintype n) A x))
                          R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
                        zstar)
                      (@BfgsVerification.AdmissibleBFGSRun.x n
                        (fun (x : BfgsVerification.Vec n) =>
                          F
                            (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                              (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                    (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                      (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                              (Fin.fintype n) A x))
                        R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
                (@Eq.{1} (BfgsVerification.Vec n) x
                  (@BfgsVerification.AffineProjection.fiberPoint n r A
                    (@BfgsVerification.AdmissibleBFGSRun.H n
                      (fun (x : BfgsVerification.Vec n) =>
                        F
                          (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                            (Fin.fintype n) A x))
                      R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
                    (@BfgsVerification.AdmissibleBFGSRun.x n
                      (fun (x : BfgsVerification.Vec n) =>
                        F
                          (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                            (Fin.fintype n) A x))
                      R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
                    zstar)))))

def EJob09.Contract04 : Prop :=
And (Countable.{1} BfgsVerification.LStepEmbedding.CountableIndex)
  (And
    (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
      @IsGreatest.{0} Real Real.instLE
        (@Set.range.{0, 1} Real BfgsVerification.LStepEmbedding.CountableIndex
          fun (j : BfgsVerification.LStepEmbedding.CountableIndex) =>
          @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@DFunLike.coe.{1, 1, 1}
              (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                Real.instAddCommMonoid
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
              (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (fun (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
              (@ContinuousLinearMap.funLike.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                Real.instAddCommMonoid
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
              (BfgsVerification.LStepEmbedding.countableLinear j) x)
            (BfgsVerification.LStepEmbedding.countableOffset j))
        (BfgsVerification.LStepEmbedding.residual x))
    (And
      (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
        @Ne.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) x
            (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
              (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instZero))) →
          @BfgsVerification.FiniteAffineLocal.PolyhedralGerm (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
            BfgsVerification.LStepEmbedding.residual x)
      (∀ (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
        @DifferentiableAt.{0, 0, 0} Real
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
            BfgsVerification.LStepEmbedding.objective x →
          And
            (@BfgsVerification.FiniteAffineLocal.AffineGerm (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              BfgsVerification.LStepEmbedding.residual x)
            (And
              (@HasFDerivAt.{0, 0, 0} Real
                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@ContinuousLinearMap.{0, 0, 0, 0} Real Real
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@NontriviallyNormedField.toNormedField.{0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                  (@DivisionSemiring.toSemiring.{0} Real
                    (@Semifield.toDivisionSemiring.{0} Real
                      (@Field.toSemifield.{0} Real
                        (@NormedField.toField.{0} Real
                          (@NontriviallyNormedField.toNormedField.{0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                  (@RingHom.id.{0} Real
                    (@Semiring.toNonAssocSemiring.{0} Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@AddCommGroup.toAddCommMonoid.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup))
                  Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
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
                (@ContinuousLinearMap.addCommGroup.{0, 0, 0, 0} Real Real.instRing Real Real.instRing
                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
                  Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@SeminormedAddCommGroup.toAddCommGroup.{0} Real
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))
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
                  (@RingHom.id.{0} Real
                    (@Semiring.toNonAssocSemiring.{0} Real
                      (@DivisionSemiring.toSemiring.{0} Real
                        (@Semifield.toDivisionSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
                  instIsTopologicalAddGroupReal)
                (@ContinuousLinearMap.module.{0, 0, 0, 0, 0} Real Real Real Real.semiring Real.semiring Real.semiring
                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
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
                  Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
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
                  BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_3
                  BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_4
                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                  BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_5)
                (@ContinuousLinearMap.topologicalSpace.{0, 0, 0, 0} Real Real Real.normedField Real.normedField
                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                  (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
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
                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  instIsTopologicalAddGroupReal)
                (@fderiv.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
                  BfgsVerification.LStepEmbedding.objective)
                (@HSMul.hSMul.{0, 0, 0} Real
                  (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                    (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      Real.instAddCommMonoid
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                    (@ContinuousLinearMap.topologicalSpace.{0, 0, 0, 0} Real Real Real.normedField Real.normedField
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
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
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      instIsTopologicalAddGroupReal)
                    (@ContinuousLinearMap.addCommMonoid.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      Real.instAddCommMonoid
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
                      BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_5)
                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                    (@ContinuousLinearMap.module.{0, 0, 0, 0, 0} Real Real Real Real.semiring Real.semiring
                      Real.semiring (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                      Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
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
                      BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_3
                      BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_4
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_5))
                  (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                    (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                      fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                    (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      Real.instAddCommMonoid
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                    (@ContinuousLinearMap.topologicalSpace.{0, 0, 0, 0} Real Real Real.normedField Real.normedField
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                      (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
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
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      instIsTopologicalAddGroupReal)
                    (@ContinuousLinearMap.addCommMonoid.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      Real.instAddCommMonoid
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
                      BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_5)
                    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                    (@ContinuousLinearMap.module.{0, 0, 0, 0, 0} Real Real Real Real.semiring Real.semiring
                      Real.semiring (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                      Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
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
                      BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_3
                      BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_4
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_5))
                  (@instHSMul.{0, 0} Real
                    (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        Real.instAddCommMonoid
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                      (@ContinuousLinearMap.topologicalSpace.{0, 0, 0, 0} Real Real Real.normedField Real.normedField
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
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
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        instIsTopologicalAddGroupReal)
                      (@ContinuousLinearMap.addCommMonoid.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        Real.instAddCommMonoid
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
                        BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_5)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                      (@ContinuousLinearMap.module.{0, 0, 0, 0, 0} Real Real Real Real.semiring Real.semiring
                        Real.semiring (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                        Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
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
                        BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_3
                        BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_4
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_5))
                    (@ContinuousLinearMap.instSMul.{0, 0, 0, 0, 0} Real Real Real.semiring Real.semiring
                      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                      (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                        @UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                        fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                      (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        Real.instAddCommMonoid
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                      (@ContinuousLinearMap.topologicalSpace.{0, 0, 0, 0} Real Real Real.normedField Real.normedField
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                        (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommGroup)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
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
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        instIsTopologicalAddGroupReal)
                      (@ContinuousLinearMap.addCommMonoid.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        Real.instAddCommMonoid
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
                        BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_5)
                      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                      (@ContinuousLinearMap.module.{0, 0, 0, 0, 0} Real Real Real Real.semiring Real.semiring
                        Real.semiring (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                        Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
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
                        BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_3
                        BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_4
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_5)
                      Real Real.instMonoid
                      (@ContinuousLinearMap.distribMulAction.{0, 0, 0, 0, 0} Real Real Real Real.semiring Real.semiring
                        Real.instMonoid (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                          @UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
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
                              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))))
                        Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
                            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike)))
                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                        (@Module.toDistribMulAction.{0, 0} Real Real Real.semiring Real.instAddCommMonoid
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
                        BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_6
                        BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_3
                        BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_5)
                      BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_7
                      BfgsVerification.LStepEmbeddingPolyhedralTarget._proof_8))
                  BfgsVerification.LEmbedding.mu BfgsVerification.LQuadraticSeed.pairingMap)
                x)
              (@Eq.{1} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@BfgsVerification.RadialHessian.matrix (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                  BfgsVerification.LStepEmbedding.objective x)
                (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@instHSMul.{0, 0} Real (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@Matrix.smul.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                      (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                        (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                        (@Algebra.id.{0} Real Real.instCommSemiring))))
                  BfgsVerification.LEmbedding.mu
                  (@OfNat.ofNat.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
                    (@One.toOfNat1.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Matrix.one.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                        (instDecidableEqFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.instZero
                        Real.instOne)))))))))

def EJob09.Contract05 : Prop :=
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

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.polyhedralBasin, ``EJob09.Contract01),
    (``BfgsVerification.smoothPLQBasin, ``EJob09.Contract02),
    (``BfgsVerification.linearImageLifting, ``EJob09.Contract03),
    (``BfgsVerification.lStepEmbeddingPolyhedral, ``EJob09.Contract04),
    (``BfgsVerification.lScalarRegularity, ``EJob09.Contract05)]
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
