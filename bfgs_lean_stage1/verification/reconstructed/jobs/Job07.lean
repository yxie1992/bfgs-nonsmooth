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

def EJob07.Contract01 : Prop :=
∀ {n r : Nat} (A : Matrix.{0, 0, 0} (Fin r) (Fin n) Real),
  @BfgsVerification.AffineProjection.FullRowRank n r A →
    ∀ (F : BfgsVerification.Vec r → Real)
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
      (k : Nat),
      @Eq.{1} (BfgsVerification.Mat r)
        (@BfgsVerification.AffineProjection.compress n r A
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
            R
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
        (@BfgsVerification.inverseBFGS r
          (@BfgsVerification.AffineProjection.compress n r A
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
              R k))
          (@BfgsVerification.bfgsStep r
            (@BfgsVerification.AffineProjection.compress n r A
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
                R k))
            (@BfgsVerification.AffineProjection.projectedGradient n r A F R k)
            (@BfgsVerification.AdmissibleBFGSRun.α n
              (fun (x : BfgsVerification.Vec n) =>
                F
                  (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) A x))
              R k))
          (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec r) (BfgsVerification.Vec r) (BfgsVerification.Vec r)
            (@instHSub.{0} (BfgsVerification.Vec r)
              (@Pi.instSub.{0, 0} (Fin r) (fun (a : Fin r) => Real) fun (i : Fin r) => Real.instSub))
            (@BfgsVerification.AffineProjection.projectedGradient n r A F R
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
            (@BfgsVerification.AffineProjection.projectedGradient n r A F R k)))

def EJob07.Contract02 : Prop :=
∀ {n r : Nat} (A : Matrix.{0, 0, 0} (Fin r) (Fin n) Real),
  @BfgsVerification.AffineProjection.FullRowRank n r A →
    ∀ (F : BfgsVerification.Vec r → Real)
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
      (k : Nat),
      @Eq.{1} (Set.{0} (Fin n → Real))
        (@Set.range.{0, 1} (Fin n → Real) (Fin r → Real)
          (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin r) Real
            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
            (Fin.fintype r)
            (@HMul.hMul.{0, 0, 0} (BfgsVerification.Mat n) (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
              (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin r) Real (Fin.fintype n)
                Real.instMul Real.instAddCommMonoid)
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
                R k)
              (@Matrix.transpose.{0, 0, 0} (Fin r) (Fin n) Real A))))
        (@Set.range.{0, 1} (Fin n → Real) (Fin r → Real)
          (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin r) Real
            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
            (Fin.fintype r)
            (@HMul.hMul.{0, 0, 0} (BfgsVerification.Mat n) (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
              (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin r) Real (Fin.fintype n)
                Real.instMul Real.instAddCommMonoid)
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
              (@Matrix.transpose.{0, 0, 0} (Fin r) (Fin n) Real A))))

def EJob07.Contract03 : Prop :=
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

def EJob07.Contract04 : Prop :=
∀ {n r : Nat} (A : Matrix.{0, 0, 0} (Fin r) (Fin n) Real) (H : BfgsVerification.Mat n) (s : BfgsVerification.Vec n)
  (y : BfgsVerification.Vec r),
  @Eq.{1} (BfgsVerification.Mat r)
    (@BfgsVerification.AffineProjection.compress n r A
      (@BfgsVerification.inverseBFGS n H s
        (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin r) Real
          (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                  (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
          (Fin.fintype r) (@Matrix.transpose.{0, 0, 0} (Fin r) (Fin n) Real A) y)))
    (@BfgsVerification.inverseBFGS r (@BfgsVerification.AffineProjection.compress n r A H)
      (@Matrix.mulVec.{0, 0, 0} (Fin r) (Fin n) Real
        (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
              (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
        (Fin.fintype n) A s)
      y)

def EJob07.Contract05 : Prop :=
∀ {n r : Nat} (A : Matrix.{0, 0, 0} (Fin r) (Fin n) Real),
  @BfgsVerification.AffineProjection.FullRowRank n r A →
    ∀ (R : BfgsVerification.FullBFGSRun n) (gbar : Nat → BfgsVerification.Vec r),
      (∀ (k : Nat),
          @Eq.{1} (Fin n → Real)
            (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin r) Real
              (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                    (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                      (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
              (Fin.fintype r) (@Matrix.transpose.{0, 0, 0} (Fin r) (Fin n) Real A) (gbar k))
            (@BfgsVerification.FullBFGSRun.g n R k)) →
        ∀ (k : Nat),
          @Eq.{1} (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
            (@HMul.hMul.{0, 0, 0} (BfgsVerification.Mat n) (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
              (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin n) (Fin r) Real (Fin.fintype n)
                Real.instMul Real.instAddCommMonoid)
              (@BfgsVerification.FullBFGSRun.H n R k) (@Matrix.transpose.{0, 0, 0} (Fin r) (Fin n) Real A))
            (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin n) (Fin r) Real) (BfgsVerification.Mat r)
              (Matrix.{0, 0, 0} (Fin n) (Fin r) Real)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin r) (Fin r) Real (Fin.fintype r)
                Real.instMul Real.instAddCommMonoid)
              (@BfgsVerification.AffineProjection.lift n r A
                (@BfgsVerification.FullBFGSRun.H n R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
              (@BfgsVerification.AffineProjection.compress n r A (@BfgsVerification.FullBFGSRun.H n R k)))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.AffineProjection.projected_update, ``EJob07.Contract01),
    (``BfgsVerification.AffineProjection.actualImageRange, ``EJob07.Contract02),
    (``BfgsVerification.linearImageLifting, ``EJob07.Contract03),
    (``BfgsVerification.AffineProjection.inverseBFGS_compress, ``EJob07.Contract04),
    (``BfgsVerification.AffineProjection.matrix_lift_invariant, ``EJob07.Contract05)]
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
