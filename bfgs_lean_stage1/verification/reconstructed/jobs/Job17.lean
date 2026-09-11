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

def EJob17.Contract01 : Prop :=
∀
  (R :
    BfgsVerification.AdmissibleBFGSRun (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
      BfgsVerification.PlanarQuadraticExample.objective),
  @LT.lt.{0} Real Real.instLT
      (BfgsVerification.PlanarQuadraticExample.objective
        (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
          BfgsVerification.PlanarQuadraticExample.objective R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 100
          (@instOfNatAtLeastTwo.{0} Real 100 Real.instNatCast
            BfgsVerification.PlanarQuadraticCoefficientsTarget._proof_5))) →
    And
      (@Filter.Tendsto.{0, 0} Nat Real
        (fun (k : Nat) =>
          BfgsVerification.PlanarQuadraticExample.objective
            (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              BfgsVerification.PlanarQuadraticExample.objective R k))
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
      (@Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
          BfgsVerification.PlanarQuadraticExample.objective R)
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

def EJob17.Contract02 : Prop :=
∀ {F : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) → Real}
  (R : BfgsVerification.AdmissibleBFGSRun (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F)
  (star : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
  (∀ (z : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))), @LE.le.{0} Real Real.instLE (F star) (F z)) →
    ∀ (b : Real),
      @IsCompact.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@setOf.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            fun (x : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
            @LE.le.{0} Real Real.instLE (F x) b) →
        @LE.le.{0} Real Real.instLE
            (F
              (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F R
                (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
            b →
          (∀ (ℓ : Real),
              @LT.lt.{0} Real Real.instLT (F star) ℓ →
                @LE.le.{0} Real Real.instLE ℓ b →
                  ∀ (x y : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                    @HasSubset.Subset.{0} (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                        (@Set.instHasSubset.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
                        (@segment.{0, 0} Real (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          Real.semiring Real.partialOrder
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.instAddCommMonoid)
                          (@Function.hasSMul.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
                            (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                              (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                              (@Algebra.id.{0} Real Real.instCommSemiring)))
                          x y)
                        (@frontier.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                            @UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@setOf.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            fun (w : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                            @LE.le.{0} Real Real.instLE (F w) ℓ)) →
                      @Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) x y) →
            (∀ (p : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                @LE.le.{0} Real Real.instLE (F p) b →
                  Not
                      (@BfgsVerification.AffineCriticalObjective.IsAffineCritical
                        (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F p) →
                    Or
                      (@ContDiffAt.{0, 0, 0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
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
                            BfgsVerification.PlanarAffineCriticalClusterTarget._proof_1))
                        F p)
                      (BfgsVerification.PlanarCornerCharts.ConvexTwoBranchRegularAt F p)) →
              (∀ (p : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                  @LE.le.{0} Real Real.instLE (F p) b →
                    @BfgsVerification.AffineCriticalObjective.AffineCorrectAt (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                      F p) →
                And
                  (@Filter.Tendsto.{0, 0} Nat Real
                    (fun (k : Nat) =>
                      F (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F R k))
                    (@Filter.atTop.{0} Nat Nat.instPreorder)
                    (@nhds.{0} Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (F star)))
                  (And
                    (@Filter.Tendsto.{0, 0} Nat Real
                      (fun (k : Nat) =>
                        @Metric.infDist.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (@pseudoMetricSpacePi.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                            (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            fun (b : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real.pseudoMetricSpace)
                          (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F R k)
                          (@BfgsVerification.argmin.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            F))
                      (@Filter.atTop.{0} Nat Nat.instPreorder)
                      (@nhds.{0} Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
                    (And
                      (@Filter.Tendsto.{0, 0} Nat Real
                        (fun (k : Nat) =>
                          @BfgsVerification.euclideanSolutionDistance (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F
                            (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F R k))
                        (@Filter.atTop.{0} Nat Nat.instPreorder)
                        (@nhds.{0} Real
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
                      ((∀ (z : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
                          @Eq.{1} Real (F z) (F star) →
                            @Eq.{1} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) z star) →
                        @Filter.Tendsto.{0, 0} Nat (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                          (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) F R)
                          (@Filter.atTop.{0} Nat Nat.instPreorder)
                          (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Real)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) =>
                              @UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                            star))))

def EJob17.Contract03 : Prop :=
∀
  (R :
    BfgsVerification.AdmissibleBFGSRun (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
      BfgsVerification.PlanarQuadraticExample.objective),
  @LT.lt.{0} Real Real.instLT
      (BfgsVerification.PlanarQuadraticExample.objective
        (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
          BfgsVerification.PlanarQuadraticExample.objective R (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 100
          (@instOfNatAtLeastTwo.{0} Real 100 Real.instNatCast
            (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 98 (instOfNatNat 98)))))) →
    ∃ (N : Nat),
      ∀ (k : Nat),
        @GE.ge.{0} Nat instLENat k N →
          @LT.lt.{0} Real Real.instLT
            (BfgsVerification.PlanarQuadraticExample.objective
              (@BfgsVerification.AdmissibleBFGSRun.x (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                BfgsVerification.PlanarQuadraticExample.objective R k))
            (@HPow.hPow.{0, 0, 0} Real Int Real
              (@instHPow.{0, 0} Real Int (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real 10
                (@instOfNatAtLeastTwo.{0} Real 10 Real.instNatCast
                  (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 8 (instOfNatNat 8)))))
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int 45 (@instOfNat 45))))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.planarQuadraticBasin, ``EJob17.Contract01),
    (``BfgsVerification.planarConvergence, ``EJob17.Contract02),
    (``BfgsVerification.EReconstruction.planar_eventual_printed_tolerance, ``EJob17.Contract03)]
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
