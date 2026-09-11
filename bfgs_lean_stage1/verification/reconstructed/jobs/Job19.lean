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

def EJob19.Contract01 : Prop :=
∀ (j : Nat) {ε : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LE.le.{0} Real Real.instLE ε
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (BfgsVerification.AccumulatingKinks.knot j)
          (@OfNat.ofNat.{0} Real 8
            (@instOfNatAtLeastTwo.{0} Real 8 Real.instNatCast
              (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 6 (instOfNatNat 6)))))) →
      @BfgsVerification.TransportedCertificate.EligiblePair (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
        BfgsVerification.AccumulatingKinks.coordinateObjective
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real 4
            (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
              (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real 2
            (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
              (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
        (BfgsVerification.AccumulatingKinks.crossingX j ε) (BfgsVerification.AccumulatingKinks.crossingZ j ε)
        (BfgsVerification.AccumulatingKinks.crossingG j ε) (BfgsVerification.AccumulatingKinks.crossingH j ε)

def EJob19.Contract02 : Prop :=
∀ (j : Nat) (ε : Real),
  @Eq.{1} Real
    (@BfgsVerification.TransportedCertificate.pairCurvature (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
      (BfgsVerification.AccumulatingKinks.crossingX j ε) (BfgsVerification.AccumulatingKinks.crossingZ j ε)
      (BfgsVerification.AccumulatingKinks.crossingG j ε) (BfgsVerification.AccumulatingKinks.crossingH j ε))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real 6
            (@instOfNatAtLeastTwo.{0} Real 6 Real.instNatCast
              (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)))))
          (BfgsVerification.AccumulatingKinks.knot j))
        ε)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) ε
          (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))

def EJob19.Contract03 : Prop :=
∀ (j : Nat),
  @Filter.Tendsto.{0, 0} Real Real
    (fun (ε : Real) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (BfgsVerification.AccumulatingKinks.crossingH j ε
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) 0)))
            (BfgsVerification.AccumulatingKinks.crossingG j ε
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) 0)))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (BfgsVerification.AccumulatingKinks.crossingZ j ε
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) 0)))
              (BfgsVerification.AccumulatingKinks.crossingX j ε
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) 0)))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (BfgsVerification.AccumulatingKinks.crossingH j ε
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) 0)))
            (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
    (@nhdsWithin.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
      (@Set.Ioi.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))))
    (@Filter.atTop.{0} Real Real.instPreorder)

def EJob19.Contract04 : Prop :=
∀ {K : Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))},
  @Membership.mem.{0, 0} (Set.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
      (Filter.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
      (@Filter.instMembership.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
      (@nhds.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0
          (@Zero.toOfNat0.{0} (BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
            (@Pi.instZero.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) => Real.instZero))))
      K →
    Not
      (@BfgsVerification.TransportedCertificate.HasBandCertificates (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
        BfgsVerification.AccumulatingKinks.coordinateObjective K
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real 4
            (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
              (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real 2
            (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
              (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.AccumulatingKinks.crossing_eligible, ``EJob19.Contract01),
    (``BfgsVerification.AccumulatingKinks.crossing_curvature, ``EJob19.Contract02),
    (``BfgsVerification.AccumulatingKinks.crossing_quotient_tendsto, ``EJob19.Contract03),
    (``BfgsVerification.AccumulatingKinks.every_neighborhood_no_certificates, ``EJob19.Contract04)]
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
