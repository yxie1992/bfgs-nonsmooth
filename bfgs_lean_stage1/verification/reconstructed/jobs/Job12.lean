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

def EJob12.Contract01.{u_1} : Prop :=
∀ {ι : Type u_1} {l : Filter.{u_1} ι} [inst : @Filter.NeBot.{u_1} ι l] {n r : Nat} {F : BfgsVerification.Vec n → Real}
  {K : Set.{0} (BfgsVerification.Vec n)} {fstar c₁ c₂ η : Real},
  @LT.lt.{0} Real Real.instLT c₂ (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) →
    ∀ (z h : ι → BfgsVerification.Vec n) (x g : ι → Fin r → BfgsVerification.Vec n) (coeff : ι → Fin r → Real),
      (∀ (a : ι),
          @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
            (@Set.instMembership.{0} (BfgsVerification.Vec n))
            (@BfgsVerification.TransportedCertificate.positiveBand n F K fstar η) (z a)) →
        (∀ (a : ι) (j : Fin r),
            @Membership.mem.{0, 0} (BfgsVerification.Vec n) (Set.{0} (BfgsVerification.Vec n))
              (@Set.instMembership.{0} (BfgsVerification.Vec n))
              (@BfgsVerification.TransportedCertificate.positiveBand n F K fstar η) (x a j)) →
          (∀ (a : ι),
              @HasFDerivAt.{0, 0, 0} Real
                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)
                (BfgsVerification.Vec n)
                (@Pi.addCommGroup.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)
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
                (@Pi.topologicalSpace.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
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
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                F (@BfgsVerification.gradientFunctional n (h a)) (z a)) →
            (∀ (a : ι) (j : Fin r),
                @BfgsVerification.TransportedCertificate.EligiblePair n F c₁ c₂ (x a j) (z a) (g a j) (h a)) →
              (∀ (j : Fin r),
                  @Filter.Tendsto.{u_1, 0} ι Real
                    (fun (a : ι) => @BfgsVerification.TransportedCertificate.pairDecrease n (x a j) (z a) (g a j)) l
                    (@nhds.{0} Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                @Filter.Eventually.{u_1} ι
                    (fun (a : ι) =>
                      @Eq.{1} (BfgsVerification.Vec n) (h a)
                        (∑ j : Fin r,
                          @HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Vec n) (BfgsVerification.Vec n)
                            (@instHSMul.{0, 0} Real (BfgsVerification.Vec n)
                              (@Function.hasSMul.{0, 0, 0} (Fin n) Real Real
                                (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                                  (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                                  (@Algebra.id.{0} Real Real.instCommSemiring))))
                            (coeff a j)
                            (@HSub.hSub.{0, 0, 0} (BfgsVerification.Vec n) (BfgsVerification.Vec n)
                              (BfgsVerification.Vec n)
                              (@instHSub.{0} (BfgsVerification.Vec n)
                                (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
                              (h a) (g a j))))
                    l →
                  @Filter.Tendsto.{u_1, 0} ι Real
                      (fun (a : ι) =>
                        ∑ j : Fin r,
                          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@abs.{0} Real Real.lattice Real.instAddGroup (coeff a j))
                            (@BfgsVerification.TransportedCertificate.pairCurvature n (x a j) (z a) (g a j) (h a)).sqrt)
                      l
                      (@nhds.{0} Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))) →
                    Not (Nonempty.{1} (@BfgsVerification.TransportedCertificate.BandCertificate n F K fstar c₁ c₂ η))

def EJob12.Contract02 : Prop :=
∀ {n : Nat} {F : BfgsVerification.Vec n → Real} {c₁ c₂ : Real} {x z g h : BfgsVerification.Vec n},
  @BfgsVerification.TransportedCertificate.EligiblePair n F c₁ c₂ x z g h →
    ∃ (H : BfgsVerification.Mat n),
      And (@Matrix.PosDef.{0, 0} (Fin n) Real (Fin.fintype n) Real.commRing Real.partialOrder instStarRingReal H)
        (And
          (@Eq.{1} (BfgsVerification.Vec n)
            (@BfgsVerification.bfgsStep n H g (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
            (@BfgsVerification.TransportedCertificate.pairStep n x z))
          (@Eq.{1} Real (@BfgsVerification.metricEnergy n H g)
            (@BfgsVerification.TransportedCertificate.pairDecrease n x z g)))

def EJob12.Contract03 : Prop :=
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

def EJob12.Contract04 : Prop :=
∀ {n : Nat} (F : BfgsVerification.Vec n → Real) (K : Set.{0} (BfgsVerification.Vec n)) (fstar c₁ c₂ η δ : Real),
  @LT.lt.{0} Real Real.instLT c₂ (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) δ →
      Iff
        (∃ (B : @BfgsVerification.TransportedCertificate.VisibilitySecantCertificate n F K fstar c₁ c₂ η),
          @Eq.{1} Real (@BfgsVerification.TransportedCertificate.VisibilitySecantCertificate.δ n F K fstar c₁ c₂ η B) δ)
        (@LT.lt.{0} ENNReal (@Preorder.toLT.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
          (@OfNat.ofNat.{0} ENNReal 0 (@Zero.toOfNat0.{0} ENNReal instENNRealZero))
          (⨅ (z : @BfgsVerification.PointwiseFeasibility.BandPoint n F K fstar η),
            @BfgsVerification.PointwiseFeasibility.sourceCapacity n F K fstar c₁ c₂ η δ z))

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.TransportedCertificate.incoming_jump_no_band_certificate, ``EJob12.Contract01),
    (``BfgsVerification.eligiblePairRealizability, ``EJob12.Contract02),
    (``BfgsVerification.AccumulatingKinks.every_neighborhood_no_certificates, ``EJob12.Contract03),
    (``BfgsVerification.PointwiseFeasibility.visibility_secant_iff_source_capacity, ``EJob12.Contract04)]
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
