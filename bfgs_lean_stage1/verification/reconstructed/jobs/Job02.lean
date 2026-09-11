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

def EJob02.Contract01 : Prop :=
∀ (H : BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
  (s y : BfgsVerification.Vec (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))),
  @Ne.{1} Real (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) y s)
      (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) →
    @Eq.{1} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
      (@BfgsVerification.inverseBFGS (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) H s y)
      (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@instHAdd.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@Matrix.add.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real.instAdd))
        (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@instHSMul.{0, 0} Real (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Matrix.smul.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
              (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                (@Algebra.id.{0} Real Real.instCommSemiring))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (BfgsVerification.PlanarUpdate.perp s)
              (@Matrix.mulVec.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
                (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                      (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                        (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                (Fin.fintype (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) H (BfgsVerification.PlanarUpdate.perp s)))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) y s)
              (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
          (@BfgsVerification.outer (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (BfgsVerification.PlanarUpdate.perp y)
            (BfgsVerification.PlanarUpdate.perp y)))
        (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
          (@instHSMul.{0, 0} Real (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Matrix.smul.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
              (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                (@Algebra.id.{0} Real Real.instCommSemiring))))
          (@Inv.inv.{0} Real Real.instInv (@BfgsVerification.dot (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) y s))
          (@BfgsVerification.outer (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) s s)))

def EJob02.Contract02 : Prop :=
∀ {n : Nat} {H : BfgsVerification.Mat n},
  @Matrix.PosDef.{0, 0} (Fin n) Real (Fin.fintype n) Real.commRing Real.partialOrder instStarRingReal H →
    ∀ {g : BfgsVerification.Vec n},
      @Ne.{1} (BfgsVerification.Vec n) g
          (@OfNat.ofNat.{0} (BfgsVerification.Vec n) 0
            (@Zero.toOfNat0.{0} (BfgsVerification.Vec n)
              (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instZero))) →
        ∀ (y : BfgsVerification.Vec n) {α : Real},
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) α →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
                (@BfgsVerification.dot n y (@BfgsVerification.bfgsStep n H g α)) →
              @Eq.{1} (BfgsVerification.Mat n)
                (@Inv.inv.{0} (BfgsVerification.Mat n)
                  (@Matrix.inv.{0, 0} (Fin n) Real (Fin.fintype n) (instDecidableEqFin n) Real.commRing)
                  (@BfgsVerification.inverseBFGS n H (@BfgsVerification.bfgsStep n H g α) y))
                (@HAdd.hAdd.{0, 0, 0} (BfgsVerification.Mat n) (BfgsVerification.Mat n) (BfgsVerification.Mat n)
                  (@instHAdd.{0} (BfgsVerification.Mat n) (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                  (@HSub.hSub.{0, 0, 0} (BfgsVerification.Mat n) (BfgsVerification.Mat n) (BfgsVerification.Mat n)
                    (@instHSub.{0} (BfgsVerification.Mat n) (@Matrix.sub.{0, 0, 0} (Fin n) (Fin n) Real Real.instSub))
                    (@Inv.inv.{0} (BfgsVerification.Mat n)
                      (@Matrix.inv.{0, 0} (Fin n) Real (Fin.fintype n) (instDecidableEqFin n) Real.commRing) H)
                    (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Mat n) (BfgsVerification.Mat n)
                      (@instHSMul.{0, 0} Real (BfgsVerification.Mat n)
                        (@Matrix.smul.{0, 0, 0, 0} (Fin n) (Fin n) Real Real
                          (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                            (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                            (@Algebra.id.{0} Real Real.instCommSemiring))))
                      (@Inv.inv.{0} Real Real.instInv (@BfgsVerification.metricEnergy n H g))
                      (@BfgsVerification.outer n g g)))
                  (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Mat n) (BfgsVerification.Mat n)
                    (@instHSMul.{0, 0} Real (BfgsVerification.Mat n)
                      (@Matrix.smul.{0, 0, 0, 0} (Fin n) (Fin n) Real Real
                        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                          (@Algebra.id.{0} Real Real.instCommSemiring))))
                    (@Inv.inv.{0} Real Real.instInv (@BfgsVerification.dot n y (@BfgsVerification.bfgsStep n H g α)))
                    (@BfgsVerification.outer n y y)))

def EJob02.Contract03 : Prop :=
@Eq.{1} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
  (BfgsVerification.SeedCycle.update
    (BfgsVerification.SeedCycle.update
      (BfgsVerification.SeedCycle.update
        (@OfNat.ofNat.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
          (@One.toOfNat1.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
            (@Matrix.one.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.instZero Real.instOne)))
        BfgsVerification.SeedCycle.g0 BfgsVerification.SeedCycle.g1
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
      BfgsVerification.SeedCycle.g1
      (BfgsVerification.SeedCycle.g2
        (BfgsVerification.AlgebraicSeed.root
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0)))
        (BfgsVerification.AlgebraicSeed.root
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 1))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))
    (BfgsVerification.SeedCycle.g2
      (BfgsVerification.AlgebraicSeed.root
        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0)))
      (BfgsVerification.AlgebraicSeed.root
        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 1))))
    BfgsVerification.SeedCycle.g0
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real 16
        (@instOfNatAtLeastTwo.{0} Real 16 Real.instNatCast
          (@instNatAtLeastTwo (@OfNat.ofNat.{0} Nat 14 (instOfNatNat 14)))))))
  (@HSMul.hSMul.{0, 0, 0} Real (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
    (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
    (@instHSMul.{0, 0} Real (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
      (@Matrix.smul.{0, 0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Real
        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring) (@Algebra.id.{0} Real Real.instCommSemiring))))
    (BfgsVerification.AlgebraicSeed.ratio
      (BfgsVerification.AlgebraicSeed.root
        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0)))
      (BfgsVerification.AlgebraicSeed.root
        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 1))))
    (@OfNat.ofNat.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1
      (@One.toOfNat1.{0} (BfgsVerification.Mat (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
        (@Matrix.one.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real.instZero Real.instOne))))

def EJob02.Contract04 : Prop :=
∀ {n : Nat} {H : BfgsVerification.Mat n},
  @Matrix.PosDef.{0, 0} (Fin n) Real (Fin.fintype n) Real.commRing Real.partialOrder instStarRingReal H →
    ∀ (s y : BfgsVerification.Vec n),
      @Ne.{1} Real (@BfgsVerification.dot n y s) (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Eq.{1} Real
          (@Matrix.det.{0, 0} (Fin n) (instDecidableEqFin n) (Fin.fintype n) Real Real.commRing
            (@BfgsVerification.inverseBFGS n H s y))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@BfgsVerification.dot n s
                (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
                  (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                        (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                          (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                  (Fin.fintype n)
                  (@Inv.inv.{0} (BfgsVerification.Mat n)
                    (@Matrix.inv.{0, 0} (Fin n) Real (Fin.fintype n) (instDecidableEqFin n) Real.commRing) H)
                  s))
              (@BfgsVerification.dot n y s))
            (@Matrix.det.{0, 0} (Fin n) (instDecidableEqFin n) (Fin.fintype n) Real Real.commRing H))

def EJob02.Contract05 : Prop :=
∀ {n : Nat} {H : BfgsVerification.Mat n},
  @Matrix.PosDef.{0, 0} (Fin n) Real (Fin.fintype n) Real.commRing Real.partialOrder instStarRingReal H →
    ∀ (s y : BfgsVerification.Vec n),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
          (@BfgsVerification.dot n y s) →
        @Matrix.PosDef.{0, 0} (Fin n) Real (Fin.fintype n) Real.commRing Real.partialOrder instStarRingReal
          (@BfgsVerification.inverseBFGS n H s y)

def EJob02.Contract06 : Prop :=
∀ {n : Nat} (H : BfgsVerification.Mat n) (s y : BfgsVerification.Vec n),
  @Ne.{1} Real (@BfgsVerification.dot n y s) (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) →
    @Eq.{1} (Fin n → Real)
      (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
        (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
              (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
        (Fin.fintype n) (@BfgsVerification.inverseBFGS n H s y) y)
      s

def EJob02.Contract07 : Prop :=
∀ {n : Nat} {H : BfgsVerification.Mat n},
  @Matrix.PosDef.{0, 0} (Fin n) Real (Fin.fintype n) Real.commRing Real.partialOrder instStarRingReal H →
    ∀ (s y : BfgsVerification.Vec n),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
          (@BfgsVerification.dot n y s) →
        @Eq.{1} (Fin n → Real)
          (@Matrix.mulVec.{0, 0, 0} (Fin n) (Fin n) Real
            (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} Real
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} Real
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
            (Fin.fintype n)
            (@Inv.inv.{0} (BfgsVerification.Mat n)
              (@Matrix.inv.{0, 0} (Fin n) Real (Fin.fintype n) (instDecidableEqFin n) Real.commRing)
              (@BfgsVerification.inverseBFGS n H s y))
            s)
          y

open Lean Elab Command in
run_cmd do
  let pairs : Array (Name × Name) := #[
    (``BfgsVerification.PlanarUpdate.inverse_formula, ``EJob02.Contract01),
    (``BfgsVerification.hessianUpdate, ``EJob02.Contract02),
    (``BfgsVerification.SeedCycle.source_cycle, ``EJob02.Contract03),
    (``BfgsVerification.inverseBFGS_det, ``EJob02.Contract04),
    (``BfgsVerification.inverseBFGS_posDef, ``EJob02.Contract05),
    (``BfgsVerification.EReconstruction.inverse_update_secant, ``EJob02.Contract06),
    (``BfgsVerification.EReconstruction.hessian_update_secant, ``EJob02.Contract07)]
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
