import BfgsVerification.NormalSpikeRational
#print BfgsVerification.NormalSpike.RationalSpikeOracleTarget
#check @BfgsVerification.NormalSpike.rationalSpikeOracle
example : BfgsVerification.NormalSpike.RationalSpikeOracleTarget := BfgsVerification.NormalSpike.rationalSpikeOracle
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.NormalSpike.rationalSpikeOracle
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.NormalSpike.RationalSpikeOracleTarget)
  unless ok do throwError "exact target mismatch: rationalSpikeOracle"
  logInfo "EXACT_TARGET_OK rationalSpikeOracle RationalSpikeOracleTarget"
