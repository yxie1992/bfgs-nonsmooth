import BfgsVerification.LGlobalTargets

#check BfgsVerification.LGlobalTargets.GlobalFailureTarget
#print axioms BfgsVerification.LGlobalTargets.GlobalFailureTarget
#check BfgsVerification.LGlobalTargets.globalFailure
#print axioms BfgsVerification.LGlobalTargets.globalFailure
#check BfgsVerification.LGlobalTargets.SpectrumTarget
#print axioms BfgsVerification.LGlobalTargets.SpectrumTarget
#check BfgsVerification.LGlobalTargets.spectrum
#print axioms BfgsVerification.LGlobalTargets.spectrum
#check BfgsVerification.LGlobalTargets.LocalInverseTarget
#print axioms BfgsVerification.LGlobalTargets.LocalInverseTarget
#check BfgsVerification.LGlobalTargets.localInverse
#print axioms BfgsVerification.LGlobalTargets.localInverse

open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `BfgsVerification.LGlobalTargets.globalFailure
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LGlobalTargets.GlobalFailureTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LGlobalTargets.globalFailure BfgsVerification.LGlobalTargets.GlobalFailureTarget"
  let info ← getConstInfo `BfgsVerification.LGlobalFailure.source_global_failure
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LGlobalTargets.GlobalFailureTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LGlobalFailure.source_global_failure BfgsVerification.LGlobalTargets.GlobalFailureTarget"
  let info ← getConstInfo `BfgsVerification.LGlobalTargets.spectrum
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LGlobalTargets.SpectrumTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LGlobalTargets.spectrum BfgsVerification.LGlobalTargets.SpectrumTarget"
  let info ← getConstInfo `BfgsVerification.LReturnSpectrum.actual_spectral_contract
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LGlobalTargets.SpectrumTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LReturnSpectrum.actual_spectral_contract BfgsVerification.LGlobalTargets.SpectrumTarget"
  let info ← getConstInfo `BfgsVerification.LGlobalTargets.localInverse
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LGlobalTargets.LocalInverseTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LGlobalTargets.localInverse BfgsVerification.LGlobalTargets.LocalInverseTarget"
  let info ← getConstInfo `BfgsVerification.LReturnLocalInverse.actual_local_inverse
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `BfgsVerification.LGlobalTargets.LocalInverseTarget)
  unless ok do throwError "target mismatch"
  logInfo "EXACT_TARGET_OK BfgsVerification.LReturnLocalInverse.actual_local_inverse BfgsVerification.LGlobalTargets.LocalInverseTarget"
