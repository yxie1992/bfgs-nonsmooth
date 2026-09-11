#!/usr/bin/env python3
"""Register the reviewed thirteenth tranche; run before its frozen full audit."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
groups = [
    ('AffineRankLoss.rankLossCurvature', 'AffineRankLoss.RankLossCurvatureTarget'),
    ('LWhitening.smoothIdentityFailure', 'LWhitening.SmoothIdentityFailureTarget'),
    ('LWhitening.stepIdentityFailure', 'LWhitening.StepIdentityFailureTarget'),
    ('LWhitening.smoothLocalFailure', 'LWhitening.SmoothLocalFailureTarget'),
    ('LWhitening.stepLocalFailure', 'LWhitening.StepLocalFailureTarget'),
    ('PlanarAllPairs.sourceAllPairTransport', 'PlanarAllPairs.SourceAllPairTransportTarget'),
    ('PlanarAllPairs.sourceAllEndpointEstimates', 'PlanarAllPairs.SourceAllEndpointEstimatesTarget'),
    ('ComparisonEnergyWarning.comparisonEnergyWarning', 'ComparisonEnergyWarning.ComparisonEnergyWarningTarget'),
    ('AffineProjection.actualImageRange', 'AffineProjection.ActualImageRangeTarget'),
    ('LReturnStableGraph.lStableManifold', 'LReturnStableGraph.LStableManifoldTarget'),
    ('LReturnStableGraph.lStableInvariantManifold', 'LReturnStableGraph.LStableInvariantManifoldTarget'),
    ('univariateSignBoundary', 'UnivariateSignBoundaryTarget'),
    ('univariateConvexCover', 'UnivariateConvexCoverTarget'),
    ('univariateCellCover', 'UnivariateCellCoverTarget'),
    ('polynomialFiberDerivative', 'PolynomialFiberDerivativeTarget'),
    ('polynomialSimpleRootChart', 'PolynomialSimpleRootChartTarget'),
    ('polynomialSimpleRootProjection', 'PolynomialSimpleRootProjectionTarget'),
]
pairs = [('BfgsVerification.'+a, 'BfgsVerification.'+b) for a,b in groups]
p = ROOT/'scripts/check.py'
code = p.read_text()
assert 'REPORT_SOURCE_CLOSURE_TARGETS' not in code
block = 'REPORT_SOURCE_CLOSURE_TARGETS = {\n'
for a,b in pairs:
    flag = a.removeprefix('BfgsVerification.').replace('.', '_')+'_verified'
    block += f'    "{flag}":\n        ("{a}", "{b}"),\n'
block += '}\n'
code = code.replace('ALL_TARGETS = ', block+'ALL_TARGETS = ', 1)
code = code.replace('| REPORT_L_FAILURE_TARGETS\n', '| REPORT_L_FAILURE_TARGETS | REPORT_SOURCE_CLOSURE_TARGETS\n', 1)
code = code.replace('MODULE_M_AND_REPORT_L_FAILURE_TARGETS_VERIFIED', 'MODULE_M_AND_REPORT_SOURCE_CLOSURE_TARGETS_VERIFIED')
old = 'A general semialgebraic projection/path/critical-value closure and rank-loss spectrum; C stronger uniform transport and higher-dimensional partial assertions; L fixed identity initialization and smooth-manifold/tangency; final family/source/synthesis/evidence reconciliation. Actual L spectrum, global failure and both fixed-SPD local-copy failures, plus the literal C spatial warning, are now checked; see REPORT_STATUS.json'
new = 'A general nonlinear semialgebraic projection/path/critical-value closure; C arbitrary-dimensional constant-rank field/secant partial assertion and semialgebraic alternative; final source/synthesis/evidence reconciliation. Actual L identity-initialized local failure families and smooth invariant stable manifold, C one-field uniform all-endpoint estimates, A rank-loss spectrum and univariate/simple-root infrastructure, and T/F source details are now checked; see REPORT_STATUS.json'
assert old in code
code = code.replace(old,new)
p.write_text(code)
p = ROOT/'BfgsVerification.lean'
old = p.read_text(); comment = old[old.index('/-!'):]
modules = sorted((ROOT/'BfgsVerification').glob('*.lean'))
p.write_text(''.join('import BfgsVerification.'+f.stem+'\n' for f in modules)+'\n'+comment)
p = ROOT/'Audit.lean'; old=p.read_text()
marker='/- Thirteenth milestone: identity failures, invariant manifold and source details. -/'
assert marker not in old
text='\n'+marker+'\n'
for a,b in pairs:
    text+=f'#print {b}\nexample : {b} := {a}\n#print axioms {a}\n'
p.write_text(old+text)
(ROOT/'audit/report_source_closure_targets.json').write_text(json.dumps(pairs,indent=2)+'\n')
sources=modules+[ROOT/'BfgsVerification.lean',ROOT/'Audit.lean']
manifest={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(sources)}
(ROOT/'audit/report_source_closure_source_hashes.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'Registered {len(pairs)} new exact targets; froze {len(sources)} Lean files.')
