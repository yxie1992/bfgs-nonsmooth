#!/usr/bin/env python3
"""Register reviewed fourteenth tranche before its frozen pinned full audit."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
groups=[
('TwoPieceBudget.twoPieceTermination','TwoPieceBudget.TwoPieceTerminationTarget'),
('TwoPieceBudget.twoPieceLinearImage','TwoPieceBudget.TwoPieceLinearImageTarget'),
('LShapePrecision.actualJacobianPrecision','LShapePrecision.ActualJacobianPrecisionTarget'),
('ConstantRankFields.sourceConstantRank','ConstantRankFields.SourceConstantRankTarget'),
('ConstantRankFields.sourceConstantRankEligible','ConstantRankFields.SourceConstantRankEligibleTarget'),
('polynomialDegreeStrata','PolynomialDegreeStrataTarget'),
('polynomialDerivativeSpecialization','PolynomialDerivativeSpecializationTarget'),
('polynomialMultiplicityStrata','PolynomialMultiplicityStrataTarget'),
('polynomialMultipleRootChart','PolynomialMultipleRootChartTarget'),
('realQuadraticElimination','RealQuadraticEliminationTarget'),
('quadraticPolynomialProjection','QuadraticPolynomialProjectionTarget'),
('quadraticUniversalConditions','QuadraticUniversalConditionsTarget'),
('actualDegreeTwoProjection','ActualDegreeTwoProjectionTarget'),
('positivePseudoDivision','PositivePseudoDivisionTarget'),
('pseudoDivisionSpecialization','PseudoDivisionSpecializationTarget'),
('finiteRootRemainders','FiniteRootRemaindersTarget'),
]
pairs=[('BfgsVerification.'+a,'BfgsVerification.'+b) for a,b in groups]
p=ROOT/'scripts/check.py';code=p.read_text()
assert 'REPORT_GEOMETRY_COMPLETION_TARGETS' not in code
block='REPORT_GEOMETRY_COMPLETION_TARGETS = {\n'
for a,b in pairs:
 flag=a.removeprefix('BfgsVerification.').replace('.','_')+'_verified'
 block+=f'    "{flag}":\n        ("{a}", "{b}"),\n'
block+='}\n'
code=code.replace('ALL_TARGETS = ',block+'ALL_TARGETS = ',1)
code=code.replace('| REPORT_SOURCE_CLOSURE_TARGETS\n','| REPORT_SOURCE_CLOSURE_TARGETS | REPORT_GEOMETRY_COMPLETION_TARGETS\n',1)
code=code.replace('MODULE_M_AND_REPORT_SOURCE_CLOSURE_TARGETS_VERIFIED','MODULE_M_AND_REPORT_GEOMETRY_COMPLETION_TARGETS_VERIFIED')
old='A general nonlinear semialgebraic projection/path/critical-value closure; C arbitrary-dimensional constant-rank field/secant partial assertion and semialgebraic alternative; final source/synthesis/evidence reconciliation. Actual L identity-initialized local failure families and smooth invariant stable manifold, C one-field uniform all-endpoint estimates, A rank-loss spectrum and univariate/simple-root infrastructure, and T/F source details are now checked; see REPORT_STATUS.json'
new='A general nonlinear Boolean semialgebraic projection/path/critical-value closure and the dependent C semialgebraic alternative; final source/synthesis/evidence reconciliation. Actual C arbitrary-dimensional constant-rank C1 field/secant theorem, L Jacobian precision, two-piece termination and arbitrary-dimensional no-infinite-continuation, and A multiplicity/quadratic-projection/positive-pseudo-division infrastructure are now checked. The finite polynomial fragments do not prove general quantifier elimination; see REPORT_STATUS.json'
assert old in code;code=code.replace(old,new);p.write_text(code)
p=ROOT/'BfgsVerification.lean';old=p.read_text();comment=old[old.index('/-!'):]
modules=sorted((ROOT/'BfgsVerification').glob('*.lean'))
assert len(modules)==580,len(modules)
p.write_text(''.join('import BfgsVerification.'+f.stem+'\n' for f in modules)+'\n'+comment)
p=ROOT/'Audit.lean';old=p.read_text();marker='/- Fourteenth milestone: constant-rank geometry, precision, termination and polynomial elimination infrastructure. -/'
assert marker not in old
text='\n'+marker+'\n'
for a,b in pairs:text+=f'#print {b}\nexample : {b} := {a}\n#print axioms {a}\n'
p.write_text(old+text)
(ROOT/'audit/report_geometry_completion_targets.json').write_text(json.dumps(pairs,indent=2)+'\n')
sources=modules+[ROOT/'BfgsVerification.lean',ROOT/'Audit.lean']
manifest={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(sources)}
(ROOT/'audit/report_geometry_completion_source_hashes.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'Registered {len(pairs)} new exact targets; froze {len(sources)} Lean files.')
