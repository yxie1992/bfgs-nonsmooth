#!/usr/bin/env python3
"""Validate delivered Lean source/log correspondence; no mathematical evaluation."""
import hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent.parent
audit=root/'audit'
modules=['FixedPointLinearization', 'ParametricFixedPoint', 'AnalyticFixedPointGraph', 'BoundedCoefficient', 'BoundedAnalyticLift', 'BoundedAnalyticDerivative', 'BoundedSequenceLinear', 'BoundedSequenceNonlinear', 'AnalyticStableSequence', 'StableGraphTangent', 'AnalyticStableGraph', 'StableGraphCoordinates', 'LinearStableSubspace', 'StableGraphEmbedding', 'LReturnStableGraph', 'LStableManifoldTargets', 'StableOrbitUniqueness', 'StableGraphInvariance', 'InvariantGraphCoordinates', 'LStableInvariantManifold']
hashes=json.loads((audit/'l_stable_manifold_source_hashes.json').read_text())
reviewed=json.loads((audit/'l_stable_manifold_reviewed_source_hashes.json').read_text())
assert set(hashes)=={'BfgsVerification/'+m+'.lean' for m in modules}
assert set(reviewed)=={m+'.lean' for m in modules}
pattern=r'^import BfgsVerification\.('+'|'.join(modules)+r')$'
names=[]
for module in modules:
    filename=module+'.lean'; path='BfgsVerification/'+filename
    source=(root/path).read_text()
    assert hashlib.sha256(source.encode()).hexdigest()==hashes[path],path
    normalized=re.sub(pattern,r'import \1',source,flags=re.M)
    assert hashlib.sha256(normalized.encode()).hexdigest()==reviewed[filename],path
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',source),path
    namespace=re.search(r'^namespace (\S+)',source,re.M)[1]
    names += [namespace+'.'+n for n in re.findall(r'^(?:def|theorem|abbrev)\s+([\w.]+)',source,re.M)]
assert names==(audit/'l_stable_manifold_declarations.txt').read_text().splitlines()
assert len(names)==len(set(names))==90
for suffix in ['build','axioms','contracts']:
    assert 'error:' not in (audit/f'l_stable_manifold_{suffix}.log').read_text(),suffix
assert 'Build completed successfully.' in (audit/'l_stable_manifold_build.log').read_text()
text=(audit/'l_stable_manifold_axioms.log').read_text()
reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
assert {n for n,a in reports}==set(names)
for n,a in reports:
    assert {v.strip() for v in a.split(',') if v.strip()}<={'propext','Classical.choice','Quot.sound'},n
text=(audit/'l_stable_manifold_contracts.log').read_text()
for name in ['lStableManifold','lStableInvariantManifold']:
    assert 'EXACT_TARGET_OK BfgsVerification.LReturnStableGraph.'+name in text,name
print('PASS: 20 main sources; 90 distinct actual declaration/standard-axiom reports; two strict source contracts; reviewed normalized hashes; actual pinned main build; delivered-only reproduction.')
