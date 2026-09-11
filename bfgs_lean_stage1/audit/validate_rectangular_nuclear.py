#!/usr/bin/env python3
"""Structural/log checks only; no mathematical evaluation."""
import hashlib,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parent.parent
AUDIT=ROOT/'audit'
hashes=json.loads((AUDIT/'rectangular_nuclear_source_hashes.json').read_text())
reviewed=json.loads((AUDIT/'rectangular_nuclear_reviewed_source_hashes.json').read_text())
declarations=[]
for path,expected in hashes.items():
    source=ROOT/path
    assert hashlib.sha256(source.read_bytes()).hexdigest()==expected
    normalize=lambda s:re.sub(r'^import BfgsVerification\.(NuclearGram|NuclearVariational|NuclearNormFacts|CenteredRectangularNuclear|FirstDifferencePenalty|RectangularNuclearTargets)$',r'import \1',s,flags=re.M)
    assert hashlib.sha256(normalize(source.read_text()).encode()).hexdigest()==reviewed[source.name]
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',source.read_text())
    ns=re.search(r'^namespace (\S+)',source.read_text(),re.M).group(1)
    declarations += [ns+'.'+name for name in re.findall(r'^(?:def|theorem)\s+(\w+)',source.read_text(),re.M)]
assert declarations==(AUDIT/'rectangular_nuclear_declarations.txt').read_text().splitlines()
log=(AUDIT/'rectangular_nuclear_axioms.log').read_text()
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)
by_name={name:{a.strip() for a in names.split(',') if a.strip()} for name,names in reports}
for name in re.findall(r"'([^']+)' does not depend on any axioms",log):by_name[name]=set()
assert set(by_name)==set(declarations)
for name,axioms in by_name.items():assert axioms<={'propext','Classical.choice','Quot.sound'},(name,axioms)
targets=[('rectangularNuclearNorm','RectangularNuclearNormTarget'),('centeredRectangularNuclear','CenteredRectangularNuclearTarget'),('mixedNuclearPowers','MixedNuclearPowersTarget'),('firstDifferenceBasin','FirstDifferenceBasinTarget')]
for thm,target in targets:assert f'EXACT_TARGET_OK {thm} {target}' in (AUDIT/'rectangular_nuclear_contracts.log').read_text()
for suffix in ['build','axioms','contracts']:assert not re.search(r'\berror:',(AUDIT/f'rectangular_nuclear_{suffix}.log').read_text())
assert 'Build completed successfully.' in (AUDIT/'rectangular_nuclear_build.log').read_text()
print(f'PASS: {len(declarations)} main declarations; standard transitive axioms; four exact targets; six main hashes; reviewed normalized source hashes; actual pinned main build.')
