#!/usr/bin/env python3
"""Validate delivered L display-precision evidence without excluded scratch."""
from pathlib import Path
import hashlib,json,re

AUDIT=Path(__file__).resolve().parent
PROJECT=AUDIT.parent
names=json.loads((AUDIT/'l_shape_precision_declarations.json').read_text())
hashes=json.loads((AUDIT/'l_shape_precision_source_hashes.json').read_text())
reviewed=json.loads((AUDIT/'l_shape_precision_reviewed_source_hashes.json').read_text())
modules=[Path(f).stem for f in hashes]
for f,h in hashes.items():
    p=PROJECT/'BfgsVerification'/f
    src=p.read_text()
    assert hashlib.sha256(p.read_bytes()).hexdigest()==h,f
    normalized=src
    for m in modules:
        normalized=normalized.replace('import BfgsVerification.'+m+'\n','import '+m+'\n')
    assert hashlib.sha256(normalized.encode()).hexdigest()==reviewed[f],f
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',src),f
log=(AUDIT/'l_shape_precision_axioms.log').read_text()
for n in names:
    m=re.search("'"+re.escape(n)+"' depends on axioms: \\[([^\\]]*)\\]",log)
    assert m,n
    assert set(re.findall(r'[\w.]+',m.group(1)))<={'propext','Classical.choice','Quot.sound'},n
for f in ['l_shape_precision_build.log','l_shape_precision_axioms.log','l_shape_precision_contracts.log']:
    text=(AUDIT/f).read_text()
    assert not re.search(r'(?im)\berror:|uses .sorry.|uncaught exception',text),f
assert 'Build completed successfully' in (AUDIT/'l_shape_precision_build.log').read_text()
assert 'EXACT_TARGET_OK BfgsVerification.LShapePrecision.actualJacobianPrecision' in (AUDIT/'l_shape_precision_contracts.log').read_text()
assert 'PASS: exact byte-identical certificate regeneration' in (AUDIT/'l_shape_precision_generation_check.log').read_text()
print(f'PASS delivered-only L precision: {len(hashes)} main modules / {len(names)} actual type and standard-axiom reports / one exact target')
print('Main hashes and normalized reviewed hashes agree; actual main lake build and byte-identical candidate regeneration passed.')
print('No scratch input is required. Python candidates do not supply mathematical evidence.')
