#!/usr/bin/env python3
"""Validate completed compiler reports, actual source hashes and standard axioms."""
import datetime
import hashlib
import json
import re
from pathlib import Path
root=Path(__file__).resolve().parent.parent
manifest=json.loads((root/'audit/l_return_dynamics_declarations.json').read_text())
text=(root/'audit/l_return_dynamics_axioms.log').read_text()
assert 'error:' not in text
allowed={'propext','Classical.choice','Quot.sound'}
expected=[]
for module,item in manifest.items():
    source=root/'BfgsVerification'/f'{module}.lean'
    assert hashlib.sha256(source.read_bytes()).hexdigest()==item['sha256'],source
    expected.extend(f'BfgsVerification.{module}.{name}' for name in item['names'])
expected.extend('BfgsVerification.LReturnJets.'+n for n in ['Jet.mk','Jet.value','Jet.tangent'])
for name in expected:
    assert f"'{name}' depends on axioms:" in text or f"'{name}' does not depend on any axioms" in text,name
reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
assert {name for name,_ in reports}==set(expected)
for name,axioms in reports:
    assert {x.strip() for x in axioms.split(',') if x.strip()}<=allowed,(name,axioms)
for module in manifest:
    source=(root/'BfgsVerification'/f'{module}.lean').read_text()
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',source),module
print(datetime.datetime.now(datetime.timezone.utc).isoformat())
print(f'PASS: {len(expected)-3} explicit declarations plus3 generated Jet declarations; {len(expected)} exact type/standard-axiom reports; {len(manifest)} frozen source hashes.')
print('Scope: actual return derivative, kernel rational-interval Jacobian certificate, exact spectral factorization and hyperbolicity, local inverse, and actual global BFGS failure in every physical neighborhood. Smooth stable-manifold regularity/tangency is a separate open source assertion.')
