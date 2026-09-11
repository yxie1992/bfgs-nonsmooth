#!/usr/bin/env python3
"""Validate delivered compiler evidence; performs no mathematical computation."""
import hashlib,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parent.parent
AUDIT=ROOT/'audit'
manifest=json.loads((AUDIT/'local_stable_orbit_declarations.json').read_text())
for item in manifest['sources']:
    data=(ROOT/item['path']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==item['sha256'],item['path']
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',data.decode()),item['path']
log=(AUDIT/'local_stable_orbit_axioms.log').read_text()
reports={name:{a.strip() for a in names.split(',') if a.strip()} for name,names in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)}
reports.update({name:set() for name in re.findall(r"'([^']+)' does not depend on any axioms",log)})
assert set(reports)==set(manifest['declarations'])
for name,axioms in reports.items():
    assert axioms<={'propext','Classical.choice','Quot.sound'},(name,axioms)
for suffix in ['build','targets_build','axioms','peer_contracts']:
    content=(AUDIT/f'local_stable_orbit_{suffix}.log').read_text()
    assert not re.search(r'\berror:',content),suffix
    if suffix.endswith('build'):assert 'Build completed successfully.' in content
contracts=(AUDIT/'local_stable_orbit_peer_contracts.log').read_text()
for thm,target in [('stableOrbit','StableOrbitTarget'),('positiveStableOrbit','PositiveStableOrbitTarget')]:
    assert f'EXACT_TARGET_OK BfgsVerification.LocalStableOrbit.{thm} BfgsVerification.LocalStableOrbit.{target}' in contracts
print(f"PASS: {len(manifest['declarations'])} complete declaration/standard transitive axiom reports; {len(manifest['sources'])} exact main source hashes; two strict exact-target checks; actual pinned builds.")
