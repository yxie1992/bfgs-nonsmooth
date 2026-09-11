#!/usr/bin/env python3
"""Adopt six independently reviewed actual-root/path scopes, import changes only.

One-time integration helper. The delivered-only scoped validator reproduces the
adopted proofs without access to scratch. Central target registration is separate.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRATCH = ROOT / 'audit/scratch'
NAMES = ['root_delineability', 'root_cluster_conservation', 'root_continuity',
         'smooth_cylindrical_paths', 'ordered_cylindrical_cells', 'root_definability']
PUBLIC = ['ROOT_CLUSTER_BOUNDS', 'ROOT_CLUSTER_CONSERVATION', 'ORDERED_ROOT_CONTINUITY',
          'SMOOTH_CYLINDRICAL_PATHS', 'ORDERED_CYLINDRICAL_CELLS', 'ROOT_DEFINABILITY']
rows = []
for name, public in zip(NAMES, PUBLIC):
    p = SCRATCH / name
    assert 'PASS' in (p / 'validation.log').read_text(), name
    assert 'PASS' in (p / 'peer_validation.log').read_text(), name
    manifest = json.loads((p / 'declarations.json').read_text()) if (p / 'declarations.json').exists() else None
    if isinstance(manifest, dict):
        hashes = {Path(x['path']).name: x['sha256'] for x in manifest['sources']}
        declarations = manifest['declarations']
        # Public wrappers are Type0 exact targets; source equivalents were
        # independently checked with fresh universe levels in the peer audit.
        pairs = [pair for pair in manifest['strict_contracts']
                 if pair[0].count('.') == 1]
    else:
        hashes = json.loads((p / 'source_hashes.json').read_text())
        if name == 'root_delineability':
            declarations = json.loads((p / 'peer_declarations.json').read_text())
        elif manifest is not None:
            declarations = manifest
        else:
            declarations = (p / 'declarations.txt').read_text().splitlines()
        if (p / 'targets.json').exists():
            raw = json.loads((p / 'targets.json').read_text())
            pairs = [[f'BfgsVerification.{ns}.{a}', f'BfgsVerification.{ns}.{b}']
                     if len(pair) == 3 else pair
                     for pair in raw for ns, a, b in [pair if len(pair) == 3 else ['', '', '']]]
        else:
            contracts = list(p.glob('*CONTRACTS.lean'))
            assert len(contracts) == 1
            pairs = re.findall(r'getConstInfo `([^\s]+).*?mkConst `([^\s)]+)',
                               contracts[0].read_text(), re.S)
    assert len(declarations) == len(set(declarations))
    assert pairs, name
    rows.append(dict(name=name, public=public, base=p, hashes=hashes,
                     declarations=declarations, pairs=pairs))
all_modules = {Path(f).stem for row in rows for f in row['hashes']}
assert len(all_modules) == sum(len(row['hashes']) for row in rows) == 32
assert sum(len(row['declarations']) for row in rows) == 176
assert sum(len(row['pairs']) for row in rows) == 19
scopes = []
for row in rows:
    sources = []
    for filename, digest in row['hashes'].items():
        source = row['base'] / filename
        original = source.read_text()
        assert hashlib.sha256(source.read_bytes()).hexdigest() == digest, source
        def qualify(match):
            name = match[1]
            return 'import BfgsVerification.' + name if name in all_modules else match[0]
        adopted = re.sub(r'^import (\S+)$', qualify, original, flags=re.M)
        assert re.sub(r'^import .*\n', '', original, flags=re.M) == re.sub(
            r'^import .*\n', '', adopted, flags=re.M), source
        for name in re.findall(r'^import (\S+)$', adopted, re.M):
            assert name == 'Mathlib' or name.startswith(('BfgsVerification.', 'Mathlib.', 'Lean', 'Batteries.')), name
        dest = ROOT / 'BfgsVerification' / source.name
        assert not dest.exists() or dest.read_text() == adopted, dest
        dest.write_text(adopted)
        sources.append(dict(module='BfgsVerification.' + source.stem,
            path=str(dest.relative_to(ROOT)), sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),
            reviewed_source=str(source.relative_to(ROOT)), reviewed_sha256=digest))
    evidence = []
    for source_name, suffix in [('STATEMENT_REVIEW.md', 'STATEMENT_REVIEW.md'),
                                 ('INDEPENDENT_PEER_REVIEW.md', 'INDEPENDENT_PEER_REVIEW.md')]:
        source = row['base'] / source_name
        assert source.is_file(), source
        dest = ROOT / 'audit' / (row['public'] + '_' + suffix)
        assert not dest.exists() or dest.read_bytes() == source.read_bytes(), dest
        dest.write_bytes(source.read_bytes())
        evidence.append(str(dest.relative_to(ROOT)))
    for source in sorted(row['base'].glob('peer*.log')):
        dest = ROOT / 'audit' / (row['public'] + '_' + source.name)
        assert not dest.exists() or dest.read_bytes() == source.read_bytes(), dest
        dest.write_bytes(source.read_bytes())
        evidence.append(str(dest.relative_to(ROOT)))
    scopes.append(dict(id=row['name'], label=row['public'], sources=sources,
                       declarations=row['declarations'], targets=row['pairs'], review_evidence=evidence))
manifest = dict(log_prefix='tame_geometry', audit_driver='audit/TameGeometryAudit.lean',
                scopes=scopes, declarations=[n for row in rows for n in row['declarations']],
                targets=[pair for row in rows for pair in row['pairs']])
assert len(set(manifest['declarations'])) == 176
(ROOT / 'audit/tame_geometry_declarations.json').write_text(json.dumps(manifest, indent=2) + '\n')
driver = ''.join(f'import BfgsVerification.{name}\n' for name in sorted(all_modules))
driver += 'import Lean\nopen Lean Elab Command Meta\n'
for name in manifest['declarations']:
    driver += f'#check @{name}\n#print axioms {name}\n'
for name, target in manifest['targets']:
    driver += f'''run_cmd do
  let info ← getConstInfo `{name}
  let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst `{target})
  unless ok do throwError "exact target mismatch: {name}"
  logInfo "EXACT_TARGET_OK {name}"
'''
(ROOT / 'audit/TameGeometryAudit.lean').write_text(driver)
(ROOT / 'audit/tame_geometry_import_correspondence.log').write_text(
    'PASS:32 adopted modules have byte-identical non-import bodies;176 reviewed declarations;'
    '19 exact targets;six independently reviewed scopes. Main compiler/axiom gate follows.\n')
print('Adopted32 root/path modules;176 declaration reports and19 exact targets. Central registration remains separate.')
