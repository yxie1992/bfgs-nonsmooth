#!/usr/bin/env python3
"""Verify delivered source hashes and actual compiler logs; no mathematical evaluation."""
import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent.parent
AUDIT = ROOT / 'audit'
MODULES = ['LScalarStepSeries', 'LScalarStepRamp', 'LScalarStepIntervals', 'LScalarStepPlateaus', 'LScalarStepAssembly', 'LScalarStepEnvelope', 'LScalarStepLocal', 'LScalarStepTargets']
TARGETS = [('lScalarStepDefinition', 'LScalarStepDefinitionTarget'), ('lScalarStepGeometry', 'LScalarStepGeometryTarget'), ('lScalarStepNodes', 'LScalarStepNodeTarget'), ('lScalarStepLocal', 'LScalarStepLocalTarget')]
hashes = json.loads((AUDIT / 'l_step_source_hashes.json').read_text())
reviewed = json.loads((AUDIT / 'l_step_reviewed_source_hashes.json').read_text())
assert set(hashes) == {'BfgsVerification/' + n + '.lean' for n in MODULES}
assert set(reviewed) == {n + '.lean' for n in MODULES}
declarations = []
pattern = r'^import BfgsVerification\.(' + '|'.join(MODULES+['LScalarTargets']) + r')$'
for module in MODULES:
    path = 'BfgsVerification/' + module + '.lean'
    source = ROOT / path
    raw = source.read_text()
    assert hashlib.sha256(source.read_bytes()).hexdigest() == hashes[path], path
    normalized = re.sub(pattern, r'import \1', raw, flags=re.M)
    assert hashlib.sha256(normalized.encode()).hexdigest() == reviewed[source.name], path
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', raw), path
    namespace = re.search(r'^namespace (\S+)', raw, re.M).group(1)
    declarations += [namespace + '.' + n for n in re.findall(r'^(?:def|theorem)\s+([\w.]+)', raw, re.M)]
assert len(declarations) == len(set(declarations)) == 78
assert declarations == (AUDIT / 'l_step_declarations.txt').read_text().splitlines()
log = (AUDIT / 'l_step_axioms.log').read_text()
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
axioms = {n: {a.strip() for a in names.split(',') if a.strip()} for n, names in reports}
for n in re.findall(r"'([^']+)' does not depend on any axioms", log):
    axioms[n] = set()
assert set(axioms) == set(declarations)
for n, deps in axioms.items():
    assert deps <= {'propext', 'Classical.choice', 'Quot.sound'}, (n, deps)
contracts = (AUDIT / 'l_step_contracts.log').read_text()
for theorem, target in TARGETS:
    assert f'EXACT_TARGET_OK {theorem} {target}' in contracts
for suffix in ['build', 'axioms', 'contracts']:
    assert not re.search(r'\berror:', (AUDIT / f'l_step_{suffix}.log').read_text()), suffix
assert 'Build completed successfully.' in (AUDIT / 'l_step_build.log').read_text()
print('PASS: 78 main declarations; standard transitive axioms; four exact targets; eight main hashes; reviewed normalized source hashes; actual pinned main build.')
