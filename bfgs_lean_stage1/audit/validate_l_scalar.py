#!/usr/bin/env python3
"""Verify delivered source hashes and actual compiler logs; no mathematical evaluation."""
import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent.parent
AUDIT = ROOT / 'audit'
MODULES = ['LScalarGeometric', 'LScalarRamp', 'LScalarSeries', 'LScalarIntervals', 'LScalarCurvature', 'LScalarJets', 'LScalarPlateaus', 'LScalarLocalCalculus', 'LScalarLipschitz', 'LScalarAssembly', 'LScalarRegularity', 'LScalarPeaks', 'LScalarSmallBounds', 'LScalarTargets']
TARGETS = [('lScalarRamp', 'LScalarRampTarget'), ('lScalarDefinition', 'LScalarDefinitionTarget'), ('lScalarRegularity', 'LScalarRegularityTarget'), ('lScalarNodes', 'LScalarNodeTarget'), ('lScalarPeaks', 'LScalarPeaksTarget')]
hashes = json.loads((AUDIT / 'l_scalar_source_hashes.json').read_text())
reviewed = json.loads((AUDIT / 'l_scalar_reviewed_source_hashes.json').read_text())
assert set(hashes) == {'BfgsVerification/' + n + '.lean' for n in MODULES}
assert set(reviewed) == {n + '.lean' for n in MODULES}
declarations = []
pattern = r'^import BfgsVerification\.(' + '|'.join(MODULES) + r')$'
for module in MODULES:
    path = 'BfgsVerification/' + module + '.lean'
    source = ROOT / path
    raw = source.read_text()
    assert hashlib.sha256(source.read_bytes()).hexdigest() == hashes[path], path
    normalized = re.sub(pattern, r'import \1', raw, flags=re.M)
    assert hashlib.sha256(normalized.encode()).hexdigest() == reviewed[source.name], path
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', raw), path
    namespace = re.search(r'^namespace (\S+)', raw, re.M).group(1)
    declarations += [namespace + '.' + n for n in re.findall(r'^(?:def|theorem)\s+(\w+)', raw, re.M)]
assert len(declarations) == len(set(declarations)) == 203
assert declarations == (AUDIT / 'l_scalar_declarations.txt').read_text().splitlines()
log = (AUDIT / 'l_scalar_axioms.log').read_text()
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
axioms = {n: {a.strip() for a in names.split(',') if a.strip()} for n, names in reports}
for n in re.findall(r"'([^']+)' does not depend on any axioms", log):
    axioms[n] = set()
assert set(axioms) == set(declarations)
for n, deps in axioms.items():
    assert deps <= {'propext', 'Classical.choice', 'Quot.sound'}, (n, deps)
contracts = (AUDIT / 'l_scalar_contracts.log').read_text()
for theorem, target in TARGETS:
    assert f'EXACT_TARGET_OK {theorem} {target}' in contracts
for suffix in ['build', 'axioms', 'contracts']:
    assert not re.search(r'\berror:', (AUDIT / f'l_scalar_{suffix}.log').read_text()), suffix
assert 'Build completed successfully.' in (AUDIT / 'l_scalar_build.log').read_text()
print('PASS: 203 main declarations; standard transitive axioms; five exact targets; fourteen main hashes; reviewed normalized source hashes; actual pinned main build.')
