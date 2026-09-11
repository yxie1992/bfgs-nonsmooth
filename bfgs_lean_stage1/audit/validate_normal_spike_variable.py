#!/usr/bin/env python3
"""Structural main-source and compiler-log checks; no mathematical evaluation."""
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
AUDIT = ROOT / 'audit'
SCRATCH = AUDIT / 'scratch/normal_spike'
SCOPES = {'variable': ['NormalSpikeVariableConvex', 'NormalSpikeVariableNonsplit', 'NormalSpikeVariableTangent', 'NormalSpikeVariableConvergence', 'NormalSpikeVariableGradient', 'NormalSpikeVariableRadialBound', 'NormalSpikeVariableSamples', 'NormalSpikeVariableSeparation', 'NormalSpikeVariableGeometry', 'NormalSpikeVariableHessian', 'NormalSpikeVariableRadialHessian', 'NormalSpikeVariableTargets']}
TARGETS = {'variable': [('variableSpikeConvergence', 'VariableSpikeConvergenceTarget'), ('variableSpikeSeparation', 'VariableSpikeSeparationTarget'), ('variableSpikeNonsplitting', 'VariableSpikeNonsplittingTarget'), ('variableSpikeGeometry', 'VariableSpikeGeometryTarget'), ('variableSpikeHessian', 'VariableSpikeHessianTarget')]}
total = 0
for scope, modules in SCOPES.items():
    sources = [ROOT / 'BfgsVerification' / (name + '.lean') for name in modules]
    declarations = ['BfgsVerification.NormalSpike.' + name for source in sources
                    for name in re.findall(r'^(?:def|theorem)\s+(\w+)', source.read_text(), re.M)]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    prefix = 'normal_spike_' + scope
    if '--prepare' in sys.argv:
        (AUDIT / (prefix + '_source_hashes.json')).write_text(json.dumps(hashes, indent=2) + '\n')
        (AUDIT / (prefix + '_declarations.txt')).write_text('\n'.join(declarations) + '\n')
        continue
    assert hashes == json.loads((AUDIT / (prefix + '_source_hashes.json')).read_text())
    reviewed = json.loads((SCRATCH / (scope + '_source_hashes.json')).read_text())
    for source in sources:
        scratch = SCRATCH / source.name
        assert reviewed[source.name] == hashlib.sha256(scratch.read_bytes()).hexdigest()
        main_text = source.read_text()
        scratch_text = scratch.read_text()
        normalize = lambda text: re.sub(r'^import BfgsVerification\.(NormalSpike\w+)', r'import \1', text, flags=re.M)
        assert normalize(main_text) == normalize(scratch_text)
        forbidden = r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by' + ('|noncomputable' if scope == 'rational' else '') + r')\b'
        assert not re.search(forbidden, main_text)
    log = (AUDIT / (prefix + '_axioms.log')).read_text()
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
    by_name = {name: {a.strip() for a in names.split(',') if a.strip()} for name, names in reports}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        by_name[name] = set()
    assert set(by_name) == set(declarations)
    for name, axioms in by_name.items():
        assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    for theorem, target in TARGETS[scope]:
        assert f'EXACT_TARGET_OK {theorem} {target}' in (AUDIT / (prefix + '_contracts.log')).read_text()
    for suffix in ['axioms', 'contracts']:
        assert not re.search(r'\berror:', (AUDIT / (prefix + '_' + suffix + '.log')).read_text())
    total += len(declarations)
    print(f'PASS {scope}: {len(declarations)} declarations; standard transitive axioms; exact targets; reviewed source unchanged except import prefixes.')
if '--prepare' not in sys.argv:
    build = (AUDIT / 'normal_spike_variable_build.log').read_text()
    assert not re.search(r'\berror:', build)
    assert 'Build completed successfully.' in build
    print(f'PASS: {total} main declarations, five exact targets, twelve source hashes, actual pinned main build.')
