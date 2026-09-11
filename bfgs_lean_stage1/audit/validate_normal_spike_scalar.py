#!/usr/bin/env python3
"""Structural compiler-log audit for the scalar U.18/U.19 tranche; no mathematical evaluation."""
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
AUDIT = ROOT / "audit"
SCRATCH = AUDIT / "scratch/normal_spike"
MODULES = ["NormalSpikeBump", "NormalSpikeScaled", "NormalSpikeSeries", "NormalSpikeGeometry",
           "NormalSpikeBounds", "NormalSpikeRegularity", "NormalSpikeOracle",
           "NormalSpikeMassSupport", "NormalSpikeTargets"]
sources = [ROOT / "BfgsVerification" / (name + ".lean") for name in MODULES]
declarations = ["BfgsVerification.NormalSpike." + name for source in sources
                for name in re.findall(r"^(?:def|theorem)\s+(\w+)", source.read_text(), re.M)]
hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
if "--prepare" in sys.argv:
    (AUDIT / "normal_spike_scalar_source_hashes.json").write_text(json.dumps(hashes, indent=2) + "\n")
    (AUDIT / "normal_spike_scalar_declarations.txt").write_text("\n".join(declarations) + "\n")
    print(f"Prepared {len(declarations)} declaration records and nine main source hashes.")
else:
    assert hashes == json.loads((AUDIT / "normal_spike_scalar_source_hashes.json").read_text())
    reviewed = json.loads((SCRATCH / "source_hashes.json").read_text())
    for source in sources:
        scratch = SCRATCH / source.name
        assert reviewed[source.name] == hashlib.sha256(scratch.read_bytes()).hexdigest()
        assert source.read_text().replace("import BfgsVerification.NormalSpike", "import NormalSpike") == scratch.read_text()
        assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b", source.read_text())
    log = (AUDIT / "normal_spike_scalar_axioms.log").read_text()
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
    by_name = {name: {a.strip() for a in names.split(",") if a.strip()} for name, names in reports}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        by_name[name] = set()
    assert set(by_name) == set(declarations)
    for name, axioms in by_name.items():
        assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, (name, axioms)
    assert "EXACT_TARGET_OK sourceSpikeProperties SourceSpikePropertiesTarget" in (AUDIT / "normal_spike_scalar_contracts.log").read_text()
    for filename in ["normal_spike_scalar_build.log", "normal_spike_scalar_axioms.log", "normal_spike_scalar_contracts.log"]:
        assert not re.search(r"\berror:", (AUDIT / filename).read_text()), filename
    assert "Build completed successfully." in (AUDIT / "normal_spike_scalar_build.log").read_text()
    print(f"PASS: {len(declarations)} main declarations; standard transitive axioms only; one exact target; nine unchanged hashes; reviewed scratch differs only by import prefixes.")
