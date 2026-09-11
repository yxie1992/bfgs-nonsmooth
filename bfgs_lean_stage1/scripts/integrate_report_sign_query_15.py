#!/usr/bin/env python3
"""Adopt six independently reviewed scratch tranches, changing imports only.

This records source correspondence and creates a delivered-only scoped gate.
It deliberately does not update the central target register or claim full audit.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCOPES = [
    ("h_sharp_cardinality", "H_SHARP_CARDINALITY", [
        ("SeedOrbit.sharpRecurrentCardinality", "SeedOrbit.SharpRecurrentCardinalityTarget")]),
    ("ridge_supersession", "RIDGE_SUPERSESSION", [
        ("RidgeSupersession.ridgeSupersession", "RidgeSupersession.RidgeSupersessionTarget")]),
    ("sturm_signs", "ROOT_SIGNS", [
        ("polynomialOneSidedSigns", "PolynomialOneSidedSignsTarget"),
        ("polynomialLogarithmicResidue", "PolynomialLogarithmicResidueTarget"),
        ("weightedLogarithmicPole", "WeightedLogarithmicPoleTarget"),
        ("tarskiCauchyLocalIdentity", "TarskiCauchyLocalIdentityTarget")]),
    ("rational_index", "RATIONAL_INDEX", [
        ("finiteJumpTelescoping", "FiniteJumpTelescopingTarget"),
        ("polynomialSignJump", "PolynomialSignJumpTarget"),
        ("rationalIndexReciprocity", "RationalIndexReciprocityTarget"),
        ("rationalIndexRemainder", "RationalIndexRemainderTarget"),
        ("euclideanIndexComputation", "EuclideanIndexComputationTarget")]),
    ("sign_determination", "SIGN_DETERMINATION", [
        ("rootSignReconstruction", "RootSignReconstructionTarget"),
        ("simultaneousRootSigns", "SimultaneousRootSignsTarget"),
        ("signQueryDetermination", "SignQueryDeterminationTarget")]),
    ("polynomial_sampling", "POLYNOMIAL_SAMPLING", [
        ("finitePolynomialSignSampling", "FinitePolynomialSignSamplingTarget"),
        ("polynomialTailSamples", "PolynomialTailSamplesTarget"),
        ("realPolynomialSignReduction", "RealPolynomialSignReductionTarget")]),
]


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


scopes = []
for folder, label, pairs in SCOPES:
    base = ROOT / "audit/scratch" / folder
    assert "PASS" in (base / "validation.log").read_text(), folder
    assert (base / "INDEPENDENT_PEER_REVIEW.md").is_file(), folder
    assert "PASS" in (base / "peer_validation.log").read_text(), folder
    if (base / "declarations.json").exists():
        data = json.loads((base / "declarations.json").read_text())
        sources = [(ROOT / row["path"], row["sha256"]) for row in data["sources"]]
        names = data["declarations"]
    else:
        sources = [(base / f, h) for f, h in
                   json.loads((base / "source_hashes.json").read_text()).items()]
        names = (base / "declarations.txt").read_text().splitlines()
    for source, h in sources:
        assert digest(source) == h, source
    scopes.append(dict(id=folder, label=label, sources=sources,
                       declarations=names,
                       targets=[["BfgsVerification." + a, "BfgsVerification." + b]
                                for a, b in pairs]))

modules = {p.stem for scope in scopes for p, _ in scope["sources"]}
assert len(modules) == 33


def normalize_imports(text):
    def line(match):
        module = match.group(1)
        leaf = module.rsplit(".", 1)[-1]
        if leaf in modules and not module.startswith("BfgsVerification."):
            return "import BfgsVerification." + leaf
        return match.group(0)
    return re.sub(r"^import ([A-Za-z0-9_.]+)$", line, text, flags=re.M)


for scope in scopes:
    rows = []
    for source, oldhash in scope["sources"]:
        text = source.read_text()
        delivered = normalize_imports(text)
        # Everything other than module imports must remain literally identical.
        strip = lambda s: re.sub(r"^import .*\n", "", s, flags=re.M)
        assert strip(text) == strip(delivered), source
        dest = ROOT / "BfgsVerification" / source.name
        assert not dest.exists(), dest
        dest.write_text(delivered)
        rows.append(dict(module="BfgsVerification." + source.stem,
                         path=str(dest.relative_to(ROOT)), sha256=digest(dest),
                         reviewed_source=str(source.relative_to(ROOT)),
                         reviewed_sha256=oldhash))
    scope["sources"] = rows
    base = ROOT / "audit/scratch" / scope["id"]
    label = scope["label"]
    evidence = []
    for original, suffix in [
        ("STATEMENT_REVIEW.md", "STATEMENT_REVIEW.md"),
        ("INDEPENDENT_PEER_REVIEW.md", "INDEPENDENT_PEER_REVIEW.md"),
        ("peer_validation.log", "peer_validation.log"),
        ("peer_axioms_contracts.log", "peer_axioms_contracts.log"),
        ("peer_axioms_contract.log", "peer_axioms_contract.log"),
        ("peer_axioms.log", "peer_axioms.log"),
        ("peer_contracts.log", "peer_contracts.log"),
    ]:
        src = base / original
        if not src.is_file():
            continue
        dest = ROOT / "audit" / (label + "_" + suffix)
        assert not dest.exists(), dest
        dest.write_bytes(src.read_bytes())
        evidence.append(str(dest.relative_to(ROOT)))
    scope["review_evidence"] = evidence

names = [name for scope in scopes for name in scope["declarations"]]
pairs = [pair for scope in scopes for pair in scope["targets"]]
assert len(names) == len(set(names)) == 212
assert len(pairs) == 17
manifest = dict(scopes=scopes, declarations=names, targets=pairs)
(ROOT / "audit/sign_query_declarations.json").write_text(json.dumps(manifest, indent=2) + "\n")
audit = ["import BfgsVerification." + name for name in sorted(modules)]
audit += ["set_option pp.universes true", "set_option pp.fullNames true", "set_option pp.all false"]
for name in names:
    audit += ["#check " + name, "#print axioms " + name]
audit += ["", "open Lean Elab Command in", "run_cmd do", "  for (decl,target) in ["]
audit += ["    (`" + a + ", `" + b + ")" + ("," if i + 1 < len(pairs) else "] do")
          for i, (a, b) in enumerate(pairs)]
audit += ["    let info ← getConstInfo decl",
          "    let ok ← liftTermElabM <| Meta.isDefEq info.type (mkConst target)",
          '    unless ok do throwError "target mismatch: {decl}"',
          '    logInfo m!"EXACT_TARGET_OK {decl}"']
(ROOT / "audit/SignQueryAudit.lean").write_text("\n".join(audit) + "\n")
(ROOT / "audit/sign_query_import_correspondence.log").write_text(
    "PASS: 33 independently reviewed source hashes matched; only module import lines changed; "
    "212 declarations and 17 targets retained. Public manifest contains both original and delivered hashes.\n")
print("Adopted 33 reviewed sources / 212 declarations / 17 targets; central audit still pending.")
