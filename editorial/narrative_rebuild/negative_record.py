#!/usr/bin/env python3
"""Refresh the negative narrative's correspondence without editing sealed records."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
BASE = "c84763f8c299aa62715c7dccd22fb5bacb218529"
RUN = HERE / "negative_formal/runs/20260912_covariance_01"

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def historical(name):
    return subprocess.check_output(["git", "show", BASE + ":" + name], cwd=ROOT).decode()

record = json.loads(historical("editorial/negative_contract_review.json"))
record["status"] = "NARRATIVE_PROOF_AND_CONTRACT_REVIEW_COMPLETE; fresh covariance compiler/structural axiom audit PASS; integrated render reviewed separately"
record["narrative_baseline_commit"] = BASE
record["prior_record"] = BASE + ":editorial/negative_contract_review.json"
record["article_file_sha256"] = {name: digest(ROOT / name) for name in record["article_file_sha256"]}
idx = json.loads((ROOT / record["canonical_declaration_index"]).read_text())
summary = json.loads((RUN / "SUMMARY.json").read_text())
supplement = json.loads((RUN / "declarations.json").read_text())
for row in record["article_labels"]:
    if row["label"] == "art:local-failure-lower":
        row["canonical_exports"] = [n for n in row["canonical_exports"] if ".Step" not in n and ".step" not in n]
        row["precise_review"] = "Finite maximum of four strongly convex C1,1 branches only. The countably piecewise-affine constant-Hessian alternative is retained in companion Chapter 13 and is no longer asserted in the article."

public = [r["name"] for r in supplement if r["name"].startswith("NarrativeNegativeScaling.") and "._proof_" not in r["name"]]
rows = [
    {
        "label": "art:regularity-map", "kind": "comparison_of_proved_regularity_regimes",
        "canonical_exports": ["BfgsVerification.DEmbedding.branch_contDiff", "BfgsVerification.DEmbedding.branch_hessian_bounds", "BfgsVerification.DEmbedding.branch_hessian_lipschitz", "BfgsVerification.DEmbedding.deterministic_embedding_failure", "BfgsVerification.LWhitening.smoothLocalFailure", "BfgsVerification.LWhitening.SmoothLocalFailureTarget"],
        "precise_review": "Two data rows compare the actual finite-branch constructions; common fixed-objective, identity-start, locality and all-query conclusions are in the caption. Parameter quantifiers are referred to the separate canonical statements, not conflated. The countable-piece alternative is absent."
    },
    {
        "label": "art:matched-local-model", "kind": "conditional_local_identity_schema",
        "canonical_exports": ["BfgsVerification.SeedEmbedding.trial_predicates", "BfgsVerification.SeedEmbedding.translated_trial", "BfgsVerification.LEmbedding.local_model"],
        "precise_review": "The general local identity is a hypothesis under consideration, not a new existence assertion. Differentiation is the ordinary local chain rule at differentiable points. Actual D and L local value/gradient identities and all-query coverage are supplied by the full construction exports, not by the covariance supplement."
    },
    {
        "label": "art:matched-scaling", "kind": "proved_general_algebraic_covariance",
        "canonical_exports": ["BfgsVerification.bfgsStep_scale_matrix", "BfgsVerification.bfgsStep_scale_gradient", "BfgsVerification.inverseBFGS_scale", "BfgsVerification.inverseBFGS_scale_secant_pair", "BfgsVerification.SeedEmbedding.metric_update", "BfgsVerification.TranslatedRun.matrix_update", "BfgsVerification.TranslatedRun.scaled_pairing"],
        "precise_review": "Fresh supplemental Lean theorems prove the actual full step, inverse update, pairings, function differences and strict/nonstrict Armijo and weak-Wolfe comparisons for the displayed factors. Formula equalities require nonzero scales; comparison equivalences require positive objective scale. The article uses positive spatial/objective scales. No orbit existence, SPD property, local model or query containment is deduced from these algebraic statements."
    }
]
for row in rows:
    row.update({"article_file": "paper/sections/failure.tex", "corrected_spans": ["D.span.7", "D.span.8", "D.span.9", "L.span.6", "L.span.7", "L.span.8"],
                "supplemental_exports": public if row["label"] != "art:regularity-map" else [],
                "essential_exports_reference": "Full union of exports from each listed source_spans entry, plus every module-owned supplemental declaration and its full retained dependency_graph.json; selected canonical_exports are navigation endpoints only.",
                "review_status": "reviewed_against_exact_formal_contracts_and_fresh_supplemental_audit"})
    for name in row["canonical_exports"]:
        if name not in idx:
            raise SystemExit("Missing canonical export: " + name)
        record["canonical_contracts"][name] = {key: idx[name][key] for key in ("signature", "source_path", "source_range", "axioms", "unsafe", "partial")}
    record["article_labels"].append(row)
for row in record["article_labels"]:
    text = (ROOT / row["article_file"]).read_text()
    match = re.search(r"\\label\{" + re.escape(row["label"]) + r"\}", text)
    if not match:
        raise SystemExit("Article label lost: " + row["label"])
    row["line"] = text[:match.start()].count("\n") + 1


# Proof navigation is explicit: a statement input is not its proof location.
def segment(file, start, end, governing_label, role="mathematical_argument"):
    text = (ROOT / file).read_text()
    if text.count(start) != 1:
        raise SystemExit("Nonunique proof start: " + start)
    lo = text.index(start)
    hi = len(text) if end is None else text.index(end, lo + len(start))
    return {"article_file": file, "start_anchor": start,
            "start_line": text[:lo].count("\n") + 1,
            "end_line": text[:hi].count("\n") + (1 if end is None else 0),
            "governing_label": governing_label, "role": role}

def proof_at(file, start, governing_label):
    result = segment(file, start, "\\end{proof}", governing_label, "explicit_proof_environment")
    result["end_line"] += 1
    return result

def proof_after(file, label):
    text = (ROOT / file).read_text()
    lo = text.index("\\label{" + label + "}")
    lo = text.index("\\begin{proof}", lo)
    hi = text.index("\\end{proof}", lo) + len("\\end{proof}")
    return {"article_file": file, "start_anchor": "first proof after \\label{" + label + "}",
            "start_line": text[:lo].count("\n") + 1,
            "end_line": text[:hi].count("\n") + 1,
            "governing_label": label, "role": "explicit_proof_environment"}

failure = "paper/sections/failure.tex"
seed = "paper/appendices/seed_certificate.tex"
lower = "paper/appendices/lower_curvature.tex"
upper_proof = proof_at(failure, "\\begin{proof}[Proof of Theorem~\\ref{art:local-failure}]", "art:local-failure")
upper_construction = segment(failure, "\\subsection{One objective and a uniform induction over all queries}", "\\begin{proof}[Proof of Theorem~\\ref{art:local-failure}]", "art:local-failure", "objective_regularity_and_local_model_before_the_main_induction")
scalar_proof = proof_after(failure, "art:upper_scalar_lemma")
root_proof = proof_after(seed, "art:root_certificate")
closure_proof = proof_at(seed, "\\begin{proof}[Proof of the algebraic part of Lemma~\\ref{art:seed_cycle}]", "art:seed_cycle")
query_proof = segment(seed, "\\subsection{Sound enclosure of every query}", None, "art:seed_cycle", "finite_rational_query_certificate_argument")
cone_proof = segment(failure, "The finite calculation becomes an infinite run through homogeneity.", "\\begin{corollary}[Coercive polyhedral global failure]", "art:seed_cycle", "infinite_actual_trial_tree_induction_from_the_finite_certificate")
polyhedral_proof = proof_after(failure, "art:failure_polyhedral")
hyperbolic_proof = proof_after(lower, "art:lower_hyperbolic")
perturbed_proof = proof_at(lower, "\\begin{proof}[Proof of Proposition~\\ref{art:quadratic_failure}]", "art:quadratic_failure")
lower_scalar = segment(lower, "On each positive interval,", "Define\n", "art:local-failure-lower", "scalar_regularity_and_plateau_proof")
lower_objective = segment(lower, "Define\n", "\\subsection{Copying one entire orbit and fixing the initial matrix}", "art:local-failure-lower", "four_branch_strong_convexity_regularity_minimizer_and_Hessian_proof")
lower_copy = segment(lower, "\\subsection{Copying one entire orbit and fixing the initial matrix}", None, "art:local-failure-lower", "all_query_copy_induction_and_one_fixed_identity_normalization")
covariance = segment(failure, "Differentiation gives", "This is a covariance calculation", "art:matched-scaling", "conditional_model_chain_rule_and_full_update_comparison_algebra")
quadratic_minimum = segment(lower, "The vector\n", "\\begin{proposition}[A perturbed bad orbit]", "art:quadratic_minimizer", "explicit_least_norm_subgradient_and_minimizer_argument")
proof_map = {
    "art:local-failure": [scalar_proof, upper_construction, upper_proof],
    "art:local-failure-lower": [hyperbolic_proof, perturbed_proof, lower_scalar, lower_objective, lower_copy],
    "art:failure": [upper_proof, lower_copy],
    "art:failure_tests": [query_proof, cone_proof],
    "art:failure_update": [closure_proof],
    "art:seed_rho": [root_proof],
    "art:seed_matrices": [closure_proof], "art:seed_steps": [closure_proof],
    "art:seed_points": [closure_proof],
    "art:seed_cycle": [root_proof, closure_proof, query_proof],
    "art:seed_margins": [query_proof], "art:seed_query_bounds": [query_proof],
    "art:trial_table": [query_proof], "art:cycle-figure": [closure_proof, query_proof],
    "art:cone_orbit": [cone_proof], "art:failure_polyhedral": [polyhedral_proof],
    "art:upper_scalar": [scalar_proof], "art:upper_scalar_lemma": [scalar_proof],
    "art:scalar_curvature": [scalar_proof], "art:scalar_plateau": [scalar_proof],
    "art:upper_objective": [scalar_proof, upper_construction],
    "art:upper_local_model": [upper_construction], "art:upper_orbit": [upper_proof],
    "art:seed_certificate": [root_proof, closure_proof, query_proof],
    "art:seed_polynomials": [root_proof, closure_proof],
    "art:root_certificate": [root_proof], "art:root_arithmetic": [root_proof],
    "art:closure_identity": [closure_proof], "art:query_box": [root_proof, query_proof],
    "art:query_lower_bounds": [query_proof],
    "art:lower_curvature": [hyperbolic_proof, perturbed_proof, lower_scalar, lower_objective, lower_copy],
    "art:quadratic_minimizer": [quadratic_minimum],
    "art:quadratic_failure": [hyperbolic_proof, perturbed_proof],
    "art:lower_return_substep": [hyperbolic_proof], "art:lower_return": [hyperbolic_proof],
    "art:lower_hyperbolic": [hyperbolic_proof], "art:shape_certificate": [hyperbolic_proof],
    "art:lower_scalar": [lower_scalar], "art:lower_plateau": [lower_scalar],
    "art:lower_objective": [lower_objective], "art:lower_local_model": [lower_copy],
    "art:matched-local-model": [covariance, upper_construction, lower_copy],
    "art:matched-scaling": [covariance],
    "art:regularity-map": [scalar_proof, upper_construction, upper_proof, lower_scalar, lower_objective, lower_copy],
}
for row in record["article_labels"]:
    if row["label"] not in proof_map:
        raise SystemExit("No explicit proof navigation for " + row["label"])
    row["proof_locations"] = proof_map[row["label"]]
    row["proof_location_scope"] = "Actual article proof/derivation locations. A definition, conditional schema, table or illustrative figure is not thereby reclassified as a theorem."

record["supplemental_formal_audit"] = {
    "summary": str((RUN / "SUMMARY.json").relative_to(ROOT)), "summary_sha256": digest(RUN / "SUMMARY.json"),
    "full_declarations": supplement, "full_dependency_graph": str((RUN / "dependency_graph.json").relative_to(ROOT)),
    "full_dependency_graph_sha256": digest(RUN / "dependency_graph.json"), "summary_data": summary,
}
record["supplemental_formal_audit"]["scope"] = "Separate supplemental algebraic audit; not part of the immutable canonical declaration index."
record["companion_only_disposition"] = {
    "claim": "Constant positive-definite classical-Hessian alternative with convex countably piecewise-affine remainder",
    "reason": "Keep the article's two central finite-branch regularity regimes focused; the countable-piece alternative remains fully stated/proved in the complete companion.",
    "article_change": "Removed the alternative's last four statement lines and final appendix subsection; no central finite-branch hypothesis or conclusion weakened.",
    "companion_file": "companion/chapters/13_L.tex", "corrected_spans": ["L.span.2", "L.span.8"],
    "canonical_exports": ["BfgsVerification.LWhitening.stepLocalFailure", "BfgsVerification.LWhitening.StepLocalFailureTarget"],
    "essential_exports_reference": "Full source_spans exports retained for L.span.2 and L.span.8; no sample-export coverage claim.",
}
record["scope_notes"].extend([
    "Both canonical negative statement inputs are now in the failure section. The upper statement is byte-identical to the narrative baseline.",
    "The lower article statement now selects only the finite C1,1 branch regime. Full source-span exports remain a conservative superset and include companion-only declarations; they are not a claim that every exported theorem appears in the article.",
    "Global coercive polyhedral and global quadratic-branch examples are retained separately; they do not settle local uniformly strongly convex C2 convergence.",
    "New explanatory comparisons of prior work are bibliography assertions, not mathematical claims proved by Lean.",
    "The general scaling supplement verifies actual update algebra and both strict/non-strict tests. Local chain-rule use and actual D/L realization retain their stated differentiability and all-query domains.",
])
record["dependency_counts"]["canonical_contracts_expanded"] = len(record["canonical_contracts"])
record["axiom_policy_check"]["supplemental_evidence"] = str((RUN / "SUMMARY.json").relative_to(ROOT))

# Exact display preservation is checked independently of prose or line wrapping.
pattern = re.compile(r"\\\[.*?\\\]|\\begin\{(equation\*?|align\*?|gather\*?)\}.*?\\end\{\1\}", re.S)
checks = {}
for name in ("paper/sections/failure.tex", "paper/appendices/seed_certificate.tex", "paper/appendices/lower_curvature.tex"):
    old = historical(name)
    if name.endswith("lower_curvature.tex"):
        old = old.split("\\subsection{The constant classical-Hessian alternative}")[0]
    new = (ROOT / name).read_text()
    old_blocks = [m.group() for m in pattern.finditer(old)]
    new_blocks = [m.group() for m in pattern.finditer(new)]
    cursor = 0
    for block in old_blocks:
        while cursor < len(new_blocks) and new_blocks[cursor] != block:
            cursor += 1
        if cursor == len(new_blocks):
            raise SystemExit("Baseline mathematical display changed: " + name + "\n" + block)
        cursor += 1
    checks[name] = {"preserved_displays": len(old_blocks), "current_displays": len(new_blocks), "exact_bytes_preserved_in_order": True}
record["display_preservation_check"] = checks
(HERE / "negative_contract_review.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({"status": "PASS", "labels": len(record["article_labels"]), "source_span_exports": len(record["all_span_exports"]), "supplemental_roots": len(supplement), "display_preservation": checks}, indent=2))
