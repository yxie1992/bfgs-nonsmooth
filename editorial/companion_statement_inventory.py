"""Classify the full companion record and recover non-environment statements.

This indexes retained mathematical text; it does not parse Lean semantics or
promote a proof passage, definition, conditional criterion, or open question to
an unconditional algorithm theorem. Every export list is the complete source
span union, never a chosen sample declaration.
"""
from pathlib import Path
import hashlib
import re

EXACT_CONTRACTS = "bfgs_lean_stage1/master_report/DECLARATION_INDEX.json"

CONDITIONAL_NOTES = {
    "M.span.4": "The moving-frame convergence criterion assumes visibility, secant control and bounded cumulative transport/inverses on a hypothetical tail; the objective must separately supply them. The fixed-reference identity is algebraic and its gap bound additionally uses a minimizer.",
    "M.span.5": "The residual-frame criterion assumes the stated fixed smooth-subspace, curvature and frame conditions. Its residual budget is derived; arbitrary objectives are not asserted to satisfy the criterion.",
    "T.span.3": "Objective-level certificate existence and every eligible-pair inequality are hypotheses; the actual BFGS conclusion follows under them.",
    "T.span.5": "The local structural hypotheses and a compact trapped low sublevel remain required; weaker late-band/tail formulations retain their explicit quantifiers.",
    "A.span.1": "Convergence from an affine-critical cluster point additionally requires no false affine criticality. The equal-rate separation identities alone are not a BFGS convergence theorem.",
    "A.span.3": "Affine independence and strictly positive optimal barycentric coefficients are hypotheses. Local affine-critical correctness and visibility do not by themselves supply arbitrary-dimensional transport.",
    "C.span.11": "Affine-critical correctness is an additional hypothesis when deriving convergence from the cluster theorem; uniqueness is needed for whole-iterate convergence.",
    "C.span.12": "The semialgebraic gap replaces the no-false-affine-criticality hypothesis only while the planar strict-contour and regular-switching assumptions are retained.",
    "C.span.15": "The constructed equal-rate field supplies visibility and bounded secant correction under the stated smooth-max hypotheses. Projected transport and arbitrary-dimensional BFGS convergence are not concluded.",
    "F.span.5": "Rates use the separately stated bounded/cumulative reference correction, bounded-below homogeneity, or quadratic-plus-coercive-gauge hypotheses. Constants are instance dependent and count accepted iterations.",
    "H.span.3": "Finite convex degree-one homogeneity and an infinite admissible full-BFGS run are hypotheses; no iterate, displacement, step-length or matrix boundedness is assumed. Bounded-below/coercive consequences add their stated objective assumptions.",
    "H.span.4": "Finite recurrent gradient alphabet and a finite value limit imply affine balance. The many-piece escape conclusion assumes affine exclusion; finite termination of every implementation is not asserted.",
    "H.span.5": "The stated planar unbounded-below dichotomy retains dimension and objective assumptions. The broader finite-value iterate conclusion requires recurrent-gradient span dimension at most two.",
    "H.span.13": "The affine-balance lemma assumes a finite recurrent gradient alphabet and a finite objective limit. It does not assume bounded displacement.",
    "U.span.2": "One exceptional hyperplane, strong convexity, Lipschitz tangential projection, off-interface local C1,1 regularity and the compact-basin hypotheses are retained. The local basin precedes arbitrary SPD initialization and fixed valid line-search constants.",
    "U.span.3": "The full-strong-convexity composite family and its tangential-only-curvature alternative are distinct. The latter keeps strict positive contours, unique minimization on the interface, and a compact initial sublevel.",
    "U.span.4": "The parallel-interface theorem requires a closed collection of genuinely nonsmooth interfaces, strong convexity and the stated tangential/smoothness conditions. Convergence additionally requires no false affine criticality, and uniqueness for iterate convergence.",
    "U.span.11": "Only projected tangential strong curvature is used, with the stated strict positive sublevels and local regularity; no normal lower-curvature assumption is inserted.",
}

# Additional results embedded in a larger source span. These exact anchors are
# author-reviewed navigation points, not automatically inferred theorem claims.
INLINE_RESULTS = [
    ("fixed-reference-energy", "M.span.4", "For any fixed reference point", "identity_and_conditional_gap_bound"),
    ("moving-frame-criterion", "M.span.4", "For $V_k\\in\\mathbb R^{n\\times r}$, suppose", "conditional_trajectory_criterion"),
    ("bounded-correction-rate", "F.span.5", "\\paragraph{Uniformly bounded reference correction.}", "conditional_rate_corollary"),
    ("homogeneous-rate", "F.span.5", "\\paragraph{Bounded-below degree-one objectives.}", "conditional_rate_corollary"),
    ("quadratic-gauge-rate", "F.span.5", "\\paragraph{Quadratic plus coercive gauge.}", "conditional_rate_corollary"),
    ("affine-barycentric-stability", "A.span.3", "Let $F=\\max_{i\\le m}f_i$", "conditional_geometric_proposition"),
    ("affine-gap-lower-semicontinuity", "A.span.3", "There is also local lower semicontinuity", "conditional_geometric_proposition"),
    ("upper-scalar-hessian-lipschitz", "D.span.7", "\\paragraph{Additional regularity.}", "scalar_regularity_result"),
    ("composite-full-curvature", "U.span.3", "An immediate family is", "conditional_convergence_corollary"),
    ("composite-tangential-curvature", "U.span.3", "Full strong convexity can be weakened", "conditional_convergence_corollary"),
]


def headings(text):
    """Balanced TeX heading/bold arguments, allowing multiline source headings."""
    for match in re.finditer(r"\\(section|subsection|subsubsection|paragraph|textbf)\*?\{", text):
        depth, pos, begin = 1, match.end(), match.end()
        while depth and pos < len(text):
            if text[pos] == "\\" and pos + 1 < len(text) and text[pos + 1] in "{}":
                pos += 2
                continue
            depth += (text[pos] == "{") - (text[pos] == "}")
            pos += 1
        assert depth == 0, (match.group(0), begin)
        yield match.start(), pos, match[1], text[begin:pos-1]


def build(root, source, claims, theorem_records):
    texts = {r["companion_file"]: (root/r["companion_file"]).read_text() for r in source["rows"]}
    span_by_id = {r["source_span"]: r for r in source["rows"]}
    assert len(span_by_id) == len(source["rows"]) == 172
    named, spans, inline = [], [], []
    env_coverage = {sid for row in theorem_records for sid in row["source_spans"]}
    manual_coverage = set()

    def row_for(sid, ident, kind, offset=None, title=None, anchor=None):
        src = span_by_id[sid]
        text = texts[src["companion_file"]]
        start = text.index("% SOURCE_BEGIN " + sid)
        end = text.index("% SOURCE_END " + sid, start)
        body_start = text.index("\n", start) + 1
        exports = sorted(claims[sid]["exports"])
        assert exports == sorted(src["formal_exports"]), sid
        pos = body_start if offset is None else offset
        classification = src["source_classification"]
        if classification == "open_question":
            status = "OPEN_QUESTION_NOT_VERIFIED"
        elif classification == "proved_summary_and_open_question":
            status = "MIXED_PROVED_SUMMARY_AND_EXPLICIT_OPEN_QUESTION"
        elif classification == "mathematics_evidence_and_open_boundaries":
            status = "MIXED_MATHEMATICS_EVIDENCE_AND_OPEN_BOUNDARIES"
        elif classification == "mathematics_and_evidence_scope":
            status = "MATHEMATICAL_SUITE_DESCRIPTION_WITH_EXECUTION_SCOPE"
        elif classification == "execution_evidence_or_scope":
            status = "EXECUTION_OR_SCOPE_RECORD_NOT_A_THEOREM"
        elif classification == "notation_or_scope":
            status = "DEFINITION_OR_SCOPE_NOT_AN_ADDITIONAL_THEOREM"
        else:
            status = "KERNEL_CHECKED_CONTRACTS_UNDER_EXACT_STATED_HYPOTHESES"
        return {
            "id": ident, "kind": kind, "title": title,
            "location": {"path": src["companion_file"], "line": text[:pos].count("\n")+1,
                         "sha256": hashlib.sha256((root/src["companion_file"]).read_bytes()).hexdigest()},
            "anchor": anchor, "source_spans": [sid],
            "source_ids": [src["editorial_id"]],
            "source_classification": classification,
            "source_corrected_lines": src["source_corrected_lines"],
            "companion_source_range": [text[:body_start].count("\n")+1, text[:end].count("\n")],
            "full_formal_exports": exports, "exact_contracts": EXACT_CONTRACTS,
            "status": status,
            "hypothesis_status": CONDITIONAL_NOTES.get(sid,
                "All hypotheses and quantifiers are those of the retained source and exact exported types. An export set is not a declaration that every listed assertion is unconditional."),
            "definition_status": "Definitions, notation and assumptions in this source context are not separately asserted as proved theorems.",
            "open_question_status": "Open assertions are not justified by adjacent theorem exports." if "open" in classification else "No open assertion is promoted by this record.",
            "source_review_note": claims[sid]["review_note"],
            "bibliographic_notes": claims[sid].get("bibliographic_notes", []),
            "coverage_policy": "The entire exact source-span export set is retained conservatively. No principal/sample export is substituted for coverage; atomic proof dependencies are read from the declaration index.",
        }

    for sid, src in span_by_id.items():
        text = texts[src["companion_file"]]
        start = text.index("% SOURCE_BEGIN " + sid)
        end = text.index("% SOURCE_END " + sid, start)
        body = text[start:end]
        hs = list(headings(body))
        title = re.sub(r"\s+", " ", hs[0][3]).strip() if hs else sid
        role = "retained_proved_mathematical_span"
        if src["source_module"] == "I": role = "inventory_summary_or_scope"
        elif src["source_module"] == "E": role = "evidence_suite_or_scope"
        elif src["source_classification"] != "proved_mathematics": role = "definition_scope_or_open_boundary"
        spans.append(row_for(sid, "companion.span." + sid, role, title=title))
        for rel, finish, heading_kind, heading in hs:
            match = re.match(r"(Theorem|Lemma|Proposition|Corollary)\s+", heading)
            if not match: continue
            # Bold 'Proof' and ordinary subsection prose are intentionally excluded.
            stem = {"H.span.3":"H:theorem-a-an-unconditional-objective-value-dichotomy",
                    "H.span.4":"H:theorem-b-a-many-piece-extension-of-the-common-tilt-geometry",
                    "H.span.5":"H:theorem-c-complete-iterate-dichotomy-in-the-planar-unbounded-below-case",
                    "H.span.13":"H:manual-lemma-7.3", "U.span.2":"U:one", "U.span.4":"U:parallel"}.get(sid)
            assert stem, (sid, heading)
            row = row_for(sid, "companion." + stem, match[1].lower(), start+rel,
                          re.sub(r"\s+", " ", heading), body[rel:finish])
            row["presentation"] = "manual_" + heading_kind
            row["labels"] = [stem] if sid != "H.span.13" else []
            row["statement_scope"] = "Named result and its retained source-span context; hypotheses are not removed by the manual heading."
            named.append(row); manual_coverage.add(sid)

    for ident, sid, anchor, kind in INLINE_RESULTS:
        src = span_by_id[sid]; text = texts[src["companion_file"]]
        start = text.index("% SOURCE_BEGIN " + sid); end = text.index("% SOURCE_END " + sid, start)
        assert text[start:end].count(anchor) == 1, (sid, anchor)
        inline.append(row_for(sid, "companion.inline." + ident, kind,
                              text.index(anchor, start, end), ident.replace("-", " "), anchor))

    unnamed = [dict(r, id=r["id"].replace("companion.span.", "companion.unnamed."),
                    kind="unnamed_mathematical_result_or_proof_bundle")
               for r in spans if r["source_classification"] == "proved_mathematics"
               and span_by_id[r["source_spans"][0]]["source_module"] not in {"I", "E"}
               and r["source_spans"][0] not in env_coverage | manual_coverage]
    all_ids = [r["id"] for r in named+inline+unnamed+spans]
    assert len(all_ids) == len(set(all_ids))
    summary = {
        "source_spans_expected": 172, "source_spans_recorded": len(spans),
        "manual_named_results": len(named), "inline_results_with_exact_anchors": len(inline),
        "unnamed_mathematical_spans_without_named_environments": len(unnamed),
        "all_source_export_lists_match": True,
        "manual_heading_detection_complete": True,
        "unmapped_source_spans": sorted(set(span_by_id)-{r["source_spans"][0] for r in spans}),
        "policy": "Named results, explicit inline corollaries, unnamed proof bundles, definitions, evidence and open questions remain separate record classes; none of these counts denotes a number of independently proved theorems.",
    }
    return named, inline, unnamed, spans, summary
