#!/usr/bin/env python3
"""Publish the ninth milestone's documentation after the complete audit passes."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
s = json.loads((ROOT / 'audit/STATUS.json').read_text())
assert s['status'] == 'MODULE_M_AND_REPORT_CONSTRUCTION_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports']
n = len(s['verified_declarations'])
total = s['audited_declaration_count']
assert n > 2193

path = ROOT / 'README.md'
text = path.read_text()
old = 'The pinned Lean 4.19.0 build and transitive axiom audit checked all 2,193 explicit\ntheorems and 3,134 theorem declarations including generated auxiliaries. All 85\nregistered exact targets passed.'
new = f'The pinned Lean 4.19.0 build and transitive axiom audit checked all {n:,} explicit\ntheorems and {total:,} theorem declarations including generated auxiliaries. All 95\nregistered exact targets passed.'
assert old in text
text = text.replace(old, new).replace('`audit/report_dynamics_check.log`.', '`audit/report_construction_check.log`.')
old = 'C endpoint/main conclusions, U examples, A semialgebraic infrastructure, D/L\ncoercive/local embeddings and return-map dynamics, and final source reconciliation\nremain open. The homogeneous seed is not the final coercive/local D counterexample.'
new = '''The ninth tranche proves D's actual coercive deterministic counterexample and
complete global C2,1 scalar construction, U's literal infinite-spike objective,
all-dimensional convergence/radial separation and executable exact rational
oracle, C's actual tail logarithmic transport, and the rectangular spectral-norm
and singular-curvature interpretations in R. See
[audit/REPORT_CONSTRUCTION_STATEMENT_REVIEW.md](audit/REPORT_CONSTRUCTION_STATEMENT_REVIEW.md).
D's local two-dimensional embedding, L's persistence/embeddings, C's secant/main
conclusions, U's variable-jump example, A's remaining infrastructure, nuclear and
descriptive family identifications, and final source reconciliation remain open.
R's old four-piece numerical attribution remains explicitly unresolved; the
supporting-plane interpretation is proved for the actual current D objective.'''
assert old in text
path.write_text(text.replace(old, new))

record = f'''

## Ninth execution milestone — completed

The pinned full build and transitive audit checked **{n:,} explicit theorems**,
**{total:,} total theorem declarations** including generated auxiliaries, and
all **95 exact targets**, with only the three standard foundational axioms.
There are **{len(s['sources'])} frozen Lean source hashes** in the status record.
Evidence: `audit/report_construction_check.log`, `audit/build.log`,
`audit/axioms.log`, and the scoped source/type/peer reviews linked in
`audit/REPORT_CONSTRUCTION_STATEMENT_REVIEW.md`.

This milestone adds the actual coercive deterministic seed, D's literal global
C2,1 scalar functions and all closed plateaus, U's actual infinite spike and
all-dimensional objective/convergence/RS separation plus terminating exact
rational oracle, C's actual full-BFGS tail logarithmic transport, and R's
spectral-norm, norm-convention, singular-curvature and current-model intercept
checks. The current-model intercept correction preserves the unresolved older
numerical attribution in the source record.

Next: finish D's actual local two-dimensional embedding and all deterministic
queries; C's secant and main/local consequences; U's variable-jump example;
L's genuine return-map persistence and embeddings; A's remaining compact
gap/semialgebraic infrastructure; remaining nuclear/descriptive identities,
historical references and final synthesis. The entire report remains incomplete.
'''
path = ROOT / 'ENTIRE_REPORT_PLAN.md'
assert '## Ninth execution milestone' not in path.read_text()
path.write_text(path.read_text() + record)

record = f'''

## Ninth whole-report tranche

Full audit: {n:,} explicit/{total:,} total theorem declarations; 95 exact targets.
The new exact constructions and remaining boundaries are reviewed in
`audit/REPORT_CONSTRUCTION_STATEMENT_REVIEW.md`. The source register now
distinguishes the completed D scalar/coercive examples, U spike/oracle,
C actual tail transport, and R examples from their remaining local embedding,
secant, variable-jump, nuclear and historical obligations. No actual BFGS
conclusion is substituted by a sequence hierarchy or an assumed limit.

R's older four-piece numerical reference is not verified for the current
objective. The actual current D supporting heights and secant limit, and
RS/SP failure on its initial sublevel, are checked and explicitly documented.
Original research sources remain unchanged. Entire-report completion is false.
'''
path = ROOT / 'PROOF_OBLIGATIONS.md'
assert '## Ninth whole-report tranche' not in path.read_text()
path.write_text(path.read_text() + record)

record = f'''

## Ninth report statement review

The frozen project audit passed {n:,} explicit and {total:,} total theorem
declarations and 95 exact targets. `REPORT_CONSTRUCTION_STATEMENT_REVIEW.md`
records the exact scope, and independent reviews cover the scalar construction,
actual infinite-spike objective/oracle, and corrected supporting-plane example.
All derivative interchanges, infinite tails, deterministic search histories,
and objective-level limits are proved in Lean. Actual derivative existence at
accumulation points is asserted explicitly where required.

D's positive scalar is implemented as a ramp series proved equal to every
printed piece. Its second derivative is an attained nonnegative ramp component;
the Lipschitz proof compares that component with the full sum. Combining the
positive and negative halves takes the maximum of their second derivatives
and constants. These proof-route changes preserve the literal construction and
sharp constants. C's right-derivative comparison avoids assuming a finite
crossing partition. U's executable rational oracle is universally identified
with the actual infinite integral, including both derivative outputs.

R's historical(-1,5),25/4 attribution could not be recovered. The currentD
objective has optimizer(-1,16), heights0,0,-1+c-16d, and actual RS/SP failure;
the discrepancy and its checked correction are explicit in
`audit/COERCIVE_SEED_INTERCEPT_CORRECTION.md`. No original source was overwritten.
The remaining entire-report obligations are retained in `audit/REPORT_STATUS.json`.
'''
path = ROOT / 'MATHEMATICAL_REVIEW.md'
assert '## Ninth report statement review' not in path.read_text()
path.write_text(path.read_text() + record)
print(f'Ninth documentation updated: {n} explicit, {total} total, 95 targets.')
