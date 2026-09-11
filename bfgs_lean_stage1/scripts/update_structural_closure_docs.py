#!/usr/bin/env python3
"""Write milestone documentation only after the complete frozen audit passes."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
s=json.loads((ROOT/'audit/STATUS.json').read_text())
assert s['status']=='MODULE_M_AND_REPORT_STRUCTURAL_CLOSURE_TARGETS_VERIFIED'
assert not s['unexpected_axioms'] and not s['missing_axiom_reports'] and not s['remaining_target_obligations']
n=len(s['verified_declarations']);total=s['audited_declaration_count'];count=len(s['sources'])
assert n>3004
p=ROOT/'README.md';t=p.read_text()
old='The pinned Lean 4.19.0 build and transitive axiom audit checked all 3,004 explicit\ntheorems and 4,254 theorem declarations including generated auxiliaries. All 106\nregistered exact targets passed.'
assert old in t
t=t.replace(old,f'The pinned Lean 4.19.0 build and transitive axiom audit checked all {n:,} explicit\ntheorems and {total:,} theorem declarations including generated auxiliaries. All 120\nregistered exact targets passed.',1)
t=t.replace('`audit/report_embedding_check.log`.','`audit/report_structural_closure_check.log`.',1)
old="L's nonlinear persistence/embeddings, A's remaining infrastructure, C's further\napplications/examples and uniform transport statement, general nuclear/descriptive\nidentities, and final source reconciliation remain open."
assert old in t
t=t.replace(old,"The eleventh tranche closes A's actual compact affine gap, C's nondegenerate\nfinite-max and explicit three-quadratic basin/radial-separation results, and R's\narbitrary rectangular nuclear norm and literal first-difference family. L's actual\nreturn/oracle neighborhood and constructive conditional stable-orbit/splitting\ncriteria are checked. See\n[audit/REPORT_STRUCTURAL_CLOSURE_STATEMENT_REVIEW.md](audit/REPORT_STRUCTURAL_CLOSURE_STATEMENT_REVIEW.md).\nL's actual spectral application and embeddings, A's semialgebraic infrastructure,\nC's remaining uniform-transport and higher-dimensional assertions, stronger\nsmooth-manifold regularity, and final source reconciliation remain open.",1)
p.write_text(t)
records={
'ENTIRE_REPORT_PLAN.md':f'''

## Eleventh execution milestone: affine gap, planar applications, matrix families

The frozen pinned build and full transitive audit pass **{n:,} explicit / {total:,}
total theorem declarations**, **120 exact targets**, and **{count} source hashes**.
Only propext, Classical.choice and Quot.sound occur. Logs are
`audit/report_structural_closure_check.log`, `audit/build.log` and `audit/axioms.log`;
statement/independent reviews are linked in
`audit/REPORT_STRUCTURAL_CLOSURE_STATEMENT_REVIEW.md`.

A now has actual local affine-distance lower semicontinuity and an attained
positive compact-band gap under its original-active nondegeneracy hypotheses.
C's finite-max corollary, actual positive branch-Hessian sufficient condition,
and every literal three-quadratic example calculation are checked, including
the exact F(x0)<1/100 all-run basin and fixed-band every-neighborhood RS exclusion.
R's arbitrary rectangular nuclear norm is proved from actual Gram eigenvalues,
with its variational formula, zero-safe polar witness, norm properties, centered
and mixed-power applications. Literal weighted first differences have the actual
nonzero-solution local basin.

L's actual analytic three-step return and deterministic oracle agreement are
checked. A constructive contraction on C0 sequences produces actual local stable
orbits; explicit five-dimensional eigenvectors/inverse coordinates convert the
stated block spectral data to this criterion. The two new stable-orbit exact
targets are conditional dynamics infrastructure. The actual J certificate and
infinite physical perturbed-run application are still separate obligations.
The direct orbit proof replaces the source's manifold route for trajectory
existence, without asserting the stronger smooth-manifold/tangency claim.

Next work continues in L's actual shape spectrum/global run and degree-two scalar
and local embeddings, A's actual path calculus and semialgebraic infrastructure,
C's remaining higher-dimensional and uniform transport assertions, and final
all-source/synthesis/evidence review. Entire-report verification remains false.
''',
'PROOF_OBLIGATIONS.md':f'''

## Eleventh whole-report tranche

The audit passes {n:,} explicit / {total:,} total theorem declarations and all
120 exact targets. A's compact affine gap, C's nondegenerate finite-max corollary
and Hessian replacement, the literal three-quadratic example, and R's arbitrary
rectangular nuclear norm/mixed powers/first-difference family have no remaining
proof premise in their stated targets.

L's actual return and oracle neighborhood are proved, as are the constructive
stable-orbit and explicit spectral-splitting criteria. These criteria retain
actual derivative/root premises and are not counted as an unconditional BFGS
failure result. Actual J intervals and the infinite physical run remain to link.
The source's stronger smooth stable-manifold/tangency assertion and local
analytic diffeomorphism are separate obligations, alongside L's C1,1/countably
affine embeddings and identity initialization. A's semialgebraic theorem, C's
remaining higher-dimensional/uniform transport claims, historical R attribution
and final synthesis remain open. See `audit/REPORT_STATUS.json` and the eleventh
statement review. No original source was changed.
''',
'MATHEMATICAL_REVIEW.md':f'''

## Eleventh report statement review

The full audit passes {n:,} explicit / {total:,} total theorem declarations and
120 exact targets. A's distance is the actual Euclidean distance to the affine
hull of the actual subdifferential, not a surrogate gap. C's finite-max application
only requires original-active independence and positive weights, and its common
Hessian premise is on actual second Frechet derivatives. The literal quadratic
example has actual eligible/SPD-realized pairs and eta chosen before every
smallness parameter and proposed radial constant; its convergence theorem does
not infer divergence from those pairs.

The rectangular nuclear construction uses actual Gram eigenvalues, square-root
trace and an attaining spectral-contraction witness in arbitrary dimensions,
including rank zero. All named objective applications derive norm properties
before applying convergence criteria. L's actual normalized return holds input
tau fixed through all three substeps, and its positive-scale neighborhood derives
all actual search decisions and point/matrix updates.

The nonlinear orbit is constructed by a contraction on the complete space of
sequences tending to zero, after proving the operator maps that space to itself;
no convergent orbit is assumed. Explicit inverse coordinates and conjugacy give
the required stable/inverse-unstable norm bounds from the stated actual block
roots. Actual spectral inputs and global BFGS application remain open in this
release; smooth-manifold regularity is not implied by orbit existence. All exact
scopes and independent reviews are linked in
`audit/REPORT_STRUCTURAL_CLOSURE_STATEMENT_REVIEW.md`.
'''}
for name,record in records.items():
 p=ROOT/name;t=p.read_text();heading=next(x for x in record.splitlines() if x.startswith('## '))
 assert heading not in t
 p.write_text(t+record)
print(f'Eleventh documentation updated: {n} explicit, {total} total, 120 exact targets.')
