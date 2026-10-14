#!/usr/bin/env python3
"""Axiom audit for the formal claims of the article and the companion.

Runs `#print axioms` (via `lake env lean`) on every declaration that
`editorial/CLAIM_LEDGER.json` cites, for the article and for the companion (every
export field of every record, and the declaration lists of the article
supplements), on every Lean name of the coverage register
(`editorial/lean_coverage/register/*.json`, items with status LEAN, DEFINITION or
OPEN), plus the principal declarations of this package. Fails if a cited
name does not exist or if any declaration depends on an axiom other than
propext, Classical.choice and Quot.sound. The names are split across `--jobs`
concurrent Lean processes. Private names (`_private.…`) in the supplements'
declaration lists cannot be referred to outside their module; they are listed
in the report, and their axioms are part of those of the public declarations
that use them.

It also records the exact signature and module of this package's principal
declarations, which `editorial/assemble_claim_ledger.py` uses for the ledger.

With --write-guard it also regenerates `BfgsArticleAxioms.lean`, which pins
the `#print axioms` output of the principal exports with `#guard_msgs`, so that
a plain `lake build` fails if any of them changes.

Usage (from bfgs_lean_article/, after `lake build BfgsArticle`):
    python3 scripts/axiom_audit.py [--jobs 3] [--write-guard] [--report AXIOM_AUDIT.json]
"""
from pathlib import Path
import argparse, datetime, json, re, subprocess, sys

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
ROOT = PACKAGE.parent
LEDGER = ROOT / 'editorial' / 'CLAIM_LEDGER.json'
COVERAGE = ROOT / 'editorial' / 'lean_coverage' / 'register'
GUARD = PACKAGE / 'BfgsArticleAxioms.lean'
STANDARD = ['propext', 'Classical.choice', 'Quot.sound']

# Principal declarations of this package.
PACKAGE_PRINCIPAL = [
    'BfgsVerification.LGlobalFailure.nonstrict_actual_global_failure',
    'BfgsVerification.LGlobalFailure.nonstrict_source_global_failure',
    'BfgsVerification.LActualCopies.NonStrictFixedMetricFailureTarget',
    'BfgsVerification.LActualCopies.nonstrict_fixed_metric_failure',
    'BfgsVerification.LActualCopies.nonstrictSmoothFailure',
    'BfgsVerification.LActualCopies.nonstrictStepFailure',
    'BfgsVerification.LWhitening.NonStrictIdentityFailureTarget',
    'BfgsVerification.LWhitening.nonstrict_identity_failure',
    'BfgsVerification.LWhitening.NonStrictSmoothLocalFailureTarget',
    'BfgsVerification.LWhitening.nonstrictSmoothLocalFailure',
    'BfgsVerification.LWhitening.NonStrictStepLocalFailureTarget',
    'BfgsVerification.LWhitening.nonstrictStepLocalFailure',
    'ArticleBranchRegularity.nonstrictSmoothLocalFailure_with_branch_obstruction',
    'BfgsVerification.AdmissibleBFGSRun.homogeneous_conclusion_of_bounded_zero_sublevel',
    'BfgsVerification.AdmissibleBFGSRun.norm_conclusion',
    'BfgsVerification.AdmissibleBFGSRun.gauge_conclusion',
    'BfgsVerification.AdmissibleBFGSRun.finiteMaxLinear_conclusion',
    'BfgsVerification.LNormalizedOracle.uniform_conditions_eventually',
    'BfgsVerification.LNormalizedOracle.UniformConditions.conditions',
    'BfgsVerification.LUniform.uniform_global_failure',
    'BfgsVerification.LUniform.FailureRun',
    'BfgsVerification.LUniform.UniformlyLocal',
    'BfgsVerification.LUniform.UniformFailureTarget',
    'BfgsVerification.LUniform.uniform_fixed_metric_failure',
    'BfgsVerification.LUniform.uniform_identity_failure',
    'BfgsVerification.LUniform.ObjectiveGeometry',
    'BfgsVerification.LUniform.branch_not_twice_differentiable_zero',
    'BfgsVerification.LUniform.UniformSmoothLocalFailureTarget',
    'BfgsVerification.LUniform.uniformSmoothLocalFailure',
]

# Names may contain apostrophes, so the name is the shortest match before `' depends`.
AXIOMS = re.compile(r"'([^\n]+?)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
# Ledger fields that list Lean declarations.
EXPORT_FIELDS = ('principal_exports', 'full_formal_exports', 'all_span_exports', 'primary_declarations', 'exports')
SIGNATURE = re.compile(r'BFGS_SIGNATURE_BEGIN (\S+) (\S+)\n(.*?)\nBFGS_SIGNATURE_END', re.S)

SIGNATURE_COMMAND = '''open Lean Elab Command in
elab "#bfgs_signature " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfo name
  let env ← getEnv
  let module := match env.getModuleIdxFor? name with
    | some idx => toString env.allImportedModuleNames[idx.toNat]!
    | none => "unknown"
  let type ← liftTermElabM <| Meta.ppExpr info.type
  logInfo m!"BFGS_SIGNATURE_BEGIN {name} {module}\\n{type}\\nBFGS_SIGNATURE_END"
'''


def collect(value, out):
    if isinstance(value, dict):
        for key, item in value.items():
            if key in EXPORT_FIELDS and isinstance(item, list):
                out.update(name for name in item if isinstance(name, str))
            else:
                collect(item, out)
    elif isinstance(value, list):
        for item in value:
            collect(item, out)


def ledger_names():
    """Article principal exports, article-cited names, companion-cited names, skipped private names."""
    ledger = json.loads(LEDGER.read_text())
    principal = set()
    for record in ledger['article_records']:
        principal.update(record.get('principal_exports', []))
    article, companion = set(principal), set()
    for key, value in ledger.items():
        if key.startswith('companion'):
            collect(value, companion)
        else:
            collect(value, article)
    supplements = [s['declarations'] for s in ledger['narrative_formal_supplements']['supplements']]
    supplements.append(ledger['literal_branch_regularity_supplement']['declarations'])
    for path in supplements:
        article.update(entry['name'] for entry in json.loads((ROOT / path).read_text()))
    private = sorted(n for n in article | companion if n.startswith('_private.'))
    article -= set(private)
    companion -= set(private)
    return sorted(principal), sorted(article), sorted(companion), private


def coverage_names():
    """Lean names of the coverage register (statuses LEAN, DEFINITION, OPEN)."""
    names = set()
    for path in sorted(COVERAGE.glob('*.json')):
        for item in json.loads(path.read_text())['items']:
            if item.get('status') in ('LEAN', 'DEFINITION', 'OPEN'):
                names.update(item.get('lean') or [])
    return sorted(names)


def run_lean(sources):
    """Run `lake env lean` on generated files concurrently; return [(code, output)]."""
    work = PACKAGE / '.lake' / 'axiom_audit'
    work.mkdir(parents=True, exist_ok=True)
    running = []
    for name, text in sources:
        source, log = work / name, work / (name + '.out')
        source.write_text(text)
        handle = log.open('w')
        process = subprocess.Popen(['lake', 'env', 'lean', str(source)], cwd=PACKAGE,
                                   stdout=handle, stderr=subprocess.STDOUT)
        running.append((process, handle, log))
    results = []
    for process, handle, log in running:
        code = process.wait()
        handle.close()
        results.append((code, log.read_text()))
    return results


def order(axioms):
    return [a for a in STANDARD if a in axioms] + sorted(a for a in axioms if a not in STANDARD)


def guard_text(names, found):
    lines = ['import BfgsArticle', '',
             '/-! Generated by `scripts/axiom_audit.py --write-guard`; do not edit by hand.',
             'Pins the axioms of every principal export cited by `editorial/CLAIM_LEDGER.json`',
             'and of the principal declarations of this package. -/', '']
    for name in names:
        axioms = found[name]
        if axioms:
            message = f"'{name}' depends on axioms: [{', '.join(order(axioms))}]"
        else:
            message = f"'{name}' does not depend on any axioms"
        lines += [f'/-- info: {message} -/', '#guard_msgs (whitespace := lax) in', f'#print axioms {name}', '']
    return '\n'.join(lines)


def command_output(command, cwd):
    return subprocess.run(command, cwd=cwd, capture_output=True, text=True).stdout.strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--write-guard', action='store_true')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--jobs', type=int, default=3, help='concurrent Lean processes (default 3)')
    args = parser.parse_args()
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    source_commit = command_output(['git', 'rev-parse', 'HEAD'], ROOT)
    source_tree_clean = command_output(['git', 'status', '--porcelain'], ROOT) == ''

    principal, article, companion, private = ledger_names()
    coverage = coverage_names()
    cited = sorted(set(article) | set(companion) | set(coverage))
    names = sorted(set(cited) | set(PACKAGE_PRINCIPAL))
    jobs = max(1, min(args.jobs, len(names)))
    sources = [(f'AxiomAudit{i}.lean', 'import BfgsArticle\n\n' +
                ''.join(f'#print axioms {n}\n' for n in names[i::jobs])) for i in range(jobs)]
    sources.append(('Signatures.lean', 'import BfgsArticle\n\n' + SIGNATURE_COMMAND + '\n' +
                    ''.join(f'set_option pp.fullNames true in\n#bfgs_signature {n}\n'
                            for n in PACKAGE_PRINCIPAL)))
    *audits, (sig_code, sig_output) = run_lean(sources)
    code = next((c for c, _ in audits if c != 0), 0)
    output = '\n'.join(o for _, o in audits)
    found = {m.group(1): order([a.strip() for a in (m.group(2) or '').replace('\n', ' ').split(',') if a.strip()])
             for m in AXIOMS.finditer(output)}
    missing = [n for n in names if n not in found]
    nonstandard = {n: a for n, a in found.items() if not set(a) <= set(STANDARD)}

    signatures = {m.group(1): (m.group(2), m.group(3)) for m in SIGNATURE.finditer(sig_output)}
    unsigned = [n for n in PACKAGE_PRINCIPAL if n not in signatures]

    counts = {}
    for axioms in found.values():
        key = ', '.join(axioms) or '(none)'
        counts[key] = counts.get(key, 0) + 1
    passed = code == 0 and sig_code == 0 and not missing and not nonstandard and not unsigned
    report = {
        'status': 'PASS' if passed else 'FAIL',
        'started_utc': started,
        'lean_version': command_output(['lake', 'env', 'lean', '--version'], PACKAGE),
        'source_commit': source_commit,
        'source_tree_clean': source_tree_clean,
        'command': 'python3 scripts/axiom_audit.py' + (' --write-guard' if args.write_guard else ''),
        'policy': 'every declaration cited by the claim ledger (article and companion) or by the coverage register exists and depends on no axiom outside ' + ', '.join(STANDARD),
        'declarations_checked': len(names),
        'ledger_principal_exports': len(principal),
        'ledger_cited_exports': len(article),
        'ledger_companion_exports': len(companion),
        'ledger_companion_only_exports': len(set(companion) - set(article)),
        'coverage_register_names': len(coverage),
        'package_principal_declarations': len(PACKAGE_PRINCIPAL),
        'axiom_set_counts': counts,
        'missing_or_unresolved': missing,
        'nonstandard_axioms': nonstandard,
        'private_names_not_referable': private,
        'package_declarations': [
            {'name': n, 'module': signatures[n][0], 'signature': signatures[n][1], 'axioms': found.get(n)}
            for n in PACKAGE_PRINCIPAL if n in signatures],
    }
    if args.report:
        args.report.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    summary = {k: v for k, v in report.items() if k != 'package_declarations'}
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    if not passed:
        print(output[-3000:], sig_output[-3000:], file=sys.stderr)
        return 1
    if args.write_guard:
        guarded = sorted(set(principal) | set(PACKAGE_PRINCIPAL))
        GUARD.write_text(guard_text(guarded, found) + '\n')
        print(f'wrote {GUARD.relative_to(ROOT)} ({len(guarded)} declarations)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
