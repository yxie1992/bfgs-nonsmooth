#!/usr/bin/env python3
"""Read-only receipt consistency review (like final_receipt_review.json of 13 Sep).

Usage: python3 receipt_review.py REPO_ROOT RUN_ID [ZIP_PATH]
Prints a JSON review; writes nothing. Checks: ZIP bytes/hash = SOURCE_MANIFEST; validation
SUMMARY PASS for the manifest's commit and archive; every command exited 0 and every
recorded stdout/stderr hash re-hashes; PDFs = manifest = RELEASE.json (if filled in).
"""
import hashlib, json, sys, datetime
from pathlib import Path
root, run_id = Path(sys.argv[1]), sys.argv[2]
zip_path = Path(sys.argv[3]) if len(sys.argv) > 3 else root / 'release/BFGS_paper_companion_sources.zip'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
findings = []
def need(ok, msg):
    if not ok: findings.append(msg)
manifest = json.loads((root / 'release/SOURCE_MANIFEST.json').read_text())
need(zip_path.stat().st_size == manifest['bytes'] and sha(zip_path) == manifest['sha256'], 'ZIP differs from SOURCE_MANIFEST')
summary_path = root / 'release/validation/runs' / run_id / 'SUMMARY.json'
summary = json.loads(summary_path.read_text())
need(summary['status'] == 'PASS', 'validation not PASS')
need(summary['source_commit'] == manifest['source_commit'] and summary['archive_sha256'] == manifest['sha256'], 'summary/manifest mismatch')
need(summary['manifest_sha256'] == sha(root / 'release/SOURCE_MANIFEST.json'), 'summary pins another SOURCE_MANIFEST')
rehashed = 0
for c in summary['commands']:
    need(c['exit_code'] == 0, 'nonzero exit: ' + ' '.join(map(str, c['command']))[:80])
    for s in ('stdout', 'stderr'):
        need(sha(root / c[s]) == c[s + '_sha256'], 'changed log ' + c[s]); rehashed += 1
need(sha(root / 'release/validation/runs' / run_id / 'commands.json') == summary['commands_sha256'], 'commands.json hash')
pdfs = {}
for name, rec in manifest['pdfs'].items():
    p = root / 'release' / name
    need(p.stat().st_size == rec['bytes'] and sha(p) == rec['sha256'], 'PDF differs: ' + name)
    pdfs[name] = rec
release = json.loads((root / 'release/RELEASE.json').read_text())
need(all(release['pdfs'][n] == r for n, r in pdfs.items()), 'RELEASE.json pdfs differ')
print(json.dumps({'status': 'PASS' if not findings else 'FAIL', 'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope': 'Read-only receipt consistency and byte identity review; not a new build or Lean run.',
    'source_commit': manifest['source_commit'], 'archive_sha256': manifest['sha256'], 'archive_bytes': manifest['bytes'],
    'archive_members': manifest['members'], 'source_manifest_sha256': sha(root / 'release/SOURCE_MANIFEST.json'),
    'validation_summary': str(summary_path.relative_to(root)), 'validation_sha256': sha(summary_path),
    'actual_commands': len(summary['commands']), 'command_outputs_rehashed': rehashed, 'pdfs': pdfs,
    'all_pages_reproduced': sum(d['pages'] for d in summary['documents']),
    'fresh_supplement_summary_hashes_verified': sum(1 for r in summary.get('fresh_supplemental_audits', []) if sha(root / r['summary']) == r['summary_sha256']),
    'unresolved_findings': findings}, indent=2))
