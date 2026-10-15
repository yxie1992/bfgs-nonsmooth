#!/usr/bin/env python3
"""Write per-chapter hints for the companion coverage from the claim ledger.

For each companion chapter, `hints/<stem>.json` lists the ledger records located in
it (source span, kind, labels, line, anchor, classification, review note) with the
span's Lean exports. An export list names the library theorems written for the
span; it is a superset of what any single item needs. The output is derived data
(git-ignored); rerun this script after `editorial/CLAIM_LEDGER.json` changes.
"""
import collections
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent / 'hints'
SECTIONS = ['companion_theorem_records', 'companion_inline_result_records',
            'companion_unnamed_mathematical_records', 'companion_source_span_records',
            'companion_frontmatter_deductions']


def main():
    ledger = json.loads((ROOT / 'editorial/CLAIM_LEDGER.json').read_text())
    out = collections.defaultdict(list)
    for key in SECTIONS:
        for r in ledger[key]:
            loc = r.get('location')
            path = loc['path'] if isinstance(loc, dict) else str(loc)
            line = loc.get('line') if isinstance(loc, dict) else None
            out[Path(path).stem].append({
                'ledger_section': key, 'id': r['id'], 'kind': r.get('kind'),
                'labels': r.get('labels'), 'title': r.get('title'), 'line': line,
                'companion_source_range': r.get('companion_source_range'),
                'anchor': r.get('anchor'),
                'source_classification': r.get('source_classification'),
                'source_review_note': r.get('source_review_note'),
                'lean': r.get('full_formal_exports') or r.get('principal_exports')})
    OUT.mkdir(exist_ok=True)
    for stem, records in sorted(out.items()):
        records.sort(key=lambda r: r['line'] or 0)
        (OUT / f'{stem}.json').write_text(json.dumps(records, indent=1, ensure_ascii=False))
        print(f'{stem}: {len(records)} records, '
              f'{sum(len(r["lean"] or []) for r in records)} export names')


if __name__ == '__main__':
    main()
