#!/usr/bin/env python3
"""Check the Lean coverage register of the article and the companion.

For every TeX file of the two documents this compares the register
(`register/<A|C>_<stem>.json`) with the items that `extract_items.py` finds,
validates every item's status and fields, resolves cross-references, and checks
that every cited Lean name is declared (textually: in a coverage module, in this
package, in an article supplement, or in the main library's declaration index).
The axiom audit (`bfgs_lean_article/scripts/axiom_audit.py`) separately checks
with Lean that every cited name exists and uses only the standard axioms.

Usage:
    python3 editorial/lean_coverage/check_coverage.py [--strict [--allow-discrepancies]] [TEX_FILE ...]
With --strict the exit code is 1 unless every item has a final status and no
problem is found. A DISCREPANCY stays open until the manuscript is corrected;
--allow-discrepancies accepts recorded discrepancies as final.
"""
from pathlib import Path
import json, re, sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import extract_items as ex

ROOT = ex.ROOT
STATUSES = {
    'LEAN': 'a coverage theorem states the claim (field lean; the first name is in the coverage module)',
    'DEFINITION': 'defines notation or an object (field lean: the Lean definitions, plus unfolding theorems)',
    'PART_OF': 'part of the statement of another item (field of)',
    'PROOF': 'a proof; its result is item `of`, whose Lean theorem is proved',
    'SAME_AS': 'restates or weakens another item (field of)',
    'OPEN': 'an open question (field lean: a Lean Prop stated without proof)',
    'NON_CLAIM': 'not a mathematical claim (field reason)',
    'DISCREPANCY': 'the claim as written is false or not provable as stated (see discrepancies)',
    'TODO': 'not yet covered (field reason)',
}
FINAL = {'LEAN', 'DEFINITION', 'PART_OF', 'PROOF', 'SAME_AS', 'OPEN', 'NON_CLAIM'}
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  r'(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([^\s:({\[]+)', re.M)


def lean_declarations(path):
    """Fully qualified names declared in a Lean file (textual approximation)."""
    names, stack = set(), []
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if m := re.match(r'namespace\s+(\S+)', line):
            stack.append(m.group(1))
        elif m := re.match(r'end(?:\s+(\S+))?\s*$', line):
            if stack and (m.group(1) is None or m.group(1) == stack[-1] or stack[-1].endswith('.' + (m.group(1) or ''))):
                stack.pop()
        elif m := DECL.match(line):
            name = m.group(1).removeprefix('_root_.')
            names.add('.'.join(stack + [name]) if stack and not m.group(1).startswith('_root_.') else name)
    return names


ITEM_REF = re.compile(r'Items?\s+`([AC]/[^`]+)`')
FILE_REF = re.compile(r'\(`((?:paper|companion)/[^`:]+\.tex):(\d+)(?:[-–](\d+))?`\)')


def docstring_refs(path):
    """(item id, file, first line, last line) for each Item `id` ... (`file:a-b`) in a Lean file.

    The file reference must follow the item id within the same docstring, before any other item id."""
    text, refs = path.read_text(), []
    for m in ITEM_REF.finditer(text):
        window = text[m.end():m.end() + 240]
        for stop in (ITEM_REF.search(window), re.search(r'-/', window)):
            if stop:
                window = window[:stop.start()]
        if f := FILE_REF.search(window):
            refs.append((m.group(1), f.group(1), int(f.group(2)), int(f.group(3) or f.group(2))))
    return refs


def known_names():
    names = set(json.loads((ROOT / 'bfgs_lean_stage1/master_report/DECLARATION_INDEX.json').read_text()))
    sources = list((ROOT / 'bfgs_lean_article').glob('BfgsArticle/**/*.lean'))
    # The declaration index misses a few library declarations; read the sources too.
    sources += list((ROOT / 'bfgs_lean_stage1').glob('BfgsVerification/**/*.lean'))
    sources += [ROOT / p for p in ['editorial/narrative_rebuild/positive_formal/MixedBenchmark.lean',
                                   'editorial/satisfaction_review/branch_formal/ArticleBranchRegularity.lean',
                                   'editorial/article_formal/ArticleGeometry.lean',
                                   'editorial/article_formal/ConvexBalance.lean',
                                   'editorial/narrative_rebuild/negative_scaling.lean',
                                   'bfgs_lean_stage1/master_report/audit/sources/OriginalClaimInterpretation.lean']]
    for source in sources:
        names |= lean_declarations(source)
    return names


def module_file(module):
    return ROOT / 'bfgs_lean_article' / Path(*module.split('.')).with_suffix('.lean')


def check(files, strict, allow_discrepancies=False):
    registers, problems = {}, []
    for path in files:
        target = ex.register_path(path)
        if not target.exists():
            problems.append(f'{path}: no register file (register/{target.name})')
            continue
        registers[path] = json.loads(target.read_text())
    all_ids = set()
    for target in ex.REGISTER.glob('*.json'):
        all_ids |= {item['id'] for item in json.loads(target.read_text())['items']}
    names = known_names()
    summary = {}
    for path, register in registers.items():
        module = register.get('lean_module')
        module_names = lean_declarations(module_file(module)) if module and module_file(module).exists() else set()
        mechanical = {item['id']: item for item in ex.items_of(path)}
        listed = {item['id']: item for item in register['items']}
        if module and module_file(module).exists():
            for item_id, cited_file, first, last in docstring_refs(module_file(module)):
                if item_id not in listed:
                    problems.append(f'{module}: docstring cites unknown item {item_id}')
                elif cited_file != path or [first, last] != listed[item_id].get('lines'):
                    problems.append(f'{module}: docstring of {item_id} cites {cited_file}:{first}-{last}, '
                                    f'register has {path}:{listed[item_id].get("lines")}')
        for item_id, item in mechanical.items():
            if item_id not in listed:
                problems.append(f'{item_id}: missing from the register')
            elif listed[item_id].get('sha256') != item['sha256']:
                problems.append(f'{item_id}: source changed since classification (sha256)')
        for item in register['items']:
            item_id, status = item['id'], item.get('status')
            if item['kind'] != 'prose' and item_id not in mechanical:
                problems.append(f'{item_id}: not found in {path} any more')
            if item['kind'] == 'prose' and not (item.get('anchor') and item.get('lines')):
                problems.append(f'{item_id}: prose items need anchor and lines')
            counts = summary.setdefault(path, {})
            counts[status] = counts.get(status, 0) + 1
            if status is None:
                continue
            if status not in STATUSES:
                problems.append(f'{item_id}: unknown status {status}')
                continue
            cited = item.get('lean') or []
            for name in cited:
                if name not in names and name not in module_names:
                    problems.append(f'{item_id}: unknown Lean name {name}')
            if status in {'LEAN', 'DEFINITION', 'OPEN'}:
                if not cited:
                    problems.append(f'{item_id}: status {status} needs lean names')
                if status == 'LEAN' and cited and cited[0] not in module_names:
                    problems.append(f'{item_id}: first lean name must be declared in {module}')
            if status in {'PART_OF', 'PROOF', 'SAME_AS'}:
                targets = item.get('of') if isinstance(item.get('of'), list) else [item.get('of')]
                if not targets or any(t not in all_ids for t in targets) or (status != 'SAME_AS' and len(targets) > 1):
                    problems.append(f'{item_id}: status {status} needs existing item id(s) in field of')
            if status in {'NON_CLAIM', 'TODO'} and not item.get('reason'):
                problems.append(f'{item_id}: status {status} needs a reason')
            if status == 'DISCREPANCY' and not any(d.get('item') == item_id for d in register.get('discrepancies', [])):
                problems.append(f'{item_id}: status DISCREPANCY needs an entry in discrepancies')
    for path, counts in summary.items():
        print(f'{path}: ' + ', '.join(f'{k or "unclassified"} {v}' for k, v in sorted(counts.items(), key=lambda t: str(t[0]))))
    totals = {}
    for counts in summary.values():
        for k, v in counts.items():
            totals[k] = totals.get(k, 0) + v
    print('TOTAL: ' + ', '.join(f'{k or "unclassified"} {v}' for k, v in sorted(totals.items(), key=lambda t: str(t[0]))))
    for register in registers.values():
        for d in register.get('discrepancies', []):
            print(f"DISCREPANCY {d.get('item')}: {d.get('description')}")
    for p in problems:
        print('PROBLEM', p)
    unfinished = sum(v for k, v in totals.items() if k not in FINAL and not (allow_discrepancies and k == 'DISCREPANCY'))
    return 1 if strict and (problems or unfinished) else 0


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    files = args or (ex.ARTICLE + ex.COMPANION)
    sys.exit(check(files, '--strict' in sys.argv, '--allow-discrepancies' in sys.argv))


if __name__ == '__main__':
    main()
