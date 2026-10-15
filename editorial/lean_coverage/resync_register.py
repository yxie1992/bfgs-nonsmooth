#!/usr/bin/env python3
"""Carry the coverage register of a TeX file across an edit of that file.

A correction of the article or the companion shifts the line numbers of the
register items, of the docstring references "Item `id` (`file:a-b`)" in the
file's coverage module, and of other references to the file. For each TeX file
this compares a committed version (--base, default HEAD) with the working tree
and
  * moves the lines of every prose item through the line mapping of the edit,
    and checks that its anchor is still inside its lines;
  * takes the lines of the mechanical items from extract_items.py, and reports
    the items whose source changed (sha256) and the ids that now name another
    item (an inserted or removed unlabelled display renumbers the later ones);
  * lists the items that overlap an edited line: check their claim, anchor and
    status by hand;
  * rewrites the docstring references of the coverage module to the register's
    lines, and moves the other references to the file (`file:a-b`, with the
    full path anywhere in the article package's Lean files and in the notes,
    reasons and open discrepancies of every register, with the bare file name
    also in the same document's coverage modules and registers) through the line
    mapping.
Without --write it only reports. --accept ID (repeatable) records the new
sha256 of a mechanical item whose changed source has been reviewed. Resolved
discrepancies (key resolved_discrepancies) keep the lines of their time.
--write refuses to run when the document's registers or the package's Lean
files differ from the base, since a second run would move the references again
(--force overrides): run it once, right after editing the TeX files, then
change statuses, anchors and docstrings by hand. For a further edit before the
first one is committed, --snapshot DIR saves the TeX files as written; a later
run with --base-dir DIR compares against that copy instead of a commit.

Usage:
    python3 editorial/lean_coverage/resync_register.py [--write [--force]] [--base REV | --base-dir DIR]
        [--snapshot DIR] [--accept ID ...] TEX_FILE ...
"""
from pathlib import Path
import argparse, bisect, difflib, json, re, subprocess, sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import extract_items as ex
import check_coverage as cc

ROOT = ex.ROOT
LEAN = ROOT / 'bfgs_lean_article' / 'BfgsArticle'


def committed(path, rev, base_dir=None):
    if base_dir:
        return (Path(base_dir) / path).read_text()
    return subprocess.run(['git', 'show', f'{rev}:{path}'], cwd=ROOT, capture_output=True, text=True,
                          check=True).stdout


def line_maps(old, new):
    """Maps of old line numbers to new ones for the first and the last line of a range,
    and the set of old lines (and gaps between old lines, as k + 0.5) that the edit touches."""
    a, b = old.split('\n'), new.split('\n')
    start, end, touched = {}, {}, set()
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == 'equal':
            for k in range(i2 - i1):
                start[i1 + k + 1] = end[i1 + k + 1] = j1 + k + 1
            continue
        if tag == 'insert':
            touched.add(i1 + 0.5)
            continue
        n, m = i2 - i1, j2 - j1
        for k in range(n):
            touched.add(i1 + k + 1)
            if m == 0:
                start[i1 + k + 1], end[i1 + k + 1] = j1 + 1, j1
            else:
                start[i1 + k + 1] = j1 + 1 + (k * m) // n
                end[i1 + k + 1] = j1 + -(-(k + 1) * m // n)
    return start, end, touched


def overlaps(lines, touched):
    first, last = lines
    return any(first <= t <= last for t in touched)


def anchor_lines(text, anchor):
    """Line numbers where the whitespace-normalized anchor starts in text."""
    words = [(m.group(0), m.start()) for m in re.finditer(r'\S+', text)]
    joined, offsets = '', []
    for word, _ in words:
        offsets.append(len(joined))
        joined += word + ' '
    target, found = ' '.join(anchor.split()), []
    i = joined.find(target) if target else -1
    while i >= 0:
        found.append(text.count('\n', 0, words[bisect.bisect_right(offsets, i) - 1][1]) + 1)
        i = joined.find(target, i + 1)
    return found


class Mapper:
    """Moves references `file:a-b` to one TeX file through the line mapping of its edit."""

    def __init__(self, path, start, end, touched):
        self.path, self.start, self.end, self.touched = path, start, end, touched
        lead = r'(?<![\w./-])'
        self.full = re.compile(lead + re.escape(path) + r':(\d+)(?:([-–])(\d+))?')
        self.any = re.compile(lead + r'(?:' + re.escape(path) + '|' + re.escape(Path(path).name) +
                              r'):(\d+)(?:([-–])(\d+))?')
        self.report = []

    def spans(self, text, bare):
        return list((self.any if bare else self.full).finditer(text))

    def moved(self, match, where):
        a = int(match.group(1))
        b = int(match.group(3)) if match.group(3) else a
        first, last = self.start.get(a), self.end.get(b)
        if first is None or last is None or last < first:
            self.report.append(f'LOSTREF {where} cites {match.group(0)}: lines deleted, fix it by hand')
            return None
        if overlaps([a, b], self.touched):
            self.report.append(f'EDITREF {where} cites {match.group(0)}, an edited range: check it')
        if (first, last) == (a, b):
            return None
        name = match.group(0)[:match.group(0).index(':')]
        return f'{name}:{first}' if not match.group(3) else f'{name}:{first}{match.group(2)}{last}'

    def apply(self, text, bare, where, fixed=()):
        """text with every reference moved, and the number of changed references;
        fixed = [(begin, end, replacement)] takes precedence over the line mapping."""
        edits = [(b, e, new) for b, e, new in fixed if text[b:e] != new]
        for match in self.spans(text, bare):
            if any(match.start() < e and b < match.end() for b, e, _ in fixed):
                continue
            new = self.moved(match, where)
            if new is not None:
                edits.append((match.start(), match.end(), new))
        for begin, finish, new in sorted(edits, reverse=True):
            text = text[:begin] + new + text[finish:]
        return text, len(edits)


def item_ref_edits(text, path, listed):
    """Replacements that set the file references of the docstrings to the register's lines
    (unchanged ones included, so that the line mapping leaves them alone)."""
    edits = []
    for m in cc.ITEM_REF.finditer(text):
        window = text[m.end():m.end() + 240]
        for stop in (cc.ITEM_REF.search(window), re.search(r'-/', window)):
            if stop:
                window = window[:stop.start()]
        ref = cc.FILE_REF.search(window)
        if not ref or ref.group(1) != path or m.group(1) not in listed:
            continue
        lines = listed[m.group(1)]['lines']
        begin, finish = m.end() + ref.start(2), m.end() + ref.end(3 if ref.group(3) else 2)
        dash = window[ref.end(2):ref.start(3)] if ref.group(3) else '-'
        edits.append((begin, finish, f'{lines[0]}' if lines[0] == lines[1] else f'{lines[0]}{dash}{lines[1]}'))
    return edits


def resync(path, base, accept, write, base_dir=None):
    article = path.startswith('paper/')
    register_file = ex.register_path(path)
    register = json.loads(register_file.read_text())
    old, new = committed(path, base, base_dir), (ROOT / path).read_text()
    if base_dir:
        base = base_dir
    start, end, touched = line_maps(old, new)
    mapper = Mapper(path, start, end, touched)
    old_items = {item['id']: item for item in ex.items_of(path, old)}
    new_items = {item['id']: item for item in ex.items_of(path, new)}
    report, moved_items = [], 0
    for item_id, item in old_items.items():
        expected = start.get(item['lines'][0])
        moved = new_items.get(item_id)
        if moved is None:
            report.append(f'GONE    {item_id} (was {path}:{item["lines"][0]})')
        elif expected is not None and moved['lines'][0] != expected and item['sha256'] != moved['sha256']:
            report.append(f'ID?     {item_id} now names the item at line {moved["lines"][0]} '
                          f'(expected near {expected}): check for renumbering')
    for item_id in new_items.keys() - old_items.keys():
        report.append(f'NEW     {item_id} at {path}:{new_items[item_id]["lines"][0]}: classify it')
    for item in register['items']:
        old_lines = item.get('lines')
        if not old_lines:
            continue
        new_lines = old_lines
        if item['kind'] != 'prose':
            moved = new_items.get(item['id'])
            if moved is None:
                continue
            new_lines = moved['lines']
            if moved['sha256'] != item.get('sha256'):
                if item['id'] in accept:
                    for key in ('labels', 'title', 'container', 'sha256'):
                        item[key] = moved[key]
                    report.append(f'ACCEPT  {item["id"]}: new sha256 {moved["sha256"]} recorded')
                else:
                    report.append(f'CHANGED {item["id"]} ({path}:{new_lines[0]}-{new_lines[1]}): '
                                  f'review it, then pass --accept {item["id"]}')
            elif item.get('container') != moved['container']:
                item['container'] = moved['container']
            if overlaps(old_lines, touched):
                report.append(f'EDITED  {item["id"]} ({item.get("status")}) {path}:{old_lines[0]}-{old_lines[1]} '
                              f'-> {new_lines[0]}-{new_lines[1]}')
        else:
            first, last = start.get(old_lines[0]), end.get(old_lines[1])
            if first is None or last is None or last < first:
                report.append(f'LOST    {item["id"]} (was {path}:{old_lines[0]}-{old_lines[1]}): set its lines by hand')
                continue
            new_lines = [first, last]
            region = '\n'.join(new.split('\n')[first - 1:last])
            if not anchor_lines(region, item.get('anchor', '')):
                where = anchor_lines(new, item.get('anchor', ''))
                report.append(f'ANCHOR  {item["id"]}: anchor not in {path}:{first}-{last}'
                              + (f' (found at line {", ".join(map(str, where))})' if where else ' (nor anywhere else)'))
            if overlaps(old_lines, touched):
                report.append(f'EDITED  {item["id"]} ({item.get("status")}) {path}:{old_lines[0]}-{old_lines[1]} '
                              f'-> {first}-{last}: check claim, anchor and status')
        if new_lines != old_lines:
            moved_items += 1
            item['lines'] = new_lines
    # Notes, reasons and open discrepancies of the registers (bare file names: same document only).
    registers = {register_file: register}
    for other in sorted(ex.REGISTER.glob('[AC]_*.json')):
        registers.setdefault(other, json.loads(other.read_text()))
    note_edits = 0
    for target, data in registers.items():
        bare = target.name.startswith('A_' if article else 'C_')
        for record in data['items'] + data.get('discrepancies', []):
            for key in ('note', 'reason', 'description'):
                if isinstance(record.get(key), str):
                    record[key], count = mapper.apply(record[key], bare,
                                                      f'{target.name} {record.get("id") or record.get("item")}')
                    note_edits += count
    # Lean files: the coverage module's docstring references, and other references.
    module = cc.module_file(register['lean_module']) if register.get('lean_module') else None
    lean_edits = {}
    listed = {item['id']: item for item in register['items']}
    same_document = LEAN / 'Coverage' / ('Article' if article else 'Companion')
    for lean in sorted(LEAN.rglob('*.lean')) + [LEAN.parent / 'BfgsArticle.lean']:
        if not lean.exists():
            continue
        text = lean.read_text()
        fixed = item_ref_edits(text, path, listed) if lean == module else []
        result, count = mapper.apply(text, same_document in lean.parents, str(lean.relative_to(ROOT)), fixed)
        if count:
            lean_edits[lean] = (result, count)
    print(f'== {path} (base {base}): {moved_items} items moved, {note_edits} references in register notes moved, '
          f'{sum(c for _, c in lean_edits.values())} references in {len(lean_edits)} Lean files moved')
    for line in report + mapper.report:
        print(line)
    if write:
        for target, data in registers.items():
            text = json.dumps(data, indent=1, ensure_ascii=False) + '\n'
            if target.read_text() != text:
                target.write_text(text)
        for lean, (text, _) in lean_edits.items():
            lean.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('files', nargs='+')
    parser.add_argument('--base', default='HEAD')
    parser.add_argument('--accept', action='append', default=[])
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--force', action='store_true',
                        help='write even if registers or Lean files differ from the base')
    parser.add_argument('--base-dir', help='compare against the TeX files saved in this directory by --snapshot')
    parser.add_argument('--snapshot', help='after --write, save the TeX files to this directory')
    args = parser.parse_args()
    if args.write and not args.force and not args.base_dir:
        # A second run would move the references again: write only onto the base's registers
        # and Lean files, then edit statuses, anchors and docstrings by hand.
        paths = ['bfgs_lean_article/BfgsArticle', 'bfgs_lean_article/BfgsArticle.lean',
                 str(ex.REGISTER.relative_to(ROOT))]
        dirty = subprocess.run(['git', 'diff', '--name-only', args.base, '--', *paths], cwd=ROOT,
                               capture_output=True, text=True, check=True).stdout.split()
        if dirty:
            sys.exit('resync_register: these files differ from ' + args.base + ' (run --write before editing them '
                     'by hand, or pass --force):\n  ' + '\n  '.join(dirty))
    for path in args.files:
        resync(path, args.base, set(args.accept), args.write, args.base_dir)
    if args.write and args.snapshot:
        for path in args.files:
            target = Path(args.snapshot) / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text((ROOT / path).read_text())
        print('saved the TeX files to', args.snapshot)


if __name__ == '__main__':
    main()
