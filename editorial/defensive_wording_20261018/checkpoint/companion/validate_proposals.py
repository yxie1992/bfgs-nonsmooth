#!/usr/bin/env python3
"""Check M44 companion proposals against the generated chapters (read-only).

Usage:
    python3 validate_proposals.py PROPOSALS.json [PROPOSALS.json ...] [--render DIR]

For every proposal {id, file, kind, old, new, reason}:
  * file is a generated chapter companion/chapters/NN_X.tex;
  * old occurs exactly once in the file, does not start on lines 1-3 (the
    chapter introduction), contains no SOURCE marker and does not overlap the
    passages the coordinator handles;
  * old must not overlap a theorem-like statement, a display or a manual
    result heading (ERROR); overlapping a proof, figure or table is reported
    as a NOTE (the item's hash changes; the coordinator re-accepts it);
  * proposals of one file must not overlap; they are applied in sequence;
  * the coverage-register prose items whose anchor overlaps old, and the item
    whose claim probably contains old (the nearest anchor before it in the same
    paragraph), are listed with their status.
With --render DIR the edited chapters (proposals without errors only) are
written to DIR (same file names) for `diff -u companion/chapters/NN_X.tex DIR/NN_X.tex`.
Exit status 1 if any ERROR is found. Never writes into the repository.
"""
import json, re, sys
from pathlib import Path

REPO = Path('/home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth')
sys.path.insert(0, str(REPO / 'editorial/lean_coverage'))
import extract_items as ex  # noqa: E402

KINDS = {'caveat', 'repeat', 'guard', 'positive'}
# Passages handled by the coordinator: (start text, end text or None).
COORDINATOR = [
    ('The following comparisons are bibliographic scholarship, separate from the formal theorem assertions.', None),
    ('Lewis--Overton~\\cite[Section~5.1]{LO} analyzes the scalar absolute-value model with its stated '
     'line-search conventions.', None),
    ('The Euclidean-norm theorem is a known case recovered here.', None),
    ('Existence of an infinite admissible run is a separate issue.', 'remains open here.'),
]
BLOCKING = ex.STATEMENTS  # theorem-like environments: never edited


def line_starts(text):
    starts = [0]
    for m in re.finditer('\n', text):
        starts.append(m.end())
    return starts


def mechanical_spans(path, text):
    """Mechanical items of a chapter with their spans in the original text."""
    stripped = ex.strip_comments(text)
    s_starts, o_starts = line_starts(stripped), line_starts(text)

    def orig(pos):
        line = stripped.count('\n', 0, pos)
        return o_starts[line] + pos - s_starts[line]

    spans, stack = [], []
    for m in ex.TOKEN.finditer(stripped):
        begin, end, token = m.group(1), m.group(2), m.group(0)
        if begin is not None or token == '\\[':
            kind = begin if begin is not None else 'display'
            if kind in ex.CONTAINERS or kind in ex.DISPLAYS or kind == 'display':
                stack.append((kind, m.start()))
            continue
        kind = end if end is not None else 'display'
        if not (kind in ex.CONTAINERS or kind in ex.DISPLAYS or kind == 'display'):
            continue
        env, start = stack.pop()
        spans.append({'environment': env, 'start': orig(start), 'end': orig(m.end())})
    for m in ex.HEADING.finditer(stripped):
        spans.append({'environment': 'heading', 'start': orig(m.start()), 'end': orig(m.end())})
    spans.sort(key=lambda r: r['start'])
    items = ex.items_of(path, text)
    assert len(items) == len(spans), (path, len(items), len(spans))
    for span, item in zip(spans, items):
        span['id'] = item['id']
        span['display'] = item['kind'] == 'display'
    return spans


def normalized(text):
    chars, index, space = [], [], False
    for i, ch in enumerate(text):
        if ch.isspace():
            if space:
                continue
            space = True
            chars.append(' ')
        else:
            space = False
            chars.append(ch)
        index.append(i)
    return ''.join(chars), index


def anchor_spans(text, register):
    norm, index = normalized(text)
    lines = lambda pos: text.count('\n', 0, pos) + 1
    found = []
    for item in register['items']:
        if item['kind'] != 'prose' or not item.get('anchor'):
            continue
        anchor = ' '.join(item['anchor'].split())
        hits = [m.start() for m in re.finditer(re.escape(anchor), norm)]
        if not hits:
            found.append((item, None, None))
            continue
        first, last = item['lines']
        best = min(hits, key=lambda k: 0 if first <= lines(index[k]) <= last else
                   min(abs(lines(index[k]) - first), abs(lines(index[k]) - last)) + 1)
        found.append((item, index[best], index[best + len(anchor) - 1] + 1))
    return found


def paragraph_of(text, pos):
    return len(re.findall(r'\n[ \t]*\n', text[:pos]))


def describe(item):
    status = item.get('status')
    extra = item.get('lean') or item.get('of') or item.get('reason') or ''
    if isinstance(extra, list):
        extra = ', '.join(extra)
    return f"{item['id']} [{status}] anchor \"{item['anchor'][:70]}\" ({str(extra)[:90]})"


def main():
    args = sys.argv[1:]
    render = None
    if '--render' in args:
        k = args.index('--render')
        render = Path(args[k + 1])
        del args[k:k + 2]
    proposals, errors = [], 0
    for name in args:
        data = json.loads(Path(name).read_text())
        proposals += data['proposals'] if isinstance(data, dict) else data
    by_file = {}
    seen_ids = set()
    for p in proposals:
        problems = []
        for key in ('id', 'file', 'kind', 'old', 'new', 'reason'):
            if key not in p:
                problems.append(f'missing field {key}')
        if problems:
            print(f"ERROR {p.get('id')}: " + '; '.join(problems))
            errors += 1
            continue
        if p['id'] in seen_ids:
            print(f"ERROR {p['id']}: duplicate id")
            errors += 1
        seen_ids.add(p['id'])
        by_file.setdefault(p['file'], []).append(p)
    for path, group in sorted(by_file.items()):
        if not re.fullmatch(r'companion/chapters/\d\d_[A-Z]\.tex', path):
            for p in group:
                print(f"ERROR {p['id']}: {path} is not a generated chapter")
            errors += len(group)
            continue
        text = (REPO / path).read_text()
        register = json.loads(ex.register_path(path).read_text())
        spans = mechanical_spans(path, text)
        anchors = anchor_spans(text, register)
        blocked = []
        for start_text, end_text in COORDINATOR:
            k = text.find(start_text)
            if k < 0:
                continue
            e = text.find(end_text, k) + len(end_text) if end_text else k + len(start_text)
            blocked.append((k, e, start_text[:50]))
        placed = []
        for p in group:
            old, new = p['old'], p['new']
            tag = f"{p['id']} ({path}"
            issues, notes = [], []
            if p['kind'] not in KINDS:
                issues.append(f"kind {p['kind']!r} not in {sorted(KINDS)}")
            count = text.count(old) if old else 0
            if count != 1:
                issues.append(f'old occurs {count} times (must be exactly once)')
                print(f"ERROR {tag}): " + '; '.join(issues))
                errors += 1
                continue
            s = text.index(old)
            e = s + len(old)
            line = text.count('\n', 0, s) + 1
            tag += f':{line})'
            if line <= 3:
                issues.append('starts in the chapter introduction (lines 1-3; coordinator)')
            if 'SOURCE_BEGIN' in old + new or 'SOURCE_END' in old + new:
                issues.append('touches a SOURCE marker')
            for b0, b1, what in blocked:
                if s < b1 and b0 < e:
                    issues.append(f'overlaps a coordinator passage ("{what}...")')
            for span in spans:
                if not (s < span['end'] and span['start'] < e):
                    continue
                inside = span['start'] <= s and e <= span['end']
                if span['environment'] in BLOCKING:
                    issues.append(f"overlaps statement {span['id']}")
                elif span['display'] or span['environment'] == 'heading':
                    issues.append(f"overlaps {span['environment']} {span['id']}")
                elif inside:
                    notes.append(f"inside {span['environment']} {span['id']} (hash changes)")
                else:
                    issues.append(f"crosses the boundary of {span['environment']} {span['id']}")
            for item, a0, a1 in anchors:
                if a0 is None or not (s < a1 and a0 < e):
                    continue
                survives = ' '.join(item['anchor'].split()) in ' '.join(
                    (text[:s] + new + text[e:])[max(0, a0 - 400):a1 + 400 + len(new)].split())
                notes.append(('anchor edited, survives: ' if survives else 'ANCHOR LOST (retire/re-anchor): ')
                             + describe(item))
            before = [(a0, item) for item, a0, a1 in anchors
                      if a0 is not None and a0 < s and paragraph_of(text, a0) == paragraph_of(text, s)]
            if before:
                notes.append('claim probably containing it: ' + describe(max(before, key=lambda t: t[0])[1]))
            for q0, q1, qid in placed:
                if s < q1 and q0 < e:
                    issues.append(f'overlaps proposal {qid}')
            placed.append((s, e, p['id']))
            if not issues:
                p['_span'] = (s, e)
            result = text[max(0, s - 1):s] + new + text[e:e + 1]
            if '  ' in result or ' \n' in result or ' .' in result or ' ,' in result:
                notes.append('check spacing at the edit boundary: ' + repr(result[:40] + '...' + result[-40:]))
            if issues:
                errors += 1
                print(f'ERROR {tag}: ' + '; '.join(issues))
            else:
                print(f"OK    {tag} [{p['kind']}]")
            for n in notes:
                print('      ' + n)
        if render:
            render.mkdir(parents=True, exist_ok=True)
            edited = text
            for p in sorted((p for p in group if '_span' in p), key=lambda p: -p['_span'][0]):
                s, e = p['_span']
                edited = edited[:s] + p['new'] + edited[e:]
            (render / Path(path).name).write_text(edited)
    print(f'{len(proposals)} proposals, {errors} with errors')
    sys.exit(1 if errors else 0)


if __name__ == '__main__':
    main()
