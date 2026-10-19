#!/usr/bin/env python3
"""Check that M44 has only changed comments in existing Lean files.

This lexical comparison is not compilation or kernel replay. It keeps string
literals, supports nested comments, and leaves term quotations/quoted identifiers
alone. Whitespace outside comments is retained, not normalized away.
"""
from pathlib import Path
import json
import re
import subprocess

ROOT = next(p for p in Path(__file__).resolve().parents
            if (p / 'editorial/lean_coverage/resync_register.py').is_file())
BASE = '66de81d3d80183effb245863cc4fd58792a29899'


def mask_comments(text):
    result = []
    cursor = 0
    i = 0
    while i < len(text):
        start = i
        if text.startswith('/-', i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            assert depth == 0, 'Unclosed comment'
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = end if end >= 0 else len(text)
        else:
            # Literals must not be interpreted as comment delimiters.
            raw = re.match(r'r(#+)?"', text[i:]) if text[i] == 'r' else None
            if raw and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")):
                stop = '"' + (raw.group(1) or '')
                end = text.find(stop, i + raw.end())
                assert end >= 0, 'Unclosed raw string'
                i = end + len(stop)
            elif text[i] == '"':
                i += 1
                while i < len(text):
                    if text[i] == '\\':
                        i += 2
                    elif text[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
                else:
                    raise AssertionError('Unclosed string')
            elif text[i] == '«':
                end = text.find('»', i + 1)
                assert end >= 0, 'Unclosed quoted identifier'
                i = end + 1
            elif text[i] == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")) \
                    and (char := re.match(r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'", text[i:])):
                i += char.end()
            else:
                i += 1
            continue
        result.append(text[cursor:start])
        result.append(' ' + '\n' * text[start:i].count('\n'))
        cursor = i
    return ''.join(result) + text[cursor:]


def main():
    names = subprocess.check_output(['git', 'diff', '--name-only', BASE, '--', 'bfgs_lean_article'],
                                    cwd=ROOT, text=True).splitlines()
    records = []
    for name in names:
        if not name.endswith('.lean'):
            continue
        old = subprocess.check_output(['git', 'show', f'{BASE}:{name}'], cwd=ROOT, text=True)
        new = (ROOT / name).read_text()
        records.append({'file': name, 'noncomment_text_identical': mask_comments(old) == mask_comments(new)})
    report = {'baseline_commit': BASE, 'scope': __doc__.strip(), 'files': records,
              'all_noncomment_text_identical': all(r['noncomment_text_identical'] for r in records)}
    out = Path(__file__).with_name('lean_comment_only.json')
    out.write_text(json.dumps(report, indent=1) + '\n')
    print('Changed Lean files:', len(records), '; code outside comments identical:', report['all_noncomment_text_identical'])
    for record in records:
        if not record['noncomment_text_identical']:
            print('CHECK:', record['file'])
    raise SystemExit(0 if report['all_noncomment_text_identical'] else 1)


if __name__ == '__main__':
    main()
