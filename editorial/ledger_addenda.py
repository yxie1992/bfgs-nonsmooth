"""Merge the October 2026 Lean-review ledger additions into the ledger records.

Reads editorial/lean_review_20261013/LEDGER_ADDITIONS.json and the article
package audit it names. Package declarations enter the declaration index with
their recorded signatures; listed exports are added to the named article
records (`additions`) and companion theorem records (`companion_additions`).
Nothing already in a record is removed or reordered.
"""
import json

STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
ADDITIONS = 'editorial/lean_review_20261013/LEDGER_ADDITIONS.json'


def apply(root, index, article, companion=()):
    additions = json.loads((root / ADDITIONS).read_text())
    audit_path = additions['package_audit']
    audit = json.loads((root / audit_path).read_text())
    assert audit['status'] == 'PASS', audit_path
    assert not audit['missing_or_unresolved'] and not audit['nonstandard_axioms'], audit_path
    package = set()
    for declaration in audit['package_declarations']:
        assert set(declaration['axioms']) <= STANDARD, declaration['name']
        assert declaration['name'] not in index, ('Package declaration shadows an indexed name', declaration['name'])
        index[declaration['name']] = declaration
        package.add(declaration['name'])
    records = {row['id']: row for row in article}
    for addition in additions['additions']:
        row = records[addition['id']]
        names = addition['principal_exports']
        assert all(name in index for name in names), addition['id']
        principal = row.setdefault('principal_exports', [])
        principal.extend(name for name in names if name not in principal)
        row['full_formal_exports'] = sorted(set(row['full_formal_exports']) | set(names))
        contracts = [audit_path] if package.intersection(names) else []
        if contracts and 'exact_contracts' in row and audit_path not in row['exact_contracts']:
            row['exact_contracts'].append(audit_path)
        row['formal_addenda'] = {'revision': additions['revision'], 'source': ADDITIONS,
                                 'principal_exports': names, 'exact_contracts': contracts,
                                 'note': addition['note']}
    companion_records = {row['id']: row for row in companion}
    for addition in additions.get('companion_additions', []):
        row = companion_records[addition['id']]
        names = addition['exports']
        assert all(name in index for name in names), addition['id']
        row['full_formal_exports'] = sorted(set(row['full_formal_exports']) | set(names))
        contracts = [audit_path] if package.intersection(names) else []
        row['formal_addenda'] = {'revision': additions['revision'], 'source': ADDITIONS,
                                 'exports': names, 'exact_contracts': contracts,
                                 'note': addition['note']}
