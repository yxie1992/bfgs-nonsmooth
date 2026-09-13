#!/usr/bin/env python3
"""Check the table's display bounds by the article's rational interval rules.

This is reproducible diagnostic arithmetic, not a premise imported into Lean.
The proof's finite certificate and sound interval rules remain in Appendix C.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent

def interval(a, b=None):
    return Q(a), Q(a if b is None else b)

def add(x, y):
    return x[0] + y[0], x[1] + y[1]

def neg(x):
    return -x[1], -x[0]

def mul(x, y):
    products = [a*b for a in x for b in y]
    return min(products), max(products)

def inv(x):
    if x[0] <= 0 <= x[1]:
        raise ValueError('Interval reciprocal would cross zero')
    return 1/x[1], 1/x[0]

def require(condition, message):
    if not condition:
        raise ValueError(message)

def check():
    data = json.loads((ROOT/'seed_data.json').read_text())
    c, r = [tuple(map(Q, data['coarse_inputs'][k])) for k in ('c','rho')]
    # z0[0] = (897/1024 - rho*(1-c))/(1-rho), using the larger query box.
    numerator = add(interval('897/1024'), neg(mul(r, add(interval(1), neg(c)))))
    denominator = add(interval(1), neg(r))
    first = mul(numerator, inv(denominator))
    accepted = [row for row in data['rows'] if row['accepted']]
    phase = [first] + [tuple(map(Q,row['value_interval'])) for row in accepted[:2]]
    outer = [(8884,8885),(1218,1219),(723,724)]
    for j, (low, high) in enumerate(outer):
        require(Q(low,10000) < phase[j][0] <= phase[j][1] < Q(high,10000),
                f'Current phase {j} bound failed')
    rows=[]
    for row in data['rows']:
        value = tuple(map(Q,row['value_interval']))
        low, high = row['value_outer_1e4']
        require(Q(low,10000) < value[0] <= value[1] < Q(high,10000),
                'Existing trial bound failed')
        if row['accepted']:
            require(Q(row['decision_margin'][0]) > 0 and
                    Q(row['descent'][0]) > 0 and
                    Q(row['new_gradient_step'][0]) > 0,
                    'Existing acceptance margins failed')
        else:
            require(value[0] > phase[row['phase']][1],
                    'Rejected value does not exceed current upper bound')
        rows.append({'phase':row['phase'],'alpha':row['alpha'],
                     'trial_outer_1e4':row['value_outer_1e4'],
                     'active':row['active'],'accepted':row['accepted']})
    return {'status':'PASS','arithmetic':'fractions.Fraction; sound interval formulas from Appendix C',
            'source':'paper/figures/seed_data.json',
            'current_exact_intervals':[[str(v) for v in pair] for pair in phase],
            'current_outer_1e4':outer,'trial_rows_unchanged':rows,
            'scope':'Read-only display/certificate diagnostic; not a mathematical axiom or Lean proof input.'}

if __name__ == '__main__':
    print(json.dumps(check(),indent=2))
