#!/usr/bin/env python3
"""Publish the canonical seed proof inside both documents, adapting references."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
src=(ROOT/'paper/appendices/seed_certificate.tex').read_text()
# The companion's preserved construction uses c,d; the article separates
# these fixed seed coordinates from its analytical constants with circle aliases.
src=src.replace(r'c_\circ','c').replace(r'd_\circ','d')
# amsthm replaces the proof heading, whereas svjour3 adds its optional title.
src=src.replace(r'\begin{proof}[the algebraic part of ',
                r'\begin{proof}[Proof of the algebraic part of ')
src=re.sub(r'^\\section\{[^\n]+\}\n\\label\{art:seed_certificate\}\n','',src)
links={'art:seed_certificate':'comp:seed_certificate','art:seed_cycle':'D:root',
       'art:seed_rho':'D:rho','art:seed_matrices':'D:closure','art:failure_update':'D:bfgs',
       'art:seed_points':'D:x0','art:trial_table':'comp:trial_table',
       'art:seed_query_bounds':'D:trialbounds'}
for a,b in links.items():src=src.replace('{'+a+'}','{'+b+'}')
src=src.replace('Lemma~\\ref{D:root}','the seed and query assertions in Chapter~\\ref{comp:D}')
src=src.replace('\\subsection{','\\section{')
src=src.replace('art:','comp:')
out=ROOT/'companion/appendices';out.mkdir(exist_ok=True)
(out/'seed_certificate.tex').write_text('% Generated from the canonical article appendix; do not edit.\n'+src)
print('Prepared shared finite certificate appendix.')
