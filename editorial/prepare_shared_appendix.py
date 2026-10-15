#!/usr/bin/env python3
"""Publish the canonical seed proof inside both documents, adapting references."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
src=(ROOT/'paper/appendices/seed_certificate.tex').read_text()
# The companion's preserved construction uses c,d; the article separates
# these fixed seed coordinates from its analytical constants with circle aliases.
src=src.replace(r'c_\circ','c').replace(r'd_\circ','d')
# Companion-only corrections from the October 2026 Lean coverage of the companion
# (TODO_MANUSCRIPT_REVIEW.md): the companion's appendix parts are sections, its trial
# table is the unnumbered table of a section of Chapter D and lists decimals, and
# its root lemma claims the thirty digits of D:rho; the article keeps its wording.
companion_only=[
 # M16 (a): the next subsection of the article is the next section here.
 ('the next\nsubsection','the next\nsection'),
 # W9: the companion calls the g_i gradients, not slopes.
 ('of the third slope','of the third gradient $g_2=(c,d)^T$'),
 # W6: the root lemma claims the thirty digits of D:rho (Lean:
 # Companion.SeedCertificate.root_certificate).
 ('In particular all divisions used below are valid.',
  'In particular all divisions used below are valid. The same interval rules on the root box give the thirty digits in \\eqref{art:seed_rho}.'),
 # M16 (b): comp:trial_table labels a section heading, not a table.
 ('Table~\\ref{art:trial_table}','the table in Section~\\ref{art:trial_table}'),
 # M15: the companion's table lists decimals; the interval operations give rational
 # enclosures of width at most 4e-4 (Lean: Companion.SeedCertificate.table_enclosure_widths).
 ('The same interval operations give the value enclosures in that table.',
  'For each trial value $G(z_j+\\alpha p_j)$ in the table of Section~\\ref{art:trial_table} and each current value $G(z_j)$ in the display after it, the same interval operations give a rational enclosure of width at most $4\\cdot10^{-4}$; the twelve-digit decimals there are explanatory.')]
for old,new in companion_only:
 assert src.count(old)==1,old
 src=src.replace(old,new)
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
