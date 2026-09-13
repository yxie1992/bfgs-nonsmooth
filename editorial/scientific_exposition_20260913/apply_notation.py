#!/usr/bin/env python3
"""One-time, scoped notation migration; formal declaration names are unchanged."""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parents[2]
files=['paper/sections/energy.tex','paper/sections/local.tex','paper/sections/failure.tex','paper/appendices/seed_certificate.tex','paper/appendices/lower_curvature.tex','paper/statements/negative_upper.tex','paper/statements/negative_lower.tex']
record={}
for name in files:
 p=ROOT/name;s=p.read_text();old=s
 s=s.replace('M_k',r'\widehat B_k') if name.endswith(('energy.tex','local.tex')) else s
 if name.endswith('energy.tex'):
  s=re.sub(r'(?<![A-Za-z\\])c(?![A-Za-z_])',lambda m:r'\omega',s)
 if name.endswith(('failure.tex','lower_curvature.tex','negative_upper.tex','negative_lower.tex')):
  s=s.replace('p_n',r'\bar x_\ell')
  s=re.sub(r'(?<![A-Za-z\\])n(?![A-Za-z])',lambda m:r'\ell',s)
 if name.endswith(('failure.tex','lower_curvature.tex','seed_certificate.tex')):
  # The generic interval endpoints c,d are unrelated to the fixed seed pair.
  interval=None
  if name.endswith('seed_certificate.tex'):
   a=s.index('An interval $[a,b]$');b=s.index('For the query calculation',a)
   interval=s[a:b];s=s[:a]+'GENERICINTERVALPLACEHOLDER\n\n'+s[b:]
  for char in ['c','d']:
   s=re.sub(r'(?<![A-Za-z\\])'+char+r'(?![A-Za-z_])',lambda m:char+r'_\circ',s)
  s=s.replace('cu+dv',r'c_\circ u+d_\circ v')
  s=s.replace('panel (c_\\circ)','panel (c)')
  if interval:s=s.replace('GENERICINTERVALPLACEHOLDER\n\n',interval)
 if name.endswith('failure.tex'):
  s=s.replace('F(p+\\lambda z)',r'F(\bar x+\lambda z)')
  s=s.replace(r'\qquad z_2<2',r'\qquad [z]_2<2')
  s=s.replace('Here $z_2$ in the middle inequality denotes the second coordinate.\n','')
  start=s.index(' Earlier prescribed-orbit');end=s.index('to the true minimizer.',start)+len('to the true minimizer.')
  s=s[:start]+s[end:]
  s=s.replace('lower bracket $\\ell=0$',r'lower bracket $\alpha_{\rm lo}=0$').replace('upper bracket\n$h=+\\infty$',r'upper bracket'+ '\n'+r'$\alpha_{\rm hi}=+\infty$')
  s=s.replace('$h=\\alpha$',r'$\alpha_{\rm hi}=\alpha$').replace('$\\ell=\\alpha$',r'$\alpha_{\rm lo}=\alpha$')
  s=s.replace('$(\\ell+h)/2$ when $h<\\infty$, and $2\\ell$',r'$(\alpha_{\rm lo}+\alpha_{\rm hi})/2$ when $\alpha_{\rm hi}<\infty$, and $2\alpha_{\rm lo}$')
 if s!=old:p.write_text(s)
 record[name]={'before_sha256':hashlib.sha256(old.encode()).hexdigest(),'after_sha256':hashlib.sha256(s.encode()).hexdigest()}
(ROOT/'editorial/scientific_exposition_20260913/notation_migration.json').write_text(json.dumps(record,indent=2)+'\n')
