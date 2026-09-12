#!/usr/bin/env python3
"""Render canonical rational-center seed coordinates as a reproducible vector PDF.
Standard library arithmetic is for drawing only, not a formal proof input.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,subprocess
ROOT=Path(__file__).resolve().parent
obj=json.loads((ROOT/'seed_data.json').read_text())
c,d=map(Q,obj['root_center_rationals'])
rho=129*(c-8*d)/((16*c-127*d-16)*(127*c+16*d+129))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def mul(t,a):return tuple(t*x for x in a)
z0=((Q(897,1024)-rho*(1-c))/(1-rho),(rho*d-Q(1,64))/(1-rho))
s=[(-Q(1),Q(0)),(Q(127,1024),Q(1,64)),mul(rho,(1-c,-d))]
z=[z0,add(z0,s[0]),add(add(z0,s[0]),s[1]),mul(rho,z0)]
p=[s[0],mul(4,s[1]),mul(16,s[2])]
def xy(a):return '('+','.join(f'{float(x):.9f}' for x in a)+')'
tex=[r'\documentclass[tikz,border=3pt]{standalone}',r'\usepackage[T1]{fontenc}',r'\usepackage{lmodern,amsmath}',r'\usetikzlibrary{arrows.meta}',r'\begin{document}',r'\begin{tikzpicture}[>=Stealth,font=\small]',r'\begin{scope}[x=5.0cm,y=26cm]',r'\draw[->,gray] (-.18,0)--(1.0,0) node[below] {$u$};',r'\draw[->,gray] (0,-.10)--(0,.021) node[left] {$v$};']
for j in range(3):tex.append(r'\draw[->,thick] '+xy(z[j])+'--'+xy(z[j+1])+';')
for j,a in enumerate(z):
 label='$z_'+str(j)+'$' if j<3 else r'$z_3=\rho z_0$'
 pos=['above','below left','below','above right'][j]
 tex.append(r'\draw[fill=white] '+xy(a)+r' circle[radius=1.5pt] node['+pos+'] {'+label+'};')
tex.extend([r'\node[anchor=north] at (.40,-.108) {(a) Accepted cycle; vertical scale enlarged};',r'\end{scope}',r'\begin{scope}[shift={(7.1cm,-2.15cm)},x=4.8cm,y=2.9cm]',r'\draw[->,gray] (-.20,0)--(1.02,0) node[below] {$u$};',r'\draw[->,gray] (0,-.12)--(0,1.0) node[left] {$v$};'])
for j in [1,2]:tex.append(r'\draw[dashed,gray] '+xy(z[j])+'--'+xy(add(z[j],p[j]))+';')
for j in range(3):tex.append(r'\fill '+xy(z[j])+r' circle[radius=1.5pt];')
for row in obj['rows']:
 j=row['phase'];a=Q(row['alpha']);v=add(z[j],mul(a,p[j]))
 if row['accepted']:
  tex.append(r'\draw[fill=white] '+xy(v)+r' circle[radius=1.6pt];')
 else:
  pos='right' if j==2 else 'below right'
  tex.append(r'\node at '+xy(v)+r' {$\times$};\node['+pos+',font=\\scriptsize] at '+xy(v)+' {$'+row['alpha']+'$};')
tex.extend([r'\node[align=left,anchor=north west,font=\scriptsize] at (-.15,.98) {$\bullet$ Current point\\$\circ$ Accepted query\\$\times$ Armijo rejection};',r'\node[anchor=north] at (.39,-.22) {(b) All queries; rejected lengths labeled};',r'\end{scope}',r'\end{tikzpicture}',r'\end{document}'])
(ROOT/'cycle_trials.tex').write_text('\n'.join(tex)+'\n')
build=ROOT/'build';build.mkdir(exist_ok=True)
with (build/'figure_build.log').open('w') as log:
 subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory=build','cycle_trials.tex'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
(ROOT/'cycle_trials.pdf').write_bytes((build/'cycle_trials.pdf').read_bytes())
print('Rendered cycle_trials.pdf from stated rational center; vector drawing only.')
