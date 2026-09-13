#!/usr/bin/env python3
"""Reproduce vector figures from the canonical seed and explicit schematics.

Fraction arithmetic preserves the stated rational-center coordinates until final
TikZ decimal output. These drawings are not certificate inputs and do not assert
stable-manifold membership. The fixed-objective scale layout is schematic.
"""
from pathlib import Path
from fractions import Fraction as Q
import json
import subprocess

ROOT = Path(__file__).resolve().parent
obj = json.loads((ROOT / 'seed_data.json').read_text())
c, d = map(Q, obj['root_center_rationals'])
rho = 129 * (c - 8*d) / ((16*c - 127*d - 16) * (127*c + 16*d + 129))

def add(a, b):
    return tuple(x + y for x, y in zip(a, b))

def mul(t, a):
    return tuple(t*x for x in a)

z0 = ((Q(897, 1024) - rho*(1-c))/(1-rho),
      (rho*d-Q(1, 64))/(1-rho))
s = [(-Q(1), Q(0)), (Q(127, 1024), Q(1, 64)), mul(rho, (1-c, -d))]
z = [z0, add(z0, s[0]), add(add(z0, s[0]), s[1]), mul(rho, z0)]
p = [s[0], mul(4, s[1]), mul(16, s[2])]

def xy(a):
    return '(' + ','.join(f'{float(x):.9f}' for x in a) + ')'

def length(alpha):
    return alpha if '/' not in alpha else r'\tfrac{' + alpha.split('/')[0] + '}{' + alpha.split('/')[1] + '}'

HEADER = [r'\documentclass[tikz,border=3pt]{standalone}',
          r'\usepackage[T1]{fontenc}', r'\usepackage{lmodern,amsmath}',
          r'\usetikzlibrary{arrows.meta,calc,patterns}',
          r'\begin{document}',
          r'\begin{tikzpicture}[>=Stealth,font=\small,',
          r'phase0/.style={solid},phase1/.style={densely dashed},',
          r'phase2/.style={dash pattern=on 4pt off 1.6pt on .7pt off 1.6pt}]']
END = [r'\end{tikzpicture}', r'\end{document}']

tex = HEADER + [
    r'\node[anchor=west] at (-.8,1.15) {(a) Accepted cycle};',
    r'\begin{scope}[x=4.6cm,y=22cm]',
    r'\draw[->,gray] (-.18,0)--(1.0,0) node[right] {$u$};',
    r'\draw[->,gray] (0,-.105)--(0,.028) node[above] {$v$};']
for j in range(3):
    tex.append(r'\draw[->,thick,phase' + str(j) + '] ' + xy(z[j]) + '--' + xy(z[j+1]) + ';')
for j, a in enumerate(z):
    pos = ['above', 'below left', 'right', 'above right'][j]
    tex.append(r'\draw[fill=white] ' + xy(a) + r' circle[radius=1.6pt] node[' + pos + '] {$z_' + str(j) + '$};')
tex += [r'\node[below] at (.48,-.084) {$\alpha=1$};',
        r'\draw[densely dotted,gray] (-.145,-.091) rectangle (.078,.012);',
        r'\node[anchor=west,font=\footnotesize] at (.12,.025) {detail in (c)};',
        r'\end{scope}',
        r'\node[font=\footnotesize] at (1.9,-2.65) {Vertical scale enlarged by $22/4.6$};',
        r'\node[anchor=west] at (6.0,1.15) {(b) All nine trial queries};',
        r'\begin{scope}[shift={(6.9cm,-2.02cm)},x=4.2cm,y=2.5cm]',
        r'\draw[->,gray] (-.20,0)--(1.02,0) node[right] {$u$};',
        r'\draw[->,gray] (0,-.12)--(0,1.0) node[above] {$v$};']
for j in range(3):
    tex.append(r'\draw[phase' + str(j) + ',black!70] ' + xy(z[j]) + '--' + xy(add(z[j],p[j])) + ';')
for row in obj['rows']:
    j, a = row['phase'], Q(row['alpha'])
    v = add(z[j], mul(a,p[j]))
    if row['accepted']:
        tex.append(r'\draw[fill=white] ' + xy(v) + r' circle[radius=1.7pt];')
    else:
        pos = 'below' if j == 1 else 'right'
        tex.append(r'\node[inner sep=0pt] at ' + xy(v) + r' {$\times$};')
        if j == 2 and a == Q(1, 8):
            tex.append(r'\draw[gray] ' + xy(v) + r'--(.27,.11);\node[right,font=\footnotesize,inner sep=1pt] at (.27,.11) {$\tfrac18$};')
        else:
            tex.append(r'\node[' + pos + r',font=\footnotesize,inner sep=2pt] at ' + xy(v) + ' {$' + length(row['alpha']) + '$};')
tex += [r'\fill ' + xy(z0) + r' circle[radius=1.5pt] node[below] {$z_0$};',
        r'\draw[densely dotted,gray] (-.145,-.091) rectangle (.078,.012);',
        r'\end{scope}',
        r'\node[anchor=west,font=\footnotesize] at (6.0,-2.82) {Rejected lengths labeled; accepted points: $\circ$};',
        r'\node[anchor=west] at (-.8,-3.50) {(c) Detail at the wrong corner};',
        r'\begin{scope}[shift={(2.35cm,-4.12cm)},x=21cm,y=23cm]',
        r'\draw[->,gray] (-.155,0)--(.093,0) node[right] {$u$};',
        r'\draw[->,gray] (0,-.105)--(0,.014) node[right] {$v$};',
        r'\begin{scope}', r'\clip (-.153,-.10) rectangle (.092,.014);']
for j in range(3):
    tex.append(r'\draw[->,thick,phase' + str(j) + '] ' + xy(z[j]) + '--' + xy(z[j+1]) + ';')
tex += [r'\end{scope}']
for j in range(1,4):
    pos = ['below left','below right','above right'][j-1]
    label = '$z_' + str(j) + '$'
    tex.append(r'\draw[fill=white] ' + xy(z[j]) + r' circle[radius=1.7pt] node[' + pos + '] {' + label + '};')
tex += [r'\node[above,fill=white,inner sep=1pt] at (-.060,-.074) {$\alpha=\tfrac14$};',
        r'\node[right,fill=white,inner sep=1pt] at (.035,-.037) {$\alpha=\tfrac1{16}$};',
        r'\node[below] at (.073,-.083) {$\alpha=1$};',
        r'\fill (0,0) circle[radius=1.4pt] node[above left] {$0$};',
        r'\end{scope}',
        r'\begin{scope}[shift={(6.0cm,-3.88cm)}]',
        r'\node[anchor=west] at (0,0) {Phase rays (same styles in all panels)};',
        r'\draw[phase0] (0,-.45)--(.85,-.45);\node[anchor=west] at (1,-.45) {phase $0$, accepted $\alpha=1$};',
        r'\draw[phase1] (0,-.95)--(.85,-.95);\node[anchor=west] at (1,-.95) {phase $1$, accepted $\alpha=1/4$};',
        r'\draw[phase2] (0,-1.45)--(.85,-1.45);\node[anchor=west] at (1,-1.45) {phase $2$, accepted $\alpha=1/16$};',
        r'\node[anchor=west,font=\footnotesize,align=left,text width=5.2cm] at (0,-2.2) {Closure: $z_3=\rho z_0$. Scales differ by panel; the origin is nonstationary.};',
        r'\end{scope}'] + END
(ROOT/'cycle_trials.tex').write_text('\n'.join(tex)+'\n')

# The locations, slab shapes, and magnification below are expressly schematic.
# The inset marks the same rational-center finite seed and two contracted copies.
tex = HEADER + [
    r'\node[anchor=west] at (0,3.6) {One fixed objective $F$: $\bar x_\ell\to x_*$};',
    r'\node[anchor=west] at (6.4,3.6) {Enlarged affine-model neighborhood};',
    r'\draw[gray] (.45,1.5)--(5.15,1.5);',
    r'\fill (.45,1.5) circle[radius=2pt] node[below=5pt] {$x_*=0$};',
    r'\node at (.95,1.5) {$\cdots$};']
for x, half, label in [('1.50','.16',r'\ell+2'),('2.60','.30',r'\ell+1'),('4.50','.56',r'\ell')]:
    x, half = Q(x), Q(half)
    tex.append(r'\draw[gray,fill=black!3] ' + xy((x-half,Q('1.5')-half)) + ' rectangle ' + xy((x+half,Q('1.5')+half)) + ';')
    tex.append(r'\fill ' + xy((x,Q('1.5'))) + r' circle[radius=1.6pt];')
    tex.append(r'\node[below] at ' + xy((x,Q('1.5')-half-Q('.1'))) + r' {$\bar x_{' + label + '}$};')
    tex.append(r'\draw[->,thick] ' + xy((x+half/2,Q('1.5')+half/3)) + '--' + xy((x,Q('1.5'))) + ';')
tex += [r'\draw[->] (4.45,.42)--(1.10,.42) node[midway,below] {bad starts arbitrarily near $x_*$};',
        r'\draw[densely dotted,gray] (3.94,2.06)--(6.4,3.15);',
        r'\draw[densely dotted,gray] (5.06,.94)--(6.4,.1);',
        r'\draw[fill=black!3] (6.4,.1) rectangle (11.85,3.15);',
        r'\draw[<->] (6.4,2.96)--(11.85,2.96) node[midway,below,inner sep=1pt] {model width $O(a_\ell)$};',
        r'\draw[fill=white,densely dotted] (8.05,.70) rectangle (10.1,2.53);',
        r'\begin{scope}[shift={(8.40cm,1.03cm)},x=1.52cm,y=1.40cm]']
for m in range(3):
    scale = rho**m
    for j in range(3):
        style = '->,>={Stealth[length=1.1mm,width=.8mm]},' if m == 0 else ''
        tex.append(r'\draw[' + style + 'phase' + str(j) + ',line width=.35pt] ' + xy(mul(scale,z[j])) + '--' + xy(mul(scale,z[j+1])) + ';')
    for row in obj['rows']:
        v = mul(scale,add(z[row['phase']],mul(Q(row['alpha']),p[row['phase']])))
        if row['accepted']:
            tex.append(r'\draw[fill=white] ' + xy(v) + r' circle[radius=' + ('.65' if m == 0 else '.25') + 'pt];')
        else:
            display_scale = float(scale)**0.5
            tex.append(r'\node[inner sep=0pt,font=\tiny,scale=' + f'{display_scale:.6f}' + '] at ' + xy(v) + r' {$\times$};')
tex += [r'\fill (0,0) circle[radius=1.6pt];',
        r'\node[below left] at (0,0) {$\bar x_\ell$};',
        r'\draw[fill=white] ' + xy(z0) + r' circle[radius=1.2pt] node[above right] {$x_0^{(\ell)}$};',
        r'\end{scope}',
        r'\draw[<->] (8.05,.54)--(10.1,.54) node[midway,below] {$O(a_\ell^2)$};',
        r'\node[anchor=north west,align=left,text width=5.3cm,font=\footnotesize] at (6.5,-.25) {All accepted and rejected queries fit inside. Their contraction copies accumulate at $\bar x_\ell$, not at $x_*$.};',
        r'\node[anchor=north west,font=\footnotesize,align=left,text width=5.3cm] at (0,-.25) {Schematic: locations and relative scales exaggerated. This panel concerns the $C^{2,1}$ embedding only.};'] + END
(ROOT/'shrinking_scales.tex').write_text('\n'.join(tex)+'\n')

build = ROOT/'build'
build.mkdir(exist_ok=True)
for stem in ['cycle_trials', 'shrinking_scales']:
    with (build/(stem+'_build.log')).open('w') as log:
        subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',
                        '-output-directory=build',stem+'.tex'],cwd=ROOT,
                       stdout=log,stderr=subprocess.STDOUT,check=True)
    (ROOT/(stem+'.pdf')).write_bytes((build/(stem+'.pdf')).read_bytes())
print('Rendered cycle_trials.pdf and shrinking_scales.pdf; drawing only, not proof inputs.')
