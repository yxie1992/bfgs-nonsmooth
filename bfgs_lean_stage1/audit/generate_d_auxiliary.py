#!/usr/bin/env python3
from pathlib import Path
P=Path(__file__).resolve().parent
s=(P/'generate_d_displays.py').read_text();exec(s[:s.index('r=129*')])
r=129*(c-8*d)/((16*c-127*d-16)*(127*c+16*d+129));u=(Q(897,1024)-r*(1-c))/(1-r);v=(r*d-Q(1,64))/(1-r)
x4=u-Q(897,1024)+16*r*(1-c);y4=v+Q(1,64)-16*r*d
A=127*c+16*d+129;U=127*c+16*d
vv0=-(d+Q(1,8));vv1=c+1
vg=vv0*c+vv1*d;vy=vv0*(1-c)-vv1*d
wg=127*c+16*d;wy=127*(1-c)-16*d
curv=-Q(1,16)*(ee(16512)/(A*A))*vy*vg-Q(1,16)*(ee(1)/(1024*A))*wy*wg
exprs=[('initial_square',u*u+v*v),('trial_four_square',x4*x4+y4*y4),('last_curvature',curv)]
p=Proof();ans=[p.build(e) for _,e in exprs]
out=['''import DDisplayRaw
noncomputable section
namespace BfgsVerification.DAuxiliaryRaw
open IntervalBounds
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
''']
for (name,e) in exprs:out += [f'def {name} (c d : ℝ) : ℝ := {e.lean()}\n']
out += ['theorem bounds {c d : ℝ}',f'    (hc : Bounds {rat(bounds["c"][0])} c {rat(bounds["c"][1])})',f'    (hd : Bounds {rat(bounds["d"][0])} d {rat(bounds["d"][1])}) :',
 '    initial_square c d < 1 ∧ 1 < trial_four_square c d ∧ (1/100 : ℝ) < last_curvature c d := by']
out += p.lines
b0,lo0,hi0=ans[0];b1,lo1,hi1=ans[1];b2,lo2,hi2=ans[2]
assert hi0<1<lo1 and Q(1,100)<lo2
out += ['  refine ⟨?_,?_,?_⟩',f'  · exact lt_of_le_of_lt {b0}.2 (by norm_num)',f'  · exact lt_of_lt_of_le (by norm_num) {b1}.1',f'  · exact lt_of_lt_of_le (by norm_num) {b2}.1','','end BfgsVerification.DAuxiliaryRaw','']
write_or_check(P/'DAuxiliaryRaw.lean','\n'.join(out))
print('Generated candidate bounds; actual Lean verification pending.')
for (name,e),(_,lo,hi) in zip(exprs,ans):print(name, float(lo),float(hi))
