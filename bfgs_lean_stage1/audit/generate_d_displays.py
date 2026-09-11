#!/usr/bin/env python3
"""Candidate generation only: all arithmetic/semantic links are checked in Lean."""
from fractions import Fraction as Q
from dataclasses import dataclass
from pathlib import Path
import json,sys,re
HERE=Path(__file__).resolve().parent
def write_or_check(path,content):
 if path.suffix=='.lean':
  path=HERE.parent/'BfgsVerification'/path.name
  content=re.sub(r'^import (DDisplayRaw)$',r'import BfgsVerification.\1',content,flags=re.M)
 if path.name=='display_candidates.json':path=HERE/'d_display_candidates.json'
 if '--check' in sys.argv:
  assert path.read_bytes()==content.encode(), f'regeneration mismatch: {path.name}'
  print(f'PASS byte-identical regeneration: {path.name}')
 else:path.write_text(content)
@dataclass(frozen=True)
class E:
 op:str
 args:tuple
 def __add__(self,o):return E('+',(self,ee(o)))
 def __radd__(self,o):return ee(o)+self
 def __sub__(self,o):return E('-',(self,ee(o)))
 def __rsub__(self,o):return ee(o)-self
 def __mul__(self,o):return E('*',(self,ee(o)))
 def __rmul__(self,o):return ee(o)*self
 def __truediv__(self,o):return self*E('inv',(ee(o),))
 def __neg__(self):return E('neg',(self,))
 def lean(self):
  if self.op=='var':return self.args[0]
  if self.op=='const':return rat(self.args[0])
  if self.op=='neg':return f'(-{self.args[0].lean()})'
  if self.op=='inv':return f'({self.args[0].lean()})⁻¹'
  return f'({self.args[0].lean()}{self.op}{self.args[1].lean()})'
def ee(x):return x if isinstance(x,E) else E('const',(Q(x),))
def rat(q):
 q=Q(q)
 return f'({q.numerator}/{q.denominator} : ℝ)' if q.denominator!=1 else f'({q.numerator} : ℝ)'
def floorq(q):return q.numerator//q.denominator
def outward(a,b):
 M=10**45
 return Q(floorq(a*M),M),Q(-floorq(-b*M),M)
c,d=[E('var',(s,)) for s in ('c','d')]
bounds={'c':(Q('0.318481427627118630646451312501'),Q('0.318481427627118630646451312504')),
'd':(Q('-1.025232119675748725481350870015'),Q('-1.025232119675748725481350870012'))}
class Proof:
 def __init__(self):self.cache={};self.lines=[]
 def build(self,e):
  if e in self.cache:return self.cache[e]
  if e.op=='var':
   ans=('h'+e.args[0],*bounds[e.args[0]]);self.cache[e]=ans;return ans
  if e.op=='const':
   a=b=e.args[0];term=f'IntervalBounds.exact {rat(a)}'
  elif e.op in ('neg','inv'):
   x,a,b=self.build(e.args[0])
   if e.op=='neg':a,b=-b,-a;term=f'IntervalBounds.neg {x}'
   else:
    assert a>0,(e,a,b)
    a,b=1/b,1/a;term=f'IntervalBounds.inv_pos {x} (by norm_num)'
  else:
   x,a,b=self.build(e.args[0]);y,cc,dd=self.build(e.args[1])
   if e.op=='+':a,b=a+cc,b+dd;term=f'IntervalBounds.add {x} {y}'
   elif e.op=='-':a,b=a-dd,b-cc;term=f'IntervalBounds.sub {x} {y}'
   else:
    if a>=0 and cc>=0:rule='nn';a,b=a*cc,b*dd
    elif a>=0 and dd<=0:rule='np';a,b=b*cc,a*dd
    elif b<=0 and cc>=0:rule='pn';a,b=a*dd,b*cc
    elif b<=0 and dd<=0:rule='pp';a,b=b*dd,a*cc
    else:raise ValueError(('straddle',e,a,b,cc,dd))
    term=f'IntervalBounds.mul_{rule} {x} {y} (by norm_num) (by norm_num)'
  lo,hi=outward(a,b)
  name=f'b{len(self.cache)}'
  self.lines += [f'  have {name} : Bounds {rat(lo)} {e.lean()} {rat(hi)} := by',f'    have h := {term}',
  '    constructor <;> dsimp only [Bounds] at h ⊢ <;> norm_num at h ⊢ <;> linarith only [h.1,h.2]']
  ans=(name,lo,hi);self.cache[e]=ans;return ans
r=129*(c-8*d)/((16*c-127*d-16)*(127*c+16*d+129))
u=(Q(897,1024)-r*(1-c))/(1-r);v=(r*d-Q(1,64))/(1-r)
points=[(u,v),(u-1,v),(u-Q(897,1024),v+Q(1,64)),(r*u,r*v)]
dirs=[(ee(-1),ee(0)),(ee(Q(127,256)),ee(Q(1,16))),(16*r*(1-c),-16*r*d)]
grads=[(ee(1),ee(0)),(ee(-1),ee(Q(-1,8))),(c,d)]
def dot(g,x):return g[0]*x[0]+g[1]*x[1]
tests=[(0,Q(1),1),(1,Q(1),0),(1,Q(1,2),0),(1,Q(1,4),2),(2,Q(1),0),(2,Q(1,2),0),(2,Q(1,4),0),(2,Q(1,8),0),(2,Q(1,16),0)]
rows=[]
def row(name,expr,printed,lines,digits=12):rows.append(dict(name=name,expr=expr,printed=printed,lines=lines,digits=digits))
row('rho',r,'0.060199206107543764815373666287',[83,86],30)
pt=[['0.888432624149','-0.082297397686'],['-0.111567375851','-0.082297397686'],['0.012456061649','-0.066672397686'],['0.053482938654','-0.004954238006']]
for j in range(4):
 for i in range(2):row(f'point_{j}_{i}',points[j][i],pt[j][i],[138+j,138+j])
values=['0.121854550561','0.384526374149','0.136479499149','0.072321707900','0.668886093720','0.340671077685','0.176563569667','0.094509815658','0.053482938654']
for k,(j,a,act) in enumerate(tests):
 z=tuple(points[j][i]+a*dirs[j][i] for i in range(2))
 row(f'trial_value_{k}',dot(grads[act],z),values[k],[184+k,184+k])
for j,s in enumerate(['0.888432624149','0.121854550561','0.072321707900']):row(f'start_value_{j}',dot(grads[j],points[j]),s,[195,198])
ars=['0.766578073588','0.393190937094','0.375205963572'];wrs=['-1','-0.186383158092','-0.817119670486']
for j,a in enumerate([Q(1),Q(1,4),Q(1,16)]):
 step=tuple(a*v for v in dirs[j]);cur=dot(grads[j],points[j]);nxt=dot(grads[(j+1)%3],points[j+1]);pred=-dot(grads[j],step)
 row(f'armijo_ratio_{j}',(cur-nxt)/pred,ars[j],[204+j,204+j])
 row(f'wolfe_ratio_{j}',-dot(grads[(j+1)%3],step)/pred,wrs[j],[204+j,204+j])
for j,b in enumerate([ee(2),2*c-32*d]):
 center=(256*b-273)/(255*b);lower=Q(273,272)-Q(383,34816)*b;upper=Q(32513,2176)*b-Q(273,17)
 for key,e,s in zip(['center','lower','upper'],[center,lower,upper],
  [['0.468627450981','0.981675091912','13.824448529412'],['0.971910573260','0.635765118558','483.655089309488']][j]):row(f'plateau_{j}_{key}',e,s,[333+j,333+j])
N=len(rows);p=Proof();answers=[p.build(rw['expr']) for rw in rows]
header='''import BfgsVerification.AlgebraicSeedFiniteCycle
import BfgsVerification.DScalarRamp
/-! Generated candidates only. Every real interval operation is kernel checked. -/
noncomputable section
namespace BfgsVerification.DDisplayRaw
open IntervalBounds
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
'''
vec=lambda xs:'!['+',\n    '.join(xs)+']'
out=[header,f'def values (c d : ℝ) : Fin {N} → ℝ :=\n  '+vec([rw['expr'].lean() for rw in rows]),'',
f'def lower : Fin {N} → ℝ :=\n  '+vec([rat(a) for _,a,b in answers]),'',
f'def upper : Fin {N} → ℝ :=\n  '+vec([rat(b) for _,a,b in answers]),'',
'''theorem values_bounds {c d : ℝ}''',f'    (hc : Bounds {rat(bounds["c"][0])} c {rat(bounds["c"][1])})',
f'    (hd : Bounds {rat(bounds["d"][0])} d {rat(bounds["d"][1])}) :',f'    ∀ i : Fin {N}, Bounds (lower i) (values c d i) (upper i) := by']
out+=p.lines
out+=['  intro i','  fin_cases i']
for name,a,b in answers:out+=[f'  · exact {name}']
out+=['','end BfgsVerification.DDisplayRaw','']
write_or_check(HERE/'DDisplayRaw.lean','\n'.join(out))
meta=[]
for i,(rw,(_,lo,hi)) in enumerate(zip(rows,answers)):
 digits=rw['digits'];unit=Q(1,10**digits);near=Q(floorq((lo+hi)/2/unit+Q(1,2)),10**digits);old=Q(rw['printed'])
 meta.append(dict(lean_expr=rw['expr'].lean(),index=i,name=rw['name'],printed=rw['printed'],lines=rw['lines'],digits=digits,lower=str(lo),upper=str(hi),nearest=str(near),
 nearest_within_half=near-unit/2<lo and hi<near+unit/2,original_within_half=old-unit/2<lo and hi<old+unit/2,
 original_within_one=old-unit<lo and hi<old+unit))
write_or_check(HERE/'display_candidates.json',json.dumps(meta,indent=2)+'\n')
print(f'Generated {N} display quantities with {len(p.cache)} interval nodes; Lean proof pending.')
for m in meta:
 print(m['index'],m['name'],'half:',m['original_within_half'],'one:',m['original_within_one'],'candidate:',m['nearest'])
