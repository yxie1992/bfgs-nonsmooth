#!/usr/bin/env python3
"""Emit rational interval proof candidates. Lean checks every real inequality.
No result of this program is used as an axiom or via native_decide.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
def rat(q):
    q=Q(q)
    return f'({q.numerator}/{q.denominator} : ℝ)' if q.denominator!=1 else f'({q.numerator} : ℝ)'
@dataclass(frozen=True)
class E:
    op:str
    args:tuple
    def __add__(self,o):return E('+',(self,as_e(o)))
    def __radd__(self,o):return as_e(o)+self
    def __sub__(self,o):return E('-',(self,as_e(o)))
    def __rsub__(self,o):return as_e(o)-self
    def __mul__(self,o):return E('*',(self,as_e(o)))
    def __rmul__(self,o):return as_e(o)*self
    def __truediv__(self,o):return self*E('inv',(as_e(o),))
    def __neg__(self):return E('neg',(self,))
    def lean(self):
        if self.op=='var':return self.args[0]
        if self.op=='const':return rat(self.args[0])
        if self.op=='neg':return f'(-{self.args[0].lean()})'
        if self.op=='inv':return f'({self.args[0].lean()})⁻¹'
        return f'({self.args[0].lean()}{self.op}{self.args[1].lean()})'
def as_e(x):return x if isinstance(x,E) else E('const',(Q(x),))
c,d,r=[E('var',(s,)) for s in ('c','d','r')]
bounds={'c':(Q('0.318481'),Q('0.318482')),'d':(Q('-1.025233'),Q('-1.025232')),'r':(Q('0.06019'),Q('0.06021'))}
class Proof:
    def __init__(self):self.cache={};self.lines=[]
    def build(self,e):
        if e in self.cache:return self.cache[e]
        if e.op=='var':
            ans=('h'+e.args[0],*bounds[e.args[0]])
            self.cache[e]=ans;return ans
        if e.op=='const':
            a=b=e.args[0];term=f'IntervalBounds.exact {rat(a)}'
        elif e.op in ('neg','inv'):
            x,a,b=self.build(e.args[0])
            if e.op=='neg':a,b=-b,-a;term=f'IntervalBounds.neg {x}'
            else:
                assert a>0
                a,b=1/b,1/a;term=f'IntervalBounds.inv_pos {x} (by norm_num)'
        else:
            x,a,b=self.build(e.args[0]);y,cc,dd=self.build(e.args[1])
            if e.op=='+':a,b=a+cc,b+dd;term=f'IntervalBounds.add {x} {y}'
            elif e.op=='-':a,b=a-dd,b-cc;term=f'IntervalBounds.sub {x} {y}'
            elif e.op=='*':
                if a>=0 and cc>=0:rule='nn';a,b=a*cc,b*dd
                elif a>=0 and dd<=0:rule='np';a,b=b*cc,a*dd
                elif b<=0 and cc>=0:rule='pn';a,b=a*dd,b*cc
                elif b<=0 and dd<=0:rule='pp';a,b=b*dd,a*cc
                else:raise ValueError(('straddle',e,a,b,cc,dd))
                term=f'IntervalBounds.mul_{rule} {x} {y} (by norm_num) (by norm_num)'
        name=f'b{len(self.cache)}'
        self.lines += [f'  have {name} : Bounds {rat(a)} {e.lean()} {rat(b)} := by',f'    convert {term} using 1 <;> norm_num']
        ans=(name,a,b);self.cache[e]=ans;return ans
    def pos(self,e):
        name,a,b=self.build(e)
        assert a>0,(float(a),float(b),e)
        return f'lt_of_lt_of_le (by norm_num : (0 : ℝ) < {rat(a)}) {name}.1'

u=(Q(897,1024)-r*(1-c))/(1-r);v=(r*d-Q(1,64))/(1-r)
points=[(u,v),(u-1,v),(u-Q(897,1024),v+Q(1,64))]
dirs=[(as_e(-1),as_e(0)),(as_e(Q(127,256)),as_e(Q(1,16))),(16*r*(1-c),-16*r*d)]
grads=[(as_e(1),as_e(0)),(as_e(-1),as_e(Q(-1,8))),(c,d)]
def dot(g,x):return g[0]*x[0]+g[1]*x[1]
tests=[(0,Q(1),1,True),(1,Q(1),0,False),(1,Q(1,2),0,False),(1,Q(1,4),2,True),(2,Q(1),0,False),(2,Q(1,2),0,False),(2,Q(1,4),0,False),(2,Q(1,8),0,False),(2,Q(1,16),0,True)]
head='''import BfgsVerification.AlgebraicSeedOrbitData
/-! Generated rational interval proof candidates for D's nine strict oracle decisions.
Every endpoint and implication is checked by Lean; Python is not trusted. -/
noncomputable section
namespace BfgsVerification.SeedOrbit
open IntervalBounds SeedCycle AlgebraicSeed
'''
hyps='''{c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000))'''
out=[head]
# Independently checked ratio enclosure from the certified c,d enclosure.
p=Proof();rho=129*(c-8*d)/((16*c-127*d-16)*(127*c+16*d+129));bn,lo,hi=p.build(rho)
out+=['theorem tight_ratio {c d : ℝ}', '    (hc : Bounds (318481/1000000) c (318482/1000000))', '    (hd : Bounds (-1025233/1000000) d (-1025232/1000000)) :', '    Bounds (6019/100000) (ratio c d) (6021/100000) := by']
out+=p.lines
out += [f'  have h := {bn}', '  unfold Bounds at h ⊢', '  dsimp only [ratio,R,V,U]', '  simp only [div_eq_mul_inv]', '  constructor <;> linarith only [h.1,h.2]', '']
# Flat polynomial/rational contracts facilitate transparent source review.
cases=[(f"base_{j}",j,Q(0),j,None) for j in range(3)]+[(f"trial_{idx}",*t) for idx,t in enumerate(tests)]
for key,j,alpha,act,accept in cases:
    pos=(points[j][0]+alpha*dirs[j][0],points[j][1]+alpha*dirs[j][1])
    vals=[dot(g,pos) for g in grads];cur=dot(grads[j],points[j]);q=alpha*dot(grads[j],dirs[j]);qn=alpha*dot(grads[act],dirs[j])
    assertions=[]
    assertions += [(f'active_{i}',vals[act]-vals[i]) for i in range(3) if i!=act]
    for i in range(3):assertions += [(f'lower_{i}',vals[i]+3),(f'upper_{i}',3-vals[i])]
    assertions += [('vertical',2-pos[1]),('value',vals[act])]
    if accept is True:assertions += [('armijo',cur+Q(1,3)*q-vals[act]),('descent',-q),('wolfe',qn)]
    elif accept is False:assertions += [('reject',vals[act]-cur),('descent',-q)]
    p=Proof();proofs=[p.pos(e) for label,e in assertions]
    out += [f'/-- Phase {j}, trial α={alpha}, unique branch {act}; '+('accept.' if accept is True else ('reject by strict increase.' if accept is False else 'accepted base point.'))+' -/',f'theorem raw_{key} '+hyps+' :']
    out += ['    '+' ∧\n    '.join(f'0 < {e.lean()}' for label,e in assertions)+' := by']
    out += p.lines
    out += ['  exact ⟨'+',\n    '.join(proofs)+'⟩','']
out+=['end BfgsVerification.SeedOrbit','']
target=ROOT/'BfgsVerification/AlgebraicSeedOracleData.lean'
target.write_text('\n'.join(out))
print(f'{target}: {len(out)} lines; nine exact candidate contracts')
