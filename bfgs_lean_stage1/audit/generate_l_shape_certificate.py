#!/usr/bin/env python3
"""Generate proof candidates for actual L return-Jacobian intervals.

No Python result is trusted. The emitted Lean file proves every interval bound
and every exact equality with the actual derivative recurrence in the kernel.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import cache
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent / "BfgsVerification"
@dataclass(frozen=True)
class E:
    op:str
    args:tuple
def C(x):return x if isinstance(x,E) else E('const',(Q(x),))
def rat(q):
    q=Q(q)
    return f'({q.numerator}/{q.denominator} : ℝ)' if q.denominator!=1 else f'({q.numerator} : ℝ)'
rounding=10**14
def outward(a,b):
    return Q(a.numerator*rounding//a.denominator,rounding),Q(-((-b.numerator*rounding)//b.denominator),rounding)
boxes={'c':(Q('0.318481427627118'),Q('0.318481427627119')),'d':(Q('-1.025232119675749'),Q('-1.025232119675748'))}
@cache
def interval(e):
    if e.op=='var':return boxes[e.args[0]]
    if e.op=='const':return e.args[0],e.args[0]
    a,bb=interval(e.args[0])
    if e.op=='neg':return -bb,-a
    if e.op=='inv':
        assert a*bb>0,('zero inverse',a,bb)
        return (1/bb,1/a) if a==bb else outward(1/bb,1/a)
    c,d=interval(e.args[1])
    if e.op=='+':lo,hi=a+c,bb+d
    else:
        p=[a*c,a*d,bb*c,bb*d];lo,hi=min(p),max(p)
    return (lo,hi) if lo==hi else outward(lo,hi)

class Proof:
    def __init__(self):self.names={};self.lines=[];self.locals=[]
    def build(self,e):
        if e in self.names:return self.names[e]
        if e.op=='var':
            self.names[e]=(e.args[0],'h'+e.args[0]);return self.names[e]
        if e.op=='const':
            return rat(e.args[0]),f'(IntervalBounds.exact {rat(e.args[0])})'
        x,hx=self.build(e.args[0]);a,b=interval(e.args[0])
        if e.op=='neg':expr=f'-{x}';term=f'IntervalBounds.neg {hx}'
        elif e.op=='inv':
            expr=f'{x}⁻¹';term=f'IntervalBounds.inv_pos {hx} (by norm_num)' if a>0 else f'inv_negative {hx} (by norm_num)'
        else:
            y,hy=self.build(e.args[1]);cc,dd=interval(e.args[1]);expr=f'{x}{e.op}{y}'
            if e.op=='+':term=f'IntervalBounds.add {hx} {hy}'
            elif e.op=='*':
                if a>=0 and cc>=0:term=f'IntervalBounds.mul_nn {hx} {hy} (by norm_num) (by norm_num)'
                elif a>=0 and dd<=0:term=f'IntervalBounds.mul_np {hx} {hy} (by norm_num) (by norm_num)'
                elif b<=0 and cc>=0:term=f'IntervalBounds.mul_pn {hx} {hy} (by norm_num) (by norm_num)'
                elif b<=0 and dd<=0:term=f'IntervalBounds.mul_pp {hx} {hy} (by norm_num) (by norm_num)'
                else:term=f'mul_corners {hx} {hy}'+''.join(' (by norm_num)'for _ in range(8))
        n=len(self.locals);name=f'v{n}';hname=f'h{n}';lo,hi=interval(e)
        self.locals.append(name)
        self.lines += [f'  let {name} : ℝ := {expr}',f'  have {hname} : Bounds {rat(lo)} {name} {rat(hi)} := by']
        if e.op=='*' and a<0<b and cc<0<dd or e.op=='*' and not ((a>=0 or b<=0) and (cc>=0 or dd<=0)):
            self.lines += [f'    exact {term}']
        else:self.lines += [f'    exact enlarge ({term}) (by norm_num) (by norm_num)']
        self.names[e]=(name,hname);return self.names[e]

p=Proof();out=[]
def v(x):return E('var',(x,))
def add(x,y):return E('+',(x,y))
def neg(x):return E('neg',(x,))
def mul(x,y):return E('*',(x,y))
def inv(x):return E('inv',(x,))
def real(e):
    if e.op=='var':return e.args[0]
    if e.op=='const':return rat(e.args[0])
    if e.op=='neg':return f'(-{real(e.args[0])})'
    if e.op=='inv':return f'({real(e.args[0])})⁻¹'
    return f'({real(e.args[0])}{e.op}{real(e.args[1])})'
@dataclass(frozen=True)
class J:
    op:str
    args:tuple
names={}
def const(x):return J('const',(x,))
def mk(x,y):return J('mk',(x,y))
def ja(x,y):return J('add',(x,y))
def jm(x,y):return J('mul',(x,y))
def js(x,y):return J('sub',(x,y))
def ji(x):return J('inv',(x,))
def gen(j):
    if j in names:return names[j]
    if j.op in ('const','mk'):
        val=j.args[0];tangent=j.args[1] if j.op=='mk' else C(0)
        expression=f'LReturnJets.constant {real(val)}' if j.op=='const' else f'⟨{real(val)},{real(tangent)}⟩'
    else:
        a=gen(j.args[0]);av,at=v(a+'.value'),v(a+'.tangent')
        if j.op=='inv':
            val=inv(av);tangent=mul(neg(at),inv(mul(av,av)))
            expression=f'LReturnJets.inv {a}'
        else:
            bb=gen(j.args[1]);bv,bt=v(bb+'.value'),v(bb+'.tangent')
            expression=f'LReturnJets.{j.op} {a} {bb}'
            if j.op=='add':val,tangent=add(av,bv),add(at,bt)
            elif j.op=='sub':val,tangent=add(av,neg(bv)),add(at,neg(bt))
            elif j.op=='mul':val,tangent=mul(av,bv),add(mul(at,bv),mul(av,bt))
    old=len(p.lines)
    nv,hv=p.build(val);nt,ht=p.build(tangent);out.extend(p.lines[old:])
    name=f'j{len(names)}';names[j]=name
    out.append(f'  obtain ⟨{name},h{name}⟩ : ∃ z : LReturnJets.Jet, {expression}=z := ⟨_,rfl⟩')
    for field,e,h in [('value',val,hv),('tangent',tangent,ht)]:
        lo,hi=interval(e);hn=f'{name}_{field}'
        out.extend([f'  have {hn} : Bounds {rat(lo)} {name}.{field} {rat(hi)} := by',
          f'    convert {h} using 1 <;> norm_num [← h{name},LReturnJets.constant]' if j.op=='const' and field=='value' and val.op=='var' else (f'    simpa only [← h{name},LReturnJets.{j.op if j.op != "const" else "constant"},LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using {h}' if j.op!='mk' else f'    simpa only [← h{name}] using {h}')])
        key=name+'.'+field;boxes[key]=(lo,hi);p.names[v(key)]=(key,hn)
    return name

def mv(H,vv):return [ja(jm(H[i][0],vv[0]),jm(H[i][1],vv[1])) for i in range(2)]
def mm(H,K):return [[ja(jm(H[i][0],K[0][j]),jm(H[i][1],K[1][j]))for j in range(2)]for i in range(2)]
def ms(r,H):return [[jm(r,H[i][j])for j in range(2)]for i in range(2)]
def ma(H,K):return [[ja(H[i][j],K[i][j])for j in range(2)]for i in range(2)]
def msub(H,K):return [[js(H[i][j],K[i][j])for j in range(2)]for i in range(2)]
def outer(s,y):return [[jm(s[i],y[j])for j in range(2)]for i in range(2)]
def mat(H):return f'!![{gen(H[0][0])},{gen(H[0][1])};{gen(H[1][0])},{gen(H[1][1])}]'
I=[[const(C(int(i==j))) for j in range(2)]for i in range(2)]
gvals=[[C(1),C(0)],[C(-1),C(Q(-1,8))],[v('c'),v('d')]]
gs=[[const(e)for e in row]for row in gvals]

HEAD="""import BfgsVerification.LShapeDerivative
import BfgsVerification.LShapeIntervalTools
noncomputable section
open Matrix
namespace BfgsVerification.LShapeIntervalCertificate
open IntervalBounds LShapeIntervalTools LShapeDerivative
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
"""
allout=[HEAD]
lows=[[Q(11123986249,10**10),Q(6459701025,10**10)],[Q(7515015701,10**10),Q(4905136882,10**10)]]
highs=[[Q(11123986253,10**10),Q(6459701029,10**10)],[Q(7515015708,10**10),Q(4905136890,10**10)]]
for column in range(2):
    p=Proof();out=[];names={};results={}
    allout += [f"""
theorem column_{column}_bounds {{c d : ℝ}}
    (hc : Bounds (318481427627118/10^15) c (318481427627119/10^15))
    (hd : Bounds (-1025232119675749/10^15) d (-1025232119675748/10^15)) :
    Bounds {rat(lows[0][column])} (jacobian c d 0 {column}) {rat(highs[0][column])} ∧
    Bounds {rat(lows[1][column])} (jacobian c d 1 {column}) {rat(highs[1][column])} := by
"""]
    interval.cache_clear()
    for j in [column]:
        H=[[const(C(1)),mk(C(0),C(int(j==0)))],[mk(C(0),C(int(j==0))),mk(C(1),C(int(j==1)))]]
        rhs=mat(H)
        initnames=','.join('← h'+names[x] for x in dict.fromkeys(x for row in H for x in row))
        out += [f'  have hm{j}0 : jetIter c d {j} 0={rhs} := by',f'    simp only [{initnames}]', '    rfl']
        for k,a in enumerate([Q(1),Q(1,4),Q(1,16)]):
            prev=set(x for row in H for x in row)
            s=[jm(const(C(-a)),x)for x in mv(H,gs[k])]
            y=[const(add(gvals[(k+1)%3][i],neg(gvals[k][i])))for i in range(2)]
            r=ji(ja(jm(y[0],s[0]),jm(y[1],s[1])))
            H=ma(mm(mm(msub(I,ms(r,outer(s,y))),H),msub(I,ms(r,outer(y,s)))),ms(r,outer(s,s)))
            rhs=mat(H)
            visited=set()
            def visit(jj):
                if jj in prev or jj in visited:return
                if jj.op not in ('const','mk'):
                    for child in jj.args:visit(child)
                visited.add(jj)
            for row in H:
                for jj in row:visit(jj)
            visited.update(jj for jj in names if jj.op=='const')
            localnames=','.join('← h'+names[jj] for jj in sorted(visited,key=lambda jj:int(names[jj][1:])))
            out += [f'  have hm{j}{k+1} : jetIter c d {j} {k+1}={rhs} := by',
              f'    rw [jetIter,hm{j}{k}]',
              '    ext i l <;> fin_cases i <;> fin_cases l',
              '    all_goals simp only [updateJet,stepJet,LReturnJets.inverseUpdate,LReturnJets.matAdd,LReturnJets.matMul,LReturnJets.matSub,LReturnJets.matScale,LReturnJets.matConstant,LReturnJets.outer,LReturnJets.vecScale,LReturnJets.mulVec,LReturnJets.vecConstant,LReturnJets.dot,SeedOrbit.phase,SeedOrbit.gradient,SeedOrbit.nextPhase,SeedOrbit.length,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.sub_apply,sub_eq_add_neg]',
              '    all_goals norm_num [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.add_apply,Pi.neg_apply,Matrix.one_apply,'+localnames+']',
              '    all_goals rfl']
        for i in range(2):
            result=jm(H[i][1],ji(H[0][0]));name=gen(result);results[i,j]=name
            out += [f'  have he{i}{j} : jacobian c d {i} {j}={name}.tangent := by',
              f'    simp only [jacobian,shapeJet,hm{j}3,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,LReturnJets.div]',
              f'    rw [← h{name},← h{names[result.args[1]]}]','    rfl']
    out += [f'  rw [he0{column},he1{column}]',
      f'  exact ⟨enlarge {results[0,column]}_tangent (by norm_num) (by norm_num),',
      f'    enlarge {results[1,column]}_tangent (by norm_num) (by norm_num)⟩']
    allout += out
    print('column',column,'Jets',len(names),'scalar nodes',len(p.locals))
allout += ["""
theorem jacobian_bounds {c d : ℝ}
    (hc : Bounds (318481427627118/10^15) c (318481427627119/10^15))
    (hd : Bounds (-1025232119675749/10^15) d (-1025232119675748/10^15)) :
    Bounds (11123986249/10^10) (jacobian c d 0 0) (11123986253/10^10) ∧
    Bounds (6459701025/10^10) (jacobian c d 0 1) (6459701029/10^10) ∧
    Bounds (7515015701/10^10) (jacobian c d 1 0) (7515015708/10^10) ∧
    Bounds (4905136882/10^10) (jacobian c d 1 1) (4905136890/10^10) := by
  constructor
  · convert (column_0_bounds hc hd).1 using 1 <;> norm_num
  constructor
  · convert (column_1_bounds hc hd).1 using 1 <;> norm_num
  constructor
  · convert (column_0_bounds hc hd).2 using 1 <;> norm_num
  · convert (column_1_bounds hc hd).2 using 1 <;> norm_num
end BfgsVerification.LShapeIntervalCertificate
"""]
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true',help='check byte-identical regeneration without editing the source')
args=parser.parse_args()
destination=ROOT/'LShapeIntervalCertificate.lean'
generated='\n'.join(allout)+'\n'
if args.check:
    assert destination.read_text()==generated, 'Generated source differs: '+str(destination)
    print('PASS: exact byte-identical certificate regeneration')
else:
    destination.write_text(generated)
    print('Wrote',destination)

