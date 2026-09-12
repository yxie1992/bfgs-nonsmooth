# Negative proof-completeness peer review

Reviewed 12 September 2026 by a separate AI agent. This is mathematical/editorial review and independent rational recalculation, not a claim of human approval. No source TeX was edited in this review.

**Outcome: no blocking proof-completeness gap found in the reviewed negative core.** The article provides the defining polynomial, exact root box, coefficient formulas and bounds, sound rational interval rules, all nine query decisions, both interpolation constructions, normalized return map, spectral certificate, stable-manifold argument, and fixed whitening transformation. Essential construction estimates are not replaced by “see companion,” a Lean theorem name, or a floating-point result.

The review compared the upper and lower statements with corrected Modules D/L and the independent literal targets in `editorial/formal_audit/sources/NegativeClaims.lean`. The wider parameter family belongs only to the upper-regularity example. The lower example fixes the line-search pair and obtains a single common SPD initialization before one fixed coordinate change. Both prove all-query locality, not merely accepted-iterate locality. The lower finite-branch example is C¹,¹, with three branches not twice differentiable at zero; the constant-Hessian alternative uses countably polyhedral geometry. The introduction explicitly defines the classical-Hessian convention to match the neighborhood-differentiability hypothesis in the formal target. No claim of generic failure or a positive-measure basin is made.

The stable-manifold theorem and inverse-function/contraction principles remain standard cited mathematical ingredients. Their hypotheses are supplied here: the return map is analytic near the seed, the derivative is invertible and hyperbolic, and a stable tangent vector has nonzero scale coordinate. This supplies positive-scale states and uniform local forward orbits. No numerically shot trajectory is substituted for stable-manifold membership.

Independent checks used Python's standard-library Fraction arithmetic, a fresh sparse-polynomial expansion, and a fresh dual-interval implementation of the displayed full inverse update. The two snippets below are complete reproducible review calculations; run from repository root. Fractions govern every asserted comparison. Floating conversions occur only after checking, to make the printed diagnostics legible.

- Root certificate: Jacobian determinant is positive; both preconditioned residual components are strictly below 10⁻⁵⁰; weighted nonlinear coefficient sums are at most 7000.
- All nine printed common lower bounds and value enclosures pass. Base active gaps, positive values, all-query slab bounds, and the stated rho enclosure pass.
- Independent differentiation of the three rational substeps over the displayed 10⁻¹⁵ c,d box lies within all four printed shape-Jacobian intervals. The four characteristic-polynomial sign comparisons also pass.

The first exploratory run also compared every intermediate interval for exact textual equality with the author's JSON and failed that equality check. Different algebraic groupings can give different valid intervals. The final independent check tests the mathematical displayed bounds directly; it does not weaken any displayed strict inequality. In fact, the independently calculated value intervals coincide with the JSON intervals. The retained calculations are additional review evidence and are not substitutes for the formal proofs.

Optional clarity improvement, not a blocker: in the constant-Hessian alternative, the claim that zero is nonsmooth follows immediately from F≥0, F(0)=0 and F(te₂)≥t+μt²/2 for t>0. Stating this one-line argument would make the conclusion explicit even though it is already forced by the displayed construction.

## Reviewed file hashes

```json
{
  "paper/sections/failure.tex": "3f7f5e921164bdcd2e9e182b14f36b842744985c8dede5c1263cbe97ebf0ffd3",
  "paper/appendices/seed_certificate.tex": "b08ab2f73ecbf03a9119e43627ad83ec27ae73dd0f263bcd19deba9cbfdb0353",
  "paper/appendices/lower_curvature.tex": "f35ee24b1820682d5ae4844c05c4460bb79965622b1331bf00785016047d7526",
  "paper/statements/negative_upper.tex": "dc24603ade146b37fe166e9ac4813e4ab8c6175b4f6dcca6947e2fe31fb17856",
  "paper/statements/negative_lower.tex": "e7125371f5ac751ecbf5629c7c0a50cd19a28cb28293f4833b066b6c1fb114b4",
  "paper/sections/introduction.tex": "fa8824b6d9a940cabb0bd4e92f690c0c05bf47b72c47d3eca43b1544d83dcdec",
  "paper/figures/seed_data.json": "2bd591dfdb35ce1b17cbf642701bc893b5eb749216f0facee0c5835a5acdd3aa",
  "editorial/formal_audit/sources/NegativeClaims.lean": "2d5df1dd0a324e92db0e7c5d18167ac9ee627a975392e4538805cd54f1c826ef",
  "bfgs_lean_stage1/master_report/latex/chapters/D.tex": "3397b9fe7c16f314ebd33652bc4baaf85c262f648cd07988a8d59bf91987df8d",
  "bfgs_lean_stage1/master_report/latex/chapters/L.tex": "4143372759ee972a596fd7afefcb4ac036c7f18eddee9472eea987d3cfff80ad"
}
```

## Independent root and query calculation

```sh
python3 - <<'PY'
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path
class I:
 def __init__(s,a,b=None):s.a=F(a);s.b=F(a if b is None else b)
 def __add__(s,o):
  o=o if isinstance(o,I) else I(o);return I(s.a+o.a,s.b+o.b)
 __radd__=__add__
 def __neg__(s):return I(-s.b,-s.a)
 def __sub__(s,o):return s+-o if isinstance(o,I) else s+-F(o)
 def __rsub__(s,o):return -s+o
 def __mul__(s,o):
  o=o if isinstance(o,I) else I(o);v=[s.a*o.a,s.a*o.b,s.b*o.a,s.b*o.b];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(s,o):
  o=o if isinstance(o,I) else I(o);assert o.a*o.b>0;return s*I(1/o.b,1/o.a)
 def pair(s):return [str(s.a),str(s.b)]
def dot(a,b):return sum((x*y for x,y in zip(a,b)),I(0))
def add(a,b):return [x+y for x,y in zip(a,b)]
def scale(t,a):return [t*x for x in a]
data=json.loads(Path('paper/figures/seed_data.json').read_text())
c=I(F(318481,10**6),F(318482,10**6));d=I(F(-1025233,10**6),F(-1025232,10**6));rho=I(F(6019,10**5),F(6021,10**5))
actualrho=129*(c-8*d)/((16*c-127*d-16)*(127*c+16*d+129))
assert rho.a<actualrho.a and actualrho.b<rho.b
g=[[I(1),I(0)],[I(-1),I(F(-1,8))],[c,d]]
z0=[(F(897,1024)-rho*(1-c))/(1-rho),(rho*d-F(1,64))/(1-rho)]
z1=add(z0,[I(-1),I(0)]);z2=add(z1,[I(F(127,1024)),I(F(1,64))]);z=[z0,z1,z2]
p=[[I(-1),I(0)],[I(F(127,256)),I(F(1,16))],scale(16*rho,[1-c,-d])]
rows=[];allpoints=list(z)
for row in data['rows']:
 j=row['phase'];alpha=F(row['alpha']);i=row['active'];accepted=row['accepted'];q=add(z[j],scale(alpha,p[j]));allpoints.append(q)
 gaps=[dot([g[i][k]-g[l][k] for k in range(2)],q) for l in range(3) if l!=i]
 value=dot(g[i],q);old=dot(g[j],z[j]);descent=-alpha*dot(g[j],p[j]);margin=old-descent/3-value if accepted else value-old
 values=gaps+[descent,margin]
 if accepted:values.append(alpha*dot(g[i],p[j]))
 lb=F(row['common_margin_lower_1e4'],10000)
 assert all(t.a>lb for t in values),(j,str(alpha),'margin failed',[float(t.a) for t in values])
 outer=row['value_outer_1e4'];assert F(outer[0],10000)<value.a and value.b<F(outer[1],10000),(j,alpha,value.pair())
 rows.append({'phase':j,'alpha':str(alpha),'common_lower':str(lb),'minimum_lower_approx':float(min(v.a for v in values)),'value_interval':value.pair(),'all_exact_comparisons':True})
for j,base in enumerate(z):assert all(dot([g[j][k]-g[l][k] for k in range(2)],base).a>0 for l in range(3) if l!=j)
for k,q in enumerate(allpoints):
 assert (2-q[1]).a>0
 assert all((3-dot(v,q)).a>0 and (3+dot(v,q)).a>0 for v in g)
 active=k if k<3 else data['rows'][k-3]['active'];assert dot(g[active],q).a>0
def clean(p):return {e:F(a) for e,a in p.items() if a}
def poly(a):return a if isinstance(a,dict) else {(0,0):F(a)}
def plus(a,b):
 out=poly(a).copy()
 for e,v in poly(b).items():out[e]=out.get(e,0)+v
 return clean(out)
def neg(a):return {e:-v for e,v in poly(a).items()}
def minus(a,b):return plus(a,neg(b))
def times(a,b):
 out={}
 for e,v in poly(a).items():
  for f,w in poly(b).items():
   t=(e[0]+f[0],e[1]+f[1]);out[t]=out.get(t,0)+v*w
 return clean(out)
C={(1,0):F(1)};D={(0,1):F(1)}
U=plus(times(127,C),times(16,D));V=minus(minus(times(16,C),times(127,D)),16);R=minus(C,times(8,D))
K=minus(plus(plus(times(8,times(C,C)),times(8,times(D,D))),D),8)
T=plus(minus(times(C,C),C),times(D,D));Y=plus(times(minus(C,1),minus(C,1)),times(D,D))
polys=[minus(times(264192,times(R,K)),times(times(U,V),plus(U,129))),minus(times(16,times(times(V,T),K)),times(times(R,U),Y))]
center=[F(x) for x in data['root_center_rationals']]
def shift(p):
 out={}
 for (a,b),v in p.items():
  for i in range(a+1):
   for j in range(b+1):out[i,j]=out.get((i,j),0)+v*comb(a,i)*comb(b,j)*center[0]**(a-i)*center[1]**(b-j)
 return clean(out)
sh=[shift(p) for p in polys];jac=[[s.get(e,0) for e in [(1,0),(0,1)]] for s in sh];det=jac[0][0]*jac[1][1]-jac[0][1]*jac[1][0];assert det!=0
A=[[jac[1][1]/det,-jac[0][1]/det],[-jac[1][0]/det,jac[0][0]/det]]
res=[sum(A[i][j]*sh[j].get((0,0),0) for j in range(2)) for i in range(2)]
coeff=[plus(times(-A[i][0],sh[0]),times(-A[i][1],sh[1])) for i in range(2)]
sums=[sum(abs(v)*sum(e) for e,v in s.items() if 2<=sum(e)<=5) for s in coeff]
assert all(abs(v)<F(1,10**50) for v in res),[float(abs(v)) for v in res]
assert all(v<=7000 for v in sums)
assert all(s.get((1,0),0)==(-1 if i==0 else 0) and s.get((0,1),0)==(-1 if i==1 else 0) for i,s in enumerate(coeff))
print(json.dumps({'root_certificate':{'det_nonzero':True,'det_sign':1 if det>0 else -1,'residual_less_than_1e50':True,'residual_absolute_approx':[float(abs(v)) for v in res],'coefficient_weighted_sums_approx':[float(v) for v in sums],'sums_le_7000':True},'query_rows':rows,'base_active_gaps_positive':True,'all_query_geometry_bounds':True,'rho_inclusion_from_coarse_cd':True},indent=2))

PY
```

Actual successful output (exit code 0):

```json
{
  "root_certificate": {
    "det_nonzero": true,
    "det_sign": 1,
    "residual_less_than_1e50": true,
    "residual_absolute_approx": [
      4.5555542552971035e-52,
      6.048242851954022e-52
    ],
    "coefficient_weighted_sums_approx": [
      6371.66318308984,
      1594.5978691375144
    ],
    "sums_le_7000": true
  },
  "query_rows": [
    {
      "phase": 0,
      "alpha": "1",
      "common_lower": "729/10000",
      "minimum_lower_approx": 0.07297882545613045,
      "value_interval": [
        "538043642490403/4416120199500000",
        "2870424082519667/23552641064000000"
      ],
      "all_exact_comparisons": true
    },
    {
      "phase": 1,
      "alpha": "1",
      "common_lower": "2417/10000",
      "minimum_lower_approx": 0.24174031648648095,
      "value_interval": [
        "48182156093/125308000000",
        "144555975757/375916000000"
      ],
      "all_exact_comparisons": true
    },
    {
      "phase": 1,
      "alpha": "1/2",
      "common_lower": "29/2000",
      "minimum_lower_approx": 0.014590236294637909,
      "value_interval": [
        "34199796561/250616000000",
        "102622373389/751832000000"
      ],
      "all_exact_comparisons": true
    },
    {
      "phase": 1,
      "alpha": "1/4",
      "common_lower": "3/400",
      "minimum_lower_approx": 0.007503828515051383,
      "value_interval": [
        "36241725455610889/501232000000000000",
        "2175508914331597/30073280000000000"
      ],
      "all_exact_comparisons": true
    },
    {
      "phase": 2,
      "alpha": "1",
      "common_lower": "1491/2500",
      "minimum_lower_approx": 0.5964283381083436,
      "value_interval": [
        "1047525694692797/1566350000000000",
        "3143696802537593/4698950000000000"
      ],
      "all_exact_comparisons": true
    },
    {
      "phase": 2,
      "alpha": "1/2",
      "common_lower": "1341/5000",
      "minimum_lower_approx": 0.26826379074834367,
      "value_interval": [
        "533505155935461/1566350000000000",
        "1601153352289109/4698950000000000"
      ],
      "all_exact_comparisons": true
    },
    {
      "phase": 2,
      "alpha": "1/4",
      "common_lower": "1041/10000",
      "minimum_lower_approx": 0.10418151706834364,
      "value_interval": [
        "276494886556793/1566350000000000",
        "829881627164867/4698950000000000"
      ],
      "all_exact_comparisons": true
    },
    {
      "phase": 2,
      "alpha": "1/8",
      "common_lower": "221/10000",
      "minimum_lower_approx": 0.022140380228343644,
      "value_interval": [
        "147989751867459/1566350000000000",
        "222122882301373/2349475000000000"
      ],
      "all_exact_comparisons": true
    },
    {
      "phase": 2,
      "alpha": "1/16",
      "common_lower": "1/500",
      "minimum_lower_approx": 0.0020571791869111247,
      "value_interval": [
        "10467148065349/195793750000000",
        "502855666643371/9397900000000000"
      ],
      "all_exact_comparisons": true
    }
  ],
  "base_active_gaps_positive": true,
  "all_query_geometry_bounds": true,
  "rho_inclusion_from_coarse_cd": true
}
```

## Independent return-map derivative calculation

```sh
python3 - <<'PY'
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path
class I:
 def __init__(s,a,b=None):s.a=F(a);s.b=F(a if b is None else b)
 def __add__(s,o):
  o=o if isinstance(o,I) else I(o);return I(s.a+o.a,s.b+o.b)
 __radd__=__add__
 def __neg__(s):return I(-s.b,-s.a)
 def __sub__(s,o):return s+-o if isinstance(o,I) else s+-F(o)
 def __rsub__(s,o):return -s+o
 def __mul__(s,o):
  o=o if isinstance(o,I) else I(o);v=[s.a*o.a,s.a*o.b,s.b*o.a,s.b*o.b];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(s,o):
  o=o if isinstance(o,I) else I(o);assert o.a*o.b>0;return s*I(1/o.b,1/o.a)
 def pair(s):return [str(s.a),str(s.b)]
def dot(a,b):return sum((x*y for x,y in zip(a,b)),I(0))
def add(a,b):return [x+y for x,y in zip(a,b)]
def scale(t,a):return [t*x for x in a]
class D:
 def __init__(s,v,der=None):s.v=v if isinstance(v,I) else I(v);s.d=der if der is not None else [I(0),I(0)]
 def __add__(s,o):
  o=o if isinstance(o,D) else D(o);return D(s.v+o.v,[s.d[i]+o.d[i] for i in range(2)])
 __radd__=__add__
 def __neg__(s):return D(-s.v,[-x for x in s.d])
 def __sub__(s,o):return s+-o if isinstance(o,D) else s+-F(o)
 def __rsub__(s,o):return -s+o
 def __mul__(s,o):
  o=o if isinstance(o,D) else D(o);return D(s.v*o.v,[s.v*o.d[i]+s.d[i]*o.v for i in range(2)])
 __rmul__=__mul__
 def inv(s):return D(I(1)/s.v,[-x/(s.v*s.v) for x in s.d])
 def __truediv__(s,o):return s*(o if isinstance(o,D) else D(o)).inv()
def dp(a,b):return sum((x*y for x,y in zip(a,b)),D(0))
def mv(m,v):return [dp(r,v) for r in m]
def mm(a,b):return [[sum((a[i][k]*b[k][j] for k in range(2)),D(0)) for j in range(2)] for i in range(2)]
def tr(a):return [[a[j][i] for j in range(2)] for i in range(2)]
c=D(I(F(318481427627118,10**15),F(318481427627119,10**15)))
d=D(I(F(-1025232119675749,10**15),F(-1025232119675748,10**15)))
g=[[D(1),D(0)],[D(-1),D(F(-1,8))],[c,d]]
b=D(0,[I(1),I(0)]);e=D(1,[I(0),I(1)]);M=[[D(1),b],[b,e]]
for j,alpha in enumerate([F(1),F(1,4),F(1,16)]):
 s=[-alpha*x for x in mv(M,g[j])]
 y=[g[(j+1)%3][i]-g[j][i] for i in range(2)];t=dp(y,s)
 V=[[D(int(i==k))-s[i]*y[k]/t for k in range(2)] for i in range(2)]
 K=mm(mm(V,M),tr(V))
 M=[[K[i][k]+s[i]*s[k]/t for k in range(2)] for i in range(2)]
r=M[0][0];outputs=[M[0][1]/r,M[1][1]/r];J=[o.d for o in outputs]
expected=[[(11123986249,11123986253),(6459701025,6459701029)],[(7515015701,7515015708),(4905136882,4905136890)]]
result=[]
for i in range(2):
 row=[]
 for j in range(2):
  v=J[i][j];lo,hi=expected[i][j];ok=F(lo,10**10)<=v.a and v.b<=F(hi,10**10)
  row.append({'enclosure_approx':[float(v.a),float(v.b)],'claimed_outer_pass':ok})
 result.append(row)
B=[[I(F(a,10**10),F(b,10**10)) for a,b in row] for row in expected]
trace=B[0][0]+B[1][1];det=B[0][0]*B[1][1]-B[0][1]*B[1][0]
signs=[]
for val,want in [(F(38,1000),1),(F(39,1000),-1),(F(1564,1000),-1),(F(1565,1000),1)]:
 v=val*val-trace*val+det
 assert (v.a>0 if want>0 else v.b<0)
 signs.append({'lambda':str(val),'expected_sign':want,'exact_comparison_pass':True})
print(json.dumps({'independent_dual_interval_J':result,'characteristic_polynomial_signs':signs},indent=2))

PY
```

Actual successful output (exit code 0):

```json
{
  "independent_dual_interval_J": [
    [
      {
        "enclosure_approx": [
          1.112398625072615,
          1.1123986250739641
        ],
        "claimed_outer_pass": true
      },
      {
        "enclosure_approx": [
          0.6459701027311541,
          0.6459701027320415
        ],
        "claimed_outer_pass": true
      }
    ],
    [
      {
        "enclosure_approx": [
          0.7515015704260456,
          0.7515015704289512
        ],
        "claimed_outer_pass": true
      },
      {
        "enclosure_approx": [
          0.4905136885821094,
          0.4905136885842413
        ],
        "claimed_outer_pass": true
      }
    ]
  ],
  "characteristic_polynomial_signs": [
    {
      "lambda": "19/500",
      "expected_sign": 1,
      "exact_comparison_pass": true
    },
    {
      "lambda": "39/1000",
      "expected_sign": -1,
      "exact_comparison_pass": true
    },
    {
      "lambda": "391/250",
      "expected_sign": -1,
      "exact_comparison_pass": true
    },
    {
      "lambda": "313/200",
      "expected_sign": 1,
      "exact_comparison_pass": true
    }
  ]
}
```
