#!/usr/bin/env python3
"""Generate exact rational certificate candidates; Lean checks every identity and bound.

This script is not a proof oracle. Run from the project root, then lake build
BfgsVerification.AlgebraicSeedJacobian and the full audit. No generated numerical
result is accepted by Lean without a ring/norm_num proof term.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
class Poly(dict):
 def __add__(self,b):
  if not isinstance(b,dict): b=Poly({(0,0):F(b)})
  d=Poly(self)
  for k,v in b.items(): d[k]=d.get(k,F(0))+v
  return Poly({k:v for k,v in d.items() if v})
 __radd__=__add__
 def __neg__(self):return Poly({k:-v for k,v in self.items()})
 def __sub__(self,b): return self+-b if isinstance(b,dict) else self+(-F(b))
 def __rsub__(self,b):return -self+b
 def __mul__(self,b):
  if not isinstance(b,dict):return Poly({k:v*F(b) for k,v in self.items() if v*F(b)})
  d=Poly()
  for (i,j),v in self.items():
   for (k,l),w in b.items(): d=d+Poly({(i+k,j+l):v*w})
  return d
 __rmul__=__mul__
 def __pow__(self,n):
  r=Poly({(0,0):F(1)})
  for _ in range(n): r=r*self
  return r
 def deriv(self,i):return Poly({(k-1,l) if i==0 else (k,l-1):v*(k if i==0 else l) for (k,l),v in self.items() if (k if i==0 else l)})
 def ev(self,c,d):return sum(v*c**k*d**l for (k,l),v in self.items())
 def shift(self,c,d):
  r=Poly()
  for (k,l),v in self.items():
   for i in range(k+1):
    for j in range(l+1):r=r+Poly({(i,j):v*comb(k,i)*comb(l,j)*c**(k-i)*d**(l-j)})
  return r
c,d=Poly({(1,0):F(1)}),Poly({(0,1):F(1)})
U=127*c+16*d;V=16*c-127*d-16;R=c-8*d;K=8*c*c+8*d*d+d-8;T=c*c-c+d*d;Y=(c-1)**2+d*d
P=[264192*R*K-U*V*(U+129),16*V*T*K-R*U*Y]
c0=F('0.31848142762711863064645131250290703717912205023605')
d0=F('-1.02523211967574872548135087001300414284511909318444')
J=[[p.deriv(i).ev(c0,d0) for i in (0,1)] for p in P]
det=J[0][0]*J[1][1]-J[0][1]*J[1][0]
M=[[J[1][1]/det,-J[0][1]/det],[-J[1][0]/det,J[0][0]/det]]
N=[v-sum(M[i][j]*P[j].shift(c0,d0) for j in (0,1)) for i,v in enumerate([c,d])]
for i,p in enumerate(N):
 assert p.get((1,0),0)==p.get((0,1),0)==0
 r0=abs(p.get((0,0),0));weight=sum(abs(v)*(k+l) for (k,l),v in p.items())
 assert r0<F(1,10**50)
 assert weight<7000

def rat(a):
 a=F(a)
 if a.denominator==1:return str(a.numerator)
 return f'({a.numerator} / {a.denominator} : ℝ)'
def poly(p):
 def term(k,l,v):return f'{rat(v)} * x 0 ^ {k} * x 1 ^ {l}'
 return ' +\n    '.join(term(k,l,v) for (k,l),v in sorted(p.items())) or '0'
words=sorted(set(k for p in N for k in p if sum(k)>=2))
head='''import BfgsVerification.PolynomialBounds
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.AlgebraicSeed
open PolynomialBounds

def U (c d : ℝ) := 127*c+16*d
def V (c d : ℝ) := 16*c-127*d-16
def R (c d : ℝ) := c-8*d
def K (c d : ℝ) := 8*c^2+8*d^2+d-8
def T (c d : ℝ) := c^2-c+d^2
def Y (c d : ℝ) := (c-1)^2+d^2
def P (x : Vec 2) : Vec 2 := ![264192*R (x 0) (x 1)*K (x 0) (x 1)-U (x 0) (x 1)*V (x 0) (x 1)*(U (x 0) (x 1)+129),16*V (x 0) (x 1)*T (x 0) (x 1)*K (x 0) (x 1)-R (x 0) (x 1)*U (x 0) (x 1)*Y (x 0) (x 1)]
'''
text=head+f'\ndef center : Vec 2 := ![{rat(c0)},{rat(d0)}]\ndef radius : ℝ := 1 / 10^30\n'
text+='def J : Mat 2 := !!['+';'.join(','.join(rat(x) for x in row) for row in J)+']\n'
text+='def M : Mat 2 := !!['+';'.join(','.join(rat(x) for x in row) for row in M)+']\n'
text+='def newton (x : Vec 2) : Vec 2 := x-M.mulVec (P (center+x))\n'
text+=f'def words : Fin {len(words)} → List (Fin 2) := !['+','.join('['+','.join(['0']*k+['1']*l)+']' for k,l in words)+']\n'
for i,p in enumerate(N):
 text+=f'\ndef coeff{i} : Fin {len(words)} → ℝ := !['+','.join(rat(p.get(k,0)) for k in words)+']\n'
 text+=f'def constant{i} : ℝ := {rat(p.get((0,0),0))}\n'
text+='\ntheorem words_quadratic (i : Fin '+str(len(words))+') : 2 ≤ (words i).length := by\n  fin_cases i <;> norm_num [words]\n'
for i,p in enumerate(N):
 text+=f'\ntheorem expansion{i} (x : Vec 2) : newton x {i} = constant{i}+∑ j,coeff{i} j*monomial (words j) x := by\n  simp only [newton,M,P,center,U,V,R,K,T,Y,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.add_apply,Pi.sub_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]\n  norm_num [constant{i},coeff{i},words,monomial,Fin.sum_univ_succ]\n  <;> ring\n'
 text+=f'\ntheorem constant{i}_small : |constant{i}| < 1 / (10:ℝ)^50 := by norm_num [constant{i},abs_div]\n'
 text+=f'\ntheorem coeff{i}_bound : (∑ j,|coeff{i} j| *(words j).length) ≤ 7000 := by\n  norm_num [coeff{i},words,Fin.sum_univ_succ,abs_div]\n'
text+='\ntheorem M_left_inverse : M * J = 1 := by\n  ext i j\n  fin_cases i <;> fin_cases j <;> norm_num [M,J,Matrix.mul_apply,Fin.sum_univ_two]\n'
text+='\nend BfgsVerification.AlgebraicSeed\n'
Path('BfgsVerification/AlgebraicSeedData.lean').write_text(text)
print('generated',len(text),'characters, words',len(words))
