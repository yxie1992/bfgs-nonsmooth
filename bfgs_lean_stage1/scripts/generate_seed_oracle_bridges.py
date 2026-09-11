#!/usr/bin/env python3
"""Regenerate transparent bridges from scalar interval proofs to actual vector/objective data."""
from pathlib import Path
import runpy
ROOT=Path(__file__).resolve().parents[1]
D=runpy.run_path(str(ROOT/'scripts/generate_seed_oracle.py'))
Q,rat,hyps=D['Q'],D['rat'],D['hyps']
defs='trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv'
lines=['import BfgsVerification.AlgebraicSeedOracleData','noncomputable section','set_option maxHeartbeats 1000000','namespace BfgsVerification.SeedOrbit','open IntervalBounds AlgebraicSeed','']
for key,j,alpha,act,accept in D['cases']:
    base=accept is None
    arg=f'PointCertificate c d (point c d r {j}) {act}' if base else f'TrialCertificate c d r {j} {rat(alpha)} {act} '+str(accept).lower()
    n=10 if base else (13 if accept else 12)
    lines += [f'theorem {key}_certificate '+hyps+' :',f'    {arg} := by',f'  obtain ⟨'+','.join(f'h{i}' for i in range(n))+f'⟩ := raw_{key} hc hd hr',f'  norm_num [div_eq_mul_inv] at '+ ' '.join(f'h{i}' for i in range(n))]
    lines += ['  refine ⟨?_,?_,?_,?_⟩' if base else '  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩']
    lines += ['  · intro k hk','    fin_cases k']
    p=0
    for i in range(3):
        if i==act:lines+=['    · exact False.elim (hk rfl)']
        else:
            lines += [f'    · norm_num [{defs}] <;> nlinarith only [h{p}]'];p+=1
    lines += ['  · intro k','    fin_cases k']
    for i in range(3):
        lines+=['    · apply abs_lt.mpr',f'      constructor <;> norm_num [{defs}] <;> nlinarith only [h{2+2*i},h{3+2*i}]']
    lines += [f'  · norm_num [{defs}] <;> nlinarith only [h8]',f'  · norm_num [{defs}] <;> nlinarith only [h9]']
    if not base:
        lines += [f'  · norm_num [{defs}] <;> nlinarith only [h11]',f'  · norm_num [{defs}] <;> nlinarith only [h10]']
        if accept:lines += ['  · intro _',f'    norm_num [{defs}] <;> nlinarith only [h12]']
        else:lines += ['  · intro h','    cases h']
    lines += ['']
lines += ['end BfgsVerification.SeedOrbit','']
(ROOT/'BfgsVerification/AlgebraicSeedOracleBridges.lean').write_text('\n'.join(lines))
