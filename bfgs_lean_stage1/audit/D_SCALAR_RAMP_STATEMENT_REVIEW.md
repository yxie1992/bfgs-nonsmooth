# Literal Module D ramp and primitive

`BfgsVerification/DScalarRamp.lean` independently formalizes D.tex lines246–357's scalar ramp prerequisite. The original source is preserved. The module contains 83 checked declarations: 64 theorems and 19 actual definitions. It does not assume a ramp oracle or an integral/derivative formula.

The constants theta=1/16, epsilon=1/128, and center(b)=[1−(1+theta+theta²)/b]/[1−theta²] are literal. The coordinate t=(x−center+epsilon)/(2epsilon) is literal. The ramp is the actual three-piece function0 / (3t²−2t³) /1, and its primitive is the actual0 / 2epsilon(t³−t⁴/2) / (x−center) function. The branch equalities cover closed exterior regions and the open transition, including the exact join values. A generic checked one-sided derivative gluing lemma matches values and first derivatives at a join; it is applied to these actual polynomials at 0 and 1 before the affine coordinate change.

`ramp_hasDerivAt` proves its actual derivative is `rampDerivative`; `primitive_hasDerivAt` proves J'=P, and `primitive_second_hasDerivAt` proves J''=P'. `ramp_contDiff` is C1 and `primitive_contDiff` is C2 everywhere, including both joins. P is monotone, 0≤P≤1 and0≤P'≤96 everywhere. The explicit derivative of the unit ramp is6 clip(t)(1−clip(t)), where clip=max(0,min(1,t)); this supplies its actual continuity, range and sharp bound 3/2 before scaling by64.

For every 2≤b≤34, the transition endpoints lie strictly in(0,1). The exact formulas

- center(b)=(256b−273)/(255b),
- lowerLength(b)=273/272−383b/34816,
- upperLength(b)=32513b/2176−273/17

prove both source plateau lengths are strictly greater than 1/2 throughout that interval. This is stronger than the source restriction b=2 or 33<b<34; no additional restriction on the source b* is introduced. The exact matching identity theta²+(1−theta²)(1−center)=(1+theta+theta²)/b is also proved. The displayed source decimal table is not treated as exact input and is unnecessary for any inequality.

`primitive_eq_integral` proves the actual interval integral from 0 to every real x equals J(x), using actual continuous P and the fundamental theorem of calculus, with J(0)=0 derived from the transition location. In particular `integral_ramp` proves integral0¹P=1−center. The derivative and value formulas hold on both exterior plateaus. Source-valid b also gives0≤J(x)≤max(0,x), hence |J(x)|≤|x|, which supplies an actual bound for the subsequent geometric series construction.

`rampDerivative_lipschitz` proves the global constant 24576=3/(2epsilon²). Its proof is an exact clipped-polynomial difference estimate, so it does not assume second differentiability of P at the transition endpoints. J'' is therefore globally Lipschitz with the same constant. Actual third-derivative existence and the polynomial formula are exported inside each open transition. The separate global `ramp_second_derivative_bound` is a bound on Lean's total deriv operation; it does not assert that P is C2 or has a classical second derivative at its joins. All source statements that need a classical derivative use an explicit HasDerivAt theorem instead.

The scaled interval expression `intervalCurvature(b,a,x)=a(1+theta)/b * P'_b((x/(ba)−theta)/(1−theta))` is actual. For b>0 and a≥0 its value lies between 0 and 102a/b. For b,a>0 it is globally Lipschitz with the literal source constant 139264/(5b²), independent of a. Inside the transition it has the actual derivative [(1+theta)/(b²(1−theta))]P''_b(coordinate), with the same absolute bound. Thus the apparent1/a scale loss cancels in a checked algebraic identity. No assertion of an actual derivative at a ramp join is smuggled into that argument.

Remaining scope belongs to the separate global scalar construction: sum the geometric ramps, establish the literal phi_b interval formula and node jets, glue the negative cubic/quadratic and positive affine exterior, handle the accumulation point 0, and derive global convexity/coercivity/unique minimum and global C2,1 regularity. This module supplies the concrete scalar ingredients but does not label that construction or the final local BFGS embedding complete. No source correction was required for the ramp formulas or constants.

Reproduction: `lake build BfgsVerification.DScalarRamp`, then `lake env lean audit/DScalarRampAudit.lean`, using the pinned scripts/env.sh environment. Actual logs: d_scalar_ramp_build.log, d_scalar_ramp_axioms.log, d_scalar_ramp_validation.log. Every explicit declaration's transitive axiom list is contained in {propext, Classical.choice, Quot.sound}. The scratch source and development evidence are preserved in audit/scratch/d_scalar_ramp. The eighth milestone whole-project status/manifest/logs remain unchanged; these declarations await the next integration audit.
