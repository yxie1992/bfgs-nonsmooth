# Supporting-plane intercept examples

Source: original `report/chapters/R.tex`, lines 176–186. Sources unchanged.

`OptimizerInterceptExamples.lean` exports the literal source intercept examples using `RadialCertificate.optimizerIntercept`, the actual source supporting-plane prediction at the optimizer. `homogeneous_intercept_zero` applies the proved Euler identity to a finite convex degree-one homogeneous objective and its actual derivative. The function value at zero is derived to be zero.

`PositiveDegree p F` means actual positive-scalar real-power homogeneity for every nonnegative factor, not an assumed Euler identity. `degree_euler` derives the actual radial pairing by differentiating the curve t↦F(t*x) at t=1. It requires neither convexity nor nonnegativity for this algebraic derivative statement. `degree_intercept` derives b=(p−1)F for every positive real degree, including all p≥1 source family cases. No homogeneity or derivatives of an auxiliary gauge are assumed.

The positive-degree/zero-value convention matters: with arbitrary degree p, the exact identity is b=(p−1)F+F(0), exported as `degree_intercept_with_zero_value`. For p>0 the value F(0)=0 follows from actual homogeneity. If the report sentence is read as including p=0 without normalization, its unqualified b=(p−1)F is false for a positive constant function. The formalization preserves the general corrected formula and the intended positive-degree formula separately, without silently imposing F(0)=0.

`quadratic_absolute_radial_pairing` and `quadratic_absolute_intercept` use the actual existing objective F(u,v)=u²+|v|. They require only the actual Fréchet derivative at the queried point; they do not add v≠0 or assume a gradient formula. The radial curve has exact model t²u²+t|v| near t=1, whose checked derivative proves b=u². Thus the sign-flipping component does not change this scalar prediction.

The report's separate four-piece counterexample paragraph is not claimed verified here. The retained chapter gives optimizer/branch values but no inline definition of that historical four-piece objective, and the retained D/L chapters now use the distinct algebraic seed constructions. The literal objective/branch identity must be recovered from its original research source before its values and supporting errors can be checked; merely proving subtraction of assumed values would not close that claim.

All eight declarations (seven theorems, one definition) main-build and print only propext, Classical.choice and Quot.sound as transitive axioms. Actual evidence: `OptimizerInterceptExamplesAudit.lean`, `optimizer_intercept_examples_{build,axioms,validation}.log`. This addition follows seventh whole-project milestone f820c46.
