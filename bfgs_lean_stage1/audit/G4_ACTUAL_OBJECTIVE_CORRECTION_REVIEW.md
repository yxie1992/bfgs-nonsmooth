# G.4: actual-objective accessibility distinction

Source: `BFGS_MASTER_REPORT_LaTeX/report/chapters/G.tex`, lines 160–176, and its later shifted-quadratic-plus-absolute-value example. Original sources are preserved.

## Exact objective and acceptance constants

`BfgsVerification/ShiftedAbsAccessibility.lean` uses the existing exact objective

`shiftedAbs t = (t+2)^2/2 + |t|`, `shiftedObjective x = shiftedAbs (x 0)`.

The decisive certificate example fixes `(c₁,c₂)=(1/8,1/4)`. These satisfy the ordinary `0<c₁<c₂<1` restrictions. They differ from the earlier source example `(1/4,1/2)`, where eligible kink crossings and certificate nonexistence were already proved. There is no contradiction between conclusions for different fixed acceptance constants.

The existing source objective is strongly convex, has unique minimizer −1 with value 3/2, and has compact sublevels. The new file proves that zero is nondifferentiable and nonoptimal, and lies in the compact positive band `K={F≤3}`, `η=1/4`.

## Actual pair exclusions and certificates

All endpoint gradients are actual Fréchet derivatives. Differentiability excludes a zero endpoint, and derivative uniqueness yields `g=x+3` on the right and `g=x+1` on the left. For every actual eligible pair with `d≤1/4` and Wolfe constant 1/4:

* A right-to-left crossing would have width at most 1/12. Weak Wolfe would require `g_z≤g_x/4`, but the exact endpoint gradients violate this inequality.
* A left-to-right crossing has `x<−1` by descent. Armijo and `F(z)>2` force `x<−2`, which makes `d>2`, contradicting the small-decrease threshold.

Thus both endpoints are on the same smooth side, and `h−g=z−x` exactly. This proves suppression for `W=I` with `C=1`. Transport holds with `L=0` because the field is constant. Finite convexity and compact positive-band geometry derive a positive uniform lower bound on the gradient, giving visibility. `identityCertificate` constructs the actual constant-I field with `δ=1/4`; `shifted_all_compact_band_certificates` covers every compact K and every positive band, including an empty band without adding a nonemptiness assumption. The crossing proof needs only `c₁>0`; its concrete counterexample uses the valid source constants above.

## Limiting gradients and the two different spans

Two explicit sequences of differentiable points remain in the fixed compact positive band and converge to zero. Their actual gradients converge to 1 and 3. These are genuine limiting active gradients of this objective, rather than an abstract assigned vector family.

Their difference 2 spans the entire one-dimensional Euclidean space. `full_active_tangent_space_eq_bot` proves that the orthogonal complement of their difference span is `{0}`, and `active_common_tangent_zero` proves that both full-active tangent projections vanish. Since these two actual gradients already span all possible difference directions in dimension one, adding any further active gradients cannot restore a tangent direction. The continuous finite field `W=I` still has strictly positive energy on both limiting gradients.

`accessible_jump_zero` quantifies over arbitrary nontrivial filters and arbitrary actual eligible endpoint/gradient families. If the endpoints converge to a common point, their curvature tends to zero, and their gradient difference has a limit, that limit is zero. The proof derives `d→0` from fixed weak Wolfe and then uses the exact small-eligible relation `h−g=z−x`. No assumption that arbitrary active gradients are accessible is inserted.

The final declaration `objective_level_accessibility_counterexample` packages the actual transported certificate, its constant finite continuous extension, all actual gradient sequences and limits inside the positive band, strict limiting visibility, and vanishing common full-active tangent projections. No BFGS trajectory with bad convergence is claimed. Indeed, the previously proved scalar convergence theorem applies to every actual admissible run on this objective.

## Required qualification to the source interpretation

The source correctly says that the certificate range is tangential to **accessible** jump directions and later emphasizes that eligibility can exclude jumps. The intervening sentence “Visibility then requires a nonzero common tangential gradient” cannot use `U=N⊥` for the earlier `N` formed from **all** active differences without an additional spanning/annihilation qualification. The actual objective above disproves that unqualified inference under finite continuous extension alone.

The valid alternatives are: use the orthogonal complement of the accessible-jump span; or require accessible jumps to span the full active-difference space (equivalently, require annihilation of the full space when applying the algebraic visibility lemma). This does not refute the source's explicitly qualified accessible-jump interpretation, the all-difference conditional algebra, or the incoming-jump obstruction. It makes precise why the accessibility qualification is necessary.

## Build and audit

With the pinned environment loaded, run `lake build BfgsVerification.ShiftedAbsAccessibility` and `lake env lean audit/ShiftedAbsAccessibilityAudit.lean`. Actual logs: `audit/shifted_abs_accessibility_build.log` and `audit/shifted_abs_accessibility_axioms.log`.

All 27 explicit declarations are compiled and their transitive axiom lists are checked against exactly `{propext, Classical.choice, Quot.sound}`. No `sorry`, `admit`, custom mathematical axiom, or unchecked external computation is used. Draft attempt logs remain clearly under `audit/scratch/shifted_abs_accessibility`; the library build and axiom logs above are the final artifacts.
