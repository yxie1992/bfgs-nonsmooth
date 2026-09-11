# Independent max-affine statement review

Reviewed `BfgsVerification/MaxAffineBasin.lean` against `BFGS_MASTER_REPORT_LaTeX/report/chapters/families.tex`, lines 51–74. This is a source/statement and proof review, separate from the root compiler/axiom audit.

## Result

No mathematical or hypothesis defect found. The main local and explicit-threshold convergence claims match the source.

- `Family.nonempty` excludes an empty finite maximum, exactly as required by the finite real-valued source objective. `objective` is the actual finite maximum, and `activeGauge` is the actual finite maximum of the slopes active at the optimizer; neither is an assumed representation.
- `local_active_identity` derives the displayed centered identity using strict inactive gaps. The active gauge is proved finite convex and positively homogeneous and is allowed to take negative values, as it must be before recentering. There is no accidental assumption that it is a norm or a nonnegative gauge.
- `inactive_radius_domination` uses the printed Euclidean radius, including equality at the radius. The factor two leaves a strict half-gap. Its nonparallel hypothesis is explicitly separated from `parallel_inactive_domination`, which gives domination everywhere. The slope and displacement norms are explicitly Euclidean, not the default coordinate Pi norm.
- `activeRegion_iff` is algebraically the source system `(a_j-a_i)ᵀx ≥ b_i-b_j`, with the indices/order rearranged. It covers identical and parallel pieces. `badRegion` is exactly the finite union of active regions of indices inactive at the optimizer.
- `threshold` uses an actual `EReal` infimum. `threshold_eq_inactive_infima` proves equality with the nested region infima; `threshold_empty` returns positive infinity. There is no real-infimum empty-set convention hidden in the definition.
- `threshold_attained` derives a finite attained minimum whenever the union is nonempty, using compact sublevels and closedness. `threshold_gt_minimum` derives compact sublevels from finite convexity and the attained unique minimizer; uniqueness excludes the attained point from having optimal value. Empty regions and empty inactive index sets remain covered.
- `threshold_convergence` constructs a strictly larger open convex sublevel still below the threshold. This gives the needed representation neighborhood of the complete compact initial sublevel; it does not assume the local identity there. `LocallyC11On univ ψ` means differentiability and local derivative Lipschitz regularity at every point, not one global Lipschitz constant. This agrees with the source's convex locally C1,1 smooth summand.
- `threshold_tail_convergence` uses the actual shifted admissible run with its current metric. No restart, metric change, convergence premise, active-set identification, or BFGS invariance under an objective transform is introduced.

The phrase “each inner infimum is a convex program” is represented by an actual finite convex objective and the displayed linear-inequality feasible set. After this review, the root also exported `activeRegion_convex`, derived directly from those inequalities, so the sole descriptive non-export identified in the initial review is closed. No claim is made that the sufficient threshold characterizes all convergent starts.
