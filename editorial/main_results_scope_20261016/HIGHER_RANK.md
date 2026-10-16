# Higher-rank certificate calibration

**Result: verified analytically and compiled in scratch Lean, 16 October 2026.**
The construction works in every finite dimension, so in particular in dimension
two with a genuinely rank-two certificate. It is additional calibration evidence,
not an assertion that this example was already present in the released package.
The completed existing-evidence `formal/REVIEW.md` has not been rewritten.

## Analytic verification

Let

\[
F(x)=\tfrac12\|x\|_2^2,\qquad F_*=0,\qquad
K=\{x:F(x)\le b\},\quad b>0.
\]

The objective is finite, convex and differentiable everywhere, with full-space
Euclidean gradient \(g(x)=x\), unique minimizer zero and compact sublevels.
For every \(\eta>0\), take

\[
W_\eta(x)=I_n,\qquad m_\eta=2\eta,\qquad
C_\eta=1,\quad L_\eta=0,\quad\delta_\eta=1.
\]

These satisfy the band-certificate definition:

1. **Positivity and visibility.** \(W_\eta\succ0\),
   \(\operatorname{rank}W_\eta=n\), and on \(K_\eta\),
   \[
   g(x)^TW_\eta(x)g(x)=\|x\|_2^2=2F(x)\ge2\eta.
   \]
2. **Exact secant control.** At any endpoints \(x,z\), write
   \(s=z-x\) and \(y=g(z)-g(x)=s\). Then
   \[
   y^TW_\eta(z)y=\|s\|_2^2=y^Ts=t=C_\eta t.
   \]
3. **Exact projected transport.** For every \(s\),
   \[
   \Pi_sW_\eta(z)\Pi_s=\Pi_sI_n\Pi_s
     =(1+0d)\Pi_sW_\eta(x)\Pi_s.
   \]

The last two identities hold for all endpoint pairs, so in particular for all
eligible pairs with \(d\le\delta_\eta\). In dimension at least two the projected
field need not vanish: in the plane, for \(s=e_1\), it is
\(\operatorname{diag}(0,1)\). Thus this does not rely on the scalar identity
\(\Pi_s=0\).

### An actual infinite admissible full-BFGS run

For any prescribed nonzero \(x_0\in\mathbb R^n\), define

\[
x_k=2^{-k}x_0,\quad g_k=x_k,\quad H_k=I_n,\quad
\alpha_k=\tfrac12,\qquad c_1=\tfrac14,\ c_2=\tfrac12.
\]

The search step and secant are

\[
s_k=-\tfrac12x_k=x_{k+1}-x_k=y_k,\qquad
q_k=\|x_k\|_2^2>0,\quad t_k=\tfrac14q_k>0.
\]

Put \(P_k=s_ks_k^T/(s_k^Ts_k)\). Since \(P_k^2=P_k\), the **full** inverse-BFGS
update is exactly

\[
H_{k+1}=(I-P_k)I(I-P_k)+P_k=I.
\]

Moreover,

\[
d_k=\tfrac12q_k,\qquad
\Delta_k=F(x_k)-F(x_{k+1})=\tfrac38q_k,
\]
\[
\frac{\Delta_k}{d_k}=\frac34>c_1,\qquad
g_{k+1}^Ts_k=-\tfrac14q_k=c_2g_k^Ts_k.
\]

Thus Armijo holds strictly and weak Wolfe holds **with equality**, which is
permitted by the article's admissible-run definition. Every gradient is
nonzero and every accepted point is differentiable. Taking \(b=F(x_0)>0\)
gives the compact initial sublevel containing the entire run, and

\[
F(x_k)=4^{-k}F(x_0)\longrightarrow0,\qquad x_k\longrightarrow0.
\]

The witness has identity initialization and the displayed fixed constants;
it is not an arbitrary-prescribed-SPD-initialization existence assertion.
The orbit lies on a ray, but the certificate conditions are proved on the
full-dimensional objective's bands for **all** eligible endpoint pairs.
This illustrates permitted matrix rank, without asserting that higher rank
is necessary for this objective or that the example is novel.

## Scratch Lean evidence

Files in this directory:
- `HigherRank.lean` — the complete new scratch construction.
- `HigherRank.log` — successful compilation output, signatures and axiom checks.

The proof uses the repository's `Vec n = Fin n → ℝ`, but the objective is
defined with `sqNorm`, not the squared Pi/sup norm.
`HigherRankCalibration.objective_euclidean` explicitly proves
`objective x = ‖euclideanVector x‖ ^ 2 / 2`.
`objective_hasGradient` proves full-space `HasFDerivAt` with
`gradientFunctional x`.

### Principal declarations

All names below are in namespace `HigherRankCalibration`; line numbers refer
to the scratch `HigherRank.lean`.

| Full Lean name | Line | Content |
|---|---:|---|
| `HigherRankCalibration.objective_euclidean` | 26 | Explicit Euclidean objective identity |
| `HigherRankCalibration.objective_hasGradient` | 35 | Actual full-space gradient equals `x` |
| `HigherRankCalibration.sublevel_compact` | 60 | Compactness of every sublevel |
| `HigherRankCalibration.certificate` | 66 | `BandCertificate` with the proposed constants, for every dimension and any set `K` |
| `HigherRankCalibration.certificate_parameters` | 89 | Exact field/constants; field SPD and matrix rank exactly `n` everywhere |
| `HigherRankCalibration.exact_field_equalities` | 97 | Secant-control and projected-transport equalities for all endpoint pairs |
| `HigherRankCalibration.inverseBFGS_identity` | 111 | `inverseBFGS (1 : Mat n) s s = 1` |
| `HigherRankCalibration.run` | 155 | Actual infinite admissible run, for every nonzero `x₀` |
| `HigherRankCalibration.run_values` | 178 | Exact geometric-decay objective formula |
| `HigherRankCalibration.joint_witness` | 183 | Run, initialization/constants, compact positive sublevel, attained minimum, all positive-band full-rank certificates and convergence, jointly |
| `HigherRankCalibration.planar_projection` | 217 | Projected identity field equals `diag(0,1)` for the planar direction `e₁` |

The joint theorem holds for arbitrary `n` and `x₀ ≠ 0`; choosing `n=2` and
`x₀=(1,1)` gives a rank-two witness. The certificate constructor itself does
not need valid line-search constants because its inequalities hold for all
pairs. The actual run uses exactly `(1/4,1/2)`.

The convergence conjuncts of `joint_witness` are obtained by applying the
existing `BfgsCoverage.Article.Energy.certificate` theorem to the newly
constructed run and certificates. The exact value formula independently
exhibits geometric decay.

### Compilation and axioms

Successful command, run from `bfgs_lean_article/`:

```sh
PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=4 lake env lean \
  /private/var/folders/9b/7wlx7vjd6rg6pzlh3tgrmyyw0000gn/T/opencode/assumptions_20261016/higher_rank/HigherRank.lean
```

Exit status **0**, with no errors or warnings. Six `#print axioms` checks
(`certificate`, `certificate_parameters`, `inverseBFGS_identity`, `run`,
`joint_witness`, `planar_projection`) each report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The scratch proof required only existing APIs and short algebraic helpers.
It used the identity example directly, rather than the alternative spatial
quadratic with `Q=diag(1,2,3)` and field `Q⁻¹`. No repository edits or git
commands were used in this follow-up; Lean checks ran sequentially, one
process at a time.

## Suggested short analytic paragraph

For a full-rank calibration, let \(F(x)=\|x\|_2^2/2\) in dimension \(n\ge2\).
On every positive band the constant field \(W_\eta=I_n\) is a certificate
with \(m_\eta=2\eta\), \(C_\eta=1\), \(L_\eta=0\), \(\delta_\eta=1\):
visibility is \(\|x\|_2^2\ge2\eta\), and both secant control and projected
transport are equalities because \(y=s\) and the field is constant.
For every nonzero \(x_0\), the sequences \(x_k=2^{-k}x_0\), \(H_k=I_n\),
\(\alpha_k=1/2\) form an infinite admissible full-BFGS run with
\((c_1,c_2)=(1/4,1/2)\). The full update fixes \(I_n\); the Armijo ratio is
\(3/4\) and weak Wolfe holds with equality. This supplies an elementary
higher-rank illustration, without asserting that such rank is necessary.
