import BfgsArticle.HypothesisExamples
import BfgsArticle.TwoQuadraticExample
import BfgsArticle.AdmissibleRunExistence

/-!
# Literal coverage: checking hypotheses on actual runs

Source: `paper/appendices/hypothesis_examples.tex`. Register:
`editorial/lean_coverage/register/A_hypothesis_examples.json`.

The six named results are covered by the statement sets below. In particular,
`mixed_certificates` retains every `b > 0`, while `mixed_history` joins the
certificate to the displayed actual run at `b = 2/3`. `mixed_smallest_eigenvalue`
identifies the least Euclidean Rayleigh value, attained at the unit eigenvector
`(0,1)`, and its limit; a singular matrix limit alone would not state this claim.
`mixed_least_spectrum` and `mixed_spectral_limit` also identify this value
directly as the least element of the actual real matrix spectrum and give its limit.
`quadratic_certificates` handles every positive sublevel, and `quadratic_history`
joins the full-rank certificate to the run from each prescribed nonzero start.

## Shared mathematical conventions

* `Vec n = Fin n → ℝ` carries the Pi norm, but every squared Euclidean norm
  here is `sqNorm x = ∑ i, (x i)^2`, or `‖euclideanVector x‖^2`.
* A finite objective is a total function to `ℝ`. Actual ambient gradients are
  `HasFDerivAt F (gradientFunctional g) x`, with `gradientFunctional g v = dot g v`.
* `AdmissibleBFGSRun n F` includes convexity, actual nonzero gradients at every
  accepted point, positive lengths, an initially SPD matrix, the unmodified
  inverse-BFGS update, and both Armijo and weak Wolfe for fixed valid constants.
  Thus every existential run below supplies all these facts for the same `F`.
* `BandCertificate F K 0 c₁ c₂ η` has `m > 0`, `L ≥ 0`, `δ > 0`, a symmetric
  PSD field on differentiable points of `{x ∈ K | η ≤ F x}`, visibility there,
  and secant/projected-transport inequalities for all eligible pairs in that
  band with `d ≤ δ`. The displayed witnesses additionally state `C ≥ 0`, which
  the library record does not require. Eligibility includes actual endpoint
  gradients, `d = -gᵀ(z-x) > 0`, `c₁d ≤ F(x)-F(z) ≤ d`, and
  `(1-c₂)d ≤ (h-g)ᵀ(z-x)`. The projector is `I - ssᵀ / sqNorm s`.
* `metricEnergy H v = vᵀHv`, `outer x x = xxᵀ`, and `(1/2)^k = 2^{-k}`.

The two-quadratic hypothesis records are unfolded below. The literal planar
neighborhood alternative is stated separately from the native library record.
No objective, geometry, certificate, or run-existence condition is assumed for
any of the concrete examples: only its printed parameter/initialization
conditions are premises.
-/

noncomputable section
open Set Filter Matrix BfgsVerification
open BfgsVerification.HypothesisExamples
open scoped BigOperators Topology ContDiff

namespace BfgsCoverage.Article.HypothesisExamples

/-- Item `A/hypothesis_examples/proposition/art:examples-mixed`
(`paper/appendices/hypothesis_examples.tex:12-30`): for every `b > 0`,
`F(u,v)=u²+|v|` is finite convex, has unique minimum zero and compact `K_b`.
For every `0 < η ≤ b` the certificate is `W(x)=xxᵀ`, `m=η²`, `C=2b`,
`L=0`, `δ=1`, including every sign condition of Definition `art:band-certificate`.
The valid constants are arbitrary; the witness is stronger and works for any constants. -/
theorem mixed_certificates (b : ℝ) (hb : 0 < b) (c₁ c₂ : ℝ)
    (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1) :
    (∀ x : Vec 2, Mixed.objective x = (x 0) ^ 2 + |x 1|) ∧
      ConvexOn ℝ univ Mixed.objective ∧ IsLeast (range Mixed.objective) 0 ∧
      (∀ x, Mixed.objective x = 0 ↔ x = 0) ∧
      IsCompact {x : Vec 2 | Mixed.objective x ≤ b} ∧
      ∀ η : ℝ, 0 < η → η ≤ b →
        ∃ B : TransportedCertificate.BandCertificate Mixed.objective
            {x | Mixed.objective x ≤ b} 0 c₁ c₂ η,
          B.W = (fun x => outer x x) ∧ B.m = η ^ 2 ∧ B.C = 2 * b ∧
            B.L = 0 ∧ B.δ = 1 ∧ 0 ≤ B.C := by
  exact ⟨Mixed.objective_formula, Mixed.objective_convex, Mixed.objective_minimum,
    Mixed.objective_eq_zero_iff, Mixed.sublevel_compact b,
    fun η hη _ => ⟨Mixed.certificate b c₁ c₂ η hη,
      Mixed.certificate_parameters hb c₁ c₂ η hη⟩⟩

/-- Item `A/hypothesis_examples/proposition/art:examples-mixed`
(`paper/appendices/hypothesis_examples.tex:12-30`): the smallest eigenvalue
of the displayed `H_k = diag(1,2^{-k})` is `2^{-k}`, and tends to zero.
Precisely, this is the least value of `vᵀH_kv` on the Euclidean unit sphere,
attained at the unit eigenvector `(0,1)`. -/
theorem mixed_smallest_eigenvalue :
    (∀ k : ℕ,
      IsLeast ((fun v : Vec 2 => metricEnergy (Mixed.run.H k) v) ''
        {v : Vec 2 | sqNorm v = 1}) ((1 / 2 : ℝ) ^ k) ∧
      sqNorm (![0, 1] : Vec 2) = 1 ∧
      (Mixed.run.H k) *ᵥ (![0, 1] : Vec 2) =
        ((1 / 2 : ℝ) ^ k) • (![0, 1] : Vec 2)) ∧
      Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
  refine ⟨fun k => ?_,
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)⟩
  have hunit : sqNorm (![0, 1] : Vec 2) = 1 := by
    norm_num [sqNorm, Fin.sum_univ_two]
  have he : metricEnergy (Mixed.run.H k) (![0, 1] : Vec 2) = (1 / 2 : ℝ) ^ k := by
    rw [Mixed.run_matrices]
    simp [metricEnergy, dot, Fin.sum_univ_two, Matrix.mulVec_diagonal]
  refine ⟨⟨⟨![0, 1], hunit, he⟩, ?_⟩, hunit, ?_⟩
  · rintro r ⟨v, hv, rfl⟩
    have hp : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hnonneg := mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg (v 0))
    simp only [mem_setOf_eq, sqNorm, Fin.sum_univ_two] at hv
    have hscaled := congrArg (fun r : ℝ => ((1 / 2 : ℝ) ^ k) * r) hv
    rw [Mixed.run_matrices]
    simp only [metricEnergy, dot, Fin.sum_univ_two, Matrix.mulVec_diagonal,
      Pi.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    nlinarith only [hscaled, hnonneg]
  · rw [Mixed.run_matrices]
    ext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal]

/-- Item `A/hypothesis_examples/proposition/art:examples-mixed`
(`paper/appendices/hypothesis_examples.tex:12-30`): the smallest eigenvalue
of the displayed `H_k = diag(1,2^{-k})` is `2^{-k}`. Directly in Mathlib's
real matrix spectrum, `2^{-k}` is its least element. -/
theorem mixed_least_spectrum (k : ℕ) :
    IsLeast (spectrum ℝ (Mixed.run.H k)) ((1 / 2 : ℝ) ^ k) := by
  rw [Mixed.run_matrices, spectrum_diagonal]
  refine ⟨⟨1, rfl⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact pow_le_one₀ (by norm_num) (by norm_num)
  · exact le_rfl

/-- Item `A/hypothesis_examples/proposition/art:examples-mixed`
(`paper/appendices/hypothesis_examples.tex:12-30`): the least actual spectral
value of every displayed `H_k` is `2^{-k}`, and these values tend to zero. -/
theorem mixed_spectral_limit :
    (∀ k, IsLeast (spectrum ℝ (Mixed.run.H k)) ((1 / 2 : ℝ) ^ k)) ∧
      Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
  ⟨mixed_least_spectrum, mixed_smallest_eigenvalue.2⟩

/-- Item `A/hypothesis_examples/proposition/art:examples-mixed`
(`paper/appendices/hypothesis_examples.tex:12-30`): all objective and certificate
hypotheses hold jointly with the printed actual full-BFGS history in `K_{2/3}`,
with `(c₁,c₂)=(1/4,1/2)`, `H₀=I`, and convergence despite the vanishing
least eigenvalue. The certificate and the history refer to this same objective,
sublevel and line-search pair. -/
theorem mixed_history :
    ConvexOn ℝ univ Mixed.objective ∧ IsLeast (range Mixed.objective) 0 ∧
      (∀ x, Mixed.objective x = 0 ↔ x = 0) ∧
      IsCompact {x : Vec 2 | Mixed.objective x ≤ 2 / 3} ∧
      ∃ R : AdmissibleBFGSRun 2 Mixed.objective,
        R.x 0 = ![0, 2 / 3] ∧ R.H 0 = 1 ∧ R.c₁ = 1 / 4 ∧ R.c₂ = 1 / 2 ∧
        (∀ k, R.x k = ![0, (2 / 3) * (-1 / 2 : ℝ) ^ k] ∧
          R.g k = ![0, (-1 : ℝ) ^ k] ∧
          R.H k = Matrix.diagonal ![1, (1 / 2 : ℝ) ^ k] ∧ R.α k = 1) ∧
        (∀ k, Mixed.objective (R.x k) ≤ 2 / 3) ∧
        (∀ η : ℝ, 0 < η → η ≤ 2 / 3 →
          ∃ B : TransportedCertificate.BandCertificate Mixed.objective
              {x | Mixed.objective x ≤ 2 / 3} 0 R.c₁ R.c₂ η,
            B.W = (fun x => outer x x) ∧ B.m = η ^ 2 ∧ B.C = 2 * (2 / 3) ∧
              B.L = 0 ∧ B.δ = 1 ∧ 0 ≤ B.C) ∧
        (∀ k, IsLeast ((fun v : Vec 2 => metricEnergy (R.H k) v) ''
          {v : Vec 2 | sqNorm v = 1}) ((1 / 2 : ℝ) ^ k)) ∧
        Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) ∧
        Tendsto (fun k => Mixed.objective (R.x k)) atTop (𝓝 0) ∧
        Tendsto R.x atTop (𝓝 0) := by
  refine ⟨Mixed.objective_convex, Mixed.objective_minimum, Mixed.objective_eq_zero_iff,
    Mixed.sublevel_compact _, Mixed.run, Mixed.run_initial.1, Mixed.run_initial.2,
    Mixed.run_constants.1, Mixed.run_constants.2.1,
    fun k => ⟨Mixed.run_points k, Mixed.run_gradients k, Mixed.run_matrices k,
      Mixed.run_constants.2.2 k⟩, ?_, ?_,
    fun k => (mixed_smallest_eigenvalue.1 k).1, mixed_smallest_eigenvalue.2,
    Mixed.run_limits.2, Mixed.run_limits.1⟩
  · intro k
    simpa only [Mixed.run_values, pow_zero, mul_one] using Mixed.run.objective_le_initial k
  · intro η hη _
    exact ⟨Mixed.certificate (2 / 3) _ _ η hη,
      Mixed.certificate_parameters (by norm_num) _ _ η hη⟩

/-- Item `A/hypothesis_examples/disp/003`
(`paper/appendices/hypothesis_examples.tex:37-40`): for differentiable endpoints
`x=(u,v), z=(r,w)` of the mixed ridge in `K_b`, when `v,w` have the same sign,
`t=2(r-u)²`, `yᵀz=2(r-u)r`, and `(yᵀz)² ≤ 2F(z)t`.
Here `y=h-g` and `t=yᵀ(z-x)` are variables with their defining equations.
The identities hold on all of `K_b`, without positive-band or eligibility restrictions. -/
theorem mixed_same_sign_secants (b : ℝ) (_hb : 0 < b) (x z g h : Vec 2)
    (_hxK : Mixed.objective x ≤ b) (_hzK : Mixed.objective z ≤ b)
    (hg : HasFDerivAt Mixed.objective (gradientFunctional g) x)
    (hh : HasFDerivAt Mixed.objective (gradientFunctional h) z)
    (y : Vec 2) (hy : y = h - g) (t : ℝ) (ht : t = dot y (z - x))
    (hsign : (0 < x 1 ∧ 0 < z 1) ∨ (x 1 < 0 ∧ z 1 < 0)) :
    t = 2 * (z 0 - x 0) ^ 2 ∧ dot y z = 2 * (z 0 - x 0) * z 0 ∧
      (dot y z) ^ 2 ≤ 2 * Mixed.objective z * t := by
  subst hy ht
  have hbound := Mixed.secant_bound (b := Mixed.objective z) le_rfl hg hh
  refine ⟨?_, ?_, hbound⟩
  all_goals
    rcases hsign with ⟨hx, hz⟩ | ⟨hx, hz⟩
    · rw [Mixed.gradient_eq_of_nonneg hx.le hg, Mixed.gradient_eq_of_nonneg hz.le hh]
      simp only [dot, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring
    · rw [Mixed.gradient_eq_of_nonpos hx.le hg, Mixed.gradient_eq_of_nonpos hz.le hh]
      simp only [dot, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring

/-- Item `A/hypothesis_examples/disp/004`
(`paper/appendices/hypothesis_examples.tex:42-44`): for opposite signs and
`S=|v|+|w|>0`, `t=2(r-u)²+2S`, `yᵀz=2(r-u)r+2|w|`.
The same full-space differentiable-endpoint assumptions as in display 003 apply. -/
theorem mixed_opposite_sign_secants (b : ℝ) (_hb : 0 < b) (x z g h : Vec 2)
    (_hxK : Mixed.objective x ≤ b) (_hzK : Mixed.objective z ≤ b)
    (hg : HasFDerivAt Mixed.objective (gradientFunctional g) x)
    (hh : HasFDerivAt Mixed.objective (gradientFunctional h) z)
    (y : Vec 2) (hy : y = h - g) (t : ℝ) (ht : t = dot y (z - x))
    (S : ℝ) (hS : S = |x 1| + |z 1|)
    (hsign : (0 < x 1 ∧ z 1 < 0) ∨ (x 1 < 0 ∧ 0 < z 1)) :
    0 < S ∧ t = 2 * (z 0 - x 0) ^ 2 + 2 * S ∧
      dot y z = 2 * (z 0 - x 0) * z 0 + 2 * |z 1| := by
  have hpos : 0 < S := by
    rw [hS]
    exact add_pos_of_nonneg_of_pos (abs_nonneg _)
      (abs_pos.mpr (Mixed.differentiable_coordinate_ne_zero hh.differentiableAt))
  refine ⟨hpos, ?_⟩
  subst hy ht hS
  rcases hsign with ⟨hx, hz⟩ | ⟨hx, hz⟩
  · rw [Mixed.gradient_eq_of_nonneg hx.le hg, Mixed.gradient_eq_of_nonpos hz.le hh]
    simp only [dot, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, abs_of_nonneg hx.le, abs_of_nonpos hz.le]
    constructor <;> ring
  · rw [Mixed.gradient_eq_of_nonpos hx.le hg, Mixed.gradient_eq_of_nonneg hz.le hh]
    simp only [dot, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, abs_of_nonpos hx.le, abs_of_nonneg hz.le]
    constructor <;> ring

/-- Item `A/hypothesis_examples/disp/005`
(`paper/appendices/hypothesis_examples.tex:46-49`): the complete weighted
Cauchy--Schwarz chain, with its printed intermediate expression:
`(yᵀz)² ≤ t(2r²+2|w|²/S) ≤ 2F(z)t ≤ 2bt`. -/
theorem mixed_crossing_cauchy (b : ℝ) (hb : 0 < b) (x z g h : Vec 2)
    (hxK : Mixed.objective x ≤ b) (hzK : Mixed.objective z ≤ b)
    (hg : HasFDerivAt Mixed.objective (gradientFunctional g) x)
    (hh : HasFDerivAt Mixed.objective (gradientFunctional h) z)
    (y : Vec 2) (hy : y = h - g) (t : ℝ) (ht : t = dot y (z - x))
    (S : ℝ) (hS : S = |x 1| + |z 1|)
    (hsign : (0 < x 1 ∧ z 1 < 0) ∨ (x 1 < 0 ∧ 0 < z 1)) :
    (dot y z) ^ 2 ≤ t * (2 * (z 0) ^ 2 + 2 * |z 1| ^ 2 / S) ∧
      t * (2 * (z 0) ^ 2 + 2 * |z 1| ^ 2 / S) ≤ 2 * Mixed.objective z * t ∧
      2 * Mixed.objective z * t ≤ 2 * b * t := by
  obtain ⟨hSpos, htval, hyval⟩ :=
    mixed_opposite_sign_secants b hb x z g h hxK hzK hg hh y hy t ht S hS hsign
  have htpos : 0 < t := by rw [htval]; positivity
  have hid :
      (2 * (z 0 - x 0) ^ 2 + 2 * S) * (2 * (z 0) ^ 2 + 2 * |z 1| ^ 2 / S) -
        (2 * (z 0 - x 0) * z 0 + 2 * |z 1|) ^ 2 =
      4 / S * ((z 0 - x 0) * |z 1| - S * z 0) ^ 2 := by
    field_simp [hSpos.ne']
    ring_nf
    simp only [sq_abs]
    ring
  have hcs : 0 ≤
      (2 * (z 0 - x 0) ^ 2 + 2 * S) * (2 * (z 0) ^ 2 + 2 * |z 1| ^ 2 / S) -
        (2 * (z 0 - x 0) * z 0 + 2 * |z 1|) ^ 2 := by
    rw [hid]
    positivity
  have hquot : |z 1| ^ 2 / S ≤ |z 1| := by
    apply (div_le_iff₀ hSpos).mpr
    rw [hS]
    nlinarith [mul_nonneg (abs_nonneg (z 1)) (abs_nonneg (x 1))]
  have hcoeff : 2 * (z 0) ^ 2 + 2 * |z 1| ^ 2 / S ≤ 2 * Mixed.objective z := by
    rw [Mixed.objective_formula, mul_div_assoc]
    linarith only [hquot]
  refine ⟨?_, ?_, ?_⟩
  · rw [htval, hyval]
    linarith only [hcs]
  · nlinarith [mul_le_mul_of_nonneg_left hcoeff htpos.le]
  · nlinarith [mul_le_mul_of_nonneg_right hzK htpos.le]

/-- Item `A/hypothesis_examples/disp/006`
(`paper/appendices/hypothesis_examples.tex:54-57`): on the printed mixed history,
`d_k=2^{-k}`, `F(x_k)-F(x_{k+1})=d_k/3`, and `t_k=2d_k`. -/
theorem mixed_history_scalars (k : ℕ) :
    Mixed.run.d k = (1 / 2 : ℝ) ^ k ∧
      Mixed.objective (Mixed.run.x k) - Mixed.objective (Mixed.run.x (k + 1)) =
        (1 / 3) * Mixed.run.d k ∧
      Mixed.run.curvature k = 2 * Mixed.run.d k := by
  obtain ⟨hd, hΔ, ht⟩ := Mixed.run_scalars k
  exact ⟨hd, by simpa only [hd] using hΔ, by simpa only [hd] using ht⟩

/-- Item `A/hypothesis_examples/proposition/art:examples-full-rank`
(`paper/appendices/hypothesis_examples.tex:64-76`): the Euclidean objective
`F(x)=‖x‖₂²/2` has unique minimum zero and compact positive sublevels in every
dimension `n ≥ 1`. On every `0 < η ≤ b` the field is `I`, with constants
`2η,1,0,1`, is positive definite, and has rank exactly `n`. -/
theorem quadratic_certificates {n : ℕ} (_hn : 1 ≤ n) (b : ℝ) (_hb : 0 < b)
    (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1) :
    (∀ x : Vec n, Quadratic.objective x = ‖euclideanVector x‖ ^ 2 / 2) ∧
      ConvexOn ℝ univ (@Quadratic.objective n) ∧
      IsLeast (range (@Quadratic.objective n)) 0 ∧
      (∀ x : Vec n, Quadratic.objective x = 0 ↔ x = 0) ∧
      IsCompact {x : Vec n | Quadratic.objective x ≤ b} ∧
      ∀ η : ℝ, 0 < η → η ≤ b →
        ∃ B : TransportedCertificate.BandCertificate (@Quadratic.objective n)
            {x | Quadratic.objective x ≤ b} 0 c₁ c₂ η,
          B.W = (fun _ => 1) ∧ B.m = 2 * η ∧ B.C = 1 ∧ B.L = 0 ∧ B.δ = 1 ∧
            0 ≤ B.C ∧ ∀ x, (B.W x).PosDef ∧ (B.W x).rank = n := by
  exact ⟨Quadratic.objective_euclidean, Quadratic.objective_convex,
    Quadratic.objective_minimum, Quadratic.objective_eq_zero_iff,
    Quadratic.sublevel_compact b, fun η hη _ =>
      ⟨Quadratic.certificate _ c₁ c₂ η hη, Quadratic.certificate_parameters _ c₁ c₂ η hη⟩⟩

/-- Item `A/hypothesis_examples/proposition/art:examples-full-rank`
(`paper/appendices/hypothesis_examples.tex:64-76`): for each prescribed `x₀ ≠ 0`,
the same Euclidean objective, sublevel, full-rank certificates, identity matrices
and actual-gradient full-BFGS history hold together. Its exact history is
`x_k=2^{-k}x₀`, `g_k=x_k`, `H_k=I`, `α_k=1/2`, with constants `(1/4,1/2)`;
it stays in `K_{F(x₀)}` and converges to zero. -/
theorem quadratic_history {n : ℕ} (_hn : 1 ≤ n) (x₀ : Vec n) (hx₀ : x₀ ≠ 0) :
    ConvexOn ℝ univ (@Quadratic.objective n) ∧
      (∀ x : Vec n, Quadratic.objective x = 0 ↔ x = 0) ∧
      ∃ (R : AdmissibleBFGSRun n Quadratic.objective) (b : ℝ),
        R.x 0 = x₀ ∧ R.H = (fun _ => 1) ∧ R.c₁ = 1 / 4 ∧ R.c₂ = 1 / 2 ∧
        (∀ k, R.x k = ((1 / 2 : ℝ) ^ k) • x₀ ∧ R.g k = R.x k ∧ R.α k = 1 / 2) ∧
        b = Quadratic.objective x₀ ∧ 0 < b ∧
        IsCompact {x : Vec n | Quadratic.objective x ≤ b} ∧
        IsLeast (range (@Quadratic.objective n)) 0 ∧ Quadratic.objective (R.x 0) ≤ b ∧
        (∀ k, Quadratic.objective (R.x k) ≤ b) ∧
        (∀ η : ℝ, 0 < η →
          ∃ B : TransportedCertificate.BandCertificate (@Quadratic.objective n)
              {x | Quadratic.objective x ≤ b} 0 R.c₁ R.c₂ η,
            B.W = (fun _ => 1) ∧ B.m = 2 * η ∧ B.C = 1 ∧ B.L = 0 ∧ B.δ = 1 ∧
              0 ≤ B.C ∧ ∀ x, (B.W x).PosDef ∧ (B.W x).rank = n) ∧
        Tendsto (fun k => Quadratic.objective (R.x k)) atTop (𝓝 0) ∧
        Tendsto R.x atTop (𝓝 0) :=
  Quadratic.joint_witness x₀ hx₀

/-- Item `A/hypothesis_examples/proof/002`
(`paper/appendices/hypothesis_examples.tex:77-85`): on the stated quadratic run,
the actual decrease is `3d_k/4` and weak Wolfe is equality. The actual-gradient,
identity-update, secant and transport equalities are also supplied by the core
declarations cited in this proof's register item. -/
theorem quadratic_history_decrease {n : ℕ} (x₀ : Vec n) (hx₀ : x₀ ≠ 0) (k : ℕ) :
    let R := Quadratic.run x₀ hx₀
    Quadratic.objective (R.x k) - Quadratic.objective (R.x (k + 1)) =
        (3 / 4) * R.d k ∧
      dot (R.g (k + 1)) (R.displacement k) = R.c₂ * dot (R.g k) (R.displacement k) := by
  dsimp only
  obtain ⟨_, hd, hΔ, _⟩ := Quadratic.run_scalars x₀ hx₀ k
  exact ⟨by rw [hd, hΔ]; ring, Quadratic.run_weak_wolfe_eq x₀ hx₀ k⟩

/-- Item `A/hypothesis_examples/lemma/art:examples-run-existence`
(`paper/appendices/hypothesis_examples.tex:89-101`): the exceptional set is the
set of failures of full-space differentiability on every line through a
differentiability point. At any actual nonzero gradient and SPD `H`, `p=-Hg`
admits a positive differentiable endpoint with strict Armijo and strict weak Wolfe.
The Wolfe pairing is with the direction `p`, as in the printed proof. -/
theorem strict_wolfe_step {n : ℕ} (_hn : 1 ≤ n) {F : Vec n → ℝ}
    (hconv : ConvexOn ℝ univ F) (hbdd : BddBelow (range F))
    (hline : ∀ x p : Vec n, DifferentiableAt ℝ F x → p ≠ 0 →
      {t : ℝ | ¬ DifferentiableAt ℝ F (x + t • p)}.Countable)
    {x g : Vec n} (hg : HasFDerivAt F (gradientFunctional g) x) (hg0 : g ≠ 0)
    {H : Mat n} (hH : H.PosDef) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1)
    (p : Vec n) (hp : p = -(H *ᵥ g)) :
    ∃ α : ℝ, 0 < α ∧ ∃ h : Vec n,
      HasFDerivAt F (gradientFunctional h) (x + α • p) ∧
      F (x + α • p) < F x + c₁ * α * dot g p ∧ c₂ * dot g p < dot h p := by
  obtain ⟨α, hα, h, hh, harm, hw⟩ :=
    AdmissibleRunExistence.exists_wolfe_step hconv hbdd hline hg hg0 hH hc₁ hc₁₂ hc₂
  have hs : bfgsStep H g α = α • p := by simp [bfgsStep, hp, neg_smul, smul_neg]
  rw [hs] at hh harm hw
  rw [dot_smul_right] at harm
  rw [dot_smul_right, dot_smul_right] at hw
  refine ⟨α, hα, h, hh, ?_, ?_⟩
  · nlinarith only [harm]
  · apply (mul_lt_mul_left hα).mp
    nlinarith only [hw]

/-- Item `A/hypothesis_examples/lemma/art:examples-run-existence`
(`paper/appendices/hypothesis_examples.tex:89-101`): with the same full-space
line condition and no differentiable stationary point, every differentiable
`x₀`, every SPD `H₀`, and every `0<c₁<c₂<1` admit an infinite actual-gradient
full-BFGS run with exactly these initial data and constants. -/
theorem admissible_run_exists {n : ℕ} (_hn : 1 ≤ n) {F : Vec n → ℝ}
    (hconv : ConvexOn ℝ univ F) (hbdd : BddBelow (range F))
    (hline : ∀ x p : Vec n, DifferentiableAt ℝ F x → p ≠ 0 →
      {t : ℝ | ¬ DifferentiableAt ℝ F (x + t • p)}.Countable)
    (hstat : ∀ x g, HasFDerivAt F (gradientFunctional g) x → g ≠ 0)
    {x₀ : Vec n} (hx₀ : DifferentiableAt ℝ F x₀) {H₀ : Mat n} (hH₀ : H₀.PosDef)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun n F,
      R.x 0 = x₀ ∧ R.g 0 = coordinateGradient F x₀ ∧ R.H 0 = H₀ ∧
        R.c₁ = c₁ ∧ R.c₂ = c₂ :=
  AdmissibleRunExistence.exists_admissible_run hconv hbdd hline hstat
    (hasFDerivAt_coordinateGradient hx₀) hH₀ hc₁ hc₁₂ hc₂

/-- Item `A/hypothesis_examples/disp/009`
(`paper/appendices/hypothesis_examples.tex:124-126`): the definition of the
two-quadratic objective, with its coefficients in the original coordinates. -/
theorem two_quadratic_formula (a b c : ℝ) (x : Vec 2) :
    TwoQuadraticExample.objective a b c x =
      max (a * (x 0) ^ 2 + b * (x 1) ^ 2 + x 1)
        (c * (x 0) ^ 2 + b * (x 1) ^ 2 - x 1) := rfl

/-- Item `A/hypothesis_examples/proposition/art:examples-two-quadratics`
(`paper/appendices/hypothesis_examples.tex:122-135`): unfold the new
`PaperRegularAt` predicate. It is the literal smooth-neighborhood or convex
two-active-`C²`-branch alternative, with independent actual branch gradients. -/
theorem paperRegularAt_iff (F : Vec 2 → ℝ) (p : Vec 2) :
    TwoQuadraticExample.PaperRegularAt F p ↔
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₀ f₁ : Vec 2 → ℝ,
        ConvexOn ℝ V f₀ ∧ ConvexOn ℝ V f₁ ∧ ContDiffOn ℝ 2 f₀ V ∧ ContDiffOn ℝ 2 f₁ V ∧
        (∀ z ∈ V, F z = max (f₀ z) (f₁ z)) ∧ f₀ p = F p ∧ f₁ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₀ p, coordinateGradient f₁ p]) := Iff.rfl

/-- Item `A/hypothesis_examples/proposition/art:examples-two-quadratics`
(`paper/appendices/hypothesis_examples.tex:122-135`): unfold every field of the
new native `PlanarHypotheses` record used by the joint witness. Affine criticality
uses the affine hull of the actual convex subdifferential; correctness means
that an affine-critical point has zero in that subdifferential. The native
regularity alternative is complemented by the literal neighborhood formulation
in `two_quadratic_planar_hypotheses`. -/
theorem planarHypotheses_iff (F : Vec 2 → ℝ) (B : ℝ) :
    TwoQuadraticExample.PlanarHypotheses F B ↔
      ConvexOn ℝ univ F ∧ IsLeast (range F) 0 ∧ 0 < B ∧ IsCompact {x | F x ≤ B} ∧
      (∀ t, 0 < t → t ≤ B → ∀ x y : Vec 2,
        segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) ∧
      (∀ p, F p ≤ B → ¬ AffineCriticalObjective.IsAffineCritical F p →
        ContDiffAt ℝ 2 F p ∨ PlanarCornerCharts.ConvexTwoBranchRegularAt F p) ∧
      (∀ p, F p ≤ B → AffineCriticalObjective.IsAffineCritical F p →
        (0 : Vec 2) ∈ ConvexSubdifferential.subdifferential F p) := by
  constructor
  · intro H
    exact ⟨H.convex, H.minimum, H.positive_level, H.compact, H.strict, H.regular, H.correct⟩
  · rintro ⟨hconv, hmin, hB, hcompact, hstrict, hregular, hcorrect⟩
    exact ⟨hconv, hmin, hB, hcompact, hstrict, hregular, hcorrect⟩

/-- Item `A/hypothesis_examples/proposition/art:examples-two-quadratics`
(`paper/appendices/hypothesis_examples.tex:122-135`): unfold every field of the
new `FiniteMaxHypotheses` record. The branch domain is the open neighborhood
`univ` of zero. The active type is `{i | f_i(0)=F(0)}` with the original indices;
the positive weights, sum-one and zero-gradient balance use that same type.
The strict-contour threshold is chosen before the run. -/
theorem finiteMaxHypotheses_iff {m : ℕ} (F : Vec 2 → ℝ) (f : Fin m → Vec 2 → ℝ)
    (w : ConvexSubdifferential.activeIndices F f 0 → ℝ) :
    TwoQuadraticExample.FiniteMaxHypotheses F f w ↔
      ConvexOn ℝ univ F ∧ (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧
      (∀ i, ConvexOn ℝ univ (f i) ∧ ContDiffOn ℝ 2 (f i) univ) ∧
      (∀ x, IsGreatest (range fun i => f i x) (F x)) ∧
      (∃ B, F 0 < B ∧ ∀ t, F 0 < t → t ≤ B → ∀ x y : Vec 2,
        segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) ∧
      AffineIndependent ℝ
        (fun i : ConvexSubdifferential.activeIndices F f 0 => coordinateGradient (f i) 0) ∧
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      (∑ i, w i • coordinateGradient (f i) 0) = 0 := by
  constructor
  · intro H
    exact ⟨H.convex, H.minimum, H.unique, H.branches, H.representation, H.contours,
      H.independent, H.positive, H.sum_one, H.balance⟩
  · rintro ⟨hconv, hmin, huniq, hbranches, hrep, hcont, hind, hpos, hsum, hbal⟩
    exact ⟨hconv, hmin, huniq, hbranches, hrep, hcont, hind, hpos, hsum, hbal⟩

/-- Item `A/hypothesis_examples/proposition/art:examples-two-quadratics`
(`paper/appendices/hypothesis_examples.tex:122-135`): for every `a,b,c>0`, zero
is the unique minimizer, all sublevels are compact, and the switching locus is
`v=(c-a)u²/2`, reducing to the line `v=0` when `a=c`.
The differentiability equivalence identifies this tie locus with the full-space
nondifferentiability locus, not merely equality of two unused formulas. -/
theorem two_quadratic_objective_geometry (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsLeast (range (TwoQuadraticExample.objective a b c)) 0 ∧
      (∀ x, TwoQuadraticExample.objective a b c x = 0 ↔ x = 0) ∧
      (∀ B : ℝ, IsCompact {x | TwoQuadraticExample.objective a b c x ≤ B}) ∧
      (∀ x : Vec 2,
        TwoQuadraticExample.branch a b c 0 x = TwoQuadraticExample.branch a b c 1 x ↔
          x 1 = (c - a) * (x 0) ^ 2 / 2) ∧
      (∀ x : Vec 2, DifferentiableAt ℝ (TwoQuadraticExample.objective a b c) x ↔
        x 1 ≠ (c - a) * (x 0) ^ 2 / 2) ∧
      (a = c → ∀ x : Vec 2,
        TwoQuadraticExample.branch a b c 0 x = TwoQuadraticExample.branch a b c 1 x ↔
          x 1 = 0) := by
  refine ⟨TwoQuadraticExample.objective_isLeast a b c ha.le hb.le hc.le,
    ?_, TwoQuadraticExample.sublevel_compact a b c ha hb hc,
    TwoQuadraticExample.tie_equation a b c, TwoQuadraticExample.differentiableAt_iff a b c, ?_⟩
  · intro x
    exact ⟨TwoQuadraticExample.objective_unique_zero a b c ha hb hc x,
      fun hx => hx ▸ TwoQuadraticExample.objective_zero a b c⟩
  · rintro rfl x
    simpa only [sub_self, zero_mul, zero_div] using TwoQuadraticExample.tie_equation a b a x

/-- Item `A/hypothesis_examples/proposition/art:examples-two-quadratics`
(`paper/appendices/hypothesis_examples.tex:122-135`): all hypotheses of
Corollary `art:planar-convergence` on each prescribed positive sublevel, written
literally rather than assuming a geometry package. This includes the full
neighborhood regularity alternative and `C_aff ∩ K_B ⊆ argmin F`. -/
theorem two_quadratic_planar_hypotheses (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (B : ℝ) (hB : 0 < B) :
    ConvexOn ℝ univ (TwoQuadraticExample.objective a b c) ∧
      IsLeast (range (TwoQuadraticExample.objective a b c)) 0 ∧ 0 < B ∧
      IsCompact {x | TwoQuadraticExample.objective a b c x ≤ B} ∧
      (∀ t, 0 < t → t ≤ B → ∀ x y : Vec 2,
        segment ℝ x y ⊆ frontier {z | TwoQuadraticExample.objective a b c z ≤ t} → x = y) ∧
      (∀ p, TwoQuadraticExample.objective a b c p ≤ B →
        ¬ AffineCriticalObjective.IsAffineCritical (TwoQuadraticExample.objective a b c) p →
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧
          ContDiffOn ℝ 2 (TwoQuadraticExample.objective a b c) V) ∨
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₀ f₁ : Vec 2 → ℝ,
          ConvexOn ℝ V f₀ ∧ ConvexOn ℝ V f₁ ∧ ContDiffOn ℝ 2 f₀ V ∧ ContDiffOn ℝ 2 f₁ V ∧
          (∀ z ∈ V, TwoQuadraticExample.objective a b c z = max (f₀ z) (f₁ z)) ∧
          f₀ p = TwoQuadraticExample.objective a b c p ∧
          f₁ p = TwoQuadraticExample.objective a b c p ∧
          LinearIndependent ℝ ![coordinateGradient f₀ p, coordinateGradient f₁ p])) ∧
      {p | AffineCriticalObjective.IsAffineCritical (TwoQuadraticExample.objective a b c) p} ∩
        {x | TwoQuadraticExample.objective a b c x ≤ B} ⊆
          argmin (TwoQuadraticExample.objective a b c) :=
  TwoQuadraticExample.paper_planar_hypotheses a b c ha hb hc B hB

/-- Item `A/hypothesis_examples/proposition/art:examples-two-quadratics`
(`paper/appendices/hypothesis_examples.tex:122-135`): the two original branches
are both active at zero, their actual gradients are `(0,1)` and `(0,-1)`, and
the complete finite-max hypotheses hold with strictly positive half weights.
`finiteMaxHypotheses_iff` spells out all fields, including indexed affine
independence, the sum of weights and the zero weighted gradient. -/
theorem two_quadratic_finite_max_hypotheses (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ConvexSubdifferential.activeIndices (TwoQuadraticExample.objective a b c)
        (TwoQuadraticExample.branch a b c) 0 = Finset.univ ∧
      coordinateGradient (TwoQuadraticExample.branch a b c 0) 0 = ![0, 1] ∧
      coordinateGradient (TwoQuadraticExample.branch a b c 1) 0 = ![0, -1] ∧
      TwoQuadraticExample.FiniteMaxHypotheses (TwoQuadraticExample.objective a b c)
        (TwoQuadraticExample.branch a b c) (fun _ => 1 / 2) := by
  rw [TwoQuadraticExample.coordinateGradient_eq, TwoQuadraticExample.coordinateGradient_eq]
  exact ⟨TwoQuadraticExample.initial_activeIndices a b c,
    (TwoQuadraticExample.initial_gradients a b c).1,
    (TwoQuadraticExample.initial_gradients a b c).2,
    TwoQuadraticExample.finite_max_hypotheses a b c ha hb hc⟩

/-- Item `A/hypothesis_examples/proposition/art:examples-two-quadratics`
(`paper/appendices/hypothesis_examples.tex:122-135`): the same family satisfies
all planar and finite-max hypotheses jointly with convergence of every admissible
run and an actual convergent run from every prescribed differentiable point,
SPD initial matrix and valid constant pair. No hypotheses about the objective
or its geometry are premises here. The two records are completely unfolded by
`planarHypotheses_iff`, `finiteMaxHypotheses_iff`, and the literal planar statement
`two_quadratic_planar_hypotheses`; the remaining objective/switching clauses are
`two_quadratic_objective_geometry`. -/
theorem two_quadratic_joint (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∀ B : ℝ, 0 < B → TwoQuadraticExample.PlanarHypotheses
      (TwoQuadraticExample.objective a b c) B) ∧
      TwoQuadraticExample.FiniteMaxHypotheses (TwoQuadraticExample.objective a b c)
        (TwoQuadraticExample.branch a b c) (fun _ => 1 / 2) ∧
      (∀ R : AdmissibleBFGSRun 2 (TwoQuadraticExample.objective a b c),
        Tendsto (fun k => TwoQuadraticExample.objective a b c (R.x k)) atTop (𝓝 0) ∧
        Tendsto (fun k => euclideanSolutionDistance (TwoQuadraticExample.objective a b c)
          (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
      ∀ x₀ : Vec 2, DifferentiableAt ℝ (TwoQuadraticExample.objective a b c) x₀ →
        ∀ H₀ : Mat 2, H₀.PosDef → ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → c₂ < 1 →
        ∃ R : AdmissibleBFGSRun 2 (TwoQuadraticExample.objective a b c),
          R.x 0 = x₀ ∧ R.g 0 = coordinateGradient (TwoQuadraticExample.objective a b c) x₀ ∧
          R.H 0 = H₀ ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
          Tendsto (fun k => TwoQuadraticExample.objective a b c (R.x k)) atTop (𝓝 0) ∧
          Tendsto R.x atTop (𝓝 0) := by
  refine ⟨TwoQuadraticExample.planar_hypotheses a b c ha hb hc,
    TwoQuadraticExample.finite_max_hypotheses a b c ha hb hc,
    TwoQuadraticExample.global_convergence a b c ha hb hc, ?_⟩
  intro x₀ hx₀ H₀ hH₀ c₁ c₂ hc₁ hc₁₂ hc₂
  exact (TwoQuadraticExample.joint_witness a b c ha hb hc hx₀ H₀ hH₀ hc₁ hc₁₂ hc₂).2.2.2

/-- Item `A/hypothesis_examples/disp/010`
(`paper/appendices/hypothesis_examples.tex:142-144`): on the tie curve,
the determinant of the two actual gradients is
`-2u(a+c+b(c-a)²u²)`. The branch definitions and tie equation precede this display. -/
theorem two_quadratic_tie_determinant (a b c : ℝ)
    (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c) (x : Vec 2)
    (ht : TwoQuadraticExample.branch a b c 0 x = TwoQuadraticExample.branch a b c 1 x) :
    HomogeneousPlanar.pairDet (coordinateGradient (TwoQuadraticExample.branch a b c 0) x)
        (coordinateGradient (TwoQuadraticExample.branch a b c 1) x) =
      -2 * x 0 * (a + c + b * (c - a) ^ 2 * (x 0) ^ 2) := by
  rw [TwoQuadraticExample.coordinateGradient_eq, TwoQuadraticExample.coordinateGradient_eq]
  exact TwoQuadraticExample.tie_determinant a b c ht

/-- Item `A/hypothesis_examples/corollary/art:examples-nonradial-runs`
(`paper/appendices/hypothesis_examples.tex:162-168`): for every differentiable
`x₀` with `F(x₀)<1/100`, every SPD `H₀` and every valid fixed pair, there is an
actual infinite full-BFGS run with exactly those data, converging to zero.
Every admissible run starting in the stated low sublevel converges in value
and iterates. Existence is not restricted to the numerical start. -/
theorem nonradial_runs {x₀ : Vec 2}
    (hx₀ : DifferentiableAt ℝ PlanarQuadraticExample.objective x₀)
    (hlow : PlanarQuadraticExample.objective x₀ < 1 / 100)
    (H₀ : Mat 2) (hH₀ : H₀.PosDef) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    (∀ R : AdmissibleBFGSRun 2 PlanarQuadraticExample.objective,
      PlanarQuadraticExample.objective (R.x 0) < 1 / 100 →
        Tendsto (fun k => PlanarQuadraticExample.objective (R.x k)) atTop (𝓝 0) ∧
        Tendsto R.x atTop (𝓝 0)) ∧
      ∃ R : AdmissibleBFGSRun 2 PlanarQuadraticExample.objective,
        R.x 0 = x₀ ∧ R.H 0 = H₀ ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
        Tendsto (fun k => PlanarQuadraticExample.objective (R.x k)) atTop (𝓝 0) ∧
        Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨R, hx, hH, h1, h2⟩ :=
    PlanarQuadraticExample.objective_exists_admissible_run hx₀ H₀ hH₀ hc₁ hc₁₂ hc₂
  exact ⟨PlanarQuadraticExample.fullBFGS_explicit_basin, R, hx, hH, h1, h2,
    PlanarQuadraticExample.fullBFGS_explicit_basin R (by simpa only [hx] using hlow)⟩

/-- Item `A/hypothesis_examples/corollary/art:examples-nonradial-runs`
(`paper/appendices/hypothesis_examples.tex:162-168`): the particular start
`(1/1000,0)` is full-space differentiable and has exactly the printed value
`1001/10^6 < 1/100`. Together with `nonradial_runs` it gives a run for every
initial SPD matrix and every valid constant pair at this same start. -/
theorem nonradial_initial_value :
    HasFDerivAt PlanarQuadraticExample.objective
      (gradientFunctional (PlanarQuadraticExample.gradient 0 ![1 / 1000, 0]))
        (![1 / 1000, 0] : Vec 2) ∧
      PlanarQuadraticExample.objective ![1 / 1000, 0] = (1001 : ℝ) / 10 ^ 6 ∧
      (1001 : ℝ) / 10 ^ 6 < 1 / 100 := by
  obtain ⟨h1, h2, hg, _⟩ := PlanarQuadraticExample.start_point_facts
  refine ⟨hg, ?_, by norm_num⟩
  rw [PlanarQuadraticExample.winner_zero_value h1.le h2.le]
  norm_num [PlanarQuadraticExample.branch]

/-- Item `A/hypothesis_examples/proposition/art:examples-no-step`
(`paper/appendices/hypothesis_examples.tex:183-190`): the literal three-linear
objective `G(u,v)=max{u,-u+v,-u-v}`. -/
theorem gauge_formula (x : Vec 2) :
    Gauge.objective x = max (x 0) (max (-x 0 + x 1) (-x 0 - x 1)) :=
  Gauge.objective_formula x

/-- Item `A/hypothesis_examples/proposition/art:examples-no-step`
(`paper/appendices/hypothesis_examples.tex:183-190`): the same finite convex
coercive homogeneous objective has unique minimizer zero and, for every `ε>0`,
a differentiable start `(ε,0)` with `H₀=I` whose whole positive search ray has
no differentiable weak-Wolfe endpoint for any `c₂<1`. Both the constant-gradient
part before zero and full-space nondifferentiability at and beyond zero are
included. Consequently no admissible run has these initial data. -/
theorem gauge_no_step {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ univ Gauge.objective ∧ Continuous Gauge.objective ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x : Vec 2, Gauge.objective (t • x) = t * Gauge.objective x) ∧
      IsLeast (range Gauge.objective) 0 ∧ (∀ x, Gauge.objective x = 0 ↔ x = 0) ∧
      (∀ b : ℝ, IsCompact {x : Vec 2 | Gauge.objective x ≤ b}) ∧
      Tendsto Gauge.objective (cocompact (Vec 2)) atTop ∧
      Gauge.objective ![ε, 0] = ε ∧
      HasFDerivAt Gauge.objective (gradientFunctional ![1, 0]) ![ε, 0] ∧
      (![1, 0] : Vec 2) ≠ 0 ∧ (1 : Mat 2).PosDef ∧
      (∀ α : ℝ, (![ε - α, 0] : Vec 2) = ![ε, 0] + bfgsStep (1 : Mat 2) ![1, 0] α) ∧
      (∀ α : ℝ, α < ε →
        HasFDerivAt Gauge.objective (gradientFunctional ![1, 0]) ![ε - α, 0]) ∧
      (∀ α : ℝ, ε ≤ α → ¬ DifferentiableAt ℝ Gauge.objective ![ε - α, 0]) ∧
      (∀ c₂ : ℝ, c₂ < 1 → ∀ α : ℝ, 0 < α → ∀ g : Vec 2,
        HasFDerivAt Gauge.objective (gradientFunctional g) ![ε - α, 0] →
        ¬ (c₂ * dot (![1, 0] : Vec 2) (bfgsStep (1 : Mat 2) ![1, 0] α) ≤
          dot g (bfgsStep (1 : Mat 2) ![1, 0] α))) ∧
      ¬ ∃ R : AdmissibleBFGSRun 2 Gauge.objective, R.x 0 = ![ε, 0] ∧ R.H 0 = 1 :=
  Gauge.joint_obstruction hε

/-- Item `A/hypothesis_examples/proposition/art:examples-no-step`
(`paper/appendices/hypothesis_examples.tex:183-190`): the gauge satisfies the
hypotheses of Theorem `art:homogeneous`; hence every infinite admissible run on it
converges to zero, while `gauge_no_step` excludes the specified initial data. -/
theorem gauge_covered_convergence (R : AdmissibleBFGSRun 2 Gauge.objective) :
    Tendsto (fun k => Gauge.objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) :=
  Gauge.admissible_runs_converge R

/-- Item `A/hypothesis_examples/prose/006`
(`paper/appendices/hypothesis_examples.tex:204-206`): this is an obstruction
to an infinite differentiable history from the specified data, rather than a
nonoptimal stagnating run. The search ray itself reaches the minimizer at the
positive length `α=ε`, but no infinite admissible run has that initialization. -/
theorem gauge_ray_minimizer {ε : ℝ} (hε : 0 < ε) :
    0 < ε ∧ Gauge.ray ε ε = 0 ∧ Gauge.objective (Gauge.ray ε ε) = 0 ∧
      ¬ ∃ R : AdmissibleBFGSRun 2 Gauge.objective, R.x 0 = ![ε, 0] ∧ R.H 0 = 1 := by
  have hray : Gauge.ray ε ε = 0 := by ext i; fin_cases i <;> simp [Gauge.ray]
  refine ⟨hε, hray, by rw [hray, Gauge.objective_zero], ?_⟩
  rintro ⟨R, hx, hH⟩
  exact Gauge.no_admissible_run hε R hx hH

/-! ## Joint non-vacuity at explicit parameter values

The two explicit histories are actual-gradient infinite full-BFGS runs.
The nonradial existence criterion is realized at the printed numerical start,
and the simpler two-quadratic family at `(a,b,c)=(1,1,2)`, `x₀=(0,1/4)`.
The gauge obstruction starts at a genuinely differentiable positive-value point.
-/

example : Nonempty (AdmissibleBFGSRun 2 Mixed.objective) := ⟨Mixed.run⟩

example : Nonempty (AdmissibleBFGSRun 2 Quadratic.objective) :=
  Quadratic.planar_run_nonempty

example : ∃ R : AdmissibleBFGSRun 2 (TwoQuadraticExample.objective 1 1 2),
    R.x 0 = ![0, 1 / 4] ∧ R.H 0 = 1 ∧ R.c₁ = 1 / 4 ∧ R.c₂ = 1 / 2 ∧
      Tendsto (fun k => TwoQuadraticExample.objective 1 1 2 (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0) := by
  have hx : DifferentiableAt ℝ (TwoQuadraticExample.objective 1 1 2) ![0, 1 / 4] := by
    rw [TwoQuadraticExample.differentiableAt_iff]
    norm_num
  obtain ⟨R, hr, _, hH, h1, h2, hv, hlim⟩ :=
    (two_quadratic_joint 1 1 2 (by norm_num) (by norm_num) (by norm_num)).2.2.2
      ![0, 1 / 4] hx 1 Matrix.PosDef.one (1 / 4) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
  exact ⟨R, hr, hH, h1, h2, hv, hlim⟩

example : ∃ R : AdmissibleBFGSRun 2 PlanarQuadraticExample.objective,
    R.x 0 = ![1 / 1000, 0] ∧ R.H 0 = 1 ∧ R.c₁ = 1 / 4 ∧ R.c₂ = 1 / 2 ∧
      Tendsto (fun k => PlanarQuadraticExample.objective (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0) := by
  exact (nonradial_runs nonradial_initial_value.1.differentiableAt
    (by rw [nonradial_initial_value.2.1]; exact nonradial_initial_value.2.2)
    1 Matrix.PosDef.one (by norm_num) (by norm_num) (by norm_num)).2

example : Gauge.objective ![1, 0] = 1 ∧
    DifferentiableAt ℝ Gauge.objective ![1, 0] ∧
    ¬ ∃ R : AdmissibleBFGSRun 2 Gauge.objective, R.x 0 = ![1, 0] ∧ R.H 0 = 1 := by
  exact ⟨(Gauge.initial_state one_pos).1,
    (Gauge.initial_state one_pos).2.1.differentiableAt, (gauge_ray_minimizer one_pos).2.2.2⟩

end BfgsCoverage.Article.HypothesisExamples
