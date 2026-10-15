import BfgsVerification.ReportCoreEndToEnd
import BfgsVerification.FoundationEndToEnd
import BfgsVerification.EndToEnd
import BfgsVerification.ObjectiveEndToEnd
import BfgsVerification.PrincipalCombinatorialIdentity
import BfgsVerification.ScalarTransportEnergy
import BfgsVerification.AccumulatingKinks

/-!
# Lean coverage: `paper/sections/energy.tex`

Section `art:energy` ("The analytical framework"): Definition `art:admissible`, Lemmas
`art:run-invariants` and `art:reference-energy`, the principal-minor sums, Theorems
`art:minor-hierarchy`, `art:reciprocal-growth` and `art:certificate`, Definition
`art:band-certificate`, the displays inside their proofs, and the claims made in prose.
Register: `editorial/lean_coverage/register/A_energy.json`.

## Lean forms (for reuse by the other coverage modules)

**Admissible runs.** An admissible run (Definition `art:admissible`) is
`R : AdmissibleBFGSRun n F` with `F : Vec n → ℝ`; `admissible_iff` shows that the structure is
exactly the definition. The objects of the run are the library's names (`run_notation`,
`notation_display` and `update_formula` unfold them):

| TeX | Lean |
|---|---|
| $x_k,\ H_k,\ g_k,\ \alpha_k,\ c_1,\ c_2$ | `R.x k`, `R.H k`, `R.g k`, `R.α k`, `R.c₁`, `R.c₂` |
| $s_k=-\alpha_kH_kg_k$ | `R.displacement k` (`= bfgsStep (R.H k) (R.g k) (R.α k)`) |
| $y_k=g_{k+1}-g_k$, $t_k=y_k^Ts_k$ | `R.gradientChange k`, `R.curvature k` |
| $B_k=H_k^{-1}$, $q_k=g_k^TH_kg_k$ | `R.hessian k`, `R.q k` |
| $d_k=-g_k^Ts_k=\alpha_kq_k$ | `R.d k` (defined as `R.α k * R.q k`) |
| $\Delta_k$, $\omega$ | `F (R.x k) - F (R.x (k + 1))`, `1 - R.c₂` |
| $\beta_k=-y_k^TH_kg_k/q_k$ | `R.beta k` |
| $\widehat B_k=B_k-g_kg_k^T/q_k$ | variable `Bhat` with `hBhat` (below) |

`hBhat : ∀ k, Bhat k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)`.
"$x$ is differentiable with $g=\nabla F(x)$" is `HasFDerivAt F (gradientFunctional g) x`.
"Bounded gradients" is `∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ` (Euclidean norm
`‖euclideanVector v‖`; $\|v\|^2$ is `sqNorm v`). "$\sum_kd_k<\infty$" is `Summable R.d`.

**One update.** Theorem `art:minor-hierarchy` and its proof use the forms of
`MatrixAlgebra.lean`: `hH : H.PosDef`, `hs : s = -α • (H *ᵥ g)`, `hα : 0 < α`,
`hq_def : q = dot g (H *ᵥ g)`, `hq : 0 < q`, `hβ_def : β = -dot y (H *ᵥ g) / q`, `hβ : 0 < β`,
`hHplus : Hplus = inverseBFGS H s y`; $Z$ with $j$ orthonormal columns is
`Z : Matrix (Fin n) (Fin j) ℝ` with `Zᵀ * Z = 1`; $\operatorname{Gram}_H(y,Z)$ is
`metricGram H (fromCols (replicateCol Unit y) Z)`. $e_j(H)$ is `principalSum H j`.

**Certificates.** An eligible pair is `TransportedCertificate.EligiblePair F c₁ c₂ x z g h`
(`eligiblePair_iff`); $\Pi_s$ is `TransportedCertificate.stepProjector s` (`stepProjector_eq`);
$K_\eta$ is `{x | x ∈ K ∧ F x ≥ Fstar + η}` (the library's `positiveBand F K Fstar η`). A band
certificate of Definition `art:band-certificate` is
`Cert : TransportedCertificate.BandCertificate F K Fstar c₁ c₂ η` together with `0 ≤ Cert.C`
(`bandCertificate_iff`; its field and constants are `Cert.W`, `Cert.m`, `Cert.C`, `Cert.L`,
`Cert.δ`). "$K$ admits the band certificates" is
`∀ η : ℝ, 0 < η → {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty → ∃ Cert, 0 ≤ Cert.C`, equivalent to the
library's `HasBandCertificates F K Fstar c₁ c₂` (`hasBandCertificates_iff`). $F_*=\min F$ is
`IsLeast (Set.range F) Fstar`; $\operatorname{dist}(x,\arg\min F)$ is
`euclideanSolutionDistance F x`.

## Items

* `definition/art:admissible` (12-28, with `disp/001`, `disp/002`): `admissible_iff`,
  `update_formula`, `armijo_weak_wolfe`; `disp/003` (36-42): `notation_display`.
* `lemma/art:run-invariants` (43-55, with `disp/004`, `disp/005`): `run_invariants`.
* `lemma/art:reference-energy` (74-89, with `disp/006`-`disp/008`): `reference_energy`,
  `reference_notation`; `disp/009`, `disp/010` (92-106): `energy_step`,
  `persistent_gap_budget` (finite-horizon form `persistent_gap_budget_general`).
* `disp/011` (116-119): `principalSum_def`.
* `theorem/art:minor-hierarchy` (130-141, with `disp/012`, `disp/013`): `minor_hierarchy`;
  `disp/014`, `disp/015` (145-161): `compression_bound`, `eigenbasis_gram_sum`.
* `theorem/art:reciprocal-growth` (168-174, with `disp/016`): `reciprocal_growth`;
  `disp/017`-`disp/020` (178-201): `run_bounds`, `normalized_hierarchy`, `potential_pos`,
  `potential_contraction`.
* `disp/021` (241-243): `eligiblePair_iff`.
* `definition/art:band-certificate` (249-263, with `disp/022`): `bandCertificate_iff`,
  `hasBandCertificates_iff`.
* `theorem/art:certificate` (270-278, with `disp/023`): `certificate`; `disp/024`, `disp/025`
  (292-307): `certificate_energy_step`, `certificate_reciprocal_budget`.

Prose claims (register ids `A/energy/prose/...`): `secant_jump_persists`,
`zero_gradient_minimizer`, `persistent_gap_contradiction`, `reciprocal_sum_linear` (with
`reciprocal_sum_linear_general`), `energy_nonneg`, `principal_sums_coefficients`,
`principal_trace_det`, `compressions_and_volume`, `summability_stronger`,
`finite_horizon_bound`, `superquadratic_growth`, `projection_no_cost`,
`accepted_pairs_eligible`, `stepProjector_eq`, `nonsmooth_optimizer_certificates` (with
`band_excludes_minimizers`), `certificate_not_necessary`.

Corrected on 15 October 2026 (M10 of `TODO_MANUSCRIPT_REVIEW.md`): `A/energy/prose/012` read
"The next theorem proves that the full update requires faster growth", which named the wrong
theorem and omitted bounded gradients; it now names Theorem `art:reciprocal-growth` and its bounded
gradients (lines 108-110). Its Lean statement is `reciprocal_sum_superlinear` (and, in the
paragraph's setting with a minimizer, `reciprocal_sum_superlinear_of_minimizer`).

## Standing assumptions inside proofs

Each display inside a proof is stated under the hypotheses of its result and the objects that
the proof has introduced, as variables with their defining equations (`Bhat`, `r`, `E`, `Rk`
for $R_k$, `Λ`, `K0`, `η`, `J`, `V` for $V_\eta$, `ℓ`, `Cert`, `Pbar` for $\overline P$). A
hypothesis whose name starts with `_` is a standing assumption that the Lean proof does not use.
The displays of the proof of Theorem `art:certificate` sit inside a proof by contradiction, so
their standing assumptions are jointly inconsistent; each is proved from a general form
(`certificate_step_general`, `certificate_budget_general`) whose assumptions are satisfiable.
Undisplayed steps that are stated too: `q_le_potential` (line 196), `certificate_energy_nonneg`
(line 289), `iterates_in_band` (lines 280-288), `normalization_bounds` (lines 301-302),
`finite_reciprocal_sum_le` (lines 303-304). Display `disp/010` and `reciprocal_sum_linear`
assume a gap $\ge\eta$ at every $k$ and $R_k\le C$ for every $k$, the hypotheses of the reductio
of lines 101-109. Together with bounded gradients these cannot all hold
(`persistent_gap_contradiction`; $d_k\to0$ follows from the minimizer); without bounded gradients
their satisfiability is not settled here. Both are proved from finite-horizon forms
(`persistent_gap_budget_general`, `reciprocal_sum_linear_general`: the gap only at $N$,
$R_k\le C$ only for $k<N$), whose assumptions are satisfiable.

## Non-vacuity

The examples at the end show that the standing assumptions can hold: those of Theorem
`art:minor-hierarchy` and its proof; an admissible run (the 1-D quadratic run
$x_k=2^{-k}$, `Example.run`) with bounded gradients and $d_k\to0$ together with the choices of
the proof of Theorem `art:reciprocal-growth`; the finite-horizon forms of display `disp/010` and
item `prose/011` ($N=1$); the hypotheses of Theorem `art:certificate` (with an explicit band
certificate, `Example.quadCert`); and those of the general forms of its proof displays.
`nonsmooth_optimizer_certificates` gives a second instance of the certificate hypotheses,
$F(x)=|x|$, which is not differentiable at its minimizer.
-/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter BfgsVerification

namespace BfgsCoverage.Article.Energy

/-! ### Helpers -/

/-- A positive definite real matrix is symmetric. -/
theorem isSymm_of_posDef {n : ℕ} {H : Mat n} (hH : H.PosDef) : H.IsSymm := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.isHermitian.eq

/-- Orthonormal columns are linearly independent. -/
theorem mulVec_injective_of_orthonormal {n j : ℕ} {Z : Matrix (Fin n) (Fin j) ℝ}
    (hZ : Zᵀ * Z = 1) : Function.Injective Z.mulVec := by
  apply Function.LeftInverse.injective (g := Zᵀ.mulVec)
  intro x
  rw [Matrix.mulVec_mulVec, hZ, Matrix.one_mulVec]

/-- The Euclidean norm: $\|v\|^2=v^Tv$ (`sqNorm v`). -/
theorem norm_sq_eq_sqNorm {n : ℕ} (v : Vec n) : ‖euclideanVector v‖ ^ 2 = sqNorm v :=
  FrameNorms.euclidean_norm_sq (euclideanVector v)

/-- The Euclidean coordinate map is linear: $\|v-w\|$ is
`‖euclideanVector v - euclideanVector w‖`. -/
theorem euclideanVector_sub {n : ℕ} (v w : Vec n) :
    euclideanVector (v - w) = euclideanVector v - euclideanVector w :=
  WithLp.equiv_symm_sub 2 v w

/-- A Euclidean bound $\|v_k\|\le\Lambda$ gives the squared bound `sqNorm (v k) ≤ Λ ^ 2`. -/
theorem sqNorm_le_of_norm_le {n : ℕ} {v : Vec n} {Λ : ℝ} (h : ‖euclideanVector v‖ ≤ Λ) :
    sqNorm v ≤ Λ ^ 2 := by
  rw [← norm_sq_eq_sqNorm]
  nlinarith [norm_nonneg (euclideanVector v)]

/-- Bounded Euclidean norms give the library's form of a gradient bound, with a positive
constant. -/
theorem sqNorm_bound_of_bounded {n : ℕ} (v : ℕ → Vec n)
    (h : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (v k)‖ ≤ Λ) :
    ∃ G : ℝ, 0 < G ∧ ∀ k, sqNorm (v k) ≤ G ^ 2 := by
  obtain ⟨Λ, hΛ⟩ := h
  exact ⟨max Λ 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun k => sqNorm_le_of_norm_le ((hΛ k).trans (le_max_left _ _))⟩

/-- In dimension one the step projector vanishes: $\Pi_s=0$ for $s\ne0$. -/
theorem stepProjector_one_dim {s : Vec 1} (hs : s ≠ 0) :
    TransportedCertificate.stepProjector s = 0 := by
  have hs0 : s 0 ≠ 0 := fun h => hs (funext fun i => by fin_cases i; exact h)
  ext i j
  fin_cases i
  fin_cases j
  simp [TransportedCertificate.stepProjector, sqNorm, outer]
  field_simp
  ring

/-- $x\mapsto|x|$ on $\R^1$ is convex. -/
theorem abs_coord_convex : ConvexOn ℝ Set.univ (fun x : Vec 1 => |x 0|) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |a * x 0 + b * y 0| ≤ |a * x 0| + |b * y 0| := abs_add _ _
    _ = a * |x 0| + b * |y 0| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-! ### Definition `art:admissible` -/

/-- Item `A/energy/definition/art:admissible` (`paper/sections/energy.tex:12-28`), Definition
`art:admissible` (Admissible runs), with its displays \eqref{art:update} and \eqref{art:aw}.

Let $F:\R^n\to\R$ be finite and convex, with $n\ge1$. An admissible run is an infinite
sequence of differentiable accepted points $x_k$, nonzero gradients $g_k=\nabla F(x_k)$, and
matrices generated by
\[ s_k=-\alpha_kH_kg_k,\quad x_{k+1}=x_k+s_k,\quad y_k=g_{k+1}-g_k,\quad
   H_{k+1}=\Bigl(I-\frac{s_ky_k^T}{t_k}\Bigr)H_k\Bigl(I-\frac{y_ks_k^T}{t_k}\Bigr)
   +\frac{s_ks_k^T}{t_k},\quad t_k=y_k^Ts_k, \]
where $H_0\succ0$, $\alpha_k>0$, and fixed constants $0<c_1<c_2<1$ satisfy
\[ F(x_{k+1})\le F(x_k)+c_1g_k^Ts_k,\qquad g_{k+1}^Ts_k\ge c_2g_k^Ts_k. \]

The library structure `AdmissibleBFGSRun n F` is exactly this definition: data `x H g α c₁ c₂`
are the data of an admissible run iff the conditions on the right hold, where $s_k,y_k,t_k$ are
the variables `s y t` with their defining equations. Readings: "finite and convex" is
`ConvexOn ℝ Set.univ F` for a real-valued `F`; "$x_k$ is a differentiable point with
$g_k=\nabla F(x_k)$" is `DifferentiableAt ℝ F (x k)` with `fderiv ℝ F (x k) v = dot (g k) v` for
all `v` (the structure stores the equivalent `HasFDerivAt F (gradientFunctional (g k)) (x k)`;
differentiability does not depend on the norm of `Vec n`); $H_0\succ0$ is `(H 0).PosDef`
(symmetric positive definite). Both line-search inequalities are non-strict; the constants are
strictly ordered. The structure omits $n\ge1$, which follows from $g_0\ne0$
(`AdmissibleBFGSRun.dimension_pos`). Lean's inverse is total ($0^{-1}=0$), but $t_k>0$ along
every admissible run (`run_invariants`), so `(t k)⁻¹` is $1/t_k$. Nothing else is assumed: not
$t_k>0$, not $H_k\succ0$ for $k\ge1$, no bound and no limit. -/
theorem admissible_iff {n : ℕ} (F : Vec n → ℝ) (x : ℕ → Vec n) (H : ℕ → Mat n)
    (g : ℕ → Vec n) (α : ℕ → ℝ) (c₁ c₂ : ℝ) (s y : ℕ → Vec n) (t : ℕ → ℝ)
    (hs : ∀ k, s k = -α k • (H k *ᵥ g k)) (hy : ∀ k, y k = g (k + 1) - g k)
    (ht : ∀ k, t k = dot (y k) (s k)) :
    (∃ R : AdmissibleBFGSRun n F,
        R.x = x ∧ R.H = H ∧ R.g = g ∧ R.α = α ∧ R.c₁ = c₁ ∧ R.c₂ = c₂) ↔
      (ConvexOn ℝ Set.univ F ∧ 1 ≤ n) ∧
      (∀ k, DifferentiableAt ℝ F (x k) ∧ g k ≠ 0 ∧ ∀ v, fderiv ℝ F (x k) v = dot (g k) v) ∧
      (∀ k, x (k + 1) = x k + s k ∧
        H (k + 1) = (1 - (t k)⁻¹ • outer (s k) (y k)) * H k * (1 - (t k)⁻¹ • outer (y k) (s k)) +
          (t k)⁻¹ • outer (s k) (s k)) ∧
      ((H 0).PosDef ∧ (∀ k, 0 < α k) ∧ 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) ∧
      (∀ k, F (x (k + 1)) ≤ F (x k) + c₁ * dot (g k) (s k) ∧
        dot (g (k + 1)) (s k) ≥ c₂ * dot (g k) (s k)) := by
  constructor
  · rintro ⟨R, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hsk : ∀ k, s k = bfgsStep (R.H k) (R.g k) (R.α k) := hs
    refine ⟨⟨R.convex, R.dimension_pos⟩, fun k => ⟨(R.hasGradient k).differentiableAt,
      R.gradient_nonzero k, fun v => by rw [(R.hasGradient k).fderiv, gradientFunctional_apply]⟩,
      fun k => ⟨by rw [R.step k, hsk k], ?_⟩,
      ⟨R.initial_posDef, R.alpha_pos, R.c₁_pos, R.c₁_lt_c₂, R.c₂_lt_one⟩,
      fun k => ⟨by rw [hsk k]; exact R.armijo k, by rw [hsk k]; exact R.weak_wolfe k⟩⟩
    rw [R.update k, ht k, hsk k, hy k]
    rfl
  · rintro ⟨⟨hconv, _hn⟩, hgrad, hupd, ⟨hH0, hα, hc₁, hc₁₂, hc₂⟩, hls⟩
    refine ⟨{ convex := hconv, x := x, H := H, g := g, α := α, c₁ := c₁, c₂ := c₂
              c₁_pos := hc₁, c₁_lt_c₂ := hc₁₂, c₂_lt_one := hc₂, initial_posDef := hH0
              alpha_pos := hα, gradient_nonzero := fun k => (hgrad k).2.1
              hasGradient := fun k => ?_, step := fun k => ?_, update := fun k => ?_
              armijo := fun k => ?_, weak_wolfe := fun k => ?_ },
      rfl, rfl, rfl, rfl, rfl, rfl⟩
    · have hf : fderiv ℝ F (x k) = gradientFunctional (g k) :=
        ContinuousLinearMap.ext fun v => by rw [(hgrad k).2.2 v, gradientFunctional_apply]
      have h := (hgrad k).1.hasFDerivAt
      rwa [hf] at h
    · rw [(hupd k).1, hs k]
      rfl
    · rw [(hupd k).2, ht k, hs k, hy k]
      rfl
    · have h := (hls k).1
      rw [hs k] at h
      exact h
    · have h := (hls k).2
      rw [hs k] at h
      exact h

/-- The library's elementary definitions, unfolded: $s=-\alpha Hg$ (`bfgsStep`), the inverse
update \eqref{art:update} with $t=y^Ts$ (`inverseBFGS`), $x^Tz$ (`dot`), $xz^T$ (`outer`),
$\|x\|^2$ (`sqNorm`), $x^THx$ (`metricEnergy`), and the derivative functional
$v\mapsto g^Tv$ represented by a gradient $g$ (`gradientFunctional`). -/
theorem library_formulas {n : ℕ} (H : Mat n) (g s y a b : Vec n) (α : ℝ) :
    bfgsStep H g α = -α • (H *ᵥ g) ∧
      inverseBFGS H s y = (1 - (dot y s)⁻¹ • outer s y) * H * (1 - (dot y s)⁻¹ • outer y s) +
        (dot y s)⁻¹ • outer s s ∧
      dot a b = ∑ i, a i * b i ∧ (∀ i j, outer a b i j = a i * b j) ∧
      sqNorm a = ∑ i, a i ^ 2 ∧ metricEnergy H a = dot a (H *ᵥ a) ∧
      ∀ v, gradientFunctional a v = dot a v :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, gradientFunctional_apply a⟩

/-- The Lean names of the run notation of Definition `art:admissible` and of the display
`paper/sections/energy.tex:36-42`, unfolded: $s_k$ is `R.displacement k`, $y_k$ is
`R.gradientChange k`, $t_k$ is `R.curvature k`, $B_k$ is `R.hessian k`, $q_k$ is `R.q k`,
$d_k$ is `R.d k`, and $\beta_k=-y_k^TH_kg_k/q_k$ (the $\beta$ of Theorem `art:minor-hierarchy`
for the $k$-th update) is `R.beta k`. -/
theorem run_notation {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.displacement k = -R.α k • (R.H k *ᵥ R.g k) ∧ R.gradientChange k = R.g (k + 1) - R.g k ∧
      R.curvature k = dot (R.gradientChange k) (R.displacement k) ∧
      R.hessian k = (R.H k)⁻¹ ∧ R.q k = dot (R.g k) (R.H k *ᵥ R.g k) ∧
      R.d k = R.α k * R.q k ∧
      R.beta k = -dot (R.gradientChange k) (R.H k *ᵥ R.g k) / R.q k :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Item `A/energy/disp/001` (`paper/sections/energy.tex:16-22`), the display
\eqref{art:update} of Definition `art:admissible`:
\[ s_k=-\alpha_kH_kg_k,\quad x_{k+1}=x_k+s_k,\quad y_k=g_{k+1}-g_k,\quad
   H_{k+1}=\Bigl(I-\frac{s_ky_k^T}{t_k}\Bigr)H_k\Bigl(I-\frac{y_ks_k^T}{t_k}\Bigr)
     +\frac{s_ks_k^T}{t_k},\quad t_k=y_k^Ts_k. \]
Every admissible run satisfies these equations, with the library's names for
$s_k,y_k,t_k$. (`(R.curvature k)⁻¹` is Lean's total inverse; $t_k>0$ by
`run_invariants`, so it is $1/t_k$.) -/
theorem update_formula {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.displacement k = -R.α k • (R.H k *ᵥ R.g k) ∧ R.x (k + 1) = R.x k + R.displacement k ∧
      R.gradientChange k = R.g (k + 1) - R.g k ∧
      R.H (k + 1) = (1 - (R.curvature k)⁻¹ • outer (R.displacement k) (R.gradientChange k)) *
          R.H k * (1 - (R.curvature k)⁻¹ • outer (R.gradientChange k) (R.displacement k)) +
        (R.curvature k)⁻¹ • outer (R.displacement k) (R.displacement k) ∧
      R.curvature k = dot (R.gradientChange k) (R.displacement k) :=
  ⟨rfl, R.step k, rfl, R.update k, rfl⟩

/-- Item `A/energy/disp/002` (`paper/sections/energy.tex:24-27`), the Armijo--weak Wolfe
conditions \eqref{art:aw} of Definition `art:admissible`, with their constants:
$0<c_1<c_2<1$ and, for every $k$,
\[ F(x_{k+1})\le F(x_k)+c_1g_k^Ts_k,\qquad g_{k+1}^Ts_k\ge c_2g_k^Ts_k. \]
Both conditions are non-strict; the constants are strictly ordered. -/
theorem armijo_weak_wolfe {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    (0 < R.c₁ ∧ R.c₁ < R.c₂ ∧ R.c₂ < 1) ∧ ∀ k,
      F (R.x (k + 1)) ≤ F (R.x k) + R.c₁ * dot (R.g k) (R.displacement k) ∧
        dot (R.g (k + 1)) (R.displacement k) ≥ R.c₂ * dot (R.g k) (R.displacement k) :=
  ⟨⟨R.c₁_pos, R.c₁_lt_c₂, R.c₂_lt_one⟩, fun k => ⟨R.armijo k, R.weak_wolfe k⟩⟩

/-- Item `A/energy/disp/003` (`paper/sections/energy.tex:36-42`):
\[ B_k=H_k^{-1},\quad q_k=g_k^TH_kg_k,\quad d_k=-g_k^Ts_k=\alpha_kq_k,\quad
   \Delta_k=F(x_k)-F(x_{k+1}),\quad \omega=1-c_2. \]
The display defines notation and asserts $-g_k^Ts_k=\alpha_kq_k$. In Lean $B_k$ is
`R.hessian k`, $q_k$ is `R.q k` and $d_k$ is `R.d k` (defined as $\alpha_kq_k$); $\Delta_k$
and $\omega$ are written out as `F (R.x k) - F (R.x (k + 1))` and `1 - R.c₂`. -/
theorem notation_display {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.hessian k = (R.H k)⁻¹ ∧ R.q k = dot (R.g k) (R.H k *ᵥ R.g k) ∧
      R.d k = -dot (R.g k) (R.displacement k) ∧
      -dot (R.g k) (R.displacement k) = R.α k * R.q k := by
  have h : dot (R.g k) (R.displacement k) = -R.d k := R.dot_step_eq_neg_d k
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [h, neg_neg]
  · rw [h, neg_neg]
    rfl

/-! ### Lemma `art:run-invariants` -/

/-- Item `A/energy/lemma/art:run-invariants` (`paper/sections/energy.tex:43-55`), Lemma
`art:run-invariants`, with its displays \eqref{art:decrease-bounds} and
\eqref{art:hessian-update}.

Every admissible run satisfies $H_k\succ0$, $q_k,d_k,t_k>0$ and
\[ c_1d_k\le\Delta_k\le d_k,\qquad t_k\ge\omega d_k. \]
Moreover,
\[ B_{k+1}=B_k-\frac{g_kg_k^T}{q_k}+\frac{y_ky_k^T}{t_k},\qquad
   \widehat B_k:=B_k-\frac{g_kg_k^T}{q_k}\succeq0,\qquad \widehat B_ks_k=0. \]
If the objective values have a finite limit, then $\sum_kd_k<\infty$.

$\widehat B_k$ is the variable `Bhat k` with its defining equation. -/
theorem run_invariants {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (Bhat : ℕ → Mat n)
    (hBhat : ∀ k, Bhat k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) :
    (∀ k, (R.H k).PosDef ∧ 0 < R.q k ∧ 0 < R.d k ∧ 0 < R.curvature k) ∧
      (∀ k, R.c₁ * R.d k ≤ F (R.x k) - F (R.x (k + 1)) ∧
        F (R.x k) - F (R.x (k + 1)) ≤ R.d k ∧ R.curvature k ≥ (1 - R.c₂) * R.d k) ∧
      (∀ k, R.hessian (k + 1) = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k) +
          (R.curvature k)⁻¹ • outer (R.gradientChange k) (R.gradientChange k) ∧
        (Bhat k).PosSemidef ∧ Bhat k *ᵥ R.displacement k = 0) ∧
      ((∃ ℓ : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) → Summable R.d) := by
  refine ⟨fun k => ⟨R.positive_definite k, R.q_pos k, R.d_pos k, R.curvature_pos k⟩,
    fun k => ⟨R.armijo_decrease k, R.convexity_decrease_upper k, R.curvature_lower_bound k⟩,
    fun k => ⟨R.hessian_update k, ?_, ?_⟩,
    fun ⟨ℓ, hℓ⟩ => R.summable_predicted_decreases_of_value_limit ℓ hℓ⟩
  · rw [hBhat k]
    exact R.annihilated_hessian_posSemidef k
  · rw [hBhat k]
    exact R.annihilated_hessian_mul_displacement k

/-! ### Lemma `art:reference-energy` -/

/-- Item `A/energy/disp/006` (`paper/sections/energy.tex:76-79`): for a fixed $x_*$, put
$r_k=x_k-x_*$ and
\[ E_k=r_k^TB_kr_k,\qquad a_k=g_k^Tr_k,\qquad R_k=\frac{(y_k^Tr_{k+1})^2}{t_k}. \]
These are the library's `R.referenceEnergy xstar k`, `R.referencePairing xstar k` and
`R.referenceCorrection xstar k`. ($R_k$ is the variable `Rk`, since `R` names the run.) -/
theorem reference_notation {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (xstar : Vec n)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (r k) (R.hessian k *ᵥ r k))
    (a : ℕ → ℝ) (ha : ∀ k, a k = dot (R.g k) (r k))
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (k : ℕ) :
    E k = R.referenceEnergy xstar k ∧ a k = R.referencePairing xstar k ∧
      Rk k = R.referenceCorrection xstar k := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hE, hr]
    rfl
  · rw [ha, hr]
    rfl
  · rw [hRk, hr]
    rfl

/-- Item `A/energy/lemma/art:reference-energy` (`paper/sections/energy.tex:74-89`), Lemma
`art:reference-energy` (Reference energy), with its displays \eqref{art:energy-identity} and
\eqref{art:energy-budget}.

For any fixed $x_*$, put $r_k=x_k-x_*$, $E_k=r_k^TB_kr_k$, $a_k=g_k^Tr_k$,
$R_k=(y_k^Tr_{k+1})^2/t_k$. Then
\[ E_{k+1}=E_k-\frac{a_k^2}{q_k}+R_k. \]
If $x_*$ minimizes $F$, with $F_*=F(x_*)$, then
\[ (F(x_N)-F_*)^2\sum_{k<N}q_k^{-1}\le E_0+\sum_{k<N}R_k. \] -/
theorem reference_energy {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (xstar : Vec n)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (r k) (R.hessian k *ᵥ r k))
    (a : ℕ → ℝ) (ha : ∀ k, a k = dot (R.g k) (r k))
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (Fstar : ℝ) (hFstar : Fstar = F xstar) :
    (∀ k, E (k + 1) = E k - a k ^ 2 / R.q k + Rk k) ∧
      ((∀ z, F xstar ≤ F z) → ∀ N : ℕ,
        (F (R.x N) - Fstar) ^ 2 * ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤
          E 0 + ∑ k ∈ Finset.range N, Rk k) := by
  have hEf : E = R.referenceEnergy xstar :=
    funext fun k => (reference_notation R xstar r hr E hE a ha Rk hRk k).1
  have haf : a = R.referencePairing xstar :=
    funext fun k => (reference_notation R xstar r hr E hE a ha Rk hRk k).2.1
  have hRf : Rk = R.referenceCorrection xstar :=
    funext fun k => (reference_notation R xstar r hr E hE a ha Rk hRk k).2.2
  subst hEf haf hRf hFstar
  exact ⟨R.fixed_reference_energy xstar, R.fixed_reference_energy_bound xstar⟩

/-- Item `A/energy/disp/009` (`paper/sections/energy.tex:92-95`), in the proof of Lemma
`art:reference-energy`. With $r_k=x_k-x_*$ and $\widehat B_k$ of Lemma `art:run-invariants`
(the variable `Bhat` with its defining equation), since $r_{k+1}=r_k+s_k$ and
$\widehat B_ks_k=0$,
\[ r_{k+1}^TB_{k+1}r_{k+1}=r_k^T\widehat B_kr_k+\frac{(y_k^Tr_{k+1})^2}{t_k}. \] -/
theorem energy_step {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (xstar : Vec n)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (Bhat : ℕ → Mat n)
    (hBhat : ∀ k, Bhat k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) (k : ℕ) :
    dot (r (k + 1)) (R.hessian (k + 1) *ᵥ r (k + 1)) =
      dot (r k) (Bhat k *ᵥ r k) + dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k := by
  have hsymm : (Bhat k).IsSymm := by
    rw [hBhat k]
    exact R.annihilated_hessian_isSymm k
  have hker : Bhat k *ᵥ R.displacement k = 0 := by
    rw [hBhat k]
    exact R.annihilated_hessian_mul_displacement k
  have hr1 : r (k + 1) = r k + R.displacement k := by
    rw [hr, hr, R.step k]
    change R.x k + R.displacement k - xstar = R.x k - xstar + R.displacement k
    abel
  have hB1 : R.hessian (k + 1) =
      Bhat k + (R.curvature k)⁻¹ • outer (R.gradientChange k) (R.gradientChange k) := by
    rw [R.hessian_update k, hBhat k]
  change metricEnergy (R.hessian (k + 1)) (r (k + 1)) = metricEnergy (Bhat k) (r k) + _
  rw [hB1, EnergyIdentities.energy_add_matrix, EnergyIdentities.energy_smul_matrix,
    EnergyIdentities.energy_outer, hr1, EnergyIdentities.energy_add_kernel hsymm hker,
    div_eq_inv_mul]

/-- The budget of display `A/energy/disp/010` on a finite horizon, in the form its argument
gives: with the notation of Lemma `art:reference-energy`, a minimizer $x_*$ and $F_*=F(x_*)$, if
$F(x_N)-F_*\ge\eta>0$ and $R_k\le C$ for $k<N$, then \eqref{art:energy-budget} gives
\[ \eta^2\sum_{k<N}q_k^{-1}\le E_0+CN. \]
Unlike the hypotheses of the display (a gap for every $k$, $R_k\le C$ for every $k$), these are
satisfiable (example at the end: the quadratic run with $N=1$). -/
theorem persistent_gap_budget_general {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (Fstar : ℝ) (hFstar : Fstar = F xstar)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (r k) (R.hessian k *ᵥ r k))
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (η : ℝ) (hη : 0 < η) (N : ℕ) (hgapN : F (R.x N) - Fstar ≥ η)
    (C : ℝ) (hC : ∀ k, k < N → Rk k ≤ C) :
    η ^ 2 * ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤ E 0 + C * N := by
  have hbudget := (reference_energy R xstar r hr E hE (fun k => dot (R.g k) (r k))
    (fun _ => rfl) Rk hRk Fstar hFstar).2 hmin N
  have hS : 0 ≤ ∑ k ∈ Finset.range N, (R.q k)⁻¹ :=
    Finset.sum_nonneg fun k _ => (inv_pos.mpr (R.q_pos k)).le
  have hsq : η ^ 2 ≤ (F (R.x N) - Fstar) ^ 2 := by
    nlinarith
  have hsumC : ∑ k ∈ Finset.range N, Rk k ≤ C * N := by
    calc ∑ k ∈ Finset.range N, Rk k ≤ ∑ _k ∈ Finset.range N, C :=
          Finset.sum_le_sum fun k hk => hC k (Finset.mem_range.mp hk)
      _ = C * N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  calc η ^ 2 * ∑ k ∈ Finset.range N, (R.q k)⁻¹
      ≤ (F (R.x N) - Fstar) ^ 2 * ∑ k ∈ Finset.range N, (R.q k)⁻¹ :=
        mul_le_mul_of_nonneg_right hsq hS
    _ ≤ E 0 + ∑ k ∈ Finset.range N, Rk k := hbudget
    _ ≤ E 0 + C * N := by linarith

/-- Item `A/energy/disp/010` (`paper/sections/energy.tex:104-106`). With the notation of
Lemma `art:reference-energy`, a minimizer $x_*$ and $F_*=F(x_*)$: if a gap of at least
$\eta>0$ persists, $F(x_k)-F_*\ge\eta$ for all $k$, and the secant correction satisfies
$R_k\le C$ for all $k$, then \eqref{art:energy-budget} gives, for every $N$,
\[ \eta^2\sum_{k<N}q_k^{-1}\le E_0+CN. \]
These are the hypotheses of the reductio of lines 101-109: together with bounded gradients
they cannot all hold (`persistent_gap_contradiction`); without bounded gradients their
satisfiability is not settled here. The proof is `persistent_gap_budget_general` (the gap only
at $N$, $R_k\le C$ only for $k<N$), whose assumptions are satisfiable. -/
theorem persistent_gap_budget {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (Fstar : ℝ) (hFstar : Fstar = F xstar)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (r k) (R.hessian k *ᵥ r k))
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (η : ℝ) (hη : 0 < η) (hgap : ∀ k, F (R.x k) - Fstar ≥ η)
    (C : ℝ) (hC : ∀ k, Rk k ≤ C) (N : ℕ) :
    η ^ 2 * ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤ E 0 + C * N :=
  persistent_gap_budget_general R xstar hmin Fstar hFstar r hr E hE Rk hRk η hη N (hgap N) C
    fun k _ => hC k

/-- The bound of item `A/energy/prose/011` on a finite horizon: under the assumptions of
`persistent_gap_budget_general` (the gap at $N$, $R_k\le C$ for $k<N$, all satisfiable),
\[ \sum_{k<N}q_k^{-1}\le\frac{E_0}{\eta^2}+\frac{C}{\eta^2}N. \] -/
theorem reciprocal_sum_linear_general {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (Fstar : ℝ) (hFstar : Fstar = F xstar)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (r k) (R.hessian k *ᵥ r k))
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (η : ℝ) (hη : 0 < η) (N : ℕ) (hgapN : F (R.x N) - Fstar ≥ η)
    (C : ℝ) (hC : ∀ k, k < N → Rk k ≤ C) :
    ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤ E 0 / η ^ 2 + C / η ^ 2 * N := by
  have h := persistent_gap_budget_general R xstar hmin Fstar hFstar r hr E hE Rk hRk η hη N
    hgapN C hC
  have hη2 : 0 < η ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_add_div_same, le_div_iff₀ hη2]
  linarith

/-- Item `A/energy/prose/011` (`paper/sections/energy.tex:107-109`): "Thus an objective-level
bound on one component of a gradient jump would force the reciprocal sum to grow at most
linearly." Under the assumptions of display `A/energy/disp/010`,
\[ \sum_{k<N}q_k^{-1}\le\frac{E_0}{\eta^2}+\frac{C}{\eta^2}N\qquad\text{for every }N. \]
Proved from `reciprocal_sum_linear_general`, whose finite-horizon assumptions are satisfiable. -/
theorem reciprocal_sum_linear {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (Fstar : ℝ) (hFstar : Fstar = F xstar)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (r k) (R.hessian k *ᵥ r k))
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (η : ℝ) (hη : 0 < η) (hgap : ∀ k, F (R.x k) - Fstar ≥ η)
    (C : ℝ) (hC : ∀ k, Rk k ≤ C) (N : ℕ) :
    ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤ E 0 / η ^ 2 + C / η ^ 2 * N :=
  reciprocal_sum_linear_general R xstar hmin Fstar hFstar r hr E hE Rk hRk η hη N (hgap N) C
    fun k _ => hC k

/-- Item `A/energy/prose/013` (`paper/sections/energy.tex:109-112`): "the initial energy is
finite, and the later energies need only remain nonnegative." For every fixed $x_*$ and
every $k$, $E_k=r_k^TB_kr_k\ge0$ (and $E_0$ is a real number). -/
theorem energy_nonneg {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (xstar : Vec n)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (r k) (R.hessian k *ᵥ r k)) (k : ℕ) :
    0 ≤ E k := by
  rw [(reference_notation R xstar r hr E hE (fun k => dot (R.g k) (r k)) (fun _ => rfl)
    (fun k => dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k) (fun _ => rfl) k).1]
  exact R.referenceEnergy_nonneg xstar k

/-! ### Principal-minor sums -/

/-- Selecting the columns of `U` indexed by `I` is multiplication by `coordinateMatrix I`. -/
theorem columnSelection_eq {n : ℕ} (U : Mat n) (I : Finset (Fin n)) :
    U.submatrix id (fun i : I => (i : Fin n)) = U * coordinateMatrix I := by
  ext a b
  simp [coordinateMatrix, Matrix.mul_apply, Matrix.one_apply]

/-- Item `A/energy/disp/011` (`paper/sections/energy.tex:117-120`): for a symmetric
$n\times n$ matrix $H$,
\[ e_j(H)=\sum_{I\subset\{1,\ldots,n\},\ |I|=j}\det H_{I,I},\qquad e_{n+1}(H)=0. \]
The library's `principalSum H j` is literally the first sum, over the `j`-element subsets
of `Fin n`; the convention $e_{n+1}(H)=0$ is a consequence (there are no such subsets). -/
theorem principalSum_def {n : ℕ} (H : Mat n) (j : ℕ) :
    principalSum H j = ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (H.submatrix (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n))).det ∧
      principalSum H (n + 1) = 0 :=
  ⟨rfl, principalSum_terminal H⟩

/-- Item `A/energy/prose/014` (`paper/sections/energy.tex:121-123`): "Multilinearity of the
determinant identifies these sums with the coefficients of $\det(I+zH)$; hence they are
invariant under orthogonal changes of coordinates and equal the elementary symmetric
polynomials of the eigenvalues."

For a symmetric $H$ (`H.IsHermitian`, which for a real matrix says $H^T=H$): the coefficient
of $z^j$ in the polynomial $\det(I+zH)$ is $e_j(H)$, so
$\det(I+zH)=\sum_{j=0}^ne_j(H)z^j$ for every real $z$; $e_j(Q^THQ)=e_j(H)$ for every
orthogonal $Q$; and $e_j(H)$ is the $j$-th elementary symmetric polynomial of the
eigenvalues `hH.eigenvalues` (with multiplicity). -/
theorem principal_sums_coefficients {n : ℕ} (H : Mat n) (hH : H.IsHermitian) :
    (∀ j : ℕ, (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • H.map Polynomial.C)).coeff j =
      principalSum H j) ∧
    (∀ z : ℝ, (1 + z • H).det = ∑ j ∈ Finset.range (n + 1), principalSum H j * z ^ j) ∧
    (∀ Q : Mat n, Qᵀ * Q = 1 → ∀ j : ℕ, principalSum (Qᵀ * H * Q) j = principalSum H j) ∧
    (∀ j : ℕ, principalSum H j = (Multiset.map hH.eigenvalues Finset.univ.val).esymm j) := by
  have hcoeff : ∀ j : ℕ,
      (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • H.map Polynomial.C)).coeff j =
        principalSum H j :=
    PrincipalInvariance.principalPolynomial_coeff H
  refine ⟨hcoeff, fun z => ?_,
    fun Q hQ j => PrincipalInvariance.principalSum_conjugate Qᵀ Q H hQ j, fun j => ?_⟩
  · have hdeg : (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • H.map Polynomial.C)).natDegree <
        n + 1 := by
      rw [Nat.lt_succ_iff, Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hcoeff]
      exact principalSum_eq_zero_of_dimension_lt H hN
    have heval : Polynomial.eval z
        (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • H.map Polynomial.C)) =
          (1 + z • H).det := by
      rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
      congr 1
      ext i k
      simp [Matrix.one_apply, apply_ite]
      ring
    rw [← heval, Polynomial.eval_eq_sum_range' hdeg]
    simp_rw [hcoeff]
  · rw [Finset.esymm_map_val]
    have hUU : star (hH.eigenvectorUnitary : Mat n) * (hH.eigenvectorUnitary : Mat n) = 1 :=
      unitary.coe_star_mul_self _
    have hid : (RCLike.ofReal ∘ hH.eigenvalues : Fin n → ℝ) = hH.eigenvalues := by
      funext i
      simp
    rw [← PrincipalInvariance.principalSum_conjugate _ _ H hUU j,
      hH.star_mul_self_mul_eq_diagonal, hid, principalSum_diagonal]

/-- Item `A/energy/prose/015` (`paper/sections/energy.tex:123`): "In particular $e_1=\tr$ and
$e_n=\det$." -/
theorem principal_trace_det {n : ℕ} (H : Mat n) (_hH : H.IsSymm) :
    principalSum H 1 = H.trace ∧ principalSum H n = H.det :=
  ⟨principalSum_one H, principalSum_top H⟩

/-- Item `A/energy/prose/017` (`paper/sections/energy.tex:125-127`): "The determinant records
volume, while the intermediate principal-minor sums retain information about
different-dimensional compressions." For a symmetric $H$: the linear map $x\mapsto Hx$
multiplies Lebesgue measure by $|\det H|$; and for every orthonormal basis $U$ (columns
$u_1,\dots,u_n$) and every $j$, $e_j(H)=\sum_{|I|=j}\det(Z_I^THZ_I)$, the sum of the
determinants of the $j$-dimensional compressions of $H$ to the coordinate subspaces of the
basis ($Z_I$ selects the columns $u_i$, $i\in I$). -/
theorem compressions_and_volume {n : ℕ} (H : Mat n) (_hH : H.IsSymm) :
    (∀ S : Set (Vec n), MeasureTheory.volume (Matrix.toLin' H '' S) =
      ENNReal.ofReal |H.det| * MeasureTheory.volume S) ∧
    ∀ U : Mat n, Uᵀ * U = 1 → ∀ j : ℕ,
      principalSum H j = ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        ((U.submatrix id (fun i : I => (i : Fin n)))ᵀ * H *
          U.submatrix id (fun i : I => (i : Fin n))).det := by
  refine ⟨fun S => by rw [MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin'],
    fun U hU j => ?_⟩
  rw [← sum_transformed_coordinate_grams H U hU j]
  apply Finset.sum_congr rfl
  intro I _
  rw [columnSelection_eq]
  rfl

/-! ### Theorem `art:minor-hierarchy` -/

/-- Item `A/energy/theorem/art:minor-hierarchy` (`paper/sections/energy.tex:131-142`), Theorem
`art:minor-hierarchy` (Principal-minor hierarchy), with its displays `A/energy/disp/012`
and \eqref{art:hierarchy}.

Let $H\succ0$, $s=-\alpha Hg$, $\alpha>0$, and suppose $q=g^THg>0$,
$\beta=-y^THg/q>0$. For the inverse-BFGS update $H_+$ in \eqref{art:update},
\[ e_j(H_+)\le\frac{\|y\|^2}{\beta^2q}e_{j+1}(H)+\frac\alpha\beta e_j(H),\qquad
   1\le j\le n. \]
At $j=n$ the exact identity is $\det H_+=(\alpha/\beta)\det H$.

The standing assumptions are written out as in `MatrixAlgebra.lean`; $\|y\|^2$ is
`sqNorm y` and $e_j$ is `principalSum`. The inequality is the library's
`principalMinorHierarchy`, the identity its `inverseBFGS_step_det_beta`. -/
theorem minor_hierarchy {n : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (hHplus : Hplus = inverseBFGS H s y) :
    (∀ j : ℕ, 1 ≤ j → j ≤ n →
      principalSum Hplus j ≤
        sqNorm y / (β ^ 2 * q) * principalSum H (j + 1) + α / β * principalSum H j) ∧
      Hplus.det = α / β * H.det := by
  have hq' : 0 < metricEnergy H g := by
    rw [hq_def] at hq
    exact hq
  have hβeq : -dot y (H.mulVec g) / metricEnergy H g = β := by
    rw [hβ_def, hq_def]
    rfl
  have hβ' : 0 < -dot y (H.mulVec g) / metricEnergy H g := by
    rw [hβeq]
    exact hβ
  have hg : g ≠ 0 := by
    rintro rfl
    simp [metricEnergy, dot] at hq'
  have ht : 0 < dot y (bfgsStep H g α) := by
    rw [curvature_eq_alpha_beta_q H g y α hq'.ne', hβeq]
    exact mul_pos (mul_pos hα hβ) hq'
  have hdet := inverseBFGS_step_det_beta hH hg y hα ht
  rw [hβeq] at hdet
  refine ⟨fun j hj hjn => ?_, ?_⟩
  · have h := principalMinorHierarchy n H g y α hH hα hq' hβ' j hj hjn
    subst hHplus hs hβ_def hq_def
    exact h
  · subst hHplus hs
    exact hdet

/-- Item `A/energy/disp/014` (`paper/sections/energy.tex:146-150`), in the proof of Theorem
`art:minor-hierarchy`. Under the assumptions of the theorem, for $1\le j\le n$ and $Z$ with
$j$ orthonormal columns (`Zᵀ * Z = 1`), Lemma `art:gram-compression` gives
\[ \det(Z^TH_+Z)\le\frac{\det\operatorname{Gram}_H(y,Z)}{\beta^2q}
   +\frac\alpha\beta\det(Z^THZ), \]
where $\operatorname{Gram}_H(y,Z)=[y\ Z]^TH[y\ Z]$ is
`metricGram H (fromCols (replicateCol Unit y) Z)`. -/
theorem compression_bound {n : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (hHplus : Hplus = inverseBFGS H s y) (j : ℕ) (_hj : 1 ≤ j) (_hjn : j ≤ n)
    (Z : Matrix (Fin n) (Fin j) ℝ) (hZ : Zᵀ * Z = 1) :
    (Zᵀ * Hplus * Z).det ≤
      (metricGram H (fromCols (replicateCol Unit y) Z)).det / (β ^ 2 * q) +
        α / β * (Zᵀ * H * Z).det := by
  have hq' : 0 < metricEnergy H g := by
    rw [hq_def] at hq
    exact hq
  have hβ' : 0 < -dot y (H.mulVec g) / metricEnergy H g := by
    have h : -dot y (H.mulVec g) / metricEnergy H g = β := by
      rw [hβ_def, hq_def]
      rfl
    rw [h]
    exact hβ
  have h := BFGSCompression.compressed_inverseBFGS_bound H Z g y α hH
    (mulVec_injective_of_orthonormal hZ) hα hq' hβ'
  subst hHplus hs hβ_def hq_def
  exact h

/-- Item `A/energy/disp/015` (`paper/sections/energy.tex:155-162`), in the proof of Theorem
`art:minor-hierarchy`. Under the assumptions of the theorem and $1\le j\le n$, choose an
orthonormal eigenbasis of $H$: `U` with `Uᵀ * U = 1` and `H * U = U * diagonal lam`
(column $i$ is an eigenvector with eigenvalue $\lambda_i>0$), and write $y_i$ (`yc i`) for
the coordinates of $y$ in this basis, `yc = Uᵀ *ᵥ y`. Its $j$-column selections $Z_I$ are
`U.submatrix id (fun i : I => i)`. Then
\[ \sum_{|I|=j}\det\operatorname{Gram}_H(y,Z_I)
   =\sum_{|I|=j}\Bigl(\prod_{i\in I}\lambda_i\Bigr)\sum_{\ell\notin I}\lambda_\ell y_\ell^2
   =\sum_{|J|=j+1}\Bigl(\prod_{i\in J}\lambda_i\Bigr)\sum_{\ell\in J}y_\ell^2
   \le\|y\|^2e_{j+1}(H). \] -/
theorem eigenbasis_gram_sum {n : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (_hH : H.PosDef) (_hs : s = -α • (H *ᵥ g)) (_hα : 0 < α)
    (_hq_def : q = dot g (H *ᵥ g)) (_hq : 0 < q)
    (_hβ_def : β = -dot y (H *ᵥ g) / q) (_hβ : 0 < β)
    (_hHplus : Hplus = inverseBFGS H s y) (j : ℕ) (_hj : 1 ≤ j) (_hjn : j ≤ n)
    (U : Mat n) (hU : Uᵀ * U = 1) (lam : Fin n → ℝ) (hHU : H * U = U * Matrix.diagonal lam)
    (hlam : ∀ i, 0 < lam i) (yc : Vec n) (hyc : yc = Uᵀ *ᵥ y) :
    ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (metricGram H (fromCols (replicateCol Unit y)
          (U.submatrix id (fun i : I => (i : Fin n))))).det =
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (∏ i ∈ I, lam i) * ∑ ℓ ∈ Finset.univ \ I, lam ℓ * yc ℓ ^ 2 ∧
    ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (∏ i ∈ I, lam i) * ∑ ℓ ∈ Finset.univ \ I, lam ℓ * yc ℓ ^ 2 =
      ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j + 1),
        (∏ i ∈ J, lam i) * ∑ ℓ ∈ J, yc ℓ ^ 2 ∧
    ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j + 1),
        (∏ i ∈ J, lam i) * ∑ ℓ ∈ J, yc ℓ ^ 2 ≤ sqNorm y * principalSum H (j + 1) := by
  have hUR : U * Uᵀ = 1 := Matrix.mul_eq_one_comm.mp hU
  have hdiag : Uᵀ * H * U = Matrix.diagonal lam := by
    rw [Matrix.mul_assoc, hHU, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hfirst : ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (metricGram H (fromCols (replicateCol Unit y)
          (U.submatrix id (fun i : I => (i : Fin n))))).det =
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (∏ i ∈ I, lam i) * ∑ ℓ ∈ Finset.univ \ I, lam ℓ * yc ℓ ^ 2 := by
    apply Finset.sum_congr rfl
    intro I _
    rw [columnSelection_eq, metricGram_append_orthogonal H U hUR y, hdiag,
      diagonal_coordinate_gram_det lam hlam, hyc]
  have hsecond := principal_product_augmented_sum_eq lam yc j
  refine ⟨hfirst, hsecond, ?_⟩
  calc _ = ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
          (∏ i ∈ I, lam i) * ∑ ℓ ∈ Finset.univ \ I, lam ℓ * yc ℓ ^ 2 := hsecond.symm
    _ ≤ sqNorm yc * ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard (j + 1), ∏ i ∈ J, lam i :=
        principal_product_augmented_sum_le lam (fun i => (hlam i).le) yc j
    _ = sqNorm y * principalSum H (j + 1) := by
        rw [← principalSum_diagonal, ← hdiag,
          PrincipalInvariance.principalSum_conjugate Uᵀ U H hU, hyc,
          sqNorm_orthogonal_coordinates U hUR y]

/-! ### Theorem `art:reciprocal-growth` -/

/-- Item `A/energy/theorem/art:reciprocal-growth` (`paper/sections/energy.tex:169-175`),
Theorem `art:reciprocal-growth` (Reciprocal growth), with its display
\eqref{art:reciprocal-limits}.

If an admissible run has bounded gradients and $d_k\to0$, then
\[ \Bigl(\prod_{k<N}q_k^{-1}\Bigr)^{1/N}\longrightarrow+\infty,\qquad
   \frac1N\sum_{k<N}q_k^{-1}\longrightarrow+\infty. \]
"Bounded gradients" is $\exists\Lambda\ \forall k\ \|g_k\|\le\Lambda$ with the Euclidean norm
(`‖euclideanVector (R.g k)‖`; every norm gives the same notion). The power is the real power
`x ^ (1 / (N : ℝ))`. The library proves this as `objectiveReciprocalGrowth`, from
`reciprocalGrowth` through `toFullBFGSRun` and `beta_lower_bound`. -/
theorem reciprocal_growth {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (hd : Tendsto R.d atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∏ k ∈ Finset.range N, (R.q k)⁻¹) ^ (1 / (N : ℝ))) atTop atTop ∧
      Tendsto (fun N : ℕ => 1 / (N : ℝ) * ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop := by
  obtain ⟨G, hG, hg⟩ := sqNorm_bound_of_bounded R.g hbdd
  obtain ⟨h1, h2⟩ := objectiveReciprocalGrowth n F R G hG hg hd
  refine ⟨h1.congr fun N => ?_, h2.congr fun N => ?_⟩
  · rw [reciprocalGeometricMean, one_div]
  · rw [reciprocalMean, div_eq_inv_mul, one_div]

/-- The weighted potential $\sum_{j=1}^n r^{j-1}e_j$ in the library's indexing. -/
theorem potential_eq_weighted (n : ℕ) (r : ℝ) (e : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 n, r ^ (j - 1) * e j = ScalarHierarchy.weightedPotential n r e := by
  rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range, ScalarHierarchy.weightedPotential,
    Nat.succ_sub_one]
  apply Finset.sum_congr rfl
  intro j _
  rw [show 1 + j - 1 = j by omega, add_comm 1 j]

/-- Item `A/energy/disp/017` (`paper/sections/energy.tex:179-182`), in the proof of Theorem
`art:reciprocal-growth`. Under the assumptions of the theorem, with $\Lambda>0$,
$\|g_k\|\le\Lambda$ for all $k$, and $K_0=4\Lambda^2/\omega^2$: for the actual run, for every $k$,
\[ \beta_k=\frac{t_k}{d_k}\ge\omega,\qquad \|y_k\|\le2\Lambda,\qquad
   \alpha_k=\frac{d_k}{q_k}. \]
$\beta_k$ is the $\beta$ of Theorem `art:minor-hierarchy` for the $k$-th update, `R.beta k`
$=-y_k^TH_kg_k/q_k$; the display's first equality is then an identity. -/
theorem run_bounds {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hd : Tendsto R.d atTop (𝓝 0))
    (Λ : ℝ) (_hΛ : 0 < Λ) (hgΛ : ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ)
    (K0 : ℝ) (_hK0 : K0 = 4 * Λ ^ 2 / (1 - R.c₂) ^ 2) (k : ℕ) :
    R.beta k = R.curvature k / R.d k ∧ R.curvature k / R.d k ≥ 1 - R.c₂ ∧
      ‖euclideanVector (R.gradientChange k)‖ ≤ 2 * Λ ∧ R.α k = R.d k / R.q k := by
  have hq := R.q_pos k
  have hdpos := R.d_pos k
  have hq0 := hq.ne'
  have hα0 := (R.alpha_pos k).ne'
  have hcurv : R.curvature k = R.α k * R.beta k * R.q k :=
    curvature_eq_alpha_beta_q (R.H k) (R.g k) (R.g (k + 1) - R.g k) (R.α k) hq0
  have hd : R.d k = R.α k * R.q k := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcurv, hd]
    field_simp
    ring
  · rw [ge_iff_le, le_div_iff₀ hdpos]
    exact R.curvature_lower_bound k
  · change ‖euclideanVector (R.g (k + 1) - R.g k)‖ ≤ 2 * Λ
    rw [euclideanVector_sub]
    calc _ ≤ ‖euclideanVector (R.g (k + 1))‖ + ‖euclideanVector (R.g k)‖ := norm_sub_le _ _
      _ ≤ Λ + Λ := add_le_add (hgΛ (k + 1)) (hgΛ k)
      _ = 2 * Λ := by ring
  · rw [hd]
    field_simp

/-- Item `A/energy/disp/018` (`paper/sections/energy.tex:184-187`), equation
`art:normalized-hierarchy`, in the proof of Theorem `art:reciprocal-growth`. Under
the assumptions of display `A/energy/disp/017`, for every $k$ and $1\le j\le n$,
\[ q_ke_j(H_{k+1})\le K_0e_{j+1}(H_k)+\frac{d_k}{\omega}e_j(H_k). \]
(The library's `fullBFGS_normalizedHierarchy`, applied to the run's own matrices.) -/
theorem normalized_hierarchy {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hd : Tendsto R.d atTop (𝓝 0))
    (Λ : ℝ) (hΛ : 0 < Λ) (hgΛ : ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ)
    (K0 : ℝ) (hK0 : K0 = 4 * Λ ^ 2 / (1 - R.c₂) ^ 2) (k j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    R.q k * principalSum (R.H (k + 1)) j ≤
      K0 * principalSum (R.H k) (j + 1) + R.d k / (1 - R.c₂) * principalSum (R.H k) j := by
  have hg : ∀ k, sqNorm (R.toFullBFGSRun.g k) ≤ Λ ^ 2 := fun k => sqNorm_le_of_norm_le (hgΛ k)
  have h := (fullBFGS_normalizedHierarchy R.toFullBFGSRun Λ (1 - R.c₂) hΛ R.wolfe_constant_pos
    hg R.beta_lower_bound).step k j hj hjn
  rw [hK0]
  exact h

/-- Item `A/energy/disp/019` (`paper/sections/energy.tex:192-194`), in the proof of Theorem
`art:reciprocal-growth`. Under the assumptions of display `A/energy/disp/017`, fix $\eta>0$
and $J$ with $d_k/\omega\le\eta$ for $k\ge J$. For $H\succ0$ define
$V_\eta(H)=\sum_{j=1}^n(K_0/\eta)^{j-1}e_j(H)$ (the variable `V`, specified on positive
definite matrices). Then $V_\eta(H)>0$ for every $H\succ0$. -/
theorem potential_pos {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hd : Tendsto R.d atTop (𝓝 0))
    (Λ : ℝ) (_hΛ : 0 < Λ) (_hgΛ : ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ)
    (K0 : ℝ) (hK0 : K0 = 4 * Λ ^ 2 / (1 - R.c₂) ^ 2)
    (η : ℝ) (hη : 0 < η) (J : ℕ) (_hJ : ∀ k, J ≤ k → R.d k / (1 - R.c₂) ≤ η)
    (V : Mat n → ℝ)
    (hV : ∀ H : Mat n, H.PosDef →
      V H = ∑ j ∈ Finset.Icc 1 n, (K0 / η) ^ (j - 1) * principalSum H j) :
    ∀ H : Mat n, H.PosDef → 0 < V H := by
  intro H hH
  have hn := R.dimension_pos
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    positivity
  rw [hV H hH, potential_eq_weighted]
  exact lt_of_lt_of_le (principalSum_one_pos hH hn)
    (ScalarHierarchy.first_le_weighted n _ _ hn (div_nonneg hK0nn hη.le)
      (principalSum_nonneg hH.posSemidef))

/-- Proof of Theorem `art:reciprocal-growth`, undisplayed claim of
`paper/sections/energy.tex:197` (not a register item): under the assumptions of display
`A/energy/disp/019`, $q_k\le\Lambda^2\tr H_k\le\Lambda^2V_\eta(H_k)$. -/
theorem q_le_potential {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hd : Tendsto R.d atTop (𝓝 0))
    (Λ : ℝ) (_hΛ : 0 < Λ) (hgΛ : ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ)
    (K0 : ℝ) (hK0 : K0 = 4 * Λ ^ 2 / (1 - R.c₂) ^ 2)
    (η : ℝ) (hη : 0 < η) (J : ℕ) (_hJ : ∀ k, J ≤ k → R.d k / (1 - R.c₂) ≤ η)
    (V : Mat n → ℝ)
    (hV : ∀ H : Mat n, H.PosDef →
      V H = ∑ j ∈ Finset.Icc 1 n, (K0 / η) ^ (j - 1) * principalSum H j) (k : ℕ) :
    R.q k ≤ Λ ^ 2 * (R.H k).trace ∧ Λ ^ 2 * (R.H k).trace ≤ Λ ^ 2 * V (R.H k) := by
  have hH := R.positive_definite k
  have hn := R.dimension_pos
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    positivity
  constructor
  · calc R.q k ≤ sqNorm (R.g k) * (R.H k).trace :=
          metricEnergy_le_sqNorm_mul_trace (R.H k) (R.g k) hH.posSemidef
      _ ≤ Λ ^ 2 * (R.H k).trace :=
          mul_le_mul_of_nonneg_right (sqNorm_le_of_norm_le (hgΛ k))
            (trace_pos_of_posDef hH hn).le
  · apply mul_le_mul_of_nonneg_left _ (sq_nonneg Λ)
    rw [hV _ hH, potential_eq_weighted, ← principalSum_one]
    exact ScalarHierarchy.first_le_weighted n _ _ hn (div_nonneg hK0nn hη.le)
      (principalSum_nonneg hH.posSemidef)

/-- Item `A/energy/disp/020` (`paper/sections/energy.tex:198-202`), in the proof of Theorem
`art:reciprocal-growth`. Under the assumptions of display `A/energy/disp/019`,
\[ V_\eta(H_{k+1})\le\frac{2\eta}{q_k}V_\eta(H_k)\quad(k\ge J),\qquad
   \prod_{k=J}^{J+m-1}q_k^{-1}\ge\frac{1}{\Lambda^2V_\eta(H_J)(2\eta)^{m-1}}\quad(m\ge1). \]
The product over $k=J,\dots,J+m-1$ is over `Finset.Ico J (J + m)`. -/
theorem potential_contraction {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (_hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (_hd : Tendsto R.d atTop (𝓝 0))
    (Λ : ℝ) (hΛ : 0 < Λ) (hgΛ : ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ)
    (K0 : ℝ) (hK0 : K0 = 4 * Λ ^ 2 / (1 - R.c₂) ^ 2)
    (η : ℝ) (hη : 0 < η) (J : ℕ) (hJ : ∀ k, J ≤ k → R.d k / (1 - R.c₂) ≤ η)
    (V : Mat n → ℝ)
    (hV : ∀ H : Mat n, H.PosDef →
      V H = ∑ j ∈ Finset.Icc 1 n, (K0 / η) ^ (j - 1) * principalSum H j) :
    (∀ k, J ≤ k → V (R.H (k + 1)) ≤ 2 * η / R.q k * V (R.H k)) ∧
      ∀ m : ℕ, 1 ≤ m →
        ∏ k ∈ Finset.Ico J (J + m), (R.q k)⁻¹ ≥ 1 / (Λ ^ 2 * V (R.H J) * (2 * η) ^ (m - 1)) := by
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    positivity
  have hVpos : ∀ k, 0 < V (R.H k) := fun k =>
    potential_pos R _hbdd _hd Λ hΛ hgΛ K0 hK0 η hη J hJ V hV (R.H k) (R.positive_definite k)
  have hVw : ∀ k, V (R.H k) =
      ScalarHierarchy.weightedPotential n (K0 / η) (principalSum (R.H k)) := fun k =>
    (hV _ (R.positive_definite k)).trans (potential_eq_weighted n _ _)
  have hcontr : ∀ k, J ≤ k → V (R.H (k + 1)) ≤ 2 * η / R.q k * V (R.H k) := by
    intro k hk
    have hq := R.q_pos k
    have hstep := ScalarHierarchy.weighted_step n (principalSum (R.H k))
      (principalSum (R.H (k + 1))) (R.q k) K0 η (R.d k / (1 - R.c₂)) hK0nn hη
      (principalSum_nonneg (R.positive_definite k).posSemidef) (principalSum_terminal (R.H k))
      (fun j hj hjn => normalized_hierarchy R _hbdd _hd Λ hΛ hgΛ K0 hK0 k j hj hjn)
    rw [← hVw k, ← hVw (k + 1)] at hstep
    have hfac : η + R.d k / (1 - R.c₂) ≤ 2 * η := by linarith [hJ k hk]
    have h2 : R.q k * V (R.H (k + 1)) ≤ 2 * η * V (R.H k) :=
      hstep.trans (mul_le_mul_of_nonneg_right hfac (hVpos k).le)
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]
    linarith
  refine ⟨hcontr, fun m hm => ?_⟩
  have hqV : ∀ k, R.q k ≤ Λ ^ 2 * V (R.H k) := fun k =>
    let h := q_le_potential R _hbdd _hd Λ hΛ hgΛ K0 hK0 η hη J hJ V hV k
    h.1.trans h.2
  have htel : ∀ i : ℕ, V (R.H (J + i)) ≤
      (2 * η) ^ i * V (R.H J) * ∏ l ∈ Finset.range i, (R.q (J + l))⁻¹ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hq := R.q_pos (J + i)
      have h1 := hcontr (J + i) (Nat.le_add_right J i)
      rw [Finset.prod_range_succ, pow_succ, ← add_assoc]
      calc V (R.H (J + i + 1)) ≤ 2 * η / R.q (J + i) * V (R.H (J + i)) := h1
        _ ≤ 2 * η / R.q (J + i) *
            ((2 * η) ^ i * V (R.H J) * ∏ l ∈ Finset.range i, (R.q (J + l))⁻¹) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (2 * η) ^ i * (2 * η) * V (R.H J) *
            ((∏ l ∈ Finset.range i, (R.q (J + l))⁻¹) * (R.q (J + i))⁻¹) := by
          rw [div_eq_mul_inv]
          ring
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Finset.prod_Ico_eq_prod_range, show J + (m' + 1) - J = m' + 1 by omega,
    Finset.prod_range_succ, show m' + 1 - 1 = m' by omega]
  have hq := R.q_pos (J + m')
  have hVJ := hVpos J
  have hbound : R.q (J + m') ≤
      Λ ^ 2 * ((2 * η) ^ m' * V (R.H J) * ∏ l ∈ Finset.range m', (R.q (J + l))⁻¹) :=
    (hqV (J + m')).trans (mul_le_mul_of_nonneg_left (htel m') (sq_nonneg Λ))
  rw [ge_iff_le, div_le_iff₀ (mul_pos (mul_pos (pow_pos hΛ 2) hVJ) (pow_pos (by positivity) m'))]
  calc (1 : ℝ) = (R.q (J + m'))⁻¹ * R.q (J + m') := (inv_mul_cancel₀ hq.ne').symm
    _ ≤ (R.q (J + m'))⁻¹ *
        (Λ ^ 2 * ((2 * η) ^ m' * V (R.H J) * ∏ l ∈ Finset.range m', (R.q (J + l))⁻¹)) :=
      mul_le_mul_of_nonneg_left hbound (inv_pos.mpr hq).le
    _ = _ := by ring

/-- Item `A/energy/prose/012` (`paper/sections/energy.tex:108-110`): "Theorem
`art:reciprocal-growth` proves that, along runs with bounded gradients, the full update requires
faster growth" (corrected on 15 October 2026, M10). It used to read "The next theorem proves that
the full update requires faster growth": in text order the next theorem is Theorem
`art:minor-hierarchy`, a one-step inequality, and the faster growth, Theorem
`art:reciprocal-growth`, needs bounded gradients (and $d_k\to0$, which the paragraph's minimizer
gives). Lean statement: if an admissible run has bounded gradients and $d_k\to0$, the reciprocal
sum is not $O(N)$, i.e. there are no $A,B$ with $\sum_{k<N}q_k^{-1}\le A+BN$ for all $N$. -/
theorem reciprocal_sum_superlinear {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (hd : Tendsto R.d atTop (𝓝 0)) :
    ¬ ∃ A B : ℝ, ∀ N : ℕ, ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤ A + B * N := by
  rintro ⟨A, B, hAB⟩
  have hmean := (reciprocal_growth R hbdd hd).2
  obtain ⟨N, hN1, hN⟩ := ((eventually_ge_atTop 1).and
    (hmean.eventually (eventually_gt_atTop (|A| + B)))).exists
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hle : 1 / (N : ℝ) * ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤ |A| + B := by
    rw [one_div, inv_mul_le_iff₀ hNpos]
    have h1 := hAB N
    have h2 : |A| ≤ |A| * N := le_mul_of_one_le_right (abs_nonneg A) hN1'
    nlinarith [le_abs_self A]
  linarith

/-- The claim of item `A/energy/prose/012` (as corrected, M10) in the setting of its paragraph
(`paper/sections/energy.tex:101-110`), where $x_*$ minimizes $F$: the values are then bounded
below, Armijo gives $d_k\to0$, and bounded gradients alone exclude
$\sum_{k<N}q_k^{-1}\le A+BN$ for all $N$. -/
theorem reciprocal_sum_superlinear_of_minimizer {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ)
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) :
    ¬ ∃ A B : ℝ, ∀ N : ℕ, ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤ A + B * N :=
  reciprocal_sum_superlinear R hbdd
    (R.summable_predicted_decreases_of_lower_bound (F xstar)
      fun k => hmin (R.x k)).tendsto_atTop_zero

/-- Item `A/energy/prose/010` (`paper/sections/energy.tex:101`): "The identity makes the
intended contradiction visible." For an admissible run with bounded gradients and
$d_k\to0$, a minimizer $x_*$ with $F_*=F(x_*)$, and the notation of Lemma
`art:reference-energy`: if the secant corrections are bounded, $R_k\le C$, the gap
$F(x_k)-F_*$ cannot stay $\ge\eta>0$ for all $k$ (display `A/energy/disp/010` against
Theorem `art:reciprocal-growth`). -/
theorem persistent_gap_contradiction {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (hd : Tendsto R.d atTop (𝓝 0))
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (Fstar : ℝ) (hFstar : Fstar = F xstar)
    (r : ℕ → Vec n) (hr : ∀ k, r k = R.x k - xstar)
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (r k) (R.hessian k *ᵥ r k))
    (Rk : ℕ → ℝ) (hRk : ∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k)
    (η : ℝ) (hη : 0 < η) (C : ℝ) (hC : ∀ k, Rk k ≤ C) :
    ¬ ∀ k, F (R.x k) - Fstar ≥ η := by
  intro hgap
  exact reciprocal_sum_superlinear R hbdd hd ⟨E 0 / η ^ 2, C / η ^ 2,
    reciprocal_sum_linear R xstar hmin Fstar hFstar r hr E hE Rk hRk η hη hgap C hC⟩

/-- Item `A/energy/prose/021` (`paper/sections/energy.tex:213-214`): "The assumption $d_k\to0$
is weaker than the summability supplied by Armijo on a compact sublevel." For every admissible
run: a compact initial sublevel $\{F\le F(x_0)\}$ gives $\sum_kd_k<\infty$, and
$\sum_kd_k<\infty$ implies $d_k\to0$. -/
theorem summability_stronger {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    (IsCompact {x | F x ≤ F (R.x 0)} → Summable R.d) ∧
      (Summable R.d → Tendsto R.d atTop (𝓝 0)) :=
  ⟨fun hK => R.summable_predicted_decreases_of_compact_sublevel hK,
    fun hs => hs.tendsto_atTop_zero⟩

/-- Item `A/energy/prose/022` (`paper/sections/energy.tex:214-217`): "Finite-horizon bounds
and the stronger reciprocal-sum consequence under summability are retained in the companion's
Chapter 2". The stronger consequence for admissible runs (companion Theorem `M:superquadratic`,
(`M:superquad`)): bounded gradients and $\sum_kd_k<\infty$ give
$\frac1{N^2}\sum_{k<N}q_k^{-1}\to+\infty$. The finite-horizon bound is `finite_horizon_bound`. -/
theorem superquadratic_growth {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) (hs : Summable R.d) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (R.q k)⁻¹) / (N : ℝ) ^ 2) atTop atTop := by
  obtain ⟨G, hG, hg⟩ := sqNorm_bound_of_bounded R.g hbdd
  exact superquadraticReciprocalGrowth n R.toFullBFGSRun G (1 - R.c₂) hG R.wolfe_constant_pos hg
    R.beta_lower_bound hs

/-- Item `A/energy/prose/022` (`paper/sections/energy.tex:214-217`): the finite-horizon bounds
of the companion's Chapter 2 (Theorem `M:superquadratic`, (`M:finitehorizon`)), for admissible
runs. Assume bounded gradients, $\|g_k\|\le G$ with $G>0$, and $\sum_kd_k<\infty$; the weak
Wolfe constant is $\omega=1-c_2$. For a tail $J$ put $D_J=\sum_{k\ge J}d_k$,
$K_0=4G^2/\omega^2$ and, for $\eta>0$, $V_\eta(H)=\sum_{j=1}^n(K_0/\eta)^{j-1}e_j(H)$ ($H\succ0$).
Then for every $m\ge2$
\[ \sum_{k=J}^{J+m-1}q_k^{-1}\ge m\,[G^2V_\eta(H_J)]^{-1/m}
   \Bigl(\eta+\frac{D_J}{\omega(m-1)}\Bigr)^{-(m-1)/m} \]
(real powers; the sum is over `Finset.Ico J (J + m)`). From the library's `finiteHorizon`, whose
block length is `m + 1`. -/
theorem finite_horizon_bound {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (G : ℝ) (hG : 0 < G) (hgG : ∀ k, ‖euclideanVector (R.g k)‖ ≤ G) (hsum : Summable R.d)
    (J : ℕ) (DJ : ℝ) (hDJ : DJ = ∑' i, R.d (J + i))
    (K0 : ℝ) (hK0 : K0 = 4 * G ^ 2 / (1 - R.c₂) ^ 2) (η : ℝ) (hη : 0 < η)
    (V : Mat n → ℝ)
    (hV : ∀ H : Mat n, H.PosDef →
      V H = ∑ j ∈ Finset.Icc 1 n, (K0 / η) ^ (j - 1) * principalSum H j)
    (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) * (G ^ 2 * V (R.H J)) ^ (-1 / (m : ℝ)) *
        (η + DJ / ((1 - R.c₂) * ((m : ℝ) - 1))) ^ (-((m : ℝ) - 1) / (m : ℝ)) ≤
      ∑ k ∈ Finset.Ico J (J + m), (R.q k)⁻¹ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hm' : 0 < m' := by omega
  have hg : ∀ k, sqNorm (R.toFullBFGSRun.g k) ≤ G ^ 2 := fun k => sqNorm_le_of_norm_le (hgG k)
  have h := finiteHorizon R.toFullBFGSRun G (1 - R.c₂) hG R.wolfe_constant_pos hg
    R.beta_lower_bound hsum J m' hm' η hη
  dsimp only at h
  have hcast : ((m' + 1 : ℕ) : ℝ) - 1 = (m' : ℝ) := by
    push_cast
    ring
  rw [hV _ (R.positive_definite J), potential_eq_weighted, hDJ, hK0, hcast,
    Finset.sum_Ico_eq_sum_range, show J + (m' + 1) - J = m' + 1 by omega]
  exact h

/-! ### Moving comparison directions: eligible pairs and band certificates -/

/-- Item `A/energy/prose/026` (`paper/sections/energy.tex:228-231`): "The identity
$\widehat B_ks_k=0$ means that movement parallel to the executed step carries no cost in the
part of the update left after its negative rank-one term. Only the perpendicular projection
needs control." For every admissible run and every $k$, with $\widehat B_k$ as in Lemma
`art:run-invariants`: $(v+cs_k)^T\widehat B_k(v+cs_k)=v^T\widehat B_kv$ for all $v$ and $c$;
$\Pi_{s_k}\widehat B_k\Pi_{s_k}=\widehat B_k$; and
$\tr(\widehat B_kW)=\tr(\widehat B_k\Pi_{s_k}W\Pi_{s_k})$ for every matrix $W$. -/
theorem projection_no_cost {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (Bhat : ℕ → Mat n)
    (hBhat : ∀ k, Bhat k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) (k : ℕ) :
    (∀ (v : Vec n) (c : ℝ), dot (v + c • R.displacement k)
        (Bhat k *ᵥ (v + c • R.displacement k)) = dot v (Bhat k *ᵥ v)) ∧
      TransportedCertificate.stepProjector (R.displacement k) * Bhat k *
          TransportedCertificate.stepProjector (R.displacement k) = Bhat k ∧
      ∀ W : Mat n, (Bhat k * W).trace =
        (Bhat k * (TransportedCertificate.stepProjector (R.displacement k) * W *
          TransportedCertificate.stepProjector (R.displacement k))).trace := by
  have hsymm : (Bhat k).IsSymm := by
    rw [hBhat k]
    exact R.annihilated_hessian_isSymm k
  have hker : Bhat k *ᵥ R.displacement k = 0 := by
    rw [hBhat k]
    exact R.annihilated_hessian_mul_displacement k
  refine ⟨fun v c => ?_, TransportedCertificate.annihilated_projector _ hsymm _ hker,
    fun W => (TransportedCertificate.trace_projected _ hsymm _ hker W).symm⟩
  have hk : Bhat k *ᵥ (c • R.displacement k) = 0 := by
    rw [Matrix.mulVec_smul, hker, smul_zero]
  exact EnergyIdentities.energy_add_kernel hsymm hk v

/-- Item `A/energy/disp/021` (`paper/sections/energy.tex:242-244`), with the notation of
lines 238-240: for differentiable $x,z$ write $g=\nabla F(x)$, $h=\nabla F(z)$, $s=z-x$,
$y=h-g$, $d=-g^Ts$, $\Delta=F(x)-F(z)$ and $t=y^Ts$; the pair is eligible when
\[ d>0,\qquad c_1d\le\Delta\le d,\qquad t\ge\omega d. \]
The library's `EligiblePair F c₁ c₂ x z g h` is exactly this condition, with $\omega=1-c_2$;
"$x$ is differentiable with $g=\nabla F(x)$" is `HasFDerivAt F (gradientFunctional g) x`. -/
theorem eligiblePair_iff {n : ℕ} (F : Vec n → ℝ) (c₁ c₂ : ℝ) (x z g h : Vec n)
    (s y : Vec n) (hs : s = z - x) (hy : y = h - g) (d Δ t : ℝ) (hd : d = -dot g s)
    (hΔ : Δ = F x - F z) (ht : t = dot y s) :
    TransportedCertificate.EligiblePair F c₁ c₂ x z g h ↔
      (HasFDerivAt F (gradientFunctional g) x ∧ HasFDerivAt F (gradientFunctional h) z) ∧
        d > 0 ∧ c₁ * d ≤ Δ ∧ Δ ≤ d ∧ t ≥ (1 - c₂) * d := by
  subst hs hy hd hΔ ht
  constructor
  · intro hp
    exact ⟨⟨hp.gradient_x, hp.gradient_z⟩, hp.decrease_pos, hp.armijo, hp.convex_decrease,
      hp.curvature⟩
  · rintro ⟨⟨hx, hz⟩, h1, h2, h3, h4⟩
    exact ⟨hx, hz, h1, h2, h3, h4⟩

/-- Item `A/energy/prose/028` (`paper/sections/energy.tex:245`): "All accepted pairs are
eligible." For every admissible run and every $k$, the pair $(x_k,x_{k+1})$ with gradients
$(g_k,g_{k+1})$ is eligible for the run's constants; its $d$ and $t$ are $d_k$ and $t_k$. -/
theorem accepted_pairs_eligible {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    TransportedCertificate.EligiblePair F R.c₁ R.c₂ (R.x k) (R.x (k + 1)) (R.g k) (R.g (k + 1)) ∧
      -dot (R.g k) (R.x (k + 1) - R.x k) = R.d k ∧
      dot (R.g (k + 1) - R.g k) (R.x (k + 1) - R.x k) = R.curvature k :=
  ⟨R.accepted_pair_eligible k, R.accepted_pair_decrease k, R.accepted_pair_curvature k⟩

/-- Item `A/energy/prose/030` (`paper/sections/energy.tex:247-248`): "Put
$\Pi_s=I-ss^T/(s^Ts)$." The library's `stepProjector s` is this matrix. -/
theorem stepProjector_eq {n : ℕ} (s : Vec n) :
    TransportedCertificate.stepProjector s = 1 - (dot s s)⁻¹ • outer s s := by
  simp only [TransportedCertificate.stepProjector, sqNorm, dot, pow_two]

/-- Item `A/energy/definition/art:band-certificate` (`paper/sections/energy.tex:250-264`),
Definition `art:band-certificate` (Band certificate), with its displays
\eqref{art:visibility}, \eqref{art:secant-control}, \eqref{art:transport}.

Let $K=\{F\le b\}$ be compact, with $b>F_*=\min F$, and $\eta>0$ with
$K_\eta=\{x\in K:F(x)\ge F_*+\eta\}$ (`Kη`). A band certificate on $K_\eta$ is a finite-valued
symmetric PSD field $W_\eta$ on the differentiable points of $K_\eta$ with constants
$m_\eta>0$, $C_\eta\ge0$, $L_\eta\ge0$, $\delta_\eta>0$ such that $g^TW_\eta(x)g\ge m_\eta$ at
every differentiable point of $K_\eta$, and, for all eligible pairs in $K_\eta$ with
$d\le\delta_\eta$,
\[ y^TW_\eta(z)y\le C_\eta t,\qquad
   \Pi_sW_\eta(z)\Pi_s\preceq(1+L_\eta d)\Pi_sW_\eta(x)\Pi_s. \]
This theorem shows that such data are exactly a library `BandCertificate` with
`0 ≤ Cert.C`. The field is a total function `Vec n → Mat n` constrained only at
differentiable points of $K_\eta$; `PosSemidef` includes symmetry; $A\preceq B$ is
`(B - A).PosSemidef`; the pair notation is that of display `A/energy/disp/021`. -/
theorem bandCertificate_iff {n : ℕ} (F : Vec n → ℝ) (b : ℝ) (K : Set (Vec n))
    (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (_hb : b > Fstar) (c₁ c₂ : ℝ)
    (_hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (_hη : 0 < η)
    (Kη : Set (Vec n)) (hKη : Kη = {x | x ∈ K ∧ F x ≥ Fstar + η}) :
    (∃ Cert : TransportedCertificate.BandCertificate F K Fstar c₁ c₂ η, 0 ≤ Cert.C) ↔
      ∃ (W : Vec n → Mat n) (m C L δ : ℝ), 0 < m ∧ 0 ≤ C ∧ 0 ≤ L ∧ 0 < δ ∧
        (∀ x ∈ Kη, DifferentiableAt ℝ F x → (W x).PosSemidef) ∧
        (∀ x ∈ Kη, ∀ g : Vec n, HasFDerivAt F (gradientFunctional g) x →
          dot g (W x *ᵥ g) ≥ m) ∧
        (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
          TransportedCertificate.EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
            dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x)) ∧
        (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
          TransportedCertificate.EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
            ((1 + L * -dot g (z - x)) • (TransportedCertificate.stepProjector (z - x) * W x *
                TransportedCertificate.stepProjector (z - x)) -
              TransportedCertificate.stepProjector (z - x) * W z *
                TransportedCertificate.stepProjector (z - x)).PosSemidef) := by
  subst hKη
  constructor
  · rintro ⟨Cert, hC⟩
    exact ⟨Cert.W, Cert.m, Cert.C, Cert.L, Cert.δ, Cert.m_pos, hC, Cert.L_nonneg,
      Cert.delta_pos, fun x hx hd => Cert.positive_semidefinite x hx hd,
      fun x hx g hg => Cert.visibility x hx g hg,
      fun x hx z hz g h hp hδ => Cert.secant x z g h hx hz hp hδ,
      fun x hx z hz g h hp hδ => Cert.transport x z g h hx hz hp hδ⟩
  · rintro ⟨W, m, C, L, δ, hm, hC, hL, hδ, hpsd, hvis, hsec, htr⟩
    exact ⟨{ W := W, m := m, C := C, L := L, δ := δ, m_pos := hm, L_nonneg := hL
             delta_pos := hδ, positive_semidefinite := hpsd, visibility := hvis
             secant := fun x z g h hx hz hp hd => hsec x hx z hz g h hp hd
             transport := fun x z g h hx hz hp hd => htr x hx z hz g h hp hd }, hC⟩

/-- "$K$ admits the band certificates" (Definition `art:band-certificate`: a certificate
with $C_\eta\ge0$ for every $\eta>0$ with $K_\eta\ne\emptyset$) is equivalent to the library's
`HasBandCertificates`, whose certificates allow any real $C$: replace $C$ by
$\max\{C,0\}$, using $t\ge\omega d>0$ on eligible pairs ($c_2<1$). -/
theorem hasBandCertificates_iff {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ : ℝ)
    (hc₂ : c₂ < 1) :
    (∀ η : ℝ, 0 < η → {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty →
        ∃ Cert : TransportedCertificate.BandCertificate F K Fstar c₁ c₂ η, 0 ≤ Cert.C) ↔
      TransportedCertificate.HasBandCertificates F K Fstar c₁ c₂ := by
  constructor
  · intro h η hη hne
    obtain ⟨Cert, _⟩ := h η hη hne
    exact ⟨Cert⟩
  · intro h η hη hne
    obtain ⟨Cert⟩ := h η hη hne
    refine ⟨{ Cert with
      C := max Cert.C 0
      secant := fun x z g h hx hz hp hd => ?_ }, le_max_right _ _⟩
    have ht : 0 ≤ TransportedCertificate.pairCurvature x z g h := by
      have h1 := hp.curvature
      have h2 := hp.decrease_pos
      nlinarith
    exact (Cert.secant x z g h hx hz hp hd).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)

/-- Item `A/energy/prose/034` (`paper/sections/energy.tex:269`): "In particular, the
condition allows nonsmoothness at an optimizer." With $F_*=\min F$, no positive band
contains a minimizer: for every $\eta>0$, $K_\eta\cap\arg\min F=\emptyset$. The certificate
conditions concern only (differentiable) points of the bands, so they impose nothing at an
optimizer. -/
theorem band_excludes_minimizers {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (η : ℝ) (hη : 0 < η) :
    ∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, x ∉ argmin F := by
  rintro x ⟨_, hx⟩ hmin
  obtain ⟨x0, hx0⟩ := hFstar.1
  have h := hmin x0
  linarith

/-- The objective $F(x)=|x|$ on $\R^1$. -/
def absF : Vec 1 → ℝ := fun x => |x 0|

/-- At a point $x\ne0$ the gradient of $|x|$ is its sign. -/
theorem absF_grad {x g : Vec 1} (hx : x 0 ≠ 0) (h : HasFDerivAt absF (gradientFunctional g) x) :
    g 0 = if 0 < x 0 then 1 else -1 := by
  have hd : HasDerivAt (fun t : ℝ => |t|) (if 0 < x 0 then 1 else -1) (x 0) := by
    split_ifs with hpos
    · exact hasDerivAt_abs_pos hpos
    · exact hasDerivAt_abs_neg (lt_of_le_of_ne (not_lt.mp hpos) hx)
  have h2 := ScalarCounterexamples.coordinate_hasGradient hd
  rw [OneDimensional.embed_eval] at h2
  have heq := h.unique h2
  have h1 := congrArg (fun L : Vec 1 →L[ℝ] ℝ => L (fun _ => 1)) heq
  simpa [gradientFunctional_apply, dot] using h1

/-- A band certificate for $|x|$ ($F_*=0$) on every band $K_\eta$, for any $K$ and constants
with $c_2<1$: $W=I$, $m=1$, $C=1/\eta$, $L=0$, $\delta=1$. Visibility: $g=\pm1$. Secant control:
$y=0$ unless the pair crosses $0$; then $|y|=2$, $t=2|s|$ and $|s|\ge2\eta$ because both
endpoints have $|x|\ge\eta$. Transport: $\Pi_s=0$ in dimension one. -/
def absCert (K : Set (Vec 1)) (c₁ c₂ η : ℝ) (hη : 0 < η) (hc₂ : c₂ < 1) :
    TransportedCertificate.BandCertificate absF K 0 c₁ c₂ η where
  W := fun _ => 1
  m := 1
  C := 1 / η
  L := 0
  δ := 1
  m_pos := one_pos
  L_nonneg := le_rfl
  delta_pos := one_pos
  positive_semidefinite := fun _ _ _ => Matrix.PosSemidef.one
  visibility := fun x hx g hg => by
    have hxb : η ≤ |x 0| := by have := hx.2; simp only [absF] at this; linarith
    have hx0 : x 0 ≠ 0 := by intro h; rw [h, abs_zero] at hxb; linarith
    have := absF_grad hx0 hg
    simp only [metricEnergy, dot, Fin.sum_univ_one, Matrix.one_mulVec]
    split_ifs at this <;> rw [this] <;> norm_num
  secant := fun x z g h hx hz hp _ => by
    have hxb : η ≤ |x 0| := by have := hx.2; simp only [absF] at this; linarith
    have hzb : η ≤ |z 0| := by have := hz.2; simp only [absF] at this; linarith
    have hx0 : x 0 ≠ 0 := by intro h; rw [h, abs_zero] at hxb; linarith
    have hz0 : z 0 ≠ 0 := by intro h; rw [h, abs_zero] at hzb; linarith
    have hg := absF_grad hx0 hp.gradient_x
    have hh := absF_grad hz0 hp.gradient_z
    have hcurv := hp.curvature
    have hdec := hp.decrease_pos
    simp only [TransportedCertificate.pairCurvature, TransportedCertificate.pairDecrease,
      TransportedCertificate.pairStep, dot, Fin.sum_univ_one, Pi.sub_apply] at hcurv hdec ⊢
    simp only [metricEnergy, dot, Fin.sum_univ_one, Matrix.one_mulVec, Pi.sub_apply]
    rw [div_mul_eq_mul_div, le_div_iff₀ hη]
    have hc : 0 < 1 - c₂ := by linarith
    split_ifs at hg hh with h1 h2 h2
    · rw [hg] at hdec; rw [hg, hh] at hcurv; nlinarith
    · rw [hg] at hdec; rw [hg, hh] at hcurv ⊢
      rw [abs_of_pos h1] at hxb
      rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h2) hz0)] at hzb
      nlinarith
    · rw [hg] at hdec; rw [hg, hh] at hcurv ⊢
      rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h1) hx0)] at hxb
      rw [abs_of_pos h2] at hzb
      nlinarith
    · rw [hg] at hdec; rw [hg, hh] at hcurv; nlinarith
  transport := fun x z g h _ _ hp _ => by
    have hs : TransportedCertificate.pairStep x z ≠ 0 := by
      intro h0
      have := hp.decrease_pos
      simp [TransportedCertificate.pairDecrease, h0, dot] at this
    rw [stepProjector_one_dim hs]
    simpa using Matrix.PosSemidef.zero

/-- Item `A/energy/prose/034` (`paper/sections/energy.tex:269`): "In particular, the
condition allows nonsmoothness at an optimizer." Witness: $F(x)=|x|$ on $\R^1$ is finite and
convex, with unique minimizer $0$ and $F_*=\min F=0$; it is not differentiable at $0$; its
sublevel sets are compact; and for all constants $0<c_1<c_2<1$ and every $b>F_*=0$ the set
$K=\{F\le b\}$ admits the band certificates of Definition `art:band-certificate` (with
$C_\eta\ge0$): on $K_\eta$ take $W=I$, $m=1$, $C=1/\eta$, $L=0$, $\delta=1$ (`absCert`). So all
hypotheses of Theorem `art:certificate` hold for an objective that is nonsmooth at its
optimizer; `band_excludes_minimizers` gives the reason: no band contains an optimizer. -/
theorem nonsmooth_optimizer_certificates :
    ∃ F : Vec 1 → ℝ, (∀ x, F x = |x 0|) ∧ ConvexOn ℝ Set.univ F ∧ IsLeast (Set.range F) 0 ∧
      F 0 = 0 ∧ (∀ x, F x = 0 → x = 0) ∧ ¬ DifferentiableAt ℝ F 0 ∧
      (∀ b : ℝ, IsCompact {x | F x ≤ b}) ∧
      ∀ b c₁ c₂ : ℝ, b > 0 → 0 < c₁ → c₁ < c₂ → c₂ < 1 →
        ∀ η : ℝ, 0 < η → {x | x ∈ {x | F x ≤ b} ∧ F x ≥ 0 + η}.Nonempty →
          ∃ Cert : TransportedCertificate.BandCertificate F {x | F x ≤ b} 0 c₁ c₂ η,
            0 ≤ Cert.C := by
  have h0 : absF 0 = 0 := by simp [absF]
  have hmin : ∀ x, absF 0 ≤ absF x := fun x => by rw [h0]; exact abs_nonneg _
  have huniq : ∀ x, absF x = 0 → x = 0 := by
    intro x hx
    funext i
    fin_cases i
    simpa [absF] using hx
  refine ⟨absF, fun _ => rfl, abs_coord_convex, ⟨⟨0, h0⟩, ?_⟩, h0, huniq, ?_,
    fun b => Localization.sublevel_compact abs_coord_convex 0 hmin
      (fun x hx => huniq x (hx.trans h0)) b,
    fun b c₁ c₂ _ _ _ hc₂ η hη _ => ⟨absCert _ c₁ c₂ η hη hc₂, (one_div_pos.mpr hη).le⟩⟩
  · rintro _ ⟨x, rfl⟩
    exact h0 ▸ hmin x
  · intro hd
    have h2 : DifferentiableAt ℝ (fun t : ℝ => absF (OneDimensional.embed t)) 0 := by
      have := hd.comp (0 : ℝ) (OneDimensional.embed.differentiableAt (x := 0))
      simpa [Function.comp_def] using this
    apply not_differentiableAt_abs_zero
    simpa [absF] using h2

/-! ### Theorem `art:certificate` -/

/-- Item `A/energy/theorem/art:certificate` (`paper/sections/energy.tex:271-279`), Theorem
`art:certificate` (Transported comparison certificate), with its display
`A/energy/disp/023`.

Let $K=\{F\le b\}$ be compact, with $b>F_*=\min F$ (`IsLeast (Set.range F) Fstar`). If $K$
admits the band certificates of Definition `art:band-certificate` (for the run's constants
$c_1,c_2$), every admissible run with $x_0\in K$ satisfies
\[ F(x_k)\to F_*,\qquad \operatorname{dist}(x_k,\arg\min F)\to0, \]
with the Euclidean distance (`euclideanSolutionDistance`). If the minimizer is unique, the
iterates converge to it. The library proves this without $C_\eta\ge0$ and without $b>F_*$
(`transportedCertificateConvergence`). -/
theorem certificate {n : ℕ} {F : Vec n → ℝ} (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (_hb : b > Fstar) (R : AdmissibleBFGSRun n F)
    (hcert : ∀ η : ℝ, 0 < η → {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty →
      ∃ Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η, 0 ≤ Cert.C)
    (hx0 : R.x 0 ∈ K) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ∀ xstar : Vec n, (∀ x, F xstar ≤ F x) → (∀ x, (∀ z, F x ≤ F z) → x = xstar) →
        Tendsto R.x atTop (𝓝 xstar) := by
  obtain ⟨xs, hxs⟩ := hFstar.1
  have hmin : ∀ x, F xs ≤ F x := fun x => hxs ▸ hFstar.2 (Set.mem_range_self x)
  have hlib := (hasBandCertificates_iff F K Fstar R.c₁ R.c₂ R.c₂_lt_one).mp hcert
  subst hK_def
  have hconv := transportedCertificateConvergence R b hK xs hmin hx0 (hxs ▸ hlib)
  rw [hxs] at hconv
  refine ⟨hconv.1, hconv.2.1, fun xstar hxstar huniq => ?_⟩
  have hFx : F xstar = Fstar := le_antisymm (hxs ▸ hxstar xs) (hFstar.2 (Set.mem_range_self _))
  have h := transportedCertificateConvergence R b hK xstar hxstar hx0 (hFx ▸ hlib)
  exact h.2.2 fun x hx => huniq x fun z => by rw [hx]; exact hxstar z

/-! ### The proof of Theorem `art:certificate`

The displays below live inside a proof by contradiction ("Suppose the limiting gap is
$\ell>0$"); together with the theorem's hypotheses, their standing assumptions cannot all
hold. Each display is therefore also proved in a general form (`..._general`) that assumes
only the facts its derivation uses (a certificate on one band $K_\eta$ and the band
memberships of the iterates involved); those general forms are satisfiable (see the
examples at the end). -/

/-- Proof of Theorem `art:certificate`, undisplayed claim of
`paper/sections/energy.tex:290` (not a register item): $E_k=\tr(B_kW(x_k))\ge0$ whenever
$x_k$ lies in the band of the certificate. -/
theorem certificate_energy_nonneg {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (K : Set (Vec n)) (Fstar η : ℝ)
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η) (k : ℕ)
    (hxk : R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}) :
    0 ≤ (R.hessian k * Cert.W (R.x k)).trace :=
  R.certificateEnergy_nonneg Cert k hxk

/-- The trace step of display `A/energy/disp/024` for one index $k$, assuming only a band
certificate on some $K_\eta$, $x_k,x_{k+1}\in K_\eta$ and $d_k\le\delta_\eta$:
\[ E_{k+1}=\tr(\widehat B_kW(x_{k+1}))+\frac{y_k^TW(x_{k+1})y_k}{t_k}
   \le(1+Ld_k)\tr(\widehat B_kW(x_k))+C\le(1+Ld_k)(E_k-m/q_k)+C. \] -/
theorem certificate_step_general {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (K : Set (Vec n)) (Fstar η : ℝ)
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η)
    (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace)
    (Bhat : ℕ → Mat n)
    (hBhat : ∀ k, Bhat k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) (k : ℕ)
    (hxk : R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hxk1 : R.x (k + 1) ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}) (hdk : R.d k ≤ Cert.δ) :
    E (k + 1) = (Bhat k * Cert.W (R.x (k + 1))).trace +
        dot (R.gradientChange k) (Cert.W (R.x (k + 1)) *ᵥ R.gradientChange k) / R.curvature k ∧
      (Bhat k * Cert.W (R.x (k + 1))).trace +
          dot (R.gradientChange k) (Cert.W (R.x (k + 1)) *ᵥ R.gradientChange k) /
            R.curvature k ≤
        (1 + Cert.L * R.d k) * (Bhat k * Cert.W (R.x k)).trace + Cert.C ∧
      (1 + Cert.L * R.d k) * (Bhat k * Cert.W (R.x k)).trace + Cert.C ≤
        (1 + Cert.L * R.d k) * (E k - Cert.m / R.q k) + Cert.C := by
  have hpair := R.accepted_pair_eligible k
  have hsmall : TransportedCertificate.pairDecrease (R.x k) (R.x (k + 1)) (R.g k) ≤ Cert.δ := by
    rwa [R.accepted_pair_decrease]
  have hT := Cert.transport _ _ _ _ hxk hxk1 hpair hsmall
  rw [R.accepted_pair_decrease, R.accepted_pair_step] at hT
  have hBpsd : (Bhat k).PosSemidef := by
    rw [hBhat k]
    exact R.annihilated_hessian_posSemidef k
  have hker : Bhat k *ᵥ R.displacement k = 0 := by
    rw [hBhat k]
    exact R.annihilated_hessian_mul_displacement k
  have htrace := TransportedCertificate.projected_transport_trace (Bhat k) hBpsd
    (R.displacement k) hker (Cert.W (R.x k)) (Cert.W (R.x (k + 1))) (1 + Cert.L * R.d k) hT
  have hS := Cert.secant _ _ _ _ hxk hxk1 hpair hsmall
  rw [R.accepted_pair_curvature] at hS
  have hcpos : 0 < R.curvature k := R.curvature_pos k
  have hcorr : dot (R.gradientChange k) (Cert.W (R.x (k + 1)) *ᵥ R.gradientChange k) /
      R.curvature k ≤ Cert.C := (div_le_iff₀ hcpos).mpr hS
  have hV := Cert.visibility _ hxk (R.g k) (R.hasGradient k)
  have hbase : (Bhat k * Cert.W (R.x k)).trace ≤ E k - Cert.m / R.q k := by
    rw [hBhat k, hE k, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
      TransportedCertificate.trace_outer_mul]
    have hdiv := div_le_div_of_nonneg_right hV (R.q_pos k).le
    simp only [smul_eq_mul, div_eq_mul_inv] at hdiv ⊢
    linarith
  have hmult : 0 ≤ 1 + Cert.L * R.d k :=
    add_nonneg zero_le_one (mul_nonneg Cert.L_nonneg (R.d_pos k).le)
  have hprod := mul_le_mul_of_nonneg_left hbase hmult
  refine ⟨?_, by linarith, by linarith⟩
  rw [hE (k + 1), R.hessian_update k, hBhat k, Matrix.add_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, TransportedCertificate.trace_outer_mul]
  simp only [smul_eq_mul, div_eq_mul_inv, metricEnergy]
  ring

/-- Under the standing assumptions of the proof of Theorem `art:certificate` (an admissible
run with $x_0\in K=\{F\le b\}$ whose gap $F(x_k)-F_*$ tends to $\ell>0$), every iterate lies
in $K_{\ell/2}$: Armijo keeps the run in $K$, and the gap decreases to $\ell$. -/
theorem iterates_in_band {n : ℕ} {F : Vec n → ℝ} (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (Fstar : ℝ) (R : AdmissibleBFGSRun n F) (hx0 : R.x 0 ∈ K)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (hlim : Tendsto (fun k => F (R.x k) - Fstar) atTop (𝓝 ℓ)) (k : ℕ) :
    R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + ℓ / 2} := by
  subst hK_def
  have hx0' : F (R.x 0) ≤ b := hx0
  have hanti : Antitone (fun k => F (R.x k) - Fstar) :=
    fun i j hij => sub_le_sub_right (R.objective_antitone hij) _
  have hge := hanti.le_of_tendsto hlim k
  refine ⟨(R.objective_le_initial k).trans hx0', ?_⟩
  show F (R.x k) ≥ Fstar + ℓ / 2
  linarith

/-- Item `A/energy/disp/024` (`paper/sections/energy.tex:293-299`), in the proof of Theorem
`art:certificate`. Standing assumptions: those of the theorem; the limiting gap
$\lim_k(F(x_k)-F_*)=\ell>0$; the certificate `Cert` of the band $K_{\ell/2}$ (with
$C\ge0$; band subscripts omitted: $W,m,C,L,\delta$ are `Cert.W`, `Cert.m`, ...); $J$ with
$d_k\le\delta$ for $k\ge J$; $E_k=\tr(B_kW(x_k))$; and $\widehat B_k$ of Lemma
`art:run-invariants`. Then for every $k\ge J$
\[ E_{k+1}=\tr(\widehat B_kW(x_{k+1}))+\frac{y_k^TW(x_{k+1})y_k}{t_k}
   \le(1+Ld_k)\tr(\widehat B_kW(x_k))+C\le(1+Ld_k)(E_k-m/q_k)+C. \]
These assumptions are jointly inconsistent (the theorem shows that the gap tends to $0$);
the proof uses only `certificate_step_general`, which is satisfiable. -/
theorem certificate_energy_step {n : ℕ} {F : Vec n → ℝ} (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (_hb : b > Fstar) (R : AdmissibleBFGSRun n F)
    (_hcert : ∀ η : ℝ, 0 < η → {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty →
      ∃ Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η, 0 ≤ Cert.C)
    (hx0 : R.x 0 ∈ K) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hlim : Tendsto (fun k => F (R.x k) - Fstar) atTop (𝓝 ℓ))
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ (ℓ / 2))
    (_hC : 0 ≤ Cert.C) (J : ℕ) (hJ : ∀ k, J ≤ k → R.d k ≤ Cert.δ)
    (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace)
    (Bhat : ℕ → Mat n)
    (hBhat : ∀ k, Bhat k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) :
    ∀ k, J ≤ k →
      E (k + 1) = (Bhat k * Cert.W (R.x (k + 1))).trace +
          dot (R.gradientChange k) (Cert.W (R.x (k + 1)) *ᵥ R.gradientChange k) /
            R.curvature k ∧
        (Bhat k * Cert.W (R.x (k + 1))).trace +
            dot (R.gradientChange k) (Cert.W (R.x (k + 1)) *ᵥ R.gradientChange k) /
              R.curvature k ≤
          (1 + Cert.L * R.d k) * (Bhat k * Cert.W (R.x k)).trace + Cert.C ∧
        (1 + Cert.L * R.d k) * (Bhat k * Cert.W (R.x k)).trace + Cert.C ≤
          (1 + Cert.L * R.d k) * (E k - Cert.m / R.q k) + Cert.C :=
  fun k hk => certificate_step_general R K Fstar (ℓ / 2) Cert E hE Bhat hBhat k
    (iterates_in_band b K hK_def Fstar R hx0 ℓ hℓ hlim k)
    (iterates_in_band b K hK_def Fstar R hx0 ℓ hℓ hlim (k + 1)) (hJ k hk)

/-- Finite normalized telescoping (the scalar step behind display `A/energy/disp/025`): if
$e_i\ge0$ for $i\le M$, $q_i>0$, $u_i\ge0$, the products
$P_i=\prod_{l<i}(1+u_l)$ satisfy $P_i\le B$ for $i\le M$, $m>0$, $C\ge0$, and
$e_{i+1}\le(1+u_i)(e_i-m/q_i)+C$ for $i<M$, then
$\frac mB\sum_{i<M}q_i^{-1}\le e_0+CM$. -/
theorem finite_reciprocal_sum_le {e q u : ℕ → ℝ} {m C B : ℝ} (M : ℕ)
    (he : ∀ i, i ≤ M → 0 ≤ e i) (hq : ∀ i, 0 < q i) (hu : ∀ i, 0 ≤ u i)
    (hB : ∀ i, i ≤ M → ResidualBudget.driftProduct u i ≤ B) (hm : 0 < m) (hC : 0 ≤ C)
    (hrec : ∀ i, i < M → e (i + 1) ≤ (1 + u i) * (e i - m / q i) + C) :
    m / B * ∑ i ∈ Finset.range M, (q i)⁻¹ ≤ e 0 + C * M := by
  set P := ResidualBudget.driftProduct u with hPdef
  have hP1 : ∀ i, 1 ≤ P i := ResidualBudget.one_le_driftProduct hu
  have hPpos : ∀ i, 0 < P i := fun i => lt_of_lt_of_le one_pos (hP1 i)
  have hnorm : ∀ i, i < M → e (i + 1) / P (i + 1) ≤ e i / P i - m / B * (q i)⁻¹ + C := by
    intro i hi
    have hfactor : 0 < 1 + u i := by linarith [hu i]
    have hchange : ((1 + u i) * (e i - m / q i) + C) / P (i + 1) =
        e i / P i - (m / q i) / P i + C / P (i + 1) := by
      rw [show P (i + 1) = P i * (1 + u i) from ResidualBudget.driftProduct_succ u i]
      field_simp [(hPpos i).ne', hfactor.ne', (hq i).ne']
      ring
    have hdes : m / B * (q i)⁻¹ ≤ (m / q i) / P i := by
      rw [show m / B * (q i)⁻¹ = (m / q i) / B by ring]
      exact div_le_div_of_nonneg_left (div_nonneg hm.le (hq i).le) (hPpos i) (hB i hi.le)
    have hadd : C / P (i + 1) ≤ C := div_le_self hC (hP1 (i + 1))
    have hdiv := div_le_div_of_nonneg_right (hrec i hi) (hPpos (i + 1)).le
    rw [hchange] at hdiv
    linarith
  have htel : ∀ i, i ≤ M →
      m / B * ∑ l ∈ Finset.range i, (q l)⁻¹ ≤ e 0 - e i / P i + C * i := by
    intro i
    induction i with
    | zero =>
      intro _
      simp [hPdef]
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hnorm i (by omega)
      rw [Finset.sum_range_succ, mul_add]
      push_cast
      linarith
  have hfin := htel M le_rfl
  have hlast : 0 ≤ e M / P M := div_nonneg (he M le_rfl) (hPpos M).le
  linarith

/-- The budget of display `A/energy/disp/025` on a finite window $J\le k<N$, assuming only a
band certificate on some $K_\eta$ with $C\ge0$, $\sum_kd_k<\infty$, $x_k\in K_\eta$ for
$J\le k\le N$ and $d_k\le\delta$ for $J\le k<N$:
\[ \frac{m}{\overline P}\sum_{k=J}^{N-1}q_k^{-1}\le E_J+C(N-J),\qquad
   \overline P=\exp\Bigl(L\sum_{j\ge J}d_j\Bigr). \] -/
theorem certificate_budget_general {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (K : Set (Vec n)) (Fstar η : ℝ)
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η) (hC : 0 ≤ Cert.C)
    (hsum : Summable R.d) (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace)
    (J N : ℕ) (hJN : J ≤ N)
    (hband : ∀ k, J ≤ k → k ≤ N → R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hsmall : ∀ k, J ≤ k → k < N → R.d k ≤ Cert.δ)
    (Pbar : ℝ) (hPbar : Pbar = Real.exp (Cert.L * ∑' j, R.d (J + j))) :
    Cert.m / Pbar * ∑ k ∈ Finset.Ico J N, (R.q k)⁻¹ ≤ E J + Cert.C * ((N : ℝ) - J) := by
  obtain ⟨Bhat, hBhat⟩ : ∃ Bhat : ℕ → Mat n,
      ∀ k, Bhat k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k) := ⟨_, fun _ => rfl⟩
  have hu : ∀ i, 0 ≤ Cert.L * R.d (J + i) := fun i => mul_nonneg Cert.L_nonneg (R.d_pos _).le
  have hsu : Summable (fun i => Cert.L * R.d (J + i)) :=
    (R.shift_summable_d hsum J).mul_left Cert.L
  have hB : ∀ i, i ≤ N - J →
      ResidualBudget.driftProduct (fun i => Cert.L * R.d (J + i)) i ≤ Pbar := by
    intro i _
    rw [hPbar, ← tsum_mul_left]
    exact ResidualBudget.driftProduct_le_exp_tsum hu hsu i
  have he : ∀ i, i ≤ N - J → 0 ≤ E (J + i) := by
    intro i hi
    rw [hE]
    exact certificate_energy_nonneg R K Fstar η Cert (J + i) (hband _ (by omega) (by omega))
  have hrec : ∀ i, i < N - J → E (J + (i + 1)) ≤
      (1 + Cert.L * R.d (J + i)) * (E (J + i) - Cert.m / R.q (J + i)) + Cert.C := by
    intro i hi
    have h := certificate_step_general R K Fstar η Cert E hE Bhat hBhat (J + i)
      (hband _ (by omega) (by omega)) (hband _ (by omega) (by omega))
      (hsmall _ (by omega) (by omega))
    rw [← add_assoc]
    linarith [h.1, h.2.1, h.2.2]
  have hfin := finite_reciprocal_sum_le (e := fun i => E (J + i)) (q := fun i => R.q (J + i))
    (u := fun i => Cert.L * R.d (J + i)) (N - J) he (fun i => R.q_pos _) hu hB Cert.m_pos hC
    hrec
  rw [Finset.sum_Ico_eq_sum_range, ← Nat.cast_sub hJN]
  simpa only [add_zero] using hfin

/-- Proof of Theorem `art:certificate`, undisplayed claim of
`paper/sections/energy.tex:302-303` (not a register item): with $P_J=1$ and
$P_{k+1}=P_k(1+Ld_k)$ ($L\ge0$), summability gives
$1\le P_k\le\exp(L\sum_{j\ge J}d_j)=\overline P$ for every $k\ge J$. -/
theorem normalization_bounds {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (L : ℝ)
    (hL : 0 ≤ L) (hsum : Summable R.d) (J : ℕ) (P : ℕ → ℝ) (hPJ : P J = 1)
    (hP : ∀ k, J ≤ k → P (k + 1) = P k * (1 + L * R.d k)) :
    ∀ k, J ≤ k → 1 ≤ P k ∧ P k ≤ Real.exp (L * ∑' j, R.d (J + j)) := by
  have hu : ∀ i, 0 ≤ L * R.d (J + i) := fun i => mul_nonneg hL (R.d_pos _).le
  have hsu : Summable (fun i => L * R.d (J + i)) := (R.shift_summable_d hsum J).mul_left L
  have hPd : ∀ i, P (J + i) = ResidualBudget.driftProduct (fun i => L * R.d (J + i)) i := by
    intro i
    induction i with
    | zero => simpa using hPJ
    | succ i ih =>
      rw [← add_assoc, hP (J + i) (Nat.le_add_right J i), ih, ResidualBudget.driftProduct_succ]
  intro k hk
  obtain ⟨i, rfl⟩ : ∃ i, k = J + i := ⟨k - J, by omega⟩
  rw [hPd i, ← tsum_mul_left]
  exact ⟨ResidualBudget.one_le_driftProduct hu i, ResidualBudget.driftProduct_le_exp_tsum hu hsu i⟩

/-- Item `A/energy/disp/025` (`paper/sections/energy.tex:305-308`), in the proof of Theorem
`art:certificate`. Under the standing assumptions of display `A/energy/disp/024`, with
$\overline P=\exp(L\sum_{j\ge J}d_j)$ (`Pbar`), for every $N\ge J$,
\[ \frac{m}{\overline P}\sum_{k=J}^{N-1}q_k^{-1}\le E_J+C(N-J). \]
As for display `A/energy/disp/024`, these standing assumptions are jointly inconsistent; the
proof uses only `certificate_budget_general`, which is satisfiable. -/
theorem certificate_reciprocal_budget {n : ℕ} {F : Vec n → ℝ} (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (_hb : b > Fstar) (R : AdmissibleBFGSRun n F)
    (_hcert : ∀ η : ℝ, 0 < η → {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty →
      ∃ Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η, 0 ≤ Cert.C)
    (hx0 : R.x 0 ∈ K) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hlim : Tendsto (fun k => F (R.x k) - Fstar) atTop (𝓝 ℓ))
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ (ℓ / 2))
    (hC : 0 ≤ Cert.C) (J : ℕ) (hJ : ∀ k, J ≤ k → R.d k ≤ Cert.δ)
    (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace)
    (Pbar : ℝ) (hPbar : Pbar = Real.exp (Cert.L * ∑' j, R.d (J + j))) :
    ∀ N : ℕ, J ≤ N →
      Cert.m / Pbar * ∑ k ∈ Finset.Ico J N, (R.q k)⁻¹ ≤ E J + Cert.C * ((N : ℝ) - J) := by
  intro N hJN
  have hsum : Summable R.d :=
    R.summable_predicted_decreases_of_lower_bound Fstar fun k => hFstar.2 (Set.mem_range_self _)
  exact certificate_budget_general R K Fstar (ℓ / 2) Cert hC hsum E hE J N hJN
    (fun k _ _ => iterates_in_band b K hK_def Fstar R hx0 ℓ hℓ hlim k)
    (fun k hk _ => hJ k hk) Pbar hPbar

/-! ### Remaining prose claims -/

/-- Item `A/energy/prose/008` (`paper/sections/energy.tex:31`): "A zero gradient is
successful termination." For a finite convex $F$, a point where $F$ is differentiable with
$\nabla F(x)=0$ is a global minimizer. -/
theorem zero_gradient_minimizer {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (x : Vec n) (hx : HasFDerivAt F (gradientFunctional 0) x) : ∀ z, F x ≤ F z :=
  global_minimum_of_zero_gradient hF hx

/-- Item `A/energy/prose/002` (`paper/sections/energy.tex:4-5`): "A nonsmooth secant can
instead contain a jump that remains large as the step shrinks." For the convex
$F(x)=|x|$ on $\R^1$: for every $\varepsilon>0$ there are differentiable points $x,z$ with
gradients $g,h$, $\|z-x\|^2=4\varepsilon^2$ and $\|h-g\|^2=4$. -/
theorem secant_jump_persists :
    ∃ F : Vec 1 → ℝ, ConvexOn ℝ Set.univ F ∧ ∀ ε : ℝ, 0 < ε →
      ∃ x z g h : Vec 1, HasFDerivAt F (gradientFunctional g) x ∧
        HasFDerivAt F (gradientFunctional h) z ∧ sqNorm (z - x) = 4 * ε ^ 2 ∧
        sqNorm (h - g) = 4 := by
  refine ⟨fun x => |x 0|, ?_, fun ε hε => ⟨OneDimensional.embed (-ε), OneDimensional.embed ε,
    OneDimensional.embed (-1), OneDimensional.embed 1, ?_, ?_, ?_, ?_⟩⟩
  · exact abs_coord_convex
  · exact ScalarCounterexamples.coordinate_hasGradient (hasDerivAt_abs_neg (by linarith))
  · exact ScalarCounterexamples.coordinate_hasGradient (hasDerivAt_abs_pos hε)
  · simp [sqNorm]
    ring
  · simp [sqNorm]
    norm_num

/-- Item `A/energy/prose/035` (`paper/sections/energy.tex:317-318`): "The companion's scalar
convergence and certificate-nonexistence results show that the certificate is not necessary
for successful BFGS behavior." The accumulating-kink objective $h$ of the companion
(Chapter G, `AccumulatingKinks.coordinateObjective`) is finite, convex, with unique minimizer
$0$, $\min h=0$ and compact sublevels; every admissible run on it converges; yet for the
constants $(c_1,c_2)=(1/4,1/2)$ no set $K=\{h\le b\}$, $b>0$, admits the band certificates of
Definition `art:band-certificate`. -/
theorem certificate_not_necessary :
    ∃ F : Vec 1 → ℝ, ConvexOn ℝ Set.univ F ∧ IsLeast (Set.range F) 0 ∧ F 0 = 0 ∧
      (∀ x, F x = 0 → x = 0) ∧ (∀ b : ℝ, IsCompact {x | F x ≤ b}) ∧
      (∀ R : AdmissibleBFGSRun 1 F,
        Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
      ∀ b : ℝ, b > 0 →
        ¬ ∀ η : ℝ, 0 < η → {x | x ∈ {x | F x ≤ b} ∧ F x ≥ 0 + η}.Nonempty →
          ∃ Cert : TransportedCertificate.BandCertificate F {x | F x ≤ b} 0 (1 / 4) (1 / 2) η,
            0 ≤ Cert.C := by
  have h0 := AccumulatingKinks.coordinateObjective_zero
  refine ⟨AccumulatingKinks.coordinateObjective, AccumulatingKinks.coordinateObjective_convex,
    ⟨⟨0, h0⟩, ?_⟩, h0,
    fun x hx => AccumulatingKinks.coordinateObjective_unique x (hx.trans h0.symm),
    AccumulatingKinks.coordinateObjective_sublevel_compact, AccumulatingKinks.actual_bfgs_converges,
    fun b hb hcert => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact h0 ▸ AccumulatingKinks.coordinateObjective_minimum x
  · have hcont := convex_continuous AccumulatingKinks.coordinateObjective_convex
    have hopen : IsOpen {x : Vec 1 | AccumulatingKinks.coordinateObjective x < b} :=
      isOpen_lt hcont continuous_const
    have hmem : (0 : Vec 1) ∈ {x : Vec 1 | AccumulatingKinks.coordinateObjective x < b} := by
      show AccumulatingKinks.coordinateObjective 0 < b
      rw [h0]
      exact hb
    have hnhds : {x | AccumulatingKinks.coordinateObjective x ≤ b} ∈ 𝓝 (0 : Vec 1) :=
      Filter.mem_of_superset (hopen.mem_nhds hmem) fun x (hx : _ < b) =>
        show AccumulatingKinks.coordinateObjective x ≤ b from hx.le
    exact AccumulatingKinks.every_neighborhood_no_certificates hnhds
      ((hasBandCertificates_iff _ _ _ _ _ (by norm_num)).mp hcert)

/-! ### Non-vacuity -/

/-- The assumptions of Theorem `art:minor-hierarchy` and of its proof can all hold at once:
$n=j=1$, $H=Z=U=I$, $g=1$, $y=-1$, $\alpha=1$, so that $s=-1$, $q=1$, $\beta=1$, $\lambda=1$. -/
example : ∃ (H Hplus : Mat 1) (g y s : Vec 1) (α q β : ℝ) (Z : Matrix (Fin 1) (Fin 1) ℝ)
    (U : Mat 1) (lam : Fin 1 → ℝ),
    H.PosDef ∧ s = -α • (H *ᵥ g) ∧ 0 < α ∧ q = dot g (H *ᵥ g) ∧ 0 < q ∧
      β = -dot y (H *ᵥ g) / q ∧ 0 < β ∧ Hplus = inverseBFGS H s y ∧ Zᵀ * Z = 1 ∧
      Uᵀ * U = 1 ∧ H * U = U * Matrix.diagonal lam ∧ ∀ i, 0 < lam i := by
  refine ⟨1, _, ![1], ![-1], _, 1, 1, 1, 1, 1, fun _ => 1, Matrix.PosDef.one, rfl, one_pos, ?_,
    one_pos, ?_, one_pos, rfl, by simp, by simp, by simp, fun _ => one_pos⟩
  · simp [dot]
  · simp [dot]

namespace Example

/-- $F(x)=x^2/2$ on $\R^1$. -/
def quad : Vec 1 → ℝ := fun x => x 0 ^ 2 / 2

theorem quad_convex : ConvexOn ℝ Set.univ quad := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [quad, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [sq_nonneg (x 0 - y 0), mul_nonneg ha hb]

theorem quad_hasDerivAt (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
  have h := (hasDerivAt_pow 2 t).div_const 2
  convert h using 1
  norm_num

theorem quad_hasGradient (x : Vec 1) : HasFDerivAt quad (gradientFunctional x) x := by
  have h := ScalarCounterexamples.coordinate_hasGradient (quad_hasDerivAt (x 0))
  rw [OneDimensional.embed_eval] at h
  exact h

theorem quad_grad_eq {x g : Vec 1} (h : HasFDerivAt quad (gradientFunctional g) x) : g = x := by
  have heq := h.unique (quad_hasGradient x)
  have h1 := congrArg (fun L : Vec 1 →L[ℝ] ℝ => L (fun _ => 1)) heq
  simp only [gradientFunctional_apply, dot, Fin.sum_univ_one, mul_one] at h1
  funext i
  fin_cases i
  exact h1

/-- The iterates $x_k=2^{-k}$. -/
def pt (k : ℕ) : Vec 1 := fun _ => (1 / 2 : ℝ) ^ k

theorem inverseBFGS_one_self (v : Vec 1) (hv : v 0 ≠ 0) : inverseBFGS 1 v v = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [inverseBFGS, outer, dot, Matrix.mul_apply, Matrix.one_apply]
  field_simp

theorem step_eq (k : ℕ) : bfgsStep (1 : Mat 1) (pt k) (1 / 2) = pt (k + 1) - pt k := by
  funext i
  simp [bfgsStep, pt, pow_succ]
  ring

/-- An admissible run on `quad`: $x_0=1$, $H_k=1$, $\alpha_k=1/2$, $(c_1,c_2)=(1/4,3/4)$, so
$x_k=2^{-k}$ and $g_k=x_k$. -/
def run : AdmissibleBFGSRun 1 quad where
  convex := quad_convex
  x := pt
  H := fun _ => 1
  g := pt
  α := fun _ => 1 / 2
  c₁ := 1 / 4
  c₂ := 3 / 4
  c₁_pos := by norm_num
  c₁_lt_c₂ := by norm_num
  c₂_lt_one := by norm_num
  initial_posDef := Matrix.PosDef.one
  alpha_pos := fun _ => by norm_num
  gradient_nonzero := fun k h => by
    have := congrFun h 0
    simp [pt] at this
  hasGradient := fun k => quad_hasGradient (pt k)
  step := fun k => by rw [step_eq]; abel
  update := fun k => by
    have hv : (pt (k + 1) - pt k) 0 ≠ 0 := by
      simp only [pt, Pi.sub_apply, pow_succ]
      have : (0 : ℝ) < (1 / 2) ^ k := by positivity
      intro h
      nlinarith
    rw [step_eq, inverseBFGS_one_self _ hv]
  armijo := fun k => by
    simp only [step_eq, quad, pt, dot, Fin.sum_univ_one, Pi.sub_apply, pow_succ]
    nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ k)]
  weak_wolfe := fun k => by
    simp only [step_eq, quad, pt, dot, Fin.sum_univ_one, Pi.sub_apply, pow_succ]
    nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ k)]

/-- A band certificate for `quad` on every band $K_\eta$ ($F_*=0$): $W=I$, $m=2\eta$, $C=1$,
$L=0$, $\delta=1$. -/
def quadCert (K : Set (Vec 1)) (c₁ c₂ η : ℝ) (hη : 0 < η) :
    TransportedCertificate.BandCertificate quad K 0 c₁ c₂ η where
  W := fun _ => 1
  m := 2 * η
  C := 1
  L := 0
  δ := 1
  m_pos := by linarith
  L_nonneg := le_rfl
  delta_pos := one_pos
  positive_semidefinite := fun _ _ _ => Matrix.PosSemidef.one
  visibility := fun x hx g hg => by
    have hgx := quad_grad_eq hg
    subst hgx
    have h := hx.2
    simp only [quad] at h
    simp [metricEnergy, dot]
    nlinarith
  secant := fun x z g h _ _ hp _ => by
    have hg := quad_grad_eq hp.gradient_x
    have hh := quad_grad_eq hp.gradient_z
    subst hg hh
    simp [metricEnergy, TransportedCertificate.pairCurvature, TransportedCertificate.pairStep]
  transport := fun x z g h _ _ hp _ => by
    have hs : TransportedCertificate.pairStep x z ≠ 0 := by
      intro h0
      have := hp.decrease_pos
      simp [TransportedCertificate.pairDecrease, h0, dot] at this
    rw [stepProjector_one_dim hs]
    simpa using Matrix.PosSemidef.zero

theorem quad_nonneg (x : Vec 1) : 0 ≤ quad x := by
  unfold quad
  positivity

theorem quad_isLeast : IsLeast (Set.range quad) 0 :=
  ⟨⟨0, by simp [quad]⟩, by rintro _ ⟨x, rfl⟩; exact quad_nonneg x⟩

theorem quad_sublevel_compact (b : ℝ) : IsCompact {x | quad x ≤ b} :=
  Localization.sublevel_compact quad_convex 0 (fun x => by simpa [quad] using quad_nonneg x)
    (fun x hx => by
      funext i
      fin_cases i
      simp [quad] at hx
      simpa using hx) b

theorem run_d (k : ℕ) : run.d k = (1 / 2) * ((1 / 2 : ℝ) ^ k) ^ 2 := by
  simp [AdmissibleBFGSRun.d, AdmissibleBFGSRun.q, run, metricEnergy, dot, pt]
  ring

theorem run_summable : Summable run.d :=
  run.summable_predicted_decreases_of_lower_bound 0 fun _ => quad_nonneg _

theorem run_bounded : ∀ k, ‖euclideanVector (run.g k)‖ ≤ 1 := by
  intro k
  have h := FrameNorms.euclidean_norm_sq (euclideanVector (run.g k))
  change ‖euclideanVector (run.g k)‖ ^ 2 = sqNorm (run.g k) at h
  have hs : sqNorm (run.g k) ≤ 1 := by
    simp only [sqNorm, Fin.sum_univ_one]
    change ((1 / 2 : ℝ) ^ k) ^ 2 ≤ 1
    have h1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h0 : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
    nlinarith
  nlinarith [norm_nonneg (euclideanVector (run.g k))]

/-- An admissible run with bounded gradients and $d_k\to0$ (the hypotheses of Theorem
`art:reciprocal-growth`), with the choices $\Lambda,K_0,\eta,J,V_\eta$ of its proof. -/
example : ∃ (F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F) (Λ K0 η : ℝ) (J : ℕ) (V : Mat 1 → ℝ),
    (∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) ∧ Tendsto R.d atTop (𝓝 0) ∧
      0 < Λ ∧ (∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) ∧ K0 = 4 * Λ ^ 2 / (1 - R.c₂) ^ 2 ∧
      0 < η ∧ (∀ k, J ≤ k → R.d k / (1 - R.c₂) ≤ η) ∧
      (∀ H : Mat 1, H.PosDef →
        V H = ∑ j ∈ Finset.Icc 1 1, (K0 / η) ^ (j - 1) * principalSum H j) := by
  refine ⟨quad, run, 1, _, 1, 1, _, ⟨1, run_bounded⟩, run_summable.tendsto_atTop_zero, one_pos,
    run_bounded, rfl, one_pos, fun k hk => ?_, fun H _ => rfl⟩
  rw [run_d]
  change 1 / 2 * ((1 / 2 : ℝ) ^ k) ^ 2 / (1 - 3 / 4) ≤ 1
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 : (1 / 2 : ℝ) ^ k' ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h0 : 0 ≤ (1 / 2 : ℝ) ^ k' := by positivity
  have hk1 : (1 / 2 : ℝ) ^ (k' + 1) = (1 / 2) ^ k' * (1 / 2) := pow_succ _ _
  rw [hk1, show 1 / 2 * ((1 / 2 : ℝ) ^ k' * (1 / 2)) ^ 2 / (1 - 3 / 4) =
    ((1 / 2 : ℝ) ^ k') ^ 2 / 2 by ring]
  nlinarith

/-- The hypotheses of Theorem `art:certificate` (and of Definition `art:band-certificate`)
can hold at once. -/
example : ∃ (F : Vec 1 → ℝ) (b : ℝ) (K : Set (Vec 1)) (Fstar : ℝ) (R : AdmissibleBFGSRun 1 F),
    K = {x | F x ≤ b} ∧ IsCompact K ∧ IsLeast (Set.range F) Fstar ∧ b > Fstar ∧
      (∀ η : ℝ, 0 < η → {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty →
        ∃ Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η, 0 ≤ Cert.C) ∧
      R.x 0 ∈ K := by
  refine ⟨quad, 1, _, 0, run, rfl, quad_sublevel_compact 1, quad_isLeast, one_pos,
    fun η hη _ => ⟨quadCert _ _ _ η hη, zero_le_one⟩, ?_⟩
  show quad (pt 0) ≤ 1
  simp [quad, pt]
  norm_num

theorem pt_band (k : ℕ) (hk : k ≤ 1) :
    run.x k ∈ {x : Vec 1 | x ∈ (Set.univ : Set (Vec 1)) ∧ quad x ≥ 0 + 1 / 8} := by
  refine ⟨Set.mem_univ _, ?_⟩
  interval_cases k <;> norm_num [run, quad, pt]

/-- The assumptions of `certificate_step_general` and `certificate_budget_general` (the general
forms of displays `A/energy/disp/024` and `A/energy/disp/025`) can hold at once. -/
example : ∃ (F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F) (K : Set (Vec 1)) (Fstar η : ℝ)
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η) (E : ℕ → ℝ)
    (Bhat : ℕ → Mat 1) (k J N : ℕ) (Pbar : ℝ),
    0 ≤ Cert.C ∧ Summable R.d ∧ (∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace) ∧
      (∀ k, Bhat k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) ∧
      R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η} ∧ R.x (k + 1) ∈ {x | x ∈ K ∧ F x ≥ Fstar + η} ∧
      R.d k ≤ Cert.δ ∧ J ≤ N ∧
      (∀ k, J ≤ k → k ≤ N → R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}) ∧
      (∀ k, J ≤ k → k < N → R.d k ≤ Cert.δ) ∧
      Pbar = Real.exp (Cert.L * ∑' j, R.d (J + j)) := by
  have hd0 : run.d 0 ≤ 1 := by rw [run_d]; norm_num
  refine ⟨quad, run, Set.univ, 0, 1 / 8, quadCert _ _ _ (1 / 8) (by norm_num), _, _, 0, 0, 1, _,
    zero_le_one, run_summable, fun _ => rfl, fun _ => rfl, pt_band 0 (by norm_num),
    pt_band 1 le_rfl, hd0, zero_le_one, fun k _ hk => pt_band k hk, fun k _ hk => ?_, rfl⟩
  obtain rfl : k = 0 := by omega
  exact hd0


/-- The assumptions of `persistent_gap_budget_general` and `reciprocal_sum_linear_general` (the
finite-horizon forms of display `A/energy/disp/010` and of item `A/energy/prose/011`) can all
hold: the quadratic run with $x_*=0$, $F_*=0$, $N=1$, $\eta=1/8$ ($F(x_1)=1/8$) and $C=1$
($R_0=1/4$). -/
example : ∃ (F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F) (xstar : Vec 1) (Fstar : ℝ)
    (r : ℕ → Vec 1) (E Rk : ℕ → ℝ) (η C : ℝ) (N : ℕ),
    (∀ z, F xstar ≤ F z) ∧ Fstar = F xstar ∧ (∀ k, r k = R.x k - xstar) ∧
      (∀ k, E k = dot (r k) (R.hessian k *ᵥ r k)) ∧
      (∀ k, Rk k = dot (R.gradientChange k) (r (k + 1)) ^ 2 / R.curvature k) ∧
      0 < η ∧ F (R.x N) - Fstar ≥ η ∧ ∀ k, k < N → Rk k ≤ C := by
  have hq0 : quad 0 = 0 := by simp [quad]
  refine ⟨quad, run, 0, quad 0, fun k => run.x k - 0, _, _, 1 / 8, 1, 1,
    fun z => by rw [hq0]; exact quad_nonneg z, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    by norm_num, ?_, fun k hk => ?_⟩
  · show quad (pt 1) - quad 0 ≥ 1 / 8
    norm_num [quad, pt]
  · obtain rfl : k = 0 := by omega
    show dot (run.gradientChange 0) (run.x (0 + 1) - 0) ^ 2 / run.curvature 0 ≤ 1
    simp [AdmissibleBFGSRun.curvature, AdmissibleBFGSRun.gradientChange,
      AdmissibleBFGSRun.displacement, run, pt, bfgsStep, dot]
    norm_num

end Example

end BfgsCoverage.Article.Energy
