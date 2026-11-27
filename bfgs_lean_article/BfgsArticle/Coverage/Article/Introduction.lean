import BfgsVerification.QuadraticCellRadial
import BfgsVerification.DEmbeddingCenter
import ConvexBalance
import MixedBenchmark
import ArticleGeometry
import BfgsVerification.PointwiseCertificateFeasibility
import BfgsVerification.PlanarQuadraticTargets
import BfgsVerification.CompactConvergence

/-!
# Lean coverage of `paper/sections/introduction.tex`

Coverage theorems for the claims made only in Section `art:introduction`. The
summary sentences that restate results of later sections are classified
`SAME_AS` in `editorial/lean_coverage/register/A_introduction.json`.

Conventions. The mixed model `F(u,v)=u^2+|v|` is
`BfgsVerification.UnexcitedMetric.objective` (`(x 0)^2+|x 1|` on `Vec 2`); actual
gradients are `coordinateGradient`. The three-quadratic example of Theorem
`art:nonradial-example` is `PlanarQuadraticExample.objective`, the maximum of
`PlanarQuadraticExample.branch 0,1,2`. On `Vec n` the `ℓ₁` norm is written
`∑ j, |y j|` and the Euclidean norm `‖euclideanVector y‖`.
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsCoverage.Article.Introduction
open BfgsVerification

/-- Item `A/introduction/disp/001` (`paper/sections/introduction.tex:31-33`): the mixed
model $F(u,v)=u^2+|v|$. The library objective `UnexcitedMetric.objective` is this
formula. -/
theorem mixed_model_formula (u v : ℝ) : UnexcitedMetric.objective ![u, v] = u ^ 2 + |v| := by
  simp [UnexcitedMetric.objective]

/-- Item `A/introduction/prose/010` (`paper/sections/introduction.tex:138-139`):
"succeeds on $F(u,v)=u^2+|v|$. Approaching the nonsmooth line $v=0$ need not make $u^2$ small, because the gradient jumps vertically between $(2u,1)$ and" For `u ≠ 0` the points `(u,1/(k+1))`, at which `F(u,v)=u^2+|v|` is
differentiable, approach the point `(u,0)` of the nonsmooth line `v=0`; their
smooth coordinate stays `u`, and their values tend to `u^2`, above the minimum
value `F(0,0)=0`. -/
theorem approach_line_without_vanishing {u : ℝ} (hu : u ≠ 0) :
    ∃ z : ℕ → Vec 2, Tendsto z atTop (𝓝 ![u, 0]) ∧
      (∀ k, z k 0 = u ∧ z k 1 ≠ 0 ∧ DifferentiableAt ℝ UnexcitedMetric.objective (z k)) ∧
      ¬ Tendsto (fun k => z k 0) atTop (𝓝 0) ∧
      Tendsto (fun k => UnexcitedMetric.objective (z k)) atTop (𝓝 (u ^ 2)) ∧
      UnexcitedMetric.objective 0 < u ^ 2 := by
  have hs : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  refine ⟨fun k => ![u, 1 / ((k : ℝ) + 1)], ?_, fun k => ⟨rfl, (hpos k).ne', ?_⟩, ?_, ?_, ?_⟩
  · rw [tendsto_pi_nhds]
    intro i
    fin_cases i
    · simp
    · simpa using hs
  · exact (ArticleGeometry.mixed_ridge_gradient (u := u) (hpos k).ne').differentiableAt
  · intro h
    exact hu (tendsto_nhds_unique tendsto_const_nhds h)
  · have hv : Tendsto (fun k : ℕ => u ^ 2 + |(1 : ℝ) / ((k : ℝ) + 1)|) atTop (𝓝 (u ^ 2 + |0|)) :=
      tendsto_const_nhds.add hs.abs
    simpa [UnexcitedMetric.objective] using hv
  · simpa [UnexcitedMetric.objective] using sq_pos_of_ne_zero hu

/-- The `ℓ₁` norm is not differentiable at any point of a coordinate hyperplane. -/
theorem l1_not_differentiable {n : ℕ} (i : Fin n) {x : Vec n} (hx : x i = 0) :
    ¬ DifferentiableAt ℝ (fun y : Vec n => ∑ j, |y j|) x := by
  intro hd
  have hl : DifferentiableAt ℝ (fun t : ℝ => x + t • (Pi.single i 1 : Vec n)) 0 :=
    (differentiableAt_const x).add (differentiableAt_id.smul_const _)
  have hd' : DifferentiableAt ℝ (fun y : Vec n => ∑ j, |y j|) (x + (0 : ℝ) • (Pi.single i 1 : Vec n)) := by
    simpa using hd
  have hc := (hd'.comp (0 : ℝ) hl).sub_const (∑ j, |x j|)
  have hf : (fun t : ℝ => ((fun y : Vec n => ∑ j, |y j|) ∘ fun t : ℝ => x + t • (Pi.single i 1 : Vec n)) t
      - ∑ j, |x j|) = fun t : ℝ => |t| := by
    funext t
    simp only [Function.comp_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp [hx]
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  rw [hf] at hc
  exact not_differentiableAt_abs_zero hc

/-- Item `A/introduction/prose/035` (`paper/sections/introduction.tex:238-240`): the norm
`‖x‖_1`, "linear maximum $\max_{1\le i\le m}a_i^Tx$. In particular, this covers $\norm{x}_1$ and $\norm{x}_\infty$, whose nonsmooth loci contain coordinate hyperplanes and diagonal facets rather than an isolated point." For `n ≥ 2`:
`∑_j |x_j|` is not differentiable at any `x` with `x_i = 0`; the Euclidean norm is
differentiable exactly at `x ≠ 0`; and the nonsmooth points of `‖·‖_1` are not
isolated: nonzero ones lie arbitrarily close to `0`. -/
theorem norm_nonsmooth_sets {n : ℕ} (hn : 2 ≤ n) :
    (∀ (i : Fin n) (x : Vec n), x i = 0 → ¬ DifferentiableAt ℝ (fun y : Vec n => ∑ j, |y j|) x) ∧
      (∀ x : Vec n, DifferentiableAt ℝ (fun y : Vec n => ‖euclideanVector y‖) x ↔ x ≠ 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ x : Vec n, x ≠ 0 ∧ ‖x‖ < ε ∧
        ¬ DifferentiableAt ℝ (fun y : Vec n => ∑ j, |y j|) x := by
  have hlin : (euclideanVector : Vec n → EuclideanSpace ℝ (Fin n)) =
      (EuclideanSpace.equiv (Fin n) ℝ).symm := by
    funext y
    rfl
  refine ⟨fun i x hx => l1_not_differentiable i hx, fun x => ⟨?_, ?_⟩, ?_⟩
  · rintro hd rfl
    let i0 : Fin n := ⟨0, by omega⟩
    haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
      ⟨⟨EuclideanSpace.single i0 1, 0, fun h => by
        have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i0) h
        simp at this⟩⟩
    apply not_differentiableAt_norm_zero (EuclideanSpace ℝ (Fin n))
    have he : (fun v : EuclideanSpace ℝ (Fin n) => ‖v‖) =
        (fun y : Vec n => ‖euclideanVector y‖) ∘ (EuclideanSpace.equiv (Fin n) ℝ) := by
      funext v
      simp [hlin]
    rw [he]
    have hd0 : DifferentiableAt ℝ (fun y : Vec n => ‖euclideanVector y‖)
        ((EuclideanSpace.equiv (Fin n) ℝ) 0) := by
      simpa using hd
    exact hd0.comp 0 (EuclideanSpace.equiv (Fin n) ℝ).differentiableAt
  · intro hx
    have hne : euclideanVector x ≠ 0 := by
      rw [hlin]
      simpa using hx
    exact ((contDiffAt_norm ℝ (n := 1) hne).differentiableAt le_rfl).comp x
      (hlin ▸ (EuclideanSpace.equiv (Fin n) ℝ).symm.differentiableAt)
  · intro ε hε
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have h01 : i1 ≠ i0 := by
      intro h
      have := congrArg Fin.val h
      simp [i0, i1] at this
    refine ⟨Pi.single i0 (ε / 2), ?_, ?_, l1_not_differentiable i1 (by simp [Pi.single_apply, h01])⟩
    · intro h
      have := congrFun h i0
      simp at this
      linarith
    · have hle : ‖(Pi.single i0 (ε / 2) : Vec n)‖ ≤ ε / 2 := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
        by_cases hj : j = i0
        · subst hj
          simp [abs_of_pos hε]
        · simp [Pi.single_apply, hj]
          positivity
      linarith

/-- A point of the switching set of branches `i` and `j` of the three-quadratic
example of Theorem `art:nonradial-example`, inside the box `|u|,|v| ≤ 1/10`:
the two branches tie and are active. -/
def SwitchingPoint (i j : Fin 3) (x : Vec 2) : Prop :=
  |x 0| ≤ 1 / 10 ∧ |x 1| ≤ 1 / 10 ∧
    PlanarQuadraticExample.branch i x = PlanarQuadraticExample.branch j x ∧
    PlanarQuadraticExample.objective x = PlanarQuadraticExample.branch i x

/-- Item `A/introduction/prose/038` (`paper/sections/introduction.tex:250-253`): "\item \emph{Curved planar switching interfaces via moving contour fields.} When switching loci bend, inward rays cross interfaces and radial secant bounds can fail on every neighborhood of the minimizer, as we demonstrate explicitly on a three-quadratic maximum (Theorem~\ref{art:nonradial-example}). Using a". For every pair of branches, the
switching set (tie of the two branches, both active) inside `|u|,|v| ≤ 1/10`
contains `0` and two points `q,r` with `0,q,r` not collinear, so it lies on no
line, and it is not a cone with vertex `0` either (`q/2` is not a switching point),
unlike the switching sets of a homogeneous maximum; and the radial secant
condition `art:radial-condition` fails on every neighbourhood of the minimizer `0`. -/
theorem three_quadratic_curved_nonradial :
    (∀ i j : Fin 3, i ≠ j → ∃ q r : Vec 2,
      SwitchingPoint i j 0 ∧ SwitchingPoint i j q ∧ SwitchingPoint i j r ∧
        q 0 * r 1 - q 1 * r 0 ≠ 0 ∧ ¬ SwitchingPoint i j ((1 / 2 : ℝ) • q)) ∧
      ∀ K ∈ 𝓝 (0 : Vec 2),
        ¬ RadialCertificate.HasRadialSecantBounds PlanarQuadraticExample.objective K 0 := by
  refine ⟨?_, fun K hK => PlanarQuadraticExample.not_radial_secant_on_neighborhood hK⟩
  have h0 : ∀ i j, SwitchingPoint i j 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ⟨![30/391, 29/391], ![40/721, 39/721], h0 _ _, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by norm_num, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]⟩
  · exact ⟨![20/461, -38/461], ![40/1921, -78/1921], h0 _ _, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by norm_num, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]⟩
  · exact ⟨![30/391, 29/391], ![40/721, 39/721], h0 _ _, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by norm_num, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]⟩
  · exact absurd rfl hij
  · exact ⟨![-19/311, 10/311], ![-39/1321, 20/1321], h0 _ _, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by norm_num, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]⟩
  · exact ⟨![20/461, -38/461], ![40/1921, -78/1921], h0 _ _, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by norm_num, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]⟩
  · exact ⟨![-19/311, 10/311], ![-39/1321, 20/1321], h0 _ _, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons], by norm_num, by
      norm_num [SwitchingPoint, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective,
        abs_le, max_def, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]⟩
  · exact absurd rfl hij

/-- Item `A/introduction/prose/041` (`paper/sections/introduction.tex:14-16`): "determinant term can compensate. On a nonsmooth objective, however, gradients can jump by $O(1)$ across kinks as the step $s_k=x_{k+1}-x_k$ shrinks: the ratio $\norm{y_k}^2/(y_k^Ts_k)$ becomes unbounded, $\tr(B_k)$ can diverge, and the inverse-Hessian approximation $H_k$" The
bound `‖y‖^2 ≤ M y^T s` of the smooth analysis (`y` the gradient change, `s` the
step) holds for no constant `M` over the pairs of differentiable points of
`F(u,v)=u^2+|v|` with `y^T s > 0`: pairs straddling the jump line `v=0` keep
`‖y‖^2=4` while `y^T s → 0`. -/
theorem uniform_secant_bound_fails :
    ¬ ∃ M : ℝ, ∀ x z : Vec 2,
      DifferentiableAt ℝ UnexcitedMetric.objective x →
      DifferentiableAt ℝ UnexcitedMetric.objective z →
      0 < dot (coordinateGradient UnexcitedMetric.objective z -
          coordinateGradient UnexcitedMetric.objective x) (z - x) →
      sqNorm (coordinateGradient UnexcitedMetric.objective z -
          coordinateGradient UnexcitedMetric.objective x) ≤
        M * dot (coordinateGradient UnexcitedMetric.objective z -
          coordinateGradient UnexcitedMetric.objective x) (z - x) := by
  rintro ⟨M, hM⟩
  set e : ℝ := 1 / (2 * (|M| + 1)) with he
  have hepos : 0 < e := by positivity
  have hgx := ArticleGeometry.mixed_ridge_gradient (u := 0) hepos.ne'
  have hgz := ArticleGeometry.mixed_ridge_gradient (u := 0) (neg_ne_zero.mpr hepos.ne')
  have hcx := PointwiseFeasibility.coordinateGradient_eq hgx
  have hcz := PointwiseFeasibility.coordinateGradient_eq hgz
  have h := hM ![0, e] ![0, -e] hgx.differentiableAt hgz.differentiableAt
  rw [hcx, hcz, Real.sign_of_pos hepos, Real.sign_of_neg (neg_neg_of_pos hepos)] at h
  simp only [dot, sqNorm, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at h
  have h4 := h (by nlinarith)
  have hMe : M * e ≤ |M| * e := mul_le_mul_of_nonneg_right (le_abs_self M) hepos.le
  have hlt : |M| * e < 1 := by
    rw [he]
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith [abs_nonneg M]
  nlinarith


/-! ## Mechanisms of Section 1.1 (moved from `paper/sections/geometry.tex` in M45)

Copies of the declarations of `BfgsCoverage.Article.Geometry` (kept unchanged for the companion
modules that import it), restated here for the items of Sections 1.1--1.2. -/

section GeometryMechanisms
open scoped InnerProductSpace

/-! ## The mixed ridge -/

/-- "Reaching $v=0$ does not eliminate the horizontal error $u^2$."
On the nonsmooth line `v=0` the mixed ridge equals `u^2`, which exceeds the
minimum value `F(0,0)=0` whenever `u ≠ 0`. -/
theorem horizontal_error_on_line (u : ℝ) :
    UnexcitedMetric.objective ![u, 0] = u ^ 2 ∧
      (u ≠ 0 → UnexcitedMetric.objective 0 < UnexcitedMetric.objective ![u, 0]) := by
  have h : UnexcitedMetric.objective ![u, 0] = u ^ 2 := by
    simp [UnexcitedMetric.objective]
  refine ⟨h, fun hu => ?_⟩
  rw [h]
  simpa [UnexcitedMetric.objective] using sq_pos_of_ne_zero hu

/-- "Yet the vertical gradient jump does not remove the direction that can reduce
this error." For `u ≠ 0` the horizontal direction `(-u,0)` strictly lowers
`F(u,v)=u^2+|v|` from every point `(u,v)`, on either side of the jump line `v=0`
and on it: `F((u,v)+t(-u,0)) < F(u,v)` for `0<t≤1`. -/
theorem horizontal_direction_reduces_error {u : ℝ} (hu : u ≠ 0) (v : ℝ) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    UnexcitedMetric.objective (![u, v] + t • ![-u, 0]) < UnexcitedMetric.objective ![u, v] := by
  have hu2 := sq_pos_of_ne_zero hu
  simp only [UnexcitedMetric.objective, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero, add_zero]
  have he : (u + t * -u) ^ 2 = (1 - t) ^ 2 * u ^ 2 := by ring
  rw [he]
  have hlt : (1 - t) ^ 2 < 1 := by nlinarith
  nlinarith

/-- The actual gradient of the mixed ridge off the line `v=0`. -/
theorem gradient_off_line {p : Vec 2} (hp : p 1 ≠ 0) :
    coordinateGradient UnexcitedMetric.objective p = ![2 * p 0, Real.sign (p 1)] := by
  have he : p = ![p 0, p 1] := by
    ext i
    fin_cases i <;> rfl
  have hg := ArticleGeometry.mixed_ridge_gradient (u := p 0) hp
  rw [← he] at hg
  exact PointwiseFeasibility.coordinateGradient_eq hg

/-- The mixed ridge is not differentiable on the line `v=0`. -/
theorem not_differentiable_on_line {p : Vec 2} (hp : p 1 = 0) :
    ¬ DifferentiableAt ℝ UnexcitedMetric.objective p := by
  intro hd
  have hl : DifferentiableAt ℝ (fun t : ℝ => p + t • (![0, 1] : Vec 2)) 0 :=
    (differentiableAt_const p).add (differentiableAt_id.smul_const _)
  have hd' : DifferentiableAt ℝ UnexcitedMetric.objective (p + (0 : ℝ) • (![0, 1] : Vec 2)) := by
    simpa using hd
  have hc := (hd'.comp (0 : ℝ) hl).sub_const ((p 0) ^ 2)
  have hf : (fun t : ℝ => (UnexcitedMetric.objective ∘ fun t : ℝ => p + t • (![0, 1] : Vec 2)) t
      - (p 0) ^ 2) = fun t : ℝ => |t| := by
    funext t
    simp only [Function.comp_def, UnexcitedMetric.objective, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero,
      add_zero, mul_one, hp, zero_add]
    ring
  rw [hf] at hc
  exact not_differentiableAt_abs_zero hc

/-- Item `A/introduction/prose/067` (`paper/sections/introduction.tex:139-140`): "make $u^2$ small, because the gradient jumps vertically between $(2u,1)$ and $(2u,-1)$. Yet both gradients have the same negative pairing $-2u^2$ with the" A vector `g` is a limit of actual gradients `∇F(p_k)` at
differentiable points `p_k → (u,0)` exactly when `g=(2u,1)` or `g=(2u,-1)`; the
difference of these two vectors is `(0,2)`. -/
theorem limiting_gradients (u : ℝ) :
    (∀ g : Vec 2,
      (∃ p : ℕ → Vec 2, Tendsto p atTop (𝓝 ![u, 0]) ∧
          (∀ k, DifferentiableAt ℝ UnexcitedMetric.objective (p k)) ∧
          Tendsto (fun k => coordinateGradient UnexcitedMetric.objective (p k)) atTop (𝓝 g)) ↔
        (g = ![2 * u, 1] ∨ g = ![2 * u, -1])) ∧
      (![2 * u, 1] : Vec 2) - ![2 * u, -1] = ![0, 2] := by
  refine ⟨fun g => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨p, hp, hd, hg⟩
    have hp1 : ∀ k, p k 1 ≠ 0 := fun k h => not_differentiable_on_line h (hd k)
    have hgk : ∀ k, coordinateGradient UnexcitedMetric.objective (p k) = ![2 * p k 0, Real.sign (p k 1)] :=
      fun k => gradient_off_line (hp1 k)
    simp only [hgk] at hg
    have hg0 := (continuous_apply 0).continuousAt.tendsto.comp hg
    have hg1 := (continuous_apply 1).continuousAt.tendsto.comp hg
    have hp0 := (continuous_apply 0).continuousAt.tendsto.comp hp
    simp only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hg0 hg1 hp0
    have h0 : g 0 = 2 * u := tendsto_nhds_unique hg0 (hp0.const_mul 2)
    have hmem : ∀ k, Real.sign (p k 1) ∈ ({1, -1} : Set ℝ) := by
      intro k
      rcases lt_or_gt_of_ne (hp1 k) with h | h
      · simp [Real.sign_of_neg h]
      · simp [Real.sign_of_pos h]
    have hclosed : IsClosed ({1, -1} : Set ℝ) := (Set.toFinite _).isClosed
    have h1 : g 1 ∈ ({1, -1} : Set ℝ) := hclosed.mem_of_tendsto hg1 (Eventually.of_forall hmem)
    rcases h1 with h1 | h1
    · left
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · right
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
  · intro hg
    have hs : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
    rcases hg with rfl | rfl
    · refine ⟨fun k => ![u, 1 / ((k : ℝ) + 1)], ?_, ?_, ?_⟩
      · rw [tendsto_pi_nhds]
        intro i
        fin_cases i
        · simp
        · simpa using hs
      · intro k
        exact (ArticleGeometry.mixed_ridge_gradient (u := u) (hpos k).ne').differentiableAt
      · have he : ∀ k : ℕ, coordinateGradient UnexcitedMetric.objective ![u, 1 / ((k : ℝ) + 1)]
            = ![2 * u, 1] := by
          intro k
          rw [gradient_off_line (by simpa using (hpos k).ne')]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
          rw [Real.sign_of_pos (hpos k)]
        simp only [he]
        exact tendsto_const_nhds
    · refine ⟨fun k => ![u, -(1 / ((k : ℝ) + 1))], ?_, ?_, ?_⟩
      · rw [tendsto_pi_nhds]
        intro i
        fin_cases i
        · simp
        · simpa using hs.neg
      · intro k
        exact (ArticleGeometry.mixed_ridge_gradient (u := u) (neg_ne_zero.mpr (hpos k).ne')).differentiableAt
      · have he : ∀ k : ℕ, coordinateGradient UnexcitedMetric.objective ![u, -(1 / ((k : ℝ) + 1))]
            = ![2 * u, -1] := by
          intro k
          rw [gradient_off_line (by simpa using (hpos k).ne')]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
          rw [Real.sign_of_neg (neg_neg_of_pos (hpos k))]
        simp only [he]
        exact tendsto_const_nhds
  · ext i
    fin_cases i <;> norm_num

/-- Item `A/introduction/prose/068` (`paper/sections/introduction.tex:140-141`): "$(2u,-1)$. Yet both gradients have the same negative pairing $-2u^2$ with the horizontal direction $(-u,0)$, and along any inward ray toward $(0,0)$ the" The gradients are the limiting
gradients `(2u,1)` and `(2u,-1)` of `limiting_gradients`. -/
theorem equal_negative_pairing {u : ℝ} (hu : u ≠ 0) :
    dot (![2 * u, 1] : Vec 2) ![-u, 0] = -2 * u ^ 2 ∧
      dot (![2 * u, -1] : Vec 2) ![-u, 0] = -2 * u ^ 2 ∧ -2 * u ^ 2 < 0 :=
  ArticleGeometry.mixed_ridge_equal_descent u hu

/-- Item `A/introduction/disp/004` (`paper/sections/introduction.tex:144-146`): "\begin{equation} F((1-\tau)(u,v))-F(u,v)+\tau\nabla F(u,v)^T(u,v)=\tau^2u^2. \end{equation}"$$
With `F(u,v)=u^2+|v|` and its actual gradient `∇F(u,v)` (which exists for `v ≠ 0`). -/
theorem mixed_inward_remainder {u v τ : ℝ} (hv : v ≠ 0) (_hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    UnexcitedMetric.objective ((1 - τ) • ![u, v]) - UnexcitedMetric.objective ![u, v] +
        τ * dot (coordinateGradient UnexcitedMetric.objective ![u, v]) ![u, v] = τ ^ 2 * u ^ 2 := by
  have hg := ArticleGeometry.mixed_ridge_gradient (u := u) hv
  rw [PointwiseFeasibility.coordinateGradient_eq hg]
  simpa using ArticleGeometry.mixed_ridge_inward hg hτ1

/-- Item `A/introduction/prose/005` (`paper/sections/introduction.tex:141-147`): "horizontal direction $(-u,0)$, and along any inward ray toward $(0,0)$ the nonsmooth term $|v|$ scales linearly with zero Taylor remainder: for $v\ne0$ and $0\le\tau\le1$, \begin{equation} F((1-\tau)(u,v))-F(u,v)+\tau\nabla F(u,v)^T(u,v)=\tau^2u^2. \end{equation} Only the smooth component $u^2$ contributes a quadratic remainder. A general" For `τ ≤ 1` the nonsmooth part
satisfies `|(1-τ)v| = (1-τ)|v|`, so its inward first-order remainder vanishes at
every `v ≠ 0` (where its derivative is `sign v`); the smooth part `u^2` has
inward remainder `((1-τ)u)^2-u^2+τ(2u)u = τ^2u^2`. -/
theorem inward_split (u v τ : ℝ) (hτ : τ ≤ 1) :
    |(1 - τ) * v| = (1 - τ) * |v| ∧
      (v ≠ 0 → |(1 - τ) * v| - |v| + τ * (Real.sign v * v) = 0) ∧
      ((1 - τ) * u) ^ 2 - u ^ 2 + τ * (2 * u * u) = τ ^ 2 * u ^ 2 := by
  have hlin : |(1 - τ) * v| = (1 - τ) * |v| := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hτ)]
  refine ⟨hlin, fun hv => ?_, by ring⟩
  rw [hlin]
  rcases lt_or_gt_of_ne hv with h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · rw [Real.sign_of_pos h, abs_of_pos h]
    ring

/-! ## The seed corner -/

/-- Item `A/introduction/prose/076` (`paper/sections/introduction.tex:168-169`): Item `A/introduction/prose/014` (`paper/sections/introduction.tex:165-168`): the slopes are "$(-1,16)^T$ decreases all three linear pieces, yet \emph{every} nonzero vector $w\in\R^2$ sees an $O(1)$ jump across at least one switching step. We show that" -/
theorem seed_affinely_independent :
    SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD =
        ![![1, 0], ![-1, -1 / 8], ![SeedOrbit.seedC, SeedOrbit.seedD]] ∧
      AffineIndependent ℝ (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD) ∧
      ∀ (v : Vec 2) (κ : ℝ),
        (∀ j, dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j) v = κ) → v = 0 := by
  refine ⟨?_, ArticleGeometry.seed_affine_independent,
    fun v κ h => ArticleGeometry.seed_equal_pairings_force_zero h⟩
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- "Yet $(-1,16)$ has negative pairing with each, and zero is outside their convex
hull." -/
theorem seed_common_descent :
    (∀ j, dot (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD j) ![-1, 16] < 0) ∧
      (0 : Vec 2) ∉ convexHull ℝ (range (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD)) :=
  ⟨ArticleGeometry.seed_strict_common_descent, ArticleGeometry.seed_convex_hull_excludes_zero⟩

/-- "The corner is therefore nonstationary." Zero is not a subgradient of the seed
objective `G(z)=max_i g_i^T z` at the corner `z=0`; indeed `G` decreases at unit
rate along `(-1,16)`. -/
theorem seed_corner_nonstationary :
    (0 : Vec 2) ∉
        ConvexSubdifferential.subdifferential (SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD) 0 ∧
      ∀ t : ℝ, 0 ≤ t → SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD (t • ![-1, 16]) = -t := by
  have hray : ∀ t : ℝ, 0 ≤ t → SeedOrbit.objective SeedOrbit.seedC SeedOrbit.seedD (t • ![-1, 16]) = -t :=
    fun t ht => DEmbedding.seed_descent_ray ht
  refine ⟨fun h => ?_, hray⟩
  have h1 := h ((1 : ℝ) • ![-1, 16])
  have h0 := hray 0 le_rfl
  rw [zero_smul] at h0
  rw [hray 1 zero_le_one, h0] at h1
  simp [dot] at h1
  linarith

/-- Item `A/introduction/prose/069` (`paper/sections/introduction.tex:130-133`): "with both. (b)~The nonstationary three-slope corner of Section~\ref{art:failure}: $0$ lies outside $\conv\{g_0,g_1,g_2\}$ (at distance $1/\sqrt{257}$ above the edge $[g_1,g_0]$, so $(-1,16)$ is a strict common descent direction), yet $\aff\{g_0,g_1,g_2\}=\R^2$, destroying any jump-canceling comparison direction.}" -/
theorem seed_hulls :
    (0 : Vec 2) ∉ convexHull ℝ (range (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD)) ∧
      affineSpan ℝ (range (SeedOrbit.gradient SeedOrbit.seedC SeedOrbit.seedD)) = ⊤ :=
  ⟨ArticleGeometry.seed_convex_hull_excludes_zero, ArticleGeometry.seed_affine_span_top⟩

/-! ## Affine and convex balance of a finite slope family -/

section Balance

/-- For a nonempty
finite family of slopes `a_i`, "equality $a_i^Tv=\kappa<0$ for every $i$ asks for a
common rate of descent ... The former fails when zero belongs to their affine
hull". -/
theorem common_rate_fails_of_mem_affineSpan {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ affineSpan ℝ (range a)) :
    ¬ ∃ (v : EuclideanSpace ℝ (Fin n)) (κ : ℝ), κ < 0 ∧ ∀ i, ⟪a i, v⟫_ℝ = κ := fun h =>
  (ArticleGeometry.affine_negative_common_rate_iff a (Classical.arbitrary ι)).mp h h0

/-- "$a_i^Tv<0$ asks
only for descent ... the latter fails when zero belongs to their convex hull." -/
theorem descent_fails_of_mem_convexHull {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ convexHull ℝ (range a)) :
    ¬ ∃ v : EuclideanSpace ℝ (Fin n), ∀ i, ⟪a i, v⟫_ℝ < 0 := fun h =>
  (ArticleGeometry.finite_slopes_common_descent_iff a).mp h h0

/-- "Indeed, a linear
functional constant on the slopes is constant on their affine hull." -/
theorem constant_on_affineSpan {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (c : ℝ) (h : ∀ i, ⟪a i, v⟫_ℝ = c) :
    ∀ z ∈ affineSpan ℝ (range a), ⟪z, v⟫_ℝ = c :=
  AffineCriticalGeometry.affine_pairing_of_constant a v c h

/-- "Conversely, if zero
is outside that affine hull, its nearest point gives a separating functional
constant on the hull; changing its sign gives the negative common value." The
nearest point `p` of the affine hull to zero satisfies `z^T p = ‖p‖^2 > 0` on the
hull, and `v=-p` gives `a_i^T v = -‖p‖^2 < 0` for every `i`. -/
theorem nearest_point_common_rate {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∉ affineSpan ℝ (range a)) :
    ∃ p ∈ affineSpan ℝ (range a),
      (∀ z ∈ affineSpan ℝ (range a), ‖p‖ ≤ ‖z‖) ∧ 0 < ‖p‖ ^ 2 ∧
      (∀ z ∈ affineSpan ℝ (range a), ⟪z, p⟫_ℝ = ‖p‖ ^ 2) ∧
      ∀ i, ⟪a i, -p⟫_ℝ = -‖p‖ ^ 2 := by
  set s := affineSpan ℝ (range a) with hs
  haveI : Nonempty s := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨⟨a i, subset_affineSpan ℝ _ (mem_range_self i)⟩⟩
  set p : EuclideanSpace ℝ (Fin n) := ↑(EuclideanGeometry.orthogonalProjection s 0) with hp
  have hps : p ∈ s := EuclideanGeometry.orthogonalProjection_mem 0
  have horth := EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal s
    (0 : EuclideanSpace ℝ (Fin n))
  rw [← hp] at horth
  have hconst : ∀ z ∈ s, ⟪z, p⟫_ℝ = ‖p‖ ^ 2 := by
    intro z hz
    have hdir : z -ᵥ p ∈ s.direction := AffineSubspace.vsub_mem_direction hz hps
    have h := (Submodule.mem_orthogonal _ _).mp horth _ hdir
    simp only [vsub_eq_sub, zero_sub, inner_neg_right, neg_eq_zero, inner_sub_left] at h
    rw [← real_inner_self_eq_norm_sq]
    linarith
  have hne : p ≠ 0 := fun h => h0 (h ▸ hps)
  have hpos : 0 < ‖p‖ ^ 2 := by positivity
  refine ⟨p, hps, fun z hz => ?_, hpos, hconst, fun i => ?_⟩
  · have hz2 : ‖z‖ ^ 2 = ‖p‖ ^ 2 + ‖z - p‖ ^ 2 := by
      have hc := hconst z hz
      rw [norm_sub_sq_real, hc]
      ring
    have : ‖p‖ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z - p‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  · rw [inner_neg_right, hconst _ (subset_affineSpan ℝ _ (mem_range_self i))]

/-- "The convex version
follows from the same closest-point argument for the convex hull." If zero is
outside the convex hull, its nearest point `p` in the hull satisfies
`z^T p ≥ ‖p‖^2 > 0` on the hull, so `v=-p` is a common strict descent direction. -/
theorem closest_point_descent {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∉ convexHull ℝ (range a)) :
    ∃ p ∈ convexHull ℝ (range a),
      (∀ z ∈ convexHull ℝ (range a), ‖p‖ ≤ ‖z‖) ∧ 0 < ‖p‖ ^ 2 ∧
      (∀ z ∈ convexHull ℝ (range a), ‖p‖ ^ 2 ≤ ⟪z, p⟫_ℝ) ∧
      ∀ i, ⟪a i, -p⟫_ℝ < 0 := by
  set K := convexHull ℝ (range a) with hK
  have hKc : IsCompact K := (Set.finite_range a).isCompact_convexHull
  have hKne : K.Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨a i, subset_convexHull ℝ _ (mem_range_self i)⟩
  have hconv : Convex ℝ K := convex_convexHull ℝ _
  obtain ⟨p, hpK, hpmin⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKc.isComplete hconv
    (0 : EuclideanSpace ℝ (Fin n))
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hconv hpK).mp hpmin
  have hlow : ∀ z ∈ K, ‖p‖ ^ 2 ≤ ⟪z, p⟫_ℝ := by
    intro z hz
    have h := hvar z hz
    simp only [zero_sub, inner_neg_left, inner_sub_right] at h
    rw [← real_inner_self_eq_norm_sq]
    have hcomm := real_inner_comm p z
    linarith
  have hne : p ≠ 0 := fun h => h0 (h ▸ hpK)
  have hpos : 0 < ‖p‖ ^ 2 := by positivity
  refine ⟨p, hpK, fun z hz => ?_, hpos, hlow, fun i => ?_⟩
  · have hz := hlow z hz
    have hcs := real_inner_le_norm z p
    have : ‖p‖ ^ 2 ≤ ‖z‖ * ‖p‖ := hz.trans hcs
    have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hne
    nlinarith
  · rw [inner_neg_right]
    have := hlow _ (subset_convexHull ℝ _ (mem_range_self i))
    linarith

end Balance

/-! ## Table `art:positive-outcomes` -/

/-- The caption of Table `art:positive-outcomes` as printed
before the correction of 15 October 2026 (M31, reader point R-A-2): "The benchmark $u^2+|v|$ has
compact sublevels everywhere, so the first row gives global convergence." The corrected caption
is `benchmark_centered_global`. Every sublevel of
`F(u,v)=u^2+|v|` is compact, and every infinite admissible run converges to the
minimizer in value and iterates. -/
theorem benchmark_compact_sublevels_global :
    (∀ b : ℝ, IsCompact {x : Vec 2 | UnexcitedMetric.objective x ≤ b}) ∧
      ∀ R : AdmissibleBFGSRun 2 UnexcitedMetric.objective,
        Tendsto (fun k => UnexcitedMetric.objective (R.x k)) atTop (𝓝 0) ∧
          Tendsto R.x atTop (𝓝 0) := by
  have hmin : ∀ x, UnexcitedMetric.objective 0 ≤ UnexcitedMetric.objective x := by
    intro x
    simpa [UnexcitedMetric.objective] using UnexcitedMetric.objective_nonneg x
  have hu : ∀ x, UnexcitedMetric.objective x = UnexcitedMetric.objective 0 → x = 0 :=
    fun _ hx => UnexcitedMetric.unique_minimum hx
  exact ⟨Localization.sublevel_compact UnexcitedMetric.objective_convex 0 hmin hu,
    ArticlePositive.mixed_benchmark_global⟩

/-- Item `A/introduction/prose/031` (`paper/sections/introduction.tex:218`): , as corrected on 15 October 2026 (M31, reader point R-A-2): "$0<c_1<c_2<1$. For $F(u,v)=u^2+|v|$ the first row applies on all of $\R^2$.}" Every sublevel of `F(u,v)=u^2+|v|` is compact; on
$U=\R^2$, $F(x)=\psi(x)+\gamma(x-x_*)$ with $x_*=0$ a minimizer of $F$, $\psi(u,v)=u^2$ convex
and locally $C^{1,1}$, and $\gamma(u,v)=|v|$ convex and positively homogeneous of degree one (the
hypotheses of Theorem `art:centered`); and every infinite admissible run converges to the
minimizer in value and iterates. -/
theorem benchmark_centered_global :
    (∀ b : ℝ, IsCompact {x : Vec 2 | UnexcitedMetric.objective x ≤ b}) ∧
      (ConvexOn ℝ univ (fun x : Vec 2 => (x 0) ^ 2) ∧
        CenteredSmoothSublinear.LocallyC11On univ (fun x : Vec 2 => (x 0) ^ 2) ∧
        ConvexOn ℝ univ (fun x : Vec 2 => |x 1|) ∧
        Homogeneous.PositiveDegreeOne (fun x : Vec 2 => |x 1|) ∧
        (∀ x, UnexcitedMetric.objective 0 ≤ UnexcitedMetric.objective x) ∧
        ∀ x, UnexcitedMetric.objective x = (x 0) ^ 2 + |(x - 0) 1|) ∧
      ∀ R : AdmissibleBFGSRun 2 UnexcitedMetric.objective,
        Tendsto (fun k => UnexcitedMetric.objective (R.x k)) atTop (𝓝 0) ∧
          Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨hcompact, hglobal⟩ := benchmark_compact_sublevels_global
  have hψ : ConvexOn ℝ univ (fun x : Vec 2 => (x 0) ^ 2) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have he : (a * x 0 + b * y 0) ^ 2 + a * b * (x 0 - y 0) ^ 2 =
        (a + b) * (a * (x 0) ^ 2 + b * (y 0) ^ 2) := by ring
    rw [hab, one_mul] at he
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0 - y 0))]
  have hψ11 : CenteredSmoothSublinear.LocallyC11On univ (fun x : Vec 2 => (x 0) ^ 2) :=
    ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ (by fun_prop : ContDiff ℝ 2
      (fun x : Vec 2 => (x 0) ^ 2)).contDiffOn
  have hγ : ConvexOn ℝ univ (fun x : Vec 2 => |x 1|) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * x 1 + b * y 1| ≤ |a * x 1| + |b * y 1| := abs_add_le _ _
      _ = a * |x 1| + b * |y 1| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hγh : Homogeneous.PositiveDegreeOne (fun x : Vec 2 => |x 1|) := by
    intro t ht x
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
  have hmin : ∀ x, UnexcitedMetric.objective 0 ≤ UnexcitedMetric.objective x := fun x => by
    simpa [UnexcitedMetric.objective] using UnexcitedMetric.objective_nonneg x
  exact ⟨hcompact, ⟨hψ, hψ11, hγ, hγh, hmin, fun x => by simp [UnexcitedMetric.objective]⟩, hglobal⟩

/-- Item `A/introduction/prose/020` (`paper/sections/introduction.tex:159-162`): The common-descent half of the balance facts, for a nonempty finite slope family `a_i` in
`EuclideanSpace ℝ (Fin n)`: a direction with `a_i^Tw < 0` for all `i` exists iff zero is outside
the convex hull of the slopes. -/
theorem common_descent_iff {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n)) :
    (∃ w : EuclideanSpace ℝ (Fin n), ∀ i, ⟪a i, w⟫_ℝ < 0) ↔
      (0 : EuclideanSpace ℝ (Fin n)) ∉ convexHull ℝ (range a) :=
  ArticleGeometry.finite_slopes_common_descent_iff a

/-- Item `A/introduction/prose/019` (`paper/sections/introduction.tex:162-165`): The equal-rate half of the balance facts: a direction with `a_i^Tw = κ < 0` for all `i`
exists iff zero is outside the affine hull of the slopes. Such a direction is exactly one that
screens out all jumps, `(a_i-a_j)^Tw = 0`, while keeping `a_i^Tw < 0`. -/
theorem equal_rate_descent_iff {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n)) :
    ((∃ (w : EuclideanSpace ℝ (Fin n)) (κ : ℝ), κ < 0 ∧ ∀ i, ⟪a i, w⟫_ℝ = κ) ↔
      (0 : EuclideanSpace ℝ (Fin n)) ∉ affineSpan ℝ (range a)) ∧
    ∀ w : EuclideanSpace ℝ (Fin n),
      ((∀ i j, ⟪a i - a j, w⟫_ℝ = 0) ∧ ∀ i, ⟪a i, w⟫_ℝ < 0) ↔
        ∃ κ : ℝ, κ < 0 ∧ ∀ i, ⟪a i, w⟫_ℝ = κ := by
  refine ⟨ArticleGeometry.affine_negative_common_rate_iff a (Classical.arbitrary ι), fun w => ?_⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟪a (Classical.arbitrary ι), w⟫_ℝ, h2 _, fun i => ?_⟩
    have := h1 i (Classical.arbitrary ι)
    rw [inner_sub_left] at this
    linarith
  · rintro ⟨κ, hκ, h⟩
    exact ⟨fun i j => by rw [inner_sub_left, h i, h j, sub_self], fun i => (h i).trans_lt hκ⟩

end GeometryMechanisms

end BfgsCoverage.Article.Introduction
