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

/-- Item `A/introduction/disp/001` (`paper/sections/introduction.tex:32-34`): the mixed
model $F(u,v)=u^2+|v|$. The library objective `UnexcitedMetric.objective` is this
formula. -/
theorem mixed_model_formula (u v : ℝ) : UnexcitedMetric.objective ![u, v] = u ^ 2 + |v| := by
  simp [UnexcitedMetric.objective]

/-- Item `A/introduction/prose/010` (`paper/sections/introduction.tex:38-39`):
"Approaching the nonsmooth line does not force the smooth coordinate $u$ to
vanish." For `u ≠ 0` the points `(u,1/(k+1))`, at which `F(u,v)=u^2+|v|` is
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

/-- Item `A/introduction/prose/035` (`paper/sections/introduction.tex:87-89`): the norm
`‖x‖_1`, "whose nonsmooth set for $n\ge2$ contains coordinate hyperplanes, beyond
the isolated nonsmooth point of the Euclidean-norm case above." For `n ≥ 2`:
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

/-- Item `A/introduction/prose/038` (`paper/sections/introduction.tex:94-96`): "The
explicit three-quadratic example in Theorem~\ref{art:nonradial-example} has curved
switching sets and fails the radial condition". For every pair of branches, the
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

/-- Item `A/introduction/prose/041` (`paper/sections/introduction.tex:101-102`): "The
uniform smooth secant bound used there need not hold when gradients jump." The
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

end BfgsCoverage.Article.Introduction
