import BfgsVerification.ConvexCellRadial
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Uniform

noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.ConvexCellRadial

theorem contDiffOn_two_locallyC11 {n : ℕ} {f : Vec n → ℝ} {U : Set (Vec n)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    CenteredSmoothSublinear.LocallyC11On U f := by
  refine ⟨hf.differentiableOn (by norm_num),?_⟩
  have hd : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  intro x hx
  obtain ⟨M,V,hV,hLip⟩ := (hd.contDiffAt (hU.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨M,V,mem_nhdsWithin_of_mem_nhds hV,hLip⟩

/-- An actual arbitrary quadratic polynomial; no symmetry, positive
semidefiniteness, or convexity of an individual cell extension is imposed. -/
def quadratic {n : ℕ} (Q : Mat n) (a : Vec n) (b : ℝ) (x : Vec n) : ℝ :=
  (∑ i, ∑ j, Q i j*x i*x j)+(∑ i, a i*x i)+b

theorem quadratic_contDiff {n : ℕ} (Q : Mat n) (a : Vec n) (b : ℝ)
    {N : WithTop ℕ∞} : ContDiff ℝ N (quadratic Q a b) := by
  unfold quadratic
  apply ContDiff.add _ contDiff_const
  apply ContDiff.add
  · apply ContDiff.sum
    intro i hi
    apply ContDiff.sum
    intro j hj
    fun_prop
  · apply ContDiff.sum
    intro i hi
    fun_prop

theorem quadratic_locallyC11 {n : ℕ} (Q : Mat n) (a : Vec n) (b : ℝ) :
    CenteredSmoothSublinear.LocallyC11On univ (quadratic Q a b) :=
  contDiffOn_two_locallyC11 isOpen_univ (quadratic_contDiff Q a b).contDiffOn

theorem locallyC11_add {n : ℕ} {f g : Vec n → ℝ} {U : Set (Vec n)}
    (hU : IsOpen U) (hf : CenteredSmoothSublinear.LocallyC11On U f)
    (hg : CenteredSmoothSublinear.LocallyC11On U g) :
    CenteredSmoothSublinear.LocallyC11On U (fun x => f x+g x) := by
  have he : ∀ x ∈ U, fderiv ℝ (fun x => f x+g x) x = fderiv ℝ f x+fderiv ℝ g x := by
    intro x hx
    exact (((hf.1 x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.add
      ((hg.1 x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt).fderiv
  refine ⟨hf.1.add hg.1,?_⟩
  intro x hx
  obtain ⟨M,V,hV,hLip⟩ := (hf.2.add hg.2) hx
  refine ⟨M,V ∩ U,inter_mem hV self_mem_nhdsWithin,?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y hy z hz
  rw [he y hy.2,he z hz.2]
  exact hLip.dist_le_mul y hy.1 z hz.1

/-- A finite convex piecewise linear-quadratic objective has the source local
convergence basin. All quadratic regularity is derived from its coefficients. -/
theorem piecewise_quadratic_basin {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (Q : ι → Mat n) (c : ι → Vec n) (d : ι → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hsU : star ∈ U)
    (hcover : ∀ x ∈ U, ∃ i, x ∈ polyhedron (a i) (b i))
    (hrep : ∀ i x, x ∈ U → x ∈ polyhedron (a i) (b i) → F x = quadratic (Q i) (c i) (d i) x)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x = star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) :=
  finite_polyhedral_basin hF a b (fun _ => univ) (fun i => quadratic (Q i) (c i) (d i))
    (fun _ => isOpen_univ) (fun i => quadratic_locallyC11 (Q i) (c i) (d i))
    hU hsU (fun _ => subset_univ _) hcover hrep hmin hu

theorem smooth_plus_piecewise_quadratic_basin {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (Q : ι → Mat n) (c : ι → Vec n) (d : ι → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hsU : star ∈ U)
    (hψ : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hcover : ∀ x ∈ U, ∃ i, x ∈ polyhedron (a i) (b i))
    (hrep : ∀ i x, x ∈ U → x ∈ polyhedron (a i) (b i) →
      F x = ψ x+quadratic (Q i) (c i) (d i) x)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x = star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  have hq (i : ι) : CenteredSmoothSublinear.LocallyC11On U (quadratic (Q i) (c i) (d i)) :=
    ⟨(quadratic_locallyC11 (Q i) (c i) (d i)).1.mono (subset_univ _),
      (quadratic_locallyC11 (Q i) (c i) (d i)).2.mono (subset_univ _)⟩
  exact finite_polyhedral_basin hF a b (fun _ => U)
    (fun i x => ψ x+quadratic (Q i) (c i) (d i) x)
    (fun _ => hU) (fun i => locallyC11_add hU hψ (hq i))
    hU hsU (fun _ => inter_subset_left) hcover hrep hmin hu

end BfgsVerification.ConvexCellRadial
