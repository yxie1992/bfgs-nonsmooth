import BfgsVerification.LEmbeddingObjective
import BfgsVerification.LScalarStepTargets

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LStepEmbedding
open LEmbedding

def residualBranch : Fin 4 → Vec 2 → ℝ :=
  ![fun x => LScalarStep.phi (parameter 0) (dot (slope 0) x),
    fun x => LScalarStep.phi (parameter 1) (dot (slope 1) x),
    fun x => LScalarStep.phi (parameter 2) (dot (slope 2) x),
    fun x => x 1]
def residual (x : Vec 2) : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => residualBranch i x)
def branch (i : Fin 4) (x : Vec 2) : ℝ := LQuadraticSeed.quadratic mu x+residualBranch i x
def objective (x : Vec 2) : ℝ := LQuadraticSeed.quadratic mu x+residual x

theorem residualBranch_old (i : Fin 3) (x : Vec 2) :
    residualBranch i.castSucc x=LScalarStep.phi (parameter i) (dot (slope i) x) := by
  fin_cases i <;> rfl

theorem residualBranch_last (x : Vec 2) : residualBranch 3 x=x 1 := rfl

theorem residualBranch_le (i : Fin 4) (x : Vec 2) : residualBranch i x≤residual x :=
  Finset.le_sup' (fun j => residualBranch j x) (Finset.mem_univ i)

theorem residual_le {x : Vec 2} {a : ℝ} (h : ∀i,residualBranch i x≤a) : residual x≤a := by
  apply Finset.sup'_le
  intro i _
  exact h i

theorem branch_le (i : Fin 4) (x : Vec 2) : branch i x≤objective x :=
  add_le_add_left (residualBranch_le i x) _

theorem objective_le {x : Vec 2} {a : ℝ} (h : ∀i,branch i x≤a) : objective x≤a := by
  have hh : residual x≤a-LQuadraticSeed.quadratic mu x := residual_le (fun i => by
    have hi := h i
    change LQuadraticSeed.quadratic mu x+residualBranch i x≤a at hi
    linarith)
  exact (add_le_add_left hh _).trans_eq (by ring)

theorem objective_eq_max (x : Vec 2) :
    objective x=Finset.univ.sup' Finset.univ_nonempty (fun i => branch i x) := by
  apply le_antisymm
  · exact objective_le (fun i => Finset.le_sup' (fun j => branch j x) (Finset.mem_univ i))
  · apply Finset.sup'_le
    intro i _
    exact branch_le i x

theorem ridge_convex (i : Fin 3) :
    ConvexOn ℝ univ (fun x => LScalarStep.phi (parameter i) (dot (slope i) x)) := by
  simpa only [preimage_univ,ContinuousLinearMap.coe_coe,gradientFunctional_apply,Function.comp_def]
    using (LScalarStep.phi_convex (parameter_bounds i).1.le (parameter_bounds i).2.le).comp_linearMap
      (gradientFunctional (slope i)).toLinearMap

theorem residualBranch_convex (i : Fin 4) : ConvexOn ℝ univ (residualBranch i) := by
  fin_cases i
  · exact ridge_convex 0
  · exact ridge_convex 1
  · exact ridge_convex 2
  · exact (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).toLinearMap.convexOn convex_univ

theorem residual_convex : ConvexOn ℝ univ residual := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  apply residual_le
  intro i
  exact ((residualBranch_convex i).2 hx hy ha hb hab).trans
    (add_le_add (mul_le_mul_of_nonneg_left (residualBranch_le i x) ha)
      (mul_le_mul_of_nonneg_left (residualBranch_le i y) hb))

theorem branch_convex (i : Fin 4) : ConvexOn ℝ univ (branch i) :=
  (LQuadraticSeed.quadratic_convex mu_pos.le).add (residualBranch_convex i)

theorem objective_convex : ConvexOn ℝ univ objective :=
  (LQuadraticSeed.quadratic_convex mu_pos.le).add residual_convex

theorem branch_strongConvex (i : Fin 4) : FixedNormal.EuclideanStrongConvexOn univ mu (branch i) := by
  simpa only [FixedNormal.EuclideanStrongConvexOn,branch,LQuadraticSeed.quadratic,add_sub_cancel_left]
    using residualBranch_convex i

theorem objective_strongConvex : FixedNormal.EuclideanStrongConvexOn univ mu objective := by
  simpa only [FixedNormal.EuclideanStrongConvexOn,objective,LQuadraticSeed.quadratic,add_sub_cancel_left]
    using residual_convex

theorem residual_nonnegative (x : Vec 2) : 0≤residual x :=
  (LScalarStep.phi_nonnegative (parameter 0) (dot (slope 0) x)).trans
    (residualBranch_le 0 x)

theorem objective_lower (x : Vec 2) : mu/2*sqNorm x≤objective x := by
  have hh := residual_nonnegative x
  change mu/2*sqNorm x ≤ mu/2*sqNorm x+residual x
  linarith

theorem residualBranch_zero (i : Fin 4) : residualBranch i 0=0 := by
  fin_cases i
  · simpa [residualBranch,dot] using LScalarStep.phi_zero (parameter_bounds 0).1.le (parameter_bounds 0).2.le
  · simpa [residualBranch,dot] using LScalarStep.phi_zero (parameter_bounds 1).1.le (parameter_bounds 1).2.le
  · simpa [residualBranch,dot] using LScalarStep.phi_zero (parameter_bounds 2).1.le (parameter_bounds 2).2.le
  · rfl

theorem residual_zero : residual 0=0 :=
  le_antisymm (residual_le (fun i => (residualBranch_zero i).le)) (residual_nonnegative 0)

theorem objective_zero : objective 0=0 := by simp [objective,LQuadraticSeed.quadratic,sqNorm,residual_zero]

theorem objective_nonnegative (x : Vec 2) : 0≤objective x :=
  (mul_nonneg (div_nonneg mu_pos.le (by norm_num)) (sqNorm_nonneg x)).trans (objective_lower x)

theorem objective_unique_zero {x : Vec 2} (hx : objective x=0) : x=0 := by
  have hh := objective_lower x
  rw [hx] at hh
  have hs : sqNorm x=0 := by
    dsimp [mu] at hh
    nlinarith [sqNorm_nonneg x]
  exact (CertificateGeometry.sqNorm_eq_zero_iff x).mp hs

theorem objective_sublevels_compact (a : ℝ) : IsCompact {x | objective x≤a} := by
  apply Localization.sublevel_compact objective_convex (0 : Vec 2)
  · intro x
    rw [objective_zero]
    exact objective_nonnegative x
  · intro x hx
    rw [objective_zero] at hx
    exact objective_unique_zero hx

end BfgsVerification.LStepEmbedding
