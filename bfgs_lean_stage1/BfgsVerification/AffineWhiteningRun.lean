import BfgsVerification.AffineImageRun
import BfgsVerification.AffineCertificateAlgebra
import BfgsVerification.DeterministicLineSearch

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.AffineWhitening
open AffineProjection

variable {n : ℕ}

def objective (A : Mat n) (F : Vec n → ℝ) : Vec n → ℝ := fun z => F (A.mulVec z)
def point (A : Mat n) (x : Vec n) : Vec n := A⁻¹.mulVec x
def metric (A H : Mat n) : Mat n := compress A⁻¹ H
def gradient (A : Mat n) (g : Vec n) : Vec n := Aᵀ.mulVec g

theorem map_point (A : Mat n) (hA : A.det≠0) (x : Vec n) : A.mulVec (point A x)=x := by
  rw [point,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hA.isUnit,Matrix.one_mulVec]

theorem point_map (A : Mat n) (hA : A.det≠0) (x : Vec n) : point A (A.mulVec x)=x := by
  rw [point,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hA.isUnit,Matrix.one_mulVec]

theorem inverse_fullRowRank (A : Mat n) (hA : A.det≠0) : FullRowRank A⁻¹ := by
  intro x y h
  have hh := congrArg Aᵀ.mulVec h
  simpa only [Matrix.mulVec_mulVec,← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul _ hA.isUnit,Matrix.transpose_one,Matrix.one_mulVec] using hh

theorem gradient_inverse (A : Mat n) (hA : A.det≠0) (g : Vec n) :
    (A⁻¹)ᵀ.mulVec (gradient A g)=g := by
  exact AffineCertificate.inverse_transpose_transpose A hA g

theorem dot_gradient_point (A : Mat n) (hA : A.det≠0) (g s : Vec n) :
    dot (gradient A g) (point A s)=dot g s := by
  rw [gradient,dot_transpose_mulVec,map_point A hA]

theorem step_equiv (A : Mat n) (hA : A.det≠0) (H : Mat n) (g : Vec n) (a : ℝ) :
    bfgsStep (metric A H) (gradient A g) a=point A (bfgsStep H g a) := by
  simpa only [gradient_inverse A hA] using (project_step A⁻¹ H (gradient A g) a).symm

theorem update_equiv (A : Mat n) (hA : A.det≠0) (H : Mat n) (s y : Vec n) :
    metric A (inverseBFGS H s y)=
      inverseBFGS (metric A H) (point A s) (gradient A y) := by
  have h := inverseBFGS_compress A⁻¹ H s (gradient A y)
  simpa only [gradient_inverse A hA] using h

theorem hasGradient_equiv (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ) (x g : Vec n)
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    HasFDerivAt (objective A F) (gradientFunctional (gradient A g)) (point A x) := by
  apply hasGradient_comp
  rwa [map_point A hA]

def run (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    AdmissibleBFGSRun n (objective A F) where
  convex := by
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    simpa only [objective,Matrix.mulVec_add,Matrix.mulVec_smul] using
      R.convex.2 (mem_univ (A.mulVec x)) (mem_univ (A.mulVec y)) ha hb hab
  x k := point A (R.x k)
  H k := metric A (R.H k)
  g k := gradient A (R.g k)
  α := R.α
  c₁ := R.c₁
  c₂ := R.c₂
  c₁_pos := R.c₁_pos
  c₁_lt_c₂ := R.c₁_lt_c₂
  c₂_lt_one := R.c₂_lt_one
  initial_posDef := compress_posDef A⁻¹ (inverse_fullRowRank A hA) R.initial_posDef
  alpha_pos := R.alpha_pos
  gradient_nonzero k := by
    intro h
    have hh := congrArg (A⁻¹)ᵀ.mulVec h
    rw [gradient_inverse A hA,Matrix.mulVec_zero] at hh
    exact R.gradient_nonzero k hh
  hasGradient k := hasGradient_equiv A hA F _ _ (R.hasGradient k)
  step k := by
    rw [R.step,step_equiv A hA]
    exact Matrix.mulVec_add _ _ _
  update k := by
    rw [R.update,update_equiv A hA,step_equiv A hA]
    simp only [gradient,Matrix.mulVec_sub]
  armijo k := by
    simpa only [objective,map_point A hA,step_equiv A hA,dot_gradient_point A hA] using R.armijo k
  weak_wolfe k := by
    simpa only [step_equiv A hA,dot_gradient_point A hA] using R.weak_wolfe k

@[simp] theorem run_x (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (k : ℕ) : (run A hA R).x k=point A (R.x k) := rfl
@[simp] theorem run_H (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (k : ℕ) : (run A hA R).H k=metric A (R.H k) := rfl
@[simp] theorem run_g (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (k : ℕ) : (run A hA R).g k=gradient A (R.g k) := rfl
@[simp] theorem run_alpha (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (k : ℕ) : (run A hA R).α k=R.α k := rfl
@[simp] theorem run_value (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (k : ℕ) : objective A F ((run A hA R).x k)=F (R.x k) := by
  exact congrArg F (map_point A hA _)

theorem query_equiv (A : Mat n) (hA : A.det≠0) (x g : Vec n) (H : Mat n) (a : ℝ) :
    point A x+a • bfgsStep (metric A H) (gradient A g) 1=
      point A (x+a • bfgsStep H g 1) := by
  rw [step_equiv A hA]
  simp only [point,Matrix.mulVec_add,Matrix.mulVec_smul]

end BfgsVerification.AffineWhitening
