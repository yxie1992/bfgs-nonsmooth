import BfgsVerification.AlgebraicSeedCycle
import BfgsVerification.MaxAffineCalculus
import BfgsVerification.IntervalBounds
noncomputable section
open scoped BigOperators
open Matrix
namespace BfgsVerification.SeedOrbit
open SeedCycle AlgebraicSeed

def gradient (c d : ℝ) : Fin 3 → Vec 2 := ![g0,g1,g2 c d]
def family (c d : ℝ) : MaxAffine.Family 2 3 where
  a := gradient c d
  b := 0
  nonempty := ⟨0⟩
def objective (c d : ℝ) : Vec 2 → ℝ := (family c d).objective

def initialPoint (c d r : ℝ) : Vec 2 := ![(897/1024-r*(1-c))/(1-r),(r*d-1/64)/(1-r)]
def point (c d r : ℝ) : Fin 3 → Vec 2 :=
  ![initialPoint c d r,initialPoint c d r+![-1,0],initialPoint c d r+![-897/1024,1/64]]
def direction (c d r : ℝ) : Fin 3 → Vec 2 :=
  ![![-1,0],![127/256,1/16],![16*r*(1-c),-16*r*d]]
def length : Fin 3 → ℝ := ![1,1/4,1/16]
def metric (c d : ℝ) : Fin 3 → Mat 2 := ![1,M1,update M1 g1 (g2 c d) (1/4)]
def trial (c d r : ℝ) (j : Fin 3) (a : ℝ) : Vec 2 := point c d r j+a • direction c d r j

def StrictActive (c d : ℝ) (x : Vec 2) (i : Fin 3) : Prop :=
  ∀ j, j ≠ i → dot (gradient c d j) x < dot (gradient c d i) x

/-- Strictly active actual branch and the uniform source coordinate/value bounds. -/
structure PointCertificate (c d : ℝ) (x : Vec 2) (i : Fin 3) : Prop where
  active : StrictActive c d x i
  branch_bounds : ∀ k, |dot (gradient c d k) x| < 3
  vertical : x 1 < 2
  value_pos : 0 < dot (gradient c d i) x

/-- Every displayed trial has a strict decision, actual descent and, on acceptance,
a positive new-gradient pairing (which implies all ordinary positive Wolfe constants). -/
structure TrialCertificate (c d r : ℝ) (j : Fin 3) (a : ℝ) (i : Fin 3) (accept : Bool) : Prop
    extends PointCertificate c d (trial c d r j a) i where
  descent : dot (gradient c d j) (a • direction c d r j) < 0
  decision : if accept then
    dot (gradient c d i) (trial c d r j a) <
      dot (gradient c d j) (point c d r j)+(1/3)*dot (gradient c d j) (a • direction c d r j)
    else dot (gradient c d j) (point c d r j) < dot (gradient c d i) (trial c d r j a)
  wolfe : accept=true → 0 < dot (gradient c d i) (a • direction c d r j)

theorem objective_of_active {c d : ℝ} {x : Vec 2} {i : Fin 3} (hi : StrictActive c d x i) :
    objective c d x = dot (gradient c d i) x := by
  apply le_antisymm
  · unfold objective MaxAffine.Family.objective
    apply Finset.sup'_le
    intro j _
    change dot (gradient c d j) x+0 ≤ _
    by_cases hj : j=i
    · subst j; simp
    · simpa using (hi j hj).le
  · simpa [MaxAffine.Family.branch,family] using (family c d).branch_le i x

theorem hasGradient_of_active {c d : ℝ} {x : Vec 2} {i : Fin 3} (hi : StrictActive c d x i) :
    HasFDerivAt (objective c d) (gradientFunctional (gradient c d i)) x := by
  apply (family c d).strict_active_hasGradient (i := i)
  simpa [MaxAffine.Family.branch,family] using hi

theorem root_tight_box :
    IntervalBounds.Bounds (318481/1000000) (root 0) (318482/1000000) ∧
      IntervalBounds.Bounds (-1025233/1000000) (root 1) (-1025232/1000000) := by
  have hc : |root 0-AlgebraicSeed.center 0| ≤ radius :=
    (show |root 0-AlgebraicSeed.center 0| ≤ ‖root-AlgebraicSeed.center‖ from norm_le_pi_norm (root-AlgebraicSeed.center) 0).trans root_spec.1
  have hd : |root 1-AlgebraicSeed.center 1| ≤ radius :=
    (show |root 1-AlgebraicSeed.center 1| ≤ ‖root-AlgebraicSeed.center‖ from norm_le_pi_norm (root-AlgebraicSeed.center) 1).trans root_spec.1
  have hca := abs_le.mp hc
  have hda := abs_le.mp hd
  norm_num [AlgebraicSeed.center,radius] at hca hda
  unfold IntervalBounds.Bounds
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith

end BfgsVerification.SeedOrbit
