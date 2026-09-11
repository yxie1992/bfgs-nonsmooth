import BfgsVerification.LBlockBasis

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LBlockSplitting
set_option maxHeartbeats 1000000

def BlockForm (F : State →L[ℝ] State) (alpha rho a b c d : ℝ) (p q h k : Vec 2) : Prop :=
  ∀ w, F w=![alpha*w 0+p 0*w 2+q 0*w 3+h 0*w 4,
    alpha*w 1+p 1*w 2+q 1*w 3+h 1*w 4,
    a*w 2+b*w 3+k 0*w 4,c*w 2+d*w 3+k 1*w 4,rho*w 4]

def shapeEigen (alpha a b : ℝ) (p q : Vec 2) (lambda : ℝ) : State :=
  ![(p 0*b+q 0*(lambda-a))/(lambda-alpha),
    (p 1*b+q 1*(lambda-a))/(lambda-alpha),b,lambda-a,0]

def scaleEigen (alpha rho u v : ℝ) (p q h : Vec 2) : State :=
  ![(p 0*u+q 0*v+h 0)/(rho-alpha),
    (p 1*u+q 1*v+h 1)/(rho-alpha),u,v,1]

theorem shape_eigen {F : State →L[ℝ] State} {alpha rho a b c d lambda : ℝ} {p q h k : Vec 2}
    (hF : BlockForm F alpha rho a b c d p q h k)
    (hl : lambda-alpha≠0) (hroot : (lambda-a)*(lambda-d)=b*c) :
    F (shapeEigen alpha a b p q lambda)=lambda • shapeEigen alpha a b p q lambda := by
  rw [hF]
  ext i
  fin_cases i <;> simp [shapeEigen,Matrix.cons_val_succ]
  · field_simp; ring
  · field_simp; ring
  · ring
  · nlinarith [hroot]

theorem scale_eigen {F : State →L[ℝ] State} {alpha rho a b c d u v : ℝ} {p q h k : Vec 2}
    (hF : BlockForm F alpha rho a b c d p q h k)
    (hr : rho-alpha≠0) (hu : a*u+b*v+k 0=rho*u) (hv : c*u+d*v+k 1=rho*v) :
    F (scaleEigen alpha rho u v p q h)=rho • scaleEigen alpha rho u v p q h := by
  rw [hF]
  ext i
  fin_cases i <;> simp [scaleEigen,Matrix.cons_val_succ]
  · field_simp; ring
  · field_simp; ring
  · exact hu
  · exact hv

theorem scale_shape_exists {rho a b c d : ℝ} (k : Vec 2)
    (hdet : (rho-a)*(rho-d)-b*c≠0) :
    ∃ u v : ℝ, a*u+b*v+k 0=rho*u ∧ c*u+d*v+k 1=rho*v := by
  refine ⟨((rho-d)*k 0+b*k 1)/((rho-a)*(rho-d)-b*c),
    (c*k 0+(rho-a)*k 1)/((rho-a)*(rho-d)-b*c),?_,?_⟩ <;>
    field_simp <;> ring

theorem characteristic_factorization {a b c d ls lu : ℝ} (hs : (ls-a)*(ls-d)=b*c)
    (hu : (lu-a)*(lu-d)=b*c) (hne : ls≠lu) (t : ℝ) :
    (t-a)*(t-d)-b*c=(t-ls)*(t-lu) := by
  have hsum : a+d=ls+lu := by
    have he : (ls-lu)*(ls+lu-a-d)=0 := by nlinarith [hs,hu]
    have hh := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)
    linarith
  nlinarith [hs,congrArg (fun x => x*ls) hsum,congrArg (fun x => x*t) hsum]

end BfgsVerification.LBlockSplitting
