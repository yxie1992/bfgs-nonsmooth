import BfgsVerification.LNormalizedReturn
import BfgsVerification.StableOrbitTargets
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LBlockSplitting
abbrev State := Vec 5
abbrev Coordinates := Vec 2 × Vec 3

def basisMap (vs vr vu : State) : Coordinates →L[ℝ] State :=
  ({ toFun := fun w => ![
      w.1 0*vs 0+w.1 1*vr 0+w.2 0+w.2 2*vu 0,
      w.1 0*vs 1+w.1 1*vr 1+w.2 1+w.2 2*vu 1,
      w.1 0*vs 2+w.1 1*vr 2+w.2 2*vu 2,
      w.1 0*vs 3+w.1 1*vr 3+w.2 2*vu 3,
      w.1 0*vs 4+w.1 1*vr 4+w.2 2*vu 4]
     map_add' := by intro x y; ext i; fin_cases i <;> simp [Matrix.cons_val_succ] <;> ring
     map_smul' := by intro c x; ext i; fin_cases i <;> simp [Matrix.cons_val_succ] <;> ring
    } : Coordinates →ₗ[ℝ] State).toContinuousLinearMap

def shapeUnstable (a b ls lu : ℝ) (vr : State) (w : State) : ℝ :=
  ((w 3-w 4*vr 3)-(ls-a)/b*(w 2-w 4*vr 2))/(lu-ls)
def shapeStable (a b ls lu : ℝ) (vr : State) (w : State) : ℝ :=
  (w 2-w 4*vr 2)/b-shapeUnstable a b ls lu vr w

def inverseMap (a b ls lu : ℝ) (vs vr vu : State) : State →L[ℝ] Coordinates :=
  ({ toFun := fun w =>
      (![shapeStable a b ls lu vr w,w 4],
       ![w 0-shapeStable a b ls lu vr w*vs 0-w 4*vr 0-shapeUnstable a b ls lu vr w*vu 0,
         w 1-shapeStable a b ls lu vr w*vs 1-w 4*vr 1-shapeUnstable a b ls lu vr w*vu 1,
         shapeUnstable a b ls lu vr w])
     map_add' := by intro x y; apply Prod.ext <;> ext i <;> fin_cases i <;>
       simp [shapeStable,shapeUnstable,Matrix.cons_val_succ] <;> ring
     map_smul' := by intro c x; apply Prod.ext <;> ext i <;> fin_cases i <;>
       simp [shapeStable,shapeUnstable,Matrix.cons_val_succ] <;> ring
    } : State →ₗ[ℝ] Coordinates).toContinuousLinearMap

theorem inverse_basis {a b ls lu : ℝ} {vs vr vu : State} (hb : b≠0) (hls : lu-ls≠0)
    (hs2 : vs 2=b) (hs3 : vs 3=ls-a) (hs4 : vs 4=0)
    (hu2 : vu 2=b) (hu3 : vu 3=lu-a) (hu4 : vu 4=0) (hr4 : vr 4=1) :
    Function.LeftInverse (inverseMap a b ls lu vs vr vu) (basisMap vs vr vu) := by
  intro w
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [inverseMap,basisMap,shapeStable,shapeUnstable,Matrix.cons_val_succ,
      hs2,hs3,hs4,hu2,hu3,hu4,hr4] <;> field_simp <;> ring

theorem basis_inverse {a b ls lu : ℝ} {vs vr vu : State} (hb : b≠0) (hls : lu-ls≠0)
    (hs2 : vs 2=b) (hs3 : vs 3=ls-a) (hs4 : vs 4=0)
    (hu2 : vu 2=b) (hu3 : vu 3=lu-a) (hu4 : vu 4=0) (hr4 : vr 4=1) :
    Function.RightInverse (inverseMap a b ls lu vs vr vu) (basisMap vs vr vu) := by
  intro w
  ext i
  fin_cases i <;>
    simp [inverseMap,basisMap,shapeStable,shapeUnstable,Matrix.cons_val_succ,
      hs2,hs3,hs4,hu2,hu3,hu4,hr4] <;> field_simp <;> ring

def basisEquiv {a b ls lu : ℝ} {vs vr vu : State} (hb : b≠0) (hls : lu-ls≠0)
    (hs2 : vs 2=b) (hs3 : vs 3=ls-a) (hs4 : vs 4=0)
    (hu2 : vu 2=b) (hu3 : vu 3=lu-a) (hu4 : vu 4=0) (hr4 : vr 4=1) :
    Coordinates ≃L[ℝ] State :=
  ContinuousLinearEquiv.equivOfInverse (basisMap vs vr vu) (inverseMap a b ls lu vs vr vu)
    (inverse_basis hb hls hs2 hs3 hs4 hu2 hu3 hu4 hr4)
    (basis_inverse hb hls hs2 hs3 hs4 hu2 hu3 hu4 hr4)

end BfgsVerification.LBlockSplitting
