import BfgsVerification.LReturnJets

noncomputable section
open scoped BigOperators Topology
open Matrix
namespace BfgsVerification.LShapeDerivative
open SeedCycle SeedOrbit LNormalizedReturn
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def center : Vec 2 := ![0,1]
def inputMatrix (x : Vec 2) : Mat 2 := !![1,x 0;x 0,x 1]
def matrixIter (c d : ℝ) (x : Vec 2) : ℕ → Mat 2
  | 0 => inputMatrix x
  | k+1 => SeedCycle.update (matrixIter c d x k) (SeedOrbit.gradient c d (phase k))
      (SeedOrbit.gradient c d (nextPhase (phase k))) (length (phase k))
def shapeMap (c d : ℝ) (x : Vec 2) : Vec 2 :=
  ![(matrixIter c d x 3) 0 1/(matrixIter c d x 3) 0 0,
    (matrixIter c d x 3) 1 1/(matrixIter c d x 3) 0 0]
def boundary (x : Vec 2) : State := ![seed 0,seed 1,x 0,x 1,0]
def shapeLift : Vec 2 →L[ℝ] State :=
  ContinuousLinearMap.pi ![0,0,ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1,0]

theorem boundary_scale (x : Vec 2) : scale (boundary x)=0 := rfl
theorem boundary_shape (x : Vec 2) : shape (boundary x)=inputMatrix x := rfl
theorem boundary_center : boundary center=seed := by ext i; fin_cases i <;> rfl

theorem matrixIter_eq_internal (μ : ℝ) (x : Vec 2) (k : ℕ) :
    matrixIter seedC seedD x k=(internal μ (boundary x) k).2 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [matrixIter,internal,boundary_scale,substep_zero,← ih]

theorem matrixIter_center (μ : ℝ) (k : ℕ) :
    matrixIter seedC seedD center k=(internal μ seed k).2 := by
  rw [matrixIter_eq_internal μ,boundary_center]

theorem shapeMap_eq_returnMap (μ : ℝ) (x : Vec 2) :
    shapeMap seedC seedD x= ![(returnMap μ (boundary x)) 2,(returnMap μ (boundary x)) 3] := by
  simp only [shapeMap,matrixIter_eq_internal μ,returnMap,returnFactor,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.cons_val_fin_one]
  rfl

def curve (j : Fin 2) (t : ℝ) : Vec 2 := center+t • (Pi.single j 1 : Vec 2)

def initialJet (j : Fin 2) : LReturnJets.JetMat :=
  !![LReturnJets.constant 1,⟨0,if j=0 then 1 else 0⟩;
    ⟨0,if j=0 then 1 else 0⟩,⟨1,if j=1 then 1 else 0⟩]
def stepJet (H : LReturnJets.JetMat) (g : Vec 2) (a : ℝ) : LReturnJets.JetVec :=
  LReturnJets.vecScale (LReturnJets.constant (-a)) (LReturnJets.mulVec H (LReturnJets.vecConstant g))
def updateJet (H : LReturnJets.JetMat) (g h : Vec 2) (a : ℝ) : LReturnJets.JetMat :=
  LReturnJets.inverseUpdate H (stepJet H g a) (LReturnJets.vecConstant (h-g))
def jetIter (c d : ℝ) (j : Fin 2) : ℕ → LReturnJets.JetMat
  | 0 => initialJet j
  | k+1 => updateJet (jetIter c d j k) (SeedOrbit.gradient c d (phase k))
      (SeedOrbit.gradient c d (nextPhase (phase k))) (length (phase k))
def shapeJet (c d : ℝ) (j : Fin 2) : LReturnJets.JetVec :=
  ![LReturnJets.div (jetIter c d j 3 0 1) (jetIter c d j 3 0 0),
    LReturnJets.div (jetIter c d j 3 1 1) (jetIter c d j 3 0 0)]
def jacobian (c d : ℝ) : Mat 2 := fun i j => (shapeJet c d j i).tangent

@[simp] theorem curve_zero (j : Fin 2) : curve j 0=center := by simp [curve]

theorem models_initial (j : Fin 2) : LReturnJets.ModelsMat (fun t => inputMatrix (curve j t)) (initialJet j) := by
  intro i k
  fin_cases j <;> fin_cases i <;> fin_cases k
  all_goals constructor
  all_goals try simp [inputMatrix,curve,center,initialJet,LReturnJets.constant]
  all_goals try dsimp [inputMatrix,curve,center,initialJet,LReturnJets.constant]
  all_goals try simp only [Pi.single_apply,Fin.isValue,ite_true,ite_false,mul_one,mul_zero,zero_add,add_zero]
  all_goals first | exact hasDerivAt_const 0 _ | exact hasDerivAt_id 0 | simpa using (hasDerivAt_id (0 : ℝ)).const_add 1

theorem models_step {H : ℝ → Mat 2} {jH : LReturnJets.JetMat} (hH : LReturnJets.ModelsMat H jH)
    (g : Vec 2) (a : ℝ) : LReturnJets.ModelsVec (fun t => bfgsStep (H t) g a) (stepJet jH g a) :=
  LReturnJets.ModelsVec.scale (LReturnJets.models_constant (-a)) (hH.mulVec (LReturnJets.models_vecConstant g))

theorem models_update {H : ℝ → Mat 2} {jH : LReturnJets.JetMat} (hH : LReturnJets.ModelsMat H jH)
    (g h : Vec 2) (a : ℝ) (ht : dot (h-g) (bfgsStep (H 0) g a) ≠ 0) :
    LReturnJets.ModelsMat (fun t => SeedCycle.update (H t) g h a) (updateJet jH g h a) :=
  LReturnJets.models_inverseUpdate hH (models_step hH g a) (LReturnJets.models_vecConstant (h-g)) ht

theorem models_iter (j : Fin 2) (k : ℕ) (hk : k ≤ 3) :
    LReturnJets.ModelsMat (fun t => matrixIter seedC seedD (curve j t) k) (jetIter seedC seedD j k) := by
  induction k with
  | zero => exact models_initial j
  | succ k ih =>
    apply models_update (ih (by omega))
    rw [curve_zero,matrixIter_center 0]
    have he : phase k=⟨k,by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [he]
    have hm : (internal 0 seed k).2=metric seedC seedD ⟨k,by omega⟩ :=
      congrArg Prod.snd (internal_seed_phase 0 ⟨k,by omega⟩)
    rw [hm]
    exact (seed_curvature_positive ⟨k,by omega⟩).ne'

theorem models_shape (j : Fin 2) :
    LReturnJets.ModelsVec (fun t => shapeMap seedC seedD (curve j t)) (shapeJet seedC seedD j) := by
  have h := models_iter j 3 le_rfl
  have hr : (jetIter seedC seedD j 3 0 0).value ≠ 0 := by
    rw [← (h 0 0).1]
    change matrixIter seedC seedD (curve j 0) 3 0 0 ≠ 0
    rw [curve_zero,matrixIter_center 0,internal_seed_three]
    simpa using source_ratio_pos_lt_one.1.ne'
  intro i
  fin_cases i
  · exact (h 0 1).div (h 0 0) hr
  · exact (h 1 1).div (h 0 0) hr

def shapeCoord : Fin 2 → Fin 5 := ![2,3]

theorem shapeLift_single (j : Fin 2) :
    shapeLift (Pi.single j 1 : Vec 2)=(Pi.single (shapeCoord j) 1 : State) := by
  ext i
  fin_cases j <;> fin_cases i <;> simp [shapeLift,shapeCoord,Pi.single_apply,Matrix.cons_val]

theorem boundary_curve (j : Fin 2) (t : ℝ) :
    boundary (curve j t)=seed+t • shapeLift (Pi.single j 1 : Vec 2) := by
  ext i
  fin_cases i <;> simp [boundary,curve,center,shapeLift,seed,LNormalizedReturn.seed,
    Matrix.cons_val_succ]

theorem boundary_curve_hasDerivAt (j : Fin 2) :
    HasDerivAt (fun t => boundary (curve j t)) (shapeLift (Pi.single j 1 : Vec 2)) 0 := by
  simp_rw [boundary_curve]
  simpa using (hasDerivAt_const (0 : ℝ) seed).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (shapeLift (Pi.single j 1 : Vec 2)))

/-- The finite forward differentiation recurrence computes the actual middle
block of the derivative of the five-dimensional return map. -/
theorem actual_shape_derivative (μ : ℝ) (i j : Fin 2) :
    (fderiv ℝ (returnMap μ) seed (shapeLift (Pi.single j 1 : Vec 2))) (shapeCoord i)=
      jacobian seedC seedD i j := by
  have hm := (analytic_returnMap_seed μ).differentiableAt.hasFDerivAt
  have hc := (boundary_curve_hasDerivAt j)
  have hcomp : HasDerivAt (fun t => returnMap μ (boundary (curve j t)))
      (fderiv ℝ (returnMap μ) seed (shapeLift (Pi.single j 1 : Vec 2))) 0 := by
    apply hm.comp_hasDerivAt_of_eq 0 hc
    rw [curve_zero,boundary_center]
  have hp := (hasDerivAt_pi.mp hcomp) (shapeCoord i)
  have hj := (models_shape j i).2
  have he : (fun t => shapeMap seedC seedD (curve j t) i)=
      (fun t => returnMap μ (boundary (curve j t)) (shapeCoord i)) := by
    funext t
    rw [shapeMap_eq_returnMap μ]
    fin_cases i <;> rfl
  rw [he] at hj
  exact hp.unique hj

end BfgsVerification.LShapeDerivative
