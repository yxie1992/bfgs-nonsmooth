import BfgsVerification.LBlockConjugacy

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LBlockSplitting
set_option maxHeartbeats 1000000

def shapeZero : State := ![0,0,1,0,0]
def shapeOne : State := ![0,0,0,1,0]
def scaleUnit : State := ![0,0,0,0,1]

theorem coordinate_decomposition (w : State) :
    w=w 0 • pointZero+w 1 • pointOne+w 2 • shapeZero+w 3 • shapeOne+w 4 • scaleUnit := by
  ext i
  fin_cases i <;> simp [pointZero,pointOne,shapeZero,shapeOne,scaleUnit,Matrix.cons_val_succ]

theorem blockForm_of_columns {F : State →L[ℝ] State} {alpha rho : ℝ}
    (h0 : F pointZero=alpha • pointZero) (h1 : F pointOne=alpha • pointOne)
    (h4 : ∀ w, F w 4=rho*w 4) :
    BlockForm F alpha rho (F shapeZero 2) (F shapeOne 2) (F shapeZero 3) (F shapeOne 3)
      ![F shapeZero 0,F shapeZero 1] ![F shapeOne 0,F shapeOne 1]
      ![F scaleUnit 0,F scaleUnit 1] ![F scaleUnit 2,F scaleUnit 3] := by
  intro w
  have he : F w=w 0 • F pointZero+w 1 • F pointOne+w 2 • F shapeZero+
      w 3 • F shapeOne+w 4 • F scaleUnit := by
    conv_lhs => rw [coordinate_decomposition w]
    simp only [map_add,map_smul]
  ext i
  fin_cases i
  all_goals try {exact h4 w}
  all_goals rw [he,h0,h1]
  all_goals simp [pointZero,pointOne,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail]
  all_goals ring

theorem shapeZero_single : shapeZero=Pi.single (2 : Fin 5) 1 := by
  ext i
  fin_cases i <;> norm_num [shapeZero,Matrix.cons_val_succ,Pi.single_apply]
  all_goals split_ifs with h
  all_goals first | rfl | (exfalso; exact absurd h (by decide))
theorem shapeOne_single : shapeOne=Pi.single (3 : Fin 5) 1 := by
  ext i
  fin_cases i <;> norm_num [shapeOne,Matrix.cons_val_succ,Pi.single_apply]
  all_goals split_ifs with h
  all_goals first | rfl | (exfalso; exact absurd h (by decide))
theorem scaleUnit_single : scaleUnit=Pi.single (4 : Fin 5) 1 := by
  ext i
  fin_cases i <;> norm_num [scaleUnit,Matrix.cons_val_succ,Pi.single_apply]
  all_goals split_ifs with h
  all_goals first | rfl | (exfalso; exact absurd h (by decide))

end BfgsVerification.LBlockSplitting
