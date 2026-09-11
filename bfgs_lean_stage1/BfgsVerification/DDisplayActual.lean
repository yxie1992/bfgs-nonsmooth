import BfgsVerification.DDisplayRaw
import BfgsVerification.DEmbeddingBounds

noncomputable section
open Matrix
namespace BfgsVerification.DDisplayActual
open SeedOrbit SeedCycle IntervalBounds
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def basePoint : Fin 4 → Vec 2 :=
  ![point seedC seedD seedRatio 0, point seedC seedD seedRatio 1,
    point seedC seedD seedRatio 2, trial seedC seedD seedRatio 2 (length 2)]

def baseValue (j : Fin 3) : ℝ :=
  objective seedC seedD (point seedC seedD seedRatio j)

def actualStep (j : Fin 3) (a : ℝ) : Vec 2 :=
  bfgsStep (metric seedC seedD j) (gradient seedC seedD j) a

def trialValue (q : Fin 9) : ℝ :=
  objective seedC seedD (point seedC seedD seedRatio (trialPhase q)+
    trialLength q • actualStep (trialPhase q) 1)

def armijoRatio (j : Fin 3) : ℝ :=
  (baseValue j-objective seedC seedD
    (point seedC seedD seedRatio j+actualStep j (length j)))/
      (-dot (gradient seedC seedD j) (actualStep j (length j)))

def wolfeRatio (j : Fin 3) : ℝ :=
  dot (gradient seedC seedD (nextPhase j)) (actualStep j (length j))/
    dot (gradient seedC seedD j) (actualStep j (length j))

def values : Fin 33 → ℝ :=
  ![seedRatio,
    basePoint 0 0,
    basePoint 0 1,
    basePoint 1 0,
    basePoint 1 1,
    basePoint 2 0,
    basePoint 2 1,
    basePoint 3 0,
    basePoint 3 1,
    trialValue 0,
    trialValue 1,
    trialValue 2,
    trialValue 3,
    trialValue 4,
    trialValue 5,
    trialValue 6,
    trialValue 7,
    trialValue 8,
    baseValue 0,
    baseValue 1,
    baseValue 2,
    armijoRatio 0,
    wolfeRatio 0,
    armijoRatio 1,
    wolfeRatio 1,
    armijoRatio 2,
    wolfeRatio 2,
    DScalarRamp.center (2 : ℝ),
    DScalarRamp.lowerLength (2 : ℝ),
    DScalarRamp.upperLength (2 : ℝ),
    DScalarRamp.center DEmbedding.bStar,
    DScalarRamp.lowerLength DEmbedding.bStar,
    DScalarRamp.upperLength DEmbedding.bStar]

theorem baseValue_eq (j : Fin 3) :
    baseValue j=dot (gradient seedC seedD j) (point seedC seedD seedRatio j) :=
  objective_of_active (source_base_certificate j).active

theorem actualStep_eq (j : Fin 3) (a : ℝ) :
    actualStep j a=a • direction seedC seedD seedRatio j := source_direction j a

theorem trialValue_eq (q : Fin 9) :
    trialValue q=dot (gradient seedC seedD (trialActive q))
      (trial seedC seedD seedRatio (trialPhase q) (trialLength q)) := by
  rw [trialValue,actualStep_eq,one_smul]
  exact objective_of_active (source_trial_certificate q).active

theorem acceptedValue_eq (j : Fin 3) :
    objective seedC seedD (point seedC seedD seedRatio j+actualStep j (length j))=
      dot (gradient seedC seedD (nextPhase j)) (basePoint j.succ) := by
  rw [actualStep_eq]
  change objective seedC seedD (trial seedC seedD seedRatio j (length j))=_
  rw [objective_of_active (source_accepted_certificate j).active]
  fin_cases j
  · change dot (SeedOrbit.gradient seedC seedD (nextPhase 0)) (trial seedC seedD seedRatio 0 (length 0))=_
    rw [phase_zero_step]; rfl
  · change dot (SeedOrbit.gradient seedC seedD (nextPhase 1)) (trial seedC seedD seedRatio 1 (length 1))=_
    rw [phase_one_step]; rfl
  · rfl

theorem basePoint_last : basePoint 3=seedRatio • point seedC seedD seedRatio 0 :=
  source_phase_two_step

theorem value_0_eq_raw : values 0=DDisplayRaw.values seedC seedD 0 := by
  change seedRatio = (((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_1_eq_raw : values 1=DDisplayRaw.values seedC seedD 1 := by
  change basePoint 0 0 = (((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_2_eq_raw : values 2=DDisplayRaw.values seedC seedD 2 := by
  change basePoint 0 1 = ((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_3_eq_raw : values 3=DDisplayRaw.values seedC seedD 3 := by
  change basePoint 1 0 = ((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(1 : ℝ))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_4_eq_raw : values 4=DDisplayRaw.values seedC seedD 4 := by
  change basePoint 1 1 = ((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_5_eq_raw : values 5=DDisplayRaw.values seedC seedD 5 := by
  change basePoint 2 0 = ((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(897/1024 : ℝ))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_6_eq_raw : values 6=DDisplayRaw.values seedC seedD 6 := by
  change basePoint 2 1 = (((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+(1/64 : ℝ))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_7_eq_raw : values 7=DDisplayRaw.values seedC seedD 7 := by
  change basePoint 3 0 = ((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*(((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_8_eq_raw : values 8=DDisplayRaw.values seedC seedD 8 := by
  change basePoint 3 1 = ((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_9_eq_raw : values 9=DDisplayRaw.values seedC seedD 9 := by
  change trialValue 0 = (((-1 : ℝ)*((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*(((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+((1 : ℝ)*(0 : ℝ)))))
  rw [trialValue_eq]
  change dot (SeedOrbit.gradient seedC seedD 1) (trial seedC seedD seedRatio 0 1) = _
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_10_eq_raw : values 10=DDisplayRaw.values seedC seedD 10 := by
  change trialValue 1 = (((1 : ℝ)*(((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*(((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))
  rw [trialValue_eq]
  change dot (SeedOrbit.gradient seedC seedD 0) (trial seedC seedD seedRatio 1 1) = _
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_11_eq_raw : values 11=DDisplayRaw.values seedC seedD 11 := by
  change trialValue 2 = (((1 : ℝ)*(((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*(((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))
  rw [trialValue_eq]
  change dot (SeedOrbit.gradient seedC seedD 0) (trial seedC seedD seedRatio 1 (1/2)) = _
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_12_eq_raw : values 12=DDisplayRaw.values seedC seedD 12 := by
  change trialValue 3 = ((seedC*(((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(seedD*(((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))
  rw [trialValue_eq]
  change dot (SeedOrbit.gradient seedC seedD 2) (trial seedC seedD seedRatio 1 (1/4)) = _
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_13_eq_raw : values 13=DDisplayRaw.values seedC seedD 13 := by
  change trialValue 4 = (((1 : ℝ)*(((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*((1 : ℝ)-seedC)))))+((0 : ℝ)*((((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*seedD)))))
  rw [trialValue_eq]
  change dot (SeedOrbit.gradient seedC seedD 0) (trial seedC seedD seedRatio 2 1) = _
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_14_eq_raw : values 14=DDisplayRaw.values seedC seedD 14 := by
  change trialValue 5 = (((1 : ℝ)*(((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*((1 : ℝ)-seedC)))))+((0 : ℝ)*((((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*seedD)))))
  rw [trialValue_eq]
  change dot (SeedOrbit.gradient seedC seedD 0) (trial seedC seedD seedRatio 2 (1/2)) = _
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_15_eq_raw : values 15=DDisplayRaw.values seedC seedD 15 := by
  change trialValue 6 = (((1 : ℝ)*(((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*((1 : ℝ)-seedC)))))+((0 : ℝ)*((((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*seedD)))))
  rw [trialValue_eq]
  change dot (SeedOrbit.gradient seedC seedD 0) (trial seedC seedD seedRatio 2 (1/4)) = _
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_16_eq_raw : values 16=DDisplayRaw.values seedC seedD 16 := by
  change trialValue 7 = (((1 : ℝ)*(((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*((1 : ℝ)-seedC)))))+((0 : ℝ)*((((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*seedD)))))
  rw [trialValue_eq]
  change dot (SeedOrbit.gradient seedC seedD 0) (trial seedC seedD seedRatio 2 (1/8)) = _
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_17_eq_raw : values 17=DDisplayRaw.values seedC seedD 17 := by
  change trialValue 8 = (((1 : ℝ)*(((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*((1 : ℝ)-seedC)))))+((0 : ℝ)*((((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*seedD)))))
  rw [trialValue_eq]
  change dot (SeedOrbit.gradient seedC seedD 0) (trial seedC seedD seedRatio 2 (1/16)) = _
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_18_eq_raw : values 18=DDisplayRaw.values seedC seedD 18 := by
  change baseValue 0 = (((1 : ℝ)*(((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹))+((0 : ℝ)*((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_19_eq_raw : values 19=DDisplayRaw.values seedC seedD 19 := by
  change baseValue 1 = (((-1 : ℝ)*((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_20_eq_raw : values 20=DDisplayRaw.values seedC seedD 20 := by
  change baseValue 2 = ((seedC*((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(897/1024 : ℝ)))+(seedD*(((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+(1/64 : ℝ))))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_21_eq_raw : values 21=DDisplayRaw.values seedC seedD 21 := by
  change armijoRatio 0 = (((((1 : ℝ)*(((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹))+((0 : ℝ)*((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)))-(((-1 : ℝ)*((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹))))*((-(((1 : ℝ)*((1 : ℝ)*(-1 : ℝ)))+((0 : ℝ)*((1 : ℝ)*(0 : ℝ))))))⁻¹)
  rw [armijoRatio,baseValue_eq,acceptedValue_eq]
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_22_eq_raw : values 22=DDisplayRaw.values seedC seedD 22 := by
  change wolfeRatio 0 = ((-(((-1 : ℝ)*((1 : ℝ)*(-1 : ℝ)))+((-1/8 : ℝ)*((1 : ℝ)*(0 : ℝ)))))*((-(((1 : ℝ)*((1 : ℝ)*(-1 : ℝ)))+((0 : ℝ)*((1 : ℝ)*(0 : ℝ))))))⁻¹)
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_23_eq_raw : values 23=DDisplayRaw.values seedC seedD 23 := by
  change armijoRatio 1 = (((((-1 : ℝ)*((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)))-((seedC*((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(897/1024 : ℝ)))+(seedD*(((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+(1/64 : ℝ)))))*((-(((-1 : ℝ)*((1/4 : ℝ)*(127/256 : ℝ)))+((-1/8 : ℝ)*((1/4 : ℝ)*(1/16 : ℝ))))))⁻¹)
  rw [armijoRatio,baseValue_eq,acceptedValue_eq]
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_24_eq_raw : values 24=DDisplayRaw.values seedC seedD 24 := by
  change wolfeRatio 1 = ((-((seedC*((1/4 : ℝ)*(127/256 : ℝ)))+(seedD*((1/4 : ℝ)*(1/16 : ℝ)))))*((-(((-1 : ℝ)*((1/4 : ℝ)*(127/256 : ℝ)))+((-1/8 : ℝ)*((1/4 : ℝ)*(1/16 : ℝ))))))⁻¹)
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_25_eq_raw : values 25=DDisplayRaw.values seedC seedD 25 := by
  change armijoRatio 2 = ((((seedC*((((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)-(897/1024 : ℝ)))+(seedD*(((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)+(1/64 : ℝ))))-(((1 : ℝ)*((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*(((897/1024 : ℝ)-((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((1 : ℝ)-seedC)))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)))+((0 : ℝ)*((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*((((((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)*seedD)-(1/64 : ℝ))*(((1 : ℝ)-(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹)))⁻¹)))))*((-((seedC*((1/16 : ℝ)*(((16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*((1 : ℝ)-seedC))))+(seedD*((1/16 : ℝ)*(((-16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*seedD))))))⁻¹)
  rw [armijoRatio,baseValue_eq,acceptedValue_eq]
  change (dot (gradient seedC seedD 2) (point seedC seedD seedRatio 2) -
    dot (gradient seedC seedD 0) (basePoint 3)) /
      (-dot (gradient seedC seedD 2) (actualStep 2 (length 2))) = _
  rw [basePoint_last]
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_26_eq_raw : values 26=DDisplayRaw.values seedC seedD 26 := by
  change wolfeRatio 2 = ((-(((1 : ℝ)*((1/16 : ℝ)*(((16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*((1 : ℝ)-seedC))))+((0 : ℝ)*((1/16 : ℝ)*(((-16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*seedD)))))*((-((seedC*((1/16 : ℝ)*(((16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*((1 : ℝ)-seedC))))+(seedD*((1/16 : ℝ)*(((-16 : ℝ)*(((129 : ℝ)*(seedC-((8 : ℝ)*seedD)))*((((((16 : ℝ)*seedC)-((127 : ℝ)*seedD))-(16 : ℝ))*((((127 : ℝ)*seedC)+((16 : ℝ)*seedD))+(129 : ℝ))))⁻¹))*seedD))))))⁻¹)
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_27_eq_raw : values 27=DDisplayRaw.values seedC seedD 27 := by
  change DScalarRamp.center (2 : ℝ) = ((((256 : ℝ)*(2 : ℝ))-(273 : ℝ))*(((255 : ℝ)*(2 : ℝ)))⁻¹)
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_28_eq_raw : values 28=DDisplayRaw.values seedC seedD 28 := by
  change DScalarRamp.lowerLength (2 : ℝ) = ((273/272 : ℝ)-((383/34816 : ℝ)*(2 : ℝ)))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_29_eq_raw : values 29=DDisplayRaw.values seedC seedD 29 := by
  change DScalarRamp.upperLength (2 : ℝ) = (((32513/2176 : ℝ)*(2 : ℝ))-(273/17 : ℝ))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_30_eq_raw : values 30=DDisplayRaw.values seedC seedD 30 := by
  change DScalarRamp.center DEmbedding.bStar = ((((256 : ℝ)*(((2 : ℝ)*seedC)-((32 : ℝ)*seedD)))-(273 : ℝ))*(((255 : ℝ)*(((2 : ℝ)*seedC)-((32 : ℝ)*seedD))))⁻¹)
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_31_eq_raw : values 31=DDisplayRaw.values seedC seedD 31 := by
  change DScalarRamp.lowerLength DEmbedding.bStar = ((273/272 : ℝ)-((383/34816 : ℝ)*(((2 : ℝ)*seedC)-((32 : ℝ)*seedD))))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem value_32_eq_raw : values 32=DDisplayRaw.values seedC seedD 32 := by
  change DScalarRamp.upperLength DEmbedding.bStar = (((32513/2176 : ℝ)*(((2 : ℝ)*seedC)-((32 : ℝ)*seedD)))-(273/17 : ℝ))
  have hb : DEmbedding.bStar≠0 := (lt_trans (by norm_num : (0 : ℝ)<33) DEmbedding.bStar_bounds.1).ne'
  have hcenter := DScalarRamp.center_formula hb
  have hlo := DScalarRamp.lowerLength_formula hb
  have hhi := DScalarRamp.upperLength_formula hb
  have hcenter2 := DScalarRamp.center_formula (b := (2 : ℝ)) (by norm_num)
  have hlo2 := DScalarRamp.lowerLength_formula (b := (2 : ℝ)) (by norm_num)
  have hhi2 := DScalarRamp.upperLength_formula (b := (2 : ℝ)) (by norm_num)
  try simp only [baseValue_eq,trialValue_eq,armijoRatio,wolfeRatio,acceptedValue_eq,
    actualStep_eq,basePoint_last,hcenter,hlo,hhi,hcenter2,hlo2,hhi2]
  all_goals try simp only [basePoint,point,trial,initialPoint,SeedOrbit.direction,SeedOrbit.gradient,
    trialPhase,trialLength,trialActive,nextPhase,length,g0,g1,g2,DEmbedding.bStar,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.vecHead,Matrix.vecTail,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,dot,Fin.sum_univ_two,seedRatio,AlgebraicSeed.ratio,
    AlgebraicSeed.R,AlgebraicSeed.V,AlgebraicSeed.U]
  all_goals try simp only [div_eq_mul_inv,neg_mul,inv_neg]
  all_goals norm_num
  all_goals ring
  all_goals simp

theorem values_eq_raw (i : Fin 33) : values i=DDisplayRaw.values seedC seedD i := by
  fin_cases i
  · exact value_0_eq_raw
  · exact value_1_eq_raw
  · exact value_2_eq_raw
  · exact value_3_eq_raw
  · exact value_4_eq_raw
  · exact value_5_eq_raw
  · exact value_6_eq_raw
  · exact value_7_eq_raw
  · exact value_8_eq_raw
  · exact value_9_eq_raw
  · exact value_10_eq_raw
  · exact value_11_eq_raw
  · exact value_12_eq_raw
  · exact value_13_eq_raw
  · exact value_14_eq_raw
  · exact value_15_eq_raw
  · exact value_16_eq_raw
  · exact value_17_eq_raw
  · exact value_18_eq_raw
  · exact value_19_eq_raw
  · exact value_20_eq_raw
  · exact value_21_eq_raw
  · exact value_22_eq_raw
  · exact value_23_eq_raw
  · exact value_24_eq_raw
  · exact value_25_eq_raw
  · exact value_26_eq_raw
  · exact value_27_eq_raw
  · exact value_28_eq_raw
  · exact value_29_eq_raw
  · exact value_30_eq_raw
  · exact value_31_eq_raw
  · exact value_32_eq_raw

end BfgsVerification.DDisplayActual
