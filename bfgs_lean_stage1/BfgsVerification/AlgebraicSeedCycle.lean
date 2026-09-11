import BfgsVerification.AlgebraicSeedRoot
import BfgsVerification.ObjectiveRun
import BfgsVerification.PlanarBFGSUpdate
import BfgsVerification.EnergyIdentities
/-! Exact full-BFGS three-step closure at the report's uniquely certified algebraic root. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace BfgsVerification.SeedCycle
open AlgebraicSeed PlanarUpdate

def g0 : Vec 2 := ![1,0]
def g1 : Vec 2 := ![-1,-1/8]
def g2 (c d : ℝ) : Vec 2 := ![c,d]
def M1 : Mat 2 := !![129/256,-1/16;-1/16,1]
def update (H : Mat 2) (g h : Vec 2) (α : ℝ) : Mat 2 :=
  inverseBFGS H (bfgsStep H g α) (h-g)

theorem first_step : bfgsStep (1 : Mat 2) g0 1 = ![-1,0] := by
  ext i
  fin_cases i <;> norm_num [bfgsStep,g0,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem first_update : update 1 g0 g1 1 = M1 := by
  unfold update
  rw [first_step]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [update,first_step,inverseBFGS,dot,outer,M1,g0,g1,Matrix.mul_apply,Fin.sum_univ_two]

theorem middle_step (β : ℝ) : bfgsStep M1 g1 β = ![127*β/256,β/16] := by
  ext i
  fin_cases i <;> norm_num [bfgsStep,M1,g1,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  <;> ring

theorem middle_curvature (β c d : ℝ) : dot (g2 c d-g1) (bfgsStep M1 g1 β) = β*(U c d+129)/256 := by
  rw [middle_step β]
  norm_num [g2,g1,dot,U,Fin.sum_univ_two]
  ring


def middleMatrix (β c d : ℝ) : Mat 2 :=
  (16512/(U c d+129)^2) • outer ![-(d+1/8),c+1] ![-(d+1/8),c+1] +
    (β/(256*(U c d+129))) • outer ![127,16] ![127,16]

theorem middle_update {β c d : ℝ} (hβ : β ≠ 0) (hU : U c d+129 ≠ 0) :
    update M1 g1 (g2 c d) β = middleMatrix β c d := by
  let s : Vec 2 := ![127*β/256,β/16]
  have ht : dot (g2 c d-g1) s = β*(U c d+129)/256 := by
    simpa only [middle_step] using middle_curvature β c d
  have htn : dot (g2 c d-g1) s ≠ 0 := by rw [ht]; exact div_ne_zero (mul_ne_zero hβ hU) (by norm_num)
  have henergy : dot (perp s) (M1.mulVec (perp s)) = 16512*(β/256)^2 := by
    norm_num [s,perp,M1,dot,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring
  unfold update
  rw [middle_step β]
  change inverseBFGS M1 s (g2 c d-g1)=_
  rw [inverse_formula M1 s (g2 c d-g1) htn,henergy,ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [middleMatrix,outer,perp,s,g1,g2]
  all_goals field_simp [hβ,hU]
  all_goals ring

def beta (c d : ℝ) : ℝ := 66048*R c d*K c d/(U c d*V c d*(U c d+129))
def gamma (c d : ℝ) : ℝ := V c d*T c d*K c d/(R c d*U c d*Y c d)
def rhoTilde (c d : ℝ) : ℝ := 2064*T c d*K c d/(U c d*(U c d+129)*Y c d)

theorem middle_metric_gradient {c d : ℝ} (hU : U c d ≠ 0) (hV : V c d ≠ 0)
    (hA : U c d+129 ≠ 0) :
    (middleMatrix (beta c d) c d).mulVec (g2 c d) =
      (2064*R c d/(V c d*(U c d+129))) • ![c-1,d] := by
  have hv : dot ![-(d+1/8),c+1] (g2 c d) = -R c d/8 := by
    norm_num [dot,g2,Fin.sum_univ_two,R]
    ring
  have hw : dot ![127,16] (g2 c d)=U c d := by
    norm_num [dot,g2,Fin.sum_univ_two,U]
  simp only [middleMatrix,Matrix.add_mulVec,Matrix.smul_mulVec_assoc,outer_mulVec,hv,hw,smul_smul]
  ext i
  fin_cases i
  all_goals dsimp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  all_goals unfold beta
  all_goals field_simp [hU,hV,hA]
  all_goals unfold U V R K; ring

theorem middle_perpendicular_energy {c d : ℝ} (hU : U c d ≠ 0) (hV : V c d ≠ 0)
    (hA : U c d+129 ≠ 0) :
    dot ![d,1-c] ((middleMatrix (beta c d) c d).mulVec ![d,1-c]) =
      2064*T c d*K c d/(U c d*(U c d+129)) := by
  have hv : dot ![-(d+1/8),c+1] ![d,1-c] = -K c d/8 := by
    norm_num [dot,Fin.sum_univ_two,K]
    ring
  have hw : dot ![127,16] ![d,1-c] = -V c d := by
    norm_num [dot,Fin.sum_univ_two,V]
    ring
  change metricEnergy (middleMatrix (beta c d) c d) ![d,1-c]=_
  simp only [middleMatrix,EnergyIdentities.energy_add_matrix,EnergyIdentities.energy_smul_matrix,
    EnergyIdentities.energy_outer,hv,hw]
  unfold beta
  field_simp [hU,hV,hA]
  unfold U V R K T
  ring


theorem beta_ne_zero {c d : ℝ} (hU : U c d ≠ 0) (hV : V c d ≠ 0)
    (hA : U c d+129 ≠ 0) (hR : R c d ≠ 0) (hK : K c d ≠ 0) : beta c d ≠ 0 := by
  unfold beta
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hR) hK) (mul_ne_zero (mul_ne_zero hU hV) hA)

theorem rhoTilde_ne_zero {c d : ℝ} (hU : U c d ≠ 0) (hA : U c d+129 ≠ 0)
    (hY : Y c d ≠ 0) (hT : T c d ≠ 0) (hK : K c d ≠ 0) : rhoTilde c d ≠ 0 := by
  unfold rhoTilde
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hT) hK) (mul_ne_zero (mul_ne_zero hU hA) hY)

theorem gamma_scale {c d : ℝ} (hU : U c d ≠ 0) (hV : V c d ≠ 0)
    (hA : U c d+129 ≠ 0) (hR : R c d ≠ 0) (hY : Y c d ≠ 0) :
    gamma c d*(2064*R c d/(V c d*(U c d+129))) = rhoTilde c d := by
  unfold gamma rhoTilde
  field_simp [hU,hV,hA,hR,hY]
  ring

theorem last_step_generic {c d : ℝ} (hU : U c d ≠ 0) (hV : V c d ≠ 0)
    (hA : U c d+129 ≠ 0) (hR : R c d ≠ 0) (hY : Y c d ≠ 0) :
    bfgsStep (middleMatrix (beta c d) c d) (g2 c d) (gamma c d) =
      rhoTilde c d • (g0-g2 c d) := by
  simp only [bfgsStep,middle_metric_gradient hU hV hA,smul_smul,neg_mul,gamma_scale hU hV hA hR hY]
  ext i
  fin_cases i <;> norm_num [g0,g2]
  ring

theorem last_curvature_norm (c d : ℝ) : dot (g0-g2 c d) (g0-g2 c d)=Y c d := by
  norm_num [dot,g0,g2,Y,Fin.sum_univ_two]
  ring

theorem last_perpendicular_energy {c d : ℝ} (hU : U c d ≠ 0) (hV : V c d ≠ 0)
    (hA : U c d+129 ≠ 0) (hY : Y c d ≠ 0) :
    dot (perp (g0-g2 c d)) ((middleMatrix (beta c d) c d).mulVec (perp (g0-g2 c d))) =
      rhoTilde c d*dot (g0-g2 c d) (g0-g2 c d) := by
  have he : perp (g0-g2 c d)=![d,1-c] := by ext i; fin_cases i <;> norm_num [perp,g0,g2]
  rw [he,middle_perpendicular_energy hU hV hA,last_curvature_norm]
  unfold rhoTilde
  field_simp [hY]
  ring

theorem last_update_generic {c d : ℝ} (hU : U c d ≠ 0) (hV : V c d ≠ 0)
    (hA : U c d+129 ≠ 0) (hR : R c d ≠ 0) (hY : Y c d ≠ 0)
    (hT : T c d ≠ 0) (hK : K c d ≠ 0) :
    update (middleMatrix (beta c d) c d) (g2 c d) g0 (gamma c d) = rhoTilde c d • (1 : Mat 2) := by
  unfold update
  rw [last_step_generic hU hV hA hR hY]
  apply aligned_identity
  · exact rhoTilde_ne_zero hU hA hY hT hK
  · rwa [last_curvature_norm]
  · exact last_perpendicular_energy hU hV hA hY

theorem generic_closure {c d : ℝ} (hU : U c d ≠ 0) (hV : V c d ≠ 0)
    (hA : U c d+129 ≠ 0) (hR : R c d ≠ 0) (hY : Y c d ≠ 0)
    (hT : T c d ≠ 0) (hK : K c d ≠ 0) :
    update (update M1 g1 (g2 c d) (beta c d)) (g2 c d) g0 (gamma c d) = rhoTilde c d • (1 : Mat 2) := by
  rw [middle_update (beta_ne_zero hU hV hA hR hK) hA]
  exact last_update_generic hU hV hA hR hY hT hK

theorem beta_quarter {c d : ℝ} (hU : U c d ≠ 0) (hV : V c d ≠ 0)
    (hA : U c d+129 ≠ 0) (hP : 264192*R c d*K c d-U c d*V c d*(U c d+129)=0) :
    beta c d=1/4 := by
  unfold beta
  field_simp [hU,hV,hA]
  nlinarith [hP]

theorem gamma_sixteenth {c d : ℝ} (hU : U c d ≠ 0) (hR : R c d ≠ 0)
    (hY : Y c d ≠ 0) (hP : 16*V c d*T c d*K c d-R c d*U c d*Y c d=0) :
    gamma c d=1/16 := by
  unfold gamma
  field_simp [hU,hR,hY]
  nlinarith [hP]

theorem rho_difference {c d : ℝ} (hU : U c d ≠ 0) (hV : V c d ≠ 0)
    (hA : U c d+129 ≠ 0) (hR : R c d ≠ 0) (hY : Y c d ≠ 0) :
    rhoTilde c d-ratio c d = (2064*R c d/(V c d*(U c d+129)))*(gamma c d-1/16) := by
  unfold rhoTilde ratio gamma
  field_simp [hU,hV,hA,hR,hY]
  ring

theorem source_root_polynomials :
    264192*R (root 0) (root 1)*K (root 0) (root 1)-U (root 0) (root 1)*V (root 0) (root 1)*(U (root 0) (root 1)+129)=0 ∧
    16*V (root 0) (root 1)*T (root 0) (root 1)*K (root 0) (root 1)-R (root 0) (root 1)*U (root 0) (root 1)*Y (root 0) (root 1)=0 := by
  constructor
  · have hh := congrArg (fun x : Vec 2 => x 0) root_spec.2
    simpa only [P,Matrix.cons_val_zero,Pi.zero_apply] using hh
  · have hh := congrArg (fun x : Vec 2 => x 1) root_spec.2
    simpa only [P,Matrix.cons_val_one,Matrix.cons_val_fin_one,Pi.zero_apply] using hh

theorem source_parameters : beta (root 0) (root 1)=1/4 ∧ gamma (root 0) (root 1)=1/16 ∧
    rhoTilde (root 0) (root 1)=ratio (root 0) (root 1) := by
  obtain ⟨hU,hV,hR,hK,hT,hY,hA,_,_⟩ := box_denominators_and_ratio root_spec.1
  have hb := beta_quarter hU.ne' hV.ne' hA.ne' source_root_polynomials.1
  have hg := gamma_sixteenth hU.ne' hR.ne' hY.ne' source_root_polynomials.2
  have hr := rho_difference hU.ne' hV.ne' hA.ne' hR.ne' hY.ne'
  rw [hg,sub_self,mul_zero] at hr
  exact ⟨hb,hg,sub_eq_zero.mp hr⟩

theorem source_cycle :
    update (update (update 1 g0 g1 1) g1 (g2 (root 0) (root 1)) (1/4))
      (g2 (root 0) (root 1)) g0 (1/16) = ratio (root 0) (root 1) • (1 : Mat 2) := by
  obtain ⟨hU,hV,hR,hK,hT,hY,hA,_,_⟩ := box_denominators_and_ratio root_spec.1
  rw [first_update,← source_parameters.1,← source_parameters.2.1]
  rw [generic_closure hU.ne' hV.ne' hA.ne' hR.ne' hY.ne' hT.ne' hK.ne',source_parameters.2.2]

end BfgsVerification.SeedCycle
