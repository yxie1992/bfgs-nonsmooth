import BfgsVerification.LBlockEigen
import BfgsVerification.LDiagonal

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LBlockSplitting
set_option maxHeartbeats 1000000

def pointZero : State := ![1,0,0,0,0]
def pointOne : State := ![0,1,0,0,0]

theorem block_point_zero {F : State →L[ℝ] State} {alpha rho a b c d : ℝ} {p q h k : Vec 2}
    (hF : BlockForm F alpha rho a b c d p q h k) : F pointZero=alpha • pointZero := by
  rw [hF]; ext i; fin_cases i <;> simp [pointZero,Matrix.cons_val_succ]
theorem block_point_one {F : State →L[ℝ] State} {alpha rho a b c d : ℝ} {p q h k : Vec 2}
    (hF : BlockForm F alpha rho a b c d p q h k) : F pointOne=alpha • pointOne := by
  rw [hF]; ext i; fin_cases i <;> simp [pointOne,Matrix.cons_val_succ]

theorem basisMap_eq (vs vr vu : State) (w : Coordinates) :
    basisMap vs vr vu w=w.1 0 • vs+w.1 1 • vr+w.2 0 • pointZero+w.2 1 • pointOne+w.2 2 • vu := by
  ext i
  fin_cases i <;> simp [basisMap,pointZero,pointOne,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail]

theorem basisMap_scale {vs vr vu : State} (hs : vs 4=0) (hr : vr 4=1) (hu : vu 4=0)
    (w : Coordinates) : basisMap vs vr vu w 4=w.1 1 := by
  simp [basisMap,Matrix.cons_val_succ,hs,hr,hu]

theorem basis_diagonal {F : State →L[ℝ] State} {alpha rho ls lu : ℝ} {vs vr vu : State}
    (hs : F vs=ls • vs) (hr : F vr=rho • vr) (hu : F vu=lu • vu)
    (h0 : F pointZero=alpha • pointZero) (h1 : F pointOne=alpha • pointOne)
    (w : Coordinates) :
    F (basisMap vs vr vu w)=basisMap vs vr vu
      (diagonalMap ![ls,rho] w.1,diagonalMap ![alpha,alpha,lu] w.2) := by
  rw [basisMap_eq,basisMap_eq]
  simp only [map_add,map_smul,hs,hr,hu,h0,h1]
  change w.1 0 • (ls • vs)+w.1 1 • (rho • vr)+w.2 0 • (alpha • pointZero)+
    w.2 1 • (alpha • pointOne)+w.2 2 • (lu • vu)=
    (ls*w.1 0) • vs+(rho*w.1 1) • vr+(alpha*w.2 0) • pointZero+
      (alpha*w.2 1) • pointOne+(lu*w.2 2) • vu
  module

/-- Explicit real diagonalization of L's upper block derivative. The final
physical-scale coordinate is exactly the second stable coordinate. -/
theorem block_splitting {F : State →L[ℝ] State} {rho a b c d ls lu : ℝ} {p q h k : Vec 2}
    (hF : BlockForm F rho⁻¹ rho a b c d p q h k)
    (hr0 : 0<rho) (hr1 : rho<1) (hs0 : 0<ls) (hsr : ls<rho)
    (hu1 : 1<lu) (hua : lu<rho⁻¹) (hb : b≠0)
    (hsroot : (ls-a)*(ls-d)=b*c) (huroot : (lu-a)*(lu-d)=b*c) :
    ∃ E : Coordinates ≃L[ℝ] State,
      (∀ w, E w 4=w.1 1) ∧
      ∃ A : Vec 2 →L[ℝ] Vec 2, ∃ L : Vec 3 ≃L[ℝ] Vec 3,
        ‖A‖<1 ∧ ‖L.symm.toContinuousLinearMap‖<1 ∧
        F.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (A.prodMap L.toContinuousLinearMap) := by
  have hra : rho<rho⁻¹ := lt_trans hr1 ((one_lt_inv₀ hr0).mpr hr1)
  have hs1 : ls<1 := hsr.trans hr1
  have hslu : ls<lu := hs1.trans hu1
  have hsrho : ls≠rho := ne_of_lt hsr
  have hrulu : rho≠lu := ne_of_lt (hr1.trans hu1)
  have hdet : (rho-a)*(rho-d)-b*c≠0 := by
    rw [characteristic_factorization hsroot huroot (ne_of_lt hslu)]
    exact mul_ne_zero (sub_ne_zero.mpr hsrho.symm) (sub_ne_zero.mpr hrulu)
  obtain ⟨u,v,hue,hve⟩ := scale_shape_exists k hdet
  let vs := shapeEigen rho⁻¹ a b p q ls
  let vu := shapeEigen rho⁻¹ a b p q lu
  let vr := scaleEigen rho⁻¹ rho u v p q h
  let E := basisEquiv (vs:=vs) (vu:=vu) (vr:=vr) hb
    (sub_ne_zero.mpr (ne_of_gt hslu)) rfl rfl rfl rfl rfl rfl rfl
  let A := diagonalMap ![ls,rho]
  have hd : ∀ i, (![rho⁻¹,rho⁻¹,lu] : Vec 3) i≠0 := by
    intro i; fin_cases i <;> simp [hr0.ne', (lt_trans zero_lt_one hu1).ne']
  let L := diagonalEquiv ![rho⁻¹,rho⁻¹,lu] hd
  refine ⟨E,?_,A,L,stable_diagonal_contraction hs0 hs1 hr0 hr1,
    unstable_diagonal_inverse_contraction hr0 hr1 hu1 hd,?_⟩
  · intro w
    exact basisMap_scale (vs:=vs) (vr:=vr) (vu:=vu) rfl rfl rfl w
  · apply ContinuousLinearMap.ext
    intro w
    exact basis_diagonal
      (shape_eigen hF (sub_ne_zero.mpr (ne_of_lt (hsr.trans hra))) hsroot)
      (scale_eigen hF (sub_ne_zero.mpr (ne_of_lt hra)) hue hve)
      (shape_eigen hF (sub_ne_zero.mpr (ne_of_lt hua)) huroot)
      (block_point_zero hF) (block_point_one hF) w

end BfgsVerification.LBlockSplitting
