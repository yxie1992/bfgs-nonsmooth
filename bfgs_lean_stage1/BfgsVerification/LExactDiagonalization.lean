import BfgsVerification.LBlockConjugacy
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix Polynomial
namespace BfgsVerification.LExactDiagonalization
open LBlockSplitting
theorem exact_block_diagonalization {F : State →L[ℝ] State} {rho a b c d ls lu : ℝ} {p q h k : Vec 2}
    (hF : BlockForm F rho⁻¹ rho a b c d p q h k)
    (hr0 : 0<rho) (hr1 : rho<1) (hs0 : 0<ls) (hsr : ls<rho)
    (hu1 : 1<lu) (hua : lu<rho⁻¹) (hb : b≠0)
    (hsroot : (ls-a)*(ls-d)=b*c) (huroot : (lu-a)*(lu-d)=b*c) :
    ∃ E : Coordinates ≃L[ℝ] State,
      (∀ w, E w 4=w.1 1) ∧
      (∀ w, F (E w)=E (diagonalMap ![ls,rho] w.1,diagonalMap ![rho⁻¹,rho⁻¹,lu] w.2)) := by
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
  refine ⟨E,?_,?_⟩
  · intro w
    exact basisMap_scale (vs:=vs) (vr:=vr) (vu:=vu) rfl rfl rfl w
  · intro w
    exact basis_diagonal
      (shape_eigen hF (sub_ne_zero.mpr (ne_of_lt (hsr.trans hra))) hsroot)
      (scale_eigen hF (sub_ne_zero.mpr (ne_of_lt hra)) hue hve)
      (shape_eigen hF (sub_ne_zero.mpr (ne_of_lt hua)) huroot)
      (block_point_zero hF) (block_point_one hF) w


theorem diagonal_charpoly {n : ℕ} (d : Vec n) :
    (diagonalMap d).toLinearMap.charpoly=∏ i, (X-C (d i)) := by
  rw [← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℝ (Fin n))]
  have he : LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
      (diagonalMap d).toLinearMap=Matrix.diagonal d := by
    ext i j
    simp [LinearMap.toMatrix_apply,diagonalMap_apply,Matrix.diagonal_apply,Pi.single_apply]
  rw [he]
  have hm : Matrix.charmatrix (Matrix.diagonal d)=Matrix.diagonal (fun i => X-C (d i)) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.charmatrix,Matrix.diagonal,hij]
  rw [Matrix.charpoly,hm,Matrix.det_diagonal]

theorem charpoly_of_exact_diagonalization {F : State →L[ℝ] State}
    {ls rho alpha lu : ℝ} (E : Coordinates ≃L[ℝ] State)
    (hE : ∀ w, F (E w)=E (diagonalMap ![ls,rho] w.1,diagonalMap ![alpha,alpha,lu] w.2)) :
    F.toLinearMap.charpoly=(X-C alpha)^2*(X-C ls)*(X-C lu)*(X-C rho) := by
  let D := (diagonalMap ![ls,rho]).toLinearMap.prodMap (diagonalMap ![alpha,alpha,lu]).toLinearMap
  have he : E.toLinearEquiv.conj D=F.toLinearMap := by
    apply LinearMap.ext
    intro w
    have h := hE (E.symm w)
    simpa [LinearEquiv.conj_apply,D] using h.symm
  rw [← he,E.toLinearEquiv.charpoly_conj,LinearMap.charpoly_prodMap]
  rw [diagonal_charpoly,diagonal_charpoly]
  norm_num [Fin.prod_univ_two,Fin.prod_univ_three,Matrix.cons_val,Matrix.cons_val_two]
  ring

end BfgsVerification.LExactDiagonalization
