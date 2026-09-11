import BfgsVerification.NuclearRotatedPairs
import BfgsVerification.HomogeneousConsequences
import BfgsVerification.PoweredGaugeRadial

/-! The separate centered-nuclear comparison in R's last sentence.
Completed after the seventh milestone; built and audited independently before integration. -/
noncomputable section
open scoped BigOperators Topology Matrix
open Set Filter
namespace BfgsVerification.NuclearSymmetric2

 theorem nuclearCoords_homogeneous : Homogeneous.PositiveDegreeOne nuclearCoords := by
  intro t ht x
  rw [nuclearCoords_eq,nuclearCoords_eq,← discrMap_norm,← discrMap_norm,map_smul,norm_smul]
  simp only [Pi.smul_apply,smul_eq_mul,← mul_add,abs_mul,Real.norm_eq_abs,abs_of_nonneg ht]
  exact (mul_max_of_nonneg _ _ ht).symm

 theorem nuclearCoords_zero : nuclearCoords 0=0 := Homogeneous.value_zero nuclearCoords_homogeneous

 theorem nuclearCoords_unique_zero (x : Vec 3) (hx : nuclearCoords x=0) : x=0 := by
  have ht : |x 0+x 2| ≤ 0 := by rw [← hx,nuclearCoords_eq]; exact le_max_left _ _
  have hd : Real.sqrt (discr x) ≤ 0 := by rw [← hx,nuclearCoords_eq]; exact le_max_right _ _
  have hsum : x 0+x 2=0 := abs_nonpos_iff.mp ht
  have hs : discr x=0 := by
    have he : Real.sqrt (discr x)=0 := le_antisymm hd (Real.sqrt_nonneg _)
    have hsq := Real.sq_sqrt (discr_nonneg x)
    rw [he] at hsq
    linarith
  unfold discr at hs
  have hdif : x 0-x 2=0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (x 1)])
  have hone : x 1=0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (x 0-x 2)])
  ext i
  fin_cases i
  · change x 0=0; linarith
  · exact hone
  · change x 2=0; linarith

 theorem nuclearCoords_minimum (x : Vec 3) : nuclearCoords 0 ≤ nuclearCoords x := by
  rw [nuclearCoords_zero]
  exact nuclear_nonneg _ _

 theorem nuclearCoords_sublevel_compact (b : ℝ) : IsCompact {x | nuclearCoords x ≤ b} :=
  Localization.sublevel_compact nuclearCoords_convex 0 nuclearCoords_minimum
    (fun x hx => nuclearCoords_unique_zero x (by simpa only [nuclearCoords_zero] using hx)) b

 theorem nuclearCoords_inward_error_zero {x g : Vec 3}
    (hg : HasFDerivAt nuclearCoords (gradientFunctional g) x) {t : ℝ} (ht : t ≤ 1) :
    RadialCertificate.supportingError nuclearCoords x g
      (RadialCertificate.inwardPoint 0 x t)=0 := by
  simpa only [sub_zero] using RadialPower.degree_one_inward_error_zero nuclearCoords_convex
    nuclearCoords_homogeneous 0 (by simpa only [sub_zero] using hg) ht

 theorem centered_nuclear_convergence (R : AdmissibleBFGSRun 3 nuclearCoords) :
    Tendsto (fun k => nuclearCoords (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  refine ⟨(R.homogeneous_bounded_below_convergence nuclearCoords_homogeneous 0
    (fun x => nuclear_nonneg _ _)).2.2,?_⟩
  exact R.homogeneous_iterates_zero_of_bounded_zero_sublevel nuclearCoords_homogeneous
    (nuclearCoords_sublevel_compact 0).isBounded

 theorem minimizer_matrix_rank : (matrix minimizer).rank=1 := by
  classical
  have he : matrix minimizer=Matrix.diagonal ![1,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [matrix,minimizer,Matrix.cons_val_two]
  rw [he,Matrix.rank_diagonal]
  norm_num [Fintype.card_subtype,Finset.univ_fin2,Finset.filter_insert,
    Finset.filter_singleton,Matrix.cons_val_zero,Matrix.cons_val_one]


 theorem centered_nuclear_inward (K : Set (Vec 3)) :
    RadialCertificate.HasInwardTaylorBounds nuclearCoords K 0 := by
  intro η hη
  refine ⟨0,1/2,by norm_num,le_rfl,?_⟩
  intro x g hx hband hg t ht htmax
  rw [nuclearCoords_inward_error_zero hg (by linarith)]
  norm_num

 theorem centered_nuclear_radial {K : Set (Vec 3)} (hK : IsCompact K) :
    RadialCertificate.HasRadialSecantBounds nuclearCoords K 0 :=
  RadialCertificate.radial_of_inward_on_compact nuclearCoords_convex hK 0 (centered_nuclear_inward K)

end BfgsVerification.NuclearSymmetric2

