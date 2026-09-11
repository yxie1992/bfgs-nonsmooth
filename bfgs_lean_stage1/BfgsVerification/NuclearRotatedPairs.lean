import BfgsVerification.NuclearSymmetric2

/-! Literal rotated rank-one matrix pairs in Module R's spectral example. -/
noncomputable section
open scoped BigOperators Topology Matrix
open Set Filter
namespace BfgsVerification.NuclearSymmetric2
open RadialCertificate

structure Rotation where
  c : ℝ
  s : ℝ
  unit : c^2+s^2=1

namespace Rotation
variable (P : Rotation)

def v : Vec 2 := ![P.c,P.s]
def u : Vec 2 := ![-P.s,P.c]
def W : Vec 3 := ![P.c^2,Real.sqrt 2*P.c*P.s,P.s^2]
def U : Vec 3 := ![P.s^2,-Real.sqrt 2*P.c*P.s,P.c^2]
def oldPoint (ε : ℝ) : Vec 3 := P.W-ε • P.U
def newPoint (ε : ℝ) : Vec 3 := P.W+ε • P.U
def oldGradient (ε : ℝ) : Vec 3 := P.oldPoint ε-center+P.W-P.U
def newGradient (ε : ℝ) : Vec 3 := P.newPoint ε-center+![1,0,1]

theorem matrix_W : matrix P.W = outer P.v P.v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix,W,outer,v,Matrix.cons_val_two]
  all_goals try field_simp [ne_of_gt sqrt_two_pos]
  all_goals ring

theorem matrix_U : matrix P.U = outer P.u P.u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix,U,outer,u,Matrix.cons_val_two]
  all_goals try field_simp [ne_of_gt sqrt_two_pos]
  all_goals ring

theorem W_add_U : P.W+P.U=![1,0,1] := by
  ext i
  fin_cases i <;> simp [W,U,Matrix.cons_val_two]
  · exact P.unit
  · linarith [P.unit]

theorem dot_W_W : dot P.W P.W=1 := by
  calc
    _ = (P.c^2+P.s^2)^2 := by
      simp [dot,W,Fin.sum_univ_three,Matrix.cons_val_two]
      ring_nf
      rw [sqrt_two_sq]
      ring
    _ = 1 := by rw [P.unit]; norm_num

theorem dot_U_U : dot P.U P.U=1 := by
  calc
    _ = (P.c^2+P.s^2)^2 := by
      simp [dot,U,Fin.sum_univ_three,Matrix.cons_val_two]
      ring_nf
      rw [sqrt_two_sq]
      ring
    _ = 1 := by rw [P.unit]; norm_num

theorem dot_U_W : dot P.U P.W=0 := by
  simp [dot,U,W,Fin.sum_univ_three,Matrix.cons_val_two]
  ring_nf
  rw [sqrt_two_sq]
  ring

theorem trace_old (ε : ℝ) : P.oldPoint ε 0+P.oldPoint ε 2=1-ε := by
  simp [oldPoint,W,U,Matrix.cons_val_two]
  linear_combination (1-ε)*P.unit

theorem trace_new (ε : ℝ) : P.newPoint ε 0+P.newPoint ε 2=1+ε := by
  simp [newPoint,W,U,Matrix.cons_val_two]
  linear_combination (1+ε)*P.unit

theorem discr_old (ε : ℝ) : discr (P.oldPoint ε)=(1+ε)^2 := by
  calc
    _ = (1+ε)^2*(P.c^2+P.s^2)^2 := by
      simp [discr,oldPoint,W,U,Matrix.cons_val_two]
      ring_nf
      rw [sqrt_two_sq]
      ring
    _ = _ := by rw [P.unit]; ring

theorem discr_new (ε : ℝ) : discr (P.newPoint ε)=(1-ε)^2 := by
  calc
    _ = (1-ε)^2*(P.c^2+P.s^2)^2 := by
      simp [discr,newPoint,W,U,Matrix.cons_val_two]
      ring_nf
      rw [sqrt_two_sq]
      ring
    _ = _ := by rw [P.unit]; ring

theorem sqrt_discr_old {ε : ℝ} (hε : 0 < ε) : Real.sqrt (discr (P.oldPoint ε))=1+ε := by
  rw [P.discr_old,Real.sqrt_sq_eq_abs,abs_of_pos (by linarith)]

theorem positive_branch_new {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (discr (P.newPoint ε)) < P.newPoint ε 0+P.newPoint ε 2 := by
  rw [P.discr_new,Real.sqrt_sq_eq_abs,P.trace_new,abs_lt]
  constructor <;> linarith

theorem indefinite_branch_old {ε : ℝ} (hε : 0 < ε) :
    |P.oldPoint ε 0+P.oldPoint ε 2| < Real.sqrt (discr (P.oldPoint ε)) := by
  rw [P.sqrt_discr_old hε,P.trace_old,abs_lt]
  constructor <;> linarith

theorem nuclear_pair_values {ε : ℝ} (hε : 0 < ε) :
    nuclearCoords (P.oldPoint ε)=1+ε ∧ nuclearCoords (P.newPoint ε)=1+ε := by
  constructor
  · rw [nuclearCoords_eq,max_eq_right (P.indefinite_branch_old hε).le,P.sqrt_discr_old hε]
  · rw [nuclearCoords_eq,P.trace_new,abs_of_pos (by linarith),P.discr_new,
      Real.sqrt_sq_eq_abs,max_eq_left]
    exact (abs_le.mpr ⟨by linarith,by linarith⟩)

theorem old_nuclear_hasGradient {ε : ℝ} (hε : 0 < ε) :
    HasFDerivAt nuclearCoords (gradientFunctional (P.W-P.U)) (P.oldPoint ε) := by
  have h := nuclearCoords_hasGradient_indef (P.indefinite_branch_old hε)
  rw [P.sqrt_discr_old hε] at h
  convert h using 1
  ext z
  simp [gradientFunctional_apply,dot,Fin.sum_univ_three,Matrix.cons_val_two,
    W,U,oldPoint,Matrix.vecHead,Matrix.vecTail]
  field_simp
  ring

theorem pair_gradients {ε : ℝ} (hε : 0 < ε) :
    HasFDerivAt objective (gradientFunctional (P.oldGradient ε)) (P.oldPoint ε) ∧
      HasFDerivAt objective (gradientFunctional (P.newGradient ε)) (P.newPoint ε) := by
  constructor
  · convert (smooth_hasGradient (P.oldPoint ε)).add (P.old_nuclear_hasGradient hε) using 1
    ext z
    simp [gradientFunctional_apply,dot,oldGradient,Finset.sum_add_distrib,
      Finset.sum_sub_distrib,add_mul,sub_mul]
    ring
  · convert (smooth_hasGradient (P.newPoint ε)).add
      (nuclearCoords_hasGradient_pos (P.positive_branch_new hε)) using 1
    ext z
    simp [gradientFunctional_apply,dot,newGradient,Fin.sum_univ_three,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    ring

theorem gradient_difference (ε : ℝ) : P.newGradient ε-P.oldGradient ε= (2*(1+ε)) • P.U := by
  rw [newGradient,oldGradient,← P.W_add_U,oldPoint,newPoint]
  module


theorem dot_U_minimizer : dot P.U minimizer=P.s^2 := by
  simp [dot,U,minimizer,Fin.sum_univ_three,Matrix.cons_val_two]

theorem sqNorm_affine (t : ℝ) :
    sqNorm (P.W+t • P.U-center)=5+t^2-4*P.c^2-4*t*P.s^2 := by
  have hWW : P.W ⬝ᵥ P.W=1 := P.dot_W_W
  have hUU : P.U ⬝ᵥ P.U=1 := P.dot_U_U
  have hUW : P.U ⬝ᵥ P.W=0 := P.dot_U_W
  have hWU : P.W ⬝ᵥ P.U=0 := by rw [dotProduct_comm]; exact hUW
  have hWC : P.W ⬝ᵥ center=2*P.c^2 := by
    simp [dotProduct,W,center,Fin.sum_univ_three,Matrix.cons_val_two]; ring
  have hUC : P.U ⬝ᵥ center=2*P.s^2 := by
    simp [dotProduct,U,center,Fin.sum_univ_three,Matrix.cons_val_two]; ring
  have hCW : center ⬝ᵥ P.W=2*P.c^2 := by rw [dotProduct_comm]; exact hWC
  have hCU : center ⬝ᵥ P.U=2*P.s^2 := by rw [dotProduct_comm]; exact hUC
  have hCC : center ⬝ᵥ center=4 := by norm_num [dotProduct,center,Fin.sum_univ_three,Matrix.cons_val_two]
  simp only [sqNorm,pow_two]
  change (P.W+t • P.U-center) ⬝ᵥ (P.W+t • P.U-center)=_
  simp only [add_dotProduct,sub_dotProduct,dotProduct_add,dotProduct_sub,
    smul_dotProduct,dotProduct_smul,smul_eq_mul,hWW,hUU,hUW,hWU,hWC,hUC,hCW,hCU,hCC]
  ring

theorem pair_values {ε : ℝ} (hε : 0 < ε) :
    objective (P.oldPoint ε)=3/2+2*P.s^2+ε*(1+2*P.s^2)+ε^2/2 ∧
      objective (P.newPoint ε)=3/2+2*P.s^2+ε*(1-2*P.s^2)+ε^2/2 := by
  obtain ⟨ho,hn⟩ := P.nuclear_pair_values hε
  have he : P.oldPoint ε=P.W+(-ε) • P.U := by unfold oldPoint; module
  constructor
  · rw [objective,smooth,ho,he,P.sqNorm_affine]
    linear_combination -2*P.unit
  · rw [objective,smooth,hn,newPoint,P.sqNorm_affine]
    linear_combination -2*P.unit

theorem pair_descent (ε : ℝ) (hε : 0 < ε) :
    objective (P.newPoint ε)-objective (P.oldPoint ε)= -4*P.s^2*ε := by
  rw [(P.pair_values hε).1,(P.pair_values hε).2]
  ring

theorem pair_curvature (ε : ℝ) :
    secantCurvature (P.oldPoint ε) (P.newPoint ε) (P.oldGradient ε) (P.newGradient ε)=
      4*ε*(1+ε) := by
  have hs : P.newPoint ε-P.oldPoint ε=(2*ε) • P.U := by unfold newPoint oldPoint; module
  rw [secantCurvature,P.gradient_difference,hs]
  change ((2*(1+ε)) • P.U) ⬝ᵥ ((2*ε) • P.U)=_
  rw [smul_dotProduct,dotProduct_smul,show P.U ⬝ᵥ P.U=1 from P.dot_U_U]
  simp only [smul_eq_mul]
  ring

theorem radial_numerator (ε : ℝ) :
    radialNumerator minimizer (P.newPoint ε) (P.oldGradient ε) (P.newGradient ε)=
      2*(1+ε)*(ε-P.s^2) := by
  rw [radialNumerator,P.gradient_difference,newPoint]
  change ((2*(1+ε)) • P.U) ⬝ᵥ (P.W+ε • P.U-minimizer)=_
  rw [smul_dotProduct,dotProduct_sub,dotProduct_add,dotProduct_smul,
    show P.U ⬝ᵥ P.U=1 from P.dot_U_U,show P.U ⬝ᵥ P.W=0 from P.dot_U_W,
    show P.U ⬝ᵥ minimizer=P.s^2 from P.dot_U_minimizer]
  simp

theorem radial_quotient {ε : ℝ} (hε : 0 < ε) :
    (radialNumerator minimizer (P.newPoint ε) (P.oldGradient ε) (P.newGradient ε))^2 /
      secantCurvature (P.oldPoint ε) (P.newPoint ε) (P.oldGradient ε) (P.newGradient ε)=
        (1+ε)*(ε-P.s^2)^2/ε := by
  rw [P.radial_numerator,P.pair_curvature]
  have hp : 1+ε ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem radial_quotient_tendsto (hP : P.s ≠ 0) :
    Tendsto (fun ε => (radialNumerator minimizer (P.newPoint ε) (P.oldGradient ε) (P.newGradient ε))^2 /
      secantCurvature (P.oldPoint ε) (P.newPoint ε) (P.oldGradient ε) (P.newGradient ε))
      (𝓝[>] 0) atTop := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hn : Tendsto (fun ε : ℝ => (1+ε)*(ε-P.s^2)^2) (𝓝[>] 0) (𝓝 ((P.s^2)^2)) := by
    convert (tendsto_const_nhds.add he).mul ((he.sub tendsto_const_nhds).pow 2) using 1 <;> norm_num
  have hq := hn.pos_mul_atTop (sq_pos_of_pos (sq_pos_of_ne_zero hP))
    tendsto_id.inv_tendsto_nhdsGT_zero
  apply hq.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simpa only [div_eq_mul_inv] using (P.radial_quotient hε).symm


theorem vectors_orthonormal : dot P.v P.v=1 ∧ dot P.u P.u=1 ∧ dot P.v P.u=0 := by
  simp [dot,v,u,Fin.sum_univ_two]
  constructor
  · nlinarith [P.unit]
  constructor
  · nlinarith [P.unit]
  · ring

theorem base_value : objective P.W-objective minimizer=2*P.s^2 := by
  have hn : nuclearCoords P.W=1 := by
    have ht := P.trace_old 0
    have hd := P.discr_old 0
    simp only [oldPoint,zero_smul,sub_zero,sub_zero,add_zero,one_pow] at ht hd
    rw [nuclearCoords_eq,ht,hd]
    norm_num
  have hnorm := P.sqNorm_affine 0
  simp only [zero_smul,add_zero,zero_pow (by norm_num : 2 ≠ 0),zero_mul,sub_zero] at hnorm
  rw [objective, smooth, hn, hnorm, objective_minimizer_value]
  linear_combination -2*P.unit

theorem pair_points_tendsto :
    Tendsto P.oldPoint (𝓝[>] 0) (𝓝 P.W) ∧ Tendsto P.newPoint (𝓝[>] 0) (𝓝 P.W) := by
  have ho : Continuous P.oldPoint := by unfold oldPoint; fun_prop
  have hn : Continuous P.newPoint := by unfold newPoint; fun_prop
  exact ⟨by simpa [oldPoint] using (ho.tendsto 0).mono_left nhdsWithin_le_nhds,
    by simpa [newPoint] using (hn.tendsto 0).mono_left nhdsWithin_le_nhds⟩


theorem pair_matrix_form (ε : ℝ) :
    matrix (P.oldPoint ε)=outer P.v P.v-ε • outer P.u P.u ∧
      matrix (P.newPoint ε)=outer P.v P.v+ε • outer P.u P.u := by
  constructor
  · rw [oldPoint,matrix_sub,matrix_smul,P.matrix_W,P.matrix_U]
  · rw [newPoint,matrix_add,matrix_smul,P.matrix_W,P.matrix_U]

theorem pair_determinants (ε : ℝ) :
    (matrix (P.oldPoint ε)).det= -ε ∧ (matrix (P.newPoint ε)).det=ε := by
  rw [matrix_det,P.trace_old,P.discr_old,matrix_det,P.trace_new,P.discr_new]
  constructor <;> ring

theorem pair_eigenvalues_nonzero {ε : ℝ} (hε : 0 < ε) :
    (∀ i, (matrix_hermitian (P.oldPoint ε)).eigenvalues i ≠ 0) ∧
      (∀ i, (matrix_hermitian (P.newPoint ε)).eigenvalues i ≠ 0) := by
  constructor
  · apply matrix_eigenvalues_nonzero
    rw [(P.pair_determinants ε).1]
    exact neg_ne_zero.mpr hε.ne'
  · apply matrix_eigenvalues_nonzero
    rw [(P.pair_determinants ε).2]
    exact hε.ne'

theorem pair_frobenius_identities (ε : ℝ) :
    matrix (P.newGradient ε)-matrix (P.oldGradient ε)=
      (2*(1+ε)) • outer P.u P.u ∧
    frobenius (matrix (P.newGradient ε)-matrix (P.oldGradient ε))
      (matrix (P.newPoint ε)-matrix (P.oldPoint ε))=4*ε*(1+ε) ∧
    frobenius (matrix (P.newGradient ε)-matrix (P.oldGradient ε))
      (matrix (P.newPoint ε)-matrix minimizer)=2*(1+ε)*(ε-P.s^2) := by
  constructor
  · rw [← matrix_sub,P.gradient_difference,matrix_smul,P.matrix_U]
  constructor
  · rw [← matrix_sub,← matrix_sub,frobenius_matrix]
    exact P.pair_curvature ε
  · rw [← matrix_sub,← matrix_sub,frobenius_matrix]
    exact P.radial_numerator ε

end Rotation

def trigRotation (θ : ℝ) : Rotation where
  c := Real.cos θ
  s := Real.sin θ
  unit := by nlinarith [Real.sin_sq_add_cos_sq θ]

theorem trigRotation_base_continuous : Continuous (fun θ => (trigRotation θ).W) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [trigRotation,Rotation.W,Matrix.cons_val_two] <;> fun_prop

theorem trigRotation_base_zero : (trigRotation 0).W=minimizer := by
  ext i
  fin_cases i <;> norm_num [trigRotation,Rotation.W,minimizer,Matrix.cons_val_two]

/-- Nontrivial literal trigonometric rotations occur inside every neighborhood
of the rank-deficient minimizer. -/
theorem exists_rotated_base {K : Set (Vec 3)} (hK : K ∈ 𝓝 minimizer) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧ K ∈ 𝓝 (trigRotation θ).W := by
  obtain ⟨O,hOK,hO,hstar⟩ := mem_nhds_iff.mp hK
  have ht : Tendsto (fun θ => (trigRotation θ).W) (𝓝[>] 0) (𝓝 minimizer) := by
    rw [← trigRotation_base_zero]
    exact (trigRotation_base_continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  have hp : ∀ᶠ θ : ℝ in 𝓝[>] 0, 0 < θ := self_mem_nhdsWithin
  have hb : ∀ᶠ θ : ℝ in 𝓝[>] 0, θ < Real.pi :=
    (eventually_lt_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds
  obtain ⟨θ,hθ,hπ,hOθ⟩ := (hp.and (hb.and (ht.eventually (hO.mem_nhds hstar)))).exists
  exact ⟨θ,hθ,hπ,mem_of_superset (hO.mem_nhds hOθ) hOK⟩

/-- A fixed positive band in every neighborhood contains literal rotated pairs
with arbitrarily large squared radial numerator divided by curvature. -/
theorem unbounded_radial_pairs {K : Set (Vec 3)} (hK : K ∈ 𝓝 minimizer) :
    ∃ θ η : ℝ, 0 < θ ∧ θ < Real.pi ∧ 0 < η ∧ ∀ C : ℝ, ∃ ε : ℝ, 0 < ε ∧
      let P := trigRotation θ
      P.oldPoint ε ∈ K ∧ P.newPoint ε ∈ K ∧
      objective minimizer+η ≤ objective (P.newPoint ε) ∧
      objective (P.newPoint ε) < objective (P.oldPoint ε) ∧
      HasFDerivAt objective (gradientFunctional (P.oldGradient ε)) (P.oldPoint ε) ∧
      HasFDerivAt objective (gradientFunctional (P.newGradient ε)) (P.newPoint ε) ∧
      0 < secantCurvature (P.oldPoint ε) (P.newPoint ε) (P.oldGradient ε) (P.newGradient ε) ∧
      C*secantCurvature (P.oldPoint ε) (P.newPoint ε) (P.oldGradient ε) (P.newGradient ε) <
        (radialNumerator minimizer (P.newPoint ε) (P.oldGradient ε) (P.newGradient ε))^2 := by
  obtain ⟨θ,hθ,hπ,hKθ⟩ := exists_rotated_base hK
  let P := trigRotation θ
  have hs : 0 < P.s := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hη : 0 < P.s^2 := sq_pos_of_pos hs
  refine ⟨θ,P.s^2,hθ,hπ,hη,?_⟩
  intro C
  have hr := (P.radial_quotient_tendsto hs.ne').eventually (eventually_gt_atTop C)
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, objective minimizer+P.s^2 < objective (P.newPoint ε) := by
    have hc := (convex_continuous objective_convex).continuousAt.tendsto.comp P.pair_points_tendsto.2
    have hb : objective minimizer+P.s^2 < objective P.W := by
      have he := P.base_value
      linarith
    exact hc.eventually (eventually_gt_nhds hb)
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hx,hz,hband,hq⟩ := (hp.and ((P.pair_points_tendsto.1.eventually hKθ).and
    ((P.pair_points_tendsto.2.eventually hKθ).and (hb.and hr)))).exists
  have ht : 0 < secantCurvature (P.oldPoint ε) (P.newPoint ε) (P.oldGradient ε) (P.newGradient ε) := by
    rw [P.pair_curvature]
    positivity
  obtain ⟨hg,hh⟩ := P.pair_gradients hε
  refine ⟨ε,hε,hx,hz,hband.le,?_,hg,hh,ht,(lt_div_iff₀ ht).mp hq⟩
  have hd := P.pair_descent ε hε
  have hn : 0 < 4*P.s^2*ε := by positivity
  linarith

theorem not_radial_secant_on_neighborhood {K : Set (Vec 3)} (hK : K ∈ 𝓝 minimizer) :
    ¬ HasRadialSecantBounds objective K minimizer := by
  intro hrs
  obtain ⟨θ,η,hθ,hπ,hη,hex⟩ := unbounded_radial_pairs hK
  obtain ⟨C,hC⟩ := hrs η hη
  obtain ⟨ε,hε,hx,hz,hband,horder,hg,hh,ht,hexcess⟩ := hex C
  have hb := hC _ _ _ _ hx hz hband horder.le hg hh ht
  exact not_lt_of_ge hb hexcess

/-- Failure occurs on every positive sublevel, each of which is compact. -/
theorem not_radial_secant_on_sublevel {B : ℝ} (hB : objective minimizer < B) :
    IsCompact {x | objective x ≤ B} ∧
      ¬ HasRadialSecantBounds objective {x | objective x ≤ B} minimizer := by
  refine ⟨objective_sublevel_compact B,not_radial_secant_on_neighborhood ?_⟩
  have hO := isOpen_lt (convex_continuous objective_convex) (continuous_const (y := B))
  exact mem_of_superset (hO.mem_nhds hB) (fun x hx => (show objective x < B from hx).le)



/-- Every literal Frobenius ball around diag(1,0) fails (RS). -/
theorem not_radial_secant_on_frobenius_ball {r : ℝ} (hr : 0 < r) :
    ¬ HasRadialSecantBounds objective
      {x | frobenius (matrix x-matrix minimizer) (matrix x-matrix minimizer) < r^2} minimizer := by
  apply not_radial_secant_on_neighborhood
  have he : (fun x : Vec 3 => frobenius (matrix x-matrix minimizer) (matrix x-matrix minimizer))=
      (fun x => dot (x-minimizer) (x-minimizer)) := by
    ext x
    rw [← matrix_sub,frobenius_matrix]
  have hc : Continuous (fun x : Vec 3 =>
      frobenius (matrix x-matrix minimizer) (matrix x-matrix minimizer)) := by
    rw [he]
    unfold dot
    fun_prop
  apply (isOpen_lt hc continuous_const).mem_nhds
  simpa [frobenius] using sq_pos_of_pos hr

end BfgsVerification.NuclearSymmetric2

