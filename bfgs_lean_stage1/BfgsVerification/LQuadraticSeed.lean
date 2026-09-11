import BfgsVerification.AlgebraicSeedFiniteCycle
import BfgsVerification.QuadraticGaugeAlgebra
import BfgsVerification.FixedNormalStrongConvex
import BfgsVerification.FiniteMaxSubdifferential
import BfgsVerification.ConvexGradientLimits
import BfgsVerification.CertificateGeometry
import BfgsVerification.RadialHessian
import BfgsVerification.FrameNorms
import Mathlib.Analysis.Convex.Strong

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.LQuadraticSeed
open SeedCycle SeedOrbit

def gbar : Vec 2 := ![1/257,-16/257]
def slopes : Set (Vec 2) := range (SeedOrbit.gradient seedC seedD)
def minimizer (μ : ℝ) : Vec 2 := (-μ⁻¹) • gbar
def quadratic (μ : ℝ) (x : Vec 2) : ℝ := μ/2*sqNorm x
def branch (μ : ℝ) (i : Fin 3) (x : Vec 2) : ℝ :=
  quadratic μ x+dot (SeedOrbit.gradient seedC seedD i) x
def objective (μ : ℝ) (x : Vec 2) : ℝ :=
  quadratic μ x+SeedOrbit.objective seedC seedD x
def branchGradient (μ : ℝ) (x : Vec 2) (i : Fin 3) : Vec 2 :=
  μ • x+SeedOrbit.gradient seedC seedD i

theorem gbar_weights : gbar=(129/257 : ℝ) • g0+(128/257 : ℝ) • g1 := by
  ext i
  fin_cases i <;> norm_num [gbar,g0,g1]

theorem gbar_sqNorm : sqNorm gbar=1/257 := by
  norm_num [gbar,sqNorm,Fin.sum_univ_two]

theorem gbar_dot_first : dot g0 gbar=1/257 ∧ dot g1 gbar=1/257 := by
  norm_num [gbar,g0,g1,dot,Fin.sum_univ_two]

theorem gbar_dot_third : 1/257 < dot (g2 seedC seedD) gbar := by
  obtain ⟨⟨hc0,hc1⟩,⟨hd0,hd1⟩⟩ := SeedOrbit.root_tight_box
  norm_num only [g2,gbar,dot,Fin.sum_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.vecHead,Matrix.vecTail]
  linarith

theorem slopes_pairing_bound (i : Fin 3) :
    sqNorm gbar ≤ dot (SeedOrbit.gradient seedC seedD i) gbar := by
  rw [gbar_sqNorm]
  fin_cases i
  · exact gbar_dot_first.1.ge
  · exact gbar_dot_first.2.ge
  · exact gbar_dot_third.le

theorem gbar_mem_convexHull : gbar ∈ convexHull ℝ slopes := by
  rw [gbar_weights]
  exact (convex_convexHull ℝ slopes)
    (subset_convexHull ℝ slopes ⟨0,rfl⟩) (subset_convexHull ℝ slopes ⟨1,rfl⟩)
    (by norm_num) (by norm_num) (by norm_num)

theorem hull_pairing_bound {g : Vec 2} (hg : g ∈ convexHull ℝ slopes) :
    sqNorm gbar ≤ dot g gbar := by
  have hc : Convex ℝ {g : Vec 2 | sqNorm gbar ≤ dot g gbar} := by
    intro x hx y hy a b ha hb hab
    change sqNorm gbar ≤ dot (a • x+b • y) gbar
    change sqNorm gbar ≤ dotProduct (a • x+b • y) gbar
    rw [add_dotProduct,smul_dotProduct,smul_dotProduct]
    change sqNorm gbar ≤ a*dot x gbar+b*dot y gbar
    have h := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    rw [← add_mul,hab,one_mul] at h
    exact h
  exact convexHull_min (by rintro _ ⟨i,rfl⟩; exact slopes_pairing_bound i) hc hg

theorem gbar_least_sqNorm {g : Vec 2} (hg : g ∈ convexHull ℝ slopes) :
    sqNorm gbar ≤ sqNorm g := by
  have hp := hull_pairing_bound hg
  have hs := dot_sq_le_sqNorm_mul_sqNorm g gbar
  rw [gbar_sqNorm] at hp hs ⊢
  nlinarith [sq_nonneg (dot g gbar-1/257)]

theorem gbar_least_norm {g : Vec 2} (hg : g ∈ convexHull ℝ slopes) :
    ‖euclideanVector gbar‖ ≤ ‖euclideanVector g‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [FrameNorms.euclidean_norm_sq,FrameNorms.euclidean_norm_sq]
  exact gbar_least_sqNorm hg

theorem zero_not_mem_convexHull : (0 : Vec 2) ∉ convexHull ℝ slopes := by
  intro h
  have hp := hull_pairing_bound h
  norm_num [gbar_sqNorm,dot] at hp

theorem seed_branch_le (i : Fin 3) (x : Vec 2) :
    dot (SeedOrbit.gradient seedC seedD i) x ≤ SeedOrbit.objective seedC seedD x := by
  simpa [SeedOrbit.objective,SeedOrbit.family,MaxAffine.Family.branch] using
    (SeedOrbit.family seedC seedD).branch_le i x

theorem seed_objective_le {x : Vec 2} {a : ℝ}
    (h : ∀ i, dot (SeedOrbit.gradient seedC seedD i) x ≤ a) :
    SeedOrbit.objective seedC seedD x ≤ a := by
  unfold SeedOrbit.objective MaxAffine.Family.objective
  apply Finset.sup'_le
  intro i _
  simpa [MaxAffine.Family.branch,SeedOrbit.family] using h i

theorem gbar_supports_seed (x : Vec 2) : dot gbar x ≤ SeedOrbit.objective seedC seedD x := by
  rw [gbar_weights]
  change dotProduct ((129/257 : ℝ) • g0+(128/257 : ℝ) • g1) x ≤ _
  rw [add_dotProduct,smul_dotProduct,smul_dotProduct]
  change (129/257 : ℝ)*dot g0 x+(128/257 : ℝ)*dot g1 x ≤ _
  have h0 : dot g0 x ≤ SeedOrbit.objective seedC seedD x := seed_branch_le 0 x
  have h1 : dot g1 x ≤ SeedOrbit.objective seedC seedD x := seed_branch_le 1 x
  linarith

theorem quadratic_convex {μ : ℝ} (hμ : 0 ≤ μ) : ConvexOn ℝ univ (quadratic μ) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have he : a=1-b := by linarith
  have hs := FixedNormal.sqNorm_convex_combination x y b
  have hp := mul_nonneg (mul_nonneg hb ha) (sqNorm_nonneg (y-x))
  simp only [quadratic,smul_eq_mul]
  rw [he,hs]
  rw [he] at hp
  nlinarith [mul_nonneg hμ hp]

theorem objective_convex {μ : ℝ} (hμ : 0 ≤ μ) : ConvexOn ℝ univ (objective μ) :=
  (quadratic_convex hμ).add (SeedOrbit.family seedC seedD).objective_convex

theorem objective_strongConvex (μ : ℝ) :
    FixedNormal.EuclideanStrongConvexOn univ μ (objective μ) := by
  simpa only [FixedNormal.EuclideanStrongConvexOn,objective,quadratic,add_sub_cancel_left]
    using (SeedOrbit.family seedC seedD).objective_convex

theorem branch_convex {μ : ℝ} (hμ : 0 ≤ μ) (i : Fin 3) : ConvexOn ℝ univ (branch μ i) := by
  have hl := (gradientFunctional (SeedOrbit.gradient seedC seedD i)).toLinearMap.convexOn convex_univ
  simpa only [ContinuousLinearMap.coe_coe,gradientFunctional_apply] using (quadratic_convex hμ).add hl

theorem branch_contDiff (μ : ℝ) (i : Fin 3) : ContDiff ℝ 2 (branch μ i) := by
  unfold branch quadratic sqNorm dot
  simp only [Fin.sum_univ_two]
  fun_prop

theorem minimizer_dot {μ : ℝ} (i : Fin 3) :
    dot (SeedOrbit.gradient seedC seedD i) (minimizer μ)=
      -μ⁻¹*dot (SeedOrbit.gradient seedC seedD i) gbar := by
  change dotProduct (SeedOrbit.gradient seedC seedD i) ((-μ⁻¹) • gbar)=_
  rw [dotProduct_smul]
  rfl

theorem minimizer_seed_active {μ : ℝ} (hμ : 0 < μ) :
    dot g0 (minimizer μ)=-1/(257*μ) ∧ dot g1 (minimizer μ)=-1/(257*μ) ∧
    dot (g2 seedC seedD) (minimizer μ) < -1/(257*μ) := by
  have he : -μ⁻¹*(1/257)=-1/(257*μ) := by ring
  have h0 := minimizer_dot (μ := μ) 0
  have h1 := minimizer_dot (μ := μ) 1
  have h2 := minimizer_dot (μ := μ) 2
  change dot g0 (minimizer μ)=-μ⁻¹*dot g0 gbar at h0
  change dot g1 (minimizer μ)=-μ⁻¹*dot g1 gbar at h1
  change dot (g2 seedC seedD) (minimizer μ)=-μ⁻¹*dot (g2 seedC seedD) gbar at h2
  rw [gbar_dot_first.1,he] at h0
  rw [gbar_dot_first.2,he] at h1
  refine ⟨h0,h1,?_⟩
  rw [h2,← he]
  exact mul_lt_mul_of_neg_left gbar_dot_third (neg_neg_of_pos (inv_pos.mpr hμ))

theorem minimizer_seed_value {μ : ℝ} (hμ : 0 < μ) :
    SeedOrbit.objective seedC seedD (minimizer μ)=-1/(257*μ) := by
  obtain ⟨h0,h1,h2⟩ := minimizer_seed_active hμ
  apply le_antisymm
  · apply seed_objective_le
    intro i
    fin_cases i
    · exact h0.le
    · exact h1.le
    · exact h2.le
  · rw [← h0]
    exact seed_branch_le 0 _

theorem minimizer_value {μ : ℝ} (hμ : 0 < μ) :
    objective μ (minimizer μ)=-1/(514*μ) := by
  rw [objective,minimizer_seed_value hμ]
  unfold quadratic minimizer sqNorm gbar
  simp only [Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp [hμ.ne']
  ring

theorem quadratic_completion {μ : ℝ} (hμ : μ ≠ 0) (x : Vec 2) :
    quadratic μ x+dot gbar x=μ/2*sqNorm (x-minimizer μ)-1/(514*μ) := by
  unfold quadratic minimizer sqNorm gbar dot
  simp only [Fin.sum_univ_two,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp [hμ]
  ring

theorem objective_lower_bound {μ : ℝ} (hμ : 0 < μ) (x : Vec 2) :
    μ/2*sqNorm (x-minimizer μ)-1/(514*μ) ≤ objective μ x := by
  rw [← quadratic_completion hμ.ne' x]
  exact add_le_add_left (gbar_supports_seed x) _

theorem objective_minimum {μ : ℝ} (hμ : 0 < μ) (x : Vec 2) :
    objective μ (minimizer μ) ≤ objective μ x := by
  rw [minimizer_value hμ]
  have hb := objective_lower_bound hμ x
  have hs := mul_nonneg (div_nonneg hμ.le (by norm_num : (0 : ℝ) ≤ 2)) (sqNorm_nonneg (x-minimizer μ))
  simp only [neg_div] at *
  linarith

theorem objective_unique_minimum {μ : ℝ} (hμ : 0 < μ) {x : Vec 2}
    (hx : objective μ x=objective μ (minimizer μ)) : x=minimizer μ := by
  have hb := objective_lower_bound hμ x
  rw [hx,minimizer_value hμ] at hb
  simp only [neg_div] at hb
  have hs : sqNorm (x-minimizer μ)=0 := by nlinarith [sqNorm_nonneg (x-minimizer μ)]
  exact sub_eq_zero.mp ((CertificateGeometry.sqNorm_eq_zero_iff _).mp hs)

theorem objective_sublevels_compact {μ : ℝ} (hμ : 0 < μ) (a : ℝ) :
    IsCompact {x | objective μ x ≤ a} :=
  Localization.sublevel_compact (objective_convex hμ.le) (minimizer μ)
    (objective_minimum hμ) (fun _ hx => objective_unique_minimum hμ hx) a

theorem objective_coercive {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (objective μ) (cocompact (Vec 2)) atTop := by
  apply tendsto_atTop.2
  intro a
  filter_upwards [(objective_sublevels_compact hμ a).compl_mem_cocompact] with x hx
  change ¬ objective μ x ≤ a at hx
  exact (lt_of_not_ge hx).le

theorem objective_euclidean_strongConvex (μ : ℝ) :
    StrongConvexOn univ μ (fun x : EuclideanSpace ℝ (Fin 2) => objective μ (fun i => x i)) := by
  rw [strongConvexOn_iff_convex]
  have hc := (SeedOrbit.family seedC seedD).objective_convex.comp_linearMap
    (WithLp.linearEquiv 2 ℝ (Vec 2)).toLinearMap
  simpa only [preimage_univ,LinearEquiv.coe_coe,WithLp.linearEquiv_apply,
    Function.comp_def,objective,quadratic,FrameNorms.euclidean_norm_sq,add_sub_cancel_left] using hc

theorem quadratic_hasGradient (μ : ℝ) (x : Vec 2) :
    HasFDerivAt (quadratic μ) (gradientFunctional (μ • x)) x := by
  have hs : ((μ : ℝ) • (1 : Mat 2)).IsSymm := by
    simp [Matrix.IsSymm,Matrix.transpose_smul]
  have h := QuadraticGauge.quadratic_hasGradient (μ • (1 : Mat 2)) hs x
  simp only [Matrix.smul_mulVec_assoc,Matrix.one_mulVec] at h
  convert h using 1
  funext z
  simp only [quadratic,metricEnergy,Matrix.smul_mulVec_assoc,Matrix.one_mulVec]
  change μ/2*sqNorm z=dotProduct z (μ • z)/2
  rw [dotProduct_smul]
  have he : dotProduct z z=sqNorm z := by simp [dotProduct,sqNorm,pow_two]
  rw [he]
  simp only [smul_eq_mul]
  ring

theorem branch_hasGradient (μ : ℝ) (i : Fin 3) (x : Vec 2) :
    HasFDerivAt (branch μ i) (gradientFunctional (branchGradient μ x i)) x := by
  have hl : HasFDerivAt (dot (SeedOrbit.gradient seedC seedD i))
      (gradientFunctional (SeedOrbit.gradient seedC seedD i)) x := by
    convert (gradientFunctional (SeedOrbit.gradient seedC seedD i)).hasFDerivAt (x := x) using 1
  convert (quadratic_hasGradient μ x).add hl using 1
  ext v
  simp only [gradientFunctional_apply,ContinuousLinearMap.add_apply,branchGradient,dot,
    Pi.add_apply,add_mul,Finset.sum_add_distrib]

def pairingMap : Vec 2 →L[ℝ] Vec 2 →L[ℝ] ℝ :=
  ∑ i : Fin 2, (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj i)

theorem pairingMap_apply (x : Vec 2) : pairingMap x=gradientFunctional x := by
  ext v
  simp [pairingMap,gradientFunctional_apply,dot,ContinuousLinearMap.smulRight_apply]

theorem branch_second_hasFDerivAt (μ : ℝ) (i : Fin 3) (x : Vec 2) :
    HasFDerivAt (fderiv ℝ (branch μ i)) (μ • pairingMap) x := by
  have he : fderiv ℝ (branch μ i)=fun z => (μ • pairingMap) z+
      gradientFunctional (SeedOrbit.gradient seedC seedD i) := by
    funext z
    rw [(branch_hasGradient μ i z).fderiv]
    ext v
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,pairingMap_apply,
      gradientFunctional_apply,branchGradient,dot,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      add_mul,mul_assoc,Finset.sum_add_distrib,Finset.mul_sum]
  rw [he]
  exact (μ • pairingMap).hasFDerivAt.add_const _

theorem branch_hessian (μ : ℝ) (i : Fin 3) (x : Vec 2) :
    RadialHessian.matrix (branch μ i) x=μ • (1 : Mat 2) := by
  rw [RadialHessian.matrix,(branch_second_hasFDerivAt μ i x).fderiv]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [RadialHessian.bilinearMatrix,ContinuousLinearMap.smul_apply,
      pairingMap_apply,gradientFunctional_apply,dot,Fin.sum_univ_two]

theorem branch_le_objective (μ : ℝ) (i : Fin 3) (x : Vec 2) :
    branch μ i x ≤ objective μ x := add_le_add_left (seed_branch_le i x) _

theorem objective_eq_branch (μ : ℝ) (x : Vec 2) : ∃ i, objective μ x=branch μ i x := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' (SeedOrbit.family seedC seedD).indices_nonempty
    (fun i => (SeedOrbit.family seedC seedD).branch i x)
  refine ⟨i,?_⟩
  have hs : SeedOrbit.objective seedC seedD x=dot (SeedOrbit.gradient seedC seedD i) x := by
    simpa only [SeedOrbit.objective,MaxAffine.Family.objective,
      MaxAffine.Family.branch,SeedOrbit.family,Pi.zero_apply,add_zero] using hi
  exact congrArg (quadratic μ x+·) hs

theorem objective_eq_sup (μ : ℝ) (x : Vec 2) :
    objective μ x=Finset.univ.sup' Finset.univ_nonempty (fun i => branch μ i x) := by
  apply le_antisymm
  · obtain ⟨i,hi⟩ := objective_eq_branch μ x
    rw [hi]
    exact Finset.le_sup' (fun j => branch μ j x) (Finset.mem_univ i)
  · exact Finset.sup'_le _ _ (fun i _ => branch_le_objective μ i x)

theorem local_representation (μ : ℝ) (x : Vec 2) :
    ConvexSubdifferential.LocalFiniteMax (objective μ) (branch μ) x := by
  apply Eventually.of_forall
  intro z
  constructor
  · obtain ⟨i,hi⟩ := objective_eq_branch μ z
    exact ⟨i,hi.symm⟩
  · rintro _ ⟨i,rfl⟩
    exact branch_le_objective μ i z

theorem branch_zero (μ : ℝ) (i : Fin 3) : branch μ i 0=0 := by
  simp [branch,quadratic,sqNorm,dot]

theorem objective_zero (μ : ℝ) : objective μ 0=0 := by
  obtain ⟨i,hi⟩ := objective_eq_branch μ 0
  exact hi.trans (branch_zero μ i)

theorem origin_subdifferential {μ : ℝ} (hμ : 0 ≤ μ) :
    ConvexSubdifferential.subdifferential (objective μ) 0=convexHull ℝ slopes := by
  have ha : ConvexSubdifferential.activeIndices (objective μ) (branch μ) 0=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    apply ConvexSubdifferential.mem_activeIndices.mpr
    rw [branch_zero,objective_zero]
  have he := ConvexSubdifferential.subdifferential_eq_active_convexHull (objective_convex hμ)
    (local_representation μ 0) (fun i => branch_hasGradient μ i 0)
  simpa only [ha,Finset.coe_univ,image_univ,branchGradient,smul_zero,zero_add,slopes] using he

theorem origin_nonstationary {μ : ℝ} (hμ : 0 ≤ μ) :
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential (objective μ) 0 := by
  rw [origin_subdifferential hμ]
  exact zero_not_mem_convexHull

theorem minimizer_ne_zero {μ : ℝ} (hμ : 0 < μ) : minimizer μ ≠ 0 := by
  intro hz
  have hv := minimizer_value hμ
  rw [hz,objective_zero] at hv
  have hn : -1/(514*μ)<0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  linarith

theorem minimizer_active_iff {μ : ℝ} (hμ : 0 < μ) (i : Fin 3) :
    branch μ i (minimizer μ)=objective μ (minimizer μ) ↔ i=0 ∨ i=1 := by
  have hs := minimizer_seed_value hμ
  obtain ⟨h0,h1,h2⟩ := minimizer_seed_active hμ
  change quadratic μ (minimizer μ)+dot (SeedOrbit.gradient seedC seedD i) (minimizer μ)=
    quadratic μ (minimizer μ)+SeedOrbit.objective seedC seedD (minimizer μ) ↔ _
  rw [add_left_cancel_iff,hs]
  fin_cases i
  · simpa [SeedOrbit.gradient] using (show dot g0 (minimizer μ)=-1/(257*μ) ↔ True from ⟨fun _ => trivial,fun _ => h0⟩)
  · simp [SeedOrbit.gradient,h1]
  · simpa [SeedOrbit.gradient] using
      (show dot (g2 seedC seedD) (minimizer μ)=-1/(257*μ) ↔ False from ⟨fun h => h2.ne h,False.elim⟩)

theorem minimizer_not_differentiable {μ : ℝ} (hμ : 0 < μ) :
    ¬ DifferentiableAt ℝ (objective μ) (minimizer μ) := by
  intro hd
  let g : Vec 2 := fun i => fderiv ℝ (objective μ) (minimizer μ) (Pi.single i 1)
  have hg : HasFDerivAt (objective μ) (gradientFunctional g) (minimizer μ) := by
    rw [show gradientFunctional g=fderiv ℝ (objective μ) (minimizer μ) from gradientFunctional_coordinates _]
    exact hd.hasFDerivAt
  have hs (i : Fin 3) (hi : i=0 ∨ i=1) : branchGradient μ (minimizer μ) i=g := by
    apply supporting_vector_eq_gradient _ hg
    exact ConvexSubdifferential.supports_of_local_minorant (objective_convex hμ.le)
      (branch_hasGradient μ i (minimizer μ)) ((minimizer_active_iff hμ i).mpr hi)
      (Eventually.of_forall (branch_le_objective μ i))
  have he := congrFun ((hs 0 (Or.inl rfl)).trans (hs 1 (Or.inr rfl)).symm) 0
  norm_num [branchGradient,SeedOrbit.gradient,g0,g1] at he

theorem minimizer_coordinates (μ : ℝ) : minimizer μ= ![-1/(257*μ),16/(257*μ)] := by
  ext i
  fin_cases i <;> norm_num [minimizer,gbar] <;> ring

theorem gbar_unique_least_sqNorm {g : Vec 2} (hg : g ∈ convexHull ℝ slopes)
    (he : sqNorm g=sqNorm gbar) : g=gbar := by
  have hp := hull_pairing_bound hg
  have hsq : sqNorm (g-gbar)=sqNorm g+sqNorm gbar-2*dot g gbar := by
    simp only [sqNorm,dot,Fin.sum_univ_two,Pi.sub_apply]
    ring
  have hz : sqNorm (g-gbar)=0 := by rw [hsq]; nlinarith [sqNorm_nonneg (g-gbar)]
  exact sub_eq_zero.mp ((CertificateGeometry.sqNorm_eq_zero_iff _).mp hz)

/-- Literal Module L quadratic seed geometry. This theorem makes no claim that
the unperturbed homogeneous orbit is an orbit of the quadratic objective. -/
theorem quadratic_seed_contract {μ : ℝ} (hμ : 0 < μ) :
    (∀ x, objective μ x=μ/2*sqNorm x+SeedOrbit.objective seedC seedD x) ∧
    (∀ x, objective μ x=Finset.univ.sup' Finset.univ_nonempty (fun i => branch μ i x)) ∧
    FixedNormal.EuclideanStrongConvexOn univ μ (objective μ) ∧
    StrongConvexOn univ μ (fun x : EuclideanSpace ℝ (Fin 2) => objective μ (fun i => x i)) ∧
    (∀ i, ConvexOn ℝ univ (branch μ i) ∧ ContDiff ℝ 2 (branch μ i)) ∧
    (∀ i x, RadialHessian.matrix (branch μ i) x=μ • (1 : Mat 2)) ∧
    Tendsto (objective μ) (cocompact (Vec 2)) atTop ∧
    (∀ a, IsCompact {x | objective μ x ≤ a}) ∧
    gbar=(129/257 : ℝ) • g0+(128/257 : ℝ) • g1 ∧
    gbar ∈ convexHull ℝ slopes ∧
    (∀ g ∈ convexHull ℝ slopes, ‖euclideanVector gbar‖ ≤ ‖euclideanVector g‖) ∧
    minimizer μ=(-μ⁻¹) • gbar ∧ minimizer μ ≠ 0 ∧
    objective μ (minimizer μ)=-1/(514*μ) ∧
    (∀ x, objective μ (minimizer μ) ≤ objective μ x) ∧
    (∀ x, objective μ x=objective μ (minimizer μ) → x=minimizer μ) ∧
    (∀ i, branch μ i (minimizer μ)=objective μ (minimizer μ) ↔ i=0 ∨ i=1) ∧
    ¬ DifferentiableAt ℝ (objective μ) (minimizer μ) ∧
    objective μ 0=0 ∧
    ConvexSubdifferential.subdifferential (objective μ) 0=convexHull ℝ slopes ∧
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential (objective μ) 0 := by
  exact ⟨fun _ => rfl,objective_eq_sup μ,objective_strongConvex μ,objective_euclidean_strongConvex μ,
    fun i => ⟨branch_convex hμ.le i,branch_contDiff μ i⟩,branch_hessian μ,
    objective_coercive hμ,objective_sublevels_compact hμ,gbar_weights,gbar_mem_convexHull,
    fun _ hg => gbar_least_norm hg,rfl,minimizer_ne_zero hμ,minimizer_value hμ,
    objective_minimum hμ,fun _ hx => objective_unique_minimum hμ hx,minimizer_active_iff hμ,
    minimizer_not_differentiable hμ,objective_zero μ,origin_subdifferential hμ.le,origin_nonstationary hμ.le⟩

end BfgsVerification.LQuadraticSeed
