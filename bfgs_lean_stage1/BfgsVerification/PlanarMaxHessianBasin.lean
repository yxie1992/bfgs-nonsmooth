import BfgsVerification.HessianStrictConvex
import BfgsVerification.PlanarFiniteMaxBasin

/-! Module C's sufficient replacement by a common positive lower bound on the
actual Hessians of the originally relevant branches. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Metric Matrix
namespace BfgsVerification
namespace PlanarMaxRegular
open ConvexSubdifferential PlanarCornerCharts AffineCriticalObjective AffineBarycentric

theorem strictConvexOn_of_hessian_lower_bound {n : ℕ} {f : Vec n → ℝ} {U : Set (Vec n)}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hf : ContDiffOn ℝ 2 f U)
    {μ : ℝ} (hμ : 0<μ) (hh : ∀ x∈U, (RadialHessian.matrix f x-μ • (1 : Mat n)).PosSemidef) :
    StrictConvexOn ℝ U f := by
  apply HessianGeometry.strictConvexOn_of_positive_hessian hU hUc hf
  intro x hx v hv
  have hs : 0<sqNorm v := lt_of_le_of_ne (sqNorm_nonneg v)
    (fun he => hv ((CertificateGeometry.sqNorm_eq_zero_iff v).mp he.symm))
  have h := (hh x hx).2 v
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec_assoc,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,smul_eq_mul] at h
  have he : dotProduct v v=sqNorm v := by simp only [dotProduct,sqNorm,pow_two]
  rw [he] at h
  change 0<dotProduct v ((RadialHessian.matrix f x).mulVec v)
  linarith [mul_pos hμ hs]

theorem strictConvexOn_finite_max {n m : ℕ} {F : Vec n → ℝ} {f : Fin m → Vec n → ℝ}
    {U : Set (Vec n)} (hU : Convex ℝ U)
    (hf : ∀ i, StrictConvexOn ℝ U (f i))
    (hrep : ∀ p∈U, IsGreatest (range (fun i => f i p)) (F p)) : StrictConvexOn ℝ U F := by
  refine ⟨hU,?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hz := hU hx hy ha.le hb.le hab
  obtain ⟨i,hi⟩ := (hrep _ hz).1
  have hlt := (hf i).2 hx hy hxy ha hb hab
  change f i (a • x+b • y)=F (a • x+b • y) at hi
  rw [hi] at hlt
  exact hlt.trans_le (add_le_add
    (mul_le_mul_of_nonneg_left ((hrep x hx).2 (mem_range_self i)) ha.le)
    (mul_le_mul_of_nonneg_left ((hrep y hy).2 (mem_range_self i)) hb.le))

theorem no_segment_frontier_of_local_strictConvex {n : ℕ} {F : Vec n → ℝ}
    (hF : Continuous F) {U : Set (Vec n)} (hstrict : StrictConvexOn ℝ U F)
    {ℓ : ℝ} (hsub : {p | F p≤ℓ}⊆U) (x y : Vec n)
    (hs : segment ℝ x y⊆frontier {p | F p≤ℓ}) : x=y := by
  by_contra hxy
  have hx : F x=ℓ := frontier_le_subset_eq hF continuous_const (hs (left_mem_segment ℝ x y))
  have hy : F y=ℓ := frontier_le_subset_eq hF continuous_const (hs (right_mem_segment ℝ x y))
  have hm : (1/2 : ℝ) • x+(1/2 : ℝ) • y∈segment ℝ x y :=
    ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩
  have he : F ((1/2 : ℝ) • x+(1/2 : ℝ) • y)=ℓ := frontier_le_subset_eq hF continuous_const (hs hm)
  have hlt := hstrict.2 (hsub hx.le) (hsub hy.le) hxy
    (by norm_num : (0 : ℝ)<1/2) (by norm_num : (0 : ℝ)<1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  rw [he,hx,hy] at hlt
  norm_num [smul_eq_mul] at hlt
  linarith

/-- The Hessian hypothesis concerns only the originally active C² branches.
Their maximum supplies strictly convex low contours by a proved local argument. -/
theorem finite_max_hessian_local_basin {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec 2) (hmin : ∀ x, F star≤F x) (hunique : ∀ x, F x=F star → x=star)
    {m : ℕ} {f : Fin m → Vec 2 → ℝ} {U : Set (Vec 2)}
    (hU : IsOpen U) (hstar : star∈U) (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hrep : LocalFiniteMax F f star)
    (hind : AffineIndependent ℝ (fun i => coordinateGradient (f (activeIndexMap F f star i)) star))
    (w : Vec (activeIndices F f star).card) (hw : ∀ i, 0<w i)
    (hsum : ∑ i, w i=1)
    (hzero : ∑ i, w i • coordinateGradient (f (activeIndexMap F f star i)) star=0)
    {μ : ℝ} (hμ : 0<μ)
    (hh : ∀ i : Fin (activeIndices F f star).card, ∀ x∈U,
      (RadialHessian.matrix (f (activeIndexMap F f star i)) x-μ • (1 : Mat 2)).PosSemidef) :
    ∃ ε : ℝ, 0<ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0)<F star+ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  let a := activeIndexMap F f star
  have hr := localFiniteMax_restrict_active (convex_continuous hF).continuousAt
    (fun i => ((hf i).2.contDiffAt (hU.mem_nhds hstar)).continuousAt) hrep
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp (hr.and (hU.mem_nhds hstar))
  have hs : StrictConvexOn ℝ (ball star r) F := by
    apply strictConvexOn_finite_max (convex_ball star r)
    · intro i
      exact strictConvexOn_of_hessian_lower_bound isOpen_ball (convex_ball star r)
        ((hf (a i)).2.mono (fun p hp => (hball hp).2)) hμ (fun p hp => hh i p (hball hp).2)
    · exact fun p hp => (hball hp).1
  obtain ⟨η,hη,hsub⟩ := Localization.neighborhood_basin hF star hmin hunique
    (isOpen_ball.mem_nhds (mem_ball_self hrpos))
  apply finite_max_local_basin hF star hmin hunique hU hstar hf hrep hind w hw hsum hzero
    (b := F star+η) (by linarith)
  intro ℓ hℓ hl x y hxy
  exact no_segment_frontier_of_local_strictConvex (convex_continuous hF) hs
    (fun p hp => hsub (hp.trans hl)) x y hxy

end PlanarMaxRegular
end BfgsVerification
