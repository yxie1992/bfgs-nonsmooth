import BfgsVerification.RatePatchBounds
import BfgsVerification.TransportedCertificateDefinitions

noncomputable section
open scoped BigOperators Topology ContDiff NNReal Manifold
open Matrix Filter Set Metric
namespace BfgsVerification.ConstantRankFields
open AffineCriticalObjective ConvexSubdifferential CenteredSmoothSublinear
open PlanarCrossing TransportedCertificate

/-- A finite rate patch gives a single uniform correction bound over all close
actual differentiable endpoint pairs with positive curvature. No line-search,
metric, iterate, or matrix-convergence premise is used. -/
theorem FiniteRatePatch.secant_bound {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ} {Q : Set (Vec n)}
    (P : FiniteRatePatch F f Q) (hQ : IsCompact Q) :
    ∃δ C : ℝ,0<δ ∧ 0≤C ∧ ∀x z g h : Vec n,
      x∈Q → z∈Q → ‖z-x‖<δ →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      0<pairCurvature x z g h →
        (dot (h-g) (P.field z))^2 / pairCurvature x z g h ≤ C := by
  obtain ⟨δ,hδ,hbuffer⟩ := P.buffer_radius
  obtain ⟨L,hL,hbranches⟩ := P.uniform_one_sided
  obtain ⟨G,hG,hfield⟩ := P.field_bound hQ
  refine ⟨δ,2*L*G^2,hδ,by positivity,?_⟩
  intro x z g h _ hz hstep hg hh ht
  have hb : ∀i : Fin P.size,P.cutoff i z≠0 →
      x∈closedBall (P.center i) ((P.chart i).radius/2) ∧
      z∈closedBall (P.center i) ((P.chart i).radius/2) := fun i hi => hbuffer i x z hi hstep
  obtain ⟨i,hi⟩ := P.cutoff.exists_pos_of_mem hz
  obtain ⟨hxi,hzi⟩ := hb i hi.ne'
  have hx' : x∈ball (P.center i) (P.chart i).radius :=
    (show dist x (P.center i)≤(P.chart i).radius/2 from hxi).trans_lt
      (by linarith [(P.chart i).radius_pos])
  have hz' : z∈ball (P.center i) (P.chart i).radius :=
    (show dist z (P.center i)≤(P.chart i).radius/2 from hzi).trans_lt
      (by linarith [(P.chart i).radius_pos])
  obtain ⟨j,hj,hgj⟩ := exists_actual_active_gradient hF ((P.chart i).representation x hx')
    (fun k => ((P.chart i).branchC2 x hx' k).differentiableAt (by norm_num)) hg
  have hcross := P.cross_pairing hz hb (mem_activeIndices.mpr hj)
  have hvis := P.supportsPairing hz (convex_supporting_inequality hF hh)
  have hnumerator : dot (h-g) (P.field z)=
      dot (coordinateGradient (f j) z-coordinateGradient (f j) x) (P.field z) := by
    rw [dot_sub_left,dot_sub_left,hvis,hcross,hgj]
  have hfz : f j z≤F z :=
    (mem_of_mem_nhds ((P.chart i).representation z hz')).2 ⟨j,rfl⟩
  have hsupport : F z-F x≤dot h (z-x) := by
    have hs := convex_supporting_inequality hF hh x
    change dot h (x-z)≤F x-F z at hs
    have he : dot h (x-z)+dot h (z-x)=0 := by
      simp only [dot,Pi.sub_apply,← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro k _
      ring
    linarith
  have hgap : f j z-f j x-dot (coordinateGradient (f j) x) (z-x) ≤
      pairCurvature x z g h := by
    rw [hj,hgj,pairCurvature,pairStep,dot_sub_left]
    linarith
  have hnorm : sqNorm (coordinateGradient (f j) z-coordinateGradient (f j) x) ≤
      (2*L)*pairCurvature x z g h :=
    (hbranches i j x hxi z hzi).trans (mul_le_mul_of_nonneg_left hgap (by positivity))
  apply (div_le_iff₀ ht).mpr
  rw [hnumerator]
  calc
    _ ≤ sqNorm (coordinateGradient (f j) z-coordinateGradient (f j) x)*sqNorm (P.field z) :=
      dot_sq_le_sqNorm_mul_sqNorm _ _
    _ ≤ ((2*L)*pairCurvature x z g h)*G^2 :=
      mul_le_mul hnorm (hfield z hz) (sqNorm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Source-level construction of visibility and correction in arbitrary finite
dimension, from the actual original-active constant-rank hypothesis. The field
has the C¹ regularity guaranteed by C² branches. -/
theorem source_common_rate_and_secant {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : Fin m → Vec n → ℝ) {K : Set (Vec n)}
    (hK : IsCompact K) (hrep : ∀p∈K,LocalFiniteMax F f p)
    (hC2 : ∀p∈K,∀j,ContDiffAt ℝ 2 (f j) p)
    (hconv : ∀p∈K,∃V : Set (Vec n),IsOpen V ∧ p∈V ∧ ∀j,ConvexOn ℝ V (f j))
    (hnc : ∀p∈K,¬IsAffineCritical F p)
    (hrank : ∀p∈K,LocallyConstantActiveRank F f p) :
    ∃v : Vec n → Vec n,ContDiff ℝ 1 v ∧ ∃V Q : Set (Vec n),
      IsOpen V ∧ K⊆V ∧ closure V⊆Q ∧ IsCompact Q ∧
      ∃G δ C : ℝ,0<G ∧ 0<δ ∧ 0≤C ∧
      (∀x∈Q,sqNorm (v x)≤G^2) ∧
      (∀x∈Q,∀g∈subdifferential F x,dot g (v x)=1) ∧
      ∀x z g h : Vec n,x∈Q → z∈Q → ‖euclideanVector (z-x)‖<δ →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
        0<pairCurvature x z g h → (dot (h-g) (v z))^2 / pairCurvature x z g h ≤ C := by
  obtain ⟨V,Q,hV,hKV,hVQ,hQ,⟨P⟩⟩ := exists_finite_ratePatch hK
    (fun p hp => nonempty_rateChart hF f p (hrep p hp) (hC2 p hp) (hnc p hp) (hrank p hp) (hconv p hp))
  obtain ⟨G,hG,hfield⟩ := P.field_bound hQ
  obtain ⟨δ,C,hδ,hC,hbound⟩ := P.secant_bound hF hQ
  refine ⟨P.field,P.fieldC1,V,Q,hV,hKV,hVQ,hQ,G,δ,C,hG,hδ,hC,hfield,
    fun x hx g hg => P.supportsPairing hx hg,?_⟩
  intro x z g h hx hz hstep
  apply hbound x z g h hx hz
  have hn := FrameNorms.euclidean_norm_sq (euclideanVector (z-x))
  change ‖euclideanVector (z-x)‖^2=sqNorm (z-x) at hn
  exact (norm_le_of_sqNorm_le (norm_nonneg _) hn.symm.le).trans_lt hstep

end BfgsVerification.ConstantRankFields
