import BfgsVerification.PlanarCornerTransport
import BfgsVerification.PlanarFieldStructure
import BfgsVerification.PlanarFieldBuffer

/-! Assembly of C's logarithmic transport for a single actual field on its
compact structural buffer. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter
namespace BfgsVerification
namespace PlanarObjectiveField
open PlanarAmbientFrame HomogeneousPlanar ConvexSubdifferential

/-- The full smooth/corner derivative estimate is discharged for every point
of the segment. The scalar comparison derives transport; it is not a premise. -/
theorem structured_field_segment_transport {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {m : ℕ} {χ : Fin m → Vec 2 → ℝ}
    {v : Fin m → ℝ → Vec 2} {Q : Set (Vec 2)} {x s g : Vec 2} {η G M A κ d : ℝ}
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hs : s ≠ 0)
    (hv : ∀ q ∈ Q, ∀ i, ContDiffAt ℝ 1 (v i) (F q))
    (hstruct : ∀ q ∈ Q, ContDiffAt ℝ 2 F q ∨ ∃ i,
      ∀ᶠ z in 𝓝 q, field hF χ v z=v i (F z))
    (hcont : ∀ q ∈ Q, ContinuousAt (field hF χ v) q)
    (hη : 0 < η) (hG : 0 < G) (hA : 0 ≤ A) (hκ : 0 < κ)
    (hvis : ∀ q ∈ Q, ∀ a ∈ subdifferential F q, η ≤ dot a (field hF χ v q))
    (hW : ∀ q ∈ Q, sqNorm (field hF χ v q) ≤ G^2)
    (hM : ∀ q ∈ Q, ‖fderiv ℝ (field hF χ v) q‖ ≤ M)
    (hvel : ∀ q ∈ Q, ∀ i, ‖euclideanVector (deriv (v i) (F q))‖ ≤ A)
    (hsegment : ∀ t ∈ Icc (0:ℝ) 1, x+t • s ∈ Q)
    (htrans : ∀ t ∈ Icc (0:ℝ) 1, κ*‖euclideanVector s‖ ≤ |pairDet s (field hF χ v (x+t • s))|)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hd : 0 ≤ d) (hgd : dot g s = -d)
    (hdescent : F (x+s) ≤ F x) :
    ∃ lam β : ℝ, 0<lam ∧ field hF χ v (x+s)=lam • field hF χ v x+β • s ∧
      |Real.log lam| ≤ 2*max (6*M/(κ*(η/G))) (A/κ)*d := by
  let φ : ℝ → ℝ := fun t => F (x+t • s)
  have hφ : ConvexOn ℝ univ φ := by
    have hc := hF.comp_affineMap (AffineMap.lineMap (k := ℝ) x (x+s))
    simpa only [AffineMap.lineMap_apply_module',add_sub_cancel_left,Function.comp_def,
      Set.preimage_univ,add_comm] using hc
  have hl : ∀ t : ℝ, HasDerivAt (fun τ : ℝ => x+τ • s) s t := by
    intro t
    simpa only [one_smul] using ((hasDerivAt_id t).smul_const s).const_add x
  have h0 : HasDerivAt φ (-d) 0 := by
    have hc := hg.comp_hasDerivAt_of_eq 0 (hl 0) (by simp)
    simpa only [gradientFunctional_apply,hgd] using hc
  have hφr (t : ℝ) : HasDerivWithinAt φ (derivWithin φ (Ioi t) t) (Ici t) t :=
    (hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)).Ici_of_Ioi
  have hxQ : x ∈ Q := by simpa using hsegment 0 (by norm_num)
  have hMn : 0 ≤ M := (norm_nonneg _).trans (hM x hxQ)
  have hμ : 0 < η/G := div_pos hη hG
  have hC : 0 ≤ max (6*M/(κ*(η/G))) (A/κ) := by positivity
  have hsn : 0 < ‖euclideanVector s‖ := norm_pos_iff.mpr (by
    intro h
    exact hs (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => fun i => z i) h))
  have hne : ∀ t ∈ Icc (0:ℝ) 1, pairDet s (field hF χ v (x+t • s)) ≠ 0 := by
    intro t ht he
    have hb := htrans t ht
    rw [he,abs_zero] at hb
    linarith [mul_pos hκ hsn]
  have hDc : ContinuousOn (fun t : ℝ => pairDet s (field hF χ v (x+t • s))) (Icc 0 1) := by
    intro t ht
    have hc : ContinuousAt (fun τ : ℝ => field hF χ v (x+τ • s)) t :=
      (hcont _ (hsegment t ht)).comp (f := fun τ : ℝ => x+τ • s) (hl t).continuousAt
    have hp : Continuous (fun q : Vec 2 => pairDet s q) := by
      unfold pairDet
      fun_prop
    exact (hp.continuousAt.comp (f := fun τ : ℝ => field hF χ v (x+τ • s)) hc).continuousWithinAt
  have hex (t : ℝ) : ∃ D' : ℝ, t ∈ Ico 0 1 →
      HasDerivWithinAt (fun τ : ℝ => pairDet s (field hF χ v (x+τ • s))) D' (Ici t) t ∧
      |D'/pairDet s (field hF χ v (x+t • s))| ≤
        max (6*M/(κ*(η/G))) (A/κ)*|derivWithin φ (Ioi t) t| := by
    by_cases ht : t ∈ Ico (0:ℝ) 1
    · have hq := hsegment t (Ico_subset_Icc_self ht)
      have hglower : DifferentiableAt ℝ F (x+t • s) →
          η/G ≤ ‖euclideanVector (coordinateGradient F (x+t • s))‖ := by
        intro hgq
        exact gradient_norm_lower_of_visibility hG (hW _ hq)
          (hvis _ hq _ (convex_supporting_inequality hF (hasFDerivAt_coordinateGradient hgq)))
      obtain ⟨D',hder,hbound⟩ := field_determinant_right_derivative_bound hF hχ hs (hv _ hq)
        (hstruct _ hq) (hφr t) hκ hμ hglower (hM _ hq) (hvel _ hq) (htrans t (Ico_subset_Icc_self ht))
      exact ⟨D',fun _ => ⟨hder,hbound⟩⟩
    · exact ⟨0,fun h => (ht h).elim⟩
  choose D' hD' using hex
  exact PlanarScalarTransport.planar_transport_from_right_derivative_budget hC hd hφ h0 hDc hne
    (fun t ht => (hD' t ht).1) (fun t ht => (hD' t ht).2) (by simpa [φ] using hdescent)

end PlanarObjectiveField
end BfgsVerification
