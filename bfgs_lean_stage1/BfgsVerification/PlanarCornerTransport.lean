import BfgsVerification.PlanarDerivativeDeterminant
import BfgsVerification.PlanarScalarTransport

/-! Actual one-sided determinant derivatives through C's corner neighborhoods. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter
namespace BfgsVerification
namespace PlanarObjectiveField
open PlanarAmbientFrame HomogeneousPlanar

theorem pairDet_eq_rotated_dot (s v : Vec 2) : pairDet s v=dot (rotate s) v := by
  simp [pairDet,dot,rotate,Fin.sum_univ_two]
  ring

theorem abs_pairDet_le_euclidean_norm (s v : Vec 2) :
    |pairDet s v| ≤ ‖euclideanVector s‖*‖euclideanVector v‖ := by
  rw [pairDet_eq_rotated_dot]
  exact abs_dot_le_of_sqNorm_le (rotate s) v ‖euclideanVector s‖ ‖euclideanVector v‖
    (norm_nonneg _) (norm_nonneg _)
    (by rw [rotate_sqNorm]; exact (FrameNorms.euclidean_norm_sq (euclideanVector s)).symm.le)
    (FrameNorms.euclidean_norm_sq (euclideanVector v)).symm.le

theorem pairDet_hasDerivWithinAt {w : ℝ → Vec 2} {w' s : Vec 2} {t : ℝ} {U : Set ℝ}
    (hw : HasDerivWithinAt w w' U t) :
    HasDerivWithinAt (fun τ => pairDet s (w τ)) (pairDet s w') U t := by
  have hd := (gradientFunctional (rotate s)).hasFDerivAt.comp_hasDerivWithinAt t hw
  change HasDerivWithinAt (fun τ => dot (rotate s) (w τ)) (dot (rotate s) w') U t at hd
  simpa only [← pairDet_eq_rotated_dot] using hd

/-- A neighborhood formula W=v(F) gives the actual determinant right
derivative, including points where the ambient objective is nonsmooth. -/
theorem corner_determinant_hasDerivWithinAt {F : Vec 2 → ℝ} {W : Vec 2 → Vec 2}
    {v : ℝ → Vec 2} {v' x s : Vec 2} {t a : ℝ}
    (hv : HasDerivAt v v' (F (x+t • s)))
    (hφ : HasDerivWithinAt (fun τ : ℝ => F (x+τ • s)) a (Ici t) t)
    (hcorner : ∀ᶠ z in 𝓝 (x+t • s), W z=v (F z)) :
    HasDerivWithinAt (fun τ : ℝ => pairDet s (W (x+τ • s)))
      (pairDet s (a • v')) (Ici t) t := by
  have hl : Continuous (fun τ : ℝ => x+τ • s) := by fun_prop
  have he : ∀ᶠ τ in 𝓝 t, W (x+τ • s)=v (F (x+τ • s)) :=
    (hl.tendsto t).eventually hcorner
  have hw := hv.scomp_hasDerivWithinAt t hφ
  have hw' : HasDerivWithinAt (fun τ : ℝ => W (x+τ • s)) (a • v') (Ici t) t := by
    exact hw.congr_of_eventuallyEq (he.filter_mono nhdsWithin_le_nhds) he.self_of_nhds
  exact pairDet_hasDerivWithinAt hw'

/-- In a corner chart only the bounded level velocity derivative enters the
quotient estimate; no bound on the normal curvature is required. -/
theorem corner_determinant_quotient_bound {s v' : Vec 2} (hs : s ≠ 0)
    {a A κ D : ℝ} (hκ : 0 < κ) (hA : ‖euclideanVector v'‖ ≤ A)
    (hD : κ*‖euclideanVector s‖ ≤ |D|) :
    |pairDet s (a • v')/D| ≤ (A/κ)*|a| := by
  have hsn : 0 < ‖euclideanVector s‖ := norm_pos_iff.mpr (by
    intro h
    exact hs (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => fun i => z i) h))
  have hAn : 0 ≤ A := (norm_nonneg _).trans hA
  have hDn : 0 < |D| := (mul_pos hκ hsn).trans_le hD
  have he : pairDet s (a • v')=a*pairDet s v' := by
    simp only [pairDet,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,abs_div,abs_mul]
  apply (div_le_iff₀ hDn).mpr
  calc
    |a| *|pairDet s v'| ≤ |a| *(‖euclideanVector s‖*‖euclideanVector v'‖) := by
      gcongr
      exact abs_pairDet_le_euclidean_norm s v'
    _ ≤ |a| *(‖euclideanVector s‖*A) := by gcongr
    _ = (A/κ)*|a| *(κ*‖euclideanVector s‖) := by field_simp; ring
    _ ≤ (A/κ)*|a| *|D| := by gcongr

/-- At either kind of structural point, the same actual field has an actual
right determinant derivative controlled by the objective right derivative. -/
theorem field_determinant_right_derivative_bound {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {m : ℕ} {χ : Fin m → Vec 2 → ℝ}
    {v : Fin m → ℝ → Vec 2} {x s : Vec 2} {t a M A κ μ : ℝ}
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hs : s ≠ 0)
    (hv : ∀ i, ContDiffAt ℝ 1 (v i) (F (x+t • s)))
    (hstruct : ContDiffAt ℝ 2 F (x+t • s) ∨ ∃ i,
      ∀ᶠ z in 𝓝 (x+t • s), field hF χ v z=v i (F z))
    (hφ : HasDerivWithinAt (fun τ : ℝ => F (x+τ • s)) a (Ici t) t)
    (hκ : 0 < κ) (hμ : 0 < μ)
    (hgμ : DifferentiableAt ℝ F (x+t • s) →
      μ ≤ ‖euclideanVector (coordinateGradient F (x+t • s))‖)
    (hM : ‖fderiv ℝ (field hF χ v) (x+t • s)‖ ≤ M)
    (hA : ∀ i, ‖euclideanVector (deriv (v i) (F (x+t • s)))‖ ≤ A)
    (hD : κ*‖euclideanVector s‖ ≤ |pairDet s (field hF χ v (x+t • s))|) :
    ∃ D' : ℝ, HasDerivWithinAt (fun τ : ℝ => pairDet s (field hF χ v (x+τ • s))) D' (Ici t) t ∧
      |D'/pairDet s (field hF χ v (x+t • s))| ≤
        max (6*M/(κ*μ)) (A/κ)*|a| := by
  rcases hstruct with hFx | ⟨i,hcorner⟩
  · have hgμ' := hgμ (hFx.differentiableAt (by norm_num))
    have hne : coordinateGradient F (x+t • s) ≠ 0 := by
      intro he
      have hn : euclideanVector (coordinateGradient F (x+t • s))=0 := by rw [he]; rfl
      rw [hn,norm_zero] at hgμ'
      linarith
    have hl : HasDerivAt (fun τ : ℝ => x+τ • s) s t := by
      simpa only [one_smul] using ((hasDerivAt_id t).smul_const s).const_add x
    have hFg := hasFDerivAt_coordinateGradient (hFx.differentiableAt (by norm_num))
    have hFl := hFg.comp_hasDerivAt t hl
    have ha : dot (coordinateGradient F (x+t • s)) s=a := by
      have he := hFl.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi t)
      change derivWithin (fun τ : ℝ => F (x+τ • s)) (Ioi t) t=
        dot (coordinateGradient F (x+t • s)) s at he
      rw [hφ.Ioi_of_Ici.derivWithin (uniqueDiffWithinAt_Ioi t)] at he
      exact he.symm
    have hW := (field_contDiffAt_smooth hF hχ hv hFx hne).differentiableAt (by norm_num)
    have hWl := hW.hasFDerivAt.comp_hasDerivAt t hl
    refine ⟨_,pairDet_hasDerivWithinAt hWl.hasDerivWithinAt,?_⟩
    have hb := tangent_determinant_quotient_bound hne hs _
      (fun u hu => actual_field_derivative_preserves_tangent hF hχ hv hFx hne hu)
      hM hκ hμ hgμ' hD
    rw [ha] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  · refine ⟨_,corner_determinant_hasDerivWithinAt
      ((hv i).differentiableAt (by norm_num)).hasDerivAt hφ hcorner,?_⟩
    exact (corner_determinant_quotient_bound hs hκ (hA i) hD).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))

end PlanarObjectiveField
end BfgsVerification
