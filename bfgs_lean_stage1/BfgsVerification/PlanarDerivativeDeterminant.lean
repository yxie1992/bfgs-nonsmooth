import BfgsVerification.PlanarFieldTangency
import BfgsVerification.FixedNormalRunBounds

/-! The actual determinant factorization from tangent preservation. The sign
agrees with det(rotated normal, normal)=-1. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarObjectiveField
open PlanarAmbientFrame HomogeneousPlanar

theorem unit_basis_triangular_determinant {w : Vec 2} (hw : sqNorm w=1)
    (sT sn a b e : ℝ) :
    pairDet (sT • rotate w+sn • w) ((a*sT+b*sn) • rotate w+(e*sn) • w)=
      sn*((a-e)*sT+b*sn) := by
  have he : pairDet (sT • rotate w+sn • w) ((a*sT+b*sn) • rotate w+(e*sn) • w)=
      sqNorm w*(sn*((a-e)*sT+b*sn)) := by
    simp only [pairDet,rotate,sqNorm,Fin.sum_univ_two,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  rw [he,hw,one_mul]

/-- Every actual linear derivative preserving the level tangent has the source
triangular determinant factorization, with coefficients defined from that map. -/
theorem actual_tangent_map_determinant {w : Vec 2} (hw : sqNorm w=1)
    (L : Vec 2 →L[ℝ] Vec 2) (ht : dot w (L (rotate w))=0) (s : Vec 2) :
    pairDet s (L s)=dot w s*
      ((dot (rotate w) (L (rotate w))-dot w (L w))*dot (rotate w) s+
        dot (rotate w) (L w)*dot w s) := by
  let sT := dot (rotate w) s
  let sn := dot w s
  let a := dot (rotate w) (L (rotate w))
  let b := dot (rotate w) (L w)
  let e := dot w (L w)
  have hs : s=sT • rotate w+sn • w := by
    have h := PlanarAmbientFrame.reconstruct hw s
    dsimp only [sT,sn]
    rw [add_comm]
    exact h.symm
  have hLt : L (rotate w)=a • rotate w := tangent_vector_eq_rotate hw ht
  have hLn : L w=b • rotate w+e • w := by
    have h := PlanarAmbientFrame.reconstruct hw (L w)
    dsimp only [b,e]
    rw [add_comm]
    exact h.symm
  have hLs : L s=(a*sT+b*sn) • rotate w+(e*sn) • w := by
    calc
      L s = L (sT • rotate w+sn • w) := congrArg L hs
      _ = _ := by
        rw [map_add,map_smul,map_smul,hLt,hLn]
        module
  calc
    pairDet s (L s) = pairDet (sT • rotate w+sn • w)
        ((a*sT+b*sn) • rotate w+(e*sn) • w) := congrArg₂ pairDet hs hLs
    _ = _ := unit_basis_triangular_determinant hw sT sn a b e

theorem rotate_sqNorm (w : Vec 2) : sqNorm (rotate w)=sqNorm w := by
  simp [sqNorm,rotate,Fin.sum_univ_two]
  ring

theorem abs_dot_unit_le_euclidean_norm {w : Vec 2} (hw : sqNorm w=1) (s : Vec 2) :
    |dot w s| ≤ ‖euclideanVector s‖ := by
  have h := abs_dot_le_of_sqNorm_le w s 1 ‖euclideanVector s‖ (by norm_num)
    (norm_nonneg _) (by simpa using hw.le)
    (FrameNorms.euclidean_norm_sq (euclideanVector s)).symm.le
  simpa using h

/-- Coefficients of the derivative in the actual Euclidean unit basis are
bounded by twice its finite-Pi operator norm. -/
theorem abs_dot_unit_map_le {u v : Vec 2} (hu : sqNorm u=1) (hv : sqNorm v=1)
    (L : Vec 2 →L[ℝ] Vec 2) : |dot u (L v)| ≤ 2*‖L‖ := by
  have hvn : ‖v‖^2 ≤ 1 := hv ▸ CenteredSmoothSublinear.pi_norm_sq_le_sqNorm v
  have hLv : sqNorm (L v) ≤ (2*‖L‖)^2 := by
    calc
      sqNorm (L v) ≤ 2*‖L v‖^2 := by
        simpa using FixedNormal.sqNorm_le_dim_mul_norm_sq (L v)
      _ ≤ 2*(‖L‖*‖v‖)^2 := by gcongr; exact L.le_opNorm v
      _ ≤ (2*‖L‖)^2 := by nlinarith [mul_le_mul_of_nonneg_left hvn (sq_nonneg ‖L‖)]
  simpa using abs_dot_le_of_sqNorm_le u (L v) 1 (2*‖L‖)
    (by norm_num) (by positivity) (by simpa using hu.le) hLv

/-- The determinant derivative is proportional to the normal component of
the step. The constant uses the ordinary finite-Pi operator norm explicitly. -/
theorem actual_tangent_map_determinant_bound {w : Vec 2} (hw : sqNorm w=1)
    (L : Vec 2 →L[ℝ] Vec 2) (ht : dot w (L (rotate w))=0) (s : Vec 2) :
    |pairDet s (L s)| ≤ 6*‖L‖*‖euclideanVector s‖*|dot w s| := by
  have hrot : sqNorm (rotate w)=1 := (rotate_sqNorm w).trans hw
  have ha := abs_dot_unit_map_le hrot hrot L
  have hb := abs_dot_unit_map_le hrot hw L
  have he := abs_dot_unit_map_le hw hw L
  have hsT := abs_dot_unit_le_euclidean_norm hrot s
  have hsn := abs_dot_unit_le_euclidean_norm hw s
  have hae : |dot (rotate w) (L (rotate w))-dot w (L w)| ≤ 4*‖L‖ :=
    (abs_sub _ _).trans (by linarith)
  rw [actual_tangent_map_determinant hw L ht,abs_mul]
  calc
    _ ≤ |dot w s| *(|dot (rotate w) (L (rotate w))-dot w (L w)| *|dot (rotate w) s|+
        |dot (rotate w) (L w)| *|dot w s|) := by
      gcongr
      simpa only [abs_mul] using abs_add
        ((dot (rotate w) (L (rotate w))-dot w (L w))*dot (rotate w) s)
        (dot (rotate w) (L w)*dot w s)
    _ ≤ |dot w s| *(4*‖L‖*‖euclideanVector s‖+2*‖L‖*‖euclideanVector s‖) := by
      gcongr
    _ = _ := by ring

/-- Tangent preservation for the actual gradient gives the objective
directional derivative factor, with no assumed lower gradient bound. -/
theorem actual_gradient_tangent_map_bound {g : Vec 2} (hg : g ≠ 0)
    (L : Vec 2 →L[ℝ] Vec 2)
    (ht : ∀ u, dot g u=0 → dot g (L u)=0) (s : Vec 2) :
    |pairDet s (L s)| ≤
      6*‖L‖*‖euclideanVector s‖*|dot g s|/‖euclideanVector g‖ := by
  have hgn : 0 < ‖euclideanVector g‖ := norm_pos_iff.mpr (by
    intro h
    exact hg (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => fun i => z i) h))
  have horth : dot g (rotate (PlanarNormalGeometry.normalized g))=0 := by
    have h := rotate_orthogonal (PlanarNormalGeometry.normalized g)
    rw [PlanarNormalGeometry.normalized,dot_smul_first] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hgn.ne')
  have htn : dot (PlanarNormalGeometry.normalized g)
      (L (rotate (PlanarNormalGeometry.normalized g)))=0 := by
    change dot (‖euclideanVector g‖⁻¹ • g) (L (rotate (PlanarNormalGeometry.normalized g)))=0
    rw [dot_smul_first,ht _ horth,mul_zero]
  have hb := actual_tangent_map_determinant_bound
    (normalized_sqNorm hg) L htn s
  convert hb using 1
  rw [PlanarNormalGeometry.normalized,dot_smul_first,abs_mul,abs_inv,abs_of_pos hgn]
  ring

/-- Applied to the actual joined objective field, the determinant derivative
bound is proved from the constructed field's actual tangent derivative. -/
theorem actual_field_determinant_derivative_bound {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {m : ℕ} {χ : Fin m → Vec 2 → ℝ}
    {v : Fin m → ℝ → Vec 2} {x : Vec 2}
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hv : ∀ i, ContDiffAt ℝ 1 (v i) (F x))
    (hFx : ContDiffAt ℝ 2 F x) (hne : coordinateGradient F x ≠ 0) (s : Vec 2) :
    |pairDet s ((fderiv ℝ (field hF χ v) x) s)| ≤
      6*‖fderiv ℝ (field hF χ v) x‖*‖euclideanVector s‖*|dot (coordinateGradient F x) s|/
        ‖euclideanVector (coordinateGradient F x)‖ := by
  exact actual_gradient_tangent_map_bound hne _
    (fun u hu => actual_field_derivative_preserves_tangent hF hχ hv hFx hne hu) s

/-- A uniform positive visibility margin and a Euclidean field bound give
the needed lower gradient bound by the actual Cauchy--Schwarz inequality. -/
theorem gradient_norm_lower_of_visibility {g w : Vec 2} {η G : ℝ}
    (hG : 0 < G) (hw : sqNorm w ≤ G^2) (hvis : η ≤ dot g w) :
    η/G ≤ ‖euclideanVector g‖ := by
  apply (div_le_iff₀ hG).mpr
  have hb := abs_dot_le_of_sqNorm_le g w ‖euclideanVector g‖ G
    (norm_nonneg _) hG.le (FrameNorms.euclidean_norm_sq (euclideanVector g)).symm.le hw
  exact hvis.trans ((le_abs_self _).trans hb)

/-- The step length cancels against actual transversality. All denominators
are justified positive, and a uniform gradient lower bound is explicit. -/
theorem tangent_determinant_quotient_bound {g s : Vec 2} (hg : g ≠ 0) (hs : s ≠ 0)
    (L : Vec 2 →L[ℝ] Vec 2) (ht : ∀ u, dot g u=0 → dot g (L u)=0)
    {M κ μ D : ℝ} (hM : ‖L‖ ≤ M) (hκ : 0 < κ) (hμ : 0 < μ)
    (hgμ : μ ≤ ‖euclideanVector g‖)
    (hD : κ*‖euclideanVector s‖ ≤ |D|) :
    |pairDet s (L s)/D| ≤ (6*M/(κ*μ))*|dot g s| := by
  have hsn : 0 < ‖euclideanVector s‖ := norm_pos_iff.mpr (by
    intro h
    exact hs (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => fun i => z i) h))
  have hgn : 0 < ‖euclideanVector g‖ := hμ.trans_le hgμ
  have hDn : 0 < |D| := (mul_pos hκ hsn).trans_le hD
  have hMn : 0 ≤ M := (norm_nonneg L).trans hM
  rw [abs_div]
  apply (div_le_iff₀ hDn).mpr
  calc
    |pairDet s (L s)| ≤ 6*‖L‖*‖euclideanVector s‖*|dot g s|/‖euclideanVector g‖ :=
      actual_gradient_tangent_map_bound hg L ht s
    _ ≤ 6*M*‖euclideanVector s‖*|dot g s|/μ := by gcongr
    _ = (6*M/(κ*μ))*|dot g s| *(κ*‖euclideanVector s‖) := by
      field_simp
      <;> ring
    _ ≤ (6*M/(κ*μ))*|dot g s| *|D| := by gcongr

end PlanarObjectiveField
end BfgsVerification
